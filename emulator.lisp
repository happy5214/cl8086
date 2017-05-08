;;;; Copyright (C) 2017 Alexander Jones
;;;;
;;;; Permission is hereby granted, free of charge, to any person obtaining a
;;;; copy of this software and associated documentation files (the "Software"),
;;;; to deal in the Software without restriction, including without limitation
;;;; the rights to use, copy, modify, merge, publish, distribute, sublicense,
;;;; and/or sell copies of the Software, and to permit persons to whom the
;;;; Software is furnished to do so, subject to the following conditions:
;;;;
;;;; The above copyright notice and this permission notice shall be included in
;;;; all copies or substantial portions of the Software.
;;;;
;;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;;;; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;;;; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;;;; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;;;; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;;;; FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;;;; DEALINGS IN THE SOFTWARE.

; State
(defparameter *ram* (make-array (* 64 1024) :initial-element 0 :element-type '(unsigned-byte 8)) "Primary segment")
(defparameter *stack* (make-array (* 64 1024) :initial-element 0 :element-type '(unsigned-byte 8)) "Stack segment")
(defparameter *flags* '(:cf nil :sf nil :zf nil) "Flags")
(defparameter *registers* '(:ax 0 :bx 0 :cx 0 :dx 0 :bp 0 :sp #x100 :si 0 :di 0 :ip 0) "Registers")

; Constants
(defconstant +byte-register-to-word+ '(:al (:ax nil) :ah (:ax t) :bl (:bx nil) :bh (:bx t) :cl (:cx nil) :ch (:cx t) :dl (:dx nil) :dh (:dx t)) "Mapping from byte registers to word registers")
(defconstant +bits-to-register+ '(:ax :cx :dx :bx :sp :bp :si :di) "Mapping from index to word register")
(defconstant +bits-to-byte-register+ '(:al :cl :dl :bl :ah :ch :dh :bh) "Mapping from index to byte register")

; Constant mappings

(defun bits->word-reg (bits)
  (elt +bits-to-register+ bits))

(defun bits->byte-reg (bits)
  (elt +bits-to-byte-register+ bits))

; setf-able locations

(defun register (reg)
  (getf *registers* reg))

(defun set-reg (reg value)
  (setf (getf *registers* reg) value))

(defsetf register set-reg)

(defun byte-register (reg)
  (let* ((register-to-word (getf +byte-register-to-word+ reg)) (word (first register-to-word)))
    (if (second register-to-word)
	(ash (register word) -8)
	(logand (register word) #x00ff))))

(defun set-byte-reg (reg value)
  (let* ((register-to-word (getf +byte-register-to-word+ reg)) (word (first register-to-word)))
    (if (second register-to-word)
	(setf (register word) (+ (ash value 8) (logand (register word) #x00ff)))
	(setf (register word) (+ value (logand (register word) #xff00))))))

(defsetf byte-register set-byte-reg)

(defun flag (flag-name)
  (getf *flags* flag-name))

(defun set-flag (flag-name is-set)
  (setf (getf *flags* flag-name) is-set))

(defsetf flag set-flag)

; Convenience functions

(defun reverse-little-endian (low high)
  "Reverse a little-endian number."
  (+ low (ash high 8)))

; RAM access

(defun read-word-from-ram (loc &optional (segment *ram*))
  "Read a word from a RAM segment."
  (reverse-little-endian (elt segment loc) (elt segment (1+ loc))))

(defun write-word-to-ram (loc word &optional (segment *ram*))
  (setf (elt segment loc) (logand word #x00ff))
  (setf (elt segment (1+ loc)) (ash (logand word #xff00) -8)))

(defun push-to-stack (b)
  (decf (register :sp) 2)
  (write-word-to-ram (register :sp) b *stack*))

(defun pop-from-stack ()
  (incf (register :sp) 2)
  (read-word-from-ram (- (register :sp) 2) *stack*))

; Instruction loader

(defun next-instruction ()
  (incf (register :ip))
  (elt *ram* (1- (register :ip))))

(defun load-instructions (instrs)
  (setf (register :ip) 0)
  (setf (subseq *ram* 0 #x7fff) instrs))

; Operations

(defun clear-carry-flag ()
  (setf (flag :cf) nil))

(defun set-carry-flag ()
  (setf (flag :cf) t))

(defun mov-byte-to-register (opcode)
  (let ((reg (bits->byte-reg (mod opcode #x08))))
    (setf (byte-register reg) (next-instruction))
    (list "mov" :src (byte-register reg) :dest reg)))

(defun mov-word-to-register (reg)
  (setf (register reg) (reverse-little-endian (next-instruction) (next-instruction)))
  (list "mov" :src (register reg) :dest reg))

(defmacro with-one-byte-opcode-register (opcode &body body)
  `(let ((reg (bits->word-reg (mod ,opcode #x08))))
     ,@body))

(defun push-register (reg)
  (push-to-stack (register reg))
  (list "push" :src reg))

(defun pop-to-register (reg)
  (setf (register reg) (pop-from-stack))
  (list "pop" :dest reg))

(defun inc-register (reg)
  (incf (register reg))
  (list "inc" :op1 reg))

(defun dec-register (reg)
  (decf (register reg))
  (list "dec" :op1 reg))

(defun xchg-register (reg)
  (if (eql reg :ax)
      (list "nop")
      (progn
	(rotatef (register :ax) (register reg))
	(list "xchg" :op1 :ax :op2 reg))))

; Opcode parsing

(defun in-8-byte-block-p (opcode block)
  (= (truncate (/ opcode 8)) (/ block 8)))

(defun parse-opcode (opcode)
  "Parse an opcode."
  (cond
    ((= opcode #xf4) (return-from parse-opcode '("hlt")))
    ((in-8-byte-block-p opcode #x40) (with-one-byte-opcode-register opcode (inc-register reg)))
    ((in-8-byte-block-p opcode #x48) (with-one-byte-opcode-register opcode (dec-register reg)))
    ((in-8-byte-block-p opcode #x50) (with-one-byte-opcode-register opcode (push-register reg)))
    ((in-8-byte-block-p opcode #x58) (with-one-byte-opcode-register opcode (pop-to-register reg)))
    ((in-8-byte-block-p opcode #x90) (with-one-byte-opcode-register opcode (xchg-register reg)))
    ((in-8-byte-block-p opcode #xb0) (mov-byte-to-register opcode))
    ((in-8-byte-block-p opcode #xb8) (with-one-byte-opcode-register opcode (mov-word-to-register reg)))
    ((= opcode #xf8) (clear-carry-flag))
    ((= opcode #xf9) (set-carry-flag))))

(defun loop-instructions (&optional (return-disasm nil))
  "Loop through loaded instructions."
  (loop
     for ret = (parse-opcode (next-instruction))
     collecting ret into disasm
     until (equal ret '("hlt"))
     finally (return (if return-disasm disasm t))))

(defparameter *test-instructions* #(#x40 #x40 #x40 #x91 #xb0 #xff #x50 #x5a #x52 #x51 #x48 #xbe #x02 #x03 #xf4))
