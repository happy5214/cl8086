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

;;; Program settings

(defparameter *disasm* nil "Whether to disassemble")

;;; State variables

(defparameter *ram* (make-array (* 64 1024) :initial-element 0 :element-type '(unsigned-byte 8)) "Primary segment")
(defparameter *stack* (make-array (* 64 1024) :initial-element 0 :element-type '(unsigned-byte 8)) "Stack segment")
(defparameter *flags* '(:cf 0 :sf 0 :zf 0) "Flags")
(defparameter *registers* '(:ax 0 :bx 0 :cx 0 :dx 0 :bp 0 :sp #x100 :si 0 :di 0 :ip 0) "Registers")

;;; Constants

(defconstant +byte-register-to-word+ '(:al (:ax nil) :ah (:ax t) :bl (:bx nil) :bh (:bx t) :cl (:cx nil) :ch (:cx t) :dl (:dx nil) :dh (:dx t)) "Mapping from byte registers to word registers")
(defconstant +bits-to-register+ '(:ax :cx :dx :bx :sp :bp :si :di) "Mapping from index to word register")
(defconstant +bits-to-byte-register+ '(:al :cl :dl :bl :ah :ch :dh :bh) "Mapping from index to byte register")

;;; Constant mappings

(defun bits->word-reg (bits)
  (elt +bits-to-register+ bits))

(defun bits->byte-reg (bits)
  (elt +bits-to-byte-register+ bits))

;;; setf-able locations

(defun register (reg)
  (getf *registers* reg))

(defun set-reg (reg value)
  (setf (getf *registers* reg) (wrap-overflow value t)))

(defsetf register set-reg)

(defun byte-register (reg)
  (let* ((register-to-word (getf +byte-register-to-word+ reg)) (word (first register-to-word)))
    (if (second register-to-word)
	(ash (register word) -8)
	(logand (register word) #x00ff))))

(defun set-byte-reg (reg value)
  (let* ((register-to-word (getf +byte-register-to-word+ reg)) (word (first register-to-word)) (wrapped-value (wrap-overflow value nil)))
    (if (second register-to-word)
	(setf (register word) (+ (ash wrapped-value 8) (logand (register word) #x00ff)))
	(setf (register word) (+ wrapped-value (logand (register word) #xff00))))))

(defsetf byte-register set-byte-reg)

(defun flag (name)
  (getf *flags* name))

(defun set-flag (name value)
  (setf (getf *flags* name) value))

(defsetf flag set-flag)

(defun flag-p (name)
  (= (flag name) 1))

(defun set-flag-p (name is-set)
  (setf (flag name) (if is-set 1 0)))

(defsetf flag-p set-flag-p)

;;; Convenience functions

(defun reverse-little-endian (low high)
  "Reverse a little-endian number."
  (+ low (ash high 8)))

(defun wrap-overflow (value is-word)
  "Wrap around an overflowed value."
  (if is-word (mod value #x10000) (mod value #x100)))

;;; Instruction loader

(defun load-instructions-into-ram (instrs)
  (setf (register :ip) 0)
  (setf (subseq *ram* 0 #x7fff) instrs)
  (length instrs))

(defun next-instruction ()
  (incf (register :ip))
  (elt *ram* (1- (register :ip))))

(defun next-word ()
  (reverse-little-endian (next-instruction) (next-instruction)))

;;; Memory access

(defun read-word-from-ram (loc &optional (segment *ram*))
  "Read a word from a RAM segment."
  (reverse-little-endian (elt segment loc) (elt segment (1+ loc))))

(defun write-word-to-ram (loc word &optional (segment *ram*))
  "Write a word to a RAM segment."
  (setf (elt segment loc) (logand word #x00ff))
  (setf (elt segment (1+ loc)) (ash (logand word #xff00) -8)))

(defun push-to-stack (value)
  (decf (register :sp) 2)
  (write-word-to-ram (register :sp) value *stack*))

(defun pop-from-stack ()
  (incf (register :sp) 2)
  (read-word-from-ram (- (register :sp) 2) *stack*))

;;; Flag effects

(defun set-cf-on-add (value is-word)
  (setf (flag-p :cf) (if is-word (>= value #x10000) (>= value #x100)))
  (wrap-overflow value is-word))

(defun set-cf-on-sub (value1 value2)
  (setf (flag-p :cf) (> value2 value1))
  value1)

(defun set-sf-on-op (value is-word)
  (setf (flag-p :sf) (if is-word (>= value #x8000) (>= value #x80)))
  value)

(defun set-zf-on-op (value)
  (setf (flag-p :zf) (= value 0))
  value)

;;; Operations

(defmacro disasm-instr (on-disasm &body body)
  `(if *disasm*
       ,on-disasm
       (progn ,@body)))

(defmacro with-one-byte-opcode-register (opcode &body body)
  `(let ((reg (bits->word-reg (mod ,opcode #x08))))
     ,@body))

(defun clear-carry-flag ()
  (disasm-instr '("clc")
    (setf (flag-p :cf) nil)))

(defun set-carry-flag ()
  (disasm-instr '("stc")
    (setf (flag-p :cf) t)))

(defun push-register (reg)
  (disasm-instr (list "push" :src reg)
    (push-to-stack (register reg))))

(defun pop-to-register (reg)
  (disasm-instr (list "pop" :dest reg)
    (setf (register reg) (pop-from-stack))))

(defun inc-register (reg)
  (disasm-instr (list "inc" :op1 reg)
    (set-sf-on-op (set-zf-on-op (incf (register reg))) t)))

(defun dec-register (reg)
  (disasm-instr (list "dec" :op1 reg)
    (set-sf-on-op (set-zf-on-op (decf (register reg))) t)))

(defun xchg-register (reg)
  (disasm-instr (if (eql reg :ax) '("nop") (list "xchg" :op1 :ax :op2 reg))
    (rotatef (register :ax) (register reg))))

(defun mov-byte-to-register (opcode)
  (let ((reg (bits->byte-reg (mod opcode #x08))))
    (disasm-instr (list "mov" :src (next-instruction) :dest reg)
      (setf (byte-register reg) (next-instruction)))))

(defun mov-word-to-register (reg)
  (disasm-instr (list "mov" :src (next-word) :dest reg)
    (setf (register reg) (next-word))))

;;; Opcode parsing

(defun in-8-byte-block-p (opcode block)
  (= (truncate (/ opcode 8)) (/ block 8)))

(defun parse-opcode (opcode)
  "Parse an opcode."
  (cond
    ((not opcode) (return-from parse-opcode nil))
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

;;; Main functions

(defun execute-instructions ()
  "Loop through loaded instructions."
  (loop
     for ret = (parse-opcode (next-instruction))
     until (equal ret '("hlt"))
     finally (return t)))

(defun disasm-instructions (instr-length)
  "Disassemble code."
  (loop
     for ret = (parse-opcode (next-instruction))
     collecting ret into disasm
     until (= (register :ip) instr-length)
     finally (return disasm)))

(defun loop-instructions (instr-length)
  (if *disasm*
      (disasm-instructions instr-length)
      (execute-instructions)))

(defun load-instructions-from-file (file)
  (format t "~a" file) ; Placeholder
  #())

(defun load-instructions (&key (file nil))
  (if file
      (load-instructions-from-file file)
      *test-instructions*))

(defun main (&key (disasm nil) (file nil))
  (setf *disasm* disasm)
  (loop-instructions (load-instructions-into-ram (load-instructions :file file))))

;;; Test instructions

(defparameter *test-instructions* #(#x40 #x40 #x40 #x91 #xb0 #xff #x50 #x5a #x52 #x51 #x48 #xbe #x02 #x03 #xf4) "Test instructions")
