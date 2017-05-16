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

(defmacro disasm-instr (on-disasm &body body)
  `(if *disasm*
       ,on-disasm
       (progn ,@body)))

;;; State variables

(defparameter *ram* (make-array (* 64 1024) :initial-element 0 :element-type '(unsigned-byte 8)) "Primary segment")
(defparameter *stack* (make-array (* 64 1024) :initial-element 0 :element-type '(unsigned-byte 8)) "Stack segment")
(defparameter *flags* '(:cf 0 :sf 0 :zf 0) "Flags")
(defparameter *registers* '(:ax 0 :bx 0 :cx 0 :dx 0 :bp 0 :sp #x100 :si 0 :di 0) "Registers")
(defparameter *ip* 0 "Instruction pointer")
(defparameter *has-overflowed* nil "Whether the last wraparound changed the value")

;;; Constants

(defconstant +byte-register-to-word+ '(:al (:ax nil) :ah (:ax t) :bl (:bx nil) :bh (:bx t) :cl (:cx nil) :ch (:cx t) :dl (:dx nil) :dh (:dx t)) "Mapping from byte registers to word registers")
(defconstant +bits-to-register+ '(:ax :cx :dx :bx :sp :bp :si :di) "Mapping from index to word register")
(defconstant +bits-to-byte-register+ '(:al :cl :dl :bl :ah :ch :dh :bh) "Mapping from index to byte register")

;;; Constant mappings

(defun bits->word-reg (bits)
  (elt +bits-to-register+ bits))

(defun bits->byte-reg (bits)
  (elt +bits-to-byte-register+ bits))

(defun address-for-r/m (mod-bits r/m-bits)
  (disasm-instr
      (if (and (= mod-bits #b00) (= r/m-bits #b100))
	  (list :disp (next-word))
	  (case r/m-bits
	    (#b000 (list :base :bx :index :si))
	    (#b001 (list :base :bx :index :di))
	    (#b010 (list :base :bp :index :si))
	    (#b011 (list :base :bp :index :di))
	    (#b100 (list :index :si))
	    (#b101 (list :index :di))
	    (#b110 (list :base :bp))
	    (#b111 (list :base :bx))))
    (if (and (= mod-bits #b00) (= r/m-bits #b100))
	(next-word)
	(case r/m-bits
	  (#b000 (+ (register :bx) (register :si)))
	  (#b001 (+ (register :bx) (register :di)))
	  (#b010 (+ (register :bp) (register :si)))
	  (#b011 (+ (register :bp) (register :di)))
	  (#b100 (register :si))
	  (#b101 (register :di))
	  (#b110 (register :bp))
	  (#b111 (register :bx))))))

;;; Convenience functions

(defun reverse-little-endian (low high)
  "Reverse a little-endian number."
  (+ low (ash high 8)))

(defun negative-p (value is-word)
  (if is-word (>= value #x8000) (>= value #x80)))

(defun twos-complement (value is-word)
  (if (negative-p value is-word)
      (- (1+ (logxor value (if is-word #xffff #xff))))
      value))

(defun wrap-overflow (value is-word)
  "Wrap around an overflowed value."
  (let ((overflow (if is-word (>= value #x10000) (>= value #x100))))
    (setf *has-overflowed* overflow)
    (if overflow
	(if is-word (mod value #x10000) (mod value #x100))
	value)))

;;; setf-able locations

(defun register (reg)
  (disasm-instr reg
    (getf *registers* reg)))

(defun set-reg (reg value)
  (setf (getf *registers* reg) (wrap-overflow value t)))

(defsetf register set-reg)

(defun byte-register (reg)
  (disasm-instr reg
    (let* ((register-to-word (getf +byte-register-to-word+ reg)) (word (first register-to-word)))
      (if (second register-to-word)
	  (ash (register word) -8)
	  (logand (register word) #x00ff)))))

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

(defun byte-in-ram (location segment)
  "Read a byte from a RAM segment."
  (elt segment location))

(defsetf byte-in-ram (location segment) (value)
  "Write a byte to a RAM segment."
  `(setf (elt ,segment ,location) ,value))

(defun word-in-ram (location segment)
  "Read a word from a RAM segment."
  (reverse-little-endian (elt segment location) (elt segment (1+ location))))

(defsetf word-in-ram (location segment) (value)
  "Write a word to a RAM segment."
  `(progn
     (setf (elt ,segment ,location) (logand ,value #x00ff))
     (setf (elt ,segment (1+ ,location)) (ash (logand ,value #xff00) -8))))

(defun indirect-address (mod-bits r/m-bits is-word)
  "Read from an indirect address."
  (disasm-instr
      (if (= mod-bits #b11) (register (if is-word (bits->word-reg r/m-bits) (bits->byte-reg r/m-bits)))
	  (let ((base-index (address-for-r/m mod-bits r/m-bits)))
	    (setf (getf base-index :disp)
		  (case mod-bits
		    (#b00 0)
		    (#b01 (next-instruction))
		    (#b10 (next-word))))
	    base-index))
    (let ((address-base (address-for-r/m mod-bits r/m-bits)))
      (case mod-bits
	(#b00 (if is-word (word-in-ram address-base *ram*) (byte-in-ram address-base *ram*)))
	(#b01 (if is-word (word-in-ram (+ address-base (next-instruction)) *ram*) (byte-in-ram (+ address-base (next-instruction)) *ram*)))
	(#b10 (if is-word (word-in-ram (+ address-base (next-word)) *ram*) (byte-in-ram (+ address-base (next-word)) *ram*)))
	(#b11 (register (if is-word (bits->word-reg r/m-bits) (bits->byte-reg r/m-bits))))))))

(defsetf indirect-address (mod-bits r/m-bits is-word) (value)
  "Write to an indirect address."
  `(let ((address-base (address-for-r/m ,mod-bits ,r/m-bits)))
    (case ,mod-bits
      (#b00 (if ,is-word (setf (word-in-ram address-base *ram*) ,value) (setf (byte-in-ram address-base *ram*) ,value)))
      (#b01 (if ,is-word (setf (word-in-ram (+ address-base (next-instruction)) *ram*) ,value) (setf (byte-in-ram (+ address-base (next-instruction)) *ram*) ,value)))
      (#b10 (if ,is-word (setf (word-in-ram (+ address-base (next-word)) *ram*) ,value) (setf (byte-in-ram (+ address-base (next-word)) *ram*) ,value)))
      (#b11 (setf (register (if ,is-word (bits->word-reg ,r/m-bits) (bits->byte-reg ,r/m-bits))) ,value)))))

;;; Instruction loader

(defun load-instructions-into-ram (instrs)
  (setf *ip* 0)
  (setf (subseq *ram* 0 #x7fff) instrs)
  (length instrs))

(defun next-instruction ()
  (incf *ip*)
  (elt *ram* (1- *ip*)))

(defun next-word ()
  (reverse-little-endian (next-instruction) (next-instruction)))

;;; Memory access

(defun read-word-from-ram (loc &optional (segment *ram*))
  (word-in-ram loc segment))

(defun write-word-to-ram (loc word &optional (segment *ram*))
  (setf (word-in-ram loc segment) word))

(defun push-to-stack (value)
  (decf (register :sp) 2)
  (write-word-to-ram (register :sp) value *stack*))

(defun pop-from-stack ()
  (incf (register :sp) 2)
  (read-word-from-ram (- (register :sp) 2) *stack*))

;;; Flag effects

(defun set-cf-on-add (value)
  (setf (flag-p :cf) *has-overflowed*)
  value)

(defun set-cf-on-sub (value1 value2)
  (setf (flag-p :cf) (> value2 value1))
  value1)

(defun set-sf-on-op (value is-word)
  (setf (flag-p :sf) (negative-p value is-word))
  value)

(defun set-zf-on-op (value)
  (setf (flag-p :zf) (= value 0))
  value)

;;; Operations

;; Context wrappers

(defun with-one-byte-opcode-register (opcode fn)
  (let ((reg (bits->word-reg (mod opcode #x08))))
    (funcall fn reg)))

(defmacro with-mod-r/m-byte (&body body)
  `(let* ((mod-r/m (next-instruction)) (r/m-bits (logand mod-r/m #b00000111)) (mod-bits (ash (logand mod-r/m #b11000000) -6)) (reg-bits (ash (logand mod-r/m #b00111000) -3)))
     ,@body))

;; Templates

(defmacro mov (src dest)
  `(disasm-instr (list "mov" :src ,src :dest ,dest)
     (setf ,dest ,src)))

(defmacro xchg (op1 op2)
  `(disasm-instr (list "xchg" :op1 ,op1 :op2 ,op2)
     (rotatef ,op1 ,op2)))

(defmacro inc (op1 is-word)
  `(disasm-instr (list "inc" :op1 ,op1)
     (set-sf-on-op (set-zf-on-op (incf ,op1)) ,is-word)))

(defmacro dec (op1 is-word)
  `(disasm-instr (list "dec" :op1 ,op1)
     (set-sf-on-op (set-zf-on-op (decf ,op1)) ,is-word)))

;; Group handling

(defmacro parse-group-byte-pair (opcode operation mod-bits r/m-bits)
  `(,operation ,mod-bits ,r/m-bits (oddp ,opcode)))

(defmacro parse-group-opcode (&body body)
  `(with-mod-r/m-byte
     (case reg-bits
       ,@body)))

;; One-byte opcodes on registers

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
  (inc (register reg) t))

(defun dec-register (reg)
  (dec (register reg) t))

(defun xchg-register (reg)
  (disasm-instr (if (eql reg :ax) '("nop") (list "xchg" :op1 :ax :op2 reg))
    (xchg (register :ax) (register reg))))

(defun mov-byte-to-register (opcode)
  (let ((reg (bits->byte-reg (mod opcode #x08))))
    (mov (next-instruction) (byte-register reg))))

(defun mov-word-to-register (reg)
  (mov (next-word) (register reg)))

;; Flow control

(defun jmp-short ()
  (disasm-instr (list "jmp" :op1 (twos-complement (next-instruction) nil))
    (incf *ip* (twos-complement (next-instruction) nil))))

(defmacro jmp-short-conditionally (opcode condition mnemonic)
  `(if (= (mod ,opcode #x02) 1)
       (disasm-instr (list (concatenate 'string "jn" ,mnemonic) :op1 (twos-complement (next-instruction) nil))
	 (unless ,condition
	   (incf *ip* (twos-complement (next-instruction) nil))))
       (disasm-instr (list (concatenate 'string "j" ,mnemonic) :op1 (twos-complement (next-instruction) nil))
	 (when ,condition
	   (incf *ip* (twos-complement (next-instruction) nil))))))

(defun call-near ()
  (disasm-instr (list "call" :op1 (twos-complement (next-word) t))
    (push-to-stack (+ *ip* 2))
    (incf *ip* (twos-complement (next-word) t))))

(defun ret-from-call ()
  (disasm-instr '("ret")
    (setf *ip* (pop-from-stack))))

;; ALU

(defmacro parse-alu-opcode (opcode operation)
  `(let ((mod-8 (mod ,opcode 8)))
     (cond
       ((= mod-8 0)
	(with-mod-r/m-byte
	  (,operation (byte-register (bits->byte-reg reg-bits)) (indirect-address mod-bits r/m-bits nil) nil)))
       ((= mod-8 1)
	(with-mod-r/m-byte
	  (,operation (register (bits->word-reg reg-bits)) (indirect-address mod-bits r/m-bits t) t)))
       ((= mod-8 2)
	(with-mod-r/m-byte
	  (,operation (indirect-address mod-bits r/m-bits nil) (byte-register (bits->byte-reg reg-bits)) nil)))
       ((= mod-8 3)
	(with-mod-r/m-byte
	  (,operation (indirect-address mod-bits r/m-bits t) (register (bits->word-reg reg-bits)) t)))
       ((= mod-8 4)
	(,operation (next-instruction) (byte-register :al) nil))
       ((= mod-8 5)
	(,operation (next-word) (register :ax) t)))))

(defmacro add-without-carry (src dest is-word)
  `(disasm-instr (list "add" :src ,src :dest ,dest)
     (set-zf-on-op (set-sf-on-op (set-cf-on-add (incf ,dest ,src)) ,is-word))))

(defmacro add-with-carry (src dest is-word)
  `(disasm-instr (list "adc" :src ,src :dest ,dest)
     (set-zf-on-op (set-sf-on-op (set-cf-on-add (incf ,dest (+ ,src (flag :cf)))) ,is-word))))

(defmacro sub-without-borrow (src dest is-word)
  `(disasm-instr (list "sub" :src ,src :dest ,dest)
     (set-zf-on-op (set-sf-on-op (set-cf-on-sub (decf ,dest ,src) ,src) ,is-word))))

(defmacro sub-with-borrow (src dest is-word)
  `(disasm-instr (list "sbb" :src ,src :dest ,dest)
     (set-zf-on-op (set-sf-on-op (set-cf-on-sub (decf ,dest (+ ,src (flag :cf))) (+ ,src (flag :cf))) ,is-word))))

(defmacro cmp-operation (src dest is-word)
  `(disasm-instr (list "cmp" :src ,src :dest ,dest)
     (set-zf-on-op (set-sf-on-op (set-cf-on-sub (- ,dest ,src) ,src) ,is-word))))

(defmacro and-operation (src dest is-word)
  `(disasm-instr (list "and" :src ,src :dest ,dest)
     (set-zf-on-op (set-sf-on-op (setf ,dest (logand ,src ,dest)) ,is-word))
     (setf (flag-p :cf) nil)))

(defmacro or-operation (src dest is-word)
  `(disasm-instr (list "or" :src ,src :dest ,dest)
     (set-zf-on-op (set-sf-on-op (setf ,dest (logior ,src ,dest)) ,is-word))
     (setf (flag-p :cf) nil)))

(defmacro xor-operation (src dest is-word)
  `(disasm-instr (list "xor" :src ,src :dest ,dest)
     (set-zf-on-op (set-sf-on-op (setf ,dest (logxor ,src ,dest)) ,is-word))
     (setf (flag-p :cf) nil)))

(defmacro parse-group1-byte (opcode operation mod-bits r/m-bits)
  `(case (mod ,opcode 4)
    (0 (,operation (next-instruction) (indirect-address ,mod-bits ,r/m-bits nil) nil))
    (1 (,operation (next-word) (indirect-address ,mod-bits ,r/m-bits t) t))
    (3 (,operation (sign-extend (next-instruction)) (indirect-address ,mod-bits ,r/m-bits t) t))))

(defmacro parse-group1-opcode (opcode)
  `(parse-group-opcode
     (0 (parse-group1-byte ,opcode add-without-carry mod-bits r/m-bits))
     (1 (parse-group1-byte ,opcode or-operation mod-bits r/m-bits))
     (2 (parse-group1-byte ,opcode add-with-carry mod-bits r/m-bits))
     (3 (parse-group1-byte ,opcode sub-with-borrow mod-bits r/m-bits))
     (4 (parse-group1-byte ,opcode and-operation mod-bits r/m-bits))
     (5 (parse-group1-byte ,opcode sub-without-borrow mod-bits r/m-bits))
     (6 (parse-group1-byte ,opcode xor-operation mod-bits r/m-bits))
     (7 (parse-group1-byte ,opcode cmp-operation mod-bits r/m-bits))))

;; Memory and register mov/xchg

(defun xchg-memory-register (opcode)
  (let ((is-word (oddp opcode)))
    (with-mod-r/m-byte
      (if is-word
	  (xchg (register (bits->word-reg reg-bits)) (indirect-address mod-bits r/m-bits is-word))
	  (xchg (byte-register (bits->byte-reg reg-bits)) (indirect-address mod-bits r/m-bits is-word))))))

(defmacro mov-immediate-to-memory (mod-bits r/m-bits is-word)
  `(if ,is-word
       (mov (next-word) (indirect-address ,mod-bits ,r/m-bits t))
       (mov (next-instruction) (indirect-address ,mod-bits ,r/m-bits nil))))

(defmacro parse-group11-opcode (opcode)
  `(parse-group-opcode
     (0 (parse-group-byte-pair ,opcode mov-immediate-to-memory mod-bits r/m-bits))))

(defmacro parse-mov-opcode (opcode)
  `(let ((mod-4 (mod ,opcode 4)))
     (with-mod-r/m-byte
       (cond
	 ((= mod-4 0)
	  (mov (byte-register (bits->byte-reg reg-bits)) (indirect-address mod-bits r/m-bits nil)))
	 ((= mod-4 1)
	  (mov (register (bits->word-reg reg-bits)) (indirect-address mod-bits r/m-bits t)))
	 ((= mod-4 2)
	  (mov (indirect-address mod-bits r/m-bits nil) (byte-register (bits->byte-reg reg-bits))))
	 ((= mod-4 3)
	  (mov (indirect-address mod-bits r/m-bits t) (register (bits->word-reg reg-bits))))))))

;; Group 4/5 (inc/dec on EAs)

(defmacro inc-indirect (mod-bits r/m-bits is-word)
  `(inc (indirect-address ,mod-bits ,r/m-bits ,is-word) ,is-word))

(defmacro dec-indirect (mod-bits r/m-bits is-word)
  `(dec (indirect-address ,mod-bits ,r/m-bits ,is-word) ,is-word))

(defmacro parse-group4/5-opcode (opcode)
  `(parse-group-opcode
     (0 (parse-group-byte-pair ,opcode inc-indirect mod-bits r/m-bits))
     (1 (parse-group-byte-pair ,opcode dec-indirect mod-bits r/m-bits))))

;;; Opcode parsing

(defun in-paired-byte-block-p (opcode block)
  (= (truncate (/ opcode 2)) (/ block 2)))

(defun in-4-byte-block-p (opcode block)
  (= (truncate (/ opcode 4)) (/ block 4)))

(defun in-8-byte-block-p (opcode block)
  (= (truncate (/ opcode 8)) (/ block 8)))

(defun in-6-byte-block-p (opcode block)
  (and (= (truncate (/ opcode 8)) (/ block 8)) (< (mod opcode 8) 6)))

(defun parse-opcode (opcode)
  "Parse an opcode."
  (cond
    ((not opcode) (return-from parse-opcode nil))
    ((= opcode #xf4) (return-from parse-opcode '("hlt")))
    ((in-8-byte-block-p opcode #x40) (with-one-byte-opcode-register opcode #'inc-register))
    ((in-8-byte-block-p opcode #x48) (with-one-byte-opcode-register opcode #'dec-register))
    ((in-8-byte-block-p opcode #x50) (with-one-byte-opcode-register opcode #'push-register))
    ((in-8-byte-block-p opcode #x58) (with-one-byte-opcode-register opcode #'pop-to-register))
    ((in-8-byte-block-p opcode #x90) (with-one-byte-opcode-register opcode #'xchg-register))
    ((in-8-byte-block-p opcode #xb0) (mov-byte-to-register opcode))
    ((in-8-byte-block-p opcode #xb8) (with-one-byte-opcode-register opcode #'mov-word-to-register))
    ((= opcode #xf8) (clear-carry-flag))
    ((= opcode #xf9) (set-carry-flag))
    ((= opcode #xeb) (jmp-short))
    ((in-paired-byte-block-p opcode #x72) (jmp-short-conditionally opcode (flag-p :cf) "b"))
    ((in-paired-byte-block-p opcode #x74) (jmp-short-conditionally opcode (flag-p :zf) "z"))
    ((in-paired-byte-block-p opcode #x76) (jmp-short-conditionally opcode (or (flag-p :cf) (flag-p :zf)) "be"))
    ((in-paired-byte-block-p opcode #x78) (jmp-short-conditionally opcode (flag-p :sf) "s"))
    ((= opcode #xe8) (call-near))
    ((= opcode #xc3) (ret-from-call))
    ((in-6-byte-block-p opcode #x00) (parse-alu-opcode opcode add-without-carry))
    ((in-6-byte-block-p opcode #x08) (parse-alu-opcode opcode or-operation))
    ((in-6-byte-block-p opcode #x10) (parse-alu-opcode opcode add-with-carry))
    ((in-6-byte-block-p opcode #x18) (parse-alu-opcode opcode sub-with-borrow))
    ((in-6-byte-block-p opcode #x20) (parse-alu-opcode opcode and-operation))
    ((in-6-byte-block-p opcode #x28) (parse-alu-opcode opcode sub-without-borrow))
    ((in-6-byte-block-p opcode #x30) (parse-alu-opcode opcode xor-operation))
    ((in-6-byte-block-p opcode #x38) (parse-alu-opcode opcode cmp-operation))
    ((in-4-byte-block-p opcode #x80) (parse-group1-opcode opcode))
    ((in-4-byte-block-p opcode #x88) (parse-mov-opcode opcode))
    ((in-paired-byte-block-p opcode #x86) (xchg-memory-register opcode))
    ((in-paired-byte-block-p opcode #xc6) (parse-group11-opcode opcode))
    ((in-paired-byte-block-p opcode #xfe) (parse-group4/5-opcode opcode))))

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
     until (= *ip* instr-length)
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

(defparameter *test-instructions* #(#x40 #x40 #x05 #x03 #x00 #x91 #xb0 #xff #x04 #x01 #x72 #x04 #x50 #x5a #x51 #x52 #x48 #xff #b11001011 #x43 #x74 #x03 #xbe #x02 #x03 #x01 #b11001111 #x47 #x83 #b11000111 #xfe #xf4) "Test instructions")
