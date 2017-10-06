;;;; Intel 8086 emulator

;;; Program settings

(defparameter *disasm* nil "Whether to disassemble")

(defmacro disasm-instr (on-disasm &body body)
  `(if *disasm*
       ,on-disasm
       (progn ,@body)))

;;; State variables

(defparameter *ram* (make-array (* 64 1024) :initial-element 0 :element-type '(unsigned-byte 8)) "Primary segment")
(defparameter *stack* (make-array (* 64 1024) :initial-element 0 :element-type '(unsigned-byte 8)) "Stack segment")
(defparameter *flags* '(:af 0 :cf 0 :df 0 :of 0 :pf 0 :sf 0 :zf 0) "Flags")
(defparameter *registers* '(:ax 0 :bx 0 :cx 0 :dx 0 :bp 0 :sp #x100 :si 0 :di 0) "Registers")
(defparameter *ip* 0 "Instruction pointer")
(defparameter *has-carried* nil "Whether the last wraparound changed the value")
(defparameter *advance* 0 "Bytes to advance IP by after an operation")

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
      (if (and (= mod-bits #b00) (= r/m-bits #b110))
	  (list :disp (peek-at-word))
	  (case r/m-bits
	    (#b000 (list :base :bx :index :si))
	    (#b001 (list :base :bx :index :di))
	    (#b010 (list :base :bp :index :si))
	    (#b011 (list :base :bp :index :di))
	    (#b100 (list :index :si))
	    (#b101 (list :index :di))
	    (#b110 (list :base :bp))
	    (#b111 (list :base :bx))))
    (if (and (= mod-bits #b00) (= r/m-bits #b110))
	(peek-at-word)
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
  (let ((sign-and (if is-word #x8000 #x80)))
    (= (logand sign-and value) sign-and)))

(defun twos-complement (value is-word)
  (if (negative-p value is-word)
      (- (1+ (logxor value (if is-word #xffff #xff))))
      value))

(defun wrap-carry (value is-word)
  "Wrap around a carried value."
  (let* ((limit (if is-word #x10000 #x100)) (carry (>= value limit)) (negative (minusp value)))
    (setf *has-carried* (or carry negative))
    (cond
      (carry (mod value limit))
      (negative (+ value limit))
      (t value))))

(defun sign-extend (value)
  (wrap-carry (twos-complement value nil) t))

;;; setf-able locations

(defun register (reg)
  (disasm-instr reg
    (getf *registers* reg)))

(defun set-reg (reg value)
  (setf (getf *registers* reg) (wrap-carry value t)))

(defsetf register set-reg)

(defun byte-register (reg)
  (disasm-instr reg
    (let* ((register-to-word (getf +byte-register-to-word+ reg)) (word (first register-to-word)))
      (if (second register-to-word)
	  (ash (register word) -8)
	  (logand (register word) #x00ff)))))

(defun set-byte-reg (reg value)
  (let* ((register-to-word (getf +byte-register-to-word+ reg)) (word (first register-to-word)) (wrapped-value (wrap-carry value nil)))
    (if (second register-to-word)
	(setf (register word) (+ (ash wrapped-value 8) (logand (register word) #x00ff)))
	(setf (register word) (+ wrapped-value (logand (register word) #xff00)))))
  value)

(defsetf byte-register set-byte-reg)

(defun flag (name)
  (getf *flags* name))

(defsetf flag (name) (value)
  `(setf (getf *flags* ,name) ,value))

(defun flag-p (name)
  (= (flag name) 1))

(defsetf flag-p (name) (is-set)
  `(setf (flag ,name) (if ,is-set 1 0)))

(defun set-flag (name)
  (setf (flag-p name) t))

(defun clear-flag (name)
  (setf (flag-p name) nil))

(defun bit-vector->integer (bit-vector)
  "Create a positive integer from a bit-vector."
  (reduce #'(lambda (first-bit second-bit)
              (+ (* first-bit 2) second-bit))
          bit-vector))

(defun flags-register (&optional (is-word t))
  (let ((flags (vector 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0)))
    (setf (elt flags (- 15 0)) (flag :cf))
    (setf (elt flags (- 15 2)) (flag :pf))
    (setf (elt flags (- 15 4)) (flag :af))
    (setf (elt flags (- 15 6)) (flag :zf))
    (setf (elt flags (- 15 7)) (flag :sf))
    (when is-word
	(setf (elt flags (- 15 11)) (flag :of)))
    (bit-vector->integer flags)))

(defun set-flags-register (value &optional (is-word t))
  (setf (flag-p :cf) (logbitp 0 value))
  (setf (flag-p :pf) (logbitp 2 value))
  (setf (flag-p :af) (logbitp 4 value))
  (setf (flag-p :zf) (logbitp 6 value))
  (setf (flag-p :sf) (logbitp 7 value))
  (when is-word
      (setf (flag-p :of) (logbitp 11 value)))
  value)

(defsetf flags-register set-flags-register)

(defun byte-in-ram (location segment)
  "Read a byte from a RAM segment."
  (elt segment location))

(defsetf byte-in-ram (location segment) (value)
  "Write a byte to a RAM segment."
  `(setf (elt ,segment ,location) (logand ,value #xff)))

(defun word-in-ram (location segment)
  "Read a word from a RAM segment."
  (reverse-little-endian (elt segment location) (elt segment (1+ location))))

(defsetf word-in-ram (location segment) (value)
  "Write a word to a RAM segment."
  `(progn
     (setf (elt ,segment ,location) (logand ,value #x00ff))
     (setf (elt ,segment (1+ ,location)) (ash (logand ,value #xff00) -8))
     ,value))

(defun indirect-address (mod-bits r/m-bits is-word)
  "Read from an indirect address."
  (disasm-instr
      (if (= mod-bits #b11) (register (if is-word (bits->word-reg r/m-bits) (bits->byte-reg r/m-bits)))
	  (let ((base-index (address-for-r/m mod-bits r/m-bits)))
	    (unless (getf base-index :disp)
	      (setf (getf base-index :disp)
		    (case mod-bits
		      (#b00 0)
		      (#b01 (next-instruction))
		      (#b10 (next-word)))))
	    base-index))
    (let ((address-base (address-for-r/m mod-bits r/m-bits)))
      (case mod-bits
	(#b00 (if is-word (word-in-ram address-base *ram*) (byte-in-ram address-base *ram*)))
	(#b01 (if is-word (word-in-ram (+ address-base (peek-at-instruction)) *ram*) (byte-in-ram (+ address-base (peek-at-instruction)) *ram*)))
	(#b10 (if is-word (word-in-ram (+ address-base (peek-at-word)) *ram*) (byte-in-ram (+ address-base (peek-at-word)) *ram*)))
	(#b11 (if is-word (register (bits->word-reg r/m-bits)) (byte-register (bits->byte-reg r/m-bits))))))))

(defsetf indirect-address (mod-bits r/m-bits is-word) (value)
  "Write to an indirect address."
  `(let ((address-base (address-for-r/m ,mod-bits ,r/m-bits)))
    (case ,mod-bits
      (#b00 (if ,is-word (setf (word-in-ram address-base *ram*) ,value) (setf (byte-in-ram address-base *ram*) ,value)))
      (#b01 (if ,is-word (setf (word-in-ram (+ address-base (peek-at-instruction)) *ram*) ,value) (setf (byte-in-ram (+ address-base (peek-at-instruction)) *ram*) ,value)))
      (#b10 (if ,is-word (setf (word-in-ram (+ address-base (peek-at-word)) *ram*) ,value) (setf (byte-in-ram (+ address-base (peek-at-word)) *ram*) ,value)))
      (#b11 (if ,is-word (setf (register (bits->word-reg ,r/m-bits)) ,value) (setf (byte-register (bits->byte-reg ,r/m-bits)) ,value))))
    ,value))

;;; setf wrappers

(defmacro setf-enhanced (fn place value)
  `(setf ,place (,fn ,place ,value)))

(defmacro logandf (place value)
  `(setf-enhanced logand ,place ,value))

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

(defun peek-at-instruction (&optional (forward 0))
  (incf *advance*)
  (elt *ram* (+ *ip* forward)))

(defun peek-at-word ()
  (reverse-little-endian (peek-at-instruction) (peek-at-instruction 1)))

(defun advance-ip ()
  (incf *ip* *advance*)
  (setf *advance* 0))

(defun advance-ip-ahead-of-indirect-address (mod-bits r/m-bits)
  (cond
    ((or (and (= mod-bits #b00) (= r/m-bits #b110)) (= mod-bits #b10)) 2)
    ((= mod-bits #b01) 1)
    (t 0)))

(defun next-instruction-ahead-of-indirect-address (mod-bits r/m-bits)
  (let ((*ip* *ip*))
    (incf *ip* (advance-ip-ahead-of-indirect-address mod-bits r/m-bits))
    (incf *advance*)
    (next-instruction)))

(defun next-word-ahead-of-indirect-address (mod-bits r/m-bits)
  (let ((*ip* *ip*))
    (incf *ip* (advance-ip-ahead-of-indirect-address mod-bits r/m-bits))
    (incf *advance* 2)
    (next-word)))

;;; Memory access

(defun read-word-from-ram (loc &optional (segment *ram*))
  (word-in-ram loc segment))

(defun write-word-to-ram (loc word &optional (segment *ram*))
  (setf (word-in-ram loc segment) word))

(defmacro push-to-stack (value)
  `(progn
     (decf (register :sp) 2)
     (write-word-to-ram (register :sp) ,value *stack*)))

; (defun push-to-stack (value)
;   (decf (register :sp) 2)
;   (write-word-to-ram (register :sp) value *stack*))

(defun pop-from-stack ()
  (incf (register :sp) 2)
  (read-word-from-ram (- (register :sp) 2) *stack*))

;;; Flag effects

(defun set-af-on-add (result operand1)
  (let ((operand2 (- result operand1)))
    (setf (flag-p :af) (> (+ (logand operand1 #x000f) (logand operand2 #x000f)) #x000f))
    result))

(defun set-af-on-sub (value1 value2)
  (setf (flag-p :af) (> (logand value2 #x000f) (logand value1 #x000f)))
  value1)

(defun set-cf-on-add (value)
  (setf (flag-p :cf) *has-carried*)
  value)

(defun set-cf-on-sub (value1 value2)
  (setf (flag-p :cf) (> value2 value1))
  (- value1 value2))

(defmacro set-of-on-op (result operation)
  `(let* ((value1 (,operation ,result value2)) (neg1 (negative-p value1 is-word)))
     (setf (flag-p :of) (and (eq neg1 (negative-p value2 is-word)) (not (eq neg1 (negative-p ,result is-word)))))
     ,result))

(defun set-of-on-add (sum value2 is-word)
  (set-of-on-op sum -))

(defun set-of-on-sub (diff value2 is-word)
  (set-of-on-op diff +))

(defun set-pf-on-op (value)
  (setf (flag-p :pf) (evenp (logcount (logand #xff value))))
  value)

(defun set-sf-on-op (value is-word)
  (setf (flag-p :sf) (negative-p value is-word))
  value)

(defun set-zf-on-op (value)
  (setf (flag-p :zf) (zerop value))
  value)

;;; Operations

;; Context wrappers

(defun with-one-byte-opcode-register (opcode fn)
  (let ((reg (bits->word-reg (mod opcode #x08))))
    (funcall fn reg)))

(defmacro with-mod-r/m-byte (&body body)
  `(let* ((mod-r/m (next-instruction)) (r/m-bits (logand mod-r/m #b00000111)) (mod-bits (ash (logand mod-r/m #b11000000) -6)) (reg-bits (ash (logand mod-r/m #b00111000) -3)))
     ,@body))

(defmacro with-size-by-last-bit (opcode &body body)
  `(let ((is-word (oddp ,opcode)))
     ,@body))

(defmacro with-in-place-mod (dest mod-bits r/m-bits &body body)
  `(progn
     ,@body
     (when (equal (car ',dest) 'indirect-address)
       (decf *advance* (advance-ip-ahead-of-indirect-address ,mod-bits ,r/m-bits)))))

;; Group handling

(defmacro parse-group-byte-pair (opcode operation mod-bits r/m-bits)
  `(,operation ,mod-bits ,r/m-bits (oddp ,opcode)))

(defmacro parse-group-opcode (&body body)
  `(with-mod-r/m-byte
     (case reg-bits
       ,@body)))

;; Templates

(defmacro mov (src dest)
  `(disasm-instr (list "mov" :src ,src :dest ,dest)
     (setf ,dest ,src)))

(defmacro xchg (op1 op2 &optional mod-bits r/m-bits)
  `(disasm-instr (list "xchg" :op1 ,op1 :op2 ,op2)
     (with-in-place-mod ,op1 ,mod-bits ,r/m-bits
       (with-in-place-mod ,op2 ,mod-bits ,r/m-bits
	 (rotatef ,op1 ,op2)))))

(defmacro push-operation (src)
  `(disasm-instr (list "push" :src ,src)
     (push-to-stack ,src)))

(defmacro pop-operation (dest)
  `(disasm-instr (list "pop" :dest ,dest)
     (setf ,dest (pop-from-stack))))

(defmacro inc (op is-word &optional mod-bits r/m-bits)
  `(disasm-instr (list "inc" :op ,op)
     (with-in-place-mod ,op ,mod-bits ,r/m-bits
       (set-af-on-add (set-of-on-add (set-pf-on-op (set-sf-on-op (set-zf-on-op (incf ,op)) ,is-word)) 1 ,is-word) 1))))

(defmacro dec (op is-word &optional mod-bits r/m-bits)
  `(disasm-instr (list "dec" :op ,op)
     (with-in-place-mod ,op ,mod-bits ,r/m-bits
       (set-af-on-sub (1+ (set-of-on-sub (set-pf-on-op (set-sf-on-op (set-zf-on-op (decf ,op)) ,is-word)) 1 ,is-word)) 1))))

;; Flag operations

(defun clear-carry-flag ()
  (disasm-instr '("clc")
    (setf (flag-p :cf) nil)))

(defun set-carry-flag ()
  (disasm-instr '("stc")
    (setf (flag-p :cf) t)))

(defun clear-direction-flag ()
  (disasm-instr '("cld")
    (setf (flag-p :df) nil)))

(defun set-direction-flag ()
  (disasm-instr '("std")
    (setf (flag-p :df) t)))

;; One-byte opcodes on registers

(defun push-register (reg)
  (push-operation (register reg)))

(defun pop-to-register (reg)
  (pop-operation (register reg)))

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

(defun jmp-near ()
  (disasm-instr (list "jmp" :op (twos-complement (next-word) t))
    (incf *ip* (twos-complement (next-word) t))))

(defun jmp-short ()
  (disasm-instr (list "jmp" :op (twos-complement (next-instruction) nil))
    (incf *ip* (twos-complement (next-instruction) nil))))

(defmacro jmp-short-conditionally (opcode condition mnemonic)
  `(let ((disp (next-instruction)))
     (if (evenp ,opcode)
       (disasm-instr (list (concatenate 'string "j" ,mnemonic) :op (twos-complement disp nil))
	 (when ,condition
	   (incf *ip* (twos-complement disp nil))))
       (disasm-instr (list (concatenate 'string "jn" ,mnemonic) :op (twos-complement disp nil))
	 (unless ,condition
	   (incf *ip* (twos-complement disp nil)))))))

(defun jmp-short-on-cx-zero ()
  (disasm-instr (list "jcxz" :op (twos-complement (next-instruction) nil))
    (if (zerop (register :cx))
	(incf *ip* (twos-complement (next-instruction) nil)))))

(defun call-near ()
  (disasm-instr (list "call" :op (twos-complement (next-word) t))
    (push-to-stack (+ *ip* 2))
    (incf *ip* (twos-complement (next-word) t))))

(defun ret-near ()
  (disasm-instr '("retn")
    (setf *ip* (pop-from-stack))))

(defun ret-near-resetting-stack ()
  (disasm-instr (list "retn" :op (next-word))
    (ret-near)
    (incf (register :sp) (next-word))))

;; ALU

(defmacro parse-alu-opcode (opcode operation)
  `(let ((mod-8 (mod ,opcode 8)))
     (case mod-8
       (0
	(with-mod-r/m-byte
	  (,operation (byte-register (bits->byte-reg reg-bits)) (indirect-address mod-bits r/m-bits nil) nil mod-bits r/m-bits)))
       (1
	(with-mod-r/m-byte
	  (,operation (register (bits->word-reg reg-bits)) (indirect-address mod-bits r/m-bits t) t mod-bits r/m-bits)))
       (2
	(with-mod-r/m-byte
	  (,operation (indirect-address mod-bits r/m-bits nil) (byte-register (bits->byte-reg reg-bits)) nil)))
       (3
	(with-mod-r/m-byte
	  (,operation (indirect-address mod-bits r/m-bits t) (register (bits->word-reg reg-bits)) t)))
       (4
	(,operation (next-instruction) (byte-register :al) nil))
       (5
	(,operation (next-word) (register :ax) t)))))

(defmacro add-without-carry (src dest is-word &optional mod-bits r/m-bits)
  `(disasm-instr (list "add" :src ,src :dest ,dest)
     (with-in-place-mod ,dest ,mod-bits ,r/m-bits
       (let ((src-value ,src))
	 (set-zf-on-op (set-sf-on-op (set-pf-on-op (set-of-on-add (set-cf-on-add (set-af-on-add (incf ,dest src-value) src-value)) src-value ,is-word)) ,is-word))))))

(defmacro add-with-carry (src dest is-word &optional mod-bits r/m-bits)
  `(disasm-instr (list "adc" :src ,src :dest ,dest)
     (with-in-place-mod ,dest ,mod-bits ,r/m-bits
       (let ((src-plus-cf (+ ,src (flag :cf))))
	 (set-zf-on-op (set-sf-on-op (set-pf-on-op (set-of-on-add (set-cf-on-add (set-af-on-add (incf ,dest src-plus-cf) src-plus-cf)) src-plus-cf ,is-word)) ,is-word))))))

(defmacro sub-without-borrow (src dest is-word &optional mod-bits r/m-bits)
  `(disasm-instr (list "sub" :src ,src :dest ,dest)
     (with-in-place-mod ,dest ,mod-bits ,r/m-bits
       (let ((src-value ,src))
	 (set-zf-on-op (set-sf-on-op (set-pf-on-op (set-of-on-sub (set-cf-on-sub (set-af-on-sub (+ (decf ,dest src-value) src-value) src-value) src-value) src-value ,is-word)) ,is-word))))))

(defmacro sub-with-borrow (src dest is-word &optional mod-bits r/m-bits)
  `(disasm-instr (list "sbb" :src ,src :dest ,dest)
     (with-in-place-mod ,dest ,mod-bits ,r/m-bits
       (let ((src-plus-cf (+ ,src (flag :cf))))
	 (set-zf-on-op (set-sf-on-op (set-pf-on-op (set-of-on-sub (set-cf-on-sub (set-af-on-sub (+ (decf ,dest src-plus-cf) src-plus-cf) src-plus-cf) src-plus-cf) src-plus-cf ,is-word)) ,is-word))))))

(defmacro cmp-operation (src dest is-word &optional mod-bits r/m-bits)
  `(disasm-instr (list "cmp" :src ,src :dest ,dest)
     (let ((src-value ,src))
       (set-zf-on-op (set-sf-on-op (set-pf-on-op (set-of-on-sub (set-cf-on-sub (set-af-on-sub ,dest src-value) src-value) src-value ,is-word)) ,is-word)))))

(defmacro and-operation (src dest is-word &optional mod-bits r/m-bits)
  `(disasm-instr (list "and" :src ,src :dest ,dest)
     (with-in-place-mod ,dest ,mod-bits ,r/m-bits
       (set-zf-on-op (set-sf-on-op (set-pf-on-op (setf ,dest (logand ,src ,dest))) ,is-word))
       (clear-flag :cf)
       (clear-flag :of))))

(defmacro or-operation (src dest is-word &optional mod-bits r/m-bits)
  `(disasm-instr (list "or" :src ,src :dest ,dest)
     (with-in-place-mod ,dest ,mod-bits ,r/m-bits
       (set-zf-on-op (set-sf-on-op (set-pf-on-op (setf ,dest (logior ,src ,dest))) ,is-word))
       (clear-flag :cf)
       (clear-flag :of))))

(defmacro xor-operation (src dest is-word &optional mod-bits r/m-bits)
  `(disasm-instr (list "xor" :src ,src :dest ,dest)
     (with-in-place-mod ,dest ,mod-bits ,r/m-bits
       (set-zf-on-op (set-sf-on-op (set-pf-on-op (setf ,dest (logxor ,src ,dest))) ,is-word))
       (clear-flag :cf)
       (clear-flag :of))))

(defmacro parse-group1-byte (opcode operation mod-bits r/m-bits)
  `(case (mod ,opcode 4)
    ((0 2) (,operation (next-instruction-ahead-of-indirect-address ,mod-bits ,r/m-bits) (indirect-address ,mod-bits ,r/m-bits nil) nil mod-bits r/m-bits))
    (1 (,operation (next-word-ahead-of-indirect-address ,mod-bits ,r/m-bits) (indirect-address ,mod-bits ,r/m-bits t) t mod-bits r/m-bits))
    (3 (,operation (sign-extend (next-instruction-ahead-of-indirect-address ,mod-bits ,r/m-bits)) (indirect-address ,mod-bits ,r/m-bits t) t mod-bits r/m-bits))))

(defun parse-group1-opcode (opcode)
  (parse-group-opcode
    (0 (parse-group1-byte opcode add-without-carry mod-bits r/m-bits))
    (1 (parse-group1-byte opcode or-operation mod-bits r/m-bits))
    (2 (parse-group1-byte opcode add-with-carry mod-bits r/m-bits))
    (3 (parse-group1-byte opcode sub-with-borrow mod-bits r/m-bits))
    (4 (parse-group1-byte opcode and-operation mod-bits r/m-bits))
    (5 (parse-group1-byte opcode sub-without-borrow mod-bits r/m-bits))
    (6 (parse-group1-byte opcode xor-operation mod-bits r/m-bits))
    (7 (parse-group1-byte opcode cmp-operation mod-bits r/m-bits))))

;; test

(defmacro test-operation (op1 op2 is-word)
  `(disasm-instr (list "test" :op1 ,op1 :op2 ,op2)
     (set-zf-on-op (set-sf-on-op (set-pf-on-op (logand ,op1 ,op2)) ,is-word))
     (clear-flag :cf)
     (clear-flag :of)))

(defun test-accumulator-with-immediate (opcode)
  (with-size-by-last-bit opcode
    (if is-word
      (test-operation (register :ax) (next-word) t)
      (test-operation (byte-register :al) (next-instruction) nil))))

(defun test-memory-register (opcode)
  (with-mod-r/m-byte
    (with-size-by-last-bit opcode
      (if is-word
	  (test-operation (register (bits->word-reg reg-bits)) (indirect-address mod-bits r/m-bits t) t)
	  (test-operation (byte-register (bits->byte-reg reg-bits)) (indirect-address mod-bits r/m-bits nil) nil)))))

(defun test-indirect-with-immediate (mod-bits r/m-bits is-word)
  (if is-word
      (test-operation (next-word-ahead-of-indirect-address mod-bits r/m-bits) (indirect-address mod-bits r/m-bits t) t)
      (test-operation (next-instruction-ahead-of-indirect-address mod-bits r/m-bits) (indirect-address mod-bits r/m-bits nil) nil)))

;; Memory and register mov/xchg

(defun xchg-memory-register (opcode)
  (with-mod-r/m-byte
    (with-size-by-last-bit opcode
      (if is-word
	  (xchg (register (bits->word-reg reg-bits)) (indirect-address mod-bits r/m-bits is-word) mod-bits r/m-bits)
	  (xchg (byte-register (bits->byte-reg reg-bits)) (indirect-address mod-bits r/m-bits is-word) mod-bits r/m-bits)))))

(defun mov-immediate-to-memory (mod-bits r/m-bits is-word)
  (if is-word
      (mov (next-word-ahead-of-indirect-address mod-bits r/m-bits) (indirect-address mod-bits r/m-bits t))
      (mov (next-instruction-ahead-of-indirect-address mod-bits r/m-bits) (indirect-address mod-bits r/m-bits nil))))

(defun parse-group11-opcode (opcode)
  (parse-group-opcode
    (0 (parse-group-byte-pair opcode mov-immediate-to-memory mod-bits r/m-bits))))

(defun parse-mov-opcode (opcode)
  (let ((mod-4 (mod opcode 4)))
    (with-mod-r/m-byte
      (case mod-4
	(0
	 (mov (byte-register (bits->byte-reg reg-bits)) (indirect-address mod-bits r/m-bits nil)))
	(1
	 (mov (register (bits->word-reg reg-bits)) (indirect-address mod-bits r/m-bits t)))
	(2
	 (mov (indirect-address mod-bits r/m-bits nil) (byte-register (bits->byte-reg reg-bits))))
	(3
	 (mov (indirect-address mod-bits r/m-bits t) (register (bits->word-reg reg-bits))))))))

(defun mov-offset-to-accumulator (opcode)
  (with-size-by-last-bit opcode
    (if is-word
	(mov (word-in-ram (next-word) *ram*) (register :ax))
	(mov (byte-in-ram (next-word) *ram*) (byte-register :al)))))

(defun mov-accumulator-to-offset (opcode)
  (with-size-by-last-bit opcode
    (if is-word
	(mov (register :ax) (word-in-ram (next-word) *ram*))
	(mov (byte-register :al) (byte-in-ram (next-word) *ram*)))))

;; Groups 1A, 4, and 5 (inc/dec, call/jmp, and push/pop on EAs)

(defun inc-indirect (mod-bits r/m-bits is-word)
  (inc (indirect-address mod-bits r/m-bits is-word) is-word))

(defun dec-indirect (mod-bits r/m-bits is-word)
  (dec (indirect-address mod-bits r/m-bits is-word) is-word))

(defun push-indirect (mod-bits r/m-bits)
  (push-operation (indirect-address mod-bits r/m-bits t)))

(defun pop-indirect (mod-bits r/m-bits)
  (pop-operation (indirect-address mod-bits r/m-bits t)))

(defun call-near-indirect (mod-bits r/m-bits)
  (let ((target (indirect-address mod-bits r/m-bits t)))
    (disasm-instr (list "call" :op target)
      (push-to-stack *ip*)
      (setf *ip* target))))

(defun jmp-near-indirect (mod-bits r/m-bits)
  (disasm-instr (list "jmp" :op (indirect-address mod-bits r/m-bits t))
    (setf *ip* (indirect-address mod-bits r/m-bits t))))

(defun parse-group1a-opcode ()
  "Group 1A (0x8F)"
  (parse-group-opcode
    (0 (pop-indirect mod-bits r/m-bits))))

(defun parse-group4-opcode ()
  "Group 4 (0xFE)"
  (parse-group-opcode
    (0 (inc-indirect mod-bits r/m-bits nil))
    (1 (dec-indirect mod-bits r/m-bits nil))))

(defun parse-group5-opcode ()
  "Group 5 (0xFF)"
  (parse-group-opcode
    (0 (inc-indirect mod-bits r/m-bits t))
    (1 (dec-indirect mod-bits r/m-bits t))
    (2 (call-near-indirect mod-bits r/m-bits))
    (4 (jmp-near-indirect mod-bits r/m-bits))
    (6 (push-indirect mod-bits r/m-bits))))

;; Group 3 (arithmetic and logical operations)

(defmacro not-operation (op mod-bits r/m-bits)
  `(disasm-instr (list "not" :op ,op)
     (with-in-place-mod ,op ,mod-bits ,r/m-bits
       (setf ,op (lognot ,op)))))

(defun not-indirect (mod-bits r/m-bits is-word)
  (not-operation (indirect-address mod-bits r/m-bits is-word) mod-bits r/m-bits))

(defmacro neg-operation (op mod-bits r/m-bits is-word)
  `(disasm-instr (list "neg" :op ,op)
     (with-in-place-mod ,op ,mod-bits ,r/m-bits
       (let ((src-value ,op))
	 (setf ,op (- src-value))
	 (set-zf-on-op (set-sf-on-op (set-pf-on-op (set-of-on-sub (set-cf-on-sub (set-af-on-sub 0 src-value) src-value) src-value ,is-word)) ,is-word))))))

(defun neg-indirect (mod-bits r/m-bits is-word)
  (neg-operation (indirect-address mod-bits r/m-bits is-word) mod-bits r/m-bits is-word))

(defun parse-group3-opcode (opcode)
  (parse-group-opcode
    (0 (parse-group-byte-pair opcode test-indirect-with-immediate mod-bits r/m-bits))
    (2 (parse-group-byte-pair opcode not-indirect mod-bits r/m-bits))
    (3 (parse-group-byte-pair opcode neg-indirect mod-bits r/m-bits))))

;; FLAGS processing

(defun push-flags ()
  (disasm-instr '("pushf")
    (push-to-stack (flags-register))))

(defun pop-flags ()
  (disasm-instr '("popf")
    (setf (flags-register) (pop-from-stack))))

(defun store-flags-to-ah ()
  (disasm-instr '("sahf")
    (setf (byte-register :ah) (flags-register nil))))

(defun load-flags-from-ah ()
  (disasm-instr '("lahf")
    (setf (flags-register nil) (byte-register :ah))))

;; Memory addressing

(defun load-effective-address ()
  "Load an effective address."
  (with-mod-r/m-byte
    (disasm-instr
	(list "lea"
	:src (let ((base-index (address-for-r/m mod-bits r/m-bits)))
	  (unless (getf base-index :disp)
	    (setf (getf base-index :disp)
		  (case mod-bits
		    (#b00 0)
		    (#b01 (next-instruction))
		    (#b10 (next-word)))))
	  base-index)
	:dest (register (bits->word-reg reg-bits)))
      (let ((address-base (address-for-r/m mod-bits r/m-bits)))
	(setf (register (bits->word-reg reg-bits))
	      (case mod-bits
		(#b00 address-base)
		(#b01 (+ address-base (next-instruction)))
		(#b10 (+ address-base (next-word)))))))))

;; Binary-coded decimal

(defmacro ascii-adjust-after-add-or-sub (modifier)
  `(let ((adjusted (or (> (logand (byte-register :al) #x0f) 9) (flag-p :af))))
     (when adjusted
       (,modifier (register :ax) #x106))
     (setf (flag-p :af) adjusted)
     (setf (flag-p :cf) adjusted)
     (logandf (byte-register :al) #x0f)))

(defmacro decimal-adjust-after-add-or-sub (modifier)
  `(let ((old-al (byte-register :al)) (old-cf (flag-p :cf)))
     (when (or (> (logand (byte-register :al) #x0f) 9) (flag-p :af))
       (,modifier (byte-register :al) 6)
       (setf (flag-p :cf) (or old-cf *has-carried*))
       (set-flag :af))
     (when (or (> old-al #x99) old-cf)
       (,modifier (byte-register :al) #x60)
       (set-flag :cf))
     (set-zf-on-op (set-sf-on-op (set-pf-on-op (byte-register :al)) nil))))

(defun ascii-adjust-after-addition ()
  (disasm-instr '("aaa")
    (ascii-adjust-after-add-or-sub incf)))

(defun ascii-adjust-after-subtraction ()
  (disasm-instr '("aas")
    (ascii-adjust-after-add-or-sub decf)))

(defun decimal-adjust-after-addition ()
  (disasm-instr '("daa")
    (decimal-adjust-after-add-or-sub incf)))

(defun decimal-adjust-after-subtraction ()
  (disasm-instr '("das")
    (decimal-adjust-after-add-or-sub decf)))

;; Sign-extension operations

(defun convert-byte-to-word ()
  (disasm-instr '("cbw")
    (setf (register :ax) (sign-extend (byte-register :al)))))

(defun convert-word-to-double ()
  (disasm-instr '("cwd")
    (setf (register :dx) (if (negative-p (register :ax) t) #xff #x00))))

;; String operations

(defun repeat-prefix (opcode)
  (let* ((end-on-zf? (evenp opcode)) (operation-full (parse-string-opcode (next-instruction))) (operation (first operation-full)) (check-zf? (second operation-full)))
    (disasm-instr (append (funcall operation opcode) (list :prefix (if check-zf? (if end-on-zf? "repnz" "repz") "rep")))
      (if (not operation) (return-from repeat-prefix))
      (loop
	 do (funcall operation opcode)
	 until (or (= (register :cx) 0) (and check-zf? (eq (flag-p :zf) end-on-zf?)))
	 do (decf (register :cx))))))

(defmacro string-operation (opcode operation)
  `(with-size-by-last-bit ,opcode
     (let ((diff (if is-word 2 1)))
       (,operation is-word)
       (when (flag-p :df)
	 (decf (register :si) diff)
	 (decf (register :di) diff))
       (unless (flag-p :df)
	 (incf (register :si) diff)
	 (incf (register :di) diff)))))

(defmacro mov-string-operation (is-word)
  `(disasm-instr '("movs")
     (if ,is-word
	 (mov (word-in-ram (register :si) *ram*) (word-in-ram (register :di) *ram*))
	 (mov (byte-in-ram (register :si) *ram*) (byte-in-ram (register :di) *ram*)))))

(defun mov-string (opcode)
  (string-operation opcode mov-string-operation))

(defmacro load-string-operation (is-word)
  `(disasm-instr '("lods")
     (if ,is-word
	 (setf (register :ax) (word-in-ram (register :si) *ram*))
	 (setf (byte-register :al) (byte-in-ram (register :si) *ram*)))))

(defun load-string (opcode)
  (string-operation opcode load-string-operation))

(defmacro store-string-operation (is-word)
  `(disasm-instr '("stos")
     (if ,is-word
	 (setf (word-in-ram (register :di) *ram*) (register :ax))
	 (setf (byte-in-ram (register :di) *ram*) (byte-register :al)))))

(defun store-string (opcode)
  (string-operation opcode store-string-operation))

(defmacro compare-string-operation (is-word)
  `(disasm-instr '("cmps")
     (if ,is-word
	 (cmp-operation (word-in-ram (register :si) *ram*) (word-in-ram (register :di) *ram*) t)
	 (cmp-operation (byte-in-ram (register :si) *ram*) (byte-in-ram (register :di) *ram*) nil))))

(defun compare-string (opcode)
  (string-operation opcode compare-string-operation))

(defmacro scan-string-operation (is-word)
  `(disasm-instr '("scas")
     (if ,is-word
	 (cmp-operation (register :ax) (word-in-ram (register :di) *ram*) t)
	 (cmp-operation (byte-register :al) (byte-in-ram (register :di) *ram*) nil))))

(defun scan-string (opcode)
  (string-operation opcode scan-string-operation))

(defun parse-string-opcode (opcode)
  (cond
    ((in-paired-byte-block-p opcode #xa4) (list #'mov-string nil))
    ((in-paired-byte-block-p opcode #xaa) (list #'store-string nil))
    ((in-paired-byte-block-p opcode #xac) (list #'load-string nil))
    ((in-paired-byte-block-p opcode #xa6) (list #'compare-string t))
    ((in-paired-byte-block-p opcode #xae) (list #'scan-string t))
    (t '(nil nil))))

;;; Opcode parsing

(defmacro in-x-byte-block-p (size)
  `(= (truncate (/ opcode ,size)) (/ block ,size)))

(defun in-paired-byte-block-p (opcode block)
  (in-x-byte-block-p 2))

(defun in-4-byte-block-p (opcode block)
  (in-x-byte-block-p 4))

(defun in-8-byte-block-p (opcode block)
  (in-x-byte-block-p 8))

(defun in-6-byte-block-p (opcode block)
  (and (in-8-byte-block-p opcode block) (< (mod opcode 8) 6)))

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
    ((= opcode #xfc) (clear-direction-flag))
    ((= opcode #xfd) (set-direction-flag))
    ((= opcode #xe9) (jmp-near))
    ((= opcode #xeb) (jmp-short))
    ((in-paired-byte-block-p opcode #x70) (jmp-short-conditionally opcode (flag-p :of) "o"))
    ((in-paired-byte-block-p opcode #x72) (jmp-short-conditionally opcode (flag-p :cf) "b"))
    ((in-paired-byte-block-p opcode #x74) (jmp-short-conditionally opcode (flag-p :zf) "z"))
    ((in-paired-byte-block-p opcode #x76) (jmp-short-conditionally opcode (or (flag-p :cf) (flag-p :zf)) "be"))
    ((in-paired-byte-block-p opcode #x78) (jmp-short-conditionally opcode (flag-p :sf) "s"))
    ((in-paired-byte-block-p opcode #x7a) (jmp-short-conditionally opcode (flag-p :pf) "p"))
    ((in-paired-byte-block-p opcode #x7c) (jmp-short-conditionally opcode (not (eq (flag-p :of) (flag-p :sf))) "l"))
    ((in-paired-byte-block-p opcode #x7e) (jmp-short-conditionally opcode (or (flag-p :zf) (not (eq (flag-p :of) (flag-p :sf)))) "le"))
    ((= opcode #xe3) (jmp-short-on-cx-zero))
    ((= opcode #xe8) (call-near))
    ((= opcode #xc2) (ret-near-resetting-stack))
    ((= opcode #xc3) (ret-near))
    ((in-6-byte-block-p opcode #x00) (parse-alu-opcode opcode add-without-carry))
    ((in-6-byte-block-p opcode #x08) (parse-alu-opcode opcode or-operation))
    ((in-6-byte-block-p opcode #x10) (parse-alu-opcode opcode add-with-carry))
    ((in-6-byte-block-p opcode #x18) (parse-alu-opcode opcode sub-with-borrow))
    ((in-6-byte-block-p opcode #x20) (parse-alu-opcode opcode and-operation))
    ((in-6-byte-block-p opcode #x28) (parse-alu-opcode opcode sub-without-borrow))
    ((in-6-byte-block-p opcode #x30) (parse-alu-opcode opcode xor-operation))
    ((in-6-byte-block-p opcode #x38) (parse-alu-opcode opcode cmp-operation))
    ((in-4-byte-block-p opcode #x80) (parse-group1-opcode opcode))
    ((in-paired-byte-block-p opcode #xa8) (test-accumulator-with-immediate opcode))
    ((in-paired-byte-block-p opcode #x84) (test-memory-register opcode))
    ((in-4-byte-block-p opcode #x88) (parse-mov-opcode opcode))
    ((in-paired-byte-block-p opcode #x86) (xchg-memory-register opcode))
    ((in-paired-byte-block-p opcode #xc6) (parse-group11-opcode opcode))
    ((in-paired-byte-block-p opcode #xa0) (mov-offset-to-accumulator opcode))
    ((in-paired-byte-block-p opcode #xa2) (mov-accumulator-to-offset opcode))
    ((= opcode #x8f) (parse-group1a-opcode))
    ((= opcode #xfe) (parse-group4-opcode))
    ((= opcode #xff) (parse-group5-opcode))
    ((in-paired-byte-block-p opcode #xf6) (parse-group3-opcode opcode))
    ((= opcode #x9c) (push-flags))
    ((= opcode #x9d) (pop-flags))
    ((= opcode #x9e) (store-flags-to-ah))
    ((= opcode #x9f) (load-flags-from-ah))
    ((= opcode #x8d) (load-effective-address))
    ((= opcode #x27) (decimal-adjust-after-addition))
    ((= opcode #x2f) (decimal-adjust-after-subtraction))
    ((= opcode #x37) (ascii-adjust-after-addition))
    ((= opcode #x3f) (ascii-adjust-after-subtraction))
    ((= opcode #x98) (convert-byte-to-word))
    ((= opcode #x99) (convert-word-to-double))
    ((in-paired-byte-block-p opcode #xf2) (repeat-prefix opcode))
    ((in-paired-byte-block-p opcode #xa4) (mov-string opcode))
    ((in-paired-byte-block-p opcode #xaa) (store-string opcode))
    ((in-paired-byte-block-p opcode #xac) (load-string opcode))
    ((in-paired-byte-block-p opcode #xa6) (compare-string opcode))
    ((in-paired-byte-block-p opcode #xae) (scan-string opcode))))

;;; Main functions

(defun execute-instructions ()
  "Loop through loaded instructions."
  (loop
     for ret = (parse-opcode (next-instruction))
     until (equal ret '("hlt"))
     do (advance-ip)
     finally (return t)))

(defun disasm-instructions (instr-length)
  "Disassemble code."
  (loop
     for ret = (parse-opcode (next-instruction))
     collecting ret into disasm
     until (>= *ip* instr-length)
     do (advance-ip)
     finally (return disasm)))

(defun loop-instructions (instr-length)
  (if *disasm*
      (disasm-instructions instr-length)
      (execute-instructions)))

(defun load-instructions-from-file (file)
  (with-open-file (in file :element-type '(unsigned-byte 8))
    (let ((instrs (make-array (file-length in) :element-type '(unsigned-byte 8) :initial-element 0 :adjustable t)))
      (read-sequence instrs in)
      instrs)))

(defun load-instructions (&key (file nil) (example #()))
  (if file
      (load-instructions-from-file file)
      example))

(defun print-video-ram (&key (width 80) (height 25) (stream t) (newline nil))
  (dotimes (line height)
    (dotimes (column width)
      (let ((char-at-cell (byte-in-ram (+ #x8000 (* line 80) column) *ram*)))
	(if (zerop char-at-cell)
	    (format stream "~a" #\Space)
	    (format stream "~a" (code-char char-at-cell)))))
    (if newline (format stream "~%"))))

(defun disasm (&key (file nil) (example #()))
  (setf *disasm* t)
  (loop-instructions (load-instructions-into-ram (load-instructions :file file :example example))))

(defun main (&key (file nil) (example #()) (display nil) (stream t) (newline nil))
  (setf *disasm* nil)
  (loop-instructions (load-instructions-into-ram (load-instructions :file file :example example)))
  (when display
    (print-video-ram :stream stream :newline newline)))
