;;;; Intel 8086 emulator (CPU)

;;; Convenience functions

(defmacro xor (op1 op2)
  "Apply an XOR operation to two booleans."
  `(not (eq ,op1 ,op2)))

;; Taken from http://www.lispforum.com/viewtopic.php?f=2&t=1205#p6269; not necessarily under same license as my code.

(defun bit-vector->integer (bit-vector)
  "Create a positive integer from a bit-vector."
  (reduce #'(lambda (first-bit second-bit)
              (+ (* first-bit 2) second-bit))
          bit-vector))

;;; Program settings

(defparameter *disasm* nil "Whether to disassemble")

(defmacro disasm-instr (on-disasm &body body)
  "Switch between disassembly and actual operation."
  `(if *disasm*
       ,on-disasm
       (progn ,@body)))

;;; State variables

(defparameter *flags* '(:af 0 :cf 0 :df 0 :if 0 :of 0 :pf 0 :sf 0 :tf 0 :zf 0) "Flags")
(defparameter *registers* '(:ax 0 :bx 0 :cx 0 :dx 0 :bp 0 :sp #x100 :si 0 :di 0) "Registers")
(defparameter *segments* '(:cs 0 :ds 0 :es 0 :ss 0) "Segments")
(defparameter *ip* 0 "Instruction pointer")
(defparameter *has-carried* nil "Whether the last wraparound changed the value")
(defparameter *advance* 0 "Bytes to advance IP by after an operation")

(defparameter *default-segment* nil "A default segment for an instruction")
(defparameter *current-segment* nil "The current override segment")

;;; Constants

(defconstant +byte-register-to-word+ '(:al (:ax nil) :ah (:ax t) :bl (:bx nil) :bh (:bx t) :cl (:cx nil) :ch (:cx t) :dl (:dx nil) :dh (:dx t)) "Mapping from byte registers to word registers")
(defconstant +bits-to-register+ '(:ax :cx :dx :bx :sp :bp :si :di) "Mapping from index to word register")
(defconstant +bits-to-byte-register+ '(:al :cl :dl :bl :ah :ch :dh :bh) "Mapping from index to byte register")
(defconstant +bits-to-segment+ '(:es :cs :ss :ds) "Mapping from index to segment register")

;;; Constant mappings

(defun bits->word-reg (bits)
  "Map a bit pattern to a word register."
  (elt +bits-to-register+ bits))

(defun bits->byte-reg (bits)
  "Map a bit pattern to a byte register."
  (elt +bits-to-byte-register+ bits))

(defun bits->segment (bits)
  "Map a bit pattern to a segment register."
  (elt +bits-to-segment+ bits))

(defmacro default-seg-to (default &optional (current *current-segment*))
  "Set a default segment if no override is given."
  `(if (null ,current) ,default ,current))

(defun address-for-r/m (mod-bits r/m-bits)
  "Determine the registers needed to calculate an indirect address."
  (disasm-instr
      (if (and (= mod-bits #b00) (= r/m-bits #b110))
	  (list :disp (peek-at-word) :segment (default-seg-to :ds))
	  (case r/m-bits
	    (#b000 (list :segment (default-seg-to :ds) :base :bx :index :si))
	    (#b001 (list :segment (default-seg-to :ds) :base :bx :index :di))
	    (#b010 (list :segment (default-seg-to :ss) :base :bp :index :si))
	    (#b011 (list :segment (default-seg-to :ss) :base :bp :index :di))
	    (#b100 (list :segment (default-seg-to :ds) :index :si))
	    (#b101 (list :segment (default-seg-to :ds) :index :di))
	    (#b110 (list :segment (default-seg-to :ss) :base :bp))
	    (#b111 (list :segment (default-seg-to :ds) :base :bx))))
    (if (and (= mod-bits #b00) (= r/m-bits #b110))
	(values (peek-at-word) (default-seg-to :ds))
	(case r/m-bits
	  (#b000 (values (+ (register :bx) (register :si)) (default-seg-to :ds)))
	  (#b001 (values (+ (register :bx) (register :di)) (default-seg-to :ds)))
	  (#b010 (values (+ (register :bp) (register :si)) (default-seg-to :ss)))
	  (#b011 (values (+ (register :bp) (register :di)) (default-seg-to :ss)))
	  (#b100 (values (register :si) (default-seg-to :ds)))
	  (#b101 (values (register :di) (default-seg-to :ds)))
	  (#b110 (values (register :bp) (default-seg-to :ss)))
	  (#b111 (values (register :bx) (default-seg-to :ds)))))))

;;; Convenience functions

(defun negative-p (value is-word)
  "Determine whether a number is negative (has its sign bit set)."
  (let ((sign-and (if is-word #x8000 #x80)))
    (= (logand sign-and value) sign-and)))

(defun twos-complement (value is-word)
  "Calculate the value of a number using two's complement."
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
  "Return a signed byte sign-extended to a word."
  (wrap-carry (twos-complement value nil) t))

(defun segment-calc (seg offset)
  "Calculate an absolute address using a segment:offset pair."
  (logand (+ (ash seg 4) offset) #xfffff))

(defun current-ip ()
  "Calculate the current instruction pointer value with the CS segment."
  (disasm-instr (segment-calc 0 *ip*)
    (segment-calc (segment :cs) *ip*)))

;;; setf-able locations

;; Registers

(defun register (reg)
  "Read from a word register."
  (disasm-instr reg
    (getf *registers* reg)))

(defsetf register (reg) (value)
  "Write to a word register."
  `(setf (getf *registers* ,reg) (wrap-carry ,value t)))

(defun byte-register (reg)
  "Read from a byte register."
  (disasm-instr reg
    (let* ((register-to-word (getf +byte-register-to-word+ reg)) (word (first register-to-word)))
      (if (second register-to-word)
	  (ash (register word) -8)
	  (logand (register word) #x00ff)))))

(defsetf byte-register (reg) (value)
  "Write to a byte register."
  `(let* ((register-to-word (getf +byte-register-to-word+ ,reg)) (word (first register-to-word)) (wrapped-value (wrap-carry ,value nil)))
     (if (second register-to-word)
	 (setf (register word) (+ (ash wrapped-value 8) (logand (register word) #x00ff)))
	 (setf (register word) (+ wrapped-value (logand (register word) #xff00))))
     ,value))

(defun segment (seg)
  "Read from a segment register."
  (disasm-instr seg
    (getf *segments* seg)))

(defsetf segment (seg) (value)
  "Write to a segment register."
  `(setf (getf *segments* ,seg) (logand ,value #xffff)))

;; Flags

(defun flag (name)
  "Read a flag value."
  (getf *flags* name))

(defsetf flag (name) (value)
  "Set a flag value."
  `(setf (getf *flags* ,name) ,value))

(defun flag-p (name)
  "Read whether a flag is set."
  (= (flag name) 1))

(defsetf flag-p (name) (is-set)
  "Write whether a flag is set."
  `(setf (flag ,name) (if ,is-set 1 0)))

(defun set-flag (name)
  "Set a flag (to 1)."
  (setf (flag-p name) t))

(defun clear-flag (name)
  "Clear a flag."
  (setf (flag-p name) nil))

(defun flags-register (&optional (is-word t))
  "Read the flags as the FLAGS register."
  (let ((flags (vector 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0)))
    (setf (elt flags (- 15 0)) (flag :cf))
    (setf (elt flags (- 15 2)) (flag :pf))
    (setf (elt flags (- 15 4)) (flag :af))
    (setf (elt flags (- 15 6)) (flag :zf))
    (setf (elt flags (- 15 7)) (flag :sf))
    (when is-word
      (setf (elt flags (- 15 8)) (flag :tf))
      (setf (elt flags (- 15 9)) (flag :if))
      (setf (elt flags (- 15 10)) (flag :df))
      (setf (elt flags (- 15 11)) (flag :of)))
    (bit-vector->integer flags)))

(defsetf flags-register (&optional (is-word t)) (value)
  "Write the flags as the FLAGS register."
  `(progn
     (setf (flag-p :cf) (logbitp 0 ,value))
     (setf (flag-p :pf) (logbitp 2 ,value))
     (setf (flag-p :af) (logbitp 4 ,value))
     (setf (flag-p :zf) (logbitp 6 ,value))
     (setf (flag-p :sf) (logbitp 7 ,value))
     (when ,is-word
       (setf (flag-p :tf) (logbitp 8 ,value))
       (setf (flag-p :if) (logbitp 9 ,value))
       (setf (flag-p :df) (logbitp 10 ,value))
       (setf (flag-p :of) (logbitp 11 ,value)))
     ,value))

;; RAM

(defun segmented-byte-in-ram (seg offset)
  "Read a byte from RAM using a segment:offset pair."
  (let ((real-seg (default-seg-to *default-segment* seg)))
    (byte-in-ram (segment-calc (segment real-seg) offset))))

(defsetf segmented-byte-in-ram (seg offset) (value)
  "Write a byte to RAM using a segment:offset pair."
  `(let ((real-seg (default-seg-to *default-segment* ,seg)))
     (setf (byte-in-ram (segment-calc (segment real-seg) ,offset)) ,value)))

(defun segmented-word-in-ram (seg offset)
  "Read a word from RAM using a segment:offset pair."
  (let ((real-seg (default-seg-to *default-segment* seg)))
    (word-in-ram (segment-calc (segment real-seg) offset))))

(defsetf segmented-word-in-ram (seg offset) (value)
  "Write a word to RAM using a segment:offset pair."
  `(let ((real-seg (default-seg-to *default-segment* ,seg)))
     (setf (word-in-ram (segment-calc (segment real-seg) ,offset)) ,value)))

(defun indirect-address (mod-bits r/m-bits is-word)
  "Read from RAM or a register using an indirect address."
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
    (multiple-value-bind (address-base seg) (address-for-r/m mod-bits r/m-bits)
      (case mod-bits
	(#b00 (if is-word (segmented-word-in-ram seg address-base) (segmented-byte-in-ram seg address-base)))
	(#b01 (if is-word (segmented-word-in-ram seg (+ address-base (peek-at-instruction))) (segmented-byte-in-ram seg (+ address-base (peek-at-instruction)))))
	(#b10 (if is-word (segmented-word-in-ram seg (+ address-base (peek-at-word))) (segmented-byte-in-ram seg (+ address-base (peek-at-word)))))
	(#b11 (if is-word (register (bits->word-reg r/m-bits)) (byte-register (bits->byte-reg r/m-bits))))))))

(defsetf indirect-address (mod-bits r/m-bits is-word) (value)
  "Write to RAM or a register using an indirect address."
  `(multiple-value-bind (address-base seg) (address-for-r/m ,mod-bits ,r/m-bits)
    (case ,mod-bits
      (#b00 (if ,is-word (setf (segmented-word-in-ram seg address-base) ,value) (setf (segmented-byte-in-ram seg address-base) ,value)))
      (#b01 (if ,is-word (setf (segmented-word-in-ram seg (+ address-base (peek-at-instruction))) ,value) (setf (segmented-byte-in-ram seg (+ address-base (peek-at-instruction))) ,value)))
      (#b10 (if ,is-word (setf (segmented-word-in-ram seg (+ address-base (peek-at-word))) ,value) (setf (segmented-byte-in-ram seg (+ address-base (peek-at-word))) ,value)))
      (#b11 (if ,is-word (setf (register (bits->word-reg ,r/m-bits)) ,value) (setf (byte-register (bits->byte-reg ,r/m-bits)) ,value))))
    ,value))

;;; Instruction loader

(defun next-instruction ()
  (incf *ip*)
  (elt *ram* (1- (current-ip))))

(defun next-word ()
  (reverse-little-endian (next-instruction) (next-instruction)))

(defun peek-at-instruction (&optional (forward 0))
  (incf *advance*)
  (elt *ram* (+ (current-ip) forward)))

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

;;; Stack

(defmacro push-to-stack (value)
  `(progn
     (decf (register :sp) 2)
     (setf (segmented-word-in-ram :ss (register :sp)) ,value)))

; (defun push-to-stack (value)
;   (decf (register :sp) 2)
;   (setf (segmented-word-to-ram :ss (register :sp)) value))

(defun pop-from-stack ()
  (incf (register :sp) 2)
  (segmented-word-in-ram :ss (- (register :sp) 2)))

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
  (let ((mod-r/m (gensym)))
    `(let* ((,mod-r/m (next-instruction)) (r/m-bits (logand ,mod-r/m #b00000111)) (mod-bits (ash (logand ,mod-r/m #b11000000) -6)) (reg-bits (ash (logand ,mod-r/m #b00111000) -3)))
       ,@body)))

(defmacro with-size-by-last-bit (opcode &body body)
  `(let ((is-word (oddp ,opcode)))
     ,@body))

(defmacro with-in-place-mod (dest mod-bits r/m-bits &body body)
  `(progn
     ,@body
     (when (equal (car ',dest) 'indirect-address)
       (decf *advance* (advance-ip-ahead-of-indirect-address ,mod-bits ,r/m-bits)))))

(defmacro with-ds-default (&body body)
  `(let ((*default-segment* :ds))
     ,@body))

(defmacro with-indirect-segment-offset (mnemonic mod-bits r/m-bits &body body)
  (let ((address-base (gensym)) (read-seg (gensym)) (offset (gensym)) (real-base (gensym)) (read-seg-value (gensym)))
    `(disasm-instr (list ,mnemonic (indirect-address ,mod-bits ,r/m-bits t))
       (multiple-value-bind (,address-base ,read-seg) (address-for-r/m ,mod-bits ,r/m-bits)
	 (let* ((,offset (case mod-bits (#b00 0) (#b01 (peek-at-instruction)) (#b10 (peek-at-word)) (#b11 0))) (,real-base (+ ,address-base ,offset)) (,read-seg-value (segment ,read-seg)) (indirect-offset (segmented-word-in-ram ,read-seg-value ,real-base)) (indirect-segment (segmented-word-in-ram ,read-seg-value (+ ,real-base 2))))
	   ,@body)))))

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

(defun complement-carry-flag ()
  (disasm-instr '("cmc")
    (setf (flag-p :cf) (not (flag-p :cf)))))

(defun clear-direction-flag ()
  (disasm-instr '("cld")
    (setf (flag-p :df) nil)))

(defun set-direction-flag ()
  (disasm-instr '("std")
    (setf (flag-p :df) t)))

(defun clear-interrupt-flag ()
  (disasm-instr '("cli")
    (setf (flag-p :if) nil)))

(defun set-interrupt-flag ()
  (disasm-instr '("sti")
    (setf (flag-p :if) t)))

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

;; Segment operations

(defun segment-prefix (seg)
  (let ((*current-segment* seg))
    (parse-opcode (next-instruction))))

(defun push-segment (seg)
  (push-operation (segment seg)))

(defun pop-segment (seg)
  (pop-operation (segment seg)))

(defun mov-segment-to-indirect ()
  (with-mod-r/m-byte
    (mov (segment (bits->segment reg-bits)) (indirect-address mod-bits r/m-bits t))))

(defun mov-indirect-to-segment ()
  (with-mod-r/m-byte
    (mov (indirect-address mod-bits r/m-bits t) (segment (bits->segment reg-bits)))))

(defun load-far-pointer (seg mnemonic)
  (with-mod-r/m-byte
    (with-indirect-segment-offset mnemonic mod-bits r/m-bits
      (setf (register (bits->word-reg reg-bits)) indirect-offset)
      (setf (segment seg) indirect-segment))))

;; Flow control

(defun jmp-far ()
  (disasm-instr (list "jmp" :op (list :offset (next-word) :segment (next-word)))
    (setf *ip* (next-word))
    (setf (segment :cs) (next-word))))

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

(defun call-far ()
  (disasm-instr (list "call" :op (list :offset (next-word) :segment (next-word)))
    (push-to-stack (segment :cs))
    (push-to-stack (+ *ip* 4))
    (setf *ip* (next-word))
    (setf (segment :cs) (next-word))))

(defun call-near ()
  (disasm-instr (list "call" :op (twos-complement (next-word) t))
    (push-to-stack (+ *ip* 2))
    (incf *ip* (twos-complement (next-word) t))))

(defun ret-far ()
  (disasm-instr '("retf")
    (setf *ip* (pop-from-stack))
    (setf (segment :cs) (pop-from-stack))))

(defun ret-far-resetting-stack ()
  (disasm-instr (list "retf" :op (next-word))
    (ret-far)
    (incf (register :sp) (next-word))))

(defun ret-near ()
  (disasm-instr '("retn")
    (setf *ip* (pop-from-stack))))

(defun ret-near-resetting-stack ()
  (disasm-instr (list "retn" :op (next-word))
    (ret-near)
    (incf (register :sp) (next-word))))

(defmacro loop-instruction (condition mnemonic)
  `(let ((disp (twos-complement (next-instruction) nil)))
     (disasm-instr (list (concatenate 'string "loop" ,mnemonic) :op disp)
       (decf (register :cx))
       (when (and (not (zerop (register :cx))) ,condition)
	 (incf *ip* disp)))))

;; Interrupts

(defun interrupt (code)
  (check-type code (unsigned-byte 8))
  (when (flag-p :if)
    (let* ((offset (* code 4)) (new-ip (word-in-ram offset)) (new-cs (word-in-ram (+ offset 2))))
      (push-to-stack (flags-register))
      (push-to-stack (segment :cs))
      (push-to-stack *ip*)
      (clear-flag :if)
      (clear-flag :tf)
      (setf *ip* new-ip)
      (setf (segment :cs) new-cs))))

(defun int-operation ()
  (disasm-instr (list "int" :op (next-instruction))
    (interrupt (next-instruction))))

(defun int-3 ()
  (disasm-instr '("int" :op 3)
    (interrupt 3)))

(defun int-on-overflow ()
  (disasm-instr '("into")
    (if (flag-p :of)
	(interrupt 4))))

(defun iret ()
  (disasm-instr '("iret")
    (setf *ip* (pop-from-stack))
    (setf (segment :cs) (pop-from-stack))
    (setf (flags-register) (pop-from-stack))))

;; Port-mapped I/O

(defmacro input-operation (port opcode)
  `(with-size-by-last-bit ,opcode
     (disasm-instr (list "in" :src ,port :dest (if is-word (byte-register :al) (register :ax)))
       (setf (byte-register :al) (read-byte-from-io-port ,port))
       (when is-word
	 (setf (byte-register :ah) (read-byte-from-io-port (1+ ,port)))))))

(defmacro output-operation (port opcode)
  `(with-size-by-last-bit ,opcode
     (disasm-instr (list "out" :src (if is-word (register :ax) (byte-register :al)) :dest ,port)
       (write-byte-to-io-port ,port (byte-register :al))
       (when is-word
	 (write-byte-to-io-port (1+ ,port) (byte-register :ah))))))

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
    (with-ds-default
      (if is-word
	  (mov (segmented-word-in-ram *current-segment* (next-word)) (register :ax))
	  (mov (segmented-byte-in-ram *current-segment* (next-word)) (byte-register :al))))))

(defun mov-accumulator-to-offset (opcode)
  (with-size-by-last-bit opcode
    (with-ds-default
      (if is-word
	  (mov (register :ax) (segmented-word-in-ram *current-segment* (next-word)))
	  (mov (byte-register :al) (segmented-byte-in-ram *current-segment* (next-word)))))))

;; Groups 1A, 4, and 5 (inc/dec, call/jmp, and push/pop on EAs)

(defun inc-indirect (mod-bits r/m-bits is-word)
  (inc (indirect-address mod-bits r/m-bits is-word) is-word mod-bits r/m-bits))

(defun dec-indirect (mod-bits r/m-bits is-word)
  (dec (indirect-address mod-bits r/m-bits is-word) is-word mod-bits r/m-bits))

(defun push-indirect (mod-bits r/m-bits)
  (push-operation (indirect-address mod-bits r/m-bits t)))

(defun pop-indirect (mod-bits r/m-bits)
  (pop-operation (indirect-address mod-bits r/m-bits t)))

(defun call-near-indirect (mod-bits r/m-bits)
  (disasm-instr (list "call" :op (indirect-address mod-bits r/m-bits t))
    (push-to-stack *ip*)
    (setf *ip* (indirect-address mod-bits r/m-bits t))))

(defun call-far-indirect (mod-bits r/m-bits)
  (with-indirect-segment-offset "call" mod-bits r/m-bits
    (push-to-stack (segment :cs))
    (push-to-stack (+ *ip* 4))
    (setf *ip* indirect-offset)
    (setf (segment :cs) indirect-segment)))

(defun jmp-near-indirect (mod-bits r/m-bits)
  (disasm-instr (list "jmp" :op (indirect-address mod-bits r/m-bits t))
    (setf *ip* (indirect-address mod-bits r/m-bits t))))

(defun jmp-far-indirect (mod-bits r/m-bits)
  (with-indirect-segment-offset "jmp" mod-bits r/m-bits
    (setf *ip* indirect-offset)
    (setf (segment :cs) indirect-segment)))

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
    (3 (call-far-indirect mod-bits r/m-bits))
    (4 (jmp-near-indirect mod-bits r/m-bits))
    (5 (jmp-far-indirect mod-bits r/m-bits))
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

(defmacro mul-operation (src dest dest-overflow is-word)
  `(disasm-instr (list "mul" :src ,src)
     (let* ((result (* ,src ,dest)) (overflow (ash result (if ,is-word -16 -8))) (overflow-zero? (zerop overflow)))
       (setf ,dest result)
       (setf ,dest-overflow overflow)
       (setf (flag-p :cf) overflow-zero?)
       (setf (flag-p :of) overflow-zero?))))

(defun mul-indirect (mod-bits r/m-bits is-word)
  (if is-word
      (mul-operation (indirect-address mod-bits r/m-bits t) (register :ax) (register :dx) t)
      (mul-operation (indirect-address mod-bits r/m-bits nil) (byte-register :al) (byte-register :ah) nil)))

(defmacro imul-operation (src dest dest-overflow is-word)
  `(disasm-instr (list "imul" :src ,src)
     (let* ((result (* (twos-complement ,src ,is-word) (twos-complement ,dest ,is-word))) (overflow (ash result (if ,is-word -16 -8))))
       (setf ,dest result)
       (setf ,dest-overflow overflow)
       (let ((overflowed? (/= (twos-complement ,dest ,is-word) result)))
	 (setf (flag-p :cf) overflowed?)
	 (setf (flag-p :of) overflowed?)))))

(defun imul-indirect (mod-bits r/m-bits is-word)
  (if is-word
      (imul-operation (indirect-address mod-bits r/m-bits t) (register :ax) (register :dx) t)
      (imul-operation (indirect-address mod-bits r/m-bits nil) (byte-register :al) (byte-register :ah) nil)))

(defmacro div-operation (src dest-low dest-high is-word)
  `(disasm-instr (list "div" :src ,src)
     (multiple-value-bind (quotient remainder) (truncate (+ ,dest-low (ash ,dest-high (if ,is-word 16 8))) ,src)
       (setf ,dest-low quotient)
       (setf ,dest-high remainder))))

(defun div-indirect (mod-bits r/m-bits is-word)
  (if is-word
      (div-operation (indirect-address mod-bits r/m-bits t) (register :ax) (register :dx) t)
      (div-operation (indirect-address mod-bits r/m-bits nil) (byte-register :al) (byte-register :ah) nil)))

(defmacro idiv-operation (src dest-low dest-high is-word)
  `(disasm-instr (list "idiv" :src ,src)
     (multiple-value-bind (quotient remainder) (truncate (+ (twos-complement ,dest-low ,is-word) (ash (twos-complement ,dest-high ,is-word) (if ,is-word 16 8))) (twos-complement ,src ,is-word))
       (setf ,dest-low quotient)
       (setf ,dest-high remainder))))

(defun idiv-indirect (mod-bits r/m-bits is-word)
  (if is-word
      (idiv-operation (indirect-address mod-bits r/m-bits t) (register :ax) (register :dx) t)
      (idiv-operation (indirect-address mod-bits r/m-bits nil) (byte-register :al) (byte-register :ah) nil)))

(defun parse-group3-opcode (opcode)
  (parse-group-opcode
    (0 (parse-group-byte-pair opcode test-indirect-with-immediate mod-bits r/m-bits))
    (2 (parse-group-byte-pair opcode not-indirect mod-bits r/m-bits))
    (3 (parse-group-byte-pair opcode neg-indirect mod-bits r/m-bits))
    (4 (parse-group-byte-pair opcode mul-indirect mod-bits r/m-bits))
    (5 (parse-group-byte-pair opcode imul-indirect mod-bits r/m-bits))
    (6 (parse-group-byte-pair opcode div-indirect mod-bits r/m-bits))
    (7 (parse-group-byte-pair opcode idiv-indirect mod-bits r/m-bits))))

;; Group 2 (shifts and rotates)

(defmacro rotate-left (mod-bits r/m-bits count is-word)
  `(disasm-instr (list "rol" :src ,count :dest (indirect-address ,mod-bits ,r/m-bits ,is-word))
     (with-in-place-mod (indirect-address ,mod-bits ,r/m-bits ,is-word) ,mod-bits ,r/m-bits
       (unless (zerop ,count)
	 (loop
	    repeat (1+ ,count)
	    for tmp-value = (indirect-address ,mod-bits ,r/m-bits ,is-word) then (+ (ash tmp-value 1) (if bit-carried? 1 0))
	    for bit-carried? = (logbitp (if ,is-word 15 7) tmp-value)
	    finally (setf (indirect-address ,mod-bits ,r/m-bits ,is-word) tmp-value) (setf (flag-p :cf) (logbitp 0 tmp-value)) (if (= ,count 1) (setf (flag-p :of) (xor (flag-p :cf) bit-carried?))))))))

(defmacro rotate-right (mod-bits r/m-bits count is-word)
  `(disasm-instr (list "ror" :src ,count :dest (indirect-address ,mod-bits ,r/m-bits ,is-word))
     (with-in-place-mod (indirect-address ,mod-bits ,r/m-bits ,is-word) ,mod-bits ,r/m-bits
       (unless (zerop ,count)
	 (loop
	    repeat (1+ ,count)
	    for tmp-value = (indirect-address ,mod-bits ,r/m-bits ,is-word) then (+ (ash tmp-value -1) (ash (if bit-carried? 1 0) 15))
	    for bit-carried? = (logbitp 0 tmp-value)
	    finally (setf (indirect-address ,mod-bits ,r/m-bits ,is-word) tmp-value) (setf (flag-p :cf) (logbitp (if ,is-word 15 7) tmp-value)) (if (= ,count 1) (setf (flag-p :of) (xor (flag-p :cf) (logbitp (if ,is-word 14 6) tmp-value)))))))))

(defmacro rotate-left-with-cf (mod-bits r/m-bits count is-word)
  `(disasm-instr (list "rcl" :src ,count :dest (indirect-address ,mod-bits ,r/m-bits ,is-word))
     (with-in-place-mod (indirect-address ,mod-bits ,r/m-bits ,is-word) ,mod-bits ,r/m-bits
       (unless (zerop ,count)
	 (loop
	    repeat (1+ ,count)
	    for tmp-value = (indirect-address ,mod-bits ,r/m-bits ,is-word) then (+ (ash tmp-value 1) (if tmp-cf 1 0))
	    for tmp-cf = (flag-p :cf) then bit-carried?
	    for bit-carried? = (logbitp (if ,is-word 15 7) tmp-value)
	    finally (setf (indirect-address ,mod-bits ,r/m-bits ,is-word) tmp-value) (setf (flag-p :cf) tmp-cf) (if (= ,count 1) (setf (flag-p :of) (xor tmp-cf bit-carried?))))))))

(defmacro rotate-right-with-cf (mod-bits r/m-bits count is-word)
  `(disasm-instr (list "rcr" :src ,count :dest (indirect-address ,mod-bits ,r/m-bits ,is-word))
     (with-in-place-mod (indirect-address ,mod-bits ,r/m-bits ,is-word) ,mod-bits ,r/m-bits
       (unless (zerop ,count)
	 (loop
	    repeat (1+ ,count)
	    for tmp-value = (indirect-address ,mod-bits ,r/m-bits ,is-word) then (+ (ash tmp-value -1) (ash (if tmp-cf 1 0) 15))
	    for tmp-cf = (flag-p :cf) then bit-carried?
	    for bit-carried? = (logbitp 0 tmp-value)
	    finally (setf (indirect-address ,mod-bits ,r/m-bits ,is-word) tmp-value) (setf (flag-p :cf) tmp-cf) (if (= ,count 1) (setf (flag-p :of) (xor tmp-cf (logbitp (if ,is-word 14 6) tmp-value)))))))))

(defmacro shift-left (mod-bits r/m-bits count is-word)
  `(disasm-instr (list "shl" :src ,count :dest (indirect-address ,mod-bits ,r/m-bits ,is-word))
     (with-in-place-mod (indirect-address ,mod-bits ,r/m-bits ,is-word) ,mod-bits ,r/m-bits
       (unless (zerop ,count)
	 (let ((src-value (indirect-address ,mod-bits ,r/m-bits ,is-word)))
	   (set-zf-on-op (set-sf-on-op (set-pf-on-op (setf (indirect-address ,mod-bits ,r/m-bits ,is-word) (ash src-value ,count))) ,is-word))
	   (setf (flag-p :cf) (logbitp (- (if ,is-word 16 8) ,count) src-value))
	   (if (= ,count 1)
	       (setf (flag-p :of) (xor (flag-p :cf) (logbitp (- (if ,is-word 16 8) ,count 1) src-value)))))))))

(defmacro shift-logical-right (mod-bits r/m-bits count is-word)
  `(disasm-instr (list "shr" :src ,count :dest (indirect-address ,mod-bits ,r/m-bits ,is-word))
     (with-in-place-mod (indirect-address ,mod-bits ,r/m-bits ,is-word) ,mod-bits ,r/m-bits
       (unless (zerop ,count)
	 (let ((src-value (indirect-address ,mod-bits ,r/m-bits ,is-word)))
	   (set-zf-on-op (set-sf-on-op (set-pf-on-op (setf (indirect-address ,mod-bits ,r/m-bits ,is-word) (ash src-value (- ,count)))) ,is-word))
	   (setf (flag-p :cf) (logbitp (1- ,count) src-value))
	   (if (= ,count 1)
	       (setf (flag-p :of) (logbitp (1- (if ,is-word 16 8)) src-value))))))))

(defmacro shift-arithmetic-right (mod-bits r/m-bits count is-word)
  `(disasm-instr (list "sar" :src ,count :dest (indirect-address ,mod-bits ,r/m-bits ,is-word))
     (with-in-place-mod (indirect-address ,mod-bits ,r/m-bits ,is-word) ,mod-bits ,r/m-bits
       (unless (zerop ,count)
	 (let ((src-value (indirect-address ,mod-bits ,r/m-bits ,is-word)))
	   (set-zf-on-op (set-sf-on-op (set-pf-on-op (setf (indirect-address ,mod-bits ,r/m-bits ,is-word) (ash (twos-complement src-value ,is-word) (- ,count)))) ,is-word))
	   (setf (flag-p :cf) (logbitp (1- ,count) src-value))
	   (if (= ,count 1) (clear-flag :of)))))))

(defmacro parse-group2-opcode (opcode count)
  `(with-mod-r/m-byte
     (with-size-by-last-bit ,opcode
       (case reg-bits
	 (0 (rotate-left mod-bits r/m-bits ,count is-word))
	 (1 (rotate-right mod-bits r/m-bits ,count is-word))
	 (2 (rotate-left-with-cf mod-bits r/m-bits ,count is-word))
	 (3 (rotate-right-with-cf mod-bits r/m-bits ,count is-word))
	 ((4 6) (shift-left mod-bits r/m-bits ,count is-word))
	 (5 (shift-logical-right mod-bits r/m-bits ,count is-word))
	 (7 (shift-arithmetic-right mod-bits r/m-bits ,count is-word))))))

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
     (setf (byte-register :al) (logand (byte-register :al) #x0f))))

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

(defun ascii-adjust-after-multiplication ()
  (disasm-instr (list "aam" :op (next-instruction))
    (let ((base (next-instruction)))
      (setf (values (byte-register :ah) (byte-register :al)) (truncate (byte-register :al) base))
      (set-zf-on-op (set-sf-on-op (set-pf-on-op (byte-register :al)) nil)))))

(defun ascii-adjust-before-division ()
  (disasm-instr (list "aad" :op (next-instruction))
    (let ((base (next-instruction)))
      (set-zf-on-op (set-sf-on-op (set-pf-on-op (setf (byte-register :al) (+ (byte-register :al) (* (byte-register :ah) base)))) nil)))))

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
     (with-ds-default
       (if ,is-word
	   (mov (segmented-word-in-ram *current-segment* (register :si)) (segmented-word-in-ram :es (register :di)))
	   (mov (segmented-byte-in-ram *current-segment* (register :si)) (segmented-byte-in-ram :es (register :di)))))))

(defun mov-string (opcode)
  (string-operation opcode mov-string-operation))

(defmacro load-string-operation (is-word)
  `(disasm-instr '("lods")
     (with-ds-default
       (if ,is-word
	   (setf (register :ax) (segmented-word-in-ram *current-segment* (register :si)))
	   (setf (byte-register :al) (segmented-byte-in-ram *current-segment* (register :si)))))))

(defun load-string (opcode)
  (string-operation opcode load-string-operation))

(defmacro store-string-operation (is-word)
  `(disasm-instr '("stos")
     (if ,is-word
	 (setf (segmented-word-in-ram :es (register :di)) (register :ax))
	 (setf (segmented-byte-in-ram :es (register :di)) (byte-register :al)))))

(defun store-string (opcode)
  (string-operation opcode store-string-operation))

(defmacro compare-string-operation (is-word)
  `(disasm-instr '("cmps")
     (with-ds-default
       (if ,is-word
	   (cmp-operation (segmented-word-in-ram *current-segment* (register :si)) (segmented-word-in-ram :es (register :di)) t)
	   (cmp-operation (segmented-byte-in-ram *current-segment* (register :si)) (segmented-byte-in-ram :es (register :di)) nil)))))

(defun compare-string (opcode)
  (string-operation opcode compare-string-operation))

(defmacro scan-string-operation (is-word)
  `(disasm-instr '("scas")
     (if ,is-word
	 (cmp-operation (register :ax) (segmented-word-in-ram :es (register :di)) t)
	 (cmp-operation (byte-register :al) (segmented-byte-in-ram :es (register :di)) nil))))

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

;; Translation table lookup

(defun xlat ()
  (disasm-instr '("xlat")
    (with-ds-default
      (setf (byte-register :al) (segmented-byte-in-ram *current-segment* (+ (register :bx) (byte-register :al)))))))

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
    ((= opcode #xf5) (complement-carry-flag))
    ((= opcode #xfc) (clear-direction-flag))
    ((= opcode #xfd) (set-direction-flag))
    ((= opcode #xfa) (clear-interrupt-flag))
    ((= opcode #xfb) (set-interrupt-flag))
    ((= opcode #x06) (push-segment :es))
    ((= opcode #x07) (pop-segment :es))
    ((= opcode #x0e) (push-segment :cs))
    ((= opcode #x0f) (pop-segment :cs))
    ((= opcode #x16) (push-segment :ss))
    ((= opcode #x17) (pop-segment :ss))
    ((= opcode #x1e) (push-segment :ds))
    ((= opcode #x1f) (pop-segment :ds))
    ((= opcode #x26) (segment-prefix :es))
    ((= opcode #x2e) (segment-prefix :cs))
    ((= opcode #x36) (segment-prefix :ss))
    ((= opcode #x3e) (segment-prefix :ds))
    ((= opcode #x8c) (mov-segment-to-indirect))
    ((= opcode #x8e) (mov-indirect-to-segment))
    ((= opcode #xc4) (load-far-pointer :es "les"))
    ((= opcode #xc5) (load-far-pointer :ds "lds"))
    ((= opcode #xea) (jmp-far))
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
    ((= opcode #x9a) (call-far))
    ((= opcode #xe8) (call-near))
    ((= opcode #xc2) (ret-near-resetting-stack))
    ((= opcode #xc3) (ret-near))
    ((= opcode #xca) (ret-far-resetting-stack))
    ((= opcode #xcb) (ret-far))
    ((= opcode #xe0) (loop-instruction (not (flag-p :zf)) "ne"))
    ((= opcode #xe1) (loop-instruction (flag-p :zf) "e"))
    ((= opcode #xe2) (loop-instruction t ""))
    ((= opcode #xcc) (int-3))
    ((= opcode #xcd) (int-operation))
    ((= opcode #xce) (int-on-overflow))
    ((= opcode #xcf) (iret))
    ((in-paired-byte-block-p opcode #xe4) (input-operation (next-instruction) opcode))
    ((in-paired-byte-block-p opcode #xe6) (output-operation (next-instruction) opcode))
    ((in-paired-byte-block-p opcode #xec) (input-operation (register :dx) opcode))
    ((in-paired-byte-block-p opcode #xee) (output-operation (register :dx) opcode))
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
    ((in-paired-byte-block-p opcode #xd0) (parse-group2-opcode opcode 1))
    ((in-paired-byte-block-p opcode #xd2) (parse-group2-opcode opcode (byte-register :cl)))
    ((= opcode #x9c) (push-flags))
    ((= opcode #x9d) (pop-flags))
    ((= opcode #x9e) (store-flags-to-ah))
    ((= opcode #x9f) (load-flags-from-ah))
    ((= opcode #x8d) (load-effective-address))
    ((= opcode #x27) (decimal-adjust-after-addition))
    ((= opcode #x2f) (decimal-adjust-after-subtraction))
    ((= opcode #x37) (ascii-adjust-after-addition))
    ((= opcode #x3f) (ascii-adjust-after-subtraction))
    ((= opcode #xd4) (ascii-adjust-after-multiplication))
    ((= opcode #xd5) (ascii-adjust-before-division))
    ((= opcode #x98) (convert-byte-to-word))
    ((= opcode #x99) (convert-word-to-double))
    ((in-paired-byte-block-p opcode #xf2) (repeat-prefix opcode))
    ((in-paired-byte-block-p opcode #xa4) (mov-string opcode))
    ((in-paired-byte-block-p opcode #xaa) (store-string opcode))
    ((in-paired-byte-block-p opcode #xac) (load-string opcode))
    ((in-paired-byte-block-p opcode #xa6) (compare-string opcode))
    ((in-paired-byte-block-p opcode #xae) (scan-string opcode))
    ((= opcode #xd7) (xlat))))

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
