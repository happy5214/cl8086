;;;; Intel 8086 emulator

;;; Convenience functions

(defun reverse-little-endian (low high)
  "Reverse a little-endian number."
  (+ low (ash high 8)))

;;; Includes

(load "ram.lisp")
(load "iospace.lisp")
(load "cpu.lisp")

;;; Main functions

(defun load-instructions-into-ram (instrs &key (position 0) (seg 0))
  (setf *ip* position)
  (setf (segment :cs) seg (segment :ds) seg (segment :es) seg (segment :ss) seg)
  (setf (subseq *ram* (segment-calc seg position) (segment-calc seg #xffff)) instrs)
  (length instrs))

(defun load-instructions-from-file (file)
  (with-open-file (in file :element-type '(unsigned-byte 8))
    (let ((instrs (make-array (file-length in) :element-type '(unsigned-byte 8) :initial-element 0 :adjustable t)))
      (read-sequence instrs in)
      instrs)))

(defun load-instructions (&key (file nil) (example #()))
  (if file
      (load-instructions-from-file file)
      example))

(defun print-video-ram (&key (width 80) (height 25) (stream t) (newline nil) (seg #x1000))
  (dotimes (line height)
    (dotimes (column width)
      (let ((char-at-cell (byte-in-ram (segment-calc seg (+ #x8000 (* line 80) column)))))
	(if (zerop char-at-cell)
	    (format stream "~a" #\Space)
	    (format stream "~a" (code-char char-at-cell)))))
    (if newline (format stream "~%"))))

(defun disasm (&key (file nil) (example #()))
  (let ((*disasm* t))
    (disasm-instructions (load-instructions-into-ram (load-instructions :file file :example example) :position 0 :seg 0))))

(defun main (&key (file nil) (example #()) (display nil) (stream t) (newline nil) (position 0) (seg #x1000))
  (let ((*disasm* nil))
    (load-instructions-into-ram (load-instructions :file file :example example) :position position :seg seg)
    (execute-instructions)
    (when display
      (print-video-ram :stream stream :newline newline :seg seg))))
