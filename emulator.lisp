;;;; Intel 8086 emulator

;;; Convenience functions

(defun reverse-little-endian (low high)
  "Reverse a little-endian number."
  (+ low (ash high 8)))

;;; Includes

(load "ram.lisp")
(load "cpu.lisp")

;;; Main functions

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
  (let ((*disasm* t))
    (disasm-instructions (load-instructions-into-ram (load-instructions :file file :example example)))))

(defun main (&key (file nil) (example #()) (display nil) (stream t) (newline nil))
  (let ((*disasm* nil))
    (load-instructions-into-ram (load-instructions :file file :example example))
    (execute-instructions)
    (when display
      (print-video-ram :stream stream :newline newline))))
