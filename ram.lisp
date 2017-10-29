;;;; Intel 8086 emulator (RAM)

;;; State variables

(defparameter *ram* (make-array (* 1024 1024) :initial-element 0 :element-type '(unsigned-byte 8)) "RAM")

;;; Accessors

(defun byte-in-ram (location)
  "Read a byte from RAM."
  (elt *ram* location))

(defsetf byte-in-ram (location) (value)
  "Write a byte to RAM."
  `(setf (elt *ram* ,location) (logand ,value #xff)))

(defun word-in-ram (location)
  "Read a word from RAM."
  (reverse-little-endian (byte-in-ram location) (byte-in-ram (1+ location))))

(defsetf word-in-ram (location) (value)
  "Write a word to RAM."
  `(progn
     (setf (byte-in-ram ,location) (logand ,value #x00ff))
     (setf (byte-in-ram (1+ ,location)) (ash (logand ,value #xff00) -8))
     ,value))
