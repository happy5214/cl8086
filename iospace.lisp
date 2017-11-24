;;;; Intel 8086 emulator (I/O address space)

(defun io-port (read write)
  (lambda (r/w)
    (if (eq r/w :read)
	read
	write)))

;;; State variables

(defparameter *io-space* (make-array (* 64 1024) :element-type 'function :initial-element (io-port (lambda () 0) (lambda (byte) byte))) "I/O space")

;;; Readers and writers

(defun read-byte-from-io-port (port)
  (funcall (funcall (elt *io-space* port) :read)))

(defun write-byte-to-io-port (port byte)
  (funcall (funcall (elt *io-space* port) :write) byte))

;;; I/O port registration

(defun set-read-only-port (port read)
  (setf (elt *io-space* port) (io-port read (lambda (byte) byte))))

(defun set-write-only-port (port write)
  (setf (elt *io-space* port) (io-port (lambda () nil) write)))

(defun set-read-write-port (port read write)
  (setf (elt *io-space* port) (io-port read write)))
