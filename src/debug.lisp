
(in-package #:cl-vknots)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter *debug* nil))

(defparameter *tracing-indent* 0)

(defun joinl (joinee lst)
  (format nil (concatenate 'string "~{~a~^" joinee "~}") lst))
(defun join (joinee &rest lst)
  (joinl joinee lst))

(defmacro tracing-init (&body body)
  (if *debug*
      `(let ((*tracing-indent* 0))
	 ,@body)
      `(progn ,@body)))

(defmacro tracing-level (&body body)
  (if *debug*
      `(let ((*tracing-indent* (+ *tracing-indent* 4)))
	 ,@body)
      `(progn ,@body)))
      
(defmacro if-debug (format-str &rest args)
  (if *debug*
      `(format t ,(join "" "~a" format-str "~%")
	       (make-string *tracing-indent* :initial-element #\space)
	       ,@args)))
