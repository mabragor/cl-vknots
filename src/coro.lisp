
(in-package #:cl-vknots)

(defmacro-driver (for var in-coroutine coro &optional with-arg (arg nil arg-p))
  (let ((kwd (if generate 'generate 'for))
	(g!-coro (gensym "G!-CORO")))
    `(progn (with ,g!-coro = ,coro)
	    ;; multiple evaluation of arg is intended
	    (,kwd ,var next (let ((vals (multiple-value-list (funcall ,g!-coro ,@(if arg-p `(,arg))))))
			      (if (not vals)
				  (terminate)
				  (car vals)))))))

(defmacro coexit! ()
  `(coexit (values)))

(defmacro! lambda-coro (arg &body body)
  `(progn (defcoroutine ,g!-name ,arg
	    ,@body
	    (coexit!))
	  (make-coroutine ',g!-name)))
