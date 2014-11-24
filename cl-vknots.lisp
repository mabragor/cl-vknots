;;;; cl-vknots.lisp

(in-package #:cl-vknots)

(enable-read-macro-tokens)

(defun read-knot (fname)
  (iter (for line in-file fname using #'read-line)
	(cond ((m~ "v (\d+) (\d+) (\d+) (\d+)" line)
	       (collect (list 'v (parse-integer $1) (parse-integer $2) (parse-integer $3) (parse-integer $4))))
	      ((m~ "d (\d+) (\d+)" line)
	       (collect (list 'd (parse-integer $1) (parse-integer $2)))))))

(defparameter primary-hypercube nil)
(defparameter output-count 0)

(defun new-deltas (deltas a b)
  ;; (let ((*print-pretty* nil))
  ;;   (format t "Deltas: ~a, a: ~a, b: ~a~%" deltas a b))
  (let ((other-a (cdr (assoc a deltas)))
	(other-b (cdr (assoc b deltas))))
    (cond ((and (equal other-a b) (equal other-b a))
	   (push `(num-circles . ,(1+ (or (cdr (assoc 'num-circles deltas))
					  0)))
		 deltas)
	   (push (cons a nil) deltas)
	   (push (cons b nil) deltas))
	  ((and other-a (not (equal other-a b)) (not other-b))
	   (push (cons a nil) deltas)
	   (push (cons other-a b) deltas)
	   (push (cons b other-a) deltas))
	  ((and other-b (not (equal other-b a)) (not other-a))
	   (push (cons b nil) deltas)
	   (push (cons other-b a) deltas)
	   (push (cons a other-b) deltas))
	  ((and (not other-a) (not other-b))
	   (push (cons a b) deltas)
	   (push (cons b a) deltas))
	  ((and other-a other-b (not (equal other-a b)) (not (equal other-b a)))
	   (push (cons a nil) deltas)
	   (push (cons b nil) deltas)
	   (push (cons other-a other-b) deltas)
	   (push (cons other-b other-a) deltas))
	  (t (error "Some error in cup-caps occured.")))
    ;; (format t "New deltas: ~a" deltas)
    deltas))

(let ((stream nil))
  (defun init-output ()
    (setf stream (open "~/data/knot-primary-hypercube" :direction :output :if-exists :supersede)))
  (defun output-hypercube-vertex (choices num-circles)
    (let ((*print-pretty* nil))
      (format stream "~a~%" num-circles)))
  (defun close-output ()
    (close stream)
    (setf stream nil)))

(defun %primary-hypercube (choices-acc deltas lst)
  (if (not lst)
      (progn (when (equal 0 (mod (incf output-count) 1000))
	       (format t "processed ~a entries~%" output-count)
	       (sb-ext:gc))
	     (output-hypercube-vertex choices-acc (or (cdr (assoc 'num-circles deltas)) 0)))
      (cond ((eq 'v (caar lst))
	     (destructuring-bind (v a b c d) (car lst)
	       (declare (ignore v))
	       (%primary-hypercube (cons 'b choices-acc)
				   (new-deltas (new-deltas deltas a c) b d)
				   (cdr lst))
	       (%primary-hypercube (cons 'w choices-acc)
				   (new-deltas (new-deltas deltas a d) b c)
				   (cdr lst))))
	    ((eq 'd (caar lst))
	     (destructuring-bind (d a b) (car lst)
	       (declare (ignore d))
	       (%primary-hypercube choices-acc
				   (new-deltas deltas a b)
				   (cdr lst)))))))
			

(defun primary-hypercube (lst)
  (let ((output-count 0))
    (unwind-protect (progn (init-output)
			   (%primary-hypercube nil nil lst))
      (close-output))))
			   
      