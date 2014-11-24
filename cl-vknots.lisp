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

(defun new-deltas (old-deltas a b)
  (let ((new-deltas old-deltas))
    (let ((other-a (gethash a old-deltas))
	  (other-b (gethash b old-deltas)))
      (cond ((and (equal other-a b) (equal other-b a))
	     (setf (gethash 'num-circles new-deltas)
		   (1+ (gethash 'num-circles new-deltas 0)))
	     (remhash a new-deltas)
	     (remhash b new-deltas))
	    ((and other-a (not (equal other-a b)) (not other-b))
	     (setf (gethash other-a new-deltas) b
		   (gethash b new-deltas) other-a))
	    ((and other-b (not (equal other-b a)) (not other-a))
	     (setf (gethash other-b new-deltas) a
		   (gethash a new-deltas) other-b))
	    ((and (not other-a) (not other-b))
	     (setf (gethash b new-deltas) a
		   (gethash a new-deltas) b))
	    (t (error "Some error in cup-caps occured.")))
      new-deltas)))

(defun %primary-hypercube (choices-acc deltas lst)
  (if (not lst)
      (push (list choices-acc (gethash 'num-circles deltas)) primary-hypercube)
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
  (let ((primary-hypercube nil))
    (%primary-hypercube nil (make-hash-table :test #'equal) lst)
    primary-hypercube))