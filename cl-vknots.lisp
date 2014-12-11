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
			   

(defparameter *sample-braid* "6 2 1 3 2 4 3 5 4 2 1 3 2 f5 4 3 5 4")

(defun deserialize-braid-rep (str)
  (mapcar (lambda (x)
	    (if (char= #\f (char x 0))
		`(flip ,(parse-integer (subseq x 1)))
		(parse-integer x)))
	  (cl-ppcre:split " " (string-trim '(#\space #\newline) str))))

(defun braid->bw (lst)
  (destructuring-bind (total . rmats) lst
    (let ((br-hash (make-hash-table :test #'equal))
	  (maxnum total))
      (iter (for i from 1 to total)
	    (setf (gethash i br-hash) i))
      (append (iter (for elt in rmats)
		    (let ((letter (if (atom elt) (if (> elt 0)
						     'b
						     'w)
				      'f))
			  (number (if (atom elt) elt (cadr elt))))
		      (collect `(,letter
				 ,(gethash (abs number) br-hash)
				 ,(gethash (1+ (abs number)) br-hash)
				 ,(+ 1 maxnum)
				 ,(+ 2 maxnum)))
		      (setf (gethash (abs number) br-hash) (incf maxnum)
			    (gethash (1+ (abs number)) br-hash) (incf maxnum))))
	      (iter (for i from 1 to total)
		    (collect `(d ,i ,(gethash i br-hash))))))))




(defclass leg ()
  ((number :initarg :number)
   (direction :initarg :direction :initform :unspecified)))

(defclass junction ()
  ())

(defclass delta (junction)
  ((left-leg :initarg :leftleg)
   (right-leg :initarg :rightleg)))

(defclass r-matrix (junction)
  ((left-bottom-leg :initarg :lb)
   (right-bottom-leg :initarg :rb)
   (left-top-leg :initarg :lt)
   (right-top-let :initarg :rt)
   (type :initarg :type)))


(defclass flip (junction)
  ((left-bottom-leg :initarg :lb)
   (right-bottom-leg :initarg :rb)
   (left-top-leg :initarg :lt)
   (right-top-let :initarg :rt)))


(defun bw->hash (lst)
  (let ((res (make-hash-table :test #'equal)))
    (iter (for elt in lst)
	  (cond ((eq 'd (car elt))
		 (let ((delta (make-instance 'delta
					     :leftleg (make-instance 'leg :number (cadr elt))
					     :rightleg (make-instance 'leg :number (caddr elt)))))
		   (setf (gethash (cadr elt) res) delta
			 (gethash (caddr elt) res) delta)))
		((eq 'f (car elt))
		 (destructuring-bind (lb rb lt rt) (cdr elt)
		   (let ((flip (make-instance 'flip
					      :lb (make-instance 'leg :number lb)
					      :rb (make-instance 'leg :number rb)
					      :rt (make-instance 'leg :number lt)
					      :rb (make-instance 'leg :number rt))))
		     (setf (gethash lb res) flip (gethash rb res) flip
			   (gethash lt res) flip (gethash rt res) flip))))
		(t (destructuring-bind (letter lb rb lt rt) elt
		     (let ((rmat (make-instance 'r-matrix
						:type letter
						:lb (make-instance 'leg :number lb)
						:rb (make-instance 'leg :number rb)
						:rt (make-instance 'leg :number lt)
						:rb (make-instance 'leg :number rt))))
		       (setf (gethash lb res) rmat (gethash rb res) rmat
			     (gethash lt res) rmat (gethash rt res) rmat))))))
    res))
		     
		