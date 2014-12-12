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
   (right-top-leg :initarg :rt)
   (type :initarg :type)))


(defclass flip (junction)
  ((left-bottom-leg :initarg :lb)
   (right-bottom-leg :initarg :rb)
   (left-top-leg :initarg :lt)
   (right-top-leg :initarg :rt)))


(defun croaky-setf-type (leg type)
  (if (eq :unspecified (slot-value leg 'direction))
      (setf (slot-value leg 'direction) type)
      (error "Visited the given leg twice: previous type is ~a" (slot-value leg 'direction))))

(defgeneric step-over (junction number)
  (:documentation "Main function, which modifies stepped-over junction by side effect, giving orientations"))

(defparameter junctions (make-hash-table :test #'equal)
  "Variable to hold the set of junctions we are currently work with")

(defmethod step-over ((junc junction) number)
  (multiple-value-bind (in-leg out-leg) (route junc number)
    (croaky-setf-type in-leg :in)
    (croaky-setf-type out-leg :out)
    (slot-value out-leg 'number)))

(defgeneric route (junction number)
  (:documentation "Given the number of the in-leg return pair of objects - in-leg and out-leg"))

(defmethod route ((delta delta) number)
  (with-slots (left-leg right-leg) delta
    (with-slots ((number-l number)) left-leg
      (with-slots ((number-r number)) right-leg
	(if (equal number-l number-r)
	    (error "Got short-circuiting delta")
	    (cond ((equal number number-l) (values left-leg right-leg))
		  ((equal number number-r) (values right-leg left-leg))
		  (t (error "This delta does not have leg with requested number, can't route"))))))))

(defmethod route ((flip flip) number)
  (with-slots (left-bottom-leg right-bottom-leg left-top-leg right-top-leg) flip
    (with-slots ((number-left-bottom number)) left-bottom-leg
      (with-slots ((number-right-bottom number)) right-bottom-leg
	(with-slots ((number-left-top number)) left-top-leg
	  (with-slots ((number-right-top number)) right-top-leg
	    (if (not (equal 4 (length (remove-duplicates (list number-left-bottom
							       number-right-bottom
							       number-left-top
							       number-right-top)
							 :test #'equal))))
		(error "Got short-circuiting flip"))
	    (cond ((equal number number-left-bottom) (values left-bottom-leg right-bottom-leg))
		  ((equal number number-right-bottom) (values right-bottom-leg left-bottom-leg))
		  ((equal number number-left-top) (values left-top-leg right-top-leg))
		  ((equal number number-right-top) (values right-top-leg left-top-leg))
		  (t (error "This flip does not have leg with requested number, can't route")))))))))

(defmethod route ((rmat r-matrix) number)
  (with-slots (left-bottom-leg right-bottom-leg left-top-leg right-top-leg) rmat
    (with-slots ((number-left-bottom number)) left-bottom-leg
      (with-slots ((number-right-bottom number)) right-bottom-leg
	(with-slots ((number-left-top number)) left-top-leg
	  (with-slots ((number-right-top number)) right-top-leg
	    (if (not (equal 4 (length (remove-duplicates (list number-left-bottom
							       number-right-bottom
							       number-left-top
							       number-right-top)
							 :test #'equal))))
		(error "Got short-circuiting r-matrix"))
	    (cond ((equal number number-left-bottom) (values left-bottom-leg right-top-leg))
		  ((equal number number-right-bottom) (values right-bottom-leg left-top-leg))
		  ((equal number number-left-top) (values left-top-leg right-bottom-leg))
		  ((equal number number-right-top) (values right-top-leg left-bottom-leg))
		  (t (error "This r-matrix does not have leg with requested number, can't route")))))))))
  
  

(defun bw->hash (lst)
  (let ((res (make-hash-table :test #'equal)))
    (iter (for elt in lst)
	  (cond ((eq 'd (car elt))
		 (let ((delta (make-instance 'delta
					     :leftleg (make-instance 'leg :number (cadr elt))
					     :rightleg (make-instance 'leg :number (caddr elt)))))
		   (push delta (gethash (cadr elt) res))
		   (push delta (gethash (caddr elt) res))))
		((eq 'f (car elt))
		 (destructuring-bind (lb rb lt rt) (cdr elt)
		   (let ((flip (make-instance 'flip
					      :lb (make-instance 'leg :number lb)
					      :rb (make-instance 'leg :number rb)
					      :lt (make-instance 'leg :number lt)
					      :rt (make-instance 'leg :number rt))))
		     (push flip (gethash lb res))
		     (push flip (gethash rb res))
		     (push flip (gethash lt res))
		     (push flip (gethash rt res)))))
		(t (destructuring-bind (letter lb rb lt rt) elt
		     (let ((rmat (make-instance 'r-matrix
						:type letter
						:lb (make-instance 'leg :number lb)
						:rb (make-instance 'leg :number rb)
						:lt (make-instance 'leg :number lt)
						:rt (make-instance 'leg :number rt))))
		       (push rmat (gethash lb res))
		       (push rmat (gethash rb res))
		       (push rmat (gethash lt res))
		       (push rmat (gethash rt res)))))))
    res))

(defun get-other-junction (last-junction number)
  (let ((fit-juncs (gethash number junctions)))
    (if (not (equal 2 (length fit-juncs)))
	(error "More than two junctions lead to same number"))
    (let ((filter-junctions (remove-if (if (not last-junction)
					   (lambda (x)
					     (typep x 'delta))
					   (lambda (x)
					     (eq x last-junction)))
				       fit-juncs)))
      (if (not (equal 1 (length filter-junctions)))
	  (error "Number of junctions after filtration not equal to 1")
	  (car filter-junctions)))))
	
		     
(defun ndetermine-orientations (hash)
  (let ((junctions hash))
    (macrolet ((the-step-over ()
		 `(let ((new-junction (get-other-junction last-junction number)))
		    (setf number (step-over new-junction number)
			  last-junction new-junction))))
      (let ((number 1)
	    (last-junction nil))
	(the-step-over)
	(iter (while (not (equal number 1)))
	      (the-step-over))))
    hash))

