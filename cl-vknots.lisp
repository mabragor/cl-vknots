;;;; cl-vknots.lisp

(in-package #:cl-vknots)

(enable-read-macro-tokens)
(cl-interpol:enable-interpol-syntax)

(defun joinl (joinee lst)
  (format nil (concatenate 'string "~{~a~^" joinee "~}") lst))
(defun join (joinee &rest lst)
  (joinl joinee lst))

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

(defun %primary-hypercube (lst &key outputter)
  (labels ((rec (choices-acc deltas lst)
	     (if (not lst)
		 (progn (when (equal 0 (mod (incf output-count) 1000))
			  (format t "processed ~a entries~%" output-count)
			  (sb-ext:gc))
			(funcall outputter choices-acc (or (cdr (assoc 'num-circles deltas)) 0)))
		 (cond ((eq 'v (caar lst))
			(destructuring-bind (v a b c d) (car lst)
			  (declare (ignore v))
			  (rec (cons 'b choices-acc)
			       (new-deltas (new-deltas deltas a c) b d)
			       (cdr lst))
			  (rec (cons 'w choices-acc)
			       (new-deltas (new-deltas deltas a d) b c)
			       (cdr lst))))
		       ((eq 'd (caar lst))
			(destructuring-bind (d a b) (car lst)
			  (declare (ignore d))
			  (rec choices-acc
			       (new-deltas deltas a b)
			       (cdr lst))))))))
    (rec nil nil lst)))
			

(defun primary-hypercube (lst)
  (let ((output-count 0))
    (unwind-protect (progn (init-output)
			   (%primary-hypercube lst :outputter #'output-hypercube-vertex))
      (close-output))))
			   

(defparameter *sample-braid* "6 2 1 3 2 4 3 5 4 2 1 3 2 f5 4 3 5 4")

(defparameter *2-strand-trefoil* "2 1 1 1")

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

(defun segment-numbers (bw)
  (let ((res (make-hash-table :test #'equal)))
    (iter (for elt in bw)
	  (iter (for num in (cdr elt))
		(setf (gethash num res) t)))
    (iter (for (key nil) in-hashtable res)
	  (collect key))))

(defun follow-up-hash (bw)
  (let ((follow-ups (make-hash-table :test #'equal)))
    (iter (for (type . nums) in bw)
	  (if (eq 'd type)
	      (setf (gethash (car nums) follow-ups) (cadr nums))
	      (setf (gethash (car nums) follow-ups) (caddr nums)
		    (gethash (cadr nums) follow-ups) (cadddr nums))))
    follow-ups))

(defun cycle-join-hash (bw)
  (let ((joins (make-hash-table :test #'equal)))
    (iter (for (type . nums) in bw)
	  (if (not (eq 'd type))
	      (setf (gethash (car nums) joins) (cadr nums)
		    (gethash (cadr nums) joins) (car nums))))
    joins))


(defun seifert-segments (bw)
  (let ((follow-ups (follow-up-hash bw)))
    (let ((segment-numbers (segment-numbers bw))
	  (seifert-segments nil)
	  (cur-cycle 0)
	  (cur-segment 0)
	  (begin-segment 0)
	  (cur-segment-sequence nil))
      (iter (while segment-numbers)
	    (incf cur-cycle)
	    ;; (format t "Searching cycle ~a~%" cur-cycle)
	    (setf cur-segment (car segment-numbers))
	    (setf begin-segment cur-segment
		  cur-segment-sequence nil)
	    (format t "Searching cycle ~a, begin segment is ~a, cur segment is ~a~%"
		    cur-cycle begin-segment cur-segment)
	    (pop segment-numbers)
	    (push cur-segment cur-segment-sequence)
	    (let ((next-segment (gethash cur-segment follow-ups)))
	      (iter (while (not (equal next-segment begin-segment)))
		    (format t "Found next segment ~a~%" next-segment)
		    (push next-segment cur-segment-sequence)
		    (setf segment-numbers (delete next-segment segment-numbers :test #'equal)
			  cur-segment next-segment)
		    (setf next-segment (gethash cur-segment follow-ups)))
	      (push (cons cur-cycle cur-segment-sequence) seifert-segments)))
      seifert-segments)))

(defclass dessin-node ()
  ((edges :initarg :edges)))

(defclass dessin-edge ()
  ((nodes)))
(defun mk-dessin-edge ()
  (let ((it (make-instance 'dessin-edge)))
    (with-slots (nodes) it
      (setf nodes (list nil nil)))))

(defun connect-left (edge node)
  (with-slots (nodes) edge
    (setf (car nodes) node)))
(defun connect-right ()
  )
	

(defclass dessin-denfant ()
  ((edges) (nodes)))
		
(defun dessin-denfant (bw)
  (let ((seifert-segments (seifert-segments bw))
	(joins (cycle-join-hash bw)))
    (list seifert-segments (cl-yy:hash->assoc joins))))
    
      
      
	    
  

(defgeneric listize (junc)
  (:documentation "Convert oriented junction into list-form"))

(defmethod listize ((delta delta))
  (with-slots (left-leg right-leg) (normalize-delta delta)
    (with-slots ((number-l number)) left-leg
      (with-slots ((number-r number)) right-leg
	`((d ,number-l ,number-r))))))

(defmethod listize ((flip flip))
  (with-slots (left-bottom-leg right-bottom-leg left-top-leg right-top-leg) flip
    (with-slots ((number-left-bottom number)) left-bottom-leg
      (with-slots ((number-right-bottom number)) right-bottom-leg
	(with-slots ((number-left-top number)) left-top-leg
	  (with-slots ((number-right-top number)) right-top-leg
	    (list `(d ,number-left-bottom ,number-right-bottom)
		  `(d ,number-left-top ,number-right-top))))))))

(defun antitype (type)
  (cond ((eq 'b type) 'w)
	((eq 'w type) 'b)
	(t (error "Unknown r-matrix type ~a" type))))


(defun oriented-r-matrix (type lb rb lt rt)
  (make-instance 'r-matrix
		 :type type
		 :lb (make-instance 'leg :number lb :direction :in)
		 :rb (make-instance 'leg :number rb :direction :in)
		 :lt (make-instance 'leg :number lt :direction :out)
		 :rt (make-instance 'leg :number rt :direction :out)))

(defun normalize-delta (delta)
  "Rotate delta such that in-leg is the left one."
  (with-slots (left-leg right-leg) delta
    (with-slots ((number-l number) (dir-l direction)) left-leg
      (with-slots ((number-r number) (dir-r direction)) right-leg
	(if (eq :in dir-l)
	    delta
	    (make-instance 'delta
			   :leftleg right-leg
			   :rightleg left-leg))))))


(defun normalize-r-matrix (rmat)
  "Rotate R-matrix such that in legs are bottom ones."
  (with-slots (left-bottom-leg right-bottom-leg left-top-leg right-top-leg type) rmat
    (with-slots ((a number) (dir-left-bottom direction)) left-bottom-leg
      (with-slots ((b number) (dir-right-bottom direction)) right-bottom-leg
	(with-slots ((c number) (dir-left-top direction)) left-top-leg
	  (with-slots ((d number) (dir-right-top direction)) right-top-leg
	    (cond ((and (eq :in dir-right-bottom) (eq :in dir-left-bottom))
		   rmat)
		  ((and (eq :in dir-left-bottom) (eq :in dir-left-top))
		   (oriented-r-matrix (antitype type) c a d b))
		  ((and (eq :in dir-left-top) (eq :in dir-right-top))
		   (oriented-r-matrix type d c b a))
		  ((and (eq :in dir-right-top) (eq :in dir-right-bottom))
		   (oriented-r-matrix (antitype type) b d a c))
		  (t (error "Something wrong with orientation guessing of r-matrix")))))))))

(defmethod listize ((rmat r-matrix))
  (let ((rmat (normalize-r-matrix rmat)))
    (with-slots (left-bottom-leg right-bottom-leg left-top-leg right-top-leg type) rmat
      (with-slots ((a number)) left-bottom-leg
	(with-slots ((b number)) right-bottom-leg
	  (with-slots ((c number)) left-top-leg
	    (with-slots ((d number)) right-top-leg
	      (list (list type a b c d)))))))))

(defun oriented-hash->bw (hash)
  (let ((single-juncs (make-hash-table)))
    (iter (for (nil val) in-hashtable hash)
	  (iter (for elt in val)
		(setf (gethash elt single-juncs) t)))
    (iter (for (key nil) in-hashtable single-juncs)
	  (appending (listize key)))))



(defparameter *a* (oriented-hash->bw 
		   (ndetermine-orientations
		    (bw->hash (braid->bw (deserialize-braid-rep *sample-braid*))))))

(defparameter *2-strand-trefoil-orient*
  (oriented-hash->bw 
   (ndetermine-orientations
    (bw->hash (braid->bw (deserialize-braid-rep *2-strand-trefoil*))))))

(defun braid->oriented-bw (braid)
  (oriented-hash->bw 
   (ndetermine-orientations
    (bw->hash (braid->bw (deserialize-braid-rep braid))))))

(defun braid->secondary-hypercube (braid)
  (destructuring-bind (initial-vertex hypercube)
      (marked-primary-hypercube-for-bw
       (oriented-hash->bw 
	(ndetermine-orientations
	 (bw->hash (braid->bw (deserialize-braid-rep braid))))))))
    
      
(defun str->marked-secondary-hypercube (str)
  (destructuring-bind (vertex cube)
      (marked-primary-hypercube-for-bw
       (oriented-hash->bw 
	(ndetermine-orientations
	 (bw->hash (braid->bw (deserialize-braid-rep str))))))
    (list vertex (primary-hypercube->secondary-hypercube cube))))

(defun serialize-marked-hypercube (x &optional (fname "~/out.txt"))
  (destructuring-bind (vertex cube) x
    (with-open-file (stream fname :direction :output :if-exists :supersede)
      (format stream "~{~a~^ ~}~%" vertex)
      (iter (for poly in-vector cube)
	    (write-line poly stream))))
  :success)

(defun digest (&key (in "~/in.txt") (out "~/out.txt"))
  (serialize-marked-hypercube (str->marked-secondary-hypercube (with-open-file (stream in)
								 (read-line stream)))
			      out))

(defgeneric choices->number (obj)
  )

(defmethod choices->number ((lst list))
  (iter (for elt in lst)
	(for i from 0)
	(if (eq 'w elt)
	    (summing (expt 2 i)))))


(defmethod choices->number ((lst vector))
  (iter (for elt in-vector lst)
	(for i from 0)
	(if (eq 'w elt)
	    (summing (expt 2 i)))))


(defun marked-primary-hypercube-for-bw (bw)
  (multiple-value-bind (dim init-vertex decolored)
      (iter (for elt in bw)
	    (if (or (eq 'b (car elt)) (eq 'w (car elt)))
		(progn (summing 1 into dim)
		       (collect (car elt) into init-vertex)
		       (collect (cons 'v (cdr elt)) into decolored))
		(collect elt into decolored))
	    (finally (return (values dim init-vertex decolored))))
    (let ((res (make-array (expt 2 dim)
			   :element-type 'integer
			   :initial-element 0)))
      (flet ((outputter (choices num-circles)
	       (setf (elt res (choices->number choices)) num-circles)))
	(%primary-hypercube decolored :outputter #'outputter))
      (list init-vertex res))))

(defparameter *2-strand-trefoil-primary-hypercube*
  (cadr (marked-primary-hypercube-for-bw *2-strand-trefoil-orient*)))

(defun n-poly-snippet (sgn power)
  #?"$((if (< 0 sgn) "+" "-")) N^$(power)")

(defun num->bw (num dim)
  (let ((res (make-list dim :initial-element 'b)))
    (iter (for char in-string (reverse (format nil "~b" num)))
	  (for place on res)
	  (if (char= #\1 char)
	      (setf (car place) 'w)))
    res))
				
(defun bw->white-places (bw-num)
  (iter (for elt in bw-num)
	(for i from 0)
	(if (eq 'w elt)
	    (collect i))))

(defun enlarge-subseq (subseq dim white-places)
  (let ((res (make-array dim :element-type 'symbol :initial-element 'b)))
    (iter (for b/w in subseq)
	  (for num in white-places)
	  (setf (elt res num) b/w))
    res))

(let ((cache (make-hash-table :test #'equal)))
  (defun make-bw-subseqs (n)
    (cond ((equal n 0) '(()))
	  ;; ((equal n 1) '((b) (w)))
	  (t (or (gethash n cache)
		 (setf (gethash n cache)
		       (iter (for subsubseq in (make-bw-subseqs (1- n)))
			     (collect (cons 'b subsubseq))
			     (collect (cons 'w subsubseq)))))))))
		      
	      
      
(defun sign-of-choice (choice)
  (expt -1
	(iter (for elt in choice)
	      (if (eq 'w elt)
		  (summing 1)))))

(defun subnumbers (i dim)
  (let ((white-places (bw->white-places (num->bw i dim))))
    (mapcar (lambda (x)
	      (list (choices->number (enlarge-subseq x dim white-places))
		    (sign-of-choice x)))
	    (make-bw-subseqs (length white-places)))))
  

(defun primary-hypercube->secondary-hypercube (cube)
  (let ((dim (floor (log (length cube) 2)))
	(res (make-array (length cube))))
    (iter (for i from 0 to (1- (length cube)))
	  (setf (elt res i)
		(joinl " " (cons "0"
				 (iter (for (j sgn) in (subnumbers i dim))
				       (collect (n-poly-snippet sgn (elt cube j))))))))
    res))
		

(defparameter *2-strand-trefoil-secondary-hypercube*
  (primary-hypercube->secondary-hypercube *2-strand-trefoil-primary-hypercube*))

(defparameter *mathematica-kernel-process* nil)

(defparameter *sigkill* 9)
(defparameter *sigint* 2)

(defun kill-mathematica ()
  (sb-ext:process-kill *mathematica-kernel-process* *sigkill*)
  (setf *mathematica-kernel-process* nil))

(defun abort-calculation ()
  (sb-ext:process-kill *mathematica-kernel-process* *sigint*))

(defrule integer ()
  (postimes (character-ranges (#\0 #\9))))

(defrule reverse-in ()
  " =:]" integer "[nI" #\newline
  :correct)

(defun join-continued-lines (lst)
  (let ((curline (car lst)))
    (iter (for line in (cdr lst))
	  (for i from 1)
	  (if (char= #\\ (char curline (1- (length curline))))
	      (setf curline (concatenate 'string
					 (subseq curline 0 (- (length curline) 2))
					 line))
	      (progn (collect curline)
		     (setf curline line)))
	  (if (equal (length (cdr lst)) i)
	      (progn (collect curline))))))

(defrule out-record ()
  "Out[" integer "]"
  (? (prog1 "//" (postimes (character-ranges (#\a #\z) (#\A #\Z)))))
  "= "
  t)
		     
(defun trim-out-record (str)
  (multiple-value-bind (head head-end-pos) (parse 'out-record str :junk-allowed t)
    (if head
	(subseq str head-end-pos))))
						  

(defun parse-output (str)
  (destructuring-bind (first . rest) (butlast (cdr (cl-ppcre:split "\\n" str)))
    (joinl "~%" (join-continued-lines (cons (trim-out-record first)
					    rest)))))


(defun output-complete-p (str)
  (parse 'reverse-in 
	 (reverse (if (> (length str) 100)
		      (subseq str (- (length str) 100))
		      str))
	 :junk-allowed t))

(defun %read-current-mathematica-output (stream &key wait)
  (if (and (not wait) (not (listen stream)))
      nil
      (progn ;; (format t "Waiting for bytes to appear~%")
	     (iter (while (not (listen stream))))
	     ;; (format t "Reading bytes~%")
	     (setf kernel-status :spewing-output)
	     (let ((res ""))
	       (iter (while (listen stream))
		     (setf res (concatenate 'string res (string (read-char stream)))))
	       res))))

(defun mathematica-read (&optional skip-status-check)
  (if (and (not skip-status-check)
	   (not (eq :calculating kernel-status)))
      (error "Nothing to read - kernel had no task to calculate"))
  (let ((stream (sb-ext:process-output *mathematica-kernel-process*)))
    (let ((res (%read-current-mathematica-output stream :wait t)))
      ;; (format t "Res is ~a" res)
      (iter (while (not (output-complete-p res)))
	    (setf res (concatenate 'string res (%read-current-mathematica-output stream :wait t))))
      (setf kernel-status :idle)
      res)))
      

(defparameter kernel-status :idle)

(defun mathematica-write (cmd &key (form :input))
  (if (not (eq :idle kernel-status))
      (error "Kernel is currently still doing something, but you can restart it, of course, if you so wish"))
  (let ((input (sb-ext:process-input *mathematica-kernel-process*)))
    (write-string cmd input)
    (cond ((eq :input form) (write-string " // InputForm" input))
	  ((eq :full form) (write-string " // FullForm" input)))
    (write-string #?"\n" input)
    (finish-output input)
    (setf kernel-status :calculating)))

(defun ensure-mathematica-is-running ()
  (if (not *mathematica-kernel-process*)
      (start-mathematica)))

(defun mathematica-perl (cmd)
  "Print-Eval-Read-Loop of Mathematica"
  (ensure-mathematica-is-running)
  (mathematica-write cmd)
  (mathematica-read))

(defun start-mathematica ()
  (when (and *mathematica-kernel-process*
	     (sb-ext:process-p *mathematica-kernel-process*))
    (kill-mathematica))
  (setf *mathematica-kernel-process*
	(sb-ext:run-program "math" '() :search t :wait nil :input :stream :output :stream :error :stream))
  (mathematica-read t)
  (setf kernel-status :idle)
  t)
  

      
