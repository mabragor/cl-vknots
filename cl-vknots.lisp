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
			  ;; (format t "processed ~a entries~%" output-count)
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

(defparameter *2-strand-unknot* "2 1")
(defparameter *double-eight* "3 1 2")

(defparameter *3-strand-trefoil* "3 1 2 1 2")

(defparameter *3-4-knot* "3 1 2 1 2 1 2 1 2")


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
	    ;; (format t "Searching cycle ~a, begin segment is ~a, cur segment is ~a~%"
	    ;; cur-cycle begin-segment cur-segment)
	    (pop segment-numbers)
	    (push cur-segment cur-segment-sequence)
	    (let ((next-segment (gethash cur-segment follow-ups)))
	      (iter (while (not (equal next-segment begin-segment)))
		    ;; (format t "Found next segment ~a~%" next-segment)
		    (push next-segment cur-segment-sequence)
		    (setf segment-numbers (delete next-segment segment-numbers :test #'equal)
			  cur-segment next-segment)
		    (setf next-segment (gethash cur-segment follow-ups)))
	      (push (cons cur-cycle cur-segment-sequence) seifert-segments)))
      seifert-segments)))

(defclass living-thing ()
  ((alive :initform t)
   (alive-stack :initform nil)))

(defclass dessin-node (living-thing)
  ((edges :initarg :edges :initform nil)))
(defun mk-dessin-node ()
  (make-instance 'dessin-node))

(defclass dessin-edge (living-thing)
  ((nodes) (color :initform :b)))
(defun mk-dessin-edge ()
  (let ((it (make-instance 'dessin-edge)))
    (with-slots (nodes) it
      (setf nodes (list nil nil)))
    it))

(defun connect-node-left (edge node)
  (with-slots (nodes) edge
    (setf (car nodes) node)))
(defun connect-node-right (edge node)
  (with-slots (nodes) edge
    (setf (cadr nodes) node)))
(defun connect-node-free (edge node)
  (with-slots (nodes) edge
    (cond ((not (car nodes)) (connect-node-left edge node))
	  ((not (cadr nodes)) (connect-node-right edge node))
	  (t (error "No place on this edge to connect nodes to")))))

(defun connect-edge-begin (node edge)
  (with-slots (edges) node
    (push edge edges)))
(defun connect-edge-end (node edge)
  (with-slots (edges) node
    (setf edges (append edges (list edge)))))
(defun connect-edge (node edge n)
  (with-slots (edges) node
    (setf (nth n edges) edge)))
(defun reverse-node (node)
  (with-slots (edges) node
    (setf edges (nreverse edges))))
  

	
(defclass dessin-denfant ()
  ((edges :initarg :edges)
   (nodes :initarg :nodes)
   (factors :initarg :factors :initform nil)))

(defun bw->dessin (bw)
  (deserialize (seifert-segments bw) (cl-yy::hash->assoc (cycle-join-hash bw))))
		
(defun deserialize (seifert-segments joins &rest factors)
  (let (all-edges all-nodes)
    (let ((edge-hash (make-hash-table :test #'equal)))
      ;; (format t "About to pre-connect edges~%")
      (iter (for (from . to) in joins)
	    ;; (format t "Considering edge (~a ~a)~%" from to)
	    (if (not (gethash from edge-hash))
		(let ((new-edge (mk-dessin-edge)))
		  (setf (gethash from edge-hash) new-edge
			(gethash to edge-hash) new-edge)
		  (push new-edge all-edges))))
      ;; (format t "Pre-connected all edges~%")
      (iter (for (num . segments) in seifert-segments)
	    ;; (format t "Connecting node ~a~%" num)
	    (let ((new-node (mk-dessin-node)))
	      (push new-node all-nodes)
	      (iter (for segment in segments)
		    (let ((edge (gethash segment edge-hash)))
		      (when edge
			(connect-node-free edge new-node)
			(connect-edge-begin new-node edge)
			))))))
    (make-instance 'dessin-denfant :edges all-edges :nodes all-nodes
		   :factors (copy-list factors))))

(defun deserialize2 (lst)
  (let (all-edges all-nodes)
    (let ((edge-hash (make-hash-table :test #'equal)))
      (iter (for (num . edge-specs) in lst)
	    (let ((cur-node (mk-dessin-node)))
	      (push cur-node all-nodes)
	      (let ((num-edge 0)
		    (edge-color :b))
		(iter (for edge-spec in edge-specs)
		      (if (atom edge-spec)
			  (progn (setf num-edge edge-spec
				       edge-color :b))
			  (progn (setf num-edge (car edge-spec)
				       edge-color (cadr edge-spec))))
		      ;; (format t "Connecting edge ~a to node ~a~%" num-edge num)
		      (let ((it (gethash num-edge edge-hash)))
			(when (not it)
			  (let ((cur-edge (mk-dessin-edge)))
			    (setf it (setf (gethash num-edge edge-hash) cur-edge)
				  (slot-value cur-edge 'color) edge-color)
			    (push it all-edges)))
			(connect-node-free it cur-node)
			(connect-edge-begin cur-node it)))))))
    (make-instance 'dessin-denfant :edges all-edges :nodes all-nodes)))
			
(defun serialize2 (dessin)
  (let ((edge-hash (make-hash-table :test #'eq)))
    (with-slots (nodes edges) dessin
      (iter (for edge in edges)
	    (for i from 1)
	    (setf (gethash edge edge-hash) i))
      (iter (for node in nodes)
	    (if (not (alive-p node))
		(next-iteration))
	    (generate i from 1)
	    (collect (cons (next i)
			   (iter (for edge in (slot-value node 'edges))
				 (if (not (alive-p edge))
				     (next-iteration))
				 (collect (gethash edge edge-hash)))))))))






				
			

(defgeneric serialize (x))

(defmethod serialize ((x list))
  (mapcar #'serialize x))

(defmethod serialize ((dessin dessin-denfant))
  (with-slots (nodes edges factors) dessin
    (let ((junc-hash (make-hash-table :test #'equal))
	  (i 0)
	  (j 0)
	  serialized-nodes
	  serialized-edges)
      (iter (for node in nodes)
	    (if (not (alive-p node))
		(next-iteration))
	    (incf j)
	    (let ((serialized-node (list j)))
	      (with-slots ((node-edges edges)) node
		(iter (for edge in node-edges)
		      (if (not (slot-value edge 'alive))
			  (next-iteration))
		      (incf i)
		      (setf (gethash (list node edge) junc-hash) i)
		      (push i serialized-node)))
	      (push (nreverse serialized-node) serialized-nodes)))
      (iter (for edge in edges)
	    (if (not (slot-value edge 'alive))
		(next-iteration))
	    (with-slots ((edge-nodes nodes)) edge
	      (let ((junc-left (gethash (list (car edge-nodes) edge) junc-hash))
		    (junc-right (gethash (list (cadr edge-nodes) edge) junc-hash)))
		(push (cons junc-left junc-right) serialized-edges)
		(push (cons junc-right junc-left) serialized-edges))))
      (cons serialized-nodes
	    (cons serialized-edges
		  (copy-list factors))))))
	    

(defun copy-dessin (dessin)
  (apply #'deserialize (serialize dessin)))
      
(defun min-valency (dessin)
  (iter (for node in (slot-value dessin 'nodes))
	(minimizing (length (slot-value node 'edges)))))
(defun max-valency (dessin)
  (iter (for node in (slot-value dessin 'nodes))
	(maximizing (length (slot-value node 'edges)))))
(defun num-nodes (dessin)
  (length (slot-value dessin 'nodes)))
(defun num-edges (dessin)
  (length (slot-value dessin 'edges)))
  

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
  

      
;; Here I'll write the recursion for calculation of dessins in fundamental representation

(defgeneric alive-p (x))

(defmethod alive-p ((x living-thing))
  (slot-value x 'alive))

(defmethod alive-p ((x dessin-denfant))
  (let (res)
    (iter (for node in (slot-value x 'nodes))
	  (when (alive-p node)
	    (setf res t)
	    (terminate)))
    res))

(defun valency (node)
  (with-slots (edges) node
    (iter (for edge in edges)
	  (if (not (alive-p edge))
	      (next-iteration))
	  (summing 1))))

(defun first-edge (node)
  (with-slots (edges) node
    (iter (for edge in edges)
	  (if (not (alive-p edge))
	      (next-iteration))
	  (return edge))))

(defun alive-edges (node)
  (let (res)
    (with-slots (edges) node
      (iter (for edge in edges)
	    (if (not (alive-p edge))
		(next-iteration))
	    (push edge res)))
    res))


(defun n-0-dessin-recursion (dessin)
  (let (touch)
    (with-slots (nodes edges factors) dessin
      (iter (for node in nodes)
	    (if (not (alive-p node))
		(next-iteration))
	    (when (equal 0 (valency node))
	      ;; (format t "applying 0-valent recursion~%")
	      (kill-node node)
	      (setf touch t)
	      (push "[N]" factors))))
    (values dessin touch)))
  

(defun n-1-dessin-recursion (dessin)
  (let (touch)
    (with-slots (nodes edges factors) dessin
      (iter (for node in nodes)
	    (if (not (alive-p node))
		(next-iteration))
	    (when (equal 1 (valency node))
	      ;; (format t "applying 1-valent recursion~%")
	      (kill-node node)
	      (setf touch t)
	      (push "[N-1]" factors))))
    (values dessin touch)))

(defmacro! with-disabled-components ((&rest components) &body body)
  `(let ((,g!-saved-states (mapcar (lambda (x)
				     (slot-value x 'alive))
				   (list ,@components))))
     (unwind-protect (progn ,@(mapcar (lambda (x)
					`(setf ,x nil))
				      components)
			    ,@body)
       (iter (for component in (list ,@components))
	     (for state in ,g!-saved-states)
	     (setf (slot-value component 'alive) state)))))

(defun looped-2-valent-vertex-p (node)
  (destructuring-bind (edge1 edge2) (alive-edges node)
    (with-slots ((nodes1 nodes)) edge1
      (with-slots ((nodes2 nodes)) edge2
	(and (eq (car nodes1) (cadr nodes1))
	     (eq (car nodes1) (car nodes2))
	     (eq (car nodes2) (cadr nodes2)))))))

(defun other-node (edge node)
  (with-slots (nodes) edge
    (iter (for inner-node in nodes)
	  (if (not (eq node inner-node))
	      (return inner-node))
	  (finally (error "Should not reach here")))))
    
(defun edges-to-different-nodes-p (node edges)
  (let ((lst (mapcar (lambda (x)
		       (other-node x node))
		     edges)))
    (equal (length lst) (length (remove-duplicates lst :test #'eq)))))

(defun edges-to-same-node-p (node edges)
  (let ((lst (mapcar (lambda (x)
		       (other-node x node))
		     edges)))
    (equal 1 (length (remove-duplicates lst :test #'eq)))))

(defun subs-node-with-another (edge old-node new-node)
  (iter (for node on (slot-value edge 'nodes))
	(if (eq old-node (car node))
	    (setf (car node) new-node))))
	    
(defun kill-node (node)
  (setf (slot-value node 'alive) nil)
  (iter (for edge in (slot-value node 'edges))
	(setf (slot-value edge 'alive) nil)))
	
(defun push-alive (thing)
  (push (slot-value thing 'alive) (slot-value thing 'alive-stack)))
(defun pop-alive (thing)
  (setf (slot-value thing 'alive) (pop (slot-value thing 'alive-stack))))



(defmacro! with-saved-node-state (node &body body)
  `(progn (push-alive ,node)
	  (iter (for edge in (slot-value ,node 'edges))
		(push-alive edge))
	  (unwind-protect (progn ,@body)
	    (pop-alive ,node)
	    (iter (for edge in (slot-value ,node 'edges))
		  (pop-alive edge)))))

(defmacro! with-saved-edge-state (edge &body body)
  `(progn (push-alive ,edge)
	  (unwind-protect (progn ,@body)
	    (pop-alive ,edge))))

(defun kill-edge (edge)
  (setf (slot-value edge 'alive) nil))

(defun dessin-with-killed-node (dessin node)
  (with-saved-node-state node
    (kill-node node)
    (copy-dessin dessin)))



(defun njoin-move (dessin node alive-edges)
  (let ((n1 (other-node (car alive-edges) node))
	(n2 (other-node (cadr alive-edges) node)))
    (let (block1 block2 block3 block4)
      (flet ((the-edge-p (x)
	       (iter (for edge in alive-edges)
		     (if (eq edge x)
			 (return-from the-edge-p t)))
	       nil))
	(let ((pos1 (position-if #'the-edge-p (slot-value n1 'edges)))
	      (pos2 (position-if #'the-edge-p (slot-value n2 'edges))))
	  (setf block1 (subseq (slot-value n1 'edges) 0 pos1)
		block2 (subseq (slot-value n1 'edges) (1+ pos1))
		block3 (subseq (slot-value n2 'edges) 0 pos2)
		block4 (subseq (slot-value n2 'edges) (1+ pos2))))
	(iter (for edge in block3)
	      (subs-node-with-another edge n2 n1))
	(iter (for edge in block4)
	      (subs-node-with-another edge n2 n1)))
      (setf (slot-value n1 'edges) (append block1 block4 block3 block2))
      (kill-node node)
      dessin)))

(defun ncut-move (dessin node alive-edges)
  (let ((n1 (other-node (car alive-edges) node)))
    (let (block1 block2 block3)
      (let ((pos (position-if (lambda (x)
				(or (eq (car alive-edges) x) (eq (cadr alive-edges) x)))
			      (slot-value n1 'edges))))
	(setf block1 (subseq (slot-value n1 'edges) 0 pos)
	      block3 (subseq (slot-value n1 'edges) (1+ pos)))
	(let ((pos1 (position-if (lambda (x)
				   (or (eq (car alive-edges) x) (eq (cadr alive-edges) x)))
				 block3)))
	  (setf block2 (subseq block3 0 pos1)
		block3 (subseq block3 (1+ pos1)))))
      ;; OK, let's first do it the dumb way
      (setf (slot-value n1 'edges) (append block1 block3))
      (let ((new-node (mk-dessin-node)))
	(setf (slot-value new-node 'edges) block2)
	(iter (for edge in block2)
	      (subs-node-with-another edge n1 new-node))
	(push new-node (slot-value dessin 'nodes)))
      (kill-node node)
      dessin)))



(defun ncut-or-join-move (dessin node alive-edges)
  (cond ((edges-to-different-nodes-p node alive-edges)
	 (njoin-move dessin node alive-edges))
	((edges-to-same-node-p node alive-edges)
	 (ncut-move dessin node alive-edges))
	(t (error "Should not reach this branch"))))


(defun n-2-dessin-recursion (dessin)
  (let (dessin1 touch)
    (with-slots (nodes edges factors) dessin
      (iter (for node in nodes)
	    (for i from 1)
	    ;; (format t "Considering node ~a~%" i)
	    (when (and (equal 2 (valency node))
		       (not (looped-2-valent-vertex-p node)))
	      (setf touch t)
	      (let ((my-edges (alive-edges node)))
		;; forget the vertex
		(setf dessin1 (dessin-with-killed-node dessin node))
		(push "[N-2]" (slot-value dessin1 'factors))
		;; contract the vertex
		(setf dessin (ncut-or-join-move dessin node my-edges))
		(terminate)))))
    (values (list dessin1 dessin) touch)))
		

;; OK, what to do with this lump of code now? How to melt it?
;; It doesn't even compile...

(defgeneric n-recursion-step (thing))

(defmethod n-recursion-step ((thing list))
  (let (step-done res)
    (iter (for elt in thing)
	  (multiple-value-bind (elt-res done) (n-recursion-step elt)
	    (setf step-done (or step-done done))
	    (push elt-res res)))
    (values (remove-if-not #'identity (alexandria:flatten res)) step-done)))

(defmethod n-recursion-step ((thing dessin-denfant))
  (let (step-done)
    (macrolet ((frob (x)
		 `(multiple-value-bind (res done) (,x thing)
		    (setf step-done (or step-done done)
			  thing res))))
      (frob n-fat-edges-recursion)
      ;; (format t "dessin state after stage -1: ~a~%" (serialize thing))
      (frob n-0-dessin-recursion)
      ;; (format t "dessin state after stage 0: ~a~%" (serialize thing))
      (frob n-1-dessin-recursion)
      ;; (format t "dessin state after stage 1: ~a~%" (serialize thing))
      (frob n-2-dessin-recursion)
      ;; (format t "dessin state after stage 2: ~a~%" (serialize thing))
      )
    ;; (format t "step done is ~a~%" step-done)
    (values thing step-done)))
  
	      
(defun n-dessin-recursion (dessin)
  (iter (while t)
	(multiple-value-bind (res done) (n-recursion-step dessin)
	  (if (listp res)
	      (setf dessin (remove-if-not #'identity res))
	      (setf dessin res))
	  (if (not done)
	      (terminate))))
  (mapcar #'serialize dessin))



;; TODO: compact human-writable notation for dessins, to be able to calculate dessins on demand,
;; without explicitly constructing knot for them

(defun next-alive-edge (node edge-lst)
  (let (following-edge)
    (iter (for edge in (cdr edge-lst))
	  (when (alive-p edge)
	    (setf following-edge edge)
	    (terminate)))
    (or following-edge
	(first-edge node))))

(defun fast-forward-to-edge (node edge)
  (iter (for cur-edge on (slot-value node 'edges))
	(if (eq edge (car cur-edge))
	    (return cur-edge))))

(defun n-fat-edges-node-recursion (dessin node)
  (let (step-done)
    (iter (generate edge on (slot-value node 'edges))
	  (if-first-time (next edge))
	  (when (not (alive-p (car edge)))
	    (next edge)
	    (next-iteration))
	  (let ((following-edge (next-alive-edge node edge)))
	    (if (or (not (eq (other-node (car edge) node)
			     (other-node following-edge node)))
		    (eq (car edge) following-edge)
		    ;; This is temporary for simplicity
		    (eq node (other-node (car edge) node)))
		(next edge)
		(let ((other-node (other-node (car edge) node)))
		  (if (eq following-edge
			  (next-alive-edge other-node (fast-forward-to-edge other-node (car edge))))
		      (progn (setf (slot-value following-edge 'alive) nil)
			     (push "[2]" (slot-value dessin 'factors)))
		      (next edge))))))
    step-done))

(defun n-fat-edges-recursion (dessin)
  (let (step-done)
    (iter (for node in (slot-value dessin 'nodes))
	  (if (not (alive-p node))
	      (next-iteration))
	  (setf step-done (or step-done (n-fat-edges-node-recursion dessin node))))
    (values dessin step-done)))



;; Ok, now I need to calculate expressions for all the subgraphs,
;; such that this won't be necessary to do by hand.

(defparameter cube (make-hash-table :test #'equal))

(defun calculate-cube-vertex (dessin level)
  ;; (format t "Calculating cube vertex for ~a~%" (serialize dessin))
  (let ((it (gethash level cube)))
    (when (not it)
      (setf it
	    (setf (gethash level cube) (make-hash-table :test #'equal))))
    (incf (gethash (n-dessin-recursion (copy-dessin dessin)) it 0))))

(defun cube-for-dessin (dessin)
  (let ((cube (make-hash-table :test #'equal)))
    (labels ((rec (left-edges level)
	       (if (not left-edges)
		   (calculate-cube-vertex dessin level)
		   (progn (rec (cdr left-edges) level)
			  (with-saved-edge-state (car left-edges)
			    (kill-edge (car left-edges))
			    (rec (cdr left-edges) (if (eq :b (slot-value (car left-edges) 'color))
						      (1+ level)
						      (1- level))))))))
      (rec (slot-value dessin 'edges) 0))
    cube))

(defun color-charge (dessin)
  (iter (for edge in (slot-value dessin 'edges))
	(if (not (alive-p edge))
	    (next-iteration))
	(summing (if (eq :b (slot-value edge 'color))
		     1
		     -1))))

(defun ask-user-for-clue (dessin)
  (format t "Can you, please, provide value for the graph~%~a >>>~%" (serialize2 dessin))
  (read-line))

(defun format-torus-dessin (lst)
  (if (equal 3 (cadr lst))
      (format nil "[N][N-1]^2 + [N][N-1][N-2] (~a)"
	      (joinl " + " (cons "0"
				 (iter (for i from 1 to (1- (car lst)))
				       (collect (format nil "[2]^~a" (1- (* 2 i))))))))
      (format nil "torusDessin[~a,~a]" (car lst) (cadr lst))))



(defun guess-the-dessin (dessin)
  ;; (declare (ignore nodes edges))
  (let ((s-dessin (serialize2 dessin)))
    (let ((it (torus-dessin-p s-dessin)))
      (if it
	  (format-torus-dessin it)
	  (ask-user-for-clue dessin)))))

(defparameter *3-3-dessin* '((1 1 2 3) (2 1 4 2 5 3 6) (3 4 5 6)))

(defun torus-range (start length)
  (iter (for i from start to (+ start (1- length)))
	(collect i)))

(defun intersperse (lst1 lst2)
  (iter (for elt1 in lst1)
	(for elt2 in lst2)
	(collect elt1)
	(collect elt2)))

(defun torus-dessin (n m)
  (let ((torus-ranges (iter (for i from 1 to (* n (1- m)) by n)
			    (collect (torus-range i n)))))
    (let ((pre-res (iter (for lst1 in torus-ranges)
			 (for lst2 previous lst1)
			 (for i from 1)
			 (collect (cons i (intersperse lst2 lst1))))))
      (setf (car pre-res) (cons 1 (car torus-ranges)))
      (append pre-res
	      (list (cons (1+ (length torus-ranges))
			  (car (last torus-ranges))))))))

(defun print-dessin-poly (stream poly)  
  (format stream "0 ")
  (iter (for (nodes edges . factors) in poly)
	;; (format t "Nodes ~a edges ~a factors ~a~%" nodes edges factors)
	(format stream "+ ~{qnum~a~^ ~} (~a)"
		factors
		(if (null nodes)
		    "1"
		    (cl-ppcre:regex-replace-all "\\[" (guess-the-dessin (deserialize nodes edges)) "qnum[")))))

(defun frnl-dessin-poly (poly)
  (with-output-to-string (stream)
    (print-dessin-poly stream poly)))

(defun homfly-for-dessin (dessin)
  (let ((cube (cube-for-dessin dessin))
	(total-charge (color-charge dessin)))
    (with-output-to-string (stream)
      (format stream "(-q^N)^(~a) (" total-charge)
      (iter (for (charge polys) in-hashtable cube)
	    (iter (for (poly coeff) in-hashtable polys)
		  (format stream "+ (-1/q)^(~a) ~a (0 " charge coeff)
		  (print-dessin-poly stream poly)
		  (format stream ")")))
      (format stream ")"))))
		
    

;; Ok, I need to generate code for expressions for many HOMFLY of 3-sausages


(defun 3-sausage-homflies (n-max &optional (fname "~/code/superpolys/ThreeSausageHOMFLIES.m"))
  (with-open-file (stream fname :direction :output :if-exists :supersede)
    (iter (for n from 2 to n-max)
	  ;; (format stream "ThreeSausageHOMFLY[~a] := ~a;~%~%"
	  ;; 	  n (homfly-for-dessin (deserialize2 (torus-dessin 3 n))))
	  (format stream "FatSausageHOMFLY[~a] := ~a;~%~%"
		  n (homfly-for-dessin (deserialize2 (torus-dessin n 3))))))
  :success!)

;; OK, I need a way to persistently store values for graphs
;; Or, a way to recognize torusDessin
;; Or both

(defun correct-poses-p (poses)
  (let ((i (car poses)))
    (if (or (equal i 0) (equal i 1))
	(iter (for pose in (cdr poses))
	      (if (not (equal (incf i 2) pose))
		  (return nil))
	      (finally (return t))))))

(defun generate-new-toric-top-lst (lst)
  (let ((first (cdar lst))
	(second (cdadr lst)))
    (let ((poses (mapcar (lambda (x)
			   (position x second :test #'equal))
			 first)))
      ;; (format t "Poses are ~a~%" poses)
      (if (correct-poses-p poses)
	  (cons (caadr lst)
		(if (evenp (car poses))
		    (iter (for elt in (cdr second) by #'cddr)
			  (collect elt))
		    (iter (for elt in second by 'cddr)
			  (collect elt))))))))

(defun torus-dessin-p (lst)
  (cond ((equal 1 (length lst)) (equal 1 (length (car lst))))
	(t (labels ((rec (lst n m)
		      ;; (format t "Lst is ~a n is ~a m is ~a~%" lst n m)
		      (cond ((equal 1 (length lst)) (if (equal 1 (length (car lst)))
							(list n (1+ m))))
			    ((equal 2 (length lst)) (if (and (equal (1+ n) (length (cadr lst)))
							     (equal (cdar lst) (cdadr lst)))
							(list n (+ 2 m))))
			    (t (if (equal (1+ n) (length (car lst)))
				   (let ((new-lst (generate-new-toric-top-lst lst)))
				     ;; (format t "  New lst is ~a~%" new-lst)
				     (if new-lst
					 (rec (cons new-lst (cddr lst)) n (1+ m)))))))))
	     (rec lst (length (cdar lst)) 0)))))

(defparameter *5-dessin-1* '((1 1 2) (2 1 3 2 4 5) (3 3 6 4 7 5 8) (4 6 9 7 10 8) (5 9 10)))
(defparameter *5-dessin-2* '((1 1 2) (2 1 3 2 4) (3 3 5 4 6 7) (4 5 8 6 9 7 10) (5 8 9 10)))

(defparameter *4-dessin-1* '((1 1 2 3) (2 1 4 2 5 3 6) (3 4 7 5 8 6) (4 7 8)))
(defparameter *4-dessin-2* '((1 1 2 3 4) (2 1 5 2 6 3 7 4 8) (3 5 9 6 10 7 8) (4 9 10)))



(defun m-2-with-2-torus-blob (n shift)
  (let ((pre-res (make-array n :initial-element nil)))
    (iter (for i from 1 to (- (* 2 n) 2))
	  (push i (elt pre-res (mod (1- i) (1- n))))
	  (push i (elt pre-res (1+ (mod (1- i) (1- n))))))
    (push (1- (* 2 n)) (elt pre-res shift))
    (push (1- (* 2 n)) (elt pre-res (1+ shift)))
    (push (* 2 n) (elt pre-res (1+ shift)))
    (push (* 2 n) (elt pre-res (+ 2 shift)))
    (iter (for j from 1)
	  (for elt in-vector pre-res)
	  (collect (cons j (nreverse elt))))))

(defun velo-tori-file (nmax &optional (fname "~/code/superpolys/veloTori.m"))
  (with-open-file (stream fname :direction :output :if-exists :supersede)
    (iter (for n from 3 to nmax)
	  (iter (for shift from 0 to (- n 3))
		(format stream "veloToriDessin~an~a = ~a;~%" n shift
			(frnl-dessin-poly
			 (n-dessin-recursion
			  (deserialize2 (m-2-with-2-torus-blob n shift)))))))))
    

