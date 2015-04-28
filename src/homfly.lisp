
(in-package #:cl-vknots)

(cl-interpol:enable-interpol-syntax)

;; In this file we will write a proper HOMFLY calculation, which will be able to
;; withstand the strain of cabled diagrams (at least 2- and 3- cabled)



;; The iteration of all sub-dessins of a serialized dessin is very easy

;; This version with serialized dessins will not work, since I need to
;; *simultaneously* diable both halfs of each edge, and not one by one.
;; So I really need to do this with dessin d'enfant

(defparameter *the-dessin* nil)

(defparameter *torus-dessin* '((1 1 2) (2 1 3 2 4) (3 3 4)))

(defmacro new-charge (charge place)
  `(if top
       ,charge
       (cond ((consp ,place) (if (string= "B" (string (car ,place)))
				(1+ ,charge)
				(1- ,charge)))
	     (t (1+ ,charge)))))
	     

(defun %over-all-subdessins (dessin callback keep-edge-counter kill-edge-counter)
  (labels ((rec (more-edges charge)
	     ;; (format t "~a" (car more-edges))
	     (if (not more-edges)
		 (if callback (funcall callback dessin charge))
		 (progn (rec (cdr more-edges) (funcall keep-edge-counter (car more-edges) charge))
			(with-saved-edge-state (car more-edges)
			  (kill-edge (car more-edges))
			  (rec (cdr more-edges) (funcall kill-edge-counter (car more-edges) charge)))))))
    (rec (slot-value dessin 'edges) 0)
    :success!))

(defun count-edge-charge (edge charge)
  (if (eq :b (slot-value edge 'color))
      (1+ charge)
      (1- charge)))

(defun ignore-edge-charge (edge charge)
  (declare (ignore edge))
  charge)

(defun over-all-subdessins (dessin callback)
  (%over-all-subdessins dessin callback #'ignore-edge-charge #'count-edge-charge))

(defun over-all-actual-subdessins (dessin callback)
  (%over-all-subdessins dessin callback #'count-edge-charge #'ignore-edge-charge))

(let ((acc  nil))
  (defun reset-simple-collector ()
    (setf acc nil))
  (defun simple-collector (dessin charge)
    (push (list (serialize2 dessin) charge) acc))
  (defun output-simple-collector ()
    (let ((it (nreverse acc)))
      (reset-simple-collector)
      it)))

(defparameter lousy-predicates `((,#'reidemeister-1-able-p :1-able)
				 (,#'virt-reidemeister-1-able-p :virt-1-able)
				 (,#'reidemeister-2.1-able-p :2.1-able)))


(defun lousy-simplifiable-p (dessin)
  (with-slots (qed-cells) dessin
    (if (not qed-cells)
	(cons :0-able nil)
	(or (iter (for cell in qed-cells)
		  ;; Other transforms really do not work on loose dessins,
		  ;; so it's important to tighten first!
		  (if (tightable-p cell)
		      (return (cons :tight-able cell)))
		  (finally (return nil)))
	    (let ((res (make-hash-table)))
	      (iter outer (for cell in qed-cells)
		    (iter (for (fun tag) in lousy-predicates)
			  (let ((it (funcall fun cell)))
			    (when it
			      (push cell (gethash tag res))))))
	      (hash->assoc res))))))

(defun lousy-decompose (dessin)
  (multiple-value-bind (n-factors n-1-factors 2-factors min-one-factors qed-dessin)
      (lousy-simplify-dessin dessin)
    `(* ,@(if (not (zerop n-factors)) `((** (q "N") ,n-factors)))
	,@(if (not (zerop n-1-factors)) `((** (q "N-1") ,n-1-factors)))
	,@(if (not (zerop 2-factors)) `((** (q "2") ,2-factors)))
	,@(if (not (zerop min-one-factors)) `((** "-1" ,min-one-factors)))
	,(decompose qed-dessin))))

(defparameter the-qed-dessin nil)

(defun remove-the-nodes! (&rest nodes)
  (setf (slot-value the-qed-dessin 'qed-cells)
	(remove-if (lambda (x)
		     (find x nodes :test #'eq))
		   (slot-value the-qed-dessin 'qed-cells))))

(defun add-the-nodes! (&rest nodes)
  (iter (for node in nodes)
	(push node (slot-value the-qed-dessin 'qed-cells))))

(defun smart-q-unlink (cell)
  (push (q-grow cell) (slot-value the-qed-dessin 'qed-cells))
  (q-unlink cell))

(defun smart-d-unlink (cell)
  (push (d-grow cell) (slot-value the-qed-dessin 'qed-cells))
  (d-unlink cell))

(defun smart-q-shrink-all (cell)
  (let ((cells (q-shrink-all cell)))
    (setf (slot-value the-qed-dessin 'qed-cells)
	  (remove-if (lambda (x)
		       (find x cells :test #'eq))
		     (slot-value the-qed-dessin 'qed-cells)))))

(defun smart-d-shrink-all (cell)
  (let ((cells (d-shrink-all cell)))
    (setf (slot-value the-qed-dessin 'qed-cells)
	  (remove-if (lambda (x)
		       (find x cells :test #'eq))
		     (slot-value the-qed-dessin 'qed-cells)))))


(defun ndo-1-reidemeister (cell)
  (if (find cell (slot-value the-qed-dessin 'qed-cells) :test #'eq)
      (let ((t-node (smart-q-unlink (cerr cell)))
	    (b-node (smart-d-unlink (cerr cell))))
	(remove-the-nodes! cell (cerr cell))
	(dq-link t-node b-node)
	t)))

(defun ndo-virt-1-reidemeister (cell)
  (if (find cell (slot-value the-qed-dessin 'qed-cells) :test #'eq)
      (let ((t-node (smart-q-unlink (cqrr cell)))
	    (b-node (smart-d-unlink cell)))
	(remove-the-nodes! cell (cqrr cell))
	(dq-link t-node b-node)
	t)))

(defun ndo-2.1-reidemeister (cell)
  (if (find cell (slot-value the-qed-dessin 'qed-cells) :test #'eq)
      ;; we really need to remove all the relevant cells, otherwise
      ;; we risk to try to apply the transformation twice
      (let ((lt-node (smart-q-unlink (cqrr cell)))
	    (rt-node (smart-q-unlink (cqerr cell)))
	    (lb-node (smart-d-unlink cell))
	    (rb-node (smart-d-unlink (cerr cell))))
	(remove-the-nodes! (cqrr cell) (cqerr cell) (cerr cell) cell)
	(let ((new-cell (qed nil))
	      (new-cerr (qed nil)))
	  (add-the-nodes! new-cell new-cerr)
	  (ee-link new-cell new-cerr)
	  (dq-link lt-node new-cell)
	  (dq-link new-cell lb-node)
	  (dq-link rt-node new-cerr)
	  (dq-link new-cerr rb-node)
	  (smart-q-shrink-all new-cell)
	  (smart-d-shrink-all new-cell)
	  (smart-q-shrink-all new-cerr)
	  (smart-d-shrink-all new-cerr)
	  t))))
  

(defun lousy-simplify-dessin (dessin)
  (let ((the-qed-dessin (deserialize-qed (serialize2 dessin t)))
	(n-factors 0)
	(n-1-factors 0)
	(2-factors 0)
	(min-one-factors 0))
    (iter (let ((plan (lousy-simplifiable-p the-qed-dessin)))
	    (if-debug "LOUSY-SIMPLIFY-DESSIN: ~a" plan)
	    (cond ((or (not plan) (eq :0-able (car plan))) (terminate))
		  ((eq :tight-able (car plan))
		   (incf n-factors (%tighten-loops the-qed-dessin)))
		  (t (iter (for (tag . cells) in plan)
			   (cond ((eq :1-able tag)
				  (incf n-1-factors (iter (for cell in cells)
							  (if (ndo-1-reidemeister cell)
							      (summing 1)))))
				 ((eq :virt-1-able tag)
				  (let ((it (iter (for cell in cells)
						  (if (ndo-virt-1-reidemeister cell)
						      (summing 1)))))
				    (incf n-1-factors it)
				    (incf min-one-factors it)))
				 ((eq :2.1-able tag)
				  (incf 2-factors (iter (for cell in cells)
							(if (ndo-2.1-reidemeister cell)
							    (summing 1)))))
				 (t (error "Unknown tag ~a in this very specialized routine" tag))))))))
    (values n-factors n-1-factors 2-factors min-one-factors
	    the-qed-dessin)))


(defun flip-at-cell (cell)
  (let ((lb-node (smart-d-unlink cell))
	(rb-node (smart-d-unlink (cerr cell))))
    (dq-link cell rb-node)
    (dq-link (cerr cell) lb-node)
    (d-shrink cell)
    (d-shrink (cerr cell))
    :success!))
    

;; I need to know:
;;   * which nodes belong to the same loop
;;   * at which EE-links do every given two loops connect

;; Also, after simplification we may suddenly see that dessin is disconnected
;; -- then we must act accordingly - return list of places where individual dessins are located

(defun gen-hordization-hashes (qed-dessin)
  (let ((node->loop (make-hash-table :test #'eq))
	(loop->node (make-hash-table :test #'equal)))
    (let ((cells-hash (make-hash-table)))
      (iter (for cell in (slot-value qed-dessin 'qed-cells))
	    (setf (gethash cell cells-hash) t))
      (iter (for new-loop-start next (multiple-value-bind (got key val) (pophash cells-hash)
				       (declare (ignore val))
				       (if (not got)
					   (terminate)
					   key)))
	    (for loop-num from 1)
	    (iter (initially (setq cell nil))
		  (for cell next (if (not cell)
				     new-loop-start
				     (let ((it (cqrr cell)))
				       (cond ((not it) (error "Attempt to hordize dessin with broken loop"))
					     ((eq new-loop-start it) (terminate))
					     (t (remhash it cells-hash)
						it)))))
		  (setf (gethash cell node->loop) loop-num)
		  (push cell (gethash loop-num loop->node)))))
    ;; Now, do I have here all the information, that's required to successfully hordize?
    (list node->loop loop->node)))

(defun glue-loop (place node->loop loop->node)
  (let ((other-loop (gethash (cerr (car place)) node->loop))
	(this-loop (gethash (car place) node->loop)))
    (let ((new-cells (gethash other-loop loop->node)))
      (iter (for cell in new-cells)
	    (setf (gethash cell node->loop) this-loop))
      (setf (cdr (last new-cells)) (cdr place)
	    (cdr place) new-cells)
      (remhash other-loop loop->node)
      (flip-at-cell (car place))
      :success!)))
    
(defun qed-dessin->%%horde (dessin)
  (let ((cell-hash (make-hash-table))
	(start-cell nil))
    (iter (initially (setq cell nil))
	  (for cell next (if (not cell)
			     (setf start-cell (car (slot-value dessin 'qed-cells)))
			     (let ((next (cqrr cell)))
			       (if (eq next start-cell)
				   (terminate)
				   next))))
	  (for num from 1)
	  (if (not (cerr cell))
	      (error "The dessin is supposed to be tight at these stage of transformations!")
	      (let ((it (gethash (cerr cell) cell-hash)))
		(if it
		    (collect (list it num))
		    (setf (gethash cell cell-hash) num)))))))
			   

(defun hordize-dessin (dessin)
  (if (not (slot-value dessin 'qed-cells))
      '((0 :empty))
      (destructuring-bind (node->loop loop->node) (gen-hordization-hashes dessin)
	(if-debug "HORDIZE-DESSIN: ~a ~a ~a" (slot-value dessin 'qed-cells) node->loop loop->node)
	(iter (for (cur-loop-num cur-loop-cells) next (multiple-value-bind (got key val) (pophash loop->node)
							(if (not got)
							    (terminate)
							    (list key val))))
	      (if-debug "  ~a ~a" node->loop loop->node)
	      (let ((n-flips 0))
		(iter (initially (setq cell-place nil))
		      (for cell-place next (if-first-time cur-loop-cells
							  (if (not (cdr cell-place))
							      (terminate)
							      (cdr cell-place))))
		      (if-debug "  ~{~a~^ ~}" cell-place)
		      (when (and (cerr (car cell-place))
				 (not (equal cur-loop-num (gethash (cerr (car cell-place)) node->loop))))
			(if-debug "  ~a ~a" cur-loop-num (gethash (cerr (car cell-place)) node->loop))
			(glue-loop cell-place node->loop loop->node)
			(if-debug "  after glue: ~{~a~^ ~}" cell-place)
			(incf n-flips)))
		(if-debug "  after all glues: ~a" cur-loop-cells)
		(let ((it (make-instance 'qed-dessin :cells cur-loop-cells)))
		  (if-debug "  qed-dessin is ~a" (serialize-qed it))
		  (collect (list n-flips (%%horde->horde (qed-dessin->%%horde it))))))))))



(defun find-or-create-place (horde diags)
  (let ((reflected-horde (reflect-horde-diag horde))
	(old-diags (gethash (horde-length horde) diags)))
    (if-debug "FIND-OR-CREATE-PLACE: ~a ~a" old-diags (under-lst horde))
    (if (not old-diags)
	(let ((it (cons nil nil)))
	  (if-debug "  ~a" (under-lst horde))
	  (push (list horde it) (gethash (horde-length horde) diags))
	  it)
	(iter outer
	      (for diag1 n-in-diag-rotations horde)
	      (for diag2 n-in-diag-rotations reflected-horde)
	      (if-debug "    rotate ~a ~a" (under-lst diag1) (under-lst diag2))
	      (iter (for (old-diag place) in old-diags)
		    (if (or (horde-primitive-equal-p old-diag diag1)
			    (horde-primitive-equal-p old-diag diag2))
			(return-from outer place)))
	      (finally (let ((it (cons nil nil)))
			 (if-debug "  ~a" (under-lst horde))
			 (push (list horde it) (gethash (horde-length horde) diags))
			 (return-from outer it)))))))

(defun hordize-the-dessin! (diags)
  (iter (for (nflips horde) in (hordize-dessin the-qed-dessin))
	(collect (list nflips (find-or-create-place horde diags)))))
    


(let ((acc  nil)
      (diags (make-hash-table :test #'equal)))
  (defun reset-homfly-calculator ()
    (setf acc nil
	  diags (make-hash-table :test #'equal)))
  (defun homfly-calculator (dessin charge)
    (if-debug "HOMFLY CALCULATOR: considering new dessin ~a" (serialize2 dessin))
    (multiple-value-bind (n-factors n-1-factors 2-factors min-one-factors qed-dessin)
	(lousy-simplify-dessin dessin)
      (if-debug "Factors are: ~a ~a ~a ~a" n-factors n-1-factors 2-factors min-one-factors)
      (let ((the-qed-dessin qed-dessin))
	(push `(* ,@(if (not (zerop n-factors)) `((** (q "N") ,n-factors)))
		  ,@(if (not (zerop n-1-factors)) `((** (q "N-1") ,n-1-factors)))
		  ,@(if (not (zerop 2-factors)) `((** (q "2") ,2-factors)))
		  ,@(if (not (zerop min-one-factors)) `((** "-1" ,min-one-factors)))
		  ,@(if (not (zerop charge)) `((** "-1/q" ,charge)))
		  ,@(iter (for (nflips place) in (hordize-the-dessin! diags))
			  (collect `(* (** "-1" ,nflips) (diag ,place)))))
	      acc))))
  (defun homfly-calculator-different-hordes ()
    (iter (for (nil hordes) in-hashtable diags)
	  (appending (mapcar (lambda (x)
			       (if (eq (car x) :empty)
				   :empty
				   (slot-value (car x) 'under-lst)))
			     hordes))))
  (defun homfly-calculator-output-lame ()
    (iter (for (length diags) in-hashtable diags)
	  (iter (for (diag place) in diags)
		(setf (car place) (under-lst diag))))
    `(+ ,. acc))
  (defun raw-diags ()
    diags)
  (defun output-homfly-calculator ()
    (let ((it (progn more-magic!)))
      (reset-homfly-calculator)
      it)))

(defun frob ()
  (reset-homfly-calculator)
  (over-all-subdessins (deserialize2 (torus-dessin 3 3))
		       #'homfly-calculator))

(defun prehomfly (dessin)
  (reset-homfly-calculator)
  (over-all-subdessins dessin #'homfly-calculator)
  (color-charge dessin))

(defun prehomfly-actual (dessin)
  (reset-homfly-calculator)
  (over-all-actual-subdessins dessin #'homfly-calculator)
  (color-charge dessin))

(defun prehomfly-serial (serial-dessin)
  (prehomfly (deserialize2 serial-dessin)))

(defun prehomfly-actual-serial (serial-dessin)
  (prehomfly-actual (deserialize2 serial-dessin)))

(defun prehomfly-planar (planar-diagram)
  (prehomfly (planar->seifert planar-diagram)))

(defun lisp-serial-homfly (serial-dessin &optional (diag-fun #'try-to-decompose-diag))
  (let ((total-charge (prehomfly-serial serial-dessin)))
    (join "" (format nil "(-q^N)^(~a) (" total-charge)
	  (mathematica-serialize (homfly-calculator-output-lame) diag-fun)
	  ")")))

(defun lisp-actual-serial-homfly (serial-dessin &optional (diag-fun #'try-to-decompose-diag))
  (let ((total-charge (prehomfly-actual-serial serial-dessin)))
    (join "" (format nil "(q^(-N+1))^(~a) (" total-charge)
	  (mathematica-serialize (homfly-calculator-output-lame) diag-fun)
	  ")")))

  
(defun homfly-serial-toolchain (serial-dessin)
  (let ((pre-expr (lisp-serial-homfly serial-dessin)))
    (mathematica-simplify-and-canonicalize (list pre-expr))
    (joinl " " (iter (for expr in-file #?"$(*fname-prefix*)lisp-in.txt" using #'read-line)
		     (collect expr)))))

(defun homfly-actual-serial-toolchain (serial-dessin)
  (let ((pre-expr (lisp-actual-serial-homfly serial-dessin)))
    (mathematica-simplify-and-canonicalize (list pre-expr))
    (joinl " " (iter (for expr in-file #?"$(*fname-prefix*)lisp-in.txt" using #'read-line)
		     (collect expr)))))


(defun substitute-q-numbers (lst)
  (mathematica-bulk-exec expr #?"$(*fname-prefix*)substitute-q-values.m" lst))

(defun substitute-q-numbers1 (expr)
  (car (substitute-q-numbers (list expr))))

(defun %compare-q-exprs (lst script-name)
  (mathematica-bulk-exec (expr1 expr2) #?"$(script-name)" lst))

(defun compare-q-exprs (lst)
  (%compare-q-exprs lst #?"$(*fname-prefix*)compare-q-exprs.m"))

(defun compare-q-exprs-minus (lst)
  (%compare-q-exprs lst #?"$(*fname-prefix*)compare-q-exprs-minus.m"))

(defun compare-q-exprs1 (expr1 expr2)
  (car (compare-q-exprs `((,expr1 ,expr2)))))

(defun compare-q-exprs-minus1 (expr1 expr2)
  (car (compare-q-exprs-minus `((,expr1 ,expr2)))))


(defun homfly-old-new-compare (serial-dessin)
  (compare-q-exprs1 (homfly-for-dessin (deserialize2 serial-dessin))
		    (homfly-serial-toolchain serial-dessin)))

(defun homfly-old-new-min-compare (serial-dessin)
  (compare-q-exprs-minus1 (homfly-for-dessin (deserialize2 serial-dessin))
			  (homfly-serial-toolchain serial-dessin)))

(defun wm-torus-knot (n m)
  #?"TorusKnot[$(n), $(m)]")

;; (defrule integer ()
;;   (text (list (? (|| #\+ #\-))
;; 	      (postimes (character-ranges (#\0 #\9))))))

;; (defrule wm-simple-int-list ()
;;   (mapcar (lambda (x)
;; 	    (parse-integer x))
;; 	  (progm #\{ (cons integer (times (progn ", " integer))) #\})))

;; (defrule wm-braid ()
;;   (let (total lst)
;;     "BR[" (setf total integer) ", " (setf lst wm-simple-int-list) "]"
;;     `(,(parse-integer total) ,@lst)))

(defun lame-parse-braid (x)
  (let ((lst (cl-ppcre:split ", " (subseq x 3 (1- (length x))))))
    (setf (cadr lst) (subseq (cadr lst) 1))
    (setf (car (last lst)) (subseq (car (last lst)) 0 (1- (length (car (last lst))))))
    (mapcar #'parse-integer lst)))

(defun get-braid-reps (lst)
  (mapcar (lambda (x)
	    ;; (format t "~a~%" x)
	    ;; (parse 'wm-braid x))
	    (lame-parse-braid x))
	  (mathematica-bulk-exec expr #?"$(*fname-prefix*)get-knots-braid.m" lst)))
(defun get-braid-rep1 (expr)
  (car (get-braid-reps (list expr))))

(defun braid->planar (braid)
  (destructuring-bind (total . specs) braid
    (let ((cur-arcs (coerce (iter (for i from 1 to total) (collect i)) 'vector))
	  (last-num total)
	  res)
      (iter (for spec in specs)
	    (let ((index (1- (abs spec))))
	      (let ((lb (elt cur-arcs index))
		    (rb (elt cur-arcs (1+ index)))
		    (lt (setf (elt cur-arcs index) (incf last-num)))
		    (rt (setf (elt cur-arcs (1+ index)) (incf last-num))))
		(push `(,(if (> spec 0) :b :w) ,lb ,rb ,lt ,rt) res))))
      (iter (for i from 1)
	    (for elt in-vector cur-arcs)
	    (push `(:d ,elt ,i) res))
      res)))
			 
(defun compare-homfly-with-katlas (lst)
  (let ((braids (get-braid-reps lst)))
    (mathematica-bulk-exec (expr1 expr2) #?"$(*fname-prefix*)compare-homfly-with-katlas.m"
			   (mapcar (lambda (x y)
				     (list (homfly-serial-toolchain (planar->seifert (braid->planar x)))
					    y))
				   braids lst))))

(defun compare-actual-homfly-with-katlas (lst)
  (let ((braids (get-braid-reps lst)))
    (mathematica-bulk-exec (expr1 expr2) #?"$(*fname-prefix*)compare-actual-homfly-with-katlas.m"
			   (mapcar (lambda (x y)
				     (list (homfly-actual-serial-toolchain (planar->seifert (braid->planar x)))
					    y))
				   braids lst))))


(defun compare-homfly-with-katlas1 (knot)
  (car (compare-homfly-with-katlas (list knot))))

(defun compare-actual-homfly-with-katlas1 (knot)
  (car (compare-actual-homfly-with-katlas (list knot))))

;; OK, now I need this code also to:
;; * (done) take into account the cons-cells, that can be in place of just numbers
;; * (done) calculate the q-charge of the sub-dessin as it goes along


;; OK, what's next?
;; Next I would like to do something more substantial with resulting dessins, rather
;; than just collecting the serialized versions
;; Namely, I would like:
;; * (done, untested) simplify the dessin *monomially* (i.e., only recognizing loops, [N-1]- and [2]- moves) as
;;   much as possible
;; * (done) a way to apply all found lousy simplifications in one go
;; * somehow classify the remnants, such as not to do double job, when calculating them.
;;   * (done, untested) bring qed-dessin to some chord diagram form
;;   * (done, untested) through rotations and reflections bring it to some already occured form
;;   * (done, untested) arrange somehow,
;;     that change to one place will automatically change value of dessin in all the others


;; Now I have polynomials of lousily simplified horde diagrams, I want to promote them
;; to honest HOMFLY polynomials in an efficient way. How do I do that? What can I use?
;; * the large part of effort should be put into memoization and into persistence of answers
;;   * how do I store answers?
;;   * how do I recognize that answer was already calculated somewhere?


;; (-q^N)^(2)
;;  (q[N]^3 * (-1/q)^2
;;   + (q[N]^2 * ((q[N-1])^(2)) * ((-1/q)^(1)) * (((-1)^(0)) * (1))) + (((q[N])^(2)) * ((q[N-1])^(2)) * ((-1/q)^(1)) * (((-1)^(0)) * (1))) + (((q[N])^(1)) * ((q[N-1])^(1)) * (((-1)^(0)) * (1))))"

;; + (-1/q)^(0) 1 qnum[N] qnum[N-1] qnum[N-1]
;; + (-1/q)^(1) 2 qnum[N] qnum[N-1] qnum[N]
;; + (-1/q)^(2) qnum[N] qnum[N] qnum[N]

;; (-q^N)^(1)
;; (+ q[N]^2 * (-1/q)^1
;;    + q[N] * q[N-1] + q[N] * q[N-1]
;;    + q[N] * q[N-1] * (-1/q)^2
;;    + q[N] * q[N-1] * q[2] * (-1/q)^(1) + q[N] * q[N-1] * q[2] * (-1/q)^(1)
;;    + q[N] * q[N-1] * q[2] * (-1/q)^(-1)
;;    + q[N] * q[N-1] * q[2]^2)

;; (-q^N)^(1)
;; (+ (-1/q)^(1) 1 qnum[N] qnum[N]
;;    + (-1/q)^(0) 2 qnum[N] qnum[N-1]
;;    + (-1/q)^(2) 1 qnum[N] qnum[N-1]
;;    + (-1/q)^(1) 2 qnum[N] qnum[N-1] qnum[2]
;;    + (-1/q)^(-1) 1 qnum[N] qnum[N-1] qnum[2]
;;    + (-1/q)^(0) qnum[N] qnum[N-1] qnum[2] qnum[2]
;;    )

(defparameter *rolfsen-total-numbers* '((3 . 1) (4 . 1) (5 . 2) (6 . 3) (7 . 7) (8 . 21) (9 . 49) (10 . 165)))
  
