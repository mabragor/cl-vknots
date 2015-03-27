
(in-package #:cl-vknots)


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
	     

(defun over-all-subdessins (dessin callback)
  (labels ((rec (more-edges charge)
	     ;; (format t "~a" (car more-edges))
	     (if (not more-edges)
		 (if callback (funcall callback dessin charge))
		 (progn (rec (cdr more-edges) (if (eq :b (slot-value (car more-edges) 'color))
						    (1+ charge)
						    (1- charge)))
			(with-saved-edge-state (car more-edges)
			  (kill-edge (car more-edges))
			  (rec (cdr more-edges) charge))))))
    (rec (slot-value dessin 'edges) 0)
    :success!))


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

(defun hash->assoc (hash)
  (iter (for (key val) in-hashtable hash)
	(collect (cons key val))))

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


(defparameter the-qed-dessin nil)

(defun remove-the-nodes! (&rest nodes)
  (setf (slot-value the-qed-dessin 'qed-cells)
	(remove-if (lambda (x)
		     (find x nodes :test #'eq))
		   (slot-value the-qed-dessin 'qed-cells))))

(defun smart-q-unlink (cell)
  (push (q-grow cell) (slot-value the-qed-dessin 'qed-cells))
  (q-unlink cell))

(defun smart-d-unlink (cell)
  (push (d-grow cell) (slot-value the-qed-dessin 'qed-cells))
  (d-unlink cell))


(defun ndo-1-reidemeister (cell)
  (if (find cell (slot-value the-qed-dessin 'qed-cells) :test #'eq)
      (let ((t-node (smart-q-unlink (cerr cell)))
	    (b-node (smart-d-unlink (cerr cell))))
	(remove-the-nodes! cell (cerr cell))
	(dq-link t-node b-node))))

(defun ndo-virt-1-reidemeister (cell)
  (if (find cell (slot-value the-qed-dessin 'qed-cells) :test #'eq)
      (let ((t-node (smart-q-unlink (cqrr cell)))
	    (b-node (smart-d-unlink cell)))
	(remove-the-nodes! cell (cqrr cell))
	(dq-link t-node b-node))))

(defun ndo-2.1-reidemeister (cell)
  (if (find cell (slot-value the-qed-dessin 'qed-cells) :test #'eq)
      (let ((lt-node (smart-q-unlink (cqrr cell)))
	    (rt-node (smart-q-unlink (cqerr cell))))
	(remove-the-nodes! (q-unlink cell) (q-unlink (cerr cell)))
	(dq-link lt-node cell)
	(dq-link rt-node (cerr cell)))))
  

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
				  (incf n-1-factors (length cells))
				  (mapc #'ndo-1-reidemeister cells))
				 ((eq :virt-1-able tag)
				  (incf n-1-factors (length cells))
				  (incf min-one-factors (length cells))
				  (mapc #'ndo-virt-1-reidemeister cells))
				 ((eq :2.1-able tag)
				  (incf 2-factors (length cells))
				  (mapc #'ndo-2.1-reidemeister cells))
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
    (if-debug "HOMFLY CALCULATOR: considering new dessin ~a" dessin)
    (multiple-value-bind (n-factors n-1-factors 2-factors min-one-factors qed-dessin)
	(lousy-simplify-dessin dessin)
      (let ((the-qed-dessin qed-dessin))
	(push `(* ,@(if (not (zerop n-factors)) `((** (q "N") ,n-factors)))
		  ,@(if (not (zerop n-1-factors)) `((** (q "N-1") ,n-factors)))
		  ,@(if (not (zerop 2-factors)) `((** (q "2") ,n-factors)))
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


