
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
		    (iter (for (fun tag) in predicates)
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
  (let ((t-node (smart-q-unlink (cerr cell)))
	(b-node (smart-d-unlink (cerr cell))))
    (remove-the-nodes! cell (cerr cell))
    (dq-link t-node b-node)))

(defun ndo-virt-1-reidemeister (cell)
  (let ((t-node (smart-q-unlink (cqrr cell)))
	(b-node (smart-d-unlink cell)))
    (remove-the-nodes! cell (cqrr cell))
    (dq-link t-node b-node)))

(defun ndo-2.1-reidemeister (cell)
  (let ((lt-node (smart-q-unlink (cqrr cell)))
	(rt-node (smart-q-unlink (cqerr cell))))
    (remove-the-nodes! (q-unlink cell) (q-unlink (cerr cell)))
    (dq-link lt-node cell)
    (dq-link rt-node (cerr cell))))
  

(defun lousy-simplify-dessin (dessin)
  (let ((the-qed-dessin (deserialize-qed (serialize2 dessin t)))
	(n-factors 0)
	(n-1-factors 0)
	(2-factors 0)
	(min-one-factors 0))
    (iter (let ((plan (lousy-simplifiable-p the-qed-dessin)))
	    (cond ((not plan) (terminate))
		  ((eq :0-able (car plan))
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
    (values `((:n-factors . ,n-factors)
	      (:n-1-factors . ,n-1-factors)
	      (:2-factors . ,2-factors)
	      (:min-one-factors . ,min-one-factors))
	    the-qed-dessin)))

    
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

