
(in-package #:cl-vknots)

;; TADA!

(cl-interpol:enable-interpol-syntax)

(defclass qed-dessin ()
  ((qed-cells :initarg :cells)))

(defclass qed-marked-dessin (qed-dessin)
  ((cycles)
   (cycle-hash)))


(defmethod copy-dessin ((dessin qed-dessin))
  (let ((qed-cells-hash (make-hash-table))
	(qed-cells-reverse-hash (make-hash-table))
	(new-qed-cells nil))
    (labels ((new-cell-for-cell (cell)
	       (let ((it (gethash cell qed-cells-hash)))
		 (or it
		     (let ((it (qed nil)))
		       (push it new-qed-cells)
		       (setf (gethash cell qed-cells-hash) it
			     (gethash it qed-cells-reverse-hash) cell)
		       it))))
	     (copy-connections (new-cell cell)
	       (if (not (cqrr new-cell))
		   (dq-link (new-cell-for-cell (cqrr cell))
			    new-cell))
	       (if (not (cdrr new-cell))
		   (qd-link (new-cell-for-cell (cdrr cell))
			    new-cell))
	       (if (not (cerr new-cell))
		   (ee-link (new-cell-for-cell (cerr cell))
			    new-cell))))
      (iter (for cell in (slot-value dessin 'qed-cells))
	    (let ((new-cell (new-cell-for-cell cell)))
	      (copy-connections new-cell cell)))
      (make-instance 'qed-dessin :cells new-qed-cells))))


(defun reidemeister-1-able-p (qed-cell)
  (eq (cqrr qed-cell) qed-cell))

(defun reidemeister-2.2-able-p (qed-cell)
  (let ((q-cell (cqrr qed-cell))
	(d-cell (cdrr qed-cell)))
    (and (not (eq q-cell qed-cell))
	 (eq q-cell d-cell))))

(defun reidemeister-2.1-able-p (qed-cell)
  (and (not (eq (cqrr qed-cell) qed-cell))
       (eq (ceqrr qed-cell) (cqerr qed-cell))))

(defun qed-valency (qed-cell)
  "Number of outgoing E edges in QD-loop of the current qed-cell, or :LOOPS,
if cells QD-loop has E-loops"
  (let ((encountered (make-hash-table)))
    (iter (initially (setq cell nil))
	  (for cell next (if (eq cell qed-cell)
			     (terminate)
			     (cqrr (or cell qed-cell))))
	  (if (gethash (cerr cell) encountered)
	      (return-from qed-valency :loops))
	  (setf (gethash cell encountered) t)
	  (summing 1))))

(defun reidemeister-3.1-able-p (qed-cell)
  (and (not (eq (cqrr qed-cell) qed-cell))
       (eq (ceqrr qed-cell)
	   (cqqerr qed-cell))))

(defun reidemeister-3.2-able-p (qed-cell)
  (equal 3 (qed-valency qed-cell)))

(defun pophash (hash)
  (with-hash-table-iterator (iter hash)
    (multiple-value-bind (got key val) (iter)
      (if got
	  (remhash key hash))
      (values got key val))))


;; (defun mark-dessin (dessin)
;;   (let ((dessin (if (typep dessin 'qed-dessin)
;; 		    (make-instance 'qed-marked-dessin :cells (slot-value dessin 'qed-cells))
;; 		    dessin)))
;;     (let ((cells-hash (make-hash-table)))
;;       (iter (for cell in (slot-value dessin 'qed-cells))
;; 	    (setf (gethash cell cells-hash) t))
;;       (iter (for new-loop-start next (multiple-value-bind (got key val) (pophash cells-hash)
;; 				       (if (not got)
;; 					   (terminate)
;; 					   key)))
;; 	    (for loop-num from 1)
;; 	    (iter (initially (setq cell nil))
;; 		  (for cell next (if (not cell)
;; 				     new-loop-start
;; 				     (let ((it (cqrr cell)))
;; 				       (if (eq new-loop-start it)
;; 					   (terminate)
;; 					   it))))
;; 		  (for cell-num from 1)
;;     dessin))

	  

;; (defun dessin-full-analysis (qed-dessin)
;;   (


(defun easy-analyze-dessin (dessin)
  (let ((reidemeister-1-able nil)
	(reidemeister-2.1-able nil)
	(reidemeister-2.2-able nil)
	(reidemeister-3.1-able nil)
	(reidemeister-3.2-able nil))
    (iter (for cell in (slot-value dessin 'qed-cells))
	  (if (reidemeister-1-able-p cell)
	      (push cell reidemeister-1-able))
	  (if (reidemeister-2.1-able-p cell)
	      (push cell reidemeister-2.1-able))
	  (if (reidemeister-2.2-able-p cell)
	      (push cell reidemeister-2.2-able))
	  (if (reidemeister-3.1-able-p cell)
	      (push cell reidemeister-3.1-able))
	  (if (reidemeister-3.2-able-p cell)
	      (push cell reidemeister-3.2-able)))
    `((:1-able . ,reidemeister-1-able)
      (:2.1-able . ,reidemeister-2.1-able)
      (:2.2-able . ,reidemeister-2.2-able)
      (:3.1-able . ,reidemeister-3.1-able)
      (:3.2-able . ,reidemeister-3.2-able))))

(defun 3.1-drift-points (dessin &optional used-points)
  (let ((reidemeister-3.1-able nil))
    (iter (for cell in (slot-value dessin 'qed-cells))
	  (if (and (or (not used-points)
		       (not (gethash cell used-points)))
		   (reidemeister-3.1-able-p cell))
	      (push cell reidemeister-3.1-able)))
    reidemeister-3.1-able))

(defun 3.1-drift (cell)
  (let ((lb-cell (d-unlink cell))
	(lt-cell (q-unlink (cqrr cell)))
	(rb-cell (d-unlink (ceqerr cell)))
	(rt-cell (q-unlink (ceqerr cell))))
    (dq-link rt-cell (cqrr cell))
    (dq-link cell rb-cell)
    (dq-link lt-cell (ceqerr cell))
    (dq-link (ceqerr cell) lb-cell)
    cell))

(defmacro! with-3.1-drift ((o!-cell) &body body)
  `(unwind-protect (progn (3.1-drift ,o!-cell)
			  ,@body)
     (3.1-drift ,o!-cell)))

(defun simplifiable-p (dessin)
  (with-slots (qed-cells) dessin
    (if (not qed-cells)
	(cons :0-able nil)
	(iter (for cell in qed-cells)
	      (if (reidemeister-1-able-p cell)
		  (return (cons :1-able cell)))
	      (if (reidemeister-2.1-able-p cell)
		  (return (cons :2.1-able cell)))
	      (if (reidemeister-2.2-able-p cell)
		  (return (cons :2.2-able cell)))
	      (finally (return nil))))))

  

(defun deserialize-qed (lst)
  (let ((cells nil)
	(encountered (make-hash-table :test #'equal)))
    (iter (for (num . cycle) in lst)
	  (format t "Loop num ~a~%" num)
	  (let ((the-loop nil)
		(first-cell nil))
	    (iter (for edge-num in cycle)
		  (format t "  edge num ~a, loop ~a~%" edge-num the-loop)
		  (let ((new-cell (qed nil)))
		    (push new-cell cells)
		    (setf the-loop (dq-link! new-cell the-loop))
		    (if-first-time (setf first-cell the-loop))
		    (let ((old-cell (gethash edge-num encountered)))
		      (if old-cell
			  (ee-link new-cell old-cell)
			  (setf (gethash edge-num encountered) new-cell)))))
	    (dq-link! first-cell the-loop)))
    (make-instance 'qed-dessin :cells cells)))
	  

(defmacro with-used-point ((o!-point) &body body)
  `(unwind-protect (progn (setf (gethash ,o!-point used-points) t)
			  ,@body)
     (remhash ,o!-point used-points)))


(defun depth-first-3.1-drift-to-simplifiable (dessin)
  (let ((used-points (make-hash-table)))
    (labels ((rec (path)
	       (let ((it (simplifiable-p dessin)))
		 (if it
		     (list :yes! (nreverse (cons it path)))
		     (iter over-drift-points
			   (for drift-point in (3.1-drift-points dessin used-points))
			   (with-used-point (drift-point)
			     (with-3.1-drift (drift-point)
			       (let ((it (rec (cons drift-point path))))
				 (if it
				     (return-from over-drift-points it)))))
			   (finally (return-from over-drift-points nil)))))))
      (rec nil))))

;; (defgeneric find-3.1-drift-to-simplifiable (smth)
;;   (:documentation "Find sequence of 3.1 Reidemeister moves, which converts a given diagram
;; into simplifiable one"))

;; (defun find-3.1-drift-to-simplifiable ((lst list))
;;   (iter (for path in lst)
;; 	(destructuring-bind (dessin last-node-used used-nodes) (car path)
;; 	  (let ((drift-points (3.1-drift-points dessin used-points)))
;; 	    (iter (for drift-point in drift-points)
;; 		  (multiple-value-bind (copy-dessin copy-drift-point copy-used-points)
;; 		      (copy-dessin-with-marked-points dessin drift-point used-points)
;; 		    (3.1-drift copy-drift-point)
;; 		    ;; 
;; 		    (let ((it (simplifiable-p copy-dessin)))
;; 		      (if (not it)
;; 			  (progn (gethash used-points
;;   ...)

;; (defmethod find-3.1-drift-to-simplifiable ((dessin qed-dessin))
;;   (find-3.1-drift-to-simplifiable (list (cons dessin (make-hash-table)))))


;; OK, now it's time to actually write the decomposer

(defmacro! with-removed-nodes ((&rest nodes) o!-dessin &body body)
  (let ((gensyms (mapcar (lambda (x) (declare (ignore x)) (gensym "REM-NODE")) nodes)))
    `(let ,(mapcar (lambda (x y)
		     `(,x ,y))
		   gensyms nodes)
       (unwind-protect (progn (setf (slot-value ,o!-dessin 'qed-cells)
				    (remove-if (lambda (x)
						 (or ,@(mapcar (lambda (x)
								 `(eq ,x x))
							       gensyms)))
					       (slot-value ,o!-dessin 'qed-cells)))
			      ,@body)
	 ,@(mapcar (lambda (x)
		     `(push ,x (slot-value ,o!-dessin 'qed-cells)))
		   gensyms)))))

(defmacro! with-added-nodes ((&rest nodes) o!-dessin &body body)
  (let ((gensyms (mapcar (lambda (x) (declare (ignore x)) (gensym "NEW-NODE")) nodes)))
    `(let ,(mapcar (lambda (x y)
		     `(,x ,y))
		   gensyms nodes)
       (unwind-protect (progn ,@(mapcar (lambda (x)
					  `(push ,x (slot-value ,o!-dessin 'qed-cells)))
					gensyms)
			      ,@body)
	 (setf (slot-value ,o!-dessin 'qed-cells)
	       (remove-if (lambda (x)
			    (or ,@(mapcar (lambda (x)
					    `(eq ,x x))
					  gensyms)))
			  (slot-value ,o!-dessin 'qed-cells)))))))


(defmacro! with-grown-nodes ((&rest node-specs) o!-dessin &body body)
  (let ((gensyms (mapcar (lambda (x)
			   (declare (ignore x))
			   (list (gensym "NODE-TO-GROW") (gensym "GROWN-NODE")))
			 node-specs)))
    `(let ,(mapcar (lambda (x y)
		     `(,(car x) ,(cadr y)))
		   gensyms node-specs)
       (let ,(mapcar #'cadr gensyms)
	 (unwind-protect (progn ,@(mapcar (lambda (x y)
					    `(setf ,(cadr x)
						   (,(intern #?"$((string (car y)))-GROW")
						     ,(car x))))
					  gensyms node-specs)
				(with-added-nodes ,(mapcar #'cadr gensyms) ,o!-dessin
				  ,@body))
	   ,@(mapcar (lambda (x y)
		       `(,(intern #?"$((string (car y)))-SHRINK") ,(car x) ,(cadr x)))
		     gensyms node-specs))))))


(defmacro! with-severed-links ((&rest link-specs) o!-dessin &body body)
  (let ((gensyms (mapcar (lambda (x) (declare (ignore x)) (gensym "THIS-LINK-END")) link-specs)))
    `(let ,(mapcar (lambda (x y)
		     `(,x ,(cadr y)))
		   gensyms link-specs)
       (with-grown-nodes ,(mapcar (lambda (x y)
				    (list (car x) y))
				  link-specs gensyms) ,o!-dessin
	 (with-severed-links! ,(mapcar (lambda (x y)
					 (list (car x) y (caddr x)))
				       link-specs gensyms)
	   ,@body)))))

(defmacro with-severed-links! ((&rest link-specs) &body body)
  (let ((gensyms (mapcar (lambda (x) (declare (ignore x)) (gensym "THIS-LINK-END")) link-specs))
	(vars (mapcar (lambda (x)
			(or (caddr x)
			    (gensym "OTHER-LINK-END")))
		      link-specs)))
    `(let ,(mapcar (lambda (x y)
		     `(,x ,(cadr y)))
		   gensyms link-specs)
       (let ,(mapcar (lambda (x y z)
		       `(,z (,(intern #?"$((string (car x)))-UNLINK") ,y)))
		     link-specs gensyms vars)
	 (unwind-protect (progn ,@body)
	   ,@(mapcar (lambda (x y z)
		       (let ((op (cond ((eq 'q (car x)) 'dq)
				       ((eq 'd (car x)) 'qd)
				       ((eq 'e (car x)) 'ee)
				       (t (error "Unknown type of linking: ~a" (car x))))))
			 `(,(intern #?"$((string op))-LINK") ,z ,y)))
		     link-specs gensyms vars))))))
  

(defmacro with-tmp-links ((&rest link-specs) &body body)
  (let ((gensyms (mapcar (lambda (x)
			   (declare (ignore x))
			   (list (gensym "LEFT-NODE") (gensym "RIGHT-NODE")))
			 link-specs)))
    `(let (,@(mapcar (lambda (x y)
		       `(,(car x) ,(cadr y)))
		     gensyms link-specs)
	   ,@(mapcar (lambda (x y)
		       `(,(cadr x) ,(caddr y)))
		     gensyms link-specs))
       ,@(mapcar (lambda (x y)
		   `(,(intern #?"$((string (car x)))-LINK") ,(car y) ,(cadr y)))
		 link-specs gensyms)
       (unwind-protect (progn ,@body)
	 ,@(mapcar (lambda (x y)
		     (let ((op (cond ((eq 'qd (car x)) 'q)
				     ((eq 'dq (car x)) 'd)
				     ((eq 'ee (car x)) 'e)
				     (t (error "Unknown type of linking: ~a" (car x))))))
		       `(,(intern #?"$((string op))-UNLINK") ,(car y))))
		   link-specs gensyms)))))


(defun do-0-reidemeister (qed-dessin node)
  "Fake Reidemeister move, to substitute empty dessin with 1"
  (declare (ignore node qed-dessin))
  "1")
  

(defun do-1-reidemeister (qed-dessin node)
  (with-slots (qed-dessins) qed-dessin
    (let ((res nil))
      (with-severed-links ((q (cerr node) t-node)
			   (d (cerr node) b-node)) qed-dessin
	(with-removed-nodes (node (cerr node)) qed-dessin
	  (with-tmp-links ((dq t-node b-node))
	    (setf res (tighten-loops (copy-dessin qed-dessin))))))
      `(* (q "N-1") ,res))))

(defun do-2.1-reidemeister (qed-dessin node)
  (with-slots (qed-dessins) qed-dessin
    (let ((res nil))
      (with-severed-links ((q (cqrr node) lt-node)
			   (d node lb-node)
			   (q (ceqrr node) rt-node)
			   (d (cerr node) rb-node))
	(with-removed-nodes (node (cqrr node) (ceqrr node) (cerr node)) qed-dessin
	  (let ((tmp-l-node (qed nil))
		(tmp-r-node (qed nil)))
	    (ee-link tmp-l-node tmp-r-node)
	    (with-added-nodes (tmp-l-node tmp-r-node) qed-dessin
	      (with-tmp-links ((dq lt-node tmp-l-node)
			       (dq rt-node tmp-r-node)
			       (dq tmp-l-node lb-node)
			       (dq tmp-r-node rb-node))
		(setf res `(* (q "2") ,(tighten-loops (copy-dessin qed-dessin)))))))))
      res)))

(defun do-2.2-reidemeister (qed-dessin node)
  (with-slots (qed-dessins) qed-dessin
    (let ((res-forget nil)
	  (res-contract nil))
      (with-severed-links ((q (cerr node) lt-node)
			   (d (cerr node) lb-node)
			   (q (ceqrr node) rt-node)
			   (d (ceqrr node) rb-node))
	(with-removed-nodes (node (cqrr node) (cerr node) (ceqrr node)) qed-dessin
	  (with-tmp-links ((dq lt-node lb-node)
			   (dq rt-node rb-node))
	    (setf res-forget (tighten-loops (copy-dessin qed-dessin))))
	  (with-tmp-links ((dq lt-node rb-node)
			   (dq rt-node lb-node))
	    (setf res-contract (tighten-loops (copy-dessin qed-dessin))))))
      `(+ (* (q "N-2") ,res-forget)
	  ,res-contract))))



(defun do-3.1-reidemeisters-then-something-else (qed-dessin plan)
  (if (equal 1 (length plan))
      (cond ((eq :0-able (caar plan)) (do-0-reidemeister qed-dessin (cadar plan)))
	    ((eq :1-able (caar plan)) (do-0-reidemeister qed-dessin (cadar plan)))
	    ((eq :2.1-able (caar plan)) (do-2.1-reidemeister qed-dessin (cadar plan)))
	    ((eq :2.2-able (caar plan)) (do-2.2-reidemeister qed-dessin (cadar plan))))
      (%do-3.1-reidemeisters-then-something-else qed-dessin plan)))

(defun %do-3.1-reidemeisters-then-something-else (qed-dessin plan)
  (let ((node (car plan)))
    (with-slots (qed-dessins) qed-dessin
      (let ((res-leave-left nil)
	    (res-leave-right nil))
	(with-severed-links ((q (cqrr node) lt-node)
			     (d node lb-node)
			     (q (ceqrr node) ct-node)
			     (d (cerr node) cb-node)
			     (q (ceqerr node) rt-node)
			     (d (ceqerr node) rb-node))
	  (with-removed-nodes (node (cqrr node)
				    (cerr node) (cqerr node) (cqqerr node)
				    (ceqerr node)) qed-dessin
	    (let ((tmp-l-node (qed nil))
		  (tmp-r-node (qed nil)))
	      (ee-link tmp-l-node tmp-r-node)
	      (with-added-nodes (tmp-l-node tmp-r-node) qed-dessin
		(with-tmp-links ((dq lt-node tmp-l-node)
				 (dq ct-node tmp-r-node)
				 (qd lb-node tmp-l-node)
				 (qd cb-node tmp-r-node)
				 (dq rt-node rb-node))
		  (setf res-leave-left (tighten-loops (copy-dessin qed-dessin))))
		(with-tmp-links ((dq ct-node tmp-l-node)
				 (dq rt-node tmp-r-node)
				 (qd cb-node tmp-l-node)
				 (qd rb-node tmp-r-node)
				 (dq lt-node lb-node))
		  (setf res-leave-right (tighten-loops (copy-dessin qed-dessin))))))))
	;; TODO: shouldn't it be also under growed outgoing links?
	(3.1-drift node)
	`(+ ,(do-3.1-reidemeisters-then-something-else qed-dessin (cdr plan))
	    ,res-leave-left
	    (- ,res-leave-right))))))


;; So, now I need to find a way to *completely* decompose qed-dessin
;; not make just one step.

(defparameter *accumulator* nil)

(defun %find-cons-dessins (poly)
  (if poly
      (progn (if (typep (car poly) 'qed-dessin)
		 (push poly *accumulator*)
		 (if (consp (car poly))
		     (%find-cons-dessins (car poly))))
	     (%find-cons-dessins (cdr poly)))))
      

(defun find-cons-dessins (dessin-poly)
  (let ((*accumulator* nil))
    (%find-cons-dessins dessin-poly)
    *accumulator*))

(defun decomposition-step (cons-of-dessin)
  (let ((plan (depth-first-3.1-drift-to-simplifiable (car cons-of-dessin))))
    (format t "~a~%" plan)
    (if (not plan)
	(error "Unable to find a decomposition plan!")
	(let ((new-stuff (do-3.1-reidemeisters-then-something-else (car cons-of-dessin) (cdr plan))))
	  (let ((cons-dessins (find-cons-dessins new-stuff)))
	    (setf (car cons-of-dessin) new-stuff)
	    cons-dessins)))))

(defun decompose (dessin)
  (let ((head (list dessin)))
    (let ((conses-of-dessins (list head)))
      (iter (for i from 1 to 10)
	    (format t "~a~%" head)
	    (setf conses-of-dessins
		  (apply #'append (remove-if-not #'identity
						 (mapcar #'decomposition-step conses-of-dessins))))
	    (if (not conses-of-dessins)
		(terminate))))
    head))

(defun tighten-loops (dessin)
  (with-slots (qed-cells) dessin
    (let ((new-qed-cells nil)
	  (num-loops 0))
      (iter (for cell in qed-cells)
	    (if (cerr cell)
		(push cell new-qed-cells)
		(if (eq (cqrr cell) cell)
		    (incf num-loops)
		    (let ((q-cell (q-unlink cell))
			  (d-cell (d-unlink cell)))
		      (dq-link q-cell d-cell)))))
      (setf qed-cells new-qed-cells)
      (if (equal 0 num-loops)
	  dessin
	  `(* (** "[N]" ,num-loops) ,dessin)))))
		

