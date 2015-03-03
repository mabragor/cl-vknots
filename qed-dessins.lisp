
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
  (iter (for cell in (slot-value dessin 'qed-cells))
	(if (reidemeister-1-able-p cell)
	    (return (cons :1-able cell)))
	(if (reidemeister-2.1-able-p cell)
	    (return (cons :2.1-able cell)))
	(if (reidemeister-2.2-able-p cell)
	    (return (cons :2.2-able cell)))
	(finally (return nil))))

  

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

(defmacro with-removed-nodes ((&rest nodes) dessin &body body)
  (let ((gensyms (mapcar (lambda (x) (declare (ignore x)) (gensym "REM-NODE")) nodes))
	(g-dessin (gensym "DESSIN")))
    `(let ,(mapcar (lambda (x y)
		     `(,x ,y))
		   gensyms nodes)
       (let ((,g-dessin ,dessin))
	 (setf (slot-value ,g-dessin 'qed-cells)
	       (remove-if (lambda (x)
			    (or ,@(mapcar (lambda (x)
					    `(eq ,x x))
					  gensyms)))
			  (slot-value ,g-dessin 'qed-cells)))
	 ;; TODO: shouldn't I propagate values from the body?
	 ,@body
	 ,@(mapcar (lambda (x)
		     `(push ,x (slot-value ,g-dessin 'qed-cells)))
		   gensyms)))))


(defmacro with-severed-links ((&rest link-specs) &body body)
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
	 ;; TODO: shouldn't I propagate values from the body?
	 ,@body
	 ,@(mapcar (lambda (x y z)
		     (let ((op (cond ((eq 'q (car x)) 'dq)
				     ((eq 'd (car x)) 'qd)
				     ((eq 'e (car x)) 'ee)
				     (t (error "Unknown type of linking: ~a" (car x))))))
		       `(,(intern #?"$((string op))-LINK") ,z ,y)))
		   link-specs gensyms vars)))))

    
(defmacro with-added-nodes ((&rest nodes) dessin &body body)
  (let ((gensyms (mapcar (lambda (x) (declare (ignore x)) (gensym "NEW-NODE")) nodes))
	(g-dessin (gensym "DESSIN")))
    `(let ,(mapcar (lambda (x y)
		     `(,x ,y))
		   gensyms nodes)
       (let ((,g-dessin ,dessin))
	 ,@(mapcar (lambda (x)
		     `(push ,x (slot-value ,g-dessin 'qed-cells)))
		   gensyms)
	 ;; TODO: shouldn't I propagate values from the body?
	 ,@body
	 (setf (slot-value ,g-dessin 'qed-cells)
	       (remove-if (lambda (x)
			    (or ,@(mapcar (lambda (x)
					    `(eq ,x x))
					  gensyms)))
			  (slot-value ,g-dessin 'qed-cells)))))))
  

(defmacro with-tmp-links ((&rest link-specs) &body body)
  (let ((gensyms (mapcar (lambda (x)
			   (declare (ignore x))
			   (list (gensym "LEFT-NODE") (gensym "RIGHT-NODE")))
			 link-specs)))
    `(let ;; OK, I know it's lame and ineffective, but it's in a macroexpansion, so
	 ;; makes little or no difference, right?
	 (,@(mapcar (lambda (x y)
		      `(,(car x) ,(cadr y)))
		    gensyms link-specs)
	  ,@(mapcar (lambda (x y)
		      `(,(cadr x) ,(caddr y)))
		    gensyms link-specs))
       ,@(mapcar (lambda (x y)
		   `(,(intern #?"$((string (car x)))-LINK") ,(car y) ,(cadr y)))
		 link-specs gensyms)
       ;; TODO: shouldn't I propagate values from the body?
       ,@body
       ,@(mapcar (lambda (x y)
		   (let ((op (cond ((eq 'qd (car x)) 'q)
				   ((eq 'dq (car x)) 'd)
				   ((eq 'ee (car x)) 'e)
				   (t (error "Unknown type of linking: ~a" (car x))))))
		     `(,(intern #?"$((string op))-UNLINK") ,(car y))))
		 link-specs gensyms))))


(defun do-1-reidemeister (qed-dessin node)
  (with-slots (qed-dessins) qed-dessin
    (let ((res nil))
      (with-severed-links ((e node))
	(with-removed-nodes (node) qed-dessin
	  (setf res `(* (q "N-1") ,(copy-dessin qed-dessin)))))
      res)))

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
		(setf res `(* (q "2") ,(copy-dessin qed-dessin))))))))
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
	    (setf res-forget (copy-dessin qed-dessin)))
	  (with-tmp-links ((dq lt-node rb-node)
			   (dq rt-node lb-node))
	    (setf res-contract (copy-dessin qed-dessin)))))
      `(+ (* (q "N-2") ,res-forget)
	  ,res-contract))))



(defun do-3.1-reidemeister (qed-dessin node)
  (with-slots (qed-dessins) qed-dessin
    (let ((res-flip nil)
	  (res-leave-left nil)
	  (res-leave-right nil))
      (with-severed-links ((q (cqrr node) lt-node)
			   (d node lb-node)
			   (q (ceqrr node) ct-node)
			   (d (cerr node) cb-node)
			   (q (ceqerr node) rt-node)
			   (d (ceqerr node) rb-node))
	(with-tmp-links ((dq lt-node (ceqerr node))
			 (dq ct-node (ceqrr node))
			 (dq rt-node (cqrr node))
			 (qd lb-node (ceqerr node))
			 (qd cb-node (cerr node))
			 (qd rb-node node))
	  (setf res-flip (copy-dessin qed-dessin)))
	(with-removed-nodes (node (cqrr node)
				  (cerr node) (cqerr node) (cqqerr node)
				  (ceqerr ndoe)) qed-dessin
	  (let ((tmp-l-node (qed nil))
		(tmp-r-node (qed nil)))
	    (ee-link tmp-l-node tmp-r-node)
	    (with-added-nodes (tmp-l-node tmp-r-node) qed-dessin
	      (with-tmp-links ((dq lt-node tmp-l-node)
			       (dq ct-node tmp-r-node)
			       (qd lb-node tmp-l-node)
			       (qd cb-node tmp-r-node)
			       (dq rt-node rb-node))
		(setf res-leave-left (copy-dessin qed-dessin)))
	      (with-tmp-links ((dq ct-node tmp-l-node)
			       (dq rt-node tmp-r-node)
			       (qd cb-node tmp-l-node)
			       (qd rb-node tmp-r-node)
			       (dq lt-node lb-node))
		(setf res-leave-right (copy-dessin qed-dessin)))))))
      `(+ ,res-flip
	  ,res-leave-left
	  (- ,res-leave-right)))))