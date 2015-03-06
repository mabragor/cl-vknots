
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
	       (if (and (cqrr cell) (not (cqrr new-cell)))
		   (dq-link (new-cell-for-cell (cqrr cell))
			    new-cell))
	       (if (and (cdrr cell) (not (cdrr new-cell)))
		   (qd-link (new-cell-for-cell (cdrr cell))
			    new-cell))
	       (if (and (cerr cell) (not (cerr new-cell)))
		   (ee-link (new-cell-for-cell (cerr cell))
			    new-cell))))
      (iter (for cell in (slot-value dessin 'qed-cells))
	    (let ((new-cell (new-cell-for-cell cell)))
	      (copy-connections new-cell cell)))
      (make-instance 'qed-dessin :cells new-qed-cells))))


(defun tightable-p (qed-cell)
  (not (cerr qed-cell)))

(defun has-breaks-p (dessin)
  (iter (for cell in (slot-value dessin 'qed-cells))
	(if (or (not (cqrr cell))
		(not (cdrr cell)))
	    (return t))
	(finally (return nil))))

(defun reidemeister-1-able-p (cell)
  (and cell (cqrr cell) (cerr cell)
       (eq (cqrr cell) cell)))

(defun reidemeister-2.1-able-p (cell)
  (and cell (cqrr cell) (ceqrr cell) (cerr cell) (cqerr cell)
       (not (eq (cqrr cell) cell))
       (eq (ceqrr cell) (cqerr cell))))

(defun reidemeister-2.2-able-p (cell)
  (let ((q-cell (cqrr cell))
	(d-cell (cdrr cell)))
    (and cell q-cell d-cell (cerr q-cell) (cerr d-cell)
	 (not (eq q-cell cell))
	 (eq q-cell d-cell))))


(defun qed-valency (qed-cell)
  "Number of outgoing E edges in QD-loop of the current qed-cell, or :LOOPS,
if cells QD-loop has E-loops"
  (let ((encountered (make-hash-table)))
    (iter (initially (setq cell nil))
	  (for cell next (if (eq cell qed-cell)
			     (terminate)
			     (cqrr (or cell qed-cell))))
	  (if (not cell) (terminate))
	  (when (cerr cell)
	    (if (gethash (cerr cell) encountered)
		(return-from qed-valency :loops))
	    (setf (gethash cell encountered) t)
	    (summing 1)))))

(defun reidemeister-3.1-able-p (cell)
  (and cell (cqrr cell) (cerr cell) (cqrr (cerr cell)) (cqqrr (cerr cell)) (ceqerr cell)
       (not (eq (cqrr cell) cell))
       (eq (ceqrr cell)
	   (cqqerr cell))))

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
  (let ((it (list (q-grow (cqrr cell))
		  (d-grow cell)
		  (q-grow (ceqerr cell))
		  (d-grow (ceqerr cell)))))
    (if-debug "3.1-DRIFT: grown nodes ~{~a~^ ~}" it))
  (let ((lb-cell (d-unlink cell))
	(lt-cell (q-unlink (cqrr cell)))
	(rb-cell (d-unlink (ceqerr cell)))
	(rt-cell (q-unlink (ceqerr cell))))
    ;; (if-debug "3.1-DRIFT: lb ~a lt ~a rb ~a rt ~a" lb-cell lt-cell rb-cell rt-cell)
    ;; (if-debug "3.1-DRIFT: c ~a cqrr ~a cqqrr ~a cdrr ~a ceqerr ~a cqeqerr ~a cdeqerr ~a"
    ;; 	      cell (cqrr cell) (cqqrr cell) (cdrr cell) (ceqerr cell)
    ;; 	      (cqrr (ceqerr cell)) (cdrr (ceqerr cell))
    (dq-link rt-cell (cqrr cell))
    (dq-link cell rb-cell)
    (dq-link lt-cell (ceqerr cell))
    (dq-link (ceqerr cell) lb-cell)
    ;; (if-debug "3.1-DRIFT: c ~a cqrr ~a cqqrr ~a cdrr ~a ceqerr ~a cqeqerr ~a cdeqerr ~a"
    ;; 	      cell (cqrr cell) (cqqrr cell) (cdrr cell) (ceqerr cell)
    ;; 	      (cqrr (ceqerr cell)) (cdrr (ceqerr cell))))
    )
  (let ((it (list (q-shrink (cqrr cell))
		  (d-shrink cell)
		  (q-shrink (ceqerr cell))
		  (d-shrink (ceqerr cell)))))
    (if-debug "3.1-DRIFT: shrank nodes ~{~a~^ ~}" it))
  cell)
  


(defmacro! with-3.1-drift ((o!-cell) &body body)
  `(unwind-protect (progn (3.1-drift ,o!-cell)
			  ,@body)
     (3.1-drift ,o!-cell)))

(defun simplifiable-p (dessin)
  (with-slots (qed-cells) dessin
    (if (not qed-cells)
	(cons :0-able nil)
	(or (iter (for cell in qed-cells)
		  ;; Other transforms really do not work on loose dessins,
		  ;; so it's important to tighten first!
		  (if (tightable-p cell)
		      (return (cons :tightable cell)))
		  (finally (return nil)))
	    (iter (for cell in qed-cells)
		  (if (reidemeister-1-able-p cell)
		      (return (cons :1-able cell)))
		  (if (reidemeister-2.1-able-p cell)
		      (return (cons :2.1-able cell)))
		  (if (reidemeister-2.2-able-p cell)
		      (return (cons :2.2-able cell)))
		  (finally (return nil)))))))

(defun tightable-dessin-p (dessin)
  (iter (for cell in (slot-value dessin 'qed-cells))
	(if (tightable-p cell)
	    (return t))
	(finally (return nil))))

(defun deserialize-qed (lst)
  (let ((cells nil)
	(encountered (make-hash-table :test #'equal)))
    (iter (for (num . cycle) in lst)
	  (format t "Loop num ~a~%" num)
	  (let ((the-loop nil)
		(first-cell (qed nil)))
	    (push first-cell cells)
	    (setf the-loop first-cell)
	    (iter (for edge-num in cycle)
		  (format t "  edge num ~a, loop ~a~%" edge-num the-loop)
		  (let ((new-cell (qed nil)))
		    (push new-cell cells)
		    (setf the-loop (dq-link! new-cell the-loop))
		    ;; (if-first-time (setf first-cell the-loop))
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


(defmacro print-nodes (dessin)
  `(if-debug "  nodes ~{~a~^ ~}" (slot-value ,dessin 'qed-cells)))


(defun depth-first-3.1-drift-to-simplifiable (dessin)
  (let ((used-points (make-hash-table)))
    (labels ((rec (path)
	       ;; (check-dessin-totally-ok dessin)
	       (print-nodes dessin)
	       (let ((it (simplifiable-p dessin)))
		 (if it
		     (cons :yes! (nreverse (cons it path)))
		     (tracing-level
		       (iter over-drift-points
			     (for drift-point in (3.1-drift-points dessin used-points))
			     (with-used-point (drift-point)
			       (with-3.1-drift (drift-point)
				 (let ((it (rec (cons drift-point path))))
				   (if it
				       (return-from over-drift-points it)))))
			     (finally (return-from over-drift-points nil))))))))
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
    `(tracing-level
       (let ,(mapcar (lambda (x y)
		       `(,x ,y))
		     gensyms nodes)
	 (unwind-protect (progn (if-debug "WITH-REMOVED-NODES: removing nodes")
				,@(mapcar (lambda (x)
					    `(if-debug "  removing ~a" ,x))
					  gensyms)
				(setf (slot-value ,o!-dessin 'qed-cells)
				      (remove-if (lambda (x)
						   (or ,@(mapcar (lambda (x)
								   `(eq ,x x))
								 gensyms)))
						 (slot-value ,o!-dessin 'qed-cells)))
				,@body)
	   (if-debug "WITH-REMOVED-NODES: adding nodes back")
	   ,@(mapcan (lambda (x)
		       `((if-debug "  adding ~a" ,x)
			 (push ,x (slot-value ,o!-dessin 'qed-cells))))
		     gensyms))))))

(defmacro! with-added-nodes ((&rest nodes) o!-dessin &body body)
  (let ((gensyms (mapcar (lambda (x) (declare (ignore x)) (gensym "NEW-NODE")) nodes)))
    `(tracing-level
       (let ,(mapcar (lambda (x y)
		       `(,x ,y))
		     gensyms nodes)
	 (unwind-protect (progn (if-debug "WITH-ADDED-NODES: adding nodes")
				,@(mapcan (lambda (x)
					    `((if-debug "  adding ~a" ,x)
					      (push ,x (slot-value ,o!-dessin 'qed-cells))))
					  gensyms)
				,@body)
	   (if-debug "WITH-ADDED-NODES: removing nodes")
	   ,@(mapcar (lambda (x)
		       `(if-debug "  removing ~a" ,x))
		     gensyms)
	   (setf (slot-value ,o!-dessin 'qed-cells)
		 (remove-if (lambda (x)
			      (or ,@(mapcar (lambda (x)
					      `(eq ,x x))
					    gensyms)))
			    (slot-value ,o!-dessin 'qed-cells))))))))


(defmacro! with-grown-nodes ((&rest node-specs) o!-dessin &body body)
  (let ((gensyms (mapcar (lambda (x)
			   (declare (ignore x))
			   (list (gensym "NODE-TO-GROW") (gensym "GROWN-NODE")))
			 node-specs)))
    `(tracing-level
       (let ,(mapcar (lambda (x y)
		       `(,(car x) ,(cadr y)))
		     gensyms node-specs)
	 (let ,(mapcar #'cadr gensyms)
	   (unwind-protect (progn (if-debug "WITH-GROWN-NODES: grow nodes")
				  ,@(mapcan (lambda (x y)
					      `((setf ,(cadr x)
						     (,(intern #?"$((string (car y)))-GROW")
						       ,(car x)))
						(if-debug "  ~a-grown ~a by ~a"
							  ,(string (car y)) ,(car x) ,(cadr x))))
					    gensyms node-specs)
				  (with-added-nodes ,(mapcar #'cadr gensyms) ,o!-dessin
				    ,@body))
	     (if-debug "WITH-GROWN-NODES: shrink nodes")
	     ,@(mapcan (lambda (x y)
			 `((if-debug "  ~a-shrinking ~a by ~a" ,(string (car y)) ,(car x) ,(cadr x))
			   (,(intern #?"$((string (car y)))-SHRINK") ,(car x) ,(cadr x))))
		       gensyms node-specs)))))))


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
    `(tracing-level
       (let ,(mapcar (lambda (x y)
		     `(,x ,(cadr y)))
		   gensyms link-specs)
       (if-debug "WITH-SEVERED-LINKS: severing links")
       (let ,(mapcar (lambda (x y z)
		       `(,z (,(intern #?"$((string (car x)))-UNLINK") ,y)))
		     link-specs gensyms vars)
	 ,@(mapcar (lambda (x y z)
		     `(if-debug "  ~a-unlinked ~a and ~a" ,(string (car x)) ,z ,y))
		   link-specs gensyms vars)
	 (unwind-protect (progn ,@body)
	   (if-debug "WITH-SEVERED-LINKS: restoring links")
	   ,@(mapcan (lambda (x y z)
		       (let ((op (cond ((eq 'q (car x)) 'dq)
				       ((eq 'd (car x)) 'qd)
				       ((eq 'e (car x)) 'ee)
				       (t (error "Unknown type of linking: ~a" (car x))))))
			 `((if-debug "  ~a-linking ~a and ~a" ,(string op) ,z ,y)
			   (,(intern #?"$((string op))-LINK") ,z ,y))))
		     link-specs gensyms vars)))))))
  

(defmacro with-tmp-links ((&rest link-specs) &body body)
  (let ((gensyms (mapcar (lambda (x)
			   (declare (ignore x))
			   (list (gensym "LEFT-NODE") (gensym "RIGHT-NODE")))
			 link-specs)))
    `(tracing-level
       (let (,@(mapcar (lambda (x y)
			 `(,(car x) ,(cadr y)))
		       gensyms link-specs)
	     ,@(mapcar (lambda (x y)
			 `(,(cadr x) ,(caddr y)))
		       gensyms link-specs))
	 (if-debug "WITH-TMP-LINKS: making links")
	 ,@(mapcar (lambda (x y)
		     `(,(intern #?"$((string (car x)))-LINK") ,(car y) ,(cadr y)))
		   link-specs gensyms)
	 (unwind-protect (progn ,@body)
	   (if-debug "WITH-TMP-LINKS: breaking links")
	   ,@(mapcar (lambda (x y)
		       (let ((op (cond ((eq 'qd (car x)) 'q)
				       ((eq 'dq (car x)) 'd)
				       ((eq 'ee (car x)) 'e)
				       (t (error "Unknown type of linking: ~a" (car x))))))
			 `(,(intern #?"$((string op))-UNLINK") ,(car y))))
		     link-specs gensyms))))))


(defun do-0-reidemeister (qed-dessin node)
  "Fake Reidemeister move, to substitute empty dessin with 1"
  (declare (ignore node qed-dessin))
  "1")
  

(defun do-1-reidemeister (qed-dessin node)
  (with-slots (qed-dessins) qed-dessin
    (let ((res nil))
      (macrolet ((debug-frob ()
		   `(if-debug "t-node ~a b-node ~a d-t-node ~a q-b-node ~a~%"
			      t-node b-node (cdrr t-node) (cqrr b-node))))
	(with-severed-links ((q (cerr node) t-node)
			     (d (cerr node) b-node)) qed-dessin
	  (with-removed-nodes (node (cerr node)) qed-dessin
	    (with-tmp-links ((dq t-node b-node))
	      (setf res (tighten-loops (copy-dessin qed-dessin)))
	      (debug-frob))
	    (debug-frob))
	  (debug-frob)))
      (format t "Res of 1-reid is: ~a~%" res)
      `(* (q "N-1") ,res))))

(defun dessin-cell-hash (dessin)
  (let ((cell-hash (make-hash-table)))
    (iter (for cell in (slot-value dessin 'qed-cells))
	  (setf (gethash cell cell-hash) t))
    cell-hash))


(defun check-dessin-totally-ok (dessin)
  (let ((cell-hash (dessin-cell-hash dessin)))
    (iter (for cell in (slot-value dessin 'qed-cells))
	  (let ((e-cell (cerr cell))
		(q-cell (cqrr cell))
		(d-cell (cdrr cell)))
	    (if (not e-cell)
		(error "Dessin is not tight"))
	    (if (not q-cell)
		(error "Dessin has Q-breaks"))
	    (if (not d-cell)
		(error "Dessin has D-breaks"))
	    (if (not (gethash e-cell cell-hash))
		(error "Dessin has E-leaks"))
	    (if (not (gethash q-cell cell-hash))
		(error "Dessin has Q-leaks"))
	    (if (not (gethash d-cell cell-hash))
		(error "Dessin has D-leaks: ~a d-connects to ~a" cell d-cell))
	    (if (eq e-cell cell)
		(error "Dessin has anomal E-links"))
	    (if (not (eq (cdrr q-cell) cell))
		(error "Dessin is non-Q-haussdorf"))
	    (if (not (eq (cqrr d-cell) cell))
		(error "Dessin is non-D-haussdorf"))
	    (if (not (eq (cerr e-cell) cell))
		(error "Dessin is non-E-haussdorf"))))
    :dessin-totally-ok!))
		
		

(defun do-2.1-reidemeister (qed-dessin node)
  (tracing-level
    (if-debug "DO 2.1: ~a ~a" (serialize-qed qed-dessin) node)
    (print-nodes qed-dessin)
    (if-debug "~a" (check-dessin-totally-ok qed-dessin))
    (if-debug "~a" (if (not (find node (slot-value qed-dessin 'qed-cells)))
		       (error "Node ~a is not part of dessin" node)))
    (with-slots (qed-dessins) qed-dessin
      (let ((res nil))
	(with-severed-links ((q (cqrr node) lt-node)
			     (d node lb-node)
			     (q (ceqrr node) rt-node)
			     (d (cerr node) rb-node)) qed-dessin
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
	res))))

(defun do-2.2-reidemeister (qed-dessin node)
  (with-slots (qed-dessins) qed-dessin
    (let ((res-forget nil)
	  (res-contract nil))
      (with-severed-links ((q (cerr node) lt-node)
			   (d (cerr node) lb-node)
			   (q (ceqrr node) rt-node)
			   (d (ceqrr node) rb-node)) qed-dessin
	(with-removed-nodes (node (cqrr node) (cerr node) (ceqrr node)) qed-dessin
	  (with-tmp-links ((dq lt-node lb-node)
			   (dq rt-node rb-node))
	    (setf res-forget (tighten-loops (copy-dessin qed-dessin))))
	  (with-tmp-links ((dq lt-node rb-node)
			   (dq rt-node lb-node))
	    (setf res-contract (tighten-loops (copy-dessin qed-dessin))))))
      `(+ (* (q "N-2") ,res-forget)
	  ,res-contract))))

(defun do-tight (dessin)
  (tighten-loops (copy-dessin dessin)))

(defun do-3.1-reidemeisters-then-something-else (qed-dessin plan)
  (tracing-level
    (if (equal 1 (length plan))
	(cond ((eq :0-able (caar plan)) (do-0-reidemeister qed-dessin (cdar plan)))
	      ((eq :tightable (caar plan)) (do-tight qed-dessin))
	      ((eq :1-able (caar plan)) (do-1-reidemeister qed-dessin (cdar plan)))
	      ((eq :2.1-able (caar plan)) (do-2.1-reidemeister qed-dessin (cdar plan)))
	      ((eq :2.2-able (caar plan)) (do-2.2-reidemeister qed-dessin (cdar plan)))
	      (t (error "Don't know how to perform this part of plan: ~a~%" (caar plan))))
	(%do-3.1-reidemeisters-then-something-else qed-dessin plan))))

(defun %do-3.1-reidemeisters-then-something-else (qed-dessin plan)
  (let ((node (car plan)))
    (if-debug "~a" (check-dessin-totally-ok qed-dessin))
    (print-nodes qed-dessin)
    (with-slots (qed-dessins) qed-dessin
      (let ((res-leave-left nil)
	    (res-leave-right nil))
	(with-severed-links ((q (cqrr node) lt-node)
			     (d node lb-node)
			     (q (ceqrr node) ct-node)
			     (d (cerr node) cb-node)
			     (q (ceqerr node) rt-node)
			     (d (ceqerr node) rb-node)) qed-dessin
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
	;; (print-nodes qed-dessin)
	(if-debug "~a" (check-dessin-totally-ok qed-dessin))
	(if-debug "Done with reidemeister 'tails' ~a ~a"
		  (tightable-dessin-p qed-dessin) (has-breaks-p qed-dessin))
	(3.1-drift node)
	(print-nodes qed-dessin)
	(if-debug "Now dessin is ~a ~a ~a"
		  (serialize-qed qed-dessin) (tightable-dessin-p qed-dessin) (has-breaks-p qed-dessin))
	`(+ ,(do-3.1-reidemeisters-then-something-else qed-dessin (cdr plan))
	    ,res-leave-left
	    (- ,res-leave-right))))))


;; So, now I need to find a way to *completely* decompose qed-dessin
;; not make just one step.

(defparameter *accumulator* nil)

(defun %find-cons-dessins (poly)
  (when (and poly (not (atom poly)))
    (if (typep (car poly) 'qed-dessin)
	(progn (if-debug "FIND-CONS-DESSINS: found ~a" poly)
	       (push poly *accumulator*))
	(if (consp (car poly))
	    (%find-cons-dessins (car poly))))
    (%find-cons-dessins (cdr poly))))
      

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
	  (format t "new stuff is: ~a~%" new-stuff)
	  (setf (car cons-of-dessin) new-stuff)
	  (let ((cons-dessins (find-cons-dessins cons-of-dessin)))
	    cons-dessins)))))

(defun decompose (dessin)
  (let ((head (list dessin)))
    (let ((conses-of-dessins (list head)))
      (iter (for i from 1 to 10)
	    (if-debug "DECOMPOSE: ~a| ~a" head conses-of-dessins)
	    (setf conses-of-dessins
		  (remove-duplicates (apply #'append (remove-if-not #'identity
								    (mapcar #'decomposition-step
									    conses-of-dessins)))
				     :key #'car :test #'eq))
	    (if (not conses-of-dessins)
		(terminate))))
    (car head)))

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
	  `(* (** (q "N") ,num-loops) ,dessin)))))
		

(defun serialize-qed (dessin)
  (let ((edges-hash (make-hash-table))
	(edge-count 0)
	res)
    (let ((cells-hash (make-hash-table))
	  (cur-loop nil))
      (iter (for cell in (slot-value dessin 'qed-cells))
	    (setf (gethash cell cells-hash) t))
      (iter (for new-loop-start next (multiple-value-bind (got key val) (pophash cells-hash)
				       (declare (ignore val))
				       (if (not got)
					   (terminate)
					   key)))
	    (for loop-num from 1)
	    (setf cur-loop (list loop-num))
	    (iter (initially (setq cell nil))
		  (for cell next (if (not cell)
				     new-loop-start
				     (let ((it (cqrr cell)))
				       (cond ((not it) (error "Attempt to serialize dessin with broken loop"))
					     ((eq new-loop-start it) (terminate))
					     (t (remhash it cells-hash)
						it)))))
		  (let ((other-end (cerr cell)))
		    (cond ((not other-end) (next-iteration))
			  ((eq cell other-end) (error "Self-referring E-place in dessin to serialize"))
			  (t (push (or (gethash other-end edges-hash)
				       (setf (gethash cell edges-hash) (incf edge-count)))
				   cur-loop)))))
	    (push (nreverse cur-loop) res)))
    (nreverse res)))
			  
			


(defparameter *a* (deserialize-qed (torus-dessin 3 3)))


(defparameter *a-step* (deserialize-qed '((1 1 2) (2 3 4 2 5 6 1) (3 3 4 5 6))))


(defun mathematica-serialize (poly)
  (cond ((stringp poly) poly)
	((eq 'q (car poly)) #?"q[$((mathematica-serialize (cadr poly)))]")
	((eq '+ (car poly)) (joinl " + " (mapcar (lambda (x)
						   #?"($((mathematica-serialize x)))")
						 (cdr poly))))
	((eq '* (car poly)) (joinl " * " (mapcar (lambda (x)
						   #?"($((mathematica-serialize x)))")
						 (cdr poly))))
	((eq '** (car poly)) #?"($((mathematica-serialize (cadr poly))))^($((caddr poly)))")
	((eq '- (car poly)) (if (not (equal 1 (length (cdr poly))))
				(joinl " - " (mapcar (lambda (x)
						   #?"($((mathematica-serialize x)))")
						     (cdr poly)))
				#?"- ($((mathematica-serialize (cadr poly))))"))
	(t (error "Don't yet knot how to MATHEMATICA-SERIALIZE this: ~a~%" poly))))