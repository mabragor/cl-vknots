
(in-package #:cl-vknots)

;; TADA!

(cl-interpol:enable-interpol-syntax)

(define-condition vknots-error (error) ())

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

(defun virt-reidemeister-1-able-p (cell)
  (and cell (cqrr cell) (cerr cell)
       (eq (cerr cell) (cqrr cell))))

(defun reidemeister-2.1-able-p (cell)
  (and cell (cqrr cell) (ceqrr cell) (cerr cell) (cqerr cell)
       (not (eq (cqrr cell) cell))
       (eq (ceqrr cell) (cqerr cell))))

(defun virt-reidemeister-2.1-able-p (cell)
  (and cell (cqrr cell) (cdrr cell) (ceqrr cell) (cerr cell) (cderr cell)
       (not (eq (cqrr cell) cell))
       (eq (ceqrr cell) (cderr cell))))


(defun reidemeister-2.2-able-p (cell)
  (let ((q-cell (cqrr cell))
	(d-cell (cdrr cell)))
    (and cell q-cell d-cell (cerr q-cell) (cerr d-cell)
	 (not (eq q-cell cell))
	 (eq q-cell d-cell))))


(defun virt-reidemeister-2.2-able-p (cell)
  (let ((q-cell (cqrr cell))
	(d-cell (cdrr cell)))
    (and cell q-cell d-cell (cerr cell)
	 (not (eq q-cell d-cell))
	 (eq (cerr q-cell) d-cell))))


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
  


(defmacro with-3.1-drift ((o!-cell) &body body)
  (let ((g!-cell (gensym "CELL")))
    `(let ((,g!-cell ,o!-cell))
       (unwind-protect (progn (3.1-drift ,g!-cell)
			      ,@body)
	 (3.1-drift ,g!-cell)))))

(defparameter predicates `((,#'reidemeister-1-able-p :1-able :short)
			   (,#'virt-reidemeister-1-able-p :virt-1-able :short)
			   (,#'reidemeister-2.1-able-p :2.1-able :short)
			   (,#'reidemeister-2.2-able-p :2.2-able)
			   (,#'virt-reidemeister-2.1-able-p :virt-2.1-able)
			   (,#'virt-reidemeister-2.2-able-p :virt-2.2-able)
			   ))

(defun simplifiable-p (dessin)
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
		    (iter (for (fun tag short-p) in predicates)
			  (let ((it (funcall fun cell)))
			    (when it
			      (if short-p
				  (return-from outer (cons tag cell))
				  (push cell (gethash tag res))))))
		    (if-debug "res ~a" (hash->assoc res))
		    (finally (iter (for (fun tag short-p) in predicates)
				   (if (not short-p)
				       (next-iteration))
				   (let ((it (gethash tag res)))
				     (if it (return-from outer (cons tag (car (last it)))))))
			     (iter (for (fun tag short-p) in predicates)
				   (let ((it (gethash tag res)))
				     (if it (return-from outer (cons tag (car (last it)))))))
			     (return-from outer nil))))))))

(defun tightable-dessin-p (dessin)
  (iter (for cell in (slot-value dessin 'qed-cells))
	(if (tightable-p cell)
	    (return t))
	(finally (return nil))))

(defun deserialize-qed (lst &key (ignore-colors t))
  (let ((cells nil)
	(encountered (make-hash-table :test #'equal)))
    (iter (for (num . cycle) in lst)
	  (if-debug "Loop num ~a" num)
	  (let ((the-loop nil)
		(first-cell (qed nil)))
	    (push first-cell cells)
	    (setf the-loop first-cell)
	    (iter (for edge-num in cycle)
		  (if (and ignore-colors
			   (consp edge-num))
		      (setf edge-num (cadr edge-num)))
		  (if-debug "  edge num ~a, loop ~a" edge-num the-loop)
		  (let ((new-cell (qed nil)))
		    (setf (slot-value new-cell 'label) edge-num)
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

(defmacro with-removed-nodes ((&rest nodes) o!-dessin &body body)
  (let ((gensyms (mapcar (lambda (x) (declare (ignore x)) (gensym "REM-NODE")) nodes))
	(g!-dessin (gensym "DESSIN")))
    `(tracing-level
       (let ((,g!-dessin ,o!-dessin))
	 (let ,(mapcar (lambda (x y)
			 `(,x ,y))
		       gensyms nodes)
	   (unwind-protect (progn (if-debug "WITH-REMOVED-NODES: removing nodes")
				  ,@(mapcar (lambda (x)
					      `(if-debug "  removing ~a" ,x))
					    gensyms)
				  (setf (slot-value ,g!-dessin 'qed-cells)
					(remove-if (lambda (x)
						     (or ,@(mapcar (lambda (x)
								     `(eq ,x x))
								   gensyms)))
						   (slot-value ,g!-dessin 'qed-cells)))
				  ,@body)
	     (if-debug "WITH-REMOVED-NODES: adding nodes back")
	     ,@(mapcan (lambda (x)
			 `((if-debug "  adding ~a" ,x)
			   (push ,x (slot-value ,g!-dessin 'qed-cells))))
		       gensyms)))))))

(defmacro with-added-nodes ((&rest nodes) o!-dessin &body body)
  (let ((gensyms (mapcar (lambda (x) (declare (ignore x)) (gensym "NEW-NODE")) nodes))
	(g!-dessin (gensym "DESSIN")))
    `(tracing-level
       (let ((,g!-dessin ,o!-dessin))
	 (let ,(mapcar (lambda (x y)
			 `(,x ,y))
		       gensyms nodes)
	   (unwind-protect (progn (if-debug "WITH-ADDED-NODES: adding nodes")
				  ,@(mapcan (lambda (x)
					      `((if-debug "  adding ~a" ,x)
						(push ,x (slot-value ,g!-dessin 'qed-cells))))
					    gensyms)
				  ,@body)
	     (if-debug "WITH-ADDED-NODES: removing nodes")
	     ,@(mapcar (lambda (x)
			 `(if-debug "  removing ~a" ,x))
		       gensyms)
	     (setf (slot-value ,g!-dessin 'qed-cells)
		   (remove-if (lambda (x)
				(or ,@(mapcar (lambda (x)
						`(eq ,x x))
					      gensyms)))
			      (slot-value ,g!-dessin 'qed-cells)))))))))


(defmacro with-grown-nodes ((&rest node-specs) o!-dessin &body body)
  (let ((gensyms (mapcar (lambda (x)
			   (declare (ignore x))
			   (list (gensym "NODE-TO-GROW") (gensym "GROWN-NODE")))
			 node-specs))
	(g!-dessin (gensym "DESSIN")))
    `(tracing-level
       (let ((,g!-dessin ,o!-dessin))
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
				    (with-added-nodes ,(mapcar #'cadr gensyms) ,g!-dessin
				      ,@body))
	       (if-debug "WITH-GROWN-NODES: shrink nodes")
	       ,@(mapcan (lambda (x y)
			   `((if-debug "  ~a-shrinking ~a by ~a" ,(string (car y)) ,(car x) ,(cadr x))
			     (,(intern #?"$((string (car y)))-SHRINK") ,(car x) ,(cadr x))))
			 gensyms node-specs))))))))


(defmacro with-severed-links ((&rest link-specs) o!-dessin &body body)
  (let ((gensyms (mapcar (lambda (x) (declare (ignore x)) (gensym "THIS-LINK-END")) link-specs))
	(g!-dessin (gensym "DESSIN")))
    `(let ((,g!-dessin ,o!-dessin))
       (let ,(mapcar (lambda (x y)
		       `(,x ,(cadr y)))
		     gensyms link-specs)
	 (with-grown-nodes ,(mapcar (lambda (x y)
				      (list (car x) y))
				    link-specs gensyms) ,g!-dessin
	   (with-severed-links! ,(mapcar (lambda (x y)
					   (list (car x) y (caddr x)))
					 link-specs gensyms)
	     ,@body))))))

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
      (if-debug "Res of 1-reid is: ~a" res)
      `(* (q "N-1") ,res))))

(defun do-virt-1-reidemeister (qed-dessin node)
  (with-slots (qed-dessins) qed-dessin
    (let ((res nil))
      (with-severed-links ((q (cqrr node) t-node)
			   (d node b-node)) qed-dessin
	(with-removed-nodes (node (cqrr node)) qed-dessin
	  (with-tmp-links ((dq t-node b-node))
	    (setf res (tighten-loops (copy-dessin qed-dessin))))))
      `(* (- (q "N-1")) ,res))))


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

(defun do-tight (dessin node)
  (declare (ignore node))
  (tighten-loops (copy-dessin dessin)))


(defun do-virt-2.1-reidemeister (qed-dessin node)
  (with-slots (qed-dessins) qed-dessin
    (let ((res-forget nil)
	  (res-contract nil))
      (with-severed-links ((q (cqrr node) lt-node)
			   (d node lb-node)
			   (q (cerr node) rt-node)
			   (d (cderr node) rb-node)) qed-dessin
	(with-removed-nodes (node (cqrr node) (cerr node) (cderr node)) qed-dessin
	  (with-tmp-links ((dq lt-node rb-node)
			   (dq rt-node lb-node))
	    (setf res-contract (tighten-loops (copy-dessin qed-dessin))))
	  (with-tmp-links ((dq lt-node lb-node)
			   (dq rt-node rb-node))
	    (setf res-forget (tighten-loops (copy-dessin qed-dessin))))))
      `(+ (* (q "N-2") ,res-contract)
	  ,res-forget))))


(defun do-virt-2.2-reidemeister (qed-dessin node)
  (with-slots (qed-dessins) qed-dessin
    (let ((res-forget nil)
	  (res-contract nil))
      (with-severed-links ((q (cqrr node) lt-node)
			   (d (cdrr node) lb-node)
			   (q (cerr node) rt-node)
			   (d (cerr node) rb-node)) qed-dessin
	(with-removed-nodes (node (cqrr node) (cdrr node) (cerr node)) qed-dessin
	  (with-tmp-links ((dq lt-node rb-node)
			   (dq rt-node lb-node))
	    (setf res-contract (tighten-loops (copy-dessin qed-dessin))))
	  (with-tmp-links ((dq lt-node lb-node)
			   (dq rt-node rb-node))
	    (setf res-forget (tighten-loops (copy-dessin qed-dessin))))))
      `(- (+ (* (q "N-2") ,res-forget)
	     ,res-contract)))))



(defparameter actions `((:0-able . ,#'do-0-reidemeister)
			(:tight-able . ,#'do-tight)
			(:1-able . ,#'do-1-reidemeister)
			(:virt-1-able . ,#'do-virt-1-reidemeister)
			(:2.1-able . ,#'do-2.1-reidemeister)
			(:virt-2.1-able . ,#'do-virt-2.1-reidemeister)
			(:2.2-able . ,#'do-2.2-reidemeister)
			(:virt-2.2-able . ,#'do-virt-2.2-reidemeister)
			))


(defun do-3.1-reidemeisters-then-something-else (qed-dessin plan)
  (tracing-level
    (if (equal 1 (length plan))
	(let ((it (assoc (caar plan) actions)))
	  (if it
	      (funcall (cdr it) qed-dessin (cdar plan))
	      (error "Don't know how to perform this part of plan: ~a~%" (caar plan))))
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

(defun serialize-to-diags (qed-dessin)
  (cons '*
	(mapcar (lambda (x)
		  `(* (** "-1" ,(car x)) (diag (,(under-lst (cadr x))))))
		(hordize-dessin qed-dessin))))

(defun decomposition-step (cons-of-dessin)
  (declare (special toplevel))
  (let ((plan (depth-first-3.1-drift-to-simplifiable (car cons-of-dessin))))
    (if-debug "~a" plan)
    (if (not plan)
	(if toplevel
	    (error 'vknots-error "Unable to find a decomposition plan for ~a" (serialize-qed (car cons-of-dessin)))
	    (progn (setf (car cons-of-dessin) (serialize-to-diags (car cons-of-dessin)))
		   nil))
	(let ((new-stuff (do-3.1-reidemeisters-then-something-else (car cons-of-dessin) (cdr plan))))
	  (if-debug "new stuff is: ~a" new-stuff)
	  (setf (car cons-of-dessin) new-stuff)
	  (let ((cons-dessins (find-cons-dessins cons-of-dessin)))
	    cons-dessins)))))

(defun decompose (dessin)
  (let ((head (list dessin))
	(toplevel t))
    (declare (special toplevel))
    (let ((conses-of-dessins (make-hash-table)))
      (setf (gethash dessin conses-of-dessins) head)
      (iter ;; (if-debug "DECOMPOSE: ~a| ~a" head conses-of-dessins)
	    (for i from 1)
	    (if (not (and (equal 1 (length head))
			  (typep (car head) 'qed-dessin)))
		(setf toplevel nil))
	    (if-debug "  DECOMPOSE: round ~a ~a" i (hash-table-count conses-of-dessins))
	    (let ((new-conses-of-dessins (make-hash-table)))
	      (iter (for (nil cons-of-dessin) in-hashtable conses-of-dessins)
		    ;; (format t "~a~%" cons-of-dessin)
		    (let ((it (decomposition-step cons-of-dessin)))
		      (if it
			  (iter (for elt in it)
				(setf (gethash (car elt) new-conses-of-dessins) elt)))))
	      (setf conses-of-dessins new-conses-of-dessins))
	    (if (equal 0 (hash-table-count conses-of-dessins))
		(terminate))))
    (car head)))

(defun %tighten-loops (dessin)
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
      num-loops)))

  
(defun tighten-loops (dessin)
  (let ((num-loops (%tighten-loops dessin)))
    (if (equal 0 num-loops)
	dessin
	`(* (** (q "N") ,num-loops) ,dessin))))
		
(defmacro! iter-over-cells-in-the-pool ((cell-var pool) &body body)
  `(let ((,g!-cells-hash (make-hash-table)))
     (iter (for cell in ,pool)
	   (setf (gethash cell ,g!-cells-hash) t))
     (macrolet ((new-random-cell ()
		  `(multiple-value-bind (got key val) (pophash ,',g!-cells-hash)
		     (declare (ignore val))
		     (if (not got)
			 (terminate)
			 key)))
		(uncheck-cell (cell)
		  `(remhash ,cell ,',g!-cells-hash)))
       (iter (for ,cell-var next (new-random-cell))
	     ,@body))))

(defmacro! iter-over-cells-in-a-loop ((cell-var loop-start-var) &body body)
  `(iter (initially (setq ,cell-var nil))
	 (for ,cell-var next (if (not ,cell-var)
				 ,loop-start-var
				 (let ((,g!-it (cqrr ,cell-var)))
				   (cond ((not ,g!-it) (error "Attempt to iterate over broken cell loop"))
					 ((eq ,loop-start-var ,g!-it) (terminate))
					 (t (uncheck-cell ,g!-it)
					    ,g!-it)))))
	 ,@body))


(defmacro! with-unique-edge-labeler (&body body)
  `(let ((edge-labels (make-hash-table :test #'equal))
	 (edge-count 0))
     (labels ((unique-edge-label (cell other-cell)
		(let ((it1 (slot-value cell 'label))
		      (it2 (slot-value other-cell 'label)))
		  (if (or (not it1)
			  (not (equal it1 it2))
			  (gethash it1 edge-labels))
		      (unique-edge-count-label)
		      (progn (setf (gethash it1 edge-labels) t)
			     it1))))
	      (unique-edge-count-label ()
		(let ((it edge-count))
		  (iter (while (gethash (incf it) edge-labels)))
		  (setf (gethash it edge-labels) t)
		  it)))
       ,@body)))

(defun serialize-qed (dessin)
  (let ((edges-hash (make-hash-table))
	res)
    (with-unique-edge-labeler
	(let ((cur-loop nil))
	  (iter-over-cells-in-the-pool (new-loop-start (slot-value dessin 'qed-cells))
	    (for loop-num from 1)
	    (setf cur-loop (list loop-num))
	    (iter-over-cells-in-a-loop (cell new-loop-start)
	      (let ((other-end (cerr cell)))
		(cond ((not other-end) (next-iteration))
		      ((eq cell other-end) (error "Self-referring E-place in dessin to serialize"))
		      (t (push (or (gethash other-end edges-hash)
				   (setf (gethash cell edges-hash) (unique-edge-label cell other-end)))
			       cur-loop)))))
	    (push (nreverse cur-loop) res)))
      (nreverse res))))

(defun next-real-cell (cell)
  (let ((next-cell (cqrr cell)))
    (if (not next-cell) (error "Broken loop in the dessin"))
    (iter (while (not (cerr next-cell)))
	  (setf next-cell (cqrr next-cell))
	  (if (not next-cell) (error "Broken loop in the dessin")))
    next-cell))





(defun mutate-by-naive-1-rule (cell ncell nncell)
  (let* ((lt-cell (q-unlink! (cerr nncell)))
	 (lb-cell (d-unlink! (cerr cell)))
	 (rt-cell (q-unlink! (cerr ncell)))
	 (rb-cell (d-unlink! (cerr ncell))))
    (dq-link! lt-cell (cerr ncell))
    (dq-link! (cerr ncell) lb-cell)
    (dq-link! rt-cell (cerr nncell))
    (dq-link! (cerr cell) rb-cell)))

(defun swap-labels (cell1 cell2)
  (with-slots ((label1 label)) cell1
    (with-slots ((label2 label)) cell2
      (let ((it label1))
	(setf label1 label2
	      label2 it)))))

(defun mutate-by-naive-n-3-rule (cell ncell nncell)
  (let* ((q-cell (q-unlink! (cerr cell)))
	 (d-cell (d-unlink! (cerr cell)))
	 (q-ncell (q-unlink! (cerr ncell)))
	 (d-ncell (d-unlink! (cerr ncell)))
	 (q-nncell (q-unlink! (cerr nncell)))
	 (d-nncell (d-unlink! (cerr nncell))))
    (swap-labels ncell nncell)
    (dq-link q-cell (cerr cell))
    (dq-link (cerr cell) d-ncell)
    (dq-link q-nncell (cerr ncell))
    (dq-link (cerr ncell) d-cell)
    (dq-link q-ncell (cerr nncell))
    (dq-link (cerr nncell) d-nncell)))
  
(defmacro! with-1-rule-mutation ((o!-cell o!-ncell o!-nncell) &body body)
  `(unwind-protect (progn (mutate-by-naive-1-rule ,o!-cell ,o!-ncell ,o!-nncell)
			  ,@body)
     (mutate-by-naive-1-rule ,o!-cell ,o!-ncell ,o!-nncell)))

(defmacro! with-n-3-rule-mutation ((o!-cell o!-ncell o!-nncell) &body body)
  `(unwind-protect (progn (mutate-by-naive-n-3-rule ,o!-cell ,o!-ncell ,o!-nncell)
			  ,@body)
     (mutate-by-naive-n-3-rule ,o!-cell ,o!-ncell ,o!-nncell)))


				    

(defun compose-new-cluster-entry (new-dessin parent-dessin mutation-type cell ncell nncell)
  (list new-dessin
	(cons parent-dessin
	      (cons mutation-type
		    (mapcar (lambda (x)
			      (slot-value x 'label))
			    (list cell ncell nncell))))))
(defun grow-everything (qed-dessin)
  (let ((new-cells nil))
    (with-slots (qed-cells) qed-dessin
      (iter (for cell in qed-cells)
	    (push (q-grow cell) new-cells)
	    (push (d-grow cell) new-cells))
      (setf qed-cells (nconc new-cells qed-cells))))
  qed-dessin)



(defun mutation-cluster (dessin)
  (let ((cluster (list (list dessin nil)))
	(leaf-dessins (list dessin)))
    (macrolet ((frob (coro-call mutation-macro mutation-type)
		 `(iter (for (cell ncell nncell) in-coroutine ,coro-call)
			(,mutation-macro
			 (cell ncell nncell)
			 (let ((new-dessin (serialize-qed qed-dessin)))
			   (when (not (find new-dessin cluster
					    :key #'car
					    :test #'dessins-bijectable-p))
			     (push new-dessin new-leaf-dessins)
			     (push (compose-new-cluster-entry new-dessin
							      leaf-dessin
							      ',mutation-type
							      cell ncell nncell)
				   cluster)))))))
      (iter (while leaf-dessins)
	    (let ((new-leaf-dessins nil))
	      (iter (for leaf-dessin in leaf-dessins)
		    (let ((qed-dessin (grow-everything (deserialize-qed leaf-dessin))))
		      (frob (all-1-rule-sites qed-dessin) with-1-rule-mutation :p)
		      (frob (all-n-3-rule-sites qed-dessin) with-n-3-rule-mutation :a)))
	      (setf leaf-dessins new-leaf-dessins))))
    cluster))
	  
    
			


(defparameter *a* (deserialize-qed (torus-dessin 5 3)))


(defparameter *a-step* (deserialize-qed '((1 1 2) (2 3 4 2 5 6 1) (3 3 4 5 6))))


(defun just-print-diag (%horde)
  (if-debug "Printing diagram ~a" %horde)
  (format nil "HordeDiag[~{~a~^, ~}]" %horde))

(defun try-to-decompose-diag (%horde &optional skip-flips)
  (if-debug "Decomposing diagram: ~a" %horde)
  (handler-case (mathematica-serialize (decompose (%horde->qed-dessin %horde))
				       #'try-to-decompose-diag)
    (vknots-error (e)
      (let ((res nil))
	(if skip-flips
	    (error e)
	    (progn (iter (for flipped-diag in (really-all-prehorde-flips (%horde->prehorde %horde)))
		   	 ;; (format t "flipped diag ~{~a~^ ~}~%" flipped-diag)
		   	 (handler-case (setf res (try-to-decompose-diag (%%horde->%horde flipped-diag) t))
		   	   (:no-error (x)
		   	     (declare (ignore x))
			     ;; (format t "I'm here!")
		   	     (return-from try-to-decompose-diag res))
		   	   (vknots-error (e)
			     ;; (format t "~a~%" e)
			     )))
		   (just-print-diag %horde)))))))

(defun mathematica-serialize (poly &optional (diag-decomposer #'just-print-diag))
  (cond ((stringp poly) poly)
	((eq 'q (car poly)) #?"q[$((mathematica-serialize (cadr poly) diag-decomposer))]")
	((eq '+ (car poly)) (joinl " + " (mapcar (lambda (x)
						   #?"($((mathematica-serialize x diag-decomposer)))")
						 (cdr poly))))
	((eq '* (car poly)) (joinl " * " (mapcar (lambda (x)
						   #?"($((mathematica-serialize x diag-decomposer)))")
						 (cdr poly))))
	((eq '** (car poly)) #?"($((mathematica-serialize (cadr poly) diag-decomposer)))^($((caddr poly)))")
	((eq '- (car poly)) (if (not (equal 1 (length (cdr poly))))
				(joinl " - " (mapcar (lambda (x)
						   #?"($((mathematica-serialize x diag-decomposer)))")
						     (cdr poly)))
				#?"- ($((mathematica-serialize (cadr poly) diag-decomposer)))"))
	((eq 'diag (car poly)) (if (equal '(:empty) (cadr poly))
				   "1"
				   (joinl " * " (mapcar diag-decomposer (cadr poly)))))
	((eq 'perm-dessin (car poly)) #?"PermDessin[$((cadr poly)), $((caddr poly))]")
	(t (error 'vknots-error "Don't yet knot how to MATHEMATICA-SERIALIZE this: ~a~%" poly))))




(defun 4-thick-decompositions (n-max &optional (fname #?"$(*fname-prefix*)FourThickDecompositions.m"))
  (with-open-file (stream fname :direction :output :if-exists :supersede)
    (iter (for n from 2 to n-max)
	  ;; (format stream "ThreeSausageHOMFLY[~a] := ~a;~%~%"
	  ;; 	  n (homfly-for-dessin (deserialize2 (torus-dessin 3 n))))
	  (format t "Doing ~a~%" n)
	  (let ((it (decompose (deserialize-qed (torus-dessin 4 n)))))
	    (format t "  done decomposing~%")
	    (format stream "FourThickDecomposition[~a] := ~a;~%~%"
		    n (mathematica-serialize it))
	    (format t "  done serializing~%"))))
  :success!)


(defparameter *closed-torus* '((1 5 1 6 2) (2 1 3 2 4) (3 3 5 4 6)))


(defparameter *almost-closed-torus* '((1 1 6 2) (2 1 3 2 4) (3 3 4 6)))


(defun dessin-valencies (dessin)
  (let ((res (make-hash-table :test #'equal)))
    (iter (for (id . edges) in dessin)
	  (push id (gethash (length edges) res)))
    (sort (hash->assoc res) #'> :key #'car)))

(defun all-permutations (lst &optional (remain lst))
  (cond ((null remain) nil)
	((null (rest lst)) (list lst))
	(t (append (mapcar (lambda (l)
			     (cons (first lst) l))
			   (all-permutations (rest lst)))
		   (all-permutations (append (rest lst) (list (first lst)))
				     (rest remain))))))

(defun all-vertex-maps (verts1 verts2)
  (mapcar (lambda (perm)
	    (mapcar (lambda (x y)
		      (cons x y))
		    verts1 perm))
	  (all-permutations verts2)))

(define-condition no-maps (error) ())

;; OK, let's write the non-iterator function first and then we'll see...
(defun vertex-maps (dessin1 dessin2)
  (let ((maps nil)
	(vals1 (dessin-valencies dessin1))
	(vals2 (dessin-valencies dessin2)))
    (if (equal (length vals1) (length vals2))
	(labels ((rec (cur-map valencies1 valencies2)
		   (if (not valencies1)
		       (push cur-map maps)
		       (destructuring-bind (val1 . vertices1) (car valencies1)
			 (destructuring-bind (val2 . vertices2) (car valencies2)
			   (if (equal val1 val2)
			       (iter (for vmap in (all-vertex-maps vertices1 vertices2))
				     (rec (nconc vmap cur-map)
					  (cdr valencies1)
					  (cdr valencies2)))
			       (error 'no-maps)))))))
	  (handler-case (rec nil vals1 vals2)
	    (no-maps () nil))))
    (nreverse maps)))
      

(defclass vertex () ())
(defclass edge () ())

(defmacro with-vertex-maps ((vertex-map) &body body)
  `(let ((vertex->nums (make-hash-table :test #'eq))
	 (num1->vertex (make-hash-table :test #'equal))
	 (num2->vertex (make-hash-table :test #'equal))
	 (num1->num2 (make-hash-table :test #'equal))
	 (num2->num1 (make-hash-table :test #'equal)))
     (declare (special vertex->nums num1->vertex num2->vertex num1->num2 num2->num1))
     (iter (for (num1 . num2) in ,vertex-map)
	   (let ((it (make-instance 'vertex)))
	     (setf (gethash it vertex->nums) (cons num1 num2)
		   (gethash num1 num1->vertex) it
		   (gethash num2 num2->vertex) it
		   (gethash num1 num1->num2) num2
		   (gethash num2 num2->num1) num1)))
     ,@body))


(define-condition match-failed (error) ())

(defun already-scanned-p (dessin-id edge-id env)
  (let ((fun (cond ((equal 1 dessin-id) #'car)
		   ((equal 2 dessin-id) #'cdr)
		   (t (error "Wrong use of ALREADY-SCANNED-P.~
                              Expected index 1 or 2 but got: ~a" dessin-id)))))
    (labels ((rec (cur-env)
	       (if (not (null cur-env))
		   (let ((it (cdr (assoc edge-id (funcall fun (car cur-env)) :test #'equal))))
		     (or it
			 (rec (cdr cur-env)))))))
      (rec env))))
		   
(defun vertex-edges (vert dessin)
  (cdr (assoc vert dessin :test #'equal)))

(defun other-vertex-of-an-edge (vert edge dessin)
  (iter (for (vert-id . edges) in dessin)
	(if (equal vert vert-id)
	    (if (equal 2 (length (remove-if-not (lambda (x)
						  (equal edge x))
						edges)))
		(return-from other-vertex-of-an-edge vert-id))
	    (if (find edge edges :test #'equal)
		(return-from other-vertex-of-an-edge vert-id))))
  (error "Unable to find another vertex of an edge -- perhaps, malformed dessin?"))

(defun to-vert-class (dessin-id vert-id)
  (declare (special num1->vertex num2->vertex))
  (gethash vert-id
	   (cond ((equal 1 dessin-id)
		  num1->vertex)
		 ((equal 2 dessin-id)
		  num2->vertex)
		 (t (error "Wrong use of ALREADY-SCANNED-P.~
                            Expected index 1 or 2 but got: ~a" dessin-id)))))

  

(defun try-to-construct-env-patch (offset)
  (declare (special vertex->nums num1->vertex num2->vertex num1->num2 num2->num1
		    dessin1 dessin2 vert1 vert2 edge-env valency))
  (let ((edge-env (cons (cons nil nil) edge-env)))
    (declare (special edge-env))
    (iter (for i from 0 below valency)
	  (let ((edge-id1 (nth i (vertex-edges vert1 dessin1)))
		(edge-id2 (nth (mod (+ i offset) valency) (vertex-edges vert2 dessin2))))
	    (let ((edge1 (already-scanned-p 1 edge-id1 edge-env))
		  (edge2 (already-scanned-p 2 edge-id2 edge-env)))
	      (cond ((and edge1 edge2)
		     (if (not (eq edge1 edge2))
			 (error 'match-failed)))
		    ((and (not edge1) (not edge2))
		     (let ((other-vert1 (to-vert-class 1 (other-vertex-of-an-edge vert1 edge-id1 dessin1)))
			   (other-vert2 (to-vert-class 2 (other-vertex-of-an-edge vert2 edge-id2 dessin2))))
		       (if (not (eq other-vert1 other-vert2))
			   (error 'match-failed)
			   (let ((new-edge (make-instance 'edge)))
			     (push (cons edge-id1 new-edge) (caar edge-env))
			     (push (cons edge-id2 new-edge) (cdar edge-env))))))
		    (t (error 'match-failed))))))
    edge-env))
		

(defun env->edge-map (env)
  (let ((distinct-edge-ids1 (make-hash-table :test #'equal))
	(distinct-edge-ids2 (make-hash-table :test #'equal)))
    (iter outer (for env-patch in env)
	  (iter (for (edge-id1 . edge1) in (car env-patch))
		(for (edge-id2 . edge2) in (cdr env-patch))
		(if (gethash edge-id1 distinct-edge-ids1)
		    (error "Corrupted edge env -- edge-id1 ~a occurs more than once" edge-id1)
		    (setf (gethash edge-id1 distinct-edge-ids1) t))
		(if (gethash edge-id2 distinct-edge-ids2)
		    (error "Corrupted edge env -- edge-id2 ~a occurs more than once" edge-id2)
		    (setf (gethash edge-id2 distinct-edge-ids2) t))
		(if (not (eq edge1 edge2))
		    (error "Corrupted edge env -- wrong order/missing of edges")
		    (in outer (collect (cons edge-id1 edge-id2))))))))
			
(defun dessins-bijectable-p (dessin1 dessin2)
  "Compares two (serialized) dessins by trying to build a bijection between them"
  (declare (special dessin1 dessin2))
  (iter (for vertex-map in (vertex-maps dessin1 dessin2))
	(with-vertex-maps (vertex-map)
	  (labels ((rec-match (vertices-to-check edge-env)
		     (declare (special edge-env))
		     (if (not vertices-to-check)
			 (return-from dessins-bijectable-p
			   (list vertex-map
				 (env->edge-map edge-env))))
		     (destructuring-bind (vert1 . vert2) (car vertices-to-check)
		       (declare (special vert1 vert2))
		       (let ((valency (length (cdr (assoc vert1 dessin1 :test #'equal)))))
			 (declare (special valency))
			 (if (equal 0 valency)
			     (rec-match (cdr vertices-to-check)
					edge-env)
			     (iter (for offset from 0 below valency)
				   (handler-case (rec-match (cdr vertices-to-check)
							    (try-to-construct-env-patch offset))
				     (match-failed () (next-iteration)))))))))
	    (rec-match vertex-map nil))))
  nil)


(defun range (n)
  (defcoroutine %range ()
    (iter (for i from 1 to n)
	  (yield i))
    (coexit!))
  (make-coroutine '%range))

(defcoroutine tensor-power (arg)
  (destructuring-bind (lst n) arg
    (if (equal 0 n)
	(yield nil)
	(iter (for elt in lst)
	      (let ((new-arg (list lst (1- n))))
		(iter (for sub-lst in-coroutine tensor-power with-arg new-arg)
		      (yield (cons elt sub-lst)))))))
  (coexit!))

(defun simple-coro-test1 ()
  (iter (for my-thing in-coroutine (range 100))
	(for my-thing2 in-coroutine (range 20))
	(collect (list my-thing my-thing2))))


(defun %%all-flip-dessin (qed-dessin remaining-cells)
  (lambda-coro ()
    (cond ((not remaining-cells) (yield (serialize-qed qed-dessin)))
	  ((not (cerr (car remaining-cells)))
	   (iter (for res in-coroutine (%%all-flip-dessin qed-dessin (cdr remaining-cells)))
		 (yield res)))
	  (t (let* ((cell1 (car remaining-cells))
		    (cell2 (cerr cell1))
		    (other-cells (remove-if (lambda (x)
					      (or (eq cell1 x) (eq cell2 x)))
					    remaining-cells)))
	       (iter (for res in-coroutine (%%all-flip-dessin qed-dessin other-cells))
		     (yield res))
	       (let ((l-cell (q-unlink! cell1))
		     (r-cell (q-unlink! cell2)))
		 (dq-link! l-cell cell2)
		 (dq-link! r-cell cell1))
	       (iter (for res in-coroutine (%%all-flip-dessin qed-dessin other-cells))
		     (yield res)))))))
	     
		     
(defun %horde->all-flip-dessins (%horde)
  (let ((qed-dessin (%horde->qed-dessin %horde))
	new-cells)
    (with-slots (qed-cells) qed-dessin
      (iter (for cell in qed-cells)
	    (push (q-grow cell) new-cells)
	    (push (d-grow cell) new-cells))
      (%%all-flip-dessin qed-dessin (remove-if-not #'cerr qed-cells)))))
  

(defmacro! collect-coro (coro &optional (arg nil arg-p))
  `(iter (for ,g!-res in-coroutine ,coro ,@(if arg-p `(with-arg ,arg)))
	 (collect ,g!-res)))
  
(defun all-distinct-dessins (n-edges)
  (let ((hordes (distinct-horde-diags n-edges))
	(cur-dessins))
    (lambda-coro ()
      (iter (for horde in hordes)
	    (iter (for serial-dessin in-coroutine (%horde->all-flip-dessins horde))
		  (when (not (find serial-dessin cur-dessins :test #'dessins-bijectable-p))
		    (push serial-dessin cur-dessins)
		    (yield serial-dessin)))))))
    

(defun dessins-clusters (n-edges)
  (let ((clusters nil))
    (lambda-coro ()
      (iter outer (for dessin in-coroutine (all-distinct-dessins n-edges))
	    (iter (for cluster in clusters)
		  (if (find dessin cluster :key #'car :test #'dessins-bijectable-p)
		      (in outer (next-iteration))))
	    (let ((it (mutation-cluster dessin)))
	      (push it clusters)
	      (yield it))))))

(defun serialize-list (lst)
  (format nil "(~{~a~^ ~})" (mapcar (lambda (x)
				      (if (listp x)
					  (serialize-list x)
					  (format nil "~a" x)))
				    lst)))

(defun gen-permanent-distinct-dessins (n-edges)
  (with-open-file (stream #?"~/quicklisp/local-projects/cl-vknots/permanent-dessins-$(n-edges).txt"
			  :direction :output :if-exists :supersede)
    (iter (for dessin in-coroutine (all-distinct-dessins n-edges))
	  (format stream "~a~%" (serialize-list dessin))))
  :success!)

(defparameter *perm-dessins-hash* (make-hash-table :test #'equal))

(defun load-perm-dessins-from-file (n-edges)
  (iter (for elt in-file #?"~/quicklisp/local-projects/cl-vknots/permanent-dessins-$(n-edges).txt"
	     using #'read)
	(collect elt)))
				    

(defun perm-dessins (n-edges)
  (or (gethash n-edges *perm-dessins-hash*)
      (setf (gethash n-edges *perm-dessins-hash*)
	    (load-perm-dessins-from-file n-edges))))
	      

(defun find-permanent-name (dessin)
  (let ((n-edges (/ (apply #'+ (mapcar (lambda (x)
					 (length (cdr x)))
				       dessin))
		    2)))
    ;; OK, this is kind of kludgy, but what of it?...
    (if (equal 0 n-edges)
	"q[N]"
	(let ((perm-dessins (perm-dessins n-edges)))
	  (iter (for perm-dessin in perm-dessins)
		(for i from 0)
		(if (dessins-bijectable-p dessin perm-dessin)
		    (return-from find-permanent-name `(perm-dessin ,n-edges ,i))))
	  (error "Somehow I was unable to find permanent version of this dessin: ~a~%"
		 dessin)))))
	  
(defmacro! with-saved-dessin-cells ((o!-dessin) &body body)
  `(let ((,g!-cells (copy-list (slot-value ,o!-dessin 'qed-cells))))
     (unwind-protect (progn ,@body)
       (setf (slot-value ,o!-dessin 'qed-cells) ,g!-cells))))

(defun n-1-rule-site-p (cell used-cells)
  (declare (ignore used-cells))
  (let* ((other-cell (cerr cell))
	 (ncell (next-real-cell other-cell)))
    (if (and (not (eq other-cell cell))
	     (eq ncell other-cell))
	(list cell))))

(defun 2-rule-site-p (cell used-cells)
  (let* ((other-cell (cerr cell))
	 (ncell (next-real-cell cell))
	 (nother-cell (next-real-cell cell)))
    (if (and (let ((it (list cell ncell other-cell nother-cell)))
	       (equal (length it) (length (remove-duplicates it :test #'eq))))
	     (not (or (gethash ncell used-cells)
		      (gethash other-cell used-cells)
		      (gethash nother-cell used-cells)
		      (gethash cell used-cells)))
	     (eq nother-cell (cerr ncell)))
	(list cell other-cell ncell nother-cell))))

(defun 1-rule-site-p (cell used-cells)
  (declare (ignore used-cells))
  (let* ((ncell (next-real-cell cell))
	 (nncell (next-real-cell ncell)))
    (if (and (let ((it (list cell ncell nncell (cerr cell) (cerr ncell) (cerr nncell))))
	       (equal (length it) (length (remove-duplicates it :test #'eq))))
	     (eq (next-real-cell (cerr cell))
		 (cerr nncell)))
	(progn ;; (format t "~{~a~^ ~}~%"
	       ;; 	       (mapcar (lambda (x)
	       ;; 			 (format nil "(~a ~a)" x (slot-value x 'label)))
	       ;; 		       (list cell ncell nncell (cerr cell) (cerr ncell) (cerr nncell)
	       ;; 			     (next-real-cell (cerr cell)))))
	       (list cell ncell nncell)))))

(defun n-3-rule-site-p (cell used-cells)
  (let* ((ncell (next-real-cell cell))
	 (nncell (next-real-cell ncell)))
    (if (and (let ((it (list cell ncell nncell (cerr cell) (cerr ncell) (cerr nncell))))
	       (equal (length it) (length (remove-duplicates it :test #'eq))))
	     (not (or (gethash ncell used-cells)
		      (gethash nncell used-cells)
		      (gethash cell used-cells)))
	     (eq (next-real-cell nncell)
		 cell))
	(list cell ncell nncell))))

(defun n-2-rule-site-p (cell used-cells)
  (let* ((loop-cell cell)
	 (nloop-cell (next-real-cell loop-cell))
	 (other-cell (cerr cell)))
    (if (and (eq loop-cell
		 (next-real-cell nloop-cell))
	     (let ((it (list cell loop-cell nloop-cell other-cell)))
	       (equal (length it) (length (remove-duplicates it :test #'eq))))
	     (not (or (gethash cell used-cells)
		      (gethash other-cell used-cells))))
	(list cell other-cell))))

(defun all-rule-sites (qed-dessin predicate)
  (let ((used-cells (make-hash-table)))
    (lambda-coro ()
      (iter (for cell in (slot-value qed-dessin 'qed-cells))
	    (if (cerr cell)
		(let ((it (funcall predicate cell used-cells)))
		  (when it
		    (iter (for thing in it)
			  (setf (gethash thing used-cells) t))
		    (yield it))))))))

(defun all-n-1-rule-sites (qed-dessin)
  (all-rule-sites qed-dessin #'n-1-rule-site-p))

(defun all-2-rule-sites (qed-dessin)
  (all-rule-sites qed-dessin #'2-rule-site-p))

(defun all-n-2-rule-sites (qed-dessin)
  (all-rule-sites qed-dessin #'n-2-rule-site-p))

(defun all-1-rule-sites (qed-dessin)
  (all-rule-sites qed-dessin #'1-rule-site-p))

(defun all-n-3-rule-sites (qed-dessin)
  (all-rule-sites qed-dessin #'n-3-rule-site-p))


(defun all-n-1-exprs (qed-dessin)
  (iter (for (cell) in-coroutine (all-n-1-rule-sites qed-dessin))
	(with-saved-dessin-cells (qed-dessin)
	  (let ((q-cell (q-unlink! cell))
		(d-cell (d-unlink! cell)))
	    (dq-link! q-cell d-cell)
	    (extract-connected-component cell qed-dessin)
	    (collect `(* "q[N-1]" ,(find-permanent-name (serialize-qed qed-dessin))))
	    (q-unlink! d-cell)
	    (dq-link! q-cell cell)
	    (dq-link! cell d-cell)))))

(defun all-2-exprs (qed-dessin)
  (iter (for (lb-cell rb-cell lt-cell rt-cell) in-coroutine (all-2-rule-sites qed-dessin))
	(with-saved-dessin-cells (qed-dessin)
	  (let ((q-lt-cell (q-unlink! lt-cell))
		(q-rt-cell (q-unlink! rt-cell))
		(q-lb-cell (q-unlink! lb-cell))
		(q-rb-cell (q-unlink! rb-cell)))
	    (dq-link! q-lt-cell lb-cell)
	    (dq-link! q-rt-cell rb-cell)
	    (extract-connected-component lt-cell qed-dessin)
	    (collect `(* "q[2]" ,(find-permanent-name (serialize-qed qed-dessin))))
	    (q-unlink! lb-cell)
	    (q-unlink! rb-cell)
	    (dq-link! q-lt-cell lt-cell)
	    (dq-link! q-rt-cell rt-cell)
	    (dq-link! q-lb-cell lb-cell)
	    (dq-link! q-rb-cell rb-cell)))))

(defun extract-connected-component (cell qed-dessin)
  (let ((component-cells (let ((it (make-hash-table)))
			   (setf (gethash cell it) t)
			   it))
	(leaf-cells (list cell)))
    (iter (while leaf-cells)
	  (let ((new-leaf-cells nil))
	    (iter (for leaf-cell in leaf-cells)
		  (iter (for fun in '(cqrr cerr cdrr))
			(let ((it (funcall fun leaf-cell)))
			  (when (and it
				     (not (gethash it component-cells)))
			    (setf (gethash it component-cells) t)
			    (push it new-leaf-cells)))))
	    (setf leaf-cells new-leaf-cells)))
    (with-slots (qed-cells) qed-dessin
      (iter (for qed-cell in qed-cells)
	    (if (gethash qed-cell component-cells)
		(collect qed-cell into new-dessin-qed-cells)
		(collect qed-cell into old-dessin-qed-cells))
	    (finally (setf qed-cells old-dessin-qed-cells)
		     (return (make-instance 'qed-dessin
					    :cells new-dessin-qed-cells)))))))
    

(defun divide-into-connected-components (qed-dessin)
  (with-slots (qed-cells) qed-dessin
    (iter (while qed-cells)
	  (collect (extract-connected-component (car qed-cells) qed-dessin)))))


(defun expression-for-possibly-disconnected-dessin (qed-dessin)
  (let ((lst (divide-into-connected-components qed-dessin)))
    (if (equal 1 (length lst))
	(find-permanent-name (serialize-qed (car lst)))
	`(* ,@(mapcar (lambda (x)
			(find-permanent-name (serialize-qed x)))
		      lst)))))


(defun all-n-2-exprs (qed-dessin)
  (iter (for (l-cell r-cell) in-coroutine (all-n-2-rule-sites qed-dessin))
	(with-saved-dessin-cells (qed-dessin)
	  (let ((q-l-cell (q-unlink! l-cell))
		(d-l-cell (d-unlink! l-cell))
		(q-r-cell (q-unlink! r-cell))
		(d-r-cell (d-unlink! r-cell)))
	    (extract-connected-component l-cell qed-dessin)
	    (let* ((forget (unwind-protect (progn (dq-link! q-l-cell d-l-cell)
						  (dq-link! q-r-cell d-r-cell)
						  (expression-for-possibly-disconnected-dessin qed-dessin))
			     (q-unlink! d-l-cell)
			     (q-unlink! d-r-cell)))
		   (contract (unwind-protect (progn (dq-link! q-l-cell d-r-cell)
						    (dq-link! q-r-cell d-l-cell)
						    (expression-for-possibly-disconnected-dessin qed-dessin))
			       (q-unlink! d-l-cell)
			       (q-unlink! d-r-cell))))
	      (collect `(+ (* "q[N-2]" ,forget)
			   ,contract)))
	    (dq-link! q-l-cell l-cell)
	    (dq-link! l-cell d-l-cell)
	    (dq-link! q-r-cell r-cell)
	    (dq-link! r-cell d-r-cell)))))



(defun decompose-only-once (dessin)
  "Input: serialized dessin -- output -- polynomial in permanently named dessins"
  (let ((qed-dessin (grow-everything (deserialize-qed dessin))))
    (nconc (all-n-1-exprs qed-dessin)
	   (all-2-exprs qed-dessin)
	   (all-n-2-exprs qed-dessin))))

    
(defun potentially-nontrivial-relations (n-edges)  
  (remove-if-not (lambda (x)
		   (> (length x) 1))
		 (mapcar #'decompose-only-once (collect-coro (all-distinct-dessins n-edges)))))


;; OK, this one was the first cut on how to extract relations,
;; and already I see that without Mathamatica comparison nothing much can be done ...
