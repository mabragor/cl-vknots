;; QED-cells are just like CONS-cells, but they have 3 places - Q,E and D, respectively.
;; Name comes from quantum electrodynamics, where all vertices are trivalent.

;; In particular, in this project we will use QED-cells to represent Feynman graphs for
;; knot diagrams

(in-package #:cl-vknots)

(cl-interpol:enable-interpol-syntax)

(defclass qed-cell ()
  ((q :initarg :q :initform nil)
   (e :initarg :e :initform nil)
   (d :initarg :d :initform nil)))

(defun qed (q &optional e d)
  (make-instance 'qed-cell :q q :e e :d d))

;; (defun cart-power (lst power)
;;   (let ((elts (coerce lst 'vector)))
;;     (let ((res (make-array (make-list power (length elts)))))
;;       (iter (for indices from 1 to (length elts) to-the-power power)
;; 	    (setf (apply #'aref res indices) (iter (for index in-vector indices)
					

(defmacro define-qed-reader (symbol)
  (let ((str-sym (string symbol)))
    `(defun ,(intern #?"C$(str-sym)RR") (qed-cell)
       (slot-value ,(if (equal 1 (length str-sym))
			'qed-cell
			`(,(intern #?"C$((subseq str-sym 1))RR") qed-cell))
		   ',(intern (string (char str-sym 0)))))))

(defmacro define-qed-writer (symbol)
  (let ((str-sym (string symbol)))
    `(defsetf ,(intern #?"C$(str-sym)RR") (qed-cell) (value)
       (list 'setf (list 'slot-value ,(if (equal 1 (length str-sym))
					  'qed-cell
					  `(list ',(intern #?"C$((subseq str-sym 1))RR") qed-cell))
			 '',(intern (string (char str-sym 0))))
	     value))))

(defmacro define-qed-readers (&rest symbols)
  `(progn ,@(mapcar (lambda (x)
		      `(define-qed-reader ,x))
		    symbols)))
(defmacro define-qed-writers (&rest symbols)
  `(progn ,@(mapcar (lambda (x)
		      `(define-qed-writer ,x))
		    symbols)))

(defmacro define-qed-accessors (&rest symbols)
  `(progn (define-qed-readers ,@symbols)
	  (define-qed-writers ,@symbols)))

(define-qed-accessors q e d
		      qq qe qd
		      eq ee ed
		      dq de dd
		      qqq qqe qqd
		      qeq qee qed
		      qdq qde qdd
		      eqq eqe eqd
		      eeq eee eed
		      edq ede edd
		      dqq dqe dqd
		      deq dee ded
		      ddq dde ddd)


;; (defparameter *a* (qed (qed 'a 'b 'c) (qed 'd 'e 'f) (qed 'g 'h 'i)))

(define-condition link-error (error simple-condition)
  ())

(defmethod print-object :before ((condition link-error) stream)
  (apply #'format stream
         (simple-condition-format-control condition)
         (simple-condition-format-arguments condition)))

(defun link-error (reason &rest args)
  (error 'link-error
	 :format-control reason
	 :format-arguments args))

(defun dq-link (cell1 cell2)
  (if (cdrr cell1)
      (link-error "CELL1 D place is non-nil"))
  (if (cqrr cell2)
      (link-error "CELL2 Q place is non-nil"))
  (dq-link! cell1 cell2))
(defun dq-link! (cell1 cell2)
  (setf (cdrr cell1) cell2)
  (if cell2
      (setf (cqrr cell2) cell1))
  cell1)

(defun qd-link (cell1 cell2)
  (if (cqrr cell1)
      (link-error "CELL1 Q place is non-nil"))
  (if (cdrr cell2)
      (link-error "CELL2 D place is non-nil"))
  (qd-link! cell1 cell2))
(defun qd-link! (cell1 cell2)
  (setf (cqrr cell1) cell2)
  (if cell2
      (setf (cdrr cell2) cell1))
  cell1)


(defun ee-link (cell1 cell2)
  (if (cerr cell1)
      (link-error "CELL1 E place is non-nil"))
  (if (cerr cell2)
      (link-error "CELL2 E place is non-nil"))
  (ee-link! cell1 cell2))
(defun ee-link! (cell1 cell2)
  (setf (cerr cell2) cell1
	(cerr cell1) cell2)
  cell1)
  

(defun d-unlink (cell)
  (if (not (cdrr cell))
      (link-error "CELL's D place is nil - nothing to unlink"))
  (d-unlink! cell))
(defun d-unlink! (cell)
  (let ((it (cdrr cell)))
    (setf (cdrr cell) nil
	  (cqrr it) nil)
    it))

(defun q-unlink (cell)
  (if (not (cqrr cell))
      (link-error "CELL's Q place is nil - nothing to unlink"))
  (q-unlink! cell))
(defun q-unlink! (cell)
  (let ((it (cqrr cell)))
    (setf (cqrr cell) nil
	  (cdrr it) nil)
    it))

(defun e-unlink (cell)
  (if (not (cerr cell))
      (link-error "CELL's E place is nil - nothing to unlink"))
  (e-unlink! cell))
(defun e-unlink! (cell)
  (let ((it (cerr cell)))
    (setf (cerr cell) nil
	  (cerr it) nil)
    it))



(defun q-grow (cell)
  (let ((new-cell (qed nil))
	(q-cell (q-unlink! cell)))
    (dq-link! q-cell new-cell)
    (dq-link! new-cell cell)
    new-cell))

(defun d-grow (cell)
  (let ((new-cell (qed nil))
	(d-cell (d-unlink! cell)))
    (dq-link! cell new-cell)
    (dq-link! new-cell d-cell)
    new-cell))

(defun q-shrink (cell &optional exact-cell-to-shrink)
  (if (and exact-cell-to-shrink
	   (not (eq exact-cell-to-shrink (cqrr cell))))
      :didn-t-do-a-shrink
      (progn (if (not (cqrr cell))
		 (link-error "Q-place is empty, can't shrink"))
	     (if (ceqrr cell)
		 (link-error "Q-place cell's E-place is not empty, can't shrink"))
	     (let ((qq-cell (q-unlink! (cqrr cell))))
	       (q-unlink! cell)
	       (dq-link! qq-cell cell)))))

(defun d-shrink (cell &optional exact-cell-to-shrink)
  (if (and exact-cell-to-shrink
	   (not (eq exact-cell-to-shrink (cqrr cell))))
      :didn-t-do-a-shrink
      (progn (if-debug "cell ~a cqrr ~a cdrr ~a cerr ~a" cell (cqrr cell) (cdrr cell) (cerr cell))
	     (if (not (cdrr cell))
		 (link-error "D-place of ~a is empty, can't shrink on ~a" cell exact-cell-to-shrink))
	     (if (cedrr cell)
		 (link-error "D-place cell ~a's E-place is not empty, can't shrink" cell))
	     (let ((dd-cell (d-unlink! (cdrr cell))))
	       (d-unlink! cell)
	       (dq-link! cell dd-cell)))))

