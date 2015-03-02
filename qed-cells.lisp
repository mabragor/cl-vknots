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

(defun cart-power (lst power)
  (let ((elts (coerce lst 'vector)))
    (let ((res (make-array (make-list power (length elts)))))
      (iter (for indices from 1 to (length elts) to-the-power power)
	    (setf (apply #'aref res indices) (iter (for index in-vector indices)
					

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



(defparameter *a* (qed (qed 'a 'b 'c) (qed 'd 'e 'f) (qed 'g 'h 'i)))