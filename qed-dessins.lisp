
(in-package #:cl-vknots)

;; TADA!

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
  (eq (ceqrr qed-cell) (cqerr qed-cell)))

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
  (eq (ceqrr qed-cell)
      (cqqerr qed-cell)))

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
	  
	