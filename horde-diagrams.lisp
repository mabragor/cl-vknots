
(in-package #:cl-vknots)

(defgeneric next-iter (obj)
  (:documentation "Main iteration method"))

(define-condition stop-iteration (error)
  ()
  (:documentation "Raized when iterator is depleted"))

(defun withouts (lst)
  (iter (for i from 1 to (length lst))
	(collect (list (elt lst (1- i))
		       (nconc (subseq lst 0 (1- i))
			      (subseq lst i))))))

(defparameter *acc* nil)

(defun horde-divisions (lst)
  (let ((*acc* nil))
    (labels ((rec (path sub-lst)
	       (if (not sub-lst)
		   (push path *acc*)
		   (let ((i (car sub-lst)))
		     (iter (for (j rest) in (withouts (cdr sub-lst)))
			   (rec (cons `(,i ,j) path) rest))))))
      (rec nil lst))
    *acc*))
		       
	   
(defun preprehorde->prehorde (prehorde)
  (let ((res (make-array (* 2 (length prehorde)))))
    (iter (for (i j) in prehorde)
	  (setf (elt res (1- i)) (- j i)
		(elt res (1- j)) (- i j)))
    (coerce res 'list)))

(defclass horde-diagram ()
  ((under-lst :initarg :under-lst)))

(defmethod rotate-clockwise (smth)
  ())
(defmethod rotate-counterclockwise (smth)
  ())

(defun under-lst (horde)
  (slot-value horde 'under-lst))

(defun %rotate-clockwise (horde)
  (let ((newval (- (length horde) (car horde)))
	(newhead (cdr horde)))
    (setf (nth (car horde) horde) newval
	  (car horde) (- newval)
	  (cdr (last horde)) horde
	  (cdr horde) nil)
    newhead))
      

(defmethod rotate-clockwise ((horde horde-diagram))
  (with-slots (under-lst) horde
    (setf under-lst (%rotate-clockwise under-lst)))
  horde)

