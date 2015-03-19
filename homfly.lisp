
(in-package #:cl-vknots)


;; In this file we will write a proper HOMFLY calculation, which will be able to
;; withstand the strain of cabled diagrams (at least 2- and 3- cabled)



;; The iteration of all sub-dessins of a serialized dessin is very easy

(defparameter *the-dessin* nil)

(defparameter *torus-dessin* '((1 1 2) (2 1 3 2 4) (3 3 4)))

(defun over-all-subdessins (dessin callback)
  (let ((the-dessin dessin))
    (labels ((rec (cur-dessin top)
	       (if (not cur-dessin)
		   (if callback
		       (funcall callback the-dessin))
		   (if (not (car cur-dessin))
		       (rec (cdr cur-dessin) t)
		       (progn (rec (cons (cdar cur-dessin)
					 (cdr cur-dessin)) nil)
			      ;; we skip the loop number
			      (if (not top)
				  (let ((it (caar cur-dessin)))
				    (unwind-protect (progn (setf (caar cur-dessin) 0)
							   (rec (cons (cdar cur-dessin)
								      (cdr cur-dessin)) nil))
				      (setf (caar cur-dessin) it)))))))))
      (rec dessin t))))

(let ((acc  nil))
  (defun reset-simple-collector ()
    (setf acc nil))
  (defun simple-collector (dessin)
    (push (copy-tree dessin) acc))
  (defun output-simple-collector ()
    (let ((it (nreverse acc)))
      (reset-simple-collector)
      it)))
	    
    
				  
