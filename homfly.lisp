
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
	    
    
;; OK, now I need this code also to:
;; * (done) take into account the cons-cells, that can be in place of just numbers
;; * (done) calculate the q-charge of the sub-dessin as it goes along
