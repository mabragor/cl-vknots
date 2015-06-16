
(in-package #:cl-vknots)

(cl-interpol:enable-interpol-syntax)

(defparameter *kishino-diagram*
  '((n 1 2 4 3)
    (b 4 3 5 11)
    (w 6 11 1 2)
    (b 5 12 7 8)
    (w 10 9 6 12)
    (n 7 8 10 9)))

(defparameter *simple-trefoil*
  '((b 1 2 3 4)
    (b 3 4 5 6)
    (b 5 6 1 2)))

(defparameter *virtual-trefoil*
  '((b 1 2 3 4)
    (n 3 4 5 6)
    (b 5 6 1 2)))

(defparameter *virtual-unknotted-trefoil*
  '((w 1 2 3 4)
    (n 3 4 5 6)
    (b 5 6 1 2)))


(defun bud-vertex (vertex n &optional vertex-id)
  (destructuring-bind (op lb rb lt rt) vertex
    (let* ((id (or vertex-id (gensym "VERTEX")))
	   (top (- (* 2 n) 2)))
      (let ((corners (if (equal 1 n)
			 (list (list op lb rb lt rt))
			 `((,op (,lb 1) (,id 1 0) (,lt 1) (,id 0 1))
			   (,op (,lb ,n) (,rb 1) (,id ,(1- top) 0) (,id ,top 1))
			   (,op (,id ,top ,(1- top)) (,rb ,n) (,id ,(1- top) ,top) (,rt ,n))
			   (,op (,id 0 ,(1- top)) (,id 1 ,top) (,lt ,n) (,rt 1)))))
	    (sides (nconc (iter (for i from 1 to (- n 2))
				(collect `(,op (,lb ,(1+ i)) (,id ,(1+ (* 2 i)) 0)
					       (,id ,(1- (* 2 i)) 0) (,id ,(* 2 i) 1))))
			  (iter (for i from 1 to (- n 2))
				(collect `(,op (,id 0 ,(1- (* 2 i))) (,id 1 ,(* 2 i))
					       (,lt ,(1+ i)) (,id 0 ,(1+ (* 2 i))))))
			  (iter (for i from 1 to (- n 2))
				(collect `(,op (,id ,top ,(1- (* 2 i))) (,rb ,(1+ i))
					       (,id ,(1- top) ,(* 2 i)) (,id ,top ,(1+ (* 2 i))))))
			  (iter (for i from 1 to (- n 2))
				(collect `(,op (,id ,(* 2 i) ,(1- top)) (,id ,(1+ (* 2 i)) ,top)
					       (,id ,(1- (* 2 i)) ,top) (,rt ,(1+ i)))))))
	    (bulk (iter outer (for i from 1 to (- n 2))
			(iter (for j from 1 to (- n 2))
			      (in outer
				  (collect `(,op (,id ,(* 2 i) ,(1- (* 2 j))) (,id ,(1+ (* 2 i)) ,(* 2 j))
						 (,id ,(1- (* 2 i)) ,(* 2 j)) (,id ,(* 2 i) ,(1+ (* 2 j))))))))))
	(nconc corners
	       sides
	       bulk)))))


(defun cable (diagram n)
  (iter (for i from 1)
	(for vertex in diagram)
	(collect (bud-vertex vertex n (intern #?"V$(i)")) into res)
	(finally (return (apply #'nconc res)))))


(defun planar->seifert (diagram)
  (let ((the-hash (make-hash-table :test #'equal))
	(b-hash (make-hash-table :test #'equal))
	(e-edge-count 0)
	res)
    (iter (for (op . args) in diagram)
	  (if (equal 4 (length args))
	      (destructuring-bind (lb rb lt rt) args
		(if (eq 'n op)
		    (setf (gethash lb the-hash) (cons rt nil)
			  (gethash rb the-hash) (cons lt nil))
		    (setf (gethash lb the-hash) (cons lt (list op (incf e-edge-count)))
			  (gethash rb the-hash) (cons rt (list op e-edge-count))))
		(setf (gethash lb b-hash) t
		      (gethash rb b-hash) t))
	      (destructuring-bind (bottom top) args
		(cond ((eq :d op) (setf (gethash bottom the-hash) (cons top nil)))
		      (t (error "Don't know how to seifertize this ~a" op))))))
    (let ((cur-loop nil))
      (iter (for loop-start next (multiple-value-bind (got key val) (pophash b-hash)
				   (declare (ignore val))
				   (if (not got)
				       (terminate)
				       key)))
	    (for loop-num from 1)
	    (setf cur-loop (list loop-num))
	    (iter (initially (setq edge nil))
		  (initially (setq e-edge nil))
		  (for (edge e-edge) next (cond ((eq :terminate edge) (terminate))
						((not edge) (list loop-start nil))
						(t (destructuring-bind (next-edge . next-e-edge)
						       (gethash edge the-hash)
						     (remhash next-edge b-hash)
						     (list (if (equal loop-start next-edge)
							       :terminate
							       next-edge)
							   next-e-edge)))))
		  (if e-edge (push e-edge cur-loop)))
	    (push (nreverse cur-loop) res))
      (nreverse res))))
					      

;; Ok, so now the only thing that remains to be done is
;; to refresh computation of hypercube and HOMFLY using DECOMPOSE instead of N-DESSIN-RECURSION...

;; ... and, of course, tests for this PLANAR->SEIFERT function, to ensure it works correctly ...    

(defparameter *10-132* '((b 1 4 2 3)
			 (w 6 5 7 4)
			 (w 8 7 9 1)
			 (w 10 3 11 5)
			 (b 13 12 8 6)
			 (w 20 2 15 10)
			 (b 15 11 19 12)
			 (w 19 16 20 18)
			 (w 14 17 13 16)
			 (w 9 18 14 17)))
			 
(defparameter *curious-horde* '(6 3 5 6 -3 5 -6 -5 3 -6 -5 -3))
