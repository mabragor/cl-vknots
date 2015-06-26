
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
  '((w 1 2 3 4)
    (n 3 4 5 6)
    (w 5 6 1 2)))

(defparameter *virtual-trefoil-next*
  '((w 1 2 3 4)
    (b 3 4 5 6)
    (w 5 6 7 8)
    (n 7 8 9 10)
    (w 9 10 1 2)))


(defparameter *2.1-knot*
  '((w 1 2 3 4)
    (n 3 4 5 6)
    (w 5 6 1 2))
  "Vertices are white according to picture from Bar-Natan")

(defparameter *2.1-link-free-cabled-semi-manually*
  '((w ((begin 1) 1) (v1 1 0) (begin (3 1)) (v1 0 1))
    (w ((begin 1) 2) (2 1) (v1 1 0) (v1 2 1)) (w (v1 2 1) (2 2) (v1 1 2) (begin (4 2)))
    (w (v1 0 1) (v1 1 2) (begin (3 2)) (begin (4 1))) (n (end (3 1)) (v2 1 0) (5 1) (v2 0 1))
    (n (begin (3 1)) (begin (3 2)) (end (3 1)) (end (3 2)))
    (n (begin (4 1)) (begin (4 2)) (end (4 1)) (end (4 2)))
    (n (end (3 2)) (end (4 1)) (v2 1 0) (v2 2 1)) (n (v2 2 1) (end (4 2)) (v2 1 2) (6 2))
    (n (v2 0 1) (v2 1 2) (5 2) (6 1)) (w (5 1) (v3 1 0) ((end 1) 1) (v3 0 1))
    (w (5 2) (6 1) (v3 1 0) (v3 2 1)) (w (v3 2 1) (6 2) (v3 1 2) (2 2))
    (w (v3 0 1) (v3 1 2) ((end 1) 2) (2 1))
    (b (flipover 1 1) (flipover 1 2) (flipover 2 1) (flipover 2 2))
    (b (flipover 2 1) (flipover 2 2) (flipover 3 1) (flipover 3 2))
    (b (flipover 3 1) (flipover 3 2) (flipover 4 1) (flipover 4 2))
    (b (flipover 4 1) (flipover 4 2) (flipover 5 1) (flipover 5 2))
    (d (flipover 5 1) ((begin 1) 1)) (d ((end 1) 1) (flipover 1 1))
    (d (flipover 5 2) ((begin 1) 2)) (d ((end 1) 2) (flipover 1 2))))

(defparameter *2.1-link-free-cabled-semi-manually-2*
  '((w ((begin 1) 1) (v1 1 0) (begin (3 1)) (v1 0 1))
    (w ((begin 1) 2) (2 1) (v1 1 0) (v1 2 1)) (w (v1 2 1) (2 2) (v1 1 2) (begin (4 2)))
    (w (v1 0 1) (v1 1 2) (begin (3 2)) (begin (4 1))) (n (end (3 1)) (v2 1 0) (5 1) (v2 0 1))
    (n (begin (3 1)) (begin (3 2)) (end (3 1)) (end (3 2)))
    ;; (n (begin (4 1)) (begin (4 2)) (end (4 1)) (end (4 2)))
    (d (begin (4 1)) (end (4 1))) (d (begin (3 1)) (end (3 1)))
    (n (end (3 2)) (end (4 1)) (v2 1 0) (v2 2 1)) (n (v2 2 1) (end (4 2)) (v2 1 2) (6 2))
    (n (v2 0 1) (v2 1 2) (5 2) (6 1)) (w (5 1) (v3 1 0) ((end 1) 1) (v3 0 1))
    (w (5 2) (6 1) (v3 1 0) (v3 2 1)) (w (v3 2 1) (6 2) (v3 1 2) (2 2))
    (w (v3 0 1) (v3 1 2) ((end 1) 2) (2 1))
    (b (flipover 1 1) (flipover 1 2) (flipover 2 1) (flipover 2 2))
    (b (flipover 2 1) (flipover 2 2) (flipover 3 1) (flipover 3 2))
    (b (flipover 3 1) (flipover 3 2) (flipover 4 1) (flipover 4 2))
    (b (flipover 4 1) (flipover 4 2) (flipover 5 1) (flipover 5 2))
    (d (flipover 5 1) ((begin 1) 1)) (d ((end 1) 1) (flipover 1 1))
    (d (flipover 5 2) ((begin 1) 2)) (d ((end 1) 2) (flipover 1 2))))



(defparameter *2.1-knot-2-cabled-manually*
  '((w (begin-1 1) (v1 1 0) (3 1) (v1 0 1)) (w (begin-1 2) (2 1) (v1 1 0) (v1 2 1))
    (w (v1 2 1) (2 2) (v1 1 2) (4 2)) (w (v1 0 1) (v1 1 2) (3 2) (4 1))
    (n (3 1) (v2 1 0) (5 1) (v2 0 1)) (n (3 2) (4 1) (v2 1 0) (v2 2 1))
    (n (v2 2 1) (4 2) (v2 1 2) (6 2)) (n (v2 0 1) (v2 1 2) (5 2) (6 1))
    (w (5 1) (v3 1 0) (end-1 1) (v3 0 1)) (w (5 2) (6 1) (v3 1 0) (v3 2 1))
    (w (v3 2 1) (6 2) (v3 1 2) (2 2)) (w (v3 0 1) (v3 1 2) (end-1 2) (2 1))
    (b (end-1 1) (end-1 2) a b) (b a b c d) (b c d e f) (b e f (begin-1 1) (begin-1 2))
    )
  "Manually unlinked 2-cabled diagram of 2.1 knot")

(defparameter *4.1-knot-morse*
  '((w 8 2 7 1)
    (w 3 1 4 2)
    (b 5 4 6 8)
    (b 6 7 5 3)))

(defparameter *virtual-unknotted-trefoil*
  '((w 1 2 3 4)
    (n 3 4 5 6)
    (b 5 6 1 2)))

(defparameter *3.1-vknot*
  '((w 1 9 7 8)
    (n 7 8 2 10)
    (b 2 4 1 3)
    (n 5 3 6 4)
    (w 6 10 5 9)))

(defparameter *3.2-vknot*
  '((w 3 1 4 2)
    (w 4 6 3 5)
    (n 2 7 6 8)
    (b 5 8 1 7)))

(defparameter *3.2-vknot-unknotted*
  '((b 3 1 4 2)
    (w 4 6 3 5)
    (n 2 7 6 8)
    (b 5 8 1 7)))


(defparameter *3.3-vknot*
  '((w 3 1 4 2)
    (n 4 6 3 5)
    (w 7 5 8 6)
    (n 8 2 10 9)
    (w 10 9 7 1)))

(defparameter *3.4-vknot*
  '((w 3 1 4 2)
    (n 4 6 3 5)
    (w 7 5 8 6)
    (n 10 9 7 1)
    (b 8 2 10 9)))

(defparameter *3.5-vknot*
  '((n 1 2 3 4)
    (w 3 4 5 6)
    (w 5 6 7 8)
    (n 7 8 9 10)
    (w 9 10 1 2)))

(defparameter *3.5-vknot-unknotted*
  '((n 1 2 3 4)
    (b 3 4 5 6)
    (w 5 6 7 8)
    (n 7 8 9 10)
    (w 9 10 1 2)))


(defparameter *3.7-vknot*
  '((n 1 2 3 4)
    (w 3 4 5 6)
    (w 5 6 7 8)
    (n 7 8 9 10)
    (b 9 10 1 2)))

(defparameter *4.94-vknot*
  '((w 9 10 8 11)
    (w 8 5 9 7)
    (n 7 6 10 12)
    (n 3 4 5 6)
    (w 1 2 3 4)
    (w 11 12 1 2)))

(defparameter *4.94-vknot-unknotted-to-trefoil-1*
  '((b 9 10 8 11)
    (w 8 5 9 7)
    (n 7 6 10 12)
    (n 3 4 5 6)
    (w 1 2 3 4)
    (w 11 12 1 2)))

(defparameter *4.94-vknot-unknotted-to-trefoil-2*
  '((w 9 10 8 11)
    (b 8 5 9 7)
    (n 7 6 10 12)
    (n 3 4 5 6)
    (w 1 2 3 4)
    (w 11 12 1 2)))

(defparameter *4.94-vknot-unknotted-to-unknot-1*
  '((w 9 10 8 11)
    (w 8 5 9 7)
    (n 7 6 10 12)
    (n 3 4 5 6)
    (b 1 2 3 4)
    (w 11 12 1 2)))

(defparameter *4.94-vknot-unknotted-to-unknot-2*
  '((w 9 10 8 11)
    (w 8 5 9 7)
    (n 7 6 10 12)
    (n 3 4 5 6)
    (w 1 2 3 4)
    (b 11 12 1 2)))


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

(defun link-free-cable (diagram n)
  (let ((total-charge (iter (for vertex in diagram)
			    (cond ((string= "B" (string (car vertex))) (summing +1))
				  ((string= "W" (string (car vertex))) (summing -1)))))
	(my-diag (copy-tree diagram)))
    (let ((begin-edge (cadar my-diag)))
      (setf (cadar my-diag) `(begin ,begin-edge))
      (iter (for vertex in my-diag)
	    (iter (for edge on (cdr vertex))
		  (if (equal begin-edge (car edge))
		      (setf (car edge) `(end ,begin-edge)))))
      (let ((num-flipovers (* n (abs total-charge))))
	(nconc (cable my-diag n)
	       (iter (for i from 1 to num-flipovers)
		     (nconcing (flipover n i (if (< 0 total-charge) 'w 'b))))
	       (iter (for i from 1 to n)
		     (collect `(d (flipover ,(1+ num-flipovers) ,i)
				  ,(if (equal 1 n)
				       `(begin ,begin-edge)
				       `((begin ,begin-edge) ,i))))
		     (collect `(d ,(if (equal 1 n)
				       `(end ,begin-edge)
				       `((end ,begin-edge) ,i))
				  (flipover 1 ,i)))))))))

	       

(defun flipover (n start-num color)
  (cond ((equal 1 n) (copy-tree `((d (flipover ,start-num 1) (flipover ,(1+ start-num) 1)))))
	((equal 2 n) (copy-tree `((,color (flipover ,start-num 1) (flipover ,start-num 2)
					  (flipover ,(1+ start-num) 1) (flipover ,(1+ start-num) 2)))))
	(t (let ((res (copy-tree `((,color (flipover ,start-num 1) (intraflipover ,start-num 2)
					   (flipover ,(1+ start-num) 1) (flipover ,(1+ start-num) 2))
				   (,color (flipover ,start-num ,(1- n)) (flipover ,start-num ,n)
					   (intraflipover ,start-num ,(1- n)) (flipover ,(1+ start-num) ,n))))))
	     (nconc res
		    (iter (for i from 2 to (- n 2))
			  (collect (copy-tree `(,color (flipover ,start-num ,i)
						       (intraflipover ,start-num ,(1+ i))
						       (intraflipover ,start-num ,i)
						       (flipover ,(1+ start-num) ,(1+ i)))))))
	     res))))

		   

(defun planar->seifert (diagram)
  (let ((the-hash (make-hash-table :test #'equal))
	(b-hash (make-hash-table :test #'equal))
	(e-edge-count 0)
	res)
    (iter (for (op . args) in diagram)
	  (if (equal 4 (length args))
	      (destructuring-bind (lb rb lt rt) args
		(if (string= "N" (string op))
		    (setf (gethash lb the-hash) (cons rt nil)
			  (gethash rb the-hash) (cons lt nil))
		    (setf (gethash lb the-hash) (cons lt (list op (incf e-edge-count)))
			  (gethash rb the-hash) (cons rt (list op e-edge-count))))
		(setf (gethash lb b-hash) t
		      (gethash rb b-hash) t))
	      (destructuring-bind (bottom top) args
		(cond ((string= "D" (string op)) (setf (gethash bottom the-hash) (cons top nil)))
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
