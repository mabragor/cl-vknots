
(in-package #:cl-vknots)

(defparameter *kishino-diagram*
  '((n 1 2 4 3)
    (b 4 3 5 11)
    (w 6 11 1 2)
    (b 5 12 7 8)
    (w 10 9 6 12)
    (n 7 8 10 9)))

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