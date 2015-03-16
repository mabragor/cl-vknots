
(in-package #:cl-vknots)

(cl-interpol:enable-interpol-syntax)

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

(defun %horde-divisions (lst)
  (let ((*acc* nil))
    (labels ((rec (path sub-lst)
	       (if (not sub-lst)
		   (push path *acc*)
		   (let ((i (car sub-lst)))
		     (iter (for (j rest) in (withouts (cdr sub-lst)))
			   (rec (cons `(,i ,j) path) rest))))))
      (rec nil lst))
    *acc*))

(defun horde-divisions (n)
  (%horde-divisions (iter (for i from 1 to n)
			  (collect i))))
	   
(defun %%horde->%horde (prehorde)
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

(defun %%horde->horde (%%horde)
  (make-instance 'horde-diagram :under-lst (%%horde->%horde %%horde)))

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

(defun horde-diagrams-equal-p (horde1 horde2)
  (with-slots ((under-lst1 under-lst)) horde1
    (with-slots ((under-lst2 under-lst)) horde2
      (let ((l1 (length under-lst1))
	    (l2 (length under-lst2)))
	(and (eq l1 l2)
	     (iter (for i from 1 to l2)
		   (rotate-clockwise horde2)
		   (if (equal under-lst1 under-lst2)
		       (return t))
		   (finally (return nil))))))))
					    

(defun grog (n)  
  (mapcar #'under-lst (remove-duplicates (mapcar #'%%horde->horde (horde-divisions (* 2 n)))
					 :test #'horde-diagrams-equal-p)))


(defmacro with-output-env (&body body)
  `(let ((indent 0))
     (declare (special indent))
     (macrolet ((say (smth)
		  `(progn (format stream  "~a" (make-string indent :initial-element #\space))
			  (format stream ,smth)
			  (format stream "~%")))
		(with-indent (&body body)
		  `(let ((indent (+ 2 indent)))
		     (declare (special indent))
		     ,@body)))
       (with-output-to-string (stream)
	 ,@body))))
  

(defun make-digits-letters ()
  (with-output-env
    (say "\\def\\makedigitsletters{")
    (with-indent
	(iter (for i from 0 to 9)
	      (say #?"\\catcode`\\$(i)=11")))
    (say "}")))

(defun make-digits-other ()
  (with-output-env
    (say "\\def\\makedigitsletters{")
    (with-indent
	(iter (for i from 0 to 9)
	      (say #?"\\catcode`\\$(i)=12")))
    (say "}")))

    
(defun %horde->tikz (%horde &key (cmd-name "foo") (radius 1))
  (with-output-env
    (say #?"\\newcommand\\$(cmd-name)[2]{")
    (with-indent
	(say #?"\\draw [ultra thick, black] (#1, #2) circle [radius = $(radius)];")
      (let ((n (length %horde)))
	(iter (for i from 1 to n)
	      (for delta in %horde)
	      (when (< 0 delta)
		(say #?"\\draw [very thick, red] (\$(#1, #2) + ($((floor (* 360 (/ (1- i) n)))):$(radius))\$)
                            to [out=$((floor (+ 180 (* 360 (/ (1- i) n))))),
                                in=$((floor (+ 180 (* 360 (/ (1- (+ i delta)) n)))))]
                            (\$(#1, #2) + ($((floor (* 360 (/ (1- (+ i delta)) n)))):$(radius))\$);")))))
    (say "}~%")))

(defun to-cifers (int)
  (mapcar (lambda (x)
	    (parse-integer (string x)))
	  (coerce (format nil "~a" int) 'list)))

(let ((names '("Zero" "One" "Two" "Three" "Four" "Five" "Six" "Seven" "Eight" "Nine")))
  (defun dumb-name-the-int (int)
    (joinl "" (mapcar (lambda (x)
			(nth x names))
		      (to-cifers int)))))


(defun horde-diagram-pics (n)
  (let ((diags (grog n)))
    (join "~%"
	  (joinl "~%"
		 (iter (for diag in diags)
		       (for i from 1)
		       (collect (%horde->tikz diag :cmd-name
					      #?"foo$((dumb-name-the-int n))n$((dumb-name-the-int i))"))))
	  (with-output-env
	    (say #?"\\global\\def\\foo$((dumb-name-the-int n)){")
	    (with-indent
		(iter (for k from 1 to (length diags))
		      (let ((i (mod k 6))
			    (j (floor k 6)))
			(say #?"\\foo$((dumb-name-the-int n))n$((dumb-name-the-int k)){$((* 3 i))}
                                {$((- (* 3 j)))}")
			(say #?"\\node at ($((* 3 i)), $((- 0 1.5 (* 3 j)))) {$(k)};"))))
	    (say "}~%")))))

(defun horde-diagram-pics! (n)
  (with-open-file (stream "~/drafts/kauffman-in-a-nutshell/foo.tex"
			  :direction :output :if-exists :supersede)
    (format stream "~a" (horde-diagram-pics n))))

	  
(defun gen-horde-diagrams-pics (&key (from 1) (to 4) (fname "~/drafts/kauffman-in-a-nutshell/foo.tex"))
  (with-open-file (stream fname
			  :direction :output :if-exists :supersede)
    (format stream (join "~%"
			 (with-output-env
			   (say "\\documentclass[a4paper]{article}")
			   (say "\\usepackage{tikz}")
			   (say "\\usetikzlibrary{calc}"))
			 (with-output-to-string (stream)
			   (iter (for i from from to to)
				 (format stream (horde-diagram-pics i))))
			 (with-output-env
			   (say "\\begin{document}")
			   (iter (for i from from to to)
				 (say #?"\\section{Horde diagrams with $(i) strands}")
				 (say "\\begin{tikzpicture}[scale=0.5]")
				 (say #?"\\foo$((dumb-name-the-int i))")
				 (say "\\end{tikzpicture}"))
			   (say "\\end{document}"))))))
		     
  