
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
  (if (eq :empty horde)
      :empty
      (slot-value horde 'under-lst)))

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
		(let ((l (length diags))
		      (done nil))
		  (iter (for j from 0)
			(while (not done))
			(say "~%~%\\begin{tikzpicture}[scale=0.5]")
			(iter (for i from 0 to 5)
			      (let ((k (+ (* 6 j) i)))
				(when (>= k l)
				  (setf done t)
				  (terminate))
				(say #?"\\foo$((dumb-name-the-int n))n$((dumb-name-the-int (1+ k))){$((* 3 i))}
                                       {$((- (* 3 j)))}")
				(say #?"\\node at ($((* 3 i)), $((- 0 1.5 (* 3 j)))) {$((1+ k))};")))
			(say "\\end{tikzpicture}~%~%"))))
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
				 (say #?"\\foo$((dumb-name-the-int i))"))
			   (say "\\end{document}"))))))
		     
  
(defun %horde->qed-dessin (%horde)
  (let ((pre-res (make-array (length %horde))))
    (iter (for i from 0 to (1- (length %horde)))
	  (setf (elt pre-res i) (qed nil)))
    (iter (for i from 0)
	  (for delta in %horde)
	  (when (< 0 delta)
	    (ee-link (elt pre-res i) (elt pre-res (+ i delta))))
	  (dq-link (elt pre-res (mod (1+ i) (length %horde)))
		   (elt pre-res i)))
    (make-instance 'qed-dessin :cells (coerce pre-res 'list))))

(defun groger2 (x)
  (handler-case (decompose (%horde->qed-dessin x))
    (error () "Fail")))

(defun groger3 (x)
  (mathematica-serialize x))
  

(defmacro! mathematica-bulk-send (pattern o!-lst)
  `(with-open-file (stream "lisp-out.txt"
			   :direction :output :if-exists :supersede)
     (iter (for ,pattern in ,o!-lst)
	   ,@(if (atom pattern)
		 `((format stream ,#?"$((stringify-symbol pattern)) = ~a;~%" ,pattern))
		 (mapcar (lambda (x)
			   `(format stream ,#?"$((stringify-symbol x)) = ~a;~%" ,x))
			 pattern)))))

(defun mathematica-bulk-run (script-name)
  (multiple-value-bind (out err errno)
      (script #?"math -script $(script-name) > $(*fname-prefix*)lisp-in.txt")
    ;; (declare (ignore out))
    (if (not (zerop errno))
	(error err)
	out)))

(defun mathematica-bulk-receive ()
  (iter (for expr in-file #?"$(*fname-prefix*)lisp-in.txt" using #'read-line)
	(collect expr)))


(defun mathematica-simplify-and-canonicalize (lst)
  (mathematica-bulk-send expr lst)
  (mathematica-bulk-run #?"$(*fname-prefix*)simple-script-input.m"))

(defmacro mathematica-bulk-exec (pattern script lst)
  `(progn (mathematica-bulk-send ,pattern ,lst)
	  (mathematica-bulk-run ,script)
	  (mathematica-bulk-receive)))

(defun grog2 (n)
  (let ((it (grog n)))
    (mathematica-simplify-and-canonicalize (mapcar (lambda (x)
						     (groger3 (groger2 x)))
						   it))
    (let ((dimens
	   (iter (for expr in-file #?"$(*fname-prefix*)lisp-in.txt" using #'read-line)
		 (collect
		     (regex-replace-all "\\^"
					(regex-replace-all "\\\\left|\\\\right"
							   (regex-replace-all "q\\(([^()]+)\\)"
									      expr "[\\1]")
							   "")
					"\\textsuperscript")))))
      (generate-tex-horde-section n it dimens))))

(defun mk-dimensions-hash (diags dimens)
  (let ((res (make-hash-table :test #'equal)))
    (iter (for diag in diags)
	  (for i from 1)
	  (for dimen in dimens)
	  (push (cons i diag) (gethash dimen res nil)))
    res))

(defun diags->tex (diags n line-width)
  (declare (ignore line-width))
  (with-output-env
    (iter (for (num . diag) in diags)
	  (say "\\begin{tikzpicture}[scale=0.5]")
	  (say #?"\\foo$((dumb-name-the-int n))n$((dumb-name-the-int num)){0}{0}")
	  (say #?"\\node at (0, - 1.5) {$(num)};")
	  (say "\\end{tikzpicture}"))))
  

(defun dimensions-hash->tex (hash n &optional (line-width 3))
  (with-output-env
    ;; (say "\\begin{equation}")
    (say "\\begin{longtable}{|p{.50\\textwidth}|p{.50\\textwidth}|}")
    (say "\\hline")
    (iter (for (dimen diags) in-hashtable hash)
	  (for i from 0)
	  (say #?"$((diags->tex diags n line-width)) & \\parbox[t]{.50\\textwidth}{$(dimen)} \\\\")
	  (say "\\hline")
	  (when (zerop (mod i 3))
	    (say "\\end{longtable} \\par")
	    ;; (say "\\end{equation}")
	    ;; (say "\\begin{equation}")
	    (say "\\begin{longtable}{|p{.50\\textwidth}|p{.50\\textwidth}|}")
	    (say "\\hline")))
    (say "\\end{longtable} \\par")
    ;; (say "\\end{equation}")
    ))

(defun diags-cmds (diags n)
  (with-output-env
    (iter (for diag in diags)
	  (for i from 1)
	  (say (%horde->tikz diag :cmd-name
			     #?"foo$((dumb-name-the-int n))n$((dumb-name-the-int i))")))))


(defun generate-tex-horde-section (n diags dimens)
  (let ((hash (mk-dimensions-hash diags dimens)))
    (with-output-env
      (say #?"\\section{Horde diagrams with $(n) strands}")
      (say (diags-cmds diags n))
      (say (dimensions-hash->tex hash n)))))


(defun gen-tex-header ()
  (with-output-env
    (say "\\documentclass[a4paper]{article}")
    (say "\\usepackage{longtable}")
    (say "\\usepackage{tikz}")
    (say "\\usetikzlibrary{calc}")
    (say "\\textheight 24.5cm")
    (say "\\textwidth 17cm")
    (say "\\voffset=-1.1in")
    (say "\\hoffset= - 1.0in")
    (say "\\begin{document}")))

(defun gen-tex-tailer ()
  (with-output-env
    (say "\\end{document}")))    

(defun gen-horde-diagrams-dimens (&key (from 1) (to 4) (fname "~/drafts/kauffman-in-a-nutshell/bar.tex"))
  (with-open-file (stream fname
			  :direction :output :if-exists :supersede)
    (format stream (gen-tex-header))
    (format stream (with-output-env
		     (iter (for i from from to to)
			   (say (grog2 i)))))
    (format stream (gen-tex-tailer))))

(defun reflect-horde-diag (horde)
  (if (eq horde :empty)
      :empty
      (make-instance 'horde-diagram
		     :under-lst (mapl (lambda (x)
					(setf (car x) (- (car x))))
				      (reverse (slot-value horde 'under-lst))))))



(defun horde-length (horde)
  (if (eq :empty horde)
      0
      (/ (length (slot-value horde 'under-lst))
	 2)))


(defun horde-primitive-equal-p (horde1 horde2)
  (if (or (eq horde1 :empty) (eq horde2 :empty))
      (eq horde1 horde2)
      (equal (slot-value horde1 'under-lst)
	     (slot-value horde2 'under-lst))))

(defmacro-driver! (for var n-in-diag-rotations horde)
  "Destructively rotate diagram in all possible ways, returning it to the same
state, if iteration does not finish early"
  (let ((kwd (if generate 'generate 'for)))
    `(progn (with ,g!-nrotations = 0)
	    (with ,g!-horde = ,horde)
	    (with ,g!-tot-rotations = (if (eq :empty ,g!-horde)
					  1
					  (length (slot-value ,g!-horde 'under-lst))))
	    (,kwd ,var next (if (equal ,g!-tot-rotations ,g!-nrotations)
				(terminate)
				(progn (incf ,g!-nrotations)
				       (if (eq :empty ,g!-horde)
					   :empty
					   (rotate-clockwise (if-first-time ,g!-horde
									    ,var)))))))))




(defun simple-in-diag-rotations-test ()
  (iter (for diag n-in-diag-rotations (make-instance 'horde-diagram :under-lst '(2 3 -2 2 -3 -2)))
	(collect (copy-list (under-lst diag)))))
