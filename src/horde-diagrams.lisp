
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
  (mapcar #'under-lst (remove-duplicates (remove-if #'easily-simplifiable-p
						    (mapcar #'%%horde->horde
							    (remove-if #'disconnected-p
								       (horde-divisions (* 2 n)))))
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

(defun %horde->puts (%horde &key (cmd-name "foo") (radius 20))
  (with-output-env
    (say #?"\\newcommand\\$(cmd-name)[2]{")
    (with-indent
	(say "\\put(#1,#2){")
      (with-indent
	  (say "\\thicklines")
	(with-indent (say "\\put(0,0){ \\linethickness{1mm}")
	  (let ((control-point (* radius 0.9)))
	    (say (frnl "\\qbezier(~,2f,0)(~,2f,~,2f)(0,~,2f)" radius control-point control-point radius))
	    (say (frnl "\\qbezier(0,~,2f)(-~,2f,~,2f)(-~,2f,0)" radius control-point control-point radius))
	    (say (frnl "\\qbezier(-~,2f,0)(-~,2f,-~,2f)(0,-~,2f)" radius control-point control-point radius))
	    (say (frnl "\\qbezier(0,-~,2f)(~,2f,-~,2f)(~,2f,0)" radius control-point control-point radius))
	    (say "}")))
	(say "\\linethickness{0.5mm}")
	(let ((n (length %horde)))
	  (iter (for i from 1 to n)
		(for delta in %horde)
		(when (< 0 delta)
		  (let ((phi-begin (* 2 pi (/ (1- i) n)))
			(phi-end (* 2 pi (/ (1- (+ i delta)) n))))
		    (let ((xbegin (* radius (cos phi-begin)))
			  (ybegin (* radius (sin phi-begin)))
			  (xend (* radius (cos phi-end)))
			  (yend (* radius (sin phi-end))))
		      (say (frnl "\\qbezier(~,2f,~,2f)(0,0)(~,2f,~,2f)"
				 xbegin ybegin xend yend))))))))
      (say "}~%"))
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
  (handler-case (try-to-decompose-diag x)
    (error () "Fail")))

(defun groger3 (x)
  (mathematica-serialize x))
  

(defmacro mathematica-bulk-send (pattern o!-lst)
  (let ((g!-lst (gensym "LST")))
    `(let ((,g!-lst ,o!-lst))
       (with-open-file (stream #?"$(*fname-prefix*)lisp-out.txt"
			       :direction :output :if-exists :supersede)
	 (iter (for ,pattern in ,g!-lst)
	       ,@(if (atom pattern)
		     `((format stream ,#?"$((stringify-symbol pattern)) = ~a;~%" ,pattern))
		     (mapcar (lambda (x)
			       `(format stream ,#?"$((stringify-symbol x)) = ~a;~%" ,x))
			     pattern)))))))

(defun mathematica-bulk-run (script-name)
  (multiple-value-bind (out err errno)
      (script #?"math -script $(script-name) > $(*fname-prefix*)lisp-in.txt")
    ;; (declare (ignore out))
    (if (not (zerop errno))
	(error err)
	out)))



(defun script1 (str)
  (multiple-value-bind (out err errno) (script str)
    (if (not (zerop errno))
	(error err)
	out)))

(defun mathematica-bulk-receive ()
  (iter (for expr in-file #?"$(*fname-prefix*)lisp-in.txt" using #'read-line)
	(collect expr)))


(defun mathematica-simplify-and-canonicalize (lst)
  (mathematica-bulk-send expr lst)
  (mathematica-bulk-run #?"$(*fname-prefix*)simple-script-input.m"))

(defun mathematica-q-poly-canonicalize (lst)
  (mathematica-bulk-send expr lst)
  (mathematica-bulk-run #?"$(*fname-prefix*)q-poly-canonicalize.m"))

(defmacro mathematica-bulk-exec (pattern script lst)
  `(progn (mathematica-bulk-send ,pattern ,lst)
	  (mathematica-bulk-run ,script)
	  (mathematica-bulk-receive)))

;; (defun mathe

(defun grog2 (n)
  (let ((it (grog n)))
    (mathematica-q-poly-canonicalize (mapcar (lambda (x)
					       (groger3 (groger2 x)))
					     it))
    (let ((dimens
	   (iter (for expr in-file #?"$(*fname-prefix*)lisp-in.txt" using #'read-line)
		 (collect
		     (regex-replace-all "\\^"
					(regex-replace-all "\\\\left|\\\\right"
							   (regex-replace-all "q\\[([^\\[\\]]+)\\]"
									      expr "[\\1]")
							   "")
					"\\textsuperscript ")))))
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

(defmacro-driver (for var n-in-diag-rotations horde)
  "Destructively rotate diagram in all possible ways, returning it to the same
state, if iteration does not finish early"
  (let ((kwd (if generate 'generate 'for))
	(g!-nrotations (gensym "NROTATIONS"))
	(g!-horde (gensym "HORDE"))
	(g!-tot-rotations (gensym "TOT-ROTATIONS")))
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

(defun easily-simplifiable-p (horde)
  (let ((lst (under-lst horde)))
    (or ;; (disconnected-p lst)
	(two-in-a-row-p lst)
	(anti-two-in-a-row-p lst))))

(defun two-in-a-row-p (lst)
  (iter (for elt on lst)
	(if (null (cdr elt))
	    (if (and (> 0 (car elt))
		     (< 1 (car lst))
		     (equal (+ (length lst) (car elt))
			    (car lst)))
		(return t)))
	(if (and (< 1 (car elt))
		 (equal (car elt) (cadr elt)))
	    (return t))
	(finally (return nil))))

(defun anti-two-in-a-row-p (lst)
  (iter (for elt on lst)
	(if (null (cdr elt))
	    (if (and (> 0 (car elt))
		     (< 0 (car lst))
		     (equal (+ (length lst) (car elt))
			    (+ 2 (car lst))))
		(return t)))
	(if (and (< 0 (car elt))
		 (< 0 (cadr elt))
		 (equal (car elt) (+ 2 (cadr elt))))
	    (return t))
	(finally (return nil))))

(defun hordes-intersect-p (horde1 horde2)
  (let ((shorde1 (sort (copy-list horde1) #'<))
	(shorde2 (sort (copy-list horde2) #'<)))
    (or (and (< (car shorde1) (car shorde2))
	     (> (cadr shorde1) (car shorde2))
	     (< (cadr shorde1) (cadr shorde2)))
	(and (< (car shorde2) (car shorde1))
	     (> (cadr shorde2) (car shorde1))
	     (< (cadr shorde2) (cadr shorde1))))))
	
    
(defun disconnected-p (prehorde)
  (let ((cluster (make-hash-table :test #'equal))
	(new-hordes (make-hash-table :test #'equal))
	(horde-intersections (make-hash-table :test #'equal)))
    (iter (for horde in prehorde)
	  (iter (for other-horde in prehorde)
		(if (hordes-intersect-p horde other-horde)
		    (push other-horde (gethash horde horde-intersections)))))
    (setf (gethash (car prehorde) cluster) t)
    (setf (gethash (car prehorde) new-hordes) t)
    (iter (while (not (equal 0 (hash-table-count new-hordes))))
	  (let ((new-intersections nil))
	    (iter (for (new-horde nil) in-hashtable new-hordes)
		  (setf new-intersections (append new-intersections (gethash new-horde horde-intersections))))
	    (clrhash new-hordes)
	    (iter (for potential-new-horde in new-intersections)
		  (when (not (gethash potential-new-horde cluster))
		    (setf (gethash potential-new-horde cluster) t
			  (gethash potential-new-horde new-hordes) t)))))
    (not (equal (hash-table-count cluster) (length prehorde)))))
		    

(defun all-prehorde-flips (prehorde)
  (let ((n (* 2 (length prehorde))))
    (iter outer (for horde1 in prehorde)
	  (iter (for horde2 in prehorde)
		(if (hordes-intersect-p horde1 horde2)
		    (in outer (collect (permute-prehorde prehorde
							 (double-flip-permutation horde1
										  horde2
										  n)))))))))

(defun is-really-new (prehorde all-flips-so-far)
  (let ((new-horde (%%horde->horde prehorde)))
    (iter (for horde in all-flips-so-far)
	  (if (horde-diagrams-equal-p new-horde horde)
	      (return-from is-really-new nil)))
    new-horde))

(defun really-all-prehorde-flips (prehorde)
  (let ((all-flips (list (%%horde->horde prehorde)))
	(new-diags (list prehorde))
	(old-new-diags nil))
    (iter (while new-diags)
	  (setf old-new-diags new-diags
		new-diags nil)
	  (iter (for new-diag in old-new-diags)
		(iter (for new-prehorde in (all-prehorde-flips new-diag))
		      (let ((it (is-really-new new-prehorde all-flips)))
			(when it
			  (push it all-flips)
			  (push new-prehorde new-diags))))))
    (mapcar (lambda (x)
	      (%horde->prehorde (under-lst x)))
	    all-flips)))


(defun horde-end-between (horde1 horde2)
  (cond ((and (< (car horde1) (car horde2))
	      (< (car horde2) (cadr horde1)))
	 (car horde2))
	((and (< (car horde1) (cadr horde2))
	      (< (cadr horde2) (cadr horde1)))
	 (cadr horde2))
	(t (error "Somehow hordes ~a and ~a seem to not intersect" horde1 horde2))))
      
(defun horde-other-point (horde point)
  (if (equal point (car horde))
      (cadr horde)
      (car horde)))

(defun rotate-to-position (pos vector)
  (let ((n (length vector)))
    (let ((res (make-array n)))
      (iter (for i from 0 below n)
	    (setf (elt res i) (elt vector (mod (+ pos i) n))))
      res)))

(defun double-flip-permutation (horde1 horde2 n)
  (let ((res (make-array n :element-type 'integer :initial-element 0))
	(between-end (horde-end-between horde1 horde2)))
    (let ((circle1 (make-array (- (cadr horde1) (car horde1)) :element-type 'integer :initial-element 0))
	  (circle2 (make-array (- n (- (cadr horde1) (car horde1))) :element-type 'integer :initial-element 0)))
      (iter (for dst-index from 0)
	    (for src-index from (car horde1) below (cadr horde1))
	    (setf (elt circle1 dst-index) src-index))
      (iter (for dst-index from 0 below (- n (- (cadr horde1) (car horde1))))
	    (for src-index from (cadr horde1))
	    (setf (elt circle2 dst-index) (1+ (mod (1- src-index) n))))
      ;; (list circle1 circle2))))
      ;; between-end)))
      (let ((rotated-circle1 (rotate-to-position (position between-end circle1)
						 circle1))
	    (rotated-circle2 (rotate-to-position (position (horde-other-point horde2 between-end)
							   circle2)
						 circle2)))
	;; (list rotated-circle1 rotated-circle2)))))
	(iter (for dest-index from (1- (car horde1)))
	      (for elt in-vector rotated-circle1)
	      (setf (elt res (mod dest-index n)) elt))
	(iter (for dest-index from (1- (cadr horde1)))
	      (for elt in-vector rotated-circle2)
	      (setf (elt res (mod dest-index n)) elt))
	(iter (for i from 1 to n)
	      (for elt in-vector res)
	      (collect (cons elt i)))))))
    
    

(defun permute-prehorde (prehorde permutation)
  (mapcar (lambda (edge)
	    (sort (mapcar (lambda (x)
			    (cdr (assoc x permutation)))
			  edge)
		  #'<))
	  prehorde))

(defun %horde->prehorde (%horde)
  (iter (for i from 1)
	(for elt in %horde)
	(if (< 0 elt)
	    (collect (list i (+ elt i))))))


(defparameter *curious-diag-1* '(2 4 -2 5 13 -4 13 7 -5 7 2 4 -2 5 -7 -4 -7 -13 -5 -13))

(defun prehorde-p (thing)
  (and (listp thing)
       (iter outer (for elt in thing)
	     (if (not (and (listp elt)
			   (equal 2 (length elt))
			   (numberp (car elt))
			   (numberp (cadr elt))))
		 (return-from outer nil))
	     (finally (return-from outer t)))))

(defun %horde-p (thing)
  (and (listp thing)
       (iter (for elt in thing)
	     (if (not (numberp elt))
		 (return nil))
	     (finally (return t)))))