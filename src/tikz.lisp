
(in-package #:cl-vknots)

(defmacro define-tikz-snippet (name (&rest args) &body body)
  nil)

(define-tikz-snippet 4-valent-int (t!-x t!-y &key (color :black) (size :normal))
  ...)

(define-tikz-snippet 3-4-valent-vertices (t!-x t!-y)
  (join "~%"
	(4-valent-int t!-x t!-y)
	(4-valent-int #?"$(t!-x) + 1" t!-y :color :white)
	(4-valent-int #?"$(t!-x) + 2" t!-y :size :small)))
    
    
(defun tikz-frob ()
  (with-open-file (stream "/tmp/tex.tex" :direction :output :if-exists :supersede)
    (format stream (gen-tex-header))
    (format stream "asdf~%")
    (format stream (gen-tex-tailer)))
  (script1 "pdflatex /tmp/tex.tex")
  (script1 "evince tex.pdf"))

;; Ok, how do I implement convenient interface to TiKZ pictures, that depend on each other,
;; such that all dependencies are automatically inserted into tex file?
  
;; The features the DEFINE-TIKZ-SNIPPET seem to be the following:
;;   * T!-variables define the ones, that are TeX-ified -- they actually become arguments of
;;     TeX macros.
;;   * The body should yield string
