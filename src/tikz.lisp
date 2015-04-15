
(in-package #:cl-vknots)


(defun tikz-frob ()
  (with-open-file (stream "/tmp/tex.tex" :direction :output :if-exists :supersede)
    (format stream (gen-tex-header))
    (format stream "asdf~%")
    (format stream (gen-tex-tailer)))
  (script1 "pdflatex /tmp/tex.tex")
  (script1 "evince tex.pdf"))
  
