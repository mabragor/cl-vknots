;;;; cl-vknots.asd

(asdf:defsystem #:cl-vknots
  :serial t
  :description "Calculate primary and secondary hypercube for a (virtual) knot"
  :author "Alexandr Popolitov <popolit@gmail.com>"
  :license "GPL"
  :depends-on (#:iterate #:cl-ppcre #:cl-interpol #:lol-re #:esrap-liquid #:cl-yaclyaml)
  :components ((:file "package")
               (:file "cl-vknots")))

