;;;; cl-vknots.asd

(defpackage :cl-vknots-system
  (:use :cl :asdf))

(in-package :cl-vknots-system)

(defsystem #:cl-vknots
  :serial t
  :description "Calculate primary and secondary hypercube for a (virtual) knot"
  :author "Alexandr Popolitov <popolit@gmail.com>"
  :license "GPL"
  :depends-on (#:iterate #:cl-ppcre #:cl-interpol #:lol-re #:esrap-liquid #:cl-yaclyaml #:defmacro-enhance
			 #:alexandria #:clesh)
  :components ((:file "package")
	       (:file "debug")
	       (:file "qed-cells")
               (:file "cl-vknots")
	       (:file "qed-dessins")
	       (:file "planar-diagrams")
	       (:file "horde-diagrams")))


(defsystem :cl-vknots-tests
  :description "Tests for CL-VKNOTS."
  :licence "GPL"
  :depends-on (#:cl-vknots #:fiveam #:cl-interpol)
  :serial t
  :pathname "tests/"
  :components ((:file "package")
               (:file "tests")))

(defmethod perform ((op test-op) (sys (eql (find-system :cl-vknots))))
  (load-system :cl-vknots)
  (funcall (intern "RUN-TESTS" :cl-vknots)))
