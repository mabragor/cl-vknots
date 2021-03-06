;;;; cl-vknots.asd

(defpackage :cl-vknots-system
  (:use :cl :asdf))

(in-package :cl-vknots-system)

(defsystem #:cl-vknots
  :serial t
  :description "Calculate primary and secondary hypercube for a (virtual) knot"
  :author "Alexandr Popolitov <popolit@gmail.com>"
  :license "GPL"
  :version "0.1"
  :depends-on (#:iterate #:cl-ppcre #:cl-interpol
			 #:alexandria #:clesh #:cg-common-ground
			 #:defmacro-enhance #:cl-coroutine
			 #:cl-fad)
  :pathname "src/"
  :components ((:file "package")
	       (:file "debug")
	       (:file "coro")
	       (:file "qed-cells")
               (:file "cl-vknots")
	       (:file "qed-dessins")
	       (:file "planar-diagrams")
	       (:file "horde-diagrams")
	       (:file "homfly")
	       ;; (:file "tikz")
	       ))


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
