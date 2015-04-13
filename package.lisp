;;;; package.lisp

(defpackage #:cl-vknots
  (:use #:cl #:iterate #:lol-re #:esrap-liquid #:defmacro-enhance #:cg-common-ground)
  (:shadowing-import-from #:clesh #:script)
  (:shadowing-import-from #:cl-ppcre #:regex-replace-all)
  (:export #:decompose #:deserialize-qed #:serialize-qed
	   #:q #:torus-dessin
	   #:bud-vertex #:cable
	   #:homfly-serial-toolchain
	   #:compare-q-exprs #:compare-q-exprs1 #:compare-q-exprs-minus #:compare-q-exprs-minus1
	   #:deserialize2 #:lousy-simplify-dessin
	   #:lousy-decompose #:mathematica-serialize
	   #:n-dessin-recursion #:print-dessin-poly
	   #:over-all-subdessins #:serialize2))


