;;;; package.lisp

(defpackage #:cl-vknots
  (:use #:cl #:iterate #:lol-re #:esrap-liquid #:defmacro-enhance)
  (:shadowing-import-from #:clesh #:script)
  (:shadowing-import-from #:cl-ppcre #:regex-replace-all)
  (:export #:decompose #:deserialize-qed #:serialize-qed
	   #:q #:torus-dessin
	   #:bud-vertex #:cable
	   #:homfly-serial-toolchain
	   #:compare-q-exprs #:compare-q-exprs1
	   #:deserialize2 #:lousy-simplify-dessin))


