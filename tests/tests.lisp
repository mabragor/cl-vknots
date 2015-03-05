
(in-package :cl-vknots-tests)

(cl-interpol:enable-interpol-syntax)

(def-suite cl-vknots)
(in-suite cl-vknots)

(test simple-loops
  (is (equal '((* (** (q "N") 1) "1")) (decompose (deserialize-qed '((1))))))
  (is (equal '((* (** (q "N") 2) "1")) (decompose (deserialize-qed '((1) (2))))))
  (is (equal '((* (** (q "N") 3) "1")) (decompose (deserialize-qed '((1) (2) (3)))))))
      
(test simple-lines
  (is (equal '((* (Q "N-1") (* (** (Q "N") 1) "1"))) (decompose (deserialize-qed '((1 1) (2 1))))))
  (is (equal '((* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))
	     (decompose (deserialize-qed '((1 1) (2 1 2) (3 2))))))
  (is (equal '((* (Q "N-1") (* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1")))))
	     (decompose (deserialize-qed '((1 1) (2 1 2) (3 2 3) (4 3)))))))