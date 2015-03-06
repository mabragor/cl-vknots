
(in-package :cl-vknots-tests)

(cl-interpol:enable-interpol-syntax)

(def-suite cl-vknots)
(in-suite cl-vknots)

(test simple-loops
  (is (equal '(* (** (q "N") 1) "1") (decompose (deserialize-qed '((1))))))
  (is (equal '(* (** (q "N") 2) "1") (decompose (deserialize-qed '((1) (2))))))
  (is (equal '(* (** (q "N") 3) "1") (decompose (deserialize-qed '((1) (2) (3)))))))
      
(test simple-lines
  (is (equal '(* (Q "N-1") (* (** (Q "N") 1) "1")) (decompose (deserialize-qed '((1 1) (2 1))))))
  (is (equal '(* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1")))
	     (decompose (deserialize-qed '((1 1) (2 1 2) (3 2))))))
  (is (equal '(* (Q "N-1") (* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))
	     (decompose (deserialize-qed '((1 1) (2 1 2) (3 2 3) (4 3)))))))

(test 2-strand-diagrams
  (is (equal '(* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1")))
	     (decompose (deserialize-qed '((1 1 2) (2 1 2))))))
  (is (equal '(* (Q "2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1"))))
	     (decompose (deserialize-qed '((1 1 2 3) (2 1 2 3))))))
  (is (equal '(* (Q "2") (* (Q "2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1")))))
	     (decompose (deserialize-qed '((1 1 2 3 4) (2 1 2 3 4)))))))

(test torus
  (is (equal '(+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1"))))
		(* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))
	     (decompose (deserialize-qed (torus-dessin 2 3)))))
  (is (equal '(+ (* (Q "N-2") (+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1"))))
				  (* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1")))))
		(* (Q "N-1") (* (Q "2") (* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))))
	     (decompose (deserialize-qed (torus-dessin 2 4)))))
  (is (equal '(+ (* (Q "2") (* (Q "2") (+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1"))))
					  (* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))))
	       (+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1"))))
		(* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))
	       (- (* (Q "2") (+ (* (Q "N-2") (* (Q "N-1") (* (** (Q "N") 1) "1")))
				(* (** (Q "N") 1) (* (Q "N-1") (* (** (Q "N") 1) "1")))))))
	     (decompose (deserialize-qed (torus-dessin 3 3))))))



(test deserialize-serialize-loops
  (macrolet ((frob (x &optional y)
	       `(is (equal ',x (serialize-qed (deserialize-qed ',(or y x)))))))
    (frob ((1)))
    (frob ((1) (2)))
    (frob ((1) (2) (3)))
    (frob ((1 1) (2 1)))
    (frob ((1 1 2) (2 1 2)))
    (frob ((1 1 2) (2 2 1)))
    (frob ((1 1 2) (2 2 1)) ((1 2 1) (2 1 2)))
    ;; KLUDGE: we should better test properly for correct cyclic order of vertices,
    ;; then fine-tuning the answer to particular implementation of hashing functions etc.
    (frob ((1 1 2) (2 1 3 2 4) (3 4 3)) ((1 1 2) (2 1 3 2 4) (3 3 4)))
    (frob ((1 1 2 3) (2 1 4 2 5 3 6) (3 6 4 5)) ((1 1 2 3) (2 1 4 2 5 3 6) (3 4 5 6)))))
  

