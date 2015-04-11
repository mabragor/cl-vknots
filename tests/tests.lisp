
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
  ;; (is (equal '(+ (* (Q "2") (* (Q "2") (+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1"))))
  ;; 					  (* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))))
  ;; 	       (+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1"))))
  ;; 		(* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))
  ;; 	       (- (* (Q "2") (+ (* (Q "N-2") (* (Q "N-1") (* (** (Q "N") 1) "1")))
  ;; 				(* (** (Q "N") 1) (* (Q "N-1") (* (** (Q "N") 1) "1")))))))
  ;; 	     (decompose (deserialize-qed (torus-dessin 3 3)))))
  ;; (is (equal '(+ (* (Q "2") (* (Q "2") (+ (* (Q "2") (* (Q "2")
  ;; 							(+ (* (Q "2") (* (Q "2") (+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1")))) (* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))))
  ;; 							   (+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1")))) (* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))
  ;; 							   (- (* (Q "2") (+ (* (Q "N-2") (* (Q "N-1") (* (** (Q "N") 1) "1"))) (* (** (Q "N") 1) (* (Q "N-1") (* (** (Q "N") 1) "1")))))))))
  ;; 					  (+ (* (Q "2") (* (Q "2") (+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1")))) (* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))))
  ;; 					     (+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1")))) (* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))
  ;; 					     (- (* (Q "2") (+ (* (Q "N-2") (* (Q "N-1") (* (** (Q "N") 1) "1"))) (* (** (Q "N") 1) (* (Q "N-1") (* (** (Q "N") 1) "1")))))))
  ;; 					  (- (* (Q "2") (* (Q "2") (+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1")))) (* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))))))))
  ;; 	       (+
  ;; 		(* (Q "2")
  ;; 		 (* (Q "2")
  ;; 		    (+
  ;; 		     (+ (* (Q "N-2") (* (Q "2") (* (Q "2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1"))))))
  ;; 			(+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1")))) (* (** (Q "N") 1) (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1"))))))
  ;; 		     (+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1")))) (* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))
  ;; 		     (- (* (Q "2") (+ (* (Q "N-2") (* (Q "N-1") (* (** (Q "N") 1) "1"))) (* (** (Q "N") 1) (* (Q "N-1") (* (** (Q "N") 1) "1")))))))))
  ;; 		(+ (* (Q "2") (* (Q "2") (+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1")))) (* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))))
  ;; 		 (+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1")))) (* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))
  ;; 		 (- (* (Q "2") (+ (* (Q "N-2") (* (Q "N-1") (* (** (Q "N") 1) "1"))) (* (** (Q "N") 1) (* (Q "N-1") (* (** (Q "N") 1) "1")))))))
  ;; 		(- (* (Q "2") (* (Q "2") (+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1")))) (* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))))))
  ;; 	       (-
  ;; 		(* (Q "2")
  ;; 		 (* (Q "2")
  ;; 		    (+
  ;; 		     (+ (* (Q "N-2") (* (Q "2") (* (Q "2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1"))))))
  ;; 			(+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1")))) (* (** (Q "N") 1) (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1"))))))
  ;; 		     (+ (* (Q "N-2") (* (Q "2") (* (Q "N-1") (* (** (Q "N") 1) "1")))) (* (Q "N-1") (* (Q "N-1") (* (** (Q "N") 1) "1"))))
  ;; 		     (- (* (Q "2") (+ (* (Q "N-2") (* (Q "N-1") (* (** (Q "N") 1) "1"))) (* (** (Q "N") 1) (* (Q "N-1") (* (** (Q "N") 1) "1")))))))))))
  ;; 	     (decompose (deserialize-qed (torus-dessin 5 3))))))
  )

(test virtuals
  (is (equal '(* (- (Q "N-1")) (* (** (Q "N") 1) "1"))
	     (decompose (deserialize-qed '((1 1 1))))))
  (is (equal '(* (- (Q "N-1")) (* (- (Q "N-1")) (* (** (Q "N") 1) "1")))
	     (decompose (deserialize-qed '((1 1 1 2 2))))))
  (is (equal '(* (Q "2") (* (- (Q "N-1")) (* (** (Q "N") 1) "1")))
	     (decompose (deserialize-qed '((1 1 2 1 2))))))
  (is (equal '(* (Q "2") (* (- (Q "N-1")) (* (Q "2") (* (- (Q "N-1")) (* (** (Q "N") 1) "1")))))
	     (decompose (deserialize-qed '((1 1 2 1 2 3 4 3 4)))))))

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
  
(test cabling
  (is (equal '((n a b c d)) (bud-vertex '(n a b c d) 1)))
  (is (equal '((n (a 1) (:a 1 0) (c 1) (:a 0 1))
	       (n (a 2) (b 1) (:a 1 0) (:a 2 1))
	       (n (:a 2 1) (b 2) (:a 1 2) (d 2))
	       (n (:a 0 1) (:a 1 2) (c 2) (d 1)))
	     (bud-vertex '(n a b c d) 2 :a)))
  (is (equal '((n (a 1) (:a 1 0) (c 1) (:a 0 1))
	       (n (a 3) (b 1) (:a 3 0) (:a 4 1))
	       (n (:a 4 3) (b 3) (:a 3 4) (d 3))
	       (n (:a 0 3) (:a 1 4) (c 3) (d 1))
	       (n (a 2) (:a 3 0) (:a 1 0) (:a 2 1))
	       (n (:a 0 1) (:a 1 2) (c 2) (:a 0 3))
	       (n (:a 4 1) (b 2) (:a 3 2) (:a 4 3))
	       (n (:a 2 3) (:a 3 4) (:a 1 4) (d 2))
	       (n (:a 2 1) (:a 3 2) (:a 1 2) (:a 2 3)))
	     (bud-vertex '(n a b c d) 3 :a)))
  (is (equal '((n (a 1) (:a 1 0) (c 1) (:a 0 1))
	       (n (a 4) (b 1) (:a 5 0) (:a 6 1))
	       (n (:a 6 5) (b 4) (:a 5 6) (d 4))
	       (n (:a 0 5) (:a 1 6) (c 4) (d 1))
	       (n (a 2) (:a 3 0) (:a 1 0) (:a 2 1))
	       (n (a 3) (:a 5 0) (:a 3 0) (:a 4 1))
	       (n (:a 0 1) (:a 1 2) (c 2) (:a 0 3))
	       (n (:a 0 3) (:a 1 4) (c 3) (:a 0 5))
	       (n (:a 6 1) (b 2) (:a 5 2) (:a 6 3))
	       (n (:a 6 3) (b 3) (:a 5 4) (:a 6 5))
	       (n (:a 2 5) (:a 3 6) (:a 1 6) (d 2))
	       (n (:a 4 5) (:a 5 6) (:a 3 6) (d 3))
	       (n (:a 2 1) (:a 3 2) (:a 1 2) (:a 2 3))
	       (n (:a 2 3) (:a 3 4) (:a 1 4) (:a 2 5))
	       (n (:a 4 1) (:a 5 2) (:a 3 2) (:a 4 3))
	       (n (:a 4 3) (:a 5 4) (:a 3 4) (:a 4 5)))
	     (bud-vertex '(n a b c d) 4 :a))))
  

(test homfly-serial-toolchain
  (is (equal "q(N)" (homfly-serial-toolchain '((1)))))
  (is (equal "q(N)^2" (homfly-serial-toolchain '((1) (2)))))
  (is (equal "q(N)^3" (homfly-serial-toolchain '((1) (2) (3))))))