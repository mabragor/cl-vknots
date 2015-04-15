
qnums[n_] := qnums[n] = q[2] qnums[n-1] - qnums[n-2];
qnums[0] = 0;
qnums[1] = 1;
QExprCanonicalForm[expr_] :=
    Collect[Expand[Simplify[(expr
			     /. {q[N + a_] :> If[a == - 1,
						 q[N-1],
						 q[a + 1] q[N] - q[a] q[N-1]]})
			    /. {q[k_Integer] :> If[k < 0,
						   - qnums[-k],
						   qnums[k]]}]],
	    {q[N], q[N-1]}];

(* AZForm1[expr_] := *)
(*     ((expr /. {q^(a_ N + b_) :> A^a q^b}) *)
(*      /. {q^N -> A}); *)

(* AZForm1[expr_] := *)
(*     FullSimplify[expr /. {N -> Log[q, A]}, *)
(* 		 Assumptions -> Element[A, Integers] && Element[q, Integers] *)
(* 		 && A > 0 && q > 0]; *)


(* AZForm[expr_] := *)
(*     AZForm1[Expand[FullSimplify[expr /. {q[x_] :> (q^x - q^(-x))/(q-q^(-1))}]]]; *)
     
(* HeuristicSimplify[expr_] := *)
(*     (expr /. {q[N] - q q[N-1] :> q^(1-N), *)
(* 	      q q[N-1] - q[N] :> -q^(1-N), *)
(* 	      q[N-1]-q q[N] :> -q^N, *)
(* 	      - q[N-1] + q q[N] :> -q^N *)
(* 	     }); *)
     
fd = OpenRead[DirectoryName[$InputFileName] <> "/lisp-out.txt"];
(* fdout = OpenWrite["~/code/superpolys/lisp-in.txt"]; *)

For[it = Read[fd], it =!= EndOfFile, it = Read[fd],
    WriteString["stdout",
		Factor[QExprCanonicalForm[expr]]//InputForm, "\n"]];

Close[fd];
(* Close[fdout]; *)
