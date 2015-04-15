QSubs[expr_] :=
    Simplify[(expr /. {q[x_] :> (q^x-q^(-x))/(q-q^(-1)),
		       qnum[x_] :> (q^x-q^(-x))/(q-q^(-1))
		      })];


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

fd = OpenRead[DirectoryName[$InputFileName] <> "/lisp-out.txt"];
(* fdout = OpenWrite["~/code/superpolys/lisp-in.txt"]; *)

For[it = Module[{}, Read[fd]; Read[fd]],
    it =!= EndOfFile,
    it = Module[{}, Read[fd]; Read[fd]],
    WriteString["stdout", Factor[QSubs[QExprCanonicalForm[expr1-expr2]]]//InputForm, "\n"]];

Close[fd];
(* Close[fdout]; *)
