
$OldOutput = $Output;
$Output = {};
Quiet[<< KnotTheory`];
(* $Output = $OldOutput; *)

QSubs[expr_] :=
    Simplify[(expr /. {q[x_] :> (q^x-q^(-x))/(q-q^(-1)),
		       qnum[x_] :> (q^x-q^(-x))/(q-q^(-1))
		      })];

CompareWithEtalon[expr_, theor_] :=
    Simplify[QSubs[expr/q[N]]
	     /(Quiet[HOMFLYPT[theor][a,z]] /. {a -> q^N, z -> q - 1/q}),
	     Assumptions -> Element[N, Integers]];

fd = OpenRead[DirectoryName[$InputFileName] <> "/lisp-out.txt"];
(* fdout = OpenWrite["~/code/superpolys/lisp-in.txt"]; *)

For[it = Module[{}, Read[fd]; Read[fd]], it =!= EndOfFile, it = Module[{}, Read[fd]; Read[fd]],
    WriteString["stdout", Quiet[CompareWithEtalon[expr1,expr2]]//InputForm, "\n"]];

Close[fd];
(* (\* Close[fdout]; *\) *)
