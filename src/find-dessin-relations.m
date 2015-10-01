#!/usr/local/bin/MathematicaScript -script

layer = ToExpression[$ScriptCommandLine[[2]]];

q[x_] := (q^x - q^(-x))/(q - q^(-1));

layer = 3;

ExpressionLayer[expr_] :=
    Module[{max = 0},
	   expr /. {PermDessin[x_, y_] :> If[x > max, max = x]};
	   max];

(* load concide expressions for all previous layers dessins *)
For[i = 1, i < layer, i++,
    Get[OpenRead[DirectoryName[$InputFileName] <> "../dessins-through-atomic-" <> ToString[i] <> ".m"]]];

(* what relations can we devise from different ways to decompose dessins? *)
Get[DirectoryName[$InputFileName] <> "../dessins-dims-" <> ToString[layer] <> ".m"];

For[i = 0, PermDessinDecompositions =!= Head[PermDessinDecompositions[layer, i]], i ++,
    Module[{exprs = PermDessinDecompositions[layer, i]},
	   GenEqns[exprs];
	   OutputSimplestExprIfAny[layer, i, exprs]]];

(* Out[7]= {PermDessin[2, 4] q[-1 + N], PermDessin[2, 4] q[-1 + N]} *)

(* what relations can we devise from mutations? *)
fd = OpenRead[DirectoryName[$InputFileName] <> "../dessins-cluster-rels-" <> ToString[layer] <> ".m"];
For[it = Read[fd], it =!= EndOfFile, it = Read[fd],
    


(*     WriteString["stdout", *)
(* 		Factor[Simplify[expr]] // InputForm, "\n"]]; *)

(* Close[fd]; *)
(* (\* Close[fdout]; *\) *)
