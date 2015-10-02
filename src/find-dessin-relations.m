#!/usr/local/bin/MathematicaScript -script

layer = ToExpression[$ScriptCommandLine[[2]]];
workDir = DirectoryName[$InputFileName];

q[x_] := (q^x - q^(-x))/(q - q^(-1));
ExpressionLayer[expr_] :=
    Module[{max = 0},
	   expr /. {PermDessin[x_, y_] :> If[x > max, max = x]};
	   max];
GenEqns[expr_] :=
    Module[{res = {}},
	   For[i = 1, i <= Length[expr] - 1, i ++,
	       Module[{it = Simplify[expr[[i]] - expr[[i + 1]]]},
		      If[it =!= 0,
			 PrependTo[res, it]]]];
	   res];
PrintAsExprs[lst_, fname_] :=
    Module[{fd = OpenWrite[fname]},
	   For[i = 1, i <= Length[lst] , i++,
	       WriteString[fd, "expr = " <> ToString[lst[[i]], InputForm] <> ";\n"]];
	   Close[fd]];
SimplestExpr[lst_, layer_] :=
    Module[{minLayer = layer,
	    curExpr = Null},
	   For[i = 1, i <= Length[lst], i ++,
	       Module[{curLayer = ExpressionLayer[lst[[i]]]},
		      If[curLayer < minLayer,
			 Module[{},
				minLayer = curLayer;
				curExpr = lst[[i]]]]]];
	   curExpr];
OutputAndRememberSimplestExprIfAny[stream_, layer_, numDessin_, exprs_] :=
    Module[{simpleExpr = SimplestExpr[exprs, layer]},
	   If[simpleExpr =!= Null,
	      (* Print["I'm here!"]; *)
	      WriteString[stream,
			  "PermDessin[" <> ToString[layer] <> ", " <> ToString[numDessin] <> "] = "
			  <> ToString[simpleExpr, InputForm] <> ";\n"];
	      (* Print["I'm there!"] *)
	      Set[PermDessin[layer, numDessin], simpleExpr]]];
PrimaryAtomicExpressions[layer_] :=
    Module[{i = 0,
	    fdNewLayer = OpenWrite[workDir
				   <> "../dessins-through-atomic-"
				   <> ToString[layer] <> ".m", FormatType -> InputForm]},
	   For[i = 0, PermDessinDecompositions =!= Head[PermDessinDecompositions[layer, i]], i ++,
	       (* Print[i]; *)
	       Module[{exprs = PermDessinDecompositions[layer, i]},
		      PrintAsExprs[GenEqns[exprs],
				   workDir
				   <> "../dessins-decomp-rels-"
				   <> ToString[layer] <> ".m"];
		      OutputAndRememberSimplestExprIfAny[fdNewLayer, layer, i, exprs]]];
	   Close[fdNewLayer]];
FindIndets[expr_, layer_] :=
    Module[{res = {}},
	   expr /. {PermDessin[i_, j_] :> Module[{},
						 If[i === layer,
						    PrependTo[res, PermDessin[i, j]]];
						 Null]};
	   Sort[res]];
ClusterRelations[layer_] :=
    Module[{fd = OpenRead[workDir <> "../dessins-cluster-rels-" <> ToString[layer] <> ".m"],
	    it = Null},
	   For[it = Read[fd], it =!= EndOfFile, it = Read[fd],
	       Print["new cycle begin"];
	       expr = Simplify[expr];
	       Print["after simplification"];
	       If[expr =!= 0,
		  Module[{thisLayerIndets = FindIndets[expr, layer]},
			 Print[thisLayerIndets];
			 If[Length[thisLayerIndets] === 0,
			    Module[{fd = OpenAppend[workDir
						    <> "../dessins-decomp-rels-"
						    <> ToString[layer] <> ".m", FormatType -> InputForm]},
				   Print["I'm there"];
				   WriteString[fd, ToString[expr, InputForm] <> ";\n"];
				   Close[fd]],
			    Module[{ans = (First[thisLayerIndets] /. Solve[expr == 0,
									   {First[thisLayerIndets]}][[1]]),
				    fd = OpenAppend[workDir
						    <> "../dessins-through-atomic-"
						    <> ToString[layer] <> ".m", FormatType -> InputForm]},
				   Print["I'm here"];
				   WriteString[fd,
					       ToString[First[thisLayerIndets], InputForm] <> " = "
					       <> ToString[ans, InputForm] <> ";\n"];
				   (RuleSet[First[thisLayerIndets],
					    ans] /. {RuleSet -> Set});
				   Close[fd]]]]]]];


(* workDir = "/home/popolit/quicklisp/local-projects/cl-vknots/src/"; *)
(* layer = 4; *)

(* load concise expressions for all previous layers dessins *)
Module[{i = 0},
       For[i = 1, i < layer, i++,
	   Get[workDir <> "../dessins-through-atomic-" <> ToString[i] <> ".m"]]];


(* what relations can we devise from different ways to decompose dessins? *)
Get[workDir <> "../dessins-dims-" <> ToString[layer] <> ".m"];

PrimaryAtomicExpressions[layer];

(* (\* what relations can we devise from mutations? *\) *)
ClusterRelations[layer];

