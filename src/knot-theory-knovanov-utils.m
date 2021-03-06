
Quiet[<< KnotTheory`];

TwoStrandKhovanov[n_] :=
    Kh[BR[2, Join[{1,-1,1,-1},
		  Map[If[n > 0, 1, -1] &, Range[1, Abs[n]]]]]][q,t];
FundEvoTheor[n_] :=
    (AA * q^n + BB * t^n q^(3 n) + CC * (-t)^n q^(3 n));
ApplyFundEvolutionMethod[family_, positiveQ_] :=
    Module[{eqns = Map[family[#] - FundEvoTheor[#] == 0 &,
		       Map[If[positiveQ,
			      #,
			      -#] &,
			   Range[1, 3]]]},
	   Module[{ans = Solve[eqns, {AA, BB, CC}]},
		  If[1 =!= Length[ans],
		     Message["More than one solution to a linear system"],
		     CompoundExpression[Print[Map[FullSimplify[family[#] - FundEvoTheor[#] /. ans[[1]]] &,
						  Map[If[positiveQ,
							 #,
							 -#] &,
						      Range[4, 10]]]];
					ans[[1]]]]]];
EigenvalueUnknownComb[eigenvalues_] :=
    Module[{i},
	   Function[{n},
		    Plus @@ Table[AA[i] eigenvalues[[i]]^n,
				  {i, 1, Length[eigenvalues]}]]];
EigenvalueIndets[eigenvalues_] :=
    Module[{i}, Table[AA[i], {i, 1, Length[eigenvalues]}]];
FitFamilyWithEigenvalues[family_, eigenvalues_] :=
    Module[{comb = EigenvalueUnknownComb[eigenvalues],
	    indets = EigenvalueIndets[eigenvalues]},
	   Module[{eqns = Map[family[#] - comb[#] == 0 &,
			      Range[1, Length[eigenvalues]]]},
		  Module[{ans = Solve[eqns, indets]},
			 If[1 =!= Length[ans],
			    Message["More than one solution to a linear system"],
			    CompoundExpression[Print[Map[FullSimplify[family[#] - comb[#] /. ans[[1]]] &,
							 Range[1 + Length[eigenvalues], 5 + Length[eigenvalues]]]],
					       ans[[1]]]]]]];
EigenvalueUnknownCombAdvanced[eigenvaluesSpecs_] :=
    Module[{body =
	    (Plus
	     @@ Map[Function[{indices},
			     (AA @@ indices)
			     (Times @@ MapIndexed[Function[{index, number},
							   eigenvaluesSpecs[[number[[1]],
									     index + 1]]^(eigenvaluesSpecs[[number[[1]], 1]]
											  /. {k -> Symbol["k"
													  <> ToString[number[[1]]]]})
							  ],
						  indices])
			    ],
		    Tuples[Map[Range[1, Length[#] - 1] &, eigenvaluesSpecs]]]),
	    args = Map[Symbol["k" <> ToString[#]] &, Range[1, Length[eigenvaluesSpecs]]]},
	   Function[Evaluate[args], Evaluate[body]]];
EigenvalueIndetsAdvanced[eigenvaluesSpecs_] :=
    Map[Function[{indices},
		 AA @@ indices],
	Tuples[Map[Range[1, Length[#] - 1] &, eigenvaluesSpecs]]];
extraPoints = 1;
(* FigeightLikePDOdd[a_, b_] := *)
(*     Module[{i, *)
(* 	    B = Abs[b], *)
(* 	    A = Abs[a]}, *)
(* 	   PD @@ Join[Table[If[a > 0, *)
(* 			       If[OddQ[i], *)
(* 				  X[2 B + A + i, B + i + 1, 2 B + A + i + 1, B + i], *)
(* 				  X[B + i, 2 B + A + i + 1, B + i + 1, 2 B + A + i]], *)
(* 			       If[OddQ[i], *)
(* 				  X[B + i, 2 B + A + i, B + i + 1, 2 B + A + i + 1], *)
(* 				  X[2 B + A + i, B + i, 2 B + A + i + 1, B + i + 1]]], *)
(* 			    {i, 1, A}], *)
(* 		      Table[If[b > 0, *)
(* 			       If[OddQ[i], *)
(* 				  X[i, 2 B + A + 2 - i, i + 1, 2 B + A + 1 - i], *)
(* 				  X[2 B + A + 1 - i, i + 1, 2 B + A + 2 - i, i]], *)
(* 			       If[OddQ[i], *)
(* 				  X[2 B + A + 1 - i, i, 2 B + A + 2 - i, i + 1], *)
(* 				  X[i, 2 B + A + 1 - i, i + 1, 2 B + A + 2 - i]]], *)
(* 			    {i, 1, B}]] /. {2 B + 2 A + 1 :> 1}]; *)
ParallelTwoStrandBraid[bottomLeft_, bottomRight_, n_] :=
    (* ### List of crossings for the parallel two-strand braid with 'n' crossings ### *)
    (* ### Bottom legs of the braid are assumed to be incoming ### *)
    (* ### 'bottomLeft' and 'bottomRight' are the starting indices ### *)
    Module[{i, NN = Abs[n]},
	   Table[If[OddQ[i],
		    If[n > 0,
		       X[bottomLeft + i - 1, bottomRight + i - 1, bottomLeft + i, bottomRight + i],
		       X[bottomRight + i - 1, bottomLeft + i, bottomRight + i, bottomLeft + i - 1]],
		    If[n > 0,
		       X[bottomRight + i - 1, bottomLeft + i - 1, bottomRight + i, bottomLeft + i],
		       X[bottomLeft + i - 1, bottomRight + i, bottomLeft + i, bottomRight + i - 1]]],
		 {i, 1, NN}]];
AntiParallelTwoStrandBraidBottomInc[bottomLeft_, topLeft_, n_] :=
    (* ### List of crossings for the anti-parallel two-strand braid with 'n' crossings ### *)
    (* ### The braid is assumed to grow from left to right, rather than from bottom to top ### *)
    (* ### Bottom left leg is incoming, top left leg is outgoing. ### *)
    (* ### There is another version of this function, in which the bottom left is outgoing and top left is incoming ### *)
    (* ### 'bottomLeft' and 'topLeft' are the corresponding indices of the arcs ### *)
    Module[{i, NN = Abs[n]},
	   Table[If[n > 0,
		    If[OddQ[i],
		       X[topLeft - i, bottomLeft + i, topLeft - i + 1, bottomLeft + i - 1],
		       X[bottomLeft + i - 1, topLeft - i + 1, bottomLeft + i, topLeft - i]],
		    If[OddQ[i],
		       X[bottomLeft + i - 1, topLeft - i, bottomLeft + i, topLeft - i + 1],
		       X[topLeft - i, bottomLeft + i - 1, topLeft - i + 1, bottomLeft + i]]],
		 {i, 1, NN}]];
AntiParallelTwoStrandBraidTopInc[bottomLeft_, topLeft_, n_] :=
    (* ### List of crossings for the anti-parallel two-strand braid with 'n' crossings ### *)
    (* ### The braid is assumed to grow from left to right, rather than from bottom to top ### *)
    (* ### Bottom left leg is outgoing, top left leg is incoming. ### *)
    (* ### There is another version of this function, in which the bottom left is incoming and top left is outgoing ### *)
    (* ### 'bottomLeft' and 'topLeft' are the corresponding indices of the arcs ### *)
    Module[{i, NN = Abs[n]},
	   Table[If[n > 0,
		    If[OddQ[i],
		       X[topLeft + i - 1, bottomLeft - i + 1, topLeft + i, bottomLeft - i],
		       X[bottomLeft - i, topLeft + i, bottomLeft - i + 1, topLeft + i - 1]],
		    If[OddQ[i],
		       X[bottomLeft - i, topLeft + i - 1, bottomLeft - i + 1, topLeft + i],
		       X[topLeft + i - 1, bottomLeft - i, topLeft + i, bottomLeft - i + 1]]],
		 {i, 1, NN}]];
ParallelDummyTwoStrandBraid[bottomLeft_, bottomRight_, n_] :=
    (* ### A dummy  version of the two-strand braid, consisting of alternating positive and negative crossings ### *)
    (* ### so that it actually unknots. ### *)
    If[Not[EvenQ[n]],
       Message["Number of crossings in the dummy braid should be even"],
       Module[{i, NN = Abs[n]},
	      Table[If[OddQ[i],
		       X[bottomLeft + i - 1, bottomRight + i - 1, bottomLeft + i, bottomRight + i],
		       X[bottomLeft + i - 1, bottomRight + i, bottomLeft + i, bottomRight + i - 1]],
		    {i, 1, NN}]]];
AntiParallelDummyTwoStrandBraidBottomInc[bottomLeft_, topLeft_, n_] :=
    (* ### Dummy version of the antiparallel two-strand braid, bottom incoming version ### *)
    If[Not[EvenQ[n]],
       Message["Number of crossings in the dummy braid should be even"],
       Module[{i, NN = Abs[n]},
	      Table[If[OddQ[i],
		       X[topLeft - i, bottomLeft + i, topLeft - i + 1, bottomLeft + i - 1],
		       X[topLeft - i, bottomLeft + i - 1, topLeft - i + 1, bottomLeft + i]],
		    {i, 1, NN}]]];
AntiParallelDummyTwoStrandBraidTopInc[bottomLeft_, topLeft_, n_] :=
    (* ### Dummy version of the antiparallel two-strand braid, top incoming version ### *)
    If[Not[EvenQ[n]],
       Message["Number of crossings in the dummy braid should be even"],
       Module[{i, NN = Abs[n]},
	      Table[If[OddQ[i],
		       X[topLeft + i - 1, bottomLeft - i + 1, topLeft + i, bottomLeft - i],
		       X[topLeft + i - 1, bottomLeft - i, topLeft + i, bottomLeft - i + 1]],
		    {i, 1, NN}]]];
FigeightLikePD[a_, b_] :=
    If[And[EvenQ[a], EvenQ[b]],
       FigeightLikePDEE[a, b],
       If[And[EvenQ[a], OddQ[b]],
	  FigeightLikePDEO[a, b],
	  If[And[OddQ[a], EvenQ[b]],
	     FigeightLikePDOE[a, b],
	     If[And[OddQ[a], OddQ[b]],
		FigeightLikePDOOSameOrient[a, b],
		Message["Error"]]]]];
FigeightLikePDAlt[a_, b_] :=
    If[And[EvenQ[a], EvenQ[b]],
       FigeightLikePDEE[a, b],
       If[And[EvenQ[a], OddQ[b]],
	  FigeightLikePDEO[a, b],
	  If[And[OddQ[a], EvenQ[b]],
	     FigeightLikePDOE[a, b],
	     If[And[OddQ[a], OddQ[b]],
		FigeightLikePDOODifferentOrient[a, b],
		Message["Error"]]]]];
FigeightLikePDEE[a_, b_] :=
    Module[{A = Abs[a],
	    B = Abs[b]},
	   (PD @@ Join[AntiParallelTwoStrandBraidTopInc[B + DD + 1, A + B + C + DD + 1, b],
		       AntiParallelDummyTwoStrandBraidTopInc[DD + 1, A + 2 B + C + DD + 1, DD],
		       AntiParallelTwoStrandBraidBottomInc[B + DD + 1, 2 A + 2 B + 2 C + 2 DD + 1, a],
		       AntiParallelDummyTwoStrandBraidBottomInc[A + B + DD + 1, A + 2 B + 2 C + 2 DD + 1, C]]
	    /. {2 A + 2 B + 2 C + 2 DD + 1-> 1})];
FigeightLikePDEO[a_, b_] :=
    Module[{A = Abs[a],
	    B = Abs[b]},
	   (PD @@ Join[AntiParallelTwoStrandBraidBottomInc[A + B + C + DD + 1, B + DD + 1, b],
		       AntiParallelDummyTwoStrandBraidTopInc[DD + 1, A + 2 B + C + DD + 1, DD],
		       ParallelTwoStrandBraid[B + C + DD + 1, A + 2 B + 2 C + 2 DD + 1, a],
		       ParallelDummyTwoStrandBraid[B + DD + 1, A + 2 B + C + 2 DD + 1, C]]
	    /. {2 A + 2 B + 2 C + 2 DD + 1 -> 1})];
FigeightLikePDOE[a_, b_] :=
    Module[{A = Abs[a],
	    B = Abs[b]},
	   (PD @@ Join[ParallelDummyTwoStrandBraid[1, A + B + C + DD + 1, DD],
		       ParallelTwoStrandBraid[DD + 1, A + B + C + 2 DD + 1, b],
		       AntiParallelTwoStrandBraidBottomInc[B + DD + 1, 2 A + 2 B + 2 C + 2 DD + 1, a],
		       AntiParallelDummyTwoStrandBraidTopInc[A + 2 B + 2 C + 2 DD + 1, A + B + DD + 1, C]]
	    /. {2 A + 2 B + 2 C + 2 DD + 1 -> 1})];
FigeightLikePDOOSameOrient[a_, b_] :=
    Module[{A = Abs[a],
	    B = Abs[b]},
	   (PD @@ Join[ParallelDummyTwoStrandBraid[1, A + B + C + DD + 2, DD],
		       ParallelTwoStrandBraid[DD + 1, A + B + C + 2 DD + 2, b],
		       AntiParallelTwoStrandBraidBottomInc[A + 2 B + C + 2 DD + 2, A + B + C + DD + 1, a],
		       AntiParallelDummyTwoStrandBraidTopInc[B + C + DD + 1, 2 A + 2 B + C + 2 DD + 2, C]]
	    /. {2 A + 2 B + 2 C + 2 DD + 2 -> A + B + C + DD + 2,
		A + B + C + DD + 1 -> 1})];
FigeightLikePDOODifferentOrient[a_, b_] :=
    Module[{A = Abs[a],
	    B = Abs[b]},
	   Module[{C = If[A + B < 2,
			  4,
			  If[A + B < 4,
			     2,
			     0]]},
		  (PD @@ Join[ParallelDummyTwoStrandBraid[B + DD + 1, A + B + C + DD + 2, C],
			      ParallelTwoStrandBraid[B + C + DD + 1, A + B + 2 C + DD + 2, a],
			      AntiParallelTwoStrandBraidBottomInc[2 A + B + 2 C + DD + 2, B + DD + 1, b],
			      AntiParallelDummyTwoStrandBraidTopInc[DD + 1, 2 A + 2 B + 2 C + DD + 2, DD]]
		   /. {2 A + 2 B + 2 C + 2 DD + 2 -> A + B + C + DD + 2,
		       A + B + C + DD + 1 -> 1})]];
(* Block[{n = 12}, *)
(*       Expand[Simplify[(Kh[FigeightLikePD[1,n]][q,t] *)
(* 		       - (q^(3 - n) + q^(1 - n)) *)
(* 		       - (1/(1 - t^(-2) q^(-4)) (1 - (t^(-2) q^(-4))^((n-2)/2)) *)
(* 			  t^(-2) q^(-n - 1) (1 + q^(-4) t^(-1)))) *)
(* 		     ]]] *)
PosFundEigenvalues[] :=
    {q, t q^3, (-t) q^3};
NegFundEigenvalues[] :=
    {q^(-1), t^(-1) q^(-3), (-t^(-1)) q^(-3)};
PosAdjEigenvalues[] :=
    {1, t q^2};
NegAdjEigenvalues[] :=
    {1, (t q^2)^(-1)};
FitFamilyWithEigenvaluesAdvanced[family_, eigenvaluesSpecs__] :=
    Module[{specs = List[eigenvaluesSpecs]},
	   Module[{comb = EigenvalueUnknownCombAdvanced[specs],
		   indets = EigenvalueIndetsAdvanced[specs]},
		   (* correctionFactors = Map[Module[{power = #[[1]] /. {k -> 0}}, *)
		   (* 				  Map[#^power &, Rest[#]]] &, *)
		   (* 			   specs] *)
		  (* Print["comb and indets: ", List[comb, indets, family]]; *)
		  Module[{eqns = Map[(family @@ #) - (comb @@ #) == 0 &,
				     Tuples[Map[Range[0, Length[#] - 1 - 1] &,
						specs]]]},
			 Module[{ans = Solve[eqns, indets]},
				(* Print["solved the system: ", ans]; *)
				If[1 =!= Length[ans],
				   Message["More than one solution to a linear system"],
				   Module[{indices = Tuples[Map[Range[0, Length[#] - 1 - 1 + extraPoints]&,
								specs]]},
					  Module[{check = Tally[Map[If[0 === FullSimplify[(family @@ #) - (comb @@ #) /. ans[[1]]],
								       0,
								       nz] &,
								    indices]]},
						 If[1 === Length[check],
						    Module[{},
							   Print[check];
							   Map[Rule[#[[1]],
								    ExpandNumerator[
									FullSimplify[(* 1/(Times
											@@ MapIndexed[correctionFactors[[#2[[1]], #1]] &,
												      (List @@ #[[1]])]) *)
										     #[[2]]]]] &,
							       ans[[1]]]],
						    Module[{}, Print[check]; checkFailed]]]]]]]]];
PlanarDiagramToAdvancedStructures[pd_] :=
    (* ### Massage the terse format of the planar diagram ### *)
    (* ### into more convenient collection of maps, which is more suitable to for asking actual questions about PD ### *)
    Module[{nextEdge = <||>,
	    prevEdge = <||>,
	    edgeCrossingsIn = <||>,
	    edgeCrossingsOut = <||>},
	   Scan[Function[{crossing},
			 (* Print[crossing]; *)
			 Module[{a,b,c,d},
				(* ### vv It is hard to pass by reference in Mathematica, that's why we don't split here ### *)
				If[X === Head[crossing],
				   CompoundExpression[{a,b,c,d} = List @@ crossing;
						      (* Print["I'm here"]; *)
						      nextEdge[a] = c;
						      prevEdge[c] = a;
						      edgeCrossingsIn[a] = crossing;
						      edgeCrossingsOut[c] = crossing;
						      If[1 == Abs[b - d],
							 (* ### ^^ If we are not at the "gluing" of the loop ### *)
							 If[d > b,
							    CompoundExpression[nextEdge[b] = d, prevEdge[d] = b,
									       edgeCrossingsIn[b] = crossing,
									       edgeCrossingsOut[d] = crossing],
							    CompoundExpression[nextEdge[d] = b, prevEdge[b] = d,
									       edgeCrossingsIn[d] = crossing,
									       edgeCrossingsOut[b] = crossing]],
							 If[d > b,
							    CompoundExpression[nextEdge[d] = b, prevEdge[b] = d,
									       edgeCrossingsIn[d] = crossing,
									       edgeCrossingsOut[b] = crossing],
							    CompoundExpression[nextEdge[b] = d, prevEdge[d] = b,
									       edgeCrossingsIn[b] = crossing,
									       edgeCrossingsOut[d] = crossing]]]],
				   If[Or[Yp === Head[crossing], Ym == Head[crossing]],
				      CompoundExpression[{a,b,c,d} = List @@ crossing;
							 nextEdge[a] = d;
							 prevEdge[d] = a;
							 edgeCrossingsIn[a] = crossing;
							 edgeCrossingsOut[d] = crossing;
							 nextEdge[b] = c;
							 prevEdge[c] = b;
							 edgeCrossingsIn[b] = crossing;
							 edgeCrossingsOut[c] = crossing;]]]]],
		List @@ pd];
	   Module[{connectedComponents = FindConnectedComponents[nextEdge]},
		  PDExtended[nextEdge, prevEdge, edgeCrossingsIn, edgeCrossingsOut, connectedComponents]]];
FindConnectedComponents[nextEdge_] :=
    Module[{freeEdges = nextEdge,
	    connectedComponents = {}},
	   While[0 =!= Length[freeEdges],
		 Module[{curMin = RandomChoice[Keys[freeEdges]]},
			KeyDropFrom[freeEdges, curMin];
			Module[{cur = curMin},
			       Module[{curComponent = {cur}},
				      While[nextEdge[cur] =!= curMin,
					    cur = nextEdge[cur];
					    KeyDropFrom[freeEdges, cur];
					    AppendTo[curComponent, cur]];
				      AppendTo[connectedComponents, curComponent]]]]];
	   connectedComponents];
XToYPM[X[a_, b_, c_, d_]] :=
    If[1 == Abs[b - d],
       If[b < d,
	  Ym[a, b, d, c],
	  Yp[d, a, c, b]],
       If[b < d,
	  Yp[d, a, c, b],
	  Ym[a, b, d, c]]];
CheeksResolution[PDExtended[nextEdge_, prevEdge_, edgeCrossingsIn_, edgeCrossingsOut_, connectedComponents_],
		 x_X] :=
    (* ### The )(-resolution of the Jones (Khovanov) skein relation ### *)
    Module[{theY = XToYPM[x],
	    nnextEdge = nextEdge,
	    pprevEdge = prevEdge},
	   nnextEdge[theY[[1]]] = "f";
	   nnextEdge["f"] = theY[[3]];
	   pprevEdge[theY[[3]]] = "f";
	   pprevEdge["f"] = theY[[1]];
	   nnextEdge[theY[[2]]] = "e";
	   nnextEdge["e"] = theY[[4]];
	   pprevEdge[theY[[4]]] = "e";
	   pprevEdge["e"] = theY[[2]];
	   Module[{newConnectedComponents = FindConnectedComponents[nnextEdge]},
		  Module[{diag = (Join[Select[DeleteDuplicates[Values[edgeCrossingsIn]],
					       # =!= x &],
					{X[theY[[2]], "f", "e", theY[[1]]], X["e", "f", theY[[4]], theY[[3]]]}]
				  /. MapIndexed[Rule[#1, #2[[1]]] &,
						Flatten[newConnectedComponents]])},
			 (* Print["Cheek diag: ", diag]; *)
			 (PD @@ diag)]]];
CupCapResolution[PDExtended[nextEdge_, prevEdge_, edgeCrossingsIn_, edgeCrossingsOut_, connectedComponents_],
		 x_X] :=
    (* The v/^-resolution of the skein relation ### *)
    Module[{theY = XToYPM[x],
	    nnextEdge = nextEdge,
	    pprevEdge = prevEdge},
	   (* Print["theY: ", theY]; *)
	   Module[{firstToArrive = Null,
		   cur = theY[[4]]},
		  While[True,
			cur = nnextEdge[cur];
			(* Print[cur]; *)
			If[cur === theY[[1]],
			   CompoundExpression[firstToArrive = "a"; Break[]]];
			If[cur === theY[[2]],
			   CompoundExpression[firstToArrive = "b"; Break[]]]];
		  (* Print[firstToArrive]; *)
		  (* ### vv Reglue the arcs in appropriate way ### *)
		  Module[{pairsToReverse = {}},
			 Module[{curCur = If["a" === firstToArrive, theY[[2]], theY[[1]]]},
				Module[{curNext = pprevEdge[curCur], (* ii = 0, *) tmp = Null},
				       While[And[theY[[3]] =!= curCur, True (* ii < 10 *)],
					     (* ii += 1; *)
					     AppendTo[pairsToReverse, {curNext, curCur}];
					     nnextEdge[curCur] = curNext;
					     tmp = curNext;
					     curNext = pprevEdge[curNext];
					     pprevEdge[tmp] = curCur;
					     curCur = tmp]]];
			 (* Print[nnextEdge, pprevEdge, pairsToReverse]; *)
			 Module[{ppLeft = theY[[3]],
				 nnLeft = theY[[4]],
				 ppRight = If["a" === firstToArrive, theY[[1]], theY[[2]]],
				 nnRight = If["a" === firstToArrive, theY[[2]], theY[[1]]]},
				nnextEdge[ppLeft] = "f";
				nnextEdge["f"] = nnLeft;
				pprevEdge[nnLeft] = "f";
				pprevEdge["f"] = ppLeft;
				nnextEdge[ppRight] = "e";
				nnextEdge["e"] = nnRight;
				pprevEdge[nnRight] = "e";
				pprevEdge["e"] = ppRight;
				Module[{newConnectedComponents = FindConnectedComponents[nnextEdge]},
				       Module[{preDiag = (Join[Select[DeleteDuplicates[Values[edgeCrossingsIn]],
								      # =!= x &],
							       If["a" == firstToArrive,
								  {X[ppRight,"f", "e", ppLeft], X["e", "f", nnRight, nnLeft]},
								  {X["e", ppLeft, nnRight, "f"], X[ppRight, nnLeft, "e", "f"]}]]
							  (* /. {X[a_, b_, c_, d_] :> *)
							  (*     Module[{newAC = If[MemberQ[pairsToReverse, {a, c}], *)
							  (* 			 {c, a}, *)
							  (* 			 {a, c}], *)
							  (* 	      newBD = If[Or[MemberQ[pairsToReverse, {b, d}], *)
							  (* 			    MemberQ[pairsToReverse, {d, b}]], *)
							  (* 			 {d, b}, *)
							  (* 			 {b, d}]}, *)
							  (* 	     X[newAC[[1]], newBD[[1]], newAC[[2]], newBD[[2]]]]} *)
							 )},
					      (* Print["preDiag: ", preDiag]; *)
					      Module[{prePreDiag = (preDiag
								    /. MapIndexed[Rule[#1, #2[[1]]] &,
										  Flatten[newConnectedComponents]])
						      /. {whole:X[a_, b_, c_, d_] :>
							  If[Or[And[1 == Abs[c - a], c < a],
								And[1 =!= Abs[c - a], c > a]],
							     X[c, d, a, b],
							     whole]}},
						     (* Print["diag: ", prePreDiag]; *)
						     (PD @@ prePreDiag)]]]]]]];
(* PD[TorusKnot[3,2]] *)
(* CheeksResolution[PlanarDiagramToAdvancedStructures[PD[TorusKnot[3,2]]], *)
(* 		 X[1,5,2,4]] *)
(* Jones[CupCapResolution[PlanarDiagramToAdvancedStructures[PD[TorusKnot[3,2]]], *)
	 (* 		       X[1,5,2,4]]] *)
PosNegIndex[pd_PD] :=
    Plus @@ Map[If[Yp === Head[XToYPM[#]],
		   +1,
		   -1] &,
		List @@ pd];
CheckKhovanovSkein[knot_, crossingNum_] :=
    Module[{pd = PD[knot]},
	   Module[{crossing = pd[[crossingNum]]},
		  Module[{cheekRes = CheeksResolution[PlanarDiagramToAdvancedStructures[pd], crossing],
			  cupcapRes = CupCapResolution[PlanarDiagramToAdvancedStructures[pd], crossing]},
			 (* Print["Indices: ", PosNegIndex[pd], " ", PosNegIndex[cheekRes], " ", PosNegIndex[cupcapRes]]; *)
			 If[Yp === Head[XToYPM[crossing]],
			    Expand[Simplify[(Kh[pd][q,t]
			    		     - q Kh[cheekRes][q,t]
			    		     - t q^2 (t q^3)^((PosNegIndex[pd] - 1 - PosNegIndex[cupcapRes])/2) Kh[cupcapRes][q,t]
			    		    )/(1+t)]],
			    (* {Expand[Simplify[Kh[pd, Program->"FastKh"][q,t] *)
			    (* 		     - (t^(-2) q^(-2) (t q^3)^((PosNegIndex[pd] - 1 - PosNegIndex[cupcapRes])/2) *)
			    (* 			Kh[cupcapRes, Program->"FastKh"][q,t])]] *)
			    (*  Expand[Simplify[Kh[cheekRes, Program->"FastKh"][q,t]]]}, *)
			    Expand[Simplify[(Kh[pd][q,t]
					     - 1/q Kh[cheekRes][q,t]
					     - (t^(-1) q^(-2) (t q^3)^((PosNegIndex[pd] + 1 - PosNegIndex[cupcapRes])/2)
						Kh[cupcapRes][q,t]))/(1+t)]]]]]];
(* Kh[CupCapResolution[PlanarDiagramToAdvancedStructures[PD[TorusKnot[3,2]]], *)
(* 		    X[1,5,2,4]], *)
(*    Program->"JavaKh"][q,t] *)
FindLabelInBraidSpec[spec_BraidSpec, label_] :=
    Module[{i,
	    specLst = List @@ spec,
	    res = {}},
	   For[i = 1, i <= Length[spec], i ++,
	       Module[{itIn = Position[specLst[[i, 3]], label]},
		      res = res ~Join~ Map[II[specLst[[i, 2]], #[[1]] - 1] &, itIn]];
	       Module[{itOut = Position[specLst[[i, 4]], label]},
		      res = res ~Join~ Map[OO[specLst[[i, 2]], #[[1]] - 1] &, itOut]]];
	   res];
ConnectionScheme[spec_BraidSpec, choiceOfResidues_] :=
    Module[{connections = <||>, i,
	    lstSpec = List @@ spec},
	   (* ### vv Create the hash, ready to be populated, and populate with connections inside the braids ### *)
	   For[i = 1, i <= Length[lstSpec], i ++,
	       Module[{braid = lstSpec[[i]]},
		      Scan[Function[{index},
				    connections[II[braid[[2]], index]] = {OO[braid[[2]],
									     Mod[index - choiceOfResidues[[i]], braid[[1]]]],
									  Null};
				    connections[OO[braid[[2]], index]] = {II[braid[[2]],
									     Mod[index + choiceOfResidues[[i]], braid[[1]]]],
									  Null}],
			   (* ### vv The 0-based numbering convention is for convenience of taking the Mod in shifts ### *)
			   Range[0, braid[[1]] - 1]]]];
	   (* ### vv Populate with connections that are outside the braids ### *)
	   Module[{externalConnectionLabels = DeleteDuplicates[Join @@ Map[#[[3]] ~Join~ #[[4]] &, lstSpec]]},
		  Scan[Function[{label},
				Module[{it = FindLabelInBraidSpec[spec, label]},
				       (* Print["label: ", label, " pos: ", it]; *)
				       connections[[Key[it[[1]]], 2]] = it[[2]];
				       connections[[Key[it[[2]]], 2]] = it[[1]]]],
		       externalConnectionLabels]];
	   connections];
ExternalConnectionScheme[spec_BraidSpec] :=
    Module[{connections = <||>, i,
	    lstSpec = List @@ spec},
	   Module[{externalConnectionLabels = DeleteDuplicates[Join @@ Map[#[[3]] ~Join~ #[[4]] &, lstSpec]]},
		  Scan[Function[{label},
				Module[{it = FindLabelInBraidSpec[spec, label]},
				       (* Print["label: ", label, " pos: ", it]; *)
				       connections[[Key[it[[1]]]]] = it[[2]];
				       connections[[Key[it[[2]]]]] = it[[1]]]],
		       externalConnectionLabels]];
	   connections];
NormalizeConnectedComponent[connComp_] :=
    Module[{minInput = Null,
	    myConnComp = connComp}, (* ### << copy the list for our manipulations ### *)
	   (* Print["my conn comp: ", myConnComp]; *)
	   (* ### vv Find the minimal input leg of the braid with the minimal name of the evolution parameter ### *)
	   Scan[Function[{node},
			 If[And[II === Head[node],
				Or[Null === minInput,
				   1 === Order[node[[1]], minInput[[1]]],
				   And[0 === Order[node[[1]], minInput[[1]]],
				       1 === Order[node[[2]], minInput[[2]]]]]],
			    minInput = node]],
		connComp];
	   (* Print["min input: ", minInput]; *)
	   (* ### vv First connection in the component should be internal within the minimal braid ### *)
	   Module[{pos = Position[myConnComp, minInput][[1,1]]},
		  Module[{nextElt = myConnComp[[1 + Mod[pos + 1 - 1, Length[myConnComp]]]]},
			 (* Print["next elt: ", nextElt]; *)
			 If[Not[And[OO === Head[nextElt],
				    nextElt[[1]] === minInput[[1]]]],
			    myConnComp = Reverse[myConnComp]]]];
	   (* ### vv Make the minimal element appear as first in list ### *)
	   Module[{pos = Position[myConnComp, minInput][[1,1]]},
		  myConnComp = Join[myConnComp[[pos ;; ]],
				    myConnComp[[ ;; pos - 1]]]];
	   myConnComp];
(* ### Another version of routine that finds connected components and works on connection schemes ### *)
ConnectedComponentsConnectionScheme[connScheme_] :=
    Module[{freeNodes = Map[True &, connScheme],
	    connectedComponents = {}},
	   While[0 =!= Length[freeNodes],
		 (* Print["freeNodes: ", freeNodes]; *)
		 Module[{firstNode = Module[{it = Keys[freeNodes][[1]]},
					    KeyDropFrom[freeNodes, it];
					    it]},
			Module[{curComponent = {firstNode},
				curNode = firstNode,
				prevNode = Null},
			       While[True,
				     Module[{nextNode = Select[connScheme[curNode], # =!= prevNode &][[1]]},
					    (* Print["nextNode: ", nextNode]; *)
					    If[nextNode === firstNode,
					       Break[],
					       CompoundExpression[prevNode = curNode,
								  curNode = nextNode,
								  KeyDropFrom[freeNodes, nextNode],
								  AppendTo[curComponent, nextNode]]]]];
			       AppendTo[connectedComponents, NormalizeConnectedComponent[curComponent]]]]];
	   (* ### vv Sort the connected component so that their starting elements are in order ### *)
	   Sort[connectedComponents,
		DepthTwoLexiSort]];
DepthTwoLexiSort[eltOne_, eltTwo_] :=
    Module[{it = Order[eltOne[[1]], eltTwo[[1]]]},
	   If[0 =!= it,
	      it,
	      Order[eltOne[[2]], eltTwo[[2]]]]];
NextNodeIsInOrderQ[spec_BraidSpec, component_, i_, residues_] :=
    Module[{item = component[[i]],
	    nextItem = component[[1 + Mod[i, Length[component]]]],
	    lstSpec = List @@ spec},
	   And[OO === Head[nextItem],
	       item[[1]] === nextItem[[1]],
	       Module[{pos = Position[lstSpec, Condition[elt_, elt[[2]] === item[[1]]], {1}, Heads->False][[1,1]]},
		      item[[2]] == Mod[nextItem[[2]] + residues[[pos]] (* ### << relevant residue ### *),
				       (lstSpec)[[pos, 1]] (* ### << relevant braid thickness ### *)]]]];
OrientationMasks[spec_BraidSpec, connectedComponents_, residues_] :=
    Map[Function[{component},
		  Module[{i, res = <||>},
			 For[i = 1, i <= Length[component], i ++,
			     If[II === Head[component[[i]]],
				res[component[[i]]] = If[NextNodeIsInOrderQ[spec, component, i, residues],
							 1,
							 -1]]];
			 res]],
	 connectedComponents];
(* ### Braidosome is that smart program that does all the work I want to get done for me ### *)
(* ### Example of input : BraidSpec[Braid[2, a, {2, 1}, {4, 3}], Braid[2, b, {3, 1}, {4, 2}]] ### *)
(* ### This example describes the figure-eight-like knots ### *)
Braidosome[spec_BraidSpec] :=
    pass;
OrientationClusters[spec_BraidSpec] :=
    Module[{lst = List @@ spec,
	    theClusters = <||>},
	   Module[
	       {allResidues = Tuples[Map[Range[0, #[[1]] - 1] &, lst]]},
	       Scan[Function[{residues},
			     (* Print["residues: ", residues]; *)
			     (* ### vv This formatting is crap, but we don't have the Module* (analog of LET* ) macro ### *)
			     (* ### vv which would be appropriate to use here ### *)
			     Module[
				 {connScheme = ConnectionScheme[spec, residues]},
				 Module[
				     {connComps = ConnectedComponentsConnectionScheme[connScheme]},
				     Module[
					 {oriMasks = OrientationMasks[spec, connComps, residues]},
					 Scan[Function[{oriChoice}, (* ### << short for 'orientation choice' ### *)
						       Module[{i, totalOrientation = {}},
							      For[i = 1, i <= Length[oriChoice], i ++,
								  AppendTo[totalOrientation,
									   Map[Rule[#[[1]],
										    oriChoice[[i]] * #[[2]]] &,
									       Normal[oriMasks[[i]]]]]];
							      (* Print["total ori: ", totalOrientation]; *)
							      Module[{key = (OriChoice @@ Sort[Join @@ totalOrientation,
											       (* ### vv We sort by keys ### *)
											       DepthTwoLexiSort[#1[[1]], #2[[1]]] &])},
								     Module[{val = Lookup[theClusters, key, {}]},
									    (* Print["val: ", val]; *)
									    theClusters[key] = Append[val, residues]]]]],
					      (* ### vv First component always contains II[a,0], so we fix sign freedom this way ### *)
					      Map[{1} ~Join~ # &, Tuples[{1,-1}, Length[connComps] - 1]]]]]]],
		    allResidues]];
	   theClusters];
YpAbs[ll_, lr_, ul_, ur_, ori1_, ori2_] :=
    (* ### ^^ the crossing that looks "positive" in the absolute frame: had both strands been oriented from down to up ### *)
    If[And[ori1 == 1, ori2 == 1],
       Yp[ll, lr, ul, ur],
       If[And[ori1 == -1, ori2 == 1],
	  Ym[lr, ur, ll, ul],
	  If[And[ori1 == 1, ori2 == -1],
	     Ym[ul, ll, ur, lr],
	     If[And[ori1 == -1, ori2 == -1],
		Yp[ur, ul, lr, ll],
		Print["Caboom!"]]]]];
YmAbs[ll_, lr_, ul_, ur_, ori1_, ori2_] :=
    (* ### ^^ the crossing that looks "negative" in the absolute frame: had both strands been oriented from down to up ### *)
    If[And[ori1 == 1, ori2 == 1],
       Ym[ll, lr, ul, ur],
       If[And[ori1 == -1, ori2 == 1],
	  Yp[lr, ur, ll, ul],
	  If[And[ori1 == 1, ori2 == -1],
	     Yp[ul, ll, ur, lr],
	     If[And[ori1 == -1, ori2 == -1],
		Ym[ur, ul, lr, ll],
		Print["Caboom!"]]]]];
ExpandBraidIntoPositiveCrossings[braid_Braid, orientations_, winding_] :=
    Module[{nWind,
	    curOris = orientations,
	    res = {},
	    numStrands = braid[[1]],
	    braidLabel = braid[[2]]},
	   For[nWind = 1, nWind <= winding, nWind ++,
	       AppendTo[res, Map[Function[{crossingIndex},
					  YpAbs[IntHor[braidLabel, nWind, crossingIndex - 1],
						IntVert[braidLabel, nWind - 1, crossingIndex],
						IntVert[braidLabel, nWind, crossingIndex - 1],
						IntHor[braidLabel, nWind, crossingIndex],
						curOris[[crossingIndex]],
						curOris[[crossingIndex + 1]]]],
				 Range[1, numStrands - 1]]];
	       curOris = Append[curOris[[2 ;; ]], curOris[[1]]]];
	   (((Join @@ res) /. {IntHor[braidLabel, wind_, 0] :> IntVert[braidLabel, wind - 1, 0],
			       IntHor[braidLabel, wind_, numStrands - 1] :> IntVert[braidLabel, wind, numStrands - 1]})
	    /. {IntVert[braidLabel, 0, k_] :> II[braidLabel, k],
		IntVert[braidLabel, winding, k_] :> OO[braidLabel, k]})];
ExpandBraidIntoNegativeCrossings[braid_Braid, orientations_, winding_] :=
    Module[{nWind,
	    curOris = orientations,
	    res = {},
	    numStrands = braid[[1]],
	    braidLabel = braid[[2]]},
	   For[nWind = 1, nWind <= winding, nWind ++,
	       AppendTo[res, Map[Function[{crossingIndex},
					  YmAbs[IntVert[braidLabel, nWind - 1, crossingIndex - 1],
						IntHor[braidLabel, nWind, crossingIndex],
						IntHor[braidLabel, nWind, crossingIndex - 1],
						IntVert[braidLabel, nWind, crossingIndex],
						curOris[[crossingIndex]],
						curOris[[crossingIndex + 1]]]],
				 Range[1, numStrands - 1]]];
	       curOris = Prepend[curOris[[ ;; -2]], curOris[[-1]]]];
	   (((Join @@ res) /. {IntHor[braidLabel, wind_, 0] :> IntVert[braidLabel, wind, 0],
			       IntHor[braidLabel, wind_, numStrands - 1] :> IntVert[braidLabel, wind - 1, numStrands - 1]})
	    /. {IntVert[braidLabel, 0, k_] :> II[braidLabel, k],
		IntVert[braidLabel, winding, k_] :> OO[braidLabel, k]})];
ExpandBraidIntoZeroCrossings[braid_Braid, orientations_] :=
    Module[{nWind,
	    curOris = orientations,
	    res = {},
	    numStrands = braid[[1]],
	    braidLabel = braid[[2]]},
	   With[{nWind = 1},
		AppendTo[res, Map[Function[{crossingIndex},
					   YpAbs[IntHor[braidLabel, nWind, crossingIndex - 1],
						 IntVert[braidLabel, nWind - 1, crossingIndex],
						 IntVert[braidLabel, nWind, crossingIndex - 1],
						 IntHor[braidLabel, nWind, crossingIndex],
						 curOris[[crossingIndex]],
						 curOris[[crossingIndex + 1]]]],
				  Range[1, numStrands - 1]]];
		curOris = Append[curOris[[2 ;; ]], curOris[[1]]]];
	   With[{nWind = 2},
		AppendTo[res, Map[Function[{crossingIndex},
					   YmAbs[IntVert[braidLabel, nWind - 1, crossingIndex - 1],
						 IntHor[braidLabel, nWind, crossingIndex],
						 IntHor[braidLabel, nWind, crossingIndex - 1],
						 IntVert[braidLabel, nWind, crossingIndex],
						 curOris[[crossingIndex]],
						 curOris[[crossingIndex + 1]]]],
				  Range[1, numStrands - 1]]];
		curOris = Prepend[curOris[[ ;; -2]], curOris[[-1]]]];
	   (((Join @@ res) /. {IntHor[braidLabel, 1, 0] :> IntVert[braidLabel, 0, 0],
			       IntHor[braidLabel, 1, numStrands - 1] :> IntVert[braidLabel, 1, numStrands - 1],
			       IntHor[braidLabel, 2, 0] :> IntVert[braidLabel, 2, 0],
			       IntHor[braidLabel, 2, numStrands - 1] :> IntVert[braidLabel, 1, numStrands - 1]})
	    /. {IntVert[braidLabel, 0, k_] :> II[braidLabel, k],
		IntVert[braidLabel, 2, k_] :> OO[braidLabel, k]})];
ExpandBraidIntoCrossings[braid_Braid, orientations_, winding_] :=
    If[winding > 0,
       ExpandBraidIntoPositiveCrossings[braid, orientations, winding],
       If[winding == 0,
	  ExpandBraidIntoZeroCrossings[braid, orientations],
	  ExpandBraidIntoNegativeCrossings[braid, orientations, Abs[winding]]]];
PlanarDiagram[spec_BraidSpec, oriChoice_, windings_] :=
    Module[{i, specLst = List @@ spec, acc = {}},
	   For[i = 1, i <= Length[specLst], i ++,
	       Module[{planeOris = Map[#[[2]] &, Select[List @@ oriChoice,
							Function[{x},
								 (* Print["x: ", x[[1,1]], " ", specLst[[i, 2]]]; *)
								 Module[{it = (x[[1, 1]] === specLst[[i, 2]])},
									(* Print["it: ", it]; *)
									it]]]]},
		      (* Print["planeOris: ", planeOris]; *)
		      AppendTo[acc,
			       ExpandBraidIntoCrossings[specLst[[i]], planeOris, windings[[i]]]]]];
	   ((Join @@ acc)
	    /. (* {} *) DeleteDuplicates[Map[Rule @@ Sort[List @@ #,
							  If[And[II === Head[#1],
								 OO === Head[#2]],
							     1,
							     If[And[OO === Head[#1],
								    II === Head[#2]],
								-1,
								DepthTwoLexiSort[#1, #2]]] &] &,
					     Normal[ExternalConnectionScheme[spec]]]])];
UnderIncomingCrossingQ[crossing_, edge_] :=
    Or[And[Ym === Head[crossing],
	   crossing[[1]] === edge],
       And[Yp === Head[crossing],
	   crossing[[2]] === edge]];
ExtendedPDToUsual[PDExtended[nextEdge_, prevEdge_, edgeCrossingsIn_, edgeCrossingsOut_, connectedComponents_]] :=
    Module[{i, j,
	    myCC = connectedComponents,
	    myNextEdge = nextEdge,
	    myPrevEdge = prevEdge,
	    myEdgeCrossingsIn = edgeCrossingsIn,
	    myEdgeCrossingsOut = edgeCrosssingsOut},
	   (* Print["myCC: ", myCC]; *)
	   For[i = 1, i <= Length[myCC], i ++,
	       Module[{foundCut = False},
		      For[j = 1, j <= Length[myCC[[i]]], j ++,
			  (* ### vv First we try to find good edge to cut the numbering at ### *)
			  If[UnderIncomingCrossingQ[myEdgeCrossingsIn[myCC[[i, j]]],
						    myCC[[i, j]]],
			     CompoundExpression[myCC[[i]] = Join[myCC[[i, j + 1 ;; ]], myCC[[i, ;; j]]],
						foundCut = True;
						Break[]]]];
		      If[Not[foundCut],
			 CompoundExpression[
			     (* ### vv If we hadn't found such an edge, we create a small loop ### *)
			     Print["I'm in creating new crossing"];
			     myCC[[i]] = myCC[[i]] ~Join~ {SmallLoopEdge[i, 1], SmallLoopEdge[i, 2]};
			     Module[{it = myPrevEdge[myCC[[i, 1]]]},
				    myNextEdge[it] = SmallLoopEdge[i, 1];
				    myNextEdge[SmallLoopEdge[i, 1]] = SmallLoopEdge[i, 2];
				    myNextEdge[SmallLoopEdge[i, 2]] = myCC[[i, 1]];
				    myPrevEdge[myCC[[i, 1]]] = SmallLoopEdge[i, 2];
				    myPrevEdge[SmallLoopEdge[i, 2]] = SmallLoopEdge[i, 1];
				    myPrevEdge[SmallLoopEdge[i, 1]] = it;
				    Module[{oldCrossing = myEdgeCrossingOut[myCC[[i, 1]]],
					    modifiedCrossing = (myEdgeCrossingOut[myCC[[i, 1]]]
								/. {myCC[[i, 1]] -> SmallLoopEdge[i, 1]}),
					    newCrossing = Yp[SmallLoopEdge[i, 2], SmallLoopEdge[i, 1],
							     SmallLoopEdge[i, 2], myCC[i, 1]]},
					   Scan[Function[{edge},
							 If[myEdgeCrossingIn[edge] === oldCrossing,
							    myEdgeCrossingIn[edge] = modifiedCrossing];
							 If[myEdgeCrossingOut[edge] === oldCrossing,
							    myEdgeCrossingOut[edge] = modifiedCrossing]],
						List @@ modifiedCrossing];
					   myEdgeCrossingOut[SmallLoopEdge[i, 1]] = modifiedCrossing;
					   myEdgeCrossingIn[SmallLoopEdge[i, 1]] = newCrossing;
					   myEdgeCrossingOut[SmallLoopEdge[i, 2]] = newCrossing;
					   myEdgeCrossingIn[SmallLoopEdge[i, 2]] = newCrossing;
					   myEdgeCrossingOut[myCC[[i, 1]]] = newCrossing;]]]]]];
	   (* Print["myCC: ", myCC]; *)
	   Module[{diag = (DeleteDuplicates[Values[myEdgeCrossingsIn]]
			   /. MapIndexed[Rule[#1, #2[[1]]] &,
					 Flatten[myCC]])},
		  YPMsToXs[(PD @@ diag)]]];
YPMsToXs[expr_] :=
    (* ### Convert notation for crossings back to the counter-intuitive notation, but which is understood by KnotTheory ### *)
    (expr /. {Ym[a_, b_, c_, d_] :> X[a, b, d, c],
	      Yp[a_, b_, c_, d_] :> X[b, d, c, a]});
ThreeStrandKhovanov[aa_] :=
    Block[{prePd = PlanarDiagram[BraidSpec[Braid[3, a, {1, 2, 3}, {4, 6, 7}],
					   Braid[2, b, {6, 7}, {5, 3}],
					   Braid[2, c, {4, 5}, {1, 2}]],
				 OriChoice[II[a, 0] -> 1, II[a, 1] -> 1, II[a, 2] -> 1,
					   II[b, 0] -> 1, II[b, 1] -> 1,
					   II[c, 0] -> 1, II[c, 1] -> 1],
				 {aa, 0 ,0}]},
	  Block[{pd = ExtendedPDToUsual[PlanarDiagramToAdvancedStructures[prePd]]},
		(* Print["pre pd: ", prePd]; *)
		(* Print["pd: ", pd]; *)
		Module[{it = Kh[pd][q,t]},
		       it]]];
FourStrandKhovanov[aa_] :=
    Block[{prePd = PlanarDiagram[BraidSpec[Braid[4, a, {1, 2, 3, 4}, {5,6,7,8}],
					   Braid[4, b, {5,6,7,8}, {1,2,3,4}]],
				 OriChoice[II[a, 0] -> 1, II[a, 1] -> 1, II[a, 2] -> 1, II[a,3] -> 1,
					   II[b, 0] -> 1, II[b, 1] -> 1, II[b, 2] -> 1, II[b,3] -> 1],
				 {aa, 0}]},
	  Block[{pd = ExtendedPDToUsual[PlanarDiagramToAdvancedStructures[prePd]]},
		(* Print["pre pd: ", prePd]; *)
		(* Print["pd: ", pd]; *)
		Module[{it = Kh[pd][q,t]},
		       it]]];
FirstNonToricKhovanov[aa_] :=
    Kh[PD[BR[3, Join @@ Table[{1, -2}, {i, 1, aa}]]]][q,t];
(* ExpandBraidIntoCrossings[Braid[2, a, {2, 1}, {4, 3}], {-1,1}, -2] *)
(* ConnectionScheme[BraidSpec[Braid[2, a, {2, 1}, {4, 3}], Braid[2, b, {3, 1}, {4, 2}]], *)
(* 		 {1,1}] *)
(* ExternalConnectionScheme[BraidSpec[Braid[2, a, {2, 1}, {4, 3}], Braid[2, b, {3, 1}, {4, 2}]]] *)

(* ### Learn the evolution coefficient matrix for the UR region ### *)
ansPP13 = Block[{C = 2, DD = 2, extraPoints = 2},
		With[{aSeries = k + 1,
		      bSeries = 2 k + 3},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
							       Kh[FigeightLikePDAlt[aSeries /. {k -> k2},
										    bSeries /. {k -> k1}]][q,t]],
						      {bSeries} ~Join~ PosAdjEigenvalues[],
						      {aSeries} ~Join~ NegFundEigenvalues[]]]];
ansPP21 = Block[{C = 2, DD = 2, extraPoints = 2},
		With[{aSeries = k + 2,
		      bSeries = 2 k + 1},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
							       Kh[FigeightLikePDAlt[aSeries /. {k -> k2},
										    bSeries /. {k -> k1}]][q,t]],
						      {bSeries} ~Join~ PosAdjEigenvalues[],
						      {aSeries} ~Join~ NegFundEigenvalues[]]]];
Print["check that answers coincide: ", Tally[ansPP13 - ansPP21]];
ansPP13 // TeXForm;
ansUR = ansPP13;

(* Factor[Simplify[ansUR /. {t -> -1}]] *)
                                                                                                                                       
(* ### Learn the evolution coefficient matrix for the UL region ### *)
ansNP01 = Block[{C = 2, DD = 2, extraPoints = 1},
		With[{aSeries = -k,
		      bSeries = 2 k + 1},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
							       Kh[FigeightLikePDAlt[aSeries /. {k -> k2},
										    bSeries /. {k -> k1}]][q,t]],
						      {bSeries} ~Join~ PosAdjEigenvalues[],
						      {aSeries} ~Join~ NegFundEigenvalues[]]]];
ansNP01 // TeXForm;
ansUL = ansNP01;

Factor[Simplify[
    {{AA[1,1], AA[1,2] + AA[1,3]},
     {AA[2,1], AA[2,2] + AA[2,3]}} /. (ansUR /. {t -> -1})]] // TeXForm

(* ### Learn the evolution coefficient matrix for the LL region ### *)
ansNN13 = Block[{C = 2, DD = 2, extraPoints = 2},
		With[{aSeries = -k - 1,
		      bSeries = -2 k - 3},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
							       Kh[FigeightLikePDAlt[aSeries /. {k -> k2},
										    bSeries /. {k -> k1}]][q,t]],
						      {bSeries} ~Join~ PosAdjEigenvalues[],
						      {aSeries} ~Join~ NegFundEigenvalues[]]]];
ansNN21 = Block[{C = 2, DD = 2, extraPoints = 2},
		With[{aSeries = -k - 2,
		      bSeries = -2 k - 1},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
							       Kh[FigeightLikePDAlt[aSeries /. {k -> k2},
										    bSeries /. {k -> k1}]][q,t]],
						      {bSeries} ~Join~ PosAdjEigenvalues[],
						      {aSeries} ~Join~ NegFundEigenvalues[]]]];
Print["check that answers coincide: ", Tally[ansNN13 - ansNN21]];
ansNN13 // TeXForm;
ansLL = ansNN13;
