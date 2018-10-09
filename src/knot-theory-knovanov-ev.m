
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
		  (* Print[List[comb, indets, correctionFactors]]; *)
		  Module[{eqns = Map[(family @@ #) - (comb @@ #) == 0 &,
				     Tuples[Map[Range[0, Length[#] - 1 - 1] &,
						specs]]]},
			 Module[{ans = Solve[eqns, indets]},
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
	    myCC = connectedComponents},
	   (* Print["myCC: ", myCC]; *)
	   For[i = 1, i <= Length[myCC], i ++,
	       Module[{foundCut = False},
		      For[j = 1, j <= Length[myCC[[i]]], j ++,
			  (* ### vv First we try to find good edge to cut the numbering at ### *)
			  If[UnderIncomingCrossingQ[edgeCrossingsIn[myCC[[i, j]]],
						    myCC[[i, j]]],
			     CompoundExpression[myCC[[i]] = Join[myCC[[i, j + 1 ;; ]], myCC[[i, ;; j]]],
						foundCut = True;
						Break[]]]];
		      If[Not[foundCut],
			 CompoundExpression[
			     (* ### vv If we hadn't found such an edge, we create a small loop ### *)
			     Print["I'm in creating new crossing"];
			     myCC[[i]] = myCC[[i]] ~Join~ {SmallLoopEdge[[i, 1]], SmallLoopEdge[[i, 2]]};
			     Module[{it = prevEdge[myCC[[i, 1]]]},
				    nextEdge[it] = SmallLoopEdge[[i, 1]];
				    nextEdge[SmallLoopEdge[[i, 1]]] = SmallLoopEdge[[i, 2]];
				    nextEdge[SmallLoopEdge[[i, 2]]] = myCC[[i, 1]];
				    prevEdge[myCC[[i, 1]]] = SmallLoopEdge[[i, 2]];
				    prevEdge[SmallLoopEdge[[i, 2]]] = SmallLoopEdge[[i, 1]];
				    prevEdge[SmallLoopEdge[[i, 1]]] = it;
				    Module[{oldCrossing = edgeCrossingOut[myCC[[i, 1]]],
					    modifiedCrossing = (edgeCrossingOut[myCC[[i, 1]]]
								/. {myCC[[i, 1]] -> SmallLoopEdge[[i, 1]]}),
					    newCrossing = Yp[SmallLoopEdge[[i, 2]], SmallLoopEdge[[i, 1]],
							     SmallLoopEdge[[i, 2]], myCC[[i, 1]]]},
					   Scan[Function[{edge},
							 If[edgeCrossingIn[edge] === oldCrossing,
							    edgeCrossingIn[edge] = modifiedCrossing];
							 If[edgeCrossingOut[edge] === oldCrossing,
							    edgeCrossingOut[edge] = modifiedCrossing]],
						List @@ modifiedCrossing];
					   edgeCrossingOut[SmallLoopEdge[[i, 1]]] = modifiedCrossing;
					   edgeCrossingIn[SmallLoopEdge[[i, 1]]] = newCrossing;
					   edgeCrossingOut[SmallLoopEdge[[i, 2]]] = newCrossing;
					   edgeCrossingIn[SmallLoopEdge[[i, 2]]] = newCrossing;
					   edgeCrossingOut[myCC[[i, 1]]] = newCrossing;]]]]]];
	   (* Print["myCC: ", myCC]; *)
	   Module[{diag = (DeleteDuplicates[Values[edgeCrossingsIn]]
			   /. MapIndexed[Rule[#1, #2[[1]]] &,
					 Flatten[myCC]])},
		  YPMsToXs[(PD @@ diag)]]];
YPMsToXs[expr_] :=
    (* ### Convert notation for crossings back to the counter-intuitive notation, but which is understood by KnotTheory ### *)
    (expr /. {Ym[a_, b_, c_, d_] :> X[a, b, d, c],
	      Yp[a_, b_, c_, d_] :> X[b, d, c, a]});
(* ExpandBraidIntoCrossings[Braid[2, a, {2, 1}, {4, 3}], {-1,1}, -2] *)
(* ConnectionScheme[BraidSpec[Braid[2, a, {2, 1}, {4, 3}], Braid[2, b, {3, 1}, {4, 2}]], *)
(* 		 {1,1}] *)
(* ExternalConnectionScheme[BraidSpec[Braid[2, a, {2, 1}, {4, 3}], Braid[2, b, {3, 1}, {4, 2}]]] *)

Block[{aa = 2, bb = 3},
      Block[{pd = PlanarDiagram[BraidSpec[Braid[2, a, {2, 1}, {4, 3}], Braid[2, b, {3, 1}, {4, 2}]],
				OriChoice[II[a, 0] -> 1, II[a, 1] -> 1, II[b, 0] -> 1, II[b, 1] -> -1],
				{aa, bb}]},
	    Module[{kh = Kh[ExtendedPDToUsual[PlanarDiagramToAdvancedStructures[pd]]][q,t]},
		   Print["kh: ", kh]]]];
      

pd

(* ### Learn the evolution coefficient matrix for the UR region ### *)
ansPP13 = Block[{extraPoints = 2},
		With[{aSeries = k + 1,
		      bSeries = 2 k + 3},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
							       Module[{it = Kh[ExtendedPDToUsual[
								   PlanarDiagramToAdvancedStructures[
								       PlanarDiagram[BraidSpec[Braid[2, a, {2, 1}, {4, 3}],
											       Braid[2, b, {3, 1}, {4, 2}]],
										     OriChoice[II[a, 0] -> 1,
											       II[a, 1] -> 1,
											       II[b, 0] -> 1,
											       II[b, 1] -> -1],
										     {(aSeries /. {k -> k2}),
										      (bSeries /. {k -> k1})}]]]][q,t]},
								      (* Print["Kh: ", it]; *)
								      it]],
						      {bSeries} ~Join~ NegAdjEigenvalues[],
						      {aSeries} ~Join~ PosFundEigenvalues[]]]];

ansPP13

PlanarDiagramToAdvancedStructures[pd]


Kh[ExtendedPDToUsual[PlanarDiagramToAdvancedStructures[pd]]][q,t]

         1
Out[40]= - + q
         q

ExtendedPDToUsual[PlanarDiagramToAdvancedStructures[pd]]



(* DepthTwoLexiSort[II[a,0], II[b,0]] *)
(* OrientationClusters[BraidSpec[Braid[2, a, {2, 1}, {4, 3}], Braid[2, b, {3, 1}, {4, 2}]]] *)

Block[{n = 12},
      Module[{knots = AllKnots[n]},
	     Scan[Function[{knot},
			   If[Not[MemberQ[Map[Length[CoefficientRules[#, {t, t^(-1)}]] &,
					      Table[CheckKhovanovSkein[knot, i], {i, 1, n}]],
					  1]],
			      Print["Knot doesn't have monomial cut: ", knot]]],
		  knots];
	     Print["n: ", n, " done"]]];
(* ### Here we've found non-monomial knot ### *)
(* ### Knot doesn't have monomial cut: Knot[11, NonAlternating, 81] ### *)


(* ### Archive the previous evaluation attempts ### *)
(* FitFamilyWithEigenvalues[TwoStrandKhovanov, PosFundEigenvalues[]] *)
(* FitFamilyWithEigenvalues[TwoStrandKhovanov[-#] &, NegFundEigenvalues[]] *)
(* FitFamilyWithEigenvalues[Kh[FigeightLikePD[1, #+1]][q,t] &, NegFundEigenvalues[]] *)
(* Block[{C = 2, DD = 2}, *)
(*       FitFamilyWithEigenvalues[Kh[FigeightLikePD[1, # - 1]][q,t] &, NegFundEigenvalues[]]] *)
(* Block[{C = 2, DD = 2}, *)
(*       FitFamilyWithEigenvalues[Kh[FigeightLikePD[1, -#-1]][q,t] &, PosFundEigenvalues[]]] *)
(* Kh[TorusKnot[2,-2]][q,t] *)
(* Block[{C = 2, DD = 2}, *)
(*       Kh[FigeightLikePDAlt[-1, 1]][q,t]] *)
(* Block[{C = 2, DD = 2}, *)
(*       Kh[FigeightLikePDAlt[-2, 4]][q,t]] *)
XsToYPMs[expr_] :=
    (* ### Convert notation for crossings of the planar diagram into more intuitive form: ### *)
    (* ### the positive and negative crossings, where indices are in the order:
       lower-left, lower-right, upper-left, upper-right ### *)
    (* ### "Lower" indices are the incoming ones, upper are "outgoing" ones ### *)
    (expr /. {X[a_, b_, c_, d_] :> If[b < d,
				      Ym[a, b, d, c],
				      Yp[d, a, c, b]]});
CheckPlanarDiagram[lst_PD] :=
    Module[{lstLst = List @@ lst},
	   Module[{indices = Tally[Flatten[Map[List @@ # &, lstLst]]]},
		  Module[{indsFirst = Map[#[[1]] &, indices]},
			 Module[{max = Max @@ indsFirst,
				 min = Min @@ indsFirst},
				If[Sort[indices, #1[[1]] < #2[[1]] &] === Map[{#, 2} &, Range[min, max]],
				   CheckPassed,
				   CheckFailed]]]]];

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

Factor[Simplify[ansLL /. {t -> -1}]]

(* ### Learn the evolution coefficient matrix for the LR region ### *)
ansPN01 = Block[{C = 2, DD = 2, extraPoints = 2},
		With[{aSeries = k,
		      bSeries = -2 k - 1},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
							       Kh[FigeightLikePDAlt[aSeries /. {k -> k2},
										    bSeries /. {k -> k1}]][q,t]],
						      {bSeries} ~Join~ PosAdjEigenvalues[],
						      {aSeries} ~Join~ NegFundEigenvalues[]]]];
ansPN01 // TeXForm;
ansLR = ansPN01;

MyJones[a_, b_] :=
    ({1, (-q^2)^b}
     . ({{AA[1,1], AA[1,2]},{AA[2,1],AA[2,2]}} /. (ansLR /. {t -> -1}))
     . {q^a, (-q^3)^a});

MyKhUR[a_, b_] :=
    ({1, (t q^2)^(b)}
     . ({{AA[1,1], AA[1,2], AA[1,3]},{AA[2,1],AA[2,2],AA[2,3]}} /. ansUR)
     . {q^(-a), (t q^3)^(-a), (-t q^3)^(-a)});
MyKhUL[a_, b_] :=
    ({1, (t q^2)^(b)}
     . ({{AA[1,1], AA[1,2], AA[1,3]},{AA[2,1],AA[2,2],AA[2,3]}} /. ansUL)
     . {q^(-a), (t q^3)^(-a), (-t q^3)^(-a)});
MyKhLR[a_, b_] :=
    ({1, (t q^2)^(b)}
     . ({{AA[1,1], AA[1,2], AA[1,3]},{AA[2,1],AA[2,2],AA[2,3]}} /. ansLR)
     . {q^(-a), (t q^3)^(-a), (-t q^3)^(-a)});
MyKhLL[a_, b_] :=
    ({1, (t q^2)^(b)}
     . ({{AA[1,1], AA[1,2], AA[1,3]},{AA[2,1],AA[2,2],AA[2,3]}} /. ansLL)
     . {q^(-a), (t q^3)^(-a), (-t q^3)^(-a)});

Simplify[MyKh[-2,1]]

Block[{sH = Null, a = -3, b = 1},
      Expand[Simplify[If[sH === Null,
			 Factor[Simplify[MyKh[a, b]]],
			 (MyKh[a, b] - q^(2 sH - 1)(1+q^2))/(1 + t q^4)]]]]

Block[{a = 10, b = 1},
      Block[{sH = -(a/2 - 1)},
	    Expand[Simplify[If[sH === Null,
			       Factor[Simplify[MyKhUR[a, b]]],
			       (MyKhUR[a, b] - q^(2 sH - 1)(1+q^2))/(1 + t q^4)]]]]]

Block[{a = -10, b = 1},
      Block[{sH = -a/2},
	    Expand[Simplify[If[sH === Null,
			       Factor[Simplify[MyKhUL[a, b]]],
			       (MyKhUL[a, b] - q^(2 sH - 1)(1+q^2))/(1 + t q^4)]]]]]

Block[{a = 10, b = -1},
      Block[{sH = -a/2},
	    Expand[Simplify[If[sH === Null,
			       Factor[Simplify[MyKhLR[a, b]]],
			       (MyKhLR[a, b] - q^(2 sH - 1)(1+q^2))/(1 + t q^4)]]]]]

Block[{a = -10, b = -1},
      Block[{sH = -a/2-1},
	    Expand[Simplify[If[sH === Null,
			       Factor[Simplify[MyKhLL[a, b]]],
			       (MyKhLL[a, b] - q^(2 sH - 1)(1+q^2))/(1 + t q^4)]]]]]

                                    


Block[{sH = 10, a = 4, b = 5},
      Expand[Simplify[If[sH === Null,
			 Factor[Simplify[MyJones[a, b]]],
			 (MyJones[a, b] - q^(2 sH - 1)(1+q^2))/(1 - q^4)]]]]


Expand[Simplify[Factor[Simplify[({{AA[1,1] - (1+q^2) q^(1), AA[1,2] + AA[1,3]},{AA[2,1], AA[2,2] + AA[2,3]}} /. ansUR)
				/. {t -> -1}]] (q + 1/q)]]

          
             -2    2    4             -2    2       -2    2
Out[207]= {{q   - q  - q , 1}, {-1 - q   - q , 1 + q   + q }}


Expand[Factor[Simplify[{{AA[1,1] - (1+q^2) q^(1), AA[1,2] + AA[1,3]},{AA[2,1], AA[2,2] + AA[2,3]}} /. ansUR]
	      /(1+t q^4) (1 - t^2 q^4) (- q t + 1/q)]] // TeXForm

         
              1       2      4  2             1      2         1      2
Out[23]= {{-(----) + q  t - q  t , 1}, {-1 + ---- + q  t, 1 - ---- - q  t}}
              2                               2                2
             q  t                            q  t             q  t


Expand[Simplify[Factor[Simplify[({{AA[1,1] - (1+q^2) q^(-1), AA[1,2] + AA[1,3]},{AA[2,1], AA[2,2] + AA[2,3]}} /. ansUL)
				/. {t -> -1}]] (q + 1/q)]]

         
                          -2    2       -2    2
Out[22]= {{-1, 1}, {-1 - q   - q , 1 + q   + q }}


Expand[Factor[Simplify[{{AA[1,1] - (1+q^2) q^(-1), AA[1,2] + AA[1,3]},{AA[2,1], AA[2,2] + AA[2,3]}} /. ansUL]
	      /(1+t q^4) (1 - t^2 q^4) (- q t + 1/q)]] // TeXForm

         
Out[55]//TeXForm= \left(
                  \begin{array}{cc}
                   t & -t \\
                   -q^2 t^2+t-\frac{1}{q^2} & q^2 t^2-t+\frac{1}{q^2} \\
                  \end{array}
                  \right)

         
                      -2        2  2   -2        2  2
Out[21]= {{t, -t}, {-q   + t - q  t , q   - t + q  t }}


Expand[Simplify[Factor[Simplify[({{AA[1,1] - (1+q^2) q^(-1), AA[1,2] + AA[1,3]},{AA[2,1], AA[2,2] + AA[2,3]}} /. ansLR)
				/. {t -> -1}]] (q + 1/q)]]

         
                          -2    2       -2    2
Out[36]= {{-1, 1}, {-1 - q   - q , 1 + q   + q }}




Expand[Factor[Simplify[{{AA[1,1] - (1+q^2) q^(-1), AA[1,2] + AA[1,3]},{AA[2,1], AA[2,2] + AA[2,3]}} /. ansLR]
	      /(1+t q^4) (1 - t^2 q^4) (- q t + 1/q)]] // TeXForm

                      -2        2  2   -2        2  2
Out[35]= {{t, -t}, {-q   + t - q  t , q   - t + q  t }}


Expand[Simplify[Factor[Simplify[({{AA[1,1] - (1+q^2) q^(-3), AA[1,2] + AA[1,3]},{AA[2,1], AA[2,2] + AA[2,3]}} /. ansLL)
				/. {t -> -1}]] (q + 1/q)]]

         
             -4    -2    2             -2    2       -2    2
Out[51]= {{-q   - q   + q , 1}, {-1 - q   - q , 1 + q   + q }}

Expand[Factor[Simplify[{{AA[1,1] - (1+q^2) q^(-3), AA[1,2] + AA[1,3]},{AA[2,1], AA[2,2] + AA[2,3]}} /. ansLL]
	      /(1+t q^4) (1 - t^2 q^4) (- q t + 1/q)]] // TeXForm

         
             -4   t     2  3   2    t     2    2  3    t      2    2  3
Out[50]= {{-q   + -- - q  t , t }, {-- - t  + q  t , -(--) + t  - q  t }}
                   2                 2                  2
                  q                 q                  q





Block[{i = 2, j = 3},
      List[Simplify[(AA[i,j] /. ansLR) / (AA[i,j] /. ansLL)],
	   Simplify[(AA[i,j] /. ansUL) / (AA[i,j] /. ansLL)],
	   Simplify[(AA[i,j] /. ansUR) / (AA[i,j] /. ansUL)]]]

                           
           2   2   2
Out[26]= {q , q , q }



Block[{C = 2, DD = 2, extraPoints = 2},
      FitFamilyWithEigenvaluesAdvanced[Function[{k1},
						Kh[FigeightLikePDAlt[k1+1, 3]][q,t]],
				       {k+1} ~Join~ NegFundEigenvalues[]]]




      
(* Block[{C = 2, DD = 2}, *)
(*       Kh[FigeightLikePD[1, -1]][q,t]] *)


Block[{C = 2, DD = 2},
      FitFamilyWithEigenvalues[Kh[FigeightLikePD[3, # - 2]][q,t] &, NegFundEigenvalues[]]]


Block[{C = 2, DD = 2},
      FitFamilyWithEigenvalues[Kh[FigeightLikePD[3, - # -1]][q,t] &, PosFundEigenvalues[]]]


Block[{C = 2, DD = 2},
      FitFamilyWithEigenvalues[Kh[FigeightLikePD[5, #-2]][q,t] &, NegFundEigenvalues[]]]

Block[{C = 2, DD = 2},
      FitFamilyWithEigenvalues[Kh[FigeightLikePD[5, -#-1]][q,t] &, PosFundEigenvalues[]]]

Block[{C = 2, DD = 2},
      FitFamilyWithEigenvalues[Kh[FigeightLikePD[7, #-2]][q,t] &, NegFundEigenvalues[]]]

Block[{C = 2, DD = 2},
      FitFamilyWithEigenvalues[Kh[FigeightLikePD[7, -#-1]][q,t] &, PosFundEigenvalues[]]]


Block[{C = 2, DD = 2},
      FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[2 # + 1, 1]][q,t] &,
			       {q^(-2), t^(-2) q^(-6)}]]

Block[{C = 2, DD = 2},
      Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[#+1, 1]][q,t] &,
				      NegFundEigenvalues[]]]]
Block[{C = 2, DD = 2},
      Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[-#+1, 1]][q,t] &,
				      PosFundEigenvalues[]]]]


Block[{C = 2, DD = 2},
      Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[#-1, -3]][q,t] &,
				      NegFundEigenvalues[]]]]

Block[{C = 2, DD = 2},
      Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[-#, -3]][q,t] &,
				      PosFundEigenvalues[]]]]

Block[{C = 2, DD = 2},
      Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[#-1, -5]][q,t] &,
				      NegFundEigenvalues[]]]]

Block[{C = 2, DD = 2},
      Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[-#, -5]][q,t] &,
				      PosFundEigenvalues[]]]]

FaltPosSeriesNegN[n_] :=
    Block[{C = 2, DD = 2},
	  Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[#-1, -2 n - 1]][q,t] &,
					  NegFundEigenvalues[]]]];
FaltNegSeriesNegN[n_] :=
    Block[{C = 2, DD = 2},
	  Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[-#, -2 n - 1]][q,t] &,
					  PosFundEigenvalues[]]]];
FaltPosSeries[n_] :=
    Block[{C = 2, DD = 2},
	  Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[#, 2 n + 1]][q,t] &,
					  NegFundEigenvalues[]]]];
FaltNegSeries[n_] :=
    Block[{C = 2, DD = 2},
	  Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[-#+1, 2 n + 1]][q,t] &,
					  PosFundEigenvalues[]]]];



Block[{C = 2, DD = 2},
      Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[-#+1, 1]][q,t] &,
				      PosFundEigenvalues[]]]]

Block[{C = 2, DD = 2},
      Kh[FigeightLikePDAlt[1, 1]]]

         
           0
         #2        0   0     2   0
Out[85]= --- + 2 #1  #2  + #1  #2  & 
           2
         #1



                  {0, 0, 0, 0, 0}

                           2    6  2    8  3                          2
                      1 + q  - q  t  + q  t               -1 + t + 2 q  t
Out[84]= {AA[1] -> -(-------------------------), AA[2] -> ---------------, 
                      2        2          2                         2
                     q  (-1 + q  t) (1 + q  t)             2 (-1 + q  t)
 
                 1 + t
>    AA[3] -> ------------}
                      2
              2 (1 + q  t)


Block[{n = 5},
      (AA[3] /. FaltPosSeries[n])
      - (-1)/2/(1 + t q^2) (1 + t) t^(2 n + 1) q^(4 n + 5)]

Block[{n = 5},
      (AA[3] /. FaltNegSeries[n])
      - 1/2/(1 + t q^2) (1 + t) t^(2 n) q^(4 n)]

FitFamilyWithEigenvalues[Function[{n},
				  (AA[3] /. FaltPosSeries[-n-1])],
			 {1, t^2 q^4}]

faltPosAns = Block[{C = 2, DD = 2},
		   Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[#+1, 1]][q,t] &,
						   NegFundEigenvalues[]]]];

faltNegAns = Block[{C = 2, DD = 2},
		   Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[-#+1, 1]][q,t] &,
						   PosFundEigenvalues[]]]];


faltPosAnsNegN = Block[{C = 2, DD = 2},
		       Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[#-1, -1]][q,t] &,
						       NegFundEigenvalues[]]]];
faltNegAnsNegN = Block[{C = 2, DD = 2},
		       Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[-#-1, -1]][q,t] &,
						       PosFundEigenvalues[]]]];

(* Block[{C = 2, DD = 2}, *)
(*       Kh[FigeightLikePDAlt[-1, -1]][q,t]] *)

faltOneNegAnsA1 = Factor[Simplify[(AA[1] + AA[2] (t^2 q^4)^n /. FitFamilyWithEigenvalues[Function[{n},
											       (AA[1] /. FaltNegSeries[n])],
										      {1, t^(2) q^(4)}]) /. {n -> 0}]];
faltOneNegAnsA2 = Factor[Simplify[(AA[1] + AA[2] (t^2 q^4)^n /. FitFamilyWithEigenvalues[Function[{n},
											       (AA[2] /. FaltNegSeries[n])],
										      {1, t^(2) q^(4)}]) /. {n -> 0}]];
faltOneNegAnsA3 = Factor[Simplify[(AA[1] + AA[2] (t^2 q^4)^n /. FitFamilyWithEigenvalues[Function[{n},
											       (AA[3] /. FaltNegSeries[n])],
										      {1, t^(2) q^(4)}]) /. {n -> 0}]];

faltOneAnsNegNA1 = Factor[Simplify[(AA[1] + AA[2] (t^(-2) q^(-4))^n /. FitFamilyWithEigenvalues[Function[{n},
												   (AA[1] /. FaltPosSeriesNegN[n])],
											  {1, t^(-2) q^(-4)}]) /. {n -> 0}]];
faltOneAnsNegNA2 = Factor[Simplify[(AA[1] + AA[2] (t^(-2) q^(-4))^n /. FitFamilyWithEigenvalues[Function[{n},
												   (AA[2] /. FaltPosSeriesNegN[n])],
											  {1, t^(-2) q^(-4)}]) /. {n -> 0}]];
faltOneAnsNegNA3 = Factor[Simplify[(AA[1] + AA[2] (t^(-2) q^(-4))^n /. FitFamilyWithEigenvalues[Function[{n},
												   (AA[3] /. FaltPosSeriesNegN[n])],
											  {1, t^(-2) q^(-4)}]) /. {n -> 0}]];


Simplify[(AA[1] /. faltPosAns)/faltOneAnsA1]

Simplify[(AA[2] /. faltPosAns)/faltOneAnsA2]

Simplify[(AA[3] /. faltPosAns)/faltOneAnsA3]


Simplify[(AA[1] /. faltNegAns)/faltOneNegAnsA1]

Simplify[(AA[2] /. faltNegAns)/faltOneNegAnsA2]

Simplify[(AA[3] /. faltNegAns)/faltOneNegAnsA3]


Simplify[(AA[1] /. faltPosAnsNegN)/faltOneAnsNegNA1]

Simplify[(AA[2] /. faltPosAnsNegN)/faltOneAnsNegNA2]

Simplify[(AA[3] /. faltPosAnsNegN)/faltOneAnsNegNA3]


FitFamilyWithEigenvalues[Function[{n},
				  (AA[2] /. FaltPosSeriesNegN[n])],
			 {1, t^(-2) q^(-4)}]

FitFamilyWithEigenvalues[Function[{n},
				  (AA[2] /. FaltNegSeriesNegN[n])],
			 {1, t^(-2) q^(-4)}]

                          2       4
                       q t  (1 + q  t)
 Out[72]= {AA[1] -> -----------------------, 
                          2   2       2
                   (-1 + q  t)  (1 + q  t)
 
                            2      4  2    4  3      6  3      8  4
              -(-1 + t + 2 q  t + q  t  + q  t  - 2 q  t  + 2 q  t )
>    AA[2] -> ------------------------------------------------------}
                             3          2   2       2
                          2 q  t (-1 + q  t)  (1 + q  t)


FitFamilyWithEigenvalues[Function[{n},
				  (AA[3] /. FaltNegSeriesNegN[n])],
			 {1, t^(-2) q^(-4)}]

FitFamilyWithEigenvalues[Function[{n},
				  (AA[1] /. FaltPosSeriesNegN[n])],
			 {1, t^(-2) q^(-4)}]

AA[1] /. Apart[FitFamilyWithEigenvalues[Function[{n},
					(AA[1] /. FaltPosSeries[n])],
			       {1, t^(2) q^(4)}],
	       t]

                            3               3               3
              1       -q - q           q - q          -q + q
Out[69]= q - --- + -------------- + ------------- + ------------
             q t            2   2            2              2
                   2 (-1 + q  t)    4 (-1 + q  t)   4 (1 + q  t)

AA[1] /. Apart[FitFamilyWithEigenvalues[Function[{n},
						 (AA[1] /. FaltNegSeries[n])],
					{1, t^(2) q^(4)}],
	       t]
              2             2                    2                 2
         1 + q         1 + q              1 + 3 q            -1 + q
Out[70]= ------ + ----------------- + ---------------- + ---------------
            2        2        2   2      2        2         2       2
           q      2 q  (-1 + q  t)    4 q  (-1 + q  t)   4 q  (1 + q  t)

FitFamilyWithEigenvalues[Function[{n},
				  (AA[1] /. FaltPosSeries[n])],
			 {1, t^2 q^4}]


FitFamilyWithEigenvalues[Function[{n},
				  (AA[1] /. FaltNegSeries[n])],
			 {1, t^2 q^4}]


FitFamilyWithEigenvalues[Function[{n},
				  (AA[2] /. FaltPosSeries[n])],
			 {1, t^2 q^4}]



FitFamilyWithEigenvalues[Function[{n},
				  (AA[2] /. FaltNegSeries[n])],
			 {1, t^2 q^4}]

                                   4
                              1 + q  t
Out[41]= {AA[1] -> -(--------------------------), 
                      2        2   2       2
                     q  (-1 + q  t)  (1 + q  t)
 
                      2    2      6  2    6  3      8  3
              -(-2 - q  + q  t + q  t  - q  t  - 2 q  t )
>    AA[2] -> -------------------------------------------}
                        2        2   2       2
                     2 q  (-1 + q  t)  (1 + q  t)




Block[{C = 2, DD = 2},
      Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[-#+1, 3]][q,t] &,
				      PosFundEigenvalues[]]]]


Block[{C = 2, DD = 2},
      Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[#, 5]][q,t] &,
				      NegFundEigenvalues[]]]]

Block[{C = 2, DD = 2},
      Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[-#+1, 5]][q,t] &,
				      PosFundEigenvalues[]]]]


Block[{C = 2, DD = 2},
      Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[#, 7]][q,t] &,
				      NegFundEigenvalues[]]]]

Block[{C = 2, DD = 2},
      Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePDAlt[-#+2, 7]][q,t] &,
				      PosFundEigenvalues[]]]]




Block[{C = 2, DD = 2},
      Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePD[1, #]][q,t] &,
				      {q^(-1), - q^(-1), t^(-1) q^(-3), -t^(-1) q^(-3)}]]]

Block[{C = 2, DD = 2},
      Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePD[2, 2 #]][q,t] &,
				      {1, t^2 q^4}]]]

(* ### Test of topological invariance of Jones polynomial in KnotTheory ### *)
TwoStrandSimpleBraid[a_] :=
    Block[{C = 4, A = Abs[a]},
	  (PD @@ Join[ParallelTwoStrandBraid[A + 2 C + 1, C + 1, a],
		      ParallelDummyTwoStrandBraid[A + C + 1, 1, C]]
	   /. {2 A + 2 C + 1 -> 1})];
(* Jones[TwoStrandSimpleBraid[-1]][q] *)


Jones[TwoStrandSimpleBraid[2]][q]

TwoStrandSimpleBraid[0]

Out[17]= PD[X[5, 1, 6, 2], X[6, 3, 7, 2], X[7, 3, 8, 4], X[8, 5, 1, 4]]

Kh[TwoStrandSimpleBraid[0] (* , Program -> "FastKh" *)][q, t]

KnotTheory::credits: 
   The Khovanov homology program FastKh was written by Dror Bar-Natan.

         1
Out[20]= - + q
         q


?? Kh

        1
Out[7]= - + q
        q

        1
Out[6]= - + q
        q



Table[Block[{C = 2, DD = 2},
	    Module[{diag = FigeightLikePD[a, b]},
		   Expand[Simplify[Jones[diag][q^2] * (- q - 1/q) (-1) (-1)^(a b), Assumptions -> q > 0]]
		    - Expand[Simplify[Kh[diag, Program -> "FastKh"][q, t] /. {t -> -1}]]]],
      {a, -5, 5},
      {b, -5, 5}]


Block[{C = 2, DD = 2},
      FigeightLikePD[1, 1]]

         
Out[23]= PD[X[1, 8, 2, 9], X[2, 10, 3, 9], X[3, 10, 4, 11], X[6, 12, 1, 11], 
 
>    X[12, 6, 13, 5], X[13, 4, 8, 5]]




Block[{C = 2, DD = 2},
      Factor[FitFamilyWithEigenvalues[Kh[FigeightLikePD[2, 2 # + 1]][q,t] &,
				      {1, t^2 q^4}]]]

                  {0, 0, 0, 0, 0}

                         4      4  2    6  3    8  3      8  4    10  5
                   -1 - q  t - q  t  + q  t  - q  t  - 2 q  t  + q   t
Out[46]= {AA[1] -> ----------------------------------------------------, 
                                     11  4        2
                                    q   t  (-1 + q  t)
 
                    4          4  2        2      4  2
              (1 + q  t) (1 + q  t ) (1 - q  t + q  t )
>    AA[2] -> -----------------------------------------}
                          11  4        2
                         q   t  (-1 + q  t)



Block[{C = 2, DD = 2, n = -2},
      Expand[Simplify[((Kh[FigeightLikePD[2, n]][q,t]
			- (q + q^3 + t^2 q^5 + t^3 q^9))
		       - (1 - (t^2 q^4)^((n-2)/2))/(1 - (t^2 q^4)) (t q^3 + t^2 q^7 + t^4 q^9 + t^5 q^13)
		      )]]]







Block[{C = 2, DD = 2, n = 6},
      Expand[Simplify[(Kh[FigeightLikePDAlt[n, 1]][q,t]
		       - (q^(1-n)
		      )
		     ]]]

                        
         -7    -5     1        1        1        1        1        1
Out[6]= q   + q   + ------ + ------ + ------ + ------ + ------ + -----
                     21  7    17  6    17  5    13  4    13  3    9  2
                    q   t    q   t    q   t    q   t    q   t    q  t

                        
         -5    -3     1        1        1        1
Out[5]= q   + q   + ------ + ------ + ------ + -----
                     15  5    11  4    11  3    7  2
                    q   t    q   t    q   t    q  t

                        
         -3   1     1       1
Out[4]= q   + - + ----- + -----
              q    9  3    5  2
                  q  t    q  t


Block[{C = 0, DD = 0},
      FigeightLikePDAlt[2, 2]]

         
Out[73]= PD[X[5, 3, 6, 2], X[1, 7, 2, 6], X[1, 4, 9, 3], X[4, 1, 5, 7]]

Block[{C = 2, DD = 2},
      FitFamilyWithEigenvalues[Kh[FigeightLikePD[3, - # -1]][q,t] &, PosFundEigenvalues[]]]



(* Expand[Block[{n = 18}, *)
(* 	     Simplify[(TwoStrandKhovanov[n] *)
(* 		       - (q^n + q^(n-2)) *)
(* 		       - t^n q^(3 n) *)
(* 		       - t^2 q^(2 + n) *)
(* 		       - (1 - (q^4 t^2)^(n/2-1))/(1 - q^4 t^2) q^(n+6) (t^3 + t^4)) *)
(* 		     ]]] *)

(* TwoStrandKhovanovTheor[n_] := *)
(*     (q^n(1 + q^(-2) + t^2 q^2 + q^6 (t^3 + t^4)/(1 - q^4 t^2)) *)
(*      + t^n q^(3 n) (1 - 1/2 (q^(-4) t^(-2) + q^(-6) t^(-3)) q^6 (t^3 + t^4)/(1 - q^4 t^2)) *)
(*      + (-t)^n q^(3 n) (-1) 1/2 (q^(-4) t^(-2) - q^(-6) t^(-3)) q^6 (t^3 + t^4)/(1 - q^4 t^2)); *)

(* Expand[Block[{n = 13}, *)
(* 	     Simplify[(TwoStrandKhovanov[n] *)
(* 		       - (q^n + q^(n-2)) *)
(* 		       - t^n q^(3 n) *)
(* 		       - t^2 q^(2 + n) *)
(* 		      ) / q^(n+6) /(t^3 + t^4) *)
(* 		      - ((1 - (q^4 t^2)^((n-3)/2))/(1 - q^4 t^2)) *)
(* 		     ]]] *)

(* Expand[Block[{n = 10}, *)
(* 	     Simplify[(TwoStrandKhovanov[n] *)
(* 		       - TwoStrandKhovanovTheor[n]) *)
(* 		     ]]] *)

