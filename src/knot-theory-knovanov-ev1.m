
Quiet[<< KnotTheory`];
Quiet[<< Combinatorica`];

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
TwoStrandKhovanov[aa_] :=
    Block[{prePd = PlanarDiagram[BraidSpec[Braid[2, a, {1, 2}, {3, 4}],
					   Braid[2, b, {3, 4}, {1, 2}]],
				 OriChoice[II[a, 0] -> 1, II[a, 1] -> 1,
					   II[b, 0] -> 1, II[b, 1] -> 1],
				 {aa, 0}]},
	  Block[{pd = ExtendedPDToUsual[PlanarDiagramToAdvancedStructures[prePd]]},
		(* Print["pre pd: ", prePd]; *)
		(* Print["pd: ", pd]; *)
		Module[{it = Kh[pd][q,t]},
		       it]]];
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
SecondNonToricKhovanov[aa_, bb_] :=
    Block[{prePd = PlanarDiagram[BraidSpec[Braid[2, a, {1, 2}, {4, 5}],
					   Braid[2, b, {6, 7}, {2, 3}],
					   Braid[3, c, {4, 5, 3}, {1, 6, 7}]],
				 OriChoice[II[a, 0] -> 1, II[a, 1] -> 1,
					   II[b, 0] -> 1, II[b, 1] -> 1,
					   II[c, 0] -> 1, II[c, 1] -> 1, II[c, 2] -> 1],
				 {aa, bb, -1}]},
	  Block[{pd = ExtendedPDToUsual[PlanarDiagramToAdvancedStructures[prePd]]},
		(* Print["pre pd: ", prePd]; *)
		(* Print["pd: ", pd]; *)
		Module[{it = Kh[pd][q,t]},
		       it]]];
SecondNonToricKhovanovPrimeBraid[aa_, bb_] :=
    Module[{i},
	   BR[3, Join[{-2, -1, 1, -1, 2, -2},
		      Table[Sign[bb] 2, {i, 1, Abs[bb]}],
		      Table[Sign[aa] 1, {i, 1, Abs[aa]}]]]];
SimplestThreeStrandBraid[aa_] :=
    Module[{i},
	   BR[3, Join[{1, -1, 2, -2},
		      Table[Sign[aa] 1, {i, 1, Abs[aa]}]]]];
SimplestThreeStrandKhovanov[aa_] := SimplestThreeStrandKhovanov[aa] =
    Kh[PD[SimplestThreeStrandBraid[aa]]][q,t];
ThirdNonToricKhovanovPrimeBraid[aa_, bb_, cc_] :=
    Module[{i},
	   BR[3, Flatten[{Table[Sign[cc] {-2, -1}, {i, 1, Abs[cc]}],
			  {1, -1, 2, -2},
			  Table[Sign[bb] 2, {i, 1, Abs[bb]}],
			  Table[Sign[aa] 1, {i, 1, Abs[aa]}]}]]];
FourthNonToricKhovanovPrimeBraid[aa_, bb_, cc_] :=
    Module[{i},
	   BR[3, Flatten[{Table[Sign[cc] {2, -1}, {i, 1, Abs[cc]}],
			  {1, -1, 2, -2},
			  Table[Sign[bb] 2, {i, 1, Abs[bb]}],
			  Table[Sign[aa] 1, {i, 1, Abs[aa]}]}]]];
FifthNonToricKhovanovPrimeBraid[aa_, bb_, cc_] :=
    Module[{i},
	   BR[3, Flatten[{Table[Sign[cc] {-2, 1}, {i, 1, Abs[cc]}],
			  If[Abs[cc] < 2, {1, -1, 2, -2}, {}],
			  Table[Sign[bb] 2, {i, 1, Abs[bb]}],
			  Table[Sign[aa] 1, {i, 1, Abs[aa]}]}]]];
SecondNonToricKhovanovPrime[aa_, bb_] :=
    Kh[PD[SecondNonToricKhovanovPrimeBraid[aa, bb]]][q,t];
ThirdNonToricKhovanovPrime[aa_, bb_, cc_] := ThirdNonToricKhovanovPrime[aa, bb, cc] =
    Kh[PD[ThirdNonToricKhovanovPrimeBraid[aa, bb, cc]]][q,t];
FourthNonToricKhovanovPrime[aa_, bb_, cc_] := FourthNonToricKhovanovPrime[aa, bb, cc] =
    Kh[PD[FourthNonToricKhovanovPrimeBraid[aa, bb, cc]]][q,t];
FifthNonToricKhovanovPrime[aa_, bb_, cc_] := FifthNonToricKhovanovPrime[aa, bb, cc] =
    Kh[PD[FifthNonToricKhovanovPrimeBraid[aa, bb, cc]]][q,t];
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
ThreeStrandOne[aa_] :=
    Module[{i},
	   Kh[PD[BR[3, Flatten[{{1,-1},{2,-2},
				Table[{1, 2}, {i, 1, aa}]}]]]][q,t]];
ThreeStrandTwo[aa_] :=
    Module[{i},
	   Kh[PD[BR[3, Flatten[{{1,-1},{2,-2},
				Table[{2, 1}, {i, 1, aa}]}]]]][q,t]];
ThreeStrandThree[aa_] :=
    Module[{i},
	   Kh[PD[BR[3, Flatten[{{1,-1},{2,-2},
				Table[{1, 1, 2}, {i, 1, aa}]}]]]][q,t]];
ThreeStrandThreePrime[aa_] :=
    Module[{i},
	   Kh[PD[BR[3, Flatten[{{1,-1},{2,-2},
				Table[{2, 1, 1}, {i, 1, aa}]}]]]][q,t]];
ThreeStrandThreePrimePrime[aa_] :=
    Module[{i},
	   Kh[PD[BR[3, Flatten[{{1,-1},{2,-2},
				Table[{1, 2, 1}, {i, 1, aa}]}]]]][q,t]];
ThreeStrandFour[aa_] :=
    Module[{i},
	   Kh[PD[BR[3, Flatten[{{1,-1},{2,-2},
				Table[{1, 1, 1, 2}, {i, 1, aa}]}]]]][q,t]];
ThreeStrandPro[n_, aa_] :=
    Module[{i, j},
	   Kh[PD[BR[3, Flatten[{{1,-1},{2,-2},
				Table[{Table[1, {j, 1, n}], 2}, {i, 1, aa}]}]]]][q,t]];
ThreeStrandPro2[n_, insert_, aa_] := ThreeStrandPro2[n, insert, aa] =
    Module[{i, j},
	   Kh[PD[BR[3, Flatten[{{1,-1},{2,-2},
				insert,
				Table[{Table[Sign[n], {j, 1, Abs[n]}], 2}, {i, 1, aa}]}]]]][q,t]];
ThreeStrandProCustom[once_, repeat_, aa_] := ThreeStrandProCustom[once, repeat, aa] =
    Module[{i, j},
	   Kh[PD[BR[3, Flatten[{{1,-1},{2,-2}, (* ### << just to make the braid non-trivial ### *)
				once,
				Table[repeat, {i, 1, aa}]}]]]][q,t]];
ThreeStrandPro3[2, {}, 1] :=
    1 + q^(-2) + 1/(q^6*t^2) + 1/(q^4*t^2);
ThreeStrandPro3[2, {}, 2] :=
    (3/q^3 + 3/q + 1/(q^11*t^4) + 1/(q^9*t^4) + 2/(q^9*t^3) + 1/(q^7*t^2) + 
     2/(q^5*t^2) + 1/(q^3*t) + t/q + q^3*t^2);
ThreeStrandPro3[2, {}, 3] :=
    (4/q^4 + 4/q^2 + 1/(q^16*t^6) + 1/(q^14*t^6) + 3/(q^14*t^5) + 3/(q^12*t^4) + 
     3/(q^10*t^4) + 4/(q^10*t^3) + 3/(q^8*t^3) + 5/(q^8*t^2) + 4/(q^6*t^2) + 
     3/(q^6*t) + 5/(q^4*t) + 3*t + (2*t)/q^2 + t^2 + 2*q^2*t^2 + q^4*t^3);
ThreeStrandPro3[2, {}, 4] :=
    11/q^5 + 15/q^3 + 1/(q^21*t^8) + 1/(q^19*t^8) + 4/(q^19*t^7) + 6/(q^17*t^6) + 
    4/(q^15*t^6) + 10/(q^15*t^5) + 6/(q^13*t^5) + 13/(q^13*t^4) + 
    10/(q^11*t^4) + 15/(q^11*t^3) + 13/(q^9*t^3) + 15/(q^9*t^2) + 15/(q^7*t^2) + 
    12/(q^7*t) + 15/(q^5*t) + (7*t)/q^3 + (8*t)/q + (3*t^2)/q + 7*q*t^2 + 
    q*t^3 + 3*q^3*t^3 + q^5*t^4;
ThreeStrandPro3[2, {}, 5] :=
    31/q^6 + 41/q^4 + 1/(q^26*t^10) + 1/(q^24*t^10) + 5/(q^24*t^9) + 
    10/(q^22*t^8) + 5/(q^20*t^8) + 20/(q^20*t^7) + 10/(q^18*t^7) + 
    30/(q^18*t^6) + 20/(q^16*t^6) + 41/(q^16*t^5) + 30/(q^14*t^5) + 
    49/(q^14*t^4) + 41/(q^12*t^4) + 51/(q^12*t^3) + 49/(q^10*t^3) + 
    49/(q^10*t^2) + 51/(q^8*t^2) + 40/(q^8*t) + 49/(q^6*t) + (19*t)/q^4 + 
    (30*t)/q^2 + 19*t^2 + (11*t^2)/q^2 + 4*t^3 + 11*q^2*t^3 + q^2*t^4 + 
    4*q^4*t^4 + q^6*t^5;
ThreeStrandPro3[2, {}, 6] :=
    (96/q^7 + 132/q^5 + 1/(q^31*t^12) + 1/(q^29*t^12) + 6/(q^29*t^11) + 
     15/(q^27*t^10) + 6/(q^25*t^10) + 35/(q^25*t^9) + 15/(q^23*t^9) + 
     61/(q^23*t^8) + 35/(q^21*t^8) + 95/(q^21*t^7) + 61/(q^19*t^7) + 
     130/(q^19*t^6) + 95/(q^17*t^6) + 158/(q^17*t^5) + 130/(q^15*t^5) + 
     175/(q^15*t^4) + 158/(q^13*t^4) + 175/(q^13*t^3) + 175/(q^11*t^3) + 
     158/(q^11*t^2) + 175/(q^9*t^2) + 129/(q^9*t) + 158/(q^7*t) + (62*t)/q^5 + 
     (93*t)/q^3 + (34*t^2)/q^3 + (62*t^2)/q + (16*t^3)/q + 34*q*t^3 + 5*q*t^4 + 
     16*q^3*t^4 + q^3*t^5 + 5*q^5*t^5 + q^7*t^6);
ThreeStrandPro3[2, {}, 7] :=
    (302/q^8 + 414/q^6 + 1/(q^36*t^14) + 1/(q^34*t^14) + 7/(q^34*t^13) + 
     21/(q^32*t^12) + 7/(q^30*t^12) + 56/(q^30*t^11) + 21/(q^28*t^11) + 
     112/(q^28*t^10) + 56/(q^26*t^10) + 196/(q^26*t^9) + 112/(q^24*t^9) + 
     301/(q^24*t^8) + 196/(q^22*t^8) + 414/(q^22*t^7) + 301/(q^20*t^7) + 
     517/(q^20*t^6) + 414/(q^18*t^6) + 589/(q^18*t^5) + 517/(q^16*t^5) + 
     615/(q^16*t^4) + 589/(q^14*t^4) + 589/(q^14*t^3) + 615/(q^12*t^3) + 
     517/(q^12*t^2) + 589/(q^10*t^2) + 413/(q^10*t) + 517/(q^8*t) + (195*t)/q^6 + 
     (301*t)/q^4 + (113*t^2)/q^4 + (195*t^2)/q^2 + 113*t^3 + (55*t^3)/q^2 + 
     22*t^4 + 55*q^2*t^4 + 6*q^2*t^5 + 22*q^4*t^5 + q^4*t^6 + 6*q^6*t^6 + q^8*t^7);
ThreeStrandPro3[2, {}, 8] :=
    (963/q^9 + 1335/q^7 + 1/(q^41*t^16) + 1/(q^39*t^16) + 8/(q^39*t^15) + 
     28/(q^37*t^14) + 8/(q^35*t^14) + 84/(q^35*t^13) + 28/(q^33*t^13) + 
     190/(q^33*t^12) + 84/(q^31*t^12) + 370/(q^31*t^11) + 190/(q^29*t^11) + 
     630/(q^29*t^10) + 370/(q^27*t^10) + 962/(q^27*t^9) + 630/(q^25*t^9) + 
     1333/(q^25*t^8) + 962/(q^23*t^8) + 1691/(q^23*t^7) + 1333/(q^21*t^7) + 
     1977/(q^21*t^6) + 1691/(q^19*t^6) + 2135/(q^19*t^5) + 1977/(q^17*t^5) + 
     2135/(q^17*t^4) + 2135/(q^15*t^4) + 1977/(q^15*t^3) + 2135/(q^13*t^3) + 
     1691/(q^13*t^2) + 1977/(q^11*t^2) + 1332/(q^11*t) + 1691/(q^9*t) + 
     (631*t)/q^7 + (960*t)/q^5 + (369*t^2)/q^5 + (631*t^2)/q^3 + (191*t^3)/q^3 + 
     (369*t^3)/q + (83*t^4)/q + 191*q*t^4 + 29*q*t^5 + 83*q^3*t^5 + 7*q^3*t^6 + 
     29*q^5*t^6 + q^5*t^7 + 7*q^7*t^7 + q^9*t^8);
ThreeStrandPro3[2, {}, 9] :=
    (3100/q^10 + 4315/q^8 + 1/(q^46*t^18) + 1/(q^44*t^18) + 9/(q^44*t^17) + 
     36/(q^42*t^16) + 9/(q^40*t^16) + 120/(q^40*t^15) + 36/(q^38*t^15) + 
     303/(q^38*t^14) + 120/(q^36*t^14) + 651/(q^36*t^13) + 303/(q^34*t^13) + 
     1218/(q^34*t^12) + 651/(q^32*t^12) + 2040/(q^32*t^11) + 1218/(q^30*t^11) + 
     3099/(q^30*t^10) + 2040/(q^28*t^10) + 4315/(q^28*t^9) + 3099/(q^26*t^9) + 
     5549/(q^26*t^8) + 4315/(q^24*t^8) + 6619/(q^24*t^7) + 5549/(q^22*t^7) + 
     7349/(q^22*t^6) + 6619/(q^20*t^6) + 7609/(q^20*t^5) + 7349/(q^18*t^5) + 
     7349/(q^18*t^4) + 7609/(q^16*t^4) + 6619/(q^16*t^3) + 7349/(q^14*t^3) + 
     5549/(q^14*t^2) + 6619/(q^12*t^2) + 4314/(q^12*t) + 5549/(q^10*t) + 
     (2039*t)/q^8 + (3099*t)/q^6 + (1219*t^2)/q^6 + (2039*t^2)/q^4 + 
     (650*t^3)/q^4 + (1219*t^3)/q^2 + 650*t^4 + (304*t^4)/q^2 + 119*t^5 + 
     304*q^2*t^5 + 37*q^2*t^6 + 119*q^4*t^6 + 8*q^4*t^7 + 37*q^6*t^7 + q^6*t^8 + 
     8*q^8*t^8 + q^10*t^9);
ThreeStrandPro3[n_, insert_, aa_] := ThreeStrandPro3[n, insert, aa] = 
    Module[{i, j},
	   Kh[PD[BR[3, Flatten[{{1,-1},{2,-2},
				insert,
				Table[{Table[-1, {j, 1, n}], 2}, {i, 1, aa}]}]]]
	      ,Program -> "JavaKh-v2",JavaOptions -> "-Xmx6g"][q,t]];
ThreeStrandPro5[n_, insert_, aa_] := ThreeStrandPro5[n, insert, aa] =
    Module[{i, j},
	   Kh[PD[BR[3, Flatten[{{1,-1},{2,-2},
				insert,
				Table[{Table[1, {j, 1, n}], 2, 2}, {i, 1, aa}]}]]]
	      ,Program -> "JavaKh-v2",JavaOptions -> "-Xmx6g"][q,t]];
ThreeStrandPro6[n1_, n2_, insert_, aa_] := ThreeStrandPro6[n1, n2, insert, aa] =
    Module[{i, j},
	   Kh[PD[BR[3, Flatten[{{1,-1},{2,-2},
				insert,
				Table[{Table[Sign[n1], {j, 1, Abs[n1]}],
				       2,
				       Table[Sign[n2], {j, 1, Abs[n2]}],
				       2},
				      {i, 1, aa}]}]]]
	      ,Program -> "JavaKh-v2",JavaOptions -> "-Xmx6g"][q,t]];
ThreeStrandPro7[n1_, n2_, n3_, insert_, aa_] := ThreeStrandPro6[n1, n2, n3, insert, aa] =
    Module[{i, j},
	   Kh[PD[BR[3, Flatten[{{1,-1},{2,-2},
				insert,
				Table[{Table[Sign[n1], {j, 1, Abs[n1]}],
				       2,
				       Table[Sign[n2], {j, 1, Abs[n2]}],
				       2,
				       Table[Sign[n3], {j, 1, Abs[n3]}],
				       2},
				      {i, 1, aa}]}]]]
	      ,Program -> "JavaKh-v2",JavaOptions -> "-Xmx6g"][q,t]];
ThreeStrandPro4[n_, insert_, aa_] := ThreeStrandPro4[n, insert, aa] = 
    Module[{i, j},
	   Kh[PD[BR[3, Flatten[{{1,-1},{2,-2},
				insert,
				Table[{Table[-1, {j, 1, n}], 2, 2}, {i, 1, aa}]}]]]
	      ,Program -> "JavaKh-v2",JavaOptions -> "-Xmx6g"][q,t]];
ThreeStrandPro3[2, {}, 10] :=
    (10043/q^11 + 14043/q^9 + 1/(q^51*t^20) + 1/(q^49*t^20) + 
     10/(q^49*t^19) + 45/(q^47*t^18) + 10/(q^45*t^18) + 165/(q^45*t^17) + 
     45/(q^43*t^17) + 460/(q^43*t^16) + 165/(q^41*t^16) + 1082/(q^41*t^15) + 
     460/(q^39*t^15) + 2208/(q^39*t^14) + 1082/(q^37*t^14) + 4022/(q^37*t^13) + 
     2208/(q^35*t^13) + 6638/(q^35*t^12) + 4022/(q^33*t^12) + 10042/(q^33*t^11) + 
     6638/(q^31*t^11) + 14041/(q^31*t^10) + 10042/(q^29*t^10) + 
     18249/(q^29*t^9) + 14041/(q^27*t^9) + 22141/(q^27*t^8) + 18249/(q^25*t^8) + 
     25149/(q^25*t^7) + 22141/(q^23*t^7) + 26791/(q^23*t^6) + 25149/(q^21*t^6) + 
     26791/(q^21*t^5) + 26791/(q^19*t^5) + 25149/(q^19*t^4) + 26791/(q^17*t^4) + 
     22141/(q^17*t^3) + 25149/(q^15*t^3) + 18249/(q^15*t^2) + 22141/(q^13*t^2) + 
     14040/(q^13*t) + 18249/(q^11*t) + (6639*t)/q^9 + (10040*t)/q^7 + 
     (4021*t^2)/q^7 + (6639*t^2)/q^5 + (2209*t^3)/q^5 + (4021*t^3)/q^3 + 
     (1081*t^4)/q^3 + (2209*t^4)/q + (461*t^5)/q + 1081*q*t^5 + 164*q*t^6 + 
     461*q^3*t^6 + 46*q^3*t^7 + 164*q^5*t^7 + 9*q^5*t^8 + 46*q^7*t^8 + q^7*t^9 + 
     9*q^9*t^9 + q^11*t^10);
ThreeStrandPro5[1, {}, 1] :=
    1 + q^2 + q^4*t^2 + q^6*t^2;
ThreeStrandPro5[1, {}, 2] :=
    q^3 + q^5 + q^7*t^2 + q^11*t^3 + q^9*t^4 + 3*q^11*t^4 + 2*q^13*t^4;
ThreeStrandPro5[1, {}, 3] :=
    (q^6 + q^8 + q^10*t^2 + q^14*t^3 + 
     q^12*t^4 + q^14*t^4 + q^16*t^5 + q^18*t^5 + q^16*t^6 + q^18*t^6);
ThreeStrandPro5[1, {}, 4] :=
    (q^9 + q^11 + q^13*t^2 + q^17*t^3 + 
     q^15*t^4 + q^17*t^4 + q^19*t^5 + q^21*t^5 + q^19*t^6 + q^23*t^7 + q^21*t^8 + 
     3*q^23*t^8 + 2*q^25*t^8);
ThreeStrandPro5[1, {}, 5] :=
    (q^12 + q^14 + q^16*t^2 + q^20*t^3 + 
     q^18*t^4 + q^20*t^4 + q^22*t^5 + q^24*t^5 + q^22*t^6 + q^26*t^7 + q^24*t^8 + 
     q^26*t^8 + q^28*t^9 + q^30*t^9 + q^28*t^10 + q^30*t^10);
ThreeStrandPro5[1, {}, 6] :=
    (q^15 + q^17 + q^19*t^2 + q^23*t^3 + 
     q^21*t^4 + q^23*t^4 + q^25*t^5 + q^27*t^5 + q^25*t^6 + q^29*t^7 + q^27*t^8 + 
     q^29*t^8 + q^31*t^9 + q^33*t^9 + q^31*t^10 + q^35*t^11 + q^33*t^12 + 
     3*q^35*t^12 + 2*q^37*t^12);
ThreeStrandPro5[1, {}, 7] :=
    (q^18 + q^20 + q^22*t^2 + q^26*t^3 + 
     q^24*t^4 + q^26*t^4 + q^28*t^5 + q^30*t^5 + q^28*t^6 + q^32*t^7 + q^30*t^8 + 
     q^32*t^8 + q^34*t^9 + q^36*t^9 + q^34*t^10 + q^38*t^11 + q^36*t^12 + 
     q^38*t^12 + q^40*t^13 + q^42*t^13 + q^40*t^14 + q^42*t^14);
ThreeStrandPro5[1, {}, 8] :=
    (q^21 + q^23 + q^25*t^2 + q^29*t^3 + 
     q^27*t^4 + q^29*t^4 + q^31*t^5 + q^33*t^5 + q^31*t^6 + q^35*t^7 + q^33*t^8 + 
     q^35*t^8 + q^37*t^9 + q^39*t^9 + q^37*t^10 + q^41*t^11 + q^39*t^12 + 
     q^41*t^12 + q^43*t^13 + q^45*t^13 + q^43*t^14 + q^47*t^15 + q^45*t^16 + 
     3*q^47*t^16 + 2*q^49*t^16);
ThreeStrandPro5[1, {}, 9] :=
    (q^24 + q^26 + q^28*t^2 + q^32*t^3 + 
     q^30*t^4 + q^32*t^4 + q^34*t^5 + q^36*t^5 + q^34*t^6 + q^38*t^7 + q^36*t^8 + 
     q^38*t^8 + q^40*t^9 + q^42*t^9 + q^40*t^10 + q^44*t^11 + q^42*t^12 + 
     q^44*t^12 + q^46*t^13 + q^48*t^13 + q^46*t^14 + q^50*t^15 + q^48*t^16 + 
     q^50*t^16 + q^52*t^17 + q^54*t^17 + q^52*t^18 + q^54*t^18);
ThreeStrandPro5[1, {}, 10] :=
    (q^27 + q^29 + q^31*t^2 + q^35*t^3 + 
     q^33*t^4 + q^35*t^4 + q^37*t^5 + q^39*t^5 + q^37*t^6 + q^41*t^7 + q^39*t^8 + 
     q^41*t^8 + q^43*t^9 + q^45*t^9 + q^43*t^10 + q^47*t^11 + q^45*t^12 + 
     q^47*t^12 + q^49*t^13 + q^51*t^13 + q^49*t^14 + q^53*t^15 + q^51*t^16 + 
     q^53*t^16 + q^55*t^17 + q^57*t^17 + q^55*t^18 + q^59*t^19 + q^57*t^20 + 
     3*q^59*t^20 + 2*q^61*t^20);
ThreeStrandPro5[1, {}, 11] :=
    (q^30 + q^32 + q^34*t^2 + q^38*t^3 + 
     q^36*t^4 + q^38*t^4 + q^40*t^5 + q^42*t^5 + q^40*t^6 + q^44*t^7 + q^42*t^8 + 
     q^44*t^8 + q^46*t^9 + q^48*t^9 + q^46*t^10 + q^50*t^11 + q^48*t^12 + 
     q^50*t^12 + q^52*t^13 + q^54*t^13 + q^52*t^14 + q^56*t^15 + q^54*t^16 + 
     q^56*t^16 + q^58*t^17 + q^60*t^17 + q^58*t^18 + q^62*t^19 + q^60*t^20 + 
     q^62*t^20 + q^64*t^21 + q^66*t^21 + q^64*t^22 + q^66*t^22);
ThreeStrandPro5[1, {}, 12] :=
    (q^33 + q^35 + q^37*t^2 + q^41*t^3 + 
     q^39*t^4 + q^41*t^4 + q^43*t^5 + q^45*t^5 + q^43*t^6 + q^47*t^7 + q^45*t^8 + 
     q^47*t^8 + q^49*t^9 + q^51*t^9 + q^49*t^10 + q^53*t^11 + q^51*t^12 + 
     q^53*t^12 + q^55*t^13 + q^57*t^13 + q^55*t^14 + q^59*t^15 + q^57*t^16 + 
     q^59*t^16 + q^61*t^17 + q^63*t^17 + q^61*t^18 + q^65*t^19 + q^63*t^20 + 
     q^65*t^20 + q^67*t^21 + q^69*t^21 + q^67*t^22 + q^71*t^23 + q^69*t^24 + 
     3*q^71*t^24 + 2*q^73*t^24);
ThreeStrandPro5[1, {}, 13] :=
    (q^36 + q^38 + q^40*t^2 + q^44*t^3 + 
     q^42*t^4 + q^44*t^4 + q^46*t^5 + q^48*t^5 + q^46*t^6 + q^50*t^7 + q^48*t^8 + 
     q^50*t^8 + q^52*t^9 + q^54*t^9 + q^52*t^10 + q^56*t^11 + q^54*t^12 + 
     q^56*t^12 + q^58*t^13 + q^60*t^13 + q^58*t^14 + q^62*t^15 + q^60*t^16 + 
     q^62*t^16 + q^64*t^17 + q^66*t^17 + q^64*t^18 + q^68*t^19 + q^66*t^20 + 
     q^68*t^20 + q^70*t^21 + q^72*t^21 + q^70*t^22 + q^74*t^23 + q^72*t^24 + 
     q^74*t^24 + q^76*t^25 + q^78*t^25 + q^76*t^26 + q^78*t^26);
ThreeStrandPro5[1, {}, 14] :=
    (q^39 + q^41 + q^43*t^2 + q^47*t^3 + 
     q^45*t^4 + q^47*t^4 + q^49*t^5 + q^51*t^5 + q^49*t^6 + q^53*t^7 + q^51*t^8 + 
     q^53*t^8 + q^55*t^9 + q^57*t^9 + q^55*t^10 + q^59*t^11 + q^57*t^12 + 
     q^59*t^12 + q^61*t^13 + q^63*t^13 + q^61*t^14 + q^65*t^15 + q^63*t^16 + 
     q^65*t^16 + q^67*t^17 + q^69*t^17 + q^67*t^18 + q^71*t^19 + q^69*t^20 + 
     q^71*t^20 + q^73*t^21 + q^75*t^21 + q^73*t^22 + q^77*t^23 + q^75*t^24 + 
     q^77*t^24 + q^79*t^25 + q^81*t^25 + q^79*t^26 + q^83*t^27 + q^81*t^28 + 
     3*q^83*t^28 + 2*q^85*t^28);
PrecalculateFname[fnameSuffix_] :=
    ("/home/popolit/quicklisp/local-projects/cl-vknots/khovanov-precomp-"
     <> fnameSuffix <> ".m");
(* ### vv Snippet to precalculate Khovanov polynomial for certain knot families ### *)
PrecalculateAndDumpKhovanovs[fnameSuffix_, family_, from_, upto_] :=
    Module[{fd = OpenWrite[PrecalculateFname[fnameSuffix], FormatType -> InputForm]},
	   Module[{i},
		  For[i = from, i <= upto, i ++,
		      Module[{it = family[i]},
			     (* ### ^^ it is important that we first do time-intensive computation and only then check the time ### *)
			     If[$Failed[q,t] === it,
				CompoundExpression[
				    WriteString[fd, ("(* ### The calculation of Khovanov polynomial for "
							 <> ToString[i] <> " had failed. ### *)\n")]],
				CompoundExpression[
				    WriteString[fd, "(* ### " <> DateString[] <> " ### *)\n"];
				    WriteString[fd, ("poly[" <> ToString[i, FormatType -> InputForm] <> "] = ("
						     <> ToString[it, FormatType -> InputForm] <> ");\n")]]]]]];
	   Close[fd]];
CustomFnameSuffix[once_, repeat_] :=
    StringJoin["pro-custom-", StringRiffle[repeat, "-"], "-once-", StringRiffle[once, "-"], "-"];
PrecalculateAndDumpKhovanovsCustom[once_, repeat_, from_, upto_] :=
    Module[{fnameSuffix = CustomFnameSuffix[once, repeat]},
	   PrecalculateAndDumpKhovanovs[fnameSuffix, ThreeStrandProCustom[once, repeat, #] &, from, upto]];
AutoCheckKhovanovsCustom[once_, repeat_, eigs_] :=
    Module[{},
	   PrecalculateAndDumpKhovanovsCustom[once, repeat, 1, 20];
	   CheckPolyEigenvalues[PrecalculateFname[CustomFnameSuffix[once, repeat]], eigs]];
CheckPolyEigenvalues[fname_, eigs_] :=
    Module[{eigsExpr = Sort[Simplify[(TryFindPolyEigenvalues[fname, Length[eigs] + 1, theDelta, theExtra]
				      /. {q -> Pi, t -> E})]],
	    eigsTheor = Sort[Simplify[eigs /. {q -> Pi, t -> E}]]},
	   Module[{it = Simplify[eigsExpr - eigsTheor]},
		  (* Print["it: ", it]; *)
		  If[Table[0, {i, 1, Length[eigsTheor]}] === it,
		     True,
		     Module[{},
			    Print[eigsExpr];
			    Print[eigsTheor];
			    False]]]];
TryFindPolyEigenvalues[fname_, order_, delta_, extra_] :=
    Module[{},
	   ClearAll[poly];
	   Get[fname]; (* ### << This import injects a bunch of "poly" definitions into the scope ### *)
	   Block[{theOrder = order,
		  theDelta = delta},
		 (* Print["delta, extra: ", theDelta, extra]; *)
		 Module[{eqns = (Map[Function[{n},
					      0 == (Plus @@
						    Map[poly[n + #] * CC[#] &,
							Range[0, theOrder-1]])],
				     Range[theDelta, theDelta + theOrder+extra]]
				 /. {CC[theOrder-1] -> 1})},
			Module[{ans = Solve[eqns, Map[CC[#] &, Range[0, theOrder - 2]]]},
			       If[ans === {},
				  Module[{}, Print["Failed to find recursion coefficients"]; $Failed],
				  Module[{ans1 = Simplify[ans[[1]]]},
					 (* ### ^^ equations are linear, so we have only one solution ### *)
					 Module[{exprEigs = Sort[Map[#[[1, 2]] &,
								     Solve[0 == Sum[CC[i] x^i, {i, 0, theOrder-1}]
									   /. {CC[theOrder-1] -> 1} /. ans1,
									   x]]]},
						exprEigs]]]]]]];
SpecialOrthogonalMatrix[1] :=
    {{1}};
SOMauxQSmall[n_] := SOMauxQSmall[n] =
    Module[{i,j,
	    prev = SpecialOrthogonalMatrix[n-1]},
	   Table[If[And[i < n, j < n],
		    prev[[i,j]],
		    If[i == j,
		       1,
		       0]],
		 {i, 1, n},
		 {j, 1, n}]];
SOMauxASmall[i_, j_, n_] :=
    Module[{res = IdentityMatrix[n]}, (* ### << Start with the trivial template for the elementary rotation matrix ### *)
	   (* ### vv Populate non-trivial entries ### *)
	   res[[i,i]] = c[i,j];
	   res[[j,j]] = c[i,j];
	   res[[i,j]] = s[i,j];
	   res[[j,i]] = -s[i,j];
	   res];
SOMauxA[n_] :=
    Module[{i},
	   Dot @@ Table[SOMauxASmall[n-i, n, n],
			{i, 1, n-1}]];
SpecialOrthogonalMatrix[n_] := SpecialOrthogonalMatrix[n] =
    (* ### ^^ This function gives a parametrization of generic SO(n) element in terms of generalized Euler angles ### *)
    (* ### ^^ c[i,j] = \cos(\phi_{i,j}), s[i,j] = \sin(\phi_{i,j}) ### *)
    (* ### ^^ The recursion is obtained in Raffenetti, Ruedenberg (1970), I'm not quite sure that for the first time ### *)
    SOMauxA[n] . SOMauxQSmall[n];
CheckReps[n_] :=
    Block[{checkRes = {}},
	  Scan[CheckRepForChoiceOfPowers[#[[1]], #[[2]]] &,
	       PrepareRepsPowers[n]];
	  checkRes];
PrepareRepsPowers[n_] :=
    Tuples[{Select[Compositions[n, 4], And[#[[1]] > 0,
					   #[[2]] + #[[3]] > 0] &],
	    Compositions[n, 5]}];
SimplifySines[expr_, i_, j_] :=
    Simplify[Plus @@ Map[#[[2]] * If[EvenQ[#[[1,1]]],
				     (1 - c[i,j]^2)^(#[[1,1]]/2),
				     (1 - c[i,j]^2)^((#[[1,1]]-1)/2) s[i,j]] &,
			 CoefficientRules[expr, s[i,j]]]];
SimplifyCosines[expr_, i_, j_] :=
    Simplify[Plus @@ Map[#[[2]] * If[EvenQ[#[[1,1]]],
				     cc[i,j]^(#[[1,1]]/2),
				     cc[i,j]^((#[[1,1]]-1)/2) c[i,j]] &,
			 CoefficientRules[expr, c[i,j]]]];
SimplifyAllSines[expr_, n_] :=
    Module[{i,j, myExpr = expr},
	   For[i = 1, i < n, i ++,
	       For[j = i + 1, j <= n, j ++,
		   myExpr = SimplifySines[myExpr, i, j]]];
	   myExpr];
SimplifyAllCosines[expr_, n_] :=
    Module[{i,j, myExpr = expr},
	   For[i = 1, i < n, i ++,
	       For[j = i + 1, j <= n, j ++,
		   myExpr = SimplifyCosines[myExpr, i, j]]];
	   myExpr];
CheckRepForChoiceOfPowers[powersR1_, powersR1R2_] :=
    Module[{i,
	    r1EigPool = {q, t q^3, -t q^3, 0},
	    r1r2EigPool = {q^2, t^(4/3) q^4, t^(4/3) q^4 E^(2 Pi I 1/3), t^(4/3) q^4 E^(2 Pi I 2/3), 0}},
	   Module[{r1Eigs = Join @@ Map[Table[r1EigPool[[#]], {i, 1, powersR1[[#]]}] &,
					Range[1,4]],
		   r1r2Eigs = Join @@ Map[Table[r1r2EigPool[[#]], {i, 1, powersR1R2[[#]]}] &,
					  Range[1,5]],
		   n = Plus @@ powersR1}, (* ### << I knot it's rather dumb to reverse engineer that instead of pass, but hey ### *)
		  (* ### Alright, not that we have eigenvalues, we construct a R1 . R2 matrix and check ### *)
		  (* ### Whether traces of powers are the same ### *)
		  (* AppendTo[checkRes, {r1Eigs, r1r2Eigs}]; *)
		  Module[{r1r2 = (DiagonalMatrix[r1Eigs] . Transpose[SpecialOrthogonalMatrix[n]]
				  . DiagonalMatrix[r1Eigs] . SpecialOrthogonalMatrix[n])},
			 (* AppendTo[checkRes, {r1r2, n}]; *)
			 Module[{eqns = Map[(Plus @@ (r1r2Eigs^#))
					    == SimplifyAllCosines[SimplifyAllSines[Tr[MatrixPower[r1r2, #]], n], n] &,
					    Range[1, n]],
				 indets = Module[{i,j}, Flatten[Table[{cc[i,j], c[i,j]}, {i,1,n}, {j, i+1, n}]]]},
				AppendTo[checkRes, {eqns, indets}];
				Appended]]]];

		
				Module[{ans = Solve[eqns, indets]},
				       (* ### vv Something cool is about to happen here ### *)
				       If[{} =!= ans,
					  Module[{},
						 AppendTo[checkRes, {powersR1, powersR1R2, ans}];
						 Appended]]]]]]];


theMaxBound = 10;
ans = Module[{res = {}, rootPower = 5},
	     For[BB = 0, BB <= theMaxBound, BB ++,
		 For[CC = 0, CC <= theMaxBound, CC ++,
		     For[DD = 0, DD <= theMaxBound, DD ++,
			 For[beta = 0, beta <= theMaxBound, beta ++,
			     For[gamma = 0, gamma <= theMaxBound, gamma ++,
				 If[IntegerQ[Simplify[4/3/rootPower BB
						      + (4/3/rootPower + 1/3) CC
						      + (4/3/rootPower + 2/3) DD
						      - 2/rootPower beta
						      - (1/rootPower + 1/2) 2 gamma]],
				    AppendTo[res, {BB, CC, DD, beta, gamma}]]]]]]];
	     res];
ans1 = Module[{res1 = {}},
	      Module[{BB, CC, DD, AA, alpha, beta, gamma},
		     Scan[Function[{choice},
				   {BB, CC, DD, beta, gamma} = choice; (* ### << we first destructure ### *)
				   (* ### vv We assume that AA is zero, because that corresponds to symmetric representation solution ### *)
				   (* ### vv which we already know ### *)
				   alpha = BB + CC + DD - beta - gamma;
				   Module[{altAlpha = Simplify[2 (BB + CC + DD) - 3 (beta + gamma)]},
					  (* Print[alpha, " ", altAlpha]; *)
					  If[And[alpha >= 0,
						 alpha === altAlpha],
					     AppendTo[res1, {BB, CC, DD, alpha, beta, gamma}]]]],
			  ans]];
	      res1];


DeleteDuplicates[Map[#[[4;;]] &, Select[ans1, #[[1]] + #[[2]] + #[[3]] == 10 &]]]

Out[13]= {{5, 0, 5}, {5, 1, 4}, {5, 2, 3}, {5, 3, 2}, {5, 4, 1}, {5, 5, 0}}

Out[11]= {{3, 0, 3}, {3, 1, 2}, {3, 2, 1}, {3, 3, 0}}




Transpose[SpecialOrthogonalMatrix[4]]
			    
Timing[Block[{n = 3},
	     tmp = PrepareRepsPowers[n]]];

Length[tmp]

tmp[[1]]

Out[39]= {{1, 0, 1, 1}, {0, 0, 0, 0, 3}}

eqnsNindets = Block[{checkRes = {}},
		    {CheckRepForChoiceOfPowers@@tmp[[1]],
		     checkRes[[1]]}];

eqnsNindets

Solve[eqnsNindets[[2,1,1]], cc[1,2]]

Simplify[eqnsNindets[[2,1]] /. Solve[eqnsNindets[[2,1,1]], cc[1,2]][[1]]]

Out[38]= {True, 2 q t cc[2, 3] == q t, True}

Out[34]= {True, q t == 0}

             4            3   2
Out[28]= {2 q  t == (q + q  t)  cc[1, 2], 
 
      4     4  2             3   2                  2   4         2
>    q  (2 q  t  - 4 t (q + q  t)  cc[1, 2] + (1 + q  t)  cc[1, 2] ) == 0}

PrepareRepsPowers[2]

tmp

Out[9]= {{2, 2}, {2, 5}, {4, 2}, {4, 5}}


Block[{n = 5},
      Simplify[SpecialOrthogonalMatrix[n] . Transpose[SpecialOrthogonalMatrix[n]]
	       /. {s[i_,j_] :> Sqrt[1 - c[i,j]^2]}]]

   


Block[{theDelta = 5,
       theExtra = 5},
      CheckPolyEigenvalues[PrecalculateFname[CustomFnameSuffix[{1}, {1,2}]],
			   {q^2, t^(4/3) q^4,
			    Exp[2 Pi I/3] t^(4/3) q^4,
			    Exp[4 Pi I/3] t^(4/3) q^4}]]




Block[{n = 8,
       theDelta = 5,
       theExtra = 5},
      Module[{res = {}},
	     Scan[Function[{once},
			   If[Not[AutoCheckKhovanovsCustom[once, {1,2},
							   {q^2, t^(4/3) q^4,
							    Exp[2 Pi I/3] t^(4/3) q^4,
							    Exp[4 Pi I/3] t^(4/3) q^4}]],
			      AppendTo[res, once]]],
		  Tuples[{1,2}, n]];
	     res]]

                                                      

CustomFnameSuffix[{}, {2}]

		   
PrecalculateAndDumpKhovanovs["pro2-0-wind-1-2-1", ThreeStrandPro2[0, {1,2,1}, #] &, 1, 20];

(* ### v Recursion for R1^(-2) R2 ### *)
rec112 = {CC[5] -> E^11*Pi^3*CC[0],
	  CC[4] -> -(E^6*Pi*(2 + E^2*Pi + E^4*Pi^2 + E^6*Pi^3)*CC[0]),
	  CC[3] -> ((E + E^3*Pi + E^5*Pi^2 + 2*E^7*Pi^3 - E^9*Pi^4)*CC[0])/Pi,
	  CC[2] -> E^2*(-1 + 2*E^2*Pi + E^4*Pi^2 + E^6*Pi^3 + E^8*Pi^4)*CC[0],
	  CC[1] -> -(((1 + E^2*Pi + E^4*Pi^2 + 2*E^6*Pi^3)*CC[0])/(E*Pi))} /. {E -> q, Pi -> t};
Solve[0 == Sum[CC[i] x^i, {i, 0, 6-1}] /. rec112,
      x] // InputForm

         
eigsm112 = 
{{x -> -q^(-1)}, {x -> q^(-1)}, {x -> 1/(q^5*t^2)}, 
 {x -> (1 + q^2*t + q^4*t^2 + q^6*t^3 - 
     Sqrt[-4*q^6*t^3 + (1 + q^2*t + q^4*t^2 + q^6*t^3)^2])/(2*q^5*t^2)}, 
 {x -> (1 + q^2*t + q^4*t^2 + q^6*t^3 + 
     Sqrt[-4*q^6*t^3 + (1 + q^2*t + q^4*t^2 + q^6*t^3)^2])/(2*q^5*t^2)}};




(* ### vv Here we check the derivation of the evolution method ### *)
JJ = ({1, (-q^2)}^b . {{(q^2 + 1 + q^(-2))/(q + q^(-1)), 1/(q + q^(-1))},
		       {- (q^2 + 1 + q^(-2))/(q + q^(-1)), (q^2 + 1 + q^(-2))/(q + q^(-1))}} . {q, (-q^3)}^(-a));
Block[{sign = a - 2},
      Expand[FullSimplify[(((JJ q^sign - (q + q^(-1)) (1 + 1/2(1 + (-1)^a) (-q^2)^(b-a)))/(q^(-1) - q^3) /. {q -> I Sqrt[t] q})
			   (q^(-1) + t q^3) + (q + q^(-1)) (1 + 1/2 (1 + (-1)^a) (t q^2)^(b-a)))
			  / q^sign /. {q -> Pi, t -> E}]]]

theOrder = 6;
eqns = Map[Function[{n},
		    0 == (Plus @@ Map[Function[{delta}, FirstNonToricKhovanov[n + delta] CC[delta]], Range[1,theOrder]])],
	   Range[1, theOrder + 1]];

ans = Solve[eqns (* /. {t -> -1} *),
	    Map[CC[#] &, Range[1,theOrder]]];
FullSimplify[ans]


Block[{k = 4},
      With[{extra = (t q^3 (t q^2 + 1)^(3 k + 1)
		     + q^(-1) (t q^2 + 1)^(3 k + 1)
		     + t^(-2) q^(-3) (t q^2 + 1)^(3 k + 2)
		    )},
	   Expand[(Normal[Series[FirstNonToricKhovanov[2 + 3 k]
				 - (extra /. {q -> 1/q, t -> 1/t})
				 - extra,
				 {q, 0, 0}]] /. {q -> 1/q, t -> 1/t})
		 ]]]


                                                                                        
Block[{aa = 2, bb = 3},
      Block[{pd = PlanarDiagram[BraidSpec[Braid[2, a, {2, 1}, {4, 3}], Braid[2, b, {3, 1}, {4, 2}]],
				OriChoice[II[a, 0] -> 1, II[a, 1] -> 1, II[b, 0] -> 1, II[b, 1] -> -1],
				{aa, bb}]},
	    Module[{kh = Kh[ExtendedPDToUsual[PlanarDiagramToAdvancedStructures[pd]]][q,t]},
		   Print["kh: ", kh]]]];

Block[{n = 7},
      Expand[FullSimplify[FirstNonToricKhovanov[n]
			  - Sum[(t q^2)^i,{i,1,n}] q
			  - Sum[(t q^2)^(-i),{i,1,n}] q^(-1)]]]


Block[{n = 4},
      ThreeStrandKhovanov[1 + 3 n]]

Block[{n = 7},
      Expand[ThreeStrandKhovanov[n]
	     - q^(2 (n-2)) (q + q^3 + t^2 q^5 + t^3 q^9)]]

Block[{n = 4},
      FourStrandKhovanov[1 + 4 n]]

ansPP13 = Block[{extraPoints = 2},
		With[{aSeries = 1 + k},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
							       TwoStrandKhovanov[aSeries /. {k -> k1}]],
						      Join[{aSeries}, {q, t q^3, (- t q^3)}]]]];
FullSimplify[ansPP13]

Block[{n = 1},
      Simplify[(AA[1] q^n + AA[2] (t q^3)^n + AA[3] (-t q^3)^n) /. ansPP13]]

FullSimplify[ansPP13]

ansPP13 = Block[{extraPoints = 2},
		With[{aSeries = 1 + k},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
							       ThreeStrandKhovanov[aSeries /. {k -> k1}]],
						      Join[{aSeries}, {q^2,
								       t^(4/3) q^4,
								       t^(4/3) q^4 Exp[2 Pi I/3],
								       t^(4/3) q^4 Exp[2 Pi I 2/3]}]]]];

TheExpr[n_] := ((AA[2] (t^(4/3) q^4)^n
		 + AA[3] (t^(4/3) q^4 Exp[2 Pi I/3])^n
		 + AA[4] (t^(4/3) q^4 Exp[2 Pi I 2/3])^n) /. ansPP13);
ExprMatPower[n_] := 3 TheExpr[n-1]/TheExpr[-1]/(t^(4/3) q^4)^n;
TheorMatPower[n_] := Tr[Table[AA[i,j], {i, 1, 3}, {j, 1, 3}]
			. MatrixPower[{{0, 1, 0}, {0, 0, 1}, {1, 0, 0}}, n]];

eqns = Map[TheorMatPower[#] - ExprMatPower[#] == 0 &, Range[0, 17]];

ans = FullSimplify[Solve[eqns,
			 Flatten[Table[AA[i,j], {i, 1, 3}, {j, 1, 3}]]]][[1]];

FullSimplify[(TheorMatPower[1] /. ans) /. {AA[1,1] -> 1, AA[2,2] -> 1, AA[1,2] -> 0, AA[2,3] -> 0, AA[1,3] -> 0, AA[2,1] -> 0}]

ans (* /. {AA[1,1] -> 1, AA[2,2] -> 1, AA[1,2] -> 0, AA[2,3] -> 0, AA[1,3] -> 0, AA[2,1] -> 0} *)

Apart[AA[3,2] t^(1/3) /. ans /. {AA[1,3] -> 0, AA[2,1] -> 0}, t]

FullSimplify[TheorMatPower[3] /. ans]

Out[73]= 3

                2       2   2
         3 + 3 q  (1 + q ) t
Out[72]= ---------------------
          2/3       2    4  2
         t    (1 + q  + q  t )

                 2                   2       2         4      2
         -6 + 3 q  (-2 + t (1 + t + q  (1 + t  (t + 2 q  t + q  (1 + 3 t)))))
Out[71]= --------------------------------------------------------------------
                            4/3       4          2    4  2
                           t    (1 + q  t) (1 + q  + q  t )

Out[70]= 3

FullSimplify[ExprMatPower[0]]

FullSimplify[ExprMatPower[2] - ExprMatPower[1]^2]

             8       2         6  4
Out[55]= -((q  (1 + q ) (-1 + q  t ) 
 
                2      8  4    6  2                2     4               3
>        (-4 + t  + 3 q  t  + q  t  (-1 + 4 t + 8 t ) + q  t (4 - t + 5 t ) + 
 
            2                     3              4   2       2    4  2 2
>          q  (-4 + t (4 + 4 t + t )))) / ((1 + q  t)  (1 + q  + q  t ) ))

M = Table[AA[i,j], {i, 1, 3}, {j, 1, 3}];

Tr[MatrixPower[M, 2]]

                 2                                 2
Out[48]= AA[1, 1]  + 2 AA[1, 2] AA[2, 1] + AA[2, 2]  + 2 AA[1, 3] AA[3, 1] + 
 
                                   2
>    2 AA[2, 3] AA[3, 2] + AA[3, 3]

Out[46]= AA[1, 1] + AA[2, 2] + AA[3, 3]


Block[{n = 5},
      FullSimplify[TheExpr[n]/TheExpr[-1]]]

         
          24  8
Out[43]= q   t

         
          20  6    22       2   8
         q   t  + q   (1 + q ) t
Out[42]= ------------------------
                   2    4  2
              1 + q  + q  t

         
           16  4        2
Out[41]= (q   t  (-2 + q  (-2 + 
 
                        2       2         4      2
>           t (1 + t + q  (1 + t  (t + 2 q  t + q  (1 + 3 t))))))) / 
 
            4          2    4  2
>    ((1 + q  t) (1 + q  + q  t ))

         
          12  4
Out[40]= q   t

         
          8  2    10       2   4
         q  t  + q   (1 + q ) t
Out[39]= -----------------------
                  2    4  2
             1 + q  + q  t

         
Out[38]= 
 
      4        2                   2       2         4      2
     q  (-2 + q  (-2 + t (1 + t + q  (1 + t  (t + 2 q  t + q  (1 + 3 t))))))
>    -----------------------------------------------------------------------
                                 4          2    4  2
                           (1 + q  t) (1 + q  + q  t )

         
Out[37]= 1



ansPP13 = Block[{extraPoints = 2},
		With[{aSeries = 4 + 4 k},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
							       FourStrandKhovanov[aSeries /. {k -> k1}]],
						      Join[{aSeries}, {q^3,
								       t^(6/4) q^5,
								       t^(2) q^6}
							  ]]]];


Block[{aa = -1, bb = 0},
      Expand[Simplify[SecondNonToricKhovanov[aa, bb]]]]



Block[{k = -5},
      Block[{aa = -k, bb = 1+k},
	    Simplify[SecondNonToricKhovanovPrime[aa, bb]]]]


       
Table[Simplify[SecondNonToricKhovanov[aa, bb] - SecondNonToricKhovanovPrime[aa, bb]],
      {aa, -5, 5},
      {bb, -5, 5}]


ansPP11 = Block[{extraPoints = 2},
		With[{aSeries = 2 + k,
		      bSeries = -2 - k},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
							       SecondNonToricKhovanov[aSeries /. {k -> k1},
										      bSeries /. {k -> k2}]],
						      Join[{aSeries}, PosFundEigenvalues[]],
						      Join[{bSeries}, PosFundEigenvalues[]]]]];

(* ### Tool to study a-evolution in isolation ### *)
ansPP11 = Block[{extraPoints = 10},
		With[{aSeries = 0-k,
		      bSeries = 2},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
							       ThirdNonToricKhovanovPrime[aSeries /. {k -> k1},
											  bSeries]],
						      Join[{aSeries}, PosFundEigenvalues[]]]]];

(* ### Tool to study b-evolution in isolation ### *)
ansPP11 = Block[{extraPoints = 2},
		With[{aSeries = -1,
		      bSeries = -k},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k2},
							       ThirdNonToricKhovanovPrime[aSeries,
											  bSeries /. {k -> k2}]],
						      Join[{bSeries}, PosFundEigenvalues[]]]]];

(* ### Tool to study two-parametric evolution ### *)
ans = Block[{extraPoints = 10},
	    With[{aSeries = -2 - k,
		  bSeries = k},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
							       ThirdNonToricKhovanovPrime[aSeries /. {k -> k1},
											  bSeries /. {k -> k2}]],
						      Join[{aSeries}, PosFundEigenvalues[]],
						      Join[{bSeries}, PosFundEigenvalues[]]]]];

Module[{cc},
       For[cc = 10, cc <= 15, cc ++,
	   (* ### Let's find 4 evolutions in all far quadrants ### *)
	   ansUL = Block[{extraPoints = 2},
			 With[{aSeries = -4 - k,
			       bSeries = 4 + k},
			      FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
									ThirdNonToricKhovanovPrime[aSeries /. {k -> k1},
												   bSeries /. {k -> k2},
												   cc]],
							       Join[{aSeries}, PosFundEigenvalues[]],
							       Join[{bSeries}, PosFundEigenvalues[]]]]];
	   ansUR = Block[{extraPoints = 2},
			 With[{aSeries = 4 + k,
			       bSeries = 4 + k},
			      FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
									ThirdNonToricKhovanovPrime[aSeries /. {k -> k1},
												   bSeries /. {k -> k2},
												   cc]],
							       Join[{aSeries}, PosFundEigenvalues[]],
							       Join[{bSeries}, PosFundEigenvalues[]]]]];
	   ansLL = Block[{extraPoints = 2},
			 With[{aSeries = - 4 - k,
			       bSeries = - 4 - k},
			      FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
									ThirdNonToricKhovanovPrime[aSeries /. {k -> k1},
												   bSeries /. {k -> k2},
												   cc]],
							       Join[{aSeries}, PosFundEigenvalues[]],
							       Join[{bSeries}, PosFundEigenvalues[]]]]];
	   ansLR = Block[{extraPoints = 2},
			 With[{aSeries = 4 + k,
			       bSeries = - 4 - k},
			      FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
									ThirdNonToricKhovanovPrime[aSeries /. {k -> k1},
												   bSeries /. {k -> k2},
												   cc]],
							       Join[{aSeries}, PosFundEigenvalues[]],
							       Join[{bSeries}, PosFundEigenvalues[]]]]];
	   TheorKhovanov[aa_, bb_, ans_] :=
	   If[ans === checkFailed,
	      checkFailed,
	      Simplify[PosFundEigenvalues[]^aa
		       . (Table[AA[i,j], {i, 1, 3}, {j, 1, 3}] /. ans)
		       . PosFundEigenvalues[]^bb]];
	   Block[{maxAbs = 10},
		 picc[cc] = Module[{aa, bb},
				   Table[Module[{ulQ = (0 === Simplify[TheorKhovanov[aa, bb, ansUL]
								       - ThirdNonToricKhovanovPrime[aa, bb, cc]]),
						 urQ = (0 === Simplify[TheorKhovanov[aa, bb, ansUR]
								       - ThirdNonToricKhovanovPrime[aa, bb, cc]]),
						 llQ = (0 === Simplify[TheorKhovanov[aa, bb, ansLL]
								       - ThirdNonToricKhovanovPrime[aa, bb, cc]]),
						 lrQ = (0 === Simplify[TheorKhovanov[aa, bb, ansLR]
								       - ThirdNonToricKhovanovPrime[aa, bb, cc]])},
						(* Print["ul, ur, ll, lr: ", ulQ, " ", urQ, " ", llQ, " ", lrQ]; *)
						If[And[ulQ, urQ, llQ, lrQ],
						   "AL",
						   If[And[ulQ, urQ, llQ],
						      "GG",
						      If[And[ulQ, llQ, lrQ],
							 "LL",
							 If[And[ulQ, urQ, lrQ],
							    "TT",
							    If[And[urQ, llQ, lrQ],
							       "dd",
							       If[And[ulQ, llQ],
								  "LE",
								  If[And[urQ, ulQ],
								     "UP",
								     If[And[urQ, lrQ],
									"RI",
									If[And[llQ, lrQ],
									   "LO",
									   If[And[ulQ, lrQ],
									      "YY",
									      If[And[llQ, urQ],
										 "NN",
										 If[ulQ,
										    "UL",
										    If[urQ,
										       "UR",
										       If[llQ,
											  "LL",
											  If[lrQ,
											     "LR",
											     "??"]]]]]]]]]]]]]]]],
					 {bb, maxAbs, -maxAbs, -1},
					 {aa, -maxAbs, maxAbs}]]]]];

(* ### vv Recursion for R1^3 R2 ### *)
Solve[x^4 - q^4 x^3 - t^8 q^24 x + t^8 q^28 == 0, x] // InputForm


(* ### vv 6th order recursion for R1^4 R2 ### *)
Solve[1 + -(1 + q^6 t^4)/q^11/t^4 x + (-1+q^2 t^2)/t^6/q^18 x^2 + (1 + t^4 q^6)/t^10/q^29 x^3 - 1/t^10/q^34 x^4 == 0,
      x]


theOrder = 6;
theDelta = 4;
Block[{k = 1,
       insert = {-1,-1,-1,-1, -1,-2,-2,-2}},
      eqns = Map[Function[{n},
			  0 == (Plus @@
				Map[Function[{delta},
					     Simplify[ThreeStrandPro2[k, insert, n + delta]]
					     * CC[delta]],
				    Range[0, theOrder-1]])],
		 Range[theDelta, theDelta + theOrder+1]]];
ans = Solve[eqns (* /. {t -> -1} *),
	    Map[CC[#] &, Range[1,theOrder]]];
ans1 = FullSimplify[ans];
Solve[0 == Sum[CC[i] x^i, {i, 0, theOrder-1}] /. ans1[[1]],
      x]

theOrder = 6;
theDelta = 1;
Block[{k = 1, nwind = 0},
      eqns = Map[Function[{n},
			  0 == (Plus @@
				Map[Function[{delta},
					     Module[{i},
						    Simplify[ThreeStrandPro5[k,
									     Join @@ Table[{2}, {i, 1, nwind}],
									     n + delta]
							    ]]
					     * CC[delta]],
				    Range[0, theOrder-1]])],
		 Range[theDelta, theDelta + theOrder+1]]];

(* ### vv Answer for recursion for R_1^(-1) R_2 ### *)
ansRecR1m1R2 = {CC[1] -> -(((1 + q^2*t + q^4*t^2)*CC[0])/(q^2*t)), CC[2] -> CC[0], 
		CC[3] -> -CC[0], CC[4] -> (1 + 1/(q^2*t) + q^2*t)*CC[0], CC[5] -> -CC[0]};
Solve[0 == Sum[CC[i] x^i, {i, 0, 5}] /. FullSimplify[ansRecR1m1R2],
      x] // InputForm

{{x -> 1}, {x -> -(-1)^(1/3)}, {x -> (-1)^(2/3)}, 
 {x -> (1 + q^2*t + q^4*t^2 - Sqrt[1 + 2*q^2*t - q^4*t^2 + 2*q^6*t^3 + 
       q^8*t^4])/(2*q^2*t)}, 
 {x -> (1 + q^2*t + q^4*t^2 + Sqrt[1 + 2*q^2*t - q^4*t^2 + 2*q^6*t^3 + 
       q^8*t^4])/(2*q^2*t)}}


TheorKhovanov[0,0,ansUR]

picc[9] // TeXForm

picc[3] = pic;


Block[{aa = -1, bb = -1},
      If[0 === Simplify[TheorKhovanov[aa, bb, ans] - ThirdNonToricKhovanovPrime[aa, bb]],
	 0,
	 nz]]

                           
Out[51]= nz





FullSimplify[ansPP11]

Frob[k_] :=
    SecondNonToricKhovanov[1 + k, -k];

Frob[3]

              -2    2
Out[61]= 2 + q   + q

              -2    2
Out[60]= 2 + q   + q

              -2    2
Out[59]= 2 + q   + q

              -2    2
Out[58]= 2 + q   + q

ansNN00 = Block[{extraPoints = 2},
		With[{aSeries = -3 - k,
		      bSeries = 3 - k},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
							       SecondNonToricKhovanov[aSeries /. {k -> k1},
										      bSeries /. {k -> k2}]],
						      Join[{aSeries}, PosFundEigenvalues[]],
						      Join[{bSeries}, PosFundEigenvalues[]]]]];

ansPN00 = Block[{extraPoints = 2},
		With[{aSeries = -2 + k,
		      bSeries = 4 + k},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
							       SecondNonToricKhovanov[aSeries /. {k -> k1},
										      bSeries /. {k -> k2}]],
						      Join[{aSeries}, PosFundEigenvalues[]],
						      Join[{bSeries}, PosFundEigenvalues[]]]]];

ansPN00 = Block[{extraPoints = 2},
		With[{aSeries = 3,
		      bSeries = -3- k},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k2},
							       SecondNonToricKhovanov[aSeries,
										      bSeries /. {k -> k2}]],
						      Join[{bSeries}, PosFundEigenvalues[]]]]];




FullSimplify[(Table[AA[i,j], {i, 1, 3}, {j, 1, 3}] /. ansNN11)
	     - (Table[AA[i,j], {i, 1, 3}, {j, 1, 3}] /. ansPP11)]

    
FullSimplify[ansNN11 - ansPP11]


ansPP13 = Block[{extraPoints = 2},
		With[{aSeries = 6 + 3 k},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
							       ThreeStrandKhovanov[aSeries /. {k -> k1}]],
						      Join[{aSeries}, {q^2, t^(4/3) q^4}]]]]

                                        comb and indets: {Function[{k1}, 
 
        2 6 + 3 k1           4  4/3 6 + 3 k1
>     (q )         AA[1] + (q  t   )         AA[2]], {AA[1], AA[2]}, 
 
>    Function[{k1$}, ThreeStrandKhovanov[6 + 3 k /. {k -> k1$}]]}
{{0, 4}}

                         2    4  2    8  3    10  5    12  5
                    1 + q  + q  t  + q  t  + q   t  + q   t
Out[104]= {AA[1] -> ----------------------------------------, 
                                    3    9  4
                                   q  - q  t
 
>    AA[2] -> 
 
               2    2      4      2  2    6  3    4  4      6  4      8  4
       -2 - 2 q  + q  t + q  t + q  t  + q  t  + q  t  + 3 q  t  + 2 q  t
>      -------------------------------------------------------------------}
                                          6  4
                                 q (-1 + q  t )


(* ### Check evolution for 3-strand knots (for positive region) ### *)
ansPP13 = Block[{extraPoints = 2},
		With[{aSeries = 4 + 3 k},
		     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
							       ThreeStrandKhovanov[aSeries /. {k -> k1}]],
						      Join[{aSeries}, {q^2, t^(4/3) q^4}]]]]

                                                  comb and indets: {Function[{k1}, 
 
        2 4 + 3 k1           4  4/3 4 + 3 k1
>     (q )         AA[1] + (q  t   )         AA[2]], {AA[1], AA[2]}, 
 
>    Function[{k1$}, ThreeStrandKhovanov[4 + 3 k /. {k -> k1$}]]}
{{0, 4}}

                         2    4  2    8  3    10  5    12  5
                    1 + q  + q  t  + q  t  + q   t  + q   t
Out[102]= {AA[1] -> ----------------------------------------, 
                                    3    9  4
                                   q  - q  t
 
               2/3    4  5/3    2  8/3    4  8/3    6  11/3    8  11/3
              t    + q  t    + q  t    + q  t    + q  t     + q  t
>    AA[2] -> --------------------------------------------------------}
                                            6  4
                                   q (-1 + q  t )




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

