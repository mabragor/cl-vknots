
Quiet[<< KnotTheory`];

(* ### vv BEGINIMPORTS ### *)
<< "tuple-iterator.m";
(* ### ^^ ENDIMPORTS ### *)

(* ### vv BEGINLIB ### *)
CCCWorkDir = "/home/popolit/quicklisp/local-projects/cl-vknots";
CCCDataDir = CCCWorkDir <> "/data";
CCCSrcDir = CCCWorkDir <> "/src";
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
		  Module[{eqns = Map[(family @@ #) - (comb @@ #) &,
				     Tuples[Map[Range[0, Length[#] - 1 - 1] &,
						specs]]],
                          lhs, rhs, ans},
                         rhs = Simplify[- (eqns /. Map[Rule[#, 0] &, indets])];
                         (* ### ^^ This minus is because a x == b <-> a x - b == 0 ### *)
                         lhs = Map[Function[{eqn},
                                            Map[Simplify[D[eqn, #]] &, indets]], (* ### << We know equation is linear in indets ### *)
                                   eqns];
                         (* Print[lhs, rhs]; *)
                         ans = Simplify[Inverse[lhs (* , ZeroTest -> PossibleZeroQ[Simplify[# /. {q -> Pi, t -> E}]] & *)] . rhs];
			 Module[{ans = Module[{i}, Table[Rule[indets[[i]], ans[[i]]], {i, 1, Length[indets]}]]},
                                Module[{indices = Tuples[Map[Range[0, Length[#] - 1 - 1 + extraPoints]&,
                                                             specs]]},
                                       Module[{check = Tally[Map[If[0 === FullSimplify[((family @@ #) - (comb @@ #) /. ans)
                                                                                       /. {q -> E, t -> Pi}], (* ### << This is just to make our life simpler in this particular case ### *)
                                                                    0,
                                                                    nz] &,
                                                                 indices]]},
                                              If[1 === Length[check],
                                                 Module[{},
                                                        Print[check];
                                                        Map[Rule[#[[1]],
                                                                 Factor[Simplify[#[[2]]]]] &,
                                                            ans]],
                                                 Module[{}, Print[check]; checkFailed]]]]]]]];
PlanarDiagramToAdvancedStructures[pd_] :=
    (* ### Massage the terse format of the planar diagram                                                          ### *)
    (* ### into more convenient collection of maps, which is more suitable to for asking actual questions about PD ### *)
    (* ### Collections of maps returned:                                                                           ### *)
    (* ###   * Next edge of a given one                                                                            ### *)
    (* ###   * Previous edge of a given one                                                                        ### *)
    (* ###   * For a given edge -- the crossing it is an *incoming* edge of (for some choice of orientation)       ### *)
    (* ###   * For a given edge -- the crossing it is an *outgoing* edge of (for some choice of orientation)       ### *)
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
(* ### vv Substitute an edge in a planar diagram with two endpoints (i.e. unlink the planar diagram at this edge) ### *)
UnlinkPDAtEdge[edge_Edge, pd_PDConvenient] :=
  (pd /. {(* ### vv We write the patterns for positive and negative crossings separately ... ### *)
            Yp[edge, b_Edge, c_Edge, d_Edge] :> Yp[Edge[Sequence @@ edge, "i"], b, c, d],
            Yp[a_Edge, edge, c_Edge, d_Edge] :> Yp[a, Edge[Sequence @@ edge, "i"], c, d],
            Yp[a_Edge, b_Edge, edge, d_Edge] :> Yp[a, b, Edge[Sequence @@ edge, "f"], d],
            Yp[a_Edge, b_Edge, c_Edge, edge] :> Yp[a, b, c, Edge[Sequence @@ edge, "f"]],
            (* ### ^v  Because I can't figure out, how to write this in a generic way ### *)
            Ym[edge, b_Edge, c_Edge, d_Edge] :> Ym[Edge[Sequence @@ edge, "i"], b, c, d],
            Ym[a_Edge, edge, c_Edge, d_Edge] :> Ym[a, Edge[Sequence @@ edge, "i"], c, d],
            Ym[a_Edge, b_Edge, edge, d_Edge] :> Ym[a, b, Edge[Sequence @@ edge, "f"], d],
            Ym[a_Edge, b_Edge, c_Edge, edge] :> Ym[a, b, c, Edge[Sequence @@ edge, "f"]]});
(* ### vv Substitute two edge-endpoints with a single edge (i.e. link the planar diagram at this edge). ### *)
(* ###    Assumes, that the planar diagram `pd` is well-formed, and `point1` and `point2` are indeed the endpoints ### *)
LinkPDAtPoints[point1_Edge, point2_Edge, pd_PDConvenient] :=
    (pd /. {point2 -> point1});

          
    
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
CSFindLabelInBraidSpec[spec_BraidSpec, label_] :=
    (* ### ^^ For this function we assume that BraidSpec is well-formed, i.e. `label` occurs somewhere exactly twice ### *)
    (* ###    But, in principle, an external arc may join not only "in" and "out" braid ends, but also two ins or two outs ### *)
    Block[{theIns = {}, theOuts = {}},
          Scan[Function[{aSpec},
                        CSFindLabelInBraidSpec[aSpec, label]],
               List @@ spec];
          Join[theIns, theOuts]];
CSFindLabelInBraidSpec[Braid[numStrands_, label_, inputConns_, outputConns_], label_] :=
    Module[{},
           theIns = Join[theIns,
                         Map[II[label, #[[1]] - 1] &,
                             Position[inputConns, label]]];
           theOuts = Join[theOuts,
                          Map[OO[label, #[[1]] - 1] &,
                              Position[outputConns, label]]];
           Success];
CSFindLabelInBraidSpec[CabledBraid[numCables_, numStrandsPerCable_, label_, inputConns_, outputConns_], label_] :=
    Module[{},
           theIns = Join[theIns,
                         Map[II[label, {#[[1]] - 1, #[[2]] - 1}] &,
                             Position[inputConns, label]]];
           theOuts = Join[theOuts,
                          Map[OO[label, {#[[1]] - 1, #[[2]] - 1}] &,
                              Position[outputConns, label]]];
           Success];
(* ### vv Calculate, which endpoints of the arcs outside of the braids are connected ### *)
(* ###    (both through the braids and out of the braids) to one another             ### *)
(* ###    Each endpoint turns out to be connected to *exactly* two other endpoints,  ### *)
(* ###    which we write as a list of two elements.                                  ### *)
(* ###    The first list element is connection inside the braid,                     ### *)
(* ###    and the second elementis connection outside the braid.                     ### *)
ConnectionScheme[spec_BraidSpec, choiceOfResidues_] :=
    Module[{i, lstSpec = List @@ spec},
           Block[{connectionsCS = <||>},
                 (* ### vv Populate the connection hash with connections inside the braids ### *)
                 For[i = 1, i <= Length[lstSpec], i ++,
                     CSPopulateInsideConnections[lstSpec[[i]], choiceOrResidues[[i]]]];
                 (* ### vv Populate with connections that are outside the braids ### *)
                 Scan[Function[{label},
                               Module[{it = CSFindLabelInBraidSpec[spec, label]},
                                      (* Print["label: ", label, " pos: ", it]; *)
                                      connections[[Key[it[[1]]], 2]] = it[[2]];
                                      connections[[Key[it[[2]]], 2]] = it[[1]]]],
                      CSGetExternalConnectionLabels[spec]];
                 connectionsCS]];
CSGetExternalConnectionLabels[spec_BraidSpec] :=
    DeleteDuplicates[Flatten[Map[CSGetExternalConnectionLabels,
                                 List @@ spec]]];
CSGetExternalConnectionLabels[Braid[numStrands_, label_, inputConns_, outputConns_]] :=
    {inputConns, outputConns};
CSGetExternalConnectionLabels[CabledBraid[numCables_, numStrandsPerCable_, label_, inputConns_, outputConns_]] :=
    {inputConns, outputConns};
CSPopulateInsideConnections[Braid[numStrands_, label_, inputConns_, outputConns_], residue_] :=
    (* ### vv `connectionsCS` is dynamically scoped variable, supposed to be set up by the caller ### *)
    Scan[Function[{index},
                  connectionsCS[II[label, index]] = {OO[label,Mod[index - residue, numStrands]],
                                                     Null}; (* ### << By convention the inside-connections are 1st element ### *)
                  connectionsCS[OO[label, index]] = {II[label, Mod[index + residue, numStrands]],
                                                     Null}],
         (* ### vv The 0-based numbering convention is for convenience of taking the Mod in shifts ### *)
         Range[0, numStrands - 1]];
CSPopulateInsideConnections[CabledBraid[numCables_, numStrandsPerCable_, label_, inputConns_, outputConns_], residue_] :=
    (* ### vv `connectionsCS` is dynamically scoped variable, supposed to be set up by the caller ### *)
    Scan[Function[{index},
                  Scan[Function[{subIndex},
                                connectionsCS[II[label, {index, subIndex}]] = {OO[label, {Mod[index - residue, numStrands],
                                                                                          subIndex}],
                                                                               Null};
                                connectionsCS[OO[label, {index, subIndex}]] = {II[label, {Mod[index + residue, numStrands],
                                                                                          subIndex}],
                                                                               Null}],
                       Range[0, numStrandsPerCable - 1]]],
         (* ### vv The 0-based numbering convention is for convenience of taking the Mod in shifts ### *)
         Range[0, numCables - 1]];
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
(* ### vv Another version of routine that finds connected components and works on connection schemes ### *)
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
				prevNode = Null, i},
			       While[True,
				     Module[{nextNodes = Select[connScheme[curNode], # =!= prevNode &]},
                                            (* ### ^^ Generically this list would contain exactly one element -- the next node ### *)
                                            If[And[{} === nextNodes,
                                                   prevNode === firstNode],
                                               Break[],
                                               Module[{nextNode = nextNodes[[1]]},
                                                      If[nextNode === firstNode,
                                                         Break[],
                                                         CompoundExpression[prevNode = curNode,
                                                                            curNode = nextNode,
                                                                            KeyDropFrom[freeNodes, nextNode],
                                                                            AppendTo[curComponent, nextNode]]]]]]];
			       AppendTo[connectedComponents, NormalizeConnectedComponent[curComponent]]]]];
	   (* ### vv Sort the connected component so that their starting elements are in order ### *)
	   Sort[connectedComponents,
		DepthTwoLexiSort]];
(* ### vv Lexicographic sorting for lists of length two ### *)
DepthTwoLexiSort[eltOne_, eltTwo_] :=
    Module[{it = Order[eltOne[[1]], eltTwo[[1]]]},
	   If[0 =!= it,
	      it,
	      Order[eltOne[[2]], eltTwo[[2]]]]];
(* ### vv The helper function for defining the sign of the orientation of the connected component      ### *)
(* ###    Returns True if the next element in the connected component is connected 'through' the braid ### *)
NextNodeIsInOrderQ[spec_BraidSpec, component_, i_, residues_] :=
    Module[{item = component[[i]],
	    nextItem = component[[1 + Mod[i, Length[component]]]],
	    lstSpec = List @@ spec},
	   And[OO === Head[nextItem], (* ### << the next item is an `output` ### *)
	       item[[1]] === nextItem[[1]], (* ### << it is in the same braid ### *)
               (* ### vv its index is consistent with the residue of the number of crossings ### *)
	       Module[{pos = Position[lstSpec, Condition[elt_, elt[[2]] === item[[1]]], {1}, Heads->False][[1,1]]},
		      item[[2]] == Mod[nextItem[[2]] + residues[[pos]] (* ### << relevant residue ### *),
				       (lstSpec)[[pos, 1]] (* ### << relevant braid thickness ### *)]]]];
(* ### vv Calculates, orientations of which incoming edges should be set consistently together, and in what way ### *)
(* ###    ... and which are independent                                                                         ### *)
(* ###    Outputs list of associations, one for each connected components, where keys in each association are   ### *)
(* ###    the braids' incoming arc-ends and values are the orientation signs                                    ### *)
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
(* ### vv Braidosome is that smart program that does all the work I want to get done for me ### *)
(* ###    Example of input :                                                                ### *)
(* ###      Braidosome[BraidSpec[Braid[2, a, {2, 1}, {4, 3}], Braid[2, b, {3, 1}, {4, 2}]], ### *)
(* ###                           OriChoice[II[a, 0] -> 1, II[a, 1] ->, II[b, 1] -> 1 ...],  ### *)
(* ###                           {10, 20}]                                                  ### *)
(* ###    This example describes the figure-eight-like knots                                ### *)
(* ###        ----                                                                          ### *)
(* ###    Each specification of a braid can be also a `CabledBraid`                         ### *)
(* ###      CabledBraid[{2, 3}, a, {{1,2,3}, {4,5,6}}, {{7,8,9}, {10,11,12}}]               ### *)
(* ###                             ^^ so you see that inputs and outputs of cabled braid    ### *)
(* ###                                are grouped by "master" strand.                       ### *)
Braidosome[spec_BraidSpec, orientationChoice_, braidWindings_] :=
    ExtendedPDToUsual[PlanarDiagramToAdvancedStructures[PlanarDiagram[spec, orientationChoice, braidWindings]]];
(* ### vv For a given braid specification, generate a list of possible orientations of the arcs between the braids, ### *)
(* ###    together with compatible possible choices of residues of the number of crossings in the braids by number of strands ### *)
(* ###    In short, split possible orientation choices into "orientation clusters" ### *)
OrientationClusters[spec_BraidSpec] :=
    Module[{theClusters = <||>},
	   Module[{allResidues = Tuples[Map[Range[0, #[[1]] - 1] &, List @@ spec]]},
                  Scan[Function[{residueChoice},
                                Module[{res = OrientationClustersForAResidueChoice[spec, residueChoice]},
                                       Scan[Module[{val = Lookup[theClusters, #[[1]], {}]},
                                                   theClusters[#[[1]]] = Append[val, #[[2]]]] &,
                                            res]]],
                       allResidues]];
           theClusters];
(* ### vv Given the choice of residues of the numbers of crossings in braids, construct compatible orientations ### *)
OrientationClustersForAResidueChoice[spec_BraidSpec, residueChoice_List] :=
    Module[{res = {}}, (* ### << In this function we assemble the result as a list, and put it into proper hash ### *)
           (*                    in the wrapping function                                                       ### *)
           (* Print["residues: ", residueChoice]; *)
           (* ### vv This formatting is crap, but we don't have the Module* (analog of LET* ) macro ### *)
           (* ###    which would be appropriate to use here ### *)
           Module[{connScheme, connComps, oriMasks},
                  connScheme = ConnectionScheme[spec, residueChoice];
                  connComps = ConnectedComponentsConnectionScheme[connScheme];
                  oriMasks = OrientationMasks[spec, connComps, residueChoice];
                  (* Print["scheme, comps, masks: ", connScheme, " ", connComps, " ", oriMasks]; *)
                  Scan[Function[{oriChoice},
                                AppendTo[res, OrientationClustersProcessOrientationChoice[oriChoice,
                                                                                          oriMasks,
                                                                                          residueChoice]]],
                       (* ### vv All possible orientation choices, but the first component always contains II[a,0], ### *)
                       (* ###    hence we fix sign freedom this way                                                 ### *)
                       Map[{1} ~Join~ # &, Tuples[{1,-1}, Length[connComps] - 1]]]];
           res];
OrientationClustersProcessOrientationChoice[oriChoice_, oriMasks_, residueChoice_] :=
    (* ### ^^ short for 'orientation choice' ### *)
    Module[{i, totalOrientation = {}},
           For[i = 1, i <= Length[oriChoice], i ++,
               AppendTo[totalOrientation,
                        Map[Rule[#[[1]],
                                 oriChoice[[i]] * #[[2]]] &,
                            Normal[oriMasks[[i]]]]]];
           (* Print["total ori: ", totalOrientation]; *)
           {(OriChoice @@ Sort[Join @@ totalOrientation,
                               (* ### vv We sort by keys ### *)
                               DepthTwoLexiSort[#1[[1]], #2[[1]]] &]),
            residueChoice}];
(* ### vv the crossing that looks "positive" in the absolute frame: had both strands been oriented from down to up ### *)
YpAbs[ll_, lr_, ul_, ur_, ori1_, ori2_] :=
    If[And[ori1 == 1, ori2 == 1],
       Yp[ll, lr, ul, ur],
       If[And[ori1 == -1, ori2 == 1],
	  Ym[lr, ur, ll, ul],
	  If[And[ori1 == 1, ori2 == -1],
	     Ym[ul, ll, ur, lr],
	     If[And[ori1 == -1, ori2 == -1],
		Yp[ur, ul, lr, ll],
		Print["Caboom!"]]]]];
(* ### vv the crossing that looks "negative" in the absolute frame: had both strands been oriented from down to up ### *)
YmAbs[ll_, lr_, ul_, ur_, ori1_, ori2_] :=
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
(* ### vv Append `head` to all edges' marks. Useful for combining of several planar diagrams into a common one. ### *)
HeadShift[head_, whole_PDConvenient] :=
    (whole /. {Edge[seq__] :> Edge[head, seq]});
(* ### vv Replace a strand in a planar diagram by `n`-cable. ### *)
Cable[1, pd_PDConvenient] :=
    pd;
Cable[n_, pd_PDConvenient] :=
    Module[{res = {}, head, a, b, c, d, i},
           Scan[Function[{crossing},
                         Print["crossing: ", crossing];
                         head = crossing[[0]];
                         {a, b, d, c} = List @@ crossing;
                         (* ### vv Add contribution of corners ### *)
                         res = Join[res, {head[Edge[Sequence[a], 0, n], Edge[Sequence[b], 1, 0],
                                               Edge[Sequence[b], 1, 1], Edge[Sequence[a], 1, n]],
                                          head[Edge[Sequence[a], 0, 1], Edge[Sequence[b], 1, n-1],
                                               Edge[Sequence[d], 1, 0], Edge[Sequence[a], 1, 1]],
                                          head[Edge[Sequence[a], n-1, 1], Edge[Sequence[b], n, n-1],
                                               Edge[Sequence[d], n, 0], Edge[Sequence[c], 0, 1]],
                                          head[Edge[Sequence[a], n-1, n], Edge[Sequence[b], n, 0],
                                               Edge[Sequence[b], n, 1], Edge[Sequence[c], 0, n]]}];
                         (* ### vv Add contribution of borders ### *)
                         For[i = 1, i <= n - 2, i ++,
                             res = Join[res, {head[Edge[Sequence[a], i, n], Edge[Sequence[b], i+1, 0],
                                                   Edge[Sequence[b], i+1, 1], Edge[Sequence[a], i+1, n]],
                                              head[Edge[Sequence[a], 0, n-i], Edge[Sequence[b], 1, i],
                                                   Edge[Sequence[b], 1, i+1], Edge[Sequence[a], 1, n-i]],
                                              head[Edge[Sequence[a], i, 1], Edge[Sequence[b], i+1, n-1],
                                                   Edge[Sequence[d], i+1, 0], Edge[Sequence[a], i+1, 1]],
                                              head[Edge[Sequence[a], n-1, n-i], Edge[Sequence[b], n, i],
                                                   Edge[Sequence[b], n, i+1], Edge[Sequence[c], 0, n-i]]}]];
                         (* ### vv Add contribution of bulk ### *)
                         For[i = 1, i <= n - 2, i  ++,
                             For[j = 1, j <= n - 2, j ++,
                                 AppendTo[res, head[Edge[Sequence[a], i, n-j], Edge[Sequence[b], i+1, j],
                                                    Edge[Sequence[b], i+1, j+1], Edge[Sequence[a], i+1, n-j]]]]]],
                List @@ pd];
           PDConvenient @@ res];
(* ### vv Convert an extended representation of a planar diagram into the terse one, that is understood by KnotTheory ### *)
(* ###    If necessary, adds dummy crossings so that connected components are convenient to cut at.                   ### *)
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
(* ### vv Convert notation for crossings back to the counter-intuitive notation, but which is understood by KnotTheory ### *)
YPMsToXs[expr_] :=
    (expr /. {Ym[a_, b_, c_, d_] :> X[a, b, d, c],
	      Yp[a_, b_, c_, d_] :> X[b, d, c, a]});
(* ### vv A symbol named after the corresponding latin letter 0 for `a`, 1 for `b` and so on. ### *)
LatinLetterSymbol[index_] :=
    If[index > 25,
       Message["Oh crap"],
       Symbol[FromCharacterCode[97 + index]]];
(* ### vv The braid specification of the pretzel knot          ### *)
(* ###    number of 2-strand braids is equal to genus plus one ### *)
PretzelBraidSpec[genus_] :=
    BraidSpec @@ Map[Braid[2, LatinLetterSymbol[#],
                           If[0 === #,
                              {genus + 1, 1},
                              {#, # + 1}],
                           If[0 === #,
                              {2 (genus + 1), (genus + 1) + 1},
                              {genus + 1 + #, genus + 1 + # + 1}]] &,
                     Range[0, genus]];
(* ### vv The simplest choice of braid orientations for the pretzel knot ### *)
PretzelBSWithParallelOrients[genus_] :=
    {PretzelBraidSpec[genus],
     OriChoice @@ Join @@ Map[{II[LatinLetterSymbol[#], 0] -> (-1)^#,
                               II[LatinLetterSymbol[#], 1] -> (-1)^# If[genus === #,
                                                                        (-1)^(genus + 1),
                                                                        1]} &,
                              Range[0, genus]]};
(* ### vv The fully antiparallel choice of braid orientations for the pretzel knot ### *)
PretzelBSWithAntiParallelOrients[genus_] :=
    {PretzelBraidSpec[genus],
     OriChoice @@ Join @@ Map[{II[LatinLetterSymbol[#], 0] -> 1,
                               II[LatinLetterSymbol[#], 1] -> (-1)} &,
                              Range[0, genus]]};
(* ### vv Khovanov polynomial for simple pretzel knot ### *)
PretzelKhovanov[windings_] :=
    If[And[OddQ[Length[windings]], (* ### << genus is even ### *)
           And @@ Map[OddQ, windings]] (* ### << all windings are odd ### *),
       Kh[Braidosome @@ Append[PretzelBSWithAntiParallelOrients[Length[windings] - 1],
                               windings]][q,t],
       (* ### vv The default 'safe' orientation case ### *)
       Kh[Braidosome @@ Append[PretzelBSWithParallelOrients[Length[windings] - 1],
                               windings]][q,t]];
PretzelReducedKhovanov[windings_] :=
    If[And[OddQ[Length[windings]], (* ### << genus is even ### *)
           And @@ Map[OddQ, windings]] (* ### << all windings are odd ### *),
       KhReduced[Braidosome @@ Append[PretzelBSWithAntiParallelOrients[Length[windings] - 1],
                                      windings]][q,t],
       (* ### vv The default 'safe' orientation case ### *)
       KhReduced[Braidosome @@ Append[PretzelBSWithParallelOrients[Length[windings] - 1],
                                      windings]][q,t]];
AllPrecomputedQ[family_, allowedVars_, eigenvaluesSpecs_] :=
    Module[{res = True},
           Iterate[{indices, MkTupleIter @@ Map[{0, extraPoints + Length[#] - 1 - 1} &, eigenvaluesSpecs]},
                   If[{} =!= Complement[Variables[family @@ indices], allowedVars],
                      Block[{},
                            res = False;
                            Message[fitFamily::nonPrecomp, indices];
                            Break[]]]];
           res];
ShiftIndices[indices_, shifts_] :=
    Module[{i, res = {}},
           Print["shifts ", shifts];
           For[i = 1, i <= Length[shifts], i ++,
               AppendTo[res, shifts[[i]] /. {k -> indices[[i]]}]];
           res];
FitFamilyWithEigenvaluesGradualInternal[family_, allowedVars_, eigenvaluesSpecs_] :=
    Module[{},
           (* ### vv First we check that all polynomials are precomputed ### *)
           If[Not[AllPrecomputedQ[family, allowedVars, eigenvaluesSpecs]],
              Return[$Failed]];
           ClearAll[FFWETmp]; (* ### << The temporary symbol where we will store all the evolution intermediate results ### *)
           Block[{FFWERes = <||>,
                  fdlog = OpenWrite["/home/popolit/tmp/FFWEGradual.log"]},
                 FitFamilyWithEigenvaluesGradualII[family, {}, eigenvaluesSpecs];
                 (* ### vv Don't forget to uncomment this (commented-out for debugging purposes) ### *)
                 (* ClearAll[FFWETmp]; *)
                 Close[fdlog];
                 FFWERes]];
Debugg[fdlog_, msg_] :=
    If[Null =!= fdlog,
       WriteString[fdlog, msg]];
CCCEigenvaluesCritLength = Null;
FitFamilyWithEigenvaluesGradualII[family_, alreadyTransformedEigenvalues_, eigenvaluesYetToTransform_] :=
    Module[{curEigSpec = eigenvaluesYetToTransform[[1]],
            restEigSpecs = eigenvaluesYetToTransform[[2 ;; ]],
            successFlag = True},
           If[CCCEigenvalueCritLength === Length[alreadyTransformedEigenvalues],
              Return[]];
           If[{} =!= restEigSpecs,
              (* ### vv The regular iteration branch ### *)
              Iterate[{restIndices, MkTupleIter @@ Map[{0, extraPoints + Length[#] - 1 -1} &, restEigSpecs]},
                      Print["restIndices: ", restIndices, " curSeries: ", curEigSpec[[1]]];
                      Module[{shiftIndices = ShiftIndices[restIndices, Map[#[[1]] &, restEigSpecs]]},
                             Debugg[fdlog, "Calculating for: "
                                    <> ToString[alreadyTransformedEigenvalues, InputForm]
                                    <> " " <> ToString[curEigSpec, InputForm]
                                    <> " " <> ToString[shiftIndices, InputForm]
                                    <> " ..."];
                             Print["shiftIndices ", shiftIndices];
                             Module[{anAns = FitFamilyWithEigenvaluesAdvanced[Function[{k},
                                                                                       (* ### vv Here we use unshifted indices   ### *)
                                                                                       (* ###    because shift is already inside ### *)
                                                                                       (* ###    definitio of `family` function  ### *)
                                                                                       family @@ Join[{k}, restIndices]],
                                                                              curEigSpec]},
                                    If[checkFailed === anAns,
                                       Debugg[fdlog, " failed\n"];
                                       successFlag = False;
                                       Break[]];
                                    (* ### ^^ At these point we have the evolution coefficients ### *)
                                    (* ###    Now we need to recurse                            ### *)
                                    Module[{i},
                                           For[i = 1, i <= Length[curEigSpec] - 1, i ++,
                                               (* ### vv 1 + i is because the 1st element is the description of a series ### *)
                                               Set[Evaluate[FFWETmp[Append[alreadyTransformedEigenvalues, curEigSpec[[1 + i]]],
                                                                    shiftIndices]],
                                                   (AA[i] /. anAns) (* ### << That's because we know what                ### *)
                                                   (*                         `FitFamilyWithEigenvaluesAdvanced` returns ### *)
                                                  ]]]];
                             Debugg[fdlog, " done!\n"]]];
              If[Not[successFlag],
                 Return[$Failed]];
              (* ### ^^ We've performed Fourier transform in the first eigenvalue set                                    ### *)
              (* ### vv Now we are ready to recurse, or finish and collect the results                                   ### *)
              Module[{i},
                     For[i = 1, i <= Length[curEigSpec] - 1, i ++,
                               Module[{newEigs = Append[alreadyTransformedEigenvalues, curEigSpec[[1 + i]]]},
                                      Module[{res = FitFamilyWithEigenvaluesGradualII[
                                          (* ### Yet to construct ### *)
                                          Function[Evaluate[Map[Symbol["k" <> ToString[#]] &,
                                                                Range[1, Length[restEigSpecs]]]],
                                                   Evaluate[FFWETmp[newEigs,
                                                                    MapIndexed[#1[[1]] /. {k -> Symbol["k" <> ToString[#2[[1]]]]} &,
                                                                               restEigSpecs]]]],
                                          newEigs,
                                          restEigSpecs]},
                                             If[$Failed === res,
                                                Return[$Failed]]]]]],
              (* ### vv The last iteration branch, we're performing FT in the last eigenvalue set                        ### *)
              Debugg[fdlog, "Calculating for: "
                     <> ToString[alreadyTransformedEigenvalues, InputForm]
                     <> " " <> ToString[curEigSpec, InputForm]
                     <> " " <> ToString[{}, InputForm]
                     <> " ..."];
              Module[{anAns = FitFamilyWithEigenvaluesAdvanced[family, curEigSpec]},
                     If[checkFailed === anAns,
                        Debugg[fdlog, " failed\n"];
                        Return[$Failed]];
                     Module[{i},
                            For[i = 1, i <= Length[curEigSpec] - 1, i ++,
                                (FFWERes[Append[alreadyTransformedEigenvalues, curEigSpec[[1 + i]]]]
                                 = AA[i] /. anAns)]]];
              Debugg[fdlog, " done!"]]];
FitFamilyWithEigenvaluesGradual[family_, eigenvaluesSpecs__] :=
    (* ### vv The {q,t}-specification is needed to check, whether we have all the polynomials precomputed ### *)
    FitFamilyWithEigenvaluesGradualInternal[family,
                                            {q, t},
                                            List[eigenvaluesSpecs]];
EvoFname["red", signs_List] :=
    EvoFname["red", signs, Null];
EvoFname[signs_List] :=
    EvoFname["vanilla", signs, Null];
EvoFname[signs_List, altIndex_] :=
    EvoFname["vanilla", signs, altIndex];
EvoFname[type_String, signs_List, altIndex_] :=
    (CCCDataDir <> "/pretzel-kh"
     <> If["red" === type,
           "-red",
           ""]
     <> "-evo-" <> ToString[Length[signs]] <> "-"
     <> StringRiffle[Map[ToString, signs], "-"]
     <> If[Null === altIndex,
           "",
           "-alt" <> ToString[altIndex]]
     <> ".m");
MkSymList[symHead_, numSyms_] :=
    Map[Symbol[ToString[symHead] <> ToString[#]] &, Range[1, numSyms]];
MkEvoFunction[evoRules_] :=
    Module[{numArgs = Length[Keys[evoRules][[1]]]}, (* ### << I know this is a bit excessive, but I don't know any other way ### *)
           Function[Evaluate[MkSymList["n", numArgs]],
                    Evaluate[Simplify[
                        Plus @@ KeyValueMap[#2
                                            * Times @@ MapIndexed[Function[{eigenvalue, number},
                                                                           eigenvalue^(Symbol["n" <> ToString[number[[1]]]])],
                                                                  #1] &,
                                            evoRules]]]]];
(* ### vv Loads all precomputed khovanov polynomials for pretzel knots of a given genus ### *)
LoadAllPrecomps[genus_] :=
    Iterate[{signs, MkTupleIter @@ Table[AList[1, -1], {i, 1, genus + 1}]},
            Get[CCCWorkDir <> "/data/pretzel-khovanovs-" <> ToString[genus + 1]
                <> "-" <> StringRiffle[Map[ToString, signs], "-"]
                <> ".m"]];
(* ### ^^ ENDLIB ### *)

