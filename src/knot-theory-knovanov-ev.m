
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
		   indets = EigenvalueIndetsAdvanced[specs],
		   correctionFactors = Map[Module[{power = #[[1]] /. {k -> 0}},
						  Map[#^power &, Rest[#]]] &,
					   specs]},
		  (* List[comb, indets, correctionFactors]; *)
		  Module[{eqns = Map[(family @@ #) - (comb @@ #) == 0 &,
				     Tuples[Map[Range[0, Length[#] - 1 - 1] &,
						specs]]]},
			 Module[{ans = Solve[eqns, indets]},
				If[1 =!= Length[ans],
				   Message["More than one solution to a linear system"],
				   Module[{indices = Tuples[Map[Range[0, Length[#] - 1 - 1 + extraPoints]&,
								specs]]},
					  Print[Tally[Map[If[0 === FullSimplify[(family @@ #) - (comb @@ #) /. ans[[1]]],
					  		     0,
					  		     nz] &,
					  		  indices]]];
					  Map[Rule[#[[1]],
						   FullSimplify[1/(Times @@ MapIndexed[correctionFactors[[#2[[1]], #1]] &,
										       (List @@ #[[1]])])
								#[[2]]]] &,
					      ans[[1]]]]]]]]];

(* ### Archive the previous evaluation attempts ### *)
(* FitFamilyWithEigenvalues[TwoStrandKhovanov, PosFundEigenvalues[]] *)
(* FitFamilyWithEigenvalues[TwoStrandKhovanov[-#] &, NegFundEigenvalues[]] *)
(* FitFamilyWithEigenvalues[Kh[FigeightLikePD[1, #+1]][q,t] &, NegFundEigenvalues[]] *)
(* Block[{C = 2, DD = 2}, *)
(*       FitFamilyWithEigenvalues[Kh[FigeightLikePD[1, # - 1]][q,t] &, NegFundEigenvalues[]]] *)
(* Block[{C = 2, DD = 2}, *)
(*       FitFamilyWithEigenvalues[Kh[FigeightLikePD[1, -#-1]][q,t] &, PosFundEigenvalues[]]] *)

Block[{C = 2, DD = 2},
      FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
						Kh[FigeightLikePDAlt[2 k1 + 3, k2+2]][q,t]],
				       {2 k + 3} ~Join~ NegAdjEigenvalues[],
				       {k+2} ~Join~ PosFundEigenvalues[]]]




      
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
