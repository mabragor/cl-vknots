
Quiet[<< KnotTheory`];

(* fd = OpenWrite["~/quicklisp/local-projects/cl-vknots/khovanovs-reduced" *)
(* 	       <> ToString[n] *)
(* 	       <> "-" <> ToString[mFrom] *)
(* 	       <> "-" <> ToString[mTo] *)
(* 	       <> ".txt"]; *)

(* Module[{m}, *)
(*        For[m = mFrom, m <= mTo, m ++, *)
(* 	   If[Not[CoprimeQ[n, m]], *)
(* 	      Continue[]]; *)
(* 	   kh = Kh[TorusKnot[n, m], JavaOptions -> "-Xmx6g"][q, t] // InputForm; *)
(* 	   Print[kh]; *)
(* 	   (\* WriteString[fd, "khRed[" <> ToString[n] <> "," *\) *)
(* 	   (\* 	       <> ToString[m] <> "]=" <> ToString[kh] <> ";\n"]; *\) *)
(* 	  ]]; *)
(* (\* Close[fd]; *\) *)

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
FigeightLikePD[a_, b_] :=
    If[And[EvenQ[a], EvenQ[b]],
       FigeightLikePDEE[a, b],
       If[And[EvenQ[a], OddQ[b]],
	  FigeightLikePDEO[a, b],
	  If[And[OddQ[a], EvenQ[b]],
	     FigeightLikePDOE[a, b],
	     If[And[OddQ[a], OddQ[b]],
		FigeightLikePDOO[a, b],
		Message["Error"]]]]];
FigeightLikePDEE[a_, b_] :=
    Module[{A = Abs[a],
	    B = Abs[b]},
	   (PD @@ Join[AntiParallelTwoStrandBraidTopInc[B + 1, A + B + 3, b],
		       AntiParallelTwoStrandBraidBottomInc[B + 1, 2 A + 2 B + 5, a],
		       {X[A + 2 B + 5, A + B + 1, A + 2 B + 4, A + B + 2],
			X[A + 2 B + 3, A + B + 2, A + 2 B + 4, A + B + 3]}]
	    /. {2 A + 2 B + 5 -> 1})];
FigeightLikePDEO[a_, b_] :=
    Module[{A = Abs[a],
	    B = Abs[b]},
	   (PD @@ Join[AntiParallelTwoStrandBraidBottomInc[A + B + 3, B + 1, b],
		       ParallelTwoStrandBraid[B + 3, A + 2 B + 5, a],
		       {X[A + 2 B + 4, B + 2, A + 2 B + 5, B + 3],
			X[A + 2 B + 3, B + 2, A + 2 B + 4, B + 1]}]
	    /. {2 A + 2 B + 5 -> 1})];
FigeightLikePDOE[a_, b_] :=
    Module[{A = Abs[a],
	    B = Abs[b]},
	   (PD @@ Join[ParallelTwoStrandBraid[1, A + B + 3, b],
		       AntiParallelTwoStrandBraidBottomInc[B + 1, 2 A + 2 B + 5, a],
		       {X[A + B + 1, A + 2 B + 5, A + B + 2, A + 2 B + 4],
			X[A + B + 2, A + 2 B + 3, A + B + 3, A + 2 B + 4]}]
	    /. {2 A + 2 B + 5 -> 1})];
FigeightLikePDOO[a_, b_] :=
    Module[{A = Abs[a],
	    B = Abs[b]},
	   (PD @@ Join[ParallelTwoStrandBraid[1, A + B + 4, b],
		       AntiParallelTwoStrandBraidBottomInc[A + 2 B + 4, A + B + 3, a],
		       {X[2 A + 2 B + 4, B + 3, 2 A + 2 B + 5, B + 2],
			X[2 A + 2 B + 5, B + 1, 2 A + 2 B + 6, B + 2]}]
	    /. {2 A + 2 B + 6 -> A + B + 4,
		A + B + 3 -> 1})];
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

FitFamilyWithEigenvalues[TwoStrandKhovanov, PosFundEigenvalues[]]

FitFamilyWithEigenvalues[TwoStrandKhovanov[-#] &, NegFundEigenvalues[]]


FitFamilyWithEigenvalues[Kh[FigeightLikePD[1, #+1]][q,t] &, NegFundEigenvalues[]]

FitFamilyWithEigenvalues[Kh[FigeightLikePD[1, -#-1]][q,t] &, PosFundEigenvalues[]]


Kh[FigeightLikePD[1, 1]][q,t]

Out[11]= AntiParallelTwoStrandBraidTopInc[4, 7, 3]

Out[10]= FigEightLikePDEE[3, 3]

ApplyFundEvolutionMethod[Kh[FigeightLikePD[#, 1]] &, True]


Kh[Knot[3,1]][q, t]

FigeightLikePD[1, 1]

Out[8]= PD[X[4, 3, 1, 2], X[1, 4, 2, 3]]

Kh[FigeightLikePD[2, 1]][q, t]

             3    5  2    9  3
Out[6]= q + q  + q  t  + q  t

          1   0     3   0     5   2     9   3
Out[5]= #1  #2  + #1  #2  + #1  #2  + #1  #2  & 
      

posTwoStrandTorus = ApplyFundEvolutionMethod[TwoStrandKhovanov, True]

PD[BR[2, {-1,-1}]]

Kh[PD[X[10, 2, 3, 1], X[1, 3, 2, 10]]][q,t]


Kh[PD[X[5, 2, 3, 1], X[1, 3, 2, 5]]][q,t]

              2    4  2    6  2
Out[12]= 1 + q  + q  t  + q  t

Out[8]= PD[X[2, 3, 1, 4], X[3, 2, 4, 1]]

Out[7]= PD[X[1, 1, 2, 2]]

{0, 0, 0, 0, 0, 0, 0}

                       2      6  3    8  3                2    2
                 -1 + q  t - q  t  - q  t          -(2 + q  - q  t)
Out[6]= {AA -> -(-------------------------), BB -> ----------------, 
                      2          4  2                        2
                     q  t (-1 + q  t )              2 (-1 + q  t)
 
               2    2
           -(-q  - q  t)
>    CC -> -------------}
                   2
           2 (1 + q  t)


Expand[Block[{n = 18},
	     Simplify[(TwoStrandKhovanov[n]
		       - (q^n + q^(n-2))
		       - t^n q^(3 n)
		       - t^2 q^(2 + n)
		       - (1 - (q^4 t^2)^(n/2-1))/(1 - q^4 t^2) q^(n+6) (t^3 + t^4))
		     ]]]

TwoStrandKhovanovTheor[n_] :=
    (q^n(1 + q^(-2) + t^2 q^2 + q^6 (t^3 + t^4)/(1 - q^4 t^2))
     + t^n q^(3 n) (1 - 1/2 (q^(-4) t^(-2) + q^(-6) t^(-3)) q^6 (t^3 + t^4)/(1 - q^4 t^2))
     + (-t)^n q^(3 n) (-1) 1/2 (q^(-4) t^(-2) - q^(-6) t^(-3)) q^6 (t^3 + t^4)/(1 - q^4 t^2));

FullSimplify[(-1) 1/2 (q^(-4) t^(-2) - q^(-6) t^(-3)) q^6 (t^3 + t^4)/(1 - q^4 t^2)]

            1 + t
Out[112]= ----------
                 2
          2 + 2 q  t

FullSimplify[(1 - 1/2 (q^(-4) t^(-2) + q^(-6) t^(-3)) q^6 (t^3 + t^4)/(1 - q^4 t^2))]

                      2
          -1 + t + 2 q  t
Out[111]= ---------------
                    2
            -2 + 2 q  t

FullSimplify[(1 + q^(-2) + t^2 q^2 + q^6 (t^3 + t^4)/(1 - q^4 t^2))]

                   8  3
              1 + q  t
Out[110]= 1 + ----------
               2    6  2
              q  - q  t

                             6  3
               -2    2  2   q  t  (1 + t)
Out[109]= 1 + q   + q  t  + -------------
                                   4  2
                              1 - q  t

Expand[Block[{n = 13},
	     Simplify[(TwoStrandKhovanov[n]
		       - (q^n + q^(n-2))
		       - t^n q^(3 n)
		       - t^2 q^(2 + n)
		      ) / q^(n+6) /(t^3 + t^4)
		      - ((1 - (q^4 t^2)^((n-3)/2))/(1 - q^4 t^2))
		     ]]]

Expand[Block[{n = 10},
	     Simplify[(TwoStrandKhovanov[n]
		       - TwoStrandKhovanovTheor[n])
		     ]]]

                              
Out[108]= 0

                              
Out[107]= 0

                              
Out[106]= 0

                              
Out[105]= 0

                              
Out[104]= 0

                              
Out[103]= 0

                              
Out[102]= 0

                              
Out[101]= 0

                              
Out[100]= 0

                           
Out[99]= 0

                           
          2    2
Out[98]= q  + q  t

                           
              -2    2
Out[96]= 2 + q   + q

