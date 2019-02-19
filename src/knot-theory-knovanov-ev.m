
<< "knot-theory-knovanov-ev-utils.m";
<< "tuple-iterator.m";

(* << "../data/pretzel-khovanovs-2-1-1.m"; *)
(* << "../data/pretzel-khovanovs-2--1--1.m"; *)
(* << "../pretzel-khovanovs-3-1-1-1.m"; *)

CCCMaxParallelWindings = 8;
CCCMaxAntiparallelWindings = 10;
PrecomputePretzels[genus_] :=
    PrecomputePretzels[genus, False];
PrecomputePretzels[genus_, force_] :=
    Module[{signIter = MkTupleIter @@ Map[AList @@ # &, Module[{i}, Table[{1,-1}, {i, 1, genus + 1}]]]},
           Module[{signs, validQ},
                  While[True,
                        {signs, validQ} = signIter[];
                        If[Not[validQ],
                           Break[]];
                        Module[{fname = ("/home/popolit/quicklisp/local-projects/cl-vknots/data/pretzel-khovanovs-"
                                         <> ToString[genus + 1] <> "-" <> StringRiffle[Map[ToString, signs], "-"] <> ".m"),
                                flogname = ("/home/popolit/quicklisp/local-projects/cl-vknots/data/pretzel-khovanovs-"
                                            <> ToString[genus + 1] <> ".log")},
                               If[And[FileExistsQ[fname],
                                      Not[force]],
                                  Block[{}, Message[pp::fileExists, "File " <> fname <> " already exists, use `force` to overwrite"];
                                        Return[]]];
                               Module[{fd = OpenWrite[fname],
                                       fdlog = OpenWrite[flogname],
                                       windsIter = MkTupleIter @@ Join[Module[{i}, Table[{1, CCCMaxParallelWindings}, {i, 1, genus}]],
                                                                       If[EvenQ[genus + 1],
                                                                          {{1, CCCMaxParallelWindings}},
                                                                          {{0, CCCMaxAntiparallelWindings, 2}}]]},
                                      Module[{windings, validQ},
                                             While[True,
                                                   {windings, validQ} = windsIter[];
                                                   If[Not[validQ],
                                                      Break[]];
                                                   Module[{signedWindings = signs * windings},
                                                          (* ### ^^ Elementwise vector multiplication (cool, right?)         ### *)
                                                          Module[{theAns = PretzelKhovanov[signedWindings]},
                                                                 WriteString[fdlog, "Calculating ("
                                                                             <> StringRiffle[Map[ToString, signedWindings], ", "]
                                                                             <> ")" (* ### << This way it also works in screen ### *)
                                                                            ];
                                                                 WriteString[fd, "PrecompKh["
                                                                             <> StringRiffle[Map[ToString, signedWindings], ", "]
                                                                             <> "] := " <> ToString[theAns, InputForm] <> ";"];
                                                                ]];
                                                  ]];
                                      Close[fd];
                                      Close[fdlog]]]]]];
PrecomputePretzelsResume[resumeWindings_] :=
    If[MemberQ[resumeWindings, 0],
       Block[{},
             Message["winding contains zeroes -- please, specify signs explicitly"];
             Return[]],
       PrecomputePretzelsResume[resumeWindings,
                                Map[Sign, resumeWindings]]];
PrecomputePretzelsResume[resumeWindings_, resumeSigns_] :=
    Module[{genus = Length[resumeWindings] - 1},
           Module[{signIter = SkipUntilIter[resumeSigns,
                                            MkTupleIter @@ Map[AList @@ # &,
                                                               Module[{i}, Table[{1,-1}, {i, 1, genus + 1}]]]]},
                  Module[{signs, validQ},
                         While[True,
                               {signs, validQ} = signIter[];
                               If[Not[validQ],
                                  Break[]];
                               Print["signs:", signs];
                               Module[{fd = OpenAppend["/home/popolit/quicklisp/local-projects/cl-vknots/data/pretzel-khovanovs-"
                                                       <> ToString[genus + 1] <> "-" <> StringRiffle[Map[ToString, signs], "-"] <> ".m"],
                                       fdlog = OpenAppend["/home/popolit/quicklisp/local-projects/cl-vknots/data/pretzel-khovanovs-"
                                                          <> ToString[genus + 1] <> ".log"],
                                       windsIter = SkipUntilIter[Map[Abs, resumeWindings],
                                                                 MkTupleIter @@ Join[Module[{i}, Table[{1, CCCMaxParallelWindings},
                                                                                                       {i, 1, genus}]],
                                                                                     If[EvenQ[genus + 1],
                                                                                        {{1, CCCMaxParallelWindings}},
                                                                                        {{0, CCCMaxAntiparallelWindings, 2}}]]]},
                                      WriteString[fdlog, "====== Resuming after some interruption ======"];
                                      WriteString[fd, "(* ====== Resuming after some interruption ====== *)"];
                                      Module[{windings, validQ},
                                             While[True,
                                                   {windings, validQ} = windsIter[];
                                                   If[Not[validQ],
                                                      Break[]];
                                                   Print["windings:", windings];
                                                   Module[{signedWindings = signs * windings},
                                                          (* ### ^^ Elementwise vector multiplication (cool, right?)         ### *)
                                                          Module[{theAns = PretzelKhovanov[signedWindings]},
                                                                 WriteString[fdlog, "Calculating ("
                                                                             <> StringRiffle[Map[ToString, signedWindings], ", "]
                                                                             <> ")" (* ### << This way it also works in screen ### *)
                                                                            ];
                                                                 WriteString[fd, "PrecompKh["
                                                                             <> StringRiffle[Map[ToString, signedWindings], ", "]
                                                                             <> "] := " <> ToString[theAns, InputForm] <> ";"];
                                                                ]];
                                                  ]];
                                      Close[fd];
                                      Close[fdlog]]]]]];
PrecomputePretzelsSoft[signs_] :=
    PrecomputePretzelsSoft[signs, True &];
PrecomputePretzelsSoft[signs_, filterFun_] :=
    (* ### ^^ Compute pretzel knots for a given genus, that had not already been computed ### *)
    Module[{genus = Length[signs] - 1},
           Get[CCCDataDir <> "/pretzel-khovanovs-" <> ToString[genus + 1] <> "-" <> StringRiffle[Map[ToString, signs], "-"] <> ".m"];
           Module[{fd = OpenWrite[CCCDataDir <> "/pretzel-khovanovs-tmp-"
                                   <> ToString[genus + 1] <> "-" <> StringRiffle[Map[ToString, signs], "-"] <> ".m"],
                   (* ### vv There is no need to append to log -- we rewrite it ### *)
                   fdlog = OpenWrite[CCCDataDir <> "/pretzel-khovanovs-" <> ToString[genus + 1] <> ".log"]},
                  Iterate[{windings, MkTupleIter @@ Join[Module[{i}, Table[{1, CCCMaxParallelWindings},
                                                                           {i, 1, genus}]],
                                                         If[EvenQ[genus + 1],
                                                            {{1, CCCMaxParallelWindings}},
                                                            {{0, CCCMaxAntiparallelWindings, 2}}]]},
                          (* Print["windings: ", windings]; *)
                          Module[{signedWindings = signs * windings},
                                 (* ### ^^ Elementwise vector multiplication (cool, right?)         ### *)
                                 If[PrecompKh =!= Head[PrecompKh @@ signedWindings],
                                    (* Print["skipping"]; *)
                                    Continue[]];
                                 If[Not[filterFun[signedWindings]], (* ### << This we need to calculate polys only in ### *)
                                    (* ###                                    regions of complicated shape.           ### *)
                                    Continue[]];
                                 Debugg[fdlog, "Calculating ("
                                        <> StringRiffle[Map[ToString, signedWindings], ", "]
                                        <> ") ..."]; (* ### << This way it also works in screen ### *)
                                 Module[{theAns = PretzelKhovanov[signedWindings]},
                                        WriteString[fd, "PrecompKh["
                                                    <> StringRiffle[Map[ToString, signedWindings], ", "]
                                                    <> "] := " <> ToString[theAns, InputForm] <> ";\n"];
                                        Debugg[fdlog, " done!\n"]]]];
                  Close[fd];
                  Close[fdlog]];
           Run["cat "
               <> CCCDataDir <> "/pretzel-khovanovs-tmp-"
               <> ToString[genus + 1] <> "-" <> StringRiffle[Map[ToString, signs], "-"] <> ".m"
               <> " >> "
               <> CCCDataDir <> "/pretzel-khovanovs-"
               <> ToString[genus + 1] <> "-" <> StringRiffle[Map[ToString, signs], "-"] <> ".m"]
          ];


Block[{CCCMaxParallelWindings = 6,
       CCCMaxAntiparallelWindings = 8},
      PrecomputePretzelsSoft[{1,1,1,1,1,1}]]

(* ### vv Snippets to precompute Khovanov polynomials for pretzel knots ### *)
(* Block[{CCCMaxParallelWindings = 10, *)
(*        CCCMaxAntiparallelWindings = 10}, *)
(*       Iterate[{signs, MkTupleIter[AList[-1, 1], AList[-1, 1], AList[-1, 1]]}, *)
(*               PrecomputePretzelsSoft[signs]]] *)
Block[{CCCMaxParallelWindings = 22,
       CCCMaxAntiparallelWindings = 16},
      PrecomputePretzelsSoft[{1,1,-1}, And[#[[1]] >= Abs[#[[3]]],
                                           #[[1]] <= Abs[#[[3]]] + 5 + 1,
                                           #[[2]] >= Abs[#[[3]]],
                                           #[[2]] <= Abs[#[[3]]] + 5 + 1] &]]

Block[{CCCMaxParallelWindings = 16,
       CCCMaxAntiparallelWindings = 10},
      PrecomputePretzelsSoft[{-1,-1,1}, And[#[[1]] <= -#[[3]],
                                            #[[1]] >= -#[[3]] - 5 - 1,
                                            #[[2]] <= -#[[3]],
                                            #[[2]] >= -#[[3]]] - 5 - 1 &]];

Block[{CCCMaxParallelWindings = 23,
       CCCMaxAntiparallelWindings = 26,
       shift = 4},
      PrecomputePretzelsSoft[{1,-1,-1}, And[#[[2]] <= -#[[1]],
                                            #[[2]] >= -(Floor[(#[[1]] + shift)/2] * 2 + 5),
                                            #[[3]] <= -#[[1]],
                                            #[[3]] >= -(Floor[(#[[1]] + shift)/2] * 2 + 2 4),
                                            #[[1]] <= 11
                                           ] &]]

Block[{CCCMaxParallelWindings = 23,
       CCCMaxAntiparallelWindings = 26,
       shift = 4},
      PrecomputePretzelsSoft[{-1,1,-1}, And[#[[1]] <= -#[[2]],
                                            #[[1]] >= -(Floor[(#[[2]] + shift)/2] * 2 + 5),
                                            #[[3]] <= -#[[2]],
                                            #[[3]] >= -(Floor[(#[[2]] + shift)/2] * 2 + 2 4),
                                            #[[2]] <= 11
                                           ] &]]

(* a = SkipUntilIter[{-1,1}, *)
(*                   MkTupleIter @@ Map[AList @@ # &, Module[{i}, Table[{1,-1}, {i, 1, 1 + 1}]]]]; *)
(* a = MkTupleIter @@ Join[Module[{i}, Table[{1, CCCMaxParallelWindings}, *)
(*                                           {i, 1, 1}]], *)
(*                         If[EvenQ[1 + 1], *)
(*                            {{1, CCCMaxParallelWindings}}, *)
(*                            {{0, CCCMaxAntiparallelWindings, 2}}]]; *)

(* ### vv M^{+++}_{i,j,k} ### *)
ans1 =  Block[{extraPoints = 2},
              With[{aSeries = k+1, bSeries = k+1, cSeries = 2 k+2},
                   FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2, k3},
                                                             PrecompKh[aSeries /. {k -> k1},
                                                                       bSeries /. {k -> k2},
                                                                       cSeries /. {k -> k3}]],
                                                    Join[{aSeries}, PosFundEigenvalues[]],
                                                    Join[{bSeries}, PosFundEigenvalues[]],
                                                    Join[{cSeries}, NegAdjEigenvalues[]]]]];


(* ### vv M^{++}_{i,j} ### *)
ans1 =  Block[{extraPoints = 2},
              With[{aSeries = k+1, bSeries = k+1},
                   FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
                                                             PrecompKh[aSeries /. {k -> k1},
                                                                       bSeries /. {k -> k2}]],
                                                    Join[{aSeries}, PosFundEigenvalues[]],
                                                    Join[{bSeries}, PosFundEigenvalues[]]]]];

(* ### vv The unknown expression for the genus one evolution ### *)
TheorGenusOne[ans_, n1_, n2_] :=
    Module[{i,j},
           Sum[AA[i,j] (PosFundEigenvalues[]^n1)[[i]] (PosFundEigenvalues[]^n2)[[j]],
               {i, 1, 3},
               {j, 1, 3}] /. ans];

(* ### vv M^{--}_{i,j} ### *)
ans1 =  Block[{extraPoints = 2},
              With[{aSeries = -k-1, bSeries = -k-1},
                   FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
                                                             PrecompKh[aSeries /. {k -> k1},
                                                                       bSeries /. {k -> k2}]],
                                                    Join[{aSeries}, PosFundEigenvalues[]],
                                                    Join[{bSeries}, PosFundEigenvalues[]]]]];

(* ### vv M^{+++}_{i,j,k} ### *)
ans1 =  Block[{extraPoints = 2},
              With[{aSeries = k+1, bSeries = k+1, cSeries = 2 k+2},
                   FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2, k3},
                                                             PrecompKh[aSeries /. {k -> k1},
                                                                       bSeries /. {k -> k2},
                                                                       cSeries /. {k -> k3}]],
                                                    Join[{aSeries}, PosFundEigenvalues[]],
                                                    Join[{bSeries}, PosFundEigenvalues[]],
                                                    Join[{cSeries}, NegAdjEigenvalues[]]]]];

(* ### vv M^{++}_{i,j} ### *)
ans2 = Block[{extraPoints = 2},
             With[{aSeries = k+2, bSeries = k+2},
                   FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
                                                             PrecompKh[aSeries /. {k -> k1},
                                                                       bSeries /. {k -> k2},
                                                                       0]],
                                                    Join[{aSeries}, PosFundEigenvalues[]],
                                                    Join[{aSeries}, PosFundEigenvalues[]]]]];


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
				Table[{Table[1, {j, 1, n}], 2}, {i, 1, aa}]}]]]][q,t]];
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
ThreeStrandPro5[n_, insert_, aa_] := ThreeStrandPro3[n, insert, aa] =
    Module[{i, j},
	   Kh[PD[BR[3, Flatten[{{1,-1},{2,-2},
				insert,
				Table[{Table[1, {j, 1, n}], 2, 2}, {i, 1, aa}]}]]]
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

(* ### vv Snippet to precalculate Khovanov polynomial for certain knot families ### *)
fd = OpenWrite["/home/popolit/quicklisp/local-projects/cl-vknots/khovanov-pro2-1.txt",
	       FormatType -> InputForm
	      ];
Module[{i},
       For[i = 1, i < 15, i ++,
	   Module[{it = ThreeStrandPro2[5, {}, i]},
		  (* ### ^^ it is important that we first do time-intensive computation and only then check the time ### *)
		  Write[fd, i, " : ", DateString[], " : ", it]]]];
Close[fd];



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

Module[{cc, deltaK = 4},
       For[cc = 1, cc <= 9, cc ++,
	   (* ### vv Let's find 4 evolutions in all far quadrants ### *)
	   ansUL = Block[{extraPoints = 2},
			 With[{aSeries = -deltaK - k,
			       bSeries = deltaK + k},
			      FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
									ThirdNonToricKhovanovPrime[aSeries /. {k -> k1},
												   bSeries /. {k -> k2},
												   cc]],
							       Join[{aSeries}, PosFundEigenvalues[]],
							       Join[{bSeries}, PosFundEigenvalues[]]]]];
	   ansUR = Block[{extraPoints = 2},
			 With[{aSeries = deltaK + k,
			       bSeries = deltaK + k},
			      FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
									ThirdNonToricKhovanovPrime[aSeries /. {k -> k1},
												   bSeries /. {k -> k2},
												   cc]],
							       Join[{aSeries}, PosFundEigenvalues[]],
							       Join[{bSeries}, PosFundEigenvalues[]]]]];
	   ansLL = Block[{extraPoints = 2},
			 With[{aSeries = - deltaK - k,
			       bSeries = - deltaK - k},
			      FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2},
									ThirdNonToricKhovanovPrime[aSeries /. {k -> k1},
												   bSeries /. {k -> k2},
												   cc]],
							       Join[{aSeries}, PosFundEigenvalues[]],
							       Join[{bSeries}, PosFundEigenvalues[]]]]];
	   ansLR = Block[{extraPoints = 2},
			 With[{aSeries = deltaK + k,
			       bSeries = - deltaK - k},
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
	   Block[{maxAbs = 5},
                 (* signsRev[cc] = Module[{aa, bb}, *)
                 (*                    Table[KnotSignature[ThirdNonToricKhovanovPrimeBraid[-aa, -bb, -cc]], *)
                 (*                          {bb, maxAbs, -maxAbs, -1}, *)
                 (*                          {aa, -maxAbs, maxAbs}]]; *)
                 (* dets[cc] = Module[{aa, bb}, *)
                 (*                   Table[KnotDet[ThirdNonToricKhovanovPrimeBraid[-aa, -bb, -cc]], *)
                 (*                         {bb, maxAbs, -maxAbs, -1}, *)
                 (*                         {aa, -maxAbs, maxAbs}]]; *)
                 alexanders[cc] = Module[{aa, bb},
                                         Table[Alexander[ThirdNonToricKhovanovPrimeBraid[aa, bb, cc]][t],
                                               {bb, maxAbs, -maxAbs, -1},
                                               {aa, -maxAbs, maxAbs}]];
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
                                                (* ### vv The legend for the graph: ### *)
                                                (* ### vv A4 -- point is described by evolution in all four regions ### *)
                                                (* ### vv {T,Y,G,H}3 -- point is described by evolution in three regions ### *)
                                                (* ### vv               placement of the key on the keyboard tells, which ones ### *)
                                                (* ### vv {W,S,A,D}2 -- point is described by evolution in two regions, ### *)
                                                (* ### vv               again, which ones is intuitive from key positions ### *)
                                                (* ### vv {U,J,I,K}1 -- point is described by evolution in just one region ### *)
                                                (* ### vv ??         -- point is isolated, not described by any ### *)
                                                (* ### vv               of the asymptotic evolutions ### *)
						If[And[ulQ, urQ, llQ, lrQ],
						   "A4",
						   If[And[ulQ, urQ, llQ],
						      "H3",
						      If[And[ulQ, llQ, lrQ],
							 "T3",
							 If[And[ulQ, urQ, lrQ],
							    "Y3",
							    If[And[urQ, llQ, lrQ],
							       "G3",
							       If[And[ulQ, llQ],
								  "W2",
								  If[And[urQ, ulQ],
                                                                     "S2",
								     If[And[urQ, lrQ],
									"D2",
									If[And[llQ, lrQ],
									   "A2",
									   If[And[ulQ, lrQ],
									      "Q2",
									      If[And[llQ, urQ],
										 "E2",
										 If[ulQ,
										    "U1",
										    If[urQ,
										       "I1",
										       If[llQ,
											  "J1",
											  If[lrQ,
											     "K1",
											     "??"]]]]]]]]]]]]]]]],
					 {bb, maxAbs, -maxAbs, -1},
					 {aa, -maxAbs, maxAbs}]]]]];

Block[{cc = 9},
      Module[{aa, bb},
             Table[Subscript[picc[cc][[aa, bb]],
                             signs[cc][[aa, bb]]],
                   {bb, 1, Length[picc[cc]]},
                   {aa, 1, Length[picc[cc]]}] // TeXForm
            ]]

Block[{cc = 1},
      Module[{aa, bb},
             Table[Subscript[picc[cc][[aa, bb]],
                             signsRev[cc][[aa, bb]]],
                   {bb, 1, Length[picc[cc]]},
                   {aa, 1, Length[picc[cc]]}] // TeXForm
            ]]

Block[{cc = 1},
      Module[{aa, bb},
             Table[Subscript[picc[cc][[aa, bb]],
                             dets[cc][[aa, bb]]],
                   {bb, 1, Length[picc[cc]]},
                   {aa, 1, Length[picc[cc]]}] // TeXForm
            ]]

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

OrientationClusters[BraidSpec[Braid[2, a, {2, 1}, {4, 3}], Braid[2, b, {3, 1}, {4, 2}]]]


ConnectionScheme[BraidSpec[Braid[2, a, {2, 1}, {4, 3}], Braid[2, b, {3, 1}, {4, 2}]],
                 {0, 0}]

OrientationClusters[BraidSpec[Braid[3, a, {1, 2, 3}, {1, 2, 3}]]]

Braidosome[BraidSpec[Braid[3, a, {1, 2, 3}, {1, 2, 3}]],
           OriChoice[II[a, 0] -> 1, II[a, 1] -> 1, II[a, 2] -> 1],
           {4}]



PretzelKhovanov[{-3,0}]


Block[{extraPoints = 2},
      With[{aSeries = k,
            bSeries = k,
            cSeries = 2 k
           },
           FitFamilyWithEigenvaluesAdvanced[Function[{k1, k2, k3},
                                                     PretzelKhovanov[{aSeries /. {k -> k1},
                                                                      bSeries /. {k -> k2},
                                                                      cSeries /. {k -> k3}}]],
                                            {aSeries} ~Join~ PosFundEigenvalues[],
                                            {bSeries} ~Join~ PosFundEigenvalues[],
                                            {cSeries} ~Join~ PosAdjEigenvalues[]]]]

OrientationClusters[PretzelBraidSpec[2]]

PretzelBSWithParallelOrients[2]

Out[22]= {BraidSpec[Braid[2, a, {3, 1}, {6, 4}], Braid[2, b, {1, 2}, {4, 5}], 
 
>     Braid[2, c, {2, 3}, {5, 6}]], 
 
>    OriChoice[II[a, 0] -> 1, II[a, 1] -> 1, II[b, 0] -> -1, II[b, 1] -> -1, 
 
>     II[c, 0] -> 1, II[c, 1] -> -1]}

Out[21]= {BraidSpec[Braid[2, a, {2, 1}, {4, 3}], 
 
>     Braid[2, b, {1, 2}, {3, 4}]], 
 
>    OriChoice[II[a, 0] -> 1, II[a, 1] -> 1, II[b, 0] -> -1, II[b, 1] -> -1]}



spec = BraidSpec[Braid[3, a, {1, 2, 3}, {1, 2, 3}]];
residues = {0};
connScheme = ConnectionScheme[spec, residues];
connComps = ConnectedComponentsConnectionScheme[connScheme];
oriMasks = OrientationMasks[spec, connComps, residues];

oriMasks

OrientationClustersForAResidueChoice[BraidSpec[Braid[3, a, {1, 2, 3}, {1, 2, 3}]],
                                     {0}]




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

