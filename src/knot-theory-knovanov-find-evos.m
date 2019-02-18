
<< "knot-theory-knovanov-ev-utils.m";
<< "tuple-iterator.m";

(* ### vv Constants to make the series detection robust ### *)
CCCSeriesShiftParr = 2;
CCCSeriesShiftAntiParr = 2;
CCCExtraPoints = 2;
FindPretzelEvos[genus_] :=
    (* ### ^^ Find evolution coefficients for pretzel knots of genus `genus`. ### *)
    Module[{signIter = MkTupleIter @@ Map[AList @@ # &, Module[{i}, Table[{1,-1}, {i, 1, genus + 1}]]],
            fdlog = OpenWrite[CCCDataDir <> "/pretzel-evo-" <> ToString[genus+1] <> ".log"]},
           Iterate[{signs, signIter},
                   (* ### ^^ We loop over all the 2^n-tants ### *)
                   FindPretzelEvosForNTant[genus, signs, fdlog]];
           Close[fdlog]];
LoadPrecomputedKhovanovs[genus_, signs_, fdlog_] :=
    Module[{},
           ClearAll[PrecompKh]; (* ### << We want to free memory from the previous round ### *)
           (* ### vv Load the precomputed data ### *)
           Debugg[fdlog, "Loading data for: ("
                  <> StringRiffle[Map[ToString, signs], ", "] <> ") ..."];
           Get[CCCDataDir <> "/pretzel-khovanovs-" <> ToString[genus + 1]
               <> "-" <> StringRiffle[Map[ToString, signs], "-"] <> ".m"];
           Debugg[fdlog, " ... done!"]];
FindPretzelEvosForNTant[genus_, signs_, fdlog_] :=
    Module[{},
           LoadPrecomputedKhovanovs[genus, signs, fdlog];
           Debugg[fdlog, "Calculating evos for: ("
                  <> StringRiffle[Map[ToString, signs], ", "] <> ") ..."];
           Module[{seriesExprs = Append[Module[{i}, Table[signs[[i]] (k + If[ListQ[CCCSeriesShiftParr],
                                                                             CCCSeriesShiftParr[[i]],
                                                                             CCCSeriesShiftParr]),
                                                          {i, 1, genus}]],
                                        If[EvenQ[genus + 1],
                                           signs[[-1]] (k + If[ListQ[CCCSeriesShiftParr],
                                                               CCCSeriesShiftParr[[-1]],
                                                               CCCSeriesShiftParr]),
                                           signs[[-1]] 2 (k + CCCSeriesShiftAntiParr)]]},
                  (* Print[seriesExprs]; *)
                  (* Print[MkPrecompFunction[seriesExprs]]; *)
                  (* Print[MkPrecompEigSpecs[seriesExprs]]; *)
                  Module[{theAns = Block[{extraPoints = CCCExtraPoints},
                                         (FitFamilyWithEigenvaluesGradual
                                          @@ Prepend[MkPrecompEigSpecs[seriesExprs],
                                                     MkPrecompFunction[seriesExprs]])]},
                         Module[{fd = OpenWrite[CCCDataDir <> "/pretzel-kh-evo-" <> ToString[genus+1]
                                                <> "-" <> StringRiffle[Map[ToString, signs], "-"]
                                                <> ".m"]},
                                WriteString[fd, ToString[Factor[Simplify[theAns]], InputForm] <> ""];
                                Close[fd]]]];
           Debugg[fdlog, " done!"]];
MkPrecompFunction[seriesExprs_] :=                
    (Function @@ {Map[Symbol["k" <> ToString[#]] &, Range[1, Length[seriesExprs]]],
                  PrecompKh @@ MapIndexed[#1 /. {k ->
                                                 Symbol["k" <> ToString[#2[[1]]]]} &,
                                          seriesExprs]});
MkPrecompEigSpecs[seriesExprs_] :=
    Append[Map[Join[{#}, PosFundEigenvalues[]] &,
               seriesExprs[[;;-2]]],
           Join[{seriesExprs[[-1]]},
                If[EvenQ[Length[seriesExprs]],
                   PosFundEigenvalues[],
                   NegAdjEigenvalues[]]]];
N3SliceFit1[a_, b_] :=
    Block[{kA = a,
           kB = a,
           kC = b,
           CCCEigenvaluesCritLength = Null,
           extraPoints = 2},
          LoadPrecomputedKhovanovs[2, {1,1,-1}, Null];
          FitFamilyWithEigenvaluesGradual[Function[{k1, k2},
                                                   PrecompKh[k1 + kA, k2 + kB, kC]],
                                          Prepend[PosFundEigenvalues[], k + kA],
                                          Prepend[PosFundEigenvalues[], k + kB]]];
N3SliceFit2[a_, b_] :=
    Block[{kA = a,
           kB = a,
           kC = b,
           CCCEigenvaluesCritLength = Null,
           extraPoints = 2},
          LoadPrecomputedKhovanovs[2, {-1,-1,1}, Null];
          FitFamilyWithEigenvaluesGradual[Function[{k1, k2},
                                                   PrecompKh[-(k1 + kA), -(k2 + kB), kC]],
                                          Prepend[PosFundEigenvalues[], -(k + kA)],
                                          Prepend[PosFundEigenvalues[], -(k + kB)]]];
N3SliceFit2Assign[a_, b_] :=
    Set @@ Rule[n3sliceFit2[b], N3SliceFit2[a, b]];
N3SliceFit3[a_, b_] :=
    Block[{kA = a,
           kB = b,
           kC = a,
           CCCEigenvaluesCritLength = Null,
           extraPoints = 2},
          LoadPrecomputedKhovanovs[2, {1,-1,1}, Null];
          FitFamilyWithEigenvaluesGradual[Function[{k1, k2},
                                                   Simplify[PrecompKh[k1 + kA, kB, 2 k2 + kC]]],
                                          Prepend[PosFundEigenvalues[], k + kA],
                                          Prepend[NegAdjEigenvalues[], 2 k + kC]]];
N3SliceFit3Assign[a_, b_] :=
    Set @@ Rule[n3sliceFit3[b], N3SliceFit3[a, b]];
N3SliceFit4[a_, b_] :=
    Block[{kA = b,
           kB = a,
           kC = a,
           CCCEigenvaluesCritLength = Null,
           extraPoints = 2},
          LoadPrecomputedKhovanovs[2, {-1,1,1}, Null];
          FitFamilyWithEigenvaluesGradual[Function[{k1, k2},
                                                   Simplify[PrecompKh[kA, k1 + kB, 2 k2 + kC]]],
                                          Prepend[PosFundEigenvalues[], k + kB],
                                          Prepend[NegAdjEigenvalues[], 2 k + kC]]];
N3SliceFit4Assign[a_, b_] :=
    Set @@ Rule[n3sliceFit4[b], N3SliceFit4[a, b]];
N3SliceFit5[a_, b_] :=
    Block[{kA = b,
           kB = a,
           kC = a,
           CCCEigenvaluesCritLength = Null,
           extraPoints = 2},
          LoadPrecomputedKhovanovs[2, {1,-1,-1}, Null];
          FitFamilyWithEigenvaluesGradual[Function[{k1, k2},
                                                   Simplify[PrecompKh[kA, -k1 - kB, -2 k2 - kC]]],
                                          Prepend[PosFundEigenvalues[], - k - kB],
                                          Prepend[NegAdjEigenvalues[], -2 k - kC]]];
N3SliceFit5Assign[a_, b_] :=
    Set @@ Rule[n3sliceFit5[b], N3SliceFit5[a, b]];
N3SliceFit6[a_, b_] :=
    Block[{kA = a,
           kB = b,
           kC = a,
           CCCEigenvaluesCritLength = Null,
           extraPoints = 2},
          LoadPrecomputedKhovanovs[2, {-1,1,-1}, Null];
          FitFamilyWithEigenvaluesGradual[Function[{k1, k2},
                                                   Simplify[PrecompKh[-k1 - kA, kB, -2 k2 - kC]]],
                                          Prepend[PosFundEigenvalues[], - k - kA],
                                          Prepend[NegAdjEigenvalues[], -2 k - kC]]];
N3SliceFit6Assign[a_, b_] :=
    Set @@ Rule[n3sliceFit6[b], N3SliceFit6[a, b]];

(* FindPretzelEvosForNTant[1, {-1, -1}, Null] *)

N3SliceFit2[3, 2]

Iterate[{l, MkRangeIter[1, 5]},
        N3SliceFit2Assign[2 l + 1, 2 l]];

Iterate[{l, MkRangeIter[1, 5]},
        N3SliceFit3Assign[2 (l + 1), -1 - l]];

Block[{l = 7},
      N3SliceFit3Assign[2 (l + 1), -1 - l]];

Block[{shift = 4},
      Iterate[{l, MkRangeIter[1, 7]},
              N3SliceFit4Assign[Floor[(l + shift)/2] * 2, -1 - l]]]

Block[{shift = 4},
      Iterate[{l, MkRangeIter[1, 7]},
              N3SliceFit5Assign[Floor[(l + shift)/2] * 2, 1 + l]]]

Block[{shift = 4},
      Iterate[{l, MkRangeIter[1, 7]},
              N3SliceFit6Assign[Floor[(l + shift)/2] * 2, 1 + l]]]


Block[{shift = 4, l = 1},
      N3SliceFit5[Floor[(l + shift)/2] * 2, 1 + l]]

Block[{shift = 4, l = 11},
      PrecompKh[l + 1, - 0 - Floor[(l + shift)/2] * 2, - 2 0 - Floor[(l + shift)/2] * 2]]


n3sliceFit3[-11] // InputForm


LoadPrecomputedKhovanovs[2, {1,-1,1}, Null];

Block[{shift = 4, l = 8},
      Simplify[PrecompKh[Floor[(l + shift)/2] * 2 + 5, -1 - l, Floor[(l + shift)/2] * 2 + 2 2]]]

n3sliceFit3[-10] // InputForm


Block[{l = 1, shift = 4},
      N3SliceFit3Assign[Floor[(l + shift)/2] * 2, -1 - l]]

(* hypotn3sliceFit3[-5] = *)
(*     <|{q, 1} -> (1 - 2*q^2*t - q^2*t^2 + q^6*t^3 - q^8*t^4)/ *)
(*     (q^6*(-1 + q^2*t)^2*(1 + q^2*t)), {q, 1/(q^2*t)} ->  *)
(*     (1 - q^2*t + q^4*t + q^4*t^2 - q^6*t^2 + q^8*t^3 - q^8*t^4 + q^10*t^5 -  *)
(*      q^12*t^5 - 2*q^12*t^6 + q^14*t^6 + q^14*t^7 - 2*q^16*t^7 - q^16*t^8 +  *)
(*      q^18*t^8 - q^20*t^9 + q^20*t^10 + q^20*t^11 - q^22*t^11 + q^24*t^11 -  *)
(*      q^22*t^12 + 2*q^24*t^12 - q^26*t^12 + q^24*t^13 - q^26*t^13 + q^28*t^13 +  *)
(*      q^28*t^14)/(q^16*t^5*(-1 + q^2*t)^2*(1 + q^2*t)),  *)
(*     {q^3*t, 1} -> (1 + q^4*t)/(q^14*t^3*(-1 + q^2*t)^2*(1 + q^2*t)),  *)
(*     {q^3*t, 1/(q^2*t)} -> (1 - t - 2*q^2*t - q^4*t^2 - q^4*t^3 + 2*q^6*t^3 -  *)
(*                            2*q^8*t^4)/(2*q^6*(-1 + q^2*t)^2*(1 + q^2*t)), {-(q^3*t), 1} -> 0,  *)
(*     {-(q^3*t), 1/(q^2*t)} -> (1 + t)/(2*q^6 + 2*q^8*t)|>; *)

NEWn3sliceFit3[-6] =
    <|{q, 1} -> (1 - 2*q^2*t - q^2*t^2 + q^6*t^3 - q^8*t^4)/
    (q^7*(-1 + q^2*t)^2*(1 + q^2*t)), {q, 1/(q^2*t)} -> 
    (1 + q^2 - q^4*t - q^4*t^2 + q^6*t^3 + q^8*t^3 - q^10*t^5 + q^12*t^6 - 
     q^14*t^6 - 2*q^14*t^7 + q^16*t^7 + q^16*t^8 - 2*q^18*t^8 - q^18*t^9 + 
     q^20*t^9 - q^22*t^10 + q^22*t^11 + q^22*t^12 - q^24*t^12 + q^26*t^12 - 
     q^24*t^13 + 2*q^26*t^13 - q^28*t^13 + q^26*t^14 - 2*q^28*t^14 + 
     q^30*t^14 - q^28*t^15 + 2*q^30*t^15 - q^32*t^15 + q^30*t^16 - q^32*t^16 + 
     q^34*t^16 + q^34*t^17)/(q^19*t^6*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1} -> (1 + t - 2*q^2*t + q^4*t^2 + q^4*t^3 + 2*q^6*t^3)/
    (2*q^19*t^6*(-1 + q^2*t)^2*(1 + q^2*t)), {q^3*t, 1/(q^2*t)} -> 
    (1 - t - 2*q^2*t - q^4*t^2 - q^4*t^3 + 2*q^6*t^3 - 2*q^8*t^4)/
    (2*q^7*(-1 + q^2*t)^2*(1 + q^2*t)), {-(q^3*t), 1} -> 
    (1 + t)/(2*q^19*t^6 + 2*q^21*t^7), {-(q^3*t), 1/(q^2*t)} -> 
    (1 + t)/(2*q^7 + 2*q^9*t)|>;
NEWn3sliceFit3[-7] =
    <|{q, 1} -> (1 - 2*q^2*t - q^2*t^2 + q^6*t^3 - q^8*t^4)/
    (q^8*(-1 + q^2*t)^2*(1 + q^2*t)), {q, 1/(q^2*t)} -> 
    (1 - q^2*t + q^4*t + q^4*t^2 - q^6*t^2 + q^8*t^3 - q^12*t^6 + q^14*t^7 - 
     q^16*t^7 - 2*q^16*t^8 + q^18*t^8 + q^18*t^9 - 2*q^20*t^9 - q^20*t^10 + 
     q^22*t^10 - q^24*t^11 + q^28*t^14 + q^28*t^15 - q^30*t^15 + q^32*t^15 - 
     q^30*t^16 + 2*q^32*t^16 - q^34*t^16 + q^32*t^17 - q^34*t^17 + q^36*t^17 + 
     q^36*t^18)/(q^22*t^7*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1} -> (1 + q^4*t)/(q^20*t^5*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1/(q^2*t)} -> (1 - t - 2*q^2*t - q^4*t^2 - q^4*t^3 + 2*q^6*t^3 - 
                           2*q^8*t^4)/(2*q^8*(-1 + q^2*t)^2*(1 + q^2*t)), {-(q^3*t), 1} -> 0, 
    {-(q^3*t), 1/(q^2*t)} -> (1 + t)/(2*q^8 + 2*q^10*t)|>;
n3sliceFit3[-8] =
    <|{q, 1} -> (1 - 2*q^2*t - q^2*t^2 + q^6*t^3 - q^8*t^4)/
    (q^9*(-1 + q^2*t)^2*(1 + q^2*t)), {q, 1/(q^2*t)} -> 
    (1 + q^2 - q^4*t - q^4*t^2 + q^6*t^3 + q^8*t^3 - q^14*t^7 + q^16*t^8 - 
     q^18*t^8 - 2*q^18*t^9 + q^20*t^9 + q^20*t^10 - 2*q^22*t^10 - q^22*t^11 + 
     q^24*t^11 - q^26*t^12 + q^30*t^15 + q^30*t^16 - q^32*t^16 + q^34*t^16 - 
     q^32*t^17 + 2*q^34*t^17 - q^36*t^17 + q^34*t^18 - 2*q^36*t^18 + 
     q^38*t^18 - q^36*t^19 + 2*q^38*t^19 - q^40*t^19 + q^38*t^20 - q^40*t^20 + 
     q^42*t^20 + q^42*t^21)/(q^25*t^8*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1} -> (1 + t - 2*q^2*t + q^4*t^2 + q^4*t^3 + 2*q^6*t^3)/
    (2*q^25*t^8*(-1 + q^2*t)^2*(1 + q^2*t)), {q^3*t, 1/(q^2*t)} -> 
    (1 - t - 2*q^2*t - q^4*t^2 - q^4*t^3 + 2*q^6*t^3 - 2*q^8*t^4)/
    (2*q^9*(-1 + q^2*t)^2*(1 + q^2*t)), {-(q^3*t), 1} -> 
    (1 + t)/(2*q^25*t^8 + 2*q^27*t^9), {-(q^3*t), 1/(q^2*t)} -> 
    (1 + t)/(2*q^9 + 2*q^11*t)|>;
n3sliceFit3[-2] = 
    <|{q, 1} -> (1 - 2*q^2*t - q^2*t^2 + q^6*t^3 - q^8*t^4)/
    (q^3*(-1 + q^2*t)^2*(1 + q^2*t)), {q, 1/(q^2*t)} -> 
    (1 + q^2 - q^2*t - q^4*t - q^6*t^2 + 2*q^8*t^3 + q^6*t^4 - q^10*t^4 - 
     q^8*t^5 + q^10*t^5 + q^10*t^6 - 2*q^12*t^6 - q^12*t^7 + 2*q^14*t^7 - 
     q^16*t^7 + q^14*t^8 - q^16*t^8 + q^18*t^8 + q^18*t^9)/
    (q^7*t^2*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1} -> (1 + t - 2*q^2*t + q^4*t^2 + q^4*t^3 + 2*q^6*t^3)/
    (2*q^7*t^2*(-1 + q^2*t)^2*(1 + q^2*t)), {q^3*t, 1/(q^2*t)} -> 
    (1 - t - 2*q^2*t - q^4*t^2 - q^4*t^3 + 2*q^6*t^3 - 2*q^8*t^4)/
    (2*q^3*(-1 + q^2*t)^2*(1 + q^2*t)), {-(q^3*t), 1} -> 
    (1 + t)/(2*q^7*t^2 + 2*q^9*t^3), {-(q^3*t), 1/(q^2*t)} -> 
    (1 + t)/(2*q^3 + 2*q^5*t)|>;
n3sliceFit3[-3] =
    <|{q, 1} -> (1 - 2*q^2*t - q^2*t^2 + q^6*t^3 - q^8*t^4)/
    (q^4*(-1 + q^2*t)^2*(1 + q^2*t)), {q, 1/(q^2*t)} -> 
    (1 - q^2*t + q^4*t - q^6*t^2 + q^6*t^3 - 2*q^8*t^4 + q^10*t^4 + q^10*t^5 - 
     2*q^12*t^5 + q^14*t^6 + q^12*t^7 - q^14*t^7 - q^14*t^8 + 2*q^16*t^8 - 
     q^18*t^8 + q^16*t^9 - q^18*t^9 + q^20*t^9 + q^20*t^10)/
    (q^10*t^3*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1} -> (1 + q^4*t)/(q^8*t*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1/(q^2*t)} -> (1 - t - 2*q^2*t - q^4*t^2 - q^4*t^3 + 2*q^6*t^3 - 
                           2*q^8*t^4)/(2*q^4*(-1 + q^2*t)^2*(1 + q^2*t)), {-(q^3*t), 1} -> 0, 
    {-(q^3*t), 1/(q^2*t)} -> (1 + t)/(2*q^4 + 2*q^6*t)|>;
n3sliceFit3[-4] =
    <|{q, 1} -> (1 - 2*q^2*t - q^2*t^2 + q^6*t^3 - q^8*t^4)/
    (q^5*(-1 + q^2*t)^2*(1 + q^2*t)), {q, 1/(q^2*t)} -> 
    (1 + q^2 - q^4*t - q^4*t^2 + q^8*t^3 + q^8*t^4 - q^10*t^4 - 2*q^10*t^5 + 
     q^12*t^5 + q^12*t^6 - 2*q^14*t^6 + q^16*t^7 + q^14*t^8 - q^16*t^8 - 
     q^16*t^9 + 2*q^18*t^9 - q^20*t^9 + q^18*t^10 - 2*q^20*t^10 + q^22*t^10 - 
     q^20*t^11 + 2*q^22*t^11 - q^24*t^11 + q^22*t^12 - q^24*t^12 + q^26*t^12 + 
     q^26*t^13)/(q^13*t^4*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1} -> (1 + t - 2*q^2*t + q^4*t^2 + q^4*t^3 + 2*q^6*t^3)/
    (2*q^13*t^4*(-1 + q^2*t)^2*(1 + q^2*t)), {q^3*t, 1/(q^2*t)} -> 
    (1 - t - 2*q^2*t - q^4*t^2 - q^4*t^3 + 2*q^6*t^3 - 2*q^8*t^4)/
    (2*q^5*(-1 + q^2*t)^2*(1 + q^2*t)), {-(q^3*t), 1} -> 
    (1 + t)/(2*q^13*t^4 + 2*q^15*t^5), {-(q^3*t), 1/(q^2*t)} -> 
    (1 + t)/(2*q^5 + 2*q^7*t)|>;
n3sliceFit3[-5] =
    <|{q, 1} -> (1 - 2*q^2*t - q^2*t^2 + q^6*t^3 - q^8*t^4)/
    (q^6*(-1 + q^2*t)^2*(1 + q^2*t)), {q, 1/(q^2*t)} -> 
    (1 - q^2*t + q^4*t + q^4*t^2 - q^6*t^2 + q^8*t^3 - q^8*t^4 + q^10*t^5 - 
     q^12*t^5 - 2*q^12*t^6 + q^14*t^6 + q^14*t^7 - 2*q^16*t^7 - q^16*t^8 + 
     q^18*t^8 - q^20*t^9 + q^20*t^10 + q^20*t^11 - q^22*t^11 + q^24*t^11 - 
     q^22*t^12 + 2*q^24*t^12 - q^26*t^12 + q^24*t^13 - q^26*t^13 + q^28*t^13 + 
     q^28*t^14)/(q^16*t^5*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1} -> (1 + q^4*t)/(q^14*t^3*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1/(q^2*t)} -> (1 - t - 2*q^2*t - q^4*t^2 - q^4*t^3 + 2*q^6*t^3 - 
                           2*q^8*t^4)/(2*q^6*(-1 + q^2*t)^2*(1 + q^2*t)), {-(q^3*t), 1} -> 0, 
    {-(q^3*t), 1/(q^2*t)} -> (1 + t)/(2*q^6 + 2*q^8*t)|>;
n3sliceFit3[-6] =
            <|{q, 1} -> (1 - 2*q^2*t - q^2*t^2 + q^6*t^3 - q^8*t^4)/
            (q^7*(-1 + q^2*t)^2*(1 + q^2*t)), {q, 1/(q^2*t)} -> 
            (1 + q^2 - q^4*t - q^4*t^2 + q^6*t^3 + q^8*t^3 - q^10*t^5 + q^12*t^6 - 
             q^14*t^6 - 2*q^14*t^7 + q^16*t^7 + q^16*t^8 - 2*q^18*t^8 - q^18*t^9 + 
             q^20*t^9 - q^22*t^10 + q^22*t^11 + q^22*t^12 - q^24*t^12 + q^26*t^12 - 
             q^24*t^13 + 2*q^26*t^13 - q^28*t^13 + q^26*t^14 - 2*q^28*t^14 + 
             q^30*t^14 - q^28*t^15 + 2*q^30*t^15 - q^32*t^15 + q^30*t^16 - q^32*t^16 + 
             q^34*t^16 + q^34*t^17)/(q^19*t^6*(-1 + q^2*t)^2*(1 + q^2*t)), 
            {q^3*t, 1} -> (1 + t - 2*q^2*t + q^4*t^2 + q^4*t^3 + 2*q^6*t^3)/
            (2*q^19*t^6*(-1 + q^2*t)^2*(1 + q^2*t)), {q^3*t, 1/(q^2*t)} -> 
            (1 - t - 2*q^2*t - q^4*t^2 - q^4*t^3 + 2*q^6*t^3 - 2*q^8*t^4)/
            (2*q^7*(-1 + q^2*t)^2*(1 + q^2*t)), {-(q^3*t), 1} -> 
            (1 + t)/(2*q^19*t^6 + 2*q^21*t^7), {-(q^3*t), 1/(q^2*t)} -> 
            (1 + t)/(2*q^7 + 2*q^9*t)|>;
n3sliceFit3[-7] =
    <|{q, 1} -> (1 - 2*q^2*t - q^2*t^2 + q^6*t^3 - q^8*t^4)/
    (q^8*(-1 + q^2*t)^2*(1 + q^2*t)), {q, 1/(q^2*t)} -> 
    (1 - q^2*t + q^4*t + q^4*t^2 - q^6*t^2 + q^8*t^3 - q^12*t^6 + q^14*t^7 - 
     q^16*t^7 - 2*q^16*t^8 + q^18*t^8 + q^18*t^9 - 2*q^20*t^9 - q^20*t^10 + 
     q^22*t^10 - q^24*t^11 + q^28*t^14 + q^28*t^15 - q^30*t^15 + q^32*t^15 - 
     q^30*t^16 + 2*q^32*t^16 - q^34*t^16 + q^32*t^17 - q^34*t^17 + q^36*t^17 + 
     q^36*t^18)/(q^22*t^7*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1} -> (1 + q^4*t)/(q^20*t^5*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1/(q^2*t)} -> (1 - t - 2*q^2*t - q^4*t^2 - q^4*t^3 + 2*q^6*t^3 - 
                           2*q^8*t^4)/(2*q^8*(-1 + q^2*t)^2*(1 + q^2*t)), {-(q^3*t), 1} -> 0, 
    {-(q^3*t), 1/(q^2*t)} -> (1 + t)/(2*q^8 + 2*q^10*t)|>;
n3sliceFit3[-10] =
    <|{q, 1} -> (1 - 2*q^2*t - q^2*t^2 + q^6*t^3 - q^8*t^4)/
    (q^11*(-1 + q^2*t)^2*(1 + q^2*t)), {q, 1/(q^2*t)} -> 
    (1 + q^2 - q^4*t - q^4*t^2 + q^6*t^3 + q^8*t^3 - q^18*t^9 + q^20*t^10 - 
     q^22*t^10 - 2*q^22*t^11 + q^24*t^11 + q^24*t^12 - 2*q^26*t^12 - 
     q^26*t^13 + q^28*t^13 - q^30*t^14 + q^38*t^19 + q^38*t^20 - q^40*t^20 + 
     q^42*t^20 - q^40*t^21 + 2*q^42*t^21 - q^44*t^21 + q^42*t^22 - 
     2*q^44*t^22 + q^46*t^22 - q^44*t^23 + 2*q^46*t^23 - q^48*t^23 + 
     q^46*t^24 - q^48*t^24 + q^50*t^24 + q^50*t^25)/
    (q^31*t^10*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1} -> (1 + t - 2*q^2*t + q^4*t^2 + q^4*t^3 + 2*q^6*t^3)/
    (2*q^31*t^10*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1/(q^2*t)} -> (1 - t - 2*q^2*t - q^4*t^2 - q^4*t^3 + 2*q^6*t^3 - 
                           2*q^8*t^4)/(2*q^11*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {-(q^3*t), 1} -> (1 + t)/(2*q^31*t^10*(1 + q^2*t)), 
    {-(q^3*t), 1/(q^2*t)} -> (1 + t)/(2*q^11 + 2*q^13*t)|>;
n3sliceFit3[-9] =
    <|{q, 1} -> (1 - 2*q^2*t - q^2*t^2 + q^6*t^3 - q^8*t^4)/
    (q^10*(-1 + q^2*t)^2*(1 + q^2*t)), {q, 1/(q^2*t)} -> 
    (1 - q^2*t + q^4*t + q^4*t^2 - q^6*t^2 + q^8*t^3 - q^16*t^8 + q^18*t^9 - 
     q^20*t^9 - 2*q^20*t^10 + q^22*t^10 + q^22*t^11 - 2*q^24*t^11 - 
     q^24*t^12 + q^26*t^12 - q^28*t^13 + q^36*t^18 + q^36*t^19 - q^38*t^19 + 
     q^40*t^19 - q^38*t^20 + 2*q^40*t^20 - q^42*t^20 + q^40*t^21 - q^42*t^21 + 
     q^44*t^21 + q^44*t^22)/(q^28*t^9*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1} -> (1 + q^4*t)/(q^26*t^7*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1/(q^2*t)} -> (1 - t - 2*q^2*t - q^4*t^2 - q^4*t^3 + 2*q^6*t^3 - 
                           2*q^8*t^4)/(2*q^10*(-1 + q^2*t)^2*(1 + q^2*t)), {-(q^3*t), 1} -> 0, 
    {-(q^3*t), 1/(q^2*t)} -> (1 + t)/(2*q^10 + 2*q^12*t)|>;
n3sliceFit3[-11] =
    <|{q, 1} -> (1 - 2*q^2*t - q^2*t^2 + q^6*t^3 - q^8*t^4)/
    (q^12*(-1 + q^2*t)^2*(1 + q^2*t)), {q, 1/(q^2*t)} -> 
    (1 - q^2*t + q^4*t + q^4*t^2 - q^6*t^2 + q^8*t^3 - q^20*t^10 + q^22*t^11 - 
     q^24*t^11 - 2*q^24*t^12 + q^26*t^12 + q^26*t^13 - 2*q^28*t^13 - 
     q^28*t^14 + q^30*t^14 - q^32*t^15 + q^44*t^22 + q^44*t^23 - q^46*t^23 + 
     q^48*t^23 - q^46*t^24 + 2*q^48*t^24 - q^50*t^24 + q^48*t^25 - q^50*t^25 + 
     q^52*t^25 + q^52*t^26)/(q^34*t^11*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1} -> (1 + q^4*t)/(q^32*t^9*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, 1/(q^2*t)} -> (1 - t - 2*q^2*t - q^4*t^2 - q^4*t^3 + 2*q^6*t^3 - 
                           2*q^8*t^4)/(2*q^12*(-1 + q^2*t)^2*(1 + q^2*t)), {-(q^3*t), 1} -> 0, 
    {-(q^3*t), 1/(q^2*t)} -> (1 + t)/(2*q^12 + 2*q^14*t)|>;

NEWn3sliceFit3[-7] - n3sliceFit3[-7]
           

(* Block[{CCCEigenvaluesCritLength = Null, *)
(*        CCCSeriesShiftParr = {2, 9}, *)
(*        CCCSeriesShiftAntiParr = 5, *)
(*       FindPretzelEvosForNTant[2, {-1,1,1}, Null]] *)

(* ### vv Figure out evolutions in planes in the exceptional region inside +++ region for genus 2 pretzel knots ### *)
Module[{k},
       For[k = 7, k <= 8, k ++,
           Timing[n3sliceFit1[-2 k] = N3SliceFit1[1 + 2 k, -2 k]]]];

Simplify[n3sliceFit1[-18]] // InputForm

n3sliceFit1[-16] =
    <|{q, q} -> (1 + q^2 - q^4*t - q^4*t^2 + q^6*t^3 + q^8*t^3 - q^30*t^15 + 
                 q^32*t^16 - q^34*t^16 - 2*q^34*t^17 + q^36*t^17 + q^36*t^18 - 2*q^38*t^18 - 
                 q^38*t^19 + q^40*t^19 - q^42*t^20 + q^62*t^31 + q^62*t^32 - q^64*t^32 + 
                 q^66*t^32 - q^64*t^33 + 2*q^66*t^33 - q^68*t^33 + q^66*t^34 - 2*q^68*t^34 + 
                 q^70*t^34 - q^68*t^35 + 2*q^70*t^35 - q^72*t^35 + q^70*t^36 - q^72*t^36 + 
                 q^74*t^36 + q^74*t^37)/((-1 + q^2*t)^2*(q + q^3*t)), 
    {q, q^3*t} -> (q^31*t^16 - q^31*t^17 - 2*q^33*t^17 - q^35*t^18 - q^35*t^19 + 
                   2*q^37*t^19 - 2*q^39*t^20)/(2*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q, -(q^3*t)} -> (q^31*t^16 + q^31*t^17)/(2 + 2*q^2*t), 
    {q^3*t, q} -> (q^31*t^16 - q^31*t^17 - 2*q^33*t^17 - q^35*t^18 - q^35*t^19 + 
                   2*q^37*t^19 - 2*q^39*t^20)/(2*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, q^3*t} -> (1 + t - 3*q^2*t + q^2*t^2 + 4*q^4*t^2)/
    (4*q*(-1 + q^2*t)^2), {q^3*t, -(q^3*t)} -> (1 + t)/(4*q + 4*q^3*t), 
    {-(q^3*t), q} -> (q^31*t^16 + q^31*t^17)/(2 + 2*q^2*t), 
    {-(q^3*t), q^3*t} -> (1 + t)/(4*q + 4*q^3*t), 
    {-(q^3*t), -(q^3*t)} -> (1 + t)/(4*q + 4*q^3*t)|>;
n3sliceFit1[-14] =
    <|{q, q} -> (1 + q^2 - q^4*t - q^4*t^2 + q^6*t^3 + q^8*t^3 - q^26*t^13 + 
                 q^28*t^14 - q^30*t^14 - 2*q^30*t^15 + q^32*t^15 + q^32*t^16 - 2*q^34*t^16 - 
                 q^34*t^17 + q^36*t^17 - q^38*t^18 + q^54*t^27 + q^54*t^28 - q^56*t^28 + 
                 q^58*t^28 - q^56*t^29 + 2*q^58*t^29 - q^60*t^29 + q^58*t^30 - 2*q^60*t^30 + 
                 q^62*t^30 - q^60*t^31 + 2*q^62*t^31 - q^64*t^31 + q^62*t^32 - q^64*t^32 + 
                 q^66*t^32 + q^66*t^33)/((-1 + q^2*t)^2*(q + q^3*t)), 
    {q, q^3*t} -> (q^27*t^14 - q^27*t^15 - 2*q^29*t^15 - q^31*t^16 - q^31*t^17 + 
                   2*q^33*t^17 - 2*q^35*t^18)/(2*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q, -(q^3*t)} -> (q^27*t^14 + q^27*t^15)/(2 + 2*q^2*t), 
    {q^3*t, q} -> (q^27*t^14 - q^27*t^15 - 2*q^29*t^15 - q^31*t^16 - q^31*t^17 + 
                   2*q^33*t^17 - 2*q^35*t^18)/(2*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, q^3*t} -> (1 + t - 3*q^2*t + q^2*t^2 + 4*q^4*t^2)/
    (4*q*(-1 + q^2*t)^2), {q^3*t, -(q^3*t)} -> (1 + t)/(4*q + 4*q^3*t), 
    {-(q^3*t), q} -> (q^27*t^14 + q^27*t^15)/(2 + 2*q^2*t), 
    {-(q^3*t), q^3*t} -> (1 + t)/(4*q + 4*q^3*t), 
    {-(q^3*t), -(q^3*t)} -> (1 + t)/(4*q + 4*q^3*t)|>;
n3sliceFit1[-12] =
    <|{q, q} -> (1 + q^2 - q^4*t - q^4*t^2 + q^6*t^3 + q^8*t^3 - q^22*t^11 + 
                 q^24*t^12 - q^26*t^12 - 2*q^26*t^13 + q^28*t^13 + q^28*t^14 - 
                 2*q^30*t^14 - q^30*t^15 + q^32*t^15 - q^34*t^16 + q^46*t^23 + q^46*t^24 - 
                 q^48*t^24 + q^50*t^24 - q^48*t^25 + 2*q^50*t^25 - q^52*t^25 + q^50*t^26 - 
                 2*q^52*t^26 + q^54*t^26 - q^52*t^27 + 2*q^54*t^27 - q^56*t^27 + 
                 q^54*t^28 - q^56*t^28 + q^58*t^28 + q^58*t^29)/
    ((-1 + q^2*t)^2*(q + q^3*t)), {q, q^3*t} -> 
    (q^23*t^12 - q^23*t^13 - 2*q^25*t^13 - q^27*t^14 - q^27*t^15 + 
     2*q^29*t^15 - 2*q^31*t^16)/(2*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q, -(q^3*t)} -> (q^23*t^12 + q^23*t^13)/(2 + 2*q^2*t), 
    {q^3*t, q} -> (q^23*t^12 - q^23*t^13 - 2*q^25*t^13 - q^27*t^14 - q^27*t^15 + 
                   2*q^29*t^15 - 2*q^31*t^16)/(2*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, q^3*t} -> (1 + t - 3*q^2*t + q^2*t^2 + 4*q^4*t^2)/
    (4*q*(-1 + q^2*t)^2), {q^3*t, -(q^3*t)} -> (1 + t)/(4*q + 4*q^3*t), 
    {-(q^3*t), q} -> (q^23*t^12 + q^23*t^13)/(2 + 2*q^2*t), 
    {-(q^3*t), q^3*t} -> (1 + t)/(4*q + 4*q^3*t), 
    {-(q^3*t), -(q^3*t)} -> (1 + t)/(4*q + 4*q^3*t)|>;
n3sliceFit1[-10] =
    <|{q, q} -> (1 + q^2 - q^4*t - q^4*t^2 + q^6*t^3 + q^8*t^3 - q^18*t^9 + 
                 q^20*t^10 - q^22*t^10 - 2*q^22*t^11 + q^24*t^11 + q^24*t^12 - 
                 2*q^26*t^12 - q^26*t^13 + q^28*t^13 - q^30*t^14 + q^38*t^19 + q^38*t^20 - 
                 q^40*t^20 + q^42*t^20 - q^40*t^21 + 2*q^42*t^21 - q^44*t^21 + q^42*t^22 - 
                 2*q^44*t^22 + q^46*t^22 - q^44*t^23 + 2*q^46*t^23 - q^48*t^23 + 
                 q^46*t^24 - q^48*t^24 + q^50*t^24 + q^50*t^25)/
    ((-1 + q^2*t)^2*(q + q^3*t)), {q, q^3*t} -> 
    (q^19*t^10 - q^19*t^11 - 2*q^21*t^11 - q^23*t^12 - q^23*t^13 + 
     2*q^25*t^13 - 2*q^27*t^14)/(2*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q, -(q^3*t)} -> (q^19*t^10 + q^19*t^11)/(2 + 2*q^2*t), 
    {q^3*t, q} -> (q^19*t^10 - q^19*t^11 - 2*q^21*t^11 - q^23*t^12 - q^23*t^13 + 
                   2*q^25*t^13 - 2*q^27*t^14)/(2*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, q^3*t} -> (1 + t - 3*q^2*t + q^2*t^2 + 4*q^4*t^2)/
    (4*q*(-1 + q^2*t)^2), {q^3*t, -(q^3*t)} -> (1 + t)/(4*q + 4*q^3*t), 
    {-(q^3*t), q} -> (q^19*t^10 + q^19*t^11)/(2 + 2*q^2*t), 
    {-(q^3*t), q^3*t} -> (1 + t)/(4*q + 4*q^3*t), 
    {-(q^3*t), -(q^3*t)} -> (1 + t)/(4*q + 4*q^3*t)|>;
n3sliceFit1[-8] =
    <|{q, q} -> (1 + q^2 - q^4*t - q^4*t^2 + q^6*t^3 + q^8*t^3 - q^14*t^7 + 
                 q^16*t^8 - q^18*t^8 - 2*q^18*t^9 + q^20*t^9 + q^20*t^10 - 2*q^22*t^10 - 
                 q^22*t^11 + q^24*t^11 - q^26*t^12 + q^30*t^15 + q^30*t^16 - q^32*t^16 + 
                 q^34*t^16 - q^32*t^17 + 2*q^34*t^17 - q^36*t^17 + q^34*t^18 - 
                 2*q^36*t^18 + q^38*t^18 - q^36*t^19 + 2*q^38*t^19 - q^40*t^19 + 
                 q^38*t^20 - q^40*t^20 + q^42*t^20 + q^42*t^21)/
    ((-1 + q^2*t)^2*(q + q^3*t)), {q, q^3*t} -> 
    (q^15*t^8 - q^15*t^9 - 2*q^17*t^9 - q^19*t^10 - q^19*t^11 + 2*q^21*t^11 - 
     2*q^23*t^12)/(2*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q, -(q^3*t)} -> (q^15*t^8 + q^15*t^9)/(2 + 2*q^2*t), 
    {q^3*t, q} -> (q^15*t^8 - q^15*t^9 - 2*q^17*t^9 - q^19*t^10 - q^19*t^11 + 
                   2*q^21*t^11 - 2*q^23*t^12)/(2*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, q^3*t} -> (1 + t - 3*q^2*t + q^2*t^2 + 4*q^4*t^2)/
    (4*q*(-1 + q^2*t)^2), {q^3*t, -(q^3*t)} -> (1 + t)/(4*q + 4*q^3*t), 
    {-(q^3*t), q} -> (q^15*t^8 + q^15*t^9)/(2 + 2*q^2*t), 
    {-(q^3*t), q^3*t} -> (1 + t)/(4*q + 4*q^3*t), 
    {-(q^3*t), -(q^3*t)} -> (1 + t)/(4*q + 4*q^3*t)|>;
n3sliceFit1[-6] =
    <|{q, q} -> (1 + q^2 - q^4*t - q^4*t^2 + q^6*t^3 + q^8*t^3 - q^10*t^5 + 
                 q^12*t^6 - q^14*t^6 - 2*q^14*t^7 + q^16*t^7 + q^16*t^8 - 2*q^18*t^8 - 
                 q^18*t^9 + q^20*t^9 - q^22*t^10 + q^22*t^11 + q^22*t^12 - q^24*t^12 + 
                 q^26*t^12 - q^24*t^13 + 2*q^26*t^13 - q^28*t^13 + q^26*t^14 - 
                 2*q^28*t^14 + q^30*t^14 - q^28*t^15 + 2*q^30*t^15 - q^32*t^15 + 
                 q^30*t^16 - q^32*t^16 + q^34*t^16 + q^34*t^17)/
    ((-1 + q^2*t)^2*(q + q^3*t)), {q, q^3*t} -> 
    (q^11*t^6 - q^11*t^7 - 2*q^13*t^7 - q^15*t^8 - q^15*t^9 + 2*q^17*t^9 - 
     2*q^19*t^10)/(2*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q, -(q^3*t)} -> (q^11*t^6 + q^11*t^7)/(2 + 2*q^2*t), 
    {q^3*t, q} -> (q^11*t^6 - q^11*t^7 - 2*q^13*t^7 - q^15*t^8 - q^15*t^9 + 
                   2*q^17*t^9 - 2*q^19*t^10)/(2*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, q^3*t} -> (1 + t - 3*q^2*t + q^2*t^2 + 4*q^4*t^2)/
    (4*q*(-1 + q^2*t)^2), {q^3*t, -(q^3*t)} -> (1 + t)/(4*q + 4*q^3*t), 
    {-(q^3*t), q} -> (q^11*t^6 + q^11*t^7)/(2 + 2*q^2*t), 
    {-(q^3*t), q^3*t} -> (1 + t)/(4*q + 4*q^3*t), 
    {-(q^3*t), -(q^3*t)} -> (1 + t)/(4*q + 4*q^3*t)|>;
n3sliceFit1[-4] =
<|{q, q} -> (1 + q^2 - q^4*t - q^4*t^2 + q^8*t^3 + q^8*t^4 - q^10*t^4 - 
    2*q^10*t^5 + q^12*t^5 + q^12*t^6 - 2*q^14*t^6 + q^16*t^7 + q^14*t^8 - 
    q^16*t^8 - q^16*t^9 + 2*q^18*t^9 - q^20*t^9 + q^18*t^10 - 2*q^20*t^10 + 
    q^22*t^10 - q^20*t^11 + 2*q^22*t^11 - q^24*t^11 + q^22*t^12 - q^24*t^12 + 
    q^26*t^12 + q^26*t^13)/((-1 + q^2*t)^2*(q + q^3*t)), 
 {q, q^3*t} -> (q^7*t^4 - q^7*t^5 - 2*q^9*t^5 - q^11*t^6 - q^11*t^7 + 
    2*q^13*t^7 - 2*q^15*t^8)/(2*(-1 + q^2*t)^2*(1 + q^2*t)), 
 {q, -(q^3*t)} -> (q^7*t^4 + q^7*t^5)/(2 + 2*q^2*t), 
 {q^3*t, q} -> (q^7*t^4 - q^7*t^5 - 2*q^9*t^5 - q^11*t^6 - q^11*t^7 + 
    2*q^13*t^7 - 2*q^15*t^8)/(2*(-1 + q^2*t)^2*(1 + q^2*t)), 
 {q^3*t, q^3*t} -> (1 + t - 3*q^2*t + q^2*t^2 + 4*q^4*t^2)/
   (4*q*(-1 + q^2*t)^2), {q^3*t, -(q^3*t)} -> (1 + t)/(4*q + 4*q^3*t), 
 {-(q^3*t), q} -> (q^7*t^4 + q^7*t^5)/(2 + 2*q^2*t), 
 {-(q^3*t), q^3*t} -> (1 + t)/(4*q + 4*q^3*t), 
 {-(q^3*t), -(q^3*t)} -> (1 + t)/(4*q + 4*q^3*t)|>;
n3sliceFit1[-2] =
    <|{q, q} -> (1 + q^2 - q^2*t - q^4*t - q^6*t^2 + 2*q^8*t^3 + q^6*t^4 - 
                 q^10*t^4 - q^8*t^5 + q^10*t^5 + q^10*t^6 - 2*q^12*t^6 - q^12*t^7 + 
                 2*q^14*t^7 - q^16*t^7 + q^14*t^8 - q^16*t^8 + q^18*t^8 + q^18*t^9)/
    ((-1 + q^2*t)^2*(q + q^3*t)), {q, q^3*t} -> 
    (q^3*t^2 - q^3*t^3 - 2*q^5*t^3 - q^7*t^4 - q^7*t^5 + 2*q^9*t^5 - 
     2*q^11*t^6)/(2*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q, -(q^3*t)} -> (q^3*t^2 + q^3*t^3)/(2 + 2*q^2*t), 
    {q^3*t, q} -> (q^3*t^2 - q^3*t^3 - 2*q^5*t^3 - q^7*t^4 - q^7*t^5 + 
                   2*q^9*t^5 - 2*q^11*t^6)/(2*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, q^3*t} -> (1 + t - 3*q^2*t + q^2*t^2 + 4*q^4*t^2)/
    (4*q*(-1 + q^2*t)^2), {q^3*t, -(q^3*t)} -> (1 + t)/(4*q + 4*q^3*t), 
    {-(q^3*t), q} -> (q^3*t^2 + q^3*t^3)/(2 + 2*q^2*t), 
    {-(q^3*t), q^3*t} -> (1 + t)/(4*q + 4*q^3*t), 
    {-(q^3*t), -(q^3*t)} -> (1 + t)/(4*q + 4*q^3*t)|>;

(* ### vv Try to find the n3 evolution in the exceptional region ### *)
Block[{kC = -2,
       extraPoints = 2,
       res = <||>},
      Iterate[{{eig1, eig2}, MkTupleIter[AList @@ PosFundEigenvalues[], AList @@ PosFundEigenvalues[]]},
              Module[{ans = FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                                     n3sliceFit1[kC - 2 k1][{eig1, eig2}]],
                                                            Prepend[{1, 1/t/q^2, 1/t^2/q^4}, kC - 2 k]]},
                     KeyValueMap[Function[{key, val},
                                          res[Join[{eig1, eig2}, key]] = Factor[Simplify[val]]],
                                 ans]]];
      res] // InputForm

(* ### vv Try to find the n3 evolution in the (-1,-1,1) exceptional region ### *)
Block[{kC = 2,
       extraPoints = 2,
       res = <||>},
      Iterate[{{eig1, eig2}, MkTupleIter[AList @@ PosFundEigenvalues[], AList @@ PosFundEigenvalues[]]},
              Module[{ans = FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                                     n3sliceFit2[kC + 2 k1][{eig1, eig2}]],
                                                            Prepend[{1, 1/t/q^2, 1/t^2/q^4}, kC + 2 k]]},
                     KeyValueMap[Function[{key, val},
                                          res[Join[{eig1, eig2}, key]] = Factor[Simplify[val]]],
                                 ans]]];
      res] // InputForm

(* ### vv Try to find the n2 evolution in the (1,-1,1) exceptional region ### *)
Block[{kC = -2,
       extraPoints = 2,
       res = <||>},
      Iterate[{{eig1, eig2}, MkTupleIter[AList @@ PosFundEigenvalues[], AList @@ NegAdjEigenvalues[]]},
              Print["eigs: ", eig1, " ", eig2];
              Module[{ans = FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                                     n3sliceFit3[kC - k1][{eig1, eig2}]],
                                                            Prepend[Join[PosFundEigenvalues[], {(t q)^(-1), (- t q)^(-1)}],
                                                                    kC - k]]},
                     KeyValueMap[Function[{key, val},
                                          res[{eig1, key[[1]], eig2}] = Factor[Simplify[val]]],
                                 ans]]];
      res] // InputForm

(* ### vv Try to find the n1 evolution in the (-1,1,1) exceptional region ### *)
Block[{kC = -2,
       extraPoints = 2,
       res = <||>},
      Iterate[{{eig1, eig2}, MkTupleIter[AList @@ PosFundEigenvalues[], AList @@ NegAdjEigenvalues[]]},
              Print["eigs: ", eig1, " ", eig2];
              Module[{ans = FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                                     n3sliceFit4[kC - k1][{eig1, eig2}]],
                                                            Prepend[Join[PosFundEigenvalues[], {(t q)^(-1), (- t q)^(-1)}],
                                                                    kC - k]]},
                     KeyValueMap[Function[{key, val},
                                          res[{key[[1]], eig1, eig2}] = Factor[Simplify[val]]],
                                 ans]]];
      res] // InputForm

(* ### vv Try to find the n1 evolution in the (1,-1,-1) exceptional region ### *)
Block[{kC = 2,
       extraPoints = 2,
       res = <||>},
      Iterate[{{eig1, eig2}, MkTupleIter[AList @@ PosFundEigenvalues[], AList @@ NegAdjEigenvalues[]]},
              Print["eigs: ", eig1, " ", eig2];
              Module[{ans = FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                                     n3sliceFit5[kC + k1][{eig1, eig2}]],
                                                            Prepend[Join[PosFundEigenvalues[], {(t q)^(-1), (- t q)^(-1)}],
                                                                    kC + k]]},
                     KeyValueMap[Function[{key, val},
                                          res[{key[[1]], eig1, eig2}] = Factor[Simplify[val]]],
                                 ans]]];
      res] // InputForm

(* ### vv Try to find the n1 evolution in the (-1,1,-1) exceptional region ### *)
Block[{kC = 2,
       extraPoints = 2,
       res = <||>},
      Iterate[{{eig1, eig2}, MkTupleIter[AList @@ PosFundEigenvalues[], AList @@ NegAdjEigenvalues[]]},
              Print["eigs: ", eig1, " ", eig2];
              Module[{ans = FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                                     n3sliceFit6[kC + k1][{eig1, eig2}]],
                                                            Prepend[Join[PosFundEigenvalues[], {(t q)^(-1), (- t q)^(-1)}],
                                                                    kC + k]]},
                     KeyValueMap[Function[{key, val},
                                          res[{eig1, key[[1]], eig2}] = Factor[Simplify[val]]],
                                 ans]]];
      res] // InputForm

Out[7]//InputForm= 
<|{q, q, 1} -> (-1 + q^2*t - q^6*t^2 - 2*q^6*t^3 + q^8*t^4)/
   (q*t*(-1 + q^2*t)^2*(1 + q^2*t)), {q, q^3*t, 1} -> 0, 
 {q, -(q^3*t), 1} -> 0, {q, 1/(q*t), 1} -> 0, {q, -(1/(q*t)), 1} -> 0, 
 {q, q, 1/(q^2*t)} -> -(((1 + q^4*t)*(1 + q^4*t^2)*(1 - q^2*t + q^4*t^2))/
    (q^3*t*(-1 + q^2*t)^2*(1 + q^2*t))), {q, q^3*t, 1/(q^2*t)} -> 
  (2 + q^2 - q^2*t - q^6*t^2 + q^6*t^3 + 2*q^8*t^3)/
   (2*q*(-1 + q^2*t)^2*(1 + q^2*t)), {q, -(q^3*t), 1/(q^2*t)} -> 
  (q*(1 + t))/(2*(1 + q^2*t)), {q, 1/(q*t), 1/(q^2*t)} -> 
  ((1 + t)*(1 + q^4*t)*(1 + q^8*t^4))/(2*q^3*t^2*(-1 + q^2*t)^2*(1 + q^2*t)), 
 {q, -(1/(q*t)), 1/(q^2*t)} -> ((1 + t)*(1 + q^4*t)*(1 + q^4*t^2))/
   (2*q^3*t^2*(1 + q^2*t)), {q^3*t, q, 1} -> 0, 
 {q^3*t, q^3*t, 1} -> (q*(4 + q^2 - 3*q^2*t + q^4*t + q^4*t^2))/
   (4*(-1 + q^2*t)^2), {q^3*t, -(q^3*t), 1} -> (q^3*(1 + t))/(4*(1 + q^2*t)), 
 {q^3*t, 1/(q*t), 1} -> 0, {q^3*t, -(1/(q*t)), 1} -> 0, 
 {q^3*t, q, 1/(q^2*t)} -> (-2 + 2*q^2*t - q^4*t - q^4*t^2 - 2*q^6*t^3 - 
    q^8*t^3 + q^8*t^4)/(2*q*t*(-1 + q^2*t)^2*(1 + q^2*t)), 
 {q^3*t, q^3*t, 1/(q^2*t)} -> 0, {q^3*t, -(q^3*t), 1/(q^2*t)} -> 0, 
 {q^3*t, 1/(q*t), 1/(q^2*t)} -> 0, {q^3*t, -(1/(q*t)), 1/(q^2*t)} -> 0, 
 {-(q^3*t), q, 1} -> 0, {-(q^3*t), q^3*t, 1} -> 
  (q^3*(1 + t))/(4*(1 + q^2*t)), {-(q^3*t), -(q^3*t), 1} -> 
  (q^3*(1 + t))/(4*(1 + q^2*t)), {-(q^3*t), 1/(q*t), 1} -> 0, 
 {-(q^3*t), -(1/(q*t)), 1} -> 0, {-(q^3*t), q, 1/(q^2*t)} -> 
  (q^3*(1 + t))/(2*(1 + q^2*t)), {-(q^3*t), q^3*t, 1/(q^2*t)} -> 0, 
 {-(q^3*t), -(q^3*t), 1/(q^2*t)} -> 0, {-(q^3*t), 1/(q*t), 1/(q^2*t)} -> 0, 
 {-(q^3*t), -(1/(q*t)), 1/(q^2*t)} -> 0|>


Out[4]//InputForm= 
    <|{q, q, 1} -> (-1 + q^2*t - q^6*t^2 - 2*q^6*t^3 + q^8*t^4)/
    (q*t*(-1 + q^2*t)^2*(1 + q^2*t)), {q^3*t, q, 1} -> 0, 
    {-(q^3*t), q, 1} -> 0, {1/(q*t), q, 1} -> 0, {-(1/(q*t)), q, 1} -> 0, 
    {q, q, 1/(q^2*t)} -> -(((1 + q^4*t)*(1 + q^4*t^2)*(1 - q^2*t + q^4*t^2))/
                           (q^3*t*(-1 + q^2*t)^2*(1 + q^2*t))), {q^3*t, q, 1/(q^2*t)} -> 
    (2 + q^2 - q^2*t - q^6*t^2 + q^6*t^3 + 2*q^8*t^3)/
    (2*q*(-1 + q^2*t)^2*(1 + q^2*t)), {-(q^3*t), q, 1/(q^2*t)} -> 
    (q*(1 + t))/(2*(1 + q^2*t)), {1/(q*t), q, 1/(q^2*t)} -> 
    ((1 + t)*(1 + q^4*t)*(1 + q^8*t^4))/(2*q^3*t^2*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {-(1/(q*t)), q, 1/(q^2*t)} -> ((1 + t)*(1 + q^4*t)*(1 + q^4*t^2))/
    (2*q^3*t^2*(1 + q^2*t)), {q, q^3*t, 1} -> 0, 
    {q^3*t, q^3*t, 1} -> (q*(4 + q^2 - 3*q^2*t + q^4*t + q^4*t^2))/
    (4*(-1 + q^2*t)^2), {-(q^3*t), q^3*t, 1} -> (q^3*(1 + t))/(4*(1 + q^2*t)), 
    {1/(q*t), q^3*t, 1} -> 0, {-(1/(q*t)), q^3*t, 1} -> 0, 
    {q, q^3*t, 1/(q^2*t)} -> (-2 + 2*q^2*t - q^4*t - q^4*t^2 - 2*q^6*t^3 - 
                              q^8*t^3 + q^8*t^4)/(2*q*t*(-1 + q^2*t)^2*(1 + q^2*t)), 
    {q^3*t, q^3*t, 1/(q^2*t)} -> 0, {-(q^3*t), q^3*t, 1/(q^2*t)} -> 0, 
    {1/(q*t), q^3*t, 1/(q^2*t)} -> 0, {-(1/(q*t)), q^3*t, 1/(q^2*t)} -> 0, 
    {q, -(q^3*t), 1} -> 0, {q^3*t, -(q^3*t), 1} -> 
    (q^3*(1 + t))/(4*(1 + q^2*t)), {-(q^3*t), -(q^3*t), 1} -> 
    (q^3*(1 + t))/(4*(1 + q^2*t)), {1/(q*t), -(q^3*t), 1} -> 0, 
    {-(1/(q*t)), -(q^3*t), 1} -> 0, {q, -(q^3*t), 1/(q^2*t)} -> 
    (q^3*(1 + t))/(2*(1 + q^2*t)), {q^3*t, -(q^3*t), 1/(q^2*t)} -> 0, 
    {-(q^3*t), -(q^3*t), 1/(q^2*t)} -> 0, {1/(q*t), -(q^3*t), 1/(q^2*t)} -> 0, 
    {-(1/(q*t)), -(q^3*t), 1/(q^2*t)} -> 0|>

Out[4]//InputForm= 
<|{q, q, 1} -> -((-1 + 2*q^2*t + q^2*t^2 - q^6*t^3 + q^8*t^4)/
    (q*(-1 + q^2*t)^2*(1 + q^2*t))), {q^3*t, q, 1} -> 0, 
 {-(q^3*t), q, 1} -> 0, {1/(q*t), q, 1} -> 0, {-(1/(q*t)), q, 1} -> 0, 
 {q, q, 1/(q^2*t)} -> -(((1 + q^4*t)*(1 + q^4*t^2)*(1 - q^2*t + q^4*t^2))/
    (q^3*t*(-1 + q^2*t)^2*(1 + q^2*t))), {q^3*t, q, 1/(q^2*t)} -> 
  (2 + q^2 - q^2*t - q^6*t^2 + q^6*t^3 + 2*q^8*t^3)/
   (2*q*(-1 + q^2*t)^2*(1 + q^2*t)), {-(q^3*t), q, 1/(q^2*t)} -> 
  (q*(1 + t))/(2*(1 + q^2*t)), {1/(q*t), q, 1/(q^2*t)} -> 
  ((1 + t)*(1 + q^4*t)*(1 + q^8*t^4))/(2*q^3*t*(-1 + q^2*t)^2*(1 + q^2*t)), 
 {-(1/(q*t)), q, 1/(q^2*t)} -> ((1 + t)*(1 + q^4*t)*(1 + q^4*t^2))/
   (2*q^3*t*(1 + q^2*t)), {q, q^3*t, 1} -> 0, 
 {q^3*t, q^3*t, 1} -> (1 + t - 3*q^2*t + q^2*t^2 + 4*q^4*t^2)/
   (4*q*(-1 + q^2*t)^2), {-(q^3*t), q^3*t, 1} -> (1 + t)/(4*q*(1 + q^2*t)), 
 {1/(q*t), q^3*t, 1} -> 0, {-(1/(q*t)), q^3*t, 1} -> 0, 
 {q, q^3*t, 1/(q^2*t)} -> -(-1 + t + 2*q^2*t + q^4*t^2 + q^4*t^3 - 
     2*q^6*t^3 + 2*q^8*t^4)/(2*q*(-1 + q^2*t)^2*(1 + q^2*t)), 
 {q^3*t, q^3*t, 1/(q^2*t)} -> 0, {-(q^3*t), q^3*t, 1/(q^2*t)} -> 0, 
 {1/(q*t), q^3*t, 1/(q^2*t)} -> 0, {-(1/(q*t)), q^3*t, 1/(q^2*t)} -> 0, 
 {q, -(q^3*t), 1} -> 0, {q^3*t, -(q^3*t), 1} -> (1 + t)/(4*q*(1 + q^2*t)), 
 {-(q^3*t), -(q^3*t), 1} -> (1 + t)/(4*q*(1 + q^2*t)), 
 {1/(q*t), -(q^3*t), 1} -> 0, {-(1/(q*t)), -(q^3*t), 1} -> 0, 
 {q, -(q^3*t), 1/(q^2*t)} -> (1 + t)/(2*q*(1 + q^2*t)), 
 {q^3*t, -(q^3*t), 1/(q^2*t)} -> 0, {-(q^3*t), -(q^3*t), 1/(q^2*t)} -> 0, 
 {1/(q*t), -(q^3*t), 1/(q^2*t)} -> 0, {-(1/(q*t)), -(q^3*t), 1/(q^2*t)} -> 0|>

Out[26]//InputForm= 
<|{q, q, 1} -> -((-1 + 2*q^2*t + q^2*t^2 - q^6*t^3 + q^8*t^4)/
    (q*(-1 + q^2*t)^2*(1 + q^2*t))), {q, q^3*t, 1} -> 0, 
 {q, -(q^3*t), 1} -> 0, {q, 1/(q*t), 1} -> 0, {q, -(1/(q*t)), 1} -> 0, 
 {q, q, 1/(q^2*t)} -> -(((1 + q^4*t)*(1 + q^4*t^2)*(1 - q^2*t + q^4*t^2))/
    (q^3*t*(-1 + q^2*t)^2*(1 + q^2*t))), {q, q^3*t, 1/(q^2*t)} -> 
  (2 + q^2 - q^2*t - q^6*t^2 + q^6*t^3 + 2*q^8*t^3)/
   (2*q*(-1 + q^2*t)^2*(1 + q^2*t)), {q, -(q^3*t), 1/(q^2*t)} -> 
  (q*(1 + t))/(2*(1 + q^2*t)), {q, 1/(q*t), 1/(q^2*t)} -> 
  ((1 + t)*(1 + q^4*t)*(1 + q^8*t^4))/(2*q^3*t*(-1 + q^2*t)^2*(1 + q^2*t)), 
 {q, -(1/(q*t)), 1/(q^2*t)} -> ((1 + t)*(1 + q^4*t)*(1 + q^4*t^2))/
   (2*q^3*t*(1 + q^2*t)), {q^3*t, q, 1} -> 0, 
 {q^3*t, q^3*t, 1} -> (1 + t - 3*q^2*t + q^2*t^2 + 4*q^4*t^2)/
   (4*q*(-1 + q^2*t)^2), {q^3*t, -(q^3*t), 1} -> (1 + t)/(4*q*(1 + q^2*t)), 
 {q^3*t, 1/(q*t), 1} -> 0, {q^3*t, -(1/(q*t)), 1} -> 0, 
 {q^3*t, q, 1/(q^2*t)} -> -(-1 + t + 2*q^2*t + q^4*t^2 + q^4*t^3 - 
     2*q^6*t^3 + 2*q^8*t^4)/(2*q*(-1 + q^2*t)^2*(1 + q^2*t)), 
 {q^3*t, q^3*t, 1/(q^2*t)} -> 0, {q^3*t, -(q^3*t), 1/(q^2*t)} -> 0, 
 {q^3*t, 1/(q*t), 1/(q^2*t)} -> 0, {q^3*t, -(1/(q*t)), 1/(q^2*t)} -> 0, 
 {-(q^3*t), q, 1} -> 0, {-(q^3*t), q^3*t, 1} -> (1 + t)/(4*q*(1 + q^2*t)), 
 {-(q^3*t), -(q^3*t), 1} -> (1 + t)/(4*q*(1 + q^2*t)), 
 {-(q^3*t), 1/(q*t), 1} -> 0, {-(q^3*t), -(1/(q*t)), 1} -> 0, 
 {-(q^3*t), q, 1/(q^2*t)} -> (1 + t)/(2*q*(1 + q^2*t)), 
 {-(q^3*t), q^3*t, 1/(q^2*t)} -> 0, {-(q^3*t), -(q^3*t), 1/(q^2*t)} -> 0, 
 {-(q^3*t), 1/(q*t), 1/(q^2*t)} -> 0, {-(q^3*t), -(1/(q*t)), 1/(q^2*t)} -> 0|>

Out[4]//InputForm= 
<|{q, q, 1} -> (1 + q^2 - q^4*t - q^4*t^2 + q^6*t^3 + q^8*t^3)/
   (q*(-1 + q^2*t)^2*(1 + q^2*t)), {q, q, 1/(q^2*t)} -> 
  -(((1 + q^4*t)*(1 + q^4*t^2)*(1 - q^2*t + q^4*t^2))/
    (q^3*t*(-1 + q^2*t)^2*(1 + q^2*t))), {q, q, 1/(q^4*t^2)} -> 
  ((1 + t)*(1 + q^4*t)*(1 - q^2*t + q^4*t^2 - q^6*t^3 + q^8*t^4))/
   (q^3*t^2*(-1 + q^2*t)^2*(1 + q^2*t)), {q, q^3*t, 1} -> 0, 
 {q, q^3*t, 1/(q^2*t)} -> (-2 + 2*q^2*t - q^4*t - q^4*t^2 - 2*q^6*t^3 - 
    q^8*t^3 + q^8*t^4)/(2*q*t*(-1 + q^2*t)^2*(1 + q^2*t)), 
 {q, q^3*t, 1/(q^4*t^2)} -> 0, {q, -(q^3*t), 1} -> 0, 
 {q, -(q^3*t), 1/(q^2*t)} -> (q^3*(1 + t))/(2*(1 + q^2*t)), 
 {q, -(q^3*t), 1/(q^4*t^2)} -> 0, {q^3*t, q, 1} -> 0, 
 {q^3*t, q, 1/(q^2*t)} -> (-2 + 2*q^2*t - q^4*t - q^4*t^2 - 2*q^6*t^3 - 
    q^8*t^3 + q^8*t^4)/(2*q*t*(-1 + q^2*t)^2*(1 + q^2*t)), 
 {q^3*t, q, 1/(q^4*t^2)} -> 0, {q^3*t, q^3*t, 1} -> 
  (q*(4 + q^2 - 3*q^2*t + q^4*t + q^4*t^2))/(4*(-1 + q^2*t)^2), 
 {q^3*t, q^3*t, 1/(q^2*t)} -> 0, {q^3*t, q^3*t, 1/(q^4*t^2)} -> 0, 
 {q^3*t, -(q^3*t), 1} -> (q^3*(1 + t))/(4*(1 + q^2*t)), 
 {q^3*t, -(q^3*t), 1/(q^2*t)} -> 0, {q^3*t, -(q^3*t), 1/(q^4*t^2)} -> 0, 
 {-(q^3*t), q, 1} -> 0, {-(q^3*t), q, 1/(q^2*t)} -> 
  (q^3*(1 + t))/(2*(1 + q^2*t)), {-(q^3*t), q, 1/(q^4*t^2)} -> 0, 
 {-(q^3*t), q^3*t, 1} -> (q^3*(1 + t))/(4*(1 + q^2*t)), 
 {-(q^3*t), q^3*t, 1/(q^2*t)} -> 0, {-(q^3*t), q^3*t, 1/(q^4*t^2)} -> 0, 
 {-(q^3*t), -(q^3*t), 1} -> (q^3*(1 + t))/(4*(1 + q^2*t)), 
 {-(q^3*t), -(q^3*t), 1/(q^2*t)} -> 0, {-(q^3*t), -(q^3*t), 1/(q^4*t^2)} -> 
  0|>


<|{q, q, 1} -> (1 + q^2 - q^4*t - q^4*t^2 + q^6*t^3 + q^8*t^3)/
   (q*(-1 + q^2*t)^2*(1 + q^2*t)), {q, q, 1/(q^2*t)} -> 
  -(((1 + q^4*t)*(1 + q^4*t^2)*(1 - q^2*t + q^4*t^2))/
    (q^3*t*(-1 + q^2*t)^2*(1 + q^2*t))), {q, q, 1/(q^4*t^2)} -> 
  ((1 + t)*(1 + q^4*t)*(1 - q^2*t + q^4*t^2 - q^6*t^3 + q^8*t^4))/
   (q^3*t*(-1 + q^2*t)^2*(1 + q^2*t)), {q, q^3*t, 1} -> 0, 
 {q, q^3*t, 1/(q^2*t)} -> -(-1 + t + 2*q^2*t + q^4*t^2 + q^4*t^3 - 
     2*q^6*t^3 + 2*q^8*t^4)/(2*q*(-1 + q^2*t)^2*(1 + q^2*t)), 
 {q, q^3*t, 1/(q^4*t^2)} -> 0, {q, -(q^3*t), 1} -> 0, 
 {q, -(q^3*t), 1/(q^2*t)} -> (1 + t)/(2*q*(1 + q^2*t)), 
 {q, -(q^3*t), 1/(q^4*t^2)} -> 0, {q^3*t, q, 1} -> 0, 
 {q^3*t, q, 1/(q^2*t)} -> -(-1 + t + 2*q^2*t + q^4*t^2 + q^4*t^3 - 
     2*q^6*t^3 + 2*q^8*t^4)/(2*q*(-1 + q^2*t)^2*(1 + q^2*t)), 
 {q^3*t, q, 1/(q^4*t^2)} -> 0, {q^3*t, q^3*t, 1} -> 
  (1 + t - 3*q^2*t + q^2*t^2 + 4*q^4*t^2)/(4*q*(-1 + q^2*t)^2), 
 {q^3*t, q^3*t, 1/(q^2*t)} -> 0, {q^3*t, q^3*t, 1/(q^4*t^2)} -> 0, 
 {q^3*t, -(q^3*t), 1} -> (1 + t)/(4*q*(1 + q^2*t)), 
 {q^3*t, -(q^3*t), 1/(q^2*t)} -> 0, {q^3*t, -(q^3*t), 1/(q^4*t^2)} -> 0, 
 {-(q^3*t), q, 1} -> 0, {-(q^3*t), q, 1/(q^2*t)} -> 
  (1 + t)/(2*q*(1 + q^2*t)), {-(q^3*t), q, 1/(q^4*t^2)} -> 0, 
 {-(q^3*t), q^3*t, 1} -> (1 + t)/(4*q*(1 + q^2*t)), 
 {-(q^3*t), q^3*t, 1/(q^2*t)} -> 0, {-(q^3*t), q^3*t, 1/(q^4*t^2)} -> 0, 
 {-(q^3*t), -(q^3*t), 1} -> (1 + t)/(4*q*(1 + q^2*t)), 
 {-(q^3*t), -(q^3*t), 1/(q^2*t)} -> 0, {-(q^3*t), -(q^3*t), 1/(q^4*t^2)} -> 
  0|>

Block[{extraPoints = 5},
      Factor[FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                      n3sliceFit1[-2 - 2 k1][{q,q}]],
                                             Prepend[{1, 1/t/q^2, 1/t^2/q^4}, -2 - 2 k]]]]

n3sliceFit2[6]

Block[{extraPoints = 2},
      Factor[FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                      n3sliceFit2[2 + 2 k1][{q,q}]],
                                             Prepend[{1, 1/t/q^2, 1/t^2/q^4}, 2 + 2 k]]]]

Block[{extraPoints = 2},
      Factor[FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                      n3sliceFit3[2 + k1][{q,1}]],
                                             Prepend[PosFundEigenvalues[], 2 + k]]]]




n3sliceFit1[-2 (6)][{q,q}]

theOrder = 4;
theDelta = 2;
eqns = Map[Function[{n},
                    0 == (Plus @@
                          Map[Function[{delta},
                                       Simplify[n3sliceFit1[-2 (n + delta)][{q,q}]]
                                       * CC[delta]],
                              Range[0, theOrder-1]])],
           Range[theDelta, theDelta + theOrder+1]];
ans = Solve[eqns (* /. {t -> -1} *),
	    Map[CC[#] &, Range[1,theOrder]]];
ans1 = FullSimplify[ans]

                                                                                                   

ans1

Solve[0 == Sum[CC[i] x^i, {i, 0, theOrder-1}] /. ans1[[1]],
      x]


Block[{k = 6},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, Expand[Simplify[n3sliceFit1[-2 k][{q,q}](q + t q^3)(1 - t q^2)^2]]];
             fun1 = Function[{k}, Expand[Simplify[fun[k+1] - fun[k]]]];
             fun2 = Function[{k}, Expand[Simplify[fun1[k+1] - t^2 q^4 fun1[k]]]];
             fun3 = Function[{k}, Expand[Simplify[fun2[k+1] - t^4 q^8 fun2[k]]]];
             (* {Length[fun1[k]], fun1[k]} *)
             fun3[k]
            ]]

Block[{k = 1},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, Expand[Simplify[n3sliceFit3[-2 - 2 k][{q,1/t/q^2}](1 + t q^2)(1 - t q^2)^2]]];
             fun1 = Function[{k}, Expand[Simplify[fun[k+1] - t^2 q^2 fun[k]]]];
             fun2 = Function[{k}, Expand[Simplify[fun1[k+1] - q^(-2) fun1[k]]]];
             fun3 = Function[{k}, Expand[Simplify[fun2[k+1] - (t^2 q^6)^(-1) fun2[k]]]];
             (* fun4 = Function[{k}, Expand[Simplify[fun3[k+1] - t^5 q^9 fun3[k]]]]; *)
             (* {Length[fun1[k]], fun1[k]} *)
             fun3[k]
            ]]

Block[{k = 2},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, Expand[Simplify[n3sliceFit3[-2 -1 - 2 k][{q,1/t/q^2}](1 + t q^2)(1 - t q^2)^2]]];
             fun1 = Function[{k}, Expand[Simplify[fun[k+1] - t^2 q^2 fun[k]]]];
             fun2 = Function[{k}, Expand[Simplify[fun1[k+1] - q^(-2) fun1[k]]]];
             fun3 = Function[{k}, Expand[Simplify[fun2[k+1] - (t^2 q^6)^(-1) fun2[k]]]];
             (* fun4 = Function[{k}, Expand[Simplify[fun3[k+1] - t^5 q^9 fun3[k]]]]; *)
             (* {Length[fun1[k]], fun1[k]} *)
             fun3[k]
            ]]

(* ### vv Let's combine odd and even series for Fit3 ### *)
Block[{k = 5},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, Expand[Simplify[n3sliceFit3[-2 - k][{q,1/t/q^2}](1 + t q^2)(1 - t q^2)^2]]];
             fun1 = Function[{k}, Expand[Simplify[fun[k+1] - t q fun[k]]]];
             fun2 = Function[{k}, Expand[Simplify[fun1[k+1] - q^(-1) fun1[k]]]];
             fun3 = Function[{k}, Expand[Simplify[fun2[k+1] - (t q^3)^(-1) fun2[k]]]];
             fun4 = Function[{k}, Expand[Simplify[fun3[k+1] - (-t q^3)^(-1) fun3[k]]]];
             fun5 = Function[{k}, Expand[Simplify[fun4[k+1] - (-t q) fun4[k]]]];
             (* {Length[fun1[k]], fun1[k]} *)
             fun5[k]
            ]]

