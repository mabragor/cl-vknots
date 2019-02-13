
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
Block[{kC = -10,
       extraPoints = 2},
      Iterate[{{eig1, eig2}, MkTupleIter[AList @@ PosFundEigenvalues[], AList @@ PosFundEigenvalues[]]},
              FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                       n3sliceFit1[kC - 2 k1][{eig1, eig2}]],
                                              Prepend[NegAdjEigenvalues[], kC - 2 k]]]]

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


Block[{k = 5},
      Module[{fun = Function[{k}, Expand[Simplify[n3sliceFit1[-2 k][{q,q}](q + t q^3)(1 - t q^2)^2]]]},
             Expand[Simplify[(fun[k+2] - fun[k+1]) - t^2 q^4 (fun[k+1] - fun[k])]]]]

