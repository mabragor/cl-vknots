
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

Block[{CCCEigenvaluesCritLength = Null,
       CCCSeriesShiftParr = {2, 9},
       CCCSeriesShiftAntiParr = 5},
      FindPretzelEvosForNTant[2, {-1,1,1}, Null]]

                        restIndices: {0, 0} curSeries: -2 - k
shifts {9 + k, 2 (5 + k)}
shiftIndices {9, 10}
{{0, 3}, {nz, 2}}




?? FFWETmp




Module[{serSpecs = {k+1, k+1}},
       FitFamilyWithEigenvaluesGradual @@ Prepend[MkPrecompEigSpecs[serSpecs],
                                                  MkPrecompFunction[serSpecs]]]


                
