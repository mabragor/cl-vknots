
<< "knot-theory-knovanov-ev-utils.m";
<< "tuple-iterator.m";

(* ### vv Convenient constants to specify filenames ### *)
CCCWorkDir = "/home/popolit/quicklisp/local-projects/cl-vknots";
CCCSrcDir = CCCWorkDir <> "/src";
CCCDataDir = CCCWorkDir <> "/data";
(* ### vv Constants to make the series detection robust ### *)
CCCSeriesShiftParr = 2;
CCCSeriesShiftAntiParr = 1;
CCCExtraPoints = 2;
FindPretzelEvos[genus_] :=
    (* ### ^^ Find evolution coefficients for pretzel knots of genus `genus`. ### *)
    Module[{signIter = MkTupleIter @@ Map[AList @@ # &, Module[{i}, Table[{1,-1}, {i, 1, genus + 1}]]],
            fdlog = OpenWrite[CCCDataDir <> "/pretzel-evo-" <> ToString[genus+1] <> ".log"]},
           Module[{signs, validQ},
                  While[True,
                        {signs, validQ} = signIter[];
                        If[Not[validQ],
                           Break[]];
                        (* ### ^^ We loop over all the 2^n-tants ### *)
                        ClearAll[PrecompKh]; (* ### << We want to free memory from the previous round ### *)
                        (* ### vv Load the precomputed data ### *)
                        WriteString[fdlog, "Loading data for: ("
                                    <> StringRiffle[Map[ToString, signs], ", "] <> ") ..."];
                        Get[CCCDataDir <> "/pretzel-khovanovs-" <> ToString[genus + 1]
                            <> "-" <> StringRiffle[Map[ToString, signs], "-"] <> ".m"];
                        WriteString[fdlog, " ... done!"];
                        WriteString[fdlog, "Calculating evos for: ("
                                    <> StringRiffle[Map[ToString, signs], ", "] <> ") ..."];
                        Module[{seriesExprs = Append[Module[{i}, Table[signs[[i]] (k + CCCSeriesShiftParr),
                                                                       {i, 1, genus}]],
                                                     If[EvenQ[genus + 1],
                                                        signs[[-1]] (k + CCCSeriesShiftParr),
                                                        signs[[-1]] 2 (k + CCCSeriesShiftAntiParr)]]},
                               (* Print[seriesExprs]; *)
                               (* Print[MkPrecompFunction[seriesExprs]]; *)
                               (* Print[MkPrecompEigSpecs[seriesExprs]]; *)
                               Module[{theAns = Block[{extraPoints = CCCExtraPoints},
                                                      (FitFamilyWithEigenvaluesAdvanced
                                                       @@ Prepend[MkPrecompEigSpecs[seriesExprs],
                                                                  MkPrecompFunction[seriesExprs]])]},
                                      Module[{fd = OpenWrite[CCCDataDir <> "/pretzel-kh-evo-" <> ToString[genus+1]
                                                             <> "-" <> StringRiffle[Map[ToString, signs], "-"]
                                                             <> ".m"]},
                                             WriteString[fd, ToString[Factor[Simplify[theAns]], InputForm] <> ""];
                                             Close[fd]]]];
                        WriteString[fdlog, " done!"]]];
Close[fdlog]];
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


(* MkPrecompFunction[{k+1,k+1}] *)
(* MkPrecompEigSpecs[{k+1,k+1,2 k + 2}] *)
                                      
FindPretzelEvos[2]

[Calculating...]

