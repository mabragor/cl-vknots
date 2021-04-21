
(* ################################################################################ *)
(* ### In this file we investigate the whitehead (reduced) Khovanov polynomials ### *)
(* ################################################################################ *)

(* ### vv BEGINIMPORTS ### *)
<< "knot-theory-knovanov-ev-utils.m";
<< "file-locks.m";
(* ### ^^ ENDIMPORTS ### *)

(* ### vv BEGINLIB ### *)
CCCPythonDir = "/home/popolit/code/planar-diagrams-py/";
CCCInputFname = "whiteheadize-pd-input.txt";
CCCOutputFname = "whiteheadize-pd-output.txt";
CCCScriptFname = "whiteheadize-pd.py";
CCCRolfsenMults = {1, 1, 2, 3, 7, 21, 49, 165};
CCCFoamhoPath = "/home/popolit/code/foamho-bin/foamho/foamho";
CCCFoamhoOutputFname = "/tmp/foamho-output.txt";
FS[x_] := Factor[Simplify[x]];
EFS[x_] := Expand[FS[x]];
PyCallWhiteheadizer[command_, pd_, args_] :=
    (* ### ^^ A general "RPC" interface to the python part of the planar diagram rig. ### *)
    (* ###    `command` -- a command to be executed ### *)
    (* ###    `pd`      -- a planar diagram (maybe cut), to be placed into a special input file. ### *)
    (* ###                 Set to None, if no input knot is needed (as for the twist-knots.) ### *)
    (* ###    `args`    -- command-line arguments to the script ### *)
    WithALock["whiteheadize-pd", (* ### << Surely we need some synchronization as we run several things using this ### *)
              (* ###                       functionality in parallel. ### *)
              Module[{code, fdWrite},
                     If[None =!= pd,
                        (* ### vv dump planar diagram into a file ### *)
                        fdWrite = OpenWrite[CCCPythonDir <> CCCInputFname];
                        WriteString[fdWrite, ToString[pd, InputForm]];
                        Close[fdWrite]];
                     (* ### vv Call a python part of the rig ### *)
                     code = Run[StringTemplate["python2 `pyDir``scriptName` `cmd` `args` > /dev/null"]
                                [<|"pyDir" -> CCCPythonDir, "scriptName" -> CCCScriptFname,
                                 "cmd" -> command, "args" -> StringJoin[StringRiffle[Map[ToString, args]]]
                                 |>]];
                     If[0 =!= code,
                        Message[PyCallWhiteheadizer::someThingWrongPython],
                        (* ### vv Read the whiteheadized diagram from the file ### *)
                        Get[CCCPythonDir <> CCCOutputFname]]]];
CutPD[knot_] :=
    (* ### ^^ Cut planar diagram of a knot at the origin ### *)
    Module[{pd = PD[knot]},
           ReplacePart[pd, FirstPosition[pd, 1] -> 0]];
PyGetWhiteheadizedPD[knot_, aWind_, bWind_] :=
    (* ### ^^ Get a double-braid satellite of the given knot ### *)
    (* ###    `knot`  -- a knot in any form that can be fed into `PD` of the knot theory ### *)
    (* ###    `aWind` -- number of windings of the a-braid of the double-braid duo ### *)
    (* ###    `bWind` -- number of windings of the b-braid of the double-braid duo ### *)
    PyCallWhiteheadizer["whiteheadize", CutPD[knot], {aWind, bWind}];
PyGetTwostrandedPD[knot_, wind_] :=
    (* ### ^^ Get a result of insertion of 2-strand braid into a 2-cable of a given knot. ### *)
    (* ###    `knot`  -- a knot in any form that can be fed into `PD` of the knot theory ### *)
    (* ###    `wind` -- number of windings of the 2-strand braid. ### *)
    PyCallWhiteheadizer["two-cable", CutPD[knot], {wind}];
PyGetTwistWhiteheadizedPD[parentWind_, childWind_] :=
    (* ### ^^ Get a twist satellite of a twist knot. Diagram is completely constructed on the Python side. ### *)
    (* ###    `parentWind` -- number of windings in the parent twist knot's 2-strand braid ### *)
    (* ###    `childWind`  -- number of windings in the child twist knot's 2-strand braid  ### *)
    PyCallWhiteheadizer["twist", None, {parentWind, childWind}];
PyGetTwistTwostrandedPD[twistWind_, wind_] :=
    (* ### ^^ Get a result of insertion of 2-strand braid into a 2-cable of a twist knot. ### *)
    (* ###    `twistWind` -- number of windings of the 2-strand braid of the twist knot. ### *)
    (* ###    `wind` -- number of windings of the 2-strand braid. ### *)
    PyCallWhiteheadizer["twist-two-cable", None, {twistWind, wind}];
PrecalculateKhRedWhiteheadizedPDs[knot_, squareSize_] :=
    (* ### ^^ Precalculate whiteheadized reduced Khovanov polynomials in some square of the double-braid space. ### *)
    (* ###    `squareSize` -- (roughly) half the length of the side of the square ### *)
    (* ###    `knot`       -- a knot spec from a Rolfsen table ### *)
    Module[{fd = OpenAppend[CCCDataDir <> "/kh-red-precomp-whiteheadized-" <> KnotToFname[knot] <> ".m"],
            i, j},
           For[i = -squareSize, i <= squareSize, i ++,
               For[j = -squareSize, j <= squareSize, j ++,
                   Module[{polly = KhReduced[PyGetWhiteheadizedPD[knot, i, j] /. {ii_Integer :> ii + 1}][q, t]},
                          WriteString[fd, "PrecompKhRed[" <> ToString[knot, InputForm] <> ", " <> ToString[i] <> ", " <> ToString[j]
                                      <> "] := " <> ToString[polly, InputForm] <> ";\n"]]]];
           Close[fd]];
PrecalculateKhRedWhiteheadizedPDsLine[knot_, from_, to_, step_] :=
    (* ### ^^ Precalculate whiteheadized reduced Khovanov polynomials specifically for a twisted line. ### *)
    (* ###    `from` and `to`-- winding iteration bounds ### *)
    (* ###    `knot`       -- a knot spec from a Rolfsen table ### *)
    Module[{fd = OpenAppend[CCCDataDir <> "/kh-red-precomp-whiteheadized-" <> KnotToFname[knot] <> ".m"],
            i},
           For[i = from, i <= to, i = i + step,
               Module[{polly = KhReduced[PyGetWhiteheadizedPD[knot, i, 2] /. {ii_Integer :> ii + 1}][q, t]},
                      WriteString[fd, "PrecompKhRed[" <> ToString[knot, InputForm] <> ", " <> ToString[i] <> ", " <> ToString[2]
                                  <> "] := " <> ToString[polly, InputForm] <> ";\n"]]];
           Close[fd]];
ConstLst[elt_, length_] :=
    (* ### ^^ Create a list of length `length` where every element is a constant `elt` ### *)
    Module[{i}, Table[elt, {i, 1, length}]];
PrecalculateKhRedWhdTorusKnotPDsLine[2, p_, midPt_, delta_, step_] :=
    (* ### ^^ Precalculate whiteheadized reduced Khovanov polynomials ### *)
    (* ###    for a 2-strand torus knot. ### *)
    (* ###    `midPt` -- the middle point of the range of windings ### *)
    (* ###    `delta` -- the winding iteration bounds are `midPt` - `delta` and `mitPt` + `delta` ### *)
    (* ###               `delta` is supposed to be multiple to `step` ### *)
    (* ###    `p`            -- the number of windings of a torus knot. ### *)
    (* ###                      Convention is p --> BR[2, {-1}^p] (so that it matches with Rolfsen) ### *)
    (* ###    26.03.2021 -- redone the calculation ### *)
    Module[{fd = OpenAppend[CCCDataDir <> "/kh-red-precomp-whiteheadized-torus-2-" <> ToString[p] <> ".m"],
            br = BR[2, Join[ConstLst[If[p > 0, -1, 1], Abs[p]],
                            If[MemberQ[{1,3}, Abs[p]],
                               {1, -1},
                               {}]]],
            i, sgn},
           Module[{polly = KhReduced[PyGetWhiteheadizedPD[PD[br], midPt, 2] /. {ii_Integer :> ii + 1}][q, t]},
                  WriteString[fd, StringTemplate["PrecompKhRed[\"w\", TorusKnot[2, `p`], `i`] := `expr`;\n"]
                              [<|"p" -> p, "i" -> midPt, "expr" -> ToString[polly, InputForm]|>]]];
           For[shift = step, shift <= delta, shift += step,
               Module[{pollyPlus = KhReduced[PyGetWhiteheadizedPD[PD[br], midPt + shift, 2]
                                             /. {ii_Integer :> ii + 1}][q, t],
                       pollyMinus = KhReduced[PyGetWhiteheadizedPD[PD[br], midPt - shift, 2]
                                             /. {ii_Integer :> ii + 1}][q, t]},
                      WriteString[fd, StringTemplate["PrecompKhRed[\"w\", TorusKnot[2, `p`], `i`] := `expr`;\n"]
                                  [<|"p" -> p, "i" -> midPt + shift, "expr" -> ToString[pollyPlus, InputForm]|>]];
                      WriteString[fd, StringTemplate["PrecompKhRed[\"w\", TorusKnot[2, `p`], `i`] := `expr`;\n"]
                                  [<|"p" -> p, "i" -> midPt - shift, "expr" -> ToString[pollyMinus, InputForm]|>]]]];
           Close[fd]];
PrecalculateKhRedTwStTorusKnotPDsLine[2, p_, from_, to_, step_] :=
    (* ### ^^ Precalculate two-cabled reduced Khovanov polynomials ### *)
    (* ###    for a 2-strand torus knot. ### *)
    (* ###    `from` and `to`-- winding iteration bounds ### *)
    (* ###    `p`            -- the number of windings of a torus knot. ### *)
    (* ###                      Convention is p --> BR[2, {-1}^p] (so that it matches with Rolfsen) ### *)
    (* ###    26.03.2021 -- redone the calculation ### *)
    Module[{fd = OpenAppend[CCCDataDir <> "/kh-red-precomp-twst-torus-2-" <> ToString[p] <> ".m"],
            br = BR[2, Join[ConstLst[If[p > 0, -1, 1], Abs[p]],
                            If[1 === Abs[p],
                               {1, -1},
                               {}]]],
            i},
           For[i = from, i <= to, i = i + step,
               Module[{polly = KhReduced[PyGetTwostrandedPD[PD[br], i] /. {ii_Integer :> ii + 1}][q, t]},
                      WriteString[fd, StringTemplate["PrecompKhRed[TorusKnotTwSt[2, `p`], `i`] := `expr`;\n"]
                                  [<|"p" -> p, "i" -> i, "expr" -> ToString[polly, InputForm]|>]]]];
           Close[fd]];
PrecalculateKhRedTwistedPDsLine[twist_, from_, to_] :=
    (* ### ^^ Precalculate reduced Khovanov polynomials for twisted-twisted knots. ### *)
    (* ###    `from` and `to`-- winding iteration bounds for a child braid. ### *)
    (* ###    `twist`        -- winding of a parent braid. ### *)
    Module[{fd = OpenAppend[CCCDataDir <> "/kh-red-precomp-whiteheadized-twist-" <> ToString[twist] <> ".m"],
            i},
           For[i = from, i <= to, i = i + 2,
               Module[{polly = KhReduced[PyGetTwistWhiteheadizedPD[twist, i] /. {ii_Integer :> ii + 1}][q, t]},
                      WriteString[fd, "PrecompKhRed[Twisted[" <> ToString[twist] <> "], " <> ToString[i]
                                  <> "] := " <> ToString[polly, InputForm] <> ";\n"]]];
           Close[fd]];
PrecalculateKhRedTwStTwistedPDsLine[twist_, from_, to_] :=
    (* ### ^^ Precalculate reduced Khovanov polynomials for twisted knots with two-strand insertion. ### *)
    (* ###    `from` and `to`-- winding iteration bounds for a child braid. ### *)
    (* ###    `twist`        -- winding of a parent braid. ### *)
    Module[{fd = OpenAppend[CCCDataDir <> "/kh-red-precomp-twst-twist-" <> ToString[twist] <> ".m"],
            i},
           For[i = from, i <= to, i = i + 2,
               Module[{polly = KhReduced[PyGetTwistTwostrandedPD[twist, i] /. {ii_Integer :> ii + 1}][q, t]},
                      WriteString[fd, "PrecompKhRed[TWSTTwisted[" <> ToString[twist] <> "], " <> ToString[i]
                                  <> "] := " <> ToString[polly, InputForm] <> ";\n"]]];
           Close[fd]];
KnotToFname[Knot[a_, b_]] :=
    ("rolfsen-knot-" <> ToString[a] <> "-" <> ToString[b]);
PDToFoamhoString[pd_PD] :=
    (* ### ^^ Prepare a string representation of planar diagram to be understood by foamho ### *)
    (* ###    "PD[X[a, b, c, d]]" goes to "[[a,b,c,d]]". ### *)
    StringReplace[ToString[pd, InputForm], RegularExpression["(PD|X|\\s)"] -> ""];
KhReducedSL3[pd_PD] :=
    (* ### ^^ Calculate sl(3) reduced rational KhR-homology, using foamho program of Lewark et al. ### *)
    (* ###    `pd` is a planar diagram in a format that KhotTheory understands ### *)
    Module[{code},
           code = Run[StringTemplate["`cmd` -q -r pd `planarDiagram` > `outputFname`"]
                      [<|"cmd" -> CCCFoamhoPath,
                       "planarDiagram" -> PDToFoamhoString[pd],
                       "outputFname" -> CCCFoamhoOutputFname|>]];
           If[0 =!= code,
              Message[KhReducedSL3::foamhoFailed]; Return[]];
           Module[{strs = StringSplit[ReadString[CCCFoamhoOutputFname],
                                      RegularExpression["\\n"]]},
                  Module[{str = First[Select[strs,
                                             StringMatchQ[#,
                                                          RegularExpression["^Rational reduced homology: .*"]] &]]},
                         ToExpression[StringReplace[str,
                                                    RegularExpression["^Rational reduced homology: "] -> ""]]]]];
PrecalculateKhRedSL3TwistedPDsLine[twist_, from_, to_] :=
    (* ### ^^ Precalculate reduced Khovanov sl(3) polynomials for twisted-twisted knots. ### *)
    (* ###    `from` and `to`-- winding iteration bounds for a child braid. ### *)
    (* ###    `twist`        -- winding of a parent braid. ### *)
    Module[{fd = OpenWrite[CCCDataDir <> "/kh-red-sl3-precomp-twisted-twisted-" <> ToString[twist] <> ".m"],
            i},
           For[i = from, i <= to, i = i + 2,
               Module[{polly = KhReducedSL3[PyGetTwistWhiteheadizedPD[twist, i] /. {ii_Integer :> ii + 1}]},
                      WriteString[fd, "PrecompKhRedSL3[Twisted[" <> ToString[twist] <> "], " <> ToString[i]
                                  <> "] := " <> ToString[polly, InputForm] <> ";\n"]]];
           Close[fd]];
LoadFirstTwostrandTorusEvolutions[] :=
    (* ### ^^ Load all the relevant evolution formulas ### *)
    Module[{i},
           For[i = -19, i <= 19, i = i + 2,
               Get[CCCDataDir <> StringTemplate["/kh-red-1evo-torus-2-``.m"][i]]]
           For[i = -19, i <= 19, i = i + 2,
               Get[CCCDataDir <> StringTemplate["/kh-red-precomp-twst-torus-2-``.m"][i]]]];
FindSecondTwostrandTorusEvolutionsTQ3[] :=
    (* ### ^^ Find actual evolutions, corresponding to "first" eigenvalue t q^3         ### *)
    (* ###    The function operates by side-effect, a bunch of `ansMinus` and `ansPlus` ### *)
    (* ###    get assigned as a result of the call                                      ### *)
    Block[{delta = aa, delta1 = bb},
          delta = -19;
          delta1 = 1;
          TheFun[k_] := Coefficient[Kh1EvoRed[Torus[2, k],"plus"] /. {(q^3 t)^n :> AA},
                                    AA, 1];
          ansMinus["plus", t q^3] =
          Block[{extraPoints = 9},
                With[{aSeries = delta + 2 k},
                     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                               Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                      Join[{aSeries},
                                                           (* {q^(-4), t^(-3) q^(-8), t^(-4) q^(-10)} *)
                                                           (* {q^(-8), t^(-6) q^(-16), t^(-8) q^(-20)} *)
                                                           {t^(-2) q^(-6)}
                                                          ]]]];
          ansPlus["plus", t q^3] =
          Block[{extraPoints = 9},
                With[{aSeries = delta1 + 2 k},
                     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                               Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                      Join[{aSeries},
                                                           {t^(-2) q^(-6)}
                                                           (* {q^(-4), t^(-3) q^(-8), t^(-4) q^(-10)} *)
                                                          ]]]];
          TheFun[k_] := Coefficient[Kh1EvoRed[Torus[2, k],"minus"] /. {(q^3 t)^n :> AA},
                                    AA, 1];
          ansMinus["minus", t q^3] =
          Block[{extraPoints = 9},
                With[{aSeries = delta + 2 k},
                     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                               Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                      Join[{aSeries},
                                                           (* {q^(-4), t^(-3) q^(-8), t^(-4) q^(-10)} *)
                                                           (* {q^(-8), t^(-6) q^(-16), t^(-8) q^(-20)} *)
                                                           {t^(-2) q^(-6)}
                                                          ]]]];
          ansPlus["minus", t q^3] =
          Block[{extraPoints = 9},
                With[{aSeries = delta1 + 2 k},
                     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                               Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                      Join[{aSeries},
                                                           {t^(-2) q^(-6)}
                                                           (* {q^(-4), t^(-3) q^(-8), t^(-4) q^(-10)} *)
                                                          ]]]];
         ];
FindSecondTwostrandTorusEvolutionsQ[] :=
    (* ### ^^ Find actual evolutions, corresponding to "first" eigenvalue q             ### *)
    (* ###    The function operates by side-effect, a bunch of `ansMinus` and `ansPlus` ### *)
    (* ###    get assigned as a result of the call                                      ### *)
    Block[{delta = aa, delta1 = bb},
          delta = -19;
          delta1 = 1;
          TheFun[k_] :=
          Expand[FS[(1 - q^2 t)/(1 - q^2 t + q^4 t^2) q^(-n)
                    Coefficient[Kh1EvoRed[Torus[2, k],"plus"] /. {(q^3 t)^n :> AA},
                                AA, 0]]];
          ansMinus["plus", q] =
          Block[{extraPoints = 7},
                With[{aSeries = delta + 2 k},
                     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                               Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                      Join[{aSeries},
                                                           {q^(-4), t^(-3) q^(-8), t^(-4) q^(-10)}
                                                           (* {t^(-2) q^(-6)} *)
                                                          ]]]];
          ansPlus["plus", q] =
          Block[{extraPoints = 7},
                With[{aSeries = delta1 + 2 k},
                     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                               Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                      Join[{aSeries},
                                                           (* {t^(-2) q^(-6)} *)
                                                           {q^(-4), t^(-3) q^(-8), t^(-4) q^(-10)}
                                                          ]]]];
          TheFun[k_] :=
          Expand[FS[(1 - q^2 t)/(1 - q^2 t + q^4 t^2) q^(-n)
                    Coefficient[Kh1EvoRed[Torus[2, k],"minus"] /. {(q^3 t)^n :> AA},
                                AA, 0]]];
          ansMinus["minus", q] =
          Block[{extraPoints = 7},
                With[{aSeries = delta + 2 k},
                     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                               Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                      Join[{aSeries},
                                                           {q^(-4), t^(-3) q^(-8), t^(-4) q^(-10)}
                                                          ]]]];
          ansPlus["minus", q] =
          Block[{extraPoints = 7},
                With[{aSeries = delta1 + 2 k},
                     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                               Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                      Join[{aSeries},
                                                           {q^(-4), t^(-3) q^(-8), t^(-4) q^(-10)}
                                                          ]]]];
         ];
Frob[] :=
    Module[{},
           LoadFirstTwostrandTorusEvolutions[];
           ClearAll[ansMinus, ansPlus]; (* ### << Clear the registers for the answers ### *)
           FindSecondTwostrandTorusEvolutionsTQ3[];
           FindSecondTwostrandTorusEvolutionsQ[];
          ];
DumpSecondTwostrandTorusEvolution[] :=
    (* ### ^^ Write previous found two-parametric evolution  ### *)
    (* ###    for two-strand torus knot satellites into file ### *)
    Module[{fd = OpenWrite[CCCDataDir <> "/kh-red-2evo-torus-2.m"]},
           WriteString[fd, "(* ### This is two-parametric evolution of two-strand torus knots ### *)\n"];
           WriteString[fd, "(* ### that are 'satellitted' with two-strand braid. ###*)\n"];
           WriteString[fd, "(* ### In `p` evolution is divided into 'plus' for p > 0 ### *)\n"];
           WriteString[fd, "(* ### and 'minus' for p < 0 ### *)\n"];
           WriteString[fd, "(* ### In `n` evolution is divided into: ### *)\n"];
           WriteString[fd, "(* ###     for p-plus: 'plus' is n > 3 - p, 'minus' is n < 3 - p ### *)\n"];
           WriteString[fd, "(* ###     for p-minus: 'plus' is n > -3 - p, 'minus' is n < -3 - p ### *)\n"];
           WriteString[fd, StringTemplate["Kh2EvoRed[Torus[2], \"torus\", \"plus\", \"plus\"] := ``;\n"]
                       [ToString[1/(1 - q^2 t) (1 - q^2 t + q^4 t^2)
                                 q^n ((AA[1] (q^(-4))^p + AA[2] (t^(-3) q^(-8))^p + AA[3] (t^(-4) q^(-10))^p)
                                      /. ansPlus["plus", q])
                                 + (t q^3)^n ((AA[1] (t^(-2) q^(-6))^p)  /. ansPlus["plus", t q^3]),
                                 InputForm]]];
           WriteString[fd, StringTemplate["Kh2EvoRed[Torus[2], \"torus\", \"plus\", \"minus\"] := ``;\n"]
                       [ToString[1/(1 - q^2 t) (1 - q^2 t + q^4 t^2)
                                 q^n ((AA[1] (q^(-4))^p + AA[2] (t^(-3) q^(-8))^p + AA[3] (t^(-4) q^(-10))^p)
                                      /. ansPlus["minus", q])
                                 + (t q^3)^n ((AA[1] (t^(-2) q^(-6))^p)  /. ansPlus["minus", t q^3]),
                                 InputForm]]];
           WriteString[fd, StringTemplate["Kh2EvoRed[Torus[2], \"torus\", \"minus\", \"plus\"] := ``;\n"]
                       [ToString[1/(1 - q^2 t) (1 - q^2 t + q^4 t^2)
                                 q^n ((AA[1] (q^(-4))^p + AA[2] (t^(-3) q^(-8))^p + AA[3] (t^(-4) q^(-10))^p)
                                      /. ansMinus["plus", q])
                                 + (t q^3)^n ((AA[1] (t^(-2) q^(-6))^p)  /. ansMinus["plus", t q^3]),
                                 InputForm]]];
           WriteString[fd, StringTemplate["Kh2EvoRed[Torus[2], \"torus\", \"minus\", \"minus\"] := ``;\n"]
                       [ToString[1/(1 - q^2 t) (1 - q^2 t + q^4 t^2)
                                 q^n ((AA[1] (q^(-4))^p + AA[2] (t^(-3) q^(-8))^p + AA[3] (t^(-4) q^(-10))^p)
                                      /. ansMinus["minus", q])
                                 + (t q^3)^n ((AA[1] (t^(-2) q^(-6))^p)  /. ansMinus["minus", t q^3]),
                                 InputForm]]];
           Close[fd];
          ];
LoadSecondTwostrandTorusEvolution[] :=
    Get[CCCDataDir <> "/kh-red-2evo-torus-2.m"];
LoadFirstWhiteheadizedTwostrandTorusEvolutions[] :=
    (* ### ^^ Load all the relevant evolution formulas for whiteheadized ### *)
    (* ###    (satellite) 2-strand torus knots.                          ### *)
    Module[{i},
           For[i = -15, i <= 15, i = i + 2,
               Get[CCCDataDir <> StringTemplate["/kh-red-1evo-wh-torus-2-``.m"][i]]];
           For[i = -15, i <= 15, i = i + 2,
               Get[CCCDataDir <> StringTemplate["/kh-red-precomp-whiteheadized-torus-2-``.m"][i]]]];
FrobWhiteheadizedTorus[] :=
    Module[{},
           LoadFirstWhiteheadizedTwostrandTorusEvolutions[];
           ClearAll[ansMinus, ansPlus]; (* ### << Clear the registers for the answers ### *)
           FindSecondWhiteheadizedTwostrandTorusEvolutions1[];
           FindSecondWhiteheadizedTwostrandTorusEvolutionsTm1Qm2[];
          ];
FindSecondWhiteheadizedTwostrandTorusEvolutionsTm1Qm2[] :=
    (* ### ^^ Find actual evolutions, corresponding to "first" eigenvalue 1/(t q^2)     ### *)
    (* ###    The function operates by side-effect, a bunch of `ansMinus` and `ansPlus` ### *)
    (* ###    get assigned as a result of the call                                      ### *)
    Block[{delta = aa, delta1 = bb, theExtraPts = 3},
          delta = -15;
          delta1 = 1;
          TheFun[k_] := EFS[Coefficient[Kh1EvoRed["w", Torus[2, k], "plus"]
                                        /. {(1/(q^2*t))^n :> AA},
                                        AA, 1] /(1 + q^2 t) /(1 - q^2 t + q^4 t^2) (1 - q^2 t)];
          ansMinus["plus", q^(-2) t^(-1)] =
          Block[{extraPoints = theExtraPts},
                With[{aSeries = delta + 2 k},
                     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                               Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                      Join[{aSeries},
                                                           {q^(-1), t^(-2) q^(-4), t^(-1) q^(-2), t^2 q^4, t^2 q^2}
                                                           (* {q^(-2), t^(-4) q^(-8), t^(-2) q^(-4), t^4 q^8, t^4 q^4} *)
                                                          ]]]];
          ansPlus["plus", q^(-2) t^(-1)] =
          Block[{extraPoints = theExtraPts},
                With[{aSeries = delta1 + 2 k},
                     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                               Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                      Join[{aSeries},
                                                           {q^(-1), t^(-2) q^(-4), t^(-1) q^(-2), t^2 q^4, t^2 q^2}
                                                           (* {q^(-2), t^(-4) q^(-8), t^(-2) q^(-4), t^4 q^8, t^4 q^4} *)
                                                          ]]]];
          TheFun[k_] := EFS[Coefficient[Kh1EvoRed["w", Torus[2, k], "minus"]
                                        /. {(1/(q^2*t))^n :> AA},
                                        AA, 1] /(1 + q^2 t) /(1 - q^2 t + q^4 t^2) (1 - q^2 t)];
          ansMinus["minus", q^(-2) t^(-1)] =
          Block[{extraPoints = theExtraPts},
                With[{aSeries = delta + 2 k},
                     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                               Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                      Join[{aSeries},
                                                           {q^(-1), t^(-2) q^(-4), t^(-1) q^(-2), t^2 q^4, t^2 q^2}
                                                           (* {q^(-2), t^(-4) q^(-8), t^(-2) q^(-4), t^4 q^8, t^4 q^4} *)
                                                          ]]]];
          ansPlus["minus", q^(-2) t^(-1)] =
          Block[{extraPoints = theExtraPts},
                With[{aSeries = delta1 + 2 k},
                     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                               Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                      Join[{aSeries},
                                                           {q^(-1), t^(-2) q^(-4), t^(-1) q^(-2), t^2 q^4, t^2 q^2}
                                                           (* {q^(-2), t^(-4) q^(-8), t^(-2) q^(-4), t^4 q^8, t^4 q^4} *)
                                                          ]]]];
         ];
FindSecondWhiteheadizedTwostrandTorusEvolutions1[] :=
    (* ### ^^ Find actual evolutions, corresponding to "first" eigenvalue 1             ### *)
    (* ###    The function operates by side-effect, a bunch of `ansMinus` and `ansPlus` ### *)
    (* ###    get assigned as a result of the call                                      ### *)
    Block[{delta = aa, delta1 = bb, theExtraPts = 7},
          delta = -15;
          delta1 = 1;
          TheFun[k_] := EFS[Coefficient[Kh1EvoRed["w", Torus[2, k], "plus"]
                                        /. {(1/(q^2*t))^n :> AA},
                                        AA, 0]];
          ansMinus["plus", 1] =
          Block[{extraPoints = theExtraPts},
                With[{aSeries = delta + 2 k},
                     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                               Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                      Join[{aSeries},
                                                           {1}
                                                          ]]]];
          ansPlus["plus", 1] =
          Block[{extraPoints = theExtraPts},
                With[{aSeries = delta1 + 2 k},
                     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                               Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                      Join[{aSeries},
                                                           {1}
                                                          ]]]];
          TheFun[k_] := EFS[Coefficient[Kh1EvoRed["w", Torus[2, k], "minus"]
                                        /. {(1/(q^2*t))^n :> AA},
                                        AA, 0]];
          ansMinus["minus", 1] =
          Block[{extraPoints = theExtraPts},
                With[{aSeries = delta + 2 k},
                     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                               Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                      Join[{aSeries},
                                                           {1}
                                                          ]]]];
          ansPlus["minus", 1] =
          Block[{extraPoints = theExtraPts},
                With[{aSeries = delta1 + 2 k},
                     FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                               Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                      Join[{aSeries},
                                                           {1}
                                                          ]]]];
         ];
DumpSecondWhiteheadizedTorusEvolution[] :=
    (* ### ^^ Write previous found two-parametric evolution  ### *)
    (* ###    for whiteheadized torus knot satellites into file ### *)
    Module[{fd = OpenWrite[CCCDataDir <> "/kh-red-2evo-wh-torus-2.m"],
            ansLabel},
           ansLabel["plus"] = ansPlus; ansLabel["minus"] = ansMinus;
           WriteString[fd, "(* ### This is two-parametric evolution for two-strand torus knots ### *)\n"];
           WriteString[fd, "(* ### that are 'satellitted' with whitehead braid. ###*)\n"];
           WriteString[fd, "(* ### In `p` evolution is divided into 'plus' for p > 0 ### *)\n"];
           WriteString[fd, "(* ### and 'minus' for p < 0 ### *)\n"];
           WriteString[fd, "(* ### In `n` evolution is divided into: ### *)\n"];
           WriteString[fd, "(* ###     for p-plus: 'plus' is n > 3 - p, 'minus' is n < 3 - p ### *)\n"];
           WriteString[fd, "(* ###     for p-minus: 'plus' is n > -3 - p, 'minus' is n < -3 - p ### *)\n"];
           Scan[Function[
               {regOne},
               Scan[Function[
                   {regTwo},
                   rules = ansLabel[regOne];
                   WriteString[fd, StringTemplate["Kh2EvoRed[Torus[2], \"wh\", \"``\", \"``\"] := ``;\n"]
                               [regOne, regTwo,
                                ToString[(1 + q^2 t) (1 - q^2 t + q^4 t^2) /(1 - q^2 t)
                                         (t^(-1) q^(-2))^n ((AA[1] (q^(-1))^p + AA[2] (t^(-2) q^(-4))^p
                                                             + AA[3] (t^(-1) q^(-2))^p + AA[4] (t^2 q^4)^p
                                                             + AA[5] (t^2 q^2)^p)
                                                            /. rules[regTwo, t^(-1) q^(-2)])
                                         + (1)^n ((AA[1] (1)^p)  /. rules[regTwo, 1]),
                                         InputForm]]];
                            ],
                    {"plus", "minus"}]],
                {"plus", "minus"}];
           Close[fd];
          ];
LoadSecondWhiteheadizedTorusEvolution[] :=
    Get[CCCDataDir <> "/kh-red-2evo-wh-torus-2.m"];
(* ### ^^ ENDLIB ### *)

FrobWhiteheadizedTorus[]

LoadFirstWhiteheadizedTwostrandTorusEvolutions[];
LoadSecondWhiteheadizedTorusEvolution[];

(* ### ### vv BEGINCHECK Whiteheadized two-strand torus (2-parametric) evolution. ### ### *)
(* ### vv Alright, now we need to check the obtained evolution ### *)
Block[{delN = 20},
      Map[Function[{pp},
                   Join[Map[Function[{nn},
                                     FS[(Kh2EvoRed[Torus[2], "wh", "minus", "minus"] /. {p -> pp, n -> nn})
                                        - PrecompKhRed["w", TorusKnot[2, pp], nn]]],
                            Range[-2 - pp - delN, -2 - pp - 2, 2]],
                        Map[Function[{nn},
                                     FS[(Kh2EvoRed[Torus[2], "wh", "minus", "plus"] /. {p -> pp, n -> nn})
                                        - PrecompKhRed["w", TorusKnot[2, pp], nn]]],
                            Range[-2 - pp + 0, -2 - pp + delN, 2]]]],
          Range[-15, -1, 2]]]
    
Block[{delN = 20},
      Map[Function[{pp},
                   Join[Map[Function[{nn},
                                     FS[(Kh2EvoRed[Torus[2], "wh", "plus", "minus"] /. {p -> pp, n -> nn})
                                        - PrecompKhRed["w", TorusKnot[2, pp], nn]]],
                            Range[4 - pp - delN, 4 - pp - 2, 2]],
                        Map[Function[{nn},
                                     FS[(Kh2EvoRed[Torus[2], "wh", "plus", "plus"] /. {p -> pp, n -> nn})
                                        - PrecompKhRed["w", TorusKnot[2, pp], nn]]],
                            Range[4 - pp + 0, 4 - pp + delN, 2]]]],
          Range[1, 15, 2]]]

(* ### ### ^^ ENDCHECK Whiteheadized two-strand torus (2-parametric) evolution. ### ### *)

LoadFirstWhiteheadizedTwostrandTorusEvolutions[]

(* ### vv Establish eigenvalues ### *)
Block[{k = 8, delta = -15},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, EFS[Coefficient[Kh1EvoRed["w", Torus[2,delta + 2 k], "plus"]
                                                 /. {(1/(q^2*t))^n :> AA},
                                                 AA, 1] /(1 + q^2 t) /(1 - q^2 t + q^4 t^2) (1 - q^2 t)]];
             fun1 = Function[{k}, Expand[FS[fun[k+1] - q^(-2) fun[k]]]];
             fun2 = Function[{k}, Expand[FS[fun1[k+1] - (t^(-4) q^(-8)) fun1[k]]]];
             fun3 = Function[{k}, Expand[FS[fun2[k+1] - (t^(-2) q^(-4)) fun2[k]]]];
             fun4 = Function[{k}, Expand[FS[fun3[k+1] - (t^(4) q^(8)) fun3[k]]]];
             fun5 = Function[{k}, Expand[FS[fun4[k+1] - (t^(4) q^(4)) fun4[k]]]];
             fun5[k]
            ]]

(* ### vv Establish eigenvalues ### *)
Block[{k = 14, delta = -15},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, EFS[Coefficient[Kh1EvoRed["w", Torus[2,delta + 2 k], "plus"]
                                                 /. {(1/(q^2*t))^n :> AA},
                                                 AA, 0]]];
             fun1 = Function[{k}, Expand[FS[fun[k+1] - 1 fun[k]]]];
             (* fun2 = Function[{k}, Expand[FS[fun1[k+1] - (t^(-4) q^(-8)) fun1[k]]]]; *)
             (* fun3 = Function[{k}, Expand[FS[fun2[k+1] - (t^(-2) q^(-4)) fun2[k]]]]; *)
             (* fun4 = Function[{k}, Expand[FS[fun3[k+1] - (t^(4) q^(8)) fun3[k]]]]; *)
             (* fun5 = Function[{k}, Expand[FS[fun4[k+1] - (t^(4) q^(4)) fun4[k]]]]; *)
             fun1[k]
            ]]

(* ### vv Establish eigenvalues ### *)
Block[{k = 14, delta = -15},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, EFS[Coefficient[Kh1EvoRed["w", Torus[2,delta + 2 k], "minus"]
                                                 /. {(1/(q^2*t))^n :> AA},
                                                 AA, 0]]];
             fun1 = Function[{k}, Expand[FS[fun[k+1] - 1 fun[k]]]];
             (* fun2 = Function[{k}, Expand[FS[fun1[k+1] - (t^(-4) q^(-8)) fun1[k]]]]; *)
             (* fun3 = Function[{k}, Expand[FS[fun2[k+1] - (t^(-2) q^(-4)) fun2[k]]]]; *)
             (* fun4 = Function[{k}, Expand[FS[fun3[k+1] - (t^(4) q^(8)) fun3[k]]]]; *)
             (* fun5 = Function[{k}, Expand[FS[fun4[k+1] - (t^(4) q^(4)) fun4[k]]]]; *)
             fun1[k]
            ]]

(* ### vv Establish eigenvalues ### *)
Block[{k = 8, delta = -15},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, EFS[Coefficient[Kh1EvoRed["w", Torus[2,delta + 2 k], "minus"]
                                                 /. {(1/(q^2*t))^n :> AA},
                                                 AA, 1] /(1 + q^2 t) /(1 - q^2 t + q^4 t^2) (1 - q^2 t)]];
             fun1 = Function[{k}, Expand[FS[fun[k+1] - q^(-2) fun[k]]]];
             fun2 = Function[{k}, Expand[FS[fun1[k+1] - (t^(-4) q^(-8)) fun1[k]]]];
             fun3 = Function[{k}, Expand[FS[fun2[k+1] - (t^(-2) q^(-4)) fun2[k]]]];
             fun4 = Function[{k}, Expand[FS[fun3[k+1] - (t^(4) q^(8)) fun3[k]]]];
             fun5 = Function[{k}, Expand[FS[fun4[k+1] - (t^(4) q^(4)) fun4[k]]]];
             fun5[k]
            ]]

                                                                                                            




(* Frob[] *)
(* DumpSecondTwostrandTorusEvolution[]; *)
LoadSecondTwostrandTorusEvolution[]
Module[{p},
       For[p = -19, p <= 19, p = p + 2,
           Get[CCCDataDir <> StringTemplate["/kh-red-precomp-twst-torus-2-``.m"][p]];
          ]];

Block[{p = -7, n = 3},
      Module[{lst = {0 === Factor[Simplify[PrecompKhRed[TorusKnotTwSt[2, p], n]
                                           - Kh2EvoRed[Torus[2], "torus", "plus", "plus"]]],
                     0 === Factor[Simplify[PrecompKhRed[TorusKnotTwSt[2, p], n]
                                           - Kh2EvoRed[Torus[2], "torus", "plus", "minus"]]],
                     0 === Factor[Simplify[PrecompKhRed[TorusKnotTwSt[2, p], n]
                                           - Kh2EvoRed[Torus[2], "torus", "minus", "plus"]]],
                     0 === Factor[Simplify[PrecompKhRed[TorusKnotTwSt[2, p], n]
                                           - Kh2EvoRed[Torus[2], "torus", "minus", "minus"]]]}},
             Print[lst];
             If[Not[MemberQ[lst, True]],
                Print["p: ", p, " n: ", n],
                (* Print["OK"] *)]]]

Factor[Simplify[(Kh2EvoRed[Torus[2], "torus", "plus", "plus"]
                 - Kh2EvoRed[Torus[2], "torus", "minus", "plus"]) /. {q -> Pi, t -> E},
                Assumptions -> And[Element[p, Integers],
                                   Element[n, Integers],
                                   p > 0,
                                   n > 0]]]

Factor[Simplify[(Kh2EvoRed[Torus[2], "torus", "plus", "plus"]
                 - Kh2EvoRed[Torus[2], "torus", "plus", "minus"]) /. {q -> Pi, t -> E},
                Assumptions -> And[Element[p, Integers],
                                   Element[n, Integers],
                                   p > 0,
                                   n > 0]]]

Factor[Simplify[(Kh2EvoRed[Torus[2], "torus", "minus", "minus"]
                 - Kh2EvoRed[Torus[2], "torus", "plus", "minus"]) /. {q -> Pi, t -> E},
                Assumptions -> And[Element[p, Integers],
                                   Element[n, Integers],
                                   p > 0,
                                   n > 0]]]

Factor[Simplify[(Kh2EvoRed[Torus[2], "torus", "minus", "minus"]
                 - Kh2EvoRed[Torus[2], "torus", "minus", "plus"]) /. {q -> Pi, t -> E},
                Assumptions -> And[Element[p, Integers],
                                   Element[n, Integers],
                                   p > 0,
                                   n > 0]]]



Module[{pp, nn, delta = 10, dd},
       For[pp = -7, pp <= 7, pp = pp + 2,
           If[pp > 0, dd = 3, dd = -3];
           For[nn = dd + 1 - pp - delta, nn <= dd + 1 - pp + delta, nn = nn + 2,
               Block[{p = pp, n = nn},
                     Module[{lst, lst1},
                            lst = {Factor[Simplify[PrecompKhRed[TorusKnotTwSt[2, p], n]
                                                   - Kh2EvoRed[Torus[2], "torus", "plus", "plus"]]],
                                   Factor[Simplify[PrecompKhRed[TorusKnotTwSt[2, p], n]
                                                   - Kh2EvoRed[Torus[2], "torus", "plus", "minus"]]],
                                   Factor[Simplify[PrecompKhRed[TorusKnotTwSt[2, p], n]
                                                   - Kh2EvoRed[Torus[2], "torus", "minus", "plus"]]],
                                   Factor[Simplify[PrecompKhRed[TorusKnotTwSt[2, p], n]
                                                   - Kh2EvoRed[Torus[2], "torus", "minus", "minus"]]]};
                            lst1 = Map[0 === # &, lst];
                            If[Not[MemberQ[lst1, True]],
                               Print["p: ", p, " n: ", n, " ", lst1, lst]
                               (* , Print["ok"] *)]]]]]]

Block[{p = 2, n = 3},
      Kh2EvoRed[Torus[2], "torus", "plus", "plus"]]


(* ### vv Alright, first evolution have been found correctly ### *)
Block[{p = -1, n = -3},
      Factor[Simplify[Kh1EvoRed[Torus[2, p],"minus"]
                      - PrecompKhRed[TorusKnotTwSt[2, p], n]]
     ]]

Block[{(* n = -3, *) p = -1, ans = ansMinus, label = "minus"},
      ((AA[1] (t^(-2) q^(-6))^p)  /. ans[label, t q^3])
      - Coefficient[Kh1EvoRed[Torus[2, p],"minus"] /. {(q^3 t)^n :> AA},
                    AA, 1]]

Block[{(* n = -3, *) p = -5, ans = ansMinus, label = "minus"},
      FS[1/(1 - q^2 t) (1 - q^2 t + q^4 t^2)
         q^n ((AA[1] (q^(-4))^p + AA[2] (t^(-3) q^(-8))^p + AA[3] (t^(-4) q^(-10))^p)
              /. ans[label, q])
         - Coefficient[Kh1EvoRed[Torus[2, p],"minus"] /. {(q^3 t)^n :> AA},
                       AA, 0]]]


(* - PrecompKhRed[TorusKnotTwSt[2, p], n] *)

(* ### vv Check minus-minus ### *)
Block[{(* n = 5, *) p = -1, ans = ansMinus, label = "minus"},
      FS[(q^n /(1 - q^2 t) (1 - q^2 t + q^4 t^2)
          (AA[1] (q^(-4))^p + AA[2] (t^(-3) q^(-8))^p + AA[3] (t^(-4) q^(-10))^p)
          /. ans[label, q])
         + (t q^3)^n ((AA[1] (t^(-2) q^(-6))^p)  /. ans[label, t q^3])
         - Kh1EvoRed[Torus[2, p], label]
        ]]

(* ### vv Check minus-plus ### *)
Block[{(* n = 5, *) p = -1, ans = ansMinus, label = "plus"},
      FS[(q^n /(1 - q^2 t) (1 - q^2 t + q^4 t^2)
          (AA[1] (q^(-4))^p + AA[2] (t^(-3) q^(-8))^p + AA[3] (t^(-4) q^(-10))^p)
          /. ans[label, q])
         + (t q^3)^n ((AA[1] (t^(-2) q^(-6))^p)  /. ans[label, t q^3])
         - Kh1EvoRed[Torus[2, p], label]
        ]]

(* ### vv Check plus-minus ### *)
Block[{(* n = 5, *) p = 19, ans = ansPlus, label = "minus"},
      FS[(q^n /(1 - q^2 t) (1 - q^2 t + q^4 t^2)
          (AA[1] (q^(-4))^p + AA[2] (t^(-3) q^(-8))^p + AA[3] (t^(-4) q^(-10))^p)
          /. ans[label, q])
         + (t q^3)^n ((AA[1] (t^(-2) q^(-6))^p)  /. ans[label, t q^3])
         - Kh1EvoRed[Torus[2, p], label]
        ]]

(* ### vv Check plus-plus ### *)
Block[{(* n = 5, *) p = 19, ans = ansPlus, label = "plus"},
      FS[(q^n /(1 - q^2 t) (1 - q^2 t + q^4 t^2)
          (AA[1] (q^(-4))^p + AA[2] (t^(-3) q^(-8))^p + AA[3] (t^(-4) q^(-10))^p)
          /. ans[label, q])
         + (t q^3)^n ((AA[1] (t^(-2) q^(-6))^p)  /. ans[label, t q^3])
         - Kh1EvoRed[Torus[2, p], label]
        ]]


PrecompKhRed[TorusKnotTwSt[2, -19], 5]


Frob[]

ansPlus["minus", q]
    
(* ### ### Alright, let's find first evolutions for insertion of whitehead block ### ### *)
(* ### ### into torus 2-strand satellite                                         ### ### *)
(* ### vv Get all the precomputed whiteheadized torus[2] ### *)
Module[{i},
       For[i = -15, i <= 15, i = i + 2,
           Get[CCCDataDir <> StringTemplate["/kh-red-precomp-whiteheadized-torus-2-``.m"][i]]]];

(* Module[{p, *)
(*         fd = OpenWrite["/tmp/precalculation.log"]}, *)
(*        For[p = -3, p >= -15, p = p - 2, *)
(*            WriteString[fd, StringTemplate["Calculating: ``"][p]]; *)
(*            PrecalculateKhRedWhdTorusKnotPDsLine[2, p, -2 - p, 20, 2]]; *)
(*        For[p = 1, p <= 15, p = p + 2, *)
(*            PrecalculateKhRedWhdTorusKnotPDsLine[2, p, 4 - p, 20, 2]]; *)
(*        Close[fd]; *)
(*       ]; *)

(* ### ### ### ### *)
(* ### ### whiteheadized evolutions for 2-strand torus knots ### ### *)
(* ### p = -1: n* = -1 ### *)
(* ### p = -3: n* = 1 ### *)
(* ### p = -5: n* = 3 ### *)
(* ### p = -7: n* = 5 ### *)
(* ### p = -9: n* = 7 ### *)
(* ### p = -11: n* = 9 ### *)
(* ### p = -13: n* = 11 ### *)
(* ### p = -15: n* = 13 ### *)
(* ### general formula: -2 - p ### *)

(* ### p = 1: n* = 3 ### *)
(* ### p = 3: n* = 1 ### *)
(* ### p = 5: n* = -1 ### *)
(* ### p = 7: n* = -3 ### *)
(* ### p = 9: n* = -5 ### *)
(* ### general formula: 4 - p ### *)

(* ### I notice that values of jumps are *the same* for all p ### *)

(* ### vv Find eigenvalues and position of jumps ### *)
Module[{k},
       Table[Block[{p = 15, delta},
                   (* ### vv For negative `p` ### *)
                   (* delta = -22 - p; *)
                   (* ### vv For positive `p` ### *)
                   delta = -16 - p;
                   Module[{fun, fun1, fun2, fun3, fun4, fun5},
                          fun = Function[{k}, PrecompKhRed["w", TorusKnot[2, p], delta + 2 k]];
                          fun1 = Function[{k}, Expand[FS[fun[k+1] - fun[k]]]];
                          fun2 = Function[{k}, Expand[FS[fun1[k+1] - t^(-2) q^(-4) fun1[k]]]];
                          (* fun3 = Function[{k}, Expand[FS[fun2[k+1] - q^6 fun2[k]]]]; *)
                          (* fun4 = Function[{k}, Expand[FS[fun3[k+1] - q^10 fun3[k]]]]; *)
                          fun2[k]
                         ]],
             {k, 0, 18}]]                                                                                                                                       
theP = -15;
(* ### vv Find evolution ### *)
Block[{p = theP, delta = aa, delta1 = bb,
       theExtraPts = 8},
      (* ### vv These are for positive `p` ### *)
      (* delta = -16 - p; *)
      (* delta1 = 4 - p; *)
      (* ### vv These are for negative `p` ### *)
      delta = -22 - p;
      delta1 = -2 - p;
      TheFun[nCrosses_] :=
      PrecompKhRed["w", TorusKnot[2, p], nCrosses];
      ansMinus = Block[{extraPoints = theExtraPts},
                       With[{aSeries = delta + 2 k},
                            FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                                      Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                             Join[{aSeries}, {1, t^(-1) q^(-2)}]]]];
      ansPlus = Block[{extraPoints = theExtraPts},
                      With[{aSeries = delta1 + 2 k},
                           FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                                     Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                            Join[{aSeries}, {1, t^(-1) q^(-2)}]]]]];
(* ### vv Check plus ### *)
Module[{n},
       Block[{p = theP},
             Table[FS[((AA[1] 1^n + AA[2] (t^(-1) q^(-2))^n) /. ansPlus)
                      - PrecompKhRed["w", TorusKnot[2, p], n] /. {q -> Pi, t -> E}],
                   {n, 4 - p, 4 - p + 10, 2}]]];
(* ### vv Check minus ### *)
Module[{n},
       Block[{p = theP},
             Table[FS[((AA[1] 1^n + AA[2] (t^(-1) q^(-2))^n) /. ansMinus)
                      - PrecompKhRed["w", TorusKnot[2, p], n] /. {q -> Pi, t -> E}],
                   {n, -2 - p, -2 - p - 10, -2}]]];
(* ### vv Dump evolution formulas ### *)
Block[{p = theP, posBound = aa},
      (* ### vv This is for positive `p` ### *)
      (* posBound = 4 - p; *)
      (* ### vv This is for negative `p` ### *)
      posBound = -2 - p;
      Module[{fd = OpenWrite[CCCDataDir <> StringTemplate["/kh-red-1evo-wh-torus-2-``.m"][p]],
              eigenValues = {1, t^(-1) q^(-2)}},
             Module[{exprPlus = (Plus @@ Map[eigenValues[[#]]^n AA[#] &, Range[1, Length[eigenValues]]]
                                 /. ansPlus),
                     exprMinus = (Plus @@ Map[eigenValues[[#]]^n AA[#] &, Range[1, Length[eigenValues]]]
                                  /. ansMinus)},
                    WriteString[fd, StringTemplate["(* ### Positive starts at n = `` ### *)\n"][posBound]];
                    WriteString[fd, StringTemplate["Kh1EvoRed[\"w\", Torus[``,``], \"plus\"] := ``;\n"]
                                [2, p, ToString[exprPlus, InputForm]]];
                    WriteString[fd, StringTemplate["Kh1EvoRed[\"w\", Torus[``,``], \"minus\"] := ``;\n"]
                                [2, p, ToString[exprMinus, InputForm]]]];
             Close[fd]]];



PyGetWhiteheadizedPD[PD[Knot[3,1]], 4, 6]

(* ### vv CURWORK ### *)
(* Module[{i, j}, *)
(*        For[i = 7, i <= 10, i ++, *)
(*            For[j = 1, j <= CCCRolfsenMults[[i - 2]], j ++, *)
(*                PrecalculateKhRedWhiteheadizedPDsLine[Knot[i, j], -10, 10, 2]]]]; *)


Module[{i},
       For[i = 1, i <= 8, i ++,
           PrecalculateKhRedTwistedTwoStrandPDsLine[2 i, -10 - 4 (i - 1) + 1, 12 - 4 (i - 1) + 1];
           PrecalculateKhRedTwistedTwoStrandPDsLine[-2 i, -10 + 4 (i - 1) + 1, 12 + 4 (i - 1) + 1]]];


Module[{i},
       For[i = 2, i <= 6, i ++,
           Block[{p = 2 i + 1},
                 PrecalculateKhRedTwStTorusKnotPDsLine[2, p, 4 - p - 10, 4 - p + 10, 2]];
           Block[{p = - 2 i - 1},
                 PrecalculateKhRedTwStTorusKnotPDsLine[2, p, 4 - p - 10, 4 - p + 10, 2]]]];

(* ### vv This interval of shifts is for positive `p` ### *)
Module[{fd = OpenWrite["/tmp/precalculation.log"]},
       For[p = 1, p >= -19, p = p - 2,
           WriteString[fd, StringTemplate["Calculating ``\n"][p]];
           PrecalculateKhRedTwStTorusKnotPDsLine[2, p, 4 - p - 10, 4 - p + 10, 2]]];

(* ### vv This interval of shifts is for `p` around zero. ### *)
Module[{fd = OpenWrite["/tmp/precalculation.log"]},
       For[p = -1, p <= 1, p = p + 2,
           WriteString[fd, StringTemplate["Calculating ``\n"][p]];
           PrecalculateKhRedTwStTorusKnotPDsLine[2, p, -4 - p - 10, 4 - p + 10, 2]]];

(* ### vv This interval of shifts is for negative `p` ### *)
Module[{fd = OpenWrite["/tmp/precalculation.log"]},
       For[p = -5, p >= -19, p = p - 2,
           WriteString[fd, StringTemplate["Calculating ``\n"][p]];
           PrecalculateKhRedTwStTorusKnotPDsLine[2, p, -4 - p - 10, -4 - p + 10, 2]];
       Close[fd]];

(* ### ### vv Calculating reduced Khovanovs for twist knots with torus cable block ### ### *)
(* ### vv This interval of shifts is for positive `p` ### *)
Module[{fd = OpenWrite["/tmp/precalculation.log"]},
       For[p = 9, p <= 19, p = p + 2,
           WriteString[fd, StringTemplate["Calculating ``\n"][p]];
           PrecalculateKhRedTwistedTwoStrandPDsLine[p, 3 - 2 p - 8, 3 - 2 p + 8]];
       Close[fd]];
(* ### vv This interval of shifts is for negative `p` ### *)
Module[{fd = OpenWrite["/tmp/precalculation.log"]},
       For[p = -9, p >= -19, p = p - 2,
           WriteString[fd, StringTemplate["Calculating ``\n"][p]];
           PrecalculateKhRedTwistedTwoStrandPDsLine[p, -3 - 2 p - 8, -3 - 2 p + 8]];
       Close[fd]];

[Calculating...]


(* ### vv Now we load the raw precalculated data ### *)
Module[{i},
       For[i = 3, i <= 7, i = i + 2,
           Get[CCCDataDir <> StringTemplate["/kh-red-precomp-twst-twist-``.m"][i]]]];
Module[{i},
       For[i = -3, i >= -7, i = i - 2,
           Get[CCCDataDir <> StringTemplate["/kh-red-precomp-twst-twist-``.m"][i]]]];


(* ### vv Find eigenvalues and position of a jump ### *)
Block[{k = 7, p = -7, delta = -3},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, PrecompKhRed[TWSTTwisted[p], delta + 2 k]];
             fun1 = Function[{k}, Expand[FS[fun[k+1] - q^2 fun[k]]]];
             fun2 = Function[{k}, Expand[FS[fun1[k+1] - t^2 q^6fun1[k]]]];
             (* fun3 = Function[{k}, Expand[FS[fun2[k+1] - q^6 fun2[k]]]]; *)
             (* fun4 = Function[{k}, Expand[FS[fun3[k+1] - q^10 fun3[k]]]]; *)
             fun2[k]
            ]]




(* ### ### vv Calculating reduced Khovanovs for twist knots with whitehead block ### ### *)
(* ### vv This interval of shifts is for positive `p` ### *)
Module[{fd = OpenWrite["/tmp/precalculation.log"]},
       For[p = 1, p <= 3, p = p + 2,
           WriteString[fd, StringTemplate["Calculating ``\n"][p]];
           PrecalculateKhRedTwistedPDsLine[p, 4 - p - 12, 4 - p + 12]];
       Close[fd]];

(* ### vv This interval of shifts is for negative `p` ### *)
Module[{fd = OpenWrite["/tmp/precalculation.log"]},
       For[p = 1, p <= 3, p = p + 2,
           WriteString[fd, StringTemplate["Calculating ``\n"][p]];
           PrecalculateKhRedTwistedPDsLine[p, 4 - p - 12, 4 - p + 12]];
       Close[fd]];


(* ### vv Now we load the raw precalculated data ### *)
Module[{i},
       For[i = -1, i <= -1, i = i + 2,
           Get[CCCDataDir <> StringTemplate["/kh-red-precomp-whiteheadized-twist-``.m"][i]]]];

(* ### vv Find eigenvalues and position of a jump ### *)
Block[{k = -4, p = 7, delta = -3},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, PrecompKhRed[Twisted[p], delta + 2 k]];
             fun1 = Function[{k}, Expand[FS[fun[k+1] - t^(-2) q^(-4) fun[k]]]];
             fun2 = Function[{k}, Expand[FS[fun1[k+1] - fun1[k]]]];
             (* fun3 = Function[{k}, Expand[FS[fun2[k+1] - q^6 fun2[k]]]]; *)
             (* fun4 = Function[{k}, Expand[FS[fun3[k+1] - q^10 fun3[k]]]]; *)
             fun2[k]
            ]]



(* ### ### vv Calculating reduced Khovanovs for 2-strand torus knots with whitehead block ### ### *)
(* ### vv This interval of shifts is for positive `p` ### *)
Module[{fd = OpenWrite["/tmp/precalculation.log"]},
       For[p = 17, p <= 19, p = p + 2,
           WriteString[fd, StringTemplate["Calculating ``\n"][p]];
           PrecalculateKhRedWhdTorusKnotPDsLine[2, p, 4 - p, 6, 2]];
       Close[fd]];


(* ### vv This interval of shifts is for negative `p` ### *)
Module[{fd = OpenWrite["/tmp/precalculation.log"]},
       For[p = -1, p >= -19, p = p - 2,
           WriteString[fd, StringTemplate["Calculating ``\n"][p]];
           PrecalculateKhRedWhdTorusKnotPDsLine[2, p, - 2 - p, 6, 2]]];


(* ### vv Now we load the raw precalculated data ### *)
Module[{i},
       For[i = 1, i <= 19, i = i + 2,
           Get[CCCDataDir <> StringTemplate["/kh-red-precomp-whiteheadized-torus-2-``.m"][i]]]];

(* ### vv Now we load the raw precalculated data ### *)
Module[{i},
       For[i = -1, i >= -19, i = i - 2,
           Get[CCCDataDir <> StringTemplate["/kh-red-precomp-whiteheadized-torus-2-``.m"][i]]]];


(* ### vv Find eigenvalues and position of a jump ### *)
Block[{k = 1, p = -3, delta = -1},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, PrecompKhRed[TorusKnot[2, p], delta + 2 k]];
             fun1 = Function[{k}, Expand[FS[fun[k+1] - t^(-2) q^(-4) fun[k]]]];
             fun2 = Function[{k}, Expand[FS[fun1[k+1] - fun1[k]]]];
             (* fun3 = Function[{k}, Expand[FS[fun2[k+1] - q^6 fun2[k]]]]; *)
             (* fun4 = Function[{k}, Expand[FS[fun3[k+1] - q^10 fun3[k]]]]; *)
             fun2[k]
            ]]




Block[{p = 1, i = 1},
      (* br = BR[2, ConstLst[If[p > 0, -1, 1], Abs[p]]]; *)
      br = BR[2, {-1, 1, -1}];
      Print[br];
      PyGetTwostrandedPD[PD[br], i]
     ]


(* ### vv Establish eigenvalues ### *)
Block[{k = 19,delta = -19},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, Coefficient[Kh1EvoRed[Torus[2,delta + 2 k],"plus"] /. {(q^3 t)^n :> AA},
                                             AA, 1]];
             fun1 = Function[{k}, Expand[FS[fun[k+1] - t^(-4) q^(-12) fun[k]]]];
             fun1[k]
            ]]


Block[{k = 16, delta = -19},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k},
                            Expand[FS[(1 - q^2 t)/(1 - q^2 t + q^4 t^2) q^(-n)
                                      Coefficient[Kh1EvoRed[Torus[2,delta + 2 k],"plus"] /. {(q^3 t)^n :> AA},
                                                  AA, 0]]]];
             fun1 = Function[{k}, Expand[FS[fun[k+1] - q^(-8) fun[k]]]];
             fun2 = Function[{k}, Expand[FS[fun1[k+1] - q^(-16) t^(-6) fun1[k]]]];
             fun3 = Function[{k}, Expand[FS[fun2[k+1] - q^(-20) t^(-8) fun2[k]]]];
             fun3[k]
            ]]


Block[{k = 19, delta = -19},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, Coefficient[Kh1EvoRed[Torus[2,delta + 2 k],"minus"] /. {(q^3 t)^n :> AA},
                                             AA, 1]];
             fun1 = Function[{k}, Expand[FS[fun[k+1] - t^(-4) q^(-12) fun[k]]]];
             fun1[k]
            ]]

Block[{k = 16, delta = -19},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k},
                            Expand[FS[(1 - q^2 t)/(1 - q^2 t + q^4 t^2) q^(-n)
                                      Coefficient[Kh1EvoRed[Torus[2,delta + 2 k],"minus"] /. {(q^3 t)^n :> AA},
                                                  AA, 0]]]];
             fun1 = Function[{k}, Expand[FS[fun[k+1] - q^(-8) fun[k]]]];
             fun2 = Function[{k}, Expand[FS[fun1[k+1] - q^(-16) t^(-6) fun1[k]]]];
             fun3 = Function[{k}, Expand[FS[fun2[k+1] - q^(-20) t^(-8) fun2[k]]]];
             fun3[k]
            ]]



ansPlus["plus", t q^3]


ansMinus["plus", t q^3]


ansPlus["minus", t q^3]


ansMinus["minus", t q^3]




ansPlus["plus", q]


ansMinus["plus", q]


ansPlus["minus", q]


ansMinus["minus", q]



(* Block[{p = -19}, *)
(*       (\* PrecalculateKhRedTwStTorusKnotPDsLine[2, p, 4 - p - 10, 4 - p + 10, 2]; *\) *)
(*       Get[CCCDataDir <> StringTemplate["/kh-red-precomp-twst-torus-2-``.m"][p]]; *)
(*       (\* (\\* ### vv Establish eigenvalues ### *\\) *\) *)
(*       (\* Block[{k = 6, p = -3, delta = -11}, *\) *)
(*       (\*       Module[{fun, fun1, fun2, fun3, fun4, fun5}, *\) *)
(*       (\*              fun = Function[{k}, PrecompKhRed[TorusKnotTwSt[2, p], delta + 2 k]]; *\) *)
(*       (\*              fun1 = Function[{k}, Expand[FS[fun[k+1] - t^2 q^6 fun[k]]]]; *\) *)
(*       (\*              fun2 = Function[{k}, Expand[FS[fun1[k+1] - q^2 fun1[k]]]]; *\) *)
(*       (\*              (\\* fun3 = Function[{k}, Expand[FS[fun2[k+1] - q^6 fun2[k]]]]; *\\) *\) *)
(*       (\*              (\\* fun4 = Function[{k}, Expand[FS[fun3[k+1] - q^10 fun3[k]]]]; *\\) *\) *)
(*       (\*              fun2[k] *\) *)
(*       (\*             ]] *\) *)
(*       (\* ### vv Find evolution ### *\) *)
(*       Block[{(\* p = -3, *\) delta = aa, delta1 = bb}, *)
(*             (\* ### vv These are for positive `p` ### *\) *)
(*             (\* delta = -6 - p; *\) *)
(*             (\* delta1 = 4 - p; *\) *)
(*             (\* ### vv These are for negative `p` ### *\) *)
(*             delta = -12 - p; *)
(*             delta1 = -2 - p; *)
(*             TheFun[nCrosses_] := *)
(*             PrecompKhRed[TorusKnotTwSt[2, p], nCrosses]; *)
(*             ansMinus = Block[{extraPoints = 3}, *)
(*                              With[{aSeries = delta + 2 k}, *)
(*                                   FitFamilyWithEigenvaluesAdvanced[Function[{k1}, *)
(*                                                                             Expand[FS[TheFun[aSeries /. {k -> k1}]]]], *)
(*                                                                    Join[{aSeries},{q, t q^3}]]]]; *)
(*             ansPlus = Block[{extraPoints = 3}, *)
(*                             With[{aSeries = delta1 + 2 k}, *)
(*                                  FitFamilyWithEigenvaluesAdvanced[Function[{k1}, *)
(*                                                                            Expand[FS[TheFun[aSeries /. {k -> k1}]]]], *)
(*                                                                   Join[{aSeries},{q, t q^3}]]]]]; *)
(*       (\* (\\* ### vv Check minus ### *\\) *\) *)
(*       (\* Block[{n = 3, p = -5}, *\) *)
(*       (\*       FS[((AA[1] q^n + AA[2] (t q^3)^n) /. ansMinus) *\) *)
(*       (\*          - PrecompKhRed[TorusKnotTwSt[2, p], n]]] *\) *)
(*       (\* (\\* ### vv Check plus ### *\\) *\) *)
(*       (\* Block[{n = 9, p = -3}, *\) *)
(*       (\*       FS[((AA[1] q^n + AA[2] (t q^3)^n) /. ansPlus) *\) *)
(*       (\*          - PrecompKhRed[TorusKnotTwSt[2, p], n]]] *\) *)
(*       (\* ### vv Dump evolution formulas ### *\) *)
(*       Block[{(\* p = -3, *\) posBound = aa}, *)
(*             (\* ### vv This is for positive `p` ### *\) *)
(*             (\* posBound = 4 - p; *\) *)
(*             (\* ### vv This is for negative `p` ### *\) *)
(*             posBound = -2 - p; *)
(*             Module[{fd = OpenWrite[CCCDataDir <> StringTemplate["/kh-red-1evo-torus-2-``.m"][p]], *)
(*                     eigenValues = {q, t q^3}}, *)
(*                    Module[{exprPlus = (Plus @@ Map[eigenValues[[#]]^n AA[#] &, Range[1, Length[eigenValues]]] *)
(*                                        /. ansPlus), *)
(*                            exprMinus = (Plus @@ Map[eigenValues[[#]]^n AA[#] &, Range[1, Length[eigenValues]]] *)
(*                                         /. ansMinus)}, *)
(*                           WriteString[fd, StringTemplate["(\* ### Positive starts at n = `` ### *\)\n"][posBound]]; *)
(*                           WriteString[fd, StringTemplate["Kh1EvoRed[Torus[``,``],\"plus\"] := ``;\n"] *)
(*                                       [2, p, ToString[exprPlus, InputForm]]]; *)
(*                           WriteString[fd, StringTemplate["Kh1EvoRed[Torus[``,``],\"minus\"] := ``;\n"] *)
(*                                       [2, p, ToString[exprMinus, InputForm]]]]; *)
(*                    Close[fd]]] *)
(*      ]; *)

               Block[{p = 1},
                     (* PrecalculateKhRedTwStTorusKnotPDsLine[2, p, 4 - p - 10, 4 - p + 10, 2]; *)
                     Get[CCCDataDir <> StringTemplate["/kh-red-precomp-twst-torus-2-``.m"][p]]];

     
      (* ### vv Establish eigenvalues ### *)
      Block[{k = 9, p = 1, delta = -15},
            Module[{fun, fun1, fun2, fun3, fun4, fun5},
                   fun = Function[{k}, PrecompKhRed[TorusKnotTwSt[2, p], delta + 2 k]];
                   fun1 = Function[{k}, Expand[FS[fun[k+1] - t^2 q^6 fun[k]]]];
                   fun2 = Function[{k}, Expand[FS[fun1[k+1] - q^2 fun1[k]]]];
                   (* fun3 = Function[{k}, Expand[FS[fun2[k+1] - q^6 fun2[k]]]]; *)
                   (* fun4 = Function[{k}, Expand[FS[fun3[k+1] - q^10 fun3[k]]]]; *)
                   fun2[k]
                  ]]
      
      (* ### vv Find evolution ### *)
      Block[{p = 1, delta = aa, delta1 = bb},
            (* ### vv These are for positive `p` ### *)
            (* delta = -6 - p; *)
            (* delta1 = 4 - p; *)
            (* ### vv These are for negative `p` ### *)
            (* delta = -12 - p; *)
            (* delta1 = -2 - p; *)
            delta = -15;
            delta1 = 3;
            TheFun[nCrosses_] :=
            PrecompKhRed[TorusKnotTwSt[2, p], nCrosses];
            ansMinus = Block[{extraPoints = 3},
                             With[{aSeries = delta + 2 k},
                                  FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                                            Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                                   Join[{aSeries},{q, t q^3}]]]];
            ansPlus = Block[{extraPoints = 3},
                            With[{aSeries = delta1 + 2 k},
                                 FitFamilyWithEigenvaluesAdvanced[Function[{k1},
                                                                           Expand[FS[TheFun[aSeries /. {k -> k1}]]]],
                                                                  Join[{aSeries},{q, t q^3}]]]]];

      (* ### vv Check minus ### *)
      Block[{n = 1, p = 1},
            FS[((AA[1] q^n + AA[2] (t q^3)^n) /. ansMinus)
               - PrecompKhRed[TorusKnotTwSt[2, p], n]]]

      
      (* ### vv Check plus ### *)
      Block[{n = 3, p = 1},
            FS[((AA[1] q^n + AA[2] (t q^3)^n) /. ansPlus)
               - PrecompKhRed[TorusKnotTwSt[2, p], n]]]

      (* ### vv Dump evolution formulas ### *)
      Block[{p = 1, posBound = aa},
            (* ### vv This is for positive `p` ### *)
            (* posBound = 4 - p; *)
            (* ### vv This is for negative `p` ### *)
            (* posBound = -2 - p; *)
            (* posBound = -1; *)
            posBound = 3;
            Module[{fd = OpenWrite[CCCDataDir <> StringTemplate["/kh-red-1evo-torus-2-``.m"][p]],
                    eigenValues = {q, t q^3}},
                   Module[{exprPlus = (Plus @@ Map[eigenValues[[#]]^n AA[#] &, Range[1, Length[eigenValues]]]
                                       /. ansPlus),
                           exprMinus = (Plus @@ Map[eigenValues[[#]]^n AA[#] &, Range[1, Length[eigenValues]]]
                                        /. ansMinus)},
                          WriteString[fd, StringTemplate["(* ### Positive starts at n = `` ### *)\n"][posBound]];
                          WriteString[fd, StringTemplate["Kh1EvoRed[Torus[``,``],\"plus\"] := ``;\n"]
                                      [2, p, ToString[exprPlus, InputForm]]];
                          WriteString[fd, StringTemplate["Kh1EvoRed[Torus[``,``],\"minus\"] := ``;\n"]
                                      [2, p, ToString[exprMinus, InputForm]]]];
                   Close[fd]]]
      
      

      
(* PrecalculateKhRedWhiteheadizedPDsLine[Knot[8,7], -10, 10, 2] *)
(* str = KhReducedSL3[PD[BR[3,{1,2,1,2,2,2,2,2,2,2,2,2,2,2}]]]; *)

PrecalculateKhRedSL3TwistedPDsLine[2, -10, 12];

KhReducedSL3[PyGetTwistWhiteheadizedPD[2, 0] /. {ii_Integer :> ii + 1}]
