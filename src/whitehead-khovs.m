
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
    Module[{fd = OpenWrite[CCCDataDir <> "/kh-red-precomp-whiteheadized-" <> KnotToFname[knot] <> ".m"],
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
PrecalculateKhRedWhdTorusKnotPDsLine[2, p_, from_, to_, step_] :=
    (* ### ^^ Precalculate whiteheadized reduced Khovanov polynomials ### *)
    (* ###    for a 2-strand torus knot. ### *)
    (* ###    `from` and `to`-- winding iteration bounds ### *)
    (* ###    `p`            -- the number of windings of a torus knot. ### *)
    (* ###                      Convention is p --> BR[2, {-1}^p] (so that it matches with Rolfsen) ### *)
    Module[{fd = OpenAppend[CCCDataDir <> "/kh-red-precomp-whiteheadized-torus-2-" <> ToString[p] <> ".m"],
            br = BR[2, ConstLst[If[p > 0, -1, 1], Abs[p]]],
            i},
           For[i = from, i <= to, i = i + step,
               Module[{polly = KhReduced[PyGetWhiteheadizedPD[PD[br], i, 2] /. {ii_Integer :> ii + 1}][q, t]},
                      WriteString[fd, StringTemplate["PrecompKhRed[TorusKnot[2, `p`], `i`] := `expr`;\n"]
                                  [<|"p" -> p, "i" -> i, "expr" -> ToString[polly, InputForm]|>]]]];
           Close[fd]];
PrecalculateKhRedTwStTorusKnotPDsLine[2, p_, from_, to_, step_] :=
    (* ### ^^ Precalculate two-cabled reduced Khovanov polynomials ### *)
    (* ###    for a 2-strand torus knot. ### *)
    (* ###    `from` and `to`-- winding iteration bounds ### *)
    (* ###    `p`            -- the number of windings of a torus knot. ### *)
    (* ###                      Convention is p --> BR[2, {-1}^p] (so that it matches with Rolfsen) ### *)
    Module[{fd = OpenAppend[CCCDataDir <> "/kh-red-precomp-twst-torus-2-" <> ToString[p] <> ".m"],
            br = BR[2, ConstLst[If[p > 0, -1, 1], Abs[p]]],
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
    Module[{fd = OpenWrite[CCCDataDir <> "/kh-red-precomp-twisted-twisted-" <> ToString[twist] <> ".m"],
            i},
           For[i = from, i <= to, i = i + 2,
               Module[{polly = KhReduced[PyGetTwistWhiteheadizedPD[twist, i] /. {ii_Integer :> ii + 1}][q, t]},
                      WriteString[fd, "PrecompKhRed[Twisted[" <> ToString[twist] <> "], " <> ToString[i]
                                  <> "] := " <> ToString[polly, InputForm] <> ";\n"]]];
           Close[fd]];
PrecalculateKhRedTwistedTwoStrandPDsLine[twist_, from_, to_] :=
    (* ### ^^ Precalculate reduced Khovanov polynomials for twisted knots with two-strand insertion. ### *)
    (* ###    `from` and `to`-- winding iteration bounds for a child braid. ### *)
    (* ###    `twist`        -- winding of a parent braid. ### *)
    Module[{fd = OpenWrite[CCCDataDir <> "/kh-red-precomp-twisted-two-strand-" <> ToString[twist] <> ".m"],
            i},
           For[i = from, i <= to, i = i + 2,
               Module[{polly = KhReduced[PyGetTwistTwostrandedPD[twist, i] /. {ii_Integer :> ii + 1}][q, t]},
                      WriteString[fd, "PrecompKhRed[TwistedTwoSt[" <> ToString[twist] <> "], " <> ToString[i]
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
(* ### ^^ ENDLIB ### *)


PyGetWhiteheadizedPD[PD[Knot[3,1]], 4, 6]

(* ### vv CURWORK ### *)
Module[{i, j},
       For[i = 7, i <= 10, i ++,
           For[j = 1, j <= CCCRolfsenMults[[i - 2]], j ++,
               PrecalculateKhRedWhiteheadizedPDsLine[Knot[i, j], -10, 10, 2]]]];


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




(* PrecalculateKhRedWhiteheadizedPDsLine[Knot[8,7], -10, 10, 2] *)
(* str = KhReducedSL3[PD[BR[3,{1,2,1,2,2,2,2,2,2,2,2,2,2,2}]]]; *)

PrecalculateKhRedSL3TwistedPDsLine[2, -10, 12];

KhReducedSL3[PyGetTwistWhiteheadizedPD[2, 0] /. {ii_Integer :> ii + 1}]
