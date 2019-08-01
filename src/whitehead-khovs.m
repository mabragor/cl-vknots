
(* ################################################################################ *)
(* ### In this file we investigate the whitehead (reduced) Khovanov polynomials ### *)
(* ################################################################################ *)

(* ### vv BEGINIMPORTS ### *)
<< "knot-theory-knovanov-ev-utils.m";
(* ### ^^ ENDIMPORTS ### *)

(* ### vv BEGINLIB ### *)
CCCPythonDir = "/home/popolit/code/planar-diagrams-py/";
CCCInputFname = "whiteheadize-pd-input.txt";
CCCOutputFname = "whiteheadize-pd-output.txt";
CCCScriptFname = "whiteheadize-pd.py";
CCCRolfsenMults = {1, 1, 2, 3, 7, 21, 49, 165};
CCCFoamhoPath = "/home/popolit/code/foamho-bin/foamho/foamho";
CCCFoamhoOutputFname = "/tmp/foamho-output.txt";
PyGetWhiteheadizedPD[knot_, aWind_, bWind_] :=
    (* ### ^^ Get a double-braid satellite of the given knot ### *)
    (* ###    `knot`  -- a knot in any form that can be fed into `PD` of the knot theory ### *)
    (* ###    `aWind` -- number of windings of the a-braid of the double-braid duo ### *)
    (* ###    `bWind` -- number of windings of the b-braid of the double-braid duo ### *)
    Module[{code, fdWrite, pd},
           (* ### vv dump planar diagram into a file ### *)
           fdWrite = OpenWrite[CCCPythonDir <> CCCInputFname];
           pd = PD[knot];
           WriteString[fdWrite, ToString[ReplacePart[pd, FirstPosition[pd, 1] -> 0], InputForm]];
           Close[fdWrite];
           (* ### vv Call a python part of the rig ### *)
           code = Run["python2 " <> CCCPythonDir <> CCCScriptFname <> " whiteheadize " <> ToString[aWind] <> " " <> ToString[bWind]
                      <> " > /dev/null"];
           If[0 =!= code,
              Message[PyGetWhiteheadizedPD::someThingWrongPython],
              (* ### vv Read the whiteheadized diagram from the file ### *)
              Get[CCCPythonDir <> CCCOutputFname]]];
PyGetTwistWhiteheadizedPD[parentWind_, childWind_] :=
    (* ### ^^ Get a twist satellite of a twist knot. Diagram is completely constructed on the Python side. ### *)
    (* ###    `parentWind` -- number of windings in the parent twist knot's 2-strand braid ### *)
    (* ###    `childWind`  -- number of windings in the child twist knot's 2-strand braid  ### *)
    Module[{code, fdWrite},
           (* ### vv Call a python part of the rig ### *)
           code = Run["python2 " <> CCCPythonDir <> CCCScriptFname <> " twist "
                      <> ToString[parentWind] <> " " <> ToString[childWind]
                      <> " > /dev/null"];
           If[0 =!= code,
              Message[PyGetWhiteheadizedPD::someThingWrongPython],
              (* ### vv Read the whiteheadized diagram from the file ### *)
              Get[CCCPythonDir <> CCCOutputFname]]];
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
    (* ### ^^ Precalculate whiteheadized reduced Khovanov polynomials specifically for a twisted line, ### *)
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
                                  [<|"p" -> p, "i" -> i, "expr" -> ToString[polly, InputForm]]]]];
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


(* ### vv CURWORK ### *)
Module[{i, j},
       For[i = 7, i <= 10, i ++,
           For[j = 1, j <= CCCRolfsenMults[[i - 2]], j ++,
               PrecalculateKhRedWhiteheadizedPDsLine[Knot[i, j], -10, 10, 2]]]];


(* PrecalculateKhRedWhiteheadizedPDsLine[Knot[8,7], -10, 10, 2] *)
(* str = KhReducedSL3[PD[BR[3,{1,2,1,2,2,2,2,2,2,2,2,2,2,2}]]]; *)

Module[{i},
       For[i = 1, i <= 8, i ++,
           PrecalculateKhRedSL3TwistedPDsLine[2 i, -6 - 4 i, 16 - 4 i]]];


KhReducedSL3[PD[Knot[4,1]]]

aaa = KhReducedSL3[PyGetTwistWhiteheadizedPD[2, 0] /. {ii_Integer :> ii + 1}];

Error 34 occurred. Either your input is not a link diagram, or this is a bug.

KhReducedSL3::foamhoFailed: -- Message text not found --


PDToFoamhoString[PyGetTwistWhiteheadizedPD[2, 0] /. {ii_Integer :> ii + 1}] // InputForm

Out[4]//InputForm= 
"[[16,29,17,30],[15,7,16,6],[19,31,20,30],[20,5,21,6],[28,13,29,14],[27,23,28\
,22],[7,15,8,14],[8,21,9,22],[11,35,12,34],[24,33,25,34],[12,1,13,2],[23,3,24\
,2],[31,11,32,10],[4,9,5,10],[32,25,33,26],[3,27,4,26],[18,35,19,36],[1,18,36\
,17]]"

Out[3]= [[16,29,17,30],[15,7,16,6],[19,31,20,30],[20,5,21,6],[28,13,29,14],[2\
 
>    7,23,28,22],[7,15,8,14],[8,21,9,22],[11,35,12,34],[24,33,25,34],[12,1,13\
 
>    ,2],[23,3,24,2],[31,11,32,10],[4,9,5,10],[32,25,33,26],[3,27,4,26],[18,3\
 
>    5,19,36],[1,18,36,17]]
