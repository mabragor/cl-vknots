
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
           code = Run["python2 " <> CCCPythonDir <> CCCScriptFname <> " " <> ToString[aWind] <> " " <> ToString[bWind]
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
KnotToFname[Knot[a_, b_]] :=
    ("rolfsen-knot-" <> ToString[a] <> "-" <> ToString[b]);
(* ### ^^ ENDLIB ### *)

(* ### vv CURWORK ### *)
CCCRolfsenMults = {1, 1, 2, 3, 7, 21, 49, 165};
Module[{i, j},
       For[i = 5, i <= 10, i ++,
           For[j = 1, j <= CCCRolfsenMults[[i - 2]], j ++,
               PrecalculateKhRedWhiteheadizedPDs[Knot[i, j], 10]]]];



