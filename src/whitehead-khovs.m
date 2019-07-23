
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
PrecalculateKhRedWhiteheadizedPDsLine[knot_, from_, to_] :=
    (* ### ^^ Precalculate whiteheadized reduced Khovanov polynomials specifically for a twisted line. ### *)
    (* ###    `from` and `to`-- winding iteration bounds ### *)
    (* ###    `knot`       -- a knot spec from a Rolfsen table ### *)
    Module[{fd = OpenWrite[CCCDataDir <> "/kh-red-precomp-whiteheadized-" <> KnotToFname[knot] <> ".m"],
            i},
           For[i = from, i <= to, i ++,
               Module[{polly = KhReduced[PyGetWhiteheadizedPD[knot, i, 2] /. {ii_Integer :> ii + 1}][q, t]},
                      WriteString[fd, "PrecompKhRed[" <> ToString[knot, InputForm] <> ", " <> ToString[i] <> ", " <> ToString[2]
                                  <> "] := " <> ToString[polly, InputForm] <> ";\n"]]];
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
(* ### ^^ ENDLIB ### *)

PyGetTwistWhiteheadizedPD[4, 2]

Module[{j},
       For[j = 8, j <= 16, j = j + 2,
           PrecalculateKhRedTwistedPDsLine[j, -12 - 2 (j - 8), -10 - 2 (j - 8)]]]

[Calculating...]


Module[{pp},
       For[p = 3, p <= 4, p ++,
           PrecalculateKhRedWhiteheadizedPDsLine[Knot[2 p + 1,1], -6 - 2 (p-2) , 6 - 2 (p-2)]]]

KhReduced[PyGetWhiteheadizedPD[Knot[9,1], 0, 2] /. {ii_Integer :> ii + 1}][q,t] // InputForm

Kh[PyGetWhiteheadizedPD[Knot[3,1], 0, 4] /. {i_Integer :> i + 1}][q, t]

aPD = PyGetWhiteheadizedPD[Knot[3,1], 0, 4]

aPD 

Out[27]= PD[X[12, 5, 13, 6], X[11, 25, 12, 24], X[17, 7, 18, 6], 
 
>    X[18, 23, 19, 24], X[8, 1, 9, 2], X[7, 29, 8, 28], X[21, 3, 22, 2], 
 
>    X[22, 27, 23, 28], X[4, 9, 5, 10], X[3, 21, 4, 20], X[25, 11, 26, 10], 
 
>    X[26, 19, 27, 20], X[16, 29, 17, 30], X[30, 15, 31, 16], 
 
>    X[14, 31, 15, 32], X[1, 14, 32, 13]]

Out[25]= PD[X[11, 4, 12, 5], X[10, 24, 11, 23], X[16, 6, 17, 5], 
 
>    X[17, 22, 18, 23], X[7, 0, 8, 1], X[6, 28, 7, 27], X[20, 2, 21, 1], 
 
>    X[21, 26, 22, 27], X[3, 8, 4, 9], X[2, 20, 3, 19], X[24, 10, 25, 9], 
 
>    X[25, 18, 26, 19], X[15, 28, 16, 29], X[29, 14, 30, 15], 
 
>    X[13, 30, 14, 31], X[0, 13, 31, 12]]

KhReduced[PD[Knot[3,1]]][q, t]
