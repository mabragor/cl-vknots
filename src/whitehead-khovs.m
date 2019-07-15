
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

PrecalculateKhRedWhiteheadizedPDs[Knot[3,1], 0]

KnotTheory::loading: Loading precomputed data in PD4Knots`.

Out[3]= /home/popolit/quicklisp/local-projects/cl-vknots/datakh-red-precomp-w\
 
>    hiteheadized-rolfsen-knot-3-1.m


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
