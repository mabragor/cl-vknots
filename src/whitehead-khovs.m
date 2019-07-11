
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
    Module[{code, fdWrite},
           (* ### vv dump planar diagram into a file ### *)
           fdWrite = OpenWrite[CCCPythonDir <> CCCInputFname];
           WriteString[fdWrite, ToString[PD[knot], InputForm]];
           Close[fdWrite];
           (* ### vv Call a python part of the rig ### *)
           code = Run["python2 " <> CCCPythonDir <> CCCScriptFname <> " " <> ToString[aWind] <> " " <> ToString[bWind]];
           If[0 =!= code,
              Message[PyGetWhiteheadizedPD::someThingWrongPython],
              (* ### vv Read the whiteheadized diagram from the file ### *)
              Get[CCCPythonDir <> CCCOutputFname]]];
(* ### ^^ ENDLIB ### *)

PyGetWhiteheadizedPD[Knot[3,1], 2,4]

KnotTheory::loading: Loading precomputed data in PD4Knots`.

StringJoin::string: 
   String expected at position 2 in 
    python2 /home/popolit/code/planar-diagrams-py/<>CCCScriptName<> 2 4.
/usr/bin/python2: can't find '__main__' module in '/home/popolit/code/planar-diagrams-py/'

PyGetWhiteheadizedPD::someThingWrongPython: -- Message text not found --

