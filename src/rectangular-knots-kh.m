
(* ### vv BEGINIMPORTS ### *)
Quiet[<< KnotTheory`];
<< "file-locks.m";
(* ### ^^ ENDIMPORTS ### *)

(* ### vv BEGINLIB ### *)
CCCWorkDir = "/home/popolit/quicklisp/local-projects/cl-vknots";
CCCDataDir = CCCWorkDir <> "/data";
CCCPythonDir = "/home/popolit/code/planar-diagrams-py/";
CCCScriptFname = "rectangular-knot.py";
CCCOutputFname = "rectangular-knot-output.txt";
RectangularKnotPD[number_] :=
    (* ### ^^ An interface to auxiliary Python code ### *)
    WithALock["rectangular-knot-pd", (* ### << Surely we need some synchronization as we run several things using this ### *)
              (* ###                       functionality in parallel. ### *)
              Module[{code},
                     (* ### vv Call a python part of the rig ### *)
                     code = Run[StringTemplate["python3 `pyDir``scriptName` `number` > /dev/null"]
                                [<|"pyDir" -> CCCPythonDir, "scriptName" -> CCCScriptFname,
                                 "number" -> number
                                 |>]];
                     If[0 =!= code,
                        Message[PyCallRectangularKnot::someThingWrongPython],
                        (* ### vv Read the whiteheadized diagram from the file ### *)
                        Get[CCCPythonDir <> CCCOutputFname]]]];
NumberLength = 8;
LargeRandomInteger[] :=
    Module[{randSeq, randNum},
           randSeq = Module[{i}, Table[Random[Integer], {i, 1, NumberLength}]];
           randNum = Module[{i, acc = 0},
                            For[i = 1, i <= NumberLength, i ++,
                                acc += randSeq[[i]] * 2^(i - 1)];
                            acc];
           randNum];
(* ### ^^ ENDLIB ### *)

For[j = 1, j <= 20, j ++,
    Module[{fd = OpenWrite[CCCDataDir
                           <> StringTemplate["/rect-knot-random-kh``.txt"][j]],
            i},
           Block[{NumberLength = 2^j},
                 For[i = 1, i <= 1000, i ++,
                     Module[{number, expr},
                            numberSeq = (StringJoin
                                         @@ Module[{i}, Table[ToString[Random[Integer]],
                                                              {i, 1, NumberLength}]]);
                            expr = Kh[RectangularKnotPD[numberSeq]][q,t];
                            If[q^(-1) + q === Expand[Simplify[expr]],
                               WriteString[fd,
                                           StringTemplate["``: ``\n"][i, ToString[numberSeq]]],
                               WriteString[fd,
                                           StringTemplate["``\n"][i]]
                              ]]]];
           Close[fd]]];



(* RectangularKnotPD["0001000001001010010100111000011001110001001000001111000010101101011001101101010011001000111100001000111011111111010000110001000101011110111101000000111001110111001010010100101110101000000101010100101000101111100001011001011001101100100100000111010110110010011110001000101110101011000111101111001111001110011111001111001000110111000010001010110001101100100011111001011010111111001100010000010000111000100001000010110001001011111000100110100010011000011110111011101110001111100110110011110001001111110001011011110001000110111010010000011011100011000001010110011110110001110110000011010000100001110101111100110100111101110011111101101010010010000001000011001010101010100111000011100001000111101001010001011011101010001110010011110111111001011100000001010101010110000000101000000010010100100101011110010011010001101101000000001111000100000000010100111110100101011111111101101011111010100100010000010110001000111110001001100110001001110111001111111111011110111111000010111111110101000011011101010011100010011010000101011011010001"] *)



(* ToString[LargeRandomInteger[] // InputForm] *)
(* IntegerDigits[1024,2] *)


For[j = 21, j <= 40, j ++,
    Module[{fd = OpenWrite[CCCDataDir
                           <> StringTemplate["/rect-knot-kh``000.txt"][j]],
            i},
           For[i = j * 1000, i <= (j+1) * 1000, i ++,
               Module[{expr = Kh[RectangularKnotPD[
                   StringJoin @@ Map[ToString, IntegerDigits[i, 2]]]][q,t]},
                      WriteString[fd, ToString[i] <> ": "
                                  <> ToString[expr, InputForm]
                                  <> "\n"
                                 ]]];
           Close[fd]]];


