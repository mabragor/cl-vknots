
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
RectangularMirrorKnotPD[numberSeq1_, numberSeq2_] :=
    (* ### ^^ An interface to auxiliary Python code ### *)
    WithALock["rectangular-knot-pd", (* ### << Surely we need some synchronization as we run several things using this ### *)
              (* ###                       functionality in parallel. ### *)
              Module[{code},
                     (* ### vv Call a python part of the rig ### *)
                     code = Run[StringTemplate["python3 `pyDir``scriptName` `numberSeq1` `numberSeq2`> /dev/null"]
                                [<|"pyDir" -> CCCPythonDir, "scriptName" -> CCCScriptFname,
                                 "numberSeq1" -> numberSeq1, "numberSeq2" -> numberSeq2
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

(* ### Let's test how the set stream position works ### *)
Module[{fd = OpenWrite[CCCDataDir <> "/test.txt"]},
       WriteString[fd, "This is a first line\n"];
       Module[{position = StreamPosition[fd]},
              Print[position];
              For[i = 1, i <= 10, i ++,
                  WriteString[fd, StringTemplate["Now counting to ``\n"][i]];
                  Pause[1];
                  SetStreamPosition[fd, position]]];
       Close[fd]];

CCCDataDir

For[j = 5, j <= 20, j ++,
    Module[{fd = OpenWrite[CCCDataDir
                           <> StringTemplate["/rect-knot-random-mirror-kh``.txt"][j]],
            i,
            timeCap = 10},
           Block[{NumberLength = 2^j,
                  numFails = 0},
                 For[i = 1, i <= 100, i ++,
                     Module[{numberSeq1, expr, res},
                            numberSeq1 = (StringJoin
                                          @@ Module[{i}, Table[ToString[Random[Integer]],
                                                               {i, 1, NumberLength}]]);
                            expr = Jones[RectangularKnotPD[numberSeq1]][q];
                            If[1 === Expand[Simplify[expr]],
                               WriteLine[fd, ToString[i]],
                               Module[{numTries = 0},
                                      res = Timing[TimeConstrained[
                                          While[True,
                                                numTries += 1;
                                                Module[{numberSeq2 = (StringJoin
                                                                      @@ Module[{i}, Table[ToString[Random[Integer]],
                                                                                           {i, 1, NumberLength}]])},
                                                       expr = List @@ Jones[RectangularMirrorKnotPD[numberSeq1, numberSeq2]][q];
                                                       If[10 >= Length[expr],
                                                          Break[]]]],
                                          timeCap,
                                          Fail]];
                                      If[res[[2]] === Null,
                                         numFails = 0,
                                         numFails += 1];
                                      If[numFails >= 3,
                                         timeCap *= 2; numFails = 0];
                                      WriteLine[fd, StringTemplate["``: `` `` `` ``"][i, res[[1]], numTries,
                                                                                      If[Null === res[[2]],
                                                                                         "Success",
                                                                                         "Fail"],
                                                                                      timeCap]];
                           ]]]]];
           Close[fd]]];











Block[{NumberLength = 16},
      Module[{numberSeq1, numberSeq2, expr},
             numberSeq1 = (StringJoin
                           @@ Module[{i}, Table[ToString[Random[Integer]],
                                                {i, 1, NumberLength}]]);
             numberSeq2 = (StringJoin
                           @@ Module[{i}, Table[ToString[Random[Integer]],
                                                {i, 1, NumberLength}]]);
             expr = Jones[RectangularMirrorKnotPD[numberSeq1, numberSeq2]][q]]]






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
                            expr = Jones[RectangularKnotPD[numberSeq]][q];
                            If[1 === Expand[Simplify[expr]],
                               WriteString[fd,
                                           StringTemplate["``: ``\n"][i, ToString[numberSeq]]],
                               WriteString[fd,
                                           StringTemplate["``\n"][i]]
                              ]]]];
           Close[fd]]];



Jones[RectangularKnotPD["10100001"]][q]

             -2   1        2
Out[8]= 1 + q   - - - q + q
                  q

              -2   1           2
Out[7]= 1 + #1   - -- - #1 + #1  & 
                   #1

Out[6]= 1 & 

Out[5]= 1 & 

Out[4]= 1 & 

Out[3]= 1 & 



(* Kh[RectangularKnotPD["11"]][q,t] *)


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


