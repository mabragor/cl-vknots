$OldOutput = $Output;
$Output = {};
Quiet[<< KnotTheory`];
$Output = $OldOutput;

fd = OpenRead[DirectoryName[$InputFileName] <> "/lisp-out.txt"];
(* fdout = OpenWrite["~/code/superpolys/lisp-in.txt"]; *)

For[it = Read[fd], it =!= EndOfFile, it = Read[fd],
    WriteString["stdout", Quiet[BR[expr]]//InputForm, "\n"];
    (* WriteString["stdout", "caboom\n"];*)
   ];
(* ### vv KLUDGE to work around mathematica error messages at the end ### *)
WriteString["stdout", "TheRealEnd"];

Close[fd];
(* (\* Close[fdout]; *\) *)
