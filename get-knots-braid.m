$OldOutput = $Output;
$Output = {};
Quiet[<< KnotTheory`];
$Output = $OldOutput;

fd = OpenRead[DirectoryName[$InputFileName] <> "/lisp-out.txt"];
(* fdout = OpenWrite["~/code/superpolys/lisp-in.txt"]; *)

For[it = Read[fd], it =!= EndOfFile, it = Read[fd],
    WriteString["stdout", Quiet[BR[expr]]//InputForm, "\n"]];

Close[fd];
(* (\* Close[fdout]; *\) *)
