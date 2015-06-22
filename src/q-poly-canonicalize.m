
q[x_] := (q^x - q^(-x))/(q - q^(-1));
     
fd = OpenRead[DirectoryName[$InputFileName] <> "/lisp-out.txt"];

For[it = Read[fd], it =!= EndOfFile, it = Read[fd],
    WriteString["stdout",
		Factor[Simplify[expr]] // InputForm, "\n"]];

Close[fd];
(* Close[fdout]; *)
