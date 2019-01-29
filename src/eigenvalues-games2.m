
fundamentalEigenvaluePool = {q, t q^3, -t q^3};
(* RotatedEigs[eig1_, eig2_, cos_] := *)
(*     {{eig1 cos^2 + eig2 (1 - cos^2), cos Sqrt[1 - cos^2] (-eig1 + eig2)}, *)
(*      {cos Sqrt[1 - cos^2] (-eig1 + eig2), eig1 (1 - cos^2) + eig2 cos^2}}; *)
(* twoByTwoBlockPairs = *)
(*     Map[{{{#[[1]], 0}, {0, #[[2]]}}, *)
(* 	 RotatedEigs[#[[1]], #[[2]], x1]} &, *)
(* 	Tuples[fundamentalEigenvaluePool, 2]]; *)
RotationMat[2] :=
    Function[{c1},
	     With[{s1 = Sqrt[1 - c1^2]},
		  {{c1, -s1}, {s1, c1}}]];
RotationMat[3] :=
    Function[{c1, c2, c3},
	     With[{s1 = Sqrt[1 - c1^2],
		   s2 = Sqrt[1 - c2^2],
		   s3 = Sqrt[1 - c3^2]},
		  {{c2, -c3 s2, s2 s3},
		   {c1 s2, c1 c2 c3 - s1 s3, -c3 s1 - c1 c2 s3},
		   {s1 s2, c1 s3 + c2 c3 s1, c1 c3 - c2 s1 s3}}]];
DiagMat[lst_] :=
    Module[{i, j},
	   Table[If[i == j, lst[[i]], 0],
		 {i, 1, Length[lst]},
		 {j, 1, Length[lst]}]];
BlockPairs[n_] :=
    Map[Module[{eigMat = DiagMat[#],
		rotMat = RotationMat[n] @@ Map[x[#] &, Range[1, DimOn[n]]]},
	       {eigMat, Simplify[Inverse[rotMat]
				 . eigMat
				 . rotMat]}] &,
	Tuples[fundamentalEigenvaluePool, n]];
(* BlockPairs[2] *)
DimOn[n_] := n(n-1)/2;
r2Eigs = {q, t q^3, -t q^3};
r2r1Eigs = {q^2, t^(4/3) q^4, t^(4/3) q^4 Exp[2 Pi I 1/3], t^(4/3) q^4 Exp[2 Pi I 2/3]};
r2r1n2Eigs = {q^3, q^6 t^2, - q^6 t^2};
r2r1n3Eigs = {q^4, q^8 t^(8/3), q^8 t^(8/3) Exp[2 Pi I 1/3], q^8 t^(8/3) Exp[2 Pi I 2/3]};
r2r1n4Eigs = {q^5, t^3 q^9, - t^3 q^9, t^4 q^11};
PopulateAdmissibleEigs[n_] :=
    Block[{res = {},
	   r2 = Module[{i,j}, Table[If[i > j, AA[j, i], AA[i, j]], {i, 1, n}, {j, 1, n}]]},
	  Scan[PopulateAdmissibleEigsElt2,
	       GenEigChoicesTuples[n]];
	  res];
GenEigChoicesTuples[n_] :=
    Tuples[Module[{eigLsts = {r2r1Eigs, r2r1n2Eigs, r2r1n3Eigs, r2r1n4Eigs}},
		  (* ### vv We make lists of different choices of eigenvalues ### *)
		  Prepend[Map[Function[{eigLst},
				       DeleteDuplicates[Map[Sort, Tuples[Append[eigLst, 0], n]]]],
			      eigLsts],
			  (* ### vv It is crucial that we don't add 0 as possible eigenvalue ### *)
			  (* ### vv for the 0 insertions of r1                               ### *)
			  DeleteDuplicates[Map[Sort, Tuples[r2Eigs, n]]]]]];
PopulateAdmissibleEigsElt[eigTuple_, blockPair_] :=
    (* ### ^^ This function operates on dynamical variable RES ### *)
    Module[{eqns = Map[Simplify[(Plus @@ (eigTuple^#)) == Tr[MatrixPower[blockPair[[2]] . blockPair[[1]],
									 #]]
				/. {q -> E, t -> Pi}] &,
		       Range[1, Length[eigTuple]]],
	    indets = Map[x[#] &, Range[1, DimOn[Length[eigTuple]]]]},
	   (* Print["eqns: ", eqns]; *)
	   (* Print["indets: ", indets]; *)
	   Module[{ans = Solve[eqns, indets] /. {E -> q, Pi -> t}},
		  Print["ans: ", ans];
		  If[ans =!= {},
		     Module[{},
			    Print["Found admissible!"];
			    Scan[Function[{eltAns},
					  AppendTo[res, {Table[blockPair[[1, i, i]],
							       {i, 1, Length[blockPair[[1]]]}],
							 (Map[x[#] &, Range[1, DimOn[Length[eigTuple]]]]
							  /. eltAns)}]],
				 ans]]]]];
PopulateAdmissibleEigsElt2[eigLsts_] :=
    (* ### ^^ This function operates on dynamical variable RES ### *)
    (* ### This functions is a huge KLUDGE. Mathematica is not so good at solving non-linear equations ### *)
    (* ### So we'll feed it a bunch of linear equations first, to narrow the search, and then tackle   ### *)
    (* ### the remaining options more closely ### *)
    Block[{r1 = DiagMat[eigLsts[[1]]]}, (* ### << The r1 is determined by the eigenvalues that run in this particular block ### *)
	  Module[{eqns = Map[Simplify[((Plus @@ eigLsts[[#+1]]) == Tr[r2 . MatrixPower[r1, #]])
				      /. {q -> E, t -> Pi}] &, (* ### << Our standard trick to simplify equations fully ### *)
			     Range[0, Length[eigLsts] - 1]],
		  indets = Map[AA[#, #] &, Range[1, Length[eigLsts[[1]]]]]},
		 (* Print["eqns: ", eqns]; *)
		 (* Print["indets: ", indets]; *)
		 Module[{ans = Quiet[Solve[eqns, indets]] /. {E -> q, Pi -> t}},
			(* Print["ans: ", ans]; *)
			If[ans =!= {},
			   Module[{},
				  Print["Found admissible!"];
				  Scan[Function[{eltAns},
						AppendTo[res, {eigLsts,
							       eltAns}]],
				       ans]]]]]];

theTuples = GenEigChoicesTuples[2];

theTuples[[1]]

Block[{n = 2},
      Block[{res = {},
	     r2 = Module[{i,j}, Table[If[i > j, AA[j, i], AA[i, j]], {i, 1, n}, {j, 1, n}]]},
	    PopulateAdmissibleEigsElt2[theTuples[[6]]];
	    res]]


PopulateAdmissibleEigs[4]

[Mathematica exited abnormally with code 1.]

Found admissible!
Found admissible!
Found admissible!
Found admissible!
Found admissible!

                         2   2   2     3   3   3     4   4   4
Out[15]= {{{{q, q, q}, {q , q , q }, {q , q , q }, {q , q , q }, 
 
         5   5   5
>      {q , q , q }}, {AA[3, 3] -> 3 q - AA[1, 1] - AA[2, 2]}}, 
 
              3      3             2     3     6  2    6  2           4
>    {{{q, -(q  t), q  t}, {0, 0, q }, {q , -(q  t ), q  t }, {0, 0, q }, 
 
         5     9  3    9  3
>      {q , -(q  t ), q  t }}, {AA[1, 1] -> q, AA[2, 2] -> 0, AA[3, 3] -> 0}}\
 
                 3      3             2     3     6  2    6  2           4
>     , {{{q, -(q  t), q  t}, {0, 0, q }, {q , -(q  t ), q  t }, {0, 0, q }, 
 
               5
>      {0, 0, q }}, {AA[1, 1] -> q, AA[2, 2] -> 0, AA[3, 3] -> 0}}, 
 
              3      3             2           3           4
>    {{{q, -(q  t), q  t}, {0, 0, q }, {0, 0, q }, {0, 0, q }, 
 
         5     9  3    9  3
>      {q , -(q  t ), q  t }}, {AA[1, 1] -> q, AA[2, 2] -> 0, AA[3, 3] -> 0}}\
 
                 3      3             2           3           4
>     , {{{q, -(q  t), q  t}, {0, 0, q }, {0, 0, q }, {0, 0, q }, 
 
               5
>      {0, 0, q }}, {AA[1, 1] -> q, AA[2, 2] -> 0, AA[3, 3] -> 0}}}

Found admissible!
Found admissible!
Found admissible!
Found admissible!
Found admissible!

                      2   2     3   3     4   4     5   5
Out[14]= {{{{q, q}, {q , q }, {q , q }, {q , q }, {q , q }}, 
 
>     {AA[2, 2] -> 2 q - AA[1, 1]}}, 
 
           3      3                 6  2    6  2
>    {{{-(q  t), q  t}, {0, 0}, {-(q  t ), q  t }, {0, 0}, 
 
           9  3    9  3
>      {-(q  t ), q  t }}, {AA[1, 1] -> 0, AA[2, 2] -> 0}}, 
 
           3      3                 6  2    6  2
>    {{{-(q  t), q  t}, {0, 0}, {-(q  t ), q  t }, {0, 0}, {0, 0}}, 
 
>     {AA[1, 1] -> 0, AA[2, 2] -> 0}}, 
 
           3      3                                 9  3    9  3
>    {{{-(q  t), q  t}, {0, 0}, {0, 0}, {0, 0}, {-(q  t ), q  t }}, 
 
>     {AA[1, 1] -> 0, AA[2, 2] -> 0}}, 
 
           3      3
>    {{{-(q  t), q  t}, {0, 0}, {0, 0}, {0, 0}, {0, 0}}, 
 
>     {AA[1, 1] -> 0, AA[2, 2] -> 0}}}

Found admissible!

                   2     3     4     5
Out[39]= {{{{q}, {q }, {q }, {q }, {q }}, {AA[1, 1] -> q}}}


                  


PopulateAdmissibleEigs[2]

twoByTwoBlockPairs

eigenvaluePool = {q^3, t^2 q^6, - t^2 q^6, 0};

r2var1 = RotatedEigs[q, t q^3, x1];
r1var1 = {{q, 0}, {0, t q^3}};

r2var3 = RotatedEigs[t q^3, -t q^3, x3];
r1var3 = {{t q^3, 0}, {0, -t q^3}};

ans = Map[Solve[Tr[r2var1 . MatrixPower[r1var1, 2]]
		== Plus @@ #,
		x1] &,
	  Tuples[eigenvaluePool, 2]];

Map[{#} &, Flatten[ans]]

Map[FullSimplify[Tr[(r2var1 . r1var1)] /. #] &,
    Map[{#} &, Flatten[ans]]]

Simplify[Tr[r2var3 . MatrixPower[r1var3, 2]]]

ans3 = Map[Solve[Tr[r2var3 . MatrixPower[r1var3, 2]]
		 == Plus @@ #,
		 x3] &,
	   Tuples[eigenvaluePool, 2]];

ans3

