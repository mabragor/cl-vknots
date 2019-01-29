
<< KnotTheory`;

n = 4;
mFrom = 13;
mTo = 14;

Get["~/quicklisp/local-projects/cl-vknots/khovanovs"
	       <> ToString[n]
	       <> "-" <> ToString[mFrom]
	       <> "-" <> ToString[mTo]
	       <> ".txt"];

Select[CoefficientRules[kh[4,14],
			{q, t}],
       #[[1, 2]] == 0 &]

                
Out[6]= {{40, 0} -> 1, {38, 0} -> 1}

PD[TorusKnot[3,2]]

? X

Out[9]= PD[X[3, 1, 4, 6], X[1, 5, 2, 4], X[5, 3, 6, 2]]

Out[8]= 3

kh = KhReduced[TorusKnot[4,13]];

kh