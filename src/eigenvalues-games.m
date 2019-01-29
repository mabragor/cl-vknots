
(* AA[3,3] = q/2 - t q^3/2 + q/(1 - t q^2); *)
(* AA[4,4] = 3 q/2 - t q^3/2 - q/(1 + t q^2); *)
(* AA[2,2] = t q^3 - q/(1 - t q^2) + q/(1 + t q^2) - AA[1,1]; *)
repSize = 6;
eigPowersChoice = {3, 3, 0};
r = 3;
t = E^(2 Pi I 1/r);
eigs0 = Join[Table[q, {i, 1, eigPowersChoice[[1]]}],
	     Table[t q^3, {i, 1, eigPowersChoice[[2]]}],
	     Table[- t q^3, {i, 1, eigPowersChoice[[3]]}]];
r1 = Module[{i}, DiagonalMatrix[eigs0]];
r2 = Module[{i,j},
	    Table[AA[i,j], {i, 1, repSize}, {j, 1, repSize}]
	    (* /. {AA[i_, j_] :> If[i <= j, AA[i, j], AA[j, i]]} *)];
(* ### vv In all the eigenvalue pools we omit the trivial eigenvalue q^(# matrices) that corresponds to symmetric rep ### *)
eigsPoolr1r2 = {t^(4/3) q^4, t^(4/3) q^4 Exp[2 Pi I/3], t^(4/3) q^4 Exp[2 Pi I 2/3]};
eigsPoolr1n2r2 = {(t q^3)^2, -(t q^3)^2};
eigsPoolr1nm1r2 = {Exp[2 Pi I/3], Exp[2 Pi I 2/3],
		 (1 + q^2*t + q^4*t^2 - Sqrt[1 + 2*q^2*t - q^4*t^2 + 2*q^6*t^3 + 
					     q^8*t^4])/(2*q^2*t),
		 (1 + q^2*t + q^4*t^2 + Sqrt[1 + 2*q^2*t - q^4*t^2 + 2*q^6*t^3 + 
					     q^8*t^4])/(2*q^2*t)};
eigsPoolr1nm2r2 = {-q^(-1), 1/(q^5*t^2),
		   (1 + q^2*t + q^4*t^2 + q^6*t^3 - Sqrt[-4*q^6*t^3 + (1 + q^2*t + q^4*t^2 + q^6*t^3)^2])/(2*q^5*t^2),
		   (1 + q^2*t + q^4*t^2 + q^6*t^3 + Sqrt[-4*q^6*t^3 + (1 + q^2*t + q^4*t^2 + q^6*t^3)^2])/(2*q^5*t^2)};
(* ### vv The eigenvalues of r1^(-1) r2^2 ### *)
eigsPoolr1nm1r2n2 = eigsPoolr1nm2r2^(-1);
(* ### vv The eigenvalues of r1^2 r2 r1 r2 ### *)
eigsPoolr1n2r2r1r2 = {(t q^3)^3, (- t q^3)^3, t^4 q^11};
eqn0n0 = (Tr[r2] - Plus @@ eigs0 == 0);
(* ### vv We need to multiply matrices in reverse order w.r.t what we have in braid description, dammit !!! ### *)
eqn0n1 = (Tr[r2 . MatrixPower[r1, -1]] - Simplify[Plus @@ eigsm1] == 0);
eqn0n2 = (Tr[r2 . MatrixPower[r1, -2]] - Simplify[Plus @@ eigsm2] == 0);
eqn0nn1 = (Tr[r2 . MatrixPower[r1, 1]] - Simplify[Plus @@ eigs1] == 0);

ans0 = Quiet[Solve[{eqn0n0, eqn0n1, eqn0n2, eqn0nn1},
		   {AA[2,2], AA[3,3], AA[4,4], duplicatedEigenvalue1n1}]][[1]];

ans0

Map[# /. {Rule -> Set} &,
    ans0];

preEigs3 = {t^(8/3) q^8, t^(8/3) q^8 Exp[2 Pi I/3], t^(8/3) q^8 Exp[2 Pi I 2/3]};
preEigs4 = {t^4 q^11, t^3 q^9, -t^3 q^9};

eigs3 = Append[preEigs3,
	       Simplify[Tr[r2 . MatrixPower[r1, 3]] - (Plus @@ preEigs3)]];
eigs4 = Append[preEigs4,
	       Simplify[Tr[r2 . MatrixPower[r1, 4]] - (Plus @@ preEigs4)]];

eigs4

MkEqn[mat_, eigs_] :=
    Simplify[(Simplify[Tr[mat] /. {freeDiagA -> theAA}
		       /. {AA[i_, j_] :> If[i < j, AA[i,j], BB[j,i]/AA[j,i]]}]
	      (* /. {AA[1,2] -> BB[1,2]/AA[2,1]} *))
	     - Simplify[(Plus @@ eigs) /. {freeDiagA -> theAA, AA[2,1] -> BB[1,2] /AA[1,2]}] == 0];

eqn0 = MkEqn[MatrixPower[r2 . MatrixPower[r1, 0], 2], eigs0^2];
eqn1 = MkEqn[MatrixPower[r2 . MatrixPower[r1, 1], 2], eigs1^2];
eqn3 = MkEqn[MatrixPower[r2 . MatrixPower[r1, 3], 2], eigs3^2];
eqn4 = MkEqn[MatrixPower[r2 . MatrixPower[r1, 4], 2], eigs4^2];
eqnm1 = MkEqn[MatrixPower[r2 . MatrixPower[r1, -1], 2], eigsm1^2];
eqnm2 = MkEqn[MatrixPower[r2 . MatrixPower[r1, -2], 2], eigsm2^2];
eqn2alt = MkEqn[MatrixPower[r2, 2] . MatrixPower[r1, -1], eigs2alt];
eqnn2n1 = MkEqn[r2 . r1 . r2 . MatrixPower[r1, 2], eigsn2n1];


theAns = Simplify[Solve[Simplify[{eqn0, (* eqn1, eqn3, eqn4, *) eqnm1, eqnm2, eqn2alt}],
			{theAA, (* duplicatedEigenvalue, *) BB[1,2], BB[1,3], BB[1,4], BB[2,3], BB[2,4], BB[3,4]}]][[1]];

theAns

Simplify[eqn1 /. theAns]

theAns2 = Simplify[Solve[Simplify[eqn1 /. theAns], BB[1,2]][[1]]];

theAns3 = Simplify[Solve[Simplify[eqn3 /. theAns /. theAns2], BB[1,3]][[1]]];

Simplify[eqn4 /. theAns /. theAns2 /. theAns3]

theAns4 = Simplify[Solve[Simplify[eqn4 /. theAns /. theAns2 /. theAns3], theAA][[1]]];

(* ### vv Alternative branch of solving, for non-trivial Jordan cell ### *)
theAns4 = Simplify[Solve[Simplify[eqn4 /. theAns /. theAns2 /. theAns3], AA[1,2]][[1]]];

theAns4

ansMat = Module[{i,j},
		Table[If[i == j,
			 AA[i,j],
			 BB @@ Sort[{i,j}]],
		      {i, 1, 4},
		      {j, 1, 4}] /. {freeDiagA -> theAA} /. theAns /. theAns2 /. theAns3 /. theAns4];

Simplify[ansMat[[1,4]]]

Out[15]= theAA

Factor[Simplify[eqnn2n1[[1]] /. {freeDiagA -> theAA} /. theAns /. theAns2 /. theAns3 /. theAns4]
       (* /. {extraR1Eigenvalue2 -> 1} *)]

         
                  2         4  2        6  3        8  4        10  5
Out[20]= (9 - 36 q  t + 60 q  t  - 120 q  t  + 232 q  t  - 288 q   t  + 
 
          8  6       10  6        12  6       10  7       12  7
>      6 q  t  + 12 q   t  + 360 q   t  - 12 q   t  - 21 q   t  - 
 
            14  7       12  8      14  8        16  8       14  9
>      400 q   t  + 14 q   t  + 4 q   t  + 368 q   t  - 28 q   t  - 
 
           16  9        18  9       16  10       18  10        20  10
>      29 q   t  - 288 q   t  + 15 q   t   + 22 q   t   + 160 q   t   - 
 
           18  11      20  11       22  11    16  12      18  12
>      20 q   t   + 8 q   t   - 64 q   t   + q   t   - 4 q   t   + 
 
           20  12       22  12       24  12    20  13      22  13
>      13 q   t   - 28 q   t   + 16 q   t   + q   t   + 4 q   t   + 
 
           24  13      20  14      22  14      24  14       26  14
>      32 q   t   + 2 q   t   - 6 q   t   - 7 q   t   - 16 q   t   + 
 
          24  15      26  15      28  15    24  16      26  16    28  16
>      2 q   t   + 8 q   t   + 4 q   t   + q   t   - 4 q   t   - q   t   + 
 
        28  17        7  8       4  2 2
>      q   t  ) / (2 q  t  (2 + q  t ) )

Factor[Simplify[ansMat[[2,2]] /. {extraR1Eigenvalue -> (1 + t) extra}] /. {t -> -1}]



Block[{a = 0},
      Factor[Normal[Series[Factor[Simplify[ansMat[[4,4]]]],
			   {extraR1Eigenvalue, -t , 0}]]]]

                  
            3  2       2    4    4      4  2    8  3
         -(q  t  (1 + q  - q  + q  t + q  t  + q  t ))
Out[42]= ---------------------------------------------
                           2          4  2
                   2 (1 + q  t) (1 + q  t )

                  
                     2      2  2      4  2    6  2      6  3    6  4
Out[41]= (q (-2 + 2 q  t + q  t  - 3 q  t  - q  t  + 3 q  t  + q  t  - 
 
            8  4    10  5               2          4  2
>        2 q  t  + q   t )) / (2 (-1 + q  t) (1 + q  t ))

                  
            4  2       2    4    4      4  2    8  3
Out[40]= -(q  t  (1 + q  - q  + q  t + q  t  + q  t ) 
 
                 2      2  2      4  2    6  2      6  3    6  4      8  4
>       (-2 + 2 q  t + q  t  - 3 q  t  - q  t  + 3 q  t  + q  t  - 2 q  t  + 
 
           10  5               2          2          4  2 2
>         q   t )) / (4 (-1 + q  t) (1 + q  t) (1 + q  t ) )

                  
Out[39]= 0

                  
Out[38]= 0

                  
Out[37]= 0

                  
                   3          2       2    4  2
         (-1 + q) q  (1 + q) t  (1 + q  + q  t )
Out[36]= ---------------------------------------
                  2          2          4  2
           (-1 + q  t) (1 + q  t) (1 + q  t )

                  
Out[35]= 0

                  
           6  2           2      4      4  2    4  3
Out[33]= (q  t  (1 + t + q  t - q  t + q  t  + q  t ) 
 
                  4      4  3    6  3    8  4
>      (-1 + t - q  t + q  t  - q  t  + q  t )) / 
 
               2          2   2       4  2 2
>    (2 (-1 + q  t) (1 + q  t)  (1 + q  t ) )



Solve[0 == Simplify[BB[1,4] /. theAns /. theAns2 /. theAns3 /. theAns4],
      extraR1Eigenvalue]


Factor[Simplify[Simplify[r2 /. {freeDiagA -> theAA} /. theAns4] /. {extraR1Eigenvalue -> q}]]





         1      8  3    12  5     2      6  2      10  4
Out[10]= - + 2 q  t  + q   t  == q  + 2 q  t  + 2 q   t
         t

Factor[theAns]

FullSimplify[theAA /. theAns /. {t -> Pi, q -> E}]


Factor[Simplify[theAns]]

theAnsSimp = Join[Factor[theAns /. {BB[1,3] -> 0, BB[1,4] -> 0}],
		  {BB[1,3] -> 0, BB[1,4] -> 0}];

Simplify[(Tr[MatrixPower[r1, -1] . MatrixPower[r2, 2]] /. {AA[1,1] -> theAA} /. {AA[i_, j_]^2 :> BB[i,j]}) /. theAnsSimp]

          2       3
Out[54]= --- + 2 q  t
         q t

Simplify[Plus @@ eigs2alt]

          1     3        5  2
Out[55]= --- + q  t + 2 q  t
         q t

Simplify[eqn2alt /. (Factor[theAns /. {BB[1,3] -> 0, BB[1,4] -> 0}]) /. {BB[1,3] -> 0, BB[1,4] -> 0}]

            5  2     1     3
Out[51]= 2 q  t  == --- + q  t
                    q t

3 q/2 + t q^3 - t^2 q^5/2

Expand[FullSimplify[AA[3,3] (* (1-t q^2) *)]]

              3
         q   q  t      q
Out[65]= - - ---- + --------
         2    2          2
                    1 - q  t

Expand[FullSimplify[AA[4,4] (* (1+t q^2) *)]]

                3
         3 q   q  t      q
Out[66]= --- - ---- - --------
          2     2          2
                      1 + q  t

                     5  2
         q    3     q  t
Out[63]= - + q  t - -----
         2            2




                              3      7  3            4  2
                      theAA (q  t + q  t  + theAA - q  t  theAA)
Out[57]= {BB[1, 2] -> ------------------------------------------, 
                                       2          2
                                (-1 + q  t) (1 + q  t)
 
                    4         4  2          2      4  2
                 -(q  t (1 + q  t ) (3 - 2 q  t + q  t ))
>    BB[2, 3] -> ----------------------------------------, 
                                 2   2       2
                        2 (-1 + q  t)  (1 + q  t)
 
                    4         4  2           2      4  2
                 -(q  t (1 + q  t ) (-1 - 2 q  t + q  t ))
>    BB[2, 4] -> -----------------------------------------, 
                                  2          2   2
                         2 (-1 + q  t) (1 + q  t)
 
                  2          2      4  2          2      4  2
                 q  (-1 - 2 q  t + q  t ) (3 - 2 q  t + q  t )
>    BB[3, 4] -> ---------------------------------------------, 
                                    2          2
                           4 (-1 + q  t) (1 + q  t)
 
>    BB[1, 3] -> 0, BB[1, 4] -> 0}