

lambda1 = q;
lambda2 = t q^3;
C1 = (1 + q^2 - q^6 t^2 + q^8 t^3)/(q^2 (1 - q^4 t^2));
C2 = ((-t)(1 + q^4 t))/((1 - q^4 t^2));
T2nTheor = C1 lambda1^n + C2 lambda2^n;
qt[n_] := (((Sqrt[-T] q)^n - (Sqrt[-T] q)^(-n))
           /((Sqrt[-T] q)^1 - (Sqrt[-T] q)^(-1)));

Expand[Factor[FullSimplify[T2nTheor /. {n -> -5}]]]

          -5     1        1        1       1     t
Out[32]= q   - ------ - ------ - ------ - ---- - --
                15  4    11  3    11  2    7      3
               q   t    q   t    q   t    q  t   q

          -3     1      1     t
Out[31]= q   - ----- - ---- - -
                9  2    5     q
               q  t    q  t

         1
Out[30]= - - q t
         q

          11    13    15  2    19  3    19  4    23  5    23  6    27  7
Out[29]= q   + q   + q   t  + q   t  + q   t  + q   t  + q   t  + q   t  + 
 
      27  8    31  9    31  10    35  11    35  12    39  13
>    q   t  + q   t  + q   t   + q   t   + q   t   + q   t

          9    11    13  2    17  3    17  4    21  5    21  6    25  7
Out[28]= q  + q   + q   t  + q   t  + q   t  + q   t  + q   t  + q   t  + 
 
      25  8    29  9    29  10    33  11
>    q   t  + q   t  + q   t   + q   t

          7    9    11  2    15  3    15  4    19  5    19  6    23  7
Out[25]= q  + q  + q   t  + q   t  + q   t  + q   t  + q   t  + q   t  + 
 
      23  8    27  9
>    q   t  + q   t

          5    7    9  2    13  3    13  4    17  5    17  6    21  7
Out[24]= q  + q  + q  t  + q   t  + q   t  + q   t  + q   t  + q   t

          3    5    7  2    11  3    11  4    15  5
Out[23]= q  + q  + q  t  + q   t  + q   t  + q   t

              3    5  2    9  3
Out[22]= q + q  + q  t  + q  t


ChiBulkGKnots[indices_] :=
    q/(Sqrt[-T]^g qt[2])
    1/(qt[2]^(g+1))
    \brackets{ \prod_{i=0}^g \Big( 1 +  {[3]_{qt}}  \brackets{q^2 T}^{n_i}\Big)
               + [3]_{qt} \prod_{i=0}^g \Big( 1 -   \brackets{q^2 T}^{n_i}\Big)}
    }


Simplify[T2nTheor /. {n -> 3}] // TeXForm

Out[9]//TeXForm= q^9 t^3+q^5 t^2+q^3+q

             3    5  2    9  3
Out[8]= q + q  + q  t  + q  t


