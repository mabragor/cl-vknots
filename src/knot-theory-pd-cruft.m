
<< "knot-theory-knovanov-ev-utils.m";

PlanarDiagramToAdvancedStructures[PD[TorusKnot[4,2]]]

Out[3]= PDExtended[<|4 -> 1, 8 -> 5, 5 -> 6, 1 -> 2, 2 -> 3, 6 -> 7, 7 -> 8, 
 
>     3 -> 4|>, <|1 -> 4, 5 -> 8, 6 -> 5, 2 -> 1, 3 -> 2, 7 -> 6, 8 -> 7, 
 
>     4 -> 3|>, <|4 -> X[4, 5, 1, 8], 8 -> X[4, 5, 1, 8], 5 -> X[5, 2, 6, 1], 
 
>     1 -> X[5, 2, 6, 1], 2 -> X[2, 7, 3, 6], 6 -> X[2, 7, 3, 6], 
 
>     7 -> X[7, 4, 8, 3], 3 -> X[7, 4, 8, 3]|>, 
 
>    <|1 -> X[4, 5, 1, 8], 5 -> X[4, 5, 1, 8], 6 -> X[5, 2, 6, 1], 
 
>     2 -> X[5, 2, 6, 1], 3 -> X[2, 7, 3, 6], 7 -> X[2, 7, 3, 6], 
 
>     8 -> X[7, 4, 8, 3], 4 -> X[7, 4, 8, 3]|>, {{7, 8, 5, 6}, {1, 2, 3, 4}}]

Out[2]= PDExtended[<|3 -> 4, 6 -> 1, 1 -> 2, 4 -> 5, 5 -> 6, 2 -> 3|>, 
 
>    <|4 -> 3, 1 -> 6, 2 -> 1, 5 -> 4, 6 -> 5, 3 -> 2|>, 
 
>    <|3 -> X[3, 1, 4, 6], 6 -> X[3, 1, 4, 6], 1 -> X[1, 5, 2, 4], 
 
>     4 -> X[1, 5, 2, 4], 5 -> X[5, 3, 6, 2], 2 -> X[5, 3, 6, 2]|>, 
 
>    <|4 -> X[3, 1, 4, 6], 1 -> X[3, 1, 4, 6], 2 -> X[1, 5, 2, 4], 
 
>     5 -> X[1, 5, 2, 4], 6 -> X[5, 3, 6, 2], 3 -> X[5, 3, 6, 2]|>, 
 
>    {{3, 4, 5, 6, 1, 2}}]

