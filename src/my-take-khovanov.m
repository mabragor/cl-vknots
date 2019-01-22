

(* ### In this file I'll write my take on calculation of Khovanov complexes for tangles. ### *)

(* ### vv Make an arc loop picture from a list of arcs and loops ### *)
MkArcLoopPic[lst__] :=
    ArcLoopPic @@ Sort[List[lst]];
(* ### vv Make an arc from a list of its endpoints ### *)
MkArc[lst__] :=
    Arc @@ Sort[List[lst]];
MkFlip[a1_Arc, a2_Arc] :=
    Flip @@ Sort[{a1, a2}];
ElementaryComplex[Xp[a_, b_, c_, d_]] :=
    Complex[Objects[{q MkArcLoopPic[MkArc[a, c], MkArc[b, d]]},
                    {t q^2 MkArcLoopPic[MkArc[a, b], MkArc[c, d]]}],
            Morphisms[{{MkFlip[MkArc[a,c], MkArc[b,d]]}}]];
ElementaryComplex[Xm[a_, b_, c_, d_]] :=
    Complex[Objects[{q^(-2) t^(-1) MkArcLoopPic[MkArc[a, b], MkArc[c, d]]},
                    {q^(-1) MkArcLoopPic[MkArc[a, c], MkArc[b, d]]}],
            Morphisms[{{MkFlip[MkArc[a,b], MkArc[c,d]]}}]];

GlueObjectsAlongArcsElt[alpic1_ArcLoopPic, alpic2_ArcLoopPic] :=
    Module[{used = <||>},
           

GlueObjectsAlongArcs[objects1_Objects, objects2_Objects] :=
    Module[{dim1 = Length[objects1] - 1,
            dim2 = Length[objects2] - 1},
           Module[{dimLayer, oneDim},
                  Objects @@ Table[Join @@ Select[Table[With[{dimTwo = dimLayer - dimOne},
                                                             If[Or[0 > dimTwo, dim2 < dimTwo],
                                                                Null,
                                                                Map[GlueObjectsAlongArcsElt[#[[1]], #[[2]]] &,
                                                                    Tuples[{objects1[[1 + dimOne]], objects2[[1 + dimTwo]]}]]]],
                                                        {dimOne, 0, dim1}],
                                                  Null =!= # &],
                                   {dimLayer, 0, dim1 + dim2}]]];

GlueComplexesAlongArcs[Complex[objects1_Objects, morphisms1_Morphisms],
                       Complex[objects2_Objects, morphisms2_Morphisms],
                       arcs_List] :=
    Block[{theArcsAssoc = MakeArcsAssociation[arcs]}, (* ### << We make the gluing recipe a `special` variable and then use it ### *)
                                                      (* ### << Everywhere ### *)
          Complex[GlueObjectsAlongArcs[objects1, objects2],
                  GlueMorphismsAlongArcs[objects1, objects2, morphisms1, morphisms2]];

          