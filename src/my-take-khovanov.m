

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

