
(* ### xx In this file we write an iterator over a tuple ### *)
(* ###    TupleIter[{1,3,4}, {}] ### *)

(* ### xx An iterator protocol for Mathematica will be the following:                            ### *)
(* ###    Upon successive calls an iterator function returns lists of two elements               ### *)
(* ###    first element is the actual value, and the second one is whether an iterator is        ### *)
(* ###    depleted or not. When iterator is depleted, a pair {Null, False} is returned.          ### *)
    
MkListIter[lst_List] :=
    Module[{i = Null,
            depletedQ = False,
            stop = Length[lst] + 1},
           Function[{},
                    If[depletedQ,
                       {Null, False},
                       Block[{},
                             If[Null === i,
                                i = 1,
                                i = i + 1];
                             If[i === stop,
                                Block[{}, depletedQ = True; {Null, False}],
                                {lst[[i]], True}]]]]];
MkRangeIter[from_Integer, to_Integer] :=
    MkRangeIter[from, to, 1];
MkRangeIter[from_Integer, to_Integer, step_Integer] :=
    Module[{i = Null,
            depletedQ = False},
           Function[{},
                    If[depletedQ, (* ### << If we've decided once that iterator is depleted, we don't waver ### *)
                       {Null, False},
                       Block[{},
                             If[Null === i,
                                i = from,
                                i = i + step];
                             (* ### ^^ Initialize or increment the counters ### *)
                             If[Or[And[step > 0,
                                       i > to],
                                   And[step < 0,
                                       i < to]],
                                (* ### ^^ Check, whether we went out of range ### *)
                                Block[{}, depletedQ = True; {Null, False}], (* ### << Stop if so ### *)
                                {i, True}]]]]]; (* ### << Return next value if not ### *)
(* ### vv Make an iterator that (lazily) loops over all the tuples, where       ### *)
(* ###    each element of a tuple is from the corresponding range (in the spec) ### *)
(* ###    or a list                                                             ### *)
(* ###    Example:                                                              ### *)
(* ###      MkTupleIter[{1,3}, {6,4,-2}, AList["a","b","c"]]                    ### *)
MkIterFromSpec[spec_AList] :=
    MkListIter[List @@ spec];
MkIterFromSpec[spec_List] :=
    MkRangeIter @@ spec;
MkTupleIter[tupleSpecs__] :=
    Module[{tupleSpecsLst = List[tupleSpecs]},
           Module[{depletedQ = False,
                   subIters = Module[{i}, Table[Null, {i, 1, Length[tupleSpecsLst]}]],
                   valuesCur = Module[{i}, Table[Null, {i, 1, Length[tupleSpecsLst]}]]},
                  Module[{totalDeinit =
                          Function[{},
                                   depletedQ = True;
                                   subIters = Null;
                                   valuesCur = Null],
                          initIter =
                          Function[{anIndex}, (* ### << Initializes specific iterator from the spec                           ### *)
                                   (*            ###    Returns True if initialized, False if skipped, cause already non-Null ### *)
                                   If[Null === subIters[[anIndex]],
                                      Block[{}, subIters[[anIndex]] = MkIterFromSpec[tupleSpecsLst[[anIndex]]]; True],
                                      False]],
                          fetchNext = (* ### << Fetches the next value from an iterator             ### *)
                          (*             ###    Returns True/False, depending on success of this.   ### *)
                          (*             ###    Sets iterator to Null if it got depleted            ### *)
                          Function[{anIndex},
                                   Module[{value, validQCur},
                                          {value, validQCur} = subIters[[anIndex]][];
                                          If[Not[validQCur],
                                             Block[{},
                                                   subIters[[anIndex]] = Null;
                                                   valuesCur[[anIndex]] = Null;
                                                   False],
                                             Block[{},
                                                   valuesCur[[anIndex]] = value;
                                                   True]]]]},
                         Module[{initAllItersButLast (* ### << Initializes all the iterators, but the last one ### *)
                                 (*                     ###    and prefetches their first value                ### *)
                                 = Function[{},
                                            Module[{i},
                                                   For[i = 1, i < Length[subIters], i ++,
                                                       (* ### ^^ the '<' is very important here ### *)
                                                       If[And[initIter[i], (* ### << We only prefetch if iter was Null ### *)
                                                              Not[fetchNext[i]]],
                                                          Message[tupleIter::err, "All ranges should be non-empty"];
                                                          totalDeinit[];] (* ### << To minimize the damage ### *)
                                                      ]]],
                                 initAndFetchNext
                                 = Function[{anIndex},
                                            initIter[anIndex];
                                            fetchNext[anIndex]],
                                 fetchNextYounger (* ### << fetch next values for all the iterators that are ### *)
                                 (*                  ###    'younger' than the specified one                 ### *)
                                 = Function[{anIndex},
                                            Module[{i},
                                                   For[i = anIndex + 1, i <= Length[subIters], i++,
                                                       And[initIter[i], fetchNext[i]]]]]
                                },
                                (* ### ^^ Here are the helper functions ### *)
                                (* ### vv The main iterator closure ### *)
                                Function[{},
                                         If[depletedQ, (* ### << Once we've decided that iterator ### *)
                                            (*            ###    is depleted,  we don't waver     ### *)
                                            {Null, False},
                                            Block[{},
                                                  initAllItersButLast[];
                                                  (* Print["valuesCur: ", valuesCur]; *)
                                                  Module[{posCur = Length[subIters]
                                                          (*, j = 0 *)
                                                         },
                                                         While[True (* && j < 10 *),
                                                               (* j += 1; *)
                                                               If[0 === posCur,
                                                                  Block[{}, totalDeinit[]; Break[]],
                                                                  If[initAndFetchNext[posCur],
                                                                     Block[{},
                                                                           fetchNextYounger[posCur];
                                                                           Break[]],
                                                                     posCur -= 1]]];
                                                         If[depletedQ,
                                                            {Null, False},
                                                            {valuesCur, True}]]]]]
                               ]]]];
CollectIter[iter_] :=
    Module[{res = {},
            value,
            validQ},
           While[True,
                 {value, validQ} = iter[];
                 If[Not[validQ],
                    Break[],
                    AppendTo[res, value]]];
           res];
SkipUntilIter[item_, subiter_] :=
    (* ### ^^ Skips all the items in the `subiter` until the one specified is found. ### *)
    (* ###    From then on is just transparent.                                      ### *)
    Module[{depletedQ = False,
            foundAnItem = False},
           Function[{},
                    If[depletedQ,
                       {Null, False},
                       If[Not[foundAnItem],
                          Module[{subitem, valid},
                                 While[True,
                                       {subitem, valid} = subiter[];
                                       If[Not[valid],
                                          Block[{}, depletedQ = True; Break[]]];
                                       If[item == subitem,
                                          Block[{}, foundAnItem = True; Break[]]]];
                                 If[depletedQ,
                                    {Null, False},
                                    {subitem, True}]],
                          Module[{subitem, valid},
                                 {subitem, valid} = subiter[];
                                 If[Not[valid],
                                    Block[{}, depletedQ = True; {Null, False}],
                                    {subitem, True}]]]]]];
(* ### vv The main macro-interface to using iterators                                           ### *)
(* ###    Let's see if I can get enough control over the Mathematica evaluator to write this    ### *)
ClearAll[Iterate];
SetAttributes[Iterate, HoldAllComplete];
Iterate[{var_, iterator_}, body_] :=
    Module[{GSIter = iterator, (* ### << We want iterator expression to be evaluated exactly once ### *)
            validQ},
           If[List === Head[Unevaluated[var]],
              Module[{GSvar}, (* ### << This gensym variable is needed, because when depleted, iterator returns {Null, False} ### *)
                     Module[var,
                            While[True,
                                  {GSvar, validQ} = GSIter[];
                                  If[Not[validQ],
                                     Break[],
                                     Block[{},
                                           var = GSvar; (* ### << The actual destructuring ### *)
                                           body]]]]],
              Module[{var},
                     While[True,
                           {var, validQ} = GSIter[];
                           If[Not[validQ],
                              Break[],
                              body]]]]];
MapIter[fun_, subiter_] :=
    Module[{depletedQ = False},
           Function[{},
                    If[depletedQ, (* ### << If we've decided once that iterator is depleted, we don't waver ### *)
                       {Null, False},
                       Module[{subVal, subValidQ},
                              {subVal, subValidQ} = subiter[];
                              If[Not[subValidQ],
                                 Block[{},
                                       depletedQ = True;
                                       {Null, False}],
                                 {fun[subVal], True}]]]]];
GrepIter[filterFun_, subiter_] :=
    Module[{depletedQ = False},
           Function[{},
                    If[depletedQ, (* ### << If we've decided once that iterator is depleted, we don't waver ### *)
                       {Null, False},
                       Module[{subVal, subValidQ},
                              While[True,
                                    {subVal, subValidQ} = subiter[];
                                    (* Print["subVal: ", subVal]; *)
                                    If[Not[subValidQ],
                                       Block[{},
                                             depletedQ = True; Break[]],
                                       If[True === filterFun[subVal],
                                          Break[]]]];
                              If[depletedQ,
                                 {Null, False},
                                 {subVal, True}]]]]];


(* ### vv Example of use of grepper                                           ### *)
(* ###    CollectIter[GrepIter[EvenQ, MkRangeIter[1, 10]]]                    ### *)

(* ### vv Example of use:                                                     ### *)
(* ###    a = MkTupleIter[{4,8}, {5,0,-1}, AList["a", "b", "c"]];             ### *)
(* ###    CollectIter[a]                                                      ### *)

(* ### vv An example of using a `skip until` iterator                         ### *)
(* ###    a = SkipUntilIter["r", MkListIter[{"a", "b", "c", "r", "t", "y"}]]; ### *)

(* ### vv An example of usage of an `Iterate` macro            ### *)
(* ###    As you can see, it easily supports nested iterations ### *)
(* ###    Iterate[{myVar, MkRangeIter[4,6]},                   ### *)
(* ###            Iterate[{myVar2, MkRangeIter[9,1,-1]},       ### *)
(* ###                    Print[myVar, " ", myVar2]]]          ### *)

