
(* ### vv BEGINIMPORTS ### *)
<< "knot-theory-knovanov-ev-utils.m";
(* ### ^^ ENDIMPORTS ### *)

(* ### vv BEGINLIB ### *)
evoRules["PPred"] = Get[EvoFname["red", {1,1}]];
evoRules["PPPred"] = Get[EvoFname["red", {1,1,1}]];
evoRules["PPPPred"] = Get[EvoFname["red", {1,1,1,1}]];
evoRules["PPPPPred"] = Get[EvoFname["red", {1,1,1,1,1}]];
evoRules["MMred"] = Get[EvoFname["red", {-1,-1}]];
evoRules["MMMred"] = Get[EvoFname["red", {-1,-1,-1}]];
evoRules["MMMMred"] = Get[EvoFname["red", {-1,-1,-1,-1}]];
evoRules["MMMMMred"] = Get[EvoFname["red", {-1,-1,-1,-1,-1}]];
evoRules["PPMred"] = Get[EvoFname["red", {1,1,-1}]];
evoRules["PPMredAlt1"] = Get[EvoFname["red", {1,1,-1}, 1]];
evoRules["PMPredAlt1"] = Get[EvoFname["red", {1,-1,1}, 1]];
evoRules["PPPMred"] = Get[EvoFname["red", {1,1,1,-1}]];
evoRules["PPPMredAlt1"] = Get[EvoFname["red", {1,1,1,-1}, 1]];
evoRules["PPPPMred"] = Get[EvoFname["red", {1,1,1,1,-1}]];
evoRules["PPPPPP"] = Get[EvoFname[{1,1,1,1,1,1}]];
evoRules["PPPPP"] = Get[EvoFname[{1,1,1,1,1}]];
evoRules["PPPP"] = Get[EvoFname[{1,1,1,1}]];
evoRules["MM"] = Get[EvoFname[{-1,-1}]];
evoRules["PP"] = Get[EvoFname[{1,1}]];
evoRules["MMM"] = Get[EvoFname[{-1,-1,-1}]];
evoRules["PPP"] = Get[EvoFname[{1,1,1}]];
evoRules["PPM"] = Get[EvoFname[{1,1,-1}]];
evoRules["MMP"] = Get[EvoFname[{-1,-1,1}]];
evoRules["PPMAlt1"] = Get[EvoFname[{1,1,-1}, 1]];
evoRules["MMPAlt1"] = Get[EvoFname[{-1,-1,1}, 1]];
evoRules["PMPAlt1"] = Get[EvoFname[{1,-1,1}, 1]];
evoRules["MPPAlt1"] = Get[EvoFname[{-1,1,1}, 1]];
evoRules["MPMAlt1"] = Get[EvoFname[{-1,1,-1}, 1]];
evoRules["PMMAlt1"] = Get[EvoFname[{1,-1,-1}, 1]];
regionLabels = {"MMM", "PPP", "PPM", "MMP", "PPMAlt1", "MMPAlt1", "PMPAlt1", "MPPAlt1", "MPMAlt1", "PMMAlt1"};
auxRegionLabels = {"MM", "PP", "PPPP", "PPPPP", "PPPPPP",
                   "PPred", "PPPred", "PPPPred", "PPPPPred",
                   "MMred", "MMMred", "MMMMred", "MMMMMred",
                   "PPMred", "PPPMred", "PPPPMred",
                   "PPMredAlt1", "PPPMredAlt1", "PMPredAlt1"};
TeXifyEvoRules[signsStr_, evoRules_] :=
    (* ### ^^ The goal of this function is to serialize evolution rules in such a way, that one conveniently can ### *)
    (* ###    copy-paste them in TeX.                                                                            ### *)
    Module[{fd = "/home/popolit/tmp/texify.tex"},
           WriteString[fd, ("\\begin{align}\n"
                            <> StringRiffle[KeyValueMap[Function[{key, val},
                                                                 "M^{" <> signsStr <> "}_{"
                                                                 <> StringRiffle[Map[ToString[#, TeXForm] &, key],
                                                                                 ", "]<>  "} &= "
                                                                 <> ToString[val, TeXForm]],
                                                        Select[evoRules, # =!= 0 &]],
                                            " \\\\ \\notag\n"]
                            <> "\n\\end{align}")];
           Close[fd];
           Success];
qq[n_] := (q^n - q^(-n))/(q - q^(-1));
AMatrix = 1/qq[2] {{1, qq[3]}, {1, -1}};
Lambda[m_] := (-1)^m q^(m (m+1));
TheorFundJones[genus_] :=
    Function[Evaluate[Map[Symbol["n" <> ToString[#]] &, Range[0, genus]]],
             Evaluate[Simplify[Module[{k, i, m},
                                      Sum[qq[2 k + 1] Product[Sum[AMatrix[[k + 1, m + 1]] Lambda[m]^Symbol["n" <> ToString[i]],
                                                                  {m, 0, 1}],
                                                              {i, 0, genus}],
                                          {k, 0, 1}]]]]];
(* TeXifyEvoRules["--+", evoRulesMMP] *)
(* fun = MkEvoFunction[evoRulesMMP]; *)
(* ### vv This code was needed to test against Jones ### *)
(* B[LoadAllPrecomps[2]; *)
(*   Iterate[{regionLabel, MkListIter[Join[regionLabels, auxRegionLabels]]}, *)
(*           Rule[evoFun[regionLabel], MkEvoFunction[evoRules[regionLabel]]] *)
(*           /. {Rule -> Set}];] *)
(* funJones = TheorFundJones[2]; *)
ClearAll[WithWrittenFrame];
SetAttributes[WithWrittenFrame, HoldAllComplete];
WithWrittenFrame[{fd_, opening_, closing_}, body_] :=
    CompoundExpression[WriteString[fd, If[ListQ[opening],
                                          StringJoin @@ Map[ToString, opening],
                                          opening]],
                       body,
                       WriteString[fd, If[ListQ[closing],
                                          StringJoin @@ Map[ToString, closing],
                                          closing]]];
CombUpEvoMap[assoc_] :=
    Association[Map[Function[{rule},
                             Module[{modrule = rule /. {q -> 1/q, t -> 1/t}},
                                    Rule[If[EvenQ[Length[modrule[[1]]]],
                                            (Mask @@ Map[# t q^3 &, modrule[[1]]]),
                                            (Mask @@ Append[Map[# t q^3 &, modrule[[1, 1 ;; -2]]],
                                                            modrule[[1, -1]]])],
                                         Factor[Simplify[modrule[[2]]]]]]],
                    Select[Normal[assoc], 0 =!= #[[2]] &]]];
(* ### vv Matching my braid orientation conventions with Morozov's ### *)
(* Expand[Factor[Block[{n0 = -5, n1 = 0, n2 = 0}, *)
(*                     Simplify[(funPPP[n0, n1, n2]/(q + q^(-1))^2 /. {t -> -1})]]]] *)
(* Expand[Factor[Block[{n0 = 0, n1 = 0, n2 = 2}, *)
(*                     Simplify[(funPPP[n0, n1, n2] /. {t -> -1})/(q + q^(-1))]]]] *)
(* Block[{n0 = 0, n1 = 0, n2 = 2}, *)
(*       Expand[Simplify[funJones[n0, n1, n2]/(q+q^(-1))^2 (- q^(-15))]]] *)
(* Block[{n0 = 10, n1 = 20, n2 = 15}, *)
(*       Simplify[(evoFun["PPM"][n0, n1, 2 n2] /. {t -> -1, q -> 1/q}) (-q^(3))^(n0 + n1) *)
(*                /funJones[n0, n1, 2 n2]]] *)
Iterate[{regionLabel, MkListIter[Join[regionLabels, auxRegionLabels]]},
        Rule[evoRulesCombed[regionLabel], CombUpEvoMap[evoRules[regionLabel]]]
        /. {Rule -> Set}];
(* ### vv Assume that we know dependence on the last parameter only in even points   ### *)
(* ###    Therefore we don't know the signs of the eigenvalues. Doubles the amount   ### *)
(* ###    of the elements of the association by introducing a bunch of new variables ### *)
(* ###    that correspond to the choice of sign. Assumes input is well-formed        ### *)
(* ###    (i.e. eigenvalues w.r.t last parameter are all positive)                   ### *)
BlowUpLastEigSigns[assoc_, indetHead_] :=
    Module[{indets = {}},
           {Association[Flatten[KeyValueMap[Function[{key, val},
                                                     AppendTo[indets, indetHead @@ key];
                                                     {Rule[key, indetHead @@ key],
                                                      Rule[Mask @@ Append[key[[ ;;-2]],
                                                                          - key[[-1]]],
                                                           val - indetHead @@ key]}],
                                            assoc]]],
            indets}];
(* ### vv Restore the dependence on the last evolution parameter, corresponding to the antiparallel braid ### *)
(* ###    from the requirement that the result is symmetric function of the eigenvalues.                  ### *)
(* ### vv This element is to conveniently structure the code, without CompoundExpression[...] or          ### *)
(* ###    Block[{}, ...]                                                                                  ### *)
ClearAll[B];
SetAttributes[B, HoldAllComplete];
B[body_] :=
    CompoundExpression[body];
SymmetricallyRestoreEvoMap[assoc_] :=
    Module[{indets, blownUpAssoc},
           {blownUpAssoc, indets} = BlowUpLastEigSigns[assoc, AA];
           Module[{eqns = {}},
                  Module[{seenQ = <||>},
                         eqns = KeyValueMap[Function[{key, val},
                                                     Module[{sortedKey = Sort[key]},
                                                            If[KeyExistsQ[seenQ, sortedKey],
                                                               {},
                                                               B[seenQ[sortedKey] = True;
                                                                 Map[Function[{permKey},
                                                                              0 == (val - Lookup[blownUpAssoc, permKey, 0])],
                                                                     Permutations[sortedKey]]]]]],
                                            blownUpAssoc];
                         (* ### ^^ Symmetry w.r.t permutation of all indices ### *)
                         eqns = Flatten[eqns];
                         Module[{ans = Solve[eqns, indets]},
                                blownUpAssoc /. ans[[1]]]]]];
(* SymmetricallyRestoreEvoMap[assoc_] := *)
(*     Module[{res = <||>, key, val, *)
(*             indets = {}}, *)
(*            Iterate[{{eig1, eig2, eig3}, MkTupleIter[AList[1, -1, t q^2], AList[1, -1, t q^2], AList[1, -1, t q^2]]}, *)
(*                    If[t q^2 === eig3, *)
(*                       AssociateTo[res, Rule[Mask[eig1, eig2, eig3], Lookup[assoc, Mask[eig1, eig2, eig3], 0]]], *)
(*                       If[1 === eig3, *)
(*                          Block[{}, *)
(*                                AppendTo[indets, AA[eig1, eig2, eig3]]; *)
(*                                AssociateTo[res, Rule[Mask[eig1, eig2, eig3], AA[eig1, eig2, eig3]]]], *)
(*                          If[-1 === eig3, *)
(*                             AssociateTo[res, Rule[Mask[eig1, eig2, eig3], *)
(*                                                   Lookup[assoc, Mask[eig1, eig2, -eig3], 0] - AA[eig1, eig2, -eig3]]]]]]]; *)
(*            (\* ### vv We further need to solve for symmetry ### *\) *)
(*            Module[{eqns = {}}, *)
(*                   Scan[Function[{eigSet}, *)
(*                                 AppendTo[eqns, Map[Lookup[res, Mask @@ #, 0] - Lookup[res, Mask @@ eigSet, 0] == 0 &, *)
(*                                                    Permutations[eigSet]]]], *)
(*                        DeleteDuplicates[Map[Sort, Tuples[{1, -1, t q^2}, 3]]]]; *)
(*                   Module[{ans = Quiet[Solve[Flatten[eqns], indets]]}, *)
(*                          res /. ans[[1]]]]]; *)
FullSymmRestore[label_] :=
    Module[{tmpans = Factor[SymmetricallyRestoreEvoMap[evoRulesCombed[label]]]},
           Rule[evoRulesSymrest[label],
                Factor[Simplify[tmpans /. Simplify[Solve[tmpans[Mask[-1,-1,1]] == 0,
                                                         {AA[1,1,1]}][[1]]]]]]
           /. {Rule -> Set}];
PretzelAnsatz[r_, g_, eigs_] :=
    Module[{i, k},
           Sum[Product[Plus @@ Map[AA[k, #] lambda[i, #] &,
                                   eigs],
                       {i, 0, g}],
               {k, 0, r}]];
(* FullSymmRestore["PPM"]; *)
(* FullSymmRestore["PPP"]; *)
(* FullSymmRestore["MMM"]; *)
CombUpEvoMap2[assoc_] :=
    Module[{res = <||>, key, val},
           Iterate[{rule, MkListIter[Normal[assoc]]},
                   (* Print["rule: ", rule]; *)
                   key = rule[[1]]; val = rule[[2]]; (* ### << We need this destructuring ### *)
                   Module[{modKey = Mask @@ Simplify[Abs[List @@ key], Assumptions -> q > 0 && t > 0]},
                          Module[{prevVal = Lookup[res, modKey, 0]},
                                 (* Print["modKey: ", modKey, " prevVal: ", prevVal]; *)
                                 AssociateTo[res, Rule[modKey, prevVal + val]]]]];
           Association[KeyValueMap[Rule[#1, Factor[Simplify[#2]]] &, res]]];
(* ### vv Figure out all free AA[*] parameters that occur in the values of a given association ### *)
GetAIndets[assoc_] :=
    Sort[Select[Variables[Values[assoc]],
                AA === Head[#] &]];
PrettyPrintRules[assoc_, preAssoc_] :=
    (* ### ^^ We need to add the preassoc, to print also delta's ### *)
    Module[{res = {},
            aIndets = GetAIndets[preAssoc]},
           (* Print["aIndets", aIndets]; *)
           Scan[Function[{key},
                         If[Or[0 =!= assoc[key], 0 =!= preAssoc[key]],
                            Module[{val = Lookup[assoc, key, 0]},
                                   (* Print["val: ", val]; *)
                                   AppendTo[res,
                                            If[1 === Length[Permutations[key]],
                                               Simplify[Times @@ MapIndexed[#1^Subscript[n, #2[[1]]-1] &, key]],
                                               (Simplify[Times @@ MapIndexed[#1^Subscript[n, #2[[1]]-1] &, key]] + perms)]
                                            * Module[{coeff = Factor[Simplify[val]], i},
                                                     For[i = 1, i <= Length[aIndets], i ++,
                                                         coeff += (Simplify[D[preAssoc[key], aIndets[[i]]]]
                                                                   * Subscript[Delta, i])];
                                                     coeff]]]]],
                DeleteDuplicates[Map[Sort, Keys[assoc]]]];
           (Plus @@ res) /. {t -> T} // TeXForm];
PrettyPrintRulesNaive[assoc_, preAssoc_] :=
    (* ### ^^ We need to add the preassoc, to print also delta's ### *)
    Module[{res = {},
            aIndets = GetAIndets[preAssoc]},
           (* Print["aIndets", aIndets]; *)
           Scan[Function[{key},
                         If[Or[0 =!= assoc[key], 0 =!= preAssoc[key]],
                            Module[{val = Lookup[assoc, key, 0]},
                                   (* Print["val: ", val]; *)
                                   AppendTo[res,
                                            Simplify[Times @@ MapIndexed[#1^Subscript[n, #2[[1]]-1] &, key]]
                                            * Module[{coeff = Factor[Simplify[val]], i},
                                                     For[i = 1, i <= Length[aIndets], i ++,
                                                         coeff += (Simplify[D[preAssoc[key], aIndets[[i]]]]
                                                                   * Subscript[Delta, i])];
                                                     coeff]]]]],
                Keys[assoc]];
           (Plus @@ res) /. {t -> T} // TeXForm];
CCCAlphabet = {"AA", "BB", "CC", "DD", "EE"}; (* ### << More than enough for our purposes ### *)
(* ### vv More elaborate version of symmetric restoring, where regions have more complex shape and  ### *)
(* ###    therefore we need to consider several of them in order to get the whole picture correctly ### *)
SymmRestoreNPletEvoMap[assocs__] :=
    Module[{indets = {}},
           Module[{blownUpAssocs = MapIndexed[Module[{res = BlowUpLastEigSigns[#1, Symbol[CCCAlphabet[[#2[[1]]]]]]},
                                                     indets = Join[indets, res[[2]]];
                                                     res[[1]]] &,
                                              List[assocs]]},
                  (* {blownUpAssocs, indets} *)
                  (* ### vv Alright, now we need to generate a bunch of equations ### *)
                  (* ###    These include: when we do a cyclic permutation of argument, we get to the next assoc   ### *)
                  (* ###                   each blown up assoc is symmetric w.r.t all of its arguments except i-th ### *)
                  Module[{eqns = {}},
                         For[i = 1, i < Length[blownUpAssocs], i ++, (* ### << We loop over all but last association ### *)
                             AppendTo[eqns,
                                      KeyValueMap[Function[{key, val},
                                                           0 == (val - Lookup[blownUpAssocs[[i+1]],
                                                                              Mask[key[[-1]], Sequence @@ key[[ ;; -2]]],
                                                                              0])],
                                                  blownUpAssocs[[i]]]]];
                         (* ### ^^ Invariance w.r.t cyclic permutation ### *)
                         For[i = 1, i <= Length[blownUpAssocs], i ++, (* ### << Here we loop over *all* associations ### *)
                             Module[{seenQ = <||>},
                                    AppendTo[eqns,
                                             KeyValueMap[Function[{key, val},
                                                                  Module[{sortedKey = Mask[key[[i]], Sequence @@ Join[key[[1 ;; i - 1]],
                                                                                                                      key[[i + 1 ;; ]]]]},
                                                                         If[KeyExistsQ[seenQ, sortedKey],
                                                                            {},
                                                                            Block[{},
                                                                                  seenQ[sortedKey] = True;
                                                                                  Map[Function[{subkey},
                                                                                               Module[{newKey = Mask[Sequence
                                                                                                                     @@ subkey[[1 ;; i - 1]],
                                                                                                                     sortedKey[[1]],
                                                                                                                     Sequence
                                                                                                                     @@ subkey[[i ;; ]]]},
                                                                                                      0 == (val
                                                                                                            - Lookup[blownUpAssocs[[i]],
                                                                                                                     newKey,
                                                                                                                     0])]],
                                                                                      Permutations[sortedKey[[2 ;; ]]]]]]]],
                                                         blownUpAssocs[[i]]]]]];
                         (* ### ^^ Symmetry w.r.t all permutations of all other indices ### *)
                         eqns = Flatten[eqns];
                         Module[{ans = Solve[eqns, indets]},
                                blownUpAssocs /. ans[[1]]]]]];
CheckRulesSymmetricQ[assoc_] :=
    And @@ Flatten[KeyValueMap[Function[{key, val},
                                        Map[0 === Simplify[val - assoc[key]] &,
                                            Permutations[key]]],
                               assoc]];
qtOne = (-t) (1 + q^4 t)/(1 + q^2 t)/(1 - q^2 t);
qtTwo = (1 - q^2 t)/q;
qtThree = (1 - q^2 t + q^4 t^2)/(-t)/q^2;
qtTwoBar = (1 - q^2 t)/q/(-t);
qtThreeBar = (1 - q^2 t + q^4 t^2)/(-t)^2/q^2;
TheorEvo[g_] :=
    (qtOne
     Product[1/qtTwo + qtThree/qtTwo (q^2 t)^n[i],
             {i, 0, g}]
     + (qtOne qtThree
        Product[1/qtTwo - 1/qtTwo (q^2 t)^n[i],
                {i, 0, g}]));
MkEvoExpr[evoRules_] :=
    Module[{numArgs = Length[Keys[evoRules][[1]]]}, (* ### << I know this is a bit excessive, but I don't know any other way ### *)
           Simplify[Plus @@ KeyValueMap[#2
                                        * Times @@ MapIndexed[Function[{eigenvalue, number},
                                                                       eigenvalue^n[number[[1]] - 1]],
                                                              #1] &,
                                        evoRules]]];
TheorEvoCorr[g_] :=
    q^(g+1) (t + 1)/2/(1 + q^2 t) (Product[1/2 + 1/2 (-1)^n[i] + (q^2 t)^n[i],
                                           {i, 0, g}]
                                   + Product[1/2 + 1/2 (-1)^n[i] - (q^2 t)^n[i],
                                             {i, 0, g}]);
TheorEvoCorr2[g_] :=
    q^(g+1)/2^(g+1) (t + 1)/(1 + q^2 t) Product[1 - (-1)^n[i],
                                                {i, 0, g}];
TheorEvoRedCorr[g_] :=
    q^(g+2) (1 + t)/2/(1 + q^2 t) (Product[1 + (q^2 t)^n[i], {i, 0, g}]
                                   + Product[1 - (q^2 t)^n[i], {i, 0, g}]);
ReducedGenusOneKhovanov[k_] := (* ### << n = 2 k + 1 ### *)
    ((1 - q^2 t + q^4 t^2) - (q^2 t)^(2 k + 2))/(1 - q^2 t);
UnreducedGenusOneKhovanov[k_] := (* ### << n = 2 k + 1 ### *)
    (q + q^(-1) + q^3 t^2 (1 + q^4 t) (1 - (q^2 t)^(2 k))/(1 - (q^2 t)^2));
TheorOneOneAllEvenRed[g_] :=
    (q^g - (1 - 1/2^g) q^(g)(1 - q^2)/(1 + q^2 t)
     + q^g (1 + q^2)/2 /(1 - q^2 t)^g
     + q^g/4 /(1 - q^2 t)^(g-1) (1 - q^2) Sum[1/2^i (1 - q^2 t)^i, {i, 0, g-2}]);
TheorOneOneMMAllEvenRed[g_] :=
    (q^(2-g)
     + (1 - 1/2^g) (1 - q^2) q^(2-g)/(q^2 + t)
     + q^g (1 + q^2)/2/(- t + q^2)^g
     - q^(g - 2)(1 - q^2)/4/(q^2 - t)^(g-1) Sum[1/2^i/q^(2 i) (q^2 - t)^i, {i, 0, g - 2}]
    );
TheorOneOneMMAllEvenRed1[g_] :=
    (q^(2-g) (T + 1)/(1 + q^2 T)
     + (1 - q^2 T) (1 + q^4 T)/(-T)/(1 + q^2 T)/q q^(g+1) (-T)^(g+1)/(1 - q^2 T)^(g+1));
TheorEvoMM[g_] :=
    (((qtOne
       Product[1/qtTwo + qtThree/qtTwo (lambda)^n[i],
               {i, 0, g}]
       + (qtOne qtThree
          Product[1/qtTwo - 1/qtTwo (lambda)^n[i],
                  {i, 0, g}])) /. {q -> 1/q, t -> 1/t})
     /. {lambda -> q^2 t});
(* ### vv Consider only knots from a series of pretzel knots ### *)
Knotify[seriesLabel_String, genus_] :=
    Knotify[evoRulesCombed[seriesLabel], genus];
Knotify[assoc_Association, genus_] :=
    Simplify[(Simplify[ReplaceAll[MkEvoExpr[assoc],
                                  Prepend[Map[Rule[n[#], 2 k[#] + 1] &, Range[0, genus - 1]],
                                          Rule[n[genus], 2 k[genus]]]],
                       Assumptions -> And @@ Map[Element[k[#], Integers] &, Range[0, genus]]]
              /. Prepend[Map[Rule[k[#], n[#]/2 - 1/2] &, Range[0, genus - 1]],
                         Rule[k[genus], n[genus]/2]])
             /. {n[i_] :> Log[q^2 t, NN[i]]},
             Assumptions -> And[q > 0, q < 1, t > 0, t < 1]];
KhRedBulkKnotsTheor[g_] :=
    q t^2/qtTwo (Product[1/qtTwo + qtThree/qtTwo NN[i], {i, 0, g}]
                 + qtThree Product[1/qtTwo - 1/qtTwo NN[i], {i, 0, g}]);
KhRedPStarKnotsTheor[g_] :=
    (q (-t)/qtTwo (Product[1/qtTwo + qtThree/qtTwo NN[i], {i, 0, g}]
                   + qtThree Product[1/qtTwo - 1/qtTwo NN[i], {i, 0, g}]));
KhRedMStarKnotsTheor[g_] :=
    (q /qtTwo (-t)^(g+1)
     (Product[1/qtTwo + qtThree/qtTwo NN[i], {i, 0, g}]
      + qtThree Product[1/qtTwo - 1/qtTwo NN[i], {i, 0, g}]));
KhAlt1KnotsTheor[g_] :=
    (q (-t)/qtTwo (Product[1/qtTwo + qtThree/qtTwo NN[i], {i, 0, g}]
                   + qtThree Product[1/qtTwo - 1/qtTwo NN[i], {i, 0, g}])
     /. {NN[i_] :> (q^2 t)^nn[i]});
(* ### vv Extracts `degree` homogeneous degree in the product of (1 + NN_i) ### *)
NNProd[numFactors_, degree_] :=
    Coefficient[Product[(1 + epsilon NN[i-1]), {i, 1, numFactors}],
                epsilon, degree];
KhRedDeltaExceptKnotsTheor[g_] :=
    ((-q t)/qtTwo (1 + t) (1 + qtThree)/qtTwo^(g+1) Product[(1 + qtThree NN[i] NN[g]), {i, 0, g - 1}]);
(* KhRedDeltaExcept2KnotsTheor[2] := *)
(*     Block[{g = 2}, *)
(*           ((-q t)/qtTwo (1 + t) (1 + qtThree)/qtTwo^(g+1) *)
(*            (1 + qtThree (NN[0] + NN[1]) NN[2] - qtThree NN[0] NN[1] NN[2]^2))]; *)
KhRedDeltaExcept2KnotsTheor[2] :=
    Block[{g = 2},
          (q (1 + t) 1/qtTwo^g qtThree (1 - NN[0] NN[2])(1 - NN[1] NN[2])
           + q (1 + 1/t) )];
KhRedDeltaExcept2KnotsTheor[g_] :=
    (q (1 + t) 1/qtTwo^g qtThree Product[(1 - NN[i] NN[g]),
                                         {i, 0, g-1}]);
KhRedPExceptKnotsTheor[g_, smartIndex_] :=
    NNSmartChange[((-t) KhRedPStarKnotsTheor[g]
                   + KhRedDeltaExceptKnotsTheor[g]),
                  smartIndex];
KhRedPExcept2KnotsTheor[3, smartIndex_] :=
    NNSmartChange[(-t) KhRedPStarKnotsTheor[3]
                  - KhRedDeltaExcept2KnotsTheor[3]
                  + q^2 (1 + t)/t 1/(q^2 t - 1)
                  + (1 + t)/t^2 (q^4 t^2)^(-1) NN[0] NN[1] NN[2] NN[3]^3
                  + (-1) (1 + t)/t^2 NN[0] NN[1] NN[2] NN[3]^3 1/(q^2 t - 1),
                  smartIndex];
KhRedPExcept2KnotsTheor[g_, smartIndex_] :=
    NNSmartChange[((-t) KhRedPStarKnotsTheor[g]
                   - KhRedDeltaExcept2KnotsTheor[g]),
                  smartIndex];
KhRedMExceptKnotsTheor[g_, smartIndex_] :=
    NNSmartChange[((-t)^(-1) KhRedMStarKnotsTheor[g]
                   - (-t)^(g-1) KhRedDeltaExceptKnotsTheor[g]),
                  smartIndex];
KhRedMExcept2KnotsTheor[3, smartIndex_] :=
    NNSmartChange[(-t)^(-1) KhRedMStarKnotsTheor[3]
                  + (-t)^2 KhRedDeltaExcept2KnotsTheor[3]
                  - (1 + t)(1 + 1/(q^2 t - 1)
                            + q^4 t^2 NN[0] NN[1] NN[2] NN[3]^3
                            + (- q^8 t^4 NN[0] NN[1] NN[2] NN[3]^3)/(q^2 t - 1)),
                  smartIndex];
KhRedMExcept2KnotsTheor[g_, smartIndex_] :=
    NNSmartChange[((-t)^(-1) KhRedMStarKnotsTheor[g]
                   + (-t)^(g-1) KhRedDeltaExcept2KnotsTheor[g]),
                  smartIndex];
NNSmartChange[expr_, smartIndex_] :=
    ReplaceAll[expr, NNSmartSubs[expr, smartIndex]];
NNSmartSubs[expr_, smartIndex_] :=
    Module[{nvars = Sort[Select[Variables[expr], NN === Head[#] &]]},
           Module[{g = nvars[[-1, 1]]},
                  Map[Rule[NN[Mod[#[[1]] + g - smartIndex, g + 1]],
                           #] &,
                      nvars]]];
GetNNCoeff[expr_, nPowers_] :=
    Module[{vars = Sort[Select[Variables[expr], NN === Head[#] &]]},
           (* Print["vars: ", vars]; *)
           Module[{preCoeff = Select[CoefficientRules[expr, vars],
                                     #[[1]] == nPowers &]},
                  (* Print["preCoeff: ", preCoeff]; *)
                  If[0 === Length[preCoeff],
                     0,
                     If[1 === Length[preCoeff],
                        preCoeff[[1, 2]],
                        GetNNCoeff::error]]]];
EvalAtIndices[expr_, indices_] :=
    (((expr /. {NN[i_] :> (q^2 t)^indices[[i+1]]})
      /. {q -> 1/q, t -> 1/t})
     * If[And[OddQ[Length[indices]],
              And @@ Map[OddQ, indices]],
          1, (* ### << In case all the indices are odd and genus is even, we used all antiparallel orientation for our pretzel knot ### *)
          (* ### vv Otherwise we used parallel-but-maybe-last-one orientation ### *)
          (t q^3)^If[EvenQ[Length[indices]],
                     (Plus @@ indices),
                     (Plus @@ indices[[1 ;; -2]])]]);
PretzelKnotsInsideALatticeIter[latticeSize_, genus_] :=
    GrepIter[Function[{indices},
                      Not[Or[Or @@ Map[EvenQ, indices[[1 ;; -2]]],
                             And[OddQ[genus], OddQ[indices[[-1]]]]]]],
             MkTupleIter @@ Module[{i}, Table[{-latticeSize, latticeSize}, {i, 0, genus}]]];
CheckKhRedOnCutoffLattice[genus_] :=
    Module[{totalCount = 0, successCount = 0,
            bulks = Table[{}, {i, 0, genus}],
            detailedResults = (<|"fails" -> {},
                               "bulks" -> Null,
                               "pExcept" -> {},
                               "mExcept" -> {},
                               "pExcept2" -> {},
                               "mExcept2" -> {}
                               |>)},
           LoadAllPrecomps[genus];
           Iterate[{indices, PretzelKnotsInsideALatticeIter[CCCLatticeSize, genus]},
                   Module[{cmp = Function[{fun},
                                          0 === Simplify[(PrecompKhRed @@ indices) - EvalAtIndices[fun, indices]]],
                           flag = False},
                          totalCount += 1;
                          Module[{pStarCmp = Simplify[(PrecompKhRed @@ indices)
                                                      /EvalAtIndices[KhRedPStarKnotsTheor[genus], indices]]},
                                 For[i = 0, i <= genus, i ++,
                                     If[pStarCmp === (-t)^(-i), (* ### << Because we are comparing on the level of writhe-ful Khovanovs ### *)
                                        AppendTo[bulks[[i + 1]], indices];
                                        flag = True]]];
                          If[Or @@ Map[cmp[KhRedPExceptKnotsTheor[genus, #]] &, Range[0, genus]],
                             AppendTo[detailedResults["pExcept"], indices]; flag = True];
                          If[Or @@ Map[cmp[KhRedMExceptKnotsTheor[genus, #]] &, Range[0, genus]],
                             AppendTo[detailedResults["mExcept"], indices]; flag = True];
                          If[Or @@ Map[cmp[KhRedPExcept2KnotsTheor[genus, #]] &, Range[0, genus]],
                             AppendTo[detailedResults["pExcept2"], indices]; flag = True];
                          If[Or @@ Map[cmp[KhRedMExcept2KnotsTheor[genus, #]] &, Range[0, genus]],
                             AppendTo[detailedResults["mExcept2"], indices]; flag = True];
                          If[flag,
                             successCount += 1,
                             AppendTo[detailedResults["fails"], indices]]]];
           Print["success / total: ", successCount, " ", totalCount];
           detailedResults["bulks"] = bulks;
           detailedResults
          ];
KnotifyRules[assoc_, "oneeven"] :=
    Module[{res = <||>, key, val},
           Scan[Function[{rule},
                         {key, val} = List @@ rule;
                         Module[{modButlastKey = Mask @@ Simplify[Abs[List @@ key[[;;-2]]], Assumptions -> q > 0 && t > 0],
                                 signButlastKey = Times @@ Simplify[Sign[List @@ key[[;;-2]]], Assumptions -> q > 0 && t > 0],
                                 modLastKey = Simplify[Abs[key[[-1]]], Assumptions -> q > 0 && t > 0]},
                                Module[{modKey = Mask[Sequence @@ modButlastKey, modLastKey]},
                                       res[modKey] = (Lookup[res, modKey, 0]
                                                      + signButlastKey * val)]]],
                Normal[assoc]];
           res];
Unframed[fun_, indices_] :=
    Module[{preAns = ((fun @@ indices)
                      /(t q^3)^(If[EvenQ[Length[indices]],
                                   (Plus @@ indices),
                                   If[OddQ[indices[[-1]]], (* ### << braid was in "all antiparallel" orientation ### *)
                                      0,
                                      (Plus @@ indices[[1 ;; -2]])]]))},
           Expand[Simplify[preAns /. {q -> 1/q, t -> 1/t}]]];
DumbEvalAtIndices[expr_, indices_] :=
    (expr /. {NN[i_] :> (q^2 t)^indices[[i+1]],
              n[i_] :> indices[[i+1]]});
KhovanovWidth[expr_] :=
    Module[{minTDeg = Exponent[expr, t, Min],
            minQDeg = Exponent[expr, q, Min]},
           Length[Tally[Map[2 #[[1]] - #[[2]] &,
                            Map[{#[[1, 1]] + minTDeg, #[[1,2]] + minQDeg} &,
                                CoefficientRules[expr t^(-minTDeg) q^(-minQDeg),
                                                 {t, q}]]]]]];
(* ### Check, that the formula for cutoff, that I propose, correctly describes all hte points in ### *)
(* ### `points`, and doesn't describe any other points in the cube, i.e. that this is the "right" ### *)
(* ### cutoff formula ### *)
CheckCutoffFormula[points_, cubeSize_, genus_, formula_] :=
    Module[{theorPoints = CollectIter[GrepIter[formula,
                                               PretzelKnotsInsideALatticeIter[cubeSize, genus]]],
            exprPoints = Select[points,
                                And @@ Map[Function[{component},
                                                    Abs[component] <= cubeSize],
                                           #] &]},
           (<|"missing" -> Complement[exprPoints, theorPoints],
            "extra" -> Complement[theorPoints, exprPoints]|>)];
Bulks0Cut[coords_] :=
    Or[And @@ Map[# > 0 &, coords],
       And[coords[[-1]] >= 0,
           And @@ Map[# > 0 &, coords[[ ;;-2]]]],
       (* And[coords[[-1]] >= -1, *)
       (*     And @@ Map[# > 1 &, coords[[ ;;-2]]]], *)
       Or @@ Map[Function[{aCoord},
                          And[coords[[aCoord]] >= -1,
                              And @@ Map[# > 1 &, Join[coords[[1 ;; aCoord - 1]],
                                                       coords[[aCoord + 1 ;; ]]]]]],
                 Range[1, Length[coords]]]];
BulksGCut[coords_] :=
    Or[And @@ Map[# < 0 &, coords],
       And[coords[[-1]] <= 0,
           And @@ Map[# < 0 &, coords[[ ;;-2]]]],
       (* And[coords[[-1]] >= -1, *)
       (*     And @@ Map[# > 1 &, coords[[ ;;-2]]]], *)
       Or @@ Map[Function[{aCoord},
                          And[coords[[aCoord]] <= 1,
                              And @@ Map[# < -1 &, Join[coords[[1 ;; aCoord - 1]],
                                                        coords[[aCoord + 1 ;; ]]]]]],
                 Range[1, Length[coords]]]];
PExceptCut[coords_] :=
    And[coords[[-1]] <= 0,
        EvenQ[coords[[-1]]],
        And @@ Map[# > - coords[[-1]] &, coords[[;; -2]]]];
MExceptCut[coords_] :=
    And[coords[[-1]] >= 0,
        EvenQ[coords[[-1]]],
        And @@ Map[# < - coords[[-1]] &, coords[[;; -2]]]];
PExcept2Cut[coords_] :=
    Or[Or @@ Map[Function[{aCoord},
                          And[coords[[aCoord]] <= 0,
                              OddQ[coords[[aCoord]]],
                              And @@ Map[# > -coords[[aCoord]] &,
                                         Join[coords[[1 ;; aCoord - 1]],
                                              coords[[aCoord + 1 ;; ]]]]]],
                 Range[1, Length[coords]]],
       Or @@ Map[Function[{aCoord},
                          And[coords[[aCoord]] == 1,
                              And @@ Map[# >= 0 &,
                                         Join[coords[[1 ;; aCoord - 1]],
                                              coords[[aCoord + 1 ;; ]]]]]],
                 Range[1, Length[coords]]]];
MExcept2Cut[coords_] :=
    Or[Or @@ Map[Function[{aCoord},
                          And[coords[[aCoord]] >= 0,
                              OddQ[coords[[aCoord]]],
                              And @@ Map[# < -coords[[aCoord]] &,
                                         Join[coords[[1 ;; aCoord - 1]],
                                              coords[[aCoord + 1 ;; ]]]]]],
                 Range[1, Length[coords]]],
       Or @@ Map[Function[{aCoord},
                          And[coords[[aCoord]] == -1,
                              And @@ Map[# <= 0 &,
                                         Join[coords[[1 ;; aCoord - 1]],
                                              coords[[aCoord + 1 ;; ]]]]]],
                 Range[1, Length[coords]]]];
OneNonNegativeQ[coords_] :=
    (0 =!= Length[Select[coords,
                         # >= 0 &]]);
OneNonPositiveQ[coords_] :=
    (0 =!= Length[Select[coords,
                         # <= 0 &]]);
NumNegatives[coords_] :=
    If[MemberQ[coords, 0],
       hasZero,
       Length[Select[coords,
                     # < 0 &]]];
Signaature[coords_] :=
    Module[{minus = 0,
            plus = 0,
            zero = 0},
           Scan[Function[{coord},
                         If[0 < coord,
                            plus += 1,
                            If[0 > coord,
                               minus += 1,
                               zero += 1]]],
                coords];
           {minus, zero, plus}];
(* ### ^^ ENDLIB ### *)

qtTwo /. {t -> q^(-2)}

LoadAllPrecomps[3];

PrecompKhRed[1,1,1,10]

KhovanovWidth[PrecompKhRed[1,1,1,2]]

Block[{genus = 3, latticeSize = 8},
      Iterate[{indices, PretzelKnotsInsideALatticeIter[latticeSize, genus]},
              Module[{it = KhovanovWidth[PrecompKhRed @@ indices]},
                     If[it > 2,
                        Print[indices, it]]]]]


status = Block[{CCCLatticeSize = 6},
               CheckKhRedOnCutoffLattice[3]];

status["bulks"][[4]]

Tally[Map[Signaature, status["bulks"][[4]]]]

Out[56]= {{{4, 0, 0}, 81}, {{3, 1, 0}, 27}}

Out[55]= {{{3, 0, 1}, 273}, {{2, 1, 1}, 81}, {{2, 0, 2}, 171}}

Out[54]= {{{2, 0, 2}, 171}, {{1, 1, 2}, 81}, {{1, 0, 3}, 273}}

Out[53]= {{{0, 1, 3}, 27}, {{0, 0, 4}, 81}}

Tally[Map[Plus @@ # &, Select[status["bulks"][[2]],
                              Signaature[#] == {2, 0, 2} &]]]

?? TorusKnot[3,5]



Select[status["bulks"][[2]],
       And[Signaature[#] == {2, 0, 2},
           (Plus @@ #) == 1]
       &]

Select[status["bulks"][[3]],
       And[Signaature[#] == {2, 0, 2},
           (Plus @@ #) == 1]
       &]

Out[74]= {{-3, -3, 1, 6}, {-3, 1, -3, 6}, {-3, 1, 5, -2}, {-3, 5, 1, -2}, 
 
>    {1, -3, -3, 6}, {1, -3, 5, -2}, {1, 5, -3, -2}, {5, -3, 1, -2}, 
 
>    {5, 1, -3, -2}}


Tally[Map[Plus @@ # &, Select[status["bulks"][[3]],
                              Signaature[#] == {2, 0, 2} &]]]

Out[72]= {{-7, 15}, {-5, 36}, {-3, 54}, {-1, 54}, {-9, 3}, {1, 9}}


Select[status["bulks"][[3]],
       Signaature[#] == {2, 0, 2} &]

CheckCutoffFormula[status["bulks"][[2]],
                   6,
                   2,
                   Function[{coords},
                            And[OneNonNegativeQ[coords],
                                OneNonPositiveQ[coords],
                                And @@ Module[{j},
                                              Table[Or[coords[[j]] > 1,
                                                       And @@ Map[# <= - coords[[j]] &, Drop[coords, {j}]]],
                                                    {j, 1, Length[coords]}]],
                                And @@ Module[{j},
                                              Table[Or[coords[[j]] < -1,
                                                       And @@ Map[# >= - coords[[j]] &, Drop[coords, {j}]]],
                                                    {j, 1, Length[coords]}]]]]]
                                



LoadAllPrecomps[2];

(* PrecompKhRed[7,7,-1,8] *)
(* Expand[Simplify[EvalAtIndices[(-t) KhRedPStarKnotsTheor[3], {7,7,-1,8}]]] *)
(* NNSmartChange[KhRedDeltaExcept2KnotsTheor[3], *)
(*               2] *)

Unframed[PrecompKhRed, {3,3,0}] // InputForm

PrecompKhRed[3,3,0] // InputForm

KhRed(3,3,0) := q^3 + 2*q^7*t^2 + 2*q^9*t^3 + q^11*t^4 + 2*q^13*t^5 + q^15*t^6;
KhRed(3,3,-1) := q^(-3) + 1/(q^9*t^3) + 1/(q^7*t^2);
KhRed(3,3,1) := q^(-3) + 1/(q^17*t^7) + 1/(q^15*t^6) + 2/(q^13*t^5) + 3/(q^11*t^4) + 2/(q^9*t^3) + 3/(q^7*t^2) + 2/(q^5*t);

KhRedNorm(3,3,0) := q^3 + 2*q^5*t + q^7*t^2 + 2*q^9*t^3 + 2*q^11*t^4 + q^15*t^6;
KhRedNorm(3,3,-1) := q^3 + 2*q^5*t + 3*q^7*t^2 + 2*q^9*t^3 + 3*q^11*t^4 + 2*q^13*t^5 + q^15*t^6 + q^17*t^7;
KhRedNorm(3,3,1) := q^3 + 2*q^5*t + 3*q^7*t^2 + 2*q^9*t^3 + 3*q^11*t^4 + 2*q^13*t^5 + q^15*t^6 + q^17*t^7;

Block[{indices = {7, 9, -3, 4}},
      Expand[Simplify[((Unframed[PrecompKhRed, indices]
                        - DumbEvalAtIndices[NNSmartChange[(-t) KhRedPStarKnotsTheor[3]
                                                          - KhRedDeltaExcept2KnotsTheor[3]
                                                          (* + q^2 (1 + t)/t 1/(q^2 t - 1) *)
                                                          + (1 + t)/t^2
                                                          + (1 + t)/t^2 (q^4 t^2)^(-1) NN[0] NN[1] NN[2] NN[3]^3
                                                          + (1 + t)/t^2 (1 - NN[0] NN[1] NN[2] NN[3]^3) 1/(q^2 t - 1)
                                                          ,2],
                                            indices]))]]]

Unframed[PrecompKhRed, {5,3,-2}] // InputForm

Expand[Simplify[DumbEvalAtIndices[KhRedPStarKnotsTheor[2] (-t), {5, 3, -2}]]

            5  2     13  6    17  8
Out[86]= -(q  t ) + q   t  + q   t

          5      13  5    17  7
Out[84]= q  t - q   t  - q   t

Out[82]//InputForm= 
q^5*t + q^7*t^2 + q^7*t^3 + q^11*t^4 + q^11*t^5 + q^13*t^6 + q^17*t^8

Block[{indices = {-3, -3, 1, -2}},
      Expand[Simplify[Unframed[PrecompKhRed, indices]]]]

            1        1        1       1       1
Out[164]= ------ + ------ + ----- + ----- + -----
           14  7    10  5    8  4    8  3    4  2
          q   t    q   t    q  t    q  t    q  t

Block[{indices = {-3, -3, 1, -2}},
      Expand[Simplify[DumbEvalAtIndices[NNSmartChange[(-t)^(-1) KhRedMStarKnotsTheor[3], 2],
                                        indices]]]]


Block[{indices = {-3, -3, 1, -2}},
      Expand[Simplify[DumbEvalAtIndices[NNSmartChange[KhRedDeltaExcept2KnotsTheor[3], 2],
                                        indices]]]]

            1       1       1       1       1      -2     1     1
Out[169]= ----- + ----- + ----- + ----- + ----- + t   + ----- + -
           8  6    8  5    6  5    6  4    2  3          2  2   t
          q  t    q  t    q  t    q  t    q  t          q  t

Block[{indices = {-3, -3, 1, -4}},
      Expand[Simplify[Unframed[PrecompKhRed, indices]
                      - DumbEvalAtIndices[KhRedMExcept2KnotsTheor[3, 2],
                                          indices]]]]


Block[{indices = {-3, -5, 1, -8}},
      Factor[Expand[Simplify[
          DumbEvalAtIndices[NNSmartChange[(Unframed[PrecompKhRed, indices]
                                           -((-t)^(-1) KhRedMStarKnotsTheor[3]
                                             + (-t)^2 KhRedDeltaExcept2KnotsTheor[3]
                                             (* - (1 + t)(1 + 1/(q^2 t - 1)) *)
                                             + q^2 t (1 + t)(1 + q^2 t + q^4 t^2)
                                             - (1 + t)(q^4 t^2 NN[0] NN[1] NN[2] NN[3]^3)
                                             - (1 + t)/(q^2 t - 1) q^8 t^4 * (1 - NN[0] NN[1] NN[2] NN[3]^3)))
                                          ,2],
                            indices]]]]]

(* FromCoefficientRules[ *)
(*     Map[Rule[#[[1]], Factor[Simplify[#[[2]]]]] &, *)
(*         CoefficientRules[ *)
(*             Expand[Block[{g = 2}, *)
(*                          Module[{i}, *)
(*                                 1/(z-1)^2 *)
(*                                 (Product[(1 + (-1/z + 1 - z) NN[i]), *)
(*                                          {i, 0, g}] *)
(*                                  + *)
(*                                  (-1/z + 1 - z) Product[(1 - NN[i]), *)
(*                                                         {i, 0, g}])]]], *)
(*             {NN[0], NN[1], NN[2]}]], *)
(*     {NN[0], NN[1], NN[2]}] *)

Expand[Factor[FullSimplify[(KhRedPStarKnotsTheor[2]
                            /. {NN[i_] :> (q^2 t)^n[i]}
                            /. {n[0] -> 1,
                                n[1] -> 31,
                                n[2] -> 10})]]] // InputForm

Out[11]//InputForm= 
q^3 + 2*q^5*t + 3*q^7*t^2 + 4*q^9*t^3 + 5*q^11*t^4 + 6*q^13*t^5 + 
 7*q^15*t^6 + 8*q^17*t^7 + 9*q^19*t^8 + 10*q^21*t^9 + 10*q^23*t^10 + 
 11*q^25*t^11 + 11*q^27*t^12 + 11*q^29*t^13 + 11*q^31*t^14 + 11*q^33*t^15 + 
 11*q^35*t^16 + 11*q^37*t^17 + 11*q^39*t^18 + 11*q^41*t^19 + 11*q^43*t^20 + 
 11*q^45*t^21 + 11*q^47*t^22 + 11*q^49*t^23 + 11*q^51*t^24 + 11*q^53*t^25 + 
 11*q^55*t^26 + 11*q^57*t^27 + 11*q^59*t^28 + 11*q^61*t^29 + 11*q^63*t^30 + 
 10*q^65*t^31 + 10*q^67*t^32 + 9*q^69*t^33 + 8*q^71*t^34 + 7*q^73*t^35 + 
 6*q^75*t^36 + 5*q^77*t^37 + 4*q^79*t^38 + 3*q^81*t^39 + 2*q^83*t^40 + 
 q^85*t^41 + q^87*t^42


LoadAllPrecomps[2]

PrecompKhRed[1,1,1]

          -3     1       1
Out[23]= q   + ----- + -----
                9  3    7  2
               q  t    q  t

KhovanovWidth[PrecompKhRed[3,3,2]]




KhovanovWidth[PrecompKhRed[3,3,-2]]

Out[17]= {{0, 0} -> PrecompKhRed[3, 3, -2]}


Expand[Factor[Simplify[EvalAtIndices[NNSmartChange[(* (-t) KhRedPStarKnotsTheor[3] *)
                                                   KhRedDeltaExcept2KnotsTheor[3],
                                                   2]
                                     ,{7,7,-1,8}]]]]




status = Block[{CCCLatticeSize = 6},
               CheckKhRedOnCutoffLattice[3]];

success / total: 1368 1512


status

Out[15]= <|fails -> 
 
>     {{-5, -5, 3, 2}, {-5, -5, 3, 4}, {-5, -5, 3, 6}, {-5, -5, 5, 2}, 
 
>      {-5, -5, 5, 4}, {-5, -5, 5, 6}, {-5, -3, 3, 2}, {-5, -3, 3, 4}, 
 
>      {-5, -3, 3, 6}, {-5, -3, 5, 2}, {-5, -3, 5, 4}, {-5, -3, 5, 6}, 
 
>      {-5, 3, -5, 2}, {-5, 3, -5, 4}, {-5, 3, -5, 6}, {-5, 3, -3, 2}, 
 
>      {-5, 3, -3, 4}, {-5, 3, -3, 6}, {-5, 3, 3, -6}, {-5, 3, 3, -4}, 
 
>      {-5, 3, 3, -2}, {-5, 3, 5, -6}, {-5, 3, 5, -4}, {-5, 3, 5, -2}, 
 
>      {-5, 5, -5, 2}, {-5, 5, -5, 4}, {-5, 5, -5, 6}, {-5, 5, -3, 2}, 
 
>      {-5, 5, -3, 4}, {-5, 5, -3, 6}, {-5, 5, 3, -6}, {-5, 5, 3, -4}, 
 
>      {-5, 5, 3, -2}, {-5, 5, 5, -6}, {-5, 5, 5, -4}, {-5, 5, 5, -2}, 
 
>      {-3, -5, 3, 2}, {-3, -5, 3, 4}, {-3, -5, 3, 6}, {-3, -5, 5, 2}, 
 
>      {-3, -5, 5, 4}, {-3, -5, 5, 6}, {-3, -3, 3, 2}, {-3, -3, 3, 4}, 
 
>      {-3, -3, 3, 6}, {-3, -3, 5, 2}, {-3, -3, 5, 4}, {-3, -3, 5, 6}, 
 
>      {-3, 3, -5, 2}, {-3, 3, -5, 4}, {-3, 3, -5, 6}, {-3, 3, -3, 2}, 
 
>      {-3, 3, -3, 4}, {-3, 3, -3, 6}, {-3, 3, 3, -6}, {-3, 3, 3, -4}, 
 
>      {-3, 3, 3, -2}, {-3, 3, 5, -6}, {-3, 3, 5, -4}, {-3, 3, 5, -2}, 
 
>      {-3, 5, -5, 2}, {-3, 5, -5, 4}, {-3, 5, -5, 6}, {-3, 5, -3, 2}, 
 
>      {-3, 5, -3, 4}, {-3, 5, -3, 6}, {-3, 5, 3, -6}, {-3, 5, 3, -4}, 
 
>      {-3, 5, 3, -2}, {-3, 5, 5, -6}, {-3, 5, 5, -4}, {-3, 5, 5, -2}, 
 
>      {3, -5, -5, 2}, {3, -5, -5, 4}, {3, -5, -5, 6}, {3, -5, -3, 2}, 
 
>      {3, -5, -3, 4}, {3, -5, -3, 6}, {3, -5, 3, -6}, {3, -5, 3, -4}, 
 
>      {3, -5, 3, -2}, {3, -5, 5, -6}, {3, -5, 5, -4}, {3, -5, 5, -2}, 
 
>      {3, -3, -5, 2}, {3, -3, -5, 4}, {3, -3, -5, 6}, {3, -3, -3, 2}, 
 
>      {3, -3, -3, 4}, {3, -3, -3, 6}, {3, -3, 3, -6}, {3, -3, 3, -4}, 
 
>      {3, -3, 3, -2}, {3, -3, 5, -6}, {3, -3, 5, -4}, {3, -3, 5, -2}, 
 
>      {3, 3, -5, -6}, {3, 3, -5, -4}, {3, 3, -5, -2}, {3, 3, -3, -6}, 
 
>      {3, 3, -3, -4}, {3, 3, -3, -2}, {3, 5, -5, -6}, {3, 5, -5, -4}, 
 
>      {3, 5, -5, -2}, {3, 5, -3, -6}, {3, 5, -3, -4}, {3, 5, -3, -2}, 
 
>      {5, -5, -5, 2}, {5, -5, -5, 4}, {5, -5, -5, 6}, {5, -5, -3, 2}, 
 
>      {5, -5, -3, 4}, {5, -5, -3, 6}, {5, -5, 3, -6}, {5, -5, 3, -4}, 
 
>      {5, -5, 3, -2}, {5, -5, 5, -6}, {5, -5, 5, -4}, {5, -5, 5, -2}, 
 
>      {5, -3, -5, 2}, {5, -3, -5, 4}, {5, -3, -5, 6}, {5, -3, -3, 2}, 
 
>      {5, -3, -3, 4}, {5, -3, -3, 6}, {5, -3, 3, -6}, {5, -3, 3, -4}, 
 
>      {5, -3, 3, -2}, {5, -3, 5, -6}, {5, -3, 5, -4}, {5, -3, 5, -2}, 
 
>      {5, 3, -5, -6}, {5, 3, -5, -4}, {5, 3, -5, -2}, {5, 3, -3, -6}, 
 
>      {5, 3, -3, -4}, {5, 3, -3, -2}, {5, 5, -5, -6}, {5, 5, -5, -4}, 
 
>      {5, 5, -5, -2}, {5, 5, -3, -6}, {5, 5, -3, -4}, {5, 5, -3, -2}}, 
 
>    bulks -> {{{1, 1, 1, 0}, {1, 1, 1, 2}, {1, 1, 1, 4}, {1, 1, 1, 6}, 
 
>       {1, 1, 3, 0}, {1, 1, 3, 2}, {1, 1, 3, 4}, {1, 1, 3, 6}, {1, 1, 5, 0}, 
 
>       {1, 1, 5, 2}, {1, 1, 5, 4}, {1, 1, 5, 6}, {1, 3, 1, 0}, {1, 3, 1, 2}, 
 
>       {1, 3, 1, 4}, {1, 3, 1, 6}, {1, 3, 3, 0}, {1, 3, 3, 2}, {1, 3, 3, 4}, 
 
>       {1, 3, 3, 6}, {1, 3, 5, 0}, {1, 3, 5, 2}, {1, 3, 5, 4}, {1, 3, 5, 6}, 
 
>       {1, 5, 1, 0}, {1, 5, 1, 2}, {1, 5, 1, 4}, {1, 5, 1, 6}, {1, 5, 3, 0}, 
 
>       {1, 5, 3, 2}, {1, 5, 3, 4}, {1, 5, 3, 6}, {1, 5, 5, 0}, {1, 5, 5, 2}, 
 
>       {1, 5, 5, 4}, {1, 5, 5, 6}, {3, 1, 1, 0}, {3, 1, 1, 2}, {3, 1, 1, 4}, 
 
>       {3, 1, 1, 6}, {3, 1, 3, 0}, {3, 1, 3, 2}, {3, 1, 3, 4}, {3, 1, 3, 6}, 
 
>       {3, 1, 5, 0}, {3, 1, 5, 2}, {3, 1, 5, 4}, {3, 1, 5, 6}, {3, 3, 1, 0}, 
 
>       {3, 3, 1, 2}, {3, 3, 1, 4}, {3, 3, 1, 6}, {3, 3, 3, 0}, {3, 3, 3, 2}, 
 
>       {3, 3, 3, 4}, {3, 3, 3, 6}, {3, 3, 5, 0}, {3, 3, 5, 2}, {3, 3, 5, 4}, 
 
>       {3, 3, 5, 6}, {3, 5, 1, 0}, {3, 5, 1, 2}, {3, 5, 1, 4}, {3, 5, 1, 6}, 
 
>       {3, 5, 3, 0}, {3, 5, 3, 2}, {3, 5, 3, 4}, {3, 5, 3, 6}, {3, 5, 5, 0}, 
 
>       {3, 5, 5, 2}, {3, 5, 5, 4}, {3, 5, 5, 6}, {5, 1, 1, 0}, {5, 1, 1, 2}, 
 
>       {5, 1, 1, 4}, {5, 1, 1, 6}, {5, 1, 3, 0}, {5, 1, 3, 2}, {5, 1, 3, 4}, 
 
>       {5, 1, 3, 6}, {5, 1, 5, 0}, {5, 1, 5, 2}, {5, 1, 5, 4}, {5, 1, 5, 6}, 
 
>       {5, 3, 1, 0}, {5, 3, 1, 2}, {5, 3, 1, 4}, {5, 3, 1, 6}, {5, 3, 3, 0}, 
 
>       {5, 3, 3, 2}, {5, 3, 3, 4}, {5, 3, 3, 6}, {5, 3, 5, 0}, {5, 3, 5, 2}, 
 
>       {5, 3, 5, 4}, {5, 3, 5, 6}, {5, 5, 1, 0}, {5, 5, 1, 2}, {5, 5, 1, 4}, 
 
>       {5, 5, 1, 6}, {5, 5, 3, 0}, {5, 5, 3, 2}, {5, 5, 3, 4}, {5, 5, 3, 6}, 
 
>       {5, 5, 5, 0}, {5, 5, 5, 2}, {5, 5, 5, 4}, {5, 5, 5, 6}}, 
 
>      {{-5, -1, 1, 6}, {-5, -1, 3, 2}, {-5, -1, 3, 4}, {-5, -1, 3, 6}, 
 
>       {-5, -1, 5, 2}, {-5, -1, 5, 4}, {-5, -1, 5, 6}, {-5, 1, -1, 6}, 
 
>       {-5, 1, 1, 0}, {-5, 1, 1, 2}, {-5, 1, 1, 4}, {-5, 1, 1, 6}, 
 
>       {-5, 1, 3, 0}, {-5, 1, 3, 2}, {-5, 1, 3, 4}, {-5, 1, 3, 6}, 
 
>       {-5, 1, 5, 0}, {-5, 1, 5, 2}, {-5, 1, 5, 4}, {-5, 1, 5, 6}, 
 
>       {-5, 3, -1, 2}, {-5, 3, -1, 4}, {-5, 3, -1, 6}, {-5, 3, 1, 0}, 
 
>       {-5, 3, 1, 2}, {-5, 3, 1, 4}, {-5, 3, 1, 6}, {-5, 3, 3, 0}, 
 
>       {-5, 3, 3, 2}, {-5, 3, 3, 4}, {-5, 3, 3, 6}, {-5, 3, 5, 0}, 
 
>       {-5, 3, 5, 2}, {-5, 3, 5, 4}, {-5, 3, 5, 6}, {-5, 5, -1, 2}, 
 
>       {-5, 5, -1, 4}, {-5, 5, -1, 6}, {-5, 5, 1, 0}, {-5, 5, 1, 2}, 
 
>       {-5, 5, 1, 4}, {-5, 5, 1, 6}, {-5, 5, 3, 0}, {-5, 5, 3, 2}, 
 
>       {-5, 5, 3, 4}, {-5, 5, 3, 6}, {-5, 5, 5, 0}, {-5, 5, 5, 2}, 
 
>       {-5, 5, 5, 4}, {-5, 5, 5, 6}, {-3, -1, 1, 4}, {-3, -1, 1, 6}, 
 
>       {-3, -1, 3, 2}, {-3, -1, 3, 4}, {-3, -1, 3, 6}, {-3, -1, 5, 2}, 
 
>       {-3, -1, 5, 4}, {-3, -1, 5, 6}, {-3, 1, -1, 4}, {-3, 1, -1, 6}, 
 
>       {-3, 1, 1, 0}, {-3, 1, 1, 2}, {-3, 1, 1, 4}, {-3, 1, 1, 6}, 
 
>       {-3, 1, 3, 0}, {-3, 1, 3, 2}, {-3, 1, 3, 4}, {-3, 1, 3, 6}, 
 
>       {-3, 1, 5, 0}, {-3, 1, 5, 2}, {-3, 1, 5, 4}, {-3, 1, 5, 6}, 
 
>       {-3, 3, -1, 2}, {-3, 3, -1, 4}, {-3, 3, -1, 6}, {-3, 3, 1, 0}, 
 
>       {-3, 3, 1, 2}, {-3, 3, 1, 4}, {-3, 3, 1, 6}, {-3, 3, 3, 0}, 
 
>       {-3, 3, 3, 2}, {-3, 3, 3, 4}, {-3, 3, 3, 6}, {-3, 3, 5, 0}, 
 
>       {-3, 3, 5, 2}, {-3, 3, 5, 4}, {-3, 3, 5, 6}, {-3, 5, -1, 2}, 
 
>       {-3, 5, -1, 4}, {-3, 5, -1, 6}, {-3, 5, 1, 0}, {-3, 5, 1, 2}, 
 
>       {-3, 5, 1, 4}, {-3, 5, 1, 6}, {-3, 5, 3, 0}, {-3, 5, 3, 2}, 
 
>       {-3, 5, 3, 4}, {-3, 5, 3, 6}, {-3, 5, 5, 0}, {-3, 5, 5, 2}, 
 
>       {-1, -5, 1, 6}, {-1, -5, 3, 2}, {-1, -5, 3, 4}, {-1, -5, 3, 6}, 
 
>       {-1, -5, 5, 2}, {-1, -5, 5, 4}, {-1, -5, 5, 6}, {-1, -3, 1, 4}, 
 
>       {-1, -3, 1, 6}, {-1, -3, 3, 2}, {-1, -3, 3, 4}, {-1, -3, 3, 6}, 
 
>       {-1, -3, 5, 2}, {-1, -3, 5, 4}, {-1, -3, 5, 6}, {-1, -1, 1, 2}, 
 
>       {-1, -1, 1, 4}, {-1, -1, 1, 6}, {-1, -1, 3, 2}, {-1, -1, 3, 4}, 
 
>       {-1, -1, 3, 6}, {-1, -1, 5, 2}, {-1, -1, 5, 4}, {-1, -1, 5, 6}, 
 
>       {-1, 1, -5, 6}, {-1, 1, -3, 4}, {-1, 1, -3, 6}, {-1, 1, -1, 2}, 
 
>       {-1, 1, -1, 4}, {-1, 1, -1, 6}, {-1, 1, 1, 0}, {-1, 1, 1, 2}, 
 
>       {-1, 1, 1, 4}, {-1, 1, 1, 6}, {-1, 1, 3, -2}, {-1, 1, 3, 0}, 
 
>       {-1, 1, 3, 2}, {-1, 1, 3, 4}, {-1, 1, 3, 6}, {-1, 1, 5, -4}, 
 
>       {-1, 1, 5, -2}, {-1, 1, 5, 0}, {-1, 1, 5, 2}, {-1, 1, 5, 4}, 
 
>       {-1, 1, 5, 6}, {-1, 3, -5, 2}, {-1, 3, -5, 4}, {-1, 3, -5, 6}, 
 
>       {-1, 3, -3, 2}, {-1, 3, -3, 4}, {-1, 3, -3, 6}, {-1, 3, -1, 2}, 
 
>       {-1, 3, -1, 4}, {-1, 3, -1, 6}, {-1, 3, 1, -2}, {-1, 3, 1, 0}, 
 
>       {-1, 3, 1, 2}, {-1, 3, 1, 4}, {-1, 3, 1, 6}, {-1, 3, 3, -6}, 
 
>       {-1, 3, 3, -4}, {-1, 3, 3, -2}, {-1, 3, 3, 0}, {-1, 3, 5, -6}, 
 
>       {-1, 3, 5, -4}, {-1, 3, 5, -2}, {-1, 3, 5, 0}, {-1, 5, -5, 2}, 
 
>       {-1, 5, -5, 4}, {-1, 5, -5, 6}, {-1, 5, -3, 2}, {-1, 5, -3, 4}, 
 
>       {-1, 5, -3, 6}, {-1, 5, -1, 2}, {-1, 5, -1, 4}, {-1, 5, -1, 6}, 
 
>       {-1, 5, 1, -4}, {-1, 5, 1, -2}, {-1, 5, 1, 0}, {-1, 5, 1, 2}, 
 
>       {-1, 5, 1, 4}, {-1, 5, 1, 6}, {-1, 5, 3, -6}, {-1, 5, 3, -4}, 
 
>       {-1, 5, 3, -2}, {-1, 5, 3, 0}, {-1, 5, 5, -6}, {-1, 5, 5, -4}, 
 
>       {-1, 5, 5, -2}, {-1, 5, 5, 0}, {1, -5, -1, 6}, {1, -5, 1, 0}, 
 
>       {1, -5, 1, 2}, {1, -5, 1, 4}, {1, -5, 1, 6}, {1, -5, 3, 0}, 
 
>       {1, -5, 3, 2}, {1, -5, 3, 4}, {1, -5, 3, 6}, {1, -5, 5, 0}, 
 
>       {1, -5, 5, 2}, {1, -5, 5, 4}, {1, -5, 5, 6}, {1, -3, -1, 4}, 
 
>       {1, -3, -1, 6}, {1, -3, 1, 0}, {1, -3, 1, 2}, {1, -3, 1, 4}, 
 
>       {1, -3, 1, 6}, {1, -3, 3, 0}, {1, -3, 3, 2}, {1, -3, 3, 4}, 
 
>       {1, -3, 3, 6}, {1, -3, 5, 0}, {1, -3, 5, 2}, {1, -3, 5, 4}, 
 
>       {1, -3, 5, 6}, {1, -1, -5, 6}, {1, -1, -3, 4}, {1, -1, -3, 6}, 
 
>       {1, -1, -1, 2}, {1, -1, -1, 4}, {1, -1, -1, 6}, {1, -1, 1, 0}, 
 
>       {1, -1, 1, 2}, {1, -1, 1, 4}, {1, -1, 1, 6}, {1, -1, 3, -2}, 
 
>       {1, -1, 3, 0}, {1, -1, 3, 2}, {1, -1, 3, 4}, {1, -1, 3, 6}, 
 
>       {1, -1, 5, -4}, {1, -1, 5, -2}, {1, -1, 5, 0}, {1, -1, 5, 2}, 
 
>       {1, -1, 5, 4}, {1, -1, 5, 6}, {1, 1, -5, 0}, {1, 1, -5, 2}, 
 
>       {1, 1, -5, 4}, {1, 1, -5, 6}, {1, 1, -3, 0}, {1, 1, -3, 2}, 
 
>       {1, 1, -3, 4}, {1, 1, -3, 6}, {1, 1, -1, 0}, {1, 1, -1, 2}, 
 
>       {1, 1, -1, 4}, {1, 1, -1, 6}, {1, 1, 1, -6}, {1, 1, 1, -4}, 
 
>       {1, 1, 1, -2}, {1, 1, 3, -6}, {1, 1, 3, -4}, {1, 1, 3, -2}, 
 
>       {1, 1, 5, -6}, {1, 1, 5, -4}, {1, 1, 5, -2}, {1, 3, -5, 0}, 
 
>       {1, 3, -5, 2}, {1, 3, -5, 4}, {1, 3, -5, 6}, {1, 3, -3, 0}, 
 
>       {1, 3, -3, 2}, {1, 3, -3, 4}, {1, 3, -3, 6}, {1, 3, -1, -2}, 
 
>       {1, 3, -1, 0}, {1, 3, -1, 2}, {1, 3, -1, 4}, {1, 3, -1, 6}, 
 
>       {1, 3, 1, -6}, {1, 3, 1, -4}, {1, 3, 1, -2}, {1, 3, 3, -6}, 
 
>       {1, 3, 3, -4}, {1, 3, 3, -2}, {1, 3, 5, -6}, {1, 3, 5, -4}, 
 
>       {1, 3, 5, -2}, {1, 5, -5, 0}, {1, 5, -5, 2}, {1, 5, -5, 4}, 
 
>       {1, 5, -5, 6}, {1, 5, -3, 0}, {1, 5, -3, 2}, {1, 5, -3, 4}, 
 
>       {1, 5, -3, 6}, {1, 5, -1, -4}, {1, 5, -1, -2}, {1, 5, -1, 0}, 
 
>       {1, 5, -1, 2}, {1, 5, -1, 4}, {1, 5, -1, 6}, {1, 5, 1, -6}, 
 
>       {1, 5, 1, -4}, {1, 5, 1, -2}, {1, 5, 3, -6}, {1, 5, 3, -4}, 
 
>       {1, 5, 3, -2}, {1, 5, 5, -6}, {1, 5, 5, -4}, {1, 5, 5, -2}, 
 
>       {3, -5, -1, 2}, {3, -5, -1, 4}, {3, -5, -1, 6}, {3, -5, 1, 0}, 
 
>       {3, -5, 1, 2}, {3, -5, 1, 4}, {3, -5, 1, 6}, {3, -5, 3, 0}, 
 
>       {3, -5, 3, 2}, {3, -5, 3, 4}, {3, -5, 3, 6}, {3, -5, 5, 0}, 
 
>       {3, -5, 5, 2}, {3, -5, 5, 4}, {3, -5, 5, 6}, {3, -3, -1, 2}, 
 
>       {3, -3, -1, 4}, {3, -3, -1, 6}, {3, -3, 1, 0}, {3, -3, 1, 2}, 
 
>       {3, -3, 1, 4}, {3, -3, 1, 6}, {3, -3, 3, 0}, {3, -3, 3, 2}, 
 
>       {3, -3, 3, 4}, {3, -3, 3, 6}, {3, -3, 5, 0}, {3, -3, 5, 2}, 
 
>       {3, -3, 5, 4}, {3, -3, 5, 6}, {3, -1, -5, 2}, {3, -1, -5, 4}, 
 
>       {3, -1, -5, 6}, {3, -1, -3, 2}, {3, -1, -3, 4}, {3, -1, -3, 6}, 
 
>       {3, -1, -1, 2}, {3, -1, -1, 4}, {3, -1, -1, 6}, {3, -1, 1, -2}, 
 
>       {3, -1, 1, 0}, {3, -1, 1, 2}, {3, -1, 1, 4}, {3, -1, 1, 6}, 
 
>       {3, -1, 3, -6}, {3, -1, 3, -4}, {3, -1, 3, -2}, {3, -1, 3, 0}, 
 
>       {3, -1, 5, -6}, {3, -1, 5, -4}, {3, -1, 5, -2}, {3, -1, 5, 0}, 
 
>       {3, 1, -5, 0}, {3, 1, -5, 2}, {3, 1, -5, 4}, {3, 1, -5, 6}, 
 
>       {3, 1, -3, 0}, {3, 1, -3, 2}, {3, 1, -3, 4}, {3, 1, -3, 6}, 
 
>       {3, 1, -1, -2}, {3, 1, -1, 0}, {3, 1, -1, 2}, {3, 1, -1, 4}, 
 
>       {3, 1, -1, 6}, {3, 1, 1, -6}, {3, 1, 1, -4}, {3, 1, 1, -2}, 
 
>       {3, 1, 3, -6}, {3, 1, 3, -4}, {3, 1, 3, -2}, {3, 1, 5, -6}, 
 
>       {3, 1, 5, -4}, {3, 1, 5, -2}, {3, 3, -5, 0}, {3, 3, -5, 2}, 
 
>       {3, 3, -5, 4}, {3, 3, -5, 6}, {3, 3, -3, 0}, {3, 3, -3, 2}, 
 
>       {3, 3, -3, 4}, {3, 3, -3, 6}, {3, 3, -1, -6}, {3, 3, -1, -4}, 
 
>       {3, 3, -1, -2}, {3, 3, -1, 0}, {3, 3, 1, -6}, {3, 3, 1, -4}, 
 
>       {3, 3, 1, -2}, {3, 3, 3, -6}, {3, 3, 3, -4}, {3, 3, 5, -6}, 
 
>       {3, 3, 5, -4}, {3, 5, -5, 0}, {3, 5, -5, 2}, {3, 5, -5, 4}, 
 
>       {3, 5, -5, 6}, {3, 5, -3, 0}, {3, 5, -3, 2}, {3, 5, -3, 4}, 
 
>       {3, 5, -3, 6}, {3, 5, -1, -6}, {3, 5, -1, -4}, {3, 5, -1, -2}, 
 
>       {3, 5, -1, 0}, {3, 5, 1, -6}, {3, 5, 1, -4}, {3, 5, 1, -2}, 
 
>       {3, 5, 3, -6}, {3, 5, 3, -4}, {3, 5, 5, -6}, {3, 5, 5, -4}, 
 
>       {5, -5, -1, 2}, {5, -5, -1, 4}, {5, -5, -1, 6}, {5, -5, 1, 0}, 
 
>       {5, -5, 1, 2}, {5, -5, 1, 4}, {5, -5, 1, 6}, {5, -5, 3, 0}, 
 
>       {5, -5, 3, 2}, {5, -5, 3, 4}, {5, -5, 3, 6}, {5, -5, 5, 0}, 
 
>       {5, -5, 5, 2}, {5, -5, 5, 4}, {5, -5, 5, 6}, {5, -3, -1, 2}, 
 
>       {5, -3, -1, 4}, {5, -3, -1, 6}, {5, -3, 1, 0}, {5, -3, 1, 2}, 
 
>       {5, -3, 1, 4}, {5, -3, 1, 6}, {5, -3, 3, 0}, {5, -3, 3, 2}, 
 
>       {5, -3, 3, 4}, {5, -3, 3, 6}, {5, -3, 5, 0}, {5, -3, 5, 2}, 
 
>       {5, -1, -5, 2}, {5, -1, -5, 4}, {5, -1, -5, 6}, {5, -1, -3, 2}, 
 
>       {5, -1, -3, 4}, {5, -1, -3, 6}, {5, -1, -1, 2}, {5, -1, -1, 4}, 
 
>       {5, -1, -1, 6}, {5, -1, 1, -4}, {5, -1, 1, -2}, {5, -1, 1, 0}, 
 
>       {5, -1, 1, 2}, {5, -1, 1, 4}, {5, -1, 1, 6}, {5, -1, 3, -6}, 
 
>       {5, -1, 3, -4}, {5, -1, 3, -2}, {5, -1, 3, 0}, {5, -1, 5, -6}, 
 
>       {5, -1, 5, -4}, {5, -1, 5, -2}, {5, -1, 5, 0}, {5, 1, -5, 0}, 
 
>       {5, 1, -5, 2}, {5, 1, -5, 4}, {5, 1, -5, 6}, {5, 1, -3, 0}, 
 
>       {5, 1, -3, 2}, {5, 1, -3, 4}, {5, 1, -3, 6}, {5, 1, -1, -4}, 
 
>       {5, 1, -1, -2}, {5, 1, -1, 0}, {5, 1, -1, 2}, {5, 1, -1, 4}, 
 
>       {5, 1, -1, 6}, {5, 1, 1, -6}, {5, 1, 1, -4}, {5, 1, 1, -2}, 
 
>       {5, 1, 3, -6}, {5, 1, 3, -4}, {5, 1, 3, -2}, {5, 1, 5, -6}, 
 
>       {5, 1, 5, -4}, {5, 1, 5, -2}, {5, 3, -5, 0}, {5, 3, -5, 2}, 
 
>       {5, 3, -5, 4}, {5, 3, -5, 6}, {5, 3, -3, 0}, {5, 3, -3, 2}, 
 
>       {5, 3, -3, 4}, {5, 3, -3, 6}, {5, 3, -1, -6}, {5, 3, -1, -4}, 
 
>       {5, 3, -1, -2}, {5, 3, -1, 0}, {5, 3, 1, -6}, {5, 3, 1, -4}, 
 
>       {5, 3, 1, -2}, {5, 3, 3, -6}, {5, 3, 3, -4}, {5, 3, 5, -6}, 
 
>       {5, 3, 5, -4}, {5, 5, -5, 0}, {5, 5, -5, 2}, {5, 5, -5, 4}, 
 
>       {5, 5, -5, 6}, {5, 5, -3, 0}, {5, 5, -3, 2}, {5, 5, -1, -6}, 
 
>       {5, 5, -1, -4}, {5, 5, -1, -2}, {5, 5, -1, 0}, {5, 5, 1, -6}, 
 
>       {5, 5, 1, -4}, {5, 5, 1, -2}, {5, 5, 3, -6}, {5, 5, 3, -4}, 
 
>       {5, 5, 5, -6}}, {{-5, -5, -5, 6}, {-5, -5, -3, 4}, {-5, -5, -3, 6}, 
 
>       {-5, -5, -1, 2}, {-5, -5, -1, 4}, {-5, -5, -1, 6}, {-5, -5, 1, 0}, 
 
>       {-5, -5, 1, 2}, {-5, -5, 1, 4}, {-5, -5, 1, 6}, {-5, -5, 3, -2}, 
 
>       {-5, -5, 3, 0}, {-5, -5, 5, -6}, {-5, -5, 5, -4}, {-5, -5, 5, -2}, 
 
>       {-5, -5, 5, 0}, {-5, -3, -5, 4}, {-5, -3, -5, 6}, {-5, -3, -3, 4}, 
 
>       {-5, -3, -3, 6}, {-5, -3, -1, 2}, {-5, -3, -1, 4}, {-5, -3, -1, 6}, 
 
>       {-5, -3, 1, 0}, {-5, -3, 1, 2}, {-5, -3, 1, 4}, {-5, -3, 1, 6}, 
 
>       {-5, -3, 3, -6}, {-5, -3, 3, -4}, {-5, -3, 3, -2}, {-5, -3, 3, 0}, 
 
>       {-5, -3, 5, -6}, {-5, -3, 5, -4}, {-5, -3, 5, -2}, {-5, -3, 5, 0}, 
 
>       {-5, -1, -5, 2}, {-5, -1, -5, 4}, {-5, -1, -5, 6}, {-5, -1, -3, 2}, 
 
>       {-5, -1, -3, 4}, {-5, -1, -3, 6}, {-5, -1, -1, 2}, {-5, -1, -1, 4}, 
 
>       {-5, -1, -1, 6}, {-5, -1, 1, -6}, {-5, -1, 1, -4}, {-5, -1, 1, -2}, 
 
>       {-5, -1, 1, 0}, {-5, -1, 1, 2}, {-5, -1, 1, 4}, {-5, -1, 3, -6}, 
 
>       {-5, -1, 3, -4}, {-5, -1, 3, -2}, {-5, -1, 3, 0}, {-5, -1, 5, -6}, 
 
>       {-5, -1, 5, -4}, {-5, -1, 5, -2}, {-5, -1, 5, 0}, {-5, 1, -5, 0}, 
 
>       {-5, 1, -5, 2}, {-5, 1, -5, 4}, {-5, 1, -5, 6}, {-5, 1, -3, 0}, 
 
>       {-5, 1, -3, 2}, {-5, 1, -3, 4}, {-5, 1, -3, 6}, {-5, 1, -1, -6}, 
 
>       {-5, 1, -1, -4}, {-5, 1, -1, -2}, {-5, 1, -1, 0}, {-5, 1, -1, 2}, 
 
>       {-5, 1, -1, 4}, {-5, 1, 1, -6}, {-5, 1, 1, -4}, {-5, 1, 1, -2}, 
 
>       {-5, 1, 3, -6}, {-5, 1, 3, -4}, {-5, 1, 3, -2}, {-5, 1, 5, -6}, 
 
>       {-5, 1, 5, -4}, {-5, 1, 5, -2}, {-5, 3, -5, -2}, {-5, 3, -5, 0}, 
 
>       {-5, 3, -3, -6}, {-5, 3, -3, -4}, {-5, 3, -3, -2}, {-5, 3, -3, 0}, 
 
>       {-5, 3, -1, -6}, {-5, 3, -1, -4}, {-5, 3, -1, -2}, {-5, 3, -1, 0}, 
 
>       {-5, 3, 1, -6}, {-5, 3, 1, -4}, {-5, 3, 1, -2}, {-5, 5, -5, -6}, 
 
>       {-5, 5, -5, -4}, {-5, 5, -5, -2}, {-5, 5, -5, 0}, {-5, 5, -3, -6}, 
 
>       {-5, 5, -3, -4}, {-5, 5, -3, -2}, {-5, 5, -3, 0}, {-5, 5, -1, -6}, 
 
>       {-5, 5, -1, -4}, {-5, 5, -1, -2}, {-5, 5, -1, 0}, {-5, 5, 1, -6}, 
 
>       {-5, 5, 1, -4}, {-5, 5, 1, -2}, {-3, -5, -5, 4}, {-3, -5, -5, 6}, 
 
>       {-3, -5, -3, 4}, {-3, -5, -3, 6}, {-3, -5, -1, 2}, {-3, -5, -1, 4}, 
 
>       {-3, -5, -1, 6}, {-3, -5, 1, 0}, {-3, -5, 1, 2}, {-3, -5, 1, 4}, 
 
>       {-3, -5, 1, 6}, {-3, -5, 3, -6}, {-3, -5, 3, -4}, {-3, -5, 3, -2}, 
 
>       {-3, -5, 3, 0}, {-3, -5, 5, -6}, {-3, -5, 5, -4}, {-3, -5, 5, -2}, 
 
>       {-3, -5, 5, 0}, {-3, -3, -5, 4}, {-3, -3, -5, 6}, {-3, -3, -3, 4}, 
 
>       {-3, -3, -3, 6}, {-3, -3, -1, 2}, {-3, -3, -1, 4}, {-3, -3, -1, 6}, 
 
>       {-3, -3, 1, 0}, {-3, -3, 1, 2}, {-3, -3, 1, 4}, {-3, -3, 1, 6}, 
 
>       {-3, -3, 3, -6}, {-3, -3, 3, -4}, {-3, -3, 3, -2}, {-3, -3, 3, 0}, 
 
>       {-3, -3, 5, -6}, {-3, -3, 5, -4}, {-3, -3, 5, -2}, {-3, -3, 5, 0}, 
 
>       {-3, -1, -5, 2}, {-3, -1, -5, 4}, {-3, -1, -5, 6}, {-3, -1, -3, 2}, 
 
>       {-3, -1, -3, 4}, {-3, -1, -3, 6}, {-3, -1, -1, 2}, {-3, -1, -1, 4}, 
 
>       {-3, -1, -1, 6}, {-3, -1, 1, -6}, {-3, -1, 1, -4}, {-3, -1, 1, -2}, 
 
>       {-3, -1, 1, 0}, {-3, -1, 1, 2}, {-3, -1, 3, -6}, {-3, -1, 3, -4}, 
 
>       {-3, -1, 3, -2}, {-3, -1, 3, 0}, {-3, -1, 5, -6}, {-3, -1, 5, -4}, 
 
>       {-3, -1, 5, -2}, {-3, -1, 5, 0}, {-3, 1, -5, 0}, {-3, 1, -5, 2}, 
 
>       {-3, 1, -5, 4}, {-3, 1, -5, 6}, {-3, 1, -3, 0}, {-3, 1, -3, 2}, 
 
>       {-3, 1, -3, 4}, {-3, 1, -3, 6}, {-3, 1, -1, -6}, {-3, 1, -1, -4}, 
 
>       {-3, 1, -1, -2}, {-3, 1, -1, 0}, {-3, 1, -1, 2}, {-3, 1, 1, -6}, 
 
>       {-3, 1, 1, -4}, {-3, 1, 1, -2}, {-3, 1, 3, -6}, {-3, 1, 3, -4}, 
 
>       {-3, 1, 3, -2}, {-3, 1, 5, -6}, {-3, 1, 5, -4}, {-3, 1, 5, -2}, 
 
>       {-3, 3, -5, -6}, {-3, 3, -5, -4}, {-3, 3, -5, -2}, {-3, 3, -5, 0}, 
 
>       {-3, 3, -3, -6}, {-3, 3, -3, -4}, {-3, 3, -3, -2}, {-3, 3, -3, 0}, 
 
>       {-3, 3, -1, -6}, {-3, 3, -1, -4}, {-3, 3, -1, -2}, {-3, 3, -1, 0}, 
 
>       {-3, 3, 1, -6}, {-3, 3, 1, -4}, {-3, 3, 1, -2}, {-3, 5, -5, -6}, 
 
>       {-3, 5, -5, -4}, {-3, 5, -5, -2}, {-3, 5, -5, 0}, {-3, 5, -3, -6}, 
 
>       {-3, 5, -3, -4}, {-3, 5, -3, -2}, {-3, 5, -3, 0}, {-3, 5, -1, -6}, 
 
>       {-3, 5, -1, -4}, {-3, 5, -1, -2}, {-3, 5, -1, 0}, {-3, 5, 1, -6}, 
 
>       {-3, 5, 1, -4}, {-3, 5, 1, -2}, {-1, -5, -5, 2}, {-1, -5, -5, 4}, 
 
>       {-1, -5, -5, 6}, {-1, -5, -3, 2}, {-1, -5, -3, 4}, {-1, -5, -3, 6}, 
 
>       {-1, -5, -1, 2}, {-1, -5, -1, 4}, {-1, -5, -1, 6}, {-1, -5, 1, -6}, 
 
>       {-1, -5, 1, -4}, {-1, -5, 1, -2}, {-1, -5, 1, 0}, {-1, -5, 1, 2}, 
 
>       {-1, -5, 1, 4}, {-1, -5, 3, -6}, {-1, -5, 3, -4}, {-1, -5, 3, -2}, 
 
>       {-1, -5, 3, 0}, {-1, -5, 5, -6}, {-1, -5, 5, -4}, {-1, -5, 5, -2}, 
 
>       {-1, -5, 5, 0}, {-1, -3, -5, 2}, {-1, -3, -5, 4}, {-1, -3, -5, 6}, 
 
>       {-1, -3, -3, 2}, {-1, -3, -3, 4}, {-1, -3, -3, 6}, {-1, -3, -1, 2}, 
 
>       {-1, -3, -1, 4}, {-1, -3, -1, 6}, {-1, -3, 1, -6}, {-1, -3, 1, -4}, 
 
>       {-1, -3, 1, -2}, {-1, -3, 1, 0}, {-1, -3, 1, 2}, {-1, -3, 3, -6}, 
 
>       {-1, -3, 3, -4}, {-1, -3, 3, -2}, {-1, -3, 3, 0}, {-1, -3, 5, -6}, 
 
>       {-1, -3, 5, -4}, {-1, -3, 5, -2}, {-1, -3, 5, 0}, {-1, -1, -5, 2}, 
 
>       {-1, -1, -5, 4}, {-1, -1, -5, 6}, {-1, -1, -3, 2}, {-1, -1, -3, 4}, 
 
>       {-1, -1, -3, 6}, {-1, -1, -1, 2}, {-1, -1, -1, 4}, {-1, -1, -1, 6}, 
 
>       {-1, -1, 1, -6}, {-1, -1, 1, -4}, {-1, -1, 1, -2}, {-1, -1, 1, 0}, 
 
>       {-1, -1, 3, -6}, {-1, -1, 3, -4}, {-1, -1, 3, -2}, {-1, -1, 3, 0}, 
 
>       {-1, -1, 5, -6}, {-1, -1, 5, -4}, {-1, -1, 5, -2}, {-1, -1, 5, 0}, 
 
>       {-1, 1, -5, -6}, {-1, 1, -5, -4}, {-1, 1, -5, -2}, {-1, 1, -5, 0}, 
 
>       {-1, 1, -5, 2}, {-1, 1, -5, 4}, {-1, 1, -3, -6}, {-1, 1, -3, -4}, 
 
>       {-1, 1, -3, -2}, {-1, 1, -3, 0}, {-1, 1, -3, 2}, {-1, 1, -1, -6}, 
 
>       {-1, 1, -1, -4}, {-1, 1, -1, -2}, {-1, 1, -1, 0}, {-1, 1, 1, -6}, 
 
>       {-1, 1, 1, -4}, {-1, 1, 1, -2}, {-1, 1, 3, -6}, {-1, 1, 3, -4}, 
 
>       {-1, 1, 5, -6}, {-1, 3, -5, -6}, {-1, 3, -5, -4}, {-1, 3, -5, -2}, 
 
>       {-1, 3, -5, 0}, {-1, 3, -3, -6}, {-1, 3, -3, -4}, {-1, 3, -3, -2}, 
 
>       {-1, 3, -3, 0}, {-1, 3, -1, -6}, {-1, 3, -1, -4}, {-1, 3, -1, -2}, 
 
>       {-1, 3, -1, 0}, {-1, 3, 1, -6}, {-1, 3, 1, -4}, {-1, 5, -5, -6}, 
 
>       {-1, 5, -5, -4}, {-1, 5, -5, -2}, {-1, 5, -5, 0}, {-1, 5, -3, -6}, 
 
>       {-1, 5, -3, -4}, {-1, 5, -3, -2}, {-1, 5, -3, 0}, {-1, 5, -1, -6}, 
 
>       {-1, 5, -1, -4}, {-1, 5, -1, -2}, {-1, 5, -1, 0}, {-1, 5, 1, -6}, 
 
>       {1, -5, -5, 0}, {1, -5, -5, 2}, {1, -5, -5, 4}, {1, -5, -5, 6}, 
 
>       {1, -5, -3, 0}, {1, -5, -3, 2}, {1, -5, -3, 4}, {1, -5, -3, 6}, 
 
>       {1, -5, -1, -6}, {1, -5, -1, -4}, {1, -5, -1, -2}, {1, -5, -1, 0}, 
 
>       {1, -5, -1, 2}, {1, -5, -1, 4}, {1, -5, 1, -6}, {1, -5, 1, -4}, 
 
>       {1, -5, 1, -2}, {1, -5, 3, -6}, {1, -5, 3, -4}, {1, -5, 3, -2}, 
 
>       {1, -5, 5, -6}, {1, -5, 5, -4}, {1, -5, 5, -2}, {1, -3, -5, 0}, 
 
>       {1, -3, -5, 2}, {1, -3, -5, 4}, {1, -3, -5, 6}, {1, -3, -3, 0}, 
 
>       {1, -3, -3, 2}, {1, -3, -3, 4}, {1, -3, -3, 6}, {1, -3, -1, -6}, 
 
>       {1, -3, -1, -4}, {1, -3, -1, -2}, {1, -3, -1, 0}, {1, -3, -1, 2}, 
 
>       {1, -3, 1, -6}, {1, -3, 1, -4}, {1, -3, 1, -2}, {1, -3, 3, -6}, 
 
>       {1, -3, 3, -4}, {1, -3, 3, -2}, {1, -3, 5, -6}, {1, -3, 5, -4}, 
 
>       {1, -3, 5, -2}, {1, -1, -5, -6}, {1, -1, -5, -4}, {1, -1, -5, -2}, 
 
>       {1, -1, -5, 0}, {1, -1, -5, 2}, {1, -1, -5, 4}, {1, -1, -3, -6}, 
 
>       {1, -1, -3, -4}, {1, -1, -3, -2}, {1, -1, -3, 0}, {1, -1, -3, 2}, 
 
>       {1, -1, -1, -6}, {1, -1, -1, -4}, {1, -1, -1, -2}, {1, -1, -1, 0}, 
 
>       {1, -1, 1, -6}, {1, -1, 1, -4}, {1, -1, 1, -2}, {1, -1, 3, -6}, 
 
>       {1, -1, 3, -4}, {1, -1, 5, -6}, {1, 1, -5, -6}, {1, 1, -5, -4}, 
 
>       {1, 1, -5, -2}, {1, 1, -3, -6}, {1, 1, -3, -4}, {1, 1, -3, -2}, 
 
>       {1, 1, -1, -6}, {1, 1, -1, -4}, {1, 1, -1, -2}, {1, 3, -5, -6}, 
 
>       {1, 3, -5, -4}, {1, 3, -5, -2}, {1, 3, -3, -6}, {1, 3, -3, -4}, 
 
>       {1, 3, -3, -2}, {1, 3, -1, -6}, {1, 3, -1, -4}, {1, 5, -5, -6}, 
 
>       {1, 5, -5, -4}, {1, 5, -5, -2}, {1, 5, -3, -6}, {1, 5, -3, -4}, 
 
>       {1, 5, -3, -2}, {1, 5, -1, -6}, {3, -5, -5, -2}, {3, -5, -5, 0}, 
 
>       {3, -5, -3, -6}, {3, -5, -3, -4}, {3, -5, -3, -2}, {3, -5, -3, 0}, 
 
>       {3, -5, -1, -6}, {3, -5, -1, -4}, {3, -5, -1, -2}, {3, -5, -1, 0}, 
 
>       {3, -5, 1, -6}, {3, -5, 1, -4}, {3, -5, 1, -2}, {3, -3, -5, -6}, 
 
>       {3, -3, -5, -4}, {3, -3, -5, -2}, {3, -3, -5, 0}, {3, -3, -3, -6}, 
 
>       {3, -3, -3, -4}, {3, -3, -3, -2}, {3, -3, -3, 0}, {3, -3, -1, -6}, 
 
>       {3, -3, -1, -4}, {3, -3, -1, -2}, {3, -3, -1, 0}, {3, -3, 1, -6}, 
 
>       {3, -3, 1, -4}, {3, -3, 1, -2}, {3, -1, -5, -6}, {3, -1, -5, -4}, 
 
>       {3, -1, -5, -2}, {3, -1, -5, 0}, {3, -1, -3, -6}, {3, -1, -3, -4}, 
 
>       {3, -1, -3, -2}, {3, -1, -3, 0}, {3, -1, -1, -6}, {3, -1, -1, -4}, 
 
>       {3, -1, -1, -2}, {3, -1, -1, 0}, {3, -1, 1, -6}, {3, -1, 1, -4}, 
 
>       {3, 1, -5, -6}, {3, 1, -5, -4}, {3, 1, -5, -2}, {3, 1, -3, -6}, 
 
>       {3, 1, -3, -4}, {3, 1, -3, -2}, {3, 1, -1, -6}, {3, 1, -1, -4}, 
 
>       {5, -5, -5, -6}, {5, -5, -5, -4}, {5, -5, -5, -2}, {5, -5, -5, 0}, 
 
>       {5, -5, -3, -6}, {5, -5, -3, -4}, {5, -5, -3, -2}, {5, -5, -3, 0}, 
 
>       {5, -5, -1, -6}, {5, -5, -1, -4}, {5, -5, -1, -2}, {5, -5, -1, 0}, 
 
>       {5, -5, 1, -6}, {5, -5, 1, -4}, {5, -5, 1, -2}, {5, -3, -5, -6}, 
 
>       {5, -3, -5, -4}, {5, -3, -5, -2}, {5, -3, -5, 0}, {5, -3, -3, -6}, 
 
>       {5, -3, -3, -4}, {5, -3, -3, -2}, {5, -3, -3, 0}, {5, -3, -1, -6}, 
 
>       {5, -3, -1, -4}, {5, -3, -1, -2}, {5, -3, -1, 0}, {5, -3, 1, -6}, 
 
>       {5, -3, 1, -4}, {5, -3, 1, -2}, {5, -1, -5, -6}, {5, -1, -5, -4}, 
 
>       {5, -1, -5, -2}, {5, -1, -5, 0}, {5, -1, -3, -6}, {5, -1, -3, -4}, 
 
>       {5, -1, -3, -2}, {5, -1, -3, 0}, {5, -1, -1, -6}, {5, -1, -1, -4}, 
 
>       {5, -1, -1, -2}, {5, -1, -1, 0}, {5, -1, 1, -6}, {5, 1, -5, -6}, 
 
>       {5, 1, -5, -4}, {5, 1, -5, -2}, {5, 1, -3, -6}, {5, 1, -3, -4}, 
 
>       {5, 1, -3, -2}, {5, 1, -1, -6}}, 
 
>      {{-5, -5, -5, -6}, {-5, -5, -5, -4}, {-5, -5, -5, -2}, 
 
>       {-5, -5, -5, 0}, {-5, -5, -3, -6}, {-5, -5, -3, -4}, 
 
>       {-5, -5, -3, -2}, {-5, -5, -3, 0}, {-5, -5, -1, -6}, 
 
>       {-5, -5, -1, -4}, {-5, -5, -1, -2}, {-5, -5, -1, 0}, 
 
>       {-5, -3, -5, -6}, {-5, -3, -5, -4}, {-5, -3, -5, -2}, 
 
>       {-5, -3, -5, 0}, {-5, -3, -3, -6}, {-5, -3, -3, -4}, 
 
>       {-5, -3, -3, -2}, {-5, -3, -3, 0}, {-5, -3, -1, -6}, 
 
>       {-5, -3, -1, -4}, {-5, -3, -1, -2}, {-5, -3, -1, 0}, 
 
>       {-5, -1, -5, -6}, {-5, -1, -5, -4}, {-5, -1, -5, -2}, 
 
>       {-5, -1, -5, 0}, {-5, -1, -3, -6}, {-5, -1, -3, -4}, 
 
>       {-5, -1, -3, -2}, {-5, -1, -3, 0}, {-5, -1, -1, -6}, 
 
>       {-5, -1, -1, -4}, {-5, -1, -1, -2}, {-5, -1, -1, 0}, 
 
>       {-3, -5, -5, -6}, {-3, -5, -5, -4}, {-3, -5, -5, -2}, 
 
>       {-3, -5, -5, 0}, {-3, -5, -3, -6}, {-3, -5, -3, -4}, 
 
>       {-3, -5, -3, -2}, {-3, -5, -3, 0}, {-3, -5, -1, -6}, 
 
>       {-3, -5, -1, -4}, {-3, -5, -1, -2}, {-3, -5, -1, 0}, 
 
>       {-3, -3, -5, -6}, {-3, -3, -5, -4}, {-3, -3, -5, -2}, 
 
>       {-3, -3, -5, 0}, {-3, -3, -3, -6}, {-3, -3, -3, -4}, 
 
>       {-3, -3, -3, -2}, {-3, -3, -3, 0}, {-3, -3, -1, -6}, 
 
>       {-3, -3, -1, -4}, {-3, -3, -1, -2}, {-3, -3, -1, 0}, 
 
>       {-3, -1, -5, -6}, {-3, -1, -5, -4}, {-3, -1, -5, -2}, 
 
>       {-3, -1, -5, 0}, {-3, -1, -3, -6}, {-3, -1, -3, -4}, 
 
>       {-3, -1, -3, -2}, {-3, -1, -3, 0}, {-3, -1, -1, -6}, 
 
>       {-3, -1, -1, -4}, {-3, -1, -1, -2}, {-3, -1, -1, 0}, 
 
>       {-1, -5, -5, -6}, {-1, -5, -5, -4}, {-1, -5, -5, -2}, 
 
>       {-1, -5, -5, 0}, {-1, -5, -3, -6}, {-1, -5, -3, -4}, 
 
>       {-1, -5, -3, -2}, {-1, -5, -3, 0}, {-1, -5, -1, -6}, 
 
>       {-1, -5, -1, -4}, {-1, -5, -1, -2}, {-1, -5, -1, 0}, 
 
>       {-1, -3, -5, -6}, {-1, -3, -5, -4}, {-1, -3, -5, -2}, 
 
>       {-1, -3, -5, 0}, {-1, -3, -3, -6}, {-1, -3, -3, -4}, 
 
>       {-1, -3, -3, -2}, {-1, -3, -3, 0}, {-1, -3, -1, -6}, 
 
>       {-1, -3, -1, -4}, {-1, -3, -1, -2}, {-1, -3, -1, 0}, 
 
>       {-1, -1, -5, -6}, {-1, -1, -5, -4}, {-1, -1, -5, -2}, 
 
>       {-1, -1, -5, 0}, {-1, -1, -3, -6}, {-1, -1, -3, -4}, 
 
>       {-1, -1, -3, -2}, {-1, -1, -3, 0}, {-1, -1, -1, -6}, 
 
>       {-1, -1, -1, -4}, {-1, -1, -1, -2}, {-1, -1, -1, 0}}}, 
 
>    pExcept -> 
 
>     {{1, 1, 1, 0}, {1, 1, 3, 0}, {1, 1, 5, 0}, {1, 3, 1, 0}, {1, 3, 3, 0}, 
 
>      {1, 3, 5, 0}, {1, 5, 1, 0}, {1, 5, 3, 0}, {1, 5, 5, 0}, {3, 1, 1, 0}, 
 
>      {3, 1, 3, 0}, {3, 1, 5, 0}, {3, 3, 1, 0}, {3, 3, 3, -2}, {3, 3, 3, 0}, 
 
>      {3, 3, 5, -2}, {3, 3, 5, 0}, {3, 5, 1, 0}, {3, 5, 3, -2}, 
 
>      {3, 5, 3, 0}, {3, 5, 5, -2}, {3, 5, 5, 0}, {5, 1, 1, 0}, {5, 1, 3, 0}, 
 
>      {5, 1, 5, 0}, {5, 3, 1, 0}, {5, 3, 3, -2}, {5, 3, 3, 0}, 
 
>      {5, 3, 5, -2}, {5, 3, 5, 0}, {5, 5, 1, 0}, {5, 5, 3, -2}, 
 
>      {5, 5, 3, 0}, {5, 5, 5, -4}, {5, 5, 5, -2}, {5, 5, 5, 0}}, 
 
>    mExcept -> 
 
>     {{-5, -5, -5, 0}, {-5, -5, -5, 2}, {-5, -5, -5, 4}, {-5, -5, -3, 0}, 
 
>      {-5, -5, -3, 2}, {-5, -5, -1, 0}, {-5, -3, -5, 0}, {-5, -3, -5, 2}, 
 
>      {-5, -3, -3, 0}, {-5, -3, -3, 2}, {-5, -3, -1, 0}, {-5, -1, -5, 0}, 
 
>      {-5, -1, -3, 0}, {-5, -1, -1, 0}, {-3, -5, -5, 0}, {-3, -5, -5, 2}, 
 
>      {-3, -5, -3, 0}, {-3, -5, -3, 2}, {-3, -5, -1, 0}, {-3, -3, -5, 0}, 
 
>      {-3, -3, -5, 2}, {-3, -3, -3, 0}, {-3, -3, -3, 2}, {-3, -3, -1, 0}, 
 
>      {-3, -1, -5, 0}, {-3, -1, -3, 0}, {-3, -1, -1, 0}, {-1, -5, -5, 0}, 
 
>      {-1, -5, -3, 0}, {-1, -5, -1, 0}, {-1, -3, -5, 0}, {-1, -3, -3, 0}, 
 
>      {-1, -3, -1, 0}, {-1, -1, -5, 0}, {-1, -1, -3, 0}, {-1, -1, -1, 0}}, 
 
>    pExcept2 -> 
 
>     {{-3, 5, 5, 4}, {-3, 5, 5, 6}, {-1, 3, 3, 2}, {-1, 3, 3, 4}, 
 
>      {-1, 3, 3, 6}, {-1, 3, 5, 2}, {-1, 3, 5, 4}, {-1, 3, 5, 6}, 
 
>      {-1, 5, 3, 2}, {-1, 5, 3, 4}, {-1, 5, 3, 6}, {-1, 5, 5, 2}, 
 
>      {-1, 5, 5, 4}, {-1, 5, 5, 6}, {1, 1, 1, 0}, {1, 1, 1, 2}, 
 
>      {1, 1, 1, 4}, {1, 1, 1, 6}, {1, 1, 3, 0}, {1, 1, 3, 2}, {1, 1, 3, 4}, 
 
>      {1, 1, 3, 6}, {1, 1, 5, 0}, {1, 1, 5, 2}, {1, 1, 5, 4}, {1, 1, 5, 6}, 
 
>      {1, 3, 1, 0}, {1, 3, 1, 2}, {1, 3, 1, 4}, {1, 3, 1, 6}, {1, 3, 3, 0}, 
 
>      {1, 3, 3, 2}, {1, 3, 3, 4}, {1, 3, 3, 6}, {1, 3, 5, 0}, {1, 3, 5, 2}, 
 
>      {1, 3, 5, 4}, {1, 3, 5, 6}, {1, 5, 1, 0}, {1, 5, 1, 2}, {1, 5, 1, 4}, 
 
>      {1, 5, 1, 6}, {1, 5, 3, 0}, {1, 5, 3, 2}, {1, 5, 3, 4}, {1, 5, 3, 6}, 
 
>      {1, 5, 5, 0}, {1, 5, 5, 2}, {1, 5, 5, 4}, {1, 5, 5, 6}, {3, -1, 3, 2}, 
 
>      {3, -1, 3, 4}, {3, -1, 3, 6}, {3, -1, 5, 2}, {3, -1, 5, 4}, 
 
>      {3, -1, 5, 6}, {3, 1, 1, 0}, {3, 1, 1, 2}, {3, 1, 1, 4}, {3, 1, 1, 6}, 
 
>      {3, 1, 3, 0}, {3, 1, 3, 2}, {3, 1, 3, 4}, {3, 1, 3, 6}, {3, 1, 5, 0}, 
 
>      {3, 1, 5, 2}, {3, 1, 5, 4}, {3, 1, 5, 6}, {3, 3, -1, 2}, 
 
>      {3, 3, -1, 4}, {3, 3, -1, 6}, {3, 3, 1, 0}, {3, 3, 1, 2}, 
 
>      {3, 3, 1, 4}, {3, 3, 1, 6}, {3, 5, -1, 2}, {3, 5, -1, 4}, 
 
>      {3, 5, -1, 6}, {3, 5, 1, 0}, {3, 5, 1, 2}, {3, 5, 1, 4}, {3, 5, 1, 6}, 
 
>      {5, -3, 5, 4}, {5, -3, 5, 6}, {5, -1, 3, 2}, {5, -1, 3, 4}, 
 
>      {5, -1, 3, 6}, {5, -1, 5, 2}, {5, -1, 5, 4}, {5, -1, 5, 6}, 
 
>      {5, 1, 1, 0}, {5, 1, 1, 2}, {5, 1, 1, 4}, {5, 1, 1, 6}, {5, 1, 3, 0}, 
 
>      {5, 1, 3, 2}, {5, 1, 3, 4}, {5, 1, 3, 6}, {5, 1, 5, 0}, {5, 1, 5, 2}, 
 
>      {5, 1, 5, 4}, {5, 1, 5, 6}, {5, 3, -1, 2}, {5, 3, -1, 4}, 
 
>      {5, 3, -1, 6}, {5, 3, 1, 0}, {5, 3, 1, 2}, {5, 3, 1, 4}, {5, 3, 1, 6}, 
 
>      {5, 5, -3, 4}, {5, 5, -3, 6}, {5, 5, -1, 2}, {5, 5, -1, 4}, 
 
>      {5, 5, -1, 6}, {5, 5, 1, 0}, {5, 5, 1, 2}, {5, 5, 1, 4}, {5, 5, 1, 6}}\
 
>     , mExcept2 -> 
 
>     {{-5, -5, -1, -6}, {-5, -5, -1, -4}, {-5, -5, -1, -2}, {-5, -5, -1, 0}, 
 
>      {-5, -5, 1, -6}, {-5, -5, 1, -4}, {-5, -5, 1, -2}, {-5, -5, 3, -6}, 
 
>      {-5, -5, 3, -4}, {-5, -3, -1, -6}, {-5, -3, -1, -4}, {-5, -3, -1, -2}, 
 
>      {-5, -3, -1, 0}, {-5, -3, 1, -6}, {-5, -3, 1, -4}, {-5, -3, 1, -2}, 
 
>      {-5, -1, -5, -6}, {-5, -1, -5, -4}, {-5, -1, -5, -2}, {-5, -1, -5, 0}, 
 
>      {-5, -1, -3, -6}, {-5, -1, -3, -4}, {-5, -1, -3, -2}, {-5, -1, -3, 0}, 
 
>      {-5, -1, -1, -6}, {-5, -1, -1, -4}, {-5, -1, -1, -2}, {-5, -1, -1, 0}, 
 
>      {-5, 1, -5, -6}, {-5, 1, -5, -4}, {-5, 1, -5, -2}, {-5, 1, -3, -6}, 
 
>      {-5, 1, -3, -4}, {-5, 1, -3, -2}, {-5, 3, -5, -6}, {-5, 3, -5, -4}, 
 
>      {-3, -5, -1, -6}, {-3, -5, -1, -4}, {-3, -5, -1, -2}, {-3, -5, -1, 0}, 
 
>      {-3, -5, 1, -6}, {-3, -5, 1, -4}, {-3, -5, 1, -2}, {-3, -3, -1, -6}, 
 
>      {-3, -3, -1, -4}, {-3, -3, -1, -2}, {-3, -3, -1, 0}, {-3, -3, 1, -6}, 
 
>      {-3, -3, 1, -4}, {-3, -3, 1, -2}, {-3, -1, -5, -6}, {-3, -1, -5, -4}, 
 
>      {-3, -1, -5, -2}, {-3, -1, -5, 0}, {-3, -1, -3, -6}, {-3, -1, -3, -4}, 
 
>      {-3, -1, -3, -2}, {-3, -1, -3, 0}, {-3, -1, -1, -6}, {-3, -1, -1, -4}, 
 
>      {-3, -1, -1, -2}, {-3, -1, -1, 0}, {-3, 1, -5, -6}, {-3, 1, -5, -4}, 
 
>      {-3, 1, -5, -2}, {-3, 1, -3, -6}, {-3, 1, -3, -4}, {-3, 1, -3, -2}, 
 
>      {-1, -5, -5, -6}, {-1, -5, -5, -4}, {-1, -5, -5, -2}, {-1, -5, -5, 0}, 
 
>      {-1, -5, -3, -6}, {-1, -5, -3, -4}, {-1, -5, -3, -2}, {-1, -5, -3, 0}, 
 
>      {-1, -5, -1, -6}, {-1, -5, -1, -4}, {-1, -5, -1, -2}, {-1, -5, -1, 0}, 
 
>      {-1, -3, -5, -6}, {-1, -3, -5, -4}, {-1, -3, -5, -2}, {-1, -3, -5, 0}, 
 
>      {-1, -3, -3, -6}, {-1, -3, -3, -4}, {-1, -3, -3, -2}, {-1, -3, -3, 0}, 
 
>      {-1, -3, -1, -6}, {-1, -3, -1, -4}, {-1, -3, -1, -2}, {-1, -3, -1, 0}, 
 
>      {-1, -1, -5, -6}, {-1, -1, -5, -4}, {-1, -1, -5, -2}, {-1, -1, -5, 0}, 
 
>      {-1, -1, -3, -6}, {-1, -1, -3, -4}, {-1, -1, -3, -2}, {-1, -1, -3, 0}, 
 
>      {-1, -1, -1, -6}, {-1, -1, -1, -4}, {-1, -1, -1, -2}, {-1, -1, -1, 0}, 
 
>      {1, -5, -5, -6}, {1, -5, -5, -4}, {1, -5, -5, -2}, {1, -5, -3, -6}, 
 
>      {1, -5, -3, -4}, {1, -5, -3, -2}, {1, -3, -5, -6}, {1, -3, -5, -4}, 
 
>      {1, -3, -5, -2}, {1, -3, -3, -6}, {1, -3, -3, -4}, {1, -3, -3, -2}, 
 
>      {3, -5, -5, -6}, {3, -5, -5, -4}}|>



Out[10]= <|fails -> 
 
>     {{-7, -7, 1, -8}, {-7, -7, 1, -6}, {-7, -7, 1, -4}, {-7, -7, 1, -2}, 
 
>      {-7, -7, 3, -8}, {-7, -7, 3, -6}, {-7, -7, 3, -4}, {-7, -7, 3, 2}, 
 
>      {-7, -7, 3, 4}, {-7, -7, 3, 6}, {-7, -7, 3, 8}, {-7, -7, 5, -8}, 
 
>      {-7, -7, 5, -6}, {-7, -7, 5, 2}, {-7, -7, 5, 4}, {-7, -7, 5, 6}, 
 
>      {-7, -7, 5, 8}, {-7, -7, 7, 2}, {-7, -7, 7, 4}, {-7, -7, 7, 6}, 
 
>      {-7, -7, 7, 8}, {-7, -5, 1, -8}, {-7, -5, 1, -6}, {-7, -5, 1, -4}, 
 
>      {-7, -5, 1, -2}, {-7, -5, 3, -8}, {-7, -5, 3, -6}, {-7, -5, 3, -4}, 
 
>      {-7, -5, 3, 2}, {-7, -5, 3, 4}, {-7, -5, 3, 6}, {-7, -5, 3, 8}, 
 
>      {-7, -5, 5, 2}, {-7, -5, 5, 4}, {-7, -5, 5, 6}, {-7, -5, 5, 8}, 
 
>      {-7, -5, 7, 2}, {-7, -5, 7, 4}, {-7, -5, 7, 6}, {-7, -5, 7, 8}, 
 
>      {-7, -3, 1, -8}, {-7, -3, 1, -6}, {-7, -3, 1, -4}, {-7, -3, 1, -2}, 
 
>      {-7, -3, 3, 2}, {-7, -3, 3, 4}, {-7, -3, 3, 6}, {-7, -3, 3, 8}, 
 
>      {-7, -3, 5, 2}, {-7, -3, 5, 4}, {-7, -3, 5, 6}, {-7, -3, 5, 8}, 
 
>      {-7, -3, 7, 2}, {-7, -3, 7, 4}, {-7, -3, 7, 6}, {-7, -3, 7, 8}, 
 
>      {-7, 1, -7, -8}, {-7, 1, -7, -6}, {-7, 1, -7, -4}, {-7, 1, -7, -2}, 
 
>      {-7, 1, -5, -8}, {-7, 1, -5, -6}, {-7, 1, -5, -4}, {-7, 1, -5, -2}, 
 
>      {-7, 1, -3, -8}, {-7, 1, -3, -6}, {-7, 1, -3, -4}, {-7, 1, -3, -2}, 
 
>      {-7, 3, -7, -8}, {-7, 3, -7, -6}, {-7, 3, -7, -4}, {-7, 3, -7, 2}, 
 
>      {-7, 3, -7, 4}, {-7, 3, -7, 6}, {-7, 3, -7, 8}, {-7, 3, -5, -8}, 
 
>      {-7, 3, -5, -6}, {-7, 3, -5, -4}, {-7, 3, -5, 2}, {-7, 3, -5, 4}, 
 
>      {-7, 3, -5, 6}, {-7, 3, -5, 8}, {-7, 3, -3, 2}, {-7, 3, -3, 4}, 
 
>      {-7, 3, -3, 6}, {-7, 3, -3, 8}, {-7, 3, 3, -8}, {-7, 3, 3, -6}, 
 
>      {-7, 3, 3, -4}, {-7, 3, 3, -2}, {-7, 3, 5, -8}, {-7, 3, 5, -6}, 
 
>      {-7, 3, 5, -4}, {-7, 3, 5, -2}, {-7, 3, 7, -8}, {-7, 3, 7, -6}, 
 
>      {-7, 3, 7, -4}, {-7, 3, 7, -2}, {-7, 5, -7, -8}, {-7, 5, -7, -6}, 
 
>      {-7, 5, -7, 2}, {-7, 5, -7, 4}, {-7, 5, -7, 6}, {-7, 5, -7, 8}, 
 
>      {-7, 5, -5, 2}, {-7, 5, -5, 4}, {-7, 5, -5, 6}, {-7, 5, -5, 8}, 
 
>      {-7, 5, -3, 2}, {-7, 5, -3, 4}, {-7, 5, -3, 6}, {-7, 5, -3, 8}, 
 
>      {-7, 5, 3, -8}, {-7, 5, 3, -6}, {-7, 5, 3, -4}, {-7, 5, 3, -2}, 
 
>      {-7, 5, 5, -8}, {-7, 5, 5, -6}, {-7, 5, 5, -4}, {-7, 5, 5, -2}, 
 
>      {-7, 5, 7, -8}, {-7, 5, 7, -6}, {-7, 5, 7, -4}, {-7, 5, 7, -2}, 
 
>      {-7, 7, -7, 2}, {-7, 7, -7, 4}, {-7, 7, -7, 6}, {-7, 7, -7, 8}, 
 
>      {-7, 7, -5, 2}, {-7, 7, -5, 4}, {-7, 7, -5, 6}, {-7, 7, -5, 8}, 
 
>      {-7, 7, -3, 2}, {-7, 7, -3, 4}, {-7, 7, -3, 6}, {-7, 7, -3, 8}, 
 
>      {-7, 7, 3, -8}, {-7, 7, 3, -6}, {-7, 7, 3, -4}, {-7, 7, 3, -2}, 
 
>      {-7, 7, 5, -8}, {-7, 7, 5, -6}, {-7, 7, 5, -4}, {-7, 7, 5, -2}, 
 
>      {-7, 7, 7, -8}, {-7, 7, 7, -6}, {-7, 7, 7, -4}, {-7, 7, 7, -2}, 
 
>      {-5, -7, 1, -8}, {-5, -7, 1, -6}, {-5, -7, 1, -4}, {-5, -7, 1, -2}, 
 
>      {-5, -7, 3, -8}, {-5, -7, 3, -6}, {-5, -7, 3, -4}, {-5, -7, 3, 2}, 
 
>      {-5, -7, 3, 4}, {-5, -7, 3, 6}, {-5, -7, 3, 8}, {-5, -7, 5, 2}, 
 
>      {-5, -7, 5, 4}, {-5, -7, 5, 6}, {-5, -7, 5, 8}, {-5, -7, 7, 2}, 
 
>      {-5, -7, 7, 4}, {-5, -7, 7, 6}, {-5, -7, 7, 8}, {-5, -5, 1, -8}, 
 
>      {-5, -5, 1, -6}, {-5, -5, 1, -4}, {-5, -5, 1, -2}, {-5, -5, 3, -8}, 
 
>      {-5, -5, 3, -6}, {-5, -5, 3, -4}, {-5, -5, 3, 2}, {-5, -5, 3, 4}, 
 
>      {-5, -5, 3, 6}, {-5, -5, 3, 8}, {-5, -5, 5, 2}, {-5, -5, 5, 4}, 
 
>      {-5, -5, 5, 6}, {-5, -5, 5, 8}, {-5, -5, 7, 2}, {-5, -5, 7, 4}, 
 
>      {-5, -5, 7, 6}, {-5, -5, 7, 8}, {-5, -3, 1, -8}, {-5, -3, 1, -6}, 
 
>      {-5, -3, 1, -4}, {-5, -3, 1, -2}, {-5, -3, 3, 2}, {-5, -3, 3, 4}, 
 
>      {-5, -3, 3, 6}, {-5, -3, 3, 8}, {-5, -3, 5, 2}, {-5, -3, 5, 4}, 
 
>      {-5, -3, 5, 6}, {-5, -3, 5, 8}, {-5, -3, 7, 2}, {-5, -3, 7, 4}, 
 
>      {-5, -3, 7, 6}, {-5, -3, 7, 8}, {-5, 1, -7, -8}, {-5, 1, -7, -6}, 
 
>      {-5, 1, -7, -4}, {-5, 1, -7, -2}, {-5, 1, -5, -8}, {-5, 1, -5, -6}, 
 
>      {-5, 1, -5, -4}, {-5, 1, -5, -2}, {-5, 1, -3, -8}, {-5, 1, -3, -6}, 
 
>      {-5, 1, -3, -4}, {-5, 1, -3, -2}, {-5, 3, -7, -8}, {-5, 3, -7, -6}, 
 
>      {-5, 3, -7, -4}, {-5, 3, -7, 2}, {-5, 3, -7, 4}, {-5, 3, -7, 6}, 
 
>      {-5, 3, -7, 8}, {-5, 3, -5, -8}, {-5, 3, -5, -6}, {-5, 3, -5, -4}, 
 
>      {-5, 3, -5, 2}, {-5, 3, -5, 4}, {-5, 3, -5, 6}, {-5, 3, -5, 8}, 
 
>      {-5, 3, -3, 2}, {-5, 3, -3, 4}, {-5, 3, -3, 6}, {-5, 3, -3, 8}, 
 
>      {-5, 3, 3, -8}, {-5, 3, 3, -6}, {-5, 3, 3, -4}, {-5, 3, 3, -2}, 
 
>      {-5, 3, 5, -8}, {-5, 3, 5, -6}, {-5, 3, 5, -4}, {-5, 3, 5, -2}, 
 
>      {-5, 3, 7, -8}, {-5, 3, 7, -6}, {-5, 3, 7, -4}, {-5, 3, 7, -2}, 
 
>      {-5, 5, -7, 2}, {-5, 5, -7, 4}, {-5, 5, -7, 6}, {-5, 5, -7, 8}, 
 
>      {-5, 5, -5, 2}, {-5, 5, -5, 4}, {-5, 5, -5, 6}, {-5, 5, -5, 8}, 
 
>      {-5, 5, -3, 2}, {-5, 5, -3, 4}, {-5, 5, -3, 6}, {-5, 5, -3, 8}, 
 
>      {-5, 5, 3, -8}, {-5, 5, 3, -6}, {-5, 5, 3, -4}, {-5, 5, 3, -2}, 
 
>      {-5, 5, 5, -8}, {-5, 5, 5, -6}, {-5, 5, 5, -4}, {-5, 5, 5, -2}, 
 
>      {-5, 5, 7, -8}, {-5, 5, 7, -6}, {-5, 5, 7, -4}, {-5, 5, 7, -2}, 
 
>      {-5, 7, -7, 2}, {-5, 7, -7, 4}, {-5, 7, -7, 6}, {-5, 7, -7, 8}, 
 
>      {-5, 7, -5, 2}, {-5, 7, -5, 4}, {-5, 7, -5, 6}, {-5, 7, -5, 8}, 
 
>      {-5, 7, -3, 2}, {-5, 7, -3, 4}, {-5, 7, -3, 6}, {-5, 7, -3, 8}, 
 
>      {-5, 7, 3, -8}, {-5, 7, 3, -6}, {-5, 7, 3, -4}, {-5, 7, 3, -2}, 
 
>      {-5, 7, 5, -8}, {-5, 7, 5, -6}, {-5, 7, 5, -4}, {-5, 7, 5, -2}, 
 
>      {-5, 7, 7, -8}, {-5, 7, 7, -6}, {-5, 7, 7, -4}, {-5, 7, 7, -2}, 
 
>      {-5, 7, 7, 6}, {-5, 7, 7, 8}, {-3, -7, 1, -8}, {-3, -7, 1, -6}, 
 
>      {-3, -7, 1, -4}, {-3, -7, 1, -2}, {-3, -7, 3, 2}, {-3, -7, 3, 4}, 
 
>      {-3, -7, 3, 6}, {-3, -7, 3, 8}, {-3, -7, 5, 2}, {-3, -7, 5, 4}, 
 
>      {-3, -7, 5, 6}, {-3, -7, 5, 8}, {-3, -7, 7, 2}, {-3, -7, 7, 4}, 
 
>      {-3, -7, 7, 6}, {-3, -7, 7, 8}, {-3, -5, 1, -8}, {-3, -5, 1, -6}, 
 
>      {-3, -5, 1, -4}, {-3, -5, 1, -2}, {-3, -5, 3, 2}, {-3, -5, 3, 4}, 
 
>      {-3, -5, 3, 6}, {-3, -5, 3, 8}, {-3, -5, 5, 2}, {-3, -5, 5, 4}, 
 
>      {-3, -5, 5, 6}, {-3, -5, 5, 8}, {-3, -5, 7, 2}, {-3, -5, 7, 4}, 
 
>      {-3, -5, 7, 6}, {-3, -5, 7, 8}, {-3, -3, 1, -8}, {-3, -3, 1, -6}, 
 
>      {-3, -3, 1, -4}, {-3, -3, 1, -2}, {-3, -3, 3, 2}, {-3, -3, 3, 4}, 
 
>      {-3, -3, 3, 6}, {-3, -3, 3, 8}, {-3, -3, 5, 2}, {-3, -3, 5, 4}, 
 
>      {-3, -3, 5, 6}, {-3, -3, 5, 8}, {-3, -3, 7, 2}, {-3, -3, 7, 4}, 
 
>      {-3, -3, 7, 6}, {-3, -3, 7, 8}, {-3, 1, -7, -8}, {-3, 1, -7, -6}, 
 
>      {-3, 1, -7, -4}, {-3, 1, -7, -2}, {-3, 1, -5, -8}, {-3, 1, -5, -6}, 
 
>      {-3, 1, -5, -4}, {-3, 1, -5, -2}, {-3, 1, -3, -8}, {-3, 1, -3, -6}, 
 
>      {-3, 1, -3, -4}, {-3, 1, -3, -2}, {-3, 3, -7, 2}, {-3, 3, -7, 4}, 
 
>      {-3, 3, -7, 6}, {-3, 3, -7, 8}, {-3, 3, -5, 2}, {-3, 3, -5, 4}, 
 
>      {-3, 3, -5, 6}, {-3, 3, -5, 8}, {-3, 3, -3, 2}, {-3, 3, -3, 4}, 
 
>      {-3, 3, -3, 6}, {-3, 3, -3, 8}, {-3, 3, 3, -8}, {-3, 3, 3, -6}, 
 
>      {-3, 3, 3, -4}, {-3, 3, 3, -2}, {-3, 3, 5, -8}, {-3, 3, 5, -6}, 
 
>      {-3, 3, 5, -4}, {-3, 3, 5, -2}, {-3, 3, 7, -8}, {-3, 3, 7, -6}, 
 
>      {-3, 3, 7, -4}, {-3, 3, 7, -2}, {-3, 5, -7, 2}, {-3, 5, -7, 4}, 
 
>      {-3, 5, -7, 6}, {-3, 5, -7, 8}, {-3, 5, -5, 2}, {-3, 5, -5, 4}, 
 
>      {-3, 5, -5, 6}, {-3, 5, -5, 8}, {-3, 5, -3, 2}, {-3, 5, -3, 4}, 
 
>      {-3, 5, -3, 6}, {-3, 5, -3, 8}, {-3, 5, 3, -8}, {-3, 5, 3, -6}, 
 
>      {-3, 5, 3, -4}, {-3, 5, 3, -2}, {-3, 5, 5, -8}, {-3, 5, 5, -6}, 
 
>      {-3, 5, 5, -4}, {-3, 5, 5, -2}, {-3, 5, 5, 4}, {-3, 5, 5, 6}, 
 
>      {-3, 5, 5, 8}, {-3, 5, 7, -8}, {-3, 5, 7, -6}, {-3, 5, 7, -4}, 
 
>      {-3, 5, 7, -2}, {-3, 5, 7, 4}, {-3, 5, 7, 6}, {-3, 5, 7, 8}, 
 
>      {-3, 7, -7, 2}, {-3, 7, -7, 4}, {-3, 7, -7, 6}, {-3, 7, -7, 8}, 
 
>      {-3, 7, -5, 2}, {-3, 7, -5, 4}, {-3, 7, -5, 6}, {-3, 7, -5, 8}, 
 
>      {-3, 7, -3, 2}, {-3, 7, -3, 4}, {-3, 7, -3, 6}, {-3, 7, -3, 8}, 
 
>      {-3, 7, 3, -8}, {-3, 7, 3, -6}, {-3, 7, 3, -4}, {-3, 7, 3, -2}, 
 
>      {-3, 7, 5, -8}, {-3, 7, 5, -6}, {-3, 7, 5, -4}, {-3, 7, 5, -2}, 
 
>      {-3, 7, 5, 4}, {-3, 7, 5, 6}, {-3, 7, 5, 8}, {-3, 7, 7, -8}, 
 
>      {-3, 7, 7, -6}, {-3, 7, 7, -4}, {-3, 7, 7, -2}, {-3, 7, 7, 4}, 
 
>      {-3, 7, 7, 6}, {-3, 7, 7, 8}, {-1, 3, 3, 2}, {-1, 3, 3, 4}, 
 
>      {-1, 3, 3, 6}, {-1, 3, 3, 8}, {-1, 3, 5, 2}, {-1, 3, 5, 4}, 
 
>      {-1, 3, 5, 6}, {-1, 3, 5, 8}, {-1, 3, 7, 2}, {-1, 3, 7, 4}, 
 
>      {-1, 3, 7, 6}, {-1, 3, 7, 8}, {-1, 5, 3, 2}, {-1, 5, 3, 4}, 
 
>      {-1, 5, 3, 6}, {-1, 5, 3, 8}, {-1, 5, 5, 2}, {-1, 5, 5, 4}, 
 
>      {-1, 5, 5, 6}, {-1, 5, 5, 8}, {-1, 5, 7, 2}, {-1, 5, 7, 4}, 
 
>      {-1, 5, 7, 6}, {-1, 5, 7, 8}, {-1, 7, 3, 2}, {-1, 7, 3, 4}, 
 
>      {-1, 7, 3, 6}, {-1, 7, 3, 8}, {-1, 7, 5, 2}, {-1, 7, 5, 4}, 
 
>      {-1, 7, 5, 6}, {-1, 7, 5, 8}, {-1, 7, 7, 2}, {-1, 7, 7, 4}, 
 
>      {-1, 7, 7, 6}, {-1, 7, 7, 8}, {1, -7, -7, -8}, {1, -7, -7, -6}, 
 
>      {1, -7, -7, -4}, {1, -7, -7, -2}, {1, -7, -5, -8}, {1, -7, -5, -6}, 
 
>      {1, -7, -5, -4}, {1, -7, -5, -2}, {1, -7, -3, -8}, {1, -7, -3, -6}, 
 
>      {1, -7, -3, -4}, {1, -7, -3, -2}, {1, -5, -7, -8}, {1, -5, -7, -6}, 
 
>      {1, -5, -7, -4}, {1, -5, -7, -2}, {1, -5, -5, -8}, {1, -5, -5, -6}, 
 
>      {1, -5, -5, -4}, {1, -5, -5, -2}, {1, -5, -3, -8}, {1, -5, -3, -6}, 
 
>      {1, -5, -3, -4}, {1, -5, -3, -2}, {1, -3, -7, -8}, {1, -3, -7, -6}, 
 
>      {1, -3, -7, -4}, {1, -3, -7, -2}, {1, -3, -5, -8}, {1, -3, -5, -6}, 
 
>      {1, -3, -5, -4}, {1, -3, -5, -2}, {1, -3, -3, -8}, {1, -3, -3, -6}, 
 
>      {1, -3, -3, -4}, {1, -3, -3, -2}, {3, -7, -7, -8}, {3, -7, -7, -6}, 
 
>      {3, -7, -7, -4}, {3, -7, -7, 2}, {3, -7, -7, 4}, {3, -7, -7, 6}, 
 
>      {3, -7, -7, 8}, {3, -7, -5, -8}, {3, -7, -5, -6}, {3, -7, -5, -4}, 
 
>      {3, -7, -5, 2}, {3, -7, -5, 4}, {3, -7, -5, 6}, {3, -7, -5, 8}, 
 
>      {3, -7, -3, 2}, {3, -7, -3, 4}, {3, -7, -3, 6}, {3, -7, -3, 8}, 
 
>      {3, -7, 3, -8}, {3, -7, 3, -6}, {3, -7, 3, -4}, {3, -7, 3, -2}, 
 
>      {3, -7, 5, -8}, {3, -7, 5, -6}, {3, -7, 5, -4}, {3, -7, 5, -2}, 
 
>      {3, -7, 7, -8}, {3, -7, 7, -6}, {3, -7, 7, -4}, {3, -7, 7, -2}, 
 
>      {3, -5, -7, -8}, {3, -5, -7, -6}, {3, -5, -7, -4}, {3, -5, -7, 2}, 
 
>      {3, -5, -7, 4}, {3, -5, -7, 6}, {3, -5, -7, 8}, {3, -5, -5, -8}, 
 
>      {3, -5, -5, -6}, {3, -5, -5, -4}, {3, -5, -5, 2}, {3, -5, -5, 4}, 
 
>      {3, -5, -5, 6}, {3, -5, -5, 8}, {3, -5, -3, 2}, {3, -5, -3, 4}, 
 
>      {3, -5, -3, 6}, {3, -5, -3, 8}, {3, -5, 3, -8}, {3, -5, 3, -6}, 
 
>      {3, -5, 3, -4}, {3, -5, 3, -2}, {3, -5, 5, -8}, {3, -5, 5, -6}, 
 
>      {3, -5, 5, -4}, {3, -5, 5, -2}, {3, -5, 7, -8}, {3, -5, 7, -6}, 
 
>      {3, -5, 7, -4}, {3, -5, 7, -2}, {3, -3, -7, 2}, {3, -3, -7, 4}, 
 
>      {3, -3, -7, 6}, {3, -3, -7, 8}, {3, -3, -5, 2}, {3, -3, -5, 4}, 
 
>      {3, -3, -5, 6}, {3, -3, -5, 8}, {3, -3, -3, 2}, {3, -3, -3, 4}, 
 
>      {3, -3, -3, 6}, {3, -3, -3, 8}, {3, -3, 3, -8}, {3, -3, 3, -6}, 
 
>      {3, -3, 3, -4}, {3, -3, 3, -2}, {3, -3, 5, -8}, {3, -3, 5, -6}, 
 
>      {3, -3, 5, -4}, {3, -3, 5, -2}, {3, -3, 7, -8}, {3, -3, 7, -6}, 
 
>      {3, -3, 7, -4}, {3, -3, 7, -2}, {3, -1, 3, 2}, {3, -1, 3, 4}, 
 
>      {3, -1, 3, 6}, {3, -1, 3, 8}, {3, -1, 5, 2}, {3, -1, 5, 4}, 
 
>      {3, -1, 5, 6}, {3, -1, 5, 8}, {3, -1, 7, 2}, {3, -1, 7, 4}, 
 
>      {3, -1, 7, 6}, {3, -1, 7, 8}, {3, 3, -7, -8}, {3, 3, -7, -6}, 
 
>      {3, 3, -7, -4}, {3, 3, -7, -2}, {3, 3, -5, -8}, {3, 3, -5, -6}, 
 
>      {3, 3, -5, -4}, {3, 3, -5, -2}, {3, 3, -3, -8}, {3, 3, -3, -6}, 
 
>      {3, 3, -3, -4}, {3, 3, -3, -2}, {3, 3, -1, 2}, {3, 3, -1, 4}, 
 
>      {3, 3, -1, 6}, {3, 3, -1, 8}, {3, 5, -7, -8}, {3, 5, -7, -6}, 
 
>      {3, 5, -7, -4}, {3, 5, -7, -2}, {3, 5, -5, -8}, {3, 5, -5, -6}, 
 
>      {3, 5, -5, -4}, {3, 5, -5, -2}, {3, 5, -3, -8}, {3, 5, -3, -6}, 
 
>      {3, 5, -3, -4}, {3, 5, -3, -2}, {3, 5, -1, 2}, {3, 5, -1, 4}, 
 
>      {3, 5, -1, 6}, {3, 5, -1, 8}, {3, 7, -7, -8}, {3, 7, -7, -6}, 
 
>      {3, 7, -7, -4}, {3, 7, -7, -2}, {3, 7, -5, -8}, {3, 7, -5, -6}, 
 
>      {3, 7, -5, -4}, {3, 7, -5, -2}, {3, 7, -3, -8}, {3, 7, -3, -6}, 
 
>      {3, 7, -3, -4}, {3, 7, -3, -2}, {3, 7, -1, 2}, {3, 7, -1, 4}, 
 
>      {3, 7, -1, 6}, {3, 7, -1, 8}, {5, -7, -7, -8}, {5, -7, -7, -6}, 
 
>      {5, -7, -7, 2}, {5, -7, -7, 4}, {5, -7, -7, 6}, {5, -7, -7, 8}, 
 
>      {5, -7, -5, 2}, {5, -7, -5, 4}, {5, -7, -5, 6}, {5, -7, -5, 8}, 
 
>      {5, -7, -3, 2}, {5, -7, -3, 4}, {5, -7, -3, 6}, {5, -7, -3, 8}, 
 
>      {5, -7, 3, -8}, {5, -7, 3, -6}, {5, -7, 3, -4}, {5, -7, 3, -2}, 
 
>      {5, -7, 5, -8}, {5, -7, 5, -6}, {5, -7, 5, -4}, {5, -7, 5, -2}, 
 
>      {5, -7, 7, -8}, {5, -7, 7, -6}, {5, -7, 7, -4}, {5, -7, 7, -2}, 
 
>      {5, -5, -7, 2}, {5, -5, -7, 4}, {5, -5, -7, 6}, {5, -5, -7, 8}, 
 
>      {5, -5, -5, 2}, {5, -5, -5, 4}, {5, -5, -5, 6}, {5, -5, -5, 8}, 
 
>      {5, -5, -3, 2}, {5, -5, -3, 4}, {5, -5, -3, 6}, {5, -5, -3, 8}, 
 
>      {5, -5, 3, -8}, {5, -5, 3, -6}, {5, -5, 3, -4}, {5, -5, 3, -2}, 
 
>      {5, -5, 5, -8}, {5, -5, 5, -6}, {5, -5, 5, -4}, {5, -5, 5, -2}, 
 
>      {5, -5, 7, -8}, {5, -5, 7, -6}, {5, -5, 7, -4}, {5, -5, 7, -2}, 
 
>      {5, -3, -7, 2}, {5, -3, -7, 4}, {5, -3, -7, 6}, {5, -3, -7, 8}, 
 
>      {5, -3, -5, 2}, {5, -3, -5, 4}, {5, -3, -5, 6}, {5, -3, -5, 8}, 
 
>      {5, -3, -3, 2}, {5, -3, -3, 4}, {5, -3, -3, 6}, {5, -3, -3, 8}, 
 
>      {5, -3, 3, -8}, {5, -3, 3, -6}, {5, -3, 3, -4}, {5, -3, 3, -2}, 
 
>      {5, -3, 5, -8}, {5, -3, 5, -6}, {5, -3, 5, -4}, {5, -3, 5, -2}, 
 
>      {5, -3, 5, 4}, {5, -3, 5, 6}, {5, -3, 5, 8}, {5, -3, 7, -8}, 
 
>      {5, -3, 7, -6}, {5, -3, 7, -4}, {5, -3, 7, -2}, {5, -3, 7, 4}, 
 
>      {5, -3, 7, 6}, {5, -3, 7, 8}, {5, -1, 3, 2}, {5, -1, 3, 4}, 
 
>      {5, -1, 3, 6}, {5, -1, 3, 8}, {5, -1, 5, 2}, {5, -1, 5, 4}, 
 
>      {5, -1, 5, 6}, {5, -1, 5, 8}, {5, -1, 7, 2}, {5, -1, 7, 4}, 
 
>      {5, -1, 7, 6}, {5, -1, 7, 8}, {5, 3, -7, -8}, {5, 3, -7, -6}, 
 
>      {5, 3, -7, -4}, {5, 3, -7, -2}, {5, 3, -5, -8}, {5, 3, -5, -6}, 
 
>      {5, 3, -5, -4}, {5, 3, -5, -2}, {5, 3, -3, -8}, {5, 3, -3, -6}, 
 
>      {5, 3, -3, -4}, {5, 3, -3, -2}, {5, 3, -1, 2}, {5, 3, -1, 4}, 
 
>      {5, 3, -1, 6}, {5, 3, -1, 8}, {5, 5, -7, -8}, {5, 5, -7, -6}, 
 
>      {5, 5, -7, -4}, {5, 5, -7, -2}, {5, 5, -5, -8}, {5, 5, -5, -6}, 
 
>      {5, 5, -5, -4}, {5, 5, -5, -2}, {5, 5, -3, -8}, {5, 5, -3, -6}, 
 
>      {5, 5, -3, -4}, {5, 5, -3, -2}, {5, 5, -3, 4}, {5, 5, -3, 6}, 
 
>      {5, 5, -3, 8}, {5, 5, -1, 2}, {5, 5, -1, 4}, {5, 5, -1, 6}, 
 
>      {5, 5, -1, 8}, {5, 7, -7, -8}, {5, 7, -7, -6}, {5, 7, -7, -4}, 
 
>      {5, 7, -7, -2}, {5, 7, -5, -8}, {5, 7, -5, -6}, {5, 7, -5, -4}, 
 
>      {5, 7, -5, -2}, {5, 7, -3, -8}, {5, 7, -3, -6}, {5, 7, -3, -4}, 
 
>      {5, 7, -3, -2}, {5, 7, -3, 4}, {5, 7, -3, 6}, {5, 7, -3, 8}, 
 
>      {5, 7, -1, 2}, {5, 7, -1, 4}, {5, 7, -1, 6}, {5, 7, -1, 8}, 
 
>      {7, -7, -7, 2}, {7, -7, -7, 4}, {7, -7, -7, 6}, {7, -7, -7, 8}, 
 
>      {7, -7, -5, 2}, {7, -7, -5, 4}, {7, -7, -5, 6}, {7, -7, -5, 8}, 
 
>      {7, -7, -3, 2}, {7, -7, -3, 4}, {7, -7, -3, 6}, {7, -7, -3, 8}, 
 
>      {7, -7, 3, -8}, {7, -7, 3, -6}, {7, -7, 3, -4}, {7, -7, 3, -2}, 
 
>      {7, -7, 5, -8}, {7, -7, 5, -6}, {7, -7, 5, -4}, {7, -7, 5, -2}, 
 
>      {7, -7, 7, -8}, {7, -7, 7, -6}, {7, -7, 7, -4}, {7, -7, 7, -2}, 
 
>      {7, -5, -7, 2}, {7, -5, -7, 4}, {7, -5, -7, 6}, {7, -5, -7, 8}, 
 
>      {7, -5, -5, 2}, {7, -5, -5, 4}, {7, -5, -5, 6}, {7, -5, -5, 8}, 
 
>      {7, -5, -3, 2}, {7, -5, -3, 4}, {7, -5, -3, 6}, {7, -5, -3, 8}, 
 
>      {7, -5, 3, -8}, {7, -5, 3, -6}, {7, -5, 3, -4}, {7, -5, 3, -2}, 
 
>      {7, -5, 5, -8}, {7, -5, 5, -6}, {7, -5, 5, -4}, {7, -5, 5, -2}, 
 
>      {7, -5, 7, -8}, {7, -5, 7, -6}, {7, -5, 7, -4}, {7, -5, 7, -2}, 
 
>      {7, -5, 7, 6}, {7, -5, 7, 8}, {7, -3, -7, 2}, {7, -3, -7, 4}, 
 
>      {7, -3, -7, 6}, {7, -3, -7, 8}, {7, -3, -5, 2}, {7, -3, -5, 4}, 
 
>      {7, -3, -5, 6}, {7, -3, -5, 8}, {7, -3, -3, 2}, {7, -3, -3, 4}, 
 
>      {7, -3, -3, 6}, {7, -3, -3, 8}, {7, -3, 3, -8}, {7, -3, 3, -6}, 
 
>      {7, -3, 3, -4}, {7, -3, 3, -2}, {7, -3, 5, -8}, {7, -3, 5, -6}, 
 
>      {7, -3, 5, -4}, {7, -3, 5, -2}, {7, -3, 5, 4}, {7, -3, 5, 6}, 
 
>      {7, -3, 5, 8}, {7, -3, 7, -8}, {7, -3, 7, -6}, {7, -3, 7, -4}, 
 
>      {7, -3, 7, -2}, {7, -3, 7, 4}, {7, -3, 7, 6}, {7, -3, 7, 8}, 
 
>      {7, -1, 3, 2}, {7, -1, 3, 4}, {7, -1, 3, 6}, {7, -1, 3, 8}, 
 
>      {7, -1, 5, 2}, {7, -1, 5, 4}, {7, -1, 5, 6}, {7, -1, 5, 8}, 
 
>      {7, -1, 7, 2}, {7, -1, 7, 4}, {7, -1, 7, 6}, {7, -1, 7, 8}, 
 
>      {7, 3, -7, -8}, {7, 3, -7, -6}, {7, 3, -7, -4}, {7, 3, -7, -2}, 
 
>      {7, 3, -5, -8}, {7, 3, -5, -6}, {7, 3, -5, -4}, {7, 3, -5, -2}, 
 
>      {7, 3, -3, -8}, {7, 3, -3, -6}, {7, 3, -3, -4}, {7, 3, -3, -2}, 
 
>      {7, 3, -1, 2}, {7, 3, -1, 4}, {7, 3, -1, 6}, {7, 3, -1, 8}, 
 
>      {7, 5, -7, -8}, {7, 5, -7, -6}, {7, 5, -7, -4}, {7, 5, -7, -2}, 
 
>      {7, 5, -5, -8}, {7, 5, -5, -6}, {7, 5, -5, -4}, {7, 5, -5, -2}, 
 
>      {7, 5, -3, -8}, {7, 5, -3, -6}, {7, 5, -3, -4}, {7, 5, -3, -2}, 
 
>      {7, 5, -3, 4}, {7, 5, -3, 6}, {7, 5, -3, 8}, {7, 5, -1, 2}, 
 
>      {7, 5, -1, 4}, {7, 5, -1, 6}, {7, 5, -1, 8}, {7, 7, -7, -8}, 
 
>      {7, 7, -7, -6}, {7, 7, -7, -4}, {7, 7, -7, -2}, {7, 7, -5, -8}, 
 
>      {7, 7, -5, -6}, {7, 7, -5, -4}, {7, 7, -5, -2}, {7, 7, -5, 6}, 
 
>      {7, 7, -5, 8}, {7, 7, -3, -8}, {7, 7, -3, -6}, {7, 7, -3, -4}, 
 
>      {7, 7, -3, -2}, {7, 7, -3, 4}, {7, 7, -3, 6}, {7, 7, -3, 8}, 
 
>      {7, 7, -1, 2}, {7, 7, -1, 4}, {7, 7, -1, 6}, {7, 7, -1, 8}}, 
 
>    bulks -> {{{1, 1, 1, 0}, {1, 1, 1, 2}, {1, 1, 1, 4}, {1, 1, 1, 6}, 
 
>       {1, 1, 1, 8}, {1, 1, 3, 0}, {1, 1, 3, 2}, {1, 1, 3, 4}, {1, 1, 3, 6}, 
 
>       {1, 1, 3, 8}, {1, 1, 5, 0}, {1, 1, 5, 2}, {1, 1, 5, 4}, {1, 1, 5, 6}, 
 
>       {1, 1, 5, 8}, {1, 1, 7, 0}, {1, 1, 7, 2}, {1, 1, 7, 4}, {1, 1, 7, 6}, 
 
>       {1, 1, 7, 8}, {1, 3, 1, 0}, {1, 3, 1, 2}, {1, 3, 1, 4}, {1, 3, 1, 6}, 
 
>       {1, 3, 1, 8}, {1, 3, 3, 0}, {1, 3, 3, 2}, {1, 3, 3, 4}, {1, 3, 3, 6}, 
 
>       {1, 3, 3, 8}, {1, 3, 5, 0}, {1, 3, 5, 2}, {1, 3, 5, 4}, {1, 3, 5, 6}, 
 
>       {1, 3, 5, 8}, {1, 3, 7, 0}, {1, 3, 7, 2}, {1, 3, 7, 4}, {1, 3, 7, 6}, 
 
>       {1, 3, 7, 8}, {1, 5, 1, 0}, {1, 5, 1, 2}, {1, 5, 1, 4}, {1, 5, 1, 6}, 
 
>       {1, 5, 1, 8}, {1, 5, 3, 0}, {1, 5, 3, 2}, {1, 5, 3, 4}, {1, 5, 3, 6}, 
 
>       {1, 5, 3, 8}, {1, 5, 5, 0}, {1, 5, 5, 2}, {1, 5, 5, 4}, {1, 5, 5, 6}, 
 
>       {1, 5, 5, 8}, {1, 5, 7, 0}, {1, 5, 7, 2}, {1, 5, 7, 4}, {1, 5, 7, 6}, 
 
>       {1, 5, 7, 8}, {1, 7, 1, 0}, {1, 7, 1, 2}, {1, 7, 1, 4}, {1, 7, 1, 6}, 
 
>       {1, 7, 1, 8}, {1, 7, 3, 0}, {1, 7, 3, 2}, {1, 7, 3, 4}, {1, 7, 3, 6}, 
 
>       {1, 7, 3, 8}, {1, 7, 5, 0}, {1, 7, 5, 2}, {1, 7, 5, 4}, {1, 7, 5, 6}, 
 
>       {1, 7, 5, 8}, {1, 7, 7, 0}, {1, 7, 7, 2}, {1, 7, 7, 4}, {1, 7, 7, 6}, 
 
>       {1, 7, 7, 8}, {3, 1, 1, 0}, {3, 1, 1, 2}, {3, 1, 1, 4}, {3, 1, 1, 6}, 
 
>       {3, 1, 1, 8}, {3, 1, 3, 0}, {3, 1, 3, 2}, {3, 1, 3, 4}, {3, 1, 3, 6}, 
 
>       {3, 1, 3, 8}, {3, 1, 5, 0}, {3, 1, 5, 2}, {3, 1, 5, 4}, {3, 1, 5, 6}, 
 
>       {3, 1, 5, 8}, {3, 1, 7, 0}, {3, 1, 7, 2}, {3, 1, 7, 4}, {3, 1, 7, 6}, 
 
>       {3, 1, 7, 8}, {3, 3, 1, 0}, {3, 3, 1, 2}, {3, 3, 1, 4}, {3, 3, 1, 6}, 
 
>       {3, 3, 1, 8}, {3, 3, 3, 0}, {3, 3, 3, 2}, {3, 3, 3, 4}, {3, 3, 3, 6}, 
 
>       {3, 3, 3, 8}, {3, 3, 5, 0}, {3, 3, 5, 2}, {3, 3, 5, 4}, {3, 3, 5, 6}, 
 
>       {3, 3, 5, 8}, {3, 3, 7, 0}, {3, 3, 7, 2}, {3, 3, 7, 4}, {3, 3, 7, 6}, 
 
>       {3, 3, 7, 8}, {3, 5, 1, 0}, {3, 5, 1, 2}, {3, 5, 1, 4}, {3, 5, 1, 6}, 
 
>       {3, 5, 1, 8}, {3, 5, 3, 0}, {3, 5, 3, 2}, {3, 5, 3, 4}, {3, 5, 3, 6}, 
 
>       {3, 5, 3, 8}, {3, 5, 5, 0}, {3, 5, 5, 2}, {3, 5, 5, 4}, {3, 5, 5, 6}, 
 
>       {3, 5, 5, 8}, {3, 5, 7, 0}, {3, 5, 7, 2}, {3, 5, 7, 4}, {3, 5, 7, 6}, 
 
>       {3, 5, 7, 8}, {3, 7, 1, 0}, {3, 7, 1, 2}, {3, 7, 1, 4}, {3, 7, 1, 6}, 
 
>       {3, 7, 1, 8}, {3, 7, 3, 0}, {3, 7, 3, 2}, {3, 7, 3, 4}, {3, 7, 3, 6}, 
 
>       {3, 7, 3, 8}, {3, 7, 5, 0}, {3, 7, 5, 2}, {3, 7, 5, 4}, {3, 7, 5, 6}, 
 
>       {3, 7, 5, 8}, {3, 7, 7, 0}, {3, 7, 7, 2}, {3, 7, 7, 4}, {3, 7, 7, 6}, 
 
>       {3, 7, 7, 8}, {5, 1, 1, 0}, {5, 1, 1, 2}, {5, 1, 1, 4}, {5, 1, 1, 6}, 
 
>       {5, 1, 1, 8}, {5, 1, 3, 0}, {5, 1, 3, 2}, {5, 1, 3, 4}, {5, 1, 3, 6}, 
 
>       {5, 1, 3, 8}, {5, 1, 5, 0}, {5, 1, 5, 2}, {5, 1, 5, 4}, {5, 1, 5, 6}, 
 
>       {5, 1, 5, 8}, {5, 1, 7, 0}, {5, 1, 7, 2}, {5, 1, 7, 4}, {5, 1, 7, 6}, 
 
>       {5, 1, 7, 8}, {5, 3, 1, 0}, {5, 3, 1, 2}, {5, 3, 1, 4}, {5, 3, 1, 6}, 
 
>       {5, 3, 1, 8}, {5, 3, 3, 0}, {5, 3, 3, 2}, {5, 3, 3, 4}, {5, 3, 3, 6}, 
 
>       {5, 3, 3, 8}, {5, 3, 5, 0}, {5, 3, 5, 2}, {5, 3, 5, 4}, {5, 3, 5, 6}, 
 
>       {5, 3, 5, 8}, {5, 3, 7, 0}, {5, 3, 7, 2}, {5, 3, 7, 4}, {5, 3, 7, 6}, 
 
>       {5, 3, 7, 8}, {5, 5, 1, 0}, {5, 5, 1, 2}, {5, 5, 1, 4}, {5, 5, 1, 6}, 
 
>       {5, 5, 1, 8}, {5, 5, 3, 0}, {5, 5, 3, 2}, {5, 5, 3, 4}, {5, 5, 3, 6}, 
 
>       {5, 5, 3, 8}, {5, 5, 5, 0}, {5, 5, 5, 2}, {5, 5, 5, 4}, {5, 5, 5, 6}, 
 
>       {5, 5, 5, 8}, {5, 5, 7, 0}, {5, 5, 7, 2}, {5, 5, 7, 4}, {5, 5, 7, 6}, 
 
>       {5, 5, 7, 8}, {5, 7, 1, 0}, {5, 7, 1, 2}, {5, 7, 1, 4}, {5, 7, 1, 6}, 
 
>       {5, 7, 1, 8}, {5, 7, 3, 0}, {5, 7, 3, 2}, {5, 7, 3, 4}, {5, 7, 3, 6}, 
 
>       {5, 7, 3, 8}, {5, 7, 5, 0}, {5, 7, 5, 2}, {5, 7, 5, 4}, {5, 7, 5, 6}, 
 
>       {5, 7, 5, 8}, {5, 7, 7, 0}, {5, 7, 7, 2}, {5, 7, 7, 4}, {5, 7, 7, 6}, 
 
>       {5, 7, 7, 8}, {7, 1, 1, 0}, {7, 1, 1, 2}, {7, 1, 1, 4}, {7, 1, 1, 6}, 
 
>       {7, 1, 1, 8}, {7, 1, 3, 0}, {7, 1, 3, 2}, {7, 1, 3, 4}, {7, 1, 3, 6}, 
 
>       {7, 1, 3, 8}, {7, 1, 5, 0}, {7, 1, 5, 2}, {7, 1, 5, 4}, {7, 1, 5, 6}, 
 
>       {7, 1, 5, 8}, {7, 1, 7, 0}, {7, 1, 7, 2}, {7, 1, 7, 4}, {7, 1, 7, 6}, 
 
>       {7, 1, 7, 8}, {7, 3, 1, 0}, {7, 3, 1, 2}, {7, 3, 1, 4}, {7, 3, 1, 6}, 
 
>       {7, 3, 1, 8}, {7, 3, 3, 0}, {7, 3, 3, 2}, {7, 3, 3, 4}, {7, 3, 3, 6}, 
 
>       {7, 3, 3, 8}, {7, 3, 5, 0}, {7, 3, 5, 2}, {7, 3, 5, 4}, {7, 3, 5, 6}, 
 
>       {7, 3, 5, 8}, {7, 3, 7, 0}, {7, 3, 7, 2}, {7, 3, 7, 4}, {7, 3, 7, 6}, 
 
>       {7, 3, 7, 8}, {7, 5, 1, 0}, {7, 5, 1, 2}, {7, 5, 1, 4}, {7, 5, 1, 6}, 
 
>       {7, 5, 1, 8}, {7, 5, 3, 0}, {7, 5, 3, 2}, {7, 5, 3, 4}, {7, 5, 3, 6}, 
 
>       {7, 5, 3, 8}, {7, 5, 5, 0}, {7, 5, 5, 2}, {7, 5, 5, 4}, {7, 5, 5, 6}, 
 
>       {7, 5, 5, 8}, {7, 5, 7, 0}, {7, 5, 7, 2}, {7, 5, 7, 4}, {7, 5, 7, 6}, 
 
>       {7, 5, 7, 8}, {7, 7, 1, 0}, {7, 7, 1, 2}, {7, 7, 1, 4}, {7, 7, 1, 6}, 
 
>       {7, 7, 1, 8}, {7, 7, 3, 0}, {7, 7, 3, 2}, {7, 7, 3, 4}, {7, 7, 3, 6}, 
 
>       {7, 7, 3, 8}, {7, 7, 5, 0}, {7, 7, 5, 2}, {7, 7, 5, 4}, {7, 7, 5, 6}, 
 
>       {7, 7, 5, 8}, {7, 7, 7, 0}, {7, 7, 7, 2}, {7, 7, 7, 4}, {7, 7, 7, 6}, 
 
>       {7, 7, 7, 8}}, {{-7, -1, 1, 8}, {-7, -1, 3, 2}, {-7, -1, 3, 4}, 
 
>       {-7, -1, 3, 6}, {-7, -1, 3, 8}, {-7, -1, 5, 2}, {-7, -1, 5, 4}, 
 
>       {-7, -1, 5, 6}, {-7, -1, 5, 8}, {-7, -1, 7, 2}, {-7, -1, 7, 4}, 
 
>       {-7, -1, 7, 6}, {-7, -1, 7, 8}, {-7, 1, -1, 8}, {-7, 1, 1, 0}, 
 
>       {-7, 1, 1, 2}, {-7, 1, 1, 4}, {-7, 1, 1, 6}, {-7, 1, 1, 8}, 
 
>       {-7, 1, 3, 0}, {-7, 1, 3, 2}, {-7, 1, 3, 4}, {-7, 1, 3, 6}, 
 
>       {-7, 1, 3, 8}, {-7, 1, 5, 0}, {-7, 1, 5, 2}, {-7, 1, 5, 4}, 
 
>       {-7, 1, 5, 6}, {-7, 1, 5, 8}, {-7, 1, 7, 0}, {-7, 1, 7, 2}, 
 
>       {-7, 1, 7, 4}, {-7, 1, 7, 6}, {-7, 1, 7, 8}, {-7, 3, -1, 2}, 
 
>       {-7, 3, -1, 4}, {-7, 3, -1, 6}, {-7, 3, -1, 8}, {-7, 3, 1, 0}, 
 
>       {-7, 3, 1, 2}, {-7, 3, 1, 4}, {-7, 3, 1, 6}, {-7, 3, 1, 8}, 
 
>       {-7, 3, 3, 0}, {-7, 3, 3, 2}, {-7, 3, 3, 4}, {-7, 3, 3, 6}, 
 
>       {-7, 3, 3, 8}, {-7, 3, 5, 0}, {-7, 3, 5, 2}, {-7, 3, 5, 4}, 
 
>       {-7, 3, 5, 6}, {-7, 3, 5, 8}, {-7, 3, 7, 0}, {-7, 3, 7, 2}, 
 
>       {-7, 3, 7, 4}, {-7, 3, 7, 6}, {-7, 3, 7, 8}, {-7, 5, -1, 2}, 
 
>       {-7, 5, -1, 4}, {-7, 5, -1, 6}, {-7, 5, -1, 8}, {-7, 5, 1, 0}, 
 
>       {-7, 5, 1, 2}, {-7, 5, 1, 4}, {-7, 5, 1, 6}, {-7, 5, 1, 8}, 
 
>       {-7, 5, 3, 0}, {-7, 5, 3, 2}, {-7, 5, 3, 4}, {-7, 5, 3, 6}, 
 
>       {-7, 5, 3, 8}, {-7, 5, 5, 0}, {-7, 5, 5, 2}, {-7, 5, 5, 4}, 
 
>       {-7, 5, 5, 6}, {-7, 5, 5, 8}, {-7, 5, 7, 0}, {-7, 5, 7, 2}, 
 
>       {-7, 5, 7, 4}, {-7, 5, 7, 6}, {-7, 5, 7, 8}, {-7, 7, -1, 2}, 
 
>       {-7, 7, -1, 4}, {-7, 7, -1, 6}, {-7, 7, -1, 8}, {-7, 7, 1, 0}, 
 
>       {-7, 7, 1, 2}, {-7, 7, 1, 4}, {-7, 7, 1, 6}, {-7, 7, 1, 8}, 
 
>       {-7, 7, 3, 0}, {-7, 7, 3, 2}, {-7, 7, 3, 4}, {-7, 7, 3, 6}, 
 
>       {-7, 7, 3, 8}, {-7, 7, 5, 0}, {-7, 7, 5, 2}, {-7, 7, 5, 4}, 
 
>       {-7, 7, 5, 6}, {-7, 7, 5, 8}, {-7, 7, 7, 0}, {-7, 7, 7, 2}, 
 
>       {-7, 7, 7, 4}, {-7, 7, 7, 6}, {-7, 7, 7, 8}, {-5, -1, 1, 6}, 
 
>       {-5, -1, 1, 8}, {-5, -1, 3, 2}, {-5, -1, 3, 4}, {-5, -1, 3, 6}, 
 
>       {-5, -1, 3, 8}, {-5, -1, 5, 2}, {-5, -1, 5, 4}, {-5, -1, 5, 6}, 
 
>       {-5, -1, 5, 8}, {-5, -1, 7, 2}, {-5, -1, 7, 4}, {-5, -1, 7, 6}, 
 
>       {-5, -1, 7, 8}, {-5, 1, -1, 6}, {-5, 1, -1, 8}, {-5, 1, 1, 0}, 
 
>       {-5, 1, 1, 2}, {-5, 1, 1, 4}, {-5, 1, 1, 6}, {-5, 1, 1, 8}, 
 
>       {-5, 1, 3, 0}, {-5, 1, 3, 2}, {-5, 1, 3, 4}, {-5, 1, 3, 6}, 
 
>       {-5, 1, 3, 8}, {-5, 1, 5, 0}, {-5, 1, 5, 2}, {-5, 1, 5, 4}, 
 
>       {-5, 1, 5, 6}, {-5, 1, 5, 8}, {-5, 1, 7, 0}, {-5, 1, 7, 2}, 
 
>       {-5, 1, 7, 4}, {-5, 1, 7, 6}, {-5, 1, 7, 8}, {-5, 3, -1, 2}, 
 
>       {-5, 3, -1, 4}, {-5, 3, -1, 6}, {-5, 3, -1, 8}, {-5, 3, 1, 0}, 
 
>       {-5, 3, 1, 2}, {-5, 3, 1, 4}, {-5, 3, 1, 6}, {-5, 3, 1, 8}, 
 
>       {-5, 3, 3, 0}, {-5, 3, 3, 2}, {-5, 3, 3, 4}, {-5, 3, 3, 6}, 
 
>       {-5, 3, 3, 8}, {-5, 3, 5, 0}, {-5, 3, 5, 2}, {-5, 3, 5, 4}, 
 
>       {-5, 3, 5, 6}, {-5, 3, 5, 8}, {-5, 3, 7, 0}, {-5, 3, 7, 2}, 
 
>       {-5, 3, 7, 4}, {-5, 3, 7, 6}, {-5, 3, 7, 8}, {-5, 5, -1, 2}, 
 
>       {-5, 5, -1, 4}, {-5, 5, -1, 6}, {-5, 5, -1, 8}, {-5, 5, 1, 0}, 
 
>       {-5, 5, 1, 2}, {-5, 5, 1, 4}, {-5, 5, 1, 6}, {-5, 5, 1, 8}, 
 
>       {-5, 5, 3, 0}, {-5, 5, 3, 2}, {-5, 5, 3, 4}, {-5, 5, 3, 6}, 
 
>       {-5, 5, 3, 8}, {-5, 5, 5, 0}, {-5, 5, 5, 2}, {-5, 5, 5, 4}, 
 
>       {-5, 5, 5, 6}, {-5, 5, 5, 8}, {-5, 5, 7, 0}, {-5, 5, 7, 2}, 
 
>       {-5, 5, 7, 4}, {-5, 5, 7, 6}, {-5, 5, 7, 8}, {-5, 7, -1, 2}, 
 
>       {-5, 7, -1, 4}, {-5, 7, -1, 6}, {-5, 7, -1, 8}, {-5, 7, 1, 0}, 
 
>       {-5, 7, 1, 2}, {-5, 7, 1, 4}, {-5, 7, 1, 6}, {-5, 7, 1, 8}, 
 
>       {-5, 7, 3, 0}, {-5, 7, 3, 2}, {-5, 7, 3, 4}, {-5, 7, 3, 6}, 
 
>       {-5, 7, 3, 8}, {-5, 7, 5, 0}, {-5, 7, 5, 2}, {-5, 7, 5, 4}, 
 
>       {-5, 7, 5, 6}, {-5, 7, 5, 8}, {-5, 7, 7, 0}, {-5, 7, 7, 2}, 
 
>       {-5, 7, 7, 4}, {-3, -1, 1, 4}, {-3, -1, 1, 6}, {-3, -1, 1, 8}, 
 
>       {-3, -1, 3, 2}, {-3, -1, 3, 4}, {-3, -1, 3, 6}, {-3, -1, 3, 8}, 
 
>       {-3, -1, 5, 2}, {-3, -1, 5, 4}, {-3, -1, 5, 6}, {-3, -1, 5, 8}, 
 
>       {-3, -1, 7, 2}, {-3, -1, 7, 4}, {-3, -1, 7, 6}, {-3, -1, 7, 8}, 
 
>       {-3, 1, -1, 4}, {-3, 1, -1, 6}, {-3, 1, -1, 8}, {-3, 1, 1, 0}, 
 
>       {-3, 1, 1, 2}, {-3, 1, 1, 4}, {-3, 1, 1, 6}, {-3, 1, 1, 8}, 
 
>       {-3, 1, 3, 0}, {-3, 1, 3, 2}, {-3, 1, 3, 4}, {-3, 1, 3, 6}, 
 
>       {-3, 1, 3, 8}, {-3, 1, 5, 0}, {-3, 1, 5, 2}, {-3, 1, 5, 4}, 
 
>       {-3, 1, 5, 6}, {-3, 1, 5, 8}, {-3, 1, 7, 0}, {-3, 1, 7, 2}, 
 
>       {-3, 1, 7, 4}, {-3, 1, 7, 6}, {-3, 1, 7, 8}, {-3, 3, -1, 2}, 
 
>       {-3, 3, -1, 4}, {-3, 3, -1, 6}, {-3, 3, -1, 8}, {-3, 3, 1, 0}, 
 
>       {-3, 3, 1, 2}, {-3, 3, 1, 4}, {-3, 3, 1, 6}, {-3, 3, 1, 8}, 
 
>       {-3, 3, 3, 0}, {-3, 3, 3, 2}, {-3, 3, 3, 4}, {-3, 3, 3, 6}, 
 
>       {-3, 3, 3, 8}, {-3, 3, 5, 0}, {-3, 3, 5, 2}, {-3, 3, 5, 4}, 
 
>       {-3, 3, 5, 6}, {-3, 3, 5, 8}, {-3, 3, 7, 0}, {-3, 3, 7, 2}, 
 
>       {-3, 3, 7, 4}, {-3, 3, 7, 6}, {-3, 3, 7, 8}, {-3, 5, -1, 2}, 
 
>       {-3, 5, -1, 4}, {-3, 5, -1, 6}, {-3, 5, -1, 8}, {-3, 5, 1, 0}, 
 
>       {-3, 5, 1, 2}, {-3, 5, 1, 4}, {-3, 5, 1, 6}, {-3, 5, 1, 8}, 
 
>       {-3, 5, 3, 0}, {-3, 5, 3, 2}, {-3, 5, 3, 4}, {-3, 5, 3, 6}, 
 
>       {-3, 5, 3, 8}, {-3, 5, 5, 0}, {-3, 5, 5, 2}, {-3, 5, 7, 0}, 
 
>       {-3, 5, 7, 2}, {-3, 7, -1, 2}, {-3, 7, -1, 4}, {-3, 7, -1, 6}, 
 
>       {-3, 7, -1, 8}, {-3, 7, 1, 0}, {-3, 7, 1, 2}, {-3, 7, 1, 4}, 
 
>       {-3, 7, 1, 6}, {-3, 7, 1, 8}, {-3, 7, 3, 0}, {-3, 7, 3, 2}, 
 
>       {-3, 7, 3, 4}, {-3, 7, 3, 6}, {-3, 7, 3, 8}, {-3, 7, 5, 0}, 
 
>       {-3, 7, 5, 2}, {-3, 7, 7, 0}, {-3, 7, 7, 2}, {-1, -7, 1, 8}, 
 
>       {-1, -7, 3, 2}, {-1, -7, 3, 4}, {-1, -7, 3, 6}, {-1, -7, 3, 8}, 
 
>       {-1, -7, 5, 2}, {-1, -7, 5, 4}, {-1, -7, 5, 6}, {-1, -7, 5, 8}, 
 
>       {-1, -7, 7, 2}, {-1, -7, 7, 4}, {-1, -7, 7, 6}, {-1, -7, 7, 8}, 
 
>       {-1, -5, 1, 6}, {-1, -5, 1, 8}, {-1, -5, 3, 2}, {-1, -5, 3, 4}, 
 
>       {-1, -5, 3, 6}, {-1, -5, 3, 8}, {-1, -5, 5, 2}, {-1, -5, 5, 4}, 
 
>       {-1, -5, 5, 6}, {-1, -5, 5, 8}, {-1, -5, 7, 2}, {-1, -5, 7, 4}, 
 
>       {-1, -5, 7, 6}, {-1, -5, 7, 8}, {-1, -3, 1, 4}, {-1, -3, 1, 6}, 
 
>       {-1, -3, 1, 8}, {-1, -3, 3, 2}, {-1, -3, 3, 4}, {-1, -3, 3, 6}, 
 
>       {-1, -3, 3, 8}, {-1, -3, 5, 2}, {-1, -3, 5, 4}, {-1, -3, 5, 6}, 
 
>       {-1, -3, 5, 8}, {-1, -3, 7, 2}, {-1, -3, 7, 4}, {-1, -3, 7, 6}, 
 
>       {-1, -3, 7, 8}, {-1, -1, 1, 2}, {-1, -1, 1, 4}, {-1, -1, 1, 6}, 
 
>       {-1, -1, 1, 8}, {-1, -1, 3, 2}, {-1, -1, 3, 4}, {-1, -1, 3, 6}, 
 
>       {-1, -1, 3, 8}, {-1, -1, 5, 2}, {-1, -1, 5, 4}, {-1, -1, 5, 6}, 
 
>       {-1, -1, 5, 8}, {-1, -1, 7, 2}, {-1, -1, 7, 4}, {-1, -1, 7, 6}, 
 
>       {-1, -1, 7, 8}, {-1, 1, -7, 8}, {-1, 1, -5, 6}, {-1, 1, -5, 8}, 
 
>       {-1, 1, -3, 4}, {-1, 1, -3, 6}, {-1, 1, -3, 8}, {-1, 1, -1, 2}, 
 
>       {-1, 1, -1, 4}, {-1, 1, -1, 6}, {-1, 1, -1, 8}, {-1, 1, 1, 0}, 
 
>       {-1, 1, 1, 2}, {-1, 1, 1, 4}, {-1, 1, 1, 6}, {-1, 1, 1, 8}, 
 
>       {-1, 1, 3, -2}, {-1, 1, 3, 0}, {-1, 1, 3, 2}, {-1, 1, 3, 4}, 
 
>       {-1, 1, 3, 6}, {-1, 1, 3, 8}, {-1, 1, 5, -4}, {-1, 1, 5, -2}, 
 
>       {-1, 1, 5, 0}, {-1, 1, 5, 2}, {-1, 1, 5, 4}, {-1, 1, 5, 6}, 
 
>       {-1, 1, 5, 8}, {-1, 1, 7, -6}, {-1, 1, 7, -4}, {-1, 1, 7, -2}, 
 
>       {-1, 1, 7, 0}, {-1, 1, 7, 2}, {-1, 1, 7, 4}, {-1, 1, 7, 6}, 
 
>       {-1, 1, 7, 8}, {-1, 3, -7, 2}, {-1, 3, -7, 4}, {-1, 3, -7, 6}, 
 
>       {-1, 3, -7, 8}, {-1, 3, -5, 2}, {-1, 3, -5, 4}, {-1, 3, -5, 6}, 
 
>       {-1, 3, -5, 8}, {-1, 3, -3, 2}, {-1, 3, -3, 4}, {-1, 3, -3, 6}, 
 
>       {-1, 3, -3, 8}, {-1, 3, -1, 2}, {-1, 3, -1, 4}, {-1, 3, -1, 6}, 
 
>       {-1, 3, -1, 8}, {-1, 3, 1, -2}, {-1, 3, 1, 0}, {-1, 3, 1, 2}, 
 
>       {-1, 3, 1, 4}, {-1, 3, 1, 6}, {-1, 3, 1, 8}, {-1, 3, 3, -8}, 
 
>       {-1, 3, 3, -6}, {-1, 3, 3, -4}, {-1, 3, 3, -2}, {-1, 3, 3, 0}, 
 
>       {-1, 3, 5, -8}, {-1, 3, 5, -6}, {-1, 3, 5, -4}, {-1, 3, 5, -2}, 
 
>       {-1, 3, 5, 0}, {-1, 3, 7, -8}, {-1, 3, 7, -6}, {-1, 3, 7, -4}, 
 
>       {-1, 3, 7, -2}, {-1, 3, 7, 0}, {-1, 5, -7, 2}, {-1, 5, -7, 4}, 
 
>       {-1, 5, -7, 6}, {-1, 5, -7, 8}, {-1, 5, -5, 2}, {-1, 5, -5, 4}, 
 
>       {-1, 5, -5, 6}, {-1, 5, -5, 8}, {-1, 5, -3, 2}, {-1, 5, -3, 4}, 
 
>       {-1, 5, -3, 6}, {-1, 5, -3, 8}, {-1, 5, -1, 2}, {-1, 5, -1, 4}, 
 
>       {-1, 5, -1, 6}, {-1, 5, -1, 8}, {-1, 5, 1, -4}, {-1, 5, 1, -2}, 
 
>       {-1, 5, 1, 0}, {-1, 5, 1, 2}, {-1, 5, 1, 4}, {-1, 5, 1, 6}, 
 
>       {-1, 5, 1, 8}, {-1, 5, 3, -8}, {-1, 5, 3, -6}, {-1, 5, 3, -4}, 
 
>       {-1, 5, 3, -2}, {-1, 5, 3, 0}, {-1, 5, 5, -8}, {-1, 5, 5, -6}, 
 
>       {-1, 5, 5, -4}, {-1, 5, 5, -2}, {-1, 5, 5, 0}, {-1, 5, 7, -8}, 
 
>       {-1, 5, 7, -6}, {-1, 5, 7, -4}, {-1, 5, 7, -2}, {-1, 5, 7, 0}, 
 
>       {-1, 7, -7, 2}, {-1, 7, -7, 4}, {-1, 7, -7, 6}, {-1, 7, -7, 8}, 
 
>       {-1, 7, -5, 2}, {-1, 7, -5, 4}, {-1, 7, -5, 6}, {-1, 7, -5, 8}, 
 
>       {-1, 7, -3, 2}, {-1, 7, -3, 4}, {-1, 7, -3, 6}, {-1, 7, -3, 8}, 
 
>       {-1, 7, -1, 2}, {-1, 7, -1, 4}, {-1, 7, -1, 6}, {-1, 7, -1, 8}, 
 
>       {-1, 7, 1, -6}, {-1, 7, 1, -4}, {-1, 7, 1, -2}, {-1, 7, 1, 0}, 
 
>       {-1, 7, 1, 2}, {-1, 7, 1, 4}, {-1, 7, 1, 6}, {-1, 7, 1, 8}, 
 
>       {-1, 7, 3, -8}, {-1, 7, 3, -6}, {-1, 7, 3, -4}, {-1, 7, 3, -2}, 
 
>       {-1, 7, 3, 0}, {-1, 7, 5, -8}, {-1, 7, 5, -6}, {-1, 7, 5, -4}, 
 
>       {-1, 7, 5, -2}, {-1, 7, 5, 0}, {-1, 7, 7, -8}, {-1, 7, 7, -6}, 
 
>       {-1, 7, 7, -4}, {-1, 7, 7, -2}, {-1, 7, 7, 0}, {1, -7, -1, 8}, 
 
>       {1, -7, 1, 0}, {1, -7, 1, 2}, {1, -7, 1, 4}, {1, -7, 1, 6}, 
 
>       {1, -7, 1, 8}, {1, -7, 3, 0}, {1, -7, 3, 2}, {1, -7, 3, 4}, 
 
>       {1, -7, 3, 6}, {1, -7, 3, 8}, {1, -7, 5, 0}, {1, -7, 5, 2}, 
 
>       {1, -7, 5, 4}, {1, -7, 5, 6}, {1, -7, 5, 8}, {1, -7, 7, 0}, 
 
>       {1, -7, 7, 2}, {1, -7, 7, 4}, {1, -7, 7, 6}, {1, -7, 7, 8}, 
 
>       {1, -5, -1, 6}, {1, -5, -1, 8}, {1, -5, 1, 0}, {1, -5, 1, 2}, 
 
>       {1, -5, 1, 4}, {1, -5, 1, 6}, {1, -5, 1, 8}, {1, -5, 3, 0}, 
 
>       {1, -5, 3, 2}, {1, -5, 3, 4}, {1, -5, 3, 6}, {1, -5, 3, 8}, 
 
>       {1, -5, 5, 0}, {1, -5, 5, 2}, {1, -5, 5, 4}, {1, -5, 5, 6}, 
 
>       {1, -5, 5, 8}, {1, -5, 7, 0}, {1, -5, 7, 2}, {1, -5, 7, 4}, 
 
>       {1, -5, 7, 6}, {1, -5, 7, 8}, {1, -3, -1, 4}, {1, -3, -1, 6}, 
 
>       {1, -3, -1, 8}, {1, -3, 1, 0}, {1, -3, 1, 2}, {1, -3, 1, 4}, 
 
>       {1, -3, 1, 6}, {1, -3, 1, 8}, {1, -3, 3, 0}, {1, -3, 3, 2}, 
 
>       {1, -3, 3, 4}, {1, -3, 3, 6}, {1, -3, 3, 8}, {1, -3, 5, 0}, 
 
>       {1, -3, 5, 2}, {1, -3, 5, 4}, {1, -3, 5, 6}, {1, -3, 5, 8}, 
 
>       {1, -3, 7, 0}, {1, -3, 7, 2}, {1, -3, 7, 4}, {1, -3, 7, 6}, 
 
>       {1, -3, 7, 8}, {1, -1, -7, 8}, {1, -1, -5, 6}, {1, -1, -5, 8}, 
 
>       {1, -1, -3, 4}, {1, -1, -3, 6}, {1, -1, -3, 8}, {1, -1, -1, 2}, 
 
>       {1, -1, -1, 4}, {1, -1, -1, 6}, {1, -1, -1, 8}, {1, -1, 1, 0}, 
 
>       {1, -1, 1, 2}, {1, -1, 1, 4}, {1, -1, 1, 6}, {1, -1, 1, 8}, 
 
>       {1, -1, 3, -2}, {1, -1, 3, 0}, {1, -1, 3, 2}, {1, -1, 3, 4}, 
 
>       {1, -1, 3, 6}, {1, -1, 3, 8}, {1, -1, 5, -4}, {1, -1, 5, -2}, 
 
>       {1, -1, 5, 0}, {1, -1, 5, 2}, {1, -1, 5, 4}, {1, -1, 5, 6}, 
 
>       {1, -1, 5, 8}, {1, -1, 7, -6}, {1, -1, 7, -4}, {1, -1, 7, -2}, 
 
>       {1, -1, 7, 0}, {1, -1, 7, 2}, {1, -1, 7, 4}, {1, -1, 7, 6}, 
 
>       {1, -1, 7, 8}, {1, 1, -7, 0}, {1, 1, -7, 2}, {1, 1, -7, 4}, 
 
>       {1, 1, -7, 6}, {1, 1, -7, 8}, {1, 1, -5, 0}, {1, 1, -5, 2}, 
 
>       {1, 1, -5, 4}, {1, 1, -5, 6}, {1, 1, -5, 8}, {1, 1, -3, 0}, 
 
>       {1, 1, -3, 2}, {1, 1, -3, 4}, {1, 1, -3, 6}, {1, 1, -3, 8}, 
 
>       {1, 1, -1, 0}, {1, 1, -1, 2}, {1, 1, -1, 4}, {1, 1, -1, 6}, 
 
>       {1, 1, -1, 8}, {1, 1, 1, -8}, {1, 1, 1, -6}, {1, 1, 1, -4}, 
 
>       {1, 1, 1, -2}, {1, 1, 3, -8}, {1, 1, 3, -6}, {1, 1, 3, -4}, 
 
>       {1, 1, 3, -2}, {1, 1, 5, -8}, {1, 1, 5, -6}, {1, 1, 5, -4}, 
 
>       {1, 1, 5, -2}, {1, 1, 7, -8}, {1, 1, 7, -6}, {1, 1, 7, -4}, 
 
>       {1, 1, 7, -2}, {1, 3, -7, 0}, {1, 3, -7, 2}, {1, 3, -7, 4}, 
 
>       {1, 3, -7, 6}, {1, 3, -7, 8}, {1, 3, -5, 0}, {1, 3, -5, 2}, 
 
>       {1, 3, -5, 4}, {1, 3, -5, 6}, {1, 3, -5, 8}, {1, 3, -3, 0}, 
 
>       {1, 3, -3, 2}, {1, 3, -3, 4}, {1, 3, -3, 6}, {1, 3, -3, 8}, 
 
>       {1, 3, -1, -2}, {1, 3, -1, 0}, {1, 3, -1, 2}, {1, 3, -1, 4}, 
 
>       {1, 3, -1, 6}, {1, 3, -1, 8}, {1, 3, 1, -8}, {1, 3, 1, -6}, 
 
>       {1, 3, 1, -4}, {1, 3, 1, -2}, {1, 3, 3, -8}, {1, 3, 3, -6}, 
 
>       {1, 3, 3, -4}, {1, 3, 3, -2}, {1, 3, 5, -8}, {1, 3, 5, -6}, 
 
>       {1, 3, 5, -4}, {1, 3, 5, -2}, {1, 3, 7, -8}, {1, 3, 7, -6}, 
 
>       {1, 3, 7, -4}, {1, 3, 7, -2}, {1, 5, -7, 0}, {1, 5, -7, 2}, 
 
>       {1, 5, -7, 4}, {1, 5, -7, 6}, {1, 5, -7, 8}, {1, 5, -5, 0}, 
 
>       {1, 5, -5, 2}, {1, 5, -5, 4}, {1, 5, -5, 6}, {1, 5, -5, 8}, 
 
>       {1, 5, -3, 0}, {1, 5, -3, 2}, {1, 5, -3, 4}, {1, 5, -3, 6}, 
 
>       {1, 5, -3, 8}, {1, 5, -1, -4}, {1, 5, -1, -2}, {1, 5, -1, 0}, 
 
>       {1, 5, -1, 2}, {1, 5, -1, 4}, {1, 5, -1, 6}, {1, 5, -1, 8}, 
 
>       {1, 5, 1, -8}, {1, 5, 1, -6}, {1, 5, 1, -4}, {1, 5, 1, -2}, 
 
>       {1, 5, 3, -8}, {1, 5, 3, -6}, {1, 5, 3, -4}, {1, 5, 3, -2}, 
 
>       {1, 5, 5, -8}, {1, 5, 5, -6}, {1, 5, 5, -4}, {1, 5, 5, -2}, 
 
>       {1, 5, 7, -8}, {1, 5, 7, -6}, {1, 5, 7, -4}, {1, 5, 7, -2}, 
 
>       {1, 7, -7, 0}, {1, 7, -7, 2}, {1, 7, -7, 4}, {1, 7, -7, 6}, 
 
>       {1, 7, -7, 8}, {1, 7, -5, 0}, {1, 7, -5, 2}, {1, 7, -5, 4}, 
 
>       {1, 7, -5, 6}, {1, 7, -5, 8}, {1, 7, -3, 0}, {1, 7, -3, 2}, 
 
>       {1, 7, -3, 4}, {1, 7, -3, 6}, {1, 7, -3, 8}, {1, 7, -1, -6}, 
 
>       {1, 7, -1, -4}, {1, 7, -1, -2}, {1, 7, -1, 0}, {1, 7, -1, 2}, 
 
>       {1, 7, -1, 4}, {1, 7, -1, 6}, {1, 7, -1, 8}, {1, 7, 1, -8}, 
 
>       {1, 7, 1, -6}, {1, 7, 1, -4}, {1, 7, 1, -2}, {1, 7, 3, -8}, 
 
>       {1, 7, 3, -6}, {1, 7, 3, -4}, {1, 7, 3, -2}, {1, 7, 5, -8}, 
 
>       {1, 7, 5, -6}, {1, 7, 5, -4}, {1, 7, 5, -2}, {1, 7, 7, -8}, 
 
>       {1, 7, 7, -6}, {1, 7, 7, -4}, {1, 7, 7, -2}, {3, -7, -1, 2}, 
 
>       {3, -7, -1, 4}, {3, -7, -1, 6}, {3, -7, -1, 8}, {3, -7, 1, 0}, 
 
>       {3, -7, 1, 2}, {3, -7, 1, 4}, {3, -7, 1, 6}, {3, -7, 1, 8}, 
 
>       {3, -7, 3, 0}, {3, -7, 3, 2}, {3, -7, 3, 4}, {3, -7, 3, 6}, 
 
>       {3, -7, 3, 8}, {3, -7, 5, 0}, {3, -7, 5, 2}, {3, -7, 5, 4}, 
 
>       {3, -7, 5, 6}, {3, -7, 5, 8}, {3, -7, 7, 0}, {3, -7, 7, 2}, 
 
>       {3, -7, 7, 4}, {3, -7, 7, 6}, {3, -7, 7, 8}, {3, -5, -1, 2}, 
 
>       {3, -5, -1, 4}, {3, -5, -1, 6}, {3, -5, -1, 8}, {3, -5, 1, 0}, 
 
>       {3, -5, 1, 2}, {3, -5, 1, 4}, {3, -5, 1, 6}, {3, -5, 1, 8}, 
 
>       {3, -5, 3, 0}, {3, -5, 3, 2}, {3, -5, 3, 4}, {3, -5, 3, 6}, 
 
>       {3, -5, 3, 8}, {3, -5, 5, 0}, {3, -5, 5, 2}, {3, -5, 5, 4}, 
 
>       {3, -5, 5, 6}, {3, -5, 5, 8}, {3, -5, 7, 0}, {3, -5, 7, 2}, 
 
>       {3, -5, 7, 4}, {3, -5, 7, 6}, {3, -5, 7, 8}, {3, -3, -1, 2}, 
 
>       {3, -3, -1, 4}, {3, -3, -1, 6}, {3, -3, -1, 8}, {3, -3, 1, 0}, 
 
>       {3, -3, 1, 2}, {3, -3, 1, 4}, {3, -3, 1, 6}, {3, -3, 1, 8}, 
 
>       {3, -3, 3, 0}, {3, -3, 3, 2}, {3, -3, 3, 4}, {3, -3, 3, 6}, 
 
>       {3, -3, 3, 8}, {3, -3, 5, 0}, {3, -3, 5, 2}, {3, -3, 5, 4}, 
 
>       {3, -3, 5, 6}, {3, -3, 5, 8}, {3, -3, 7, 0}, {3, -3, 7, 2}, 
 
>       {3, -3, 7, 4}, {3, -3, 7, 6}, {3, -3, 7, 8}, {3, -1, -7, 2}, 
 
>       {3, -1, -7, 4}, {3, -1, -7, 6}, {3, -1, -7, 8}, {3, -1, -5, 2}, 
 
>       {3, -1, -5, 4}, {3, -1, -5, 6}, {3, -1, -5, 8}, {3, -1, -3, 2}, 
 
>       {3, -1, -3, 4}, {3, -1, -3, 6}, {3, -1, -3, 8}, {3, -1, -1, 2}, 
 
>       {3, -1, -1, 4}, {3, -1, -1, 6}, {3, -1, -1, 8}, {3, -1, 1, -2}, 
 
>       {3, -1, 1, 0}, {3, -1, 1, 2}, {3, -1, 1, 4}, {3, -1, 1, 6}, 
 
>       {3, -1, 1, 8}, {3, -1, 3, -8}, {3, -1, 3, -6}, {3, -1, 3, -4}, 
 
>       {3, -1, 3, -2}, {3, -1, 3, 0}, {3, -1, 5, -8}, {3, -1, 5, -6}, 
 
>       {3, -1, 5, -4}, {3, -1, 5, -2}, {3, -1, 5, 0}, {3, -1, 7, -8}, 
 
>       {3, -1, 7, -6}, {3, -1, 7, -4}, {3, -1, 7, -2}, {3, -1, 7, 0}, 
 
>       {3, 1, -7, 0}, {3, 1, -7, 2}, {3, 1, -7, 4}, {3, 1, -7, 6}, 
 
>       {3, 1, -7, 8}, {3, 1, -5, 0}, {3, 1, -5, 2}, {3, 1, -5, 4}, 
 
>       {3, 1, -5, 6}, {3, 1, -5, 8}, {3, 1, -3, 0}, {3, 1, -3, 2}, 
 
>       {3, 1, -3, 4}, {3, 1, -3, 6}, {3, 1, -3, 8}, {3, 1, -1, -2}, 
 
>       {3, 1, -1, 0}, {3, 1, -1, 2}, {3, 1, -1, 4}, {3, 1, -1, 6}, 
 
>       {3, 1, -1, 8}, {3, 1, 1, -8}, {3, 1, 1, -6}, {3, 1, 1, -4}, 
 
>       {3, 1, 1, -2}, {3, 1, 3, -8}, {3, 1, 3, -6}, {3, 1, 3, -4}, 
 
>       {3, 1, 3, -2}, {3, 1, 5, -8}, {3, 1, 5, -6}, {3, 1, 5, -4}, 
 
>       {3, 1, 5, -2}, {3, 1, 7, -8}, {3, 1, 7, -6}, {3, 1, 7, -4}, 
 
>       {3, 1, 7, -2}, {3, 3, -7, 0}, {3, 3, -7, 2}, {3, 3, -7, 4}, 
 
>       {3, 3, -7, 6}, {3, 3, -7, 8}, {3, 3, -5, 0}, {3, 3, -5, 2}, 
 
>       {3, 3, -5, 4}, {3, 3, -5, 6}, {3, 3, -5, 8}, {3, 3, -3, 0}, 
 
>       {3, 3, -3, 2}, {3, 3, -3, 4}, {3, 3, -3, 6}, {3, 3, -3, 8}, 
 
>       {3, 3, -1, -8}, {3, 3, -1, -6}, {3, 3, -1, -4}, {3, 3, -1, -2}, 
 
>       {3, 3, -1, 0}, {3, 3, 1, -8}, {3, 3, 1, -6}, {3, 3, 1, -4}, 
 
>       {3, 3, 1, -2}, {3, 3, 3, -8}, {3, 3, 3, -6}, {3, 3, 3, -4}, 
 
>       {3, 3, 5, -8}, {3, 3, 5, -6}, {3, 3, 5, -4}, {3, 3, 7, -8}, 
 
>       {3, 3, 7, -6}, {3, 3, 7, -4}, {3, 5, -7, 0}, {3, 5, -7, 2}, 
 
>       {3, 5, -7, 4}, {3, 5, -7, 6}, {3, 5, -7, 8}, {3, 5, -5, 0}, 
 
>       {3, 5, -5, 2}, {3, 5, -5, 4}, {3, 5, -5, 6}, {3, 5, -5, 8}, 
 
>       {3, 5, -3, 0}, {3, 5, -3, 2}, {3, 5, -3, 4}, {3, 5, -3, 6}, 
 
>       {3, 5, -3, 8}, {3, 5, -1, -8}, {3, 5, -1, -6}, {3, 5, -1, -4}, 
 
>       {3, 5, -1, -2}, {3, 5, -1, 0}, {3, 5, 1, -8}, {3, 5, 1, -6}, 
 
>       {3, 5, 1, -4}, {3, 5, 1, -2}, {3, 5, 3, -8}, {3, 5, 3, -6}, 
 
>       {3, 5, 3, -4}, {3, 5, 5, -8}, {3, 5, 5, -6}, {3, 5, 5, -4}, 
 
>       {3, 5, 7, -8}, {3, 5, 7, -6}, {3, 5, 7, -4}, {3, 7, -7, 0}, 
 
>       {3, 7, -7, 2}, {3, 7, -7, 4}, {3, 7, -7, 6}, {3, 7, -7, 8}, 
 
>       {3, 7, -5, 0}, {3, 7, -5, 2}, {3, 7, -5, 4}, {3, 7, -5, 6}, 
 
>       {3, 7, -5, 8}, {3, 7, -3, 0}, {3, 7, -3, 2}, {3, 7, -3, 4}, 
 
>       {3, 7, -3, 6}, {3, 7, -3, 8}, {3, 7, -1, -8}, {3, 7, -1, -6}, 
 
>       {3, 7, -1, -4}, {3, 7, -1, -2}, {3, 7, -1, 0}, {3, 7, 1, -8}, 
 
>       {3, 7, 1, -6}, {3, 7, 1, -4}, {3, 7, 1, -2}, {3, 7, 3, -8}, 
 
>       {3, 7, 3, -6}, {3, 7, 3, -4}, {3, 7, 5, -8}, {3, 7, 5, -6}, 
 
>       {3, 7, 5, -4}, {3, 7, 7, -8}, {3, 7, 7, -6}, {3, 7, 7, -4}, 
 
>       {5, -7, -1, 2}, {5, -7, -1, 4}, {5, -7, -1, 6}, {5, -7, -1, 8}, 
 
>       {5, -7, 1, 0}, {5, -7, 1, 2}, {5, -7, 1, 4}, {5, -7, 1, 6}, 
 
>       {5, -7, 1, 8}, {5, -7, 3, 0}, {5, -7, 3, 2}, {5, -7, 3, 4}, 
 
>       {5, -7, 3, 6}, {5, -7, 3, 8}, {5, -7, 5, 0}, {5, -7, 5, 2}, 
 
>       {5, -7, 5, 4}, {5, -7, 5, 6}, {5, -7, 5, 8}, {5, -7, 7, 0}, 
 
>       {5, -7, 7, 2}, {5, -7, 7, 4}, {5, -7, 7, 6}, {5, -7, 7, 8}, 
 
>       {5, -5, -1, 2}, {5, -5, -1, 4}, {5, -5, -1, 6}, {5, -5, -1, 8}, 
 
>       {5, -5, 1, 0}, {5, -5, 1, 2}, {5, -5, 1, 4}, {5, -5, 1, 6}, 
 
>       {5, -5, 1, 8}, {5, -5, 3, 0}, {5, -5, 3, 2}, {5, -5, 3, 4}, 
 
>       {5, -5, 3, 6}, {5, -5, 3, 8}, {5, -5, 5, 0}, {5, -5, 5, 2}, 
 
>       {5, -5, 5, 4}, {5, -5, 5, 6}, {5, -5, 5, 8}, {5, -5, 7, 0}, 
 
>       {5, -5, 7, 2}, {5, -5, 7, 4}, {5, -5, 7, 6}, {5, -5, 7, 8}, 
 
>       {5, -3, -1, 2}, {5, -3, -1, 4}, {5, -3, -1, 6}, {5, -3, -1, 8}, 
 
>       {5, -3, 1, 0}, {5, -3, 1, 2}, {5, -3, 1, 4}, {5, -3, 1, 6}, 
 
>       {5, -3, 1, 8}, {5, -3, 3, 0}, {5, -3, 3, 2}, {5, -3, 3, 4}, 
 
>       {5, -3, 3, 6}, {5, -3, 3, 8}, {5, -3, 5, 0}, {5, -3, 5, 2}, 
 
>       {5, -3, 7, 0}, {5, -3, 7, 2}, {5, -1, -7, 2}, {5, -1, -7, 4}, 
 
>       {5, -1, -7, 6}, {5, -1, -7, 8}, {5, -1, -5, 2}, {5, -1, -5, 4}, 
 
>       {5, -1, -5, 6}, {5, -1, -5, 8}, {5, -1, -3, 2}, {5, -1, -3, 4}, 
 
>       {5, -1, -3, 6}, {5, -1, -3, 8}, {5, -1, -1, 2}, {5, -1, -1, 4}, 
 
>       {5, -1, -1, 6}, {5, -1, -1, 8}, {5, -1, 1, -4}, {5, -1, 1, -2}, 
 
>       {5, -1, 1, 0}, {5, -1, 1, 2}, {5, -1, 1, 4}, {5, -1, 1, 6}, 
 
>       {5, -1, 1, 8}, {5, -1, 3, -8}, {5, -1, 3, -6}, {5, -1, 3, -4}, 
 
>       {5, -1, 3, -2}, {5, -1, 3, 0}, {5, -1, 5, -8}, {5, -1, 5, -6}, 
 
>       {5, -1, 5, -4}, {5, -1, 5, -2}, {5, -1, 5, 0}, {5, -1, 7, -8}, 
 
>       {5, -1, 7, -6}, {5, -1, 7, -4}, {5, -1, 7, -2}, {5, -1, 7, 0}, 
 
>       {5, 1, -7, 0}, {5, 1, -7, 2}, {5, 1, -7, 4}, {5, 1, -7, 6}, 
 
>       {5, 1, -7, 8}, {5, 1, -5, 0}, {5, 1, -5, 2}, {5, 1, -5, 4}, 
 
>       {5, 1, -5, 6}, {5, 1, -5, 8}, {5, 1, -3, 0}, {5, 1, -3, 2}, 
 
>       {5, 1, -3, 4}, {5, 1, -3, 6}, {5, 1, -3, 8}, {5, 1, -1, -4}, 
 
>       {5, 1, -1, -2}, {5, 1, -1, 0}, {5, 1, -1, 2}, {5, 1, -1, 4}, 
 
>       {5, 1, -1, 6}, {5, 1, -1, 8}, {5, 1, 1, -8}, {5, 1, 1, -6}, 
 
>       {5, 1, 1, -4}, {5, 1, 1, -2}, {5, 1, 3, -8}, {5, 1, 3, -6}, 
 
>       {5, 1, 3, -4}, {5, 1, 3, -2}, {5, 1, 5, -8}, {5, 1, 5, -6}, 
 
>       {5, 1, 5, -4}, {5, 1, 5, -2}, {5, 1, 7, -8}, {5, 1, 7, -6}, 
 
>       {5, 1, 7, -4}, {5, 1, 7, -2}, {5, 3, -7, 0}, {5, 3, -7, 2}, 
 
>       {5, 3, -7, 4}, {5, 3, -7, 6}, {5, 3, -7, 8}, {5, 3, -5, 0}, 
 
>       {5, 3, -5, 2}, {5, 3, -5, 4}, {5, 3, -5, 6}, {5, 3, -5, 8}, 
 
>       {5, 3, -3, 0}, {5, 3, -3, 2}, {5, 3, -3, 4}, {5, 3, -3, 6}, 
 
>       {5, 3, -3, 8}, {5, 3, -1, -8}, {5, 3, -1, -6}, {5, 3, -1, -4}, 
 
>       {5, 3, -1, -2}, {5, 3, -1, 0}, {5, 3, 1, -8}, {5, 3, 1, -6}, 
 
>       {5, 3, 1, -4}, {5, 3, 1, -2}, {5, 3, 3, -8}, {5, 3, 3, -6}, 
 
>       {5, 3, 3, -4}, {5, 3, 5, -8}, {5, 3, 5, -6}, {5, 3, 5, -4}, 
 
>       {5, 3, 7, -8}, {5, 3, 7, -6}, {5, 3, 7, -4}, {5, 5, -7, 0}, 
 
>       {5, 5, -7, 2}, {5, 5, -7, 4}, {5, 5, -7, 6}, {5, 5, -7, 8}, 
 
>       {5, 5, -5, 0}, {5, 5, -5, 2}, {5, 5, -5, 4}, {5, 5, -5, 6}, 
 
>       {5, 5, -5, 8}, {5, 5, -3, 0}, {5, 5, -3, 2}, {5, 5, -1, -8}, 
 
>       {5, 5, -1, -6}, {5, 5, -1, -4}, {5, 5, -1, -2}, {5, 5, -1, 0}, 
 
>       {5, 5, 1, -8}, {5, 5, 1, -6}, {5, 5, 1, -4}, {5, 5, 1, -2}, 
 
>       {5, 5, 3, -8}, {5, 5, 3, -6}, {5, 5, 3, -4}, {5, 5, 5, -8}, 
 
>       {5, 5, 5, -6}, {5, 5, 7, -8}, {5, 5, 7, -6}, {5, 7, -7, 0}, 
 
>       {5, 7, -7, 2}, {5, 7, -7, 4}, {5, 7, -7, 6}, {5, 7, -7, 8}, 
 
>       {5, 7, -5, 0}, {5, 7, -5, 2}, {5, 7, -5, 4}, {5, 7, -5, 6}, 
 
>       {5, 7, -5, 8}, {5, 7, -3, 0}, {5, 7, -3, 2}, {5, 7, -1, -8}, 
 
>       {5, 7, -1, -6}, {5, 7, -1, -4}, {5, 7, -1, -2}, {5, 7, -1, 0}, 
 
>       {5, 7, 1, -8}, {5, 7, 1, -6}, {5, 7, 1, -4}, {5, 7, 1, -2}, 
 
>       {5, 7, 3, -8}, {5, 7, 3, -6}, {5, 7, 3, -4}, {5, 7, 5, -8}, 
 
>       {5, 7, 5, -6}, {5, 7, 7, -8}, {5, 7, 7, -6}, {7, -7, -1, 2}, 
 
>       {7, -7, -1, 4}, {7, -7, -1, 6}, {7, -7, -1, 8}, {7, -7, 1, 0}, 
 
>       {7, -7, 1, 2}, {7, -7, 1, 4}, {7, -7, 1, 6}, {7, -7, 1, 8}, 
 
>       {7, -7, 3, 0}, {7, -7, 3, 2}, {7, -7, 3, 4}, {7, -7, 3, 6}, 
 
>       {7, -7, 3, 8}, {7, -7, 5, 0}, {7, -7, 5, 2}, {7, -7, 5, 4}, 
 
>       {7, -7, 5, 6}, {7, -7, 5, 8}, {7, -7, 7, 0}, {7, -7, 7, 2}, 
 
>       {7, -7, 7, 4}, {7, -7, 7, 6}, {7, -7, 7, 8}, {7, -5, -1, 2}, 
 
>       {7, -5, -1, 4}, {7, -5, -1, 6}, {7, -5, -1, 8}, {7, -5, 1, 0}, 
 
>       {7, -5, 1, 2}, {7, -5, 1, 4}, {7, -5, 1, 6}, {7, -5, 1, 8}, 
 
>       {7, -5, 3, 0}, {7, -5, 3, 2}, {7, -5, 3, 4}, {7, -5, 3, 6}, 
 
>       {7, -5, 3, 8}, {7, -5, 5, 0}, {7, -5, 5, 2}, {7, -5, 5, 4}, 
 
>       {7, -5, 5, 6}, {7, -5, 5, 8}, {7, -5, 7, 0}, {7, -5, 7, 2}, 
 
>       {7, -5, 7, 4}, {7, -3, -1, 2}, {7, -3, -1, 4}, {7, -3, -1, 6}, 
 
>       {7, -3, -1, 8}, {7, -3, 1, 0}, {7, -3, 1, 2}, {7, -3, 1, 4}, 
 
>       {7, -3, 1, 6}, {7, -3, 1, 8}, {7, -3, 3, 0}, {7, -3, 3, 2}, 
 
>       {7, -3, 3, 4}, {7, -3, 3, 6}, {7, -3, 3, 8}, {7, -3, 5, 0}, 
 
>       {7, -3, 5, 2}, {7, -3, 7, 0}, {7, -3, 7, 2}, {7, -1, -7, 2}, 
 
>       {7, -1, -7, 4}, {7, -1, -7, 6}, {7, -1, -7, 8}, {7, -1, -5, 2}, 
 
>       {7, -1, -5, 4}, {7, -1, -5, 6}, {7, -1, -5, 8}, {7, -1, -3, 2}, 
 
>       {7, -1, -3, 4}, {7, -1, -3, 6}, {7, -1, -3, 8}, {7, -1, -1, 2}, 
 
>       {7, -1, -1, 4}, {7, -1, -1, 6}, {7, -1, -1, 8}, {7, -1, 1, -6}, 
 
>       {7, -1, 1, -4}, {7, -1, 1, -2}, {7, -1, 1, 0}, {7, -1, 1, 2}, 
 
>       {7, -1, 1, 4}, {7, -1, 1, 6}, {7, -1, 1, 8}, {7, -1, 3, -8}, 
 
>       {7, -1, 3, -6}, {7, -1, 3, -4}, {7, -1, 3, -2}, {7, -1, 3, 0}, 
 
>       {7, -1, 5, -8}, {7, -1, 5, -6}, {7, -1, 5, -4}, {7, -1, 5, -2}, 
 
>       {7, -1, 5, 0}, {7, -1, 7, -8}, {7, -1, 7, -6}, {7, -1, 7, -4}, 
 
>       {7, -1, 7, -2}, {7, -1, 7, 0}, {7, 1, -7, 0}, {7, 1, -7, 2}, 
 
>       {7, 1, -7, 4}, {7, 1, -7, 6}, {7, 1, -7, 8}, {7, 1, -5, 0}, 
 
>       {7, 1, -5, 2}, {7, 1, -5, 4}, {7, 1, -5, 6}, {7, 1, -5, 8}, 
 
>       {7, 1, -3, 0}, {7, 1, -3, 2}, {7, 1, -3, 4}, {7, 1, -3, 6}, 
 
>       {7, 1, -3, 8}, {7, 1, -1, -6}, {7, 1, -1, -4}, {7, 1, -1, -2}, 
 
>       {7, 1, -1, 0}, {7, 1, -1, 2}, {7, 1, -1, 4}, {7, 1, -1, 6}, 
 
>       {7, 1, -1, 8}, {7, 1, 1, -8}, {7, 1, 1, -6}, {7, 1, 1, -4}, 
 
>       {7, 1, 1, -2}, {7, 1, 3, -8}, {7, 1, 3, -6}, {7, 1, 3, -4}, 
 
>       {7, 1, 3, -2}, {7, 1, 5, -8}, {7, 1, 5, -6}, {7, 1, 5, -4}, 
 
>       {7, 1, 5, -2}, {7, 1, 7, -8}, {7, 1, 7, -6}, {7, 1, 7, -4}, 
 
>       {7, 1, 7, -2}, {7, 3, -7, 0}, {7, 3, -7, 2}, {7, 3, -7, 4}, 
 
>       {7, 3, -7, 6}, {7, 3, -7, 8}, {7, 3, -5, 0}, {7, 3, -5, 2}, 
 
>       {7, 3, -5, 4}, {7, 3, -5, 6}, {7, 3, -5, 8}, {7, 3, -3, 0}, 
 
>       {7, 3, -3, 2}, {7, 3, -3, 4}, {7, 3, -3, 6}, {7, 3, -3, 8}, 
 
>       {7, 3, -1, -8}, {7, 3, -1, -6}, {7, 3, -1, -4}, {7, 3, -1, -2}, 
 
>       {7, 3, -1, 0}, {7, 3, 1, -8}, {7, 3, 1, -6}, {7, 3, 1, -4}, 
 
>       {7, 3, 1, -2}, {7, 3, 3, -8}, {7, 3, 3, -6}, {7, 3, 3, -4}, 
 
>       {7, 3, 5, -8}, {7, 3, 5, -6}, {7, 3, 5, -4}, {7, 3, 7, -8}, 
 
>       {7, 3, 7, -6}, {7, 3, 7, -4}, {7, 5, -7, 0}, {7, 5, -7, 2}, 
 
>       {7, 5, -7, 4}, {7, 5, -7, 6}, {7, 5, -7, 8}, {7, 5, -5, 0}, 
 
>       {7, 5, -5, 2}, {7, 5, -5, 4}, {7, 5, -5, 6}, {7, 5, -5, 8}, 
 
>       {7, 5, -3, 0}, {7, 5, -3, 2}, {7, 5, -1, -8}, {7, 5, -1, -6}, 
 
>       {7, 5, -1, -4}, {7, 5, -1, -2}, {7, 5, -1, 0}, {7, 5, 1, -8}, 
 
>       {7, 5, 1, -6}, {7, 5, 1, -4}, {7, 5, 1, -2}, {7, 5, 3, -8}, 
 
>       {7, 5, 3, -6}, {7, 5, 3, -4}, {7, 5, 5, -8}, {7, 5, 5, -6}, 
 
>       {7, 5, 7, -8}, {7, 5, 7, -6}, {7, 7, -7, 0}, {7, 7, -7, 2}, 
 
>       {7, 7, -7, 4}, {7, 7, -7, 6}, {7, 7, -7, 8}, {7, 7, -5, 0}, 
 
>       {7, 7, -5, 2}, {7, 7, -5, 4}, {7, 7, -3, 0}, {7, 7, -3, 2}, 
 
>       {7, 7, -1, -8}, {7, 7, -1, -6}, {7, 7, -1, -4}, {7, 7, -1, -2}, 
 
>       {7, 7, -1, 0}, {7, 7, 1, -8}, {7, 7, 1, -6}, {7, 7, 1, -4}, 
 
>       {7, 7, 1, -2}, {7, 7, 3, -8}, {7, 7, 3, -6}, {7, 7, 3, -4}, 
 
>       {7, 7, 5, -8}, {7, 7, 5, -6}, {7, 7, 7, -8}}, 
 
>      {{-7, -7, -7, 8}, {-7, -7, -5, 6}, {-7, -7, -5, 8}, {-7, -7, -3, 4}, 
 
>       {-7, -7, -3, 6}, {-7, -7, -3, 8}, {-7, -7, -1, 2}, {-7, -7, -1, 4}, 
 
>       {-7, -7, -1, 6}, {-7, -7, -1, 8}, {-7, -7, 1, 0}, {-7, -7, 1, 2}, 
 
>       {-7, -7, 1, 4}, {-7, -7, 1, 6}, {-7, -7, 1, 8}, {-7, -7, 3, -2}, 
 
>       {-7, -7, 3, 0}, {-7, -7, 5, -4}, {-7, -7, 5, -2}, {-7, -7, 5, 0}, 
 
>       {-7, -7, 7, -8}, {-7, -7, 7, -6}, {-7, -7, 7, -4}, {-7, -7, 7, -2}, 
 
>       {-7, -7, 7, 0}, {-7, -5, -7, 6}, {-7, -5, -7, 8}, {-7, -5, -5, 6}, 
 
>       {-7, -5, -5, 8}, {-7, -5, -3, 4}, {-7, -5, -3, 6}, {-7, -5, -3, 8}, 
 
>       {-7, -5, -1, 2}, {-7, -5, -1, 4}, {-7, -5, -1, 6}, {-7, -5, -1, 8}, 
 
>       {-7, -5, 1, 0}, {-7, -5, 1, 2}, {-7, -5, 1, 4}, {-7, -5, 1, 6}, 
 
>       {-7, -5, 1, 8}, {-7, -5, 3, -2}, {-7, -5, 3, 0}, {-7, -5, 5, -8}, 
 
>       {-7, -5, 5, -6}, {-7, -5, 5, -4}, {-7, -5, 5, -2}, {-7, -5, 5, 0}, 
 
>       {-7, -5, 7, -8}, {-7, -5, 7, -6}, {-7, -5, 7, -4}, {-7, -5, 7, -2}, 
 
>       {-7, -5, 7, 0}, {-7, -3, -7, 4}, {-7, -3, -7, 6}, {-7, -3, -7, 8}, 
 
>       {-7, -3, -5, 4}, {-7, -3, -5, 6}, {-7, -3, -5, 8}, {-7, -3, -3, 4}, 
 
>       {-7, -3, -3, 6}, {-7, -3, -3, 8}, {-7, -3, -1, 2}, {-7, -3, -1, 4}, 
 
>       {-7, -3, -1, 6}, {-7, -3, -1, 8}, {-7, -3, 1, 0}, {-7, -3, 1, 2}, 
 
>       {-7, -3, 1, 4}, {-7, -3, 1, 6}, {-7, -3, 1, 8}, {-7, -3, 3, -8}, 
 
>       {-7, -3, 3, -6}, {-7, -3, 3, -4}, {-7, -3, 3, -2}, {-7, -3, 3, 0}, 
 
>       {-7, -3, 5, -8}, {-7, -3, 5, -6}, {-7, -3, 5, -4}, {-7, -3, 5, -2}, 
 
>       {-7, -3, 5, 0}, {-7, -3, 7, -8}, {-7, -3, 7, -6}, {-7, -3, 7, -4}, 
 
>       {-7, -3, 7, -2}, {-7, -3, 7, 0}, {-7, -1, -7, 2}, {-7, -1, -7, 4}, 
 
>       {-7, -1, -7, 6}, {-7, -1, -7, 8}, {-7, -1, -5, 2}, {-7, -1, -5, 4}, 
 
>       {-7, -1, -5, 6}, {-7, -1, -5, 8}, {-7, -1, -3, 2}, {-7, -1, -3, 4}, 
 
>       {-7, -1, -3, 6}, {-7, -1, -3, 8}, {-7, -1, -1, 2}, {-7, -1, -1, 4}, 
 
>       {-7, -1, -1, 6}, {-7, -1, -1, 8}, {-7, -1, 1, -8}, {-7, -1, 1, -6}, 
 
>       {-7, -1, 1, -4}, {-7, -1, 1, -2}, {-7, -1, 1, 0}, {-7, -1, 1, 2}, 
 
>       {-7, -1, 1, 4}, {-7, -1, 1, 6}, {-7, -1, 3, -8}, {-7, -1, 3, -6}, 
 
>       {-7, -1, 3, -4}, {-7, -1, 3, -2}, {-7, -1, 3, 0}, {-7, -1, 5, -8}, 
 
>       {-7, -1, 5, -6}, {-7, -1, 5, -4}, {-7, -1, 5, -2}, {-7, -1, 5, 0}, 
 
>       {-7, -1, 7, -8}, {-7, -1, 7, -6}, {-7, -1, 7, -4}, {-7, -1, 7, -2}, 
 
>       {-7, -1, 7, 0}, {-7, 1, -7, 0}, {-7, 1, -7, 2}, {-7, 1, -7, 4}, 
 
>       {-7, 1, -7, 6}, {-7, 1, -7, 8}, {-7, 1, -5, 0}, {-7, 1, -5, 2}, 
 
>       {-7, 1, -5, 4}, {-7, 1, -5, 6}, {-7, 1, -5, 8}, {-7, 1, -3, 0}, 
 
>       {-7, 1, -3, 2}, {-7, 1, -3, 4}, {-7, 1, -3, 6}, {-7, 1, -3, 8}, 
 
>       {-7, 1, -1, -8}, {-7, 1, -1, -6}, {-7, 1, -1, -4}, {-7, 1, -1, -2}, 
 
>       {-7, 1, -1, 0}, {-7, 1, -1, 2}, {-7, 1, -1, 4}, {-7, 1, -1, 6}, 
 
>       {-7, 1, 1, -8}, {-7, 1, 1, -6}, {-7, 1, 1, -4}, {-7, 1, 1, -2}, 
 
>       {-7, 1, 3, -8}, {-7, 1, 3, -6}, {-7, 1, 3, -4}, {-7, 1, 3, -2}, 
 
>       {-7, 1, 5, -8}, {-7, 1, 5, -6}, {-7, 1, 5, -4}, {-7, 1, 5, -2}, 
 
>       {-7, 1, 7, -8}, {-7, 1, 7, -6}, {-7, 1, 7, -4}, {-7, 1, 7, -2}, 
 
>       {-7, 3, -7, -2}, {-7, 3, -7, 0}, {-7, 3, -5, -2}, {-7, 3, -5, 0}, 
 
>       {-7, 3, -3, -8}, {-7, 3, -3, -6}, {-7, 3, -3, -4}, {-7, 3, -3, -2}, 
 
>       {-7, 3, -3, 0}, {-7, 3, -1, -8}, {-7, 3, -1, -6}, {-7, 3, -1, -4}, 
 
>       {-7, 3, -1, -2}, {-7, 3, -1, 0}, {-7, 3, 1, -8}, {-7, 3, 1, -6}, 
 
>       {-7, 3, 1, -4}, {-7, 3, 1, -2}, {-7, 5, -7, -4}, {-7, 5, -7, -2}, 
 
>       {-7, 5, -7, 0}, {-7, 5, -5, -8}, {-7, 5, -5, -6}, {-7, 5, -5, -4}, 
 
>       {-7, 5, -5, -2}, {-7, 5, -5, 0}, {-7, 5, -3, -8}, {-7, 5, -3, -6}, 
 
>       {-7, 5, -3, -4}, {-7, 5, -3, -2}, {-7, 5, -3, 0}, {-7, 5, -1, -8}, 
 
>       {-7, 5, -1, -6}, {-7, 5, -1, -4}, {-7, 5, -1, -2}, {-7, 5, -1, 0}, 
 
>       {-7, 5, 1, -8}, {-7, 5, 1, -6}, {-7, 5, 1, -4}, {-7, 5, 1, -2}, 
 
>       {-7, 7, -7, -8}, {-7, 7, -7, -6}, {-7, 7, -7, -4}, {-7, 7, -7, -2}, 
 
>       {-7, 7, -7, 0}, {-7, 7, -5, -8}, {-7, 7, -5, -6}, {-7, 7, -5, -4}, 
 
>       {-7, 7, -5, -2}, {-7, 7, -5, 0}, {-7, 7, -3, -8}, {-7, 7, -3, -6}, 
 
>       {-7, 7, -3, -4}, {-7, 7, -3, -2}, {-7, 7, -3, 0}, {-7, 7, -1, -8}, 
 
>       {-7, 7, -1, -6}, {-7, 7, -1, -4}, {-7, 7, -1, -2}, {-7, 7, -1, 0}, 
 
>       {-7, 7, 1, -8}, {-7, 7, 1, -6}, {-7, 7, 1, -4}, {-7, 7, 1, -2}, 
 
>       {-5, -7, -7, 6}, {-5, -7, -7, 8}, {-5, -7, -5, 6}, {-5, -7, -5, 8}, 
 
>       {-5, -7, -3, 4}, {-5, -7, -3, 6}, {-5, -7, -3, 8}, {-5, -7, -1, 2}, 
 
>       {-5, -7, -1, 4}, {-5, -7, -1, 6}, {-5, -7, -1, 8}, {-5, -7, 1, 0}, 
 
>       {-5, -7, 1, 2}, {-5, -7, 1, 4}, {-5, -7, 1, 6}, {-5, -7, 1, 8}, 
 
>       {-5, -7, 3, -2}, {-5, -7, 3, 0}, {-5, -7, 5, -8}, {-5, -7, 5, -6}, 
 
>       {-5, -7, 5, -4}, {-5, -7, 5, -2}, {-5, -7, 5, 0}, {-5, -7, 7, -8}, 
 
>       {-5, -7, 7, -6}, {-5, -7, 7, -4}, {-5, -7, 7, -2}, {-5, -7, 7, 0}, 
 
>       {-5, -5, -7, 6}, {-5, -5, -7, 8}, {-5, -5, -5, 6}, {-5, -5, -5, 8}, 
 
>       {-5, -5, -3, 4}, {-5, -5, -3, 6}, {-5, -5, -3, 8}, {-5, -5, -1, 2}, 
 
>       {-5, -5, -1, 4}, {-5, -5, -1, 6}, {-5, -5, -1, 8}, {-5, -5, 1, 0}, 
 
>       {-5, -5, 1, 2}, {-5, -5, 1, 4}, {-5, -5, 1, 6}, {-5, -5, 1, 8}, 
 
>       {-5, -5, 3, -2}, {-5, -5, 3, 0}, {-5, -5, 5, -8}, {-5, -5, 5, -6}, 
 
>       {-5, -5, 5, -4}, {-5, -5, 5, -2}, {-5, -5, 5, 0}, {-5, -5, 7, -8}, 
 
>       {-5, -5, 7, -6}, {-5, -5, 7, -4}, {-5, -5, 7, -2}, {-5, -5, 7, 0}, 
 
>       {-5, -3, -7, 4}, {-5, -3, -7, 6}, {-5, -3, -7, 8}, {-5, -3, -5, 4}, 
 
>       {-5, -3, -5, 6}, {-5, -3, -5, 8}, {-5, -3, -3, 4}, {-5, -3, -3, 6}, 
 
>       {-5, -3, -3, 8}, {-5, -3, -1, 2}, {-5, -3, -1, 4}, {-5, -3, -1, 6}, 
 
>       {-5, -3, -1, 8}, {-5, -3, 1, 0}, {-5, -3, 1, 2}, {-5, -3, 1, 4}, 
 
>       {-5, -3, 1, 6}, {-5, -3, 1, 8}, {-5, -3, 3, -8}, {-5, -3, 3, -6}, 
 
>       {-5, -3, 3, -4}, {-5, -3, 3, -2}, {-5, -3, 3, 0}, {-5, -3, 5, -8}, 
 
>       {-5, -3, 5, -6}, {-5, -3, 5, -4}, {-5, -3, 5, -2}, {-5, -3, 5, 0}, 
 
>       {-5, -3, 7, -8}, {-5, -3, 7, -6}, {-5, -3, 7, -4}, {-5, -3, 7, -2}, 
 
>       {-5, -3, 7, 0}, {-5, -1, -7, 2}, {-5, -1, -7, 4}, {-5, -1, -7, 6}, 
 
>       {-5, -1, -7, 8}, {-5, -1, -5, 2}, {-5, -1, -5, 4}, {-5, -1, -5, 6}, 
 
>       {-5, -1, -5, 8}, {-5, -1, -3, 2}, {-5, -1, -3, 4}, {-5, -1, -3, 6}, 
 
>       {-5, -1, -3, 8}, {-5, -1, -1, 2}, {-5, -1, -1, 4}, {-5, -1, -1, 6}, 
 
>       {-5, -1, -1, 8}, {-5, -1, 1, -8}, {-5, -1, 1, -6}, {-5, -1, 1, -4}, 
 
>       {-5, -1, 1, -2}, {-5, -1, 1, 0}, {-5, -1, 1, 2}, {-5, -1, 1, 4}, 
 
>       {-5, -1, 3, -8}, {-5, -1, 3, -6}, {-5, -1, 3, -4}, {-5, -1, 3, -2}, 
 
>       {-5, -1, 3, 0}, {-5, -1, 5, -8}, {-5, -1, 5, -6}, {-5, -1, 5, -4}, 
 
>       {-5, -1, 5, -2}, {-5, -1, 5, 0}, {-5, -1, 7, -8}, {-5, -1, 7, -6}, 
 
>       {-5, -1, 7, -4}, {-5, -1, 7, -2}, {-5, -1, 7, 0}, {-5, 1, -7, 0}, 
 
>       {-5, 1, -7, 2}, {-5, 1, -7, 4}, {-5, 1, -7, 6}, {-5, 1, -7, 8}, 
 
>       {-5, 1, -5, 0}, {-5, 1, -5, 2}, {-5, 1, -5, 4}, {-5, 1, -5, 6}, 
 
>       {-5, 1, -5, 8}, {-5, 1, -3, 0}, {-5, 1, -3, 2}, {-5, 1, -3, 4}, 
 
>       {-5, 1, -3, 6}, {-5, 1, -3, 8}, {-5, 1, -1, -8}, {-5, 1, -1, -6}, 
 
>       {-5, 1, -1, -4}, {-5, 1, -1, -2}, {-5, 1, -1, 0}, {-5, 1, -1, 2}, 
 
>       {-5, 1, -1, 4}, {-5, 1, 1, -8}, {-5, 1, 1, -6}, {-5, 1, 1, -4}, 
 
>       {-5, 1, 1, -2}, {-5, 1, 3, -8}, {-5, 1, 3, -6}, {-5, 1, 3, -4}, 
 
>       {-5, 1, 3, -2}, {-5, 1, 5, -8}, {-5, 1, 5, -6}, {-5, 1, 5, -4}, 
 
>       {-5, 1, 5, -2}, {-5, 1, 7, -8}, {-5, 1, 7, -6}, {-5, 1, 7, -4}, 
 
>       {-5, 1, 7, -2}, {-5, 3, -7, -2}, {-5, 3, -7, 0}, {-5, 3, -5, -2}, 
 
>       {-5, 3, -5, 0}, {-5, 3, -3, -8}, {-5, 3, -3, -6}, {-5, 3, -3, -4}, 
 
>       {-5, 3, -3, -2}, {-5, 3, -3, 0}, {-5, 3, -1, -8}, {-5, 3, -1, -6}, 
 
>       {-5, 3, -1, -4}, {-5, 3, -1, -2}, {-5, 3, -1, 0}, {-5, 3, 1, -8}, 
 
>       {-5, 3, 1, -6}, {-5, 3, 1, -4}, {-5, 3, 1, -2}, {-5, 5, -7, -8}, 
 
>       {-5, 5, -7, -6}, {-5, 5, -7, -4}, {-5, 5, -7, -2}, {-5, 5, -7, 0}, 
 
>       {-5, 5, -5, -8}, {-5, 5, -5, -6}, {-5, 5, -5, -4}, {-5, 5, -5, -2}, 
 
>       {-5, 5, -5, 0}, {-5, 5, -3, -8}, {-5, 5, -3, -6}, {-5, 5, -3, -4}, 
 
>       {-5, 5, -3, -2}, {-5, 5, -3, 0}, {-5, 5, -1, -8}, {-5, 5, -1, -6}, 
 
>       {-5, 5, -1, -4}, {-5, 5, -1, -2}, {-5, 5, -1, 0}, {-5, 5, 1, -8}, 
 
>       {-5, 5, 1, -6}, {-5, 5, 1, -4}, {-5, 5, 1, -2}, {-5, 7, -7, -8}, 
 
>       {-5, 7, -7, -6}, {-5, 7, -7, -4}, {-5, 7, -7, -2}, {-5, 7, -7, 0}, 
 
>       {-5, 7, -5, -8}, {-5, 7, -5, -6}, {-5, 7, -5, -4}, {-5, 7, -5, -2}, 
 
>       {-5, 7, -5, 0}, {-5, 7, -3, -8}, {-5, 7, -3, -6}, {-5, 7, -3, -4}, 
 
>       {-5, 7, -3, -2}, {-5, 7, -3, 0}, {-5, 7, -1, -8}, {-5, 7, -1, -6}, 
 
>       {-5, 7, -1, -4}, {-5, 7, -1, -2}, {-5, 7, -1, 0}, {-5, 7, 1, -8}, 
 
>       {-5, 7, 1, -6}, {-5, 7, 1, -4}, {-5, 7, 1, -2}, {-3, -7, -7, 4}, 
 
>       {-3, -7, -7, 6}, {-3, -7, -7, 8}, {-3, -7, -5, 4}, {-3, -7, -5, 6}, 
 
>       {-3, -7, -5, 8}, {-3, -7, -3, 4}, {-3, -7, -3, 6}, {-3, -7, -3, 8}, 
 
>       {-3, -7, -1, 2}, {-3, -7, -1, 4}, {-3, -7, -1, 6}, {-3, -7, -1, 8}, 
 
>       {-3, -7, 1, 0}, {-3, -7, 1, 2}, {-3, -7, 1, 4}, {-3, -7, 1, 6}, 
 
>       {-3, -7, 1, 8}, {-3, -7, 3, -8}, {-3, -7, 3, -6}, {-3, -7, 3, -4}, 
 
>       {-3, -7, 3, -2}, {-3, -7, 3, 0}, {-3, -7, 5, -8}, {-3, -7, 5, -6}, 
 
>       {-3, -7, 5, -4}, {-3, -7, 5, -2}, {-3, -7, 5, 0}, {-3, -7, 7, -8}, 
 
>       {-3, -7, 7, -6}, {-3, -7, 7, -4}, {-3, -7, 7, -2}, {-3, -7, 7, 0}, 
 
>       {-3, -5, -7, 4}, {-3, -5, -7, 6}, {-3, -5, -7, 8}, {-3, -5, -5, 4}, 
 
>       {-3, -5, -5, 6}, {-3, -5, -5, 8}, {-3, -5, -3, 4}, {-3, -5, -3, 6}, 
 
>       {-3, -5, -3, 8}, {-3, -5, -1, 2}, {-3, -5, -1, 4}, {-3, -5, -1, 6}, 
 
>       {-3, -5, -1, 8}, {-3, -5, 1, 0}, {-3, -5, 1, 2}, {-3, -5, 1, 4}, 
 
>       {-3, -5, 1, 6}, {-3, -5, 1, 8}, {-3, -5, 3, -8}, {-3, -5, 3, -6}, 
 
>       {-3, -5, 3, -4}, {-3, -5, 3, -2}, {-3, -5, 3, 0}, {-3, -5, 5, -8}, 
 
>       {-3, -5, 5, -6}, {-3, -5, 5, -4}, {-3, -5, 5, -2}, {-3, -5, 5, 0}, 
 
>       {-3, -5, 7, -8}, {-3, -5, 7, -6}, {-3, -5, 7, -4}, {-3, -5, 7, -2}, 
 
>       {-3, -5, 7, 0}, {-3, -3, -7, 4}, {-3, -3, -7, 6}, {-3, -3, -7, 8}, 
 
>       {-3, -3, -5, 4}, {-3, -3, -5, 6}, {-3, -3, -5, 8}, {-3, -3, -3, 4}, 
 
>       {-3, -3, -3, 6}, {-3, -3, -3, 8}, {-3, -3, -1, 2}, {-3, -3, -1, 4}, 
 
>       {-3, -3, -1, 6}, {-3, -3, -1, 8}, {-3, -3, 1, 0}, {-3, -3, 1, 2}, 
 
>       {-3, -3, 1, 4}, {-3, -3, 1, 6}, {-3, -3, 1, 8}, {-3, -3, 3, -8}, 
 
>       {-3, -3, 3, -6}, {-3, -3, 3, -4}, {-3, -3, 3, -2}, {-3, -3, 3, 0}, 
 
>       {-3, -3, 5, -8}, {-3, -3, 5, -6}, {-3, -3, 5, -4}, {-3, -3, 5, -2}, 
 
>       {-3, -3, 5, 0}, {-3, -3, 7, -8}, {-3, -3, 7, -6}, {-3, -3, 7, -4}, 
 
>       {-3, -3, 7, -2}, {-3, -3, 7, 0}, {-3, -1, -7, 2}, {-3, -1, -7, 4}, 
 
>       {-3, -1, -7, 6}, {-3, -1, -7, 8}, {-3, -1, -5, 2}, {-3, -1, -5, 4}, 
 
>       {-3, -1, -5, 6}, {-3, -1, -5, 8}, {-3, -1, -3, 2}, {-3, -1, -3, 4}, 
 
>       {-3, -1, -3, 6}, {-3, -1, -3, 8}, {-3, -1, -1, 2}, {-3, -1, -1, 4}, 
 
>       {-3, -1, -1, 6}, {-3, -1, -1, 8}, {-3, -1, 1, -8}, {-3, -1, 1, -6}, 
 
>       {-3, -1, 1, -4}, {-3, -1, 1, -2}, {-3, -1, 1, 0}, {-3, -1, 1, 2}, 
 
>       {-3, -1, 3, -8}, {-3, -1, 3, -6}, {-3, -1, 3, -4}, {-3, -1, 3, -2}, 
 
>       {-3, -1, 3, 0}, {-3, -1, 5, -8}, {-3, -1, 5, -6}, {-3, -1, 5, -4}, 
 
>       {-3, -1, 5, -2}, {-3, -1, 5, 0}, {-3, -1, 7, -8}, {-3, -1, 7, -6}, 
 
>       {-3, -1, 7, -4}, {-3, -1, 7, -2}, {-3, -1, 7, 0}, {-3, 1, -7, 0}, 
 
>       {-3, 1, -7, 2}, {-3, 1, -7, 4}, {-3, 1, -7, 6}, {-3, 1, -7, 8}, 
 
>       {-3, 1, -5, 0}, {-3, 1, -5, 2}, {-3, 1, -5, 4}, {-3, 1, -5, 6}, 
 
>       {-3, 1, -5, 8}, {-3, 1, -3, 0}, {-3, 1, -3, 2}, {-3, 1, -3, 4}, 
 
>       {-3, 1, -3, 6}, {-3, 1, -3, 8}, {-3, 1, -1, -8}, {-3, 1, -1, -6}, 
 
>       {-3, 1, -1, -4}, {-3, 1, -1, -2}, {-3, 1, -1, 0}, {-3, 1, -1, 2}, 
 
>       {-3, 1, 1, -8}, {-3, 1, 1, -6}, {-3, 1, 1, -4}, {-3, 1, 1, -2}, 
 
>       {-3, 1, 3, -8}, {-3, 1, 3, -6}, {-3, 1, 3, -4}, {-3, 1, 3, -2}, 
 
>       {-3, 1, 5, -8}, {-3, 1, 5, -6}, {-3, 1, 5, -4}, {-3, 1, 5, -2}, 
 
>       {-3, 1, 7, -8}, {-3, 1, 7, -6}, {-3, 1, 7, -4}, {-3, 1, 7, -2}, 
 
>       {-3, 3, -7, -8}, {-3, 3, -7, -6}, {-3, 3, -7, -4}, {-3, 3, -7, -2}, 
 
>       {-3, 3, -7, 0}, {-3, 3, -5, -8}, {-3, 3, -5, -6}, {-3, 3, -5, -4}, 
 
>       {-3, 3, -5, -2}, {-3, 3, -5, 0}, {-3, 3, -3, -8}, {-3, 3, -3, -6}, 
 
>       {-3, 3, -3, -4}, {-3, 3, -3, -2}, {-3, 3, -3, 0}, {-3, 3, -1, -8}, 
 
>       {-3, 3, -1, -6}, {-3, 3, -1, -4}, {-3, 3, -1, -2}, {-3, 3, -1, 0}, 
 
>       {-3, 3, 1, -8}, {-3, 3, 1, -6}, {-3, 3, 1, -4}, {-3, 3, 1, -2}, 
 
>       {-3, 5, -7, -8}, {-3, 5, -7, -6}, {-3, 5, -7, -4}, {-3, 5, -7, -2}, 
 
>       {-3, 5, -7, 0}, {-3, 5, -5, -8}, {-3, 5, -5, -6}, {-3, 5, -5, -4}, 
 
>       {-3, 5, -5, -2}, {-3, 5, -5, 0}, {-3, 5, -3, -8}, {-3, 5, -3, -6}, 
 
>       {-3, 5, -3, -4}, {-3, 5, -3, -2}, {-3, 5, -3, 0}, {-3, 5, -1, -8}, 
 
>       {-3, 5, -1, -6}, {-3, 5, -1, -4}, {-3, 5, -1, -2}, {-3, 5, -1, 0}, 
 
>       {-3, 5, 1, -8}, {-3, 5, 1, -6}, {-3, 5, 1, -4}, {-3, 5, 1, -2}, 
 
>       {-3, 7, -7, -8}, {-3, 7, -7, -6}, {-3, 7, -7, -4}, {-3, 7, -7, -2}, 
 
>       {-3, 7, -7, 0}, {-3, 7, -5, -8}, {-3, 7, -5, -6}, {-3, 7, -5, -4}, 
 
>       {-3, 7, -5, -2}, {-3, 7, -5, 0}, {-3, 7, -3, -8}, {-3, 7, -3, -6}, 
 
>       {-3, 7, -3, -4}, {-3, 7, -3, -2}, {-3, 7, -3, 0}, {-3, 7, -1, -8}, 
 
>       {-3, 7, -1, -6}, {-3, 7, -1, -4}, {-3, 7, -1, -2}, {-3, 7, -1, 0}, 
 
>       {-3, 7, 1, -8}, {-3, 7, 1, -6}, {-3, 7, 1, -4}, {-3, 7, 1, -2}, 
 
>       {-1, -7, -7, 2}, {-1, -7, -7, 4}, {-1, -7, -7, 6}, {-1, -7, -7, 8}, 
 
>       {-1, -7, -5, 2}, {-1, -7, -5, 4}, {-1, -7, -5, 6}, {-1, -7, -5, 8}, 
 
>       {-1, -7, -3, 2}, {-1, -7, -3, 4}, {-1, -7, -3, 6}, {-1, -7, -3, 8}, 
 
>       {-1, -7, -1, 2}, {-1, -7, -1, 4}, {-1, -7, -1, 6}, {-1, -7, -1, 8}, 
 
>       {-1, -7, 1, -8}, {-1, -7, 1, -6}, {-1, -7, 1, -4}, {-1, -7, 1, -2}, 
 
>       {-1, -7, 1, 0}, {-1, -7, 1, 2}, {-1, -7, 1, 4}, {-1, -7, 1, 6}, 
 
>       {-1, -7, 3, -8}, {-1, -7, 3, -6}, {-1, -7, 3, -4}, {-1, -7, 3, -2}, 
 
>       {-1, -7, 3, 0}, {-1, -7, 5, -8}, {-1, -7, 5, -6}, {-1, -7, 5, -4}, 
 
>       {-1, -7, 5, -2}, {-1, -7, 5, 0}, {-1, -7, 7, -8}, {-1, -7, 7, -6}, 
 
>       {-1, -7, 7, -4}, {-1, -7, 7, -2}, {-1, -7, 7, 0}, {-1, -5, -7, 2}, 
 
>       {-1, -5, -7, 4}, {-1, -5, -7, 6}, {-1, -5, -7, 8}, {-1, -5, -5, 2}, 
 
>       {-1, -5, -5, 4}, {-1, -5, -5, 6}, {-1, -5, -5, 8}, {-1, -5, -3, 2}, 
 
>       {-1, -5, -3, 4}, {-1, -5, -3, 6}, {-1, -5, -3, 8}, {-1, -5, -1, 2}, 
 
>       {-1, -5, -1, 4}, {-1, -5, -1, 6}, {-1, -5, -1, 8}, {-1, -5, 1, -8}, 
 
>       {-1, -5, 1, -6}, {-1, -5, 1, -4}, {-1, -5, 1, -2}, {-1, -5, 1, 0}, 
 
>       {-1, -5, 1, 2}, {-1, -5, 1, 4}, {-1, -5, 3, -8}, {-1, -5, 3, -6}, 
 
>       {-1, -5, 3, -4}, {-1, -5, 3, -2}, {-1, -5, 3, 0}, {-1, -5, 5, -8}, 
 
>       {-1, -5, 5, -6}, {-1, -5, 5, -4}, {-1, -5, 5, -2}, {-1, -5, 5, 0}, 
 
>       {-1, -5, 7, -8}, {-1, -5, 7, -6}, {-1, -5, 7, -4}, {-1, -5, 7, -2}, 
 
>       {-1, -5, 7, 0}, {-1, -3, -7, 2}, {-1, -3, -7, 4}, {-1, -3, -7, 6}, 
 
>       {-1, -3, -7, 8}, {-1, -3, -5, 2}, {-1, -3, -5, 4}, {-1, -3, -5, 6}, 
 
>       {-1, -3, -5, 8}, {-1, -3, -3, 2}, {-1, -3, -3, 4}, {-1, -3, -3, 6}, 
 
>       {-1, -3, -3, 8}, {-1, -3, -1, 2}, {-1, -3, -1, 4}, {-1, -3, -1, 6}, 
 
>       {-1, -3, -1, 8}, {-1, -3, 1, -8}, {-1, -3, 1, -6}, {-1, -3, 1, -4}, 
 
>       {-1, -3, 1, -2}, {-1, -3, 1, 0}, {-1, -3, 1, 2}, {-1, -3, 3, -8}, 
 
>       {-1, -3, 3, -6}, {-1, -3, 3, -4}, {-1, -3, 3, -2}, {-1, -3, 3, 0}, 
 
>       {-1, -3, 5, -8}, {-1, -3, 5, -6}, {-1, -3, 5, -4}, {-1, -3, 5, -2}, 
 
>       {-1, -3, 5, 0}, {-1, -3, 7, -8}, {-1, -3, 7, -6}, {-1, -3, 7, -4}, 
 
>       {-1, -3, 7, -2}, {-1, -3, 7, 0}, {-1, -1, -7, 2}, {-1, -1, -7, 4}, 
 
>       {-1, -1, -7, 6}, {-1, -1, -7, 8}, {-1, -1, -5, 2}, {-1, -1, -5, 4}, 
 
>       {-1, -1, -5, 6}, {-1, -1, -5, 8}, {-1, -1, -3, 2}, {-1, -1, -3, 4}, 
 
>       {-1, -1, -3, 6}, {-1, -1, -3, 8}, {-1, -1, -1, 2}, {-1, -1, -1, 4}, 
 
>       {-1, -1, -1, 6}, {-1, -1, -1, 8}, {-1, -1, 1, -8}, {-1, -1, 1, -6}, 
 
>       {-1, -1, 1, -4}, {-1, -1, 1, -2}, {-1, -1, 1, 0}, {-1, -1, 3, -8}, 
 
>       {-1, -1, 3, -6}, {-1, -1, 3, -4}, {-1, -1, 3, -2}, {-1, -1, 3, 0}, 
 
>       {-1, -1, 5, -8}, {-1, -1, 5, -6}, {-1, -1, 5, -4}, {-1, -1, 5, -2}, 
 
>       {-1, -1, 5, 0}, {-1, -1, 7, -8}, {-1, -1, 7, -6}, {-1, -1, 7, -4}, 
 
>       {-1, -1, 7, -2}, {-1, -1, 7, 0}, {-1, 1, -7, -8}, {-1, 1, -7, -6}, 
 
>       {-1, 1, -7, -4}, {-1, 1, -7, -2}, {-1, 1, -7, 0}, {-1, 1, -7, 2}, 
 
>       {-1, 1, -7, 4}, {-1, 1, -7, 6}, {-1, 1, -5, -8}, {-1, 1, -5, -6}, 
 
>       {-1, 1, -5, -4}, {-1, 1, -5, -2}, {-1, 1, -5, 0}, {-1, 1, -5, 2}, 
 
>       {-1, 1, -5, 4}, {-1, 1, -3, -8}, {-1, 1, -3, -6}, {-1, 1, -3, -4}, 
 
>       {-1, 1, -3, -2}, {-1, 1, -3, 0}, {-1, 1, -3, 2}, {-1, 1, -1, -8}, 
 
>       {-1, 1, -1, -6}, {-1, 1, -1, -4}, {-1, 1, -1, -2}, {-1, 1, -1, 0}, 
 
>       {-1, 1, 1, -8}, {-1, 1, 1, -6}, {-1, 1, 1, -4}, {-1, 1, 1, -2}, 
 
>       {-1, 1, 3, -8}, {-1, 1, 3, -6}, {-1, 1, 3, -4}, {-1, 1, 5, -8}, 
 
>       {-1, 1, 5, -6}, {-1, 1, 7, -8}, {-1, 3, -7, -8}, {-1, 3, -7, -6}, 
 
>       {-1, 3, -7, -4}, {-1, 3, -7, -2}, {-1, 3, -7, 0}, {-1, 3, -5, -8}, 
 
>       {-1, 3, -5, -6}, {-1, 3, -5, -4}, {-1, 3, -5, -2}, {-1, 3, -5, 0}, 
 
>       {-1, 3, -3, -8}, {-1, 3, -3, -6}, {-1, 3, -3, -4}, {-1, 3, -3, -2}, 
 
>       {-1, 3, -3, 0}, {-1, 3, -1, -8}, {-1, 3, -1, -6}, {-1, 3, -1, -4}, 
 
>       {-1, 3, -1, -2}, {-1, 3, -1, 0}, {-1, 3, 1, -8}, {-1, 3, 1, -6}, 
 
>       {-1, 3, 1, -4}, {-1, 5, -7, -8}, {-1, 5, -7, -6}, {-1, 5, -7, -4}, 
 
>       {-1, 5, -7, -2}, {-1, 5, -7, 0}, {-1, 5, -5, -8}, {-1, 5, -5, -6}, 
 
>       {-1, 5, -5, -4}, {-1, 5, -5, -2}, {-1, 5, -5, 0}, {-1, 5, -3, -8}, 
 
>       {-1, 5, -3, -6}, {-1, 5, -3, -4}, {-1, 5, -3, -2}, {-1, 5, -3, 0}, 
 
>       {-1, 5, -1, -8}, {-1, 5, -1, -6}, {-1, 5, -1, -4}, {-1, 5, -1, -2}, 
 
>       {-1, 5, -1, 0}, {-1, 5, 1, -8}, {-1, 5, 1, -6}, {-1, 7, -7, -8}, 
 
>       {-1, 7, -7, -6}, {-1, 7, -7, -4}, {-1, 7, -7, -2}, {-1, 7, -7, 0}, 
 
>       {-1, 7, -5, -8}, {-1, 7, -5, -6}, {-1, 7, -5, -4}, {-1, 7, -5, -2}, 
 
>       {-1, 7, -5, 0}, {-1, 7, -3, -8}, {-1, 7, -3, -6}, {-1, 7, -3, -4}, 
 
>       {-1, 7, -3, -2}, {-1, 7, -3, 0}, {-1, 7, -1, -8}, {-1, 7, -1, -6}, 
 
>       {-1, 7, -1, -4}, {-1, 7, -1, -2}, {-1, 7, -1, 0}, {-1, 7, 1, -8}, 
 
>       {1, -7, -7, 0}, {1, -7, -7, 2}, {1, -7, -7, 4}, {1, -7, -7, 6}, 
 
>       {1, -7, -7, 8}, {1, -7, -5, 0}, {1, -7, -5, 2}, {1, -7, -5, 4}, 
 
>       {1, -7, -5, 6}, {1, -7, -5, 8}, {1, -7, -3, 0}, {1, -7, -3, 2}, 
 
>       {1, -7, -3, 4}, {1, -7, -3, 6}, {1, -7, -3, 8}, {1, -7, -1, -8}, 
 
>       {1, -7, -1, -6}, {1, -7, -1, -4}, {1, -7, -1, -2}, {1, -7, -1, 0}, 
 
>       {1, -7, -1, 2}, {1, -7, -1, 4}, {1, -7, -1, 6}, {1, -7, 1, -8}, 
 
>       {1, -7, 1, -6}, {1, -7, 1, -4}, {1, -7, 1, -2}, {1, -7, 3, -8}, 
 
>       {1, -7, 3, -6}, {1, -7, 3, -4}, {1, -7, 3, -2}, {1, -7, 5, -8}, 
 
>       {1, -7, 5, -6}, {1, -7, 5, -4}, {1, -7, 5, -2}, {1, -7, 7, -8}, 
 
>       {1, -7, 7, -6}, {1, -7, 7, -4}, {1, -7, 7, -2}, {1, -5, -7, 0}, 
 
>       {1, -5, -7, 2}, {1, -5, -7, 4}, {1, -5, -7, 6}, {1, -5, -7, 8}, 
 
>       {1, -5, -5, 0}, {1, -5, -5, 2}, {1, -5, -5, 4}, {1, -5, -5, 6}, 
 
>       {1, -5, -5, 8}, {1, -5, -3, 0}, {1, -5, -3, 2}, {1, -5, -3, 4}, 
 
>       {1, -5, -3, 6}, {1, -5, -3, 8}, {1, -5, -1, -8}, {1, -5, -1, -6}, 
 
>       {1, -5, -1, -4}, {1, -5, -1, -2}, {1, -5, -1, 0}, {1, -5, -1, 2}, 
 
>       {1, -5, -1, 4}, {1, -5, 1, -8}, {1, -5, 1, -6}, {1, -5, 1, -4}, 
 
>       {1, -5, 1, -2}, {1, -5, 3, -8}, {1, -5, 3, -6}, {1, -5, 3, -4}, 
 
>       {1, -5, 3, -2}, {1, -5, 5, -8}, {1, -5, 5, -6}, {1, -5, 5, -4}, 
 
>       {1, -5, 5, -2}, {1, -5, 7, -8}, {1, -5, 7, -6}, {1, -5, 7, -4}, 
 
>       {1, -5, 7, -2}, {1, -3, -7, 0}, {1, -3, -7, 2}, {1, -3, -7, 4}, 
 
>       {1, -3, -7, 6}, {1, -3, -7, 8}, {1, -3, -5, 0}, {1, -3, -5, 2}, 
 
>       {1, -3, -5, 4}, {1, -3, -5, 6}, {1, -3, -5, 8}, {1, -3, -3, 0}, 
 
>       {1, -3, -3, 2}, {1, -3, -3, 4}, {1, -3, -3, 6}, {1, -3, -3, 8}, 
 
>       {1, -3, -1, -8}, {1, -3, -1, -6}, {1, -3, -1, -4}, {1, -3, -1, -2}, 
 
>       {1, -3, -1, 0}, {1, -3, -1, 2}, {1, -3, 1, -8}, {1, -3, 1, -6}, 
 
>       {1, -3, 1, -4}, {1, -3, 1, -2}, {1, -3, 3, -8}, {1, -3, 3, -6}, 
 
>       {1, -3, 3, -4}, {1, -3, 3, -2}, {1, -3, 5, -8}, {1, -3, 5, -6}, 
 
>       {1, -3, 5, -4}, {1, -3, 5, -2}, {1, -3, 7, -8}, {1, -3, 7, -6}, 
 
>       {1, -3, 7, -4}, {1, -3, 7, -2}, {1, -1, -7, -8}, {1, -1, -7, -6}, 
 
>       {1, -1, -7, -4}, {1, -1, -7, -2}, {1, -1, -7, 0}, {1, -1, -7, 2}, 
 
>       {1, -1, -7, 4}, {1, -1, -7, 6}, {1, -1, -5, -8}, {1, -1, -5, -6}, 
 
>       {1, -1, -5, -4}, {1, -1, -5, -2}, {1, -1, -5, 0}, {1, -1, -5, 2}, 
 
>       {1, -1, -5, 4}, {1, -1, -3, -8}, {1, -1, -3, -6}, {1, -1, -3, -4}, 
 
>       {1, -1, -3, -2}, {1, -1, -3, 0}, {1, -1, -3, 2}, {1, -1, -1, -8}, 
 
>       {1, -1, -1, -6}, {1, -1, -1, -4}, {1, -1, -1, -2}, {1, -1, -1, 0}, 
 
>       {1, -1, 1, -8}, {1, -1, 1, -6}, {1, -1, 1, -4}, {1, -1, 1, -2}, 
 
>       {1, -1, 3, -8}, {1, -1, 3, -6}, {1, -1, 3, -4}, {1, -1, 5, -8}, 
 
>       {1, -1, 5, -6}, {1, -1, 7, -8}, {1, 1, -7, -8}, {1, 1, -7, -6}, 
 
>       {1, 1, -7, -4}, {1, 1, -7, -2}, {1, 1, -5, -8}, {1, 1, -5, -6}, 
 
>       {1, 1, -5, -4}, {1, 1, -5, -2}, {1, 1, -3, -8}, {1, 1, -3, -6}, 
 
>       {1, 1, -3, -4}, {1, 1, -3, -2}, {1, 1, -1, -8}, {1, 1, -1, -6}, 
 
>       {1, 1, -1, -4}, {1, 1, -1, -2}, {1, 3, -7, -8}, {1, 3, -7, -6}, 
 
>       {1, 3, -7, -4}, {1, 3, -7, -2}, {1, 3, -5, -8}, {1, 3, -5, -6}, 
 
>       {1, 3, -5, -4}, {1, 3, -5, -2}, {1, 3, -3, -8}, {1, 3, -3, -6}, 
 
>       {1, 3, -3, -4}, {1, 3, -3, -2}, {1, 3, -1, -8}, {1, 3, -1, -6}, 
 
>       {1, 3, -1, -4}, {1, 5, -7, -8}, {1, 5, -7, -6}, {1, 5, -7, -4}, 
 
>       {1, 5, -7, -2}, {1, 5, -5, -8}, {1, 5, -5, -6}, {1, 5, -5, -4}, 
 
>       {1, 5, -5, -2}, {1, 5, -3, -8}, {1, 5, -3, -6}, {1, 5, -3, -4}, 
 
>       {1, 5, -3, -2}, {1, 5, -1, -8}, {1, 5, -1, -6}, {1, 7, -7, -8}, 
 
>       {1, 7, -7, -6}, {1, 7, -7, -4}, {1, 7, -7, -2}, {1, 7, -5, -8}, 
 
>       {1, 7, -5, -6}, {1, 7, -5, -4}, {1, 7, -5, -2}, {1, 7, -3, -8}, 
 
>       {1, 7, -3, -6}, {1, 7, -3, -4}, {1, 7, -3, -2}, {1, 7, -1, -8}, 
 
>       {3, -7, -7, -2}, {3, -7, -7, 0}, {3, -7, -5, -2}, {3, -7, -5, 0}, 
 
>       {3, -7, -3, -8}, {3, -7, -3, -6}, {3, -7, -3, -4}, {3, -7, -3, -2}, 
 
>       {3, -7, -3, 0}, {3, -7, -1, -8}, {3, -7, -1, -6}, {3, -7, -1, -4}, 
 
>       {3, -7, -1, -2}, {3, -7, -1, 0}, {3, -7, 1, -8}, {3, -7, 1, -6}, 
 
>       {3, -7, 1, -4}, {3, -7, 1, -2}, {3, -5, -7, -2}, {3, -5, -7, 0}, 
 
>       {3, -5, -5, -2}, {3, -5, -5, 0}, {3, -5, -3, -8}, {3, -5, -3, -6}, 
 
>       {3, -5, -3, -4}, {3, -5, -3, -2}, {3, -5, -3, 0}, {3, -5, -1, -8}, 
 
>       {3, -5, -1, -6}, {3, -5, -1, -4}, {3, -5, -1, -2}, {3, -5, -1, 0}, 
 
>       {3, -5, 1, -8}, {3, -5, 1, -6}, {3, -5, 1, -4}, {3, -5, 1, -2}, 
 
>       {3, -3, -7, -8}, {3, -3, -7, -6}, {3, -3, -7, -4}, {3, -3, -7, -2}, 
 
>       {3, -3, -7, 0}, {3, -3, -5, -8}, {3, -3, -5, -6}, {3, -3, -5, -4}, 
 
>       {3, -3, -5, -2}, {3, -3, -5, 0}, {3, -3, -3, -8}, {3, -3, -3, -6}, 
 
>       {3, -3, -3, -4}, {3, -3, -3, -2}, {3, -3, -3, 0}, {3, -3, -1, -8}, 
 
>       {3, -3, -1, -6}, {3, -3, -1, -4}, {3, -3, -1, -2}, {3, -3, -1, 0}, 
 
>       {3, -3, 1, -8}, {3, -3, 1, -6}, {3, -3, 1, -4}, {3, -3, 1, -2}, 
 
>       {3, -1, -7, -8}, {3, -1, -7, -6}, {3, -1, -7, -4}, {3, -1, -7, -2}, 
 
>       {3, -1, -7, 0}, {3, -1, -5, -8}, {3, -1, -5, -6}, {3, -1, -5, -4}, 
 
>       {3, -1, -5, -2}, {3, -1, -5, 0}, {3, -1, -3, -8}, {3, -1, -3, -6}, 
 
>       {3, -1, -3, -4}, {3, -1, -3, -2}, {3, -1, -3, 0}, {3, -1, -1, -8}, 
 
>       {3, -1, -1, -6}, {3, -1, -1, -4}, {3, -1, -1, -2}, {3, -1, -1, 0}, 
 
>       {3, -1, 1, -8}, {3, -1, 1, -6}, {3, -1, 1, -4}, {3, 1, -7, -8}, 
 
>       {3, 1, -7, -6}, {3, 1, -7, -4}, {3, 1, -7, -2}, {3, 1, -5, -8}, 
 
>       {3, 1, -5, -6}, {3, 1, -5, -4}, {3, 1, -5, -2}, {3, 1, -3, -8}, 
 
>       {3, 1, -3, -6}, {3, 1, -3, -4}, {3, 1, -3, -2}, {3, 1, -1, -8}, 
 
>       {3, 1, -1, -6}, {3, 1, -1, -4}, {5, -7, -7, -4}, {5, -7, -7, -2}, 
 
>       {5, -7, -7, 0}, {5, -7, -5, -8}, {5, -7, -5, -6}, {5, -7, -5, -4}, 
 
>       {5, -7, -5, -2}, {5, -7, -5, 0}, {5, -7, -3, -8}, {5, -7, -3, -6}, 
 
>       {5, -7, -3, -4}, {5, -7, -3, -2}, {5, -7, -3, 0}, {5, -7, -1, -8}, 
 
>       {5, -7, -1, -6}, {5, -7, -1, -4}, {5, -7, -1, -2}, {5, -7, -1, 0}, 
 
>       {5, -7, 1, -8}, {5, -7, 1, -6}, {5, -7, 1, -4}, {5, -7, 1, -2}, 
 
>       {5, -5, -7, -8}, {5, -5, -7, -6}, {5, -5, -7, -4}, {5, -5, -7, -2}, 
 
>       {5, -5, -7, 0}, {5, -5, -5, -8}, {5, -5, -5, -6}, {5, -5, -5, -4}, 
 
>       {5, -5, -5, -2}, {5, -5, -5, 0}, {5, -5, -3, -8}, {5, -5, -3, -6}, 
 
>       {5, -5, -3, -4}, {5, -5, -3, -2}, {5, -5, -3, 0}, {5, -5, -1, -8}, 
 
>       {5, -5, -1, -6}, {5, -5, -1, -4}, {5, -5, -1, -2}, {5, -5, -1, 0}, 
 
>       {5, -5, 1, -8}, {5, -5, 1, -6}, {5, -5, 1, -4}, {5, -5, 1, -2}, 
 
>       {5, -3, -7, -8}, {5, -3, -7, -6}, {5, -3, -7, -4}, {5, -3, -7, -2}, 
 
>       {5, -3, -7, 0}, {5, -3, -5, -8}, {5, -3, -5, -6}, {5, -3, -5, -4}, 
 
>       {5, -3, -5, -2}, {5, -3, -5, 0}, {5, -3, -3, -8}, {5, -3, -3, -6}, 
 
>       {5, -3, -3, -4}, {5, -3, -3, -2}, {5, -3, -3, 0}, {5, -3, -1, -8}, 
 
>       {5, -3, -1, -6}, {5, -3, -1, -4}, {5, -3, -1, -2}, {5, -3, -1, 0}, 
 
>       {5, -3, 1, -8}, {5, -3, 1, -6}, {5, -3, 1, -4}, {5, -3, 1, -2}, 
 
>       {5, -1, -7, -8}, {5, -1, -7, -6}, {5, -1, -7, -4}, {5, -1, -7, -2}, 
 
>       {5, -1, -7, 0}, {5, -1, -5, -8}, {5, -1, -5, -6}, {5, -1, -5, -4}, 
 
>       {5, -1, -5, -2}, {5, -1, -5, 0}, {5, -1, -3, -8}, {5, -1, -3, -6}, 
 
>       {5, -1, -3, -4}, {5, -1, -3, -2}, {5, -1, -3, 0}, {5, -1, -1, -8}, 
 
>       {5, -1, -1, -6}, {5, -1, -1, -4}, {5, -1, -1, -2}, {5, -1, -1, 0}, 
 
>       {5, -1, 1, -8}, {5, -1, 1, -6}, {5, 1, -7, -8}, {5, 1, -7, -6}, 
 
>       {5, 1, -7, -4}, {5, 1, -7, -2}, {5, 1, -5, -8}, {5, 1, -5, -6}, 
 
>       {5, 1, -5, -4}, {5, 1, -5, -2}, {5, 1, -3, -8}, {5, 1, -3, -6}, 
 
>       {5, 1, -3, -4}, {5, 1, -3, -2}, {5, 1, -1, -8}, {5, 1, -1, -6}, 
 
>       {7, -7, -7, -8}, {7, -7, -7, -6}, {7, -7, -7, -4}, {7, -7, -7, -2}, 
 
>       {7, -7, -7, 0}, {7, -7, -5, -8}, {7, -7, -5, -6}, {7, -7, -5, -4}, 
 
>       {7, -7, -5, -2}, {7, -7, -5, 0}, {7, -7, -3, -8}, {7, -7, -3, -6}, 
 
>       {7, -7, -3, -4}, {7, -7, -3, -2}, {7, -7, -3, 0}, {7, -7, -1, -8}, 
 
>       {7, -7, -1, -6}, {7, -7, -1, -4}, {7, -7, -1, -2}, {7, -7, -1, 0}, 
 
>       {7, -7, 1, -8}, {7, -7, 1, -6}, {7, -7, 1, -4}, {7, -7, 1, -2}, 
 
>       {7, -5, -7, -8}, {7, -5, -7, -6}, {7, -5, -7, -4}, {7, -5, -7, -2}, 
 
>       {7, -5, -7, 0}, {7, -5, -5, -8}, {7, -5, -5, -6}, {7, -5, -5, -4}, 
 
>       {7, -5, -5, -2}, {7, -5, -5, 0}, {7, -5, -3, -8}, {7, -5, -3, -6}, 
 
>       {7, -5, -3, -4}, {7, -5, -3, -2}, {7, -5, -3, 0}, {7, -5, -1, -8}, 
 
>       {7, -5, -1, -6}, {7, -5, -1, -4}, {7, -5, -1, -2}, {7, -5, -1, 0}, 
 
>       {7, -5, 1, -8}, {7, -5, 1, -6}, {7, -5, 1, -4}, {7, -5, 1, -2}, 
 
>       {7, -3, -7, -8}, {7, -3, -7, -6}, {7, -3, -7, -4}, {7, -3, -7, -2}, 
 
>       {7, -3, -7, 0}, {7, -3, -5, -8}, {7, -3, -5, -6}, {7, -3, -5, -4}, 
 
>       {7, -3, -5, -2}, {7, -3, -5, 0}, {7, -3, -3, -8}, {7, -3, -3, -6}, 
 
>       {7, -3, -3, -4}, {7, -3, -3, -2}, {7, -3, -3, 0}, {7, -3, -1, -8}, 
 
>       {7, -3, -1, -6}, {7, -3, -1, -4}, {7, -3, -1, -2}, {7, -3, -1, 0}, 
 
>       {7, -3, 1, -8}, {7, -3, 1, -6}, {7, -3, 1, -4}, {7, -3, 1, -2}, 
 
>       {7, -1, -7, -8}, {7, -1, -7, -6}, {7, -1, -7, -4}, {7, -1, -7, -2}, 
 
>       {7, -1, -7, 0}, {7, -1, -5, -8}, {7, -1, -5, -6}, {7, -1, -5, -4}, 
 
>       {7, -1, -5, -2}, {7, -1, -5, 0}, {7, -1, -3, -8}, {7, -1, -3, -6}, 
 
>       {7, -1, -3, -4}, {7, -1, -3, -2}, {7, -1, -3, 0}, {7, -1, -1, -8}, 
 
>       {7, -1, -1, -6}, {7, -1, -1, -4}, {7, -1, -1, -2}, {7, -1, -1, 0}, 
 
>       {7, -1, 1, -8}, {7, 1, -7, -8}, {7, 1, -7, -6}, {7, 1, -7, -4}, 
 
>       {7, 1, -7, -2}, {7, 1, -5, -8}, {7, 1, -5, -6}, {7, 1, -5, -4}, 
 
>       {7, 1, -5, -2}, {7, 1, -3, -8}, {7, 1, -3, -6}, {7, 1, -3, -4}, 
 
>       {7, 1, -3, -2}, {7, 1, -1, -8}}, 
 
>      {{-7, -7, -7, -8}, {-7, -7, -7, -6}, {-7, -7, -7, -4}, 
 
>       {-7, -7, -7, -2}, {-7, -7, -7, 0}, {-7, -7, -5, -8}, 
 
>       {-7, -7, -5, -6}, {-7, -7, -5, -4}, {-7, -7, -5, -2}, 
 
>       {-7, -7, -5, 0}, {-7, -7, -3, -8}, {-7, -7, -3, -6}, 
 
>       {-7, -7, -3, -4}, {-7, -7, -3, -2}, {-7, -7, -3, 0}, 
 
>       {-7, -7, -1, -8}, {-7, -7, -1, -6}, {-7, -7, -1, -4}, 
 
>       {-7, -7, -1, -2}, {-7, -7, -1, 0}, {-7, -5, -7, -8}, 
 
>       {-7, -5, -7, -6}, {-7, -5, -7, -4}, {-7, -5, -7, -2}, 
 
>       {-7, -5, -7, 0}, {-7, -5, -5, -8}, {-7, -5, -5, -6}, 
 
>       {-7, -5, -5, -4}, {-7, -5, -5, -2}, {-7, -5, -5, 0}, 
 
>       {-7, -5, -3, -8}, {-7, -5, -3, -6}, {-7, -5, -3, -4}, 
 
>       {-7, -5, -3, -2}, {-7, -5, -3, 0}, {-7, -5, -1, -8}, 
 
>       {-7, -5, -1, -6}, {-7, -5, -1, -4}, {-7, -5, -1, -2}, 
 
>       {-7, -5, -1, 0}, {-7, -3, -7, -8}, {-7, -3, -7, -6}, 
 
>       {-7, -3, -7, -4}, {-7, -3, -7, -2}, {-7, -3, -7, 0}, 
 
>       {-7, -3, -5, -8}, {-7, -3, -5, -6}, {-7, -3, -5, -4}, 
 
>       {-7, -3, -5, -2}, {-7, -3, -5, 0}, {-7, -3, -3, -8}, 
 
>       {-7, -3, -3, -6}, {-7, -3, -3, -4}, {-7, -3, -3, -2}, 
 
>       {-7, -3, -3, 0}, {-7, -3, -1, -8}, {-7, -3, -1, -6}, 
 
>       {-7, -3, -1, -4}, {-7, -3, -1, -2}, {-7, -3, -1, 0}, 
 
>       {-7, -1, -7, -8}, {-7, -1, -7, -6}, {-7, -1, -7, -4}, 
 
>       {-7, -1, -7, -2}, {-7, -1, -7, 0}, {-7, -1, -5, -8}, 
 
>       {-7, -1, -5, -6}, {-7, -1, -5, -4}, {-7, -1, -5, -2}, 
 
>       {-7, -1, -5, 0}, {-7, -1, -3, -8}, {-7, -1, -3, -6}, 
 
>       {-7, -1, -3, -4}, {-7, -1, -3, -2}, {-7, -1, -3, 0}, 
 
>       {-7, -1, -1, -8}, {-7, -1, -1, -6}, {-7, -1, -1, -4}, 
 
>       {-7, -1, -1, -2}, {-7, -1, -1, 0}, {-5, -7, -7, -8}, 
 
>       {-5, -7, -7, -6}, {-5, -7, -7, -4}, {-5, -7, -7, -2}, 
 
>       {-5, -7, -7, 0}, {-5, -7, -5, -8}, {-5, -7, -5, -6}, 
 
>       {-5, -7, -5, -4}, {-5, -7, -5, -2}, {-5, -7, -5, 0}, 
 
>       {-5, -7, -3, -8}, {-5, -7, -3, -6}, {-5, -7, -3, -4}, 
 
>       {-5, -7, -3, -2}, {-5, -7, -3, 0}, {-5, -7, -1, -8}, 
 
>       {-5, -7, -1, -6}, {-5, -7, -1, -4}, {-5, -7, -1, -2}, 
 
>       {-5, -7, -1, 0}, {-5, -5, -7, -8}, {-5, -5, -7, -6}, 
 
>       {-5, -5, -7, -4}, {-5, -5, -7, -2}, {-5, -5, -7, 0}, 
 
>       {-5, -5, -5, -8}, {-5, -5, -5, -6}, {-5, -5, -5, -4}, 
 
>       {-5, -5, -5, -2}, {-5, -5, -5, 0}, {-5, -5, -3, -8}, 
 
>       {-5, -5, -3, -6}, {-5, -5, -3, -4}, {-5, -5, -3, -2}, 
 
>       {-5, -5, -3, 0}, {-5, -5, -1, -8}, {-5, -5, -1, -6}, 
 
>       {-5, -5, -1, -4}, {-5, -5, -1, -2}, {-5, -5, -1, 0}, 
 
>       {-5, -3, -7, -8}, {-5, -3, -7, -6}, {-5, -3, -7, -4}, 
 
>       {-5, -3, -7, -2}, {-5, -3, -7, 0}, {-5, -3, -5, -8}, 
 
>       {-5, -3, -5, -6}, {-5, -3, -5, -4}, {-5, -3, -5, -2}, 
 
>       {-5, -3, -5, 0}, {-5, -3, -3, -8}, {-5, -3, -3, -6}, 
 
>       {-5, -3, -3, -4}, {-5, -3, -3, -2}, {-5, -3, -3, 0}, 
 
>       {-5, -3, -1, -8}, {-5, -3, -1, -6}, {-5, -3, -1, -4}, 
 
>       {-5, -3, -1, -2}, {-5, -3, -1, 0}, {-5, -1, -7, -8}, 
 
>       {-5, -1, -7, -6}, {-5, -1, -7, -4}, {-5, -1, -7, -2}, 
 
>       {-5, -1, -7, 0}, {-5, -1, -5, -8}, {-5, -1, -5, -6}, 
 
>       {-5, -1, -5, -4}, {-5, -1, -5, -2}, {-5, -1, -5, 0}, 
 
>       {-5, -1, -3, -8}, {-5, -1, -3, -6}, {-5, -1, -3, -4}, 
 
>       {-5, -1, -3, -2}, {-5, -1, -3, 0}, {-5, -1, -1, -8}, 
 
>       {-5, -1, -1, -6}, {-5, -1, -1, -4}, {-5, -1, -1, -2}, 
 
>       {-5, -1, -1, 0}, {-3, -7, -7, -8}, {-3, -7, -7, -6}, 
 
>       {-3, -7, -7, -4}, {-3, -7, -7, -2}, {-3, -7, -7, 0}, 
 
>       {-3, -7, -5, -8}, {-3, -7, -5, -6}, {-3, -7, -5, -4}, 
 
>       {-3, -7, -5, -2}, {-3, -7, -5, 0}, {-3, -7, -3, -8}, 
 
>       {-3, -7, -3, -6}, {-3, -7, -3, -4}, {-3, -7, -3, -2}, 
 
>       {-3, -7, -3, 0}, {-3, -7, -1, -8}, {-3, -7, -1, -6}, 
 
>       {-3, -7, -1, -4}, {-3, -7, -1, -2}, {-3, -7, -1, 0}, 
 
>       {-3, -5, -7, -8}, {-3, -5, -7, -6}, {-3, -5, -7, -4}, 
 
>       {-3, -5, -7, -2}, {-3, -5, -7, 0}, {-3, -5, -5, -8}, 
 
>       {-3, -5, -5, -6}, {-3, -5, -5, -4}, {-3, -5, -5, -2}, 
 
>       {-3, -5, -5, 0}, {-3, -5, -3, -8}, {-3, -5, -3, -6}, 
 
>       {-3, -5, -3, -4}, {-3, -5, -3, -2}, {-3, -5, -3, 0}, 
 
>       {-3, -5, -1, -8}, {-3, -5, -1, -6}, {-3, -5, -1, -4}, 
 
>       {-3, -5, -1, -2}, {-3, -5, -1, 0}, {-3, -3, -7, -8}, 
 
>       {-3, -3, -7, -6}, {-3, -3, -7, -4}, {-3, -3, -7, -2}, 
 
>       {-3, -3, -7, 0}, {-3, -3, -5, -8}, {-3, -3, -5, -6}, 
 
>       {-3, -3, -5, -4}, {-3, -3, -5, -2}, {-3, -3, -5, 0}, 
 
>       {-3, -3, -3, -8}, {-3, -3, -3, -6}, {-3, -3, -3, -4}, 
 
>       {-3, -3, -3, -2}, {-3, -3, -3, 0}, {-3, -3, -1, -8}, 
 
>       {-3, -3, -1, -6}, {-3, -3, -1, -4}, {-3, -3, -1, -2}, 
 
>       {-3, -3, -1, 0}, {-3, -1, -7, -8}, {-3, -1, -7, -6}, 
 
>       {-3, -1, -7, -4}, {-3, -1, -7, -2}, {-3, -1, -7, 0}, 
 
>       {-3, -1, -5, -8}, {-3, -1, -5, -6}, {-3, -1, -5, -4}, 
 
>       {-3, -1, -5, -2}, {-3, -1, -5, 0}, {-3, -1, -3, -8}, 
 
>       {-3, -1, -3, -6}, {-3, -1, -3, -4}, {-3, -1, -3, -2}, 
 
>       {-3, -1, -3, 0}, {-3, -1, -1, -8}, {-3, -1, -1, -6}, 
 
>       {-3, -1, -1, -4}, {-3, -1, -1, -2}, {-3, -1, -1, 0}, 
 
>       {-1, -7, -7, -8}, {-1, -7, -7, -6}, {-1, -7, -7, -4}, 
 
>       {-1, -7, -7, -2}, {-1, -7, -7, 0}, {-1, -7, -5, -8}, 
 
>       {-1, -7, -5, -6}, {-1, -7, -5, -4}, {-1, -7, -5, -2}, 
 
>       {-1, -7, -5, 0}, {-1, -7, -3, -8}, {-1, -7, -3, -6}, 
 
>       {-1, -7, -3, -4}, {-1, -7, -3, -2}, {-1, -7, -3, 0}, 
 
>       {-1, -7, -1, -8}, {-1, -7, -1, -6}, {-1, -7, -1, -4}, 
 
>       {-1, -7, -1, -2}, {-1, -7, -1, 0}, {-1, -5, -7, -8}, 
 
>       {-1, -5, -7, -6}, {-1, -5, -7, -4}, {-1, -5, -7, -2}, 
 
>       {-1, -5, -7, 0}, {-1, -5, -5, -8}, {-1, -5, -5, -6}, 
 
>       {-1, -5, -5, -4}, {-1, -5, -5, -2}, {-1, -5, -5, 0}, 
 
>       {-1, -5, -3, -8}, {-1, -5, -3, -6}, {-1, -5, -3, -4}, 
 
>       {-1, -5, -3, -2}, {-1, -5, -3, 0}, {-1, -5, -1, -8}, 
 
>       {-1, -5, -1, -6}, {-1, -5, -1, -4}, {-1, -5, -1, -2}, 
 
>       {-1, -5, -1, 0}, {-1, -3, -7, -8}, {-1, -3, -7, -6}, 
 
>       {-1, -3, -7, -4}, {-1, -3, -7, -2}, {-1, -3, -7, 0}, 
 
>       {-1, -3, -5, -8}, {-1, -3, -5, -6}, {-1, -3, -5, -4}, 
 
>       {-1, -3, -5, -2}, {-1, -3, -5, 0}, {-1, -3, -3, -8}, 
 
>       {-1, -3, -3, -6}, {-1, -3, -3, -4}, {-1, -3, -3, -2}, 
 
>       {-1, -3, -3, 0}, {-1, -3, -1, -8}, {-1, -3, -1, -6}, 
 
>       {-1, -3, -1, -4}, {-1, -3, -1, -2}, {-1, -3, -1, 0}, 
 
>       {-1, -1, -7, -8}, {-1, -1, -7, -6}, {-1, -1, -7, -4}, 
 
>       {-1, -1, -7, -2}, {-1, -1, -7, 0}, {-1, -1, -5, -8}, 
 
>       {-1, -1, -5, -6}, {-1, -1, -5, -4}, {-1, -1, -5, -2}, 
 
>       {-1, -1, -5, 0}, {-1, -1, -3, -8}, {-1, -1, -3, -6}, 
 
>       {-1, -1, -3, -4}, {-1, -1, -3, -2}, {-1, -1, -3, 0}, 
 
>       {-1, -1, -1, -8}, {-1, -1, -1, -6}, {-1, -1, -1, -4}, 
 
>       {-1, -1, -1, -2}, {-1, -1, -1, 0}}}, 
 
>    pExcept -> 
 
>     {{1, 1, 1, 0}, {1, 1, 3, 0}, {1, 1, 5, 0}, {1, 1, 7, 0}, {1, 3, 1, 0}, 
 
>      {1, 3, 3, 0}, {1, 3, 5, 0}, {1, 3, 7, 0}, {1, 5, 1, 0}, {1, 5, 3, 0}, 
 
>      {1, 5, 5, 0}, {1, 5, 7, 0}, {1, 7, 1, 0}, {1, 7, 3, 0}, {1, 7, 5, 0}, 
 
>      {1, 7, 7, 0}, {3, 1, 1, 0}, {3, 1, 3, 0}, {3, 1, 5, 0}, {3, 1, 7, 0}, 
 
>      {3, 3, 1, 0}, {3, 3, 3, -2}, {3, 3, 3, 0}, {3, 3, 5, -2}, 
 
>      {3, 3, 5, 0}, {3, 3, 7, -2}, {3, 3, 7, 0}, {3, 5, 1, 0}, 
 
>      {3, 5, 3, -2}, {3, 5, 3, 0}, {3, 5, 5, -2}, {3, 5, 5, 0}, 
 
>      {3, 5, 7, -2}, {3, 5, 7, 0}, {3, 7, 1, 0}, {3, 7, 3, -2}, 
 
>      {3, 7, 3, 0}, {3, 7, 5, -2}, {3, 7, 5, 0}, {3, 7, 7, -2}, 
 
>      {3, 7, 7, 0}, {5, 1, 1, 0}, {5, 1, 3, 0}, {5, 1, 5, 0}, {5, 1, 7, 0}, 
 
>      {5, 3, 1, 0}, {5, 3, 3, -2}, {5, 3, 3, 0}, {5, 3, 5, -2}, 
 
>      {5, 3, 5, 0}, {5, 3, 7, -2}, {5, 3, 7, 0}, {5, 5, 1, 0}, 
 
>      {5, 5, 3, -2}, {5, 5, 3, 0}, {5, 5, 5, -4}, {5, 5, 5, -2}, 
 
>      {5, 5, 5, 0}, {5, 5, 7, -4}, {5, 5, 7, -2}, {5, 5, 7, 0}, 
 
>      {5, 7, 1, 0}, {5, 7, 3, -2}, {5, 7, 3, 0}, {5, 7, 5, -4}, 
 
>      {5, 7, 5, -2}, {5, 7, 5, 0}, {5, 7, 7, -4}, {5, 7, 7, -2}, 
 
>      {5, 7, 7, 0}, {7, 1, 1, 0}, {7, 1, 3, 0}, {7, 1, 5, 0}, {7, 1, 7, 0}, 
 
>      {7, 3, 1, 0}, {7, 3, 3, -2}, {7, 3, 3, 0}, {7, 3, 5, -2}, 
 
>      {7, 3, 5, 0}, {7, 3, 7, -2}, {7, 3, 7, 0}, {7, 5, 1, 0}, 
 
>      {7, 5, 3, -2}, {7, 5, 3, 0}, {7, 5, 5, -4}, {7, 5, 5, -2}, 
 
>      {7, 5, 5, 0}, {7, 5, 7, -4}, {7, 5, 7, -2}, {7, 5, 7, 0}, 
 
>      {7, 7, 1, 0}, {7, 7, 3, -2}, {7, 7, 3, 0}, {7, 7, 5, -4}, 
 
>      {7, 7, 5, -2}, {7, 7, 5, 0}, {7, 7, 7, -6}, {7, 7, 7, -4}, 
 
>      {7, 7, 7, -2}, {7, 7, 7, 0}}, 
 
>    mExcept -> 
 
>     {{-7, -7, -7, 0}, {-7, -7, -7, 2}, {-7, -7, -7, 4}, {-7, -7, -7, 6}, 
 
>      {-7, -7, -5, 0}, {-7, -7, -5, 2}, {-7, -7, -5, 4}, {-7, -7, -3, 0}, 
 
>      {-7, -7, -3, 2}, {-7, -7, -1, 0}, {-7, -5, -7, 0}, {-7, -5, -7, 2}, 
 
>      {-7, -5, -7, 4}, {-7, -5, -5, 0}, {-7, -5, -5, 2}, {-7, -5, -5, 4}, 
 
>      {-7, -5, -3, 0}, {-7, -5, -3, 2}, {-7, -5, -1, 0}, {-7, -3, -7, 0}, 
 
>      {-7, -3, -7, 2}, {-7, -3, -5, 0}, {-7, -3, -5, 2}, {-7, -3, -3, 0}, 
 
>      {-7, -3, -3, 2}, {-7, -3, -1, 0}, {-7, -1, -7, 0}, {-7, -1, -5, 0}, 
 
>      {-7, -1, -3, 0}, {-7, -1, -1, 0}, {-5, -7, -7, 0}, {-5, -7, -7, 2}, 
 
>      {-5, -7, -7, 4}, {-5, -7, -5, 0}, {-5, -7, -5, 2}, {-5, -7, -5, 4}, 
 
>      {-5, -7, -3, 0}, {-5, -7, -3, 2}, {-5, -7, -1, 0}, {-5, -5, -7, 0}, 
 
>      {-5, -5, -7, 2}, {-5, -5, -7, 4}, {-5, -5, -5, 0}, {-5, -5, -5, 2}, 
 
>      {-5, -5, -5, 4}, {-5, -5, -3, 0}, {-5, -5, -3, 2}, {-5, -5, -1, 0}, 
 
>      {-5, -3, -7, 0}, {-5, -3, -7, 2}, {-5, -3, -5, 0}, {-5, -3, -5, 2}, 
 
>      {-5, -3, -3, 0}, {-5, -3, -3, 2}, {-5, -3, -1, 0}, {-5, -1, -7, 0}, 
 
>      {-5, -1, -5, 0}, {-5, -1, -3, 0}, {-5, -1, -1, 0}, {-3, -7, -7, 0}, 
 
>      {-3, -7, -7, 2}, {-3, -7, -5, 0}, {-3, -7, -5, 2}, {-3, -7, -3, 0}, 
 
>      {-3, -7, -3, 2}, {-3, -7, -1, 0}, {-3, -5, -7, 0}, {-3, -5, -7, 2}, 
 
>      {-3, -5, -5, 0}, {-3, -5, -5, 2}, {-3, -5, -3, 0}, {-3, -5, -3, 2}, 
 
>      {-3, -5, -1, 0}, {-3, -3, -7, 0}, {-3, -3, -7, 2}, {-3, -3, -5, 0}, 
 
>      {-3, -3, -5, 2}, {-3, -3, -3, 0}, {-3, -3, -3, 2}, {-3, -3, -1, 0}, 
 
>      {-3, -1, -7, 0}, {-3, -1, -5, 0}, {-3, -1, -3, 0}, {-3, -1, -1, 0}, 
 
>      {-1, -7, -7, 0}, {-1, -7, -5, 0}, {-1, -7, -3, 0}, {-1, -7, -1, 0}, 
 
>      {-1, -5, -7, 0}, {-1, -5, -5, 0}, {-1, -5, -3, 0}, {-1, -5, -1, 0}, 
 
>      {-1, -3, -7, 0}, {-1, -3, -5, 0}, {-1, -3, -3, 0}, {-1, -3, -1, 0}, 
 
>      {-1, -1, -7, 0}, {-1, -1, -5, 0}, {-1, -1, -3, 0}, {-1, -1, -1, 0}}, 
 
>    pExcept2 -> {}, mExcept2 -> {}|>


Expand[Simplify[Unframed[PrecompKhRed, {-5,-5,3}]
                - DumbEvalAtIndices[(* (-t)^(-1) KhRedMStarKnotsTheor[2] *)
                                    KhRedMExcept2KnotsTheor[2, 2],
                                    {-5, -5, 3}]]]

Expand[Simplify[Unframed[PrecompKhRed, {5,5,-3}]
                - DumbEvalAtIndices[(* (-t)^(-1) KhRedMStarKnotsTheor[2] *)
                                    KhRedPExcept2KnotsTheor[2, 2],
                                    {5, 5, -3}]]]


Expand[Simplify[DumbEvalAtIndices[(-t) KhRedDeltaExcept2KnotsTheor[2], {-5, -5, 3}]]]

         1     1       1       1       1      1
Out[25]= - + ----- + ----- + ----- + ----- + ---
         q    7  4    7  3    5  3    5  2   q t
             q  t    q  t    q  t    q  t


status




CheckCutoffFormula[status["bulks"][[2]],
                   8,
                   2,
                   Function[{coords},
                            Not[Or[Bulks0Cut[coords],
                                   BulksGCut[coords],
                                   PExceptCut[coords],
                                   MExceptCut[coords],
                                   PExcept2Cut[coords],
                                   MExcept2Cut[coords]]]]]


Simplify[(1 + qtThree)/qtTwo^2]










Factor[Simplify[evoRulesCombed["PMPredAlt1"][Mask[t q^2,1,t q^2]] /((-q t) (-t) /qtTwo /qtTwo^3 (1 + qtThree) qtThree)]]

FullSimplify[(MkEvoExpr[evoRulesCombed["PMPredAlt1"]]
              - (-t) (KhRedPStarKnotsTheor[2] /. {NN[i_] :> (q^2 t)^n[i]}))
             /((-q t) (1 + t) /qtTwo (1 + qtThree)/qtTwo^3)
             - (1 + qtThree T^n[1] (T^n[0] + T^n[2]) - qtThree T^(2 n[1]) (T^n[0] * T^n[2]))
             /. {t -> T/q^2}
             ,
             Assumptions -> And[q > 0, t > 0,
                                Element[n[0], Integers],
                                Element[n[1], Integers],
                                Element[n[2], Integers]]]


    
(* ### vv Archive of one-liner snippets that help write TeX-code ### *)
(* Simplify[MkEvoExpr[Apart[Factor[Simplify[KnotifyRules[evoRules["PP"], "oneeven"]]], t]] /. {n[0] -> -1, n[1] -> 0}] *)
(* LoadAllPrecomps[2]; *)
(* Unframed[PrecompKhRed, {3,3,-2}] // TeXForm *)
(* Expand[Simplify[DumbEvalAtIndices[(-t) KhRedPStarKnotsTheor[2], {3,3,-2}]]] // TeXForm *)
(* Simplify[Unframed[PrecompKhRed, {6, 8, -4}] *)
(*          - Unframed[PrecompKhRed, {-4, 6, 8}]] *)
(* Expand[Simplify[EvalAtIndices[KhRedMExceptKnotsTheor[2, 1], {-3, 5, 4}]]] *)
(* Expand[Simplify[(\* Unframed[PrecompKhRed, {6,5, -4}] - *\) *)
(*                 Expand[Simplify[DumbEvalAtIndices[(-t) KhRedPStarKnotsTheor[2], {6,5,-4}]]]]] *)
(* Expand[Simplify[EvalAtIndices[KhRedDeltaExceptKnotsTheor[2], {5, 4, -3}]]] *)
(* ### vv The 'fails' that were separately precomputed ### *)
(* fails = Get["../data/genus-3-fails.m"]; *)
(* ### ------ ### *)
(* Block[{n = 3}, *)
(*       Expand[Simplify[Kh[PD[TorusKnot[2, n]]][q,t]]]] *)
(* Block[{n = 7}, *)
(*       Expand[Simplify[(q + q^(-1))HOMFLYPT[TorusKnot[2, n]][q^2, q - q^(-1)]]]] *)
(* Expand[Simplify[EvalAtIndices[KhRedPStarKnotsTheor[2], {3,5,1}]]] *)

(* ### vv Learn the correction in the special region for unreduced polynomial ### *)
(* Block[{label = "PPPPP", *)
(*        genus = 4}, *)
(*       FullSimplify[((Knotify[evoRulesCombed[label], genus] /. {NN[i_] :> (q^2 t)^n[i]}) *)
(*                     - TheorEvo[genus]) *)
(*                    / (q^(genus + 1)/(1 + t q^2) (1 + t)), *)
(*                    Assumptions -> And[q > 0, t > 0]]] *)

(* ### vv Learn the correction for genus 2 for unreduced polynomial ### *)
(* Block[{label = "MMM", *)
(*        genus = 2}, *)
(*       FullSimplify[Knotify[evoRulesCombed[label], genus] *)
(*                    - (1 + q^4 t) /q^2/(1 + q^2 t) KhRedMStarKnotsTheor[genus] *)
(*                    , Assumptions -> And[q > 0, t > 0]]] *)
(* Block[{label = "PPM", *)
(*        genus = 2}, *)
(*       FullSimplify[Knotify[evoRulesCombed[label], genus] *)
(*                    - (1 + q^4 t) /q^2/(1 + q^2 t) KhRedBulkKnotsTheor[genus] *)
(*                    , Assumptions -> And[q > 0, t > 0]]] *)

Block[{label = "PPMAlt1",
       genus = 2},
      Factor[Simplify[MkEvoExpr[KnotifyRules[evoRulesCombed[label], "oneeven"]]
                      - (1 + q^4 t) /q^2/(1 + q^2 t) (KhRedPExceptKnotsTheor[2, 2] /. {NN[i_] :> (q^2 t)^n[i]})
                      - q/(1 + q^2 t) (1 + t) (q^2 t)^(n[0] + n[1])
                      - (1 + t)(1 + q^4 t)/(1 + q^2 t) /q/t (q^2 t)^(n[0] + n[1]) (q^4 t^2)^n[2]
                      , Assumptions -> And[q > 0, t > 0]]]]

Block[{label = "PPMAlt1",
       genus = 2},
      Factor[Simplify[MkEvoExpr[KnotifyRules[evoRulesCombed[label], "oneeven"]]
                      - (1 + q^4 t) /q^2/(1 + q^2 t) (KhRedPExceptKnotsTheor[2, 2] /. {NN[i_] :> (q^2 t)^n[i]})
                      - q/(1 + q^2 t) (1 + t) (q^2 t)^(n[0] + n[1])
                      - (1 + t)(1 + q^4 t)/(1 + q^2 t) /q/t (q^2 t)^(n[0] + n[1]) (q^4 t^2)^n[2]
                      , Assumptions -> And[q > 0, t > 0]]]]


(* Block[{label = "MMPAlt1", *)
(*        genus = 2}, *)
(*       Factor[Simplify[MkEvoExpr[KnotifyRules[evoRulesCombed[label], "oneeven"]] *)
(*                       - (1 + q^4 t) /q^2/(1 + q^2 t) (KhRedMExceptKnotsTheor[2, 2] /. {NN[i_] :> (q^2 t)^n[i]}) *)
(*                       - q/(1 + q^2 t) (1 + t) (q^2 t)^(n[0] + n[1]) *)
(*                       , Assumptions -> And[q > 0, t > 0]]]] *)

(* A = PrecompKhRed[-3,-3,-3,2] *)
(* CCC = Expand[Simplify[EvalAtIndices[KhRedMExceptKnotsTheor[3,3], {-3,-3,-3,2}]]] *)
(* A - CCC *)
(* B = Expand[Simplify[EvalAtIndices[(-t)^(-1) KhRedMStarKnotsTheor[3], {-3,-3,-3,2}]]] *)
(* A - B *)
(* Expand[Simplify[EvalAtIndices[t KhRedDeltaExceptKnotsTheor[3], {-3,-3,-3,2}]]] *)
(* Expand[Simplify[EvalAtIndices[KhRedPExceptKnotsTheor[2, 2] *)
(*                               - (-t) KhRedPStarKnotsTheor[2] *)
(*                               , {3,3,-2}]]] // TeXForm *)
(* Block[{indices = {5, 5, -3, 6}}, *)
(*       Factor[Simplify[PrecompKhRed @@ indices *)
(*                       - EvalAtIndices[KhRedPExceptKnotsTheor[3, 2], indices]]]] *)
(* Block[{indices = {5, 5, -3, 4}}, *)
(*       Expand[Simplify[PrecompKhRed @@ indices]]] *)
(* Block[{indices = {5, 5, -3, 4}}, *)
(*       Expand[Simplify[EvalAtIndices[KhRedPExceptKnotsTheor[3, 2], indices]]]] *)

(* ### vv Successful check that for genus 2 (up to cutoff 16) there are no further formulas than I describe ### *)
(* success / total: 8448 8448 *)
(* bulks: {1347, 4480, 1347} *)
(* pExcept: 204 *)
(* mExcept: 204 *)
(* pExcept2: 1060 *)
(* mExcept2: 1060 *)

(* Unframed[PrecompKhRed, {5,-3,4}] *)
(* - Expand[Simplify[DumbEvalAtIndices[(-t) KhRedPStarKnotsTheor[2], {5, -3, 4}]]] *)
(* Expand[Simplify[DumbEvalAtIndices[KhRedDeltaExcept2KnotsTheor[2], {5, 4, -3}]]] *)

(* ### vv Testing particular values to go back from my evolution formulas to the actual reduced Khovanov polynomials ### *)
(* PrecompKhRed[-1,-1,-1,-2] *)
(* Block[{indices = {1,1,1,2}}, *)
(*       Expand[(Simplify[(KhRedBulkKnotsTheor[3] /. {NN[i_] :> (q^2 t)^indices[[i+1]]})] *)
(*               /. {q -> 1/q, t -> 1/t}) (t q^3)^5 (-t)]] *)
(* Block[{indices = {1,1,1,2}}, *)
(*       Expand[(Simplify[(KhRedPStarKnotsTheor[3] /. {NN[i_] :> (q^2 t)^indices[[i+1]]})] *)
(*               /. {q -> 1/q, t -> 1/t}) (t q^3)^5 (\* (-t) *\)]] *)
(* Block[{indices = {-1,-1,-1,-2}}, *)
(*       Expand[Simplify[((KhRedMStarKnotsTheor[3] /. {NN[i_] :> (q^2 t)^indices[[i+1]]}) *)
(*                        /. {q -> 1/q, t -> 1/t}) (t q^3)^(-5) (\* (-t) *\)]]] *)
(* Simplify[evoRulesCombed["PPPMredAlt1"][Mask[1,1,1,1]] *)
(*          /((1 + qtThree) /qtTwo^4 /qtTwo (-q t))] *)
(* Block[{powers = {1, 1, 1, 3}}, *)
(*       Factor[Simplify[(Lookup[evoRulesCombed["PPPMredAlt1"], Mask @@ Map[(t q^2)^# &, powers], 0] *)
(*                        - GetNNCoeff[KhAlt2KnotsTheor[3], powers]) *)
(*                       (\* / ((-1) (1 + t) (qtThree^2 + qtThree)/qtTwo^4 (-q t)/qtTwo) *\) *)
(*                       (\* / ((-1) (1 + t) (qtThree^3 - qtThree)/qtTwo^4 (-q t)/qtTwo) *\) *)
(*                       (\* / ((-1) (1 + t) (qtThree^4 + qtThree)/qtTwo^4 (-q t)/qtTwo) *\) *)
(*                       (\* / ((1 + t) (-q t)/qtTwo 1/qtTwo^4 (qtThree^3 + qtThree^2)) *\) *)
(*                       / ((1 + t) (-q t)/qtTwo 1/qtTwo^4 (qtThree^4 + qtThree^3)) *)
(*                      ]]] *)
(* Factor[FullSimplify[MkEvoExpr[evoRulesCombed["PPPMredAlt1"]] *)
(*                     - KhAlt1KnotsTheor[3]]] *)
(* FullSimplify[FullSimplify[Knotify[evoRulesCombed["PPMredAlt1"], 2]] *)
(*              - KhAlt2KnotsTheor[2]] *)
(* Factor[Simplify[evoRulesCombed["PPMredAlt1"][Mask[1,1,1]] *)
(*                 / ((qtThree + 1) /qtTwo^3 /qtTwo (- q t))]] *)
(* Factor[Simplify[evoRulesCombed["PPMredAlt1"][Mask[q^2 t, q^2 t, q^2 t]] *)
(*                 / ((qtThree^3 - qtThree) /qtTwo^3 /qtTwo (- q t) (-t))]] *)
(* Factor[Simplify[evoRulesCombed["PPMredAlt1"][Mask[1, q^2 t, q^2 t]] *)
(*                 / ((qtThree^2 + qtThree) /qtTwo^3 /qtTwo (- q t))]] *)
(* Factor[Simplify[evoRulesCombed["PPMredAlt1"][Mask[q^2 t, q^2 t, 1]] *)
(*                 / ((qtThree^2 + qtThree) /qtTwo^3 /qtTwo (- q t) (-t))]] *)
(* Factor[Simplify[evoRulesCombed["PPMredAlt1"][Mask[q^2 t, q^2 t, q^4 t^2]] *)
(*                 / (qtThree^2 (1 + qtThree) /qtTwo^4 q (1 + t) (-t))]] *)
(* Simplify[MkEvoExpr[evoRulesCombed["PPMredAlt1"]] *)
(*          - KhAlt1KnotsTheor[2], *)
(*          Assumptions -> And[Element[n[0], Integers], *)
(*                             Element[n[1], Integers], *)
(*                             Element[n[2], Integers], *)
(*                             q > 0, *)
(*                             t > 0]] *)
                            
(* Simplify[(TheorOneOneMMAllEvenRed[g] /. {t -> 1/T}) *)
(*          - TheorOneOneMMAllEvenRed1[g], *)
(*          Assumptions -> Element[g, Integers]] *)
(* Factor[Simplify[(Knotify["PPMred", 2] *)
(*                  /. {NN[_] -> 0})] *)
(*        /((1 + qtThree) /(qtTwo^3) qtTwo^(-1) q t^2)] *)
(* Factor[Knotify[Association[Select[Normal[evoRulesCombed["PPPMred"]], *)
(*                                   Not[Or[MemberQ[#[[1]], q^2 t], *)
(*                                          MemberQ[#[[1]], -q^2 t]]] &]], *)
(*                3] *)
(*        /((1 + qtThree)/qtTwo^4 qtTwo^(-1) q t^2)] *)
(* Factor[Simplify[Coefficient[Coefficient[Coefficient[Knotify["PPMred", 2], NN[0], 1], NN[1], 1], NN[2], 1] *)
(*                 / ((qtThree^3 - qtThree) /qtTwo^3 /qtTwo q t^2) *)
(*                ]] *)
(* Factor[Simplify[Coefficient[Coefficient[Coefficient[Knotify["PPMred", 2], NN[0], 1], NN[1], 1], NN[2], 0] *)
(*                 / (qtThree /qtTwo^2 (-t) q) *)
(*                ]] *)
(* aa = Simplify[Coefficient[Coefficient[Coefficient[Coefficient[ *)
(*     Knotify["PPPMred", 3], *)
(*     NN[0], 1], NN[1], 1], NN[2], 1], NN[3], 1]]; *)
(* Simplify[Coefficient[Coefficient[Coefficient[Coefficient[Knotify["PPPMred", 3], *)
(*                                                          NN[0], 1], NN[1], 0], NN[2], 0], NN[3], 0]] *)
(* aa1 = Simplify[Coefficient[Coefficient[Coefficient[Coefficient[Knotify["PPPMred", 3], *)
(*                                                                NN[0], 1], NN[1], 1], NN[2], 1], NN[3], 0]]; *)

(* Block[{genus = 4}, *)
(*       Simplify[Simplify[ReplaceAll[MkEvoExpr[evoRulesCombed[StringRiffle[Table["M", {i, 0, genus}], ""] <> "red"]], *)
(*                                    Prepend[Map[Rule[n[#], 2 k[#] + 1] &, Range[0, genus - 1]], *)
(*                                            Rule[n[genus], 2 k[genus]]]], *)
(*                         Assumptions -> And @@ Map[Element[k[#], Integers] &, Range[0, genus]]] *)
(*                /ReplaceAll[TheorEvoMM[genus], *)
(*                            Prepend[Map[Rule[n[#], 2 k[#] + 1] &, Range[0, genus - 1]], *)
(*                                    Rule[n[genus], 2 k[genus]]]]]] *)

(* ### vv Figure out, how qt-numbers transform when going between strata ### *)
(* Simplify[qtOne] *)
(* Simplify[qtThree /. {q -> 1/q, t -> 1/t}] *)


Block[{genus = 2, ncomps = 2},
      Simplify[(1/2/(1 + q^2 t) (Product[q + q (q^2 t)^(2 k[i]), {i, genus - ncomps + 1 , genus}]
                                 + (-1)^(ncomps + genus) Product[q + (-1)^genus q (q^2 t)^(2 k[i]), {i, genus - ncomps + 1 , genus}]))
              ]]

Block[{genus = 1, ncomps = 1},
      Simplify[(Simplify[ReplaceAll[MkEvoExpr[evoRulesCombed[StringRiffle[Table["P", {i, 0, genus}], ""] <> "red"]],
                                    Join[Map[Rule[n[#], 2 k[#] + 1] &, Range[0, genus - ncomps]],
                                         Map[Rule[n[#], 2 k[#]] &, Range[genus - ncomps + 1, genus]]]],
                         Assumptions -> And @@ Map[Element[k[#], Integers] &, Range[0, genus]]]
                - q ReplaceAll[TheorEvo[genus],
                               Join[Map[Rule[n[#], 2 k[#] + 1] &, Range[0, genus - ncomps]],
                                    Map[Rule[n[#], 2 k[#]] &, Range[genus - ncomps + 1, genus]]]])
               /((1+t)/2/(1 + q^2 t) q^(genus - ncomps + 2)
                 Product[(t q^2)^(2 k[i] + 1), {i, 0, genus - ncomps}]
                 (Product[q + q (q^2 t)^(2 k[i]), {i, genus - ncomps + 1 , genus}]
                  + (-1)^(genus + ncomps +1) Product[q - q (q^2 t)^(2 k[i]), {i, genus - ncomps + 1 , genus}]))
              ]]




Simplify[MkEvoExpr[CombUpEvoMap2[evoRulesCombed["PPred"]]]
         - q TheorEvo[1]
         - TheorEvoRedCorr[1]]
    
Factor[Simplify[MkEvoExpr[CombUpEvoMap2[evoRulesCombed["PPPred"]]]
                - q TheorEvo[2]
                - TheorEvoRedCorr[2]]]

Factor[Simplify[MkEvoExpr[CombUpEvoMap2[evoRulesCombed["PPPPred"]]]
                - q TheorEvo[3]
                - TheorEvoRedCorr[3]]]

Factor[Simplify[MkEvoExpr[CombUpEvoMap2[evoRulesCombed["PPPPPred"]]]
                - q TheorEvo[4]
                - TheorEvoRedCorr[4]]]

Apart[(CombUpEvoMap2[evoRulesCombed["MMred"]][Mask[1,1]]
       /. {t -> 1/t})
      - TheorOneOneMMAllEvenRed[1]
      , t]

Apart[(CombUpEvoMap2[evoRulesCombed["MMMred"]][Mask[1,1,1]] /. {t -> 1/t})
      - TheorOneOneMMAllEvenRed[2]
      , t]

Apart[(CombUpEvoMap2[evoRulesCombed["MMMMred"]][Mask[1,1,1,1]] /. {t -> 1/t})
      - TheorOneOneMMAllEvenRed[3]
      , t]

Apart[(CombUpEvoMap2[evoRulesCombed["MMMMMred"]][Mask[1,1,1,1,1]] /. {t -> 1/t})
      - TheorOneOneMMAllEvenRed[4]
      , t]

TheorQSTQSTAllEvenRed[g_] :=
    (0);

Block[{g = 1},
      Apart[Factor[CombUpEvoMap2[evoRulesCombed["PPred"]][Mask @@ Table[q^2 t, {i, 0, g}]]
             (* TheorQSTQSTAllEvenRed[g] *)
                   (q t)^g],
            t]]

                                 2               2
          2       2         1 + q          -1 + q
Out[77]= q  (1 + q ) t + ------------- + ------------
                                  2              2
                         2 (-1 + q  t)   2 (1 + q  t)

Block[{g = 2},
      Factor[ExpandNumerator[Factor[CombUpEvoMap2[evoRulesCombed["PPPred"]][Mask @@ Table[q^2 t, {i, 0, g}]]
                                    (* - TheorQSTQSTAllEvenRed[g] *)
                                    (q t)^g (1 - q^2 t)^g (1 + q^2 t)
                                    (* - (1 - q^2 t) *)
                                   ]]]]

               4          4  2        2      4  2
Out[68]= (1 + q  t) (1 + q  t ) (1 - q  t + q  t )

Block[{g = 3},
      Factor[ExpandNumerator[Simplify[CombUpEvoMap2[evoRulesCombed["PPPPred"]][Mask @@ Table[q^2 t, {i, 0, g}]]
                                      (* - TheorQSTQSTAllEvenRed[g] *)
                                      (q t)^g (1 - q^2 t)^g (1 + q^2 t)
                                      + (1 + q^4 t)(1 + q^4 t^2)(1 - q^2 t + q^4 t^2)^3]]]]


Apart[CombUpEvoMap2[evoRulesCombed["PPPred"]][Mask[1,1,1]]
      - TheorQSTQSTAllEvenRed[2], t]
Apart[CombUpEvoMap2[evoRulesCombed["PPPPred"]][Mask[1,1,1,1]]
      - TheorQSTQSTAllEvenRed[3], t]


Block[{k = 1},
      Expand[Simplify[{(KhReduced[PD[BR[2, Table[1, {i, 1, 2 k + 1}]]]][q,t] /. {q -> 1/q, t -> 1/t})
                       , Kh[PD[BR[2, Table[1, {i, 1, 2 k + 1}]]]][q,t]}]]]


Block[{k = 5},
      Expand[Simplify[(MkEvoExpr[evoRules["PP"]] /. {n[0] -> 2 k + 1, n[1] -> 0})
                      - UnreducedGenusOneKhovanov[k] * q^(2 k)]]]

Block[{k = 6},
      Expand[Simplify[(MkEvoExpr[evoRules["PPred"]] /. {n[0] -> 2 k + 1, n[1] -> 0})
                      - ReducedGenusOneKhovanov[k] q^(2 k - 1)]]]


Simplify[MkEvoExpr[evoRules["PPred"]]
         /(MkEvoExpr[evoRulesCombed["PPred"]] /. {q -> 1/q, t -> 1/t}),
         Assumptions -> q > 0 && t > 0 && Element[n[0], Integers] && Element[n[1], Integers]]

          3 (n[0] + n[1])  n[0] + n[1]
Out[37]= q                t
    

Simplify[(MkEvoExpr[evoRulesCombed["PPred"]] /. {n[0] -> 2 k + 1, n[1] -> 0})
         / ((ReducedGenusOneKhovanov[k] q^(2 k - 1) /. {q -> 1/q, t -> 1/t}) (t q^3)^(2 k + 1)),
         Assumptions -> q > 0 && t > 0 && Element[n[0], Integers] && Element[n[1], Integers] && Element[k, Integers]]



Block[{k = 5},
      Simplify[KhReduced[PD[BR[2, Table[1, {i, 1, 2 k + 1}]]]][q,t] (1 - q^2 t)
               /((1 - q^2 t + q^4 t^2) - (t q^2)^(2 k + 2))]]

Block[{k = 1},
      Expand[Simplify[{(KhReduced[PD[BR[2, Table[1, {i, 1, 2 k + 1}]]]][q,t] /. {q -> 1/q, t -> 1/t})
                       , Kh[PD[BR[2, Table[1, {i, 1, 2 k + 1}]]]][q,t]}]]]

                  
          1     1       1         3    5  2    9  3
Out[55]= {- + ----- + -----, q + q  + q  t  + q  t }
          q    7  3    5  2
              q  t    q  t


Block[{k = 4},
      Factor[Simplify[MkEvoExpr[evoRules["PPred"]] /. {n[1] -> 2 k + 1 - n[0]},
                      Assumptions -> Element[k, Integers]]
             / KhReduced[PD[BR[2, Table[1, {i, 1, 2 k + 1}]]]][q,t]
            ]]


(* theorCross1 = ExpandNumerator[Simplify[qtOne / qtTwo (qtThree/qtTwo)^2 + qtOne qtThree /qtTwo /(-qtTwo)^2]]; *)

evoRulesSymrest["PPP"][Mask[-1,-1,-1]]

TheorEvoCorr[2]

Module[{g = 2},
       Factor[Simplify[(MkEvoExpr[(* bb *) evoRulesSymrest["PPP"]]
                        - TheorEvo[g] - TheorEvoCorr[g] - TheorEvoCorr2[g])
                      ]]]

                   n[0]            n[1]            n[2]   3
         (-1 + (-1)    ) (-1 + (-1)    ) (-1 + (-1)    ) q  (1 + t)
Out[39]= ----------------------------------------------------------
                                        2
                                4 (1 + q  t)

         
Factor[Simplify[evoRulesSymrest["PPP"][Mask[-1,-1,-1]]]]

           3
          q  (1 + t)
Out[15]= ------------
                 2
         4 (1 + q  t)



Factor[Simplify[evoRulesSymrest["PPP"][Mask[q^2 t, q^2 t, 1]]
                - theorCross1]]
 
           3
          q  (1 + t)
Out[14]= ------------
                 2
         2 (1 + q  t)


Simplify[TheorEvo[2]]

   
FullSymmRestore["PPP"];



SymmetricallyRestoreEvoMap[evoRulesCombed["PPPPP"]][Mask[-1,-1,-1,-1,-1]]

FullSymmRestore["PPPPP"]

CheckRulesSymmetricQ[evoRulesCombed["PPPP"]]

Factor[Simplify[evoRulesCombed["PPPP"]]]

(* ### vv The three "positive" covariant regions ### *)
aa = SymmRestoreNPletEvoMap[evoRulesCombed["MPPAlt1"],
                            evoRulesCombed["PMPAlt1"],
                            evoRulesCombed["PPMAlt1"]];
bb = Map[Factor[Simplify[# /. (Solve[Factor[Simplify[#]][Mask[1,-1,-1]] == 0,
                                     AA[1,1,1]][[1]])]] &,
         aa];

(* ### vv The three "negative" covariant regions ### *)
aa = SymmRestoreNPletEvoMap[evoRulesCombed["PMMAlt1"],
                            evoRulesCombed["MPMAlt1"],
                            evoRulesCombed["MMPAlt1"]];
bb = Map[Factor[Simplify[# /. (Solve[Factor[Simplify[#]][Mask[1,-1,-1]] == 0,
                                     AA[1,1,1]][[1]])]] &,
         aa];

Factor[Simplify[bb[[1]]]]

(* ### vv The three "positive" covariant regions ### *)
aa = SymmetricallyRestoreEvoMap[evoRulesCombed["PPPPP"]];
bb = Factor[Simplify[aa /. (Solve[Factor[Simplify[aa]][Mask[1,1,1,-1,-1]] == 0,
                                  AA[1,1,1,1,1]][[1]])]];

bb


(* ### vvv Figuring out evolution coefficient of (1)^(g+1) ### *)
(* B[TheorOneCoeff[g_] := *)
(*     (q^(g-1)/2^g q^2 (t+1)/(1 + q^2 t) + q^(g-1) (1 + q^4 t)/(1 - q^2 t)^(g)/(1 + q^2 t) *)
(*      (\* + q^(g+1)/2^g /(1 + q^2 t) *\)); *)
(*   Apart[FullSimplify[evoRulesCombed["PP"][Mask[1,1]] *)
(*                      - TheorOneCoeff[1]], *)
(*         t] *)
(*   Apart[FullSimplify[evoRulesCombed["PPP"][Mask[1,1,1]] *)
(*                      - TheorOneCoeff[2]], *)
(*         t] *)
(*   Apart[FullSimplify[evoRulesCombed["PPPP"][Mask[1,1,1,1]] *)
(*                      - TheorOneCoeff[3]], *)
(*         t] *)
(*   Apart[FullSimplify[evoRulesCombed["PPPPP"][Mask[1,1,1,1,1]] *)
(*                      - TheorOneCoeff[4]], *)
(*         t] // InputForm *)
(*   Apart[FullSimplify[evoRulesCombed["PPPPPP"][Mask[1,1,1,1,1,1]] *)
(*                      - TheorOneCoeff[5]], *)
(*         t] // InputForm] *)

TheorTwoCoeff[g_] :=
    (1 + q^4 t) (1 + q^4 t^2) (1 - q^2 t + q^4 t^2)^(g-1)
    /q^(g+1) /t^(g) /(-1 + q^2 t)^g /(1 + q^2 t);

TheorQSquaredTEvenGenus[g_] :=
    (- t)(1 + q^4 t)/(1 + q^2 t)/(1 - q^2 t)
    * (q^(g+1) (1 - q^2 t + q^4 t^2) /q^2 /t /(1 - q^2 t)^(g+1)
       - (1 - q^2 t + q^4 t^2)^(g+1)/q^(g+1)/t^(g+1)/(1 - q^2 t)^(g+1));
AuxQSquaredTTerm[g_] :=
    q^(g-1) (1 + (1 - 1/2^g)(-1 + q^2)/(1 + q^2 t)
             + (1 - q^2)/2/(1 - q^2 t)^g Sum[1/2^i (1 - q^2 t)^i, {i, 0, g-1}]
             + q^2/(1 - q^2 t)^g);
TheorQSquaredTOddGenusPart[g_] :=
    (1 + q^4 t)/(1 + q^2 t)/(1 - q^2 t)
    * (q^(g+1) t/(1 - q^2 t)^(g+1) - t (1 - q^2 t + q^4 t^2)^(g+1)/q^(g+1)/t^(g+1)/(1 - q^2 t)^(g+1));
TheorQSquaredTOddGenusWhole[g_] :=
    ((1 + q^4 t)/(1 + q^2 t)/(1 - q^2 t) (-t) (1 - q^2 t + q^4 t^2)^(g+1)/q^(g+1)/t^(g+1)/(1 - q^2 t)^(g+1)
     + (1 + q^4 t) q^(g+1)/(1 - q^2 t)^(g+2)/(1 + q^2 t)/q^2 (1 - q^2 t + q^4 t^2)
     + q^(g+1) (1 + t)/(1 + q^2 t));
TheorQSquaredTAllGenera[g_] :=
    (s1 (1 + q^4 t)/(1 + q^2 t)/(-1 + q^2 t) t (1 - q^2 t + q^4 t^2)^(g+1)/q^(g+1)/t^(g+1)/(-1 + q^2 t)^(g+1)
     - s2 (1 + q^4 t)/(1 + q^2 t)/(-1 + q^2 t) (1 - q^2 t + q^4 t^2) /q^2 q^(g+1)/(-1 + q^2 t)^(g+1)
     + s3 1/2 (1 - (-1)^g) q^(g+1) (t + 1)/(1 + q^2 t));

Simplify[AuxQSquaredTTerm[g]]

          -1 + g       4      2               2   g
         q       (1 + q  t + q  (1 + t) (1 - q  t) )
Out[73]= -------------------------------------------
                         2   g       2
                   (1 - q  t)  (1 + q  t)

anExprEvenGenus = Simplify[Sum[TheorTwoCoeff[2 k - 2 i] q^(2 i)/(1 - q^2 t)^(2 i),
                               {i, 0, k - 1}] (* /. {q -> E, t -> Pi} *),
                           Assumptions -> q > 0 && t > 0 && Element[k, Integers]] /. {k -> g/2};

anExprOddGenus = Simplify[Sum[TheorTwoCoeff[2 k + 1 - 2 i] q^(2 i)/(1 - q^2 t)^(2 i),
                              {i, 0, k}] (* /. {q -> E, t -> Pi} *),
                          Assumptions -> q > 0 && t > 0 && Element[k, Integers]] /. {k -> (g-1)/2};


(* FullSimplify[anExprOddGenus] // TeXForm *)

Block[{s1 = 1, s2 = 1, s3 = 1},
      Apart[Factor[FullSimplify[evoRulesCombed["PP"][Mask[q^2 t, q^2 t]]
                                (* - TheorTwoCoeff[1] *)
                                (* - TheorQSquaredTOddGenus[1] *)
                                (* - AuxQSquaredTTerm[1] *)
                                (* - TheorQSquaredTOddGenusWhole[1] *)
                                - TheorQSquaredTAllGenera[1]
                                (* - 1 - (1 - 1/2)(-1 + q^2)/(1 + q^2 t) *)
                                (* - (1 - q^2)/2/(1 - q^2 t) Sum[1/2^i (1 - q^2 t)^i, {i, 0, 0}] *)
                                (* - q^2/(1 - q^2 t) *)
                               ]],
            t]]

Block[{s1 = 1, s2 = 1, s3 = 1},
      Factor[FullSimplify[evoRulesSymrest["PPP"][Mask[q^2 t, q^2 t, q^2 t]]
                          (* - TheorTwoCoeff[2] *)
                          - TheorQSquaredTAllGenera[2]
                          (* - TheorQSquaredTEvenGenus[2] *)
                          (* - (anExpr /. {g -> 2}) *)
                         ]]]

Block[{s1 = 1, s2 = 1, s3 = 1},
      Apart[Factor[FullSimplify[evoRulesCombed["PPPP"][Mask[q^2 t, q^2 t, q^2 t, q^2 t]]
                                (* - TheorTwoCoeff[3] - q^2 /(1 - q^2 t)^2 TheorTwoCoeff[1] *)
                               ]
                   (* - q^2(1 + (1 - 1/8)(-1 + q^2)/(1 + q^2 t) *)
                   (*       + (1 - q^2)/2/(1 - q^2 t)^3 Sum[1/2^i (1 - q^2 t)^i, {i, 0, 2}] *)
                   (*       + q^2/(1 - q^2 t)^3) *)
                   - TheorQSquaredTAllGenera[3]
                   (* - TheorQSquaredTOddGenusWhole[3] *)
                   (* - TheorQSquaredTOddGenus[3] *)
                   (* - AuxQSquaredTTerm[3] *)
                  ], t]]

(* ### vv The three "positive" covariant regions ### *)
aa = SymmetricallyRestoreEvoMap[evoRulesCombed["PPPPP"]];
bb = Factor[Simplify[aa /. (Solve[Factor[Simplify[aa]][Mask[1,1,1,-1,-1]] == 0,
                                  AA[1,1,1,1,1]][[1]])]];

Block[{s1 = 1, s2 = 1, s3 = 1},
      Factor[FullSimplify[evoRulesCombed["PPPPP"][Mask[q^2 t, q^2 t, q^2 t, q^2 t, q^2 t]]
                          (* - TheorTwoCoeff[4] - q^2 /(1 - q^2 t)^2 TheorTwoCoeff[2] *)
                          (* - TheorQSquaredTEvenGenus[4] *)
                          - TheorQSquaredTAllGenera[4]
                          (* - (anExpr /. {g -> 4}) *)
                         ]]]

Block[{s1 = 1, s2 = 1, s3 = 1},
      Apart[ExpandNumerator[Factor[FullSimplify[evoRulesCombed["PPPPPP"][Mask @@ Table[q^2 t, {i, 1, 6}]]
                                                (* - TheorTwoCoeff[5] - q^2 /(1 - q^2 t)^2 TheorTwoCoeff[3] *)
                                                (* - q^4 /(1 - q^2 t)^4 TheorTwoCoeff[1] *)
                                                (* - TheorQSquaredTOddGenus[5] *)
                                                (* - AuxQSquaredTTerm[5] *)
                                                (* - TheorQSquaredTOddGenusWhole[5] *)
                                                - TheorQSquaredTAllGenera[5]
                                               ]
                                   (* - q^4 (1 + (1 - 1/32)(-1 + q^2)/(1 + q^2 t) *)
                                   (*        + (1 - q^2)/2/(1 - q^2 t)^5 Sum[1/2^i (1 - q^2 t)^i, {i, 0, 4}] *)
                                   (*        + q^2/(1 - q^2 t)^5) *)
                                  ]],
            t]]


Block[{n = 20},
      Factor[FullSimplify[qq[n] q^(n-1)]]]



FullSymmRestore["PPMAlt1"]

Block[{label = "PPMAlt1"},
      Association[KeyValueMap[Rule[Mask[#1[[2]], #1[[1]], #1[[3]]], #2] &, evoRulesCombed[label]]]
      - evoRulesCombed[label]]
            

PrettyPrintRules[CombUpEvoMap2[evoRulesCombed["MMM"]], <||>]

PrettyPrintRules[Factor[Simplify[evoRulesCombed["PPred"]]], <||>]

Out[4]//TeXForm= 
   \frac{(-1)^{n_0+n_1} q \left(q^4 T^2+q^3 T-q^2 T-q^2+q-1\right)}{2
    \left(q^2 T-1\right) \left(q^2 T+1\right)}+\frac{\left(q^8 T^3-q^7 T^3+q^6
    T^3-q^2 T-q+1\right) \left(-q^2 T\right)^{n_0+n_1}}{2 q T \left(q^2
    T-1\right) \left(q^2 T+1\right)}+\frac{\left(q^8 T^3+q^7 T^3+q^6 T^3-q^2
    T+q+1\right) \left(q^2 T\right)^{n_0+n_1}}{2 q T \left(q^2 T-1\right)
    \left(q^2 T+1\right)}+\frac{q \left(q^4 T^2-q^3 T-q^2 T-q^2-q-1\right)}{2
    \left(q^2 T-1\right) \left(q^2 T+1\right)}



preRules = SymmetricallyRestoreEvoMap[evoRulesCombed["PPMAlt1"]];

Apart[preRules, AA[1,1,1]]


Variables[evoRulesSymrest["MMM"]]

GetAIndets[SymmetricallyRestoreEvoMap[Evaluate[evoRulesCombed["PPM"]]]]

D[AA[1,1,1]^2, AA[1,1,1]]

Out[49]= {AA[1, 1, 1]}

Block[{label = "MMM"},
      PrettyPrintRules[evoRulesSymrest[label],
                       SymmetricallyRestoreEvoMap[Evaluate[evoRulesCombed[label]]]]]

evoRulesCombed["PP"][Mask[-1, -1]]
                                                                              
Block[{label = "PP"},
      PrettyPrintRules[evoRulesCombed[label],
                       <||>]]

Out[19]//TeXForm= 
   \frac{(-1)^{n_0+n_1} q^2 (T+1)}{2 \left(q^2 T+1\right)}+\frac{\left(q^8
    T^3+q^6 T^3-q^2 T+1\right) \left(q^2 T\right)^{n_0+n_1}}{q^2 T \left(q^2
    T-1\right) \left(q^2 T+1\right)}+\frac{q^2 T-q^2-2}{2 \left(q^2
    T-1\right)}
                                                                              
                  
                  

Factor[Simplify[preRules /. Solve[preRules[Mask[1,1,-1]] - preRules[Mask[t q^2, t q^2,-1]] == 0,
                                  AA[1,1,1]][[1]]]]

Select[Normal[Simplify[evoRulesSymrest["PPP"]]],
       0 =!= #[[2]] &] /. {t -> T} // TeXForm

         

Simplify[evoRulesSymrest["PPM"][Mask[1,1,1]] /. {t -> -1}]

Simplify[evoRulesSymrest["PPM"][Mask[t q^2, t q^2, t q^2]] /. {t -> -1}]

Factor[Simplify[evoRulesSymrest["PPP"] - evoRulesSymrest["PPM"]]]

Factor[Simplify[ans2]]


Factor[FullSimplify[evoRulesCombed["PP"][Mask[-1,-1]]]]

           2
          q  (1 + t)
Out[22]= ------------
                 2
         2 (1 + q  t)

evoRulesSymrest["PPP"]

Factor[Simplify[Apart[FullSimplify[evoRulesSymrest["PPP"][Mask[-1,-1,-1]]]


          3
         q  t (1 + t)
Out[12]= ------------
                 2
         4 (1 + q  t)

Factor[Simplify[Apart[FullSimplify[evoRulesCombed["PPPP"][Mask[-1,-1,-1,-1]]]
                      t]]]

          4
         q  t (1 + t)
Out[14]= ------------
                 2
         8 (1 + q  t)


(* ### vv Symbolic checks that my formula coincides with formula (5) from 1412.2616 ### *)
(* Simplify[(funPPM[n0, n1, 2 n2] /. {t -> -1, q -> 1/q}) (-q^(3))^(n0 + n1) *)
(*          - funJones[n0, n1, 2 n2], *)
(*          Assumptions -> Element[n0, Integers] && Element[n1, Integers] && Element[n2, Integers]] *)
(* ### ---------------------------------------------------------------------------------------- ### *)
(* funPPMCombed = MkEvoFunction[CombUpEvoMap[evoRules["PPM"]]]; *)
(* Simplify[(funPPMCombed[n0, n1, 2 n2] /. {t -> -1}) *)
(*          - funJones[n0, n1, 2 n2], *)
(*          Assumptions -> Element[n0, Integers] && Element[n1, Integers] && Element[n2, Integers]] *)
(* ### ^^ Alright, after first combing we still get match with Jones ### *)


funPPMCombed2 = MkEvoFunction[CombUpEvoMap2[CombUpEvoMap[evoRulesPPM]]];

(* ### vv After the second combing, the function is still in agreement with Jones at t = -1 ### *)
Simplify[(funPPMCombed2[2 n0, 2 n1, 2 n2] /. {t -> -1})
         - funJones[2 n0, 2 n1, 2 n2],
         Assumptions -> Element[n0, Integers] && Element[n1, Integers] && Element[n2, Integers]]


evoRulesMMMCombed2 = Association[KeyValueMap[Rule[#1, Factor[Simplify[#2]]] &, CombUpEvoMap2[CombUpEvoMap[evoRulesMMM]]]];
evoRulesPPPCombed2 = Association[KeyValueMap[Rule[#1, Factor[Simplify[#2]]] &, CombUpEvoMap2[CombUpEvoMap[evoRulesPPP]]]];
evoRulesPPMCombed2 = Association[KeyValueMap[Rule[#1, Factor[Simplify[#2]]] &, CombUpEvoMap2[CombUpEvoMap[evoRulesPPM]]]];
evoRulesMMPCombed2 = Association[KeyValueMap[Rule[#1, Factor[Simplify[#2]]] &, CombUpEvoMap2[CombUpEvoMap[evoRulesMMP]]]];
evoRulesPPMAlt1Combed2 = Association[KeyValueMap[Rule[#1, Factor[Simplify[#2]]] &, CombUpEvoMap2[CombUpEvoMap[evoRulesPPMAlt1]]]];
evoRulesMMPAlt1Combed2 = Association[KeyValueMap[Rule[#1, Factor[Simplify[#2]]] &, CombUpEvoMap2[CombUpEvoMap[evoRulesMMPAlt1]]]];
evoRulesPMPAlt1Combed2 = Association[KeyValueMap[Rule[#1, Factor[Simplify[#2]]] &, CombUpEvoMap2[CombUpEvoMap[evoRulesPMPAlt1]]]];
evoRulesMPPAlt1Combed2 = Association[KeyValueMap[Rule[#1, Factor[Simplify[#2]]] &, CombUpEvoMap2[CombUpEvoMap[evoRulesMPPAlt1]]]];
evoRulesMPMAlt1Combed2 = Association[KeyValueMap[Rule[#1, Factor[Simplify[#2]]] &, CombUpEvoMap2[CombUpEvoMap[evoRulesMPMAlt1]]]];
evoRulesPMMAlt1Combed2 = Association[KeyValueMap[Rule[#1, Factor[Simplify[#2]]] &, CombUpEvoMap2[CombUpEvoMap[evoRulesPMMAlt1]]]];

evoRulesMMMDiff = Association[Select[KeyValueMap[Rule[#1, Factor[Simplify[#2]]] &, evoRulesMMMCombed2 - evoRulesPPMCombed2],
                                     0 =!= #[[2]] &]];
evoRulesPPPDiff = Association[Select[KeyValueMap[Rule[#1, Factor[Simplify[#2]]] &, evoRulesPPPCombed2 - evoRulesPPMCombed2],
                                     0 =!= #[[2]] &]];
evoRulesPPMDiff = Association[Select[KeyValueMap[Rule[#1, Factor[Simplify[#2]]] &, evoRulesPPMCombed2 - evoRulesPPMCombed2],
                                     0 =!= #[[2]] &]];
evoRulesPPMDiff = Association[Select[KeyValueMap[Rule[#1, Factor[Simplify[#2]]] &, evoRulesPPMCombed2 - evoRulesPPMCombed2],
                                     0 =!= #[[2]] &]];

(* ### vv The Jones function is indeed symmetric in all of its arguments ### *)
Map[funJones[n1, n2, n3] - funJones @@ # &,
    Permutations[{n1,n2,n3}]]


CombUpEvoMap2[CombUpEvoMap[evoRulesPPM] /. {t -> -1}]

    
(* Module[{n0,n1,n2, max = 5}, *)
(*        Tally[Flatten[Table[Simplify[(funPPP[n0, n1, 2 n2] /. {t -> -1}) *)
(*                                     /(funJones[n0, n1, 2 n2] (-q^(-3))^(n0 + n1 + 0 n2) /. {q -> 1/q})], *)
(*                            {n0, -max, max}, *)
(*                            {n1, -max, max}, *)
(*                            {n2, -max, max}]]]] *)
CCCPicXSize = 300;
CCCPicYSize = 300;
CCCPicXCoordStart = 0;
CCCPicYCoordStart = 0;
CCCBasePointXShift = 15;
CCCBasePointYShift = 15;
CCCLatticeSize = 4;
VisualizeEvolutions[] :=
    Module[{theFd = OpenWrite["/home/popolit/tmp/visualize-evolutions.tex"]},
           Iterate[{n3, MkRangeIter[-CCCLatticeSize, CCCLatticeSize, 2]},
                   WithWrittenFrame[{theFd,
                                     {"$n_3 = ", n3, "$\n\\begin{align}\n",
                                      "\\begin{picture}(", CCCPicXSize, ",", CCCPicYSize, ")"
                                      , "(", -CCCPicXSize/2, ",", -CCCPicYSize/2, ")\n"},
                                     {"\\end{picture}\n", "\\end{align}\n"}},
                                    Iterate[{{n1, n2}, MkTupleIter[{-CCCLatticeSize, CCCLatticeSize},
                                                                   {-CCCLatticeSize, CCCLatticeSize}]},
                                            WithWrittenFrame[{theFd,
                                                              {"\\put(", CCCPicXCoordStart + n1 * CCCBasePointXShift,
                                                               ", ", CCCPicYCoordStart + n2 * CCCBasePointYShift, ") {\n"},
                                                              "}\n"},
                                                             WriteString[theFd, "\\basePoint\n"];
                                                             Module[{expr = PrecompKh[n1,n2,n3]},
                                                                    If[0 === Simplify[funPPP[n1,n2,n3] - expr],
                                                                       WriteString[theFd, "\\urPoint\n"]];
                                                                    If[0 === Simplify[funPPM[n1,n2,n3] - expr],
                                                                       WriteString[theFd, "\\rPoint\n"]];
                                                                    If[0 === Simplify[funMMP[n1,n2,n3] - expr],
                                                                       WriteString[theFd, "\\lPoint\n"]];
                                                                    If[0 === Simplify[funMMM[n1,n2,n3] - expr],
                                                                       WriteString[theFd, "\\dlPoint\n"]];
                                                                    If[0 === Simplify[funPPMAlt1[n1,n2,n3] - expr],
                                                                       WriteString[theFd, "\\uPoint\n"]];
                                                                    If[0 === Simplify[funMMPAlt1[n1,n2,n3] - expr],
                                                                       WriteString[theFd, "\\dPoint\n"]];
                                                                    If[0 === Simplify[funPMPAlt1[n1,n2,n3] - expr],
                                                                       WriteString[theFd, "\\drPoint\n"]];
                                                                    If[0 === Simplify[funMPPAlt1[n1,n2,n3] - expr],
                                                                       WriteString[theFd, "\\ulPoint\n"]];
                                                                    If[0 === Simplify[funMPMAlt1[n1,n2,n3] - expr],
                                                                       WriteString[theFd, "\\drAltPoint\n"]];
                                                                    If[0 === Simplify[funPMMAlt1[n1,n2,n3] - expr],
                                                                       WriteString[theFd, "\\ulAltPoint\n"]];
                                                                   ];
                                                            ]]]];
           Close[theFd];
           Success];

Block[{n1 = 10, n2 = -3, n3 = 6},
      FullSimplify[funPMPAlt1[n1, n2, n3] - PrecompKh[n1, n2, n3]]]

TeXifyEvoRules["+--alt", evoRulesPMMAlt1]

evoRulesPPMMod1 = evoRulesPPM;
evoRulesPPMMod1[{q,q, (t^2 q^4)^(-1)}] = 0;

evoRulesPPMMod1

evoRulesPPMAlt1 - evoRulesPPMMod1

(* ### vv Matching of my and Morozov's conventions about braids orientations and framing ### *)
(* Expand[Factor[Block[{n0 = -5, n1 = 0, n2 = 0}, *)
(*                     Simplify[(funPPP[n0, n1, n2]/(q + q^(-1))^2 /. {t -> -1})]]]] *)
(* Expand[Factor[Block[{n0 = 0, n1 = 0, n2 = 2}, *)
(*                     Simplify[(funPPP[n0, n1, n2] /. {t -> -1})/(q + q^(-1))]]]] *)
(* Block[{n0 = 0, n1 = 0, n2 = 2}, *)
(*       Expand[Simplify[funJones[n0, n1, n2]/(q+q^(-1))^2 (- q^(-15))]]] *)
(* Block[{n0 = 0, n1 = 0, n2 = 3}, *)
(*       Simplify[(funPPP[n0, n1, 2 n2] /. {t -> -1}) *)
(*                /(funJones[n0, n1, 2 n2] (-q^(-3))^(n0 + n1) /. {q -> 1/q})]] *)

Simplify[(evoFun["MM"][n0, n1] /. {t -> -1})
         - (TheorFundJones[1][n0, n1, 2 n2] (-q^(-3))^(n0 + n1) /. {q -> 1/q}),
         Assumptions -> q > 0 && t > 0 && Element[n0, Integers] && Element[n1, Integers]]

(* Module[{n0,n1,n2, max = 5}, *)
(*        Tally[Flatten[Table[Simplify[(funPPP[n0, n1, 2 n2] /. {t -> -1}) *)
(*                                     /(funJones[n0, n1, 2 n2] (-q^(-3))^(n0 + n1 + 0 n2) /. {q -> 1/q})], *)
(*                            {n0, -max, max}, *)
(*                            {n1, -max, max}, *)
(*                            {n2, -max, max}]]]] *)

Block[{CCCLatticeSize = 8},
      VisualizeEvolutions[]]

        
Out[4]= Success

Simplify[funMMP[1,2,4] - PrecompKh[1,2,4]]

anAns = Module[{res = {}},
               Iterate[{ns, MkTupleIter[{-10, -1}, {1, 10}, {0, 10, 2}]},
                       If[Not[Or[0 === Simplify[(funPPP @@ ns) - PrecompKh @@ ns],
                                 0 === Simplify[(funPPM @@ ns) - PrecompKh @@ ns],
                                 0 === Simplify[(funMMP @@ ns) - PrecompKh @@ ns],
                                 0 === Simplify[(funMMM @@ ns) - PrecompKh @@ ns]]],
                          PrependTo[res, ns]]];
               res];

(* funMMM[1,1,1] *)

anAns

Sort[Select[anAns,
            And[#[[1]] < 0, #[[2]] > 0, #[[3]] > 0] &]]




Simplify[fun[1,2,0]]

(* ### vv Here we try to make sense of our evolution answer at least at t = -1 ### *)
Select[KeyValueMap[#1 -> Simplify[#2 /. {t -> -1}] &, evoRules],
       #[[2]] =!= 0 &]

(* a = MkTupleIter @@ Table[AList[1, -1], {i, 1, 1 + 1}]; *)


   
    