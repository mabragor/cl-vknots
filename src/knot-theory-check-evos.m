
<< "knot-theory-knovanov-ev-utils.m";

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
LoadAllPrecomps[2];
Iterate[{regionLabel, MkListIter[Join[regionLabels, {"MM", "PP", "PPPP"}]]},
        Rule[evoFun[regionLabel], MkEvoFunction[evoRules[regionLabel]]]
        /. {Rule -> Set}];
funJones = TheorFundJones[2];
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
Iterate[{regionLabel, MkListIter[Join[regionLabels, {"MM", "PP", "PPPP"}]]},
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
SymmetricallyRestoreEvoMap[assoc_] :=
    Module[{res = <||>, key, val,
            indets = {}},
           Iterate[{{eig1, eig2, eig3}, MkTupleIter[AList[1, -1, t q^2], AList[1, -1, t q^2], AList[1, -1, t q^2]]},
                   If[t q^2 === eig3,
                      AssociateTo[res, Rule[Mask[eig1, eig2, eig3], Lookup[assoc, Mask[eig1, eig2, eig3], 0]]],
                      If[1 === eig3,
                         Block[{},
                               AppendTo[indets, AA[eig1, eig2, eig3]];
                               AssociateTo[res, Rule[Mask[eig1, eig2, eig3], AA[eig1, eig2, eig3]]]],
                         If[-1 === eig3,
                            AssociateTo[res, Rule[Mask[eig1, eig2, eig3],
                                                  Lookup[assoc, Mask[eig1, eig2, -eig3], 0] - AA[eig1, eig2, -eig3]]]]]]];
           (* ### vv We further need to solve for symmetry ### *)
           Module[{eqns = {}},
                  Scan[Function[{eigSet},
                                AppendTo[eqns, Map[Lookup[res, Mask @@ #, 0] - Lookup[res, Mask @@ eigSet, 0] == 0 &,
                                                   Permutations[eigSet]]]],
                       DeleteDuplicates[Map[Sort, Tuples[{1, -1, t q^2}, 3]]]];
                  Module[{ans = Quiet[Solve[Flatten[eqns], indets]]},
                         res /. ans[[1]]]]];
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
FullSymmRestore["PPM"];
FullSymmRestore["PPP"];
FullSymmRestore["MMM"];
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
                  (* ###    These include: each blown up assoc is symmetric w.r.t all of its arguments except i-th ### *)
                  (* ###    When we do a cyclic permutation of argument, we get to the next assoc ### *)
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

PrettyPrintRules[evoRulesCombed["PPPP"], <||>]

Apart[FullSimplify[evoRulesCombed["PP"][Mask[1,1]]], t]

                      2
         1      -1 - q
Out[13]= - + -------------
         2            2
             2 (-1 + q  t)

Apart[FullSimplify[evoRulesCombed["PPP"][Mask[1,1,1]]], t]

                      3                3
         q       q + q           -q + q
Out[14]= - + -------------- + -------------
         4            2   2            2
             2 (-1 + q  t)    4 (-1 + q  t)

Apart[FullSimplify[evoRulesCombed["PPPP"][Mask[1,1,1,1]]], t]

          2        2    4          2    4           2    4
         q       -q  - q          q  - q          -q  + q
Out[12]= -- + -------------- + -------------- + -------------
         8             2   3            2   2            2
              2 (-1 + q  t)    4 (-1 + q  t)    8 (-1 + q  t)


Apart[FullSimplify[evoRulesCombed["PP"][Mask[1,1]]], t]


Block[{index = 1},
      PrettyPrintRulesNaive[bb[[index]],
                            aa[[index]]]]

Out[18]//TeXForm= 
   (-1)^{n_0} \left(\frac{T+1}{4 q \left(q^2
    T+1\right)}-\text{Delta}_1\right)+(-1)^{n_1} \left(\frac{T+1}{4 q
    \left(q^2 T+1\right)}-\text{Delta}_1\right)+(-1)^{n_2} \left(\frac{T+1}{4
    q \left(q^2 T+1\right)}-\text{Delta}_1\right)+(-1)^{n_0+n_1+n_2}
    \left(\frac{T+1}{4 q \left(q^2
    T+1\right)}-\text{Delta}_1\right)+\text{Delta}_1
    (-1)^{n_0+n_1}+\text{Delta}_1 (-1)^{n_0+n_2}+\text{Delta}_1
    (-1)^{n_1+n_2}+\text{Delta}_1+\frac{(-1)^{n_2} (T+1) \left(q^2
    T\right)^{n_0+n_1}}{2 q \left(q^2 T+1\right)}+\frac{(-1)^{n_1} (T+1)
    \left(q^2 T\right)^{n_0+n_2}}{2 q \left(q^2 T+1\right)}+\frac{(-1)^{n_0} q
    (T+1) \left(q^2 T\right)^{n_1+n_2}}{2 \left(q^2 T+1\right)}+\frac{\left(2
    q^8 T^3+q^6 T^3-q^6 T^2-q^2 T+q^2+2\right) \left(q^2 T\right)^{n_1+n_2}}{2
    q \left(q^2 T-1\right)^2 \left(q^2 T+1\right)}+\frac{(T+1) \left(q^4
    T+1\right) \left(q^4 T^2+1\right) \left(q^2 T\right)^{n_1+n_2} \left(-q^4
    T^2\right)^{n_0}}{2 q^3 T \left(q^2 T+1\right)}-\frac{\left(q^4 T+1\right)
    \left(q^4 T^2+1\right) \left(q^4 T^2-q^2 T+1\right) \left(q^2
    T\right)^{n_0+n_1+n_2}}{q^3 T \left(q^2 T-1\right)^2 \left(q^2
    T+1\right)}-\frac{\left(2 q^8 T^4-2 q^6 T^3+q^4 T^3+q^4 T^2+2 q^2
    T+T-1\right) \left(q^2 T\right)^{n_0+n_1}}{2 q \left(q^2 T-1\right)^2
    \left(q^2 T+1\right)}-\frac{\left(2 q^8 T^4-2 q^6 T^3+q^4 T^3+q^4 T^2+2
    q^2 T+T-1\right) \left(q^2 T\right)^{n_0+n_2}}{2 q \left(q^2 T-1\right)^2
    \left(q^2 T+1\right)}+\frac{(T+1) \left(q^4 T+1\right) \left(q^8
    T^4+1\right) \left(q^2 T\right)^{n_1+n_2} \left(q^4 T^2\right)^{n_0}}{2
    q^3 T \left(q^2 T-1\right)^2 \left(q^2 T+1\right)}+\frac{q T^2 \left(q^4
    T+1\right)}{\left(q^2 T-1\right)^2 \left(q^2 T+1\right)}

          

FullSymmRestore["PPMAlt1"]

Block[{label = "PPMAlt1"},
      Association[KeyValueMap[Rule[Mask[#1[[2]], #1[[1]], #1[[3]]], #2] &, evoRulesCombed[label]]]
      - evoRulesCombed[label]]
            

PrettyPrintRules[CombUpEvoMap2[evoRulesCombed["MMM"]], <||>]

Out[5]//TeXForm= 
   -\frac{\left(q^8 T^4-q^6 T^3+q^2 T^2+2 q^2 T-1\right) \left(\left(q^2
    T\right)^{n_1+n_2}+\text{perms}\right)}{q \left(q^2 T-1\right)^2 \left(q^2
    T+1\right)}+\frac{\left(q^4 T+1\right) \left(q^4 T^2+1\right) \left(q^4
    T^2-q^2 T+1\right) \left(q^2 T\right)^{n_0+n_1+n_2}}{q^3 \left(q^2
    T-1\right)^2 \left(q^2 T+1\right)}+\frac{q^6 T^3+q^4 T^3+q^4 T^2-q^2 T^2-2
    q^2 T+T+1}{q \left(q^2 T-1\right)^2 \left(q^2 T+1\right)}

Out[4]//TeXForm= 
   \frac{\left(q^8 T^4-2 q^6 T^3-q^6 T^2+q^2 T-1\right) \left(\left(q^2
    T\right)^{n_1+n_2}+\text{perms}\right)}{q T \left(q^2 T-1\right)^2
    \left(q^2 T+1\right)}+\frac{\left(q^4 T+1\right) \left(q^4 T^2+1\right)
    \left(q^4 T^2-q^2 T+1\right) \left(q^2 T\right)^{n_0+n_1+n_2}}{q^3 T^2
    \left(q^2 T-1\right)^2 \left(q^2 T+1\right)}+\frac{q \left(q^6 T^3+q^6
    T^2-2 q^4 T^2-q^4 T+q^2 T+q^2+1\right)}{\left(q^2 T-1\right)^2 \left(q^2
    T+1\right)}

Out[3]//TeXForm= 
   \frac{\left(q^8 T^3+q^6 T^3-q^4 T^2-q^4 T+q^2+1\right) \left(\left(q^2
    T\right)^{n_1+n_2}+\text{perms}\right)}{q \left(q^2 T-1\right)^2 \left(q^2
    T+1\right)}-\frac{\left(q^4 T+1\right) \left(q^4 T^2+1\right) \left(q^4
    T^2-q^2 T+1\right) \left(q^2 T\right)^{n_0+n_1+n_2}}{q^3 T \left(q^2
    T-1\right)^2 \left(q^2 T+1\right)}+\frac{q \left(q^4 T^3-2 q^2 T^2-2 q^2
    T+1\right)}{\left(q^2 T-1\right)^2 \left(q^2 T+1\right)}

?? SymmetricallyRestoreEvoMap

preRules = SymmetricallyRestoreEvoMap[evoRulesCombed["PPMAlt1"]];

Apart[preRules, AA[1,1,1]]


Variables[evoRulesSymrest["MMM"]]

GetAIndets[SymmetricallyRestoreEvoMap[Evaluate[evoRulesCombed["PPM"]]]]

D[AA[1,1,1]^2, AA[1,1,1]]

Out[49]= {AA[1, 1, 1]}

Block[{label = "MMM"},
      PrettyPrintRules[evoRulesSymrest[label],
                       SymmetricallyRestoreEvoMap[Evaluate[evoRulesCombed[label]]]]]

                  
                  

Factor[Simplify[preRules /. Solve[preRules[Mask[1,1,-1]] - preRules[Mask[t q^2, t q^2,-1]] == 0,
                                  AA[1,1,1]][[1]]]]

Select[Normal[Simplify[evoRulesSymrest["PPP"]]],
       0 =!= #[[2]] &] /. {t -> T} // TeXForm

         

Simplify[evoRulesSymrest["PPM"][Mask[1,1,1]] /. {t -> -1}]

Simplify[evoRulesSymrest["PPM"][Mask[t q^2, t q^2, t q^2]] /. {t -> -1}]

Factor[Simplify[evoRulesSymrest["PPP"] - evoRulesSymrest["PPM"]]]

Factor[Simplify[ans2]]

                   
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
VizualizeEvolutions[] :=
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
      VizualizeEvolutions[]]

        
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


   
    