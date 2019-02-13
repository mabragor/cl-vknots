
<< "knot-theory-knovanov-ev-utils.m";

evoRulesMMM = Get[EvoFname[{-1,-1,-1}]];
evoRulesPPP = Get[EvoFname[{1,1,1}]];
evoRulesPPM = Get[EvoFname[{1,1,-1}]];
evoRulesMMP = Get[EvoFname[{-1,-1,1}]];
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
funPPP = MkEvoFunction[evoRulesPPP];
funPPM = MkEvoFunction[evoRulesPPM];
funMMM = MkEvoFunction[evoRulesMMM];
funMMP = MkEvoFunction[evoRulesMMP];
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
(* ### vv Matching my braid orientation conventions with Morozov's ### *)
(* Expand[Factor[Block[{n0 = -5, n1 = 0, n2 = 0}, *)
(*                     Simplify[(funPPP[n0, n1, n2]/(q + q^(-1))^2 /. {t -> -1})]]]] *)
(* Expand[Factor[Block[{n0 = 0, n1 = 0, n2 = 2}, *)
(*                     Simplify[(funPPP[n0, n1, n2] /. {t -> -1})/(q + q^(-1))]]]] *)
(* Block[{n0 = 0, n1 = 0, n2 = 2}, *)
(*       Expand[Simplify[funJones[n0, n1, n2]/(q+q^(-1))^2 (- q^(-15))]]] *)
(* Block[{n0 = 0, n1 = 0, n2 = 3}, *)
(*       Simplify[(funPPP[n0, n1, 2 n2] /. {t -> -1}) *)
(*                /(funJones[n0, n1, 2 n2] (-q^(-3))^(n0 + n1) /. {q -> 1/q})]] *)
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
VizualizeEvolutions[] :=
    Module[{theFd = OpenWrite["/home/popolit/tmp/visualize-evolutions.tex"]},
           Iterate[{n3, MkRangeIter[-10, 10, 2]},
                   WithWrittenFrame[{theFd,
                                     {"$n_3 = ", n3, "$\n\\begin{align}\n", "\\begin{picture}(", CCCPicXSize, ",", CCCPicYSize, ")\n"},
                                     {"\\end{picture}\n", "\\end{align}\n"}},
                                    Iterate[{{n1, n2}, MkTupleIter[{-10, 10}, {-10, 10}]},
                                            WithWrittenFrame[{theFd,
                                                              {"\\put(", CCCPicXCoordStart + n1 * CCCBasePointXShift,
                                                               ", ", CCCPicYCoordStart + n2 * CCCBasePointYShift, ") {\n"},
                                                              "}\n"},
                                                             WriteString[theFd, "\\basePoint\n"];
                                                             If[0 === Simplify[funPPP[n1,n2,n3] - PrecompKh[n1,n2,n3]],
                                                                WriteString[theFd, "\\urPoint\n"]];
                                                             If[0 === Simplify[funPPM[n1,n2,n3] - PrecompKh[n1,n2,n3]],
                                                                WriteString[theFd, "\\rPoint\n"]];
                                                             If[0 === Simplify[funMMP[n1,n2,n3] - PrecompKh[n1,n2,n3]],
                                                                WriteString[theFd, "\\lPoint\n"]];
                                                             If[0 === Simplify[funMMM[n1,n2,n3] - PrecompKh[n1,n2,n3]],
                                                                WriteString[theFd, "\\dlPoint\n"]]]]]];
           Close[theFd];
           Success];

VizualizeEvolutions[]

Out[14]= Success

Simplify[funMMP[1,2,4] - PrecompKh[1,2,4]]

Out[10]= 0

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


   
    