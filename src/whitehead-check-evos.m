
(* ############################################################################################ *)
(* ### In this file we study the evolutions of whiteheadized links we pre-calculated before ### *)
(* ############################################################################################ *)

(* ### vv BEGINIMPORTS ### *)
<< "knot-theory-knovanov-ev-utils.m";
(* ### ^^ ENDIMPORTS ### *)

(* ### vv BEGINLIB ### *)
LoadWhiteheadizedPrecomps[knot_] :=
    Module[{fname = (CCCDataDir <> "/kh-red-precomp-whiteheadized-rolfsen-"
                     <> KnotToFname[knot] <> ".m")},
           Get[fname]];
LoadTwistedPrecomps[n_] :=
    Module[{fname = (CCCDataDir <> "/kh-red-precomp-twisted-twisted-"
                     <> ToString[n] <> ".m")},
           Get[fname]];
LoadTwTwoStrandPrecomps[n_] :=
    (* ### ^^ Load the precomputed before 2-cables of twist knots, with a simple 2-strand braid inserted into the cable. ### *)
    Module[{fname = (CCCDataDir <> "/kh-red-precomp-twisted-two-strand-"
                     <> ToString[n] <> ".m")},
           Get[fname]];
KnotToFname[Knot[a_, b_]] :=
    ("knot-" <> ToString[a] <> "-" <> ToString[b]);
FitUR[knot_, a_] :=
    Block[{kA = a,
           kB = a,
           CCCEigenvaluesCritLength = Null,
           extraPoints = 1},
          LoadWhiteheadizedPrecomps[knot];
          FitFamilyWithEigenvaluesGradual[Function[{k1, k2},
                                                   PrecompKhRed[knot, 2 k1 + kA, 2 k2 + kB]],
                                          Prepend[{1, (t q^2)^(-1)}, 2 k + kA],
                                          Prepend[{1, (t q^2)^(-1)}, 2 k + kB]]];
FitUL[knot_, a_] :=
    Block[{kA = -a,
           kB = a,
           CCCEigenvaluesCritLength = Null,
           extraPoints = 1},
          LoadWhiteheadizedPrecomps[knot];
          FitFamilyWithEigenvaluesGradual[Function[{k1, k2},
                                                   PrecompKhRed[knot, - 2 k1 + kA, 2 k2 + kB]],
                                          Prepend[{1, (t q^2)^(-1)}, - 2 k + kA],
                                          Prepend[{1, (t q^2)^(-1)}, 2 k + kB]]];
FitDL[knot_, a_] :=
    Block[{kA = -a,
           kB = -a,
           CCCEigenvaluesCritLength = Null,
           extraPoints = 1},
          LoadWhiteheadizedPrecomps[knot];
          FitFamilyWithEigenvaluesGradual[Function[{k1, k2},
                                                   PrecompKhRed[knot, - 2 k1 + kA, - 2 k2 + kB]],
                                          Prepend[{1, (t q^2)^(-1)}, - 2 k + kA],
                                          Prepend[{1, (t q^2)^(-1)}, - 2 k + kB]]];
FitDR[knot_, a_] :=
    Block[{kA = a,
           kB = -a,
           CCCEigenvaluesCritLength = Null,
           extraPoints = 1},
          LoadWhiteheadizedPrecomps[knot];
          FitFamilyWithEigenvaluesGradual[Function[{k1, k2},
                                                   PrecompKhRed[knot, 2 k1 + kA, - 2 k2 + kB]],
                                          Prepend[{1, (t q^2)^(-1)}, 2 k + kA],
                                          Prepend[{1, (t q^2)^(-1)}, - 2 k + kB]]];
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
CCCPicXSize = 300;
CCCPicYSize = 300;
CCCPicXCoordStart = 0;
CCCPicYCoordStart = 0;
CCCBasePointXShift = 15;
CCCBasePointYShift = 15;
CCCLatticeSize = 10;
VisualizeWhiteheadizedEvolutions[knot_] :=
    Module[{theFd = OpenWrite["/home/popolit/tmp/visualize-whiteheadized-evolutions.tex"]},
           WithWrittenFrame[{theFd,
                             {"\\begin{align}\n",
                              "\\begin{picture}(", CCCPicXSize, ",", CCCPicYSize, ")"
                              , "(", -CCCPicXSize/2, ",", -CCCPicYSize/2, ")\n"},
                             {"\\end{picture}\n", "\\end{align}\n"}},
                            Iterate[{{n1, n2}, MkTupleIter[{-CCCLatticeSize, CCCLatticeSize, 2},
                                                           {-CCCLatticeSize, CCCLatticeSize, 2}]},
                                    WithWrittenFrame[{theFd,
                                                      {"\\put(", CCCPicXCoordStart + n1 * CCCBasePointXShift,
                                                       ", ", CCCPicYCoordStart + n2 * CCCBasePointYShift, ") {\n"},
                                                      "}\n"},
                                                     WriteString[theFd, "\\basePoint\n"];
                                                     Module[{expr = PrecompKhRed[knot, n1,n2]},
                                                            If[0 === Simplify[FunUR[knot][n1,n2] - expr],
                                                               WriteString[theFd, "\\urPoint\n"]];
                                                            If[0 === Simplify[FunUL[knot][n1,n2] - expr],
                                                               WriteString[theFd, "\\ulPoint\n"]];
                                                            If[0 === Simplify[FunDR[knot][n1,n2] - expr],
                                                               WriteString[theFd, "\\drPoint\n"]];
                                                            If[0 === Simplify[FunDL[knot][n1,n2] - expr],
                                                               WriteString[theFd, "\\dlPoint\n"]];
                                                           ]]]];
           Close[theFd];
           Success];
FunUR[knot_] := FunUR[knot] =
    MkEvoFunction[Factor[Simplify[FitUR[knot, 6]]]];
FunUL[knot_] := FunUL[knot] =
    MkEvoFunction[Factor[Simplify[FitUL[knot, 6]]]];
FunDL[knot_] := FunDL[knot] =
    MkEvoFunction[Factor[Simplify[FitDL[knot, 6]]]];
FunDR[knot_] := FunDR[knot] =
    MkEvoFunction[Factor[Simplify[FitDR[knot, 6]]]];
Braces[x_] :=
    (x - x^(-1));
SatelliteHOMFLY[Knot[3,1], k_] :=
    (1 + Braces[A q] Braces[A/q] ((1 - A^(2 k))/(1 - A^(-2))
                                  + A^(2 k) ((q^2 + q^(-2))^2 - (q^4 - q^2 + 1 - q^(-2) + q^(-4)) A^2 - Braces[q]^2 A^4)));
SatelliteSuperpolynomialMorozov[Knot[3,1], k_] :=
    (1 + (a^2 q^2 t^3 + 1)(a^2 t + q^2)/a^2/q^2/t^2 ((1 - (a t)^(2 k))/(1 + (a t)^(-2))
                                                     + (a^2 t)^k ((q^2 t^unknown1 + q^(-2) t^(- unknown2))^2
                                                                  + a^2 t (q^4 t^2 + 1 + q^(-2) t^(-1) + q^(-4) t^(-4))
                                                                  + (q^2 t + 1)^2/q^2/t a^4 t^2)));
SatelliteSuperpolynomial[Knot[3,1], k_] :=
    (1 - (a^2 q^2 t^3 + 1)(a^2 + q^2 t)/a^2/q^2/t^2 ((1 - (a^2 (-t))^k)/(1 + 1/(a^2 t))
                                                     + (a^2 (-t))^k ((q^2 t^2 + q^(-2) t^(-2))^2
                                                                     + a^2 t (q^4 t^4 - q^2 t^2 + 1
                                                                              - q^(-2) t^(-2) + q^(-4) t^(-4))
                                                                     - a^4 t^2 (- q t + 1/q/t)^2 )));
TwistHOMFLY[k_] :=
    (1 + Braces[A q] Braces[A/q] (1 - A^(2 k)) /(1 - A^(-2)));
SatelliteHOMFLY[TorusKnot[2, m_], k_] :=
    Module[{p = (m - 1)/2},
           TwistHOMFLY[k]
           - (Braces[A q] Braces[A] Braces[A/q] A^(k + 5)/(q + q^(-1))^2
              ((q + q^(-1))^2 Braces[q]^2 /Braces[A q] /Braces[A]^2 /Braces[A/q] (A^(8 p) - 1)
               + q^2 A^(-2) Braces[A/q^3] /Braces[q]^2 /Braces[A/q] (q^(4 p) A^(4 p) - 1)
               + q^(-2) A^(-2) Braces[A q^3] /Braces[q]^2 /Braces[A q] (q^(-4 p) A^(4 p) - 1)
               - 2 A^(-2) Braces[A q^2] Braces[A/q^2] /Braces[q]^2 /Braces[A]^2 (A^(4 p) - 1)))];
UniformAdjointHOMFLY[Knot[3,1]] :=
    (1 + Braces[A]^2 ((A^6 - 2 A^4 - A^2) + Braces[q]^2 (A^8 + 4 A^6) + Braces[q]^4 A^6));
(* ### vv Here are the (maple) formulas I got from Morozov to check my calculations against ### *)
(* ### vv (jmp1) ### *)
(* ### vv The expression for Twist HOMFLY from (8).1801.02407 ### *)
TwistHOMFLYPrime :=
    (A^2
     - A * Braces[q]^2/Braces[A]
     - (A * Braces[A*q] * Braces[A/q] /Braces[A]
        * (M/A^6)));
(* ### vv Formula (16).1801.02407 about HOMFLY of a trefoil satellite ### *)
H16 :=
    (1 + Braces[A*q] Braces[A/q] ((1-M)/(1-1/A^2)
                                  + M * ((q^2+1/q^2)^2 - (q^4-q^2+1-1/q^2+1/q^4) * A^2 - Braces[q]^2*A^4)));
(* ### vv A combination of formulas (8) and (9) from 1801.02407, HOMFLY for trefoil satellite, *note* ### *)
(* ###    the choice of k-parametrization M/A^6, where M = A^(2k) ### *)
H89 :=
    (A^2
     - A * Braces[q]^2/Braces[A]
     - (A * Braces[A*q] * Braces[A/q] /Braces[A]
        * (M/A^6)) * (1 + Braces[A]^2 * (A^6 - 2 * A^4 - A^2 + Braces[q]^2 * (A^8 + 4 * A^6) + Braces[q]^4 * A^6))
    );
H19[p_, w_] :=
    (* ### ^^ A general formula for satellite of a 2-strand torus knot ### *)
    (* ###    `2 p + 1` -- the number of windings of the 2 braids, i.e. we have TorusKnot[2, 2 p + 1] ### *)
    (* ###     `w`      -- the writhe, i.e. the shift of the k-parameter of the windings in the insertion ### *)
    Module[{},
           1
           + Braces[A q] Braces[A/q] (1-M*A^(2*w)) /(1-1/A^2)
           - (Braces[A q] Braces[A] Braces[A/q] M /(A*(q+1/q)^2)
              ((q+1/q)^2 Braces[q]^2 (A^(8 p)-1)/(Braces[A q] Braces[A]^2 Braces[A/q])
               + q^2 Braces[A/q^3] (q^(4 p) A^(4 p)-1) /(A^2 Braces[q]^2 Braces[A/q])
               + Braces[A q^3] (q^(-4 p) A^(4 p)-1) /(q^2 A^2 Braces[q]^2 Braces[A q])
               - 2 Braces[A q^2] Braces[A/q^2] (A^(4 p)-1) /(A^2 Braces[q]^2 Braces[A]^2)))
          ];
TwistedKhovanov[k_] :=
    (* ### ^^ The reduced Khovanov polynomial of the twisted satellite of an unknot ### *)
    (1 + (q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2 q^4 t^2 /(q^4 t^2 - 1) (1 - (q^4 t^2)^k));
TwistedKhovanov[] :=
    (* ### ^^ The reduced Khovanov polynomial of the twisted satellite of an unknot ### *)
    (1 + (q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2 q^4 t^2 /(q^4 t^2 - 1));
(* ### vv Test how two different conventions (18) vs (19) are related ### *)
(* Simplify[(TwistHOMFLY[k] - TwistHOMFLYPrime) /. {M -> A^(2 k + 6)}] *)
(* Factor[Simplify[H89-H16]]; *)
(* Factor[H16-H19[1, -3]]; *)
(* ### ^^ ### *)
(* ### ^^ (jmp1) ### *)
TorusMassagedPositive[Knot[n_,1], k_] :=
    Module[{weight = (n-1)/2 - 1},
           Simplify[((PrecompKhRed[Knot[n,1], 2 k, 2] /. {q -> 1/q, t -> 1/t})
                     - TwistedKhovanov[k + weight]/ (q^2 t^2 (-1)))
                    /((q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2 (q^4 t^2)^(k + weight))]];
TorusMassagedNegative[Knot[n_,1], k_] :=
    Module[{weight = (n-1)/2 - 1},
           Simplify[((PrecompKhRed[Knot[n,1], 2 k, 2] /. {q -> 1/q, t -> 1/t})
                     - TwistedKhovanov[k + weight]/ (q^2 t))
                    /((q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2 (q^4 t^2)^(k + weight))]];
UniformTorusFitPositive[] :=
    Block[{CCCEigenvaluesCritLength = Null,
           extraPoints = 2},
          FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                   TorusMassagedPositive[Knot[2 k1 + 1, 1], 2 - k1]],
                                          Prepend[{t^2 q^4, 1, (t^6 q^8)^(-1)}, k]]];
UniformTorusFitNegative[] :=
    Block[{CCCEigenvaluesCritLength = Null,
           extraPoints = 2},
          FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                   TorusMassagedNegative[Knot[2 k1 + 1, 1], 2 - k1 - 1]],
                                          Prepend[{t^2 q^4, 1, (t^6 q^8)^(-1)}, k]]];
TwistedMassagedPositive[n_, k_] :=
    Module[{weight = n - 2},
           Simplify[((PrecompKhRed[Twisted[n], 2 k] /. {q -> 1/q, t -> 1/t})
                     - TwistedKhovanov[k + weight]/ (q^2 t^2 (-1)))
                    /((q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2 (q^4 t^2)^(k + weight))]];
TwistedMassagedNegative[n_, k_] :=
    Module[{weight = n - 2},
           Simplify[((PrecompKhRed[Twisted[n], 2 k] /. {q -> 1/q, t -> 1/t})
                     - TwistedKhovanov[k + weight]/ (q^2 t ))
                    /((q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2 (q^4 t^2)^(k + weight))]];
TwistedMassagedPositiveNegP[n_, k_] :=
    Module[{weight = n - 2},
           Simplify[((PrecompKhRed[Twisted[n], 2 k] /. {q -> 1/q, t -> 1/t})
                     - TwistedKhovanov[k + weight + 3]/ (q^2 t^2 (-1)))
                    /((q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2 (q^4 t^2)^(k + weight))]];
TwistedMassagedNegativeNegP[n_, k_] :=
    Module[{weight = n - 2},
           Simplify[((PrecompKhRed[Twisted[n], 2 k] /. {q -> 1/q, t -> 1/t})
                     - TwistedKhovanov[k + weight + 3]/ (q^2 t ))
                    /((q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2 (q^4 t^2)^(k + weight))]];
TwTwoCableMassagedPositive[twist_, ncrossings_] :=
    (* ### ^^ Remove the constant eigenvalue contribution from twisted 2-cable (in the posK-posP region) ### *)
    Module[{},
           Simplify[((PrecompKhRed[TwistedTwoSt[twist], ncrossings] /. {q -> 1/q, t -> 1/t})
                     (q^3 t)^(ncrossings + 2 twist - 4)
                     - q^2(1/(1 - q^2 t) + (q^2 t)^(ncrossings + 2 twist - 4) /(q^4 t^2 - 1) (q^6 t^3 + 1) /q^2 /t
                          ))
                    /(q^2 t)^(ncrossings + 2 twist - 4) /((q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2)
                    /(q^2 t) (1 + q^2 t)]];
TwTwoCableMassagedNegative[twist_, ncrossings_] :=
    (* ### ^^ Remove the constant eigenvalue contribution from twisted 2-cable (in the negK-posP region) ### *)
    Module[{},
           Simplify[((PrecompKhRed[TwistedTwoSt[twist], ncrossings] /. {q -> 1/q, t -> 1/t})
                     (q^3 t)^(ncrossings + 2 twist - 4)
                     - q^2 (-t) (1 /(1 - q^2 t) + (q^2 t)^(ncrossings + 2 twist - 4) /(q^4 t^2 - 1) (q^6 t^3 + 1) /q^2 /t))
                    /(q^2 t)^(ncrossings + 2 twist - 4) /((q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2)
                    /(q^2 t) (1 + q^2 t)]];
TwTwoCableMassagedPositiveNegP[twist_, ncrossings_] :=
    (* ### ^^ Remove the constant eigenvalue contribution from twisted 2-cable (in the posK-negP region) ### *)
    Module[{},
           Simplify[((PrecompKhRed[TwistedTwoSt[twist], ncrossings] /. {q -> 1/q, t -> 1/t})
                     (q^3 t)^(ncrossings + 2 twist - 4)
                     - q^2(1/(1 - q^2 t)
                           + q^12 t^6 (q^2 t)^(ncrossings + 2 twist - 4) /(q^4 t^2 - 1) (q^6 t^3 + 1) /q^2 /t
                          ))
                    /(q^2 t)^(ncrossings + 2 twist - 4) /((q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2)
                    /(q^2 t) (1 + q^2 t)]];
TwTwoCableMassagedNegativeNegP[twist_, ncrossings_] :=
    (* ### ^^ Remove the constant eigenvalue contribution from twisted 2-cable (in the negK-negP region) ### *)
    Module[{},
           Simplify[((PrecompKhRed[TwistedTwoSt[twist], ncrossings] /. {q -> 1/q, t -> 1/t})
                     (q^3 t)^(ncrossings + 2 twist - 4)
                     - q^2 (-t) (1 /(1 - q^2 t)
                                 + q^12 t^6 (q^2 t)^(ncrossings + 2 twist - 4) /(q^4 t^2 - 1) (q^6 t^3 + 1) /q^2 /t
                                ))
                    /(q^2 t)^(ncrossings + 2 twist - 4) /((q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2)
                    /(q^2 t) (1 + q^2 t)]];
UniformTwTwoCableFitPositive[] :=
    Block[{CCCEigenvaluesCritLength = Null,
           extraPoints = 3
           , CCCExtraAllowedVars = {aa, bb}
          },
          FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                   TwTwoCableMassagedPositive[2 k1 + 2, 5 - 2 2 (k1 + 1)]],
                                          Prepend[{1, t^(-1) q^(-2), t^(-4) q^(-6)}, 2 k + 2]]];
UniformTwTwoCableFitNegative[] :=
    Block[{CCCEigenvaluesCritLength = Null,
           extraPoints = 3
           , CCCExtraAllowedVars = {aa, bb}
          },
          FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                   TwTwoCableMassagedNegative[2 k1 + 2, 5 - 2 2 (k1 + 1) - 2]],
                                          Prepend[{1, t^(-1) q^(-2), t^(-4) q^(-6)}, 2 k + 2]]];
UniformTwTwoCableFitPositiveNegP[] :=
    Block[{CCCEigenvaluesCritLength = Null,
           extraPoints = 3
           , CCCExtraAllowedVars = {aa, bb}
           , shiftP = -8
          },
          FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                   TwTwoCableMassagedPositiveNegP[2 (k1 + shiftP), -1 - 2 2 (k1 + shiftP)]],
                                          Prepend[{1, t^(-1) q^(-2), t^(-4) q^(-6)}, 2 (k + shiftP)]]];
UniformTwTwoCableFitNegativeNegP[] :=
    Block[{CCCEigenvaluesCritLength = Null,
           extraPoints = 3
           , CCCExtraAllowedVars = {aa, bb}
           , shiftP = -8
          },
          FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                   TwTwoCableMassagedNegativeNegP[2 (k1 + shiftP), -1 - 2 2 (k1 + shiftP) - 2]],
                                          Prepend[{1, t^(-1) q^(-2), t^(-4) q^(-6)}, 2 (k + shiftP)]]];
UniformTwistedFitPositive[] :=
    Block[{CCCEigenvaluesCritLength = Null,
           extraPoints = 3},
          FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                   TwistedMassagedPositive[2 k1 + 2, 1 - 2 k1]],
                                          Prepend[{1, t^(-2) q^(-4), t^(-8) q^(-12)}, k + 1]]];
UniformTwistedFitNegative[] :=
    Block[{CCCEigenvaluesCritLength = Null,
           extraPoints = 3},
          FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                   TwistedMassagedNegative[2 k1 + 2, 0 - 2 k1]],
                                          Prepend[{1, t^(-2) q^(-4), t^(-8) q^(-12)}, k + 1]]];
UniformTwistedFitPositiveNegP[] :=
    Block[{CCCEigenvaluesCritLength = Null,
           extraPoints = 3,
           shiftP = -8},
          FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                   TwistedMassagedPositiveNegP[2 (k1 + shiftP), - 2 (k1 + shiftP)]],
                                          Prepend[{1, t^(-2) q^(-4), t^(-8) q^(-12)}, k + shiftP]]];
UniformTwistedFitNegativeNegP[] :=
    Block[{CCCEigenvaluesCritLength = Null,
           extraPoints = 3,
           shiftP = -8},
          FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                   TwistedMassagedNegativeNegP[2 (k1 + shiftP), -1 - 2 (k1 + shiftP)]],
                                          Prepend[{1, t^(-2) q^(-4), t^(-8) q^(-12)}, k + shiftP]]];
MassagedSuperPositive[knot_, k_] :=
    (* ### ^^ Extract a constant term in the evolution of the twist satellite in the rightmost region. ### *)
    Simplify[((PrecompKhRed[knot, 2 k, 2] /. {q -> 1/q, t -> 1/t})
              - TwistedKhovanov[]/ (q^2 t^2 (-1)))
             (q^4 t^2 - 1) /((q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2 (q^4 t^2)^(k))];
MassagedSuperNegative[knot_, k_] :=
    (* ### ^^ Extract a constant term in the evolution of the twist satellite in the leftmost region. ### *)
    Simplify[((PrecompKhRed[knot, 2 k, 2] /. {q -> 1/q, t -> 1/t})
              - TwistedKhovanov[]/ (q^2 t ))
             (q^4 t^2 - 1) /((q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2 (q^4 t^2)^(k))];
DetermineSuperPositiveArea[knot_, kRightmost_] :=
    (* ### ^^ Determine (with the very naive heuristics), up to which point (in the left direction) ### *)
    (* ###    does the rightmost evolution region stretch ### *)
    Module[{kCritical},
           Module[{k},
                  For[k = kRightmost, True, k = k - 1,
                      Module[{expr = Denominator[MassagedSuperPositive[knot, k]]},
                             (* ### vv if after the massaging we obtain a (q,t)-monomial, we continue *)
                             If[And[SubsetQ[{q, t}, Variables[expr]],
                                    Plus =!= Head[Expand[expr]]],
                                Null,
                                kCritical = k + 1; Break[]]]]];
           Print["kCritical: ", kCritical];
           (* ### vv Now we check that all the found points fit one simple evolution ### *)
           Block[{CCCEigenvaluesCritLength = Null,
                  extraPoints = (kRightmost - kCritical + 1) - 2},
                 Module[{evoCoeffs = FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                                              PrecompKhRed[knot, 2 (k1 + kCritical), 2]],
                                                                     Prepend[{1, (t q^2)^(-1)}, 2 (k + kCritical)]]},
                        If[$Failed =!= evoCoeffs,
                           {$Success, kCritical, kRightmost},
                           {$Failed}]]]];
DetermineSuperNegativeArea[knot_, kLeftmost_] :=
    (* ### ^^ Determine (with the very naive heuristics), up to which point (in the right direction) ### *)
    (* ###    does the leftmost evolution region stretch ### *)
    Module[{kCritical},
           Module[{k},
                  For[k = kLeftmost, True, k = k + 1,
                      Module[{expr = Denominator[MassagedSuperNegative[knot, k]]},
                             (* ### vv if after the massaging we obtain a (q,t)-monomial, we continue *)
                             If[And[SubsetQ[{q, t}, Variables[expr]],
                                    Plus =!= Head[Expand[expr]]],
                                Null,
                                kCritical = k - 1; Break[]]]]];
           Print["kCritical: ", kCritical];
           (* ### vv Now we check that all the found points fit one simple evolution ### *)
           Block[{CCCEigenvaluesCritLength = Null,
                  extraPoints = (kCritical - kLeftmost + 1) - 2},
                 Module[{evoCoeffs = FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                                              PrecompKhRed[knot, 2 (k1 + kLeftmost), 2]],
                                                                     Prepend[{1, (t q^2)^(-1)}, 2 (k + kLeftmost)]]},
                        If[$Failed =!= evoCoeffs,
                           {$Success, kLeftmost, kCritical},
                           {$Failed}]]]];
SimpleSuperTestRig[knot_] :=
    SimpleSuperTestRig[knot, -5, 5];
SimpleSuperTestRig[knot_, min_, max_] :=
    (* ### ^^ A simple rig that tests whether a given knot's twist satellite just has two evolution regions ### *)
    (* ###    (with eigenvalues 1 and (q^2 t)^(-1)) ### *)
    Module[{},
           LoadWhiteheadizedPrecomps[knot];
           Module[{pos = DetermineSuperPositiveArea[knot, max],
                   neg = DetermineSuperNegativeArea[knot, min]},
                  {neg, pos}]];
(* ### vv I need to have a theoretical formula for my reduced Khovanov polynomials of ### *)
(* ###    whitehead satellites of twist knots ### *)
(* ###    ... and for simple 2-strand cables as well ### *)
KhRedTheor[Twisted[twist_], ncrossings_] :=
    (* ### `twist`      -- is even, equal to 2 p for some p. ### *)
    (* ### `ncrossings` -- is also even, equal to 2 k for some k. ### *)
    Block[{epPiece = If[twist > 0, EigenvaluePiecePlus[twist], EigenvaluePieceMinus[twist]],
           thetaFact = If[twist > 0,
                          ThetaPiecePlus[Twisted, twist, ncrossings],
                          ThetaPieceMinus[Twisted, twist, ncrossings]],
           pecPower = If[twist > 0, ncrossings + 2 twist - 4, ncrossings + 2 twist + 2]},
          KhRedTheorInternal[Twisted[twist], ncrossings]];
KhRedTheor[TwistedTwoSt[twist_], ncrossings_] :=
    (* ### `twist`      -- is even, equal to 2 p for some p.    ### *)
    (* ### `ncrossings` -- is odd, equal to 2 k + 1 for some k. ### *)
    Block[{epPiece = If[twist > 0, EigenvaluePiecePlus[twist], EigenvaluePieceMinus[twist]],
           thetaFact = If[twist > 0,
                          ThetaPiecePlus[TwistedTwSt, twist, ncrossings],
                          ThetaPieceMinus[TwistedTwSt, twist, ncrossings]],
           pecPower = If[twist > 0, ncrossings + 2 twist - 4, ncrossings + 2 twist + 2]},
          KhRedTheorInternal[TwistedTwoSt[twist], ncrossings]];
KhRedTheorInternal[TwistedTwoSt[twist_], ncrossings_] :=
    (epPiece (q^2 t) /(1 + q^2 t) (q^2 t)^(ncrossings + 2 twist - 4) ((q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2)
     + thetaFact (q^2/(1 - q^2 t) + (q^2 t)^pecPower /(q^4 t^2 - 1) (q^6 t^3 + 1) /t))
    /(q^3 t)^(ncrossings + 2 twist - 4);
KhRedTheorInternal[Twisted[twist_], ncrossings_] :=
    (epPiece (q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2 (q^2 t)^(ncrossings + 2 twist - 4)
     + thetaFact ((1 + (q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2 q^4 t^2 /(q^4 t^2 - 1) (1 - (q^2 t)^pecPower))
                  / (q^2 t^2 (-1))));
KhRedTheorPosK[TwistedTwoSt[twist_], ncrossings_] :=
    (EigenvaluePiecePlus[twist] (q^2 t) /(1 + q^2 t) (q^2 t)^(ncrossings + 2 twist - 4) ((q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2)
     + (q^2/(1 - q^2 t) + (q^2 t)^(ncrossings + 2 twist - 4) /(q^4 t^2 - 1) (q^6 t^3 + 1) /t))
    /(q^3 t)^(ncrossings + 2 twist - 4);
ThetaPiecePlus[TwistedTwSt, twist_, ncrossings_] :=
    If[ncrossings > 4 - 2 twist,
       1,
       -t];
ThetaPieceMinus[TwistedTwSt, twist_, ncrossings_] :=
    If[ncrossings > -2 - 2 twist,
       1,
       -t];
ThetaPiecePlus[Twisted, twist_, ncrossings_] :=
    If[ncrossings > 4 - 2 twist,
       1,
       -t];
ThetaPieceMinus[Twisted, twist_, ncrossings_] :=
    If[ncrossings > -2 - 2 twist,
       1,
       -t];
EigenvaluePiecePlus[twist_] :=
    (((q^2 t)^(-twist) - 1)/(q^4 t^2 - 1) (1 + t) (1 + t + q^2 (-1 + 2 t + t^2))/(1 - t)
     - ((q^6 t^4)^(-twist) - 1)/(q^6 t^4 - 1) (1 + 3 t + 4 q^2 t^2 + 3 q^4 t^3 + q^4 t^4)/(1 - t)/t
     + ((q^6 t^4)^(-twist) - (q^2 t)^(-twist))/(q^8 t^6 - 1) (1 + t) (1 + t + q^2 t^2 + q^2 t^3 + 2 q^4 t^4 + 2 q^6 t^5) /(1 - t) /t^2
     + t^(-1) (1 + 3 t + t^2) + q^2 (1 + 3 t + t^2) + q^4 t^2 (2 + t) + q^6 t^4 + q^8 t^5 + q^10 t^6
     + (q^2 t)^(-twist) (- q^10 t^6 - q^6 t^3 (1 + t) - q^8 t^4 (1 + t) - (1 + t)^3/t^2 - q^4 t^2 (2 + t) - q^2 (1 + t)(2 + t))
     + (q^6 t^4)^(-twist) (q^2 + q^6 t^3 + q^8 t^4 + t^(-2) + 2 t^(-1)));
EigenvaluePieceMinus[twist_] :=
    (((q^2 t)^(-twist) - 1)/(q^4 t^2 - 1) (1 + t) (1 + t + q^2 t 2)/(1 - t)/t^2
     - ((q^6 t^4)^(-twist) - 1)/(q^6 t^4 - 1) (1 + 3 t + 4 q^2 t^2 + 3 q^4 t^3 + q^4 t^4)/(1 - t)/t^3
     + ((q^6 t^4)^(-twist) - (q^2 t)^(-twist))/(q^8 t^6 - 1) (1 + t) (1 + t + q^2 t^2 + q^2 t^3 + 2 q^4 t^4 + 2 q^6 t^5) /(1 - t) /t^4
     + t^(-3) (1 + 3 t + t^2) + 2 q^2 t^(-1) + q^4 (2 + t) + q^8 t^3
     + (q^2 t)^(-twist) (-(q^10*t^4) - (q^2*(1 + t))/t^2 - q^6*t*(1 + t) - q^8*t^2*(1 + t) - (1 + t)^3/t^4 - q^4*(2 + t))
     + (q^6 t^4)^(-twist) (q^2/t^2 + q^6*t + q^8*t^2 + (1 + 2*t)/t^4));
EnsureTwistedPrecompsLoaded[] :=
    Module[{},
           Module[{j},
                  For[j = 2, j <= 16, j = j + 2,
                      LoadTwistedPrecomps[j];
                      LoadTwistedPrecomps[-j]]];
           Module[{j},
                  For[j = 2, j <= 16, j = j + 2,
                      LoadTwTwoStrandPrecomps[j];
                      LoadTwTwoStrandPrecomps[-j]]]];
TestKhRedTwistedTwSt[] :=
    Module[{twist, ncrossings, res = True},
           EnsureTwistedPrecompsLoaded[];
           For[twist = -16, twist <= 16, twist += 2,
               If[0 === twist, Continue[]];
               For[ncrossings = -4 - 1 - 2 twist, ncrossings <= 8 - 1 - 2 twist, ncrossings += 2,
                   Module[{theor = KhRedTheor[TwistedTwoSt[twist], ncrossings],
                           expr = (PrecompKhRed[TwistedTwoSt[twist], ncrossings] /. {q -> 1/q, t -> 1/t})},
                          If[1 =!= Simplify[Simplify[expr]/Simplify[theor]],
                             Print["Test failed for: ", twist, " ", ncrossings]; res = False]]]];
           res];
TestKhRedTwisted[] :=
    Module[{twist, ncrossings, res = True},
           EnsureTwistedPrecompsLoaded[];
           For[twist = -16, twist <= 16, twist += 2,
               If[0 === twist, Continue[]];
               For[ncrossings = - 8 - 2 twist, ncrossings <= 8 - 2 twist, ncrossings += 2,
                   Module[{theor = KhRedTheor[Twisted[twist], ncrossings],
                           expr = (PrecompKhRed[Twisted[twist], ncrossings] /. {q -> 1/q, t -> 1/t})},
                          If[1 =!= Simplify[Simplify[expr]/Simplify[theor]],
                             If[PrecompKhRed === Head[expr],
                                Print["Uncalculated: ", twist, " ", ncrossings]];
                             Print["Test failed for: ", twist, " ", ncrossings]; res = False]]]];
           res];
Araces[x_] :=
    (* ### ^^ The anticommutator braces ### *)
    (x + x^(-1));
UniformAdjoint[TwistKnot[twist_]] :=
    (1 + Braces[A]^2 A^4/Araces[q]^2 (-2 Araces[q] Araces[q^3] (A^twist - 1)/(A^2 - 1)
                                      + Braces[A q^3] Araces[A/q] ((q^2 A^2)^twist - 1)/((q^2 A^2) - 1)
                                      + Braces[A/q^3] Araces[A q] ((q^(-2) A^2)^twist - 1)/((q^(-2) A^2) - 1)
                                      - 2 Braces[A q^2] Braces[A q^(-2)] (A^(2 twist) - 1)/(A^2 - 1)));
TwSatHOMFLY[TwistKnot[twist_], numcr_] :=
    (A^2 - A Braces[q]^2/Braces[A] - A Braces[A q] Braces[A/q] /Braces[A] A^(numcr + 2 w) UniformAdjoint[TwistKnot[twist]]);
TwTwoHOMFLY[TwistKnot[twist_], numcr_] :=
    (1 + Braces[A q] Braces[A/q] A^(numcr + 2 w) UniformAdjoint[TwistKnot[twist]]);
(* ### ^^ ENDLIB ### *)

Block[{w = -2},
      Expand[Simplify[TwSatHOMFLY[TwistKnot[2], 2] /. {A -> q^2}]]]

         
              6    8    14    16    18      20    22
Out[22]= 1 + q  - q  - q   + q   - q   + 2 q   - q

         
(* ### vv Figure out how exactly is our Khovanov polynomial related to previously computed Twist HOMFLY ### *)
Block[{twist = -4, numcr = -4},
      Factor[((-q^2) (PrecompKhRed[Twisted[twist], numcr] /. {q -> 1/q, t -> -1})
              - (A^2 - A Braces[q]^2/Braces[A]) /. {A -> q^2})
             /(UniformAdjoint[TwistKnot[-twist]] /. {A -> q^2})
             /((-1) A Braces[A q] Braces[A/q] /Braces[A] A^numcr /. {A -> q^2})
             / q^(4 (twist - 2))
            ]]

(* ### vv Figure out how exactly is our Khovanov polynomial related to previously computed HOMFLY ### *)
(* ###    for 2-cable of a twist knot ### *)
(* ###    Not sure that I've correctly interpreted all A-factors ### *)
Block[{twist = -4, numcr = 9},
      Factor[((PrecompKhRed[TwistedTwoSt[twist], numcr] /. {q -> 1/q, t -> -1}) (- q^3)^(numcr + 2 twist - 4)
              - q^2/(1 + q^2))
             /(UniformAdjoint[TwistKnot[-twist]]
               Braces[A q]/Braces[A/q] /Araces[q] q (-1) A^numcr
               /. {A -> q^2})
             / q^(4 (twist - 2))
            ]]




Block[{twist = 6, ncrossings = 1},
      Module[{expr = TwTwoCableMassagedPositive[twist, ncrossings],
              theor = EigenvaluePiecePlus[twist]},
             Simplify[expr - theor]]]


EnsureTwistedPrecompsLoaded[]

TestKhRedTwisted[]

Factor[Simplify[(q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2 q^4 t^2 /(q^4 t^2 - 1) q^2 t /(1 + q^2 t) /(- q^2 t^2)]]

                2      4  2
           1 - q  t + q  t
Out[38]= -(----------------)
                     2
            t (-1 + q  t)

              2      4  2
         1 - q  t + q  t
Out[37]= ----------------
                 2  2
            t - q  t

Simplify[(1 + (q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2 q^4 t^2 /(q^4 t^2 - 1)) q^2 t /(1 + q^2 t) /(- q^2 t^2)]

Simplify[(1 + (q^6 t^3 + 1) (q^4 t + q^2)/q^6/t^2 q^4 t^2 /(q^4 t^2 - 1)) /(- q^2 t^2)]

              4  2
         1 + q  t
Out[39]= ---------
              2  2
         t - q  t


Block[{twist = -4, ncrossings = 11},
      Module[{theor = KhRedTheor[TwistedTwoSt[twist], ncrossings],
              expr = (PrecompKhRed[TwistedTwoSt[twist], ncrossings] /. {q -> 1/q, t -> 1/t})},
             Simplify[Simplify[expr]/Simplify[theor]]]]

Block[{twist = 4, ncrossings = },
      Module[{theor = KhRedTheor[Twisted[twist], ncrossings],
              expr = (PrecompKhRed[Twisted[twist], ncrossings] /. {q -> 1/q, t -> 1/t})},
             Simplify[Simplify[expr]/Simplify[theor]]]]



Block[{k = 0, twist = 4},
      Simplify[TwTwoCableMassagedPositive[twist, 2(k + 1) + 1] - TwTwoCableMassagedPositive[twist, 2 k + 1]]]

(* ### vv LOADTWISTPRECOMPS Load all that we have precomputed about twist-knots ### *)
EnsureTwistedPrecompsLoaded[];
(* ### ^^ LOADTWISTPRECOMPS ### *)

Block[{twist = 4, ncrossings = 5},
      Factor[TwTwoCableMassagedPositive[twist, ncrossings]]]

(* ### vv Determine p-eigenvalues of twisted 2-strand knots, positive k, positive p ### *)
Block[{k = 2},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, Expand[Factor[Simplify[(q^6 t^3 + 1) TwTwoCableMassagedPositive[2 (k + 1), 5 - 2 2 k]]]]];
             fun1 = Function[{k}, Expand[Simplify[fun[k+1] - fun[k]]]];
             fun2 = Function[{k}, Expand[Simplify[fun1[k+1] - q^(-12) t^(-8) fun1[k]]]];
             fun3 = Function[{k}, Expand[Simplify[fun2[k+1] - (t^2 q^4)^(-1) fun2[k]]]];
             (* {Length[fun1[k]], fun1[k]} *)
             fun3[k]
            ]]

(* ### vv Determine p-eigenvalues of twisted 2-strand knots, negative k, positive p ### *)
Block[{k = 3},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, Expand[TwTwoCableMassagedNegative[2 (k + 1), 5 - 2 2 k - 2]]];
             fun1 = Function[{k}, Expand[Simplify[fun[k+1] - fun[k]]]];
             fun2 = Function[{k}, Expand[Simplify[fun1[k+1] - q^(-12) t^(-8) fun1[k]]]];
             fun3 = Function[{k}, Expand[Simplify[fun2[k+1] - (t^2 q^4)^(-1) fun2[k]]]];
             fun3[k]
            ]]

(* ### CURWORK ### *)

posKposPtwisted = UniformTwistedFitPositive[];
posKposPtwTwoCable = UniformTwTwoCableFitPositive[];
posKposPtwTwoevoFun = MkEvoFunction[Factor[posKposPtwTwoCable]];
negKposPtwTwoCable = UniformTwTwoCableFitNegative[];
posKnegPtwisted = UniformTwistedFitPositiveNegP[];
posKnegPtwTwoCable = UniformTwTwoCableFitPositiveNegP[];
posKnegPtwTwoevoFun = MkEvoFunction[Factor[posKnegPtwTwoCable]];
negKnegPtwTwoCable = UniformTwTwoCableFitNegativeNegP[];


Block[{twist = tw},
      Simplify[posKposPtwTwoevoFun[twist]/EigenvaluePiecePlus[twist],
               Assumptions -> q > 0 && t > 0]]

Block[{twist = 14},
      Simplify[posKnegPtwTwoevoFun[twist]/EigenvaluePieceMinus[twist],
                   Assumptions -> q > 0 && t > 0]]


(* ### vv The posK and negK evolutions coincide (we've successfully isolated the "jump") ### *)
Factor[Simplify[posKposPtwTwoCable - negKposPtwTwoCable]]

Factor[Simplify[posKnegPtwTwoCable - negKnegPtwTwoCable]]


(* ### vv How do 2-cable evolutions relate to the twisted evolution ### *)

(* ### vv ... for positive P region ### *)
Simplify[Lookup[posKposPtwisted, Key[{q^(-12) t^(-8)}]]
         - Lookup[posKposPtwTwoCable, Key[{q^(-6) t^(-4)}]]]

Simplify[Lookup[posKposPtwisted, Key[{q^(-4) t^(-2)}]]
         - Lookup[posKposPtwTwoCable, Key[{q^(-2) t^(-1)}]]]

Simplify[Lookup[posKposPtwisted, Key[{q^(0) t^(0)}]]
         - Lookup[posKposPtwTwoCable, Key[{1}]]]


(* ### vv ... and for negative P region ### *)

Simplify[Lookup[posKnegPtwisted, Key[{q^(-12) t^(-8)}]]
         - Lookup[posKnegPtwTwoCable, Key[{q^(-6) t^(-4)}]]]

Simplify[Lookup[posKnegPtwisted, Key[{q^(-4) t^(-2)}]]
         - Lookup[posKnegPtwTwoCable, Key[{q^(-2) t^(-1)}]]]

Simplify[Lookup[posKnegPtwisted, Key[{q^(0) t^(0)}]]
         - Lookup[posKnegPtwTwoCable, Key[{1}]]]


Keys[posKposPtwisted]

Keys[posKposPtwTwoCable]

             1       2       4  2
Out[16]= {{-----}, {q  t}, {q  t }}
            2  2
           q  t


Simplify[(q^12 t^6 - 1) /(q^6 t^3 - 1) /(q^4 t^2 - 1)]


Factor[Simplify[Plus @@ negKposPtwTwoCable]]





Factor[Simplify[((2*t + q*t + q*t^2 + 2*q^2*t^2)/ (2*(-1 + t)*(-1 + q^3*t^2))
                 + (-2*t + q*t + q*t^2 - 2*q^2*t^2)/ (2*(-1 + t)*(1 + q^3*t^2)))
                (q^6 t^4 - 1)]]
         

Factor[Simplify[((3 + 4*t + q^2*t + t^2 + 4*q^2*t^2 + 3*q^2*t^3)/(2*(-1 + q^4*t^3))
                 - ((1 + t)^2*(1 + q^2*t))/(2*(1 + q^4*t^3)))
                (q^8 t^6 - 1)]]


(* ### vv Bring the p-dependence in posP region of 2-cabled twist knots to the human-readable form ### *)
Apart[Simplify[(Apart[Lookup[posKposPtwTwoCable, Key[{q^(-2) t^(-2)}]], q]
                - (2*t + q*t + q*t^2 + 2*q^2*t^2)/ (2*(-1 + t)*(-1 + q^3*t^2))
                - (-2*t + q*t + q*t^2 - 2*q^2*t^2)/ (2*(-1 + t)*(1 + q^3*t^2))
                - (-1 - 2*t - t^2 - 2*q^2*t^2 - 2*q^2*t^3)/  (2*(-1 + t)*(-1 + q^4*t^3))
                - (-1 - t)/(2*(1 + q^4*t^3))
               )],
      q] // InputForm

Out[42]//InputForm= 1 + 1/(q^4*t^2)

Out[41]//InputForm= 
    1 + 1/(q^4*t^2) + (2*t + q*t + q*t^2 + 2*q^2*t^2)/ (2*(-1 + t)*(-1 + q^3*t^2))
    + (-2*t + q*t + q*t^2 - 2*q^2*t^2)/ (2*(-1 + t)*(1 + q^3*t^2))
    + (-1 - 2*t - t^2 - 2*q^2*t^2 - 2*q^2*t^3)/  (2*(-1 + t)*(-1 + q^4*t^3))
    + (-1 - t)/(2*(1 + q^4*t^3))

Factor[Simplify[((-3 - 4*t - q^2*t - t^2 - 4*q^2*t^2 - 3*q^2*t^3)/(2*(-1 + q^4*t^3))
                 + (1 + 2*t + q^2*t + t^2 + 2*q^2*t^2 + q^2*t^3)/(2*(1 + q^4*t^3)))
                (q^8 t^6 - 1)]]


Factor[Apart[Simplify[(Apart[Lookup[posKposPtwTwoCable, Key[{q^2 t}]], q]
                       - (-3 - 4*t - q^2*t - t^2 - 4*q^2*t^2 - 3*q^2*t^3)/(2*(-1 + q^4*t^3))
                       - (1 + 2*t + q^2*t + t^2 + 2*q^2*t^2 + q^2*t^3)/(2*(1 + q^4*t^3))
                      )],
             q]] // InputForm

Apart[Simplify[(Apart[Lookup[posKposPtwTwoCable, Key[{q^4 t^2}]], q]
                      )],
      q] // InputForm

Out[35]//InputForm= 
-(1/(q^12*t^7)) - 1/(q^10*t^6) + 1/(q^6*t^4) + 2/(q^4*t^3) - 1/(q^2*t) + 
 q^2*t^2 + q^4*t^3 + (1 + t)/(q^8*t^5) + (1 + t + 3*q*t + 3*q^2*t^2)/
  (2*(-1 + q^3*t^2)) + (-1 - t + 3*q*t - 3*q^2*t^2)/(2*(1 + q^3*t^2)) - 
 1/(t*(1 - q^2*t + q^4*t^2))


Keys[posKposPtwTwoCable]

             1       2       4  2
Out[28]= {{-----}, {q  t}, {q  t }}
            2  2
           q  t

(* ### vv Determine k-eigenvalues of twisted 2-strand knots, positive k ### *)
Block[{k = 6, twist = 8},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, Expand[PrecompKhRed[TwistedTwoSt[twist], 3 + 2 k - 2 twist]]];
             fun1 = Function[{k}, Expand[Simplify[fun[k+1] - q^2 fun[k]]]];
             fun2 = Function[{k}, Expand[Simplify[fun1[k+1] - q^6 t^2 fun1[k]]]];
             (* fun3 = Function[{k}, Expand[Simplify[fun2[k+1] - (t^4 q^4)^(-1) (t^2 q^4)^a fun2[k]]]]; *)
             (* {Length[fun1[k]], fun1[k]} *)
             fun2[k]
            ]]

(* ### vv Determine k-eigenvalues of twisted 2-strand knots, negative k ### *)
Block[{k = -3, twist = -10},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, Expand[PrecompKhRed[TwistedTwoSt[twist], 3 + 2 k - 2 twist]]];
             fun1 = Function[{k}, Expand[Simplify[fun[k+1] - q^2 fun[k]]]];
             fun2 = Function[{k}, Expand[Simplify[fun1[k+1] - q^6 t^2 fun1[k]]]];
             (* fun3 = Function[{k}, Expand[Simplify[fun2[k+1] - (t^4 q^4)^(-1) (t^2 q^4)^a fun2[k]]]]; *)
             (* {Length[fun1[k]], fun1[k]} *)
             Print[3 + 2 k - 2 twist];
             fun2[k]
            ]]


FitTwistTwoStrandPositiveInK[twist_] :=
    (* ### ^^ Fit the dependence on k for 2-strand cabled twist knot ### *)
    Block[{CCCEigenvaluesCritLength = Null,
           extraPoints = 3},
          FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                   Expand[(PrecompKhRed[TwistedTwoSt[twist], 2 k1 + 5 - 2 twist] /. {q -> 1/q, t -> 1/t})
                                                          q^(2 k1 + 1) (q^2 t)^(2 k1 + 1) (* ### << The framing convention ### *)
                                                         ]],
                                          Prepend[{1, (t q^2)(* ^(-1) *)}, 2 k + 5 - 2 twist]]]

FitTwistTwoStrandNegativeInK[twist_] :=
    (* ### ^^ Fit the dependence on k for 2-strand cabled twist knot ### *)
    Block[{CCCEigenvaluesCritLength = Null,
           extraPoints = 3},
          FitFamilyWithEigenvaluesGradual[Function[{k1},
                                                   Expand[(PrecompKhRed[TwistedTwoSt[twist], 2 k1 + 5 - 2 twist - 10] /. {q -> 1/q, t -> 1/t})
                                                          q^(2 k1 + 1 - 10) (q^2 t)^(2 k1 + 1 - 10) (* ### << The framing convention ### *)
                                                         ]],
                                          Prepend[{1, (t q^2)(* ^(-1) *)}, 2 k + 5 - 2 twist - 10]]]


Lookup[FitTwistTwoStrandNegativeInK[4], Key[{1}]]











positivePpositiveK = UniformTwistedFitPositive[];
positivePpositiveKevoFun = MkEvoFunction[Factor[positivePpositiveK]];

Expand[FullSimplify[positivePpositiveKevoFun[4]]]

positivePnegativeK = UniformTwistedFitNegative[];
positivePnegativeKevoFun = MkEvoFunction[Factor[positivePnegativeK]];

negativePpositiveK = UniformTwistedFitPositiveNegP[];
negativePpositiveKevoFun = MkEvoFunction[Factor[negativePpositiveK]];

negativePnegativeK = UniformTwistedFitNegativeNegP[];
negativePnegativeKevoFun = MkEvoFunction[Factor[negativePnegativeK]];

TwistedMassagedNegative[-4, 2]

(* TwistedMassagedPositive[-6,6] *)

Simplify[positivePpositiveK/ positivePnegativeK]

Factor[FullSimplify[negativePpositiveK - negativePnegativeK]]

Factor[Simplify[positivePpositiveK / negativePpositiveK]]


Factor[Simplify[positivePpositiveK - negativePpositiveK /. {t -> -1}]]

Factor[Simplify[positivePnegativeK - negativePnegativeK /. {t -> -1}]]


(* ### Alright, let's figure out, how to write a formula for the twisted Eigenvalue piece in a way ### *)
(* ### that makes p -> -p transition easy. ### *)

Lookup[positivePpositiveK, Key[{q^(-12) t^(-8)}]]

positivePpositiveK

Collect[Simplify[evoPos[3]], q]

(* ### vv Load the precomputed reduced Khovanov's for twist knots ### *)
Module[{j},
       For[j = 2, j <= 16, j = j + 2,
           LoadTwistedPrecomps[j]]];


pos = UniformTwistedFitPositive[];

(* ### vv Get the apart expression for coeff of {1} ### *)
Simplify[(1 + t)/(2*t*(1 + q^2*t))
         + (-1 + 2*t + 5*t^2 + 2*t^3)/(2*(-1 + t)*t*(-1 + q^2*t))]
    
Simplify[(-1 - 3*t - 3*q*t - q*t^2 - 4*q^2*t^2)/ (2*(-1 + t)*t*(-1 + q^3*t^2))
         + (1 + 3*t - 3*q*t - q*t^2 + 4*q^2*t^2)/ (2*(-1 + t)*t*(1 + q^3*t^2))]


Simplify[Apart[(Apart[Lookup[positivePpositiveK, Key[{1}]], q]
                       - (1 + t)/(2*t*(1 + q^2*t))
                       - (-1 + 2*t + 5*t^2 + 2*t^3)/(2*(-1 + t)*t*(-1 + q^2*t))
                       - (-1 - 3*t - 3*q*t - q*t^2 - 4*q^2*t^2)/ (2*(-1 + t)*t*(-1 + q^3*t^2))
                       - (1 + 3*t - 3*q*t - q*t^2 + 4*q^2*t^2)/ (2*(-1 + t)*t*(1 + q^3*t^2))
                      ),
               q]]


Factor[Simplify[
    (-1 - t)/(2*t*(1 + q^2*t))
    - ((1 + t)*(-1 + 3*t + 2*t^2))/(2*(-1 + t)*t*(-1 + q^2*t))]]


Factor[Simplify[
    (1 + t - q^2*t^2 - q^2*t^3)/ (2*t^2*(1 + q^4*t^3))
    + (1 + 4*t + 3*t^2 + 3*q^2*t^2 + 4*q^2*t^3 + q^2*t^4)/ (2*(-1 + t)*t^2*(-1 + q^4*t^3))]]

Simplify[Apart[(Apart[Lookup[pos, Key[{q^(-4) t^(-2)}]], q]
                - (-1 - t)/(2*t*(1 + q^2*t))
                + ((1 + t)*(-1 + 3*t + 2*t^2))/(2*(-1 + t)*t*(-1 + q^2*t))
                - (1 + t - q^2*t^2 - q^2*t^3)/ (2*t^2*(1 + q^4*t^3))
                - (1 + 4*t + 3*t^2 + 3*q^2*t^2 + 4*q^2*t^3 + q^2*t^4)/ (2*(-1 + t)*t^2*(-1 + q^4*t^3))
               ),
               q]]

Factor[Simplify[((1 + 3*t + 3*q*t + q*t^2 + 4*q^2*t^2)/(2*(-1 + t)*t*(-1 + q^3*t^2))
                 + (-1 - 3*t + 3*q*t + q*t^2 - 4*q^2*t^2)/(2*(-1 + t)*t*(1 + q^3*t^2)))
                (q^6 t^4 - 1)]]

                  
                      2  2      4  3    4  4
         1 + 3 t + 4 q  t  + 3 q  t  + q  t
Out[52]= -----------------------------------
                     (-1 + t) t


Apart[(Apart[Lookup[positivePpositiveK, Key[{q^(-12) t^(-8)}]], q]
       - (1 + 3*t + 3*q*t + q*t^2 + 4*q^2*t^2)/(2*(-1 + t)*t*(-1 + q^3*t^2))
       - (-1 - 3*t + 3*q*t + q*t^2 - 4*q^2*t^2)/(2*(-1 + t)*t*(1 + q^3*t^2))
       - (-1 - t + q^2*t^2 + q^2*t^3)/(2*t^2*(1 + q^4*t^3))
       - (-1 - 4*t - 3*t^2 - 3*q^2*t^2 - 4*q^2*t^3 - q^2*t^4)/(2*(-1 + t)*t^2*(-1 + q^4*t^3))
      ),
      q] // InputForm

                                                      
Out[51]//InputForm= q^2 + q^6*t^3 + q^8*t^4 + (1 + 2*t)/t^2



Simplify[(- (1 + t)/(2*t^2*(1 + q^2*t))
          - (3 + 4*t + t^2)/(2*(1 - t)*t^2*(-1 + q^2*t)))
         (q^4 t^2 - 1)]

Factor[Simplify[((-1 - 3*t - 3*q*t - q*t^2 - 4*q^2*t^2)/(2*(-1 + t)*t^3*(-1 + q^3*t^2))
                 +  (1 + 3*t - 3*q*t - q*t^2 + 4*q^2*t^2)/(2*(-1 + t)*t^3*(1 + q^3*t^2)))
                (q^6 t^4 - 1)]]


Apart[Simplify[Apart[Lookup[negativePpositiveK, Key[{1}]], q]
               + (1 + t)/(2*t^2*(1 + q^2*t))
               + (3 + 4*t + t^2)/(2*(1 - t)*t^2*(-1 + q^2*t))
               - (-1 - 3*t - 3*q*t - q*t^2 - 4*q^2*t^2)/(2*(-1 + t)*t^3*(-1 + q^3*t^2))
               - (1 + 3*t - 3*q*t - q*t^2 + 4*q^2*t^2)/(2*(-1 + t)*t^3*(1 + q^3*t^2))
              ],
      q] // InputForm

Apart[Simplify[(- ((1 + t)*(3 + t))/ (2*(-1 + t)*t^2*(-1 + q^2*t))
                + (1 + t)/(2*t^2*(1 + q^2*t))) (q^4 t^2 - 1)], t]

Factor[Simplify[(- ((1 + t)*(-1 + q^2*t^2))/(2*t^4*(1 + q^4*t^3))
                 + (1 + 4*t + 3*t^2 + 3*q^2*t^2 + 4*q^2*t^3 + q^2*t^4)/ (2*(-1 + t)*t^4*(-1 + q^4*t^3)))
                (q^8 t^6 - 1)]]

Apart[Simplify[Apart[Lookup[negativePpositiveK, Key[{q^(-4) t^(-2)}]], q]
               + ((1 + t)*(3 + t))/ (2*(-1 + t)*t^2*(-1 + q^2*t))
               - (1 + t)/(2*t^2*(1 + q^2*t))
               + ((1 + t)*(-1 + q^2*t^2))/(2*t^4*(1 + q^4*t^3))
               - (1 + 4*t + 3*t^2 + 3*q^2*t^2 + 4*q^2*t^3 + q^2*t^4)/ (2*(-1 + t)*t^4*(-1 + q^4*t^3))
              ],
      q] // InputForm

Factor[Simplify[((1 + 3*t + 3*q*t + q*t^2 + 4*q^2*t^2)/(2*(-1 + t)*t^3*(-1 + q^3*t^2))
                 + (-1 - 3*t + 3*q*t + q*t^2 - 4*q^2*t^2)/(2*(-1 + t)*t^3*(1 + q^3*t^2)))
                (q^6 t^4 - 1)
               ]]

                           
Factor[Simplify[(((1 + t)*(-1 + q^2*t^2))/(2*t^4*(1 + q^4*t^3))
                 + (-1 - 4*t - 3*t^2 - 3*q^2*t^2 - 4*q^2*t^3 - q^2*t^4)/ (2*(-1 + t)*t^4*(-1 + q^4*t^3)))
                (q^8 t^6 - 1)]]


Simplify[negativePpositiveK / positivePpositiveK]


Apart[Simplify[Apart[Lookup[negativePpositiveK, Key[{q^(-12) t^(-8)}]], q]
               - (1 + 3*t + 3*q*t + q*t^2 + 4*q^2*t^2)/(2*(-1 + t)*t^3*(-1 + q^3*t^2))
               - (-1 - 3*t + 3*q*t + q*t^2 - 4*q^2*t^2)/(2*(-1 + t)*t^3*(1 + q^3*t^2))
               - ((1 + t)*(-1 + q^2*t^2))/(2*t^4*(1 + q^4*t^3))
               - (-1 - 4*t - 3*t^2 - 3*q^2*t^2 - 4*q^2*t^3 - q^2*t^4)/ (2*(-1 + t)*t^4*(-1 + q^4*t^3))
              ],
      q] // InputForm

Out[11]//InputForm= q^2/t^2 + q^6*t + q^8*t^2 + (1 + 2*t)/t^4





Simplify[(Lookup[positivePpositiveK, Key[{1}]]
          + Lookup[positivePpositiveK, Key[{q^(-4) t^(-2)}]]
          + Lookup[positivePpositiveK, Key[{q^(-12) t^(-8)}]])]

Simplify[(Lookup[negativePpositiveK, Key[{1}]]
          + Lookup[negativePpositiveK, Key[{q^(-4) t^(-2)}]]
          + Lookup[negativePpositiveK, Key[{q^(-12) t^(-8)}]])]

                  
            2        4  3    8  5
           q  (-1 + q  t  + q  t )
Out[36]= -(-----------------------)
                      t



evoPos = MkEvoFunction[Factor[pos]];

(Apart[Factor[Simplify[evoPos[p]]]
       - (1 - (q^4 t^2)^(-p)) (1 + t)/2/t/(1 + q^2 t)
       , q])
    /. {(1 + q^2 t) -> 1/aaa}


Factor[TwistedMassagedPositive[10, -7]]

LoadWhiteheadizedPrecomps[Knot[8]]

MassagedSuperPositive[Knot[7,1], 5]


SimpleSuperTestRig[Knot[8,4], -5, 5]

kCritical: -2
{{0, 8}}
kCritical: -3
{{0, 3}}

Out[42]= {{$Success, -5, -3}, {$Success, -2, 5}}

(* PD[Knot[7,4]] *)


Factor[((1 + q^4 t^2 - q^10 t^6 + q^14 t^9) /. {t -> -1})/(q^10 - 1) /(q^8 - 1) (q^4 - 1) (-1)]

(* Simplify[(1 + Braces[A*q] Braces[A/q] 1/(1-1/A^2)) - (A^2 - A * Braces[q]^2/Braces[A])] *)
(* Simplify[(H89 /. {M -> M q^4}) - H89] *)
(* Factor[H16-H19[1, -3]] *)

Module[{i},
       For[i = 0, i <= 4, i ++,
           LoadWhiteheadizedPrecomps[Knot[2 i + 1,1]]]];



PrecompKhRed[Knot[7,1], -10, 2]

SimpleSuperTestRig[Knot[7,1]]

kCritical: 6
{}
kCritical: -6
{}

Out[14]= {{$Success, 6, 5}, {$Success, -5, -6}}


Denominator[MassagedSuperNegative[Knot[7,3], 0]]




Block[{k = 4, n = 1},
      Simplify[TorusMassagedPositive[Knot[n, 1], k + 1]
               - TorusMassagedPositive[Knot[n, 1], k]]]

Factor[TorusMassagedPositive[Knot[5, 1], -1]]

(* ### vv Determine torus eigenvalues of the hypothetical uniform Khovanov adjoint ### *)
Block[{k = 2, a = -1},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, Expand[(q^4 t^2 - 1) TorusMassagedPositive[Knot[2 k + 1, 1], 2 - k]]];
             fun1 = Function[{k}, Expand[Simplify[fun[k+1] - t^4 q^8 (t^2 q^4)^a fun[k]]]];
             fun2 = Function[{k}, Expand[Simplify[fun1[k+1] - (t^2 q^4) (t^2 q^4)^a fun1[k]]]];
             fun3 = Function[{k}, Expand[Simplify[fun2[k+1] - (t^4 q^4)^(-1) (t^2 q^4)^a fun2[k]]]];
             (* {Length[fun1[k]], fun1[k]} *)
             fun3[k]
            ]]

(* ### vv Determine torus eigenvalues of the hypothetical uniform Khovanov adjoint (negative region) ### *)
Block[{k = 1, a = -1},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, Expand[(q^4 t^2 - 1) TorusMassagedNegative[Knot[2 k + 1, 1], 2 - k - 1]]];
             fun1 = Function[{k}, Expand[Simplify[fun[k+1] - t^4 q^8 (t^2 q^4)^a fun[k]]]];
             fun2 = Function[{k}, Expand[Simplify[fun1[k+1] - (t^2 q^4) (t^2 q^4)^a fun1[k]]]];
             fun3 = Function[{k}, Expand[Simplify[fun2[k+1] - (t^4 q^4)^(-1) (t^2 q^4)^a fun2[k]]]];
             (* {Length[fun1[k]], fun1[k]} *)
             fun3[k]
            ]]

(* ### vv Determine eigenvalues for twisted-twisted knots positive ### *)
Block[{k = 5, a = -2},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, Expand[(q^4 t^2 - 1) TwistedMassagedPositive[2 k + 2, 1 - 2 k]]];
             fun1 = Function[{k}, Expand[Simplify[fun[k+1] - t^4 q^8 (t^2 q^4)^a fun[k]]]];
             fun2 = Function[{k}, Expand[Simplify[fun1[k+1] - (t^2 q^4) (t^2 q^4)^a fun1[k]]]];
             fun3 = Function[{k}, Expand[Simplify[fun2[k+1] - (t^4 q^4)^(-1) (t^2 q^4)^a fun2[k]]]];
             (* {Length[fun1[k]], fun1[k]} *)
             fun3[k]
            ]]

(* ### vv Determine eigenvalues for twisted-twisted knots negative ### *)
Block[{k = 4, a = -2},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, Expand[(q^4 t^2 - 1) TwistedMassagedNegative[2 k + 2, 0 - 2 k]]];
             fun1 = Function[{k}, Expand[Simplify[fun[k+1] - t^4 q^8 (t^2 q^4)^a fun[k]]]];
             fun2 = Function[{k}, Expand[Simplify[fun1[k+1] - (t^2 q^4) (t^2 q^4)^a fun1[k]]]];
             fun3 = Function[{k}, Expand[Simplify[fun2[k+1] - (t^4 q^4)^(-1) (t^2 q^4)^a fun2[k]]]];
             (* {Length[fun1[k]], fun1[k]} *)
             fun3[k]
            ]]







TorusMassagedPositive[Knot[1, 1], 2]

pos = Factor[UniformTorusFitPositive[]];
neg = Factor[UniformTorusFitNegative[]];


pos = Factor[UniformTwistedFitPositive[]];
neg = Factor[UniformTwistedFitNegative[]];

Simplify[Plus @@ neg]

Simplify[pos - neg]

Factor[Simplify[Lookup[pos, Key[{1}]]
                + Lookup[pos, Key[{1/q^12/t^8}]]
                + Lookup[pos, Key[{1/q^4/t^2}]]]]

Factor[Simplify[Lookup[pos, Key[{1/q^12/t^8}]]]] // TeXForm

Factor[Simplify[Lookup[pos, Key[{1/q^4/t^2}]]]] // TeXForm


Factor[Simplify[Lookup[pos, Key[{t^2 q^4}]]]]

Factor[Simplify[Lookup[pos, Key[{1}]]]]

Factor[Simplify[Lookup[pos, Key[{(t^6 q^8)^(-1)}]]]]

                  2         4  2    10  6    14  9
                 q  t (1 + q  t  - q   t  + q   t )
Out[148]= -------------------------------------------------
                 3  2        3  2         4  3        4  3
          (-1 + q  t ) (1 + q  t ) (-1 + q  t ) (1 + q  t )


                
                

Factor[Simplify[pos - neg]]



Factor[Solve[{AA /(-q^2 t^2) + BB == Lookup[pos, Key[{q^(-4) t^(-4)}]],
              AA /(q^2 t) + BB == Lookup[neg, Key[{q^(-4) t^(-4)}]]},
             {AA, BB}]]


Factor[Solve[{AA /(-q^2 t^2) + BB == Lookup[pos, Key[{q^4 t^2}]],
              AA /(q^2 t) + BB == Lookup[neg, Key[{q^4 t^2}]]},
             {AA, BB}]]

Factor[Solve[{AA /(-q^2 t^2) + BB == Lookup[pos, Key[{q^8 t^4}]],
              AA /(q^2 t) + BB == Lookup[neg, Key[{q^8 t^4}]]},
             {AA, BB}]]

                  
                            4  2
                           q  t
Out[96]= {{AA -> -(----------------------), 
                          2          2
                   (-1 + q  t) (1 + q  t)
 
              2          4      6  3    6  4    8  4    8  5    10  5
>     BB -> (q  t (-1 - q  t + q  t  + q  t  + q  t  + q  t  + q   t  + 
 
               10  6    12  7    16  10    18  11
>           2 q   t  + q   t  + q   t   + q   t  )) / 
 
                2          2           3  2        3  2
>       ((-1 + q  t) (1 + q  t) (-1 + q  t ) (1 + q  t ))}}



Expand[Simplify[TwistedKhovanov[] (1 - q^4 t^2)] / (q^2 t^2 (-1))]

          2   1    4      6  2
Out[45]= q  + - + q  t + q  t
              t

Block[{k = 1},
      Simplify[(PrecompKhRed[Knot[3,1], 2 (k+1), 2] /. {q -> 1/q, t -> 1/t})
               - q^4 t^2 (PrecompKhRed[Knot[3,1], 2 k, 2] /. {q -> 1/q, t -> 1/t})]]

                  
          2   1    4      6  2
Out[23]= q  + - + q  t + q  t
              t

                  
         1    2        2       6  2
Out[22]= - + q  (-1 + q ) t + q  t
         t


Block[{k = 0},
      Simplify[(PrecompKhRed[Knot[5,1], 2 (k+1), 2] /. {q -> 1/q, t -> 1/t})
               - q^4 t^2 (PrecompKhRed[Knot[5,1], 2 k, 2] /. {q -> 1/q, t -> 1/t})]]

                  
          2   1    4      6  2
Out[47]= q  + - + q  t + q  t
              t


Expand[Simplify[((A^2 - A Braces[q]^2/Braces[A]) /. {A -> q^2})
                (1 + q^4 t^2)]]




Factor[TorusMassagedPositive[Knot[3, 1], 1]]






Factor[(UniformAdjointHOMFLY[Knot[3,1]] - 1)/(1 - A^(-2))] // InputForm

Out[115]//InputForm= 
((-1 + A)*A^2*(1 + A)*(A^4 + A^6*q^2 - q^4 - 2*A^2*q^4 - A^4*q^4 - 
   2*A^6*q^4 + A^6*q^6 + A^4*q^8))/q^4

                     2           4    6  2    4      2  4    4  4      6  4
Out[114]= ((-1 + A) A  (1 + A) (A  + A  q  - q  - 2 A  q  - A  q  - 2 A  q  + 
 
          6  6    4  8      4
>        A  q  + A  q )) / q

                                       6    8    8    10
           2    4    6    8      10   A    A    A    A      8  2    10  2
Out[113]= A  + A  - A  + A  - 2 A   - -- + -- - -- + --- - A  q  + A   q  - 
                                       4    4    2    2
                                      q    q    q    q
 
      6  4    8  4
>    A  q  + A  q


Block[{k = 0},
      Simplify[SatelliteHOMFLY[TorusKnot[2, 1], k]
               -SatelliteHOMFLY[Knot[3,1], k]]]


VisualizeWhiteheadizedEvolutions[Knot[5,1]]



Block[{k = 4},
      Expand[Simplify[Simplify[SatelliteSuperpolynomial[Knot[3,1], k] /. {a -> q^2, t -> -1, unknown2 -> unknown1},
                               Assumptions -> And[Element[unknown1, Integers],
                                                  Element[unknown2, Integers]]]
                      - SatelliteHOMFLY[Knot[3,1], k] /. {A -> q^2}]]]

Factor[Block[{k = 0},
             Expand[Simplify[Simplify[SatelliteSuperpolynomial[Knot[3,1], k] /. {a -> q^2}]
                             - Simplify[q^2/t (PrecompKhRed[Knot[3,1], 0, 2] /. {q -> 1/q, t -> 1/t})]]]]]


Factor[q^6 t^3 + 1]

LotsOfFun[k_] :=
    Factor[(Expand[Simplify[q^2 t (-t) (PrecompKhRed[Knot[3,1], 2 k, 2] /. {q -> 1/q, t -> 1/t})]]
            - 1) /(q^6 t^3 + 1)/(q^2 t + 1) q^6 t^2
           - q^6 t^2/(q^4 t^2 - 1)
          ];

LotsOfFun1[k_] :=
    Factor[((Expand[Simplify[q^2 t (PrecompKhRed[Knot[3,1], 2 k, 2] /. {q -> 1/q, t -> 1/t})]]
             - 1) /(q^6 t^3 + 1)/(q^2 t + 1) q^6 t^2
            - q^6 t^2/(q^4 t^2 - 1))
          ];

LotsOfFun51[k_] :=
    Factor[(PrecompKhRed[Knot[5,1], 2 k, 2] /. {q -> 1/q, t -> 1/t})
          ];

Factor[1 + (q^6 t^3 + 1) (q^4 t + q^2) /(q^6 t^2) q^4 t^2 (q^4 t^2 - 1)]

           2          2      6  3    8  4    10  5
Out[104]= q  t (-1 + q  t - q  t  + q  t  + q   t )

Block[{k = 3},
      Factor[Simplify[LotsOfFun51[k + 1] - q^4 t^2 LotsOfFun51[k]]]
     ]

                    
                2          4  2
          (1 + q  t) (1 + q  t )
Out[106]= ----------------------
                    t



Block[{k = 0},
      Expand[Simplify[(PrecompKhRed[Knot[5, 1], 2 k, 2] /. {q -> 1/q, t -> -1})]]]


Block[{k = 0},
      Expand[Simplify[(PrecompKhRed[Knot[5, 1], 2 k, 2] /. {q -> 1/q, t -> -1})]]]


Block[{k = 0, m = -3},
      LotsOfFun51[k]]


LotsOfFun1[-2]


Block[{k = -3},
      Expand[LotsOfFun1[k + 1] - q^4 t^2 LotsOfFun1[k]]]

Block[{k = -5},
      Simplify[LotsOfFun1[k+1]/LotsOfFun1[k]]]


Block[{k = 1},
      Expand[Factor[Simplify[LotsOfFun[k]/(q^4 t^2)^k + q^6 t^2 /(q^4 t^2 - 1)]]]]



Block[{k = -3},
      Expand[Factor[Simplify[LotsOfFun1[k]/(q^4 t^2)^k + q^6 t^2 /(q^4 t^2 - 1)]]]]








Block[{k = 3},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = LotsOfFun;
             fun1 = Function[{k}, Expand[Simplify[fun[k+1] - fun[k]]]];
             fun2 = Function[{k}, Expand[Simplify[fun1[k+1] - (t^2 q^4) fun1[k]]]];
             (* fun3 = Function[{k}, Expand[Simplify[fun2[k+1] - t^4 q^8 fun2[k]]]]; *)
             (* {Length[fun1[k]], fun1[k]} *)
             fun2[k]
            ]]




Expand[q^2/t Simplify[PrecompKhRed[Knot[3,1], 0, 2] /. {q -> 1/q, t -> 1/t}]]




(* ### vv Matching between Morozov's formulas for satellite trefoil and precomputed Khovanov formulas ### *)
(* Block[{k = -5}, *)
(*       Simplify[(SatelliteHOMFLY[Knot[3,1], k] /. {A -> q^2}) *)
(*                - (-q^2) (PrecompKhRed[Knot[3,1], 2 k, 2] /. {t -> -1} /. {q -> 1/q})]] *)






Block[{k = 3},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, Expand[Simplify[PrecompKhRed[Knot[3, 1], 2, 2 k + 2]]]];
             fun1 = Function[{k}, Expand[Simplify[fun[k+1] - fun[k]]]];
             fun2 = Function[{k}, Expand[Simplify[fun1[k+1] - (t^2 q^4)^(-1) fun1[k]]]];
             (* fun3 = Function[{k}, Expand[Simplify[fun2[k+1] - t^4 q^8 fun2[k]]]]; *)
             (* {Length[fun1[k]], fun1[k]} *)
             fun2[k]
            ]]

Block[{k = 2},
      Module[{fun, fun1, fun2, fun3, fun4, fun5},
             fun = Function[{k}, Expand[Simplify[PrecompKhRed[Knot[3, 1], 2 k + 2, 2]]]];
             fun1 = Function[{k}, Expand[Simplify[fun[k+1] - fun[k]]]];
             fun2 = Function[{k}, Expand[Simplify[fun1[k+1] - (t^2 q^4)^(-1) fun1[k]]]];
             (* fun3 = Function[{k}, Expand[Simplify[fun2[k+1] - t^4 q^8 fun2[k]]]]; *)
             (* {Length[fun1[k]], fun1[k]} *)
             fun2[k]
            ]]

