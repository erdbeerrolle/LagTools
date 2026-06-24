(* ::Package:: *)
(* ------------------------------------------------------------------ *)
(*  Test suite for LagTools.wl                                        *)
(*  Run with:                                                          *)
(*    dir = "C:\\Users\\laras\\Documents\\Mathematica\\LagTools";     *)
(*    r = TestReport[FileNameJoin[{dir, "Tests.wlt"}]];               *)
(*    r["AllTestsSucceeded"]                                           *)
(*    r["TestResultsDataset"]   (* drill into any failures *)          *)
(*                                                                     *)
(*  The suite loads the package itself and declares a fixed set of     *)
(*  fields/couplings, so it is self-contained.                         *)
(* ------------------------------------------------------------------ *)

Get[FileNameJoin[{DirectoryName[$TestFileName], "LagTools.wl"}]];

(* ---- fixtures: declare fields + real couplings once ---- *)
DeclareBoson[Wp]; DeclareBoson[Wm]; DeclareBoson[Zb]; DeclareBoson[AA];
DeclareFermion[nu]; DeclareFermion[el];
DeclareGrassmann[cc];                       (* a ghost: bare Grassmann symbol *)
(gw /: Conjugate[gw] := gw);                 (* declare couplings real *)
(ee /: Conjugate[ee] := ee);
(gz /: Conjugate[gz] := gz);
(gL /: Conjugate[gL] := gL);
(gR /: Conjugate[gR] := gR);


VerificationTest[ConjugateTranspose[a], Conjugate[a], TestID -> "conjugate-transp-scalar"];

(* ================================================================== *)
(* 1. predicates                                                      *)
(* ================================================================== *)

VerificationTest[bosonQ[Wp[LI[i[1]]]],             True,  TestID -> "bosonQ-indexed"];
VerificationTest[bosonQ[el],                    False, TestID -> "bosonQ-fermion"];
VerificationTest[oddQ[el],                      True,  TestID -> "oddQ-fermion"];
VerificationTest[oddQ[bar[el]],                 True,  TestID -> "oddQ-barfermion"];
VerificationTest[oddQ[cc],                      True,  TestID -> "oddQ-ghost"];
VerificationTest[oddQ[Wp[LI[i[1]]]],               False, TestID -> "oddQ-boson"];
VerificationTest[fieldQ[Wp[LI[i[1]]]] && fieldQ[el] && fieldQ[bar[nu]], True,
   TestID -> "fieldQ-all"];
VerificationTest[STindepQ[gw],                   True,  TestID -> "STindepQ-coupling"];
VerificationTest[STindepQ[el] || STindepQ[Wp[LI[i[1]]]],
   False, TestID -> "STindepQ-nonscalars"];
VerificationTest[diracMatQ[ga[LI[i[1]]]] && diracMatQ[PL] && diracMatQ[ga5],
   True,  TestID -> "diracMatQ-gamma-head"];   (* the Bug-2 regression guard *)

(* ================================================================== *)
(* 2. graded product **                                               *)
(* ================================================================== *)

(* boson/scalar factors fall out of the chain to an ordinary Times *)
VerificationTest[AA[LI[i[1]]] ** el,        AA[LI[i[1]]] NC[el],    TestID -> "nc-boson-out"];
VerificationTest[gw ** el,               gw NC[el],            TestID -> "nc-scalar-out"];
(* VerificationTest[NonCommutativeMultiply[el], el,            TestID -> "nc-single"]; *)
(* mixed Times argument: commuting part out, spinor part stays ordered *)
VerificationTest[bar[el] ** (gw ga[LI[i[1]]]) ** el,
   gw (bar[el] ** ga[LI[i[1]]] ** el),                        TestID -> "nc-mixed-split"];

(* ================================================================== *)
(* 3. bar conjugate                                                   *)
(* ================================================================== *)

VerificationTest[bar[el + nu],            bar[el] + bar[nu], TestID -> "bar-linear"];
VerificationTest[bar[gw el],              gw bar[el],        TestID -> "bar-real-coupling"];
VerificationTest[bar[0],                  0,                 TestID -> "bar-zero"];

(* ================================================================== *)
(* 4. derivative d                                                    *)
(* ================================================================== *)

VerificationTest[d[LI[i[1]]][gw AA[LI[i[2]]]], gw d[LI[i[1]]][AA[LI[i[2]]]],
   TestID -> "d-scalar-out"];
VerificationTest[d[LI[i[1]]][ga[LI[i[2]]]],    0,                 TestID -> "d-gamma-zero"];
(* graded Leibniz over a chain *)
VerificationTest[d[LI[i[1]]][bar[nu] ** el],
   d[LI[i[1]]][bar[nu]] ** el + bar[nu] ** d[LI[i[1]]][NC[el]],
   TestID -> "d-leibniz-chain"];

(* ================================================================== *)
(* 5. metric + contraction                                            *)
(* ================================================================== *)

VerificationTest[g[LI[i[1]], LI[i[1]]], 4, TestID -> "g-trace"];
VerificationTest[g[LI[i[1]], LI[i[2]]], g[LI[i[2]], LI[i[1]]],  TestID -> "g-symmetric"];
VerificationTest[contract[g[LI[i[1]], LI[i[2]]] AA[LI[i[2]]]],  AA[LI[i[1]]],
   TestID -> "contract-vector"];

(* ================================================================== *)
(* 6. dummy-index canonicalization                                    *)
(* ================================================================== *)

(* the headline identity: relabelling dummies leaves a term invariant *)
VerificationTest[
   canonical[INS[Wp[LI[i[1]]] Wm[LI[i[1]]] AA[LI[i[2]]] AA[LI[i[2]]]]] ===
   canonical[INS[Wp[LI[i[2]]] Wm[LI[i[2]]] AA[LI[i[1]]] AA[LI[i[1]]]]],
   True, TestID -> "canon-relabel-invariant"];
(* canonical preserves the INS wrapper *)
VerificationTest[
   Head[canonical[INS[Wp[LI[i[1]]] Wm[LI[i[1]]]]]],
   INS, TestID -> "canon-preserves-INS"];
(* a free index must NOT be renamed away *)
VerificationTest[FreeQ[canonical[INS[Wp[LI[i[3]]] Wm[LI[i[1]]] AA[LI[i[1]]]]], LI[i[3]]],
   False, TestID -> "canon-free-preserved"];

(* ================================================================== *)
(* 7. diracSimplify                                                   *)
(* ================================================================== *)

(* projector pushed right through a gamma:  PL ga^mu = ga^mu PR *)
VerificationTest[diracSimplify[PL ** ga[LI[i[1]]]],  ga[LI[i[1]]] ** PR,
   TestID -> "ds-PL-commute"];
(* idempotence / orthogonality *)
VerificationTest[diracSimplify[PL ** PL],          NC[PL],    TestID -> "ds-PLsq"];
VerificationTest[diracSimplify[PL ** PR],          0,         TestID -> "ds-PLPR"];
(* gamma5 -> projectors *)
VerificationTest[diracSimplify[bar[el] ** ga[LI[i[1]]] ** ga5 ** el],
   bar[el] ** ga[LI[i[1]]] ** PR ** el - bar[el] ** ga[LI[i[1]]] ** PL ** el,
   TestID -> "ds-ga5-expand"];
(* completeness P_L + P_R = 1 collapses a matched sum — now via recombineProjectors *)
VerificationTest[recombineProjectors[diracSimplify[
      bar[el] ** ga[LI[i[1]]] ** PL ** el + bar[el] ** ga[LI[i[1]]] ** PR ** el]],
   bar[el] ** ga[LI[i[1]]] ** el,
   TestID -> "ds-completeness"];
(* ghost floats LEFT past a gamma (Bug-2 regression: gamma has head ga) *)
VerificationTest[diracSimplify[ga[LI[i[1]]] ** cc ** PL],
   cc ** ga[LI[i[1]]] ** PL,
   TestID -> "ds-ghost-float-gamma"];
(* ghost float then projector collection in one go *)
VerificationTest[diracSimplify[PL ** cc ** ga[LI[i[1]]]],
   cc ** ga[LI[i[1]]] ** PR,
   TestID -> "ds-ghost-float-then-commute"];

(* ================================================================== *)
(* 8. renorm substitution                                             *)
(* ================================================================== *)

(* Substitute only the right-handed leg el (no bar) so the test isolates    *)
(* the el -> (1+dZL)PL el + (1+dZR)PR el rule and the chain distribution.    *)
VerificationTest[
   recombineProjectors[diracSimplify[(ga[LI[i[1]]] ** el) /. renorm[el, dZL, dZR]]] // Expand,
   NC[ga[LI[i[1]]],el]+dZL NC[ga[LI[i[1]]],PL,el]+dZR NC[ga[LI[i[1]]],PR,el],
   TestID -> "renorm-el-leg"];

(* ================================================================== *)
(* 9. Feynman rules (the end-to-end pipeline)                          *)
(* ================================================================== *)

VerificationTest[fdiff[{bar[nu], None,
  k2}, (gw/Sqrt[2]) (bar[nu] ** ga[LI[i[1]]] ** PL ** el) Wp[LI[i[1]]]],(gw*NC[ga[LI[i[1]]], PL, el]*Wp[LI[i[1]]])/Sqrt[2],TestID->"fdiff"];

(* charged-current W vertex: purely left-handed — plain input *)
VerificationTest[
   feynmanRule[(gw/Sqrt[2]) (bar[nu] ** ga[LI[i[1]]] ** PL ** el) Wp[LI[i[1]]],
      {{Wp, LI[i[2]], k1}, {bar[nu], None, k2}, {el, None, k3}}],
   I INS[(gw/Sqrt[2]) (ga[LI[i[2]]] ** PL)],
   TestID -> "fr-W-vertex"];

(* charged-current W vertex: INS-wrapped input gives INS-wrapped output *)
VerificationTest[
   feynmanRule[INS[(gw/Sqrt[2]) (bar[nu] ** ga[LI[i[1]]] ** PL ** el) Wp[LI[i[1]]]],
      {{Wp, LI[i[2]], k1}, {bar[nu], None, k2}, {el, None, k3}}],
   I INS[(gw/Sqrt[2]) (ga[LI[i[2]]] ** PL)],
   TestID -> "fr-W-vertex-INS"];

(* pure vector coupling: no projector survives *)
VerificationTest[
   feynmanRule[ee (bar[el] ** ga[LI[i[1]]] ** el) AA[LI[i[1]]],
      {{AA, LI[i[2]], k1}, {bar[el], None, k2}, {el, None, k3}}],
   I ee INS[NC[ga[LI[i[2]]]]],
   TestID -> "fr-QED-vertex"];

(* general chiral Z coupling: keeps both projectors with their couplings *)
VerificationTest[
   Expand[feynmanRule[gz (bar[el] ** ga[LI[i[1]]] ** (gL PL + gR PR) ** el) Zb[LI[i[1]]],
      {{Zb, LI[i[2]], k1}, {bar[el], None, k2}, {el, None, k3}}]],
   Expand[I gz INS[(gL (ga[LI[i[2]]] ** PL) + gR (ga[LI[i[2]]] ** PR))]],
   TestID -> "fr-Z-vertex"];

(* derivative -> momentum:  delta(d_mu A_nu)/delta A_al = (-I p_mu) g_{al nu}. *)
(* Tested directly on fdiff to isolate the rule (no spurious contraction).     *)
VerificationTest[
   fdiff[{AA, LI[i[2]], k1}, d[LI[i[1]]][AA[LI[i[3]]]]],
   (-I k1[LI[i[1]]]) g[LI[i[2]], LI[i[3]]],
   TestID -> "fdiff-derivative-momentum"];

(* ================================================================== *)
(* 10. ElectricCharge auto-assignment                                  *)
(* ================================================================== *)

DeclareRealBoson[HH]; DeclareRealBoson[chi];
DeclareComplexBoson[phip, phim];
(* nu, el already declared as fermions in the fixture above *)

VerificationTest[ElectricCharge[HH],   0, TestID -> "charge-realboson"];
VerificationTest[ElectricCharge[chi],  0, TestID -> "charge-realboson-2"];
VerificationTest[ElectricCharge[phip], 1, TestID -> "charge-complexboson-plus"];
VerificationTest[ElectricCharge[phim],-1, TestID -> "charge-complexboson-minus"];
(* fermion charge stays symbolic — ElectricCharge[el] has no assignment *)
VerificationTest[NumericQ[ElectricCharge[el]], False, TestID -> "charge-fermion-symbolic"];
(* charges are real: Conjugate passes through *)
VerificationTest[Conjugate[ElectricCharge[el]], ElectricCharge[el],
   TestID -> "charge-fermion-real"];

(* ================================================================== *)
(* 11. DeclareGaugeDoublet                                             *)
(* ================================================================== *)

DeclareRealParam[v];

(* Higgs-like bosonic doublet: lower component (v+HH+I chi)/Sqrt[2]   *)
(* Both HH and chi have Q=0, T3=-1/2 -> Y = 2*(0+1/2) = 1            *)
DeclareGaugeDoublet[Phi, "\[Phi]", Phi :> {phip, (v + HH + I*chi)/Sqrt[2]}];

VerificationTest[su2DoubletQ[Phi],  True,  TestID -> "doublet-su2DoubletQ"];
VerificationTest[bosonQ[Phi],       True,  TestID -> "doublet-bosonQ-inferred"];
VerificationTest[fermionQ[Phi],     False, TestID -> "doublet-not-fermionic"];
VerificationTest[Hypercharge[Phi],  1,     TestID -> "doublet-hypercharge-higgs"];

(* Predicates lift through indices *)
VerificationTest[su2DoubletQ[Phi[FI[i[1]]]], True, TestID -> "doublet-indexed-predicate"];
VerificationTest[bosonQ[Phi[LI[i[1]]]],      True, TestID -> "doublet-LI-predicate"];

(* Fermionic doublet: lower component el, Q=ElectricCharge[el] (symbolic) *)
DeclareGaugeDoublet[LeptL, Subscript["L", "L"], LeptL :> {nu, el}];

VerificationTest[su2DoubletQ[LeptL], True,  TestID -> "doublet-LeptL-su2"];
VerificationTest[fermionQ[LeptL],    True,  TestID -> "doublet-LeptL-fermionic"];
VerificationTest[bosonQ[LeptL],      False, TestID -> "doublet-LeptL-not-bosonic"];
VerificationTest[Hypercharge[LeptL], 2*(ElectricCharge[el] + 1/2),
   TestID -> "doublet-LeptL-hypercharge"];

(* Consistency error: lower component mixes fields with different hypercharges *)
DeclareComplexBoson[hplus, hminus];  (* Q[hplus]=1, Q[hminus]=-1 *)
(* lower component hplus+hminus: Y from hplus = 2*(1+1/2)=3, from hminus = 2*(-1+1/2)=-1 *)
VerificationTest[
   DeclareGaugeDoublet[BadDoublet, "bad", BadDoublet :> {hplus, hplus + hminus}],
   $Failed,
   {DeclareGaugeDoublet::hypercharge},
   TestID -> "doublet-hypercharge-inconsistency-error"];

(* ================================================================== *)
(* 12. DeclareGaugeSinglet                                             *)
(* ================================================================== *)

DeclareGaugeSinglet[LeptR, Subscript["l", "R"], LeptR[FI[a_]] :> PR**el[FI[a]]];

VerificationTest[su2SingletQ[LeptR],   True,  TestID -> "singlet-su2SingletQ"];
VerificationTest[fermionQ[LeptR],      True,  TestID -> "singlet-fermionic"];
VerificationTest[bosonQ[LeptR],        False, TestID -> "singlet-not-bosonic"];
VerificationTest[ElectricCharge[LeptR], ElectricCharge[el],
   TestID -> "singlet-inherits-charge"];
VerificationTest[Hypercharge[LeptR],   2*ElectricCharge[el],
   TestID -> "singlet-hypercharge"];

(* Indexed predicate lifts *)
VerificationTest[su2SingletQ[LeptR[FI[i[1]]]], True, TestID -> "singlet-indexed-predicate"];

(* ================================================================== *)
(* 13. SU2T and U1Y generators                                         *)
(* ================================================================== *)

(* sigma[1] = {{0,1},{1,0}}, so (1/2) sigma[1].Col[a,b] = Col[b/2, a/2] *)
VerificationTest[SU2T[GI[1]][Col[aa, bb]], Col[bb/2, aa/2],
   TestID -> "SU2T-sigma1-Col"];
(* sigma[3] = {{1,0},{0,-1}}, so (1/2) sigma[3].Col[a,b] = Col[a/2, -b/2] *)
VerificationTest[SU2T[GI[3]][Col[aa, bb]], Col[aa/2, -bb/2],
   TestID -> "SU2T-sigma3-Col"];

(* SU(2) generator vanishes on declared singlets *)
VerificationTest[SU2T[GI[i[1]]][LeptR],       0, TestID -> "SU2T-singlet-bare"];
VerificationTest[SU2T[GI[i[2]]][LeptR[FI[i[1]]]], 0, TestID -> "SU2T-singlet-indexed"];

(* U1Y acts as a generator: eigenvalue * field *)
VerificationTest[U1Y[Phi],              Hypercharge[Phi] * Phi,              TestID -> "U1Y-doublet-bare"];
VerificationTest[U1Y[LeptR],            Hypercharge[LeptR] * LeptR,          TestID -> "U1Y-singlet-bare"];
VerificationTest[U1Y[LeptL[FI[i[1]]]], Hypercharge[LeptL] * LeptL[FI[i[1]]], TestID -> "U1Y-doublet-indexed"];

(* ================================================================== *)
(* 14. DeclareCovD and ExplCovD                                        *)
(* ================================================================== *)

DeclareBoson[Amu];
DeclareCovD[CD, "D", CD[mu_][f_] :> d[mu][f] + I*Amu[mu]*f];

VerificationTest[covDQ[CD], True, TestID -> "covD-predicate"];
VerificationTest[
   ExplCovD[CD[LI[i[1]]][HH]],
   d[LI[i[1]]][HH] + I*Amu[LI[i[1]]]*HH,
   TestID -> "covD-expl-scalar"];
(* ExplCovD leaves non-CD objects alone *)
VerificationTest[
   ExplCovD[d[LI[i[1]]][HH]],
   d[LI[i[1]]][HH],
   TestID -> "covD-expl-passthrough"];

(* ================================================================== *)
(* 15. DeclareFieldStr and ExplFieldStr                                *)
(* ================================================================== *)

DeclareFieldStr[Fmn, "F", Fmn[LI[a_], LI[b_]] :> d[LI[a]][Amu[LI[b]]] - d[LI[b]][Amu[LI[a]]]];

VerificationTest[fieldStrQ[Fmn], True, TestID -> "fieldStr-predicate"];
VerificationTest[
   ExplFieldStr[Fmn[LI[i[1]], LI[i[2]]]],
   d[LI[i[1]]][Amu[LI[i[2]]]] - d[LI[i[2]]][Amu[LI[i[1]]]],
   TestID -> "fieldStr-expl"];
(* antisymmetry comes from the rule *)
VerificationTest[
   ExplFieldStr[Fmn[LI[i[2]], LI[i[1]]]],
   d[LI[i[2]]][Amu[LI[i[1]]]] - d[LI[i[1]]][Amu[LI[i[2]]]],
   TestID -> "fieldStr-expl-antisym"];
(* ExplFieldStr leaves other objects alone *)
VerificationTest[
   ExplFieldStr[d[LI[i[1]]][HH]],
   d[LI[i[1]]][HH],
   TestID -> "fieldStr-expl-passthrough"];

(* ================================================================== *)
(* 16. ExplGaugeMult                                                   *)
(* ================================================================== *)

(* scalar doublet: bare symbol replaced by Col of components *)
VerificationTest[
   ExplGaugeMult[Phi],
   Col[phip, (v + HH + I*chi)/Sqrt[2]],
   TestID -> "explMult-doublet-bare"];

(* scalar multiplication threads into Col components *)
VerificationTest[
   ExplGaugeMult[3*Phi],
   Col[3*phip, 3*(v + HH + I*chi)/Sqrt[2]],
   TestID -> "explMult-doublet-scaled"];

(* fermionic singlet with function expansion: LeptR[FI[i[1]]] -> PR ** el[FI[i[1]]] *)
VerificationTest[
   ExplGaugeMult[LeptR[FI[i[1]]]],
   NC[PR, el[FI[i[1]]]],
   TestID -> "explMult-singlet-indexed"];

(* fermionic doublet bare *)
VerificationTest[
   ExplGaugeMult[LeptL],
   Col[nu, el],
   TestID -> "explMult-doublet-fermionic"];

(* non-multiplet symbols are untouched *)
VerificationTest[
   ExplGaugeMult[HH + d[LI[i[1]]][HH]],
   HH + d[LI[i[1]]][HH],
   TestID -> "explMult-passthrough"];

(* indexed fermionic doublet: FI[i[1]] must propagate into each component,
   not be left as a stray argument on the Col (regression for bug where
   FI[1] was baked in during DeclareGaugeDoublet and the actual index dropped) *)
DeclareFermion[uq, "u"]; DeclareFermion[dq, "d"];
DeclareGaugeDoublet[QuarkL, Subscript["Q", "L"], QuarkL[FI[a_]] :> {NC[PL, uq[FI[a]]], NC[PL, dq[FI[a]]]}];
VerificationTest[
   bar[QuarkL[FI[i[1]]]] // ExplGaugeMult,
   bar[Col[NC[PL, uq[FI[i[1]]]], NC[PL, dq[FI[i[1]]]]]],
   TestID -> "explMult-doublet-indexed-fi"];

(* ================================================================== *)
(* 17. INS (IndexNamespace)                                            *)
(* ================================================================== *)

DeclareBoson[W1]; DeclareBoson[W2]; DeclareBoson[W3];

(* Multiplication with no index conflict: inner expressions combined verbatim *)
VerificationTest[
   INS[W1[GI[i[1]]] W2[GI[i[2]]]] * INS[W3[GI[i[3]]]],
   INS[W1[GI[i[1]]] W2[GI[i[2]]] W3[GI[i[3]]]],
   TestID -> "INS-times-no-conflict"];

(* Multiplication renames conflicting dummy in the second factor *)
VerificationTest[
   With[{res = INS[W1[GI[i[1]]] W2[GI[i[1]]]] * INS[W2[GI[i[1]]] W3[GI[i[1]]]]},
     MatchQ[res, INS[_]] &&
     (* the result must still contain the original first factor's i[1] *)
     !FreeQ[res, GI[i[1]]] &&
     (* and the second factor's dummy must have been renamed to something else *)
     Length[DeleteDuplicates[
       Cases[res /. INS[e_] :> e, GI[i[n_Integer]] :> n, Infinity]]] === 2
   ],
   True,
   TestID -> "INS-times-renames-dummy"];

(* NC with bosonic INS: commuting content collapses NC to Times, then Times rule renames *)
VerificationTest[
   With[{res = NC[INS[W1[GI[i[1]]] W2[GI[i[1]]]], INS[W2[GI[i[1]]] W3[GI[i[1]]]]]},
     MatchQ[res, INS[_]] &&
     !FreeQ[res, GI[i[1]]] &&
     Length[DeleteDuplicates[Cases[res /. INS[e_] :> e, GI[i[n_Integer]] :> n, Infinity]]] === 2
   ],
   True,
   TestID -> "INS-NC-renames-dummy"];

(* INS is linear over Plus: each summand gets its own namespace *)
VerificationTest[
   INS[W1[GI[i[1]]] + W2[GI[i[1]]]],
   INS[W1[GI[i[1]]]] + INS[W2[GI[i[1]]]],
   TestID -> "INS-linear-plus"];

(* Index-free factors are pulled out of INS *)
VerificationTest[INS[3 W1[GI[i[1]]]], 3 INS[W1[GI[i[1]]]], TestID -> "INS-pull-number"];
VerificationTest[INS[gw W1[GI[i[1]]]], gw INS[W1[GI[i[1]]]], TestID -> "INS-pull-coupling"];
(* An indexed field must NOT be pulled out *)
VerificationTest[INS[W1[GI[i[1]]] W2[GI[i[1]]]], INS[W1[GI[i[1]]] W2[GI[i[1]]]], TestID -> "INS-pull-indexed-stays"];
(* Pure index-free expression collapses the wrapper *)
VerificationTest[INS[gw], gw, TestID -> "INS-pull-pure-scalar"];
(* Scaled sum: index-free factor pulled out, then Plus splits *)
VerificationTest[
   INS[3 (W1[GI[i[1]]] + W2[GI[i[1]]])],
   3*(INS[W1[GI[i[1]]]] + INS[W2[GI[i[1]]]]),
   TestID -> "INS-pull-scalar-times-sum"];

(* Expand pushes inside INS and splits the product *)
VerificationTest[
   Expand[INS[(W1[GI[i[1]]] + W2[GI[i[1]]]) (W3[GI[i[1]]] + W3[GI[i[2]]])]],
   INS[W1[GI[i[1]]] W3[GI[i[1]]]] + INS[W1[GI[i[1]]] W3[GI[i[2]]]] +
   INS[W2[GI[i[1]]] W3[GI[i[1]]]] + INS[W2[GI[i[1]]] W3[GI[i[2]]]],
   TestID -> "INS-expand-product"];

(* Expand followed by GISum correctly sums over the now-independent dummy in each term *)
VerificationTest[
   With[{res = GISum[Expand[INS[W1[GI[i[1]]] (W2[GI[i[1]]] + W3[GI[i[1]]])]]]},
     res === GISum[INS[W1[GI[i[1]]] W2[GI[i[1]]]]] + GISum[INS[W1[GI[i[1]]] W3[GI[i[1]]]]]
   ],
   True,
   TestID -> "INS-expand-then-GISum"];

(* INS does NOT merge under Plus — each summand stays wrapped *)
VerificationTest[
   Head[INS[W1[GI[i[1]]] W2[GI[i[1]]]] + INS[W2[GI[i[1]]] W3[GI[i[1]]]]],
   Plus,
   TestID -> "INS-plus-no-merge"];

(* INS[x]^2: result is a single INS, and the two copies of any dummy get
   distinct index names (so the squared expression has 2 independent summation indices) *)
VerificationTest[
   With[{res = INS[W1[GI[i[1]]] W2[GI[i[1]]]]^2},
     MatchQ[res, INS[_]] &&
     Length[DeleteDuplicates[
       Cases[res /. INS[e_] :> e, GI[i[n_Integer]] :> n, Infinity]]] === 2
   ],
   True,
   TestID -> "INS-power-square-renames-dummy"];

(* INS[x]^3: three independent dummy indices *)
VerificationTest[
   With[{res = INS[W1[GI[i[1]]] W2[GI[i[1]]]]^3},
     MatchQ[res, INS[_]] &&
     Length[DeleteDuplicates[
       Cases[res /. INS[e_] :> e, GI[i[n_Integer]] :> n, Infinity]]] === 3
   ],
   True,
   TestID -> "INS-power-cube-renames-dummy"];

(* ================================================================== *)
(* 18. GISum                                                           *)
(* ================================================================== *)

(* Single INS term: INS wrapper preserved in each summed term *)
VerificationTest[
   GISum[INS[W1[GI[i[1]]] W2[GI[i[1]]]]],
   INS[W1[GI[1]] W2[GI[1]]] + INS[W1[GI[2]] W2[GI[2]]] + INS[W1[GI[3]] W2[GI[3]]],
   TestID -> "GISum-single-dummy"];

(* Bare sum: each summand auto-wrapped in INS, then summed *)
VerificationTest[
   GISum[W1[GI[i[1]]] W2[GI[i[1]]] + W2[GI[i[1]]] W3[GI[i[1]]]],
   (INS[W1[GI[1]] W2[GI[1]]] + INS[W1[GI[2]] W2[GI[2]]] + INS[W1[GI[3]] W2[GI[3]]]) +
   (INS[W2[GI[1]] W3[GI[1]]] + INS[W2[GI[2]] W3[GI[2]]] + INS[W2[GI[3]] W3[GI[3]]]),
   TestID -> "GISum-bare-sum-auto-wrap"];

(* No dummy index: INS wrapper returned unchanged *)
VerificationTest[
   GISum[INS[W1[GI[i[1]]] W2[GI[i[2]]]]],
   INS[W1[GI[i[1]]] W2[GI[i[2]]]],
   TestID -> "GISum-no-dummy"];

(* Concrete index GI[3] must NOT be treated as a dummy *)
VerificationTest[
   GISum[INS[W1[GI[3]] W2[GI[i[1]]]]],
   INS[W1[GI[3]] W2[GI[i[1]]]],
   TestID -> "GISum-concrete-index-not-dummy"];

(* Sum of two INS terms: each summed independently, INS preserved *)
VerificationTest[
   GISum[INS[W1[GI[i[1]]] W2[GI[i[1]]]] + INS[W2[GI[i[1]]] W3[GI[i[1]]]]],
   (INS[W1[GI[1]] W2[GI[1]]] + INS[W1[GI[2]] W2[GI[2]]] + INS[W1[GI[3]] W2[GI[3]]]) +
   (INS[W2[GI[1]] W3[GI[1]]] + INS[W2[GI[2]] W3[GI[2]]] + INS[W2[GI[3]] W3[GI[3]]]),
   TestID -> "GISum-sum-of-two-terms"];

(* Two independent GI dummies in one term: nested sums, INS on each term *)
VerificationTest[
   GISum[INS[W1[GI[i[1]]] W2[GI[i[1]]] W2[GI[i[2]]] W3[GI[i[2]]]]],
   Sum[INS[W1[GI[a]] W2[GI[a]] W2[GI[b]] W3[GI[b]]], {a, 1, 3}, {b, 1, 3}],
   TestID -> "GISum-two-dummies"];

(* End-to-end: covariant-derivative kinetic term with both LI and GI dummies.
   After INS multiplication resolves the GI conflict, GISum sums over the GI    *)
(* dummy; LI dummy i[1] stays free within each INS-wrapped summand.             *)
DeclareBoson[BB];
VerificationTest[
   With[{kinTerm =
     Expand[Conjugate[INS[BB[GI[i[1]], LI[i[1]]] + W1[GI[i[1]], LI[i[1]]]]] *
              INS[BB[GI[i[1]],LI[i[1]]] + W1[GI[i[1]], LI[i[1]]]]]},
     (* result is a Plus of INS-wrapped terms; GI index is concrete (1,2,3) *)
     MatchQ[GISum[kinTerm], _Plus] &&
     FreeQ[GISum[kinTerm], GI[i[_]]]
   ],
   True,
   TestID -> "GISum-mixed-LI-GI"];

(* ================================================================== *)
(* 19. Col: SU(2) column-vector wrapper                                *)
(* ================================================================== *)

(* Addition is component-wise — no spurious distribution *)
VerificationTest[Col[aa, bb] + Col[cc, dd], Col[aa + cc, bb + dd],
   TestID -> "Col-addition"];

(* Scalar multiplication threads into components *)
VerificationTest[3 * Col[aa, bb], Col[3 aa, 3 bb],
   TestID -> "Col-scalar-mult"];

(* KEY REGRESSION: symbolic S . Col[...] stays as Dot, then adding a Col
   does NOT distribute S.Col into each component *)
VerificationTest[
   Head[Col[aa, bb] + SS . Col[cc, dd]],
   Plus,
   TestID -> "Col-no-spurious-distribution"];
VerificationTest[
   FreeQ[Col[aa, bb] + SS . Col[cc, dd], Col[aa + SS . Col[cc, dd], __]],
   True,
   TestID -> "Col-plus-Dot-is-not-distributed"];

(* Explicit matrix dot: sigma[1] . Col[a,b] = Col[b, a] (before 1/2) *)
VerificationTest[
   sigma[GI[1]] . Col[aa, bb],
   Col[bb, aa],
   TestID -> "Col-mat-dot"];

(* Inner product Col . Col -> scalar *)
VerificationTest[Col[aa, bb] . Col[cc, dd], aa cc + bb dd,
   TestID -> "Col-inner-product"];

(* Row . matrix (CT context): {a,b} . {{1,0},{0,-1}} = {a,-b}, wrapped in Col *)
VerificationTest[
   Col[aa, bb] . sigma[GI[3]],
   Col[aa, -bb],
   TestID -> "Col-row-mat-dot"];

(* bar threads component-wise *)
VerificationTest[bar[Col[nu, el]], Col[bar[nu], bar[el]],
   TestID -> "Col-bar"];

(* d[mu] threads component-wise *)
VerificationTest[d[LI[i[1]]][Col[HH, chi]], Col[d[LI[i[1]]][HH], d[LI[i[1]]][chi]],
   TestID -> "Col-derivative"];

(* Conjugate threads component-wise *)
VerificationTest[Conjugate[Col[phip, phim]], Col[phim, phip],
   TestID -> "Col-conjugate"];

(* ConjugateTranspose threads Conjugate component-wise *)
VerificationTest[ConjugateTranspose[Col[phip, phim]], Col[phim, phip],
   TestID -> "Col-CT"];

(* ChargeConj: i sigma[2] . Conj[{phip,phim}] = i {{0,-I},{I,0}}.{phim,phip}
   = i {-I phip, I phim} = {phip, -phim} *)
VerificationTest[
   ChargeConj[Col[phip, phim]] === Col[phip, -phim],
   True,
   TestID -> "Col-ChargeConj"];

(* NC distributes over Col: Dirac operators act on each SU(2) component *)
VerificationTest[
   NC[PL, Col[nu, el]],
   Col[NC[PL, nu], NC[PL, el]],
   TestID -> "Col-NC-distributes"];

(* phi† M phi is a scalar: ConjugateTranspose . matrix . Col -> number-valued *)
VerificationTest[
   ConjugateTranspose[Col[aa, bb]] . sigma[GI[3]] . Col[aa, bb],
   Conjugate[aa] aa - Conjugate[bb] bb,
   TestID -> "Col-bilinear-scalar"];
