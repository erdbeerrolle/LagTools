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
DeclareBoson[W1]; DeclareBoson[W2]; DeclareBoson[W3];
DeclareFermion[f1]; DeclareFermion[f2]; DeclareFermion[f3]; 
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
(* nested NC flattens into a single chain *)
VerificationTest[NC[bar[el], NC[ga[LI[i[1]]], el]],
   NC[bar[el], ga[LI[i[1]]], el],                             TestID -> "nc-flatten"];
(* adjacent ga0 pair cancels (ga0.ga0 = 1) — relied on by ConjugateTranspose chains *)
VerificationTest[NC[bar[el], ga0, ga0, el],
   NC[bar[el], el],                                           TestID -> "nc-ga0ga0-collapse"];

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

(* d[mu] on INS: pushed inside and index conflicts resolved.
   W1[LI[i[1]]] W2[LI[i[1]]] — LI[i[1]] is a dummy inside the INS.
   d[LI[i[1]]] carries LI[i[1]] as a free index, which would clash with
   the dummy.  The dummy must be renamed so it differs from i[1].
   We check that inside the derivative's argument the index i[1] is gone
   (it was renamed), while d[LI[i[1]]] itself still carries i[1]. *)
VerificationTest[
  With[{res = d[LI[i[1]]][INS[W1[LI[i[1]]] W2[LI[i[1]]]]]},
    (* d[LI[i[1]]] is present somewhere in the result *)
    !FreeQ[res, d[LI[i[1]]]] &&
    (* inside every d[LI[i[1]]][arg], the original dummy i[1] is absent *)
    AllTrue[
      Cases[res, d[LI[i[1]]][arg_] :> arg, Infinity],
      FreeQ[#, LI[i[1]]] &]
  ],
  True,
  TestID -> "d-INS-renames-dummy-clashing-with-derivative-index"];

(* ================================================================== *)
(* 5. metric + contraction                                            *)
(* ================================================================== *)

VerificationTest[g[LI[i[1]], LI[i[1]]], 4, TestID -> "g-trace"];
VerificationTest[g[LI[i[1]], LI[i[2]]], g[LI[i[2]], LI[i[1]]],  TestID -> "g-symmetric"];
VerificationTest[contract[g[LI[i[1]], LI[i[2]]] AA[LI[i[2]]]],  AA[LI[i[1]]],
   TestID -> "contract-vector"];

(* kd3 trace (sum rule) and off-diagonal *)
VerificationTest[kd3[FI[i[1]], FI[i[1]]], 3, TestID -> "kd3-FI-trace"];
VerificationTest[kd3[GI[i[1]], GI[i[1]]], 3, TestID -> "kd3-GI-trace"];
VerificationTest[kd3[FI[i[1]], FI[i[2]]], kd3[FI[i[2]], FI[i[1]]], TestID -> "kd3-symmetric"];
VerificationTest[contract[kd3[FI[i[1]], FI[i[2]]] el[FI[i[2]]]], el[FI[i[1]]], TestID -> "kd3-contract-FI"];

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
(* 7b. ConjugateTranspose (dagger) and Hermiticity                    *)
(* ================================================================== *)

(* atomic Dirac rules *)
VerificationTest[ConjugateTranspose[ga[LI[i[1]]]], NC[ga0, ga[LI[i[1]]], ga0], TestID -> "CT-gamma"];
VerificationTest[ConjugateTranspose[ga0],          ga0,                        TestID -> "CT-ga0"];
VerificationTest[ConjugateTranspose[ga5],          -NC[ga0, ga5, ga0],         TestID -> "CT-ga5"];
VerificationTest[ConjugateTranspose[PL],           NC[ga0, PR, ga0],           TestID -> "CT-PL"];
VerificationTest[ConjugateTranspose[PR],           NC[ga0, PL, ga0],           TestID -> "CT-PR"];
VerificationTest[ConjugateTranspose[el],           NC[bar[el], ga0],           TestID -> "CT-fermion"];
VerificationTest[ConjugateTranspose[bar[el]],      NC[ga0, el],                TestID -> "CT-barfermion"];

(* NC-chain reversal: (nu-bar gamma^mu P_L el)^dagger = el-bar gamma^mu P_L nu
   (h.c. of the charged current).  Exercises chain reversal AND the
   ga0.ga0 -> 1 collapse together. *)
VerificationTest[
   diracSimplify[ConjugateTranspose[NC[bar[nu], ga[LI[i[1]]], PL, el]]],
   NC[bar[el], ga[LI[i[1]]], PL, nu],
   TestID -> "CT-chain-reversal-hc"];

(* the vector current el-bar gamma^mu el is Hermitian: dagger returns it unchanged *)
VerificationTest[
   diracSimplify[ConjugateTranspose[NC[bar[el], ga[LI[i[1]]], el]]],
   NC[bar[el], ga[LI[i[1]]], el],
   TestID -> "CT-vector-current-hermitian"];

(* involution: dagger-dagger is the identity (up to diracSimplify normal form) *)
VerificationTest[
   diracSimplify[ConjugateTranspose[ConjugateTranspose[NC[bar[nu], ga[LI[i[1]]], PL, el]]]],
   diracSimplify[NC[bar[nu], ga[LI[i[1]]], PL, el]],
   TestID -> "CT-involution"];

(* Hermiticity round-trip on a coupled term (gw real): dagger-dagger preserves it.
   Composes scalar Conjugate, chain reversal, ga0 collapse and bar/fermion CT. *)
VerificationTest[
   Expand[diracSimplify[ConjugateTranspose[ConjugateTranspose[
      gw NC[bar[nu], ga[LI[i[1]]], PL, el]]]]],
   Expand[diracSimplify[gw NC[bar[nu], ga[LI[i[1]]], PL, el]]],
   TestID -> "CT-hermiticity-roundtrip"];

(* dagger pushes through INS (the refactor's converted UpValue): CT[INS[x]] = INS[CT[x]] *)
VerificationTest[
   ConjugateTranspose[INS[bar[el[FI[i[1]]]]]],
   INS[NC[ga0, el[FI[i[1]]]]],
   TestID -> "CT-INS-pushthrough"];
(* dagger inside INS on a full bilinear: INS preserved, bilinear is Hermitian *)
VerificationTest[
   ConjugateTranspose[INS[bar[el] ** ga[LI[i[1]]] ** el]],
   INS[bar[el] ** ga[LI[i[1]]] ** el],
   TestID -> "CT-INS-bilinear-hermitian"];

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
  k2}, (gw/Sqrt[2]) (bar[nu] ** ga[LI[i[1]]] ** PL ** el) Wp[LI[i[1]]]],(gw*INS[NC[ga[LI[i[1]]], PL, el]*Wp[LI[i[1]]]])/Sqrt[2],TestID->"fdiff"];

(* dummy clash resolution: leg index i[1] clashes with dummy i[1] in expression; *)
(* after contraction the result must equal the clash-free case *)
VerificationTest[
  contract[fdiff[{AA, LI[i[1]], k1}, AA[LI[i[1]]] * AA[LI[i[1]]]]],
  2 INS[AA[LI[i[1]]]],
  TestID -> "fdiff-dummy-clash-resolution"];

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
   (-I) INS[k1[LI[i[1]]] * g[LI[i[2]], LI[i[3]]]],
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

(* Multiplication with no index conflict: inner expressions combined verbatim *)
VerificationTest[
   INS[W1[GI[i[1]]] W2[GI[i[2]]]] * INS[W3[GI[i[3]]]],
   INS[W1[GI[i[1]]] W2[GI[i[2]]] W3[GI[i[3]]]],
   TestID -> "INS-times-no-conflict"];

(* Multiplication renames conflicting dummy in the second factor *)
VerificationTest[
   With[{res = INS[W1[GI[i[1]]] W2[GI[i[1]]]] * INS[W2[GI[i[1]]] W3[GI[i[1]]]]},
     MatchQ[res, INS[_]] &&
     (* the result must still contain the original first factor's i[1]--outdated *)
     (*!FreeQ[res, GI[i[1]]] &&*)
     (* and the second factor's dummy must have been renamed to something else *)
     Length[DeleteDuplicates[
       Cases[res /. INS[e_] :> e, GI[i[n_Integer]] :> n, Infinity]]] === 2
   ],
   True,
   TestID -> "INS-times-renames-dummy"];

(* NC with bosonic INS: commuting content collapses NC to Times, then Times rule renames *)
VerificationTest[
   With[{res = NC[INS[f1[GI[i[1]]] f2[GI[i[1]]]], INS[f2[GI[i[1]]] f3[GI[i[1]]]]]},
     MatchQ[res, HoldPattern[INS[NC[__]]]] &&
     (*!FreeQ[res, GI[i[1]]] &&*)
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

(* Dummy in first clashes with free index in second, and vice versa.
   The original bug renamed the free indices instead of the dummies.
   Setup: a[FI[i[1]], FI[i[2]], FI[i[2]]]  — free i[1], dummy i[2]
          b[FI[i[2]], FI[i[1]], FI[i[1]]]  — free i[2], dummy i[1]
   Correct result: dummies renamed to fresh values; free indices i[1] and i[2]
   untouched.  Combined expression must have exactly 4 distinct FI index values. *)
VerificationTest[
  With[{res = INS[a[FI[i[1]], FI[i[2]], FI[i[2]]]] *
              INS[b[FI[i[2]], FI[i[1]], FI[i[1]]]]},
    Length[DeleteDuplicates[
      Cases[res /. INS[e_] :> e, FI[i[n_Integer]] :> n, Infinity]]] === 4
  ],
  True,
  TestID -> "INS-times-free-dummy-cross-clash-4-indices"];

(* Same setup: free index i[1] in the first factor must NOT be renamed —
   a[FI[i[1]], _, _] must still appear in the result *)
VerificationTest[
  With[{res = INS[a[FI[i[1]], FI[i[2]], FI[i[2]]]] *
              INS[b[FI[i[2]], FI[i[1]], FI[i[1]]]]},
    !FreeQ[res /. INS[e_] :> e, a[FI[i[1]], _, _]]
  ],
  True,
  TestID -> "INS-times-free-index-survives"];

(* INS[a] * b where b is indexed but not INS-wrapped: b is absorbed into INS
   and dummy conflicts are resolved.  Result must be a single INS with 2
   distinct index values (one from a's dummy, one from b's dummy). *)
VerificationTest[
  With[{res = INS[W1[GI[i[1]]] W2[GI[i[1]]]] * W3[GI[i[1]]] W4[GI[i[1]]]},
    MatchQ[res, HoldPattern[INS[_]]] &&
    Length[DeleteDuplicates[
      Cases[res /. INS[e_] :> e, GI[i[n_Integer]] :> n, Infinity]]] === 2
  ],
  True,
  TestID -> "INS-times-absorb-indexed-non-INS"];

(* NC variant: free-dummy cross-clash between two fermion bilinears *)
VerificationTest[
  With[{res = NC[INS[f1[GI[i[1]]] f2[GI[i[1]]]],
               INS[f2[GI[i[1]]] f3[GI[i[1]]]]]},
    MatchQ[res, HoldPattern[INS[NC[__]]]] &&
    Length[DeleteDuplicates[
      Cases[res /. INS[e_] :> e, GI[i[n_Integer]] :> n, Infinity]]] === 2
  ],
  True,
  TestID -> "INS-NC-free-dummy-clash-2-distinct-indices"];

(* ================================================================== *)
(* 17b. INS inside Dot chains (lines 343-352 of LagTools.wl)         *)
(* ================================================================== *)

(* Two INS in a Dot chain: dummy conflicts resolved, result is a single INS[Dot[...]] *)
(* Use sigma matrices: they are su2MatQ (not su2ScalarQ) so they stay inside Dot *)
VerificationTest[
  With[{res = INS[sigma[GI[i[1]]]^2] . INS[sigma[GI[i[1]]]^2]},
    MatchQ[res, HoldPattern[INS[_Dot]]] &&
    Length[DeleteDuplicates[
      Cases[res /. INS[e_] :> e, GI[i[n_Integer]] :> n, Infinity]]] === 2
  ],
  True,
  TestID -> "INS-dot-two-INS-conflict-resolved"];

(* Index-free factor to the right of INS: absorbed without conflict check *)
VerificationTest[
  INS[sigma[GI[i[1]]]^2] . gw,
  INS[Dot[sigma[GI[i[1]]]^2, gw]],
  TestID -> "INS-dot-indexfree-right"];

(* Index-free factor to the left of INS: absorbed without conflict check *)
VerificationTest[
  gw . INS[sigma[GI[i[1]]]^2],
  INS[Dot[gw, sigma[GI[i[1]]]^2]],
  TestID -> "INS-dot-indexfree-left"];

(* Indexed non-INS to the right: absorbed into INS, dummy conflicts resolved *)
VerificationTest[
  With[{res = INS[sigma[GI[i[1]]]^2] . sigma[GI[i[1]]]},
    MatchQ[res, HoldPattern[INS[_Dot]]] &&
    Length[DeleteDuplicates[
      Cases[res , GI[i[n_Integer]] :> n, Infinity]]] === 2
  ],
  True,
  TestID -> "INS-dot-indexed-non-INS-right"];

(* Indexed non-INS to the left: absorbed into INS, dummy conflicts resolved *)
VerificationTest[
  With[{res = sigma[GI[i[1]]] . INS[sigma[GI[i[1]]]^2]},
    MatchQ[res, HoldPattern[INS[_Dot]]] &&
    Length[DeleteDuplicates[
      Cases[res, GI[i[n_Integer]] :> n, Infinity]]] === 2
  ],
  True,
  TestID -> "INS-dot-indexed-non-INS-left"];

(* Order preserved: b . INS[a] gives INS[Dot[b', a']] with b' first *)
VerificationTest[
  With[{res = sigma[GI[i[1]]] . INS[sigma[GI[i[1]]]^2]},
    MatchQ[res /. HoldPattern[INS[e_]]:>e, Dot[sigma[_], __]]
  ],
  True,
  TestID -> "INS-dot-indexed-non-INS-left-order"];

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
(*VerificationTest[
   NC[PL, Col[nu, el]],
   Col[NC[PL, nu], NC[PL, el]],
   TestID -> "Col-NC-distributes"];*)

(* phi† M phi is a scalar: ConjugateTranspose . matrix . Col -> number-valued *)
VerificationTest[
   ConjugateTranspose[Col[aa, bb]] . sigma[GI[3]] . Col[aa, bb],
   Conjugate[aa] aa - Conjugate[bb] bb,
   TestID -> "Col-bilinear-scalar"];

(* NC of two doublets sums over the 2x2 components (Col owns NC via UpValue) *)
VerificationTest[
   NC[Col[bar[nu], bar[el]], Col[nu, el]],
   NC[bar[nu], nu] + NC[bar[nu], el] + NC[bar[el], nu] + NC[bar[el], el],
   TestID -> "Col-NC-two-doublets"];
(* with an SU(2)-scalar (PL) sandwiched between the doublets *)
VerificationTest[
   NC[Col[bar[nu], bar[el]], PL, Col[nu, el]],
   NC[bar[nu], PL, nu] + NC[bar[nu], PL, el] + NC[bar[el], PL, nu] + NC[bar[el], PL, el],
   TestID -> "Col-NC-two-doublets-su2scalar"];

(* ------------------------------------------------------------------ *)
(*  INSFreeRule                                                        *)
(* ------------------------------------------------------------------ *)

(* Basic renaming: matched index i[1] forces explicit i[1] -> i[2] *)
VerificationTest[
   dq[FI[i[1]]] /. {INSRule[dq[FI[i[c_]]],
      dq[FI[i[1]]] * Conjugate[Ud[FI[i[1]], FI[i[c]]]]]},
   INS[Conjugate[Ud[FI[i[2]], FI[i[1]]]] dq[FI[i[2]]]],
   TestID -> "INSRule-rename-clash"];

(* No clash: matched index i[2] leaves explicit i[1] as-is *)
VerificationTest[
   dq[FI[i[2]]] /. {INSRule[dq[FI[i[c_]]],
      dq[FI[i[1]]] * Conjugate[Ud[FI[i[1]], FI[i[c]]]]]},
   INS[Conjugate[Ud[FI[i[1]], FI[i[2]]]] dq[FI[i[1]]]],
   TestID -> "INSRule-no-clash"];

(* Two explicit indices with a higher matched index: both must be renamed *)
VerificationTest[
   dq[FI[i[3]]] /. {INSRule[dq[FI[i[c_]]],
      dq[FI[i[1]]] * Ud[FI[i[1]], FI[i[2]]] * Ud[FI[i[2]], FI[i[c]]]]},
   INS[dq[FI[i[1]]] * Ud[FI[i[1]], FI[i[2]]] * Ud[FI[i[2]], FI[i[3]]]],
   TestID -> "INSRule-two-explicit-no-clash"];

(* ================================================================== *)
(* 20. INS absorption into NC chains                                   *)
(* ================================================================== *)

(* index-free element on the right of INS is absorbed without conflict check *)
VerificationTest[
   NC[INS[W1[GI[i[1]]] W2[GI[i[1]]]], PL],
   INS[NC[W1[GI[i[1]]] W2[GI[i[1]]], PL]],
   TestID -> "INS-NC-absorb-indexfree-right"];

(* index-free element on the left of INS is absorbed without conflict check *)
VerificationTest[
   NC[PR, INS[W1[GI[i[1]]] W2[GI[i[1]]]]],
   INS[NC[PR, W1[GI[i[1]]] W2[GI[i[1]]]]],
   TestID -> "INS-NC-absorb-indexfree-left"];

(* singleton NC[INS[a]] collapses to INS[NC[a]] *)
VerificationTest[
   NC[INS[W1[GI[i[1]]] W2[GI[i[1]]]]],
   INS[NC[W1[GI[i[1]]] W2[GI[i[1]]]]],
   TestID -> "INS-NC-singleton"];

(* sandwiched index-free: NC[INS[a], PL, INS[b]] with bosonic content.
   W bosons commute out of NC, so the result is an index-free prefactor times
   a single INS — no remaining NC[..., INS[...], ...] in the output. *)
VerificationTest[
   With[{res = NC[INS[W1[GI[i[1]]] W2[GI[i[1]]]], PL, INS[W1[GI[i[1]]] W3[GI[i[1]]]]]},
      (* no INS should remain as a direct argument of NC *)
      FreeQ[res, HoldPattern[NC[___, _INS, ___]]] &&
      (* result still contains a single INS *)
      !FreeQ[res, _INS] &&
      (* two distinct GI dummy indices from the merged product *)
      Length[DeleteDuplicates[Cases[res, GI[i[n_Integer]] :> n, Infinity]]] === 2
   ],
   True,
   TestID -> "INS-NC-absorb-PL-sandwich"];

(* bar pushes through INS *)
VerificationTest[
   bar[INS[W1[GI[i[1]]] W2[GI[i[1]]]]],
   INS[bar[W1[GI[i[1]]] W2[GI[i[1]]]]],
   TestID -> "INS-bar-pushthrough"];

(* full flavor-matrix example: NC[INS[a], PL, INS[b]] with fermionic/FI content.
   After all absorptions the result contains no NC with INS arguments,
   and the merged INS holds 4 distinct FI dummy index slots. *)
VerificationTest[
   With[{res = NC[
         INS[bar[dq[FI[i[1]]]] Ud[FI[i[1]], FI[i[2]]]],
         PL,
         INS[Conjugate[Ud[FI[i[2]], FI[i[1]]]] dq[FI[i[2]]]]]},
      FreeQ[res, HoldPattern[NC[___, _INS, ___]]] &&
      !FreeQ[res, _INS] &&
      Length[DeleteDuplicates[Cases[res, FI[i[n_Integer]] :> n, Infinity]]] === 4
   ],
   True,
   TestID -> "INS-NC-flavor-matrix-fullexample"];

(* ================================================================== *)
(* 21. Gauge structure: ExplGaugeMult / ExplCovD order-independence    *)
(*                                                                     *)
(*  Regressions for bugs where applying ExplGaugeMult BEFORE ExplCovD  *)
(*  (the doublet symbol is expanded to its component Col first) gave   *)
(*  wrong results, while ExplCovD-first worked.                        *)
(* ================================================================== *)

DeclareRealParam[g1]; DeclareRealParam[g2];
DeclareRealBoson[Bb]; DeclareRealBoson[Wb];

(* EW-style covariant derivative: d - i g2 W^a T^a + i/2 g1 B Y *)
DeclareCovD[CovDew, "D",
   CovDew[mu_][f_] :> INS[d[mu][f]
      - I*g2*Wb[GI[i[1]], mu]*SU2T[GI[i[1]]][f]
      + I/2*g1*Bb[mu]*U1Y[f]]];

(* ---- root cause: a doublet column is NOT an SU(2) scalar ---- *)
VerificationTest[su2ScalarQ[Col[phip, HH]], False,
   TestID -> "col-not-su2scalar"];
VerificationTest[
   scalarQ[CovDew[LI[i[1]]][Col[phip, (v + HH + I*chi)/Sqrt[2]]]],
   False,
   TestID -> "covD-of-col-not-scalar"];

(* ---- bug 2: an index shared across the two Col entries is ONE slot ---- *)
VerificationTest[
   dummyIndices[GI][Col[aa[GI[i[1]]], bb[GI[i[1]]]]],
   {},
   TestID -> "col-shared-index-not-dummy"];
VerificationTest[
   dummyIndices[GI][qq[GI[i[1]]]*Col[aa[GI[i[1]]], bb[GI[i[1]]]]],
   {GI[i[1]]},
   TestID -> "col-index-contracts-once"];
(* a constant upper component must not hide the index in the lower one *)
VerificationTest[
   extractIndices[GI][Col[1, bb[GI[i[1]]]]],
   {i[1]},
   TestID -> "col-constant-entry-keeps-index"];

(* ---- bare fields are treated as SU(2) singlets by both generators ---- *)
DeclareRealBoson[loneS];                 (* Q = 0 real scalar, unregistered *)
DeclareComplexBoson[loneP, loneM];       (* Q[loneP] = +1 *)
VerificationTest[U1Y[loneS], 0,                  TestID -> "U1Y-singlet-fallback-neutral"];
VerificationTest[U1Y[loneP], 2*ElectricCharge[loneP]*loneP, TestID -> "U1Y-singlet-fallback-charged"];
VerificationTest[SU2T[GI[i[1]]][loneS], 0,       TestID -> "SU2T-singlet-fallback"];
(* non-fields must NOT trigger the singlet fallback -> stay unevaluated *)
VerificationTest[U1Y[loneS + loneP],   U1Y[loneS + loneP],   TestID -> "U1Y-nonfield-unevaluated"];
VerificationTest[SU2T[GI[i[1]]][loneS + loneP], SU2T[GI[i[1]]][loneS + loneP],
   TestID -> "SU2T-nonfield-unevaluated"];
(* a doublet symbol awaiting ExplGaugeMult must NOT be annihilated *)
VerificationTest[SU2T[GI[i[1]]][Phi], SU2T[GI[i[1]]][Phi], TestID -> "SU2T-doublet-symbol-symbolic"];

(* ---- bug 3: U1Y recovers the multiplet hypercharge from a column ---- *)
VerificationTest[
   U1Y[Col[phip, (v + HH + I*chi)/Sqrt[2]]],
   Hypercharge[Phi]*Col[phip, (v + HH + I*chi)/Sqrt[2]],
   TestID -> "U1Y-doublet-column"];
(* the daggered column (from ConjugateTranspose[Phi]) carries the same Y *)
VerificationTest[
   U1Y[Col[phim, (v + HH - I*chi)/Sqrt[2]]],
   Hypercharge[Phi]*Col[phim, (v + HH - I*chi)/Sqrt[2]],
   TestID -> "U1Y-conjugate-column"];

(* ---- bug 1: (D_mu X)^dagger is the conjugate rep: sigma moves to the
        RIGHT of the column, no Pauli matrix left dangling on a scalar ---- *)
(* CT of an unexpanded covariant derivative stays symbolic until ExplCovD *)
VerificationTest[
   MatchQ[
      ConjugateTranspose[CovDew[LI[i[1]]][Col[phip, (v + HH + I*chi)/Sqrt[2]]]],
      _ConjugateTranspose],
   True,
   TestID -> "CT-covD-stays-symbolic"];
(* once expanded, daggering gives the conjugate rep: sigma sits to the RIGHT of
   the column (no Pauli matrix dangling at the head of a Dot) *)
VerificationTest[
   Cases[
      ExplCovD[ConjugateTranspose[CovDew[LI[i[1]]][Col[phip, (v + HH + I*chi)/Sqrt[2]]]]],
      Dot[sigma[_], ___], Infinity],
   {},
   TestID -> "CT-covD-sigma-on-right"];

(* ---- headline: |D Phi|^2 is identical in both expansion orders ---- *)
VerificationTest[
   Module[{dphi = ConjugateTranspose[CovDew[LI[i[1]]][Phi]] . CovDew[LI[i[1]]][Phi]},
      canonical[Expand[GISum[ExplGaugeMult[ExplCovD[dphi]]]]] ===
      canonical[Expand[GISum[ExplCovD[ExplGaugeMult[dphi]]]]]],
   True,
   TestID -> "covD-order-independence-higgs"];
