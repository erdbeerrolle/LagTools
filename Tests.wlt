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

(* ================================================================== *)
(* 1. predicates                                                      *)
(* ================================================================== *)

VerificationTest[bosonQ[Wp[LI[1]]],             True,  TestID -> "bosonQ-indexed"];
VerificationTest[bosonQ[el],                    False, TestID -> "bosonQ-fermion"];
VerificationTest[oddQ[el],                      True,  TestID -> "oddQ-fermion"];
VerificationTest[oddQ[bar[el]],                 True,  TestID -> "oddQ-barfermion"];
VerificationTest[oddQ[cc],                      True,  TestID -> "oddQ-ghost"];
VerificationTest[oddQ[Wp[LI[1]]],               False, TestID -> "oddQ-boson"];
VerificationTest[fieldQ[Wp[LI[1]]] && fieldQ[el] && fieldQ[bar[nu]], True,
   TestID -> "fieldQ-all"];
VerificationTest[STindepQ[gw],                   True,  TestID -> "STindepQ-coupling"];
VerificationTest[STindepQ[el] || STindepQ[Wp[LI[1]]],
   False, TestID -> "STindepQ-nonscalars"];
VerificationTest[diracMatQ[ga[LI[1]]] && diracMatQ[PL] && diracMatQ[ga5],
   True,  TestID -> "diracMatQ-gamma-head"];   (* the Bug-2 regression guard *)

(* ================================================================== *)
(* 2. graded product **                                               *)
(* ================================================================== *)

(* boson/scalar factors fall out of the chain to an ordinary Times *)
VerificationTest[AA[LI[1]] ** el,        AA[LI[1]] NC[el],    TestID -> "nc-boson-out"];
VerificationTest[gw ** el,               gw NC[el],            TestID -> "nc-scalar-out"];
(* VerificationTest[NonCommutativeMultiply[el], el,            TestID -> "nc-single"]; *)
(* mixed Times argument: commuting part out, spinor part stays ordered *)
VerificationTest[bar[el] ** (gw ga[LI[1]]) ** el,
   gw (bar[el] ** ga[LI[1]] ** el),                        TestID -> "nc-mixed-split"];

(* ================================================================== *)
(* 3. bar conjugate                                                   *)
(* ================================================================== *)

VerificationTest[bar[el + nu],            bar[el] + bar[nu], TestID -> "bar-linear"];
VerificationTest[bar[gw el],              gw bar[el],        TestID -> "bar-real-coupling"];
VerificationTest[bar[0],                  0,                 TestID -> "bar-zero"];

(* ================================================================== *)
(* 4. derivative d                                                    *)
(* ================================================================== *)

VerificationTest[d[LI[1]][gw AA[LI[2]]], gw d[LI[1]][AA[LI[2]]],
   TestID -> "d-scalar-out"];
VerificationTest[d[LI[1]][ga[LI[2]]],    0,                 TestID -> "d-gamma-zero"];
(* graded Leibniz over a chain *)
VerificationTest[d[LI[1]][bar[nu] ** el],
   d[LI[1]][bar[nu]] ** el + bar[nu] ** d[LI[1]][NC[el]],
   TestID -> "d-leibniz-chain"];

(* ================================================================== *)
(* 5. metric + contraction                                            *)
(* ================================================================== *)

VerificationTest[g[LI[1], LI[1]],        4,                 TestID -> "g-trace"];
VerificationTest[g[LI[1], LI[2]],        g[LI[2], LI[1]],  TestID -> "g-symmetric"];
VerificationTest[contract[g[LI[1], LI[2]] AA[LI[2]]],  AA[LI[1]],
   TestID -> "contract-vector"];

(* ================================================================== *)
(* 6. dummy-index canonicalization                                    *)
(* ================================================================== *)

(* the headline identity: relabelling dummies leaves a term invariant *)
VerificationTest[
   canonical[Wp[LI[1]] Wm[LI[1]] AA[LI[2]] AA[LI[2]]] ===
   canonical[Wp[LI[2]] Wm[LI[2]] AA[LI[1]] AA[LI[1]]],
   True, TestID -> "canon-relabel-invariant"];
(* a free index must NOT be renamed away *)
VerificationTest[FreeQ[canonical[Wp[LI[3]] Wm[LI[1]] AA[LI[1]]], LI[3]],
   False, TestID -> "canon-free-preserved"];

(* ================================================================== *)
(* 7. diracSimplify                                                   *)
(* ================================================================== *)

(* projector pushed right through a gamma:  PL ga^mu = ga^mu PR *)
VerificationTest[diracSimplify[PL ** ga[LI[1]]],  ga[LI[1]] ** PR,
   TestID -> "ds-PL-commute"];
(* idempotence / orthogonality *)
VerificationTest[diracSimplify[PL ** PL],          NC[PL],    TestID -> "ds-PLsq"];
VerificationTest[diracSimplify[PL ** PR],          0,         TestID -> "ds-PLPR"];
(* gamma5 -> projectors *)
VerificationTest[diracSimplify[bar[el] ** ga[LI[1]] ** ga5 ** el],
   bar[el] ** ga[LI[1]] ** PR ** el - bar[el] ** ga[LI[1]] ** PL ** el,
   TestID -> "ds-ga5-expand"];
(* completeness P_L + P_R = 1 collapses a matched sum *)
VerificationTest[diracSimplify[
      bar[el] ** ga[LI[1]] ** PL ** el + bar[el] ** ga[LI[1]] ** PR ** el],
   bar[el] ** ga[LI[1]] ** el,
   TestID -> "ds-completeness"];
(* ghost floats LEFT past a gamma (Bug-2 regression: gamma has head ga) *)
VerificationTest[diracSimplify[ga[LI[1]] ** cc ** PL],
   cc ** ga[LI[1]] ** PL,
   TestID -> "ds-ghost-float-gamma"];
(* ghost float then projector collection in one go *)
VerificationTest[diracSimplify[PL ** cc ** ga[LI[1]]],
   cc ** ga[LI[1]] ** PR,
   TestID -> "ds-ghost-float-then-commute"];

(* ================================================================== *)
(* 8. renorm substitution                                             *)
(* ================================================================== *)

(* Substitute only the right-handed leg el (no bar) so the test isolates    *)
(* the el -> (1+dZL)PL el + (1+dZR)PR el rule and the chain distribution.    *)
VerificationTest[
   diracSimplify[(ga[LI[1]] ** el) /. renorm[el, dZL, dZR]] // Expand,
   NC[ga[LI[1]],el]+dZL NC[ga[LI[1]],PL,el]+dZR NC[ga[LI[1]],PR,el],
   TestID -> "renorm-el-leg"];

(* ================================================================== *)
(* 9. Feynman rules (the end-to-end pipeline)                          *)
(* ================================================================== *)

VerificationTest[fdiff[{bar[nu], None,
  k2}, (gw/Sqrt[2]) (bar[nu] ** ga[LI[1]] ** PL ** el) Wp[LI[1]]],(gw*NC[ga[LI[1]], PL, el]*Wp[LI[1]])/Sqrt[2],TestID->"fdiff"];

(* charged-current W vertex: purely left-handed *)
VerificationTest[
   feynmanRule[(gw/Sqrt[2]) (bar[nu] ** ga[LI[1]] ** PL ** el) Wp[LI[1]],
      {{Wp, LI[2], k1}, {bar[nu], None, k2}, {el, None, k3}}],
   I (gw/Sqrt[2]) (ga[LI[2]] ** PL),
   TestID -> "fr-W-vertex"];

(* pure vector coupling: no projector survives *)
VerificationTest[
   feynmanRule[ee (bar[el] ** ga[LI[1]] ** el) AA[LI[1]],
      {{AA, LI[2], k1}, {bar[el], None, k2}, {el, None, k3}}],
   I ee NC[ga[LI[2]]],
   TestID -> "fr-QED-vertex"];

(* general chiral Z coupling: keeps both projectors with their couplings *)
VerificationTest[
   Expand[feynmanRule[gz (bar[el] ** ga[LI[1]] ** (gL PL + gR PR) ** el) Zb[LI[1]],
      {{Zb, LI[2], k1}, {bar[el], None, k2}, {el, None, k3}}]],
   Expand[I gz (gL (ga[LI[2]] ** PL) + gR (ga[LI[2]] ** PR))],
   TestID -> "fr-Z-vertex"];

(* derivative -> momentum:  delta(d_mu A_nu)/delta A_al = (-I p_mu) g_{al nu}. *)
(* Tested directly on fdiff to isolate the rule (no spurious contraction).     *)
VerificationTest[
   fdiff[{AA, LI[2], k1}, d[LI[1]][AA[LI[3]]]],
   (-I k1[LI[1]]) g[LI[2], LI[3]],
   TestID -> "fdiff-derivative-momentum"];
