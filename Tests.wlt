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

VerificationTest[bosonQ[Wp[LI[mu]]],            True,  TestID -> "bosonQ-indexed"];
VerificationTest[bosonQ[el],                    False, TestID -> "bosonQ-fermion"];
VerificationTest[oddQ[el],                      True,  TestID -> "oddQ-fermion"];
VerificationTest[oddQ[bar[el]],                 True,  TestID -> "oddQ-barfermion"];
VerificationTest[oddQ[cc],                      True,  TestID -> "oddQ-ghost"];
VerificationTest[oddQ[Wp[LI[mu]]],              False, TestID -> "oddQ-boson"];
VerificationTest[fieldQ[Wp[LI[mu]]] && fieldQ[el] && fieldQ[bar[nu]], True,
   TestID -> "fieldQ-all"];
VerificationTest[scalarQ[gw],                   True,  TestID -> "scalarQ-coupling"];
VerificationTest[scalarQ[el] || scalarQ[Wp[LI[mu]]] || scalarQ[g[LI[a],LI[b]]],
   False, TestID -> "scalarQ-nonscalars"];
VerificationTest[diracMatQ[ga[LI[mu]]] && diracMatQ[PL] && diracMatQ[ga5],
   True,  TestID -> "diracMatQ-gamma-head"];   (* the Bug-2 regression guard *)

(* ================================================================== *)
(* 2. graded product **                                               *)
(* ================================================================== *)

(* boson/scalar factors fall out of the chain to an ordinary Times *)
VerificationTest[AA[LI[mu]] ** el,        AA[LI[mu]] NC[el],    TestID -> "nc-boson-out"];
VerificationTest[gw ** el,                gw NC[el],            TestID -> "nc-scalar-out"];
(* VerificationTest[NonCommutativeMultiply[el], el,            TestID -> "nc-single"]; *)
(* mixed Times argument: commuting part out, spinor part stays ordered *)
VerificationTest[bar[el] ** (gw ga[LI[mu]]) ** el,
   gw (bar[el] ** ga[LI[mu]] ** el),                        TestID -> "nc-mixed-split"];

(* ================================================================== *)
(* 3. bar conjugate                                                   *)
(* ================================================================== *)

VerificationTest[bar[el + nu],            bar[el] + bar[nu], TestID -> "bar-linear"];
VerificationTest[bar[gw el],              gw bar[el],        TestID -> "bar-real-coupling"];
VerificationTest[bar[0],                  0,                 TestID -> "bar-zero"];

(* ================================================================== *)
(* 4. derivative d                                                    *)
(* ================================================================== *)

VerificationTest[d[LI[mu]][gw AA[LI[nu]]], gw d[LI[mu]][AA[LI[nu]]],
   TestID -> "d-scalar-out"];
VerificationTest[d[LI[mu]][ga[LI[nu]]],   0,                 TestID -> "d-gamma-zero"];
(* graded Leibniz over a chain *)
VerificationTest[d[LI[mu]][bar[nu] ** el],
   d[LI[mu]][bar[nu]] ** el + bar[nu] ** d[LI[mu]][NC[el]],
   TestID -> "d-leibniz-chain"];

(* ================================================================== *)
(* 5. metric + contraction                                            *)
(* ================================================================== *)

VerificationTest[g[LI[mu], LI[mu]],       4,                 TestID -> "g-trace"];
VerificationTest[g[LI[a], LI[b]],         g[LI[b], LI[a]],   TestID -> "g-symmetric"];
VerificationTest[contract[g[LI[mu], LI[nu]] AA[LI[nu]]],  AA[LI[mu]],
   TestID -> "contract-vector"];

(* ================================================================== *)
(* 6. dummy-index canonicalization                                    *)
(* ================================================================== *)

(* the headline identity: relabelling dummies leaves a term invariant *)
VerificationTest[
   canonical[Wp[LI[mu]] Wm[LI[mu]] AA[LI[nu]] AA[LI[nu]]] ===
   canonical[Wp[LI[nu]] Wm[LI[nu]] AA[LI[mu]] AA[LI[mu]]],
   True, TestID -> "canon-relabel-invariant"];
(* a free index must NOT be renamed away *)
VerificationTest[FreeQ[canonical[Wp[LI[al]] Wm[LI[mu]] AA[LI[mu]]], LI[al]],
   False, TestID -> "canon-free-preserved"];

(* ================================================================== *)
(* 7. diracSimplify                                                   *)
(* ================================================================== *)

(* projector pushed right through a gamma:  PL ga^mu = ga^mu PR *)
VerificationTest[diracSimplify[PL ** ga[LI[mu]]],  ga[LI[mu]] ** PR,
   TestID -> "ds-PL-commute"];
(* idempotence / orthogonality *)
VerificationTest[diracSimplify[PL ** PL],          NC[PL],    TestID -> "ds-PLsq"];
VerificationTest[diracSimplify[PL ** PR],          0,     TestID -> "ds-PLPR"];
(* gamma5 -> projectors *)
VerificationTest[diracSimplify[bar[el] ** ga[LI[mu]] ** ga5 ** el],
   bar[el] ** ga[LI[mu]] ** PR ** el - bar[el] ** ga[LI[mu]] ** PL ** el,
   TestID -> "ds-ga5-expand"];
(* completeness P_L + P_R = 1 collapses a matched sum *)
VerificationTest[diracSimplify[
      bar[el] ** ga[LI[mu]] ** PL ** el + bar[el] ** ga[LI[mu]] ** PR ** el],
   bar[el] ** ga[LI[mu]] ** el,
   TestID -> "ds-completeness"];
(* ghost floats LEFT past a gamma (Bug-2 regression: gamma has head ga) *)
VerificationTest[diracSimplify[ga[LI[mu]] ** cc ** PL],
   cc ** ga[LI[mu]] ** PL,
   TestID -> "ds-ghost-float-gamma"];
(* ghost float then projector collection in one go *)
VerificationTest[diracSimplify[PL ** cc ** ga[LI[mu]]],
   cc ** ga[LI[mu]] ** PR,
   TestID -> "ds-ghost-float-then-commute"];

(* ================================================================== *)
(* 8. renorm substitution                                             *)
(* ================================================================== *)

(* Substitute only the right-handed leg el (no bar) so the test isolates    *)
(* the el -> (1+dZL)PL el + (1+dZR)PR el rule and the chain distribution.    *)
VerificationTest[
   diracSimplify[(ga[LI[mu]] ** el) /. renorm[el, dZL, dZR]] // Expand,
   NC[ga[LI[mu]],el]+dZL NC[ga[LI[mu]],PL,el]+dZR NC[ga[LI[mu]],PR,el],
   TestID -> "renorm-el-leg"];

(* ================================================================== *)
(* 9. Feynman rules (the end-to-end pipeline)                          *)
(* ================================================================== *)

VerificationTest[fdiff[{bar[nu], None, 
  k2}, (gw/Sqrt[2]) (bar[nu] ** ga[LI[mu]] ** PL ** el) Wp[LI[mu]]],(gw*NC[ga[LI[mu]], PL, el]*Wp[LI[mu]])/Sqrt[2],TestID->"fdiff"];

(* charged-current W vertex: purely left-handed *)
VerificationTest[
   feynmanRule[(gw/Sqrt[2]) (bar[nu] ** ga[LI[mu]] ** PL ** el) Wp[LI[mu]],
      {{Wp, LI[al], k1}, {bar[nu], None, k2}, {el, None, k3}}],
   I (gw/Sqrt[2]) (ga[LI[al]] ** PL),
   TestID -> "fr-W-vertex"];

(* pure vector coupling: no projector survives *)
VerificationTest[
   feynmanRule[ee (bar[el] ** ga[LI[mu]] ** el) AA[LI[mu]],
      {{AA, LI[al], k1}, {bar[el], None, k2}, {el, None, k3}}],
   I ee NC[ga[LI[al]]],
   TestID -> "fr-QED-vertex"];

(* general chiral Z coupling: keeps both projectors with their couplings *)
VerificationTest[
   Expand[feynmanRule[gz (bar[el] ** ga[LI[mu]] ** (gL PL + gR PR) ** el) Zb[LI[mu]],
      {{Zb, LI[al], k1}, {bar[el], None, k2}, {el, None, k3}}]],
   Expand[I gz (gL (ga[LI[al]] ** PL) + gR (ga[LI[al]] ** PR))],
   TestID -> "fr-Z-vertex"];

(* derivative -> momentum:  delta(d_mu A_nu)/delta A_al = (-I p_mu) g_{al nu}. *)
(* Tested directly on fdiff to isolate the rule (no spurious contraction).     *)
VerificationTest[
   fdiff[{AA, LI[al], k1}, d[LI[mu]][AA[LI[nu]]]],
   (-I k1[LI[mu]]) g[LI[al], LI[nu]],
   TestID -> "fdiff-derivative-momentum"];
