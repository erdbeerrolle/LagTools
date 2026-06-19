(* ::Package:: *)
(* ---------------------------------------------------------------------- *)
(*  SM electroweak Lagrangian                                             *)
(*  One lepton generation: e, nu_e.  No quarks.                           *)
(*  't Hooft-Feynman gauge                                                *)
(*  Reference: Denner, Dittmaier, EW Review, eqs. (22), (27)-(30).        *)
(*                                                                        *)
(*  Load with:                                                            *)
(*    Get[FileNameJoin[{ParentDirectory[$InputFileName], "LagTools.wl"}]] *)
(*    Get["...path.../Examples/EW.wl"]                                    *)
(* ---------------------------------------------------------------------- *)

Get[FileNameJoin[{ParentDirectory @ DirectoryName[$InputFileName], "LagTools.wl"}]];

(* ================================================================== *)
(*  1.  Fields                                                        *)
(* ================================================================== *)

DeclareBoson[AA, "A"];                                    (* photon            *)
DeclareBoson[Zb, "Z"];                                    (* Z boson           *)
DeclareBoson[Wp, SuperscriptBox["W", "+"]];               (* W+                *)
DeclareBoson[Wm, SuperscriptBox["W", "-"]];               (* W-                *)
DeclareBoson[HH,   "H"];                                  (* Higgs             *)
DeclareBoson[phi,  SuperscriptBox["\[Phi]", "+"]];        (* charged Goldstone *)
DeclareBoson[phim, SuperscriptBox["\[Phi]", "-"]];        (* charged Goldstone *)
DeclareBoson[chi,  "\[Chi]"];                             (* neutral Goldstone *)
DeclareFermion[el, "e"];                                  (* Electron          *)
DeclareFermion[nu, SubscriptBox["\[Nu]", "e"]];           (* Electron neutrino *)

(* ----- Faddeev-Popov ghosts: one u^a / ubar^a per gauge boson ----- *)
(*  The antighost ubar^a is a separate independent field, NOT bar[u]  *)            (* Why? *)
DeclareGrassmann[up,  SuperscriptBox["u", "+"]];
DeclareGrassmann[um,  SuperscriptBox["u", "-"]];
DeclareGrassmann[uz,  SuperscriptBox["u", "Z"]];
DeclareGrassmann[ua,  SuperscriptBox["u", "A"]];
DeclareGrassmann[ubp, SuperscriptBox[OverscriptBox["u", "\[Macron]"], "+"]];
DeclareGrassmann[ubm, SuperscriptBox[OverscriptBox["u", "\[Macron]"], "-"]];
DeclareGrassmann[ubz, SuperscriptBox[OverscriptBox["u", "\[Macron]"], "Z"]];
DeclareGrassmann[uba, SuperscriptBox[OverscriptBox["u", "\[Macron]"], "A"]];

(* ================================================================== *)
(*  2.  Parameters                                                    *)
(* ================================================================== *)

(*  All real *)
Scan[(# /: Conjugate[#] := #) &, {ee, sw, cw, I3we, Qe, I3wnu, MW, MZ, MH, me}];

(*  Neutrino: massless left-handed fermion -> PR ** nu = 0            *)
DeclareMassless[nu];

(*  Fancy display names                                               *)
MakeBoxes[I3we,  StandardForm] := SubsuperscriptBox["I", "3", "e"];
MakeBoxes[I3wnu, StandardForm] := SubsuperscriptBox["I", "3", "\[Nu]"];
MakeBoxes[Qe,    StandardForm] := SubscriptBox["Q", "e"];
MakeBoxes[ee,    StandardForm] := SubscriptBox["e", "EM"];
MakeBoxes[sw,    StandardForm] := SubscriptBox["s", "w"];
MakeBoxes[cw,    StandardForm] := SubscriptBox["c", "w"];
MakeBoxes[MW,    StandardForm] := SubscriptBox["M", "W"];
MakeBoxes[MZ,    StandardForm] := SubscriptBox["M", "Z"];
MakeBoxes[MH,    StandardForm] := SubscriptBox["M", "H"];
MakeBoxes[me,    StandardForm] := SubscriptBox["e", "e"];

(* ================================================================== *)
(*  3.  Covariant derivatives and field strengths                     *)
(* ================================================================== *)

(*  NC couplings derived from quantum numbers                        *)
gL[I3w,Q] := I3w  - Q  sw^2;    
gR[Q] := -Q  sw^2;

(* covaraint derivative *)
covDferm[mu_, Qf_, Iw3f_][f_] :=
   d[LI[mu]][f]
   - I ee Qf AA[LI[mu]] f
   - I (ee/(sw cw)) (gL[I3wf,Qf] PL + gR[Qf] PR) ** (Zb[LI[mu]] f);

(*  Non-abelian field strengths in the mass-eigenstate basis.         *)
FA[mu_, nu_] :=
   d[LI[mu]][AA[LI[nu]]] - d[LI[nu]][AA[LI[mu]]]
   + I ee (Wm[LI[mu]] Wp[LI[nu]] - Wp[LI[mu]] Wm[LI[nu]]);

FZ[mu_, nu_] :=
   d[LI[mu]][Zb[LI[nu]]] - d[LI[nu]][Zb[LI[mu]]]
   + I ee (cw/sw) (Wm[LI[mu]] Wp[LI[nu]] - Wp[LI[mu]] Wm[LI[nu]]);
   
FWp[mu_, nu_] :=
   d[LI[mu]][Wp[LI[nu]]] - d[LI[nu]][Wp[LI[mu]]]
   - I ee (AA[LI[mu]] Wp[LI[nu]] - Wp[LI[mu]] AA[LI[nu]])
   + I ee (cw/sw) (Zb[LI[mu]] Wp[LI[nu]] - Wp[LI[mu]] Zb[LI[nu]]);

FWm[mu_, nu_] :=
   d[LI[mu]][Wm[LI[nu]]] - d[LI[nu]][Wm[LI[mu]]]
   + I ee (AA[LI[mu]] Wm[LI[nu]] - Wm[LI[mu]] AA[LI[nu]])
   - I ee (cw/sw) (Zb[LI[mu]] Wm[LI[nu]] - Wm[LI[mu]] Zb[LI[nu]]);

(*  Helper: gauge-kinetic term from a field strength.                 *)
gaugeKin[F_] := -(1/4) g[LI[mu], LI[rh]] g[LI[nu], LI[si]]
                        F[mu, nu] F[rh, si];

(*  Higgs-sector covariant derivative (acts on the complex scalar     *)
(*  doublet; written here in terms of the mass-eigenstate fields).    *)
covDphi[mu_] :=
   d[LI[mu]][phi]
   - I ee AA[LI[mu]] phi
   + I ee (cw^2 - sw^2)/(2 sw cw) Zb[LI[mu]] phi
   + I (ee/(Sqrt[2] sw)) Wp[LI[mu]] (HH + I chi);

covDphim[mu_] :=
   d[LI[mu]][phim]
   + I ee AA[LI[mu]] phim
   - I ee (cw^2 - sw^2)/(2 sw cw) Zb[LI[mu]] phim
   - I (ee/(Sqrt[2] sw)) Wm[LI[mu]] (HH - I chi);

covDH[mu_] :=
   d[LI[mu]][HH]
   - (ee/(2 sw cw)) Zb[LI[mu]] chi
   - I (ee/(2 sw)) (Wp[LI[mu]] phim - Wm[LI[mu]] phi);

covDchi[mu_] :=
   d[LI[mu]][chi]
   + (ee/(2 sw cw)) Zb[LI[mu]] HH
   + (ee/(2 sw)) (Wp[LI[mu]] phim + Wm[LI[mu]] phi);

(* ================================================================== *)
(*  4.  Lagrangian                                                    *)
(* ================================================================== *)

(* ---- 4a. Fermion sector ---- *)
Lferm = Expand[
   (* covaraint derivative contains neutral-current couplings *)
   I bar[nu] ** ga[LI[mu]] ** covDferm[mu, 0,  I3wnu][nu]
 + I bar[el] ** ga[LI[mu]] ** covDferm[mu, Qe, I3we][el]
   (* charged current: W mixes nu <-> e *)
 + (ee/(Sqrt[2] sw)) bar[nu] ** ga[LI[mu]] ** PL ** el Wp[LI[mu]]
 + (ee/(Sqrt[2] sw)) bar[el] ** ga[LI[mu]] ** PL ** nu Wm[LI[mu]]
   (* electron mass; neutrino taken massless *)
 - me bar[el] ** el
];

(* ---- 4b. Gauge kinetic sector ---- *)

LgaugeA  = gaugeKin[FA];
LgaugeZ  = gaugeKin[FZ];
LgaugeW  = -(1/2) g[LI[mu], LI[rh]] g[LI[nu], LI[si]]
                  (FWp[mu, nu] FWm[rh, si] + FWm[mu, nu] FWp[rh, si]);

Lgauge = LgaugeA + LgaugeZ + LgaugeW;

(* ---- 4c. Higgs / scalar sector ---- *)
LHiggsKin = Expand[
   g[LI[mu], LI[nu]] (
      covDphim[mu] covDphi[nu]
    + (1/2) covDH[mu] covDH[nu]
    + (1/2) covDchi[mu] covDchi[nu])
];

LHiggsMass = -(1/2) MH^2 HH^2
             - MW^2 g[LI[mu], LI[nu]] Wp[LI[mu]] Wm[LI[nu]]
             - (1/2) MZ^2 g[LI[mu], LI[nu]] Zb[LI[mu]] Zb[LI[nu]]
             - MW^2 phi phim
             - (1/2) MZ^2 chi^2;

LHiggs = LHiggsKin + LHiggsMass;

(* ---- 4d. Yukawa coupling ---- *)
LYuk = -(ee me / (Sqrt[2] sw MW)) (
   bar[el] ** el HH
   + I bar[el] ** ga5 ** el chi     (* pseudoscalar Yukawa from chi *)
);

(* ---- 4e. Gauge-fixing Lagrangian ('t Hooft-Feynman, xi=1) ---- *)
(*  The gauge-fixing terms cancel the mixed  V_mu d^mu Goldstone   *)
(*  propagator entries from LHiggsKin.                             *)
CA[mu_]  := d[LI[mu]][AA[LI[mu]]];
CZ[mu_]  := d[LI[mu]][Zb[LI[mu]]] - MZ chi;
CWp[mu_] := d[LI[mu]][Wp[LI[mu]]] - I MW phi;
CWm[mu_] := d[LI[mu]][Wm[LI[mu]]] + I MW phim;

Lfix = Expand[
   -(1/2) g[LI[a], LI[b]] (d[LI[a]][AA[LI[b]]]) (d[LI[a]][AA[LI[b]]])
   -(1/2) (g[LI[a], LI[b]] d[LI[a]][Zb[LI[b]]] - MZ chi)^2
   -(g[LI[a], LI[b]] d[LI[a]][Wp[LI[b]]] - I MW phi) *
    (g[LI[a], LI[b]] d[LI[a]][Wm[LI[b]]] + I MW phim)
];

(* ---- 4f. Faddeev-Popov ghost Lagrangian ---- *)
(*  L_FP = ubar^a (-delta^{ab} d^2 - M^{ab}^2) u^b + interactions  *)
(*  In 't Hooft-Feynman gauge the ghost kinetic terms and masses are:*)
(*    ubar^+ (-d^2 - MW^2) u^+  +  ubar^- (-d^2 - MW^2) u^-         *)
(*    ubar^Z (-d^2 - MZ^2) u^Z  +  ubar^A (-d^2) u^A                *)
(*  Ghost interactions (gauge + Higgs) follow from the FP procedure  *)
(*  L_FP = - int d^4y ubar^a(x) delta C^a / delta theta^b(y) u^b(y) *)
(*  and are not written out here (extract vertices with feynmanRule). *)
LghostKin = Expand[
   g[LI[mu], LI[nu]] (
      ubp d[LI[mu]][d[LI[nu]][up]]
    + ubm d[LI[mu]][d[LI[nu]][um]]
    + ubz d[LI[mu]][d[LI[nu]][uz]]
    + uba d[LI[mu]][d[LI[nu]][ua]])
   - MW^2 (ubp up + ubm um)
   - MZ^2 (ubz uz)
];

Lghost = LghostKin;   (* add interaction terms from FP procedure as needed *)

(* ---- Total Lagrangian ---- *)
L = Expand[Lferm + Lgauge + LHiggs + LYuk + Lfix + Lghost];

(* ================================================================== *)
(*  5.  Example: extract Feynman rules                               *)
(* ================================================================== *)

(*  Photon-electron vertex  i e gamma^al                              *)
(*  feynmanRule[Lferm, {{AA, LI[al], k1}, {bar[el], None, k2}, {el, None, k3}}]  *)

(*  W-lepton charged-current vertex  i (e/sqrt2 sw) gamma^al PL      *)
(*  feynmanRule[Lferm, {{Wp, LI[al], k1}, {bar[nu], None, k2}, {el, None, k3}}]  *)

(*  Z-electron vertex  i (e/sw cw)(gLe gamma^al PL + gRe gamma^al PR)*)
(*  feynmanRule[Lferm, {{Zb, LI[al], k1}, {bar[el], None, k2}, {el, None, k3}}]  *)
