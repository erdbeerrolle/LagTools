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
   - I (ee/(sw cw)) (gL[I3wf,Qf] PL + gR[Qf] PR) ** f Zb[LI[mu]];

(*  Non-abelian field strengths in the mass-eigenstate basis.         *)
FA[mu_, nu_] :=
   d[LI[mu]][AA[LI[nu]]] - d[LI[nu]][AA[LI[mu]]]
   + I ee (Wm[LI[mu]] Wp[LI[nu]] - Wp[LI[mu]] Wm[LI[nu]]);

FZ[mu_, nu_] :=
   d[LI[mu]][Zb[LI[nu]]] - d[LI[nu]][Zb[LI[mu]]]
   + I ee (cw/sw) (Wm[LI[mu]] Wp[LI[nu]] - Wp[LI[mu]] Wm[LI[nu]]);
   
FWp[mu_, nu_] :=
   d[LI[mu]][Wp[LI[nu]]] - d[LI[nu]][Wp[LI[mu]]]
   - I ee ( Wp[LI[mu]] AA[LI[nu]] - AA[LI[mu]] Wp[LI[nu]])
   + I ee (cw/sw) (Wp[LI[mu]] Zb[LI[nu]] - Zb[LI[mu]] Wp[LI[nu]]);

FWm[mu_, nu_] :=
   d[LI[mu]][Wm[LI[nu]]] - d[LI[nu]][Wm[LI[mu]]]
   + I ee (Wm[LI[mu]] AA[LI[nu]] - AA[LI[mu]] Wm[LI[nu]])
   - I ee (cw/sw) (Wm[LI[mu]] Zb[LI[nu]] - Zb[LI[mu]] Wm[LI[nu]]);

(*  Higgs-sector covariant derivative (?) *)
covDphi[mu_] :=
   d[LI[mu]][phi]
   + I ee AA[LI[mu]] phi
   - I ee (cw^2 - sw^2)/(2 sw cw) Zb[LI[mu]] phi
   - I MW Wp[LI[mu]]
   - I (ee/(2 sw)) Wp[LI[mu]] (HH + I chi);

covDphim[mu_] :=
   d[LI[mu]][phim]
   - I ee AA[LI[mu]] phim
   + I ee (cw^2 - sw^2)/(2 sw cw) Zb[LI[mu]] phim
   + I MW Wm[LI[mu]]
   + I (ee/(2 sw)) Wm[LI[mu]] (HH - I chi);

covDHchi[mu_] :=
   d[LI[mu]][(HH + I chi)]
   - I (ee/sw) Wm[LI[mu]] phi
   + I MZ Zb[LI[mu]]
   + I (ee/(2 sw cw)) Zb[LI[mu]] (H + I chi);

covDHchiCC[mu_] :=
   d[LI[mu]][(HH - I chi)]
   + I (ee/sw) Wp[LI[mu]] phim
   - I MZ Zb[LI[mu]]
   - I (ee/(2 sw cw)) Zb[LI[mu]] (H - I chi);

(* ================================================================== *)
(*  4.  Lagrangian                                                    *)
(* ================================================================== *)

(* ---- 4a. Fermion sector (✓) ---- *)
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

(* ---- 4b. Gauge sector (✓) ---- *)

LgaugeA  = -(1/4) FA[mu, nu] FA[mu, nu];
LgaugeZ  = -(1/4) FZ[mu, nu] FZ[mu, nu];
LgaugeW  = -(1/2) FWp[mu, nu] FWm[mu, nu];

Lgauge = LgaugeA + LgaugeZ + LgaugeW;

(* ---- 4c. Higgs sector ---- *)
LHiggs1 = Expand[
      covDphim[mu] covDphi[mu]
    + (1/2) covDHchi[mu] covDHchiCC[mu]
];

LHiggs2 = ...;

LHiggs = LHiggs1 + LHiggs2;

(* ---- 4d. Yukawa coupling (✓) ---- *)
LYuk = -(ee me / (Sqrt[2] sw MW)) (
   bar[el] ** el HH
   - 2 I3we I bar[el] ** ga5 ** el chi    
);

(* ---- 4e. Gauge-fixing Lagrangian ('t Hooft-Feynman, xi=1) (✓) ---- *)
CA[mu_]  := d[LI[mu]][AA[LI[mu]]];
CZ[mu_]  := d[LI[mu]][Zb[LI[mu]]] - MZ chi;
CWp[mu_] := d[LI[mu]][Wp[LI[mu]]] - I MW phi;
CWm[mu_] := d[LI[mu]][Wm[LI[mu]]] + I MW phim;

Lfix = Expand[
   -(1/2) CA[a] CA[b]
   -(1/2) CZ[a] CZ[b]
   -CWp[a] * CWm[b]
];

(* ---- 4f. Faddeev-Popov ghost Lagrangian ---- *)
Lghost = 0;   (* to do -- derive using gauge trafo *)

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
