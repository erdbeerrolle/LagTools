(* ::Package:: *)

(* ======================================================================
   EWSMLagrangian.wl  --  Electroweak Standard Model Lagrangian
   Conventions: Denner & Dittmaier, Phys. Rept. 864 (2020) 1
                arXiv:1912.06823, Sects. 2.1.1-2.1.3
   ====================================================================== *)

Get[FileNameJoin[{DirectoryName[$InputFileName], "LagTools.wl"}]];

(* ====================================================================== *)
(*  FIELDS                                                                 *)
(* ====================================================================== *)

(* --- Gauge bosons in the gauge basis (used in steps 1-2) --- *)
DeclareBoson[W, "W"];    (* SU(2) *)
DeclareBoson[B, "B"];    (* U(1)  *)

(* --- Physical (mass-eigenstate) gauge bosons  (DD eqs. 15-16) --- *)
DeclareBoson[AA,  "A"];
DeclareBoson[Zb,  "Z"];
DeclareBoson[Wp,  SuperscriptBox["W", "+"]];
DeclareBoson[Wm,  SuperscriptBox["W", "-"]];

(* --- Higgs and would-be Goldstone fields in the physical basis  (DD eq. 14) ---
   Phi = { phi^+,  (v + H + i chi)/Sqrt[2] }
   phi^- = (phi^+)^*,  chi and H are real                                 *)
DeclareBoson[HH,   "H"];
DeclareBoson[phi,  SuperscriptBox["\[Phi]", "+"]];
DeclareBoson[phim, SuperscriptBox["\[Phi]", "-"]];
DeclareBoson[chi,  "\[Chi]"];

(* --- Fermions: Dirac spinor fields. Chiral components via PL/PR --- *)
DeclareFermion[nu, "\[Nu]"];
DeclareFermion[el, "l"];
DeclareFermion[uq, "u"];
DeclareFermion[dq, "d"];

(* --- Faddeev-Popov ghosts in the physical basis --- *)
DeclareGrassmann[up,  SuperscriptBox["u",         "+"]];
DeclareGrassmann[um,  SuperscriptBox["u",         "-"]];
DeclareGrassmann[uz,  SuperscriptBox["u",         "Z"]];
DeclareGrassmann[ua,  SuperscriptBox["u",         "A"]];
DeclareGrassmann[ubp, SuperscriptBox[OverBar["u"],"+"]];
DeclareGrassmann[ubm, SuperscriptBox[OverBar["u"],"-"]];
DeclareGrassmann[ubz, SuperscriptBox[OverBar["u"],"Z"]];
DeclareGrassmann[uba, SuperscriptBox[OverBar["u"],"A"]];

(* ====================================================================== *)
(*  PARAMETERS                                                             *)
(* ====================================================================== *)

(* Real scalar fields *)
Scan[(# /: Conjugate[#] := #) &, {HH, chi}];
phi  /: Conjugate[phi]  := phim;
phim /: Conjugate[phim] := phi;

(* Real gauge-basis parameters *)
Scan[(# /: Conjugate[#] := #) &, {g1, g2, mu2, lam, v}];

Unprotect[MakeBoxes];
MakeBoxes[g1,  StandardForm] := SubscriptBox["g", "1"];
MakeBoxes[g2,  StandardForm] := SubscriptBox["g", "2"];
MakeBoxes[mu2, StandardForm] := SuperscriptBox["\[Mu]", "2"];
MakeBoxes[lam, StandardForm] := "\[Lambda]";
MakeBoxes[v,   StandardForm] := "v";

(* Real physical parameters *)
Scan[(# /: Conjugate[#] := #) &, {ee, sw, cw, MW, MZ, MH, xiW, xiZ}];

MakeBoxes[ee,  StandardForm] := SubscriptBox["e",  "EM"];
MakeBoxes[sw,  StandardForm] := SubscriptBox["s",  "w"];
MakeBoxes[cw,  StandardForm] := SubscriptBox["c",  "w"];
MakeBoxes[MW,  StandardForm] := SubscriptBox["M",  "W"];
MakeBoxes[MZ,  StandardForm] := SubscriptBox["M",  "Z"];
MakeBoxes[MH,  StandardForm] := SubscriptBox["M",  "H"];
MakeBoxes[xiW, StandardForm] := SubscriptBox["\[Xi]", "W"];
MakeBoxes[xiZ, StandardForm] := SubscriptBox["\[Xi]", "Z"];
MakeBoxes[mf[f_, i_], StandardForm] :=
  SubscriptBox["m", RowBox[{MakeBoxes[f, StandardForm], ",", MakeBoxes[i, StandardForm]}]];

(* Yukawa coupling matrices y^f_{ij} *)
MakeBoxes[yl[i_,j_], StandardForm] :=
  SubsuperscriptBox["y", RowBox[{MakeBoxes[i,StandardForm], MakeBoxes[j,StandardForm]}], "l"];
MakeBoxes[yu[i_,j_], StandardForm] :=
  SubsuperscriptBox["y", RowBox[{MakeBoxes[i,StandardForm], MakeBoxes[j,StandardForm]}], "u"];
MakeBoxes[yd[i_,j_], StandardForm] :=
  SubsuperscriptBox["y", RowBox[{MakeBoxes[i,StandardForm], MakeBoxes[j,StandardForm]}], "d"];
Protect[MakeBoxes];

(* ====================================================================== *)
(*  STEP 1 — CLASSICAL LAGRANGIAN (ABSTRACT FORM)                         *)
(*                                                                        *)
(*  L = -1/4 W^a_{mu nu} W^{a mu nu} - 1/4 B_{mu nu} B^{mu nu}          *)
(*    + (D_mu Phi)^dag (D^mu Phi) + mu^2 Phi^dag Phi - lam/4(Phi^dag Phi)^2 *)
(*    + i fbar_L gamma^mu D_mu f_L + i fbar_R gamma^mu D_mu f_R          *)
(*    - [fbar_L Y_f f_R Phi + h.c.]                                       *)
(*                                                                        *)
(*  Higgs doublet in the physical (mass-eigenstate) basis  (DD eq. 14):  *)
(*    Phi  = { phi^+,  (v + H + i chi)/Sqrt[2] }                         *)
(*    Phi^c = i sigma^2 Phi^* = { (v+H-i chi)/Sqrt[2], -phi^- }          *)
(*                                                                        *)
(*  Covariant derivative on a doublet with hypercharge Y_w  (DD eq. 3):  *)
(*    D_mu Phi = d_mu Phi - i g2 W^a_mu T^a Phi + i (g1 Y_w/2) B_mu Phi *)
(*                                                                        *)
(*  Field strengths  (DD eq. 2):                                          *)
(*    W^a_{mu nu} = d_mu W^a_nu - d_nu W^a_mu + g2 eps^{abc} W^b_mu W^c_nu *)
(*    B_{mu nu}   = d_mu B_nu - d_nu B_mu                                *)
(* ====================================================================== *)

(* ====================================================================== *)
(*  STEP 2 — EXPLICIT GAUGE-BASIS EXPRESSIONS                             *)
(* ====================================================================== *)

(* --- Higgs doublet directly in the physical basis  (DD eq. 14) --- *)
Phi  = {phi, (v + HH + I chi)/Sqrt[2]};
PhiC = I * sigma[2] . Conjugate[Phi];   (* = {(v+HH-I chi)/Sqrt[2], -phim} *)

(* --- SU(2) gauge-field matrix W_mu = (sigma^a/2) W^a_mu --- *)
Wmat[mu_] := (1/2) Sum[sigma[a] * W[GI[a], LI[mu]], {a, 1, 3}];

(* --- Covariant derivative on a doublet (left-handed)  (DD eq. 3) --- *)
covDdoublet[mu_, Yw_][psi_List] :=
  d[LI[mu]] /@ psi
  - I g2 * Wmat[mu] . psi
  + I g1 * (Yw/2) * B[LI[mu]] * psi;

(* --- Covariant derivative on a right-handed singlet --- *)
covDsinglet[mu_, Yw_][f_] :=
  d[LI[mu]][f] + I g1 * (Yw/2) * B[LI[mu]] * f;

(* --- SU(2) field strength W^a_{mu nu}  (DD eq. 2) --- *)
Wstr[GI[aa_], LI[mu_], LI[nu_]] :=
  d[LI[mu]][W[GI[aa], LI[nu]]] - d[LI[nu]][W[GI[aa], LI[mu]]]
  + g2 * Sum[eps3[aa, b, c] * W[GI[b], LI[mu]] * W[GI[c], LI[nu]], {b,1,3}, {c,1,3}];

(* --- U(1) field strength B_{mu nu} --- *)
Bstr[LI[mu_], LI[nu_]] :=
  d[LI[mu]][B[LI[nu]]] - d[LI[nu]][B[LI[mu]]];

(* ---- Gauge kinetic terms ---- *)
LgaugeSym =
  -(1/4) Bstr[LI[mu], LI[nu]] Bstr[LI[mu], LI[nu]]
  -(1/4) Sum[Wstr[GI[a], LI[mu], LI[nu]] Wstr[GI[a], LI[mu], LI[nu]], {a, 1, 3}];

(* ---- Higgs sector: kinetic + potential  (DD eq. 8) ---- *)
LHiggsKin[mu_] := With[
  {DPhi = covDdoublet[mu, 1][Phi]},
  Conjugate[DPhi] . DPhi
];

PhiDagPhi = Expand[Conjugate[Phi] . Phi];

LHiggsPot = Expand[mu2 * PhiDagPhi - (lam/4) * PhiDagPhi^2];

(* ---- Fermion kinetic terms  (DD eq. 8, hypercharges: DD eq. 7) ----
   L^L (nu,el): Y_w=-1,  Q^L (uq,dq): Y_w=+1/3
   el^R: Y_w=-2,  uq^R: Y_w=+4/3,  dq^R: Y_w=-2/3                     *)

LfermDoubletKin[f1_, f2_, Yw_] := Expand[
    I bar[f1] ** ga[LI[mu]] ** PL ** (covDdoublet[mu, Yw][{f1, f2}])[[1]]
  + I bar[f2] ** ga[LI[mu]] ** PL ** (covDdoublet[mu, Yw][{f1, f2}])[[2]]
];

LfermSingletKin[f_, Yw_] := Expand[
  I bar[f] ** ga[LI[mu]] ** PR ** covDsinglet[mu, Yw][f]
];

LfermLep = Sum[
  LfermDoubletKin[nu[FI[i]], el[FI[i]], -1]
+ LfermSingletKin[el[FI[i]], -2],
{i, 1, 3}];

LfermQuark = Sum[
  LfermDoubletKin[uq[FI[i]], dq[FI[i]], 1/3]
+ LfermSingletKin[uq[FI[i]], 4/3]
+ LfermSingletKin[dq[FI[i]], -2/3],
{i, 1, 3}];

LfermSym = LfermLep + LfermQuark;

(* ---- Yukawa terms  (DD eq. 8 last line, eq. 9) ---- *)
LYukSym = Expand[-Sum[
  yl[FI[i], FI[j]] * (
    bar[nu[FI[i]]] ** PR ** el[FI[j]] * Phi[[1]] +
    bar[el[FI[i]]] ** PR ** el[FI[j]] * Phi[[2]]) +
  Conjugate[yl[FI[i], FI[j]]] * (
    bar[el[FI[j]]] ** PL ** nu[FI[i]] * Conjugate[Phi[[1]]] +
    bar[el[FI[j]]] ** PL ** el[FI[i]] * Conjugate[Phi[[2]]]) +
  yu[FI[i], FI[j]] * (
    bar[uq[FI[i]]] ** PR ** uq[FI[j]] * PhiC[[1]] +
    bar[dq[FI[i]]] ** PR ** uq[FI[j]] * PhiC[[2]]) +
  Conjugate[yu[FI[i], FI[j]]] * (
    bar[uq[FI[j]]] ** PL ** uq[FI[i]] * Conjugate[PhiC[[1]]] +
    bar[uq[FI[j]]] ** PL ** dq[FI[i]] * Conjugate[PhiC[[2]]]) +
  yd[FI[i], FI[j]] * (
    bar[uq[FI[i]]] ** PR ** dq[FI[j]] * Phi[[1]] +
    bar[dq[FI[i]]] ** PR ** dq[FI[j]] * Phi[[2]]) +
  Conjugate[yd[FI[i], FI[j]]] * (
    bar[dq[FI[j]]] ** PL ** uq[FI[i]] * Conjugate[Phi[[1]]] +
    bar[dq[FI[j]]] ** PL ** dq[FI[i]] * Conjugate[Phi[[2]]]),
{i, 1, 3}, {j, 1, 3}]];

(* ---- Total classical Lagrangian in the gauge basis ---- *)
LclassSym = LgaugeSym + LHiggsPot + LfermSym + LYukSym;

(* ====================================================================== *)
(*  STEP 3 — PHYSICAL BASIS: GAUGE-FIELD ROTATION + PARAMETER SUBS       *)
(*                                                                        *)
(*  W^1 = (W^+ + W^-)/Sqrt[2],  W^2 = i(W^+ - W^-)/Sqrt[2]             *)
(*  W^3 = cw Z - sw A,          B   = sw Z + cw A                        *)
(*  cw = g2/Sqrt[g1^2+g2^2],   sw = g1/Sqrt[g1^2+g2^2],   e = g2 sw    *)
(*  v = 2 sw MW/e,  lam = e^2 MH^2/(8 sw^2 MW^2),  mu2 = MH^2/2        *)
(* ====================================================================== *)

gaugeFieldRotation = {
  W[GI[1], LI[mu_]] :> (Wp[LI[mu]] + Wm[LI[mu]]) / Sqrt[2],
  W[GI[2], LI[mu_]] :> I (Wp[LI[mu]] - Wm[LI[mu]]) / Sqrt[2],
  W[GI[3], LI[mu_]] :> cw Zb[LI[mu]] - sw AA[LI[mu]],
  B[LI[mu_]]        :> sw Zb[LI[mu]] + cw AA[LI[mu]]
};

paramSubs = {
  g2  -> ee / sw,
  g1  -> ee / cw,
  v   -> 2 sw MW / ee,
  lam -> ee^2 MH^2 / (8 sw^2 MW^2),
  mu2 -> MH^2 / 2
};

(* Diagonal Yukawa in mass-eigenstate basis: y^f_{ij} = Sqrt[2] mf_i/v delta_{ij} *)
yukawaSubs = Flatten[{
  Table[yl[FI[i], FI[j]] :>
    If[i == j, Sqrt[2] mf[el, FI[i]] * ee / (2 sw MW), 0], {i,1,3},{j,1,3}],
  Table[yu[FI[i], FI[j]] :>
    If[i == j, Sqrt[2] mf[uq, FI[i]] * ee / (2 sw MW), 0], {i,1,3},{j,1,3}],
  Table[yd[FI[i], FI[j]] :>
    If[i == j, Sqrt[2] mf[dq, FI[i]] * ee / (2 sw MW), 0], {i,1,3},{j,1,3}]
}];

toPhysical = Join[gaugeFieldRotation, paramSubs];

(* ====================================================================== *)
(*  STEP 4 — EW GAUGE TRANSFORMATIONS AND INVARIANCE CHECK                *)
(*                                                                        *)
(*  Physical-basis gauge parameters (one per mass-eigenstate gauge field):*)
(*    thA, thZ, thp (for W^+), thm (for W^-)                             *)
(*  Related to the SU(2)xU(1) parameters by the same rotation as the     *)
(*  gauge fields.                                                         *)
(*                                                                        *)
(*  Gauge transformations  (DD eqs. 17-19, rotated to physical basis):   *)
(*    delta W^+_mu = d_mu thp + i e(cw/sw thZ - thA) W^+_mu             *)
(*                  - i e(cw/sw Z_mu - A_mu) thp                         *)
(*    delta W^-_mu = (complex conjugate)                                  *)
(*    delta Z_mu   = d_mu thZ + i e cw/sw (W^-_mu thp - W^+_mu thm)     *)
(*    delta A_mu   = d_mu thA - i e (W^-_mu thp - W^+_mu thm)           *)
(*    delta phi^+ = i e [(cw^2-sw^2)/(2sw cw) thZ - thA] phi^+          *)
(*                 + i e/(2sw) thp (v+H+i chi)                           *)
(*    delta phi^- = (complex conjugate)                                   *)
(*    delta chi   = -e/(2sw cw) (v+H) thZ - e/(2sw)(phi^+ thm + phi^- thp) *)
(*    delta H     = e/(2sw cw) chi thZ - i e/(2sw)(phi^+ thm - phi^- thp) *)
(* ====================================================================== *)

DeclareGaugeParam /@ {thA, thZ, thp, thm};

(* Gauge transformation rules: F -> F + delta F (linear in gauge parameters) *)
gaugeTrafoRules = {
  Wp[LI[mu_]] :> Wp[LI[mu]]
    + d[LI[mu]][thp]
    + I ee (cw/sw thZ - thA) Wp[LI[mu]]
    - I ee (cw/sw Zb[LI[mu]] - AA[LI[mu]]) thp,

  Wm[LI[mu_]] :> Wm[LI[mu]]
    + d[LI[mu]][thm]
    - I ee (cw/sw thZ - thA) Wm[LI[mu]]
    + I ee (cw/sw Zb[LI[mu]] - AA[LI[mu]]) thm,

  Zb[LI[mu_]] :> Zb[LI[mu]]
    + d[LI[mu]][thZ]
    + I ee cw/sw (Wm[LI[mu]] thp - Wp[LI[mu]] thm),

  AA[LI[mu_]] :> AA[LI[mu]]
    + d[LI[mu]][thA]
    - I ee (Wm[LI[mu]] thp - Wp[LI[mu]] thm),

  phi  :> phi
    + I ee ((cw^2 - sw^2)/(2 sw cw) thZ - thA) phi
    + I ee/(2 sw) thp (v + HH + I chi),

  phim :> phim
    - I ee ((cw^2 - sw^2)/(2 sw cw) thZ - thA) phim
    - I ee/(2 sw) thm (v + HH - I chi),

  chi  :> chi
    - ee/(2 sw cw) (v + HH) thZ
    - ee/(2 sw) (phi thm + phim thp),

  HH   :> HH
    + ee/(2 sw cw) chi thZ
    - I ee/(2 sw) (phi thm - phim thp)
};

(* ---- Invariance check (evaluate after applying toPhysical) ----
   Extract O(theta) piece and verify it vanishes (up to total derivatives):
     deltaLclass = (LclassSym /. toPhysical /. gaugeTrafoRules)
                   - (LclassSym /. toPhysical)
   Should be zero modulo total derivatives and use of e.o.m.              *)

(* ====================================================================== *)
(*  STEP 5 — GAUGE FIXING AND FADDEEV-POPOV GHOST LAGRANGIAN             *)
(*                                                                        *)
(*  Rxi gauge-fixing conditions  (DD eqs. 27-28):                        *)
(*    C^A = d^mu A_mu                                                     *)
(*    C^Z = d^mu Z_mu - MZ xi_Z chi                                      *)
(*    C^+ = d^mu W^+_mu - i MW xi_W phi^+                                *)
(*    C^- = d^mu W^-_mu + i MW xi_W phi^-                                *)
(*  L_fix = -1/(2) (C^A)^2 - 1/2 (C^Z)^2 - C^+ C^-                     *)
(*                                                                        *)
(*  FP ghost Lagrangian:                                                  *)
(*    L_FP = -ubar^a (delta C^a / delta theta^b) u^b                     *)
(*  Derived automatically: compute delta C^a = C^a[F->F+deltaF] - C^a,   *)
(*  substitute theta^b -> u^b, multiply by -ubar^a.                      *)
(* ====================================================================== *)

(* ---- Gauge-fixing conditions ---- *)
CA[mu_]  := d[LI[mu]][AA[LI[mu]]];
CZ[mu_]  := d[LI[mu]][Zb[LI[mu]]] - MZ xiZ chi;
CWp[mu_] := d[LI[mu]][Wp[LI[mu]]] - I MW xiW phi;
CWm[mu_] := d[LI[mu]][Wm[LI[mu]]] + I MW xiW phim;

Lfix = Expand[
  -(1/2) CA[mu]  CA[mu]
  -(1/2) CZ[mu]  CZ[mu]
  -      CWp[mu] CWm[mu]
];

(* ---- Variations of gauge-fixing conditions under gauge transformations ---- *)
deltaCA[mu_]  := Expand[CA[mu]  /. gaugeTrafoRules] - CA[mu];
deltaCZ[mu_]  := Expand[CZ[mu]  /. gaugeTrafoRules] - CZ[mu];
deltaCWp[mu_] := Expand[CWp[mu] /. gaugeTrafoRules] - CWp[mu];
deltaCWm[mu_] := Expand[CWm[mu] /. gaugeTrafoRules] - CWm[mu];

(* ---- Substitute gauge parameters -> ghost fields and assemble L_FP ---- *)
toGhosts = {thA -> ua, thZ -> uz, thp -> up, thm -> um};

Lghost = Expand[
  - uba ** (deltaCA[mu]  /. toGhosts)
  - ubz ** (deltaCZ[mu]  /. toGhosts)
  - ubp ** (deltaCWp[mu] /. toGhosts)
  - ubm ** (deltaCWm[mu] /. toGhosts)
];

(* ====================================================================== *)
(*  STEP 6 — FEYNMAN RULES (tree level)                                   *)
(*                                                                        *)
(*  Total Lagrangian in the physical basis:                               *)
(*    Ltotal = (LclassSym /. toPhysical) + Lfix + Lghost                 *)
(*  Extract Feynman rules with feynmanRule[L, legs].                      *)
(*                                                                        *)
(*  Examples (evaluate as needed):                                        *)
(*    feynmanRule[LclassSym /. toPhysical, ...]                           *)
(* ====================================================================== *)

(* ====================================================================== *)
(*  RENORMALIZATION  (OS scheme, DD Sect. 3.1)                            *)
(* ====================================================================== *)

Scan[(# /: Conjugate[#] := #) &, {
  dZW, dZZZ, dZZA, dZAZ, dZAA, dZH,
  dZeL, dZeR, dZnuL, dZuL, dZuR, dZdL, dZdR,
  dZe, dMW2, dMZ2, dMH2
}];
Unprotect[MakeBoxes];
MakeBoxes[dZW,   StandardForm] := SubscriptBox["\[Delta]Z", "W"];
MakeBoxes[dZZZ,  StandardForm] := SubscriptBox["\[Delta]Z", "ZZ"];
MakeBoxes[dZZA,  StandardForm] := SubscriptBox["\[Delta]Z", "Z\[Gamma]"];
MakeBoxes[dZAZ,  StandardForm] := SubscriptBox["\[Delta]Z", "\[Gamma]Z"];
MakeBoxes[dZAA,  StandardForm] := SubscriptBox["\[Delta]Z", "\[Gamma]\[Gamma]"];
MakeBoxes[dZH,   StandardForm] := SubscriptBox["\[Delta]Z", "H"];
MakeBoxes[dZe,   StandardForm] := SubscriptBox["\[Delta]Z", "e"];
MakeBoxes[dMW2,  StandardForm] := SuperscriptBox[SubscriptBox["\[Delta]M", "W"], "2"];
MakeBoxes[dMZ2,  StandardForm] := SuperscriptBox[SubscriptBox["\[Delta]M", "Z"], "2"];
MakeBoxes[dMH2,  StandardForm] := SuperscriptBox[SubscriptBox["\[Delta]M", "H"], "2"];
Protect[MakeBoxes];
renormFields = Flatten[{
  renormBoson[Wp,   dZW],
  renormBoson[Wm,   dZW],
  renormMix[Zb, AA, dZZZ, dZZA, dZAZ, dZAA],
  renormBoson[HH,   dZH],
  renormBoson[phi,  dZW],
  renormBoson[phim, dZW],
  renormBoson[chi,  dZZZ],
  Table[renorm[nu[FI[i]], dZnuL/2, 0     ], {i,1,3}],
  Table[renorm[el[FI[i]], dZeL/2,  dZeR/2], {i,1,3}],
  Table[renorm[uq[FI[i]], dZuL/2,  dZuR/2], {i,1,3}],
  Table[renorm[dq[FI[i]], dZdL/2,  dZdR/2], {i,1,3}]
}];

renormParams = {
  ee   -> (1 + dZe) ee,
  sw   -> sw (1 - (cw^2/(2 sw^2)) (dMW2/MW^2 - dMZ2/MZ^2)),
  cw   -> cw (1 + (1/2)           (dMW2/MW^2 - dMZ2/MZ^2)),
  MW^2 -> MW^2 + dMW2,
  MZ^2 -> MZ^2 + dMZ2,
  MH^2 -> MH^2 + dMH2
};
