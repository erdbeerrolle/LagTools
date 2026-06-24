(* ::Package:: *)
Get[FileNameJoin[{DirectoryName[$InputFileName], "LagTools.wl"}]];

(* ====================================================================== *)
(*  FIELDS                                                                *)
(* ====================================================================== *)

(* gauge bosons in the gauge basis *)
DeclareRealBoson[W, "W"];    (*SU(2)*)
DeclareRealBoson[B, "B"];    (*U(1)*)

(* gauge bosons in physical basis *)
DeclareRealBoson[AA, "A"];
DeclareRealBoson[Zb, "Z"];
DeclareComplexBoson[Wp, Wm, "W"];

(* higgs sector *)
DeclareRealBoson[HH, "H"];
DeclareRealBoson[chi, "\[Chi]"];
DeclareComplexBoson[phi, phim, "\[Phi]"];
(* higgs doublet *)
DeclareGaugeDoublet[Phi, "\[CapitalPhi]",
  Phi :> {phi, (v + HH + I*chi)/Sqrt[2]}];

(* Dirac fermions *)
DeclareFermion[nu, "\[Nu]"];
DeclareFermion[el, "l"];
DeclareFermion[uq, "u"];
DeclareFermion[dq, "d"];

(* fermion Doublets and Singlets *)
DeclareGaugeDoublet[LeptL, Subscript["L", "L"],
  LeptL[FI[a_]] :> {PL**nu[FI[a]], PL**el[FI[a]]}];
DeclareGaugeDoublet[QuarkL, Subscript["Q", "L"],
  QuarkL[FI[a_]] :> {PL**uq[FI[a]], PL**dq[FI[a]]}];
DeclareGaugeSinglet[LeptR, Subscript["l", "R"],
  LeptR[FI[a_]] :> PR**el[FI[a]]];
DeclareGaugeSinglet[UpR, Subscript["u", "R"],
  UpR[FI[a_]] :> PR**uq[FI[a]]];
DeclareGaugeSinglet[DownR, Subscript["d", "R"],
  DownR[FI[a_]] :> PR**dq[FI[a]]];

(*---Faddeev-Popov ghosts in the physical basis---*)
DeclareGrassmann[up, Superscript["u", "+"]];
DeclareGrassmann[um, Superscript["u", "-"]];
DeclareGrassmann[uz, Superscript["u", "Z"]];
DeclareGrassmann[ua, Superscript["u", "A"]];
DeclareGrassmann[ubp, Superscript[OverBar["u"], "+"]];
DeclareGrassmann[ubm, Superscript[OverBar["u"], "-"]];
DeclareGrassmann[ubz, Superscript[OverBar["u"], "Z"]];
DeclareGrassmann[uba, Superscript[OverBar["u"], "A"]];


(* ====================================================================== *)
(* PARAMETERS                                                             *)
(* ====================================================================== *)

(*Real gauge-basis parameters*)
DeclareRealParam[g1, Subscript["g", "1"]];
DeclareRealParam[g2, Subscript["g", "2"]];
DeclareRealParam[mu2, Superscript["\[Mu]", "2"]];
DeclareRealParam[lam, "\[Lambda]"];
DeclareRealParam[v, "v"];

(*Real physical parameters*)
DeclareRealParam[ee, Subscript["e", "EM"]];
DeclareRealParam[sw, Subscript["s", "w"]];
DeclareRealParam[cw, Subscript["c", "w"]];
DeclareRealParam[MW, Subscript["M", "W"]];
DeclareRealParam[MZ, Subscript["M", "Z"]];
DeclareRealParam[MH, Subscript["M", "H"]];
DeclareRealParam[xiW, Subscript["\[Xi]", "W"]];
DeclareRealParam[xiZ, Subscript["\[Xi]", "Z"]];

DeclareRealParam[ml, Subscript["m", "l"]];
DeclareRealParam[mu, Subscript["m", "u"]];
DeclareRealParam[md, Subscript["m", "d"]];
DeclareRealParam[yl, Superscript["Y", "(l)"]];
DeclareRealParam[yu, Superscript["Y", "(u)"]];
DeclareRealParam[yd, Superscript["Y", "(d)"]];

(* ====================================================================== *)
(* COVARIANT DERIVATIVE AND FIELD STRENGHTS                               *)
(* ====================================================================== *)

(* gauge-covariant derivative for EW gauge symmetry *)
DeclareCovD[CovD, "D", 
  CovD[mu_][f_] :> 
   INS[d[mu][f] - I*g2*W[GI[i[1]], mu]*SU2T[GI[i[1]]][f] + I*g1*B[mu]*U1Y[f]]];

(* Field strength tensor for W^a *)
(* dynamic indices and index name space to avoid accidental doubled indices *)
DeclareFieldStr[WFieldStr, "W", 
  WFieldStr[GI[i[c_]], LI[a_], LI[b_]] :> 
   INS[d[LI[a]][W[GI[i[c]], LI[b]]] - d[LI[b]][W[GI[i[c]], LI[a]]] + 
     I*g2*eps3[GI[i[c]], GI[i[c + 1]], GI[i[c + 2]]]*
      W[GI[i[c + 1]], LI[a]]*W[GI[i[c + 2]], LI[b]]]];

(* Field strength tensor for B *)
DeclareFieldStr[BFieldStr, "B", 
  BFieldStr[LI[a_], LI[b_]] :> d[LI[a]][B[LI[b]]] - d[LI[b]][B[LI[a]]]];

(* ====================================================================== *)
(* CLASSICAL LAGRANGIAN                                                   *)
(* ====================================================================== *)

(* fermion kinetic *)
LFermPart[f_] := 
  I* bar[f[FI[i[1]]]] ** ga[LI[i[1]]] ** CovD[LI[i[1]]][f[FI[i[1]]]];

LFerm = Total[LFermPart /@ {LeptL, LeptR, QuarkL, UpR, DownR}];

(* gauge kinetic *)
LGauge = -(1/4)*BFieldStr[LI[i[1]], LI[i[2]]]*
   BFieldStr[LI[i[1]], LI[i[2]]] - (1/4)*
   WFieldStr[GI[i[1]], LI[i[1]], LI[i[2]]]*
   WFieldStr[GI[i[1]], LI[i[1]], LI[i[2]]];
   
(* higgs sector *)
LHiggs = 
 Expand[With[{DPhi = CovD[LI[i[1]]][Phi]}, 
    ConjugateTranspose[DPhi] . DPhi] + 
   mu2*ConjugateTranspose[Phi] . 
     Phi - (lam/4)*(ConjugateTranspose[Phi] . Phi)^2];

(* yukawa *)
LYukawaLept = -yl[FI[i[1]], 
     FI[i[2]]] (bar[LeptL[FI[i[1]]]] ** LeptR[FI[i[2]]]) . Phi;
LYukawaUp     = -yu[FI[i[1]], 
     FI[i[2]]] (bar[QuarkL[FI[i[1]]]] ** UpR[FI[i[2]]]) . 
    ChargeConj[Phi];
LYukawaDown = -yd[FI[i[1]], 
     FI[i[2]]] (bar[QuarkL[FI[i[1]]]] ** DownR[FI[i[2]]]) . Phi;

LYukawa = (LYukawaLept + LYukawaUp + LYukawaDown) + 
  ConjugateTranspose[(LYukawaLept + LYukawaUp + LYukawaDown)];


(* full classical lagrangian *)
LClass = LFerm + LGauge + LHiggs + LYukawa

(* ====================================================================== *)
(* PHYSICAL BASIS: GAUGE-FIELD ROTATION + PARAMETER SUBSTITUTION          *)
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

(* Diagonal Yukawa in mass-eigenstate basis *)
diagMassMatSubs[y_,m_] := Flatten[Table[
  y[FI[i], FI[j]] :> If[i == j, Sqrt[2] m[FI[i]]*ee/(2 sw MW), 0], {i, 1, 3}, {j, 1, 3}]]

toPhysical = Join[gaugeFieldRotation, paramSubs, diagMassMatSubs[yl,ml],diagMassMatSubs[yu,mu],diagMassMatSubs[yd,md]];

(* ====================================================================== *)
(* GAUGE TRANSFORMATIONS                                                  *)
(* ====================================================================== *)

(*DeclareGaugeParam /@ {thA, thZ, thp, thm};*)

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
  -(1/2) CA[i[1]]  CA[i[1]]
  -(1/2) CZ[i[1]]  CZ[i[1]]
  -      CWp[i[1]] CWm[i[1]]
];

(* ---- Variations of gauge-fixing conditions under gauge transformations ---- *)
deltaCA[mu_]  := Expand[CA[mu]  /. gaugeTrafoRules] - CA[mu];
deltaCZ[mu_]  := Expand[CZ[mu]  /. gaugeTrafoRules] - CZ[mu];
deltaCWp[mu_] := Expand[CWp[mu] /. gaugeTrafoRules] - CWp[mu];
deltaCWm[mu_] := Expand[CWm[mu] /. gaugeTrafoRules] - CWm[mu];

(* ---- Substitute gauge parameters -> ghost fields and assemble L_FP ---- *)
toGhosts = {thA -> ua, thZ -> uz, thp -> up, thm -> um};

Lghost = Expand[
  - uba ** (deltaCA[i[1]]  /. toGhosts)
  - ubz ** (deltaCZ[i[1]]  /. toGhosts)
  - ubp ** (deltaCWp[i[1]] /. toGhosts)
  - ubm ** (deltaCWm[i[1]] /. toGhosts)
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
