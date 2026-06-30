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
DeclareRealParam[cw, Subscript["c", "w"]];
DeclareRealParam[MW, Subscript["M", "W"]];
DeclareRealParam[MZ, Subscript["M", "Z"]];
DeclareRealParam[MH, Subscript["M", "H"]];
DeclareRealParam[xiW, Subscript["\[Xi]", "W"]];
DeclareRealParam[xiZ, Subscript["\[Xi]", "Z"]];
DeclareRealParam[xiA, Subscript["\[Xi]", "A"]];

(* sw^2 = 1-cw^2 as shorthand without having to do transformations between the two *)
sw = Sqrt[1 - cw^2];
$Assumptions = {cw \[Element] Reals, cw > 0, cw < 1};

Unprotect[MakeBoxes];
MakeBoxes[Sqrt[1 - cw^2],  StandardForm] := SubscriptBox["s", "w"];
MakeBoxes[1 - cw^2,        StandardForm] := SuperscriptBox[SubscriptBox["s", "w"], "2"];
Protect[MakeBoxes];

DeclareRealParam[ml, Subscript["m", "l"]];
DeclareRealParam[mu, Subscript["m", "u"]];
DeclareRealParam[md, Subscript["m", "d"]];
DeclareComplexParam[yl, Superscript["Y", "(l)"]];
DeclareComplexParam[yu, Superscript["Y", "(u)"]];
DeclareComplexParam[yd, Superscript["Y", "(d)"]];

(* CKM matrix *)
DeclareComplexParam[V,"V"]

(* ====================================================================== *)
(* COVARIANT DERIVATIVE AND FIELD STRENGHTS                               *)
(* ====================================================================== *)

(* gauge-covariant derivative for EW gauge symmetry -- assumption: argument of cov d has no indices conflicting with defnition of covd *)
DeclareCovD[CovD, "D", 
  CovD[mu_][f_]:>
   INS[d[mu][f] - I*g2*W[GI[i[1]], mu]*SU2T[GI[i[1]]][f] + I/2*g1*B[mu]*U1Y[f]]];

(* Field strength tensor for W^a *)
(* dynamic indices and index name space to avoid accidental doubled indices *)
DeclareFieldStr[WFieldStr, "W", 
  INSRule[WFieldStr[GI[i[c_]], LI[a_], LI[b_]],
   d[LI[a]][W[GI[i[c]], LI[b]]] - d[LI[b]][W[GI[i[c]], LI[a]]] + 
     g2*eps3[GI[i[c]], GI[i[1]], GI[i[2]]]*
      W[GI[i[1]], LI[a]]*W[GI[i[2]], LI[b]]]];

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


LFermFull = LFerm // ExplCovD // GISum // ExplGaugeMult // diracSimplify // Expand;
LGaugeFull = LGauge // ExplFieldStr // GISum // canonical;
LHiggsFull = LHiggs // ExplCovD // ExplGaugeMult // GISum // Expand;
LYukawaFull = LYukawa // ExplGaugeMult // Expand // diracSimplify;


LClassFull = LFermFull + LGaugeFull + LHiggsFull + LYukawaFull;


(* ====================================================================== *)
(* PHYSICAL BASIS (MASS EIGENSTATES)                                      *)
(* ====================================================================== *)

(*  ---- Part I: Gauge-field rotation ----  *)
gaugeFieldRotation = {
  W[GI[1], LI[mu_]] :> (Wp[LI[mu]] + Wm[LI[mu]]) / Sqrt[2],
  W[GI[2], LI[mu_]] :> I (Wp[LI[mu]] - Wm[LI[mu]]) / Sqrt[2],
  W[GI[3], LI[mu_]] :> cw Zb[LI[mu]] - sw AA[LI[mu]],
  B[LI[mu_]]        :> sw Zb[LI[mu]] + cw AA[LI[mu]]
};

paramSubs = {
  g2  -> ee / sw,
  g1  -> ee / cw,
  v   -> 2 sw MW / ee, (* v = 2 MW / g2 *)
  lam -> ee^2 MH^2 / (2 sw^2 MW^2), (* lam = 2 MH^2 /v^2 *)
  mu2 -> MH^2 / 2
};

GaugeBasisChange[e_] := e //. Join[gaugeFieldRotation, paramSubs];

(*  ---- Part II: Fermion mass basis  ----  *)

(* Components of unitary basis trafo matrices *)
DeclareComplexParam[Ul, Superscript["U", "(l)"]];
DeclareComplexParam[Ud, Superscript["U", "(d)"]];
DeclareComplexParam[Uu, Superscript["U", "(u)"]];
(* diagonal mass matrices *)
DeclareRealParam[Mdiagl, Superscript["M", "(l)"]];
DeclareRealParam[Mdiagd, Superscript["M", "(d)"]];
DeclareRealParam[Mdiagu, Superscript["M", "(u)"]];

MassMatSub[e_] := e //.{
  yl[FI[a_], FI[b_]] :> Mdiagl[FI[a], FI[b]]*Sqrt[2] * ee/(2 sw MW),
  yu[FI[a_], FI[b_]] :> Mdiagu[FI[a], FI[b]]*Sqrt[2] * ee/(2 sw MW),
  yd[FI[a_], FI[b_]] :> Mdiagd[FI[a], FI[b]]*Sqrt[2] * ee/(2 sw MW)
};

ExplMassMat[e_] := e //. {
  Mdiagl[FI[a_], FI[b_]] :> kd3[FI[a], FI[b]]* ml[FI[a]],
  Mdiagu[FI[a_], FI[b_]] :> kd3[FI[a], FI[b]]* mu[FI[a]],
  Mdiagd[FI[a_], FI[b_]] :> kd3[FI[a], FI[b]]* md[FI[a]]
};

SetAttributes[Mdiagl,Orderless];
SetAttributes[Mdiagu,Orderless];
SetAttributes[Mdiagd,Orderless];

basisChangeFields = {
   INSRule[dq[FI[i[c_]]], dq[FI[i[1]]]*Conjugate[Ud[FI[i[1]], FI[i[c]]]]],
   INSRule[uq[FI[i[c_]]], uq[FI[i[1]]]*Conjugate[Uu[FI[i[1]], FI[i[c]]]]],
   INSRule[el[FI[i[c_]]], el[FI[i[1]]]*Conjugate[Ul[FI[i[1]], FI[i[c]]]]],
   INSRule[nu[FI[i[c_]]], nu[FI[i[1]]]*Conjugate[Ul[FI[i[1]], FI[i[c]]]]]};

diagMassMatSubs[y_, u_] := 
  INSRule[y[FI[i[a_]], FI[i[b_]]], 
   y[FI[i[1]], FI[i[2]]]*u[FI[i[2]], FI[i[b]]]*
    Conjugate[u[FI[i[1]], FI[i[a]]]]];

basisChangeYukawaMat = {
  diagMassMatSubs[yl, Ul], 
  diagMassMatSubs[yu, Uu], 
  diagMassMatSubs[yd, Ud]
};

unitarity = {
   (* Unitarity Uu *)
   Times[r1___, Uu[FI[a_], FI[b_]], r2___, Conjugate[Uu[FI[a_], FI[c_]]],
      r3___] :> kd3[FI[b], FI[c]] Times[r1, r2, r3], 
   Times[r1___, Uu[FI[a_], FI[b_]], r2___, Conjugate[Uu[FI[c_], FI[b_]]],
      r3___] :> kd3[FI[a], FI[c]] Times[r1, r2, r3],
   (* Unitarity: Ud *)
   Times[r1___, Ud[FI[a_], FI[b_]], r2___, Conjugate[Ud[FI[a_], FI[c_]]],
      r3___] :> kd3[FI[b], FI[c]] Times[r1, r2, r3], 
   Times[r1___, Ud[FI[a_], FI[b_]], r2___, Conjugate[Ud[FI[c_], FI[b_]]],
      r3___] :> kd3[FI[a], FI[c]] Times[r1, r2, r3],
   (* Unitarity: Ul *)
   Times[r1___, Ul[FI[a_], FI[b_]], r2___, Conjugate[Ul[FI[a_], FI[c_]]],
      r3___] :> kd3[FI[b], FI[c]] Times[r1, r2, r3], 
   Times[r1___, Ul[FI[a_], FI[b_]], r2___, Conjugate[Ul[FI[c_], FI[b_]]],
      r3___] :> kd3[FI[a], FI[c]] Times[r1, r2, r3]
  };

ckmdef = {
   (* CKM: Uu.Ud^dagger *)
   Times[r1___, Uu[FI[a_], FI[b_]], r2___, Conjugate[Ud[FI[c_], FI[b_]]],
      r3___] :> V[FI[a], FI[c]] Times[r1, r2, r3],
   (* Ud.Uu^dagger *)
   Times[r1___, Conjugate[Uu[FI[a_], FI[b_]]], r2___, 
     Ud[FI[c_], FI[b_]], r3___] :> 
    Conjugate[V[FI[a], FI[c]]] Times[r1, r2, r3]
  };

FermionBasisChange[e_] := ((e /. Join[basisChangeFields, basisChangeYukawaMat]) //. Join[unitarity, ckmdef]) // contract // MassMatSub;

(*  ---- full basis transformation    ----  *)

toPhysical[e_] := e // FermionBasisChange // GaugeBasisChange;

(* ====================================================================== *)
(* GAUGE TRANSFORMATIONS                                                  *)
(* ====================================================================== *)

(* space-time-dependent gauge parameters (STindepQ = False, so they survive
   derivatives in the gauge-fixing / FP-ghost derivation below) *)
DeclareLocalGaugeParam[thA, Superscript["\[Theta]", "A"]];
DeclareLocalGaugeParam[thZ, Superscript["\[Theta]", "Z"]];
DeclareLocalGaugeParam[thp, Superscript["\[Theta]", "+"]];
DeclareLocalGaugeParam[thm, Superscript["\[Theta]", "-"]];

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
(*  STEP 5 — GAUGE FIXING AND FADDEEV-POPOV GHOST LAGRANGIAN              *)
(* ====================================================================== *)

(* ---- Gauge-fixing conditions ---- *)
CA[mu_]  := d[LI[mu]][AA[LI[mu]]];
CZ[mu_]  := d[LI[mu]][Zb[LI[mu]]] - MZ xiZ chi;
CWp[mu_] := d[LI[mu]][Wp[LI[mu]]] - I MW xiW phi;
CWm[mu_] := d[LI[mu]][Wm[LI[mu]]] + I MW xiW phim;

Lfix = Expand[ (* could also use INS here ... *)
  - 1/(2 * xiA) CA[i[1]]  CA[i[2]]
  - 1/(2 * xiZ) CZ[i[1]]  CZ[i[2]]
  - 1/xiW *     CWp[i[1]] CWm[i[2]]
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
] /. paramSubs; (* replace v *)

(* ====================================================================== *)
(*  STEP 6 — total lagrangian                                            *)
(* ====================================================================== *)

Ltotal = (LClassFull // toPhysical // Expand // canonical // 
   RemoveINS) + Lghost + Lfix;

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
  renormBoson[Wp,   alpha dZW],
  renormBoson[Wm,   alpha dZW],
  renormMix[Zb, AA, alpha dZZZ, alpha dZZA, alpha dZAZ, alpha dZAA],
  renormBoson[HH,   alpha dZH],
  renormBoson[phi,  alpha dZW],
  renormBoson[phim, alpha dZW],
  renormBoson[chi,  alpha dZZZ],
  Table[renorm[nu[FI[i]], alpha dZnuL/2, 0     ], {i,1,3}],
  Table[renorm[el[FI[i]], alpha dZeL/2,  alpha dZeR/2], {i,1,3}],
  Table[renorm[uq[FI[i]], alpha dZuL/2,  alpha dZuR/2], {i,1,3}],
  Table[renorm[dq[FI[i]], alpha dZdL/2,  alpha dZdR/2], {i,1,3}]
}];

renormParams = {
  ee   -> (1 + alpha dZe) ee,
  sw   -> sw (1 - (cw^2/(2 sw^2)) alpha (dMW2/MW^2 - dMZ2/MZ^2)),
  cw   -> cw (1 + (1/2)           alpha (dMW2/MW^2 - dMZ2/MZ^2)),
  MW^2 -> MW^2 + alpha dMW2,
  MZ^2 -> MZ^2 + alpha dMZ2,
  MH^2 -> MH^2 + alpha dMH2
};
