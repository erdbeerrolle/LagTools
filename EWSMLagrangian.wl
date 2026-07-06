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
(* substitute mu2 and lam for tadpole constant and higgs mass             *)
(* ====================================================================== *)
DeclareRealParam[tpc, "t"]; (* tadpole constant *)

lamMuSubs = Solve[
   {GetTerm[LHiggsFull, HH^2] == -1/2 MH^2 HH^2,
    GetTerm[LHiggsFull, HH]   == tpc HH},
   {lam, mu2}][[1]] // Expand;

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
  v   -> 2 sw MW / ee (* v = 2 MW / g2 *)
};

GaugeBasisChange[e_] := (e //. lamMuSubs) //. Join[gaugeFieldRotation, paramSubs];

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

(* simplification of summands is needed to simplify stuff like Conjugate[1/Sqrt[1-cw^2]]*)
LClassPhys = Simplify/@(LClassFull // toPhysical // Expand // canonical // 
   RemoveINS);
Ltotal = LClassPhys + Lghost + Lfix;


(* ====================================================================== *)
(*  Tadpole renormalization                                               *)
(* ====================================================================== *)
(* ordering parameter for 1-loop expansion *)
DeclareRealParam[alpha, "\[Alpha]"];

DeclareRealParam[dtFJ, Superscript["\[Delta]t", "FJTS"]];
DeclareRealParam[dtPR, Superscript["\[Delta]t", "PRTS"]];

FJTSsubs = {HH :> HH - alpha * dtFJ / MH^2};
PRTSsubs = {tpc :> alpha * dtPR};

(* ====================================================================== *)
(*  RENORMALIZATION TRAFO (OS scheme, DD Sect. 3.1)                       *)
(* ====================================================================== *)

DeclareRealParam[dZW, Subscript["\[Delta]Z", "W"]];
DeclareRealParam[dZZZ, Subscript["\[Delta]Z", "ZZ"]];
DeclareRealParam[dZZA, Subscript["\[Delta]Z", "Z\[Gamma]"]];
DeclareRealParam[dZAZ, Subscript["\[Delta]Z", "\[Gamma]Z"]];
DeclareRealParam[dZAA, Subscript["\[Delta]Z", "\[Gamma]\[Gamma]"]];
DeclareRealParam[dZH, Subscript["\[Delta]Z", "H"]];
DeclareRealParam[dZe, Subscript["\[Delta]Z", "e"]];
DeclareRealParam[dMW2, Subsuperscript["\[Delta]M", "W", "2"]];
DeclareRealParam[dMZ2, Subsuperscript["\[Delta]M", "Z", "2"]];
DeclareRealParam[dMH2, Subsuperscript["\[Delta]M", "H", "2"]];
DeclareRealParam[dMdiagl, Subsuperscript["\[Delta]M", "l", "2"]];
DeclareRealParam[dMdiagu, Subsuperscript["\[Delta]M", "u", "2"]];
DeclareRealParam[dMdiagd, Subsuperscript["\[Delta]M", "d", "2"]];
DeclareComplexParam[dZeL, Subsuperscript["\[Delta]Z", "e", "L"]];
DeclareComplexParam[dZeR, Subsuperscript["\[Delta]Z", "e", "R"]];
DeclareComplexParam[dZuL, Subsuperscript["\[Delta]Z", "u", "L"]];
DeclareComplexParam[dZuR, Subsuperscript["\[Delta]Z", "u", "R"]];
DeclareComplexParam[dZdL, Subsuperscript["\[Delta]Z", "d", "L"]];
DeclareComplexParam[dZdR, Subsuperscript["\[Delta]Z", "d", "R"]];
DeclareComplexParam[dZnuL, Subsuperscript["\[Delta]Z", "\[Nu]", "L"]];
DeclareComplexParam[dZnuR, Subsuperscript["\[Delta]Z", "\[Nu]", "R"]];
DeclareComplexParam[dV, "\[Delta]V"];

SetAttributes[dMdiagl, Orderless];
SetAttributes[dMdiagu, Orderless];
SetAttributes[dMdiagd, Orderless];

renormFields = Flatten[{
  renormBoson[Wp,   alpha dZW],
  renormBoson[Wm,   alpha dZW],
  renormMix[Zb, AA, alpha dZZZ, alpha dZZA, alpha dZAZ, alpha dZAA],
  renormBoson[HH,   alpha dZH],
  renormFlavor[nu, (alpha dZnuL[#1,#2]/2)&, (0 &)                  ],
  renormFlavor[el, (alpha dZeL[#1,#2]/2)&,  (alpha dZeR[#1,#2]/2)& ],
  renormFlavor[uq, (alpha dZuL[#1,#2]/2)&,  (alpha dZuR[#1,#2]/2)& ],
  renormFlavor[dq, (alpha dZdL[#1,#2]/2)&,  (alpha dZdR[#1,#2]/2)& ]
}];

renormParams = {
  ee   -> (1 + alpha dZe) ee,
  (*sw   -> sw (1 - (cw^2/(2 sw^2)) alpha (dMW2/MW^2 - dMZ2/MZ^2)),*)
  cw   -> cw (1 + (1/2) alpha (dMW2/MW^2 - dMZ2/MZ^2)),
  MW -> MW + alpha dMW2 / (2 MW),
  MZ -> MZ + alpha dMZ2 / (2 MZ),
  MH -> MH + alpha dMH2 / (2 MH),
  Mdiagl[FI[a_], FI[b_]] :> Mdiagl[FI[a], FI[b]] + alpha dMdiagl[FI[a], FI[b]],
  Mdiagu[FI[a_], FI[b_]] :> Mdiagu[FI[a], FI[b]] + alpha dMdiagu[FI[a], FI[b]],
  Mdiagd[FI[a_], FI[b_]] :> Mdiagd[FI[a], FI[b]] + alpha dMdiagd[FI[a], FI[b]],
  V[FI[a_], FI[b_]] :> V[FI[a], FI[b]] + alpha dV[FI[a], FI[b]]
};


(* ======================================================================== *)
(*  1-LOOP RENORMALIZED LAGRANGIAN                                          *)
(* ======================================================================== *)

(* perform renormalizatin with Hold around sums of renormalization constants *)
renTermHold[e_] := Module[{sub, ren, a},
   sub = (e /. Join[FJTSsubs, PRTSsubs]) /. Join[renormFields, renormParams];
   ren = Series[sub, {alpha, 0, 1}] // Normal;
   HoldFieldPrefacts @ ren];

renormalize[e_] := diracSimplify @ HoldFieldPrefacts @ Total @ (renTermHold /@ SumToList[e]);

(* full 1-loop ren lag *)
Lren = renormalize @ LClassPhys + Lghost + Lfix