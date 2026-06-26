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

(* sw^2 = 1-cw^2 as shorthand without having to do transformations between the two *)
sw = Sqrt[1 - cw^2];

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
     I*g2*eps3[GI[i[c]], GI[i[1]], GI[i[2]]]*
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
  v   -> 2 sw MW / ee,
  lam -> ee^2 MH^2 / (8 sw^2 MW^2),
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
(*  STEP 6 — FEYNMAN RULES (all EWSM tree-level vertices)                 *)
(*                                                                        *)
(*  feynmanRules["key"] = i * d^n S / d phi_1 ... d phi_n  in p-space.  *)
(*  Momenta p1,p2,... flow INTO the vertex; i[n] are the Lorentz /       *)
(*  flavor indices of the respective leg.                                 *)
(*                                                                        *)
(*  Usage in a notebook:                                                  *)
(*    Get["path/to/EWSMLagrangian.wl"]                                    *)
(*    feynmanRules["A-Wp-Wm"]    (*  AWW vertex  *)                      *)
(*    Keys[feynmanRules]          (*  list all computed vertices  *)       *)
(* ====================================================================== *)

Ltotal = (LClassFull // toPhysical // Expand // canonical // 
   RemoveINS) + Lghost + Lfix;

feynmanRules = <||>;

(* ---- 2-point: gauge bosons ------------------------------------------ *)
feynmanRules["AA-AA"]    = feynmanRule[Ltotal, {{AA,  LI[i[1]], p1}, {AA,  LI[i[2]], p2}}];
feynmanRules["Zb-Zb"]    = feynmanRule[Ltotal, {{Zb,  LI[i[1]], p1}, {Zb,  LI[i[2]], p2}}];
feynmanRules["Wp-Wm"]    = feynmanRule[Ltotal, {{Wp,  LI[i[1]], p1}, {Wm,  LI[i[2]], p2}}];

(* ---- 2-point: scalars ------------------------------------------------ *)
feynmanRules["HH-HH"]    = feynmanRule[Ltotal, {{HH,  None, p1}, {HH,  None, p2}}];
feynmanRules["chi-chi"]  = feynmanRule[Ltotal, {{chi, None, p1}, {chi, None, p2}}];
feynmanRules["phi-phim"] = feynmanRule[Ltotal, {{phi, None, p1}, {phim,None, p2}}];

(* ---- 2-point: fermions (flavor indices i[2],i[3] appear in result) --- *)
feynmanRules["el-bar"]   = feynmanRule[Ltotal, {{bar[el], FI[i[2]], p1}, {el, FI[i[3]], p2}}];
feynmanRules["nu-bar"]   = feynmanRule[Ltotal, {{bar[nu], FI[i[2]], p1}, {nu, FI[i[3]], p2}}];
feynmanRules["uq-bar"]   = feynmanRule[Ltotal, {{bar[uq], FI[i[2]], p1}, {uq, FI[i[3]], p2}}];
feynmanRules["dq-bar"]   = feynmanRule[Ltotal, {{bar[dq], FI[i[2]], p1}, {dq, FI[i[3]], p2}}];

(* ---- 2-point: ghosts ------------------------------------------------- *)
feynmanRules["uba-ua"]   = feynmanRule[Ltotal, {{uba, None, p1}, {ua,  None, p2}}];
feynmanRules["ubz-uz"]   = feynmanRule[Ltotal, {{ubz, None, p1}, {uz,  None, p2}}];
feynmanRules["ubp-up"]   = feynmanRule[Ltotal, {{ubp, None, p1}, {up,  None, p2}}];
feynmanRules["ubm-um"]   = feynmanRule[Ltotal, {{ubm, None, p1}, {um,  None, p2}}];

(* ---- 3-point: triple gauge ------------------------------------------- *)
feynmanRules["A-Wp-Wm"]  = feynmanRule[Ltotal, {{AA,  LI[i[1]], p1}, {Wp, LI[i[2]], p2}, {Wm, LI[i[3]], p3}}];
feynmanRules["Z-Wp-Wm"]  = feynmanRule[Ltotal, {{Zb,  LI[i[1]], p1}, {Wp, LI[i[2]], p2}, {Wm, LI[i[3]], p3}}];

(* ---- 3-point: Higgs – massive gauge ---------------------------------- *)
feynmanRules["H-Wp-Wm"]  = feynmanRule[Ltotal, {{HH,  None, p1}, {Wp, LI[i[1]], p2}, {Wm, LI[i[2]], p3}}];
feynmanRules["H-Z-Z"]    = feynmanRule[Ltotal, {{HH,  None, p1}, {Zb, LI[i[1]], p2}, {Zb, LI[i[2]], p3}}];
feynmanRules["H-A-Z"]    = feynmanRule[Ltotal, {{HH,  None, p1}, {AA, LI[i[1]], p2}, {Zb, LI[i[2]], p3}}];

(* ---- 3-point: Goldstone – gauge -------------------------------------- *)
feynmanRules["chi-Z-H"]     = feynmanRule[Ltotal, {{chi,  None,      p1}, {Zb, LI[i[1]], p2}, {HH,  None,       p3}}];
feynmanRules["phi-A-Wm"]    = feynmanRule[Ltotal, {{phi,  None,      p1}, {AA, LI[i[1]], p2}, {Wm,  LI[i[2]],   p3}}];
feynmanRules["phi-Z-Wm"]    = feynmanRule[Ltotal, {{phi,  None,      p1}, {Zb, LI[i[1]], p2}, {Wm,  LI[i[2]],   p3}}];
feynmanRules["phim-A-Wp"]   = feynmanRule[Ltotal, {{phim, None,      p1}, {AA, LI[i[1]], p2}, {Wp,  LI[i[2]],   p3}}];
feynmanRules["phim-Z-Wp"]   = feynmanRule[Ltotal, {{phim, None,      p1}, {Zb, LI[i[1]], p2}, {Wp,  LI[i[2]],   p3}}];
feynmanRules["phi-H-Wm"]    = feynmanRule[Ltotal, {{phi,  None,      p1}, {HH, None,       p2}, {Wm,  LI[i[1]], p3}}];
feynmanRules["phim-H-Wp"]   = feynmanRule[Ltotal, {{phim, None,      p1}, {HH, None,       p2}, {Wp,  LI[i[1]], p3}}];
feynmanRules["phi-chi-Wm"]  = feynmanRule[Ltotal, {{phi,  None,      p1}, {chi,None,       p2}, {Wm,  LI[i[1]], p3}}];
feynmanRules["phim-chi-Wp"] = feynmanRule[Ltotal, {{phim, None,      p1}, {chi,None,       p2}, {Wp,  LI[i[1]], p3}}];
feynmanRules["phi-phim-A"]  = feynmanRule[Ltotal, {{phi,  None,      p1}, {phim,None,      p2}, {AA,  LI[i[1]], p3}}];
feynmanRules["phi-phim-Z"]  = feynmanRule[Ltotal, {{phi,  None,      p1}, {phim,None,      p2}, {Zb,  LI[i[1]], p3}}];

(* ---- 3-point: Higgs self-coupling ------------------------------------ *)
feynmanRules["H-H-H"]       = feynmanRule[Ltotal, {{HH,  None, p1}, {HH,  None, p2}, {HH,  None, p3}}];
feynmanRules["H-chi-chi"]   = feynmanRule[Ltotal, {{HH,  None, p1}, {chi, None, p2}, {chi, None, p3}}];
feynmanRules["H-phi-phim"]  = feynmanRule[Ltotal, {{HH,  None, p1}, {phi, None, p2}, {phim,None, p3}}];

(* ---- 3-point: fermion – gauge --------------------------------------- *)
feynmanRules["el-bar-A"]     = feynmanRule[Ltotal, {{bar[el], FI[i[2]], p1}, {el, FI[i[3]], p2}, {AA, LI[i[1]], p3}}];
feynmanRules["el-bar-Z"]     = feynmanRule[Ltotal, {{bar[el], FI[i[2]], p1}, {el, FI[i[3]], p2}, {Zb, LI[i[1]], p3}}];
feynmanRules["nu-bar-Z"]     = feynmanRule[Ltotal, {{bar[nu], FI[i[2]], p1}, {nu, FI[i[3]], p2}, {Zb, LI[i[1]], p3}}];
feynmanRules["nubar-el-Wp"]  = feynmanRule[Ltotal, {{bar[nu], FI[i[2]], p1}, {el, FI[i[3]], p2}, {Wp, LI[i[1]], p3}}];
feynmanRules["elbar-nu-Wm"]  = feynmanRule[Ltotal, {{bar[el], FI[i[2]], p1}, {nu, FI[i[3]], p2}, {Wm, LI[i[1]], p3}}];
feynmanRules["uq-bar-A"]     = feynmanRule[Ltotal, {{bar[uq], FI[i[2]], p1}, {uq, FI[i[3]], p2}, {AA, LI[i[1]], p3}}];
feynmanRules["uq-bar-Z"]     = feynmanRule[Ltotal, {{bar[uq], FI[i[2]], p1}, {uq, FI[i[3]], p2}, {Zb, LI[i[1]], p3}}];
feynmanRules["dq-bar-Z"]     = feynmanRule[Ltotal, {{bar[dq], FI[i[2]], p1}, {dq, FI[i[3]], p2}, {Zb, LI[i[1]], p3}}];
feynmanRules["uqbar-dq-Wp"]  = feynmanRule[Ltotal, {{bar[uq], FI[i[2]], p1}, {dq, FI[i[3]], p2}, {Wp, LI[i[1]], p3}}];
feynmanRules["dqbar-uq-Wm"]  = feynmanRule[Ltotal, {{bar[dq], FI[i[2]], p1}, {uq, FI[i[3]], p2}, {Wm, LI[i[1]], p3}}];

(* ---- 3-point: fermion – Yukawa (H, chi, Goldstones) ----------------- *)
feynmanRules["el-bar-H"]      = feynmanRule[Ltotal, {{bar[el], FI[i[2]], p1}, {el, FI[i[3]], p2}, {HH,  None, p3}}];
feynmanRules["uq-bar-H"]      = feynmanRule[Ltotal, {{bar[uq], FI[i[2]], p1}, {uq, FI[i[3]], p2}, {HH,  None, p3}}];
feynmanRules["dq-bar-H"]      = feynmanRule[Ltotal, {{bar[dq], FI[i[2]], p1}, {dq, FI[i[3]], p2}, {HH,  None, p3}}];
feynmanRules["el-bar-chi"]    = feynmanRule[Ltotal, {{bar[el], FI[i[2]], p1}, {el, FI[i[3]], p2}, {chi, None, p3}}];
feynmanRules["uq-bar-chi"]    = feynmanRule[Ltotal, {{bar[uq], FI[i[2]], p1}, {uq, FI[i[3]], p2}, {chi, None, p3}}];
feynmanRules["dq-bar-chi"]    = feynmanRule[Ltotal, {{bar[dq], FI[i[2]], p1}, {dq, FI[i[3]], p2}, {chi, None, p3}}];
feynmanRules["nubar-el-phi"]  = feynmanRule[Ltotal, {{bar[nu], FI[i[2]], p1}, {el, FI[i[3]], p2}, {phi, None, p3}}];
feynmanRules["elbar-nu-phim"] = feynmanRule[Ltotal, {{bar[el], FI[i[2]], p1}, {nu, FI[i[3]], p2}, {phim,None, p3}}];
feynmanRules["uqbar-dq-phi"]  = feynmanRule[Ltotal, {{bar[uq], FI[i[2]], p1}, {dq, FI[i[3]], p2}, {phi, None, p3}}];
feynmanRules["dqbar-uq-phim"] = feynmanRule[Ltotal, {{bar[dq], FI[i[2]], p1}, {uq, FI[i[3]], p2}, {phim,None, p3}}];

(* ---- 3-point: ghost – gauge / ghost – scalar ------------------------- *)
feynmanRules["uba-ua-A"]    = feynmanRule[Ltotal, {{uba, None, p1}, {ua,  None, p2}, {AA,  LI[i[1]], p3}}];
feynmanRules["uba-ua-Z"]    = feynmanRule[Ltotal, {{uba, None, p1}, {ua,  None, p2}, {Zb,  LI[i[1]], p3}}];
feynmanRules["uba-ua-Wp"]   = feynmanRule[Ltotal, {{uba, None, p1}, {ua,  None, p2}, {Wp,  LI[i[1]], p3}}];
feynmanRules["uba-ua-Wm"]   = feynmanRule[Ltotal, {{uba, None, p1}, {ua,  None, p2}, {Wm,  LI[i[1]], p3}}];
feynmanRules["ubz-uz-A"]    = feynmanRule[Ltotal, {{ubz, None, p1}, {uz,  None, p2}, {AA,  LI[i[1]], p3}}];
feynmanRules["ubz-uz-Z"]    = feynmanRule[Ltotal, {{ubz, None, p1}, {uz,  None, p2}, {Zb,  LI[i[1]], p3}}];
feynmanRules["ubz-uz-Wp"]   = feynmanRule[Ltotal, {{ubz, None, p1}, {uz,  None, p2}, {Wp,  LI[i[1]], p3}}];
feynmanRules["ubz-uz-Wm"]   = feynmanRule[Ltotal, {{ubz, None, p1}, {uz,  None, p2}, {Wm,  LI[i[1]], p3}}];
feynmanRules["ubz-uz-H"]    = feynmanRule[Ltotal, {{ubz, None, p1}, {uz,  None, p2}, {HH,  None, p3}}];
feynmanRules["ubz-uz-chi"]  = feynmanRule[Ltotal, {{ubz, None, p1}, {uz,  None, p2}, {chi, None, p3}}];
feynmanRules["ubp-up-A"]    = feynmanRule[Ltotal, {{ubp, None, p1}, {up,  None, p2}, {AA,  LI[i[1]], p3}}];
feynmanRules["ubp-up-Z"]    = feynmanRule[Ltotal, {{ubp, None, p1}, {up,  None, p2}, {Zb,  LI[i[1]], p3}}];
feynmanRules["ubp-up-Wp"]   = feynmanRule[Ltotal, {{ubp, None, p1}, {up,  None, p2}, {Wp,  LI[i[1]], p3}}];
feynmanRules["ubp-up-Wm"]   = feynmanRule[Ltotal, {{ubp, None, p1}, {up,  None, p2}, {Wm,  LI[i[1]], p3}}];
feynmanRules["ubp-up-H"]    = feynmanRule[Ltotal, {{ubp, None, p1}, {up,  None, p2}, {HH,  None, p3}}];
feynmanRules["ubp-up-phi"]  = feynmanRule[Ltotal, {{ubp, None, p1}, {up,  None, p2}, {phi, None, p3}}];
feynmanRules["ubp-up-phim"] = feynmanRule[Ltotal, {{ubp, None, p1}, {up,  None, p2}, {phim,None, p3}}];
feynmanRules["ubm-um-A"]    = feynmanRule[Ltotal, {{ubm, None, p1}, {um,  None, p2}, {AA,  LI[i[1]], p3}}];
feynmanRules["ubm-um-Z"]    = feynmanRule[Ltotal, {{ubm, None, p1}, {um,  None, p2}, {Zb,  LI[i[1]], p3}}];
feynmanRules["ubm-um-Wp"]   = feynmanRule[Ltotal, {{ubm, None, p1}, {um,  None, p2}, {Wp,  LI[i[1]], p3}}];
feynmanRules["ubm-um-Wm"]   = feynmanRule[Ltotal, {{ubm, None, p1}, {um,  None, p2}, {Wm,  LI[i[1]], p3}}];
feynmanRules["ubm-um-H"]    = feynmanRule[Ltotal, {{ubm, None, p1}, {um,  None, p2}, {HH,  None, p3}}];
feynmanRules["ubm-um-phi"]  = feynmanRule[Ltotal, {{ubm, None, p1}, {um,  None, p2}, {phi, None, p3}}];
feynmanRules["ubm-um-phim"] = feynmanRule[Ltotal, {{ubm, None, p1}, {um,  None, p2}, {phim,None, p3}}];

(* ---- 4-point: quartic gauge ----------------------------------------- *)
feynmanRules["A-A-Wp-Wm"]     = feynmanRule[Ltotal, {{AA,  LI[i[1]], p1}, {AA,  LI[i[2]], p2}, {Wp, LI[i[3]], p3}, {Wm, LI[i[4]], p4}}];
feynmanRules["A-Z-Wp-Wm"]     = feynmanRule[Ltotal, {{AA,  LI[i[1]], p1}, {Zb,  LI[i[2]], p2}, {Wp, LI[i[3]], p3}, {Wm, LI[i[4]], p4}}];
feynmanRules["Z-Z-Wp-Wm"]     = feynmanRule[Ltotal, {{Zb,  LI[i[1]], p1}, {Zb,  LI[i[2]], p2}, {Wp, LI[i[3]], p3}, {Wm, LI[i[4]], p4}}];
feynmanRules["Wp-Wp-Wm-Wm"]   = feynmanRule[Ltotal, {{Wp,  LI[i[1]], p1}, {Wp,  LI[i[2]], p2}, {Wm, LI[i[3]], p3}, {Wm, LI[i[4]], p4}}];

(* ---- 4-point: Higgs self-coupling ------------------------------------ *)
feynmanRules["H-H-H-H"]          = feynmanRule[Ltotal, {{HH,  None, p1}, {HH,  None, p2}, {HH,  None, p3}, {HH,  None, p4}}];
feynmanRules["H-H-chi-chi"]      = feynmanRule[Ltotal, {{HH,  None, p1}, {HH,  None, p2}, {chi, None, p3}, {chi, None, p4}}];
feynmanRules["H-H-phi-phim"]     = feynmanRule[Ltotal, {{HH,  None, p1}, {HH,  None, p2}, {phi, None, p3}, {phim,None, p4}}];
feynmanRules["chi-chi-chi-chi"]  = feynmanRule[Ltotal, {{chi, None, p1}, {chi, None, p2}, {chi, None, p3}, {chi, None, p4}}];
feynmanRules["chi-chi-phi-phim"] = feynmanRule[Ltotal, {{chi, None, p1}, {chi, None, p2}, {phi, None, p3}, {phim,None, p4}}];
feynmanRules["phi-phi-phim-phim"]= feynmanRule[Ltotal, {{phi, None, p1}, {phi, None, p2}, {phim,None, p3}, {phim,None, p4}}];

(* ---- 4-point: Higgs – gauge ----------------------------------------- *)
feynmanRules["H-H-Wp-Wm"]       = feynmanRule[Ltotal, {{HH,  None, p1}, {HH,  None, p2}, {Wp, LI[i[1]], p3}, {Wm, LI[i[2]], p4}}];
feynmanRules["H-H-Z-Z"]         = feynmanRule[Ltotal, {{HH,  None, p1}, {HH,  None, p2}, {Zb, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}];
feynmanRules["H-H-A-A"]         = feynmanRule[Ltotal, {{HH,  None, p1}, {HH,  None, p2}, {AA, LI[i[1]], p3}, {AA, LI[i[2]], p4}}];
feynmanRules["H-H-A-Z"]         = feynmanRule[Ltotal, {{HH,  None, p1}, {HH,  None, p2}, {AA, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}];
feynmanRules["chi-chi-Wp-Wm"]   = feynmanRule[Ltotal, {{chi, None, p1}, {chi, None, p2}, {Wp, LI[i[1]], p3}, {Wm, LI[i[2]], p4}}];
feynmanRules["chi-chi-Z-Z"]     = feynmanRule[Ltotal, {{chi, None, p1}, {chi, None, p2}, {Zb, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}];
feynmanRules["chi-chi-A-A"]     = feynmanRule[Ltotal, {{chi, None, p1}, {chi, None, p2}, {AA, LI[i[1]], p3}, {AA, LI[i[2]], p4}}];
feynmanRules["phi-phim-Wp-Wm"]  = feynmanRule[Ltotal, {{phi, None, p1}, {phim,None, p2}, {Wp, LI[i[1]], p3}, {Wm, LI[i[2]], p4}}];
feynmanRules["phi-phim-Z-Z"]    = feynmanRule[Ltotal, {{phi, None, p1}, {phim,None, p2}, {Zb, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}];
feynmanRules["phi-phim-A-A"]    = feynmanRule[Ltotal, {{phi, None, p1}, {phim,None, p2}, {AA, LI[i[1]], p3}, {AA, LI[i[2]], p4}}];
feynmanRules["phi-phim-A-Z"]    = feynmanRule[Ltotal, {{phi, None, p1}, {phim,None, p2}, {AA, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}];
feynmanRules["phi-phi-Wm-Wm"]   = feynmanRule[Ltotal, {{phi, None, p1}, {phi, None, p2}, {Wm, LI[i[1]], p3}, {Wm, LI[i[2]], p4}}];
feynmanRules["phim-phim-Wp-Wp"] = feynmanRule[Ltotal, {{phim,None, p1}, {phim,None, p2}, {Wp, LI[i[1]], p3}, {Wp, LI[i[2]], p4}}];
feynmanRules["H-chi-Wp-Wm"]     = feynmanRule[Ltotal, {{HH,  None, p1}, {chi, None, p2}, {Wp, LI[i[1]], p3}, {Wm, LI[i[2]], p4}}];
feynmanRules["H-chi-A-Z"]       = feynmanRule[Ltotal, {{HH,  None, p1}, {chi, None, p2}, {AA, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}];
feynmanRules["H-phi-Wm-Z"]      = feynmanRule[Ltotal, {{HH,  None, p1}, {phi, None, p2}, {Wm, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}];
feynmanRules["H-phim-Wp-Z"]     = feynmanRule[Ltotal, {{HH,  None, p1}, {phim,None, p2}, {Wp, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}];
feynmanRules["H-phi-Wm-A"]      = feynmanRule[Ltotal, {{HH,  None, p1}, {phi, None, p2}, {Wm, LI[i[1]], p3}, {AA, LI[i[2]], p4}}];
feynmanRules["H-phim-Wp-A"]     = feynmanRule[Ltotal, {{HH,  None, p1}, {phim,None, p2}, {Wp, LI[i[1]], p3}, {AA, LI[i[2]], p4}}];
feynmanRules["chi-phi-Wm-Z"]    = feynmanRule[Ltotal, {{chi, None, p1}, {phi, None, p2}, {Wm, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}];
feynmanRules["chi-phim-Wp-Z"]   = feynmanRule[Ltotal, {{chi, None, p1}, {phim,None, p2}, {Wp, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}];
feynmanRules["chi-phi-Wm-A"]    = feynmanRule[Ltotal, {{chi, None, p1}, {phi, None, p2}, {Wm, LI[i[1]], p3}, {AA, LI[i[2]], p4}}];
feynmanRules["chi-phim-Wp-A"]   = feynmanRule[Ltotal, {{chi, None, p1}, {phim,None, p2}, {Wp, LI[i[1]], p3}, {AA, LI[i[2]], p4}}];

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
