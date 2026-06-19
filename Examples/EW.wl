(* ::Package:: *)
(* ------------------------------------------------------------------ *)
(*  EW.wl  --  SM electroweak Lagrangian                              *)
(*  One lepton generation: e, nu_e.  No quarks.                       *)
(*  Gauge: 't Hooft-Feynman  (xi_A = xi_Z = xi_W = 1).               *)
(*  Reference: Bohm, Hollik, Spiesberger eqs (22), (27)-(30).        *)
(*                                                                     *)
(*  Load with:                                                         *)
(*    Get[FileNameJoin[{ParentDirectory[$InputFileName], "LagTools.wl"}]] *)
(*    Get["...path.../Examples/EW.wl"]                                 *)
(* ------------------------------------------------------------------ *)

Get[FileNameJoin[{ParentDirectory @ DirectoryName[$InputFileName], "LagTools.wl"}]];

(* ================================================================== *)
(*  1.  Fields                                                         *)
(* ================================================================== *)

(* ---- Gauge bosons ---- *)
DeclareBoson[AA, "A"];                                    (* photon            *)
DeclareBoson[Zb, "Z"];                                    (* Z boson           *)
DeclareBoson[Wp, SuperscriptBox["W", "+"]];               (* W+                *)
DeclareBoson[Wm, SuperscriptBox["W", "-"]];               (* W-                *)

(* ---- Physical Higgs + would-be Goldstone bosons ---- *)
(*  In 't Hooft gauge the Goldstones remain as propagating fields     *)
(*  with masses M_phi = xi_W MW  ->  MW  and  M_chi = xi_Z MZ -> MZ  *)
DeclareBoson[HH,   "H"];
DeclareBoson[phi,  SuperscriptBox["\[Phi]", "+"]];        (* charged Goldstone *)
DeclareBoson[phim, SuperscriptBox["\[Phi]", "-"]];        (* charged Goldstone *)
DeclareBoson[chi,  "\[Chi]"];                             (* neutral Goldstone *)

(* ---- Leptons: one generation ---- *)
DeclareFermion[el, "e"];
DeclareFermion[nu, SubscriptBox["\[Nu]", "e"]];   (* massless: DeclareMassless called in §2 *)

(* ---- Faddeev-Popov ghosts: one u^a / ubar^a per gauge boson ---- *)
(*  Declared with DeclareGrassmann (Grassmann-odd, no Dirac index).  *)
(*  The antighost ubar^a is a separate independent field, NOT bar[u] *)
DeclareGrassmann[up,  SuperscriptBox["u", "+"]];
DeclareGrassmann[um,  SuperscriptBox["u", "-"]];
DeclareGrassmann[uz,  SuperscriptBox["u", "Z"]];
DeclareGrassmann[ua,  SuperscriptBox["u", "A"]];
DeclareGrassmann[ubp, SuperscriptBox[OverscriptBox["u", "\[Macron]"], "+"]];
DeclareGrassmann[ubm, SuperscriptBox[OverscriptBox["u", "\[Macron]"], "-"]];
DeclareGrassmann[ubz, SuperscriptBox[OverscriptBox["u", "\[Macron]"], "Z"]];
DeclareGrassmann[uba, SuperscriptBox[OverscriptBox["u", "\[Macron]"], "A"]];

(* ================================================================== *)
(*  2.  Parameters                                                     *)
(* ================================================================== *)

(*  Gauge couplings, masses: all real *)
Scan[(# /: Conjugate[#] := #) &, {ee, sw, cw, MW, MZ, MH, me}];

(*  Fermion quantum numbers: weak isospin I3w and electric charge Q.  *)
(*  Declared as independent real symbols; set numerical values by     *)
(*  substitution if needed (e.g. /. {I3we -> -1/2, Qe -> -1}).       *)
Scan[(# /: Conjugate[#] := #) &, {I3we, Qe, I3wnu, Qnu}];

(*  Neutrino: massless left-handed fermion -> PR ** nu = 0            *)
(*            (equivalent: no right-handed neutrino in this model)     *)
DeclareMassless[nu];

(*  Display names for quantum number symbols                          *)
MakeBoxes[I3we,  StandardForm] := SubsuperscriptBox["I", "3", "e"];
MakeBoxes[I3wnu, StandardForm] := SubsuperscriptBox["I", "3", "\[Nu]"];
MakeBoxes[Qe,    StandardForm] := SubscriptBox["Q", "e"];

(*  Identities (not enforced automatically; substitute as needed):    *)
(*    sw^2 + cw^2 = 1 ,  MW = cw MZ ,  v = Sqrt[2] sw MW / ee       *)

(* ================================================================== *)
(*  3.  Covariant derivatives and field strengths                     *)
(* ================================================================== *)

(*  NC couplings derived from quantum numbers                        *)
gL[I3w,Q] := I3w  - Q  sw^2;    
gR[Q] := -Q  sw^2;

(*  covDferm[mu, f, Qf, gLf, gRf]  gives  D_mu f  for a fermion f   *)
(*  with electric charge Qf and neutral-current couplings gLf, gRf.  *)
(*  The W mixing term  (e/sqrt2 sw) W^pm_mu P_L (partner)  is off-   *)
(*  diagonal in generation space and is added separately in Lferm.   *)
covDferm[mu_, Qf_, Iw3f_][f_] :=
   d[LI[mu]][f]
   - I ee Qf AA[LI[mu]] f
   - I (ee/(sw cw)) (gL[I3wf,Qf] PL + gR[Qf] PR) ** (Zb[LI[mu]] f);

(*  Non-abelian field strengths in the mass-eigenstate basis.         *)
(*  Each  F[mu,nu]  is an ordinary (commuting) expression in the      *)
(*  bosonic fields d, AA, Zb, Wp, Wm.  The kinetic Lagrangian is     *)
(*  L_kin = -1/4 g^{mu rho} g^{nu si} F_{mu,nu} F_{rho,si}.         *)
(*                                                                     *)
(*  F^A_{mu nu} = d_mu A_nu - d_nu A_mu                              *)
(*              + ie(W-_mu W+_nu - W+_mu W-_nu)                      *)
FA[mu_, nu_] :=
   d[LI[mu]][AA[LI[nu]]] - d[LI[nu]][AA[LI[mu]]]
   + I ee (Wm[LI[mu]] Wp[LI[nu]] - Wp[LI[mu]] Wm[LI[nu]]);

(*  F^Z_{mu nu} = d_mu Z_nu - d_nu Z_mu                              *)
(*              + ie(cw/sw)(W-_mu W+_nu - W+_mu W-_nu)               *)
FZ[mu_, nu_] :=
   d[LI[mu]][Zb[LI[nu]]] - d[LI[nu]][Zb[LI[mu]]]
   + I ee (cw/sw) (Wm[LI[mu]] Wp[LI[nu]] - Wp[LI[mu]] Wm[LI[nu]]);

(*  F^{W+}_{mu nu} = d_mu W+_nu - d_nu W+_mu                        *)
(*                 - ie(A_mu W+_nu - W+_mu A_nu)                     *)
(*                 + ie(cw/sw)(Z_mu W+_nu - W+_mu Z_nu)              *)
FWp[mu_, nu_] :=
   d[LI[mu]][Wp[LI[nu]]] - d[LI[nu]][Wp[LI[mu]]]
   - I ee (AA[LI[mu]] Wp[LI[nu]] - Wp[LI[mu]] AA[LI[nu]])
   + I ee (cw/sw) (Zb[LI[mu]] Wp[LI[nu]] - Wp[LI[mu]] Zb[LI[nu]]);

(*  FWm is the complex conjugate of FWp (A,Z couplings real here)    *)
FWm[mu_, nu_] :=
   d[LI[mu]][Wm[LI[nu]]] - d[LI[nu]][Wm[LI[mu]]]
   + I ee (AA[LI[mu]] Wm[LI[nu]] - Wm[LI[mu]] AA[LI[nu]])
   - I ee (cw/sw) (Zb[LI[mu]] Wm[LI[nu]] - Wm[LI[mu]] Zb[LI[nu]]);

(*  Helper: gauge-kinetic term from a field strength.                 *)
(*  gaugeKin[F] = -1/4 g^{mu rho} g^{nu si} F_{munu} F_{rhosi}      *)
(*  mu,nu,rh,si are fresh dummy symbols local to each call.           *)
gaugeKin[F_] := -(1/4) g[LI[mu], LI[rh]] g[LI[nu], LI[si]]
                        F[mu, nu] F[rh, si];

(*  Higgs-sector covariant derivative (acts on the complex scalar     *)
(*  doublet; written here in terms of the mass-eigenstate fields).    *)
(*  D_mu H+ = d_mu phi+ - ie A_mu phi+                               *)
(*          + ie(cw^2-sw^2)/(2 sw cw) Z_mu phi+                      *)
(*          + ie/(sqrt2 sw) W+_mu (H+ichi)/2 + ...                   *)
(*  In practice we expand (D_mu H)^dag (D_mu H) directly:            *)

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
(*  4.  Lagrangian sectors                                            *)
(* ================================================================== *)

(* ---- 4a. Fermion sector ---- *)
(*  i psibar gamma^mu D_mu psi - m psibar psi                        *)
(*  The charged-current (W mixing) term is off-diagonal:             *)
(*    (e/sqrt2 sw)(nubar gamma^mu PL e W+_mu + ebar gamma^mu PL nu W-_mu) *)

Lferm = Expand[
   I bar[nu] ** ga[LI[mu]] ** covDferm[mu, 0,  I3wnu][nu]
 + I bar[el] ** ga[LI[mu]] ** covDferm[mu, Qe, I3we][el]
   (* charged current: W mixes nu <-> e *)
 + (ee/(Sqrt[2] sw)) bar[nu] ** ga[LI[mu]] ** PL ** el Wp[LI[mu]]
 + (ee/(Sqrt[2] sw)) bar[el] ** ga[LI[mu]] ** PL ** nu Wm[LI[mu]]
   (* electron mass; neutrino taken massless *)
 - me bar[el] ** el
];

(* ---- 4b. Gauge kinetic sector ---- *)
(*  L_gauge = -1/4 (F^A)^2 - 1/4 (F^Z)^2 - 1/2 (F^{W+} F^{W-} + h.c.) *)
(*  Each term is computed by gaugeKin[F]; use contract[Expand[...]]   *)
(*  to reduce dummy indices before extracting vertices.               *)

LgaugeA  = gaugeKin[FA];
LgaugeZ  = gaugeKin[FZ];
LgaugeW  = -(1/2) g[LI[mu], LI[rh]] g[LI[nu], LI[si]]
                  (FWp[mu, nu] FWm[rh, si] + FWm[mu, nu] FWp[rh, si]);

Lgauge = LgaugeA + LgaugeZ + LgaugeW;

(* ---- 4c. Higgs / scalar sector ---- *)
(*  Kinetic: (D_mu phi+)* D_mu phi+ + (D_mu phi-)* D_mu phi-         *)
(*           + (D_mu H)^2 / 2 + (D_mu chi)^2 / 2                    *)
(*  Mass (from Higgs potential after SSB):                            *)
(*    -1/2 MH^2 H^2  -  MH^2 H^3/(2v) - ...  (kept to quadratic)   *)
(*    MW^2 W+_mu W-_mu  +  1/2 MZ^2 Z_mu Z_mu  (from gauge kin.)    *)
(*  In 't Hooft gauge the Goldstones get masses = gauge boson masses: *)
(*    M_phi = MW ,   M_chi = MZ                                       *)

(*  For Feynman-rule extraction, expand covD products:                *)
LHiggsKin = Expand[
   g[LI[mu], LI[nu]] (
      covDphim[mu] covDphi[nu]
    + (1/2) covDH[mu] covDH[nu]
    + (1/2) covDchi[mu] covDchi[nu])
];

(*  Mass terms (quadratic in fields; higher Higgs self-couplings omitted) *)
LHiggsMass = -(1/2) MH^2 HH^2
             - MW^2 g[LI[mu], LI[nu]] Wp[LI[mu]] Wm[LI[nu]]
             - (1/2) MZ^2 g[LI[mu], LI[nu]] Zb[LI[mu]] Zb[LI[nu]]
             - MW^2 phi phim
             - (1/2) MZ^2 chi^2;

LHiggs = LHiggsKin + LHiggsMass;

(* ---- 4d. Yukawa coupling ---- *)
(*  L_Yuk = - (e me)/(sqrt2 sw MW) (ebar el H - 2 I3w,e ebar el i chi)  *)
(*  In projector notation:  -me/v ebar el H  (v = sqrt2 sw MW / ee)      *)
(*  The ga5 Yukawa  -i me/v ebar ga5 el chi  is only for massive nu;     *)
(*  with massless nu we keep only the electron term.                     *)

LYuk = -(ee me / (Sqrt[2] sw MW)) (
   bar[el] ** el HH
   + I bar[el] ** ga5 ** el chi     (* pseudoscalar Yukawa from chi *)
);

(* ---- 4e. Gauge-fixing Lagrangian ('t Hooft-Feynman, xi=1) ---- *)
(*  L_fix = -1/2 (d^mu A_mu)^2  -  1/2 (d^mu Z_mu - MZ chi)^2    *)
(*          - (d^mu W+_mu - i MW phi+)(d^mu W-_mu + i MW phi-)     *)
(*  The gauge-fixing terms cancel the mixed  V_mu d^mu Goldstone   *)
(*  propagator entries from LHiggsKin.                              *)

CA[mu_]  := d[LI[mu]][AA[LI[mu]]];       (* note: mu used as dummy below *)
CZ[mu_]  := d[LI[mu]][Zb[LI[mu]]] - MZ chi;
CWp[mu_] := d[LI[mu]][Wp[LI[mu]]] - I MW phi;
CWm[mu_] := d[LI[mu]][Wm[LI[mu]]] + I MW phim;

(*  Use fresh dummy symbols to avoid index clashes in the squares    *)
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
