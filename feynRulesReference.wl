(* ::Package:: *)

(* ===================================================================== *)
(*  feynRulesReference.wl                                                 *)
(*                                                                        *)
(*  Reference (KNOWN-CORRECT) EWSM Feynman rules, transcribed from        *)
(*  ewsmFeynRulesCorrect.tex (Denner/Dittmaier conventions).             *)
(*                                                                        *)
(*  Full one-loop COUNTERTERM rules: tree term (the "1") + counterterms.  *)
(*  Counterterms from renormalization of UNPHYSICAL fields (Goldstone /   *)
(*  ghost field renorm) and gauge-fixing are NOT included, following the  *)
(*  tex.                                                                  *)
(*                                                                        *)
(*  Keys match the entries of `feynmanRules` in EWSMLagrangian.wl.        *)
(*  Only genuine VERTICES are provided (2-point / propagator counterterms *)
(*  are skipped).                                                         *)
(*                                                                        *)
(*  CONVENTIONS                                                           *)
(*   * all momenta p1,p2,p3,p4 flow INTO the vertex (tex k_i -> p_i,      *)
(*     in leg order);                                                     *)
(*   * Lorentz/flavour indices are taken from the leg specification, e.g. *)
(*     {AA,LI[i[1]],p3} contributes index LI[i[1]];                       *)
(*   * Dirac structures are wrapped in NC[..]; omega_- -> PL, omega_+ -> PR; *)
(*   * metric -> g[LI[..],LI[..]], delta_ij -> kd3[FI[..],FI[..]];        *)
(*   * a field-renorm matrix carries two flavour indices, e.g.            *)
(*     dZeL[FI[i],FI[j]] = (dZ^{e,L})_{ij};  its hermitian conjugate is   *)
(*     (dZ^{e,L,dagger})_{ij} = Conjugate[dZeL[FI[j],FI[i]]];             *)
(*   * repeated flavour dummy index FI[i[4]] is summed (sum over k).      *)
(* ===================================================================== *)


(* --------------------------------------------------------------------- *)
(*  Helper definitions for counterterm constants not among the primitive  *)
(*  renormalization constants of EWSMLagrangian.wl.                       *)
(* --------------------------------------------------------------------- *)

(* sw,cw renormalization ratios delta s / s and delta c / c are kept as    *)
(* the OPAQUE symbols  dsw , dcw  inside the stored Feynman rules (so the   *)
(* rules stay readable and checkable against the reference).  Expand them   *)
(* only when actually evaluating, via the replacement rule below:           *)
(*     feynruleMap[legs] /. expandSC                                        *)
expandSC = {
  dsw -> -(cw^2/(2 sw^2)) (dMW2/MW^2 - dMZ2/MZ^2),   (* delta s / s *)
  dcw ->  (1/2)            (dMW2/MW^2 - dMZ2/MZ^2)    (* delta c / c *)
};

(* weak isospin T^3 of the fermions (electric charge via ElectricCharge[]) *)
I3f[nu] = 1/2;  I3f[el] = -1/2;  I3f[uq] = 1/2;  I3f[dq] = -1/2;

(* Z chiral couplings g_f^+- and their counterterms (tex eq. geZ) *)
gpf[f_] := -(sw/cw) ElectricCharge[f];
gmf[f_] := (I3f[f] - sw^2 ElectricCharge[f])/(sw cw);
dgpf[f_] := -(sw/cw) ElectricCharge[f] (dZe + (1/cw^2) dsw);
dgmf[f_] := (I3f[f]/(sw cw)) (dZe + ((sw^2 - cw^2)/cw^2) dsw) + dgpf[f];

(* Further independent counterterms used below (symbolic):                *)
(*   dtFJ, dtPR                : tadpole CTs (FJTS / PRTS schemes)         *)
(*   dV[FI[a],FI[b]]           : CKM-matrix CT  delta V_{ab}               *)
(*   dZeL,dZeR,dZnuL,dZuL,dZuR,dZdL,dZdR  : field-renorm matrices [FI,FI]  *)

(* Fermion masses appear ONLY through the diagonal mass matrices           *)
(* Mdiagl,Mdiagu,Mdiagd (defined in EWSMLagrangian.wl), so that no bare    *)
(* m_{f,i} ever carries a repeated flavour index (which the summation      *)
(* convention would mis-contract: delta_ij m_i -> Mdiagl_ij, and a mass    *)
(* sandwiched in a product becomes a matrix factor, e.g. m_i (dZ)_ij ->    *)
(* Mdiag_ik (dZ)_kj summed over k).  Their counterterms                    *)
(* dMdiagl/dMdiagu/dMdiagd ( = delta_ij delta m_{f,i} ) are declared here. *)
SetAttributes[dMdiagl, Orderless];
SetAttributes[dMdiagu, Orderless];
SetAttributes[dMdiagd, Orderless];
Scan[(# /: Conjugate[#] := #) &, {dMdiagl, dMdiagu, dMdiagd}];

ClearAll[feynruleMap];


(* ===================================================================== *)
(*  TRIPLE GAUGE   VVV                                                    *)
(*  i e C [ g_mn (k1-k2)_r + g_nr (k2-k3)_m + g_rm (k3-k1)_n ]            *)
(*  (mu,nu,rho)=(LI[i[1]],LI[i[2]],LI[i[3]]) ; (k1,k2,k3)=(p1,p2,p3)      *)
(* ===================================================================== *)

vvvTensor[ma_, mb_, mc_] :=
    g[ma, mb] (p1[mc] - p2[mc]) + g[mb, mc] (p2[ma] - p3[ma]) + g[mc, ma] (p3[mb] - p1[mb]);

feynruleMap[{{AA, LI[i[1]], p1}, {Wp, LI[i[2]], p2}, {Wm, LI[i[3]], p3}}] =
  I ee (1 + dZe + dZW + 1/2 dZAA - 1/2 (cw/sw) dZZA) *
    vvvTensor[LI[i[1]], LI[i[2]], LI[i[3]]];

feynruleMap[{{Zb, LI[i[1]], p1}, {Wp, LI[i[2]], p2}, {Wm, LI[i[3]], p3}}] =
  I ee ( -(cw/sw) (1 + dZe - (1/cw^2) dsw + dZW + 1/2 dZZZ) + 1/2 dZAZ ) *
    vvvTensor[LI[i[1]], LI[i[2]], LI[i[3]]];


(* ===================================================================== *)
(*  SCALAR - VECTOR - VECTOR   S V V :   i e g_mn C                       *)
(*  (the two vector legs supply the metric indices)                      *)
(* ===================================================================== *)

(* H W+ W- *)
feynruleMap[{{HH, None, p1}, {Wp, LI[i[1]], p2}, {Wm, LI[i[2]], p3}}] =
  I ee g[LI[i[1]], LI[i[2]]] *
    MW (1/sw) (1 + dZe - dsw + 1/2 dMW2/MW^2 - ee/(2 sw MH^2 MW) dtFJ
               + 1/2 dZH + dZW);

(* H Z Z *)
feynruleMap[{{HH, None, p1}, {Zb, LI[i[1]], p2}, {Zb, LI[i[2]], p3}}] =
  I ee g[LI[i[1]], LI[i[2]]] *
    MW (1/(sw cw^2)) (1 + dZe + ((2 sw^2 - cw^2)/cw^2) dsw + 1/2 dMW2/MW^2
               - ee/(2 sw MH^2 MW) dtFJ + 1/2 dZH + dZZZ);

(* H A Z  (pure counterterm, from Z-A mixing) *)
feynruleMap[{{HH, None, p1}, {AA, LI[i[1]], p2}, {Zb, LI[i[2]], p3}}] =
  I ee g[LI[i[1]], LI[i[2]]] *
    MW (1/(sw cw^2)) (1/2 dZZA);

(* phi^+ W^- A   and charge conjugates  (S V V form: i e g_mn C)         *)
(* C(phi W A) and C(phi W Z) carry no explicit +- dependence.            *)
feynruleMap[{{phi, None, p1}, {AA, LI[i[1]], p2}, {Wm, LI[i[2]], p3}}] =
  I ee g[LI[i[1]], LI[i[2]]] *
    ( -MW (1 + dZe + 1/2 dMW2/MW^2 - ee/(2 sw MH^2 MW) dtFJ
           + 1/2 dZW + 1/2 dZAA)
      - MW (sw/cw) (1/2 dZZA) );

feynruleMap[{{phim, None, p1}, {AA, LI[i[1]], p2}, {Wp, LI[i[2]], p3}}] =
  I ee g[LI[i[1]], LI[i[2]]] *
    ( -MW (1 + dZe + 1/2 dMW2/MW^2 - ee/(2 sw MH^2 MW) dtFJ
           + 1/2 dZW + 1/2 dZAA)
      - MW (sw/cw) (1/2 dZZA) );

feynruleMap[{{phi, None, p1}, {Zb, LI[i[1]], p2}, {Wm, LI[i[2]], p3}}] =
  I ee g[LI[i[1]], LI[i[2]]] *
    ( -MW (sw/cw) (1 + dZe + (1/cw^2) dsw + 1/2 dMW2/MW^2
           - ee/(2 sw MH^2 MW) dtFJ + 1/2 dZW + 1/2 dZZZ)
      - MW (1/2 dZAZ) );

feynruleMap[{{phim, None, p1}, {Zb, LI[i[1]], p2}, {Wp, LI[i[2]], p3}}] =
  I ee g[LI[i[1]], LI[i[2]]] *
    ( -MW (sw/cw) (1 + dZe + (1/cw^2) dsw + 1/2 dMW2/MW^2
           - ee/(2 sw MH^2 MW) dtFJ + 1/2 dZW + 1/2 dZZZ)
      - MW (1/2 dZAZ) );


(* ===================================================================== *)
(*  VECTOR - SCALAR - SCALAR   V S S :   i e C (k1-k2)_mu                 *)
(*  k1 = momentum of first scalar (S1), k2 = momentum of second (S2),    *)
(*  in the order they appear in the tex row.                             *)
(* ===================================================================== *)

(* Z chi H   (S1=chi -> p1, S2=H -> p3) *)
feynruleMap[{{chi, None, p1}, {Zb, LI[i[1]], p2}, {HH, None, p3}}] =
  I ee ( -I/(2 cw sw) (1 + dZe + ((sw^2 - cw^2)/cw^2) dsw + 1/2 dZH + 1/2 dZZZ) ) *
    (p1[LI[i[1]]] - p3[LI[i[1]]]);

(* A phi^+ phi^-   (S1=phi^+ -> p1, S2=phi^- -> p2) *)
feynruleMap[{{phi, None, p1}, {phim, None, p2}, {AA, LI[i[1]], p3}}] =
  I ee ( -(1 + dZe + 1/2 dZAA + ((sw^2 - cw^2)/(2 sw cw)) (1/2 dZZA)) ) *
    (p1[LI[i[1]]] - p2[LI[i[1]]]);

(* Z phi^+ phi^- *)
feynruleMap[{{phi, None, p1}, {phim, None, p2}, {Zb, LI[i[1]], p3}}] =
  I ee ( -((sw^2 - cw^2)/(2 sw cw)) (1 + dZe + (1/((sw^2 - cw^2) cw^2)) dsw
           + 1/2 dZZZ) - 1/2 dZAZ ) *
    (p1[LI[i[1]]] - p2[LI[i[1]]]);

(* W^- phi^+ H  (tex W^{+-} phi^{-+} H, lower sign => +)  S1=phi^+ ->p1, S2=H ->p2 *)
feynruleMap[{{phi, None, p1}, {HH, None, p2}, {Wm, LI[i[1]], p3}}] =
  I ee ( +(1/(2 sw)) (1 + dZe - dsw + 1/2 dZW + 1/2 dZH) ) *
    (p1[LI[i[1]]] - p2[LI[i[1]]]);

(* W^+ phi^- H  (upper sign => -) *)
feynruleMap[{{phim, None, p1}, {HH, None, p2}, {Wp, LI[i[1]], p3}}] =
  I ee ( -(1/(2 sw)) (1 + dZe - dsw + 1/2 dZW + 1/2 dZH) ) *
    (p1[LI[i[1]]] - p2[LI[i[1]]]);

(* W^- phi^+ chi  (no +- dependence)  S1=phi^+ ->p1, S2=chi ->p2 *)
feynruleMap[{{phi, None, p1}, {chi, None, p2}, {Wm, LI[i[1]], p3}}] =
  I ee ( -I/(2 sw) (1 + dZe - dsw + 1/2 dZW) ) *
    (p1[LI[i[1]]] - p2[LI[i[1]]]);

(* W^+ phi^- chi *)
feynruleMap[{{phim, None, p1}, {chi, None, p2}, {Wp, LI[i[1]], p3}}] =
  I ee ( -I/(2 sw) (1 + dZe - dsw + 1/2 dZW) ) *
    (p1[LI[i[1]]] - p2[LI[i[1]]]);


(* ===================================================================== *)
(*  SCALAR SELF-COUPLING   S S S :   i e C                               *)
(* ===================================================================== *)

(* H H H *)
feynruleMap[{{HH, None, p1}, {HH, None, p2}, {HH, None, p3}}] =
  I ee ( -(3/(2 sw)) (MH^2/MW) (1 + dZe - dsw + dMH2/MH^2
       + ee/(2 sw MH^2 MW) (dtPR - dtFJ) - 1/2 dMW2/MW^2 + 3/2 dZH) );

(* H chi chi *)
feynruleMap[{{HH, None, p1}, {chi, None, p2}, {chi, None, p3}}] =
  I ee ( -(1/(2 sw)) (MH^2/MW) (1 + dZe - dsw + dMH2/MH^2
       + ee/(2 sw MH^2 MW) (dtPR - dtFJ) - 1/2 dMW2/MW^2 + 1/2 dZH) );

(* H phi^+ phi^-  (same C as H chi chi) *)
feynruleMap[{{HH, None, p1}, {phi, None, p2}, {phim, None, p3}}] =
  I ee ( -(1/(2 sw)) (MH^2/MW) (1 + dZe - dsw + dMH2/MH^2
       + ee/(2 sw MH^2 MW) (dtPR - dtFJ) - 1/2 dMW2/MW^2 + 1/2 dZH) );


(* ===================================================================== *)
(*  VECTOR - FERMION - FERMION   V Fbar F :                              *)
(*       i e gamma_mu ( CL omega_- + CR omega_+ )                        *)
(*  bar f_i = FI[i[2]] (= i),  f_j = FI[i[3]] (= j)                      *)
(* ===================================================================== *)

(* --- photon : CL,CR = -Q_f[ delta_ij(1+dZe+1/2 dZAA) + 1/2(dZL+dZL^d) ] *)
(*              + delta_ij g_f^-+ (1/2 dZZA)                              *)
vffPhoton[f_, dZL_, dZR_] :=
  I ee (
    NC[ga[LI[i[1]]], PL] (
       -ElectricCharge[f] ( kd3[FI[i[2]], FI[i[3]]] (1 + dZe + 1/2 dZAA)
            + 1/2 (dZL[FI[i[2]], FI[i[3]]] + Conjugate[dZL[FI[i[3]], FI[i[2]]]]) )
       + kd3[FI[i[2]], FI[i[3]]] gmf[f] (1/2 dZZA) )
  + NC[ga[LI[i[1]]], PR] (
       -ElectricCharge[f] ( kd3[FI[i[2]], FI[i[3]]] (1 + dZe + 1/2 dZAA)
            + 1/2 (dZR[FI[i[2]], FI[i[3]]] + Conjugate[dZR[FI[i[3]], FI[i[2]]]]) )
       + kd3[FI[i[2]], FI[i[3]]] gpf[f] (1/2 dZZA) ) );

(* --- Z : CL,CR = g_f^-+ [ delta_ij(1+dg/g+1/2 dZZ) + 1/2(dZ+dZ^d) ]    *)
(*               - delta_ij Q_f (1/2 dZAZ)                                *)
vffZ[f_, dZL_, dZR_] :=
  I ee (
    NC[ga[LI[i[1]]], PL] (
       kd3[FI[i[2]], FI[i[3]]] ( gmf[f] + dgmf[f] + gmf[f] (1/2 dZZZ)
            - ElectricCharge[f] (1/2 dZAZ) )
       + gmf[f] (1/2) (dZL[FI[i[2]], FI[i[3]]] + Conjugate[dZL[FI[i[3]], FI[i[2]]]]) )
  + NC[ga[LI[i[1]]], PR] (
       kd3[FI[i[2]], FI[i[3]]] ( gpf[f] + dgpf[f] + gpf[f] (1/2 dZZZ)
            - ElectricCharge[f] (1/2 dZAZ) )
       + gpf[f] (1/2) (dZR[FI[i[2]], FI[i[3]]] + Conjugate[dZR[FI[i[3]], FI[i[2]]]]) ) );

feynruleMap[{{bar[el], FI[i[2]], p1}, {el, FI[i[3]], p2}, {AA, LI[i[1]], p3}}] =
  vffPhoton[el, dZeL, dZeR];
feynruleMap[{{bar[uq], FI[i[2]], p1}, {uq, FI[i[3]], p2}, {AA, LI[i[1]], p3}}] =
  vffPhoton[uq, dZuL, dZuR];

feynruleMap[{{bar[el], FI[i[2]], p1}, {el, FI[i[3]], p2}, {Zb, LI[i[1]], p3}}] =
  vffZ[el, dZeL, dZeR];
feynruleMap[{{bar[uq], FI[i[2]], p1}, {uq, FI[i[3]], p2}, {Zb, LI[i[1]], p3}}] =
  vffZ[uq, dZuL, dZuR];
feynruleMap[{{bar[dq], FI[i[2]], p1}, {dq, FI[i[3]], p2}, {Zb, LI[i[1]], p3}}] =
  vffZ[dq, dZdL, dZdR];

(* neutrino : Q_nu = 0, g_nu^+ = 0, no right-handed field => CR = 0 *)
feynruleMap[{{bar[nu], FI[i[2]], p1}, {nu, FI[i[3]], p2}, {Zb, LI[i[1]], p3}}] =
  I ee NC[ga[LI[i[1]]], PL] (
       kd3[FI[i[2]], FI[i[3]]] ( gmf[nu] + dgmf[nu] + gmf[nu] (1/2 dZZZ)
            - ElectricCharge[nu] (1/2 dZAZ) )
       + gmf[nu] (1/2) (dZnuL[FI[i[2]], FI[i[3]]]
            + Conjugate[dZnuL[FI[i[3]], FI[i[2]]]]) );


(* ===================================================================== *)
(*  CHARGED-CURRENT   W Fbar F :  i e gamma_mu ( CL omega_- + CR omega_+ ) *)
(*  CR = 0 in all cases.                                                  *)
(* ===================================================================== *)

(* W^+ nubar_i l_j  (lepton, V -> delta) *)
feynruleMap[{{bar[nu], FI[i[2]], p1}, {el, FI[i[3]], p2}, {Wp, LI[i[1]], p3}}] =
  I ee NC[ga[LI[i[1]]], PL] (
    1/(Sqrt[2] sw) ( kd3[FI[i[2]], FI[i[3]]] (1 + dZe - dsw + 1/2 dZW)
       + 1/2 ( Conjugate[dZnuL[FI[i[3]], FI[i[2]]]] + dZeL[FI[i[2]], FI[i[3]]] ) ) );

(* W^- lbar_j nu_i *)
feynruleMap[{{bar[el], FI[i[2]], p1}, {nu, FI[i[3]], p2}, {Wm, LI[i[1]], p3}}] =
  I ee NC[ga[LI[i[1]]], PL] (
    1/(Sqrt[2] sw) ( kd3[FI[i[2]], FI[i[3]]] (1 + dZe - dsw + 1/2 dZW)
       + 1/2 ( Conjugate[dZeL[FI[i[3]], FI[i[2]]]] + dZnuL[FI[i[2]], FI[i[3]]] ) ) );

(* W^+ ubar_i d_j   (i = up = FI[i[2]], j = down = FI[i[3]]) *)
feynruleMap[{{bar[uq], FI[i[2]], p1}, {dq, FI[i[3]], p2}, {Wp, LI[i[1]], p3}}] =
  I ee NC[ga[LI[i[1]]], PL] (
    1/(Sqrt[2] sw) ( V[FI[i[2]], FI[i[3]]] (1 + dZe - dsw + 1/2 dZW)
       + dV[FI[i[2]], FI[i[3]]]
       + 1/2 ( Conjugate[dZuL[FI[i[4]], FI[i[2]]]] V[FI[i[4]], FI[i[3]]]
             + V[FI[i[2]], FI[i[4]]] dZdL[FI[i[4]], FI[i[3]]] ) ) );

(* W^- dbar_j u_i   (j = down = FI[i[2]], i = up = FI[i[3]]) *)
feynruleMap[{{bar[dq], FI[i[2]], p1}, {uq, FI[i[3]], p2}, {Wm, LI[i[1]], p3}}] =
  I ee NC[ga[LI[i[1]]], PL] (
    1/(Sqrt[2] sw) ( Conjugate[V[FI[i[3]], FI[i[2]]]] (1 + dZe - dsw + 1/2 dZW)
       + Conjugate[dV[FI[i[3]], FI[i[2]]]]
       + 1/2 ( Conjugate[dZdL[FI[i[4]], FI[i[2]]]] Conjugate[V[FI[i[3]], FI[i[4]]]]
             + Conjugate[V[FI[i[4]], FI[i[2]]]] dZuL[FI[i[4]], FI[i[3]]] ) ) );


(* ===================================================================== *)
(*  SCALAR - FERMION - FERMION   S Fbar F :                              *)
(*       i e ( CL omega_- + CR omega_+ )                                 *)
(*  No Goldstone field-renorm CTs (unphysical fields).                   *)
(* ===================================================================== *)

(* --- Higgs : CR = -1/(2 s MW)[ delta_ij m_i(...) + 1/2(m_i dZR + dZL^d m_j) ] *)
(*             CL : R<->L.  (mass-CT symbol differs per fermion, so the    *)
(*             three Higgs-fermion vertices are written out explicitly.)   *)

(* H ebar e *)
feynruleMap[{{bar[el], FI[i[2]], p1}, {el, FI[i[3]], p2}, {HH, None, p3}}] =
  I ee (-(1/(2 sw MW))) (
    NC[PL] (
       Mdiagl[FI[i[2]], FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2 + 1/2 dZH)
       + dMdiagl[FI[i[2]], FI[i[3]]]
       + 1/2 ( Mdiagl[FI[i[2]], FI[i[4]]] dZeL[FI[i[4]], FI[i[3]]]
             + Conjugate[dZeR[FI[i[4]], FI[i[2]]]] Mdiagl[FI[i[4]], FI[i[3]]] ) )
  + NC[PR] (
       Mdiagl[FI[i[2]], FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2 + 1/2 dZH)
       + dMdiagl[FI[i[2]], FI[i[3]]]
       + 1/2 ( Mdiagl[FI[i[2]], FI[i[4]]] dZeR[FI[i[4]], FI[i[3]]]
             + Conjugate[dZeL[FI[i[4]], FI[i[2]]]] Mdiagl[FI[i[4]], FI[i[3]]] ) ) );

(* H ubar u *)
feynruleMap[{{bar[uq], FI[i[2]], p1}, {uq, FI[i[3]], p2}, {HH, None, p3}}] =
  I ee (-(1/(2 sw MW))) (
    NC[PL] (
       Mdiagu[FI[i[2]], FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2 + 1/2 dZH)
       + dMdiagu[FI[i[2]], FI[i[3]]]
       + 1/2 ( Mdiagu[FI[i[2]], FI[i[4]]] dZuL[FI[i[4]], FI[i[3]]]
             + Conjugate[dZuR[FI[i[4]], FI[i[2]]]] Mdiagu[FI[i[4]], FI[i[3]]] ) )
  + NC[PR] (
       Mdiagu[FI[i[2]], FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2 + 1/2 dZH)
       + dMdiagu[FI[i[2]], FI[i[3]]]
       + 1/2 ( Mdiagu[FI[i[2]], FI[i[4]]] dZuR[FI[i[4]], FI[i[3]]]
             + Conjugate[dZuL[FI[i[4]], FI[i[2]]]] Mdiagu[FI[i[4]], FI[i[3]]] ) ) );

(* H dbar d *)
feynruleMap[{{bar[dq], FI[i[2]], p1}, {dq, FI[i[3]], p2}, {HH, None, p3}}] =
  I ee (-(1/(2 sw MW))) (
    NC[PL] (
       Mdiagd[FI[i[2]], FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2 + 1/2 dZH)
       + dMdiagd[FI[i[2]], FI[i[3]]]
       + 1/2 ( Mdiagd[FI[i[2]], FI[i[4]]] dZdL[FI[i[4]], FI[i[3]]]
             + Conjugate[dZdR[FI[i[4]], FI[i[2]]]] Mdiagd[FI[i[4]], FI[i[3]]] ) )
  + NC[PR] (
       Mdiagd[FI[i[2]], FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2 + 1/2 dZH)
       + dMdiagd[FI[i[2]], FI[i[3]]]
       + 1/2 ( Mdiagd[FI[i[2]], FI[i[4]]] dZdR[FI[i[4]], FI[i[3]]]
             + Conjugate[dZdL[FI[i[4]], FI[i[2]]]] Mdiagd[FI[i[4]], FI[i[3]]] ) ) );

(* --- chi : CR = +i/(2s) 2 I3_f /MW [ delta_ij m_i(...) + 1/2(m_i dZR+dZL^d m_j) ] *)
(*           CL = -i/(2s) 2 I3_f /MW [ delta_ij m_i(...) + 1/2(m_i dZL+dZR^d m_j) ] *)
(*  bracket: 1+dZe-dsw+dm_i/m_i-1/2 dMW2/MW2  (no dZH).                   *)

(* chi ebar e *)
feynruleMap[{{bar[el], FI[i[2]], p1}, {el, FI[i[3]], p2}, {chi, None, p3}}] =
  I ee (
    NC[PL] ( -I/(2 sw) (2 I3f[el]) (1/MW) (
         Mdiagl[FI[i[2]], FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
       + dMdiagl[FI[i[2]], FI[i[3]]]
       + 1/2 ( Mdiagl[FI[i[2]], FI[i[4]]] dZeL[FI[i[4]], FI[i[3]]]
             + Conjugate[dZeR[FI[i[4]], FI[i[2]]]] Mdiagl[FI[i[4]], FI[i[3]]] ) ) )
  + NC[PR] ( +I/(2 sw) (2 I3f[el]) (1/MW) (
         Mdiagl[FI[i[2]], FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
       + dMdiagl[FI[i[2]], FI[i[3]]]
       + 1/2 ( Mdiagl[FI[i[2]], FI[i[4]]] dZeR[FI[i[4]], FI[i[3]]]
             + Conjugate[dZeL[FI[i[4]], FI[i[2]]]] Mdiagl[FI[i[4]], FI[i[3]]] ) ) ) );

(* chi ubar u *)
feynruleMap[{{bar[uq], FI[i[2]], p1}, {uq, FI[i[3]], p2}, {chi, None, p3}}] =
  I ee (
    NC[PL] ( -I/(2 sw) (2 I3f[uq]) (1/MW) (
         Mdiagu[FI[i[2]], FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
       + dMdiagu[FI[i[2]], FI[i[3]]]
       + 1/2 ( Mdiagu[FI[i[2]], FI[i[4]]] dZuL[FI[i[4]], FI[i[3]]]
             + Conjugate[dZuR[FI[i[4]], FI[i[2]]]] Mdiagu[FI[i[4]], FI[i[3]]] ) ) )
  + NC[PR] ( +I/(2 sw) (2 I3f[uq]) (1/MW) (
         Mdiagu[FI[i[2]], FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
       + dMdiagu[FI[i[2]], FI[i[3]]]
       + 1/2 ( Mdiagu[FI[i[2]], FI[i[4]]] dZuR[FI[i[4]], FI[i[3]]]
             + Conjugate[dZuL[FI[i[4]], FI[i[2]]]] Mdiagu[FI[i[4]], FI[i[3]]] ) ) ) );

(* chi dbar d *)
feynruleMap[{{bar[dq], FI[i[2]], p1}, {dq, FI[i[3]], p2}, {chi, None, p3}}] =
  I ee (
    NC[PL] ( -I/(2 sw) (2 I3f[dq]) (1/MW) (
         Mdiagd[FI[i[2]], FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
       + dMdiagd[FI[i[2]], FI[i[3]]]
       + 1/2 ( Mdiagd[FI[i[2]], FI[i[4]]] dZdL[FI[i[4]], FI[i[3]]]
             + Conjugate[dZdR[FI[i[4]], FI[i[2]]]] Mdiagd[FI[i[4]], FI[i[3]]] ) ) )
  + NC[PR] ( +I/(2 sw) (2 I3f[dq]) (1/MW) (
         Mdiagd[FI[i[2]], FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
       + dMdiagd[FI[i[2]], FI[i[3]]]
       + 1/2 ( Mdiagd[FI[i[2]], FI[i[4]]] dZdR[FI[i[4]], FI[i[3]]]
             + Conjugate[dZdL[FI[i[4]], FI[i[2]]]] Mdiagd[FI[i[4]], FI[i[3]]] ) ) ) );


(* ===================================================================== *)
(*  CHARGED GOLDSTONE - FERMION - FERMION   phi Fbar F                    *)
(* ===================================================================== *)

(* phi^+ ubar_i d_j   (i=up=FI[i[2]], j=down=FI[i[3]]; sums over i[4],i[5]) *)
feynruleMap[{{bar[uq], FI[i[2]], p1}, {dq, FI[i[3]], p2}, {phi, None, p3}}] =
  I ee (
    NC[PL] ( 1/(Sqrt[2] sw MW) (
         Mdiagu[FI[i[2]], FI[i[4]]] V[FI[i[4]], FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
       + dMdiagu[FI[i[2]], FI[i[4]]] V[FI[i[4]], FI[i[3]]]
       + Mdiagu[FI[i[2]], FI[i[4]]] dV[FI[i[4]], FI[i[3]]]
       + 1/2 ( Conjugate[dZuR[FI[i[4]], FI[i[2]]]] Mdiagu[FI[i[4]], FI[i[5]]] V[FI[i[5]], FI[i[3]]]
             + Mdiagu[FI[i[2]], FI[i[4]]] V[FI[i[4]], FI[i[5]]] dZdL[FI[i[5]], FI[i[3]]] ) ) )
  + NC[PR] ( -(1/(Sqrt[2] sw MW)) (
         V[FI[i[2]], FI[i[4]]] Mdiagd[FI[i[4]], FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
       + V[FI[i[2]], FI[i[4]]] dMdiagd[FI[i[4]], FI[i[3]]]
       + dV[FI[i[2]], FI[i[4]]] Mdiagd[FI[i[4]], FI[i[3]]]
       + 1/2 ( Conjugate[dZuL[FI[i[4]], FI[i[2]]]] V[FI[i[4]], FI[i[5]]] Mdiagd[FI[i[5]], FI[i[3]]]
             + V[FI[i[2]], FI[i[4]]] Mdiagd[FI[i[4]], FI[i[5]]] dZdR[FI[i[5]], FI[i[3]]] ) ) ) );

(* phi^- dbar_j u_i   (j=down=FI[i[2]], i=up=FI[i[3]]; sums over i[4],i[5]) *)
feynruleMap[{{bar[dq], FI[i[2]], p1}, {uq, FI[i[3]], p2}, {phim, None, p3}}] =
  I ee (
    NC[PL] ( -(1/(Sqrt[2] sw MW)) (
         Mdiagd[FI[i[2]], FI[i[4]]] Conjugate[V[FI[i[3]], FI[i[4]]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
       + dMdiagd[FI[i[2]], FI[i[4]]] Conjugate[V[FI[i[3]], FI[i[4]]]]
       + Mdiagd[FI[i[2]], FI[i[4]]] Conjugate[dV[FI[i[3]], FI[i[4]]]]
       + 1/2 ( Conjugate[dZdR[FI[i[4]], FI[i[2]]]] Mdiagd[FI[i[4]], FI[i[5]]] Conjugate[V[FI[i[3]], FI[i[5]]]]
             + Mdiagd[FI[i[2]], FI[i[5]]] Conjugate[V[FI[i[4]], FI[i[5]]]] dZuL[FI[i[4]], FI[i[3]]] ) ) )
  + NC[PR] ( 1/(Sqrt[2] sw MW) (
         Conjugate[V[FI[i[4]], FI[i[2]]]] Mdiagu[FI[i[4]], FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
       + Conjugate[V[FI[i[4]], FI[i[2]]]] dMdiagu[FI[i[4]], FI[i[3]]]
       + Conjugate[dV[FI[i[4]], FI[i[2]]]] Mdiagu[FI[i[4]], FI[i[3]]]
       + 1/2 ( Conjugate[dZdL[FI[i[4]], FI[i[2]]]] Conjugate[V[FI[i[5]], FI[i[4]]]] Mdiagu[FI[i[5]], FI[i[3]]]
             + Conjugate[V[FI[i[4]], FI[i[2]]]] Mdiagu[FI[i[4]], FI[i[5]]] dZuR[FI[i[5]], FI[i[3]]] ) ) ) );

(* phi^+ nubar_i l_j   (lepton, V -> delta, neutrino massless => CL = 0) *)
feynruleMap[{{bar[nu], FI[i[2]], p1}, {el, FI[i[3]], p2}, {phi, None, p3}}] =
  I ee NC[PR] ( -(1/(Sqrt[2] sw MW)) (
       Mdiagl[FI[i[2]], FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
     + dMdiagl[FI[i[2]], FI[i[3]]]
     + 1/2 ( Conjugate[dZnuL[FI[i[4]], FI[i[2]]]] Mdiagl[FI[i[4]], FI[i[3]]]
           + Mdiagl[FI[i[2]], FI[i[4]]] dZeR[FI[i[4]], FI[i[3]]] ) ) );

(* phi^- lbar_j nu_i   (CR = 0) *)
feynruleMap[{{bar[el], FI[i[2]], p1}, {nu, FI[i[3]], p2}, {phim, None, p3}}] =
  I ee NC[PL] ( -(1/(Sqrt[2] sw MW)) (
       Mdiagl[FI[i[2]], FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
     + dMdiagl[FI[i[2]], FI[i[3]]]
     + 1/2 ( Conjugate[dZeR[FI[i[4]], FI[i[2]]]] Mdiagl[FI[i[4]], FI[i[3]]]
           + Mdiagl[FI[i[2]], FI[i[4]]] dZnuL[FI[i[4]], FI[i[3]]] ) ) );


(* ===================================================================== *)
(*  QUARTIC GAUGE   V V V V :                                            *)
(*    i e^2 C [ 2 g_mn g_rs - g_ms g_nr - g_mr g_ns ]                    *)
(*  index pairing follows the tex row (V1 V2 V3 V4 = mu nu rho sigma).   *)
(* ===================================================================== *)

(* W+ W+ W- W- : (mu,nu,rho,sigma)=(i1,i2,i3,i4) directly *)
feynruleMap[{{Wp, LI[i[1]], p1}, {Wp, LI[i[2]], p2}, {Wm, LI[i[3]], p3}, {Wm, LI[i[4]], p4}}] =
  I ee^2 ( (1/sw^2) (1 + 2 dZe - 2 dsw + 2 dZW) ) *
    ( 2 g[LI[i[1]], LI[i[2]]] g[LI[i[3]], LI[i[4]]]
      - g[LI[i[1]], LI[i[4]]] g[LI[i[2]], LI[i[3]]]
      - g[LI[i[1]], LI[i[3]]] g[LI[i[2]], LI[i[4]]] );

(* W+ W- Z Z  --  our leg order (Z,Z,W+,W-)=(i1,i2,i3,i4);              *)
(*               tex (mu,nu,rho,sigma)=(W+,W-,Z,Z)=(i3,i4,i1,i2)        *)
feynruleMap[{{Zb, LI[i[1]], p1}, {Zb, LI[i[2]], p2}, {Wp, LI[i[3]], p3}, {Wm, LI[i[4]], p4}}] =
  I ee^2 ( -(cw^2/sw^2) (1 + 2 dZe - (2/cw^2) dsw + dZW + dZZZ) + (cw/sw) dZAZ ) *
    ( 2 g[LI[i[3]], LI[i[4]]] g[LI[i[1]], LI[i[2]]]
      - g[LI[i[3]], LI[i[2]]] g[LI[i[4]], LI[i[1]]]
      - g[LI[i[3]], LI[i[1]]] g[LI[i[4]], LI[i[2]]] );

(* W+ W- A Z  --  our order (A,Z,W+,W-)=(i1,i2,i3,i4);                  *)
(*               tex (W+,W-,A,Z)=(i3,i4,i1,i2)                          *)
feynruleMap[{{AA, LI[i[1]], p1}, {Zb, LI[i[2]], p2}, {Wp, LI[i[3]], p3}, {Wm, LI[i[4]], p4}}] =
  I ee^2 ( (cw/sw) (1 + 2 dZe - (1/cw^2) dsw + dZW + 1/2 dZZZ + 1/2 dZAA)
           - 1/2 dZAZ - 1/2 (cw^2/sw^2) dZZA ) *
    ( 2 g[LI[i[3]], LI[i[4]]] g[LI[i[1]], LI[i[2]]]
      - g[LI[i[3]], LI[i[2]]] g[LI[i[4]], LI[i[1]]]
      - g[LI[i[3]], LI[i[1]]] g[LI[i[4]], LI[i[2]]] );

(* W+ W- A A  --  our order (A,A,W+,W-)=(i1,i2,i3,i4);                  *)
(*               tex (W+,W-,A,A)=(i3,i4,i1,i2)                          *)
feynruleMap[{{AA, LI[i[1]], p1}, {AA, LI[i[2]], p2}, {Wp, LI[i[3]], p3}, {Wm, LI[i[4]], p4}}] =
  I ee^2 ( -(1 + 2 dZe + dZW + dZAA) + (cw/sw) dZZA ) *
    ( 2 g[LI[i[3]], LI[i[4]]] g[LI[i[1]], LI[i[2]]]
      - g[LI[i[3]], LI[i[2]]] g[LI[i[4]], LI[i[1]]]
      - g[LI[i[3]], LI[i[1]]] g[LI[i[4]], LI[i[2]]] );


(* ===================================================================== *)
(*  QUARTIC SCALAR   S S S S :   i e^2 C                                 *)
(* ===================================================================== *)

(* shared bracket without the field-renorm piece *)
ssssBr := 1 + 2 dZe - 2 dsw + dMH2/MH^2 + ee/(2 sw MH^2 MW) dtPR - dMW2/MW^2;

feynruleMap[{{HH, None, p1}, {HH, None, p2}, {HH, None, p3}, {HH, None, p4}}] =
  I ee^2 ( -(3/(4 sw^2)) (MH^2/MW^2) (ssssBr + 2 dZH) );

feynruleMap[{{HH, None, p1}, {HH, None, p2}, {chi, None, p3}, {chi, None, p4}}] =
  I ee^2 ( -(1/(4 sw^2)) (MH^2/MW^2) (ssssBr + dZH) );

feynruleMap[{{HH, None, p1}, {HH, None, p2}, {phi, None, p3}, {phim, None, p4}}] =
  I ee^2 ( -(1/(4 sw^2)) (MH^2/MW^2) (ssssBr + dZH) );

feynruleMap[{{chi, None, p1}, {chi, None, p2}, {chi, None, p3}, {chi, None, p4}}] =
  I ee^2 ( -(3/(4 sw^2)) (MH^2/MW^2) ssssBr );

feynruleMap[{{chi, None, p1}, {chi, None, p2}, {phi, None, p3}, {phim, None, p4}}] =
  I ee^2 ( -(1/(4 sw^2)) (MH^2/MW^2) ssssBr );

feynruleMap[{{phi, None, p1}, {phi, None, p2}, {phim, None, p3}, {phim, None, p4}}] =
  I ee^2 ( -(1/(2 sw^2)) (MH^2/MW^2) ssssBr );


(* ===================================================================== *)
(*  VECTOR VECTOR SCALAR SCALAR   V V S S :   i e^2 g_mn C               *)
(*  (the two vector legs supply the metric indices)                      *)
(* ===================================================================== *)

(* W+ W- H H *)
feynruleMap[{{HH, None, p1}, {HH, None, p2}, {Wp, LI[i[1]], p3}, {Wm, LI[i[2]], p4}}] =
  I ee^2 g[LI[i[1]], LI[i[2]]] ( (1/(2 sw^2)) (1 + 2 dZe - 2 dsw + dZW + dZH) );

(* Z Z H H *)
feynruleMap[{{HH, None, p1}, {HH, None, p2}, {Zb, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}] =
  I ee^2 g[LI[i[1]], LI[i[2]]] (
    (1/(2 sw^2 cw^2)) (1 + 2 dZe + (2 (sw^2 - cw^2)/cw^2) dsw + dZZZ + dZH) );

(* A A H H : no such tree or counterterm vertex *)
feynruleMap[{{HH, None, p1}, {HH, None, p2}, {AA, LI[i[1]], p3}, {AA, LI[i[2]], p4}}] = 0;

(* Z A H H : pure counterterm *)
feynruleMap[{{HH, None, p1}, {HH, None, p2}, {AA, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}] =
  I ee^2 g[LI[i[1]], LI[i[2]]] ( (1/(2 sw^2 cw^2)) (1/2 dZZA) );

(* W+ W- chi chi *)
feynruleMap[{{chi, None, p1}, {chi, None, p2}, {Wp, LI[i[1]], p3}, {Wm, LI[i[2]], p4}}] =
  I ee^2 g[LI[i[1]], LI[i[2]]] ( (1/(2 sw^2)) (1 + 2 dZe - 2 dsw + dZW) );

(* Z Z chi chi *)
feynruleMap[{{chi, None, p1}, {chi, None, p2}, {Zb, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}] =
  I ee^2 g[LI[i[1]], LI[i[2]]] (
    (1/(2 sw^2 cw^2)) (1 + 2 dZe + (2 (sw^2 - cw^2)/cw^2) dsw + dZZZ) );

(* A A chi chi : none *)
feynruleMap[{{chi, None, p1}, {chi, None, p2}, {AA, LI[i[1]], p3}, {AA, LI[i[2]], p4}}] = 0;

(* W+ W- phi+ phi- *)
feynruleMap[{{phi, None, p1}, {phim, None, p2}, {Wp, LI[i[1]], p3}, {Wm, LI[i[2]], p4}}] =
  I ee^2 g[LI[i[1]], LI[i[2]]] ( (1/(2 sw^2)) (1 + 2 dZe - 2 dsw + dZW) );

(* Z Z phi+ phi- *)
feynruleMap[{{phi, None, p1}, {phim, None, p2}, {Zb, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}] =
  I ee^2 g[LI[i[1]], LI[i[2]]] (
    ((sw^2 - cw^2)^2/(2 sw^2 cw^2)) (1 + 2 dZe + (2/((sw^2 - cw^2) cw^2)) dsw + dZZZ)
    + ((sw^2 - cw^2)/(sw cw)) dZAZ );

(* A A phi+ phi- *)
feynruleMap[{{phi, None, p1}, {phim, None, p2}, {AA, LI[i[1]], p3}, {AA, LI[i[2]], p4}}] =
  I ee^2 g[LI[i[1]], LI[i[2]]] (
    2 (1 + 2 dZe + dZAA) + ((sw^2 - cw^2)/(sw cw)) dZZA );

(* Z A phi+ phi-  (our vector order A,Z) *)
feynruleMap[{{phi, None, p1}, {phim, None, p2}, {AA, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}] =
  I ee^2 g[LI[i[1]], LI[i[2]]] (
    ((sw^2 - cw^2)/(sw cw)) (1 + 2 dZe + (1/((sw^2 - cw^2) cw^2)) dsw
        + 1/2 dZZZ + 1/2 dZAA)
    + ((sw^2 - cw^2)^2/(2 sw^2 cw^2)) (1/2 dZZA) + dZAZ );

(* phi+ phi+ W- W- and c.c. : no such vertex *)
feynruleMap[{{phi, None, p1}, {phi, None, p2}, {Wm, LI[i[1]], p3}, {Wm, LI[i[2]], p4}}] = 0;
feynruleMap[{{phim, None, p1}, {phim, None, p2}, {Wp, LI[i[1]], p3}, {Wp, LI[i[2]], p4}}] = 0;

(* H chi V V : no such vertex *)
feynruleMap[{{HH, None, p1}, {chi, None, p2}, {Wp, LI[i[1]], p3}, {Wm, LI[i[2]], p4}}] = 0;
feynruleMap[{{HH, None, p1}, {chi, None, p2}, {AA, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}] = 0;

(* W^{-+} Z phi^{+-} H  --  C has no +- dependence; vector legs (W,Z)    *)
feynruleMap[{{HH, None, p1}, {phi, None, p2}, {Wm, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}] =
  I ee^2 g[LI[i[1]], LI[i[2]]] (
    -(1/(2 cw)) (1 + 2 dZe - dcw + 1/2 dZW + 1/2 dZH + 1/2 dZZZ)
    - (1/(2 sw)) (1/2 dZAZ) );
feynruleMap[{{HH, None, p1}, {phim, None, p2}, {Wp, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}] =
  I ee^2 g[LI[i[1]], LI[i[2]]] (
    -(1/(2 cw)) (1 + 2 dZe - dcw + 1/2 dZW + 1/2 dZH + 1/2 dZZZ)
    - (1/(2 sw)) (1/2 dZAZ) );

(* W^{-+} A phi^{+-} H *)
feynruleMap[{{HH, None, p1}, {phi, None, p2}, {Wm, LI[i[1]], p3}, {AA, LI[i[2]], p4}}] =
  I ee^2 g[LI[i[1]], LI[i[2]]] (
    -(1/(2 sw)) (1 + 2 dZe - dsw + 1/2 dZW + 1/2 dZH + 1/2 dZAA)
    - (1/(2 cw)) (1/2 dZZA) );
feynruleMap[{{HH, None, p1}, {phim, None, p2}, {Wp, LI[i[1]], p3}, {AA, LI[i[2]], p4}}] =
  I ee^2 g[LI[i[1]], LI[i[2]]] (
    -(1/(2 sw)) (1 + 2 dZe - dsw + 1/2 dZW + 1/2 dZH + 1/2 dZAA)
    - (1/(2 cw)) (1/2 dZZA) );

(* W^{-+} Z phi^{+-} chi  --  prefactor sign = -(sign of W charge):       *)
(*   W^- (phi^+) -> +i ;  W^+ (phi^-) -> -i                               *)
feynruleMap[{{chi, None, p1}, {phi, None, p2}, {Wm, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}] =
  I ee^2 g[LI[i[1]], LI[i[2]]] (
    +(I/(2 cw)) (1 + 2 dZe - dcw + 1/2 dZW + 1/2 dZZZ)
    + (I/(2 sw)) (1/2 dZAZ) );
feynruleMap[{{chi, None, p1}, {phim, None, p2}, {Wp, LI[i[1]], p3}, {Zb, LI[i[2]], p4}}] =
  I ee^2 g[LI[i[1]], LI[i[2]]] (
    -(I/(2 cw)) (1 + 2 dZe - dcw + 1/2 dZW + 1/2 dZZZ)
    - (I/(2 sw)) (1/2 dZAZ) );

(* W^{-+} A phi^{+-} chi *)
feynruleMap[{{chi, None, p1}, {phi, None, p2}, {Wm, LI[i[1]], p3}, {AA, LI[i[2]], p4}}] =
  I ee^2 g[LI[i[1]], LI[i[2]]] (
    +(I/(2 sw)) (1 + 2 dZe - dsw + 1/2 dZW + 1/2 dZAA)
    + (I/(2 cw)) (1/2 dZZA) );
feynruleMap[{{chi, None, p1}, {phim, None, p2}, {Wp, LI[i[1]], p3}, {AA, LI[i[2]], p4}}] =
  I ee^2 g[LI[i[1]], LI[i[2]]] (
    -(I/(2 sw)) (1 + 2 dZe - dsw + 1/2 dZW + 1/2 dZAA)
    - (I/(2 cw)) (1/2 dZZA) );


(* ===================================================================== *)
(*  FADDEEV-POPOV GHOSTS                                                  *)
(*                                                                        *)
(*  V Ubar U :  i e C k1_mu ,  k1 = momentum of the ANTI-ghost (p1).      *)
(*  S Ubar U :  i e C.                                                    *)
(*                                                                        *)
(*  Only same-type ghost pairs (ubar^a u^a) appear in the keys below;     *)
(*  most are therefore zero (the nonzero W-ghost couplings mix ghost      *)
(*  types and are not among these keys).                                  *)
(* ===================================================================== *)

(* --- V Ubar U : nonzero only for charged ghosts with A or Z --- *)
feynruleMap[{{ubp, None, p1}, {up, None, p2}, {AA, LI[i[1]], p3}}] =
  I ee (+1) p1[LI[i[1]]];
feynruleMap[{{ubm, None, p1}, {um, None, p2}, {AA, LI[i[1]], p3}}] =
  I ee (-1) p1[LI[i[1]]];
feynruleMap[{{ubp, None, p1}, {up, None, p2}, {Zb, LI[i[1]], p3}}] =
  I ee (-(cw/sw)) p1[LI[i[1]]];
feynruleMap[{{ubm, None, p1}, {um, None, p2}, {Zb, LI[i[1]], p3}}] =
  I ee (+(cw/sw)) p1[LI[i[1]]];

(* the remaining V Ubar U keys vanish *)
feynruleMap[{{uba, None, p1}, {ua, None, p2}, {AA, LI[i[1]], p3}}] = 0;
feynruleMap[{{uba, None, p1}, {ua, None, p2}, {Zb, LI[i[1]], p3}}] = 0;
feynruleMap[{{uba, None, p1}, {ua, None, p2}, {Wp, LI[i[1]], p3}}] = 0;
feynruleMap[{{uba, None, p1}, {ua, None, p2}, {Wm, LI[i[1]], p3}}] = 0;
feynruleMap[{{ubz, None, p1}, {uz, None, p2}, {AA, LI[i[1]], p3}}] = 0;
feynruleMap[{{ubz, None, p1}, {uz, None, p2}, {Zb, LI[i[1]], p3}}] = 0;
feynruleMap[{{ubz, None, p1}, {uz, None, p2}, {Wp, LI[i[1]], p3}}] = 0;
feynruleMap[{{ubz, None, p1}, {uz, None, p2}, {Wm, LI[i[1]], p3}}] = 0;
feynruleMap[{{ubp, None, p1}, {up, None, p2}, {Wp, LI[i[1]], p3}}] = 0;
feynruleMap[{{ubp, None, p1}, {up, None, p2}, {Wm, LI[i[1]], p3}}] = 0;
feynruleMap[{{ubm, None, p1}, {um, None, p2}, {Wp, LI[i[1]], p3}}] = 0;
feynruleMap[{{ubm, None, p1}, {um, None, p2}, {Wm, LI[i[1]], p3}}] = 0;

(* --- S Ubar U --- *)
(* H ubar^Z u^Z *)
feynruleMap[{{ubz, None, p1}, {uz, None, p2}, {HH, None, p3}}] =
  I ee ( -(1/(2 sw cw^2)) MW xiZ );
(* H ubar^+ u^+ , H ubar^- u^- *)
feynruleMap[{{ubp, None, p1}, {up, None, p2}, {HH, None, p3}}] =
  I ee ( -(1/(2 sw)) MW xiW );
feynruleMap[{{ubm, None, p1}, {um, None, p2}, {HH, None, p3}}] =
  I ee ( -(1/(2 sw)) MW xiW );

(* the remaining S Ubar U keys vanish *)
feynruleMap[{{ubz, None, p1}, {uz, None, p2}, {chi, None, p3}}] = 0;
feynruleMap[{{ubp, None, p1}, {up, None, p2}, {phi, None, p3}}] = 0;
feynruleMap[{{ubp, None, p1}, {up, None, p2}, {phim, None, p3}}] = 0;
feynruleMap[{{ubm, None, p1}, {um, None, p2}, {phi, None, p3}}] = 0;
feynruleMap[{{ubm, None, p1}, {um, None, p2}, {phim, None, p3}}] = 0;


(* ===================================================================== *)
(*  PROPAGATORS                                                          *)
(*                                                                       *)
(*  General 't Hooft (R_xi) gauge, all propagators diagonal.             *)
(*  Stored in `propagatorMap`, keyed in the same leg format as the       *)
(*  vertices: {{F1,idx1,p1},{F2,idx2,p2}}, distinct momentum per leg and  *)
(*  `None` where a field carries no index.  The line momentum is the     *)
(*  leg-1 incoming momentum p1 (p1 = -p2 by momentum conservation);       *)
(*  p1Sq = p1^2 (scalar invariant), eps = +0^+ (Feynman i*epsilon).       *)
(*  Masses:  M_A = 0,  M_chi = Sqrt[xiZ] MZ,  M_phi = Sqrt[xiW] MW,      *)
(*           M_{u^A} = 0, M_{u^Z} = Sqrt[xiZ] MZ, M_{u^pm} = Sqrt[xiW] MW.*)
(*  xiA is the photon gauge parameter (introduced here for completeness). *)
(* ===================================================================== *)

DeclareRealParam[xiA, Subscript["\[Xi]", "A"]];

ClearAll[propagatorMap];

(* p1-slash from the line momentum p1 (contracted dummy Lorentz i[5]).    *)
(* p1Sq is the SCALAR invariant p1^2; it must stay free of Lorentz        *)
(* indices, otherwise extractIndices cannot descend through the negative  *)
(* power of the propagator denominator (LagTools.wl:207 only handles      *)
(* positive integer powers).                                             *)
p1slash := NC[ga[LI[i[5]]]] p1[LI[i[5]]];
DeclareRealParam[p1Sq, Superscript["p", "2"]];

(* ---- gauge bosons :  V V  ------------------------------------------- *)
(*   -i g_mn /(k^2 - M^2 + i eps)                                        *)
(*   + i (1 - xi) k_m k_n / [ (k^2 - M^2 + i eps)(k^2 - xi M^2 + i eps) ] *)

(* photon  (M_A = 0) *)
propagatorMap[{{AA, LI[i[1]], p1}, {AA, LI[i[2]], p2}}] = (
    -I g[LI[i[1]], LI[i[2]]]/(p1Sq + I eps)
    + I (1 - xiA) p1[LI[i[1]]] p1[LI[i[2]]]/(p1Sq + I eps)^2 );

(* Z boson *)
propagatorMap[{{Zb, LI[i[1]], p1}, {Zb, LI[i[2]], p2}}] = (
    -I g[LI[i[1]], LI[i[2]]]/(p1Sq - MZ^2 + I eps)
    + I (1 - xiZ) p1[LI[i[1]]] p1[LI[i[2]]]/((p1Sq - MZ^2 + I eps) (p1Sq - xiZ MZ^2 + I eps)) );

(* W boson *)
propagatorMap[{{Wp, LI[i[1]], p1}, {Wm, LI[i[2]], p2}}] = (
    -I g[LI[i[1]], LI[i[2]]]/(p1Sq - MW^2 + I eps)
    + I (1 - xiW) p1[LI[i[1]]] p1[LI[i[2]]]/((p1Sq - MW^2 + I eps) (p1Sq - xiW MW^2 + I eps)) );

(* ---- scalars :  S S  --  i /(k^2 - M_S^2 + i eps) ------------------- *)
propagatorMap[{{HH, None, p1}, {HH, None, p2}}]    = I/(p1Sq - MH^2 + I eps);
propagatorMap[{{chi, None, p1}, {chi, None, p2}}]  = I/(p1Sq - xiZ MZ^2 + I eps);
propagatorMap[{{phi, None, p1}, {phim, None, p2}}] = I/(p1Sq - xiW MW^2 + I eps);

(* ---- Faddeev-Popov ghosts :  Ubar U  --  i /(k^2 - M_U^2 + i eps) --- *)
propagatorMap[{{uba, None, p1}, {ua, None, p2}}] = I/(p1Sq + I eps);          (* M_{u^A} = 0 *)
propagatorMap[{{ubz, None, p1}, {uz, None, p2}}] = I/(p1Sq - xiZ MZ^2 + I eps);
propagatorMap[{{ubp, None, p1}, {up, None, p2}}] = I/(p1Sq - xiW MW^2 + I eps);
propagatorMap[{{ubm, None, p1}, {um, None, p2}}] = I/(p1Sq - xiW MW^2 + I eps);

(* ---- fermions :  Fbar F  ------------------------------------------- *)
(*   i delta_ij (k-slash + m_{f,i}) / (k^2 - m_{f,i}^2 + i eps),         *)
(*   diagonal in flavour; numerator mass term is the diagonal matrix     *)
(*   Mdiag_ij, the scalar denominator uses the line's flavour mass.      *)
(*                                                                       *)
(*   CAUTION -- FI canonicalization is INVALID for these entries.        *)
(*   The denominator carries a flavour-indexed mass ml/mu/md[FI[i[2]]].  *)
(*   The leg indices i[2],i[3] are OPEN (external), but the open index   *)
(*   i[2] also appears once in the denominator mass, so the "appears     *)
(*   twice => dummy" heuristic (dummyIndices, LagTools.wl) would          *)
(*   misclassify i[2] as a contracted dummy and relabel it.  An indexed  *)
(*   mass in a denominator is a scalar invariant that can be neither     *)
(*   contracted nor FI-canonicalized.  When comparing these entries,     *)
(*   restrict canonicalization to the safe index types, e.g.             *)
(*       canonical[expr, {LI, GI}]                                       *)
(*   which still canonicalizes the LI dummy i[5] in p1slash (numerator,  *)
(*   safe) while skipping the FI fold.  There are no FI dummies to lose: *)
(*   propagator leg indices are always open.                            *)
propagatorMap[{{bar[el], FI[i[2]], p1}, {el, FI[i[3]], p2}}] =
  I (kd3[FI[i[2]], FI[i[3]]] p1slash + Mdiagl[FI[i[2]], FI[i[3]]])/
    (p1Sq - ml[FI[i[2]]]^2 + I eps);

propagatorMap[{{bar[uq], FI[i[2]], p1}, {uq, FI[i[3]], p2}}] =
  I (kd3[FI[i[2]], FI[i[3]]] p1slash + Mdiagu[FI[i[2]], FI[i[3]]])/
    (p1Sq - mu[FI[i[2]]]^2 + I eps);

propagatorMap[{{bar[dq], FI[i[2]], p1}, {dq, FI[i[3]], p2}}] =
  I (kd3[FI[i[2]], FI[i[3]]] p1slash + Mdiagd[FI[i[2]], FI[i[3]]])/
    (p1Sq - md[FI[i[2]]]^2 + I eps);

(* neutrino is massless *)
propagatorMap[{{bar[nu], FI[i[2]], p1}, {nu, FI[i[3]], p2}}] =
  I kd3[FI[i[2]], FI[i[3]]] p1slash/(p1Sq + I eps);
