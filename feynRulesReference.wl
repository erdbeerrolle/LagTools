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
(*   dml[FI[a]],dmu[FI[a]],dmd[FI[a]] : fermion mass CTs  delta m_{f,a}    *)
(*   dV[FI[a],FI[b]]           : CKM-matrix CT  delta V_{ab}               *)
(*   dZeL,dZeR,dZnuL,dZuL,dZuR,dZdL,dZdR  : field-renorm matrices [FI,FI]  *)

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
       kd3[FI[i[2]], FI[i[3]]] ( ml[FI[i[2]]] (1 + dZe - dsw - 1/2 dMW2/MW^2 + 1/2 dZH)
            + dml[FI[i[2]]] )
       + 1/2 ( ml[FI[i[2]]] dZeL[FI[i[2]], FI[i[3]]]
             + Conjugate[dZeR[FI[i[3]], FI[i[2]]]] ml[FI[i[3]]] ) )
  + NC[PR] (
       kd3[FI[i[2]], FI[i[3]]] ( ml[FI[i[2]]] (1 + dZe - dsw - 1/2 dMW2/MW^2 + 1/2 dZH)
            + dml[FI[i[2]]] )
       + 1/2 ( ml[FI[i[2]]] dZeR[FI[i[2]], FI[i[3]]]
             + Conjugate[dZeL[FI[i[3]], FI[i[2]]]] ml[FI[i[3]]] ) ) );

(* H ubar u *)
feynruleMap[{{bar[uq], FI[i[2]], p1}, {uq, FI[i[3]], p2}, {HH, None, p3}}] =
  I ee (-(1/(2 sw MW))) (
    NC[PL] (
       kd3[FI[i[2]], FI[i[3]]] ( mu[FI[i[2]]] (1 + dZe - dsw - 1/2 dMW2/MW^2 + 1/2 dZH)
            + dmu[FI[i[2]]] )
       + 1/2 ( mu[FI[i[2]]] dZuL[FI[i[2]], FI[i[3]]]
             + Conjugate[dZuR[FI[i[3]], FI[i[2]]]] mu[FI[i[3]]] ) )
  + NC[PR] (
       kd3[FI[i[2]], FI[i[3]]] ( mu[FI[i[2]]] (1 + dZe - dsw - 1/2 dMW2/MW^2 + 1/2 dZH)
            + dmu[FI[i[2]]] )
       + 1/2 ( mu[FI[i[2]]] dZuR[FI[i[2]], FI[i[3]]]
             + Conjugate[dZuL[FI[i[3]], FI[i[2]]]] mu[FI[i[3]]] ) ) );

(* H dbar d *)
feynruleMap[{{bar[dq], FI[i[2]], p1}, {dq, FI[i[3]], p2}, {HH, None, p3}}] =
  I ee (-(1/(2 sw MW))) (
    NC[PL] (
       kd3[FI[i[2]], FI[i[3]]] ( md[FI[i[2]]] (1 + dZe - dsw - 1/2 dMW2/MW^2 + 1/2 dZH)
            + dmd[FI[i[2]]] )
       + 1/2 ( md[FI[i[2]]] dZdL[FI[i[2]], FI[i[3]]]
             + Conjugate[dZdR[FI[i[3]], FI[i[2]]]] md[FI[i[3]]] ) )
  + NC[PR] (
       kd3[FI[i[2]], FI[i[3]]] ( md[FI[i[2]]] (1 + dZe - dsw - 1/2 dMW2/MW^2 + 1/2 dZH)
            + dmd[FI[i[2]]] )
       + 1/2 ( md[FI[i[2]]] dZdR[FI[i[2]], FI[i[3]]]
             + Conjugate[dZdL[FI[i[3]], FI[i[2]]]] md[FI[i[3]]] ) ) );

(* --- chi : CR = +i/(2s) 2 I3_f /MW [ delta_ij m_i(...) + 1/2(m_i dZR+dZL^d m_j) ] *)
(*           CL = -i/(2s) 2 I3_f /MW [ delta_ij m_i(...) + 1/2(m_i dZL+dZR^d m_j) ] *)
(*  bracket: 1+dZe-dsw+dm_i/m_i-1/2 dMW2/MW2  (no dZH).                   *)

(* chi ebar e *)
feynruleMap[{{bar[el], FI[i[2]], p1}, {el, FI[i[3]], p2}, {chi, None, p3}}] =
  I ee (
    NC[PL] ( -I/(2 sw) (2 I3f[el]) (1/MW) (
         kd3[FI[i[2]], FI[i[3]]] ( ml[FI[i[2]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
              + dml[FI[i[2]]] )
       + 1/2 ( ml[FI[i[2]]] dZeL[FI[i[2]], FI[i[3]]]
             + Conjugate[dZeR[FI[i[3]], FI[i[2]]]] ml[FI[i[3]]] ) ) )
  + NC[PR] ( +I/(2 sw) (2 I3f[el]) (1/MW) (
         kd3[FI[i[2]], FI[i[3]]] ( ml[FI[i[2]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
              + dml[FI[i[2]]] )
       + 1/2 ( ml[FI[i[2]]] dZeR[FI[i[2]], FI[i[3]]]
             + Conjugate[dZeL[FI[i[3]], FI[i[2]]]] ml[FI[i[3]]] ) ) ) );

(* chi ubar u *)
feynruleMap[{{bar[uq], FI[i[2]], p1}, {uq, FI[i[3]], p2}, {chi, None, p3}}] =
  I ee (
    NC[PL] ( -I/(2 sw) (2 I3f[uq]) (1/MW) (
         kd3[FI[i[2]], FI[i[3]]] ( mu[FI[i[2]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
              + dmu[FI[i[2]]] )
       + 1/2 ( mu[FI[i[2]]] dZuL[FI[i[2]], FI[i[3]]]
             + Conjugate[dZuR[FI[i[3]], FI[i[2]]]] mu[FI[i[3]]] ) ) )
  + NC[PR] ( +I/(2 sw) (2 I3f[uq]) (1/MW) (
         kd3[FI[i[2]], FI[i[3]]] ( mu[FI[i[2]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
              + dmu[FI[i[2]]] )
       + 1/2 ( mu[FI[i[2]]] dZuR[FI[i[2]], FI[i[3]]]
             + Conjugate[dZuL[FI[i[3]], FI[i[2]]]] mu[FI[i[3]]] ) ) ) );

(* chi dbar d *)
feynruleMap[{{bar[dq], FI[i[2]], p1}, {dq, FI[i[3]], p2}, {chi, None, p3}}] =
  I ee (
    NC[PL] ( -I/(2 sw) (2 I3f[dq]) (1/MW) (
         kd3[FI[i[2]], FI[i[3]]] ( md[FI[i[2]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
              + dmd[FI[i[2]]] )
       + 1/2 ( md[FI[i[2]]] dZdL[FI[i[2]], FI[i[3]]]
             + Conjugate[dZdR[FI[i[3]], FI[i[2]]]] md[FI[i[3]]] ) ) )
  + NC[PR] ( +I/(2 sw) (2 I3f[dq]) (1/MW) (
         kd3[FI[i[2]], FI[i[3]]] ( md[FI[i[2]]] (1 + dZe - dsw - 1/2 dMW2/MW^2)
              + dmd[FI[i[2]]] )
       + 1/2 ( md[FI[i[2]]] dZdR[FI[i[2]], FI[i[3]]]
             + Conjugate[dZdL[FI[i[3]], FI[i[2]]]] md[FI[i[3]]] ) ) ) );


(* ===================================================================== *)
(*  CHARGED GOLDSTONE - FERMION - FERMION   phi Fbar F                    *)
(* ===================================================================== *)

(* phi^+ ubar_i d_j   (i=up=FI[i[2]], j=down=FI[i[3]]) *)
feynruleMap[{{bar[uq], FI[i[2]], p1}, {dq, FI[i[3]], p2}, {phi, None, p3}}] =
  I ee (
    NC[PL] ( 1/(Sqrt[2] sw MW) (
         (mu[FI[i[2]]] (1 + dZe - dsw - 1/2 dMW2/MW^2) + dmu[FI[i[2]]]) V[FI[i[2]], FI[i[3]]]
       + mu[FI[i[2]]] dV[FI[i[2]], FI[i[3]]]
       + 1/2 ( Conjugate[dZuR[FI[i[4]], FI[i[2]]]] mu[FI[i[4]]] V[FI[i[4]], FI[i[3]]]
             + mu[FI[i[2]]] V[FI[i[2]], FI[i[4]]] dZdL[FI[i[4]], FI[i[3]]] ) ) )
  + NC[PR] ( -(1/(Sqrt[2] sw MW)) (
         V[FI[i[2]], FI[i[3]]] (md[FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2) + dmd[FI[i[3]]])
       + dV[FI[i[2]], FI[i[3]]] md[FI[i[3]]]
       + 1/2 ( Conjugate[dZuL[FI[i[4]], FI[i[2]]]] V[FI[i[4]], FI[i[3]]] md[FI[i[3]]]
             + V[FI[i[2]], FI[i[4]]] md[FI[i[4]]] dZdR[FI[i[4]], FI[i[3]]] ) ) ) );

(* phi^- dbar_j u_i   (j=down=FI[i[2]], i=up=FI[i[3]]) *)
feynruleMap[{{bar[dq], FI[i[2]], p1}, {uq, FI[i[3]], p2}, {phim, None, p3}}] =
  I ee (
    NC[PL] ( -(1/(Sqrt[2] sw MW)) (
         (md[FI[i[2]]] (1 + dZe - dsw - 1/2 dMW2/MW^2) + dmd[FI[i[2]]]) Conjugate[V[FI[i[3]], FI[i[2]]]]
       + md[FI[i[2]]] Conjugate[dV[FI[i[3]], FI[i[2]]]]
       + 1/2 ( Conjugate[dZdR[FI[i[4]], FI[i[2]]]] md[FI[i[4]]] Conjugate[V[FI[i[3]], FI[i[4]]]]
             + md[FI[i[2]]] Conjugate[V[FI[i[4]], FI[i[2]]]] dZuL[FI[i[4]], FI[i[3]]] ) ) )
  + NC[PR] ( 1/(Sqrt[2] sw MW) (
         Conjugate[V[FI[i[3]], FI[i[2]]]] (mu[FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2) + dmu[FI[i[3]]])
       + Conjugate[dV[FI[i[3]], FI[i[2]]]] mu[FI[i[3]]]
       + 1/2 ( Conjugate[dZdL[FI[i[4]], FI[i[2]]]] Conjugate[V[FI[i[3]], FI[i[4]]]] mu[FI[i[3]]]
             + Conjugate[V[FI[i[4]], FI[i[2]]]] mu[FI[i[4]]] dZuR[FI[i[4]], FI[i[3]]] ) ) ) );

(* phi^+ nubar_i l_j   (lepton, V -> delta, neutrino massless => CL = 0) *)
feynruleMap[{{bar[nu], FI[i[2]], p1}, {el, FI[i[3]], p2}, {phi, None, p3}}] =
  I ee NC[PR] ( -(1/(Sqrt[2] sw MW)) (
       kd3[FI[i[2]], FI[i[3]]] (ml[FI[i[3]]] (1 + dZe - dsw - 1/2 dMW2/MW^2) + dml[FI[i[3]]])
     + 1/2 ( Conjugate[dZnuL[FI[i[3]], FI[i[2]]]] ml[FI[i[3]]]
           + ml[FI[i[2]]] dZeR[FI[i[2]], FI[i[3]]] ) ) );

(* phi^- lbar_j nu_i   (CR = 0) *)
feynruleMap[{{bar[el], FI[i[2]], p1}, {nu, FI[i[3]], p2}, {phim, None, p3}}] =
  I ee NC[PL] ( -(1/(Sqrt[2] sw MW)) (
       kd3[FI[i[2]], FI[i[3]]] (ml[FI[i[2]]] (1 + dZe - dsw - 1/2 dMW2/MW^2) + dml[FI[i[2]]])
     + 1/2 ( Conjugate[dZeR[FI[i[3]], FI[i[2]]]] ml[FI[i[3]]]
           + ml[FI[i[2]]] dZnuL[FI[i[2]], FI[i[3]]] ) ) );


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
