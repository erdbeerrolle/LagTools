(* ::Package:: *)

(* ===================================================================== *)
(*  Reference for EWSM Feynman rules, transcribed from                   *)
(*  Denner, Dittmaier EW review.                                         *)
(*  ewsmFeynRulesCorrect.tex (Denner/Dittmaier conventions).             *)
(* ===================================================================== *)

(* shorthand replacement rules for sw and cw counterterms *)
expandSC = {
  dsw -> -(cw^2/(2 sw^2)) (dMW2/MW^2 - dMZ2/MZ^2),    (* delta s / s *)
  dcw ->  (1/2)            (dMW2/MW^2 - dMZ2/MZ^2)    (* delta c / c *)
};

(* weak isospin T^3 of the fermions *)
I3f[nu] = 1/2;  I3f[el] = -1/2;  I3f[uq] = 1/2;  I3f[dq] = -1/2;

(* Z chiral couplings g_f^+- and their counterterms *)
gpf[f_] := -(sw/cw) ElectricCharge[f];
gmf[f_] := (I3f[f] - sw^2 ElectricCharge[f])/(sw cw);
dgpf[f_] := -(sw/cw) ElectricCharge[f] (dZe + (1/cw^2) dsw);
dgmf[f_] := (I3f[f]/(sw cw)) (dZe + ((sw^2 - cw^2)/cw^2) dsw) + dgpf[f];

ClearAll[feynruleMap];

(* ===================================================================== *)
(*  TRIPLE GAUGE   VVV                                                    *)
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
(*  SCALAR - VECTOR - VECTOR   S V V                                     *)
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

(* H A Z *)
feynruleMap[{{HH, None, p1}, {AA, LI[i[1]], p2}, {Zb, LI[i[2]], p3}}] =
  I ee g[LI[i[1]], LI[i[2]]] *
    MW (1/(sw cw^2)) (1/2 dZZA);

(* phi^+ W^- A *)
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
(*  VECTOR - SCALAR - SCALAR   V S S                                     *)
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
(*  SCALAR SELF-COUPLING   S S S                                         *)
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
(*  VECTOR - FERMION - FERMION   V Fbar F                                *)
(* ===================================================================== *)

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
(*  CHARGED-CURRENT   W Fbar F                                           *)
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
(*  SCALAR - FERMION - FERMION   S Fbar F                                *)
(* ===================================================================== *)

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
(*  QUARTIC GAUGE   V V V V                                              *)
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
(*  QUARTIC SCALAR   S S S S                                             *)
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
(*  VECTOR VECTOR SCALAR SCALAR   V V S S :                              *)
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
(*  FADDEEV-POPOV GHOSTS                                                 *)
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
(* ===================================================================== *)

DeclareRealParam[xiA, Subscript["\[Xi]", "A"]];

ClearAll[propagatorMap];

p1slash := NC[ga[LI[i[5]]]] p1[LI[i[5]]];
Sq /: Conjugate[Sq[x_]] := Sq[x];
Format[Sq[x_]] := Superscript[x, 2];


(* photon  (M_A = 0) *)
propagatorMap[{{AA, LI[i[1]], p1}, {AA, LI[i[2]], p2}}] = (
    -I g[LI[i[1]], LI[i[2]]]/(Sq[p1] + I eps)
    + I (1 - xiA) p1[LI[i[1]]] p1[LI[i[2]]]/(Sq[p1] + I eps)^2 );

(* Z boson *)
propagatorMap[{{Zb, LI[i[1]], p1}, {Zb, LI[i[2]], p2}}] = (
    -I g[LI[i[1]], LI[i[2]]]/(Sq[p1] - MZ^2 + I eps)
    + I (1 - xiZ) p1[LI[i[1]]] p1[LI[i[2]]]/((Sq[p1] - MZ^2 + I eps) (Sq[p1] - xiZ MZ^2 + I eps)) );

(* W boson *)
propagatorMap[{{Wp, LI[i[1]], p1}, {Wm, LI[i[2]], p2}}] = (
    -I g[LI[i[1]], LI[i[2]]]/(Sq[p1] - MW^2 + I eps)
    + I (1 - xiW) p1[LI[i[1]]] p1[LI[i[2]]]/((Sq[p1] - MW^2 + I eps) (Sq[p1] - xiW MW^2 + I eps)) );

(* ---- scalars :  S S  --  i /(k^2 - M_S^2 + i eps) ------------------- *)
propagatorMap[{{HH, None, p1}, {HH, None, p2}}]    = I/(Sq[p1] - MH^2 + I eps);
propagatorMap[{{chi, None, p1}, {chi, None, p2}}]  = I/(Sq[p1] - xiZ MZ^2 + I eps);
propagatorMap[{{phi, None, p1}, {phim, None, p2}}] = I/(Sq[p1] - xiW MW^2 + I eps);

(* ---- Faddeev-Popov ghosts :  Ubar U  --  i /(k^2 - M_U^2 + i eps) --- *)
propagatorMap[{{uba, None, p1}, {ua, None, p2}}] = I/(Sq[p1] + I eps);          (* M_{u^A} = 0 *)
propagatorMap[{{ubz, None, p1}, {uz, None, p2}}] = I/(Sq[p1] - xiZ MZ^2 + I eps);
propagatorMap[{{ubp, None, p1}, {up, None, p2}}] = I/(Sq[p1] - xiW MW^2 + I eps);
propagatorMap[{{ubm, None, p1}, {um, None, p2}}] = I/(Sq[p1] - xiW MW^2 + I eps);

(* ---- fermions :  Fbar F  -------------------------------------------- *)
(*   CAUTION -- FI canonicalization is invalid for these entries.        *)
(*   The denominator carries a flavour-indexed mass ml/mu/md[FI[i[2]]].  *)

(* the momentum p in the reference is p2 = -p1 *)
propagatorMap[{{bar[el], FI[i[2]], p1}, {el, FI[i[3]], p2}}] =
  I (-kd3[FI[i[2]], FI[i[3]]] p1slash + Mdiagl[FI[i[2]], FI[i[3]]])/
    (Sq[p1] - ml[FI[i[2]]]^2 + I eps);

propagatorMap[{{bar[uq], FI[i[2]], p1}, {uq, FI[i[3]], p2}}] =
  I (-kd3[FI[i[2]], FI[i[3]]] p1slash + Mdiagu[FI[i[2]], FI[i[3]]])/
    (Sq[p1] - mu[FI[i[2]]]^2 + I eps);

propagatorMap[{{bar[dq], FI[i[2]], p1}, {dq, FI[i[3]], p2}}] =
  I (-kd3[FI[i[2]], FI[i[3]]] p1slash + Mdiagd[FI[i[2]], FI[i[3]]])/
    (Sq[p1] - md[FI[i[2]]]^2 + I eps);

(* Neutrino is massless left-handed; P_L in propagator breaks the computation *)
(* Solution would be to use PL nu = nu and drop the PL. not implemented       *)
(*propagatorMap[{{bar[nu], FI[i[2]], p1}, {nu, FI[i[3]], p2}}] =
  I kd3[FI[i[2]], FI[i[3]]] p1slash/(Sq[p1] + I eps);*)


(* ===================================================================== *)
(*  TWO-POINT COUNTERTERMS                                               *)
(*  Transcribed from ewreview_appfr.tex, lines 264-356.                  *)
(*                                                                       *)
(*  Momentum convention (single external momentum k):                    *)
(*   - bosonic legs use  k = p1  (as for the tree-level propagators);    *)
(*   - fermionic legs use k = p2 = -p1 (as for the fermion propagator,   *)
(*     hence the sign in front of p1slash below).                        *)
(*  The generic tadpole dt of the review is written here as dtFJ (its    *)
(*  value in the FJ tadpole scheme; it contributes in both schemes).     *)
(* ===================================================================== *)

(* ---- tadpole :  one-point Higgs vertex,  i dt --------------------- *)
feynruleMap[{{HH, None, p1}}] = I dtFJ; (* not really dtFJ, this is universal -> introduce a third parameter? *)

(* ---- V V counterterm :  i[(-g_mn k^2 + k_m k_n) C1 + g_mn C2] ------- *)

(* W+ W- *)
feynruleMap[{{Wp, LI[i[1]], p1}, {Wm, LI[i[2]], p2}}] =
  I ( (-g[LI[i[1]], LI[i[2]]] p1[LI[i[3]]] p1[LI[i[3]]] + p1[LI[i[1]]] p1[LI[i[2]]]) dZW
      + g[LI[i[1]], LI[i[2]]] (dZW MW^2 + dMW2 - ee MW/(sw MH^2) dtFJ) );

(* Z Z *)
feynruleMap[{{Zb, LI[i[1]], p1}, {Zb, LI[i[2]], p2}}] =
  I ( (-g[LI[i[1]], LI[i[2]]] p1[LI[i[3]]] p1[LI[i[3]]] + p1[LI[i[1]]] p1[LI[i[2]]]) dZZZ
      + g[LI[i[1]], LI[i[2]]] (dZZZ MZ^2 + dMZ2 - ee MZ/(sw cw MH^2) dtFJ) );

(* A Z *)
feynruleMap[{{AA, LI[i[1]], p1}, {Zb, LI[i[2]], p2}}] =
  I ( (-g[LI[i[1]], LI[i[2]]] p1[LI[i[3]]] p1[LI[i[3]]] + p1[LI[i[1]]] p1[LI[i[2]]]) (1/2 dZAZ + 1/2 dZZA)
      + g[LI[i[1]], LI[i[2]]] (1/2 dZZA MZ^2) );

(* A A *)
feynruleMap[{{AA, LI[i[1]], p1}, {AA, LI[i[2]], p2}}] =
  I ( (-g[LI[i[1]], LI[i[2]]] p1[LI[i[3]]] p1[LI[i[3]]] + p1[LI[i[1]]] p1[LI[i[2]]]) dZAA );

(* ---- V S counterterm :  i k_m C ------------------------------------ *)

(* W+ phi- *)
feynruleMap[{{Wp, LI[i[1]], p1}, {phim, None, p2}}] =
  I p1[LI[i[1]]] (
     +(1/2) (dZW + dMW2/MW^2 - ee/(sw MH^2 MW) dtFJ) MW );

(* W- phi+ *)
feynruleMap[{{Wm, LI[i[1]], p1}, {phi, None, p2}}] =
  I p1[LI[i[1]]] (
     -(1/2) (dZW + dMW2/MW^2 - ee/(sw MH^2 MW) dtFJ) MW );

(* Z chi *)
feynruleMap[{{Zb, LI[i[1]], p1}, {chi, None, p2}}] =
  I p1[LI[i[1]]] (
     I (1/2) (dZZZ + dMZ2/MZ^2 - ee/(sw MH^2 MW) dtFJ) MZ );

(* A chi *)
feynruleMap[{{AA, LI[i[1]], p1}, {chi, None, p2}}] =
  I p1[LI[i[1]]] (
     I (1/2) dZZA MZ );

(* ---- S S counterterm :  i[C1 k^2 - C2] ----------------------------- *)
(* k^2 written as p1[LI[i[1]]] p1[LI[i[1]]] (not Sq[p1]) so that       *)
(* canonical can match the dummy LI index against the computed result.   *)

(* H H *)
feynruleMap[{{HH, None, p1}, {HH, None, p2}}] =
  I ( dZH p1[LI[i[1]]] p1[LI[i[1]]] - (dZH MH^2 + dMH2 - 3 ee/(2 sw MW) dtFJ) );

(* chi chi *)
feynruleMap[{{chi, None, p1}, {chi, None, p2}}] =
  I ( - (- ee/(2 sw MW) dtFJ) );

(* phi phi *)
feynruleMap[{{phi, None, p1}, {phim, None, p2}}] =
  I ( - (- ee/(2 sw MW) dtFJ) );

(* ---- F Fbar counterterm : ------------------------------------------ *)
(*   i[ CL k-slash w_- + CR k-slash w_+ - CS^- w_- - CS^+ w_+ ]          *)
(*   with w_- = PL, w_+ = PR, and k = p2 = -p1 (fermion propagator       *)
(*   convention), hence the leading minus on the k-slash terms.          *)

ffbarCT[dZL_, dZR_, Mdiag_, dMdiag_] := Module[{cL, cR, cSm, cSp},
  cL  = (1/2) (dZL[FI[i[2]], FI[i[3]]] + Conjugate[dZL[FI[i[3]], FI[i[2]]]]);
  cR  = (1/2) (dZR[FI[i[2]], FI[i[3]]] + Conjugate[dZR[FI[i[3]], FI[i[2]]]]);
  cSm = (1/2) ( Mdiag[FI[i[2]], FI[i[4]]] dZL[FI[i[4]], FI[i[3]]]
              + Conjugate[dZR[FI[i[4]], FI[i[2]]]] Mdiag[FI[i[4]], FI[i[3]]] )
        + dMdiag[FI[i[2]], FI[i[3]]]
        - Mdiag[FI[i[2]], FI[i[3]]] ee/(2 sw MH^2 MW) dtFJ;
  cSp = (1/2) ( Mdiag[FI[i[2]], FI[i[4]]] dZR[FI[i[4]], FI[i[3]]]
              + Conjugate[dZL[FI[i[4]], FI[i[2]]]] Mdiag[FI[i[4]], FI[i[3]]] )
        + dMdiag[FI[i[2]], FI[i[3]]]
        - Mdiag[FI[i[2]], FI[i[3]]] ee/(2 sw MH^2 MW) dtFJ;
  I ( - cL NC[ga[LI[i[5]]], PL] p1[LI[i[5]]]
      - cR NC[ga[LI[i[5]]], PR] p1[LI[i[5]]]
      - cSm NC[PL] - cSp NC[PR] )
  ];

(* e ebar *)
feynruleMap[{{bar[el], FI[i[2]], p1}, {el, FI[i[3]], p2}}] =
  ffbarCT[dZeL, dZeR, Mdiagl, dMdiagl];

(* u ubar *)
feynruleMap[{{bar[uq], FI[i[2]], p1}, {uq, FI[i[3]], p2}}] =
  ffbarCT[dZuL, dZuR, Mdiagu, dMdiagu];

(* d dbar *)
feynruleMap[{{bar[dq], FI[i[2]], p1}, {dq, FI[i[3]], p2}}] =
  ffbarCT[dZdL, dZdR, Mdiagd, dMdiagd];

(* Neutrino two-point counterterm omitted, as for the neutrino propagator. *)


(* ======================================================================= *)
(* Helpers for Feynman rule comparison                                     *)
(* ======================================================================= *)
GetLegsLst[map_] := Module[{dv = DownValues[map]},
   dv[[#, 1, 1, 1]] & /@ Range@Length@dv];

feynRuleLegsLst = GetLegsLst[feynruleMap];
propagatorLegsLst = GetLegsLst[propagatorMap];