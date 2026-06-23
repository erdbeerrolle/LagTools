#!/usr/bin/env wolframscript
(* ======================================================================
   example_feynman.wls  --  Demo: SM Lagrangian pieces + Feynman rules
   Run via:  wolframscript -file scripts/example_feynman.wls
   or:       make example
   ====================================================================== *)

Get[FileNameJoin[{DirectoryName[$InputFileName], "..", "EWSMLagrangian.wl"}]];

(* ------------------------------------------------------------------ *)
(*  Helper: pretty-print a labelled result                            *)
(* ------------------------------------------------------------------ *)
show[label_, expr_] := (
  Print[""];
  Print["=== " <> label <> " ==="];
  Print[expr]
);

(* ================================================================== *)
(*  1. Display Lagrangian pieces                                       *)
(* ================================================================== *)

show["Higgs potential (gauge basis)", LHiggsPot];

show["Higgs doublet Phi", Phi];
show["Charge-conjugate doublet Phi^c", PhiC];

show["Higgs kinetic term L_H(mu=1) [gauge basis]", LHiggsKin[1]];

show["Gauge kinetic term [gauge basis, schematic]",
     "LgaugeSym (defined, not expanded here for brevity)"];

(* Apply physical-basis substitution to the Higgs kinetic term *)
LHiggsKinPhys = Expand[Sum[LHiggsKin[mu], {mu, 1, 4}] /. toPhysical];
show["Higgs kinetic term [physical basis, summed over mu]", LHiggsKinPhys];

(* ================================================================== *)
(*  2. Gauge-fixing and ghost Lagrangians                             *)
(* ================================================================== *)

show["Gauge-fixing Lagrangian L_fix", Lfix];
show["Ghost Lagrangian L_ghost (auto-derived)", Lghost];

(* ================================================================== *)
(*  3. Example Feynman rules                                          *)
(* ================================================================== *)

(* Physical Lagrangian (Higgs sector only for speed) *)
LphysHiggs = Expand[(LHiggsPot + Sum[LHiggsKin[mu], {mu,1,4}]) /. toPhysical /. paramSubs];

(* 3a. HHH coupling: third functional derivative w.r.t. HH *)
show["HHH vertex (from Higgs potential)",
  feynmanRule[LHiggsPot /. paramSubs,
    {{HH, None, p1}, {HH, None, p2}, {HH, None, p3}}]
];

(* 3b. H chi chi vertex *)
show["H chi chi vertex",
  feynmanRule[LHiggsPot /. paramSubs,
    {{HH, None, p1}, {chi, None, p2}, {chi, None, p3}}]
];

(* 3c. H phi^+ phi^- vertex *)
show["H phi^+ phi^- vertex",
  feynmanRule[LHiggsPot /. paramSubs,
    {{HH, None, p1}, {phi, None, p2}, {phim, None, p3}}]
];

(* 3d. Ghost propagator numerator from ghost kinetic term:
       extract coefficient of -ubp ** d^2 up from Lghost *)
show["Ghost Lagrangian kinetic+mass terms (coefficient of ubp**uz etc.)",
  "See Lghost above; mass poles at p^2 = xiW MW^2 and p^2 = xiZ MZ^2"];

Print[""];
Print["Done."];
