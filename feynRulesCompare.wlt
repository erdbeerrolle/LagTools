(* ====================================================================== *)
(*  Regression suite that checks every Feynman rule computed from the     *)
(*  EWSM Lagrangian against the literature reference.                     *)
(* ====================================================================== *)

Get[FileNameJoin[{DirectoryName[$TestFileName], "EWSMLagrangian.wl"}]];
Get[FileNameJoin[{DirectoryName[$TestFileName], "feynRulesReference.wl"}]];

(* ---- comparison helpers (ported from feynRulesView.nb) --------------- *)

normalizationRpl = {
   MZ -> MW/cw, 
   PR -> 1 - PL, 
   ElectricCharge[el] -> -1,
   ElectricCharge[nu] -> 0, 
   ElectricCharge[uq] -> 2/3,
   ElectricCharge[dq] -> -1/3, 
   eps -> 0
   };

tadpoleCtZero = {dtFJ -> 0, dtPR -> 0};

momentumCons[legs_] := Module[{a, momenta},
   momenta = (#[[3]] &) /@ legs;
   {First[momenta][a_] :> -Total[(#[a] &) /@ Rest[momenta]],
    Sq[First[momenta]] -> Sq[Total[Rest[momenta]]]}];

compareDiff[comp_, legs_, map_, canIdc_ : {LI, FI, GI}, postFn_ : (#&)] :=      
   Module[{ref, normRepl},
      ref = map[legs] /. Join[expandSC, tadpoleCtZero];
      normRepl = Join[normalizationRpl, momentumCons[legs]];
      FullSimplify @ postFn @ canonical[ref - comp //.normRepl, canIdc]
   ];

(* readable, unique TestID from the leg field symbols *)
fieldTag[bar[f_]] := "bar" <> ToString[f];
fieldTag[f_]      := ToString[f];
legLabel[legs_]   := StringRiffle[fieldTag /@ (First /@ legs), "-"];

(*ghostFields = {up, um, uz, ua, ubp, ubm, ubz, uba};
noGhostQ[legs_] := FreeQ[legs, Alternatives @@ ghostFields];*)

(* ====================================================================== *)
(*  Renormalized 3/4-point vertices                                       *)
(* ====================================================================== *)

Do[
   With[{lg = k},
      VerificationTest[
         compareDiff[vertexFct[Lren, lg], lg, feynruleMap],
         0,
         TestID -> "vertex-" <> legLabel[lg]]],
   {k, Select[feynRuleLegsLst, Length[#] >= 3 &]}];

(* ====================================================================== *)
(*  Propagators (unrenormalized)                                          *)
(* ====================================================================== *)

Do[
   With[{lg = k},
      VerificationTest[
         compareDiff[
            Propagator[Ltotal, lg], 
            lg, 
            propagatorMap, 
            {LI}, 
            ExplMassMat
         ],
         0,
         TestID -> "prop-" <> legLabel[lg]]],
   {k, propagatorLegsLst}];

(* ====================================================================== *)
(*  2-point counterterms                                                  *)
(* ====================================================================== *)

Do[
   With[{lg = k},
      VerificationTest[
         compareDiff[vertexCt[Lren, lg], lg, feynruleMap],
         0,
         TestID -> "ct-" <> legLabel[lg]]],
   {k, Select[feynRuleLegsLst, Length[#] == 2 (*&& noGhostQ[#]*) &]}];
