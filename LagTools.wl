(* ::Package:: *)

If[TrueQ[$LagToolsLoaded], Return[]];
$LagToolsLoaded = True;

(*---- Dirac matrices ----*)
$diracMat = {ga, ga0, ga5, PL, PR};
diracMatQ[m_] := MemberQ[$diracMat,m] || MemberQ[$diracMat,Head[m]];

$indices = {LI, GI, FI};

(*---- Field declarations ----*)
DeclareFermion[f_Symbol] := (fermionQ[f] = True; f);
DeclareFermion[f_Symbol,  lbl_] := (DeclareFermion[f]; Format[f] = lbl; f);

DeclareGrassmann[f_Symbol] := (grassmannQ[f] = True; f);
DeclareGrassmann[f_Symbol,lbl_] := (DeclareGrassmann[f]; Format[f] = lbl; f);

DeclareBoson[h_Symbol] := (bosonQ[h] = True; h);
DeclareBoson[h_Symbol, lbl_] := (DeclareBoson[h]; Format[h] = lbl; h);

SetConjugate[h_Symbol, hc_Symbol] := (
  h /: Conjugate[h] = hc;
  h /: Conjugate[h[args__]] := hc[args];
);

(* Real fields: Conjugate[h] = h, electric charge = 0 *)
DeclareRealBoson[h_Symbol] := (DeclareBoson[h]; SetConjugate[h, h]; ElectricCharge[h] = 0; h);
DeclareRealBoson[h_Symbol, lbl_] := (DeclareRealBoson[h]; Format[h] = lbl; h);

(* Complex-conjugate pairs: Conjugate[hp] = hm, charges +1/-1 by convention *)
DeclareComplexBoson[hp_Symbol, hm_Symbol] := (
  DeclareBoson[hp]; DeclareBoson[hm];
  SetConjugate[hp, hm]; SetConjugate[hm, hp];
  ElectricCharge[hp] = 1;
  ElectricCharge[hm] = -1;
  {hp, hm}
);
DeclareComplexBoson[hp_Symbol, hm_Symbol, lbl_] := (
  DeclareComplexBoson[hp, hm];
  Format[hp] = Superscript[lbl, "+"]; Format[hm] = Superscript[lbl, "-"];
  {hp, hm}
);

(*---- Parameter declarations ----*)
DeclareComplexParam[p_Symbol]       := p;
DeclareComplexParam[p_Symbol, lbl_] := (Format[p] = lbl; p);
DeclareRealParam[p_Symbol]       := (DeclareComplexParam[p]; SetConjugate[p, p]; p);
DeclareRealParam[p_Symbol, lbl_] := (DeclareRealParam[p]; Format[p] = lbl; p);

(* Local (space-time dependent) gauge parameters: real parameters that are
   NOT space-time independent, so they survive derivatives d[mu][.] (needed
   e.g. to derive the Faddeev-Popov ghost Lagrangian). *)
DeclareLocalGaugeParam[p_Symbol]       := (DeclareRealParam[p]; gaugeParamQ[p] = True; p);
DeclareLocalGaugeParam[p_Symbol, lbl_] := (DeclareLocalGaugeParam[p]; Format[p] = lbl; p);

(*----defaults----*)
bosonQ[_]       := False;
fermionQ[_]     := False;
grassmannQ[_]   := False;
gaugeParamQ[_]  := False;

(* lift all predicates through indexed fields and bar *)
With[{preds={bosonQ, fermionQ, grassmannQ, gaugeParamQ}},
  Scan[(#[h_[___]] /; h=!=bar := #[h])&, preds];
  Scan[(#[bar[f_]] := #[f])&, preds];
];

(* ---- composite predicates ---- *)
fieldQ[x_] := bosonQ[x] || fermionQ[x] || grassmannQ[x];
oddQ[x_]   := fermionQ[x] || grassmannQ[x];

(* FreeQ descends into ElectricCharge[f] and sees f, so erase metadata wrappers before scanning *)
$metadataP = _ElectricCharge | _Hypercharge;
stripMeta[x_] := x /. $metadataP :> 1;

(*---- composite predicates with deep-scan ----*)
commutingQ[x_]   := FreeQ[stripMeta[x], _?oddQ | _?diracMatQ];
STindepQ[x_]     := FreeQ[stripMeta[x], _?fieldQ | _?gaugeParamQ];
diracScalarQ[x_] := FreeQ[stripMeta[x], _?fermionQ | _?diracMatQ];
su2MatQ[_]        := False;
su2MatQ[sigma[_]] := True;
(* A Col is an SU(2) doublet/multiplet vector, never an SU(2) scalar, even
   after its symbolic head has been expanded to explicit components. *)
su2ScalarQ[x_] := FreeQ[x, _?su2MatQ | _?su2DoubletQ | _Col];
scalarQ[x_] := diracScalarQ[x] && su2ScalarQ[x];

properIndexStructureQ[inds__] := And @@ (MemberQ[$indices, Head[#]] & /@ {inds});

(* True when the expression carries no index slots of any type *)
indexFreeQ[e_] := FreeQ[e, Alternatives @@ (Blank /@ $indices)];

(* ---- metric ----   g symmetric;  g_{mu}^{mu} = D = 4 *)
SetAttributes[g, Orderless];
g[LI[i[a_]], LI[i[a_]]] /; IntegerQ[a] := 4;
(* full double contraction g_{mu nu} g^{mu nu} = D = 4.  A squared metric    *)
(* with distinct indices is always a complete contraction (a free index is   *)
(* never squared), so this collapse -- which `contract` misses because the   *)
(* two metrics auto-combine into a Power -- is unambiguous.                  *)
g /: g[LI[i[a_]], LI[i[b_]]]^2 := 4 /; a =!= b;

(* ---- Kronecker delta for flavour indices and su2 gauge indices ---- delta symmetric;  delta_{i}^{i} = 3 *)
SetAttributes[kd3, Orderless];
kd3[h_[i[a_]], h_[i[a_]]] /; IntegerQ[a] && MemberQ[{FI, GI}, h] := 3;
kd3[h_[a_],h_[a_]] /; IntegerQ[a] && MemberQ[{FI, GI}, h] := 1;

(* ---- SU(2) Levi-Civita / structure constant: eps3[a,b,c] = epsilon^{abc} ---- *)
eps3[GI[a_Integer], GI[b_Integer], GI[c_Integer]] := Signature[{a, b, c}];

(* ---- Pauli matrices sigma[1,2,3] as explicit 2x2 matrices ---- *)
sigma[GI[1]] = {{0, 1}, {1, 0}};
sigma[GI[2]] = {{0, -I}, {I, 0}};
sigma[GI[3]] = {{1, 0}, {0, -1}};

(* Charge conjugation for an SU(2) doublet *)
ChargeConj[phi_List] := I * sigma[GI[2]] . Conjugate[phi];
ChargeConj[col_Col]  := Col @@ (I * sigma[GI[2]] . Conjugate[List @@ col]);


(* ---- noncommutative product **  (boson/scalar factors are pulled out) ---- *)
NC[] := 1;
NC[x___, p_Plus, y___]           := NC[x, #, y]& /@ p;
NC[x___, c_?commutingQ, y___]    := c * NC[x, y];
NC[x___, c_?commutingQ*d_, y___] := c * NC[x, d, y];
NC[x___, NC[z___], y___]         := NC[x, z, y];
NC[x___, l_List, y___]           := NC[x, #, y]& /@ l;
(*NC[x___, col_Col, y___]          := Col @@ (NC[x, #, y]& /@ List@@col);*)
NC[x___, ga0, ga0, y___] := NC[x, y];

(* ** delegates to NC *)
Unprotect[NonCommutativeMultiply];
ClearAll[NonCommutativeMultiply];
NonCommutativeMultiply[args___]:=NC[args];
Protect[NonCommutativeMultiply];

(* ---- Dirac conjugate bar: linear, antilinear in scalars ---- *)
bar[0] = 0;
bar[a_Plus] := bar /@ a;
bar[a_List]      := bar /@ a;
bar[col_Col]     := Col @@ (bar /@ List@@col);
bar[c_ * x_] := Conjugate[c] bar[x] /; diracScalarQ[c];
bar[PL ** f_] := bar[f] ** PR;
bar[PR ** f_] := bar[f] ** PL;

(* ---- Hermitian conjugate (†) ---- *)
(*  CT reverses the NC chain and applies † to each factor;             *)
(*  ga0 factors cancel pairwise via the NC rule ga0.ga0 = 1            *)
Unprotect[ConjugateTranspose];
ConjugateTranspose[sigma[a___]] := sigma[a];  (* Pauli matrices are Hermitian *)
ConjugateTranspose[x_?scalarQ] := Conjugate[x];
ConjugateTranspose[ga[mu_]]     := NC[ga0, ga[mu], ga0];
ConjugateTranspose[ga5]         := NC[-ga0, ga5, ga0];
ConjugateTranspose[ga0]         := ga0;
ConjugateTranspose[PL]          := NC[ga0, PR, ga0];
ConjugateTranspose[PR]          := NC[ga0, PL, ga0];
ConjugateTranspose[f_?fermionQ] := NC[bar[f], ga0] /; Head[f] =!= bar;
ConjugateTranspose[bar[f_?fermionQ]] := NC[ga0, f];
ConjugateTranspose[NC[a_]]      := ConjugateTranspose[a];
ConjugateTranspose[NC[a_, b__]] :=
  NC[ConjugateTranspose[NC[b]], ConjugateTranspose[a]];
ConjugateTranspose[a_Plus]      := ConjugateTranspose /@ a;
ConjugateTranspose[a_Dot]      := ConjugateTranspose /@ Reverse[a];
ConjugateTranspose[c_ * x_]     := Conjugate[c] ConjugateTranspose[x] /; scalarQ[c];
ConjugateTranspose[0]           := 0;
ConjugateTranspose[d[a_][b_]] := d[a][ConjugateTranspose[b]];
ConjugateTranspose[col_Col]   := Col @@ (ConjugateTranspose /@ List@@col);
ConjugateTranspose[INS[a_]] := INS[ConjugateTranspose[a]];
ConjugateTranspose[ConjugateTranspose[a_]]:=a;
Protect[ConjugateTranspose];

Unprotect[Conjugate];
(*Conjugate[h_[inds__]] /; properIndexStructureQ[inds] := Conjugate[h][inds];*)
Conjugate[ElectricCharge[f_]] := ElectricCharge[f];
Conjugate[d[a_][b_]] := d[a][Conjugate[b]];
Conjugate[INS[a___]] := INS[Conjugate[a]];
Conjugate[a_Times] := Conjugate /@ a;
Conjugate[eps3[args___]] := eps3[args]; Conjugate[kd3[args___]] := kd3[args];
Protect[Conjugate];

Unprotect[Dot];
Dot[x___, a_Plus, y___] := Dot[x, #, y]& /@ a /; {x,y} =!= {};
Dot[x___, c_?su2ScalarQ * a_, y___] := c*Dot[x,a,y] /; {x,y} =!= {};
Dot[x___, c_?su2ScalarQ ** a_, y___] := c**Dot[x,a,y] /; {x,y} =!= {};
Dot[x___, a_**c_?su2ScalarQ, y___] := Dot[x,a,y]**c /; {x,y} =!= {};
Protect[Dot];

(* ---- derivative d_mu ---- *)
d[mu_][a_Plus] := d[mu] /@ a;
d[mu_][Times[a_, b__]] :=  d[mu][a] Times[b] + a d[mu][Times[b]];
d[mu_][NC[a_, b___]]   := NC[d[mu][a], NC[b]] + NC[a, d[mu][NC[b]]];
d[mu_][c_] := 0 /; STindepQ[c];
d[mu_][HoldPattern[INS[a_]]] := INS[d[mu][resolvedE2[mu, a]]]; (* assumption: mu contains no dummy indices *)
d[mu_][l_List]  := d[mu] /@ l;
d[mu_][col_Col] := Col @@ (d[mu] /@ List@@col);


(* ---- metric contraction:  g_{mu nu} X^{..nu..} = X^{..mu..}  (nu a dummy) ---- *)
contractIndexType[e_, metric_, indexType_] := e //. HoldPattern[Times[metric[indexType[a_], indexType[b_]], r__]] /;
     Count[Cases[Times[r], indexType[x_] :> x, Infinity], b] == 1 :> (Times[r] /. indexType[b] -> indexType[a]);
     
contract[e_]:= Module[{e1, e2},
  e1 = contractIndexType[e, g, LI];
  e2 = contractIndexType[e1, kd3, GI];
  contractIndexType[e2, kd3, FI]
]

(* ---- dummy-index canonicalization (free indices preserved) ---- *)
HeadAndArgs[e_] := Join[List@@e,{Head[e]}];

extractIndices[t_][e_] /; FreeQ[e, t] := {};
extractIndices[t_][h_[i[x_]]] /; MemberQ[$indices, h] := If[h === t, {i[x]}, {}];
extractIndices[t_][Power[b_, n_Integer?Positive]] := Join @@ ConstantArray[extractIndices[t][b], n];
extractIndices[t_][col_Col] := First @ MaximalBy[extractIndices[t] /@ (List @@ col), Length];
extractIndices[t_][e_] /; Head[e] =!= Power := If[AtomQ[e], {}, Join @@ (extractIndices[t] /@ HeadAndArgs @ e)];

dummyIndices[t_][e_] := Cases[Tally[extractIndices[t][e]], {x_, 2} :> t[x]];

(* open (free) indices of type t: those appearing exactly once.  Detection   *)
(* is per monomial, since across a Plus a free index recurs once per summand  *)
(* and would be miscounted as a dummy; one representative term suffices       *)
(* (free indices are common to every term).                                  *)
openIndices[t_][e_] := Module[{term = Expand[e]},
  term = If[Head[term] === Plus, First[term], term];
  Cases[Tally @ extractIndices[t][term], {x_, 1} :> t[x]]];

canonicalizeOneIndexType[e_, indexType_] := Module[{dum, open, n, canonIdxLst},
  (* any index appearing twice in expression is a dummy index *)
  dum = dummyIndices[indexType][e];
  open = openIndices[indexType][e] /. indexType[i[x_]] :> x;
  n = Length[dum];
  canonIdxLst = FirstFreeIdx[open, #] & /@ (Range @ n);
  If[n === 0, e,
    First @ Sort @ Table[
      e /. Thread[dum -> Table[indexType[i[p[[k]]]], {k, n}]],
      {p, Permutations @ canonIdxLst}
    ]
  ]
];

(* canonical: normalize via Expand[INS[...]] then canonicalize dummy names. *)
(* Optional second arg `types` restricts canonicalization to the listed    *)
(* index types (default: all of $indices).  Use this to skip an index type *)
(* whose dummy detection cannot be applied to a given expression -- e.g.   *)
(* a propagator with a flavour-indexed mass in the denominator, where FI   *)
(* canonicalization is invalid (see fermion propagatorMap entries).        *)
canonicalizeINS[x_?indexFreeQ, types_:$indices]:=x;
canonicalizeINS[INS[x_], types_:$indices] := INS[Fold[canonicalizeOneIndexType, x, types]];
canonicalizeINS[e_Plus, types_:$indices]  := canonicalizeINS[#, types]& /@ e;
canonicalizeINS[e_Times, types_:$indices] := canonicalizeINS[#, types]& /@ e;
canonical[e_, types_:$indices] := canonicalizeINS[Expand[INS[e]], types];

(* perform sum over gauge indices *)
SumOverIndices[expr_, {}] := expr;
SumOverIndices[expr_, dum_List] :=
 Module[{d = First[dum], rest = Rest[dum]},
  Sum[SumOverIndices[expr /. d :> Head[d][a], rest], {a, 1, 3}]];

(* IdxSum: sum GI dummy indices; INS wrapper is preserved in each summand *)
IdxSumINS[_][x_?indexFreeQ]:=x;
IdxSumINS[h_][INS[x_]] := With[{dum = dummyIndices[h][x]}, SumOverIndices[INS[x], dum]];
IdxSumINS[h_][e_Plus]  := IdxSumINS[h] /@ e;
IdxSumINS[h_][e_Times] := IdxSumINS[h] /@ e;
(*IdxSumINS[c_*INS[x_]] := With[{dum = dummyIndices[GI][x]}, If[Length[dum]===0,c*INS[x],c*SumOverIndices[INS[x], dum]]];*)
IdxSum[h_][e_]      := IdxSumINS[h][Expand[INS[e]]] /; MemberQ[{GI,FI}, h];

GISum = IdxSum[GI];
FISum = IdxSum[FI];

(* =================================================================== *)
(*  IndexNamespace (INS)                                               *)
(* =================================================================== *)

IndexNamespace := INS;

(* --- General rules ------------------------------------------------- *)

INS[INS[a_]]                               := INS[a];
INS[c_?indexFreeQ]                         := c;
INS[c_?indexFreeQ * a_]                    := c * INS[a];
INS[a_Plus]                                := INS /@ a;
INS[a_Times] /; MemberQ[List @@ a, _Plus] := INS[Expand[a]];
INS[Power[a_Plus, b_?NumericQ]]            := INS[Expand[Power[a, b]]];

INS /: HoldPattern[NC[INS[a_]]] := INS[NC[a]];
bar[HoldPattern[INS[a_]]]       := INS[bar[a]];

(* --- Conflict resolution algorithm --------------------------------- *)

iValsOf[indexType_][expr_] :=
  DeleteDuplicates @ Cases[extractIndices[indexType][expr], i[n_Integer] :> n];

resolveIndexConflicts[expr1_, expr2_] :=
  Fold[
    Function[{pair, t},
      Module[{e1, e2, dum1, dum2, idx1, idx2, c1, c2, allUsed, nFresh, fresh},
        {e1, e2} = pair;
        dum1 = dummyIndices[t][e1];
        dum2 = dummyIndices[t][e2];
        idx1 = extractIndices[t][e1];
        idx2 = extractIndices[t][e2];
        c1 = Select[dum1, MemberQ[idx2, First[#]] &];
        c2 = Select[dum2, MemberQ[idx1, First[#]] &];
        If[c1 === {} && c2 === {},
          pair,
          allUsed = Union[iValsOf[t][e1], iValsOf[t][e2]];
          nFresh = Length[c1] + Length[c2];
          fresh = Take[
            Select[Range[Max[Append[allUsed, 0]] + 2 nFresh + 2],
                   !MemberQ[allUsed, #] &],
            nFresh];
          {
            e1 /. Thread[c1 -> (t[i[#]] & /@ fresh[[1 ;; Length[c1]]])],
            e2 /. Thread[c2 -> (t[i[#]] & /@ fresh[[Length[c1] + 1 ;; nFresh]])]
          }
        ]
      ]
    ],
    {expr1, expr2}, $indices
  ];

(* Avoid With[] in upvalue rules — it interacts badly with NC's HoldAll *)
resolvedE1[a_, b_] := resolveIndexConflicts[a, b][[1]];
resolvedE2[a_, b_] := resolveIndexConflicts[a, b][[2]];

(* --- Times and Power ----------------------------------------------- *)

INS /: HoldPattern[INS[a_] * INS[b_]] :=
  INS[resolvedE1[a, b] * resolvedE2[a, b]];

INS /: HoldPattern[INS[a_] * b_] /; !indexFreeQ[b] && Head[b] =!= INS :=
  INS[resolvedE1[a, b] * resolvedE2[a, b]];

INS /: HoldPattern[INS[a_]^n_Integer?Positive] /; n >= 2 :=
  INS[a] * INS[a]^(n - 1);

(* --- NC chain ------------------------------------------------------ *)

INS /: HoldPattern[NC[x___, INS[a_], INS[b_], y___]] :=
  NC[x, INS[NC[resolvedE1[a, b], resolvedE2[a, b]]], y];

INS /: HoldPattern[NC[x___, INS[a_], b_?indexFreeQ, y___]] :=
  NC[x, INS[NC[a, b]], y];
INS /: HoldPattern[NC[x___, b_?indexFreeQ, INS[a_], y___]] :=
  NC[x, INS[NC[b, a]], y];
INS /: HoldPattern[NC[x___, INS[a_], b_, y___]] /; !indexFreeQ[b] && Head[b] =!= INS :=
  NC[x, INS[NC[resolvedE1[a, b], resolvedE2[a, b]]], y];
INS /: HoldPattern[NC[x___, b_, INS[a_], y___]] /; !indexFreeQ[b] && Head[b] =!= INS :=
  NC[x, INS[NC[resolvedE2[a, b], resolvedE1[a, b]]], y];

(* --- Dot chain ----------------------------------------------------- *)

Unprotect[Dot];
INS /: HoldPattern[Dot[x___, INS[a_], INS[b_], y___]] :=
  Dot[x, INS[Dot[resolvedE1[a, b], resolvedE2[a, b]]], y];
INS /: HoldPattern[Dot[x___, INS[a_], b_?indexFreeQ, y___]] :=
  Dot[x, INS[Dot[a, b]], y];
INS /: HoldPattern[Dot[x___, b_?indexFreeQ, INS[a_], y___]] :=
  Dot[x, INS[Dot[b, a]], y];
INS /: HoldPattern[Dot[x___, INS[a_], b_, y___]] /; !indexFreeQ[b] && Head[b] =!= INS :=
  Dot[x, INS[Dot[resolvedE1[a, b], resolvedE2[a, b]]], y];
INS /: HoldPattern[Dot[x___, b_, INS[a_], y___]] /; !indexFreeQ[b] && Head[b] =!= INS :=
  Dot[x, INS[Dot[resolvedE2[a, b], resolvedE1[a, b]]], y];
Protect[Dot];

(* --- INSRule ------------------------------------------------------- *)

(* helpers *)
FirstFreeIdx[taken : {___Integer}, n_Integer] :=
  If[Length[taken] === 0, n, Complement[Range[1, Length[taken] + n], taken][[n]]];
FirstFreeIdxRepl[taken_List, e_] := e /. {i[n_Integer] :> i[FirstFreeIdx[taken, n]]};

SetAttributes[INSRule, HoldAll];
INSRule[lhs_, rhs_] :=
  Module[{patternVars, freshVars, newLhs, newRhs},
    patternVars =
      DeleteDuplicates @
        Cases[Unevaluated[rhs], i[s_Symbol] :> s, Infinity];
    freshVars = Table[Unique[], {Length[patternVars]}];
    newLhs = lhs /. Thread[patternVars -> freshVars];
    newRhs =
      INS[FirstFreeIdxRepl[freshVars, rhs /. Thread[patternVars -> freshVars]]];
    Evaluate[newLhs] :> Evaluate[newRhs]];

(* =================================================================== *)
(*  Dirac-chain normaliser                                              *)
(*  (1) gamma5 = P_R - P_L                                                      *)
(*  (2) move ghost fields to the left past dirac matrices                       *)
(*  (3) move projectors right past gammas and collapse products:                *)
(*        P_{L,R} gamma^mu = gamma^mu P_{R,L} ,  P^2 = P ,  P_L P_R = 0         *)
(*  (4) completeness in a sum:  c X P_L Y + c X P_R Y -> c X Y  (P_L+P_R=1)    *)
(*     applied AFTER (3) so projectors are already in canonical right position  *)
diracSimplify[e_] := Module[{x},
   x = e /. ga5 -> PR - PL;
   x = x //. NC[a___, m_, f_, b___] /;
                  (grassmannQ[f] && diracMatQ[m]) :>
              NC[a, f, m, b];
   x = x //. {
      NC[a___, PL, ga[m_], b___] :> NC[a, ga[m], PR, b],
      NC[a___, PR, ga[m_], b___] :> NC[a, ga[m], PL, b],
      NC[a___, PL, PL, b___] :> NC[a, PL, b],
      NC[a___, PR, PR, b___] :> NC[a, PR, b],
      NC[a___, PL, PR, b___] :> 0,
      NC[a___, PR, PL, b___] :> 0};
   x];

(* Collapse P_L + P_R -> 1 in sums of Dirac chains.  Expensive on large
   expressions; call explicitly after feynman-rule extraction, not during
   simplification of the full Lagrangian. *)
recombineProjectors[e_] := Expand[e] //. {
   Plus[u___, c_. * NC[gg___, PL, hh___],
              c_. * NC[gg___, PR, hh___], v___] :>
      Plus[u, v, c NC[gg, hh]],
   Plus[u___, c_. * NC[PL], c_. * NC[PR], v___] :> Plus[u, v, c],
   Plus[u___, c_. * PL, c_. * PR, v___] :> Plus[u, v, c]};
   
(* ---- chiral field renormalisation ---- *)
(*   psi -> (1+dZL) P_L psi + (1+dZR) P_R psi                                   *)
(*   psibar -> (1+dZL) psibar P_R + (1+dZR) psibar P_L                           *)
(* returns the substitution rules; apply with  L /. renorm[f, dZL, dZR] .       *)
renorm[f_, zL_, zR_] := {
   f -> (1 + zL) * NC[PL, f] + (1 + zR) NC[PR, f],
   bar[f] ->   (1 + Conjugate[zL]) NC[bar[f], PR] + (1 + Conjugate[zR]) NC[bar[f], PL]};

(* ---- boson field renormalisation ---- *)
(*  Diagonal: h_0 = (1 + dZ/2) h                                                   *)
(*  Returns two rules so both indexed  h[idx]  and bare scalar  h  are covered.    *)
(*  The indexed rule  h[idx___] :> ...  fires first (more specific),               *)
(*  so the bare rule never incorrectly replaces a head position.                   *)
(*  Apply with  expr /. renormBoson[h, dZ]  or include in a Flatten[{...}] list.  *)
renormBoson[h_, dZ_] := {
   h[idx___] :> (1 + dZ/2) h[idx],
   h          :> (1 + dZ/2) h};

(*  2\[Times]2 mixing renormalisation: (h1_0, h2_0) = Z^{1/2} (h1, h2), where            *)
(*     h1_0 = (1 + dZ11/2) h1 + (dZ12/2) h2                                       *)
(*     h2_0 = (dZ21/2) h1 + (1 + dZ22/2) h2                                       *)
(*  Typical use: renormMix[Zb, AA, dZZZ, dZZA, dZAZ, dZAA]                        *)
(*  Rules applied simultaneously by /. so mixing on the RHS is NOT re-expanded.   *)
renormMix[h1_, h2_, dZ11_, dZ12_, dZ21_, dZ22_] := {
   h1[idx___] :> (1 + dZ11/2) h1[idx] + (dZ12/2) h2[idx],
   h2[idx___] :> (dZ21/2) h1[idx] + (1 + dZ22/2) h2[idx],
   h1          :> (1 + dZ11/2) h1 + (dZ12/2) h2,
   h2          :> (dZ21/2) h1 + (1 + dZ22/2) h2};
   
(* ---- functional derivative ---- *)
(* fdiffINS operates on bare or INS-wrapped expressions.  The INS rule       *)
(* renames dummies in x that clash with the leg index xi before recursing,   *)
(* mirroring the same pattern used in d[mu_][HoldPattern[INS[a_]]].          *)
fdiffINS[lg_, a_Plus]     := fdiffINS[lg, #] & /@ a;
fdiffINS[{f_, xi_, p_}, HoldPattern[INS[x_]]] := INS[fdiffINS[{f, xi, p}, resolvedE2[xi, x]]];
fdiffINS[lg_, c_ * x_]   := c fdiffINS[lg, x] /; STindepQ[c];
fdiffINS[lg_, c_]         := 0 /; STindepQ[c];
fdiffINS[lg_, Times[a_, b__]] := fdiffINS[lg, a] Times[b] + a fdiffINS[lg, Times[b]];
fdiffINS[lg_, Power[b_, n_Integer?Positive]] := n b^(n - 1) fdiffINS[lg, b];

(* functional differentiation of field derivatives with transition to         *)
(* momentum space                                                             *)
fdiffINS[{f_, xi_, p_}, HoldPattern[d[m_][z_]]] :=
  (-I p[m]) fdiffINS[{f, xi, p}, z];

(* delta phi_LI1 / delta phi_LI2 *)
fdiffINS[{f_, LI[a_], p_}, f_[LI[b_]]] := g[LI[a], LI[b]];
fdiffINS[{f_, h_[a_], p_}, f_[h_[b_]]] := kd3[h[a], h[b]] /; MemberQ[{GI, FI}, h];
(* delta bar[f]_h1 / delta bar[f]_h2  (anti-fermion with flavor/color index) *)
fdiffINS[{bar[f_], h_[a_], p_}, bar[f_[h_[b_]]]] := kd3[h[a], h[b]] /; MemberQ[{GI, FI}, h];
(* delta phi / delta phi *)
fdiffINS[{f_, None, _}, f_] := 1 /; fieldQ[f];
(* delta theta / delta theta  (gauge parameters: bosonic, no Grassmann sign) *)
(*fdiffINS[{f_, None, _}, f_] := 1 /; gaugeParamQ[f];*)

(* graded Leibniz over a chain. pick up (-1)^(#odd factors to the left)      *)
(* when the derivative is odd.                                               *)
GrassmFact[a_,l_]:=If[!oddQ[a],1,Power[-1,Count[l, _?oddQ]]];
fdiffINS[{f_, xi_, p_}, ch_NC] := With[{l = List @@ ch},
   Sum[GrassmFact[f,Take[l,n-1]]*NC@@MapAt[fdiffINS[{f, xi, p},#]&,l,n],
{n,1,Length[l]}]
];
(* anything independent of the leg field -> 0 *)
fdiffINS[{f_, _, _}, x_] := 0 /; FreeQ[x, f];

(* public API: wrap the expression in INS so dummy indices are tracked, then  *)
(* dispatch to fdiffINS which resolves any clash with the leg index           *)
fdiff[lg_, e_] := fdiffINS[lg, INS[e]];

(* ---- Feynman rules ---- *)
(* differentiate wrt each leg in turn, then send the leftover fields to zero *)
(*setZero[e_] := e /. x_ /; fieldQ[x] :> 0;*)
setZero[a_] /; FreeQ[a, _?fieldQ] := a;
setZero[a_?fieldQ] := 0;
setZero[ElectricCharge[x_]] := ElectricCharge[x];
setZero[e_] := Map[setZero, e];

functionalD[L_, legs_] := Module[{e = Expand[L]},
   Do[e = Expand[fdiff[lg, e]], {lg, legs}];
   Expand[setZero[e]]];

(* Diagonal mass matrices (Mdiagl/Mdiagu/Mdiagd) are expanded to their       *)
(* kd3 * mass form by the model (ExplMassMat, defined in EWSMLagrangian.wl).  *)
(* This stub is the load-order-safe default (identity): LagTools is usable    *)
(* standalone, and the model's definition replaces this one when loaded.      *)
ExplMassMat[e_] := e;

(* tree-level vertex:  i * delta^n S / delta phi... , contracted, Dirac- and    *)
(* index-canonicalised.  ExplMassMat is the final step so that diagonal mass    *)
(* matrices appear as kd3 * mass (needed by the fermion propagator inversion,   *)
(* which factors the internal-index Kronecker delta out).                       *)
RemoveINS[e_] := e //. {HoldPattern[INS[a_]] -> a};
vertexFct[l_, legs_] := Expand[I recombineProjectors @ RemoveINS @ Expand @ FullSimplify @ canonical @ diracSimplify @ contract @ functionalD[RemoveINS@l, legs]];

(* =================================================================== *)
(*  Dirac trace (D = 4 spacetime dimensions)                            *)
(* =================================================================== *)
(*  The trace handles pure gamma chains via the standard recursion (any   *)
(*  even length; odd -> 0).  For every MASSIVE fermion the two-point       *)
(*  function combines into projector-free form (p-slash + m): the P_L and  *)
(*  P_R pieces of the kinetic term recombine via P_L + P_R = 1, so only    *)
(*  bare gamma chains reach the trace.                                     *)
(*                                                                         *)
(*  EXCEPTION -- accepted, not fixed: a genuinely chiral (massless,        *)
(*  left-handed) fermion -- here only the neutrino -- has a two-point      *)
(*  function ~ gamma.p P_L with no P_R partner to recombine, so the P_L is *)
(*  irreducible and reaches traceGammas, which emits a harmless            *)
(*  First::normal ("First[PL]") message and leaves that trace unevaluated. *)
(*  Physically P_R nu = 0, so the projector is redundant and the correct   *)
(*  neutrino propagator is the projector-free i p-slash/p^2 (the reference *)
(*  convention), obtained on paper by simply dropping P_L.  We do not      *)
(*  reintroduce gamma5 / epsilon trace machinery for this single entry.    *)
(*                                                                         *)
(*  diracTrace is INS-aware: it commutes with the index namespace wrapper *)
(*  (Tr[INS[x]] = INS[Tr[x]]), so a trace of an INS-resolved chain stays  *)
(*  inside its namespace and, once the metric indices are contracted away,*)
(*  the index-free coefficient collapses back out of INS on its own.      *)

traceGammas[{}] := 4;
traceGammas[lst_List] /; OddQ[Length[lst]] := 0;
traceGammas[lst_List] := Module[{m1 = First[lst], rest = Rest[lst]},
   Sum[(-1)^(p + 1) g[First[m1], First[rest[[p]]]] traceGammas[Delete[rest, p]],
       {p, 1, Length[rest]}]];

diracTrace[e_]                          := traceDispatch @ Expand[e];
traceDispatch[a_Plus]                   := traceDispatch /@ a;
traceDispatch[HoldPattern[INS[a_]]]              := INS[diracTrace[a]];
traceDispatch[c_?diracScalarQ * HoldPattern[INS[a_]]] := c INS[diracTrace[a]];
traceDispatch[c_?diracScalarQ * ch_NC]  := c traceGammas[List @@ ch];
traceDispatch[ch_NC]                    := traceGammas[List @@ ch];
traceDispatch[c_?diracScalarQ]          := 4 c;          (* scalar * identity *)

(* =================================================================== *)
(*  Two-point-function inversion -> propagator                          *)
(* =================================================================== *)
(*  invertTwoPoint[A, p, pSq, type] inverts the (matrix-valued) two-point *)
(*  function A to the propagator B with  A B = 1  (fermion / scalar) or   *)
(*  A^{mu nu} B_{nu rho} = delta^mu_rho (vector), following the           *)
(*  projector-basis method:                                              *)
(*                                                                        *)
(*    fermion :  P_pm = 1/2 ( 1 +/- pslash / Sqrt[pSq] ),                 *)
(*               A_pm = 1/2 Tr[P_pm A],   B = P_+/A_+ + P_-/A_- .          *)
(*    vector  :  P1 = g - p p / pSq ,  P2 = p p / pSq ,                   *)
(*               A_i = (P_i : A)/Tr[P_i] (Tr P1 = D-1 = 3, Tr P2 = 1),    *)
(*               B = P1/A_1 + P2/A_2 .                                    *)
(*                                                                        *)
(*  p    : momentum symbol of the line.                                  *)
(*  pSq  : the scalar invariant p^2 (kept index-free, like the           *)
(*         propagatorMap denominators).                                  *)
(*  type : "scalar" | "fermion" | "vector" (supplied by the caller).     *)
(*  The scalar coefficients A_i are treated as commuting (valid when A    *)
(*  is diagonal in any internal flavour/colour indices, as at tree level).*)

(* contract, then map the contracted momentum invariant p_mu p^mu (an     *)
(* indexed Power) onto the index-free scalar pSq used in the propagator   *)
(* denominators.  The metric self-contraction g_{mu nu} g^{mu nu} = 4 is  *)
(* handled by the general rule with the metric definitions.               *)
momSqReduce[e_, p_, pSq_] := contract[Expand[e]] /. Power[p[LI[_]], 2] :> pSq;

(* The fifth argument intIdx is the pair of OPEN internal (flavour / colour)  *)
(* leg indices, e.g. {FI[i[2]], FI[i[3]]}, supplied by Propagator from the     *)
(* legs.  It cannot be inferred reliably from A: a flavour-indexed mass        *)
(* md[FI[i[2]]] re-uses an open leg index, defeating multiplicity heuristics.  *)
(* Default: no internal structure (intIdx = {}).                              *)
invertTwoPoint[A_, p_, pSq_, type_] := invertTwoPoint[A, p, pSq, type, {}];

invertTwoPoint[A_, p_, pSq_, "scalar", _] := 1/momSqReduce[A, p, pSq];

invertTwoPoint[A_, p_, pSq_, "fermion", intIdx_List] := Module[
   {delta, Adir, pslash, Pp, Pm, Aplus, Aminus},
   (* The fermion two-point function is diagonal in any internal (flavour /  *)
   (* colour) space: every term carries one Kronecker delta kd3[j,k] over    *)
   (* the open leg indices (the mass term too, once Mdiag -> kd3*mass has     *)
   (* been expanded by ExplMassMat).  A scalar reciprocal 1/A_jk is NOT the   *)
   (* matrix inverse, so we factor the delta out, invert the remaining        *)
   (* per-flavour Dirac-scalar object, and reattach the delta.               *)
   delta = If[intIdx === {}, 1, kd3 @@ intIdx];
   Adir  = If[intIdx === {}, A, A //. (kd3 @@ intIdx -> 1)];
   (* INS gives pslash's dummy a private name so it cannot collide with an  *)
   (* index already in Adir; the clash is resolved when NC[P., Adir] is      *)
   (* formed, and the contracted coefficients collapse back to plain scalars.*)
   pslash = INS[NC[ga[LI[i[1]]]] p[LI[i[1]]]];
   Pp = (1 + pslash / Sqrt[pSq]) / 2;
   Pm = (1 - pslash / Sqrt[pSq]) / 2;
   Aplus  = momSqReduce[diracTrace[NC[Pp, Adir]], p, pSq] / 2;
   Aminus = momSqReduce[diracTrace[NC[Pm, Adir]], p, pSq] / 2;
   (* final commit of the index namespace, as feynmanRule does for vertices *)
   delta RemoveINS @ FullSimplify[Pp/Aplus + Pm/Aminus, pSq > 0]];

invertTwoPoint[A_, p_, pSq_, "vector", _] := Module[
   {mu, nu, P1, P2, A1, A2},
   {mu, nu} = openIndices[LI][A];
   P1 = g[mu, nu] - p[mu] p[nu] / pSq;
   P2 = p[mu] p[nu] / pSq;
   A1 = momSqReduce[P1 A, p, pSq] / 3;  (* / (D-1) *)
   A2 = momSqReduce[P2 A, p, pSq];
   FullSimplify[P1/A1 + P2/A2, pSq > 0]];

(* =================================================================== *)
(*  Propagator: invert the two-point function                           *)
(* =================================================================== *)
(*  The field type of a leg {field, idx, mom} is read off the leg: a     *)
(*  Lorentz (LI) index -> vector, a fermion field -> fermion, otherwise  *)
(*  scalar (incl. ghosts, with index None).                              *)
legFieldType[{f_, idx_, _}] := Which[
   fermionQ[f] || Head[f] === bar, "fermion",
   Head[idx] === LI,               "vector",
   True,                           "scalar"];

Propagator::legtype = "The two legs carry different field types (`1`, `2`).";

(*  Propagator[L, {{F1,idx1,p1}, {F2,idx2,p2}}]:  build the two-point      *)
(*  function from L, impose momentum conservation p2 = -p1, and invert    *)
(*  with line momentum p1.  Sq[p1] is the index-free scalar invariant     *)
(*  p1^2 used in the denominators.                                        *)
Propagator[l_, legs : {{_, _, _}, {_, _, _}}] := Module[
   {p1 = legs[[1, 3]], p2 = legs[[2, 3]], t1, t2, A, intIdx},
   t1 = legFieldType[legs[[1]]];
   t2 = legFieldType[legs[[2]]];
   If[t1 =!= t2, Message[Propagator::legtype, t1, t2]; Return[$Failed]];
   A = (ExplMassMat @ vertexFct[l, legs]) /. p2[a___] :> -p1[a];   (* p2 = -p1 *)
   (* the open internal (flavour/colour) leg indices, used by the fermion    *)
   (* inversion to factor the diagonal Kronecker delta out; {} if the legs    *)
   (* carry no internal index (e.g. index None).                             *)
   intIdx = {legs[[1, 2]], legs[[2, 2]]};
   intIdx = If[MatchQ[intIdx, {(FI | GI)[_], (FI | GI)[_]}], intIdx, {}];
   invertTwoPoint[A, p1, Sq[p1], t1, intIdx]];

(* feynmanRule dispatches: two external legs -> propagator, else vertex. *)
feynmanRule[l_, legs_] :=
   If[Length[legs] === 2, Propagator[l, legs], vertexFct[l, legs]];

(* =================================================================== *)
(*  Gauge multiplet infrastructure                                     *)
(* =================================================================== *)

su2DoubletQ[_] := False;
su2SingletQ[_] := False;
su2DoubletQ[h_[___]] /; h =!= bar := su2DoubletQ[h];
su2SingletQ[h_[___]] /; h =!= bar := su2SingletQ[h];

(* Collect distinct bare field-symbol atoms from an expression.
   Heads -> True is required so that el inside el[FI[1]] is found
   (heads sit at the {0} position and are invisible to the default levelspec). *)
fieldSymbolsIn[expr_] :=
  DeleteDuplicates @ Cases[{expr}, x_ /; AtomQ[x] && fieldQ[x], Infinity, Heads -> True];

DeclareGaugeDoublet::nofields    = "No field symbols found in lower component of doublet `1`.";
DeclareGaugeDoublet::hypercharge = "Inconsistent hypercharges in lower component of `1`: `2`.";

DeclareGaugeDoublet[sym_Symbol, lbl_, rule_RuleDelayed] := Module[
  {comps, lowerFields, yValues},
  comps = rule[[2]];
  If[!MatchQ[comps, {_, _}],
    Message[DeclareGaugeDoublet::nofields, sym]; Return[$Failed]];
  su2DoubletQ[sym] = True;
  With[{fs = fieldSymbolsIn[comps]},
    If[AnyTrue[fs, fermionQ], fermionQ[sym] = True, bosonQ[sym] = True]];
  (* Hypercharge from lower component (T3 = -1/2): Y = 2*(Q + 1/2) *)
  lowerFields = fieldSymbolsIn[comps[[2]]];
  If[lowerFields === {},
    Message[DeclareGaugeDoublet::nofields, sym]; Return[$Failed]];
  yValues = 2*(ElectricCharge[#] + 1/2) & /@ lowerFields;
  If[!SameQ @@ yValues,
    Message[DeclareGaugeDoublet::hypercharge, sym, yValues]; Return[$Failed]];
  Hypercharge[sym] = First[yValues];
  GaugeMultExpansion[sym] = ReplacePart[rule, 2 -> Col @@ comps];
  Format[sym] = lbl;
  sym
];

DeclareGaugeSinglet[sym_Symbol, lbl_, rule_RuleDelayed] := Module[
  {fields},
  su2SingletQ[sym] = True;
  fields = fieldSymbolsIn[rule[[2]]];
  If[AnyTrue[fields, fermionQ], fermionQ[sym] = True, bosonQ[sym] = True];
  (* Inherit charge from the underlying field unless sym IS that field *)
  If[fields =!= {} && First[fields] =!= sym,
    ElectricCharge[sym] = ElectricCharge[First[fields]]];
  Hypercharge[sym] = 2 * ElectricCharge[sym];  (* T3 = 0: Y = 2Q *)
  GaugeMultExpansion[sym] = rule;
  Format[sym] = lbl;
  sym
];

(* =================================================================== *)
(*  Col: SU(2) column-vector wrapper                                   *)
(*  Not Listable — Plus/Times never distribute into doublet components  *)
(* =================================================================== *)

Col /: Col[a__] + Col[b__] := Col @@ MapThread[Plus, {{a}, {b}}];
Col /: c_?scalarQ * Col[a__]       := Col @@ (c * {a});
Col /: c_?scalarQ ** Col[a__]      := Col @@ (c ** {a});
(*Col /: bar[Col[args___]]   := Col @@ (bar /@ args);*)

(* mat . Col[v] — explicit matrix acting on column *)
Unprotect[Dot];
Col /: Dot[mat_List, Col[v__]]  := Col @@ (mat . {v});
(* Col . mat — row context (result of ConjugateTranspose) *)
Col /: Dot[Col[a__], mat_List]  := Col @@ ({a} . mat);
(* Col . Col — inner product -> scalar *)
Col /: Dot[Col[a__], Col[b__]]  := {a} . {b};
Protect[Dot];

NC[c1_Col,y___,c2_Col] := Sum[NC[c1[[sumidx1]],y,c2[[sumidx2]]],{sumidx1,1,2},{sumidx2,1,2}] /; su2ScalarQ[y];
NC[c1_Col,c2_Col] := Sum[NC[c1[[sumidx1]],c2[[sumidx2]]],{sumidx1,1,2},{sumidx2,1,2}];

Unprotect[Conjugate];
Col /: Conjugate[Col[v__]] := Col @@ (Conjugate /@ {v});
Protect[Conjugate];

(* =================================================================== *)
(*  SU(2) and U(1)_Y generators                                        *)
(* =================================================================== *)

(* sigma[a]/2 acting on a Col doublet *)
SU2T[a_][col_Col] := (1/2) sigma[a] . col;
(* SU(2) generator vanishes on singlets *)
SU2T[GI[_]][sym_?su2SingletQ]  := 0;
SU2T[GI[_]][f_] /; su2SingletQ[Head[f]] := 0;
SU2T[GI[_]][f_?fieldQ] /; FreeQ[f, _?su2DoubletQ] := 0;

(* U(1)_Y generator: return hypercharge of the multiplet.
   Split bare-symbol vs indexed to avoid Hypercharge[sym[idx]] when idx is present. *)
U1Y[sym_Symbol] /; su2DoubletQ[sym] || su2SingletQ[sym] := Hypercharge[sym]*sym;
U1Y[f_[inds___]]    /; su2DoubletQ[f]   || su2SingletQ[f]   := Hypercharge[f]*f[inds];

(* Hypercharge of a doublet from its lower (T3 = -1/2) component: Y = 2(Q+1/2).
   Same formula DeclareGaugeDoublet uses to set Hypercharge[sym]. *)
lowerCompHypercharge[lower_] := 2 (ElectricCharge[First[fieldSymbolsIn[lower]]] + 1/2);

U1Y[col_Col] := lowerCompHypercharge[col[[2]]] * col;
U1Y[f_?fieldQ] := 2 ElectricCharge[f] * f;

(* =================================================================== *)
(*  Covariant derivative and field strength declarations                *)
(* =================================================================== *)

covDQ[_]     := False;
fieldStrQ[_] := False;

DeclareCovD[sym_Symbol, lbl_, rule_RuleDelayed] := (
  covDQ[sym] = True;
  CovDExpansion[sym] = rule;
  Format[sym] = lbl;
  sym
);

DeclareFieldStr[sym_Symbol, lbl_, rule_RuleDelayed] := (
  fieldStrQ[sym] = True;
  FieldStrExpansion[sym] = rule;
  Format[sym] = lbl;
  sym
);

(* Covariant derivative applied to an INS-wrapped argument: push INS inside,
   renaming any dummy in a that clashes with the indices carried by h. *)
INS /: HoldPattern[h_[mu_][INS[a_]]] /; covDQ[h] :=
  INS[h[mu][resolvedE2[mu, a]]];

(* =================================================================== *)
(*  Explicit substitution                                               *)
(* =================================================================== *)

ExplGaugeMult[e_] := e /. (Last /@ DownValues[GaugeMultExpansion]);
ExplCovD[e_]      := e /. (Last /@ DownValues[CovDExpansion]);
ExplFieldStr[e_]  := e /. (Last /@ DownValues[FieldStrExpansion]);

(* =================================================================== *)
(*  Display formatting (notebook output)                               *)
(* =================================================================== *)


Unprotect[MakeBoxes];

$IdxNames = {
  LI -> {"\[Mu]", "\[Nu]", "\[Rho]", "\[Sigma]", "\[Lambda]", "\[Kappa]", "\[Alpha]", "\[Beta]"},
  FI -> {"i", "j", "k", "l", "m", "n", "o", "p"},
  GI -> {"a", "b", "c", "d", "e", "f", "g", "h"}
};

(* indexType[i[n]] — dummy/symbolic slot: look up pretty name (μ, a, i, …) *)
IdxBox[type_][i[n_Integer]] := Module[
  {names = type /. $IdxNames},
  If[n <= Length[names],
    names[[n]],
    RowBox[{ToString[type], "[", ToString[n], "]"}]
  ]
];

(* indexType[n] bare integer — display the number directly *)
IdxBox[type_][n_Integer] := ToString[n];

IdxBox[type_][n_] := RowBox[{ToString[type], "[", ToString[n, InputForm], "]"}];

MakeBoxes[h_[x_],                     StandardForm] /;MemberQ[$indices,h]:= IdxBox[h][x];
MakeBoxes[h_[inds__], StandardForm] /; properIndexStructureQ[inds] :=
  SubsuperscriptBox[
    MakeBoxes[h, StandardForm],
    RowBox[Cases[{inds}, LI[x_] :> IdxBox[LI][x]] ~Join~
           Cases[{inds}, FI[x_] :> IdxBox[FI][x]]],
    RowBox[Cases[{inds}, GI[x_] :> IdxBox[GI][x]]]
  ];
MakeBoxes[f_,                 StandardForm] /; fieldQ[f] && Head[f] =!= bar := ToString[f];
MakeBoxes[bar[f_],            StandardForm] := OverscriptBox[MakeBoxes[f, StandardForm], "_"];
MakeBoxes[d[LI[x_]][expr_],   StandardForm] := RowBox[{"(", SubscriptBox["\[PartialD]", IdxBox[LI][x]], "\[ThinSpace]", MakeBoxes[expr, StandardForm],")"}];
MakeBoxes[ga,   StandardForm] := "\[Gamma]";
MakeBoxes[ga0,  StandardForm] := SubscriptBox["\[Gamma]", "0"];
MakeBoxes[ga5,  StandardForm] := SubscriptBox["\[Gamma]", "5"];
MakeBoxes[PL,   StandardForm] := SubscriptBox["P", "L"];
MakeBoxes[PR,   StandardForm] := SubscriptBox["P", "R"];
MakeBoxes[g,    StandardForm] := "g";
MakeBoxes[kd3,  StandardForm] := "\[Delta]";
MakeBoxes[eps3, StandardForm] := "\[Epsilon]";
MakeBoxes[sigma[n_], StandardForm] := SuperscriptBox["\[Sigma]", ToString[n]];
MakeBoxes[expr_NC, StandardForm] := RowBox[MakeBoxes[#, StandardForm] & /@ List @@ expr];

(* Conjugate: single symbol -> symbol^*, compound -> (...)^* *)
MakeBoxes[Conjugate[s_Symbol], StandardForm] :=
  SuperscriptBox[MakeBoxes[s, StandardForm], "*"];
MakeBoxes[Conjugate[expr_], StandardForm] :=
  SuperscriptBox[RowBox[{"(", MakeBoxes[expr, StandardForm], ")"}], "*"];

(* ChargeConj: single symbol -> symbol^C, compound -> (...)^C *)
MakeBoxes[ChargeConj[s_Symbol], StandardForm] :=
  SuperscriptBox[MakeBoxes[s, StandardForm], "C"];
MakeBoxes[ChargeConj[expr_], StandardForm] :=
  SuperscriptBox[RowBox[{"(", MakeBoxes[expr, StandardForm], ")"}], "C"];

(* Quantum numbers *)
MakeBoxes[ElectricCharge[f_Symbol], StandardForm] :=
  SubscriptBox["Q", MakeBoxes[f, StandardForm]];
MakeBoxes[Hypercharge[f_Symbol], StandardForm] :=
  SubscriptBox["Y", MakeBoxes[f, StandardForm]];

(* Covariant derivative: (D_mu expr) *)
MakeBoxes[sym_[LI[x_]][expr_], StandardForm] /; covDQ[sym] :=
  RowBox[{"(", SubscriptBox[MakeBoxes[sym, StandardForm], IdxBox[LI][x]],
          "\[ThinSpace]", MakeBoxes[expr, StandardForm], ")"}];

(* SU(2) generator: T^a expr *)
MakeBoxes[SU2T[GI[a_]][expr_], StandardForm] :=
  RowBox[{SuperscriptBox["T", IdxBox[GI][a]], "\[ThinSpace]",
          MakeBoxes[expr, StandardForm]}];

(* U1Y: Y[expr] — only appears before evaluation for undeclared fields *)
MakeBoxes[U1Y[expr_], StandardForm] :=
  RowBox[{"Y", "[", MakeBoxes[expr, StandardForm], "]"}];

Protect[MakeBoxes];
