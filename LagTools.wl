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

(* Real fields: Conjugate[h] = h, electric charge = 0 *)
DeclareRealBoson[h_Symbol] := (DeclareBoson[h]; h /: Conjugate[h] = h; ElectricCharge[h] = 0; h);
DeclareRealBoson[h_Symbol, lbl_] := (DeclareRealBoson[h]; Format[h] = lbl; h);

(* Complex-conjugate pairs: Conjugate[hp] = hm, charges +1/-1 by convention *)
DeclareComplexBoson[hp_Symbol, hm_Symbol] := (
  DeclareBoson[hp]; DeclareBoson[hm];
  hp /: Conjugate[hp] = hm;
  hm /: Conjugate[hm] = hp;
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
DeclareRealParam[p_Symbol]       := (DeclareComplexParam[p]; p /: Conjugate[p] = p; p);
DeclareRealParam[p_Symbol, lbl_] := (DeclareRealParam[p]; Format[p] = lbl; p);

(*----defaults----*)
bosonQ[_]      := False;
fermionQ[_]    := False;
grassmannQ[_]  := False;

(* lift all predicates through indexed fields and bar *)
With[{preds={bosonQ, fermionQ, grassmannQ}},
  Scan[(#[h_[___]] /; h=!=bar := #[h])&, preds];
  Scan[(#[bar[f_]] := #[f])&, preds];
];

(* ---- composite predicates ---- *)
fieldQ[x_] := bosonQ[x] || fermionQ[x] || grassmannQ[x];
oddQ[x_]   := fermionQ[x] || grassmannQ[x];

(*---- composite predicates with deep-scan ----*)
commutingQ[x_]   := FreeQ[x, _?oddQ | _?diracMatQ];
STindepQ[x_]     := FreeQ[x, _?fieldQ];
diracScalarQ[x_] := FreeQ[x, _?fermionQ | _?diracMatQ];
scalarQ[x_] := diracScalarQ[x] && FreeQ[x, _?su2DoubletQ];

properIndexStructureQ[inds__] := And @@ (MemberQ[$indices, Head[#]] & /@ {inds});

(* True when the expression carries no index slots of any type *)
indexFreeQ[e_] := FreeQ[e, Alternatives @@ (Blank /@ $indices)];

(* ---- metric ----   g symmetric;  g_{mu}^{mu} = D = 4 *)
SetAttributes[g, Orderless];
g[LI[i[a_]], LI[i[a_]]] /; IntegerQ[a] := 4;

(* ---- Kronecker delta for flavour indices and su2 gauge indices ---- delta symmetric;  delta_{i}^{i} = 3 *)
SetAttributes[kd3, Orderless];
kd3[h_[i[a_]], h_[i[a_]]] /; IntegerQ[a] && MemberQ[h, {FI, GI}] := 3;
kd3[h_[a_],h_[a_]] /; IntegerQ[a] && MemberQ[h, {FI, GI}] := 1;

(* ---- SU(2) Levi-Civita / structure constant: eps3[a,b,c] = epsilon^{abc} ---- *)
eps3[h_[a_Integer], h_[b_Integer], h_[c_Integer]] /; MemberQ[h, {GI}] := Signature[{a, b, c}];

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
NC[x___, col_Col, y___]          := Col @@ (NC[x, #, y]& /@ List@@col);
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
ConjugateTranspose[col_Col]   := Col @@ (Conjugate /@ List@@col);
Protect[ConjugateTranspose];

Unprotect[Conjugate];
Conjugate[h_[inds__]] /; properIndexStructureQ[inds] := Conjugate[h][inds];
Conjugate[ElectricCharge[f_]] := ElectricCharge[f];
Conjugate[d[a_][b_]] := d[a][Conjugate[b]];
Conjugate[INS[a___]] := INS[Conjugate[a]];
Protect[Conjugate];

(* ---- derivative d_mu ---- *)
d[mu_][a_Plus] := d[mu] /@ a;
d[mu_][Times[a_, b__]] :=  d[mu][a] Times[b] + a d[mu][Times[b]];
d[mu_][NC[a_, b___]]   := NC[d[mu][a], NC[b]] + NC[a, d[mu][NC[b]]];
d[mu_][c_] := 0 /; STindepQ[c];
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
extractIndices[t_][e_] /; Head[e] =!= Power := If[AtomQ[e], {}, Join @@ (extractIndices[t] /@ HeadAndArgs @ e)];

dummyIndices[t_][e_] := Cases[Tally[extractIndices[t][e]], {x_, 2} :> t[x]];

canonicalizeOneIndexType[e_, indexType_] := Module[{dum, n},
  (* any index appearing twice in expression is a dummy index *)
  dum = dummyIndices[indexType][e];
  n = Length[dum];
  If[n === 0, e,
    First @ Sort @ Table[
      e /. Thread[dum -> Table[indexType[i[p[[k]]]], {k, n}]],
      {p, Permutations @ Range @ n}
    ]
  ]
];

(* canonical: normalize via Expand[INS[...]] then canonicalize dummy names *)
canonicalizeINS[INS[x_]] := INS[Fold[canonicalizeOneIndexType, x, $indices]];
canonicalizeINS[e_Plus]  := canonicalizeINS /@ e;
canonicalizeINS[e_]      := e;
canonical[e_] := canonicalizeINS[Expand[INS[e]]];

(* perform sum over gauge indices *)
SumOverIndices[expr_, {}] := expr;
SumOverIndices[expr_, dum_List] :=
 Module[{d = First[dum], rest = Rest[dum]},
  Sum[SumOverIndices[expr /. d :> Head[d][a], rest], {a, 1, 3}]];

(* GISum: sum GI dummy indices; INS wrapper is preserved in each summand *)
GISum[INS[x_]] := With[{dum = dummyIndices[GI][x]}, SumOverIndices[INS[x], dum]];
GISum[e_Plus]  := GISum /@ e;
GISum[e_]      := GISum[INS[e]];

(* =================================================================== *)
(*  IndexNamespace (INS): expression wrapper that prevents dummy-index  *)
(*  collisions when combining sub-expressions.                          *)
(*                                                                      *)
(*  INS[a] * INS[b]  = INS[a * b']     b' has conflicting dummies      *)
(*  INS[a] ** INS[b] = INS[NC[a, b']]  renamed before combining        *)
(* =================================================================== *)

IndexNamespace := INS;

(* Collect all i[n] integer values for indexType present in expr *)
iValsOf[indexType_][expr_] :=
  DeleteDuplicates @ Cases[extractIndices[indexType][expr], i[n_Integer] :> n];

(* Rename conflicting dummy indices in expr2 so they don't clash with expr1 *)
resolveIndexConflicts[expr1_, expr2_] :=
  Fold[
    Function[{e2, t},
      Module[{conflicts, allUsed, fresh, rules},
        conflicts = Intersection[dummyIndices[t][expr1], dummyIndices[t][e2]];
        If[conflicts === {}, e2,
          allUsed = Union[iValsOf[t][expr1], iValsOf[t][e2]];
          fresh = Take[
            Select[Range[Max[Append[allUsed, 0]] + 2 Length[conflicts] + 2],
                   !MemberQ[allUsed, #] &],
            Length[conflicts]];
          e2 /. Thread[conflicts -> (t[i[#]] & /@ fresh)]
        ]
      ]
    ],
    expr2, $indices
  ];

INS[INS[a_]]:=INS[a];


(* Index-free factors have no dummy-index conflicts — pull them out *)
INS[c_?indexFreeQ]        := c;
INS[c_?indexFreeQ * a_]   := c * INS[a];

(* Plus: INS is linear — each summand gets its own namespace *)
INS[a_Plus] := INS /@ a;

(* Products of sums expand before dummy-index renaming *)
INS[a_Times] /; !FreeQ[a, _Plus] := INS[Expand[a]];

(* Times: rename dummies in b before multiplying *)
INS /: HoldPattern[INS[a_] * INS[b_]] :=
  INS[a * resolveIndexConflicts[a, b]];

(* Power: INS[x]^n unfolds to iterated Times, triggering rename at each step *)
INS /: HoldPattern[INS[a_]^n_Integer?Positive] /; n >= 2 :=
  INS[a] * INS[a]^(n - 1);

(* NC chain: resolve each adjacent INS pair left-to-right *)
INS /: HoldPattern[NC[x___, INS[a_], INS[b_], y___]] :=
  NC[x, INS[NC[a, resolveIndexConflicts[a, b]]], y];

Unprotect[Dot];
INS /: HoldPattern[Dot[x___, INS[a_], INS[b_], y___]] :=
  Dot[x, INS[Dot[a, resolveIndexConflicts[a, b]]], y];
Protect[Dot];

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
   (* next step is not performant *)
   x = Expand[x] //. {
      Plus[u___, c_. * NC[gg___, PL, hh___],
                 c_. * NC[gg___, PR, hh___], v___] :>
         Plus[u, v, c NC[gg, hh]],
      Plus[u___, c_. * PL, c_. * PR, v___] :> Plus[u, v, c]};
   x];
   
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
fdiff[lg_, a_Plus]     := fdiff[lg, #] & /@ a;
(*fdiff[lg_, INS[x_]]    := INS[fdiff[lg, x]];*)
fdiff[lg_, c_ * x_]   := c fdiff[lg, x] /; STindepQ[c];
fdiff[lg_, c_]         := 0 /; STindepQ[c];
fdiff[lg_, Times[a_, b__]] := fdiff[lg, a] Times[b] + a fdiff[lg, Times[b]];
fdiff[lg_, Power[b_, n_Integer?Positive]] := n b^(n - 1) fdiff[lg, b];

(* functional differentiation of field derivatives with transition to         *)
(* momentum space                                                             *)
fdiff[{f_, xi_, p_}, HoldPattern[d[m_][z_]]] :=
  (-I p[m]) fdiff[{f, xi, p}, z];

(* delta phi_LI1 / delta phi_LI2 *)
fdiff[{f_, LI[a_], p_}, f_[LI[b_]]] := g[LI[a], LI[b]];
fdiff[{f_, h_[a_], p_}, f_[h_[b_]]] := kd3[h[a], h[b]] /; MemberQ[{GI, FI}, h];
(* delta phi / delta phi *)
fdiff[{f_, None, _}, f_] := 1 /; fieldQ[f];
(* delta theta / delta theta  (gauge parameters: bosonic, no Grassmann sign) *)
(*fdiff[{f_, None, _}, f_] := 1 /; gaugeParamQ[f];*)

(* graded Leibniz over a chain. pick up (-1)^(#odd factors to the left)      *)
(* when the derivative is odd.                                               *)
GrassmFact[a_,l_]:=If[!oddQ[a],1,Power[-1,Count[l, _?oddQ]]];
fdiff[{f_, xi_, p_}, ch_NC] := With[{l = List @@ ch},
   Sum[GrassmFact[f,Take[l,n-1]]*NC@@MapAt[fdiff[{f, xi, p},#]&,l,n],
{n,1,Length[l]}]
];
(* anything independent of the leg field -> 0 *)
fdiff[{f_, _, _}, x_] := 0 /; FreeQ[x, f];

(* ---- Feynman rules ---- *)
(* differentiate wrt each leg in turn, then send the leftover fields to zero *)
setZero[e_] := e /. x_ /; fieldQ[x] :> 0;
functionalD[L_, legs_] := Module[{e = Expand[L]},
   Do[e = Expand[fdiff[lg, e]], {lg, legs}];
   Expand[setZero[e]]];

(* tree-level vertex:  i * delta^n S / delta phi... , contracted, Dirac- and    *)
(* index-canonicalised *)
RemoveINS[e_] := Module[{L}, (e /. {INS -> L}) /. {L[a_] -> a}]
feynmanRule[l_, legs_] := I canonical[diracSimplify[contract[functionalD[RemoveINS@l, legs]]]];

(* =================================================================== *)
(*  Gauge multiplet infrastructure                                      *)
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
Col /: c_ * Col[a__]       := Col @@ (c * {a});
Col /: c_ ** Col[a__]      := Col @@ (c ** {a});
(*Col /: bar[Col[args___]]   := Col @@ (bar /@ args);*)

(* mat . Col[v] — explicit matrix acting on column *)
Unprotect[Dot];
Col /: Dot[mat_List, Col[v__]]  := Col @@ (mat . {v});
(* Col . mat — row context (result of ConjugateTranspose) *)
Col /: Dot[Col[a__], mat_List]  := Col @@ ({a} . mat);
(* Col . Col — inner product -> scalar *)
Col /: Dot[Col[a__], Col[b__]]  := {a} . {b};
Protect[Dot];

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

(* U(1)_Y generator: return hypercharge of the multiplet.
   Split bare-symbol vs indexed to avoid Hypercharge[sym[idx]] when idx is present. *)
U1Y[sym_Symbol] /; su2DoubletQ[sym] || su2SingletQ[sym] := Hypercharge[sym]*sym;
U1Y[f_[inds___]]    /; su2DoubletQ[f]   || su2SingletQ[f]   := Hypercharge[f]*f[inds];

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
