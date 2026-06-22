(* ::Package:: *)

(*---- Dirac matrices ----*)
$diracMat = {ga, ga5, PL, PR};
diracMatQ[m_]:=MemberQ[$diracMat,m]||MemberQ[$diracMat,Head[m]];

(* Index types: Lorentz index LI, gauge index GI, Flavour index FI *)
$indices = {LI, GI, FI};

(*---- Field declarations ----*)
DeclareBoson[h_Symbol]    :=(bosonQ[h] = True;     h);
DeclareFermion[f_Symbol]  :=(fermionQ[f] = True;   f);
DeclareGrassmann[f_Symbol]:=(grassmannQ[f] = True; f);

DeclareBoson[h_Symbol,    lbl_]:=(DeclareBoson[h];    Format[h] = lbl; h);
DeclareFermion[f_Symbol,  lbl_]:=(DeclareFermion[f];   Format[f] = lbl; f);
DeclareGrassmann[f_Symbol,lbl_]:=(DeclareGrassmann[f]; Format[f] = lbl; f);

(*----defaults----*)
bosonQ[_]      :=False;
fermionQ[_]    :=False;
grassmannQ[_]  :=False;

(* lift all predicates through indexed fields and bar *)
With[{preds={bosonQ,fermionQ,grassmannQ}},
  Scan[(#[h_[___]] /; h=!=bar := #[h])&, preds];
  Scan[(#[bar[f_]] := #[f])&, preds];
];

(* ---- composite predicates ---- *)
fieldQ[x_] := bosonQ[x] || fermionQ[x] || grassmannQ[x];
oddQ[x_]   := fermionQ[x] || grassmannQ[x];

(*---- composite predicates with deep-scan ----*)
commutingQ[x_] := FreeQ[x, _?oddQ | _?diracMatQ];
scalarQ[x_]    := FreeQ[x, _?fieldQ | _?diracMatQ | Alternatives@@$indices | d];

(* ---- metric ----   g symmetric;  g_{mu}^{mu} = D = 4 *)
SetAttributes[g, Orderless];
g[a_, a_] := 4;

(* ---- Kronecker delta for flavour indices and su2 gauge indices ---- delta symmetric;  delta_{i}^{i} = 3 *)
SetAttributes[kroneckerDelta3, Orderless];
kroneckerDelta3[a_, a_] := 3;
KD3=kroneckerDelta3;

(* ---- noncommutative product **  (boson/scalar factors are pulled out) ---- *)
NC[]:=1;
NC[x___,p_Plus,y___]:=NC[x,#,y]&/@p;
NC[x___,c_?commutingQ,y___] := c*NC[x,y];
NC[x___,c_?commutingQ d_,y___] := c*NC[x,d,y];
NC[x___,NC[z___],y___]:=NC[x,z,y];

(* ** delegates to NC *)
Unprotect[NonCommutativeMultiply];
ClearAll[NonCommutativeMultiply];
NonCommutativeMultiply[args___]:=NC[args];
Protect[NonCommutativeMultiply];

(* ---- Dirac conjugate bar: linear, antilinear in scalars ---- *)
bar[0] = 0;
bar[a_Plus] := bar /@ a;
bar[c_ x_] := Conjugate[c] bar[x] /; scalarQ[c];

(* ---- derivative d_mu ---- *)
d[mu_][a_Plus] := d[mu] /@ a;
d[mu_][c_ x_] := c d[mu][x] /; scalarQ[c];
d[mu_][c_] := 0 /; scalarQ[c];
d[mu_][Times[a_, b__]] := d[mu][a] Times[b] + a d[mu][Times[b]];
d[mu_][NC[a_, b__]] :=
   d[mu][a] ** NC[b] + a ** d[mu][NC[b]];
d[_][ga[_]] = 0; d[_][ga5] = 0; d[_][PL] = 0; d[_][PR] = 0; d[_][g[__]] = 0; d[_][KD3[__]] = 0;

(* ---- metric contraction:  g_{mu nu} X^{..nu..} = X^{..mu..}  (nu a dummy) ---- *)
contractIndexType[e_, metric_, indexType_] := e //. HoldPattern[Times[metric[indexType[a_], indexType[b_]], r__]] /;
     Count[Cases[Times[r], indexType[x_] :> x, Infinity], b] == 1 :> (Times[r] /. indexType[b] -> indexType[a]);
     
contract[e_]:= Module[{e1, e2},
  e1 = contractIndexType[e, g, LI];
  e2 = contractIndexType[e1, KD3, GI];
  contractIndexType[e2, KD3, FI]
]

(* ---- dummy-index canonicalization (free indices preserved) ---- *)
extractIndices[t_][h_[x_]] /; MemberQ[$indices, h] := If[h === t, {x}, {}];
extractIndices[t_][Power[b_, n_Integer?Positive]] := Join @@ ConstantArray[extractIndices[t][b], n];
extractIndices[t_][e_] := If[AtomQ[e], {}, Join @@ (extractIndices[t] /@ List @@ e)];

canonicalizeOneIndexType[e_, indexType_] := Module[{dum, n},
  (* any index appearing twice in expression is a dummy index *)
  dum = Cases[Tally[extractIndices[indexType][e]], {x_, 2} :> indexType[x]];
  n = Length[dum];
  If[n === 0, e,
    First @ Sort @ Table[
      e /. Thread[dum -> Table[indexType[p[[k]]], {k, n}]],
      {p, Permutations @ Range @ n}
    ]
  ]
];

(*apply canonicalization in all indices*)
canonicalizeTerm[t_] := Module[
  {fac, prefac, core},
  fac  = If[Head[t] === Times, List @@ t, {t}];
  prefac  = Times @@ Select[fac, FreeQ[#, Alternatives@@$indices] &];
  core = Times @@ Select[fac, !FreeQ[#, Alternatives@@$indices] &];
  (* Canonicalise each index type independently, in sequence *)
  core = Fold[canonicalizeOneIndexType, core, $indices];
  prefac * core
];

canonical[e_] := With[{x = Expand[e]},
  If[Head[x] === Plus, canonicalizeTerm /@ x, canonicalizeTerm[x]]];
  
(* ---- Dirac-chain normaliser ---- *)
(*  (1) gamma5 = P_R - P_L                                                      *)
(*  (2) move ghost fields to the left past dirac matrices                       *)
(*  (3) move projectors right past gammas and collapse products:                *)
(*        P_{L,R} gamma^mu = gamma^mu P_{R,L} ,  P^2 = P ,  P_L P_R = 0         *)
(*  (4) completeness in a sum:  c X P_L Y + c X P_R Y -> c X Y  (P_L+P_R=1)    *)
(*  (5) massless chirality (DeclareMassless[f]):                                 *)
(*        PR ** f = 0 ,   bar[f] ** PL = 0                                       *)
(*     applied AFTER (3) so projectors are already in canonical right position  *)
diracSimplify[e_] := Module[{x},
   x = e /. ga5 -> PR - PL;
   x = x //. NonCommutativeMultiply[a___, m_, f_, b___] /;
                  (grassmannQ[f] && diracMatQ[m]) :>
              NonCommutativeMultiply[a, f, m, b];
   x = x //. {
      NonCommutativeMultiply[a___, PL, ga[m_], b___] :> NonCommutativeMultiply[a, ga[m], PR, b],
      NonCommutativeMultiply[a___, PR, ga[m_], b___] :> NonCommutativeMultiply[a, ga[m], PL, b],
      NonCommutativeMultiply[a___, PL, PL, b___] :> NonCommutativeMultiply[a, PL, b],
      NonCommutativeMultiply[a___, PR, PR, b___] :> NonCommutativeMultiply[a, PR, b],
      NonCommutativeMultiply[a___, PL, PR, b___] :> 0,
      NonCommutativeMultiply[a___, PR, PL, b___] :> 0};
   x = Expand[x] //. {
      Plus[u___, c_. NonCommutativeMultiply[gg___, PL, hh___],
                 c_. NonCommutativeMultiply[gg___, PR, hh___], v___] :>
         Plus[u, v, c NonCommutativeMultiply[gg, hh]],
      Plus[u___, c_. PL, c_. PR, v___] :> Plus[u, v, c]};
   x];
   
(* ---- chiral field renormalisation ---- *)
(*   psi -> (1+dZL) P_L psi + (1+dZR) P_R psi                                   *)
(*   psibar -> (1+dZL) psibar P_R + (1+dZR) psibar P_L                           *)
(* returns the substitution rules; apply with  L /. renorm[f, dZL, dZR] .       *)
renorm[f_, zL_, zR_] := {
   f -> (1 + zL) PL ** f + (1 + zR) PR ** f,
   bar[f] -> (1 + Conjugate[zL]) bar[f] ** PR + (1 + Conjugate[zR]) bar[f] ** PL};

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
fdiff[lg_, a_Plus] := fdiff[lg, #] & /@ a;
fdiff[lg_, c_ x_] := c fdiff[lg, x] /; scalarQ[c];
fdiff[lg_, c_] := 0 /; scalarQ[c];
fdiff[lg_, Times[a_, b__]] := fdiff[lg, a] Times[b] + a fdiff[lg, Times[b]];
fdiff[lg_, Power[b_, n_Integer?Positive]] := n b^(n - 1) fdiff[lg, b];

(* functional differentiation of field derivatives with transition to         *)
(* momentum space                                                             *)
fdiff[{f_, xi_, p_}, d[m_][z_]] := (-I p[m]) fdiff[{f, xi, p}, z];

(* delta phi_LI1 / delta phi_LI2 *)
fdiff[{f_, LI[a_], p_}, f_[LI[b_]]] := g[LI[a], LI[b]];
(* delta phi / delta phi *)
fdiff[{f_, None, _}, f_] := 1 /; fieldQ[f];

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
feynmanRule[L_, legs_] := I canonical[diracSimplify[contract[functionalD[L, legs]]]];

(* =================================================================== *)
(*  Display formatting (notebook output)                               *)
(*  Canonical dummy indices are integers (1,2,...) and display as      *)
(*  \[Mu]\:2081, \[Mu]\:2082, ...                                                        *)
(* =================================================================== *)

Unprotect[MakeBoxes];

$IdxNames = {
  LI -> {"\[Mu]", "\[Nu]", "\[Rho]", "\[Sigma]", "\[Lambda]", "\[Kappa]", "\[Alpha]", "\[Beta]"},
  FI -> {"i", "j", "k", "l", "m", "n", "o", "p"},
  GI -> {"a", "b", "c", "d", "e", "f", "g", "h"}
};

IdxBox[type_][n_Integer] := Module[
  {names = type /. $IdxNames},
  If[n <= Length[names],
    names[[n]],
    RowBox[{ToString[type], "[", ToString[n], "]"}]
  ]
];

IdxBox[type_][n_] := RowBox[{ToString[type], "[", ToString[n], "]"}];

MakeBoxes[h_[x_],                     StandardForm] /;MemberQ[$indices,h]:= IdxBox[h][x];
MakeBoxes[h_[inds__], StandardForm] /; fieldQ[h] :=
  SubsuperscriptBox[
    ToString[h, StandardForm],
    RowBox[Cases[{inds}, LI[x_] :> IdxBox[LI][x]] ~Join~
           Cases[{inds}, FI[x_] :> IdxBox[FI][x]]],
    RowBox[Cases[{inds}, GI[x_] :> IdxBox[GI][x]]]
  ];
MakeBoxes[f_,                 StandardForm] /; oddQ[f]   := ToString[f, StandardForm];
MakeBoxes[bar[f_],            StandardForm] := OverscriptBox[MakeBoxes[f, StandardForm], "_"];
MakeBoxes[d[LI[x_]][expr_],   StandardForm] := RowBox[{SubscriptBox["\[PartialD]", IdxBox[LI][x]], "\[ThinSpace]", MakeBoxes[expr, StandardForm]}];
MakeBoxes[ga[LI[x_]],         StandardForm] := SubscriptBox["\[Gamma]", IdxBox[LI][x]];
MakeBoxes[ga5,                StandardForm] := SubscriptBox["\[Gamma]", "5"];
MakeBoxes[PL,                 StandardForm] := SubscriptBox["P", "L"];
MakeBoxes[PR,                 StandardForm] := SubscriptBox["P", "R"];
MakeBoxes[g[LI[a_], LI[b_]],  StandardForm] := SubscriptBox["g", RowBox[{IdxBox[LI][a], IdxBox[LI][b]}]];
MakeBoxes[KD3[h_[a_], h[b_]], StandardForm] /; MemberQ[{FI,GI},h] := SubscriptBox["\[Delta]", RowBox[{IdxBox[LI][a], IdxBox[LI][b]}]];
MakeBoxes[expr_NC, StandardForm] := RowBox[MakeBoxes[#, StandardForm] & /@ List @@ expr];

Protect[MakeBoxes];
