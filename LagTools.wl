(* ::Package:: *)
(* ------------------------------------------------------------------ *)
(*  EW Lagrangian -> Feynman rules.                                   *)
(*  Lorentz indices: LI[mu].                                          *)
(*  Spinor indices implicit (positional in the noncommutative         *)
(*  product **)                                                       *)
(*  Metric (+,-,-,-), D=4                                             *)
(*  all momenta incoming, d_mu -> -I p_mu.                            *)
(* ------------------------------------------------------------------ *)

$bosons      = {};
$fermions    = {};
$grassmann   = {};
$massless    = {};     (* fermions with no right-handed component: PR**f = 0 *)
$diracMat    = {ga, ga5, PL, PR};
$displayName = <||>;   (* head -> label box/string used in MakeBoxes *)

DeclareBoson[h_]          := (AppendTo[$bosons,    h]; h);
DeclareFermion[f_]        := (AppendTo[$fermions,  f]; f);
DeclareGrassmann[f_]      := (AppendTo[$grassmann, f]; f);
(* DeclareMassless[f]: declare f purely left-handed, so PR**f = 0 and bar[f]**PL = 0 *)
DeclareMassless[f_]       := (AppendTo[$massless,  f]);
DeclareBoson[h_,     lbl_] := (DeclareBoson[h];     $displayName[h] = lbl; h);
DeclareFermion[f_,   lbl_] := (DeclareFermion[f];   $displayName[f] = lbl; f);
DeclareGrassmann[f_, lbl_] := (DeclareGrassmann[f]; $displayName[f] = lbl; f);

(* ---- predicates ---- *)
bosonQ[h_] := MemberQ[$bosons, h] || MemberQ[$bosons, Head[h]];

oddQ[f_Symbol]  := MemberQ[Join[$fermions, $grassmann], f];
oddQ[bar[f_]]   := MemberQ[Join[$fermions, $grassmann], f];
oddQ[_]         := False;

fieldQ[x_] := bosonQ[x] || oddQ[x];

(* a Dirac-matrix element of a chain: ga[_], ga5, PL, PR.  Note ga[mu] has   *)
(* head ga, so a bare-symbol MemberQ alone would miss it -- check Head too.   *)
diracMatQ[m_] := MemberQ[$diracMat, m] || MemberQ[$diracMat, Head[m]];

nonCommutingHeads[] := Join[$fermions, $grassmann, {bar}, $diracMat];
nonScalarHeads[]    := Join[$bosons, nonCommutingHeads[]];
commutingQ[x_] := FreeQ[x, Alternatives @@ nonCommutingHeads[]];
scalarQ[x_]    := FreeQ[x, Alternatives @@ nonScalarHeads[]] && FreeQ[x, LI] && FreeQ[x, d];

(* ---- metric ----   g symmetric;  g_{mu}^{mu} = D = 4 *)
SetAttributes[g, Orderless];
g[a_, a_] := 4;

(* ---- graded noncommutative product **  (boson/scalar factors fall out) ---- *)
Unprotect[NonCommutativeMultiply];
NonCommutativeMultiply[x___, p_Plus, y___] := (NonCommutativeMultiply[x, #, y] &) /@ p;
NonCommutativeMultiply[x___, Times[u__], y___] := (Times @@ Select[{u}, commutingQ]) *
     NonCommutativeMultiply[x, Sequence @@ Select[{u}, Not@*commutingQ], y] /;
   AnyTrue[{u}, commutingQ] && AnyTrue[{u}, Not@*commutingQ];
NonCommutativeMultiply[x___, c_, y___] := c NonCommutativeMultiply[x, y] /; commutingQ[c];
NonCommutativeMultiply[x_] := x;
NonCommutativeMultiply[] := 1;
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
d[mu_][NonCommutativeMultiply[a_, b__]] :=
   d[mu][a] ** NonCommutativeMultiply[b] + a ** d[mu][NonCommutativeMultiply[b]];
d[_][ga[_]] = 0; d[_][ga5] = 0; d[_][PL] = 0; d[_][PR] = 0; d[_][g[__]] = 0;

(* ---- metric contraction:  g_{mu nu} X^{..nu..} = X^{..mu..}  (nu a dummy) ---- *)
contract[e_] := e //. HoldPattern[Times[g[LI[a_], LI[b_]], r__]] /;
     Count[Cases[Times[r], LI[x_] :> x, Infinity], b] == 1 :> (Times[r] /. LI[b] -> LI[a]);

(* ---- dummy-index canonicalization (free indices preserved) ---- *)
(* a label occurring exactly twice (counting powers: A[LI[mu]]^2 = A_mu A_mu)  *)
(* is a contracted dummy.  Rename the k dummies to 1..k over all k! orderings   *)
(* and keep the canonically smallest form.  Only index-bearing factors are      *)
(* permuted; an index-free prefactor is split off and multiplied back.          *)
labels[LI[x_]] := {x};
labels[Power[b_, n_Integer?Positive]] := Join @@ ConstantArray[labels[b], n];
labels[e_] := If[AtomQ[e], {}, Join @@ (labels /@ List @@ e)];
canonTerm[t_] := Module[
   {fac = If[Head[t] === Times, List @@ t, {t}], pre, core, dum},
   pre  = Times @@ Select[fac, FreeQ[#, LI] &];
   core = Times @@ Select[fac, ! FreeQ[#, LI] &];
   dum = Cases[Tally[labels[core]], {x_, 2} :> x];
   pre If[dum === {}, core,
      First @ Sort @ Table[core /. Thread[dum -> p], {p, Permutations @ Range @ Length @ dum}]]];
canonical[e_] := With[{x = Expand[e]},
   If[Head[x] === Plus, canonTerm /@ x, canonTerm[x]]];

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
                  (MemberQ[$grassmann, f] && diracMatQ[m]) :>
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
   If[$massless =!= {},
      x = x //. {
         NonCommutativeMultiply[a___, PR, f_, b___]    /; MemberQ[$massless, f] :> 0,
         NonCommutativeMultiply[a___, bar[f_], PL, b___] /; MemberQ[$massless, f] :> 0}];
   x];

(* ---- chiral field renormalisation ---- *)
(*   psi -> (1+dZL) P_L psi + (1+dZR) P_R psi                                   *)
(*   psibar -> (1+dZL*) psibar P_R + (1+dZR*) psibar P_L                        *)
(* returns the substitution rules; apply with  L /. renorm[f, dZL, dZR] .       *)
renorm[f_, zL_, zR_] := {
   f -> (1 + zL) PL ** f + (1 + zR) PR ** f,
   bar[f] -> (1 + Conjugate[zL]) bar[f] ** PR + (1 + Conjugate[zR]) bar[f] ** PL};

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
fdiff[{f_, LI[a_], p_}, f_[LI[b_]] := g[LI[a], LI[b]];
(* delta phi / delta phi *)
fdiff[{f_Symbol, _, _}, f_Symbol] := 1 /; fieldQ[f];

(* graded Leibniz over a chain. pick up (-1)^(#odd factors to the left)      *)
(* when the derivative is odd.                                               *)
fdiff[{f_, xi_, p_}, ch_NonCommutativeMultiply] := With[{q = List @@ ch},
   Sum[(If[oddQ[f], (-1)^Count[q[[1 ;; i - 1]], _?oddQ], 1]) *
       NonCommutativeMultiply[Sequence @@ q[[1 ;; i - 1]], fdiff[{f, xi, p}, q[[i]]],
                              Sequence @@ q[[i + 1 ;;]]], {i, Length[q]}]];
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
(*  μ₁, μ₂, ...                                                        *)
(* =================================================================== *)

(* Box for a field head: registered label or plain symbol name *)
ltFieldBox[h_] := If[KeyExistsQ[$displayName, h], $displayName[h], SymbolName[h]];

(* Box for a Lorentz index label: integer dummies -> mu_n, symbols -> Greek or name *)
ltIdxBox[n_Integer] := SubscriptBox["\[Mu]", ToString[n]];
ltIdxBox[s_Symbol]  := ltIdxBox[s_Symbol] := SymbolName[s];;

(* LI wrapper disappears; only the index label is shown *)
MakeBoxes[LI[x_], StandardForm] := ltIdxBox[x];

(* boson field with one Lorentz index:   A[LI[mu]] -> A_mu *)
MakeBoxes[h_Symbol[LI[x_]], StandardForm] /; MemberQ[$bosons, h] :=
   SubscriptBox[ltFieldBox[h], ltIdxBox[x]];

(* zero-index boson field: H[] or bare H *)
MakeBoxes[h_Symbol[], StandardForm] /; MemberQ[$bosons, h] := ltFieldBox[h];
MakeBoxes[h_Symbol,   StandardForm] /; MemberQ[$bosons, h] := ltFieldBox[h];

(* bare fermion / ghost with a registered label *)
MakeBoxes[f_Symbol, StandardForm] /;
    MemberQ[Join[$fermions, $grassmann], f] && KeyExistsQ[$displayName, f] :=
   $displayName[f];

(* Dirac conjugate:  bar[psi] -> psi with overbar *)
MakeBoxes[bar[f_], StandardForm] :=
   OverscriptBox[MakeBoxes[f, StandardForm], "_"];

(* derivative:   d[LI[mu]][expr] -> partial_mu expr *)
MakeBoxes[d[LI[x_]][expr_], StandardForm] :=
   RowBox[{SubscriptBox["\[PartialD]", ltIdxBox[x]], "\[ThinSpace]",
           MakeBoxes[expr, StandardForm]}];

(* Dirac matrices *)
MakeBoxes[ga[LI[x_]], StandardForm] := SuperscriptBox["\[Gamma]", ltIdxBox[x]];
MakeBoxes[ga5,         StandardForm] := SubscriptBox["\[Gamma]", "5"];
MakeBoxes[PL,          StandardForm] := SubscriptBox["P", "L"];
MakeBoxes[PR,          StandardForm] := SubscriptBox["P", "R"];

(* metric tensor:  g[LI[a],LI[b]] -> g_{ab} *)
MakeBoxes[g[LI[a_], LI[b_]], StandardForm] :=
   SubscriptBox["g", RowBox[{ltIdxBox[a], ltIdxBox[b]}]];

(* NonCommutativeMultiply: juxtapose without a ** symbol.              *)
(* MakeBoxes is not Protected, so a downvalue with head restriction    *)
(* works without Unprotecting NonCommutativeMultiply.                  *)
MakeBoxes[expr_NonCommutativeMultiply, StandardForm] :=
   RowBox[MakeBoxes[#, StandardForm] & /@ List @@ expr];
