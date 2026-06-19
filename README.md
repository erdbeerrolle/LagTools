# LagTools

A small Wolfram Language layer for symbolic manipulation of (electroweak)
Lagrangians and extraction of momentum-space Feynman rules.

> **Status:** written before a Mathematica kernel was available on this
> machine, so **everything is untested**. `Tests.wlt` is the contract — run it
> first (see below) and we iterate from real failures. Targets WL **14.2 and
> 15.0** (only long-stable language features are used).

## Files

| File | Contents |
|------|----------|
| `LagTools.wl` | Core algebra: typed indices, field declaration, graded `**` product, `OP` container, derivative `d`, metric/gamma/deltas, `Canonicalize`, `Contract`. |
| `FeynmanRules.wl` | Functional derivative `FunctionalD`, momentum-space `FeynmanRule`. |
| `DiracAlgebra.wl` | Clifford algebra `DiracSimplify`, projector handling, `DiracTrace`, Levi-Civita `eps`. |
| `Tests.wlt` | Verification tests for the core + Feynman rules. **Run this first.** |
| `DiracTests.wlt` | Trace and Clifford-identity tests for the Dirac module. |
| `Examples/EW.wl` | A slice of the EW Lagrangian and a few vertices (illustrative). |

## Loading

```mathematica
dir = "C:\\Users\\laras\\Documents\\Mathematica\\LagTools";
Get[FileNameJoin[{dir, "LagTools.wl"}]];
Get[FileNameJoin[{dir, "FeynmanRules.wl"}]];

report = TestReport[FileNameJoin[{dir, "Tests.wlt"}]];
report["AllTestsSucceeded"]
report["TestResultsDataset"]   (* drill into failures *)
```

On the uni PC (14.2) copy the whole `LagTools` folder and point `dir` at it.
Nothing depends on an absolute path except the convenience default inside
`Tests.wlt`, which falls back to `$InputFileName`.

## Core concepts

### Typed indices
`LI[a]` Lorentz, `DI[a]` Dirac/spinor, `GI[a]` gauge/adjoint, `CI[a]` colour,
`FI[a]` flavour. An index is a *dummy* (summed) when its label appears exactly
twice in a term, *free* otherwise.

### Fields
```mathematica
DeclareField[Wp, Indices -> {LI}, Conjugate -> Wm, Mass -> mW];
DeclareField[el, Grassmann -> True, Dirac -> True, Indices -> {}];
```
A field is a head applied to its declared indices: `Wp[LI[mu]]`, a scalar is
`HH[]`, a Dirac fermion is `el[]` (its **spinor index is implicit** — see
below). `DeclareCoupling[ee, gw, ...]` registers index-free scalars.

### Dirac chains: the graded product `**`
Fermion bilinears are written with `**` (`NonCommutativeMultiply`):
```mathematica
elbar[] ** ga[LI[mu]] ** el[]            (* ebar gamma^mu e *)
```
Spinor indices are **positional** — the chain order encodes the matrix
multiplication `ebar_a (gamma^mu)_ab e_b`, so `el`/`elbar` carry no explicit
`DI` index. The product automatically:
- factors **scalars and bosonic fields out** to an ordinary `Times`
  (`A[LI[mu]] ** el[]` → `A[LI[mu]] el[]`);
- keeps **non-central Dirac objects ordered** (`ga`, `ga5`, `PL`, `PR`);
- treats the **identity `del` as central** (it factors out and relabels, like a
  metric).

### Linear container `OP`
`OP[...]` wraps one Lagrangian monomial (or a sum). It is linear: scalars and
couplings are pulled to the front, sums are distributed.

### Derivative `d`
`d[LI[mu]][A[LI[nu]]]` is ∂_μ A_ν. `d` is linear, kills couplings/constants and
gamma matrices, and obeys the graded Leibniz rule over `Times` and `**`.

### Canonicalization
`Canonicalize[expr]` renames contracted (dummy) indices to a canonical labelling
so that terms equal up to dummy relabelling **and** commuting-factor order
collapse. Free indices are preserved (they label external legs). The headline
identity holds:
```mathematica
Canonicalize[OP[Wp[LI[mu]] Wm[LI[mu]] A[LI[nu]] A[LI[nu]]]] ===
Canonicalize[OP[Wp[LI[nu]] Wm[LI[nu]] A[LI[mu]] A[LI[mu]]]]   (* True *)
```
The current engine is brute-force-minimal over the `k!` dummy relabellings of a
term — fine for the few dummies in a typical EW term, **not** a full
Butler–Portugal canonicalizer (see Roadmap).

## Feynman rules

`FeynmanRule[L, {leg1, leg2, ...}]` returns the momentum-space vertex
```
  i * delta^n S / (delta phi_1 ... delta phi_n) |_(fields=0)
```
contracted and canonicalized. Each `leg` is `{field, index, momentum}`:
- `index` is the open index of that external line (`LI[al]` for a vector,
  `None` for a scalar or for the implicit spinor index of a fermion);
- `momentum` is a symbol, taken **incoming**.

```mathematica
FeynmanRule[ee (elbar[] ** ga[LI[mu]] ** el[]) AA[LI[mu]],
  {{AA, LI[al], k1}, {elbar, None, k2}, {el, None, k3}}]
(* -> I ee ga[LI[al]] *)
```

### Conventions (all easy to change)

| Convention | Default | Where to change |
|------------|---------|-----------------|
| Metric signature | mostly-minus (+,−,−,−) | documented in `$MetricSignature`; signs live in `g` |
| Spacetime dim | `$Dim = 4` (`g[LI[a],LI[a]] -> 4`) | `LagTools.wl` |
| Momenta | all **incoming** | `fdiff` derivative rule |
| Derivative → momentum | `d_mu phi -> -I p_mu` | `fdiff[{f,xi,p}, d[mu][inner]]` |
| Overall vertex factor | `I` (from e^{iS}) | `FeynmanRule` |
| Fermion derivative | **left** derivative, legs applied in listed order | `fdiff` chain rule |

> The fermion **sign** convention is the part most likely to need adjustment —
> the relative signs between diagrams are what matter and they follow the leg
> order. The two fermionic tests are tagged `(* CHECK *)`.

## Dirac algebra (`DiracAlgebra.wl`)

```mathematica
Get[FileNameJoin[{dir, "DiracAlgebra.wl"}]];

DiracTrace[ga[LI[mu]] ** ga[LI[nu]]]                    (* 4 g[LI[mu],LI[nu]] *)
Contract[DiracTrace[p[LI[mu]] q[LI[nu]] (ga[LI[mu]] ** ga[LI[nu]])]]  (* 4 p.q *)
DiracSimplify[ga[LI[mu]] ** ga[LI[al]] ** ga[LI[mu]]]   (* -2 ga[LI[al]] *)
DiracTrace[ga[LI[mu]] ** ga[LI[nu]] ** PL]              (* 2 g[LI[mu],LI[nu]] *)
```

- `DiracTrace` is linear, pulls commuting factors (momenta/metric/couplings)
  out, and traces a chain with **at most one `ga5`** (a `ga5` trace needs ≥4
  gammas and yields an `eps`). The no-`ga5` trace is exact to all orders.
- `DiracSimplify` anticommutes `ga5` rightward, applies `(ga5)^2=1`, projector
  products (`PL^2=PL`, `PL PR=0`, …) and the `D=$Dim` gamma-contraction
  identities `ga^mu … ga_mu`.
- **`(* CHECK *)`**: the `ga5`-trace sign uses
  `tr(ga5 ga^mu ga^nu ga^rho ga^sig) = -4 I eps[mu,nu,rho,sig]`. Flip in
  `traceG5` if your `eps` convention differs.

## Roadmap / known gaps

1. **Validate against the kernel.** Run `Tests.wlt`; fix the `(* CHECK *)`
   conventions; add tests for terms with 3–4 dummies.
2. **Gamma algebra & traces.** *(first cut done — `DiracAlgebra.wl`.)*
   `DiracSimplify` (Clifford algebra, `ga5` anticommutation, projector products,
   `D`-dim contraction identities) and `DiracTrace` (all-orders no-`ga5` trace,
   4-gamma `ga5` trace → `eps`). **Remaining:** `ga5` traces with ≥6 gammas,
   and a `DiracTrace`/`Contract` convenience wrapper.
3. **Metric raising/lowering.** Currently all indices are "down" with `g`
   inserted explicitly; add explicit up/down position handling if needed.
4. **Real canonicalizer.** Replace the brute-force dummy minimisation with a
   Butler–Portugal-style algorithm (as in xAct/xPerm) for terms with many
   dummies and tensor symmetries (e.g. Levi-Civita `eps`, field-strength
   antisymmetry).
5. **Covariant derivative & field strengths.** Helpers to expand
   `D_mu = d_mu - i g (...)` and `F_mu_nu` so you write the gauge Lagrangian
   compactly and let the engine distribute.
6. **Full SM EW Lagrangian.** Build it in the mass-eigenstate basis on top of
   the above, then regression-test vertices (WWZ, WWgamma, WWH, ffZ, ...)
   against a reference (FeynRules / Romao's notes).
7. **External-leg conventions.** Wavefunction factors / spinors (u, v, eps) for
   on-shell amplitudes, if you go beyond bare vertices.

## Open questions for you

- Metric signature — I assumed **mostly-minus (+,−,−,−)**. Particle-physics
  standard, but confirm.
- Do you want indices to carry explicit up/down position, or keep the
  "all-down + explicit `g`" scheme (simpler, what's implemented)?
- Should the canonicalizer also fold in tensor symmetries (antisymmetric field
  strengths, `eps`) now, or after the gamma algebra lands?
