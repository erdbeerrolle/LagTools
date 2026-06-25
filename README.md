# LagTools

Symbolic tooling (Wolfram Language) for building electroweak Lagrangians and
extracting tree-level Feynman rules: noncommutative Dirac algebra, SU(2)×U(1)
gauge structure, automatic dummy-index bookkeeping, functional differentiation,
and notebook-quality display formatting.

## Layout

| file | role |
|------|------|
| `LagTools.wl` | the package — all definitions, organised into the six modules below |
| `EWSMLagrangian.wl` | example: declares the Standard Model electroweak fields and Lagrangian on top of `LagTools.wl` |
| `Tests.wlt` | self-contained test suite (`TestReport`) |
| `scripts/run_tests.sh` | test runner used by `make test` |
| `Makefile` | `make test` |

`LagTools.wl` is a flat single-context (`Global`) package loaded with `Get`:

```wolfram
Get["LagTools.wl"];          (* re-loading is guarded by $LagToolsLoaded *)
```

### Modules (in load order)

1. **Fields** — field/parameter declarations (`DeclareFermion`, `DeclareBoson`,
   `DeclareComplexBoson`, …) and the predicate algebra (`fermionQ`, `bosonQ`,
   `scalarQ`, `commutingQ`, `indexFreeQ`, …).
2. **DiracAlgebra** — the noncommutative product `NC` (and `**`), the Dirac bar
   `bar`, the Hermitian conjugate `ConjugateTranspose`, and the chain
   simplifiers `diracSimplify` / `recombineProjectors`.
3. **IndexAlgebra** — the index tensors `g`, `kd3`, `eps3`; the derivative `d`;
   scalar `Conjugate`; metric contraction; dummy-index canonicalization;
   `IdxSum`; and the `INS` index-namespace machinery (conflict resolution +
   `INSRule`).
4. **Gauge** — Pauli matrices `sigma`, charge conjugation, SU(2)-scalar `Dot`
   linearity, the `Col` doublet wrapper, the `SU2T` / `U1Y` generators, gauge
   multiplet declarations (`DeclareGaugeDoublet` / `DeclareGaugeSinglet`), and
   covariant-derivative / field-strength declarations.
5. **FeynmanRules** — renormalisation rule builders (`renorm`, `renormBoson`,
   `renormMix`), functional differentiation (`fdiff`), and the vertex extractor
   `feynmanRule`.
6. **Formatting** — `MakeBoxes` display rules.

Each module is self-contained (every definition is delayed, single context), so
the file is ready to be split into one file per module without any behavioural
change.

## Running the tests

```sh
make test            # wolframscript + Tests.wlt, coloured PASS/FAIL summary
```

(Requires an activated Wolfram Engine / Mathematica on `PATH` as `wolframscript`.)

## Design conventions — UpValues, DownValues, and "wrappers"

This package leans heavily on Wolfram's term-rewriting, so it follows one
deliberate rule for **where a rule lives** (i.e. which symbol carries it).

### Two flows: distributors vs. wrappers

Every *algebraic-rewriting* head falls into one of two patterns:

- **Distributors** push their head inward toward the leaves and then vanish:
  `bar`, `Conjugate`, `ConjugateTranspose`, `d[mu]`, `fdiff`, plus the one-shot
  passes (`contract`, `diracSimplify`, `recombineProjectors`, `canonical`,
  `IdxSum`). `bar[a+b] → bar[a]+bar[b]`, `bar[c x] → c* bar[x]`, terminating at a
  leaf such as `bar[field]`. A distributor never survives wrapped around a
  composite — only around an irreducible leaf, which is then treated like any
  atom.

- **Wrappers** are *semantic containers* whose head stays outermost and absorbs
  its neighbours while maintaining an invariant. There are exactly two:
  - **`INS`** — carries an *index namespace* around a (sub)expression, keeping
    dummy indices disjoint (`INS[a] INS[b] → INS[…]` after renaming clashes).
  - **`Col`** — carries an SU(2) *doublet*; operations distribute into its two
    fixed components.

  `INS[expr]` and `Col[c1, c2]` are legitimate normal forms: they persist, so
  *other* operators keep meeting them.

A wrapper is a **container**, not a structural product. `NC`, `Times`, `Plus`,
`Dot` also persist, but they are products/structural combinators, not wrappers.

### The rule

> **A wrapper (`INS`, `Col`) owns every rule for how a *general* operator acts
> on it, written as an UpValue (`INS /: …`, `Col /: …`). Everything else is a
> DownValue on the operator it defines.**

Consequences:

- When a distributor meets a wrapper it passes *inside* and the wrapper stays
  outermost — e.g. `Conjugate[INS[a]] → INS[Conjugate[a]]`. That meeting point is
  owned by the **wrapper** (UpValue), because what is being protected is the
  wrapper's invariant (index disjointness / doublet structure), not anything
  intrinsic to the distributor. So all such rules live in the `INS` / `Col`
  blocks, even when they reference an operator (e.g. `fdiffINS`, `covD`) defined
  in another module — harmless, because every rule is delayed.
- A rule keyed on a **structural product** (`NC`, `Times`, `Plus`, `Dot`) stays
  a DownValue on the operator: `ConjugateTranspose[NC[a, b]] := NC[CT[b], CT[a]]`
  is a `ConjugateTranspose` DownValue, whereas `NC[Col, Col]` is a `Col`
  UpValue.
- A **specialised** operator whose entire purpose is the wrapped structure keeps
  its DownValues — `ChargeConj`, `SU2T`, `U1Y` are defined *on* doublets, so
  `ChargeConj[col_Col]` is a `ChargeConj` DownValue, not a `Col` UpValue. The
  UpValue convention is only for *general* operators traversing a wrapper.
- For Protected built-ins (`Conjugate`, `ConjugateTranspose`, `Dot`,
  `NonCommutativeMultiply`, `MakeBoxes`) the remaining generic DownValues are
  collected in a single `Unprotect … Protect` block per built-in. Wrapper
  UpValues need no `Unprotect` (they attach to `INS`/`Col`, which we own).

### Everything else

The Up/Down question only arises inside the distributor/wrapper family. The rest
of the package is DownValues/SubValues on its own head with no ambiguity:
constructors (`Declare*`, `SetConjugate`), predicates (`fermionQ`, `scalarQ`, …),
object self-evaluation (`g`, `kd3`, `eps3`), expanders (`SU2T`, `ExplCovD`),
rule-set builders (`renorm`, `INSRule`), and the presentation layer
(`MakeBoxes`, deliberately one centralised block regardless of object).
