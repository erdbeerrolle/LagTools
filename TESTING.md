# Testing notes

Coverage status of `Tests.wlt` and a prioritised backlog of what still needs
covering. Run the suite with `make test`.

## Done — Batch 1

- **`ConjugateTranspose` (dagger)** — previously almost untested. Now: atomic
  rules (γ, γ0, γ5, P_L, P_R, fermion, bar-fermion); NC-chain reversal; the
  vector-current Hermiticity identity; the dagger involution; and a Hermiticity
  round-trip on a coupled term.
- **`NC` core** — chain flattening and the `ga0.ga0 -> 1` collapse (the latter
  is what makes CT chains reduce).
- **Refactor-specific holes** closed: `ConjugateTranspose[INS[...]]` push-through
  and `NC[Col, Col]` (two- and three-argument su2-scalar forms) — both were
  converted from operator DownValues to wrapper UpValues and previously had no
  active test (the old `Col-NC-distributes` test was commented out).

## Backlog — not yet covered

### `bar` (Dirac conjugate)
- Antilinearity with a **genuinely complex** coupling: `bar[c x] -> Conjugate[c] bar[x]`.
  Every current `bar` test uses real couplings, so `Conjugate` never actually
  does anything.
- Chiral flip `bar[PL ** f] -> bar[f] ** PR` (and PR -> PL) tested directly.

### `Conjugate`
- `Conjugate[eps3[...]]` and `Conjugate[kd3[...]]` reality rules.
- `Conjugate[a_Times]` distribution in isolation.

### `Dot` / SU(2) linearity (Gauge module)
- The `Dot[x___, c_?su2ScalarQ * a_, y___]` pull-through rules (an SU(2)-scalar
  factor threaded out of a `Dot` product). Only Col-specific `Dot` is tested.

### `renorm` family
- `renorm` for the `bar[f]` leg (only the `el` leg is tested).
- `renormBoson` and `renormMix` (untested entirely).
- `recombineProjectors` on larger / nested sums.

### Integration — declared machinery -> vertex
- Chain `DeclareGaugeDoublet` / `DeclareCovD` -> `ExplGaugeMult` / `ExplCovD`
  -> `feynmanRule` end to end, so INS dummy-index bookkeeping meets the new GI
  dummies introduced by `ExplCovD` expansion in a realistic term. Currently each
  declaration mechanism and `feynmanRule` are tested only in isolation.

### Integration — `EWSMLagrangian.wl`
- Smoke test: the model file loads without error and a couple of known `Ltotal`
  coefficients match. Top-level safety net for the whole pipeline.
