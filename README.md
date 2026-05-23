# gibbs-variational

Mathlib-only Lean 4 library for the **Gibbs / Donsker–Varadhan variational principle** and the
**finite-dimensional Boué–Dupuis bound** — the entropy/free-energy duality at the heart of the
modern *variational* approach to constructive QFT moment bounds.

The point: volume-uniform exponential-moment bounds (the kind needed for infinite-volume /
cylinder limits of P(φ)₂) can be obtained from a **single test-drift Ansatz** via the
variational formula, **bypassing the combinatorics of cluster expansions** — and, at the
lattice, the whole argument is *finite-dimensional* (Gaussian IBP + Cameron–Martin shift +
convex duality), needing no stochastic-calculus / Wiener-space machinery.

## Contents

| File | Result | Status |
|---|---|---|
| `GibbsVariational/Variational.lean` | `integral_le_log_integral_exp_add_klDiv` — Gibbs variational inequality `∫f dν ≤ log∫eᶠ dμ + KL(ν‖μ)` | **proved** (bare Mathlib trio) |
| | `log_integral_exp_eq_sSup_sub_klDiv` — Donsker–Varadhan duality | skeleton (`sorry`) |
| `GibbsVariational/GaussianEntropy.lean` | `klDiv_gaussianReal_shift` — 1D building block `KL(N(c,1)‖N(0,1)) = ½c²` | **proved** (bare Mathlib trio) |
| | `klDiv_stdGaussian_map_add` — `KL(shifted std Gaussian ‖ std Gaussian) = ½‖h‖²` (Cameron–Martin cost) | **proved** (bare Mathlib trio) |
| | `klDiv_pi` / `klDiv_prod` / `klDiv_map_measurableEquiv` — KL tensorisation over `Measure.pi` / binary products / invariance under measurable equiv (general, Mathlib-upstreamable) | **proved** |
| `GibbsVariational/BoueDupuis.lean` | `neg_log_integral_exp_neg_le` — finite-dim Boué–Dupuis: `−log∫e^{−V} ≤ ∫V(·+h) + ½‖h‖²` | skeleton |

Built on Mathlib's `InformationTheory.klDiv` (Kullback–Leibler divergence) and
`ProbabilityTheory.gaussianReal`. **Dependency: Mathlib only** (`v4.29.0`).

## Why a separate library

This is general, reusable, Mathlib-upstreamable machinery (the variational principle is
universal — large deviations, Gibbs measures, statistical mechanics), independent of any
particular semigroup or QFT. It sits *below* `markov-semigroups` / `gaussian-field` /
`gaussian-hilbert` / `pphi2`, which can all consume it. Downstream, `pphi2` uses
`neg_log_integral_exp_neg_le` (with a local Wick-cancelling drift) to discharge the
volume-uniform exponential-moment bound for the cylinder S¹×ℝ φ⁴₂ construction
(CYL-1a in `pphi2/docs/cylinder-master-plan.md`).

## Build

```bash
lake exe cache get   # Mathlib oleans
lake build
```
