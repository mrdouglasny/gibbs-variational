/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Gibbs / Donsker–Varadhan variational principle

The entropy/free-energy duality between the Kullback–Leibler divergence (`InformationTheory.klDiv`)
and the log-Laplace transform (cumulant generating functional):

* `∫ f dν ≤ log (∫ eᶠ dμ) + KL(ν‖μ)`        — Gibbs variational inequality (the workhorse);
* `log (∫ eᶠ dμ) = ⨆_ν (∫ f dν − KL(ν‖μ))`  — Donsker–Varadhan duality (full principle).

This is the analytic backbone of the variational (Boué–Dupuis) approach to constructive-QFT
moment bounds. It is pure measure theory over Mathlib's `klDiv`, hence a Mathlib-upstream
candidate. Downstream, the finite-dimensional Gaussian specialization (`BoueDupuis`) discharges
the volume-uniform exponential-moment bound (`pphi2` CYL-1a) without cluster expansions.

## References
* Dupuis–Ellis, *A Weak Convergence Approach to the Theory of Large Deviations* (1997), §1.4.2.
* Donsker–Varadhan; the Gibbs variational principle / Gibbs' inequality.
-/
import Mathlib

open MeasureTheory Real InformationTheory
open scoped ENNReal

namespace GibbsVariational

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- **Gibbs variational inequality** (the workhorse).

For probability measures with `ν ≪ μ`, `eᶠ ∈ L¹(μ)`, `f ∈ L¹(ν)`, and finite KL,
`∫ f dν ≤ log (∫ eᶠ dμ) + KL(ν‖μ)`.

**Proof strategy.** Tilt `μ` to `μ_f := μ.withDensity (fun x => ENNReal.ofReal (exp (f x) / Z))`
with `Z := ∫ eᶠ dμ > 0`; then `μ_f` is a probability measure and `ν ≪ μ_f`. The
Radon–Nikodym chain rule gives, `ν`-a.e., `llr ν μ_f = llr ν μ + log Z − f`, hence
`KL(ν‖μ_f) = KL(ν‖μ) + log Z − ∫ f dν`. Gibbs' inequality `0 ≤ KL(ν‖μ_f)`
(`klDiv` is `ℝ≥0∞`-valued, so nonneg by type) rearranges to the claim.

Key Mathlib API: the `klDiv = ∫ llr dμ` form (`klDiv_eq_integral_klFun` /
`toReal_klDiv_eq_integral_…`), `Measure.rnDeriv_withDensity`, the rnDeriv chain rule, and the
`llr` lemmas (`LogLikelihoodRatio.lean`). -/
theorem integral_le_log_integral_exp_add_klDiv
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμν : ν ≪ μ)
    {f : α → ℝ} (hf_exp : Integrable (fun x => Real.exp (f x)) μ)
    (hf_int : Integrable f ν) (h_kl : klDiv ν μ ≠ ∞) :
    ∫ x, f x ∂ν ≤ Real.log (∫ x, Real.exp (f x) ∂μ) + (klDiv ν μ).toReal := by
  sorry

/-- **Donsker–Varadhan duality** (the full variational principle; the upstream goal).

`log (∫ eᶠ dμ)` equals the supremum, over probability measures `ν ≪ μ`, of
`∫ f dν − KL(ν‖μ)`; the supremum is attained at the tilted measure `μ_f`.

**Proof strategy.** The upper bound on each element of the set is `integral_le_…` above
(rearranged: `∫ f dν − KL(ν‖μ) ≤ log Z`). Attainment plugs `ν = μ_f`, where
`KL(μ_f‖μ) = ∫ f dμ_f − log Z`, giving equality. -/
theorem log_integral_exp_eq_sSup_sub_klDiv
    [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf_exp : Integrable (fun x => Real.exp (f x)) μ) :
    Real.log (∫ x, Real.exp (f x) ∂μ)
      = sSup {r : ℝ | ∃ ν : Measure α, IsProbabilityMeasure ν ∧ ν ≪ μ ∧
          Integrable f ν ∧ r = ∫ x, f x ∂ν - (klDiv ν μ).toReal} := by
  sorry

end GibbsVariational
