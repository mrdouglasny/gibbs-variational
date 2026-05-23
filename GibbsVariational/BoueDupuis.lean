/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite-dimensional Boué–Dupuis bound

The synthesis of the two prerequisites: applying the Gibbs variational inequality
(`Variational`) to a shifted Gaussian, whose KL cost is the Cameron–Martin quadratic
(`GaussianEntropy`), gives the **finite-dimensional Boué–Dupuis upper bound on the free
energy** — a *single test drift* `h` controls `−log ∫ e^{−V}`:

  `−log ∫ e^{−V} d(stdGaussian n) ≤ ∫ V(· + h) d(stdGaussian n) + ½‖h‖²`.

The full Boué–Dupuis variational formula is the infimum over drifts `h`. For volume-uniform
moment bounds (`pphi2` CYL-1a), one chooses a *local* drift `h` cancelling the most singular
(Wick-ordered) part of `V`, making the right-hand side **extensive** (volume-linear) — so the
bound per unit volume is uniform in the volume, with no cluster expansion.
-/
import GibbsVariational.Variational
import GibbsVariational.GaussianEntropy

open MeasureTheory Real InformationTheory
open scoped ENNReal

namespace GibbsVariational

/-- **Finite-dimensional Boué–Dupuis upper bound on the free energy.**

For the standard finite-dimensional Gaussian and any drift `h`,
`−log ∫ e^{−V} d(stdGaussian n) ≤ ∫ V(· + h) d(stdGaussian n) + ½‖h‖²`.

**Proof strategy.** Apply `integral_le_log_integral_exp_add_klDiv` (`Variational`) with
`μ := stdGaussian n`, `ν := (stdGaussian n).map (· + h)`, and `f := fun x => − V x`:
* `∫ (−V) dν = ∫ (fun x => − V (x + h)) d(stdGaussian n)` by the change-of-variables
  `integral_map` along the shift `(· + h)`;
* `klDiv ν μ = ½‖h‖²` by `klDiv_stdGaussian_map_add` (`GaussianEntropy`).
Substituting and negating both sides yields the stated bound. -/
theorem neg_log_integral_exp_neg_le (n : ℕ) (h : Fin n → ℝ) {V : (Fin n → ℝ) → ℝ}
    (hV : Integrable (fun x => Real.exp (- V x)) (stdGaussian n))
    (hVh : Integrable (fun x => V (x + h)) (stdGaussian n)) :
    - Real.log (∫ x, Real.exp (- V x) ∂(stdGaussian n))
      ≤ (∫ x, V (x + h) ∂(stdGaussian n)) + 2⁻¹ * ∑ i, (h i) ^ 2 := by
  -- The shifted Gaussian `ν := (stdGaussian n).map (· + h)` is a probability measure.
  haveI : IsProbabilityMeasure ((stdGaussian n).map (· + h)) :=
    Measure.isProbabilityMeasure_map (measurable_id.add_const h).aemeasurable
  -- Its relative entropy is the Cameron–Martin cost `½‖h‖²` (P-B); finiteness gives `ν ≪ μ`.
  have hkl : klDiv ((stdGaussian n).map (· + h)) (stdGaussian n)
      = ENNReal.ofReal (2⁻¹ * ∑ i, (h i) ^ 2) := klDiv_stdGaussian_map_add n h
  have h_kl : klDiv ((stdGaussian n).map (· + h)) (stdGaussian n) ≠ ∞ := by
    rw [hkl]; exact ENNReal.ofReal_ne_top
  have hac : (stdGaussian n).map (· + h) ≪ stdGaussian n := (klDiv_ne_top_iff.mp h_kl).1
  have hkl_real : (klDiv ((stdGaussian n).map (· + h)) (stdGaussian n)).toReal
      = 2⁻¹ * ∑ i, (h i) ^ 2 := by
    rw [hkl, ENNReal.toReal_ofReal]; positivity
  -- Change of variables for `f = −V` along the translation equivalence `· + h`.
  have hint_int : Integrable (fun x => - V x) ((stdGaussian n).map (· + h)) :=
    (integrable_map_equiv (MeasurableEquiv.addRight h) (fun x => - V x)).mpr hVh.neg
  have hint_eq : ∫ x, (- V x) ∂((stdGaussian n).map (· + h))
      = - ∫ x, V (x + h) ∂(stdGaussian n) := by
    have h1 : ∫ x, (- V x) ∂((stdGaussian n).map (· + h)) = ∫ x, - V (x + h) ∂(stdGaussian n) :=
      integral_map_equiv (MeasurableEquiv.addRight h) (fun x => - V x)
    rw [h1, integral_neg]
  -- The Gibbs variational inequality (P-A) with `μ = stdGaussian n`, `ν`, `f = −V`.
  have key : ∫ x, (- V x) ∂((stdGaussian n).map (· + h))
      ≤ Real.log (∫ x, Real.exp (- V x) ∂(stdGaussian n)) + 2⁻¹ * ∑ i, (h i) ^ 2 := by
    have hPA := integral_le_log_integral_exp_add_klDiv (μ := stdGaussian n)
      (ν := (stdGaussian n).map (· + h)) (f := fun x => - V x) hac hV hint_int h_kl
    rwa [hkl_real] at hPA
  rw [hint_eq] at key
  linarith

end GibbsVariational
