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
  sorry

end GibbsVariational
