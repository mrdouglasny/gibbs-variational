/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cameron–Martin relative entropy of a finite-dimensional Gaussian

The relative entropy (KL divergence) between a shifted standard Gaussian and the standard
Gaussian is exactly the Cameron–Martin cost of the shift:

  `KL((stdGaussian n).map (· + h) ‖ stdGaussian n) = ½‖h‖²`.

This is the second prerequisite of the variational (Boué–Dupuis) route: it identifies the
abstract `klDiv` of a Gaussian shift with the explicit quadratic drift cost. Mathlib-only —
the Cameron–Martin shift density is re-derived from `ProbabilityTheory.gaussianReal`, not
imported from the heavier project-specific instance lemmas.
-/
import Mathlib

open MeasureTheory Real InformationTheory ProbabilityTheory
open scoped ENNReal

namespace GibbsVariational

/-- The standard `n`-dimensional Gaussian measure on `Fin n → ℝ`. -/
noncomputable def stdGaussian (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance (n : ℕ) : IsProbabilityMeasure (stdGaussian n) := by
  unfold stdGaussian; infer_instance

/-- **Cameron–Martin relative entropy** for the standard finite-dimensional Gaussian.

Shifting the standard Gaussian by `h` costs relative entropy `½‖h‖²`:
`KL((stdGaussian n).map (· + h) ‖ stdGaussian n) = ½ ∑ᵢ (h i)²`.

**Proof strategy.** The Cameron–Martin density factorizes over coordinates:
`d((stdGaussian n).map (·+h)) / d(stdGaussian n) (x) = exp(∑ᵢ (h i · x i − ½ (h i)²))`
(product of the 1D Gaussian shift densities `exp(hᵢ xᵢ − ½ hᵢ²)`, each from `gaussianReal`).
Hence, `(shifted)`-a.e., `llr (shifted) (stdGaussian n) (x) = ∑ᵢ h i · x i − ½ ∑ᵢ (h i)²`, so
`KL = ∫ llr d(shifted) = ∑ᵢ h i · 𝔼_shifted[xᵢ] − ½ ∑ᵢ (h i)² = ∑ᵢ (h i)² − ½ ∑ᵢ (h i)²`
`= ½ ∑ᵢ (h i)²`, using `𝔼_shifted[xᵢ] = h i` (the shifted Gaussian has mean `h`).

Reduce to the 1D case `klDiv (gaussianReal (h i) 1) (gaussianReal 0 1) = ½ (h i)²` (a direct
density computation) and tensorize via `klDiv` of product measures over `Measure.pi`. -/
theorem klDiv_stdGaussian_map_add (n : ℕ) (h : Fin n → ℝ) :
    klDiv ((stdGaussian n).map (· + h)) (stdGaussian n)
      = ENNReal.ofReal (2⁻¹ * ∑ i, (h i) ^ 2) := by
  sorry

/-- The 1D building block: `KL(N(c,1) ‖ N(0,1)) = ½ c²`. Direct density computation
(`gaussianReal` PDF ratio is `exp(c x − ½ c²)`). -/
theorem klDiv_gaussianReal_shift (c : ℝ) :
    klDiv (gaussianReal c 1) (gaussianReal 0 1) = ENNReal.ofReal (2⁻¹ * c ^ 2) := by
  sorry

end GibbsVariational
