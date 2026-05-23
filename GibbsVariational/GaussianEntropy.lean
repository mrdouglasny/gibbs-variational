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
open scoped ENNReal NNReal

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

/-- The 1D building block: `KL(N(c,1) ‖ N(0,1)) = ½ c²`.

Direct density computation. The Radon–Nikodym derivative `d N(c,1)/d N(0,1)` is the PDF ratio
`gaussianPDFReal c 1 / gaussianPDFReal 0 1`, whose `√(2π)` normalisations cancel, leaving
`exp(c·x − ½c²)`; so `llr = c·x − ½c²`, and `KL = ∫ llr d N(c,1) = c·c − ½c² = ½c²`
using `∫ x d N(c,1) = c` (`integral_id_gaussianReal`). -/
theorem klDiv_gaussianReal_shift (c : ℝ) :
    klDiv (gaussianReal c 1) (gaussianReal 0 1) = ENNReal.ofReal (2⁻¹ * c ^ 2) := by
  have h1 : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have hac : gaussianReal c 1 ≪ gaussianReal 0 1 :=
    (gaussianReal_absolutelyContinuous c h1).trans (gaussianReal_absolutelyContinuous' 0 h1)
  -- The Radon–Nikodym derivative is the PDF ratio (`volume`-a.e.).
  have hrn : (gaussianReal c 1).rnDeriv (gaussianReal 0 1) =ᵐ[volume]
      fun x => (gaussianPDF 0 1 x)⁻¹ * gaussianPDF c 1 x := by
    have h := Measure.rnDeriv_withDensity_right (gaussianReal c 1) volume
      (f := gaussianPDF 0 1) (measurable_gaussianPDF 0 1).aemeasurable
      (ae_of_all _ fun x => (gaussianPDF_pos 0 h1 x).ne')
      (ae_of_all _ fun _ => gaussianPDF_lt_top.ne)
    rw [← gaussianReal_of_var_ne_zero 0 h1] at h
    filter_upwards [h, rnDeriv_gaussianReal c 1] with x hx hxrn
    rw [hx, hxrn]
  -- Hence `llr` is the linear function `c·x − ½c²` (`N(c,1)`-a.e.).
  have hllr : llr (gaussianReal c 1) (gaussianReal 0 1) =ᵐ[gaussianReal c 1]
      fun x => c * x - 2⁻¹ * c ^ 2 := by
    have hs : Real.sqrt (2 * π) ≠ 0 := by positivity
    filter_upwards [(gaussianReal_absolutelyContinuous c h1).ae_le hrn] with x hx
    have hpdf : (gaussianPDFReal 0 1 x)⁻¹ * gaussianPDFReal c 1 x
        = Real.exp (c * x - 2⁻¹ * c ^ 2) := by
      simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one]
      rw [mul_inv, inv_inv, ← Real.exp_neg, mul_mul_mul_comm, mul_inv_cancel₀ hs, one_mul,
        ← Real.exp_add]
      congr 1
      ring
    unfold llr
    rw [hx, ENNReal.toReal_mul, ENNReal.toReal_inv, toReal_gaussianPDF, toReal_gaussianPDF,
      hpdf, Real.log_exp]
  -- Integrability of the linear `llr`.
  have hid : Integrable (fun x => x) (gaussianReal c 1) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hint : Integrable (llr (gaussianReal c 1) (gaussianReal 0 1)) (gaussianReal c 1) := by
    rw [integrable_congr hllr]
    exact (hid.const_mul c).sub (integrable_const _)
  have hne : klDiv (gaussianReal c 1) (gaussianReal 0 1) ≠ ∞ :=
    klDiv_ne_top_iff.mpr ⟨hac, hint⟩
  -- The mean computation `∫ (c·x − ½c²) d N(c,1) = ½c²`.
  have hmean : ∫ x, (c * x - 2⁻¹ * c ^ 2) ∂(gaussianReal c 1) = 2⁻¹ * c ^ 2 := by
    have hs2 : ∫ x, (c * x - 2⁻¹ * c ^ 2) ∂(gaussianReal c 1)
        = (∫ x, c * x ∂(gaussianReal c 1)) - ∫ _x, (2⁻¹ * c ^ 2 : ℝ) ∂(gaussianReal c 1) :=
      integral_sub (hid.const_mul c) (integrable_const _)
    rw [hs2, integral_const_mul, integral_id_gaussianReal]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul,
      one_mul]
    ring
  have hval : (klDiv (gaussianReal c 1) (gaussianReal 0 1)).toReal = 2⁻¹ * c ^ 2 := by
    rw [toReal_klDiv hac hint,
      show ∫ a, llr (gaussianReal c 1) (gaussianReal 0 1) a ∂(gaussianReal c 1) = 2⁻¹ * c ^ 2
        from (integral_congr_ae hllr).trans hmean]
    simp
  rw [← ENNReal.ofReal_toReal hne, hval]

end GibbsVariational
