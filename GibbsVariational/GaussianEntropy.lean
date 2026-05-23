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

/-- The standard Gaussian measure on `ι → ℝ` for a finite index type `ι`
(the product of one-dimensional `N(0,1)` factors). -/
noncomputable def stdGaussian (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (stdGaussian ι) := by
  unfold stdGaussian; infer_instance

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

lemma klDiv_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  by_cases h : μ ≪ ν
  · rw [klDiv_eq_lintegral_klFun_of_ac (μ := μ.map e) (ν := ν.map e)
      (e.measurableEmbedding.absolutelyContinuous_map h)]
    rw [klDiv_eq_lintegral_klFun_of_ac (μ := μ) (ν := ν) h]
    rw [MeasureTheory.lintegral_map_equiv (μ := ν)
      (f := fun y => ENNReal.ofReal (klFun (((μ.map e).rnDeriv (ν.map e) y).toReal))) e]
    refine lintegral_congr_ae ?_
    filter_upwards [e.measurableEmbedding.rnDeriv_map μ ν] with x hx
    simp [hx]
  · have hmap : ¬ μ.map e ≪ ν.map e := by
      intro hmap
      have hback := e.symm.measurableEmbedding.absolutelyContinuous_map hmap
      exact h (by simpa using hback)
    rw [klDiv_of_not_ac hmap, klDiv_of_not_ac h]

lemma klDiv_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂] :
    klDiv (μ₁.prod μ₂) (ν₁.prod ν₂) = klDiv μ₁ ν₁ + klDiv μ₂ ν₂ := by
  have hswap : klDiv (μ₁.prod μ₂) (μ₁.prod ν₂) = klDiv (μ₂.prod μ₁) (ν₂.prod μ₁) := by
    have h := klDiv_map_measurableEquiv (e := MeasurableEquiv.prodComm) (μ := μ₁.prod μ₂)
      (ν := μ₁.prod ν₂)
    change klDiv (Measure.map Prod.swap (μ₁.prod μ₂)) (Measure.map Prod.swap (μ₁.prod ν₂)) = _
      at h
    symm
    simpa [MeasureTheory.Measure.prod_swap] using h
  have hright : klDiv (μ₂.prod μ₁) (ν₂.prod μ₁) = klDiv μ₂ ν₂ := by
    simpa [Measure.compProd_const] using
      (klDiv_compProd_left (μ := μ₂) (ν := ν₂) (κ := Kernel.const β μ₁))
  calc
    klDiv (μ₁.prod μ₂) (ν₁.prod ν₂)
        = klDiv μ₁ ν₁ + klDiv (μ₁.prod μ₂) (μ₁.prod ν₂) := by
            simpa [Measure.compProd_const] using
              (klDiv_compProd_eq_add (μ := μ₁) (ν := ν₁)
                (κ := Kernel.const α μ₂) (η := Kernel.const α ν₂))
    _ = klDiv μ₁ ν₁ + klDiv (μ₂.prod μ₁) (ν₂.prod μ₁) := by rw [hswap]
    _ = klDiv μ₁ ν₁ + klDiv μ₂ ν₂ := by rw [hright]

lemma klDiv_pi :
    ∀ {n : ℕ} {X : Fin n → Type*} [∀ i, MeasurableSpace (X i)]
      (μ ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
      [∀ i, IsProbabilityMeasure (ν i)],
      klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i)
  | 0, X, _, μ, ν, _, _ => by
      calc
        klDiv (Measure.pi μ) (Measure.pi ν)
            = klDiv ((Measure.pi μ).map (MeasurableEquiv.ofUniqueOfUnique ((i : Fin 0) → X i)
                Unit))
                ((Measure.pi ν).map (MeasurableEquiv.ofUniqueOfUnique ((i : Fin 0) → X i)
                Unit)) := by
                  symm
                  exact klDiv_map_measurableEquiv
                    (e := MeasurableEquiv.ofUniqueOfUnique ((i : Fin 0) → X i) Unit)
                    (μ := Measure.pi μ) (ν := Measure.pi ν)
        _ = 0 := by
            rw [(MeasureTheory.measurePreserving_pi_empty (μ := μ)).map_eq,
              (MeasureTheory.measurePreserving_pi_empty (μ := ν)).map_eq]
            simp
        _ = ∑ i, klDiv (μ i) (ν i) := by simp
  | n + 1, X, _, μ, ν, _, _ => by
      calc
        klDiv (Measure.pi μ) (Measure.pi ν)
            = klDiv ((Measure.pi μ).map (MeasurableEquiv.piFinSuccAbove X 0))
                ((Measure.pi ν).map (MeasurableEquiv.piFinSuccAbove X 0)) := by
                  symm
                  exact klDiv_map_measurableEquiv (e := MeasurableEquiv.piFinSuccAbove X 0)
                    (μ := Measure.pi μ) (ν := Measure.pi ν)
        _ = klDiv ((μ 0).prod (Measure.pi fun i => μ (Fin.succ i)))
              ((ν 0).prod (Measure.pi fun i => ν (Fin.succ i))) := by
                rw [(MeasureTheory.measurePreserving_piFinSuccAbove (μ := μ) 0).map_eq,
                  (MeasureTheory.measurePreserving_piFinSuccAbove (μ := ν) 0).map_eq]
                rfl
        _ = klDiv (μ 0) (ν 0) + klDiv (Measure.pi fun i => μ (Fin.succ i))
              (Measure.pi fun i => ν (Fin.succ i)) := by
                rw [klDiv_prod]
        _ = klDiv (μ 0) (ν 0) + ∑ i, klDiv (μ (Fin.succ i)) (ν (Fin.succ i)) := by
                rw [klDiv_pi (μ := fun i => μ (Fin.succ i)) (ν := fun i => ν (Fin.succ i))]
        _ = ∑ i, klDiv (μ i) (ν i) := by rw [Fin.sum_univ_succ]

/-- KL divergence tensorises over `Measure.pi` for an arbitrary finite index type `ι`
(constant-fibre form). Transported from the `Fin n` case `klDiv_pi` via `Fintype.equivFin`,
using `klDiv` invariance under the reindexing measurable equivalence. -/
lemma klDiv_pi_fintype {ι : Type*} [Fintype ι] {X : Type*} [MeasurableSpace X]
    (μ ν : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i) := by
  let e := Fintype.equivFin ι
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => X) e
  haveI : ∀ j, IsProbabilityMeasure (μ (e.symm j)) := fun j => inferInstance
  haveI : ∀ j, IsProbabilityMeasure (ν (e.symm j)) := fun j => inferInstance
  haveI : ∀ j, SigmaFinite (μ (e.symm j)) := fun j => inferInstance
  haveI : ∀ j, SigmaFinite (ν (e.symm j)) := fun j => inferInstance
  have hstarμ : (Measure.pi μ).map E = Measure.pi (fun j => μ (e.symm j)) := by
    have h := Measure.pi_map_piCongrLeft (β := fun _ : Fin (Fintype.card ι) => X) e
      (μ := fun j => μ (e.symm j))
    rwa [show (fun i => μ (e.symm (e i))) = μ from
      funext fun i => by rw [e.symm_apply_apply]] at h
  have hstarν : (Measure.pi ν).map E = Measure.pi (fun j => ν (e.symm j)) := by
    have h := Measure.pi_map_piCongrLeft (β := fun _ : Fin (Fintype.card ι) => X) e
      (μ := fun j => ν (e.symm j))
    rwa [show (fun i => ν (e.symm (e i))) = ν from
      funext fun i => by rw [e.symm_apply_apply]] at h
  calc klDiv (Measure.pi μ) (Measure.pi ν)
      = klDiv ((Measure.pi μ).map E) ((Measure.pi ν).map E) :=
        (klDiv_map_measurableEquiv E (Measure.pi μ) (Measure.pi ν)).symm
    _ = klDiv (Measure.pi (fun j => μ (e.symm j))) (Measure.pi (fun j => ν (e.symm j))) := by
        rw [hstarμ, hstarν]
    _ = ∑ j, klDiv (μ (e.symm j)) (ν (e.symm j)) := klDiv_pi _ _
    _ = ∑ i, klDiv (μ i) (ν i) := Equiv.sum_comp e.symm (fun i => klDiv (μ i) (ν i))

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
theorem klDiv_stdGaussian_map_add {ι : Type*} [Fintype ι] (h : ι → ℝ) :
    klDiv ((stdGaussian ι).map (· + h)) (stdGaussian ι)
      = ENNReal.ofReal (2⁻¹ * ∑ i, (h i) ^ 2) := by
  have hmap : (stdGaussian ι).map (· + h) = Measure.pi (fun i => gaussianReal (h i) 1) := by
    unfold stdGaussian
    change (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun x i => x i + h i) =
      Measure.pi (fun i => gaussianReal (h i) 1)
    rw [show (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun x i => x i + h i) =
        Measure.pi (fun i => (gaussianReal 0 1).map (fun x : ℝ => x + h i)) by
          simpa using (Measure.pi_map_pi (μ := fun _ : ι => gaussianReal 0 1)
            (f := fun i (x : ℝ) => x + h i) (hf := fun i => by fun_prop))]
    exact congrArg Measure.pi <| funext fun i => by
      simpa using gaussianReal_map_add_const (μ := 0) (v := 1) (y := h i)
  rw [hmap, stdGaussian, klDiv_pi_fintype]
  simp_rw [klDiv_gaussianReal_shift]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    rw [Finset.mul_sum]
  · intro i hi
    positivity

end GibbsVariational
