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

**Proof.** Write `Z := ∫ eᶠ dμ > 0` and `g := d ν / d μ` (the real Radon–Nikodym derivative).
Since `KL(ν‖μ) = ∫ llr ν μ dν = ∫ log g dν` (`toReal_klDiv`, the `±1` from the unit masses
cancelling), it suffices to show `∫ (f − log g − log Z) dν ≤ 0`. Pointwise `ν`-a.e. (where
`g > 0`), `f − log g − log Z = log (eᶠ / (g·Z)) ≤ eᶠ / (g·Z) − 1` by
`Real.log_le_sub_one_of_pos`. Integrating and changing variables `∫ φ dν = ∫ g·φ dμ`
(`withDensity_rnDeriv_eq` + `integral_withDensity_eq_integral_toReal_smul`), the bound becomes
`Z⁻¹ · ∫ g·(eᶠ/g) dμ − 1 ≤ Z⁻¹ · Z − 1 = 0`, using `g·(eᶠ/g) ≤ eᶠ` everywhere. -/
theorem integral_le_log_integral_exp_add_klDiv
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμν : ν ≪ μ)
    {f : α → ℝ} (hf_exp : Integrable (fun x => Real.exp (f x)) μ)
    (hf_int : Integrable f ν) (h_kl : klDiv ν μ ≠ ∞) :
    ∫ x, f x ∂ν ≤ Real.log (∫ x, Real.exp (f x) ∂μ) + (klDiv ν μ).toReal := by
  set Z : ℝ := ∫ x, Real.exp (f x) ∂μ with hZ
  set g : α → ℝ := fun x => (ν.rnDeriv μ x).toReal with hg
  have hg_meas : Measurable g := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  -- `Z > 0` since `eᶠ > 0` everywhere and `μ` is a probability measure.
  have hZpos : 0 < Z := by
    rw [hZ, integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le) hf_exp]
    have hsupp : Function.support (fun x => Real.exp (f x)) = Set.univ := by
      ext x; simp [Function.mem_support, Real.exp_ne_zero]
    rw [hsupp, measure_univ]; exact one_pos
  -- KL as the `llr` integral.
  have hllr_int : Integrable (llr ν μ) ν := (klDiv_ne_top_iff.mp h_kl).2
  have hkl_eq : (klDiv ν μ).toReal = ∫ x, llr ν μ x ∂ν := by
    rw [toReal_klDiv hμν hllr_int]; simp
  -- Change of variables `∫ φ dν = ∫ g·φ dμ`.
  have hcov : ∀ φ : α → ℝ, ∫ x, φ x ∂ν = ∫ x, g x * φ x ∂μ := by
    intro φ
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq ν μ hμν]
    rw [integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv ν μ)
      (Measure.rnDeriv_lt_top ν μ) φ]
    simp only [smul_eq_mul, hg]
  -- `g > 0` and `g < ∞`, hence `0 < g`, holds `ν`-a.e.
  have hg_pos : ∀ᵐ x ∂ν, 0 < g x := by
    have h1 : ∀ᵐ x ∂ν, 0 < ν.rnDeriv μ x := Measure.rnDeriv_pos hμν
    have h2 : ∀ᵐ x ∂ν, ν.rnDeriv μ x < ∞ := hμν.ae_le (Measure.rnDeriv_lt_top ν μ)
    filter_upwards [h1, h2] with x hx1 hx2
    exact ENNReal.toReal_pos hx1.ne' hx2.ne
  -- `g·(eᶠ/g) ≤ eᶠ` pointwise, and the LHS is `μ`-integrable (dominated by `eᶠ`).
  have hbound : ∀ x, g x * (Real.exp (f x) / g x) ≤ Real.exp (f x) := by
    intro x
    rcases eq_or_ne (g x) 0 with hgx | hgx
    · simp [hgx, (Real.exp_pos _).le]
    · rw [mul_comm, div_mul_cancel₀ _ hgx]
  have hgexp_nonneg : ∀ x, 0 ≤ g x * (Real.exp (f x) / g x) := by
    intro x
    exact mul_nonneg (ENNReal.toReal_nonneg)
      (div_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)
  have hgexp_meas : AEStronglyMeasurable (fun x => g x * (Real.exp (f x) / g x)) μ := by
    have hgm : AEMeasurable g μ := hg_meas.aemeasurable
    have hfm : AEMeasurable (fun x => Real.exp (f x)) μ := hf_exp.aestronglyMeasurable.aemeasurable
    exact (hgm.mul (hfm.div hgm)).aestronglyMeasurable
  have hgexp_int : Integrable (fun x => g x * (Real.exp (f x) / g x)) μ :=
    Integrable.mono' hf_exp hgexp_meas
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hgexp_nonneg x)]; exact hbound x)
  -- `∫ eᶠ/g dν = ∫ g·(eᶠ/g) dμ ≤ Z`.
  have hsmall : ∫ x, Real.exp (f x) / g x ∂ν ≤ Z := by
    rw [hcov (fun x => Real.exp (f x) / g x)]
    exact integral_mono hgexp_int hf_exp hbound
  -- Integrability of `eᶠ/g` w.r.t. `ν` (transfer of `hgexp_int`).
  have hinv_int : Integrable (fun x => Real.exp (f x) / g x) ν := by
    rw [← Measure.withDensity_rnDeriv_eq ν μ hμν,
      integrable_withDensity_iff_integrable_smul' (Measure.measurable_rnDeriv ν μ)
        (Measure.rnDeriv_lt_top ν μ)]
    simpa only [smul_eq_mul, hg] using hgexp_int
  -- Core: `∫ (f − log g − log Z) dν ≤ 0`.
  have hcore : ∫ x, (f x - Real.log (g x) - Real.log Z) ∂ν ≤ 0 := by
    -- pointwise bound, `ν`-a.e.
    have hpt : ∀ᵐ x ∂ν,
        f x - Real.log (g x) - Real.log Z ≤ Real.exp (f x) / (g x * Z) - 1 := by
      filter_upwards [hg_pos] with x hgx
      have ht : (0 : ℝ) < Real.exp (f x) / (g x * Z) :=
        div_pos (Real.exp_pos _) (mul_pos hgx hZpos)
      have hlog : Real.log (Real.exp (f x) / (g x * Z))
          = f x - Real.log (g x) - Real.log Z := by
        rw [Real.log_div (Real.exp_ne_zero _) (by positivity),
          Real.log_exp, Real.log_mul hgx.ne' hZpos.ne']
        ring
      calc f x - Real.log (g x) - Real.log Z
          = Real.log (Real.exp (f x) / (g x * Z)) := hlog.symm
        _ ≤ Real.exp (f x) / (g x * Z) - 1 := Real.log_le_sub_one_of_pos ht
    -- `∫ eᶠ/(g·Z) dν` is integrable (rescaled `hinv_int`).
    have h1 : Integrable (fun x => Real.exp (f x) / (g x * Z)) ν := by
      have heq : (fun x => Real.exp (f x) / (g x * Z))
          = fun x => Z⁻¹ * (Real.exp (f x) / g x) := by
        ext x; rw [div_mul_eq_div_div]; ring
      rw [heq]; exact hinv_int.const_mul Z⁻¹
    have hrhs_int : Integrable (fun x => Real.exp (f x) / (g x * Z) - 1) ν :=
      h1.sub (integrable_const 1)
    have hlhs_int : Integrable (fun x => f x - Real.log (g x) - Real.log Z) ν :=
      (hf_int.sub hllr_int).sub (integrable_const _)
    calc ∫ x, (f x - Real.log (g x) - Real.log Z) ∂ν
        ≤ ∫ x, (Real.exp (f x) / (g x * Z) - 1) ∂ν :=
          integral_mono_ae hlhs_int hrhs_int hpt
      _ = (∫ x, Real.exp (f x) / (g x * Z) ∂ν) - 1 := by
          rw [integral_sub h1 (integrable_const 1)]; simp
      _ = Z⁻¹ * (∫ x, Real.exp (f x) / g x ∂ν) - 1 := by
          congr 1
          rw [← integral_const_mul]
          congr 1; ext x; rw [div_mul_eq_div_div]; ring
      _ ≤ Z⁻¹ * Z - 1 := by
          have := mul_le_mul_of_nonneg_left hsmall (by positivity : (0:ℝ) ≤ Z⁻¹)
          linarith
      _ = 0 := by rw [inv_mul_cancel₀ hZpos.ne']; norm_num
  -- Conclude.
  have hsplit : ∫ x, (f x - Real.log (g x) - Real.log Z) ∂ν
      = (∫ x, f x ∂ν) - (∫ x, llr ν μ x ∂ν) - Real.log Z := by
    have hint1 : Integrable (fun x => Real.log (g x)) ν := hllr_int
    have hs1 : ∫ x, (f x - Real.log (g x)) ∂ν
        = (∫ x, f x ∂ν) - ∫ x, Real.log (g x) ∂ν := integral_sub hf_int hint1
    have hs2 : ∫ x, (f x - Real.log (g x) - Real.log Z) ∂ν
        = (∫ x, (f x - Real.log (g x)) ∂ν) - ∫ x, (Real.log Z) ∂ν :=
      integral_sub (hf_int.sub hint1) (integrable_const _)
    have hc : ∫ _x, (Real.log Z) ∂ν = Real.log Z := by simp
    have hllr_eq : ∫ x, Real.log (g x) ∂ν = ∫ x, llr ν μ x ∂ν := rfl
    rw [hs2, hs1, hc, hllr_eq]
  rw [hkl_eq]
  rw [hsplit] at hcore
  linarith

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
