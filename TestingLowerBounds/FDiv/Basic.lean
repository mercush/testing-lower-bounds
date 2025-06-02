/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.Notation
import TestingLowerBounds.ForMathlib.Integrable
import TestingLowerBounds.IntegrableFRNDeriv
/-!

# f-Divergences

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

The most natural type for `f` is `ℝ≥0∞ → EReal` since we apply it to an `ℝ≥0∞`-valued RN derivative,
and its value can be in general both positive or negative, and potentially +∞.
However, we use `ℝ → ℝ` instead, for the following reasons:
* domain: convexity results like `ConvexOn.map_average_le` don't work for `ℝ≥0∞` because they
  require a normed space with scalars in `ℝ`, but `ℝ≥0∞` is a module over `ℝ≥0`.
  Also, the RN derivative is almost everywhere finite for σ-finite measures, so losing ∞ in the
  domain is not an issue.
* codomain: `EReal` is underdeveloped, and all functions we will actually use are finite anyway.

Most results will require these conditions on `f`:
`(hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0)) (hf_one : f 1 = 0)`

## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {f g : ℝ → ℝ}

open Classical in
/-- f-Divergence of two measures. -/
noncomputable
def fDiv (f : ℝ → ℝ) (μ ν : Measure α) : EReal :=
  if ¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν then ⊤
  else ∫ x, f ((∂μ/∂ν) x).toReal ∂ν + derivAtTop f * μ.singularPart ν .univ

lemma fDiv_of_not_integrable (hf : ¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν = ⊤ := if_pos hf

lemma fDiv_of_integrable (hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν + derivAtTop f * μ.singularPart ν .univ :=
  if_neg (not_not.mpr hf)

lemma fDiv_ne_bot [IsFiniteMeasure μ] (hf_cvx : ConvexOn ℝ (Ici 0) f) : fDiv f μ ν ≠ ⊥ := by
  rw [fDiv]
  split_ifs with h
  · simp only [ne_eq, EReal.add_eq_bot_iff, EReal.coe_ne_bot, false_or]
    rw [EReal.mul_eq_bot]
    simp [hf_cvx.derivAtTop_ne_bot, not_lt.mpr (EReal.coe_ennreal_nonneg _), measure_ne_top]
  · simp

lemma fDiv_ne_bot_of_derivAtTop_nonneg (hf : 0 ≤ derivAtTop f) : fDiv f μ ν ≠ ⊥ := by
  rw [fDiv]
  split_ifs with h
  · simp only [ne_eq, EReal.add_eq_bot_iff, EReal.coe_ne_bot, false_or]
    rw [EReal.mul_eq_bot]
    have h_ne_bot : derivAtTop f ≠ ⊥ := fun h_eq ↦ by
      rw [h_eq] at hf
      simp at hf
    simp [h_ne_bot, not_lt.mpr (EReal.coe_ennreal_nonneg _), not_lt.mpr hf]
  · simp

section SimpleValues

@[simp] lemma fDiv_zero (μ ν : Measure α) : fDiv (fun _ ↦ 0) μ ν = 0 := by simp [fDiv]

@[simp]
lemma fDiv_zero_measure_left (ν : Measure α) [IsFiniteMeasure ν] : fDiv f 0 ν = f 0 * ν .univ := by
  have : (fun x ↦ f ((∂0/∂ν) x).toReal) =ᵐ[ν] fun _ ↦ f 0 := by
    filter_upwards [ν.rnDeriv_zero] with x hx
    rw [hx]
    simp
  rw [fDiv_of_integrable]
  · simp only [Measure.singularPart_zero, Measure.coe_zero, Pi.zero_apply, EReal.coe_ennreal_zero,
      mul_zero, add_zero]
    rw [integral_congr_ae this, mul_comm (f 0 : EReal), integral_const, smul_eq_mul, EReal.coe_mul,
      ← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  · rw [integrable_congr this]
    exact integrable_const _

@[simp]
lemma fDiv_zero_measure_right (μ : Measure α) : fDiv f μ 0 = derivAtTop f * μ .univ := by
  rw [fDiv_of_integrable] <;> simp

@[simp]
lemma fDiv_const (c : ℝ) (μ ν : Measure α) [IsFiniteMeasure ν] :
    fDiv (fun _ ↦ c) μ ν = ν .univ * c := by
  rw [fDiv_of_integrable (integrable_const c), integral_const]
  simp only [smul_eq_mul, EReal.coe_mul, derivAtTop_const, zero_mul, add_zero]
  congr
  rw [EReal.coe_ennreal_toReal]
  exact measure_ne_top _ _

lemma fDiv_const' {c : ℝ} (hc : 0 ≤ c) (μ ν : Measure α) :
    fDiv (fun _ ↦ c) μ ν = ν .univ * c := by
  by_cases hν : IsFiniteMeasure ν
  · exact fDiv_const c μ ν
  · have : ν .univ = ∞ := by
      by_contra h_univ
      exact absurd ⟨Ne.lt_top h_univ⟩ hν
    rw [this]
    by_cases hc0 : c = 0
    · simp [hc0]
    rw [fDiv_of_not_integrable]
    · simp only [EReal.coe_ennreal_top]
      rw [EReal.top_mul_of_pos]
      refine lt_of_le_of_ne ?_ (Ne.symm ?_)
      · exact mod_cast hc
      · exact mod_cast hc0
    · rw [integrable_const_iff]
      simp [hc0, this]

lemma fDiv_self (hf_one : f 1 = 0) (μ : Measure α) [SigmaFinite μ] : fDiv f μ μ = 0 := by
  have h : (fun x ↦ f (μ.rnDeriv μ x).toReal) =ᵐ[μ] 0 := by
    filter_upwards [μ.rnDeriv_self] with x hx
    rw [hx, ENNReal.one_toReal, hf_one]
    rfl
  rw [fDiv_of_integrable]
  swap; · rw [integrable_congr h]; exact integrable_zero _ _ _
  rw [integral_congr_ae h]
  simp only [Pi.zero_apply, integral_zero, EReal.coe_zero, zero_add]
  rw [Measure.singularPart_self]
  simp

@[simp]
lemma fDiv_id (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    fDiv id μ ν = μ .univ := by
  by_cases h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_of_integrable h_int]
    simp only [id_eq, derivAtTop_id, one_mul]
    rw [← setIntegral_univ, Measure.setIntegral_toReal_rnDeriv_eq_withDensity]
    have h_ne_top : (ν.withDensity (∂μ/∂ν)) .univ ≠ ∞ := by
      rw [withDensity_apply _ .univ, setLIntegral_univ]
      rwa [integrable_toReal_iff] at h_int
      · exact (μ.measurable_rnDeriv ν).aemeasurable
      · exact μ.rnDeriv_ne_top ν
    rw [EReal.coe_ennreal_toReal h_ne_top]
    norm_cast
    conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
    simp
  · rw [fDiv_of_not_integrable h_int]
    symm
    by_contra h_ne_top
    have : IsFiniteMeasure μ := ⟨Ne.lt_top ?_⟩
    swap; · rw [← EReal.coe_ennreal_top] at h_ne_top; exact mod_cast h_ne_top
    refine h_int <| integrable_toReal_of_lintegral_ne_top (μ.measurable_rnDeriv ν).aemeasurable ?_
    exact (μ.lintegral_rnDeriv_lt_top _).ne

@[simp]
lemma fDiv_id' (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    fDiv (fun x ↦ x) μ ν = μ .univ := fDiv_id μ ν

end SimpleValues

section Congr

lemma fDiv_congr' (μ ν : Measure α) (hfg : ∀ᵐ x ∂ν.map (fun x ↦ ((∂μ/∂ν) x).toReal), f x = g x)
    (hfg' : f =ᶠ[atTop] g) :
    fDiv f μ ν = fDiv g μ ν := by
  have h : (fun a ↦ f ((∂μ/∂ν) a).toReal) =ᶠ[ae ν] fun a ↦ g ((∂μ/∂ν) a).toReal :=
    ae_of_ae_map (μ.measurable_rnDeriv ν).ennreal_toReal.aemeasurable hfg
  rw [fDiv, derivAtTop_congr hfg']
  congr 2
  · exact eq_iff_iff.mpr ⟨fun hf ↦ hf.congr h, fun hf ↦ hf.congr h.symm⟩
  · exact EReal.coe_eq_coe_iff.mpr (integral_congr_ae h)

lemma fDiv_congr (μ ν : Measure α) (h : ∀ x ≥ 0, f x = g x) :
    fDiv f μ ν = fDiv g μ ν := by
  have (x : α) : f ((∂μ/∂ν) x).toReal = g ((∂μ/∂ν) x).toReal := h _ ENNReal.toReal_nonneg
  simp_rw [fDiv, this, derivAtTop_congr_nonneg h]
  congr
  simp_rw [this]

lemma fDiv_congr_measure {μ ν : Measure α} {μ' ν' : Measure β}
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
      ↔ Integrable (fun x ↦ f ((∂μ'/∂ν') x).toReal) ν')
    (h_eq : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν →
      Integrable (fun x ↦ f ((∂μ'/∂ν') x).toReal) ν' →
      ∫ x, f ((∂μ/∂ν) x).toReal ∂ν = ∫ x, f ((∂μ'/∂ν') x).toReal ∂ν')
    (h_sing : μ.singularPart ν univ = μ'.singularPart ν' univ) :
    fDiv f μ ν = fDiv f μ' ν' := by
  rw [fDiv, fDiv, h_int, h_sing]
  split_ifs with h
  · rw [h_eq (h_int.mpr h) h]
  · rfl

lemma fDiv_eq_zero_of_forall_nonneg (μ ν : Measure α) (hf : ∀ x ≥ 0, f x = 0) :
    fDiv f μ ν = 0 := by
  rw [← fDiv_zero (μ := μ) (ν := ν)]
  exact fDiv_congr μ ν hf

end Congr

section MulAdd

lemma fDiv_mul {c : ℝ} (hc : 0 ≤ c) (hf_cvx : ConvexOn ℝ (Ici 0) f) (μ ν : Measure α) :
    fDiv (fun x ↦ c * f x) μ ν = c * fDiv f μ ν := by
  by_cases hc0 : c = 0
  · simp [hc0]
  by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_of_integrable h_int, fDiv_of_integrable]
    swap; · exact h_int.const_mul _
    rw [integral_mul_left, derivAtTop_const_mul hf_cvx hc0,
      EReal.coe_mul, EReal.coe_mul_add_of_nonneg hc, mul_assoc]
  · rw [fDiv_of_not_integrable h_int, fDiv_of_not_integrable]
    · rw [EReal.mul_top_of_pos]
      norm_cast
      exact lt_of_le_of_ne hc (Ne.symm hc0)
    · refine fun h ↦ h_int ?_
      have : (fun x ↦ f ((∂μ/∂ν) x).toReal) = (fun x ↦ c⁻¹ * (c * f ((∂μ/∂ν) x).toReal)) := by
        ext; rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
      rw [this]
      exact h.const_mul _

lemma fDiv_mul_of_ne_top (c : ℝ) (hf_cvx : ConvexOn ℝ (Ici 0) f) (h_top : derivAtTop f ≠ ⊤)
    (μ ν : Measure α) [IsFiniteMeasure μ] (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv (fun x ↦ c * f x) μ ν = c * fDiv f μ ν := by
  by_cases hc0 : c = 0
  · simp [hc0]
  rw [fDiv_of_integrable h_int, fDiv_of_integrable]
  swap; · exact h_int.const_mul _
  rw [integral_mul_left, derivAtTop_const_mul hf_cvx hc0]
  lift derivAtTop f to ℝ using ⟨h_top, hf_cvx.derivAtTop_ne_bot⟩ with df
  rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  norm_cast
  ring

-- TODO: in the case where both functions are convex, integrability of the sum is equivalent to
-- integrability of both, and we don't need hf and hg.
-- In general it's not true that if the sum is integrable then both are, even if the functions are
-- convex, take for example f(x) = -x and g(x) = x with the Lebesgue measure. But maybe with some
-- additional hypothesis it's true.
lemma fDiv_add [IsFiniteMeasure μ] (hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (hg : Integrable (fun x ↦ g ((∂μ/∂ν) x).toReal) ν)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hg_cvx : ConvexOn ℝ (Ici 0) g) :
    fDiv (fun x ↦ f x + g x) μ ν = fDiv f μ ν + fDiv g μ ν := by
  rw [fDiv_of_integrable (hf.add hg), integral_add hf hg, fDiv_of_integrable hf,
    fDiv_of_integrable hg, derivAtTop_add hf_cvx hg_cvx]
  simp only [EReal.coe_add]
  rw [add_assoc, add_assoc]
  congr 1
  conv_rhs => rw [← add_assoc, add_comm, ← add_assoc, add_comm]
  congr 1
  rw [← EReal.coe_ennreal_toReal]
  · rw [add_comm, EReal.add_mul_coe_of_nonneg ENNReal.toReal_nonneg]
  · exact measure_ne_top _ _

noncomputable def conjugate_fn_finite (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ x * f (1/x)

noncomputable def conjugate_fn (f : ℝ → ℝ) : ℝ → ℝ := by
  exact fun x ↦ if x = 0 then (derivAtTop f).toReal else conjugate_fn_finite f x

lemma derivAtTop_eq_lim_conjugate (f : ℝ → ℝ) (hd : derivAtTop f ≠ ⊤) (hb : derivAtTop f ≠ ⊥):
    Tendsto (fun x ↦ x * f (1/x)) (𝓝[Set.Ioi 0] 0) (𝓝 ((derivAtTop f).toReal)) := by
  sorry -- Change of variables from derivAtTop definition

lemma lim_conjugate_fn (f : ℝ → ℝ) (hd : derivAtTop f ≠ ⊤) (hb : derivAtTop f ≠ ⊥):
    Tendsto (conjugate_fn f) (𝓝 0) (𝓝 (conjugate_fn f 0)) := by
  sorry

lemma conjugate_convex_finite (hf_cvx : ConvexOn ℝ (Ioi 0) f)  :
    ConvexOn ℝ (Ioi 0) (conjugate_fn_finite f) := by

  -- Use the characterization: ConvexOn s g ↔ ∀ x y ∈ s, ∀ a b ≥ 0, a + b = 1 → g(ax + by) ≤ ag(x) + bg(y)
  rw [ConvexOn]
  unfold conjugate_fn_finite
  constructor
  · exact convex_Ioi 0
  · intro x hx y hy a b ha hb hab
    set z := a • x + b • y with hz
    have hz_pos : 0 < z := by
      simp only [z]
      by_cases hb_pos : 0 < b
      · -- Case: b > 0
        cases' ha.eq_or_lt with ha_zero ha_pos
        · -- Subcase: a = 0, b > 0
          rw [← ha_zero, zero_smul, zero_add]
          exact smul_pos hb_pos (mem_Ioi.mp hy)
        · -- Subcase: a > 0, b > 0
          exact add_pos (smul_pos ha_pos (mem_Ioi.mp hx)) (smul_pos hb_pos (mem_Ioi.mp hy))
      · -- Case: b ≤ 0
        -- Since hb : 0 ≤ b and ¬(0 < b), we have b = 0
        have hb_zero : b = 0 := le_antisymm (le_of_not_gt hb_pos) hb
        rw [hb_zero, zero_smul, add_zero]
        -- Now we need a > 0 (can't have both a = 0 and b = 0 since a + b = 1)
        rw [hb_zero] at hab
        simp [add_zero] at hab
        rw [hab, one_smul]
        exact hx
    set w1 := a * x / z with hw₁
    set w2 := b * y / z with hw₂
    have hw_sum : w1 + w2 = 1 := by
      simp [w1, w2, z]
      rw [← add_div]
      rw [div_self]
      show z ≠ 0
      apply hz_pos.ne'

    have rhs_transform : a • (x * f (1/x)) + b • (y * f (1/y)) = z * (w1 * f (1/x) + w2 * f (1/y)) := by
      -- Expand w1 and w2 definitions
      simp [w1, w2]
      -- Now we have: a • (x * f (1/x)) + b • (y * f (1/y)) = z * ((a * x / z) * f (1/x) + (b * y / z) * f (1/y))
      field_simp
      simp only [mul_assoc]
      -- This should simplify to: a * x * f (1/x) + b * y * f (1/y)
      -- And since • is the same as * in ℝ, this matches the LHS
    have left_transform : 1/z = w1 * (1 / x) + w2 * (1 / y) := by
      simp [w1, w2, one_div]
      -- Goal becomes: a * x / z / x + b * y / z / y = 1/z
      field_simp [div_div]
      field_simp [ne_of_gt (mem_Ioi.mp hx), ne_of_gt (mem_Ioi.mp hy), ne_of_gt hz_pos]
      -- This should give: (a + b) / z = 1/z
      field_simp [mul_assoc, mul_comm, ← mul_add]  -- Use a + b = 1
      field_simp [mul_comm a, mul_comm b, mul_assoc x 2, mul_comm x 3, ← mul_assoc x, ← mul_assoc y, mul_comm x y, ← mul_add]
      rw [hab]
      field_simp
      ac_rfl
    rw [rhs_transform]
    rw [mul_le_mul_left hz_pos]
    rw [left_transform]
    apply hf_cvx.2  -- Use the convexity directly
    rw [Set.mem_Ioi, one_div]
    exact inv_pos.mpr (mem_Ioi.mp hx)
    rw [Set.mem_Ioi, one_div]
    exact inv_pos.mpr (mem_Ioi.mp hy)
    rw [hw₁]  -- Unfold w1 = a * x / z
    exact div_nonneg (mul_nonneg ha (le_of_lt (mem_Ioi.mp hx))) (le_of_lt hz_pos)
    rw [hw₂]  -- Unfold w2 = b * y / z
    exact div_nonneg (mul_nonneg hb (le_of_lt (mem_Ioi.mp hy))) (le_of_lt hz_pos)
    exact hw_sum

lemma integral_rnDeriv_change_of_variables [SigmaFinite μ] [SigmaFinite ν]
    (hf : StronglyMeasurable f) (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    ∫ x, f ((∂μ/∂ν) x).toReal ∂ν = ∫ x, ((∂ν/∂μ) x).toReal * f (1 / ((∂ν/∂μ) x).toReal) ∂μ := by sorry

-- The chain rule for Radon-Nikodym derivatives
lemma rnDeriv_chain_rule [SigmaFinite μ] [SigmaFinite ν] :
    ∀ᵐ x ∂ν, ((∂ν/∂μ) x).toReal * ((∂μ/∂ν) x).toReal = 1 := by sorry

-- The Radon-Nikodym reciprocal relationship
lemma rnDeriv_reciprocal [SigmaFinite μ] [SigmaFinite ν] :
    ∀ᵐ x ∂ν, ((∂μ/∂ν) x).toReal ≠ 0 → ((∂ν/∂μ) x).toReal = 1 / ((∂μ/∂ν) x).toReal := by sorry

-- Alternative formulation using the conjugate function directly
lemma integral_conjugate_transform [SigmaFinite μ] [SigmaFinite ν]
    (hf : StronglyMeasurable f) (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    ∫ x, f ((∂μ/∂ν) x).toReal ∂ν = ∫ x, (fun t ↦ t * f (1/t)) ((∂ν/∂μ) x).toReal ∂μ := by sorry

-- Integrability transfer under conjugate transformation
lemma integrable_conjugate_rnDeriv [IsFiniteMeasure μ] [SigmaFinite ν]
    (hf : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    Integrable (fun x ↦ ((∂ν/∂μ) x).toReal * f (1 / ((∂ν/∂μ) x).toReal)) μ := by sorry

-- Equivalently, using the conjugate function
lemma integrable_conjugate_function [IsFiniteMeasure μ] [SigmaFinite ν]
    (hf : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ioi 0) f)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    Integrable (fun x ↦ (fun t ↦ t * f (1/t)) ((∂ν/∂μ) x).toReal) μ := by sorry

-- Symmetry of singular parts
lemma singularPart_symm [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ.singularPart ν .univ = ν.singularPart μ .univ := by sorry

-- The derivAtTop behavior under conjugation
lemma derivAtTop_conjugate (hf_cvx : ConvexOn ℝ (Ioi 0) f) :
    derivAtTop (fun x ↦ x * f (1/x)) = derivAtTop f := by sorry

-- Alternative formulation: derivAtTop is preserved under perspective transformation
lemma derivAtTop_perspective (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    derivAtTop f = derivAtTop (fun x ↦ x * f (1/x)) := by sorry

-- More general change of variables with measure transformation
lemma change_of_variables_general [SigmaFinite μ] [SigmaFinite ν]
    (hf : StronglyMeasurable f) (g : ℝ → ℝ) (hg : StronglyMeasurable g)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_transform : ∀ t > 0, g (1/t) = t * f t) :
    ∫ x, f ((∂μ/∂ν) x).toReal ∂ν = ∫ x, g ((∂ν/∂μ) x).toReal ∂μ := by sorry

-- The key lemma that directly establishes the f-divergence symmetry
lemma fDiv_integral_symm [IsFiniteMeasure μ] [SigmaFinite ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf : StronglyMeasurable f)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    ∫ x, f ((∂μ/∂ν) x).toReal ∂ν + derivAtTop f * μ.singularPart ν .univ =
    ∫ x, (fun t ↦ t * f (1/t)) ((∂ν/∂μ) x).toReal ∂μ + derivAtTop f * ν.singularPart μ .univ := by sorry

-- Version that handles the case where ν is also finite
lemma fDiv_integral_symm_finite [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf : StronglyMeasurable f)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    ∫ x, f ((∂μ/∂ν) x).toReal ∂ν + derivAtTop f * μ.singularPart ν .univ =
    ∫ x, (fun t ↦ t * f (1/t)) ((∂ν/∂μ) x).toReal ∂μ + derivAtTop f * ν.singularPart μ .univ := by sorry

-- A more elementary version focusing on absolutely continuous measures
lemma integral_rnDeriv_symm_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ) (hf : StronglyMeasurable f)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    ∫ x, f ((∂μ/∂ν) x).toReal ∂ν = ∫ x, (fun t ↦ t * f (1/t)) ((∂ν/∂μ) x).toReal ∂μ := by sorry

lemma fDiv_symm [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hf_cvx : ConvexOn ℝ (Ioi 0) f)
    (hf : StronglyMeasurable f) (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν = fDiv (fun x ↦ x * f (1/x)) ν μ := by

  -- Define the conjugate function for clarity
  let g := fun x ↦ x * f (1/x)

  -- First, establish that g is convex (using our infrastructure)
  -- Note: conjugate_convex should be a lemma, so we apply it

  -- Show that the conjugate function is integrable with respect to the swapped measures
  have hg_int : Integrable (fun x ↦ g ((∂ν/∂μ) x).toReal) μ :=
    integrable_conjugate_function hf hf_cvx h_int

  -- Now we can expand both f-divergences using the definition
  rw [fDiv_of_integrable h_int, fDiv_of_integrable hg_int]

  -- We need to show equality of two parts:
  -- 1. The integral parts are equal
  -- 2. The singular part contributions are equal

  -- Part 1: Integral equality
  have h_integral_eq : ∫ x, f ((∂μ/∂ν) x).toReal ∂ν = ∫ x, g ((∂ν/∂μ) x).toReal ∂μ := by
    -- Use the change of variables lemma
    rw [integral_conjugate_transform hf h_int]
    -- This gives us exactly what we want since g(t) = t * f(1/t)

  -- Part 2: Singular parts equality
    -- Need to add IsFiniteMeasure ν assumption for singularPart_symm
  have h_singular_eq : derivAtTop f * μ.singularPart ν .univ = derivAtTop g * ν.singularPart μ .univ := by
    rw [derivAtTop_conjugate hf_cvx, singularPart_symm]

  -- Combine both parts
  rw [h_integral_eq, h_singular_eq]

lemma fDiv_add_const (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (c : ℝ) :
    fDiv (fun x ↦ f x + c) μ ν = fDiv f μ ν + c * ν .univ := by
  by_cases hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_add hf_int (integrable_const _) hf_cvx, fDiv_const, mul_comm]
    exact convexOn_const _ (convex_Ici 0)
  · rw [fDiv_of_not_integrable hf_int, fDiv_of_not_integrable]
    · rw [← EReal.coe_ennreal_toReal, ← EReal.coe_mul, EReal.top_add_coe]
      exact measure_ne_top _ _
    · have : (fun x ↦ f ((∂μ/∂ν) x).toReal) = (fun x ↦ (f ((∂μ/∂ν) x).toReal + c) - c) := by
        ext; simp
      rw [this] at hf_int
      exact fun h_int ↦ hf_int (h_int.sub (integrable_const _))

lemma fDiv_sub_const (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (c : ℝ) :
    fDiv (fun x ↦ f x - c) μ ν = fDiv f μ ν - c * ν .univ := by
  have : f = fun x ↦ (f x - c) + c := by ext; simp
  conv_rhs => rw [this]
  rw [fDiv_add_const]
  · rw [← EReal.coe_ennreal_toReal (measure_ne_top ν _), ← EReal.coe_mul, EReal.add_sub_cancel]
  · exact hf_cvx.sub (concaveOn_const _ (convex_Ici 0))

lemma fDiv_linear {c : ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv (fun x ↦ c * (x - 1)) μ ν
      = c * ((μ .univ).toReal - (ν .univ).toReal) := by
  rw [fDiv_mul_of_ne_top]
  rotate_left
  · exact (convexOn_id (convex_Ici 0)).add (convexOn_const _ (convex_Ici 0))
  · rw [derivAtTop_sub_const, derivAtTop_id']
    swap; · exact convexOn_id (convex_Ici 0)
    exact ne_of_beq_false rfl
  · exact integrable_add_const_iff.mpr Measure.integrable_toReal_rnDeriv
  rw [fDiv_sub_const, fDiv_id']
  swap; · exact convexOn_id (convex_Ici 0)
  simp [EReal.coe_ennreal_toReal, measure_ne_top]

lemma fDiv_add_linear' {c : ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv (fun x ↦ f x + c * (x - 1)) μ ν
      = fDiv f μ ν + c * ((μ .univ).toReal - (ν .univ).toReal) := by
  by_cases hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_add hf _ hf_cvx _, fDiv_linear]
    · exact (Measure.integrable_toReal_rnDeriv.sub (integrable_const _)).const_mul c
    · rcases le_total 0 c with (hc | hc)
      · exact ((convexOn_id (convex_Ici 0)).sub (concaveOn_const _ (convex_Ici 0))).smul hc
      · rw [← neg_neg c]
        simp_rw [neg_mul (-c)]
        exact (concaveOn_id (convex_Ici 0)).sub (convexOn_const _ (convex_Ici 0)) |>.smul
          (neg_nonneg.mpr hc) |>.neg
  · rw [fDiv_of_not_integrable hf, fDiv_of_not_integrable, EReal.top_add_of_ne_bot]
    · refine (EReal.mul_ne_bot _ _).mpr ⟨?_, ?_, ?_, ?_⟩
      · simp
      · exact Or.inr <| EReal.add_top_iff_ne_bot.mp rfl
      · simp
      · exact Or.inr <| Ne.symm (ne_of_beq_false rfl)
    · refine fun h_int ↦ hf ?_
      have : (fun x ↦ f ((∂μ/∂ν) x).toReal)
          = fun x ↦ (f ((∂μ/∂ν) x).toReal + c * (((∂μ/∂ν) x).toReal - 1))
            - c * (((∂μ/∂ν) x).toReal - 1) := by ext x; simp
      rw [this]
      exact h_int.add ((Measure.integrable_toReal_rnDeriv.sub (integrable_const _)).const_mul c).neg

lemma fDiv_add_linear {c : ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (h_eq : μ .univ = ν .univ) :
    fDiv (fun x ↦ f x + c * (x - 1)) μ ν = fDiv f μ ν := by
  rw [fDiv_add_linear' hf_cvx, h_eq, ← EReal.coe_sub, sub_self]
  simp

lemma fDiv_eq_fDiv_centeredFunction [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f μ ν = fDiv (fun x ↦ f x - f 1 - rightDeriv f 1 * (x - 1)) μ ν
      + f 1 * ν univ + rightDeriv f 1 * ((μ univ).toReal - (ν univ).toReal) := by
  simp_rw [sub_eq_add_neg (f _), sub_eq_add_neg (_ + _), ← neg_mul]
  rw [fDiv_add_linear' ?_, fDiv_add_const _ _ hf_cvx]
  swap; · exact hf_cvx.add_const _
  simp_rw [EReal.coe_neg, neg_mul]
  rw [add_assoc, add_comm (_ * _), ← add_assoc, add_assoc _ (-(_ * _)), add_comm (-(_ * _)),
    ← sub_eq_add_neg (_ * _), EReal.sub_self, add_zero]
  rotate_left
  · refine (EReal.mul_ne_top _ _).mpr ⟨?_, Or.inr <| EReal.add_top_iff_ne_bot.mp rfl,
      ?_, Or.inr <| Ne.symm (ne_of_beq_false rfl)⟩ <;> simp
  · refine (EReal.mul_ne_bot _ _).mpr ⟨?_, Or.inr <| EReal.add_top_iff_ne_bot.mp rfl,
      ?_, Or.inr <| Ne.symm (ne_of_beq_false rfl)⟩ <;> simp
  rw [add_assoc, add_comm (-(_ * _)), ← sub_eq_add_neg, EReal.sub_self, add_zero]
    <;> simp [EReal.mul_ne_top, EReal.mul_ne_bot, measure_ne_top]

end MulAdd

section AbsolutelyContinuousMutuallySingular

lemma fDiv_of_mutuallySingular [SigmaFinite μ] [IsFiniteMeasure ν] (h : μ ⟂ₘ ν) :
    fDiv f μ ν = (f 0 : EReal) * ν .univ + derivAtTop f * μ .univ := by
  have : μ.singularPart ν = μ := (μ.singularPart_eq_self).mpr h
  have hf_rnDeriv : (fun x ↦ f ((∂μ/∂ν) x).toReal) =ᵐ[ν] fun _ ↦ f 0 := by
    filter_upwards [Measure.rnDeriv_eq_zero_of_mutuallySingular h Measure.AbsolutelyContinuous.rfl]
      with x hx using by simp [hx]
  have h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
      rw [integrable_congr hf_rnDeriv]
      exact integrable_const _
  rw [fDiv_of_integrable h_int, integral_congr_ae hf_rnDeriv]
  simp only [integral_const, smul_eq_mul, EReal.coe_mul, this]
  rw [mul_comm]
  congr
  rw [EReal.coe_ennreal_toReal]
  exact measure_ne_top _ _

lemma fDiv_of_absolutelyContinuous
    [Decidable (Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)] (h : μ ≪ ν) :
    fDiv f μ ν = if Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
      then (↑(∫ x, f ((∂μ/∂ν) x).toReal ∂ν) : EReal) else ⊤ := by
  split_ifs with h_int
  · rw [fDiv_of_integrable h_int, Measure.singularPart_eq_zero_of_ac h]
    simp only [Measure.coe_zero, Pi.zero_apply, mul_zero, ENNReal.zero_toReal, add_zero]
    simp [Measure.singularPart_eq_zero_of_ac h]
  · rw [fDiv_of_not_integrable h_int]

lemma fDiv_eq_add_withDensity_singularPart
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f μ ν = fDiv f (ν.withDensity (∂μ/∂ν)) ν + fDiv f (μ.singularPart ν) ν
      - f 0 * ν .univ := by
  have h_int_iff : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
      ↔ Integrable (fun x ↦ f ((∂(ν.withDensity (∂μ/∂ν))/∂ν) x).toReal) ν := by
    refine integrable_congr ?_
    filter_upwards [ν.rnDeriv_withDensity (μ.measurable_rnDeriv ν)] with x hx
    rw [hx]
  classical
  rw [fDiv_of_mutuallySingular (μ.mutuallySingular_singularPart _)]
  by_cases hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_of_absolutelyContinuous (withDensity_absolutelyContinuous _ _), if_pos,
      fDiv_of_integrable hf]
    swap
    · exact h_int_iff.mp hf
    rw [add_sub_assoc]
    congr 2
    · refine integral_congr_ae ?_
      filter_upwards [ν.rnDeriv_withDensity (μ.measurable_rnDeriv ν)] with x hx
      rw [hx]
    rw [← EReal.coe_ennreal_toReal (measure_ne_top ν _), ← EReal.coe_mul, EReal.add_sub_cancel']
  · rw [fDiv_of_not_integrable hf, fDiv_of_not_integrable]
    · rw [add_sub_assoc, ← EReal.coe_ennreal_toReal (measure_ne_top ν _), ← EReal.coe_mul,
        EReal.add_sub_cancel']
      by_cases h0 : μ.singularPart ν .univ = 0
      · simp [h0]
      · by_cases h_top : derivAtTop f = ⊤
        · rw [h_top, EReal.top_mul_ennreal_coe h0, EReal.top_add_top]
        · lift derivAtTop f to ℝ using ⟨h_top, hf_cvx.derivAtTop_ne_bot⟩ with x
          rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _), ← EReal.coe_mul, EReal.top_add_coe]
    · rwa [← h_int_iff]

lemma fDiv_eq_add_withDensity_singularPart'
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f μ ν = fDiv (fun x ↦ f x - f 0) (ν.withDensity (∂μ/∂ν)) ν
      + fDiv f (μ.singularPart ν) ν := by
  rw [fDiv_eq_add_withDensity_singularPart _ _ hf_cvx, fDiv_sub_const, add_sub_assoc,
    sub_eq_add_neg, sub_eq_add_neg, add_assoc]
  · congr 1
    rw [add_comm]
  · exact hf_cvx

lemma fDiv_eq_add_withDensity_singularPart''
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f μ ν = fDiv f (ν.withDensity (∂μ/∂ν)) ν
      + fDiv (fun x ↦ f x - f 0) (μ.singularPart ν) ν := by
  rw [fDiv_eq_add_withDensity_singularPart _ _ hf_cvx, fDiv_sub_const, add_sub_assoc,
    sub_eq_add_neg]
  exact hf_cvx

lemma fDiv_eq_add_withDensity_derivAtTop
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f μ ν = fDiv f (ν.withDensity (∂μ/∂ν)) ν + derivAtTop f * μ.singularPart ν .univ := by
  rw [fDiv_eq_add_withDensity_singularPart'' μ ν hf_cvx,
    fDiv_of_mutuallySingular (μ.mutuallySingular_singularPart _), derivAtTop_sub_const hf_cvx]
  simp

end AbsolutelyContinuousMutuallySingular

section AddMeasure

lemma fDiv_absolutelyContinuous_add_mutuallySingular {μ₁ μ₂ ν : Measure α}
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν] (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ⟂ₘ ν)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f (μ₁ + μ₂) ν = fDiv f μ₁ ν + derivAtTop f * μ₂ .univ := by
  rw [fDiv_eq_add_withDensity_derivAtTop  _ _ hf_cvx, Measure.singularPart_add,
    Measure.singularPart_eq_zero_of_ac h₁, Measure.singularPart_eq_self.mpr h₂, zero_add]
  congr
  conv_rhs => rw [← μ₁.withDensity_rnDeriv_eq ν h₁]
  refine withDensity_congr_ae ?_
  refine (μ₁.rnDeriv_add' _ _).trans ?_
  filter_upwards [Measure.rnDeriv_eq_zero_of_mutuallySingular h₂ Measure.AbsolutelyContinuous.rfl]
    with x hx
  simp [hx]

/-- Auxiliary lemma for `fDiv_add_measure_le`. -/
lemma fDiv_add_measure_le_of_ac {μ₁ μ₂ ν : Measure α} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure ν] (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ≪ ν)
    (hf : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f (μ₁ + μ₂) ν ≤ fDiv f μ₁ ν + derivAtTop f * μ₂ .univ := by
  classical
  by_cases hμ₂0 : μ₂ = 0
  · simp [hμ₂0]
  by_cases h_top : derivAtTop f = ⊤
  · rw [h_top, EReal.top_mul_of_pos, EReal.add_top_of_ne_bot]
    · exact le_top
    · refine fDiv_ne_bot_of_derivAtTop_nonneg ?_
      simp [h_top]
    · simp [hμ₂0]
  have h_int : Integrable (fun x ↦ f ((∂μ₁/∂ν) x).toReal) ν :=
    integrable_f_rnDeriv_of_derivAtTop_ne_top _ _ hf hf_cvx h_top
  have h_int_add : Integrable (fun x ↦ f ((∂μ₁ + μ₂/∂ν) x).toReal) ν :=
    integrable_f_rnDeriv_of_derivAtTop_ne_top _ _ hf hf_cvx h_top
  have h_le : ∀ᵐ x ∂ν, f ((∂μ₁ + μ₂/∂ν) x).toReal
      ≤ f ((∂μ₁/∂ν) x).toReal + (derivAtTop f).toReal * ((∂μ₂/∂ν) x).toReal := by
    have h_add := μ₁.rnDeriv_add' μ₂ ν
    filter_upwards [h_add, μ₁.rnDeriv_lt_top ν, μ₂.rnDeriv_lt_top ν] with x hx hx₁ hx₂
    rw [hx, Pi.add_apply, ENNReal.toReal_add hx₁.ne hx₂.ne]
    exact le_add_derivAtTop'' hf_cvx h_top ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  rw [fDiv_of_absolutelyContinuous (Measure.AbsolutelyContinuous.add_left_iff.mpr ⟨h₁, h₂⟩),
    if_pos h_int_add, fDiv_of_absolutelyContinuous h₁, if_pos h_int]
  lift derivAtTop f to ℝ using ⟨h_top, hf_cvx.derivAtTop_ne_bot⟩ with df
  rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  norm_cast
  calc ∫ x, f ((∂μ₁ + μ₂/∂ν) x).toReal ∂ν
    ≤ ∫ x, f ((∂μ₁/∂ν) x).toReal + df * ((∂μ₂/∂ν) x).toReal ∂ν := by
        refine integral_mono_ae h_int_add ?_ h_le
        exact h_int.add (Measure.integrable_toReal_rnDeriv.const_mul _)
  _ ≤ ∫ x, f ((∂μ₁/∂ν) x).toReal ∂ν + df * (μ₂ .univ).toReal := by
        rw [integral_add h_int (Measure.integrable_toReal_rnDeriv.const_mul _),
          integral_mul_left, Measure.integral_toReal_rnDeriv h₂]

lemma fDiv_add_measure_le (μ₁ μ₂ ν : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure ν] (hf : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f (μ₁ + μ₂) ν ≤ fDiv f μ₁ ν + derivAtTop f * μ₂ .univ := by
  rw [μ₂.haveLebesgueDecomposition_add ν, μ₁.haveLebesgueDecomposition_add ν]
  have : μ₁.singularPart ν + ν.withDensity (∂μ₁/∂ν) + (μ₂.singularPart ν + ν.withDensity (∂μ₂/∂ν))
      = (ν.withDensity (∂μ₁/∂ν) + ν.withDensity (∂μ₂/∂ν))
        + (μ₁.singularPart ν + μ₂.singularPart ν) := by
    abel
  rw [this, fDiv_absolutelyContinuous_add_mutuallySingular
      ((withDensity_absolutelyContinuous _ _).add_left (withDensity_absolutelyContinuous _ _))
      ((μ₁.mutuallySingular_singularPart _).add_left (μ₂.mutuallySingular_singularPart _)) hf_cvx]
  simp only [Measure.coe_add, Pi.add_apply, EReal.coe_ennreal_add]
  conv_rhs => rw [add_comm (μ₁.singularPart ν)]
  rw [fDiv_absolutelyContinuous_add_mutuallySingular (withDensity_absolutelyContinuous _ _)
    (μ₁.mutuallySingular_singularPart _) hf_cvx]
  calc fDiv f (ν.withDensity (∂μ₁/∂ν) + ν.withDensity (∂μ₂/∂ν)) ν +
      derivAtTop f * (↑(μ₁.singularPart ν .univ) + ↑(μ₂.singularPart ν .univ))
    = fDiv f (ν.withDensity (∂μ₁/∂ν) + ν.withDensity (∂μ₂/∂ν)) ν
      + derivAtTop f * μ₁.singularPart ν .univ + derivAtTop f * μ₂.singularPart ν .univ := by
        simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
        rw [add_assoc, EReal.mul_add_coe_of_nonneg _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  _ ≤ fDiv f (ν.withDensity (∂μ₁/∂ν)) ν + derivAtTop f * ν.withDensity (∂μ₂/∂ν) .univ
      + derivAtTop f * μ₁.singularPart ν .univ + derivAtTop f * μ₂.singularPart ν .univ := by
        gcongr
        exact fDiv_add_measure_le_of_ac (withDensity_absolutelyContinuous _ _)
          (withDensity_absolutelyContinuous _ _) hf hf_cvx
  _ = fDiv f (ν.withDensity (∂μ₁/∂ν)) ν + derivAtTop f * μ₁.singularPart ν .univ
      + derivAtTop f * μ₂.singularPart ν .univ + derivAtTop f * ν.withDensity (∂μ₂/∂ν) .univ := by
        abel
  _ = fDiv f (ν.withDensity (∂μ₁/∂ν)) ν + derivAtTop f * μ₁.singularPart ν .univ
      + derivAtTop f * (↑(μ₂.singularPart ν .univ) + ↑(ν.withDensity (∂μ₂/∂ν) .univ)) := by
        simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
        rw [add_assoc, EReal.mul_add_coe_of_nonneg _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg]

end AddMeasure

/-- Auxiliary lemma for `fDiv_le_zero_add_top`. -/
lemma fDiv_le_zero_add_top_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f μ ν ≤ f 0 * ν .univ + derivAtTop f * μ .univ := by
  classical
  by_cases hμ : μ = 0
  · simp [hμ]
  by_cases h_top : derivAtTop f = ⊤
  · rw [h_top, ← EReal.coe_ennreal_toReal (measure_ne_top _ _),
      ← EReal.coe_ennreal_toReal (measure_ne_top _ _), EReal.top_mul_of_pos, ← EReal.coe_mul,
      EReal.coe_add_top]
    · exact le_top
    · norm_cast
      refine ENNReal.toReal_pos (by simp [hμ]) (measure_ne_top _ _)
  · have h_int := integrable_f_rnDeriv_of_derivAtTop_ne_top μ ν hf hf_cvx h_top
    rw [fDiv_of_absolutelyContinuous hμν, if_pos h_int]
    have h := fun x ↦ le_add_derivAtTop'' hf_cvx h_top le_rfl
      (ENNReal.toReal_nonneg : 0 ≤ ((∂μ/∂ν) x).toReal)
    simp only [zero_add] at h
    rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _),
      ← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
    lift derivAtTop f to ℝ using ⟨h_top, hf_cvx.derivAtTop_ne_bot⟩ with df
    norm_cast
    refine (integral_mono h_int ?_ h).trans_eq ?_
    · exact (integrable_const _).add (Measure.integrable_toReal_rnDeriv.const_mul _)
    rw [integral_add (integrable_const _), integral_const, integral_mul_left, smul_eq_mul, mul_comm,
      Measure.integral_toReal_rnDeriv hμν]
    · simp
    · exact Measure.integrable_toReal_rnDeriv.const_mul _

lemma fDiv_le_zero_add_top [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f μ ν ≤ f 0 * ν .univ + derivAtTop f * μ .univ := by
  rw [fDiv_eq_add_withDensity_derivAtTop _ _ hf_cvx]
  calc fDiv f (ν.withDensity (∂μ/∂ν)) ν + derivAtTop f * μ.singularPart ν .univ
    ≤ f 0 * ν .univ + derivAtTop f * ν.withDensity (∂μ/∂ν) .univ
      + derivAtTop f * μ.singularPart ν .univ := by
        gcongr
        exact fDiv_le_zero_add_top_of_ac (withDensity_absolutelyContinuous _ _) hf hf_cvx
    _ ≤ f 0 * ν .univ + derivAtTop f * μ .univ := by
      rw [add_assoc]
      gcongr
      conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
      simp only [Measure.coe_add, Pi.add_apply, EReal.coe_ennreal_add]
      simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
      rw [EReal.mul_add_coe_of_nonneg _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg]

lemma fDiv_lt_top_of_ac (h : μ ≪ ν) (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν < ⊤ := by
  classical
  rw [fDiv_of_absolutelyContinuous h, if_pos h_int]
  simp

section derivAtTopTop

lemma fDiv_of_not_ac [SigmaFinite μ] [SigmaFinite ν] (hf : derivAtTop f = ⊤) (hμν : ¬ μ ≪ ν) :
    fDiv f μ ν = ⊤ := by
  rw [fDiv]
  split_ifs with h_int
  · rw [hf]
    suffices μ.singularPart ν .univ ≠ 0 by
      rw [EReal.top_mul_of_pos, EReal.coe_add_top]
      refine lt_of_le_of_ne (EReal.coe_ennreal_nonneg _) ?_
      exact mod_cast this.symm
    simp only [ne_eq, Measure.measure_univ_eq_zero]
    rw [Measure.singularPart_eq_zero]
    exact hμν
  · rfl

lemma fDiv_lt_top_iff_ac [SigmaFinite μ] [SigmaFinite ν] (hf : derivAtTop f = ⊤)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν < ⊤ ↔ μ ≪ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ fDiv_lt_top_of_ac h h_int⟩
  by_contra h_not_ac
  refine h.ne (fDiv_of_not_ac hf h_not_ac)

lemma fDiv_ne_top_iff_ac [SigmaFinite μ] [SigmaFinite ν] (hf : derivAtTop f = ⊤)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν ≠ ⊤ ↔ μ ≪ ν := by
  rw [← fDiv_lt_top_iff_ac hf h_int, lt_top_iff_ne_top]

lemma fDiv_eq_top_iff_not_ac [SigmaFinite μ] [SigmaFinite ν] (hf : derivAtTop f = ⊤)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν = ⊤ ↔ ¬ μ ≪ ν := by
  rw [← fDiv_ne_top_iff_ac hf h_int, not_not]

lemma fDiv_of_derivAtTop_eq_top [SigmaFinite μ] [SigmaFinite ν] (hf : derivAtTop f = ⊤)
    [Decidable (Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν ∧ μ ≪ ν)] :
    fDiv f μ ν = if (Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν ∧ μ ≪ ν)
      then ((∫ x, f ((∂μ/∂ν) x).toReal ∂ν : ℝ) : EReal)
      else ⊤ := by
  split_ifs with h
  · rw [fDiv_of_integrable h.1, Measure.singularPart_eq_zero_of_ac h.2]
    simp
  · push_neg at h
    by_cases hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
    · exact fDiv_of_not_ac hf (h hf_int)
    · exact fDiv_of_not_integrable hf_int

end derivAtTopTop

lemma fDiv_lt_top_of_derivAtTop_ne_top [IsFiniteMeasure μ] (hf : derivAtTop f ≠ ⊤)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν < ⊤ := by
  rw [fDiv_of_integrable h_int]
  refine EReal.add_lt_top ?_ ?_
  · simp
  · rw [ne_eq, EReal.mul_eq_top]
    simp only [EReal.coe_ennreal_ne_bot, and_false, EReal.coe_ennreal_pos, Measure.measure_univ_pos,
      ne_eq, EReal.coe_ennreal_eq_top_iff, false_or, not_or, not_and, not_lt, not_not]
    refine ⟨fun _ ↦ ?_, ?_, ?_⟩
    · norm_cast
      exact zero_le'
    · simp [hf]
    · exact fun _ ↦ measure_ne_top _ _

lemma fDiv_lt_top_of_derivAtTop_ne_top' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_top : derivAtTop f ≠ ⊤) (hf : StronglyMeasurable f) (h_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f μ ν < ⊤ := by
  have h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν :=
    integrable_f_rnDeriv_of_derivAtTop_ne_top μ ν hf h_cvx h_top
  exact fDiv_lt_top_of_derivAtTop_ne_top h_top h_int

lemma fDiv_lt_top_iff_of_derivAtTop_ne_top [IsFiniteMeasure μ] (hf : derivAtTop f ≠ ⊤) :
    fDiv f μ ν < ⊤ ↔ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  refine ⟨fun h ↦ ?_, fDiv_lt_top_of_derivAtTop_ne_top hf⟩
  by_contra h_not_int
  rw [fDiv_of_not_integrable h_not_int] at h
  simp at h

lemma fDiv_ne_top_of_derivAtTop_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_top : derivAtTop f ≠ ⊤) (hf : StronglyMeasurable f) (h_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f μ ν ≠ ⊤ := by
  rw [← lt_top_iff_ne_top]
  exact fDiv_lt_top_of_derivAtTop_ne_top' h_top hf h_cvx

lemma fDiv_ne_top_iff_of_derivAtTop_ne_top [IsFiniteMeasure μ] (hf : derivAtTop f ≠ ⊤) :
    fDiv f μ ν ≠ ⊤ ↔ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  rw [← fDiv_lt_top_iff_of_derivAtTop_ne_top hf, lt_top_iff_ne_top]

lemma fDiv_eq_top_iff_of_derivAtTop_ne_top [IsFiniteMeasure μ] (hf : derivAtTop f ≠ ⊤) :
    fDiv f μ ν = ⊤ ↔ ¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  rw [← fDiv_ne_top_iff_of_derivAtTop_ne_top hf, not_not]

lemma fDiv_eq_top_iff [IsFiniteMeasure μ] [SigmaFinite ν] :
    fDiv f μ ν = ⊤
      ↔ (¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) ∨ (derivAtTop f = ⊤ ∧ ¬ μ ≪ ν) := by
  by_cases h : derivAtTop f = ⊤
  · simp only [h, true_and]
    by_cases hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
    · simp only [hf, not_true_eq_false, false_or]
      exact fDiv_eq_top_iff_not_ac h hf
    · simp [hf, fDiv_of_not_integrable hf]
  · simp only [h, false_and, or_false]
    exact fDiv_eq_top_iff_of_derivAtTop_ne_top h

lemma fDiv_eq_top_iff' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf : StronglyMeasurable f) (h_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f μ ν = ⊤
      ↔ derivAtTop f = ⊤ ∧ (¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν ∨ ¬ μ ≪ ν) := by
  by_cases h_top : derivAtTop f = ⊤
  · rw [fDiv_eq_top_iff]
    simp only [h_top, true_and]
  · simp only [h_top, false_and, iff_false]
    exact fDiv_ne_top_of_derivAtTop_ne_top h_top hf h_cvx

lemma fDiv_ne_top_iff [IsFiniteMeasure μ] [SigmaFinite ν] :
    fDiv f μ ν ≠ ⊤
      ↔ (Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) ∧ (derivAtTop f = ⊤ → μ ≪ ν) := by
  rw [ne_eq, fDiv_eq_top_iff]
  push_neg
  rfl

lemma fDiv_ne_top_iff' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf : StronglyMeasurable f) (h_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f μ ν ≠ ⊤ ↔ derivAtTop f = ⊤ → (Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν ∧ μ ≪ ν) := by
  rw [ne_eq, fDiv_eq_top_iff' hf h_cvx]
  push_neg
  rfl

lemma integrable_of_fDiv_ne_top (h : fDiv f μ ν ≠ ⊤) :
    Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  by_contra h_not
  exact h (fDiv_of_not_integrable h_not)

lemma fDiv_of_ne_top (h : fDiv f μ ν ≠ ⊤) :
    fDiv f μ ν = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν + derivAtTop f * μ.singularPart ν .univ := by
  rw [fDiv_of_integrable]
  exact integrable_of_fDiv_ne_top h

lemma toReal_fDiv_of_integrable [IsFiniteMeasure μ] (hf_cvx : ConvexOn ℝ (Ici 0) f)
    (hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_deriv : derivAtTop f = ⊤ → μ ≪ ν) :
    (fDiv f μ ν).toReal = ∫ y, f ((∂μ/∂ν) y).toReal ∂ν
        + (derivAtTop f * μ.singularPart ν .univ).toReal := by
  rw [fDiv_of_integrable hf_int, EReal.toReal_add]
  rotate_left
  · simp
  · simp
  · simp only [ne_eq, EReal.mul_eq_top, hf_cvx.derivAtTop_ne_bot, false_and,
      EReal.coe_ennreal_ne_bot, and_false, EReal.coe_ennreal_pos, Measure.measure_univ_pos,
      EReal.coe_ennreal_eq_top_iff, measure_ne_top, or_false, false_or, not_and, not_not]
    intro h_top
    simp [h_top, Measure.singularPart_eq_zero_of_ac (h_deriv h_top)]
  · simp only [ne_eq, EReal.mul_eq_bot, hf_cvx.derivAtTop_ne_bot, EReal.coe_ennreal_pos,
      Measure.measure_univ_pos, false_and, EReal.coe_ennreal_ne_bot, and_false,
      EReal.coe_ennreal_eq_top_iff, measure_ne_top, or_false, false_or, not_and, not_lt]
    exact fun _ ↦ EReal.coe_ennreal_nonneg _
  rfl

lemma le_fDiv_of_ac [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (hμν : μ ≪ ν) :
    f (μ .univ).toReal ≤ fDiv f μ ν := by
  by_cases hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  swap; · rw [fDiv_of_not_integrable hf_int]; exact le_top
  rw [fDiv_of_integrable hf_int, Measure.singularPart_eq_zero_of_ac hμν]
  simp only [Measure.coe_zero, Pi.zero_apply,
    EReal.coe_ennreal_zero, mul_zero, add_zero, EReal.coe_le_coe_iff]
  calc f (μ .univ).toReal
    = f (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by rw [Measure.integral_toReal_rnDeriv hμν]
  _ ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
    rw [← average_eq_integral, ← average_eq_integral]
    exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp)
      Measure.integrable_toReal_rnDeriv hf_int

lemma f_measure_univ_le_add (μ ν : Measure α) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) :
    f (μ .univ).toReal
      ≤ f (ν.withDensity (∂μ/∂ν) .univ).toReal + derivAtTop f * μ.singularPart ν .univ := by
  have : μ .univ = ν.withDensity (∂μ/∂ν) .univ + μ.singularPart ν .univ := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
    simp
  rw [this]
  exact toReal_le_add_derivAtTop hf_cvx (measure_ne_top _ _) (measure_ne_top _ _)

lemma le_fDiv [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0)) :
    f (μ .univ).toReal ≤ fDiv f μ ν := by
  refine (f_measure_univ_le_add μ ν hf_cvx).trans ?_
  rw [fDiv_eq_add_withDensity_singularPart'' μ _ hf_cvx,
    fDiv_of_mutuallySingular  (μ.mutuallySingular_singularPart ν), derivAtTop_sub_const hf_cvx]
  simp only [MeasurableSet.univ, withDensity_apply, Measure.restrict_univ, sub_self, EReal.coe_zero,
    measure_univ, EReal.coe_ennreal_one, mul_one, zero_add]
  gcongr
  rw [← setLIntegral_univ, ← withDensity_apply _ .univ]
  exact le_fDiv_of_ac hf_cvx hf_cont (withDensity_absolutelyContinuous _ _)

lemma fDiv_nonneg [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0)) (hf_one : f 1 = 0) :
    0 ≤ fDiv f μ ν := by
  calc (0 : EReal) = f (μ .univ).toReal := by simp [hf_one]
  _ ≤ fDiv f μ ν := le_fDiv hf_cvx hf_cont

/- The hypothesis `hfg'` can maybe become something like `f ≤ᵐ[atTop] g`, but then we would need
some lemma like `derivAtTop_mono`, and I'm not sure this is true in gneral, without any assumption
on `f`.
We could prove it if we had some lemma saying that the new derivAtTop is equal to the
old definition. This is probably false in general, but under some assumptions it should be true. -/
lemma fDiv_mono'' (hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (hfg : f ≤ᵐ[ν.map (fun x ↦ ((∂μ/∂ν) x).toReal)] g) (hfg' : derivAtTop f ≤ derivAtTop g) :
    fDiv f μ ν ≤ fDiv g μ ν := by
  rw [fDiv_of_integrable hf_int, fDiv]
  split_ifs with hg_int
  swap; · simp
  gcongr
  · exact EReal.coe_le_coe_iff.mpr <| integral_mono_ae hf_int hg_int <|
      ae_of_ae_map (μ.measurable_rnDeriv ν).ennreal_toReal.aemeasurable hfg
  · exact EReal.coe_ennreal_nonneg _

/- The hypothesis `hfg'` can probably be removed if we ask for the functions to be convex,
since then it is true that `derivAtTop` is monotone, but we still don't have the result formalized.
Moreover in the convex case we can also relax `hf_int` and only ask for a.e. strong measurability
of `f` (at least when `μ` and `ν` are finite), because then the negative part of the function
is always integrable, hence if `f` is not integrable `g` is also not integrable. -/
lemma fDiv_mono' (hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (hfg : f ≤ g) (hfg' : derivAtTop f ≤ derivAtTop g) : fDiv f μ ν ≤ fDiv g μ ν :=
  fDiv_mono'' hf_int (.of_forall hfg) hfg'

lemma fDiv_nonneg_of_nonneg (hf : 0 ≤ f) (hf' : 0 ≤ derivAtTop f) :
    0 ≤ fDiv f μ ν :=
  fDiv_zero μ ν ▸ fDiv_mono' (integrable_zero α ℝ ν) hf (derivAtTop_zero ▸ hf')

lemma fDiv_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_mass : μ .univ = ν .univ)
    (hf_deriv : derivAtTop f = ⊤) (hf_cvx : StrictConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousOn f (Ici 0)) (hf_one : f 1 = 0) :
    fDiv f μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ fDiv_self hf_one _⟩
  by_cases hμν : μ ≪ ν
  swap; · rw [fDiv_of_not_ac hf_deriv hμν] at h; exact (EReal.top_ne_zero h).elim
  by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  swap; · rw [fDiv_of_not_integrable h_int] at h; exact (EReal.top_ne_zero h).elim
  by_cases hμ_zero : μ = 0
  · rw [hμ_zero] at h_mass ⊢
    rw [Measure.measure_univ_eq_zero.mp h_mass.symm]
  classical
  rw [fDiv_of_derivAtTop_eq_top hf_deriv, if_pos ⟨h_int, hμν⟩, EReal.coe_eq_zero] at h
  have h_eq := StrictConvexOn.ae_eq_const_or_map_average_lt hf_cvx hf_cont isClosed_Ici (by simp)
    Measure.integrable_toReal_rnDeriv h_int
  simp only [average, integral_smul_measure, smul_eq_mul, h, mul_zero, ← h_mass] at h_eq
  rw [Measure.integral_toReal_rnDeriv hμν, ← ENNReal.toReal_mul,
    ENNReal.inv_mul_cancel (Measure.measure_univ_ne_zero.mpr hμ_zero) (measure_ne_top μ _)] at h_eq
  simp only [ENNReal.one_toReal, Function.const_one, log_one, mul_zero, lt_self_iff_false,
    or_false, hf_one] at h_eq
  exact (Measure.rnDeriv_eq_one_iff_eq hμν).mp <| ENNReal.eventuallyEq_of_toReal_eventuallyEq
    (μ.rnDeriv_ne_top _) (.of_forall fun _ ↦ ENNReal.one_ne_top) h_eq

lemma fDiv_eq_zero_iff' [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hf_deriv : derivAtTop f = ⊤) (hf_cvx : StrictConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousOn f (Ici 0)) (hf_one : f 1 = 0) :
    fDiv f μ ν = 0 ↔ μ = ν := by
  exact fDiv_eq_zero_iff (by simp) hf_deriv hf_cvx hf_cont hf_one

lemma fDiv_map_measurableEmbedding [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : α → β} (hg : MeasurableEmbedding g) :
    fDiv f (μ.map g) (ν.map g) = fDiv f μ ν := by
  by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_of_integrable h_int, fDiv_of_integrable]
    swap
    · rw [hg.integrable_map_iff]
      refine (integrable_congr ?_).mpr h_int
      filter_upwards [hg.rnDeriv_map μ ν] with a ha using ha ▸ rfl
    rw [hg.integral_map]
    congr 2
    · refine integral_congr_ae ?_
      filter_upwards [hg.rnDeriv_map μ ν] with a ha using ha ▸ rfl
    · rw [hg.singularPart_map μ ν, hg.map_apply, preimage_univ]
  · rw [fDiv_of_not_integrable h_int, fDiv_of_not_integrable]
    rwa [hg.integrable_map_iff, integrable_congr ?_]
    filter_upwards [hg.rnDeriv_map μ ν] with a ha using ha ▸ rfl

lemma fDiv_restrict_of_integrable (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set α} (hs : MeasurableSet s) (h_int : IntegrableOn (fun x ↦ f ((∂μ/∂ν) x).toReal) s ν) :
    fDiv f (μ.restrict s) ν = ∫ x in s, f ((∂μ/∂ν) x).toReal ∂ν
        + f 0 * ν sᶜ + derivAtTop f * (μ.singularPart ν s) := by
  classical
  have h : (fun x ↦ f ((∂μ.restrict s/∂ν) x).toReal)
      =ᵐ[ν] s.piecewise (fun x ↦ f ((∂μ/∂ν) x).toReal) (fun _ ↦ f 0) := by
    filter_upwards [μ.rnDeriv_restrict ν hs] with a ha
    rw [ha]
    by_cases has : a ∈ s <;> simp [has]
  rw [fDiv_of_integrable, μ.singularPart_restrict ν hs, Measure.restrict_apply_univ]
  swap;
  · rw [integrable_congr h]
    exact Integrable.piecewise hs h_int (integrable_const _)
  congr 1
  rw [integral_congr_ae h, integral_piecewise hs h_int (integrable_const _), integral_const]
  simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, smul_eq_mul, EReal.coe_add,
    EReal.coe_mul]
  rw [EReal.coe_ennreal_toReal, mul_comm]
  exact measure_ne_top _ _

end ProbabilityTheory
