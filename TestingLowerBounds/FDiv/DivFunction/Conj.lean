/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.FDiv.DivFunction.DerivAtTop
/-!

# f-Divergences functions

-/

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}
  {f : ℝ → ℝ}

namespace DivFunction

section Conj

noncomputable
def conjFn (f : DivFunction) :=
  (fun x ↦ if x = 0 then f.derivAtTop else x * f x⁻¹)

lemma ConjugateFnContinuousAt (f : DivFunction):
    ContinuousAt (conjFn f) 0 := by
  sorry

lemma conjFnContinuous (f : DivFunction):
    Continuous (conjFn f) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = 0
    · rw [hx]; exact ConjugateFnContinuousAt f
    ·
      have hx_pos : 0 < x := lt_of_le_of_ne (zero_le x) (Ne.symm hx)

      -- On a neighborhood of x, conjFn f y = y * f y⁻¹
      have h_eq : conjFn f =ᶠ[𝓝 x] fun y ↦ y * f y⁻¹ := by
        filter_upwards [isOpen_Ioi.mem_nhds hx_pos] with y hy
        unfold conjFn
        simp [hy.ne']

      rw [continuousAt_congr h_eq]

      -- Two cases:
      -- · f 0 = 0
      --   Then f is constant 0 before 1
      --   Constant function is continuous
      -- · f 0 ≠ 0
      by_cases hf_zero : f 0 ≠ 0
      · apply ENNReal.Tendsto.mul
        · -- 1. Identity function y ↦ y is continuous
          exact continuousAt_id
        · -- 2. Composition: y ↦ f y⁻¹ is continuous
          simp [hx]
        · apply Tendsto.comp
          . exact f.continuous.continuousAt.tendsto
          · exact ContinuousAt.inv continuousAt_id
        · by_cases hx_inf : x ≠ ⊤
          · exact Or.inr hx_inf
          · simp at hx_inf
            rw [hx_inf]
            rw [ENNReal.inv_top]
            exact Or.inl hf_zero
      · simp at hf_zero;
        have h := antitoneOn f
        rw [AntitoneOn] at h
        by_cases hx_one : x ≤ 1
        · apply ENNReal.Tendsto.mul
          · -- 1. Identity function y ↦ y is continuous
            exact continuousAt_id
          · -- 2. Composition: y ↦ f y⁻¹ is continuous
            simp [hx]
          · apply Tendsto.comp
            . exact f.continuous.continuousAt.tendsto
            · exact ContinuousAt.inv continuousAt_id
          · have hx_inf : x < ⊤ := lt_of_le_of_lt hx_one ENNReal.one_lt_top
            exact Or.inr hx_inf.ne
        ·
          simp at hx_one
          have antitone := antitoneOn f
          rw [AntitoneOn] at antitone
          have f_zero_on_unit : ∀ y ∈ Set.Iio 1, f y = 0 := by
            intro y hy
            have h_antitone: f y ≤ f 0 := antitone (mem_Iic.mpr (zero_le_one' ℝ≥0∞)) (mem_Iic_of_Iio hy) (zero_le y)
            rw [hf_zero] at h_antitone
            exact nonpos_iff_eq_zero.mp h_antitone
          have h_zero : (fun y ↦ y * f y⁻¹) =ᶠ[𝓝 x] fun _ ↦ 0 := by
            filter_upwards [isOpen_Ioi.mem_nhds hx_one] with y hy
            have y_inv_lt_one : y⁻¹ < 1 := by
              rw [ENNReal.inv_lt_one]
              exact hy
            have y_inv_in_domain : y⁻¹ ∈ Set.Iio 1 := y_inv_lt_one
            rw [f_zero_on_unit (y⁻¹) y_inv_in_domain, mul_zero]
          rw [continuousAt_congr h_zero]
          exact continuousAt_const
        -- use monotonicity, simp, const_mul

lemma conjFnConvexIoi (f : DivFunction)  :
    ConvexOn ℝ≥0 (Ioi 0) (conjFn f) := by
  -- #check EReal.coe_toENNReal_eq_max Why does this not work? It's in the docs.
  rw [ConvexOn]
  unfold conjFn
  constructor
  · refine OrdConnected.convex ?left.hs; exact ordConnected_Ioi -- I have no idea what this means
  · intro x hx y hy a b ha hb hab
    by_cases hxinf : (x ≠ ⊤) ∧ (y ≠ ⊤)
    · set z := a • x + b • y with hz
      have hz_pos : 0 < z := by
        simp only [z]
        by_cases hb_pos : 0 < b
        ·
          cases' ha.eq_or_lt with ha_zero ha_pos
          ·
            rw [← ha_zero, zero_smul, zero_add]
            exact smul_pos hb_pos (mem_Ioi.mp hy)
          ·
            have hax_pos : 0 < a • x :=  ENNReal.mul_pos (ENNReal.coe_lt_coe.mpr ha_pos).ne' (mem_Ioi.mp hx).ne'
            have hby_pos : 0 < b • y :=  ENNReal.mul_pos (ENNReal.coe_lt_coe.mpr hb_pos).ne' (mem_Ioi.mp hy).ne'
            exact Right.add_pos' hax_pos hby_pos
        ·
          have hb_zero : b = 0 := le_antisymm (le_of_not_gt hb_pos) hb
          simp [hb_zero, add_zero] at hab
          rw [hb_zero, zero_smul, add_zero, hab, one_smul]
          exact hx
      simp [hz_pos.ne', (Set.mem_Ioi.mp hx).ne', (Set.mem_Ioi.mp hy).ne']
      let w1 := a • x / z
      let w2 := b • y / z
      have hz_inf : z < ⊤ := by
        let c := a • x
        let d := b • y
        have ineq3 : c < ⊤ := by exact ENNReal.nnreal_smul_lt_top (lt_top_iff_ne_top.mpr hxinf.1)
        have ineq4 : d < ⊤ := by exact ENNReal.nnreal_smul_lt_top (lt_top_iff_ne_top.mpr hxinf.2)
        exact ENNReal.add_lt_top.mpr ⟨ineq3, ineq4⟩


      -- Fill in for hw_top : w1 ≠ ⊤ ∧ w2 ≠ ⊤
      have hw_top : w1 ≠ ⊤ ∧ w2 ≠ ⊤ := by
        constructor
        · -- w1 = a • x / z ≠ ⊤
          rw [ne_eq, ENNReal.div_eq_top]
          push_neg
          constructor
          · exact (fun _ : a • x ≠ 0 => hz_pos.ne')
          · intro h
            rw [h] at hz
            simp at hz
            exact hz
        · -- w2 = b • y / z ≠ ⊤
          rw [ne_eq, ENNReal.div_eq_top]
          push_neg
          constructor
          · exact (fun _ : b • y ≠ 0 => hz_pos.ne')
          · intro h
            rw [h] at hz
            simp at hz
            exact hz

      have hw_sum : w1 + w2 = 1 := by
        simp only [w1, w2, z]
        rw [ENNReal.div_add_div_same]
        rw [ENNReal.div_self]
        simp only [← hz]
        exact hz_pos.ne'
        refine lt_top_iff_ne_top.mp ?hI.a
        exact hz_inf

      have hw_sum_nnreal : w1.toNNReal + w2.toNNReal = 1 := by
        rw [← ENNReal.toNNReal_add hw_top.1 hw_top.2]
        rw [hw_sum]
        exact rfl

      have rhs_transform :=
        calc z * (w1 • f.toFun (1/x) + w2 • f.toFun (1/y))
        _ = z * ((a • x) * z⁻¹ * f.toFun (1/x) + (b • y) * z⁻¹ * f.toFun (1/y)) := by rfl
        _ = z * ((a • x) * z⁻¹ * f.toFun (1/x)) + z * ((b • y) * z⁻¹ * f.toFun (1/y)) := by simp [mul_add]
        _ = (z * ((a • x) * z⁻¹)) * f.toFun x⁻¹ + (z * ((b • y) * z⁻¹)) * f.toFun y⁻¹ := by simp; ac_rfl
        _ = (z * z⁻¹) * (a • x) * f.toFun x⁻¹ + (z * z⁻¹) * (b • y) * f.toFun y⁻¹ := by simp; ac_rfl
        _ = (a • x) * f.toFun x⁻¹ + (b • y) * f.toFun y⁻¹ := by simp only [ENNReal.mul_inv_cancel hz_pos.ne' hz_inf.ne]; simp
        _ = a • (x * f.toFun x⁻¹) + b • (y * f.toFun y⁻¹) := by simp

      have left_transform :=
        calc w1 • (1 / x) + w2 • (1 / y)
        _ = ((a • x) * z⁻¹) * x⁻¹ + ((b • y) * z⁻¹) * y⁻¹ := by
          simp [w1, w2, ENNReal.smul_def, div_eq_mul_inv]
        _ = (a • z⁻¹) * (x * x⁻¹) + (b • z⁻¹) * (y * y⁻¹) := by
          rw [ENNReal.smul_def, ENNReal.smul_def]
          simp [ENNReal.smul_def]
          ring_nf

        _ = (a • z⁻¹) + (b • z⁻¹) := by
          rw [ENNReal.mul_inv_cancel (mem_Ioi.mp hx).ne' hxinf.1]
          rw [ENNReal.mul_inv_cancel (mem_Ioi.mp hy).ne' hxinf.2]
          simp only [mul_one]
        _ = (a + b) • z⁻¹ := by
          -- #check ENNReal.add_smul
          have h1 : a • z⁻¹ ≠ ⊤:= ENNReal.nnreal_smul_ne_top (ENNReal.inv_ne_top.mpr hz_pos.ne')
          have h2 : b • z⁻¹ ≠ ⊤ :=  ENNReal.nnreal_smul_ne_top (ENNReal.inv_ne_top.mpr hz_pos.ne')
          rw [←(ENNReal.toNNReal_eq_toNNReal_iff' _ _)]
          rw [ENNReal.toNNReal_add]
          simp [add_mul]
          · exact h1
          · exact h2
          exact ENNReal.add_ne_top.mpr ⟨h1, h2⟩
          refine ENNReal.nnreal_smul_ne_top (ENNReal.inv_ne_top.mpr hz_pos.ne')

        _ = z⁻¹ := by
          rw [hab, one_smul]


      rw [←rhs_transform]
      refine mul_le_mul' (by exact Preorder.le_refl z) ?_
      rw [←left_transform]

      let hw1_nnreal := w1.toNNReal
      let hw2_nnreal := w2.toNNReal
      rw [←ENNReal.coe_toNNReal hw_top.1]
      rw [←ENNReal.coe_toNNReal hw_top.2]
      apply f.convexOn.2
      exact trivial
      exact trivial
      exact zero_le hw1_nnreal
      exact zero_le hw2_nnreal
      exact hw_sum_nnreal
    rw [not_and_or] at hxinf
    cases' hxinf with hx_eq_top hy_eq_top

    · -- Case: x = ∞
        -- simp [hx_eq_top]
        simp at hx_eq_top
        -- When x = ∞, we have x * f x⁻¹ = ∞ * f 0
        -- The left side (a • ∞ + b • y) * f (a • ∞ + b • y)⁻¹ is also ∞ * f 0 when a > 0
        by_cases ha_pos : 0 < a
        · -- If a > 0, then a • ∞ = ∞, so a • x + b • y = ∞
          have h_sum_top : a • x + b • y = ∞ := by
            rw [hx_eq_top]
            simp [ENNReal.smul_def, ha_pos.ne']
          simp [h_sum_top, hx_eq_top, ha_pos.ne', (Set.mem_Ioi.mp hy).ne']
          have ineq :=
            calc (a • ⊤ + b • y) * f.toFun (a • ⊤ + b • y)⁻¹
            _ = ⊤ * f.toFun 0 := by
              simp [ENNReal.smul_def, ha_pos.ne']
            _ = a • (⊤ * f.toFun 0) := by
              rw [← smul_mul_assoc]
              simp [ENNReal.smul_top, ha_pos.ne']
            _ ≤ a • (⊤ * f.toFun 0) + b • (y * f.toFun y⁻¹) := by
              nth_rewrite 1 [← add_zero (a • (⊤ * f 0))]
              by_cases h : a • (⊤ * f 0) = ⊤
              · simp
              · rw [ENNReal.add_le_add_iff_left h]
                exact zero_le _
          exact ineq

        · -- If a = 0, then the sum is b • y
          have ha_zero : a = 0 := le_antisymm (le_of_not_gt ha_pos) ha
          simp [ha_zero, hx_eq_top]
          rw [ha_zero] at hab
          simp at hab
          rw [hab, one_smul]
          -- Trivial case: y * f y⁻¹ ≤ y * f y⁻¹
          simp
    · -- Case: x = ∞
        simp at hy_eq_top
        by_cases hb_pos : 0 < b
        · -- If a > 0, then a • ∞ = ∞, so a • x + b • y = ∞
          have h_sum_top : a • x + b • y = ∞ := by
            rw [hy_eq_top]
            simp [ENNReal.smul_def, hb_pos.ne']
          simp [h_sum_top, hy_eq_top, hb_pos.ne', (Set.mem_Ioi.mp hx).ne']
          have ineq :=
            calc (a • x + b • ⊤) * f.toFun (a • x + b • ⊤)⁻¹
            _ = ⊤ * f.toFun 0 := by
              simp [ENNReal.smul_def, hb_pos.ne']
            _ = b • (⊤ * f.toFun 0) := by
              rw [← smul_mul_assoc]
              simp [ENNReal.smul_top, hb_pos.ne']

            _ ≤ a • (x * f.toFun x⁻¹) + b • (⊤ * f.toFun 0) := by
              nth_rewrite 1 [← add_zero (b • (⊤ * f 0))]
              rw [add_comm]
              by_cases h : b • (⊤ * f 0) = ⊤
              · simp
              · rw [ENNReal.add_le_add_iff_right h]
                exact zero_le _

          exact ineq

        · -- If a = 0, then the sum is b • y
          have hb_zero : b = 0 := le_antisymm (le_of_not_gt hb_pos) hb
          simp [hb_zero, hy_eq_top]
          rw [hb_zero] at hab
          simp at hab
          rw [hab, one_smul]
          -- Trivial case: y * f y⁻¹ ≤ y * f y⁻¹
          simp


lemma conjFnConvex (f : DivFunction):
    ConvexOn ℝ≥0 univ (conjFn f) := by
  rw [ConvexOn]
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb0 hab

    have convex_on_open (x : ℝ≥0∞) (hx : 0 < x)
    (y : ℝ≥0∞) (hy : 0 < y) (a : ℝ≥0) (b : ℝ≥0)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
      conjFn f (a • x + b • y) ≤ a • conjFn f x + b • conjFn f y := by

      have h2 : ∀ r > 0, conjFn f r = (fun x ↦ x * f x⁻¹) r := by
        intro r hr
        unfold conjFn
        simp [hr.ne']

      have h_sum_pos : 0 < a • x + b • y := by
        by_cases hb_zero : b = 0
        ·
          rw [hb_zero, add_zero] at hab
          rw [hb_zero, zero_smul, add_zero, hab, one_smul]
          exact hx
        ·
          refine Right.add_pos_of_nonneg_of_pos ?_ ?_
          exact zero_le (a • x)
          refine (smul_pos_iff_of_pos_left (pos_iff_ne_zero.mpr hb_zero)).mpr hy

      rw [h2 (a • x + b • y) h_sum_pos, h2 x hx, h2 y hy]
      -- #check (Set.Ioi_subset_Ici_self) (convex_Ioi 0)
      have h_conv_finite := conjFnConvexIoi f
      have conv := h_conv_finite.2 (mem_Ioi.mpr hx) (mem_Ioi.mpr hy) ha hb hab
      simp [conjFn, h_sum_pos.ne', hx.ne', hy.ne'] at conv
      exact conv

    have main_claim (x : ℝ≥0∞) (y : ℝ≥0∞) (a : ℝ≥0) (ha : 0 ≤ a) (b : ℝ≥0) (hb0 : 0 ≤ b)
        (hab : a + b = 1) (hx_zero : x = 0) (hy_zero : y ≠ 0) : (conjFn f (a • x + b • y) ≤ a • f.conjFn x + b • f.conjFn y) := by
      have hy_pos : 0 < y := lt_of_le_of_ne (zero_le y) (Ne.symm hy_zero)
      unfold conjFn
      simp [hx_zero, hy_zero]

      by_cases hb_zero : b = 0
      ·
        rw [hb_zero, add_zero] at hab
        simp [hb_zero, hab]

      ·
        have hby_pos : 0 < b • y := smul_pos (by positivity) hy_pos
        have hby_ne_zero : b • y ≠ 0 := ne_of_gt hby_pos
        simp [hby_ne_zero, hb_zero]
        have h_bound : b • (y * f (b • y)⁻¹) ≤ b •( y * f y⁻¹) + a • f.derivAtTop := by

          have h1 : (r : ℝ≥0∞) → (hr : r ≠ 0) → f.conjFn r = r * f (1 / r) := by
            intro r hr
            unfold conjFn
            simp [hr]

          have h3 : f.conjFn 0 = f.derivAtTop := by
            unfold conjFn
            simp [zero_le f.derivAtTop]

          have h_main : f.conjFn (b • y) ≤ a • f.conjFn 0 + b • f.conjFn y := by

            have h_eps : ∀ ε > 0, f.conjFn (a • ε + b • y) ≤ a • f.conjFn ε + b • f.conjFn y := by
              intro ε hε
              exact convex_on_open ε hε y hy_pos a b ha hb0 hab
            have h_lim : Tendsto (fun ε => f.conjFn (a • ε + b • y)) (𝓝[>] 0) (𝓝 (f.conjFn (b • y))) := by
              have h_cont : Continuous (fun x => a • x + b • y) := by
                exact (ENNReal.continuous_const_mul ENNReal.coe_lt_top.ne).add continuous_const
              have h_cont2 :  ContinuousAt (fun x => a • x + b • y) 0 := h_cont.continuousAt
              unfold ContinuousAt at h_cont2
              simp at h_cont2
              have h_seq_lim : Tendsto (fun ε => a • ε + b • y) (𝓝[>] 0) (𝓝 (b • y)) :=
                tendsto_nhdsWithin_of_tendsto_nhds h_cont2
              have h_cont_at : ContinuousAt (f.conjFn) (b • y) := (conjFnContinuous f).continuousAt
              exact Tendsto.comp h_cont_at h_seq_lim

            have h_lim_rhs : Tendsto (fun ε => a • f.conjFn ε + b • f.conjFn y) (𝓝[>] 0)
              (𝓝 (a • f.conjFn 0 + b • f.conjFn y)) := by
              have h_lim_conj : Tendsto (fun ε => f.conjFn ε) (𝓝[>] 0) (𝓝 (f.conjFn 0)) := by
                exact (ConjugateFnContinuousAt f).tendsto.mono_left nhdsWithin_le_nhds
              have h : Continuous (fun ε ↦ a • ε + b • f.conjFn y) := (ENNReal.continuous_const_mul ENNReal.coe_lt_top.ne).add continuous_const
              exact h.continuousAt.tendsto.comp h_lim_conj

            exact le_of_tendsto_of_tendsto h_lim h_lim_rhs (eventually_nhdsWithin_of_forall h_eps)
          rw [h1 y (hy_zero), h1 (b • y)  hby_pos.ne', h3] at h_main
          rw [add_comm] at h_main
          rw [one_div, one_div, smul_mul_assoc] at h_main
          exact h_main
        rw [add_comm]
        exact h_bound

    by_cases hx_zero : x = 0
    · by_cases hy_zero : y = 0
      ·
        simp [hx_zero, hy_zero, zero_smul]
        rw [← add_smul, hab, one_smul]
      ·
        exact main_claim x y a ha b hb0 hab hx_zero hy_zero

    ·
      have hx_pos : 0 < x := lt_of_le_of_ne (zero_le x) (Ne.symm hx_zero)

      by_cases hy_zero : y = 0
      · rw [add_comm] at hab
        have convexity := main_claim y x b hb0 a ha hab hy_zero hx_zero
        rw [add_comm, add_comm (a • conjFn f x)]
        exact convexity

      ·
        have hy_pos : 0 < y := lt_of_le_of_ne (zero_le y) (Ne.symm hy_zero)
        exact convex_on_open x hx_pos y hy_pos a b ha hb0 hab

noncomputable
def conj (f : DivFunction) : DivFunction where
  toFun x := conjFn f x
  one := by unfold conjFn; simp
  convexOn' := conjFnConvex f
  continuous' := conjFnContinuous f

end Conj

end DivFunction

end ProbabilityTheory
