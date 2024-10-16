import Mathlib.Analysis.Complex.AbsMax
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Maximum-modulus criteria for functions to be constant
-/

open Complex

/--
If `f` is differentiable on `{z : ℂ | ‖z‖ < 1}`, and `‖f‖` attains a maximum in this open ball,
then `f` is constant.
-/
lemma eq_const_of_exists_max {f : ℂ → ℂ} (h_an : DifferentiableOn ℂ f {z : ℂ | ‖z‖ < 1})
    {v : ℂ} (hv : ‖v‖ < 1) (hv_max : ∀ z, ‖z‖ < 1 → ‖f z‖ ≤ ‖f v‖) :
    Set.EqOn f (Function.const ℂ (f v)) {z : ℂ | ‖z‖ < 1} := by
  refine Complex.eqOn_of_isPreconnected_of_isMaxOn_norm ?_ ?_ h_an hv hv_max
  · apply Convex.isPreconnected
    simpa only [ball_zero_eq] using convex_ball (0 : ℂ) 1
  · simpa only [← ball_zero_eq] using Metric.isOpen_ball

/--
If `f` is a function differentiable on the open unit ball, and there exists an `r < 1` such that
any value of `‖f‖` on the open ball is bounded above by some value on the closed ball of radius `r`,
then `f` is constant.
-/
lemma eq_const_of_exists_le {f : ℂ → ℂ} (h_an : DifferentiableOn ℂ f {z : ℂ | ‖z‖ < 1})
    {r : ℝ} (hr_nn : 0 ≤ r) (hr_lt : r < 1)
    (hr : ∀ z, ‖z‖ < 1 → ∃ w, ‖w‖ ≤ r ∧ ‖f z‖ ≤ ‖f w‖) :
    Set.EqOn f (Function.const ℂ (f 0)) {z : ℂ | ‖z‖ < 1} := by
  let V : Set ℂ := {z | ‖z‖ ≤ r}
  have hVc : IsCompact V := by simpa only [norm_eq_abs, Metric.closedBall, dist_eq_norm_sub,
    sub_zero, V] using isCompact_closedBall (0 : ℂ) r
  have hVne : V.Nonempty := ⟨0, by simp only [norm_eq_abs, Set.mem_setOf_eq, map_zero, hr_nn, V]⟩
  have : ContinuousOn f V := by
    apply h_an.continuousOn.mono
    simpa only [norm_eq_abs, Set.setOf_subset_setOf, V] using fun _ ha ↦ ha.trans_lt hr_lt
  obtain ⟨x, hx_mem, hx_max⟩ := hVc.exists_isMaxOn hVne this.norm
  suffices Set.EqOn f (Function.const ℂ (f x)) {z : ℂ | ‖z‖ < 1} by
    refine this.trans fun y _ ↦ ?_
    simp only [Function.const_apply, this (by simp only [norm_zero, zero_lt_one] : ‖(0 : ℂ)‖ < 1)]
  apply eq_const_of_exists_max h_an (lt_of_le_of_lt hx_mem hr_lt) (fun z hz ↦ ?_)
  obtain ⟨w, hw, hw'⟩ := hr z hz
  exact hw'.trans (hx_max hw)

/-
We want to apply the above lemma to `cusp_function h f`, where `f` is a modular form of weight 0.
If we choose `r = exp (-π * √3)`, then the image of the fundamental domain is contained in
`{z | ‖z‖ ≤ r}`.
-/

open UpperHalfPlane Modular
local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

/-- non-strict variant of `ModularGroup.three_le_four_mul_im_sq_of_mem_fdo` -/
theorem ModularGroup.three_le_four_mul_im_sq_of_mem_fd {τ : ℍ} (h : τ ∈ 𝒟) : 3 ≤ 4 * τ.im ^ 2 := by
  have : 1 ≤ τ.re * τ.re + τ.im * τ.im := by simpa [Complex.normSq_apply] using h.1
  have := h.2
  cases abs_cases τ.re <;> nlinarith

lemma exists_translate (τ : ℍ) :
    ∃ γ : SL(2, ℤ), 1 / 2 ≤ im (γ • τ) := by
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  use γ
  have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hγ
  have := UpperHalfPlane.im_pos (γ • τ)
  nlinarith

abbrev Γ := CongruenceSubgroup.Gamma 1

lemma denom_one (τ : ℍ) : denom 1 τ = 1 := by
  simp only [denom, OneMemClass.coe_one, Fin.isValue, Units.val_one, ne_eq, one_ne_zero,
    not_false_eq_true, Matrix.one_apply_ne, ofReal_zero, zero_mul, Matrix.one_apply_eq, ofReal_one,
    zero_add, norm_one]

lemma ModularGroup.coe_one : UpperHalfPlane.ModularGroup.coe' 1 = 1 := by
  simp only [ModularGroup.coe', map_one]

lemma exists_translate' (τ : ℍ) :
    ∃ γ : SL(2, ℤ), 1 / 2 ≤ im (γ • τ) ∧ ‖denom γ τ‖ ≤ 1 := by
  by_cases h : 1 / 2 ≤ τ.im
  · refine ⟨1, by simpa using h, by simp [ModularGroup.coe_one, denom_one]⟩
  · obtain ⟨γ, hγ⟩ := exists_translate τ
    refine ⟨γ, hγ, ?_⟩
    have h0 := im_smul_eq_div_normSq γ τ
    simp only [ModularGroup.det_coe', one_mul, ← UpperHalfPlane.ModularGroup.sl_moeb] at h0
    have h1 : τ.im ≤ (γ • τ).im := by nlinarith
    rw [h0, le_div_iff₀ (normSq_denom_pos (↑γ) τ), normSq_eq_norm_sq] at h1
    have H : ‖denom γ τ‖^2 ≤ 1 := (mul_le_iff_le_one_right τ.2).mp h1
    simpa using H

def coe1 : SL(2, ℤ) → Γ :=
  fun g => ⟨↑g, by simp [Γ, CongruenceSubgroup.Gamma_one_top]⟩

instance : Coe SL(2, ℤ) Γ := ⟨coe1⟩

@[simp]
lemma coe_smul_eq_smul {g : SL(2, ℤ)} {τ : ℍ} : (g : Γ) • τ =  (g • τ)  := by
  rw [coe1]
  simp

@[simp]
lemma denom_coe1_eq_denom {g : SL(2, ℤ)} {τ : ℍ} : denom (g : Γ) τ = denom g τ := by
  simp only [denom, coe1, Fin.isValue, ModularGroup.coe'_apply_complex]

variable {F : Type*} [FunLike F ℍ ℂ]

theorem slash_action_eqn'' (k : ℤ) (Γ : Subgroup SL(2, ℤ)) [SlashInvariantFormClass F Γ k] (f : F)
    (γ : Γ) (z : ℍ) : f (γ • z) = (denom γ z) ^ k * f z := by
  rw [denom]
  exact (SlashInvariantForm.slash_action_eqn' k Γ f γ z)

lemma modform_exists_norm_le {k : ℤ} (hk : k ≤ 0) (f : ModularForm Γ k) (τ : ℍ) :
    ∃ ξ : ℍ, 1/2 ≤ ξ.im ∧ ‖f τ‖ ≤ ‖f ξ‖ := by
    /- Proof: take ξ = γ • τ where γ is as in `exists_translate'`. Then use the equation
  `f ξ = (denom γ τ) ^ k * f τ` and the fact that `k ≤ 0` and `‖denom γ τ‖ ≤ 1`.
  -/
  obtain ⟨γ, hγ, hdenom⟩ := exists_translate' τ
  use γ • τ
  refine ⟨hγ, ?_⟩
  have := slash_action_eqn'' k Γ f γ τ
  rw [coe_smul_eq_smul, denom_coe1_eq_denom] at this
  rw [this,norm_mul, norm_zpow]
  have h2 : 0 ≤ ‖f τ‖ := norm_nonneg (f τ)
  have h3 : 1 ≤  ‖denom (γ : SL(2, ℤ)) τ‖ ^ k := by
    apply one_le_zpow_of_nonpos₀ _ hdenom hk
    rw [norm_pos_iff]
    apply denom_ne_zero
  nlinarith


-- Now, if we can get the `cusp function` stuff from QExpansion.lean working properly, we can
-- deduce that any level 1, wt ≤ 0 modular form is constant.
-- Clearly a nonzero constant can't be modular of weight < 0 -- we should probably have a lemma
-- that a function which is modular for the same group in two different levels is 0 --
-- so we are done.
