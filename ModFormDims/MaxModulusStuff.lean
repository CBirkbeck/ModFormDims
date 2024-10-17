import Mathlib.Analysis.Complex.AbsMax
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import ModFormDims.QExpansionModform

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
lemma coe_smul_eq_smul {g : SL(2, ℤ)} {τ : ℍ} : (g : Γ) • τ = (g • τ) := by
  simp only [coe1, Subgroup.mk_smul, ModularGroup.sl_moeb]

@[simp]
lemma denom_coe1_eq_denom {g : SL(2, ℤ)} {τ : ℍ} : denom (g : Γ) τ = denom g τ := by
  simp only [denom, coe1, Fin.isValue, ModularGroup.coe'_apply_complex]

theorem slash_action_eqn'' {F : Type*} [FunLike F ℍ ℂ] (k : ℤ) (Γ : Subgroup SL(2, ℤ))
    [SlashInvariantFormClass F Γ k] (f : F) (γ : Γ) (z : ℍ) :
    f (γ • z) = (denom γ z) ^ k * f z := by
  rw [denom]
  exact (SlashInvariantForm.slash_action_eqn' k Γ f γ z)

lemma modform_exists_norm_le {k : ℤ} (hk : k ≤ 0) {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F)  (τ : ℍ) :
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
  have h3 : 1 ≤ ‖denom (γ : SL(2, ℤ)) τ‖ ^ k := by
    apply one_le_zpow_of_nonpos₀ _ hdenom hk
    rw [norm_pos_iff]
    apply denom_ne_zero
  nlinarith
open ModularForm CongruenceSubgroup

/- local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

lemma aux (A B : SL(2, ℤ)) : (ModularGroup.coe' A) * B = ModularGroup.coe' (A * B) := by
  simp_rw [ModularGroup.coe']
  simp only [map_mul]

lemma aux2  : (ModularGroup.coe' 1)  = 1 := by
  simp_rw [ModularGroup.coe']
  simp only [map_one] -/

lemma slash_eq_func_prod (f : ℍ → ℂ) (k : ℤ) (H : Subgroup SL(2, ℤ)) (γ : H) : f ∣[k] γ =
    (fun z => f (γ • z)) * (fun z => (denom γ z)^k)⁻¹ := by
  ext z
  simp [slash_def, slash]

@[simp]
lemma denom_S (z : ℍ) : denom (ModularGroup.S) z = z.1 := by
  rw [ModularGroup.S, denom]
  simp only [Int.reduceNeg, Fin.isValue, ModularGroup.coe'_apply_complex, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.head_fin_const, Int.cast_one, one_mul, Matrix.head_cons,
    Int.cast_zero, add_zero]
  rfl

lemma Complex.zpow_two_eq_one (k : ℤ) (h : (2 : ℂ) ^ k = 1) : k = 0 := by
  replace h : ‖(2 : ℂ)^k‖ = 1 := by simp [h]
  replace h : ‖(2 : ℝ)^k‖ = 1 := by simp [← h]
  replace h : (2 : ℝ)^k = (2 : ℝ)^(0 : ℤ) := by simp [← h]
  exact zpow_right_injective₀ (by norm_num) (by norm_num) h


lemma const_modform_neg_wt_eq_zero_lvl_one {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
    [ModularFormClass F Γ k] (f : F) (c : ℂ) (hf : ⇑f = (fun _ => c)) : k = 0 ∨ c = 0 := by
  have := slash_action_eqn'' k Γ f
  rw [hf] at this
  have hI := (this ModularGroup.S) I
  have h2I2 := (this ModularGroup.S) ⟨2 * Complex.I, by simp⟩
  simp only [SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe, subgroup_slash,
    Subtype.forall, Gamma_mem, Fin.isValue, and_imp, denom_coe1_eq_denom, denom_S, Pi.mul_apply,
    Pi.inv_apply] at *
  nth_rw 1 [ hI] at h2I2
  simp  [mul_eq_mul_left_iff, inv_inj] at h2I2
  rcases h2I2 with H | H
  · left
    symm at H
    rw [UpperHalfPlane.I, mul_zpow, mul_left_eq_self₀] at H
    rcases H with H | H
    · apply Complex.zpow_two_eq_one k H
    · exfalso
      exact (zpow_ne_zero k I_ne_zero) H
  · exact Or.inr H

open Real

lemma neg_wt_modform_zero (k : ℤ) (hk : k ≤ 0) {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) : ⇑f = 0 ∨ (k = 0 ∧ ∃ c : ℂ, ⇑f = fun _ => c) := by
  have hdiff : DifferentiableOn ℂ (cuspFcnH f) {z : ℂ | ‖z‖ < 1} := by
    exact fun z hz ↦ DifferentiableAt.differentiableWithinAt (cusp_fcn_diff f hz)
  have heq : Set.EqOn (cuspFcnH f) (Function.const ℂ ((cuspFcnH f) 0)) {z : ℂ | ‖z‖ < 1} := by
    apply eq_const_of_exists_le (r := exp (-(π * √3)/2)) hdiff
    · exact exp_nonneg _
    · refine exp_lt_one_iff.mpr ?hr_lt.a
      rw [@div_neg_iff]
      right
      simp only [Left.neg_neg_iff, pi_pos, mul_pos_iff_of_pos_left, sqrt_pos, Nat.ofNat_pos,
        and_self]
    · intro z hz
      rcases eq_or_ne z 0 with rfl | hz'
      · refine ⟨0, by simpa using exp_nonneg _, by rfl⟩
      · obtain ⟨ξ, hξ, hξ₂⟩ := modform_exists_norm_le hk f ⟨(Z 1 z), by apply z_in_H hz hz'⟩
        use Q 1 ξ
        constructor
        · rw [Q]
          simp only [ofReal_one, div_one, Complex.norm_eq_abs, Complex.abs_exp]
          gcongr
          simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
            Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re,
            coe_im, zero_sub, neg_le]
          ring_nf
          simp_rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ pi_nonneg
          have : 1 ≤ ξ.im * 2 := by
            rw [div_le_iff₀ zero_lt_two] at hξ
            exact hξ
          apply le_trans _ this
          have : √3 ≤ 2 := by
            apply sqrt_le_iff.mpr ?_
            norm_cast
          linarith
        · rw [eq_cuspFcnH f ξ, eq_cuspFcnH f ⟨(Z 1 z), by apply z_in_H hz hz'⟩] at hξ₂
          convert hξ₂
          exact (QZ_eq_id one_ne_zero z hz').symm
  have H : ⇑f = Function.const ℍ ((cuspFcnH f) 0) := by
    ext z
    have e1 := eq_cuspFcnH f z
    have hQ : Q 1 z ∈ {z | ‖z‖ < 1} := by
      simpa using (abs_q_lt_iff zero_lt_one 0 z.1).mpr z.2
    simpa only [SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe, e1,
      Function.const_apply] using heq hQ
  have HF := const_modform_neg_wt_eq_zero_lvl_one k f (cuspFcnH f 0) H
  rcases HF with HF | HF
  · right
    simp [HF]
    use (cuspFcnH (⇑f) 0)
    simpa using H
  · left
    ext z
    have := congrFun H z
    rw [HF] at this
    simpa only [zero_apply, SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe,
      Function.const_apply] using this


lemma ModularForm_neg_weigth_eq_zero (k : ℤ) (hk : k < 0) {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) : ⇑f = 0 := by
  rcases neg_wt_modform_zero k hk.le f with h | ⟨rfl, _, _⟩
  exact h
  aesop

lemma ModularForm_weight_zero_constant {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ 0] (f : F) : ∃ c : ℂ, ⇑f = fun _ => c := by
  rcases neg_wt_modform_zero 0 (by rfl) f with h1 | h2
  refine ⟨0, ?_⟩
  simp only [h1, SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe, coe_zero]
  rfl
  aesop

lemma weigth_zero_rank_eq_one : Module.rank ℂ (ModularForm Γ 0) = 1 := by
  let f := ModularForm.const 1 (Γ := Γ)
  have hf : f ≠ 0 := by
    rw [@DFunLike.ne_iff]
    use I
    simp only [const_toFun, Function.const_apply, zero_apply, ne_eq, one_ne_zero, not_false_eq_true,
      f]
  apply rank_eq_one f hf
  intro g
  rw [@DFunLike.ne_iff] at hf
  obtain ⟨c', hc'⟩ := ModularForm_weight_zero_constant g
  use c'
  ext z
  simp only [zero_apply, ne_eq, SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe,
    smul_apply, smul_eq_mul] at *
  have : f z = 1 := rfl
  simp [this]
  exact Eq.symm (congrFun hc' z)

lemma neg_weight_rank_zero (k : ℤ) (hk : k < 0) : Module.rank ℂ (ModularForm Γ k) = 0 := by
  rw [rank_eq_zero_iff]
  intro f
  refine ⟨1, by simp, ?_⟩
  exact
    Eq.mpr (id (congrArg (fun x ↦ x = 0) (one_smul ℂ f)))
      (ModularForm.ext_iff.mpr (congrFun (ModularForm_neg_weigth_eq_zero k hk f)))

-- Now, if we can get the `cusp function` stuff from QExpansion.lean working properly, we can
-- deduce that any level 1, wt ≤ 0 modular form is constant.
-- Clearly a nonzero constant can't be modular of weight < 0 -- we should probably have a lemma
-- that a function which is modular for the same group in two different weights is 0 --
-- so we are done.
