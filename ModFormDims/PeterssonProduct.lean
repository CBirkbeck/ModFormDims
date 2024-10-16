import ModFormDims.QExpansion

section PeterssonDefs

/-!
## Definitions around the Petersson product
-/

/-- Integrand in the Petersson product of two weight `k` modular forms. -/
def pet (f g : ℍ → ℂ) (k : ℤ) (z : ℍ) : ℂ := conj (f z) * g z * z.im ^ k

/--
Integrand in the Petersson product of a weight `k` form with itself (as a real-valued function).
-/
def petSelf (f : ℍ → ℂ) (k : ℤ) (z : ℍ) : ℝ :=  Complex.abs (f z) ^ 2 * z.im ^ k

theorem pet_is_invariant {k : ℤ} {Γ : Subgroup SL(2, ℤ)} (f g : SlashInvariantForm Γ k)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (z : ℍ) :
    pet f g k (γ • z) = pet f g k z := by
  let D := denom γ z
  have hD : D ≠ 0 := by apply denom_ne_zero
  have mod_g : g (γ • z) = D ^ k * g z := by
    have tt := (SlashInvariantForm.slash_action_eqn' k Γ g) ⟨γ, hγ⟩ z
    dsimp only [denom] at *; exact tt
  have mod_f : conj (f (γ • z)) = conj D ^ k * conj (f z) := by
    have tt : f (γ • z) = D ^ k * f z := by
      apply (SlashInvariantForm.slash_action_eqn' k Γ f) ⟨γ, hγ⟩ z
    rw [tt, starRingEnd_apply, starRingEnd_apply, star_mul', ← star_zpow₀]; rfl
  dsimp only [pet]
  rw [mod_f, mod_g]
  suffices ↑(γ • z).im = ↑(UpperHalfPlane.im z) / D / conj D by
    rw [this]; simp (config := { zeta := false }) only [coe_im, div_zpow]
    trans (z.im : ℂ) ^ k / D ^ k / conj D ^ k * D ^ k * conj D ^ k * g z * conj (f z)
    · ring
    trans (UpperHalfPlane.im z : ℂ) ^ k * g z * conj (f z)
    swap
    · ring
    congr 2
    have h1 : D ^ k ≠ 0 := zpow_ne_zero _ hD
    have h2 : conj D ^ k ≠ 0 := by
      apply zpow_ne_zero
      rw [starRingEnd_apply, star_ne_zero]
      exact hD
    rw [div_div, mul_assoc];
    apply div_mul_cancel₀
    apply mul_ne_zero h1 h2
  have : ((γ • z : ℍ) : ℂ).im = UpperHalfPlane.im z / Complex.normSq D :=  by
    rw [UpperHalfPlane.coe_im, sl_moeb', UpperHalfPlane.im_smul_eq_div_normSq γ z]
    refine congr_arg (fun x ↦ x / Complex.normSq D) ?_
    convert one_mul (UpperHalfPlane.im z)
    simp  [UpperHalfPlane.coe_im,
      Matrix.SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.coe_matrix_coe, Int.coe_castRingHom]
  apply_fun ((↑) : ℝ → ℂ) at this
  convert this
  simp only [UpperHalfPlane.coe_im, Complex.ofReal_div]
  rw [div_div, mul_conj]

theorem petSelf_eq (f : ℍ → ℂ) (k : ℤ) (z : ℍ) : petSelf f k z = re (pet f f k z) := by
  dsimp only [pet, petSelf]
  simp_rw [starRingEnd_apply]
  have : (star (f z) * f z * (z.im : ℂ) ^ k).re = (star (f z) * f z).re * ↑z.im ^ k := by
    conv => enter [1, 1]; rw [mul_comm]
    rw [← ofReal_zpow, re_ofReal_mul, mul_comm]
  rw [this]
  congr
  rw [mul_comm, ← normSq_eq_abs, normSq]
  simp only [MonoidWithZeroHom.coe_mk, mul_re, conj_re, conj_im, mul_neg,
    sub_neg_eq_add]
  simp only [ZeroHom.coe_mk, RCLike.star_def, conj_re, conj_im, mul_neg, sub_neg_eq_add]

theorem petSelf_is_invariant {k : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : SlashInvariantForm Γ k)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (z : ℍ) : petSelf f k (γ • z) = petSelf f k z := by
  rw [petSelf_eq, petSelf_eq, pet_is_invariant f f hγ z]

end PeterssonDefs

section Petersson

open scoped ModularForm

-- Bound on abs(f z) for large values of z
theorem pet_bounded_large {k : ℤ} (f : CuspForm ⊤ k) :
    ∃ A C : ℝ, ∀ z : ℍ, A ≤ im z → (petSelf f k) z ≤ C := by
  -- first get bound for large values of im z
  have h1 := exp_decay_of_cuspform _ f
  have : IsBigO UpperHalfPlane.atImInfty (fun z : ℍ ↦ Real.exp (-2 * π * z.im))
      fun z : ℍ ↦ 1 / z.im ^ ((k : ℝ) / 2) := by
    apply IsLittleO.isBigO;
    apply isLittleO_of_tendsto
    · intro x hx; exfalso
      contrapose! hx; apply one_div_ne_zero
      refine' (Real.rpow_pos_of_pos x.2 _).ne'
    rw [UpperHalfPlane.atImInfty]
    let F := fun y : ℝ ↦ Real.exp (-2 * π * y) / (1 / y ^ ((k : ℝ) / 2))
    apply (@tendsto_comap'_iff _ _ _ F _ _ _ _).mpr
    · have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_0 ((k : ℝ) / 2) (2 * π) Real.two_pi_pos
      refine' Tendsto.congr' _ this; apply eventually_of_mem (Ioi_mem_atTop (0 : ℝ))
      intro y _;  simp; apply mul_comm;
    · convert Ioi_mem_atTop (0 : ℝ); ext1 x; rw [Set.mem_range]
      constructor; · rintro ⟨y, hy⟩; rw [← hy]; exact y.2
      · intro h;
        use ⟨x * I, ?_⟩
        swap
        · rw [mul_I_im]; exact h
        · rw [UpperHalfPlane.im]
          simp  [Subtype.coe_mk, mul_im, ofReal_re, I_im, mul_one, I_re, MulZeroClass.mul_zero,
            add_zero]
  obtain ⟨C1, h1'⟩ := (h1.trans this).bound
  rw [eventually_iff, UpperHalfPlane.atImInfty_mem] at h1' ; cases' h1' with A h1'
  dsimp at h1' ; refine' ⟨A, C1 ^ 2, _⟩
  intro z hz; specialize h1' z hz; rw [petSelf]
  have : im z ^ k = (im z ^ ((k : ℝ) / 2)) ^ 2 := by
    norm_cast
    rw [← Real.rpow_int_cast, ← Real.rpow_nat_cast, ← Real.rpow_mul]
    swap; exact z.2.le; congr 1; norm_cast
    rw [Rat.divInt_eq_div]
    field_simp
  rw [← UpperHalfPlane.coe_im, this, ← mul_pow]
  rw [sq_le_sq]
  have e : 0 < z.im ^ ((k : ℝ) / 2) := by apply Real.rpow_pos_of_pos; exact z.2
  have : abs (f z) * im z ^ ((k : ℝ) / 2) ≤ C1 := by
    rw [div_eq_inv_mul, mul_one, _root_.abs_inv, mul_comm] at h1'
    simp at *
    have h2 : 0 ≤ (z.1).im ^ ((k : ℝ) / 2) := by
      norm_cast
      apply Real.rpow_nonneg
      exact z.2.le
    have h1'' := mul_le_mul_of_nonneg_right h1' h2
    refine' le_trans h1'' _
    · rw [_root_.abs_of_nonneg]
      swap;
      · norm_cast at *
      conv =>
        lhs
        congr
        rw [mul_comm];
      rw [mul_assoc]
      suffices th : (z.im ^ ((k : ℝ) / 2))⁻¹ * z.im ^ ((k : ℝ) / 2) = 1 by
        simp_rw [← UpperHalfPlane.coe_im] at *
        erw [th]; -- TODO why erw
        simp
      apply inv_mul_cancel; exact e.ne'
  apply abs_le_abs;
  norm_cast at *
  have aux : -(Complex.abs (f z) * (z.1).im ^ ((k : ℝ) / 2)) ≤ Complex.abs (f z) * z.1.im ^ ((k : ℝ) / 2) := by
    simp
    apply mul_nonneg; apply AbsoluteValue.nonneg; exact e.le
  norm_cast at *
  apply le_trans aux this


end Petersson
