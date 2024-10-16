import ModFormDims.QExpansion

/-!
# q-expansions of modular forms

We show that if `f : ℂ → ℂ` satisfies `f(z + h) = f(z)`, for some nonzero real `h`, then
there is a well-defined `F` such that `f(z) = F(exp(2 * π * I * z / h))` for all `z`;
and if `f` is holomorphic at some `z`, then `F` is holomorphic at `q = exp (2 * π * I * z / h)`.

We also show (using Riemann's removable singularity theorem) that if `f` is holomorphic and bounded
for all sufficiently large `im z`, then `F` extends to a holomorphic function on a neighbourhood of
`0`. As a consequence, if `f` tends to zero as `im z → ∞`, then in fact it decays *exponentially*
to zero.
-/

open ModularForm Complex Filter Asymptotics UpperHalfPlane

open scoped Real Topology Manifold Filter ComplexConjugate SlashInvariantForm

noncomputable section

/-!
## Formalism copied from elsewhere in ModularForms library
-/
local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

attribute [-instance] Matrix.SpecialLinearGroup.instCoeFun
attribute [-instance] Matrix.GeneralLinearGroup.instCoeFun

variable (g : SL(2, ℤ)) (z : ℍ) (Γ : Subgroup SL(2, ℤ))

/-! Now we prove corresponding results about modular forms. -/

instance : VAdd ℝ ℍ := by
  constructor; intro h z; refine' ⟨z + h, _⟩;
  suffices 0 < Complex.im (z + h) by exact this
  rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact z.2

/-! Tedious checks that notions of holomorphic, bounded, etc are compatible with extension-by-0--/


section ModformEquivs

variable {f : ℍ → ℂ} {k : ℤ}

theorem modform_bound_aux (C : ℝ) (g : ℂ → ℂ) (hc : 0 ≤ C)
    (h_bd : IsBigOWith C atImInfty f fun z : ℍ ↦ g z) :
    IsBigOWith C atIInf' (extendByZero f) g := by
  rw [isBigOWith_iff] at h_bd ⊢
  apply eventually_of_mem
  show {z : ℂ | Complex.abs (extendByZero f z) ≤ C * Complex.abs (g z)} ∈ atIInf'
  · rw [atIInf'_mem]
    rw [atImInfty, eventually_iff_exists_mem] at h_bd ; obtain ⟨v, hv, h_bd⟩ := h_bd
    rw [mem_comap', mem_atTop_sets] at hv ; cases' hv with a hv; use a
    intro z hz; specialize hv (im z) hz.le; dsimp at hv
    simp_rw [extendByZero]; dsimp; split_ifs with h
    swap; · rw [AbsoluteValue.map_zero]; refine' mul_nonneg hc _; apply AbsoluteValue.nonneg
    specialize h_bd ⟨z, h⟩
    specialize h_bd (hv _); rfl; exact h_bd
  · dsimp; intro x hx; linarith

local notation:73 f "∣[" k:0 "," A "]" => SlashAction.map ℂ k A f

theorem modform_bounded (f : ModularForm ⊤ k) :
    IsBigO atIInf' (extendByZero f) (1 : ℂ → ℂ) := by
  have bd := f.bdd_at_infty' (1 : SL(2, ℤ))
  have : f.toFun∣[k,(1 : SL(2, ℤ))] = f := by apply SlashAction.slash_one
  simp at bd
  rw [ IsBoundedAtImInfty] at bd
  rw [BoundedAtFilter] at bd
  obtain ⟨c, c_pos, bd⟩ := bd.exists_nonneg
  rw [atIInf']
  apply (modform_bound_aux c 1 c_pos _).isBigO
  simp
  simp_rw [IsBigOWith] at *
  simp at *
  exact bd

theorem cuspform_vanish_infty (f : CuspForm ⊤ k) :
    IsLittleO atIInf' (extendByZero f) (1 : ℂ → ℂ) := by
  have bd := f.zero_at_infty' (1 : SL(2, ℤ))
  have : f.toFun∣[k,(1 : SL(2, ℤ))] = f := by apply SlashAction.slash_one
  simp at bd
  rw [IsZeroAtImInfty] at bd
  have : IsLittleO atImInfty f (1 : ℍ → ℂ) := by
    apply isLittleO_of_tendsto; simp;
    simpa using bd
  rw [IsLittleO] at *; exact fun c hc ↦ modform_bound_aux c 1 hc.le (this hc)

theorem modform_periodic (f : ModularForm (CongruenceSubgroup.Gamma 1) k) (w : ℂ) :
    (extendByZero f) (w + 1) = (extendByZero f) w := by
  by_cases hw : 0 < im w
  · rw [extendByZero_eq_of_mem f w hw]
    have : 0 < im (w + 1) := by rw [add_im, one_im, add_zero]; exact hw
    rw [extendByZero_eq_of_mem f _ this]
    have t := SlashInvariantForm.vAdd_width_periodic 1 k 1 f.1 ⟨w, hw⟩
    convert t
    simp
    rw [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_vadd]
    simp
    apply add_comm
  · have : extendByZero f w = 0 := by
      rw [extendByZero];
      split_ifs with h
      exfalso;
      swap
      rfl
      exact  hw h
    rw [this]
    have : extendByZero f (w + 1) = 0 := by
      rw [extendByZero]
      split_ifs with h
      exfalso
      have : 0 < im (w + 1) := by tauto
      rw [add_im, one_im, add_zero] at this
      exact hw this
      rfl
    exact this

theorem modform_hol (f : ModularForm ⊤ k) (z : ℂ) (hz : 0 < im z) :
    DifferentiableAt ℂ (extendByZero f) z := by
  have foo1 : extendByZero f =ᶠ[𝓝 z] f ∘ UpperHalfPlane.ofComplex := by
    refine eventually_of_mem (U := {z : ℂ | 0 < z.im}) ?_ ?_
    · apply IsOpen.mem_nhds
      exact continuous_im.isOpen_preimage _ isOpen_Ioi
      exact hz
    · intro x hx
      rw [extendByZero_eq_of_mem _ _ hx]
      simp only [Function.comp_apply]
      have : ofComplex x = ⟨x, hx⟩ := UpperHalfPlane.ofComplex_apply ⟨x, hx⟩
      rw [← this]
  have foo2 : UpperHalfPlane.coe ∘ UpperHalfPlane.ofComplex =ᶠ[𝓝 z] id := by
    refine eventually_of_mem (U := {z : ℂ | 0 < z.im}) ?_ ?_
    · apply IsOpen.mem_nhds
      exact continuous_im.isOpen_preimage _ isOpen_Ioi
      exact hz
    · intro x hx
      simp only [Function.comp_apply, id_eq, Set.mem_setOf.mp hx, dite_true]
      have : ofComplex x = ⟨x, hx⟩ := UpperHalfPlane.ofComplex_apply ⟨x, hx⟩
      rw [this]
      rfl
  refine DifferentiableAt.congr_of_eventuallyEq ?_ foo1
  rw [← mdifferentiableAt_iff_differentiableAt]
  refine MDifferentiableAt.comp z (f.holo' _) ?_
  rw [mdifferentiableAt_iff]
  constructor
  · rw [ContinuousAt, nhds_induced, tendsto_comap_iff]
    refine Tendsto.congr' foo2.symm ?_
    have : ofComplex z = ⟨z, hz⟩ := UpperHalfPlane.ofComplex_apply ⟨z, hz⟩
    rw [this, Subtype.coe_mk]
    exact tendsto_id
  · simp only [writtenInExtChartAt, extChartAt, PartialHomeomorph.extend,
      OpenEmbedding.toPartialHomeomorph_source, PartialHomeomorph.singletonChartedSpace_chartAt_eq,
      modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, PartialHomeomorph.toFun_eq_coe,
      OpenEmbedding.toPartialHomeomorph_apply, PartialHomeomorph.refl_partialEquiv,
      PartialEquiv.refl_source, PartialEquiv.refl_symm, PartialEquiv.refl_coe, CompTriple.comp_eq,
      modelWithCornersSelf_coe, Set.range_id, id_eq, differentiableWithinAt_univ]
    exact DifferentiableAt.congr_of_eventuallyEq differentiableAt_id foo2


theorem modform_hol_infty (f : ModularForm ⊤ k) :
    ∀ᶠ z : ℂ in atIInf', DifferentiableAt ℂ (extendByZero f) z := by
  refine' eventually_of_mem (_ : UpperHalfPlane.upperHalfSpace ∈ atIInf') _
  · rw [atIInf'_mem]; use 0; tauto
  · intro x hx; exact modform_hol f x hx

end ModformEquivs

section Modforms

def unitDiscSset :=
  {z : ℂ | Complex.abs z< 1}

theorem unit_disc_isOpen : IsOpen unitDiscSset :=
  isOpen_Iio.preimage Complex.continuous_abs

local notation "𝔻" =>  (TopologicalSpace.Opens.mk unitDiscSset unit_disc_isOpen)

variable (f : ℍ → ℂ) (k : ℤ)

--lemma q_in_D (z : ℍ) : abs (Q 1 z) < 1 := by { convert (abs_q_lt_iff 1 0 z).mpr z.2, simp }
theorem z_in_H (q : 𝔻) (hq : (q : ℂ) ≠ 0) :
    0 < im (Z 1 q) := by
  rw [im_z_eq 1 q]
  apply mul_pos_of_neg_of_neg
  · exact div_neg_of_neg_of_pos (neg_lt_zero.mpr zero_lt_one) Real.two_pi_pos
  rw [Real.log_neg_iff]; exact q.2
  apply AbsoluteValue.pos; exact hq

def cuspFcnH : ℂ → ℂ :=
  cuspFcn 1 <| extendByZero f

theorem eq_cuspFcnH (z : ℍ) (f : ModularForm ⊤ k) :
    f z = (cuspFcnH f) (Q 1 z) := by
  have t := eq_cuspFcn 1 (extendByZero f) (modform_periodic f) z
  rw [cuspFcnH]; convert t
  rw [extendByZero_eq_of_mem f _ _]; · simp;
  · cases z; tauto

theorem cusp_fcn_diff (f : ModularForm ⊤ k) (q : 𝔻) :
    DifferentiableAt ℂ (cuspFcnH f) q := by
  by_cases hq : (q : ℂ) = 0
  · rw [hq];
    exact
      F_diff_at_zero 1 (extendByZero f) (modform_periodic f) (modform_bounded f)
        (modform_hol_infty f)
  · have t :=
      cuspFcn_diff_at 1 (extendByZero f) (modform_periodic f) _ (modform_hol f _ <| z_in_H q hq)
    rw [QZ_eq_id 1 q hq] at t ; rw [cuspFcnH]; exact t

/-
def cuspFormToModForm (f : CuspForm ⊤ k) : ModularForm ⊤ k
    where
  toFun := f.toFun
  slash_action_eq' := f.slash_action_eq'
  holo' := f.holo'
  bdd_at_infty' := by
    intro A;
    simp
    have := (f.zero_at_infty' A).BoundedAtFilter; convert this

  instance : Coe (CuspForm ⊤ k) (ModularForm ⊤ k) :=
-/



theorem cusp_fcn_vanish (f : CuspForm ⊤ k) : cuspFcnH f 0 = 0 := by
  have :=cuspFcn_zero_of_zero_at_inf 1 (extendByZero f) ?_
  apply this
  apply cuspform_vanish_infty


theorem exp_decay_of_cuspform (f : CuspForm ⊤ k) :
    IsBigO UpperHalfPlane.atImInfty f fun z : ℍ ↦ Real.exp (-2 * π * im z) := by
  have := exp_decay_of_zero_at_inf 1 (extendByZero f) (modform_periodic (f : ModularForm ⊤ k))
    (cuspform_vanish_infty f) (modform_hol_infty (f : ModularForm ⊤ k))
  simp at *
  have h2 := this.isBigOWith
  obtain ⟨C, hC⟩ := h2
  rw [IsBigO]; use C
  rw [isBigOWith_iff, eventually_iff] at hC ⊢
  rw [atIInf'_mem] at hC ; rw [UpperHalfPlane.atImInfty_mem]
  obtain ⟨A, hC⟩ := hC; use A + 1; intro z hz; specialize hC z
  have h : A < im z := by
    simp at *
    rw [UpperHalfPlane.im] at hz
    norm_cast at *
    simp at *
    linarith;
  simp at hC
  rw [extendByZero_eq_of_mem] at hC ;
  swap; exact z.2
  have : ((1 : ℝPos) : ℝ) = (1 : ℝ) := by rfl
  simp  [Subtype.coe_eta, div_one] at hC ;
  have HC := hC h
  simp
  exact HC

end Modforms
