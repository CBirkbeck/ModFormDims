import ModFormDims.QExpansion
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.Identities

/-!
# q-expansions of modular forms
-/

open ModularForm Complex Filter Asymptotics UpperHalfPlane

open scoped Real Topology Manifold Filter ComplexConjugate SlashInvariantForm

noncomputable section

/-!
## Extending functions from `ℍ` to `ℂ`
-/
namespace UpperHalfPlane

@[simp] lemma coe_mk_subtype (z : ℂ) (hz : 0 < z.im) :
    UpperHalfPlane.coe ⟨z, hz⟩ = z := by
  rfl

lemma ofComplex_apply' {z : ℂ} (hz : 0 < z.im) :
    ofComplex z = ⟨z, hz⟩ :=
  by simpa only [coe_mk_subtype] using ofComplex_apply ⟨z, hz⟩

lemma eventuallyEq_coe_comp_ofComplex (z : ℂ) (hz : 0 < z.im) :
    UpperHalfPlane.coe ∘ ofComplex =ᶠ[𝓝 z] id := by
  refine eventually_of_mem
    ((Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds hz) (fun x hx ↦ ?_)
  simp only [Function.comp_apply, ofComplex_apply' hx, id_eq, coe_mk_subtype]

lemma tendsto_atIInf'_ofComplex :
    Tendsto ofComplex atIInf' atImInfty := by
  intro U hU
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hU
  simp only [Filter.mem_map, atIInf'_mem, Set.mem_preimage]
  refine ⟨max 0 A, fun z hz ↦ hA _ ?_⟩
  simpa only [ofComplex_apply' <| (le_max_left _ _).trans_lt hz] using
    (le_max_right _ _).trans hz.le

lemma tendsto_val_atImInfty :
    Tendsto UpperHalfPlane.coe atImInfty atIInf' := by
  intro U hU
  obtain ⟨A, hA⟩ := atIInf'_mem.mp hU
  simp only [Filter.mem_map, atImInfty_mem, Set.mem_preimage]
  refine ⟨A + 1, fun z hz ↦ hA _ ?_⟩
  simp only [coe_im]
  linarith

lemma im_pos_mem_atIInf' : {z | 0 < z.im} ∈ atIInf' := atIInf'_mem.mpr ⟨0, fun _ ↦ by tauto⟩

lemma mdifferentiableAt_ofComplex (z : ℂ) (hz : 0 < z.im) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ofComplex z := by
  rw [mdifferentiableAt_iff]
  constructor
  · rw [ContinuousAt, nhds_induced, tendsto_comap_iff]
    refine Tendsto.congr' (eventuallyEq_coe_comp_ofComplex z hz).symm ?_
    simpa only [UpperHalfPlane.ofComplex_apply' hz, Subtype.coe_mk] using tendsto_id
  · simp only [writtenInExtChartAt, extChartAt, PartialHomeomorph.extend,
      OpenEmbedding.toPartialHomeomorph_source, PartialHomeomorph.singletonChartedSpace_chartAt_eq,
      modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, PartialHomeomorph.toFun_eq_coe,
      OpenEmbedding.toPartialHomeomorph_apply, PartialHomeomorph.refl_partialEquiv,
      PartialEquiv.refl_source, PartialEquiv.refl_symm, PartialEquiv.refl_coe, CompTriple.comp_eq,
      modelWithCornersSelf_coe, Set.range_id, id_eq, differentiableWithinAt_univ]
    exact differentiableAt_id.congr_of_eventuallyEq (eventuallyEq_coe_comp_ofComplex z hz)

end UpperHalfPlane

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R


section ModformEquivs

variable {k : ℤ}

theorem modform_bounded_atIInf'
    {Γ : Subgroup SL(2, ℤ)} {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) :
    BoundedAtFilter atIInf' (f ∘ ofComplex) := by
  simpa only [SlashAction.slash_one, ModularForm.toSlashInvariantForm_coe]
    using IsBigO.comp_tendsto (ModularFormClass.bdd_at_infty f 1) tendsto_atIInf'_ofComplex

theorem cuspform_zero_atIInf' {Γ : Subgroup SL(2, ℤ)} {F : Type*} [FunLike F ℍ ℂ]
    [CuspFormClass F Γ k] (f : F) : ZeroAtFilter atIInf' (f ∘ ofComplex) := by
  simpa only [SlashAction.slash_one, CuspForm.toSlashInvariantForm_coe]
    using (CuspFormClass.zero_at_infty f 1).comp tendsto_atIInf'_ofComplex

theorem modform_periodic {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F (CongruenceSubgroup.Gamma 1) k] (f : F) (w : ℂ) :
    (f ∘ ofComplex) (w + 1) = (f ∘ ofComplex) w := by
  by_cases hw : 0 < im w
  · have : 0 < im (w + 1) := by simp only [add_im, one_im, add_zero, hw]
    simp only [Function.comp_apply, ofComplex_apply' hw, ofComplex_apply' this]
    convert SlashInvariantForm.vAdd_width_periodic 1 k 1 f ⟨w, hw⟩ using 2
    simp only [Nat.cast_one, Int.cast_one, mul_one, UpperHalfPlane.ext_iff, coe_mk_subtype,
      coe_vadd, ofReal_one, add_comm]
  · have : ¬0 < im (w + 1) := by simp only [add_im, one_im, add_zero, hw, not_false_eq_true]
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos (not_lt.mp hw),
      ofComplex_apply_of_im_nonpos (not_lt.mp this)]

theorem modform_hol {Γ : Subgroup SL(2, ℤ)} {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k]
    (f : F) (z : ℂ) (hz : 0 < im z) :
    DifferentiableAt ℂ (f ∘ ofComplex) z := by
  rw [← mdifferentiableAt_iff_differentiableAt]
  exact (ModularFormClass.holo f _).comp z (mdifferentiableAt_ofComplex z hz)

theorem modform_hol_infty
    {Γ : Subgroup SL(2, ℤ)} {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) :
    ∀ᶠ z : ℂ in atIInf', DifferentiableAt ℂ (f ∘ ofComplex) z :=
  eventually_of_mem im_pos_mem_atIInf' (modform_hol f)

end ModformEquivs

section Modforms

theorem z_in_H {q : ℂ} (hq : Complex.abs q < 1) (hq_ne : q ≠ 0) : 0 < im (Z 1 q) := by
  rw [im_z_eq 1 q]
  apply mul_pos_of_neg_of_neg
  · exact div_neg_of_neg_of_pos (neg_lt_zero.mpr zero_lt_one) Real.two_pi_pos
  rw [Real.log_neg_iff]
  · exact hq
  · apply AbsoluteValue.pos
    exact hq_ne

def cuspFcnH (f : ℍ → ℂ) : ℂ → ℂ := cuspFcn 1 (f ∘ ofComplex)

variable {k : ℤ}

abbrev Γ := CongruenceSubgroup.Gamma 1

theorem eq_cuspFcnH {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) (z : ℍ) :
    f z = cuspFcnH f (Q 1 z) := by
  convert eq_cuspFcn one_ne_zero (modform_periodic f) z
  simp only [Function.comp_apply, ofComplex_apply]

theorem cusp_fcn_diff {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F)
    {q : ℂ} (hq : Complex.abs q < 1) :
    DifferentiableAt ℂ (cuspFcnH f) q := by
  rcases eq_or_ne q 0 with rfl | hq'
  · exact F_diff_at_zero zero_lt_one (modform_bounded_atIInf' f)
      (modform_hol_infty f) (modform_periodic f)
  · exact QZ_eq_id one_ne_zero q hq' ▸ (cuspFcn_diff_at _ one_ne_zero _
      (modform_hol f _ <| z_in_H hq hq') (modform_periodic f))

theorem cusp_fcn_vanish {F : Type*} [FunLike F ℍ ℂ] [CuspFormClass F Γ k] (f : F) :
    cuspFcnH f 0 = 0 :=
  cuspFcn_zero_of_zero_at_inf zero_lt_one (cuspform_zero_atIInf' f)

theorem exp_decay_of_cuspform {F : Type*} [FunLike F ℍ ℂ] [CuspFormClass F Γ k] (f : F) :
    IsBigO atImInfty f fun z : ℍ ↦ Real.exp (-2 * π * z.im) := by
  have := exp_decay_of_zero_at_inf zero_lt_one
    (cuspform_zero_atIInf' f) (modform_hol_infty f) (modform_periodic f)
  simp only [div_one] at this
  convert this.comp_tendsto tendsto_val_atImInfty using 1
  ext τ
  simp only [Function.comp_apply, ofComplex_apply]

end Modforms
