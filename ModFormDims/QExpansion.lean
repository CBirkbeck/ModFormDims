import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

/-!
# q-expansions of periodic functions

We show that if `f : ℂ → ℂ` satisfies `f (z + h) = f z`, for some nonzero real `h`, then
there is a well-defined `F` such that `f z = F (exp (2 * π * I * z / h))` for all `z`;
and if `f` is holomorphic at some `z`, then `F` is holomorphic at `q = exp (2 * π * I * z / h)`.

We also show (using Riemann's removable singularity theorem) that if `f` is holomorphic and bounded
for all sufficiently large `im z`, then `F` extends to a holomorphic function on a neighbourhood of
`0`. As a consequence, if `f` tends to zero as `im z → ∞`, then in fact it decays *exponentially*
to zero.
-/

open Complex Filter Asymptotics

open scoped Real Topology

noncomputable section

/-- Function-theoretic lemma, maybe move this elsewhere? -/
theorem bound_holo_fcn (g : ℂ → ℂ) (hg : DifferentiableAt ℂ g 0) (hg' : g 0 = 0) :
    IsBigO (𝓝 0) g id := by
  simpa only [hg', sub_zero] using hg.hasDerivAt.isBigO_sub

section QAndZ

theorem log_exp' (z : ℂ) :
    ∃ n : ℤ, log (exp z) = z + n * (2 * π * Complex.I) := by
  rw [← exp_eq_exp_iff_exists_int, exp_log]
  exact exp_ne_zero z

variable (h : ℝ)

def Q (z : ℂ) : ℂ := exp (2 * π * Complex.I * z / h)

def Z (q : ℂ) : ℂ :=
  h / (2 * π * Complex.I) * log q

theorem abs_q_eq (z : ℂ) :
    abs (Q h z) = Real.exp (-2 * π * im z / h) := by
  dsimp only [Q]
  rw [abs_exp]
  congr
  have : (↑h)⁻¹ = (↑(h : ℝ)⁻¹ : ℂ) := by
    simp
  rw [div_eq_mul_inv, mul_comm, this, re_ofReal_mul]
  have : 2 * ↑π * Complex.I * z = ↑(2 * π) * z * Complex.I := by
    simp
    ring
  simp only [this, mul_I_re, im_ofReal_mul, div_eq_inv_mul, neg_mul]

theorem im_z_eq (q : ℂ) : im (Z h q) = -h / (2 * π) * Real.log (abs q) := by
  dsimp only [Z]
  have : ↑h / (2 * (π :ℂ) * Complex.I) * log q = -↑h / (2 * ↑π) * log q * Complex.I := by
    field_simp [ofReal_ne_zero.mpr Real.pi_pos.ne', two_pi_I_ne_zero]
    ring_nf
    simp
  rw [this, mul_I_im]
  have : -↑h / (2 * ↑π) * log q = ↑(-↑h / (2 * π)) * log q := by
    simp only [ofReal_div, ofReal_neg, ofReal_mul, ofReal_ofNat]
  rw [this, re_ofReal_mul, log_re]

variable {h} -- next few theorems all assume h ≠ 0 or 0 < h

theorem QZ_eq_id (hh : h ≠ 0) (e : ℂ) (hq : e ≠ 0) :
    Q h (Z h e) = e := by
  suffices 2 * ↑π * Complex.I * (↑h / (2 * ↑π * Complex.I) * log e) / ↑h = log e by
    simpa only [Q, Z, this] using exp_log hq
  have : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh
  field_simp [two_pi_I_ne_zero, this]

theorem ZQ_eq_mod_period (hh : h ≠ 0) (s : ℂ) : ∃ m : ℤ, Z h (Q h s) = s + m * h := by
  dsimp only [Q, Z]
  have t := log_exp' (2 * ↑π * Complex.I * s / ↑h)
  cases' t with m t
  use m
  rw [t]
  have : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh
  field_simp [two_pi_I_ne_zero]; ring

theorem abs_q_lt_iff (hh : 0 < h) (A : ℝ) (z : ℂ) :
    abs (Q h z) < Real.exp (-2 * π * A / h) ↔ A < im z := by
  rw [abs_q_eq, Real.exp_lt_exp]
  constructor
  · intro hz
    rw [div_lt_div_right hh] at hz
    have : -2 * π < 0 := by simpa using Real.pi_pos
    rwa [mul_lt_mul_left_of_neg this] at hz
  · intro hz
    rw [div_lt_div_right hh]
    have : -2 * π < 0 := by simpa using Real.pi_pos
    rwa [mul_lt_mul_left_of_neg this]

-- Filter stuff
def atIInf' : Filter ℂ := atTop.comap im

theorem atIInf'_mem {S : Set ℂ} :
    S ∈ atIInf' ↔ ∃ A : ℝ, ∀ z : ℂ, A < im z → z ∈ S := by
  simp only [atIInf', mem_comap', Filter.mem_atTop_sets, ge_iff_le, Set.mem_setOf_eq]
  constructor
  · exact fun ⟨a, h⟩ ↦ ⟨a, fun z hz ↦ h _ hz.le rfl⟩
  · exact fun ⟨A, h⟩ ↦ ⟨A + 1, fun b hb x hx ↦ h x (by linarith)⟩

theorem z_tendsto (hh : 0 < h) :
    Tendsto (Z h) (𝓝[{0}ᶜ] 0) atIInf' := by
  rw [Tendsto, map_le_iff_le_comap, comap]
  intro S h
  simp_rw [atIInf'_mem] at h
  obtain ⟨T, ⟨A, hA⟩, hT⟩ := h
  simp_rw [Metric.mem_nhdsWithin_iff, Metric.ball, dist_eq, sub_zero]
  use Real.exp (-2 * π * A / h)
  constructor
  apply Real.exp_pos
  intro q
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
  rintro ⟨u1, u2⟩
  rw [← QZ_eq_id hh.ne' _ u2] at u1
  have := abs_q_lt_iff hh A (Z h q)
  rw [this] at u1
  exact hT (hA (Z h q) u1)

theorem q_tendsto (hh : 0 < h) : Tendsto (Q h) atIInf' (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_eq_abs, abs_q_eq]
  have : Set.range Complex.im ∈ atTop := by
    suffices Set.range Complex.im = ⊤ by
      rw [this]
      apply univ_mem
    ext1 x
    simp only [Set.mem_range, Set.top_eq_univ, Set.mem_univ, iff_true]
    use Complex.I * x
    simp
  have := (@tendsto_comap'_iff ℝ ℝ ℂ (fun y ↦ Real.exp (-2 * π * y / ↑h)) atTop (𝓝 0) im this).mpr
  apply this; refine' Real.tendsto_exp_atBot.comp _
  apply Filter.Tendsto.atBot_div_const hh
  apply Filter.Tendsto.const_mul_atTop_of_neg
  · simpa using Real.pi_pos
  apply tendsto_id

end QAndZ

section PeriodicOnC

variable (h : ℝ) (f : ℂ → ℂ)

def cuspFcn0 : ℂ → ℂ := fun q ↦ f (Z h q)

def cuspFcn : ℂ → ℂ :=
  Function.update (cuspFcn0 h f) 0 (limUnder (𝓝[≠] (0 : ℂ)) (cuspFcn0 h f))

theorem cuspFcn_eq_of_nonzero (q : ℂ) (hq : q ≠ 0) :
    cuspFcn h f q = cuspFcn0 h f q :=
  Function.update_noteq hq ..

theorem update_twice :
    cuspFcn h f = Function.update (cuspFcn h f) 0 (limUnder (𝓝[≠] (0 : ℂ)) (cuspFcn h f)) := by
  ext1 q
  rw [Function.update]
  split_ifs
  · rw [cuspFcn, Function.update]
    split_ifs
    rw [limUnder, limUnder]
    simp only [eq_rec_constant]
    congr 1
    apply Filter.map_congr; apply eventuallyEq_nhdsWithin_of_eqOn
    intro r hr; simp at hr
    rw [Function.update]; split_ifs; rfl
  · rfl

variable {f h}

private theorem is_periodic_aux (hf : ∀ w : ℂ, f (w + h) = f w) (z : ℂ) (m : ℕ) :
    f (z + m * h) = f z := by
  induction' m with m hm generalizing z
  · simp
  rw [Nat.cast_add, Nat.cast_one, add_mul, ← add_assoc, one_mul]
  rw [hf (z + m * h)]; exact hm z

theorem is_periodic (hf : ∀ w : ℂ, f (w + h) = f w) (z : ℂ) (m : ℤ) :
    f (z + m * h) = f z := by
  cases' m with m m
  · apply is_periodic_aux
    apply hf
  simp only [neg_add_rev, Int.cast_negSucc]
  norm_cast at *
  simp at *
  have := (is_periodic_aux hf (z - (m + 1) * h) (m + 1) ).symm
  norm_cast at *
  simp at *
  rw [← this]
  apply congr_arg
  ring

theorem eq_cuspFcn (hh : h ≠ 0) (hf : ∀ w : ℂ, f (w + h) = f w) (z : ℂ) :
    f z = (cuspFcn h f) (Q h z) := by
  have : (cuspFcn h f) (Q h z) = (cuspFcn0 h f) (Q h z) := by
    rw [cuspFcn]; rw [Function.update]; split_ifs
    · exfalso; have : Q h z ≠ 0 := by apply exp_ne_zero
      norm_cast at *
    · rfl
  rw [this]
  dsimp only [cuspFcn0]
  obtain ⟨m, hm⟩ := ZQ_eq_mod_period hh z
  rw [hm]; exact (is_periodic hf z m).symm

end PeriodicOnC

section HoloOnC

variable {h : ℝ} (f : ℂ → ℂ) (hf : ∀ w : ℂ, f (w + h) = f w)

theorem cuspFcn_diff_at (hh : h ≠ 0)
    (z : ℂ) (hol_z : DifferentiableAt ℂ f z) (hf : ∀ w : ℂ, f (w + h) = f w) :
    DifferentiableAt ℂ (cuspFcn h f) (Q h z) := by
  let q := Q h z
  have qdiff : HasStrictDerivAt (Q h) (q * (2 * π * Complex.I / h) ) z := by
    apply HasStrictDerivAt.cexp
    apply HasStrictDerivAt.div_const
    have := HasStrictDerivAt.const_mul  (2 * π * Complex.I) (hasStrictDerivAt_id z)
    simp at *
    apply this
  -- Now show that the q-map has a differentiable local inverse at z, say L : ℂ → ℂ, with L(q) = z.
  have diff_ne : q * (2 * π * Complex.I / h) ≠ 0 := by
    apply mul_ne_zero
    · apply exp_ne_zero
    · apply div_ne_zero
      · exact two_pi_I_ne_zero
      · simpa using hh
  let L := (qdiff.localInverse (Q h) _ z) diff_ne
  have diff_L : DifferentiableAt ℂ L q := (qdiff.to_localInverse diff_ne).differentiableAt
  have hL : Q h ∘ L =ᶠ[𝓝 q] (id : ℂ → ℂ) :=
    (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_right_inverse
  --Thus, if F = cusp_expansion f, we have F(q') = f(L(q')) for q' near q.
  --Since L is differentiable at q, and f is diffble at L(q) [ = z], we conclude
  --that F is differentiable at q.
  have hF := EventuallyEq.fun_comp hL (cuspFcn h f)
  dsimp at hF
  have : cuspFcn h f ∘ Q h ∘ L = f ∘ L := by ext1 z; exact (eq_cuspFcn hh hf (L z)).symm
  rw [this] at hF
  have : z = L q := by
    have hL2 : L ∘ Q h =ᶠ[𝓝 z] (id : ℂ → ℂ) :=
      (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_left_inverse
    replace hL2 := EventuallyEq.eq_of_nhds hL2
    rw [id_eq] at hL2
    rw [← hL2]
    simp
  rw [this] at hol_z
  exact (DifferentiableAt.comp q hol_z diff_L).congr_of_eventuallyEq hF.symm

theorem F_diff_near_zero (hh : 0 < h) (h_hol : ∀ᶠ z : ℂ in atIInf', DifferentiableAt ℂ f z)
    (hf : ∀ w : ℂ, f (w + h) = f w) :
    ∀ᶠ q : ℂ in 𝓝[≠] 0, DifferentiableAt ℂ (cuspFcn h f) q := by
  refine' ((z_tendsto hh).eventually h_hol).mp _
  apply eventually_nhdsWithin_of_forall; intro q hq h_diff
  rw [← QZ_eq_id hh.ne' _ hq]
  apply cuspFcn_diff_at _ hh.ne'
  exact h_diff
  exact hf

end HoloOnC

section HoloAtInfC

variable {h : ℝ} {f : ℂ → ℂ} (hf : ∀ w : ℂ, f (w + h) = f w)

theorem F_bound (hh : 0 < h) (h_bd : BoundedAtFilter atIInf' f) :
    BoundedAtFilter (𝓝[≠] (0 : ℂ)) (cuspFcn h f) := by
  refine IsBigO.congr' (h_bd.comp_tendsto <| z_tendsto hh) ?_ (by rfl)
  apply eventually_nhdsWithin_of_forall; intro q hq
  rw [cuspFcn_eq_of_nonzero _ _ _ hq]; rfl

theorem F_diff_at_zero (hh : 0 < h) (h_bd : BoundedAtFilter atIInf' f)
    (h_hol : ∀ᶠ z : ℂ in atIInf', DifferentiableAt ℂ f z) (hf : ∀ w : ℂ, f (w + h) = f w) :
    DifferentiableAt ℂ (cuspFcn h f) 0 := by
  obtain ⟨c, t⟩ := (F_bound hh h_bd).bound
  have T:= (F_diff_near_zero f hh h_hol hf)
  replace t := T.and t
  simp only [norm_eq_abs, Pi.one_apply, AbsoluteValue.map_one, mul_one] at t
  obtain ⟨S, hS1, hS2, hS3⟩ := eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp t)
  have h_diff : DifferentiableOn ℂ (cuspFcn h f) (S \ {0}) := by
    intro x hx; apply DifferentiableAt.differentiableWithinAt
    exact (hS1 x ((Set.mem_diff _).mp hx).1 ((Set.mem_diff _).mp hx).2).1
  have hF_bd : BddAbove (norm ∘ cuspFcn h f '' (S \ {0})) := by
    use c
    rw [mem_upperBounds]
    simp only [Function.comp_apply, norm_eq_abs, Set.mem_image, Set.mem_diff, Set.mem_singleton_iff,
      forall_exists_index, and_imp]
    intro y q hq hq2 hy
    simpa only [← hy, norm_one, mul_one] using (hS1 q hq hq2).2
  have := differentiableOn_update_limUnder_of_bddAbove (IsOpen.mem_nhds hS2 hS3) h_diff hF_bd
  rw [← update_twice] at this
  exact this.differentiableAt (IsOpen.mem_nhds hS2 hS3)

/-- If `f` is periodic, and holomorphic and bounded near `I∞`, then it tends to a limit at `I∞`,
and this limit is the value of its cusp function at 0. -/
theorem tendsto_at_I_inf (hh : 0 < h) (h_bd : BoundedAtFilter atIInf' f)
    (h_hol : ∀ᶠ z : ℂ in atIInf', DifferentiableAt ℂ f z) (hf : ∀ w : ℂ, f (w + h) = f w) :
    Tendsto f atIInf' (𝓝 <| cuspFcn h f 0) := by
  suffices Tendsto (cuspFcn h f) (𝓝[≠] 0) (𝓝 <| cuspFcn h f 0) by
    have t2 : f = cuspFcn h f ∘ Q h := by
      ext1; apply eq_cuspFcn hh.ne' hf
    conv =>
      congr
      rw [t2]
    apply Tendsto.comp; exact this
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    exact q_tendsto hh
    apply Eventually.of_forall; intro q; apply exp_ne_zero
  exact tendsto_nhdsWithin_of_tendsto_nhds
    (F_diff_at_zero hh h_bd h_hol hf).continuousAt.tendsto

theorem cuspFcn_zero_of_zero_at_inf (hh : 0 < h) (h_zer : ZeroAtFilter atIInf' f) :
    cuspFcn h f 0 = 0 := by
  rw [cuspFcn, Function.update_same]
  suffices Tendsto (cuspFcn0 h f) (𝓝[{0}ᶜ] 0) (𝓝 (0 : ℂ)) from Tendsto.limUnder_eq this
  exact h_zer.comp (z_tendsto hh)

/--
Main theorem of this file: if `f` is periodic, holomorphic near `I∞`, and tends to zero at `I∞`,
then in fact it tends to zero exponentially fast.
-/
theorem exp_decay_of_zero_at_inf (hh : 0 < h) (h_zer : ZeroAtFilter atIInf' f)
    (h_hol : ∀ᶠ z : ℂ in atIInf', DifferentiableAt ℂ f z) (hf : ∀ w : ℂ, f (w + h) = f w) :
    IsBigO atIInf' f fun z : ℂ ↦ Real.exp (-2 * π * im z / h) := by
  rw [funext (eq_cuspFcn hh.ne' hf)]
  simp only [← abs_q_eq h, ← norm_eq_abs]
  refine ((bound_holo_fcn _ ?_ ?_).comp_tendsto (q_tendsto hh)).norm_right
  · exact F_diff_at_zero hh h_zer.boundedAtFilter h_hol hf
  · exact cuspFcn_zero_of_zero_at_inf hh h_zer

end HoloAtInfC
