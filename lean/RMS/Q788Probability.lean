/-
# Q788 — Stage 1: the arbitrary-`n` probabilistic interface

This module extends `RequestProject.Q788` (whose declarations are left untouched) with the
common interface used by all the general-`n` results:

* analytic facts about the chord product `chordProd θ t = ∏_j |e^{it} - e^{iθ_j}|`
  (continuity, joint continuity, periodicity, reduction of the supremum to one period,
  attainment of the supremum), so that the already defined `Q788.chordMax` — an uncountable
  `iSup` — can be used as a genuine random variable;
* the uniform angle law `angleLaw` on one period and its `n`-fold product `angleLawN n`
  on `Fin n → ℝ`, which is the law of the angles of `n` independent Haar-uniform points of
  the unit circle;
* the real valued probabilities `probLT n α = ℙ(Dₙ < α)` and `probGE n α = ℙ(Dₙ ≥ α)`;
* the compatibility of `angleLawN 2` with the measure `Q788.unifAngles` used in the
  first-run exact two-point computation.
-/
import RMS.Q788

open Real Complex MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Q788

/-! ## The chord product as a function of the free point -/

/-- `chordProd θ t = ∏_j ‖e^{it} - e^{iθ_j}‖` is the product of the distances from the point
`e^{it}` of the unit circle to the configuration points. -/
noncomputable def chordProd {n : ℕ} (θ : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∏ j, ‖Complex.exp ((t : ℂ) * Complex.I) - Complex.exp ((θ j : ℂ) * Complex.I)‖

theorem chordMax_eq_iSup {n : ℕ} (θ : Fin n → ℝ) : chordMax θ = ⨆ t : ℝ, chordProd θ t := rfl

theorem chordProd_nonneg {n : ℕ} (θ : Fin n → ℝ) (t : ℝ) : 0 ≤ chordProd θ t :=
  Finset.prod_nonneg fun _ _ => norm_nonneg _

theorem continuous_chordProd_uncurry {n : ℕ} :
    Continuous (Function.uncurry (chordProd : (Fin n → ℝ) → ℝ → ℝ)) := by
  unfold chordProd Function.uncurry; fun_prop

theorem continuous_chordProd {n : ℕ} (θ : Fin n → ℝ) : Continuous (chordProd θ) :=
  continuous_chordProd_uncurry.comp (continuous_const.prodMk continuous_id)

/-- The chord product is `2π`-periodic in the free point. -/
theorem chordProd_periodic {n : ℕ} (θ : Fin n → ℝ) :
    Function.Periodic (chordProd θ) (2 * π) := by
  intro t
  unfold chordProd
  congr 1
  push_cast
  rw [add_mul, Complex.exp_add,
    show ((2 : ℂ) * (π : ℝ)) * Complex.I = 2 * (π : ℝ) * Complex.I by ring]
  simp [Complex.exp_two_pi_mul_I]

/-- One period already carries all the values of the chord product. -/
theorem chordProd_image_Icc {n : ℕ} (θ : Fin n → ℝ) :
    chordProd θ '' (Set.Icc 0 (2 * π)) = Set.range (chordProd θ) := by
  refine Subset.antisymm (Set.image_subset_range _ _) ?_
  rw [← (chordProd_periodic θ).image_Ioc Real.two_pi_pos 0]
  exact Set.image_mono (by rw [zero_add]; exact Set.Ioc_subset_Icc_self)

/-- The supremum defining `Dₙ` may be computed on the compact period `[0, 2π]`. -/
theorem chordMax_eq_sSup_image {n : ℕ} (θ : Fin n → ℝ) :
    chordMax θ = sSup (chordProd θ '' Set.Icc 0 (2 * π)) := by
  rw [chordMax_eq_iSup, iSup, chordProd_image_Icc]

/-- `θ ↦ Dₙ(θ)` is continuous. -/
theorem continuous_chordMax {n : ℕ} : Continuous fun θ : Fin n → ℝ => chordMax θ := by
  have h : Continuous fun θ : Fin n → ℝ => sSup (chordProd θ '' Set.Icc 0 (2 * π)) :=
    IsCompact.continuous_sSup (f := fun (θ : Fin n → ℝ) (t : ℝ) => chordProd θ t)
      (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)) continuous_chordProd_uncurry
  simpa only [← chordMax_eq_sSup_image] using h

/-- `θ ↦ Dₙ(θ)` is Borel measurable, hence a genuine random variable. -/
theorem measurable_chordMax {n : ℕ} : Measurable fun θ : Fin n → ℝ => chordMax θ :=
  continuous_chordMax.measurable

theorem chordProd_le_chordMax {n : ℕ} (θ : Fin n → ℝ) (t : ℝ) : chordProd θ t ≤ chordMax θ :=
  le_ciSup (bddAbove_chordProd θ) t

/-- **The maximum is attained**: for every configuration there is a point of the circle
realizing `Dₙ`. -/
theorem isGreatest_chordProd {n : ℕ} (θ : Fin n → ℝ) :
    IsGreatest (Set.range (chordProd θ)) (chordMax θ) := by
  obtain ⟨t, ht, hmax⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_isMaxOn
      (Set.nonempty_Icc.2 (by positivity)) (continuous_chordProd θ).continuousOn
  have hle : ∀ s : ℝ, chordProd θ s ≤ chordProd θ t := by
    intro s
    have : chordProd θ s ∈ chordProd θ '' Set.Icc 0 (2 * π) := by
      rw [chordProd_image_Icc]; exact ⟨s, rfl⟩
    obtain ⟨u, hu, hus⟩ := this
    exact hus ▸ hmax hu
  have : chordMax θ = chordProd θ t :=
    le_antisymm (ciSup_le hle) (chordProd_le_chordMax θ t)
  exact ⟨⟨t, this.symm⟩, by rintro y ⟨s, rfl⟩; rw [this]; exact hle s⟩

/-- The maximizing point of the circle. -/
theorem exists_chordProd_eq_chordMax {n : ℕ} (θ : Fin n → ℝ) :
    ∃ t : ℝ, chordProd θ t = chordMax θ := by
  obtain ⟨⟨t, ht⟩, -⟩ := isGreatest_chordProd θ
  exact ⟨t, ht⟩

/-! ## Symmetries -/

theorem chordProd_add_const {n : ℕ} (θ : Fin n → ℝ) (c t : ℝ) :
    chordProd (fun j => θ j + c) (t + c) = chordProd θ t := by
  unfold chordProd
  refine Finset.prod_congr rfl fun j _ => ?_
  have h : ∀ a : ℝ, Complex.exp (((a + c : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((a : ℂ) * Complex.I) * Complex.exp ((c : ℂ) * Complex.I) := by
    intro a; push_cast; rw [← Complex.exp_add]; ring_nf
  rw [h t, h (θ j), ← sub_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- `Dₙ` is invariant under a common rotation of all the points. -/
theorem chordMax_add_const {n : ℕ} (θ : Fin n → ℝ) (c : ℝ) :
    chordMax (fun j => θ j + c) = chordMax θ := by
  have hrange : Set.range (chordProd fun j => θ j + c) = Set.range (chordProd θ) := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t - c, by rw [← chordProd_add_const θ c (t - c)]; ring_nf⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t + c, chordProd_add_const θ c t⟩
  rw [chordMax_eq_iSup, chordMax_eq_iSup, iSup, iSup, hrange]

/-- `Dₙ` is invariant under relabelling of the points. -/
theorem chordMax_comp_equiv {n : ℕ} (θ : Fin n → ℝ) (e : Equiv.Perm (Fin n)) :
    chordMax (θ ∘ e) = chordMax θ := by
  have h : ∀ t, chordProd (θ ∘ e) t = chordProd θ t := by
    intro t
    unfold chordProd
    exact Fintype.prod_equiv e _ _ fun j => rfl
  rw [chordMax_eq_iSup, chordMax_eq_iSup]
  exact iSup_congr h

/-! ## The uniform angle law and its finite products -/

/-- The uniform probability measure on one period `[0, 2π)`: the law of the angle of a
Haar-uniform random point of the unit circle. -/
noncomputable def angleLaw : Measure ℝ :=
  (ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Set.Ico 0 (2 * π))

instance : IsProbabilityMeasure angleLaw := by
  constructor
  have hpi := Real.pi_pos
  rw [angleLaw, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ico, sub_zero,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simp [ENNReal.ofReal_eq_zero]; positivity)
    ENNReal.ofReal_ne_top

instance : IsFiniteMeasure angleLaw := inferInstance

/-- The endpoints of the period are null, so the `[0,2π)` and `(0,2π]` conventions agree. -/
theorem angleLaw_eq_Ioc :
    angleLaw = (ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Set.Ioc 0 (2 * π)) := by
  have h : volume.restrict (Set.Ico 0 (2 * π)) = volume.restrict (Set.Ioc 0 (2 * π)) := by
    refine Measure.restrict_congr_set ?_
    have h1 : (Set.Ico (0:ℝ) (2 * π)) =ᵐ[volume] Set.Ioo 0 (2 * π) := Ioo_ae_eq_Ico.symm
    have h2 : (Set.Ioo (0:ℝ) (2 * π)) =ᵐ[volume] Set.Ioc 0 (2 * π) := Ioo_ae_eq_Ioc
    exact h1.trans h2
  rw [angleLaw, h]

/-- The law of the `n` angles of `n` independent Haar-uniform points of the unit circle. -/
noncomputable def angleLawN (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ => angleLaw

instance (n : ℕ) : IsProbabilityMeasure (angleLawN n) := by
  unfold angleLawN; infer_instance

/-- Explicit description of the `n`-fold product law as a normalized restriction of the
Lebesgue measure of `Fin n → ℝ` to the box `[0,2π)ⁿ`. -/
theorem angleLawN_eq (n : ℕ) :
    angleLawN n = ((ENNReal.ofReal (2 * π))⁻¹) ^ n •
      volume.restrict (Set.univ.pi fun _ : Fin n => Set.Ico 0 (2 * π)) := by
  rw [angleLawN]
  refine Measure.pi_eq (μ := fun _ : Fin n => angleLaw) ?_
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs), smul_eq_mul,
    ← Set.pi_inter_distrib, volume_pi_pi,
    show ((ENNReal.ofReal (2 * π))⁻¹) ^ n = ∏ _i : Fin n, (ENNReal.ofReal (2 * π))⁻¹ by simp,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [angleLaw, Measure.smul_apply, Measure.restrict_apply (hs i), smul_eq_mul]

/-- The model is absolutely continuous with respect to Lebesgue measure. -/
theorem angleLawN_absolutelyContinuous (n : ℕ) :
    angleLawN n ≪ (volume : Measure (Fin n → ℝ)) := by
  rw [angleLawN_eq]
  refine Measure.AbsolutelyContinuous.mk fun t ht h0 => ?_
  have h : (volume : Measure (Fin n → ℝ)).restrict
      (Set.univ.pi fun _ : Fin n => Set.Ico 0 (2 * π)) t = 0 := by
    rw [Measure.restrict_apply ht]
    exact measure_mono_null Set.inter_subset_left h0
  simp [h]

instance : NoAtoms angleLaw := by
  constructor
  intro a
  rw [angleLaw, Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton a),
    smul_eq_mul, measure_mono_null (Set.inter_subset_left (t := Set.Ico (0:ℝ) (2 * π)))
      (by simp : volume ({a} : Set ℝ) = 0), mul_zero]

/-! ## The events and their probabilities -/

theorem measurableSet_chordMax_lt {n : ℕ} (α : ℝ) :
    MeasurableSet {θ : Fin n → ℝ | chordMax θ < α} :=
  measurableSet_lt measurable_chordMax measurable_const

theorem measurableSet_chordMax_ge {n : ℕ} (α : ℝ) :
    MeasurableSet {θ : Fin n → ℝ | α ≤ chordMax θ} :=
  measurableSet_le measurable_const measurable_chordMax

theorem measurableSet_chordMax_eq {n : ℕ} (α : ℝ) :
    MeasurableSet {θ : Fin n → ℝ | chordMax θ = α} :=
  measurableSet_eq_fun measurable_chordMax measurable_const

/-- `ℙ(Dₙ < α)`. -/
noncomputable def probLT (n : ℕ) (α : ℝ) : ℝ :=
  ENNReal.toReal (angleLawN n {θ | chordMax θ < α})

/-- `ℙ(Dₙ ≥ α)`. -/
noncomputable def probGE (n : ℕ) (α : ℝ) : ℝ :=
  ENNReal.toReal (angleLawN n {θ | α ≤ chordMax θ})

theorem probLT_nonneg (n : ℕ) (α : ℝ) : 0 ≤ probLT n α := ENNReal.toReal_nonneg
theorem probGE_nonneg (n : ℕ) (α : ℝ) : 0 ≤ probGE n α := ENNReal.toReal_nonneg

theorem probLT_le_one (n : ℕ) (α : ℝ) : probLT n α ≤ 1 := by
  have h : angleLawN n {θ : Fin n → ℝ | chordMax θ < α} ≤ 1 := prob_le_one
  calc probLT n α ≤ ENNReal.toReal 1 := ENNReal.toReal_mono ENNReal.one_ne_top h
    _ = 1 := ENNReal.toReal_one

theorem probGE_le_one (n : ℕ) (α : ℝ) : probGE n α ≤ 1 := by
  have h : angleLawN n {θ : Fin n → ℝ | α ≤ chordMax θ} ≤ 1 := prob_le_one
  calc probGE n α ≤ ENNReal.toReal 1 := ENNReal.toReal_mono ENNReal.one_ne_top h
    _ = 1 := ENNReal.toReal_one

/-- The two probabilities are complementary. -/
theorem probGE_eq_one_sub_probLT (n : ℕ) (α : ℝ) : probGE n α = 1 - probLT n α := by
  have hcompl : {θ : Fin n → ℝ | α ≤ chordMax θ} = {θ : Fin n → ℝ | chordMax θ < α}ᶜ := by
    ext θ; simp [not_lt]
  rw [probGE, probLT, hcompl,
    measure_compl (measurableSet_chordMax_lt α) (measure_ne_top _ _), measure_univ]
  rw [ENNReal.toReal_sub_of_le
    (show angleLawN n {θ : Fin n → ℝ | chordMax θ < α} ≤ 1 from prob_le_one) (by simp)]
  simp

/-- **The trivial regime of part (a)**: for `α ≤ 2` the event `Dₙ ≥ α` is sure, for every
`n ≥ 1` (in particular for every `n ≥ 2`). -/
theorem probGE_of_le_two {n : ℕ} (hn : 0 < n) (α : ℝ) (hα : α ≤ 2) : probGE n α = 1 := by
  have huniv : {θ : Fin n → ℝ | α ≤ chordMax θ} = Set.univ := by
    ext θ; simpa using hα.trans (two_le_chordMax hn θ)
  rw [probGE, huniv, measure_univ, ENNReal.toReal_one]

theorem probLT_of_le_two {n : ℕ} (hn : 0 < n) (α : ℝ) (hα : α ≤ 2) : probLT n α = 0 := by
  have := probGE_eq_one_sub_probLT n α
  rw [probGE_of_le_two hn α hα] at this
  linarith

/-! ## Compatibility with the two-point measure of the first run -/

theorem angleLaw_prod_angleLaw : angleLaw.prod angleLaw = unifAngles := by
  have hpi := Real.pi_pos
  rw [angleLaw, unifAngles, Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.prod_restrict, ← Measure.volume_eq_prod, smul_smul]
  have hne0 : ENNReal.ofReal (2 * π) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hnetop : ENNReal.ofReal (2 * π) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h2 : ENNReal.ofReal (4 * π ^ 2) = ENNReal.ofReal (2 * π) * ENNReal.ofReal (2 * π) := by
    rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  congr 1
  rw [h2, ENNReal.mul_inv (Or.inl hne0) (Or.inl hnetop)]

/-- The general model at `n = 2` is exactly the measure `unifAngles` used in the first-run
exact computation of the law of `D₂`. -/
theorem map_angleLawN_two :
    Measure.map (fun f : Fin 2 → ℝ => (f 0, f 1)) (angleLawN 2) = unifAngles := by
  have h := measurePreserving_piFinTwo (fun _ : Fin 2 => angleLaw)
  have : Measure.map (⇑(MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℝ)) (angleLawN 2)
      = angleLaw.prod angleLaw := h.map_eq
  rw [← angleLaw_prod_angleLaw, ← this]
  rfl

theorem matrix_eta_two (f : Fin 2 → ℝ) : ![f 0, f 1] = f := by
  funext i; fin_cases i <;> simp

/-- The general-`n` probability specializes at `n = 2` to the exact two-point law already
proved in `RequestProject.Q788`. -/
theorem probGE_two_eq (α : ℝ) :
    probGE 2 α = ENNReal.toReal (unifAngles {p : ℝ × ℝ | α ≤ chordMax ![p.1, p.2]}) := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | α ≤ chordMax ![p.1, p.2]} := by
    apply measurableSet_le measurable_const
    exact measurable_chordMax.comp
      (measurable_pi_lambda _ fun i => by fin_cases i <;> simp <;> fun_prop)
  have hpre : (fun f : Fin 2 → ℝ => (f 0, f 1)) ⁻¹' {p : ℝ × ℝ | α ≤ chordMax ![p.1, p.2]}
      = {θ : Fin 2 → ℝ | α ≤ chordMax θ} := by
    ext f; simp [matrix_eta_two f]
  rw [probGE, ← hpre, ← Measure.map_apply (by fun_prop) hmeas, map_angleLawN_two]

/-- **The exact law of `D₂` in the general interface**: `ℙ(D₂ ≥ α) = (4/π) arccos(√α/2)`
for `2 ≤ α ≤ 4`. -/
theorem probGE_two (α : ℝ) (h2 : 2 ≤ α) (h4 : α ≤ 4) :
    probGE 2 α = 4 / π * Real.arccos (Real.sqrt α / 2) := by
  have harc : 0 ≤ Real.arccos (Real.sqrt α / 2) := Real.arccos_nonneg _
  have hpi := Real.pi_pos
  rw [probGE_two_eq, prob_chordMax_two_ge α h2 h4,
    ENNReal.toReal_ofReal (by positivity)]

end Q788
