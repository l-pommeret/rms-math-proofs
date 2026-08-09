import RMS.Q766Decay

/-!
# Q766, Stage 1 : construction of the nondecreasing rearrangement

For a probability measure `μ` on `ℝ` we define its generalized quantile

`Q766.quantile μ u = sInf {y | u ≤ cdf μ y}`,

prove the Galois correspondence `quantile μ u ≤ y ↔ u ≤ cdf μ y` for `u ∈ (0,1)`, and deduce that
`quantile μ` pushes the Lebesgue measure of `(0,1]` forward to `μ` (inverse transform sampling).

Applied to `μ = Measure.map f ν` this produces the nondecreasing rearrangement of the printed
function `f`, with the same distribution and hence the same distortion functional.
-/

open scoped BigOperators
open MeasureTheory Set Filter Topology ProbabilityTheory

namespace Q766

/-- Lebesgue measure on the parameter interval `(0,1]`, a probability measure. -/
noncomputable def nu : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1)

instance isProbabilityMeasure_nu : IsProbabilityMeasure nu := by
  constructor
  rw [nu, Measure.restrict_apply_univ, Real.volume_Ioc]
  norm_num

section Quantile

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- The generalized quantile (inverse CDF) of a probability measure on `ℝ`. -/
noncomputable def quantile (μ : Measure ℝ) (u : ℝ) : ℝ := sInf {y : ℝ | u ≤ cdf μ y}

variable {μ}

lemma quantile_set_nonempty {u : ℝ} (hu : u < 1) : {y : ℝ | u ≤ cdf μ y}.Nonempty := by
  have h : ∀ᶠ y in atTop, u < cdf μ y :=
    Filter.Tendsto.eventually_const_lt hu (tendsto_cdf_atTop (μ := μ))
  obtain ⟨y, hy⟩ := h.exists
  exact ⟨y, hy.le⟩

lemma quantile_set_bddBelow {u : ℝ} (hu : 0 < u) : BddBelow {y : ℝ | u ≤ cdf μ y} := by
  have h : ∀ᶠ y in atBot, cdf μ y < u :=
    Filter.Tendsto.eventually_lt_const hu (tendsto_cdf_atBot (μ := μ))
  rw [eventually_atBot] at h
  obtain ⟨y₀, hy₀⟩ := h
  refine ⟨y₀, fun y hy => ?_⟩
  by_contra hcon
  push_neg at hcon
  have h1 : cdf μ y ≤ cdf μ y₀ := monotone_cdf μ hcon.le
  have h2 : cdf μ y₀ < u := hy₀ y₀ le_rfl
  exact absurd hy (not_le.2 (lt_of_le_of_lt h1 h2))

/-- The Galois correspondence characterising the quantile. -/
lemma quantile_le_iff {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (y : ℝ) :
    quantile μ u ≤ y ↔ u ≤ cdf μ y := by
  constructor
  · intro h
    -- `u ≤ cdf μ z` for every `z > y`, then use right-continuity of the CDF
    have hev : ∀ z, y < z → u ≤ cdf μ z := by
      intro z hz
      obtain ⟨w, hw, hwz⟩ := Real.lt_sInf_add_pos
        (quantile_set_nonempty (μ := μ) hu1) (ε := z - y) (by linarith)
      have hwlt : w < z := by
        have : sInf {y : ℝ | u ≤ cdf μ y} ≤ y := h
        linarith
      exact le_trans hw (monotone_cdf μ hwlt.le)
    have hcont : Tendsto (cdf μ) (𝓝[>] y) (𝓝 (cdf μ y)) :=
      ((cdf μ).right_continuous y).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    refine ge_of_tendsto hcont ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hev z hz
  · intro h
    exact csInf_le (quantile_set_bddBelow hu0) h

lemma monotoneOn_quantile : MonotoneOn (quantile μ) (Set.Ioo (0:ℝ) 1) := by
  intro u hu v hv huv
  refine csInf_le_csInf (quantile_set_bddBelow hu.1) (quantile_set_nonempty hv.2) ?_
  intro y hy
  exact le_trans huv hy

lemma aemeasurable_quantile : AEMeasurable (quantile μ) nu := by
  have hset : nu = volume.restrict (Set.Ioo (0:ℝ) 1) := by
    rw [nu]
    exact (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm
  rw [hset]
  exact aemeasurable_restrict_of_monotoneOn measurableSet_Ioo monotoneOn_quantile

/-- **Inverse transform sampling.**  The quantile of `μ` pushes the uniform measure on `(0,1]`
forward to `μ`. -/
theorem map_quantile_eq : Measure.map (quantile μ) nu = μ := by
  haveI := Measure.isProbabilityMeasure_map (aemeasurable_quantile (μ := μ))
  refine Measure.ext_of_Iic _ _ fun y => ?_
  rw [Measure.map_apply_of_aemeasurable aemeasurable_quantile measurableSet_Iic]
  set c : ℝ := cdf μ y with hc
  have hc0 : 0 ≤ c := cdf_nonneg μ y
  have hc1 : c ≤ 1 := cdf_le_one μ y
  rw [nu, Measure.restrict_apply' measurableSet_Ioc]
  set B : Set ℝ := quantile μ ⁻¹' Set.Iic y ∩ Set.Ioc 0 1 with hB
  have hAB : Set.Ioo (0:ℝ) c ⊆ B := by
    intro u hu
    refine ⟨?_, ⟨hu.1, le_trans hu.2.le hc1⟩⟩
    have hu1 : u < 1 := lt_of_lt_of_le hu.2 hc1
    exact (quantile_le_iff hu.1 hu1 y).2 (le_of_lt hu.2)
  have hBA : B ⊆ Set.Ioc (0:ℝ) c ∪ {(1:ℝ)} := by
    rintro u ⟨hq, hu01⟩
    by_cases hu1 : u = 1
    · exact Or.inr (by simp [hu1])
    · have hult : u < 1 := lt_of_le_of_ne hu01.2 hu1
      have := (quantile_le_iff hu01.1 hult y).1 hq
      exact Or.inl ⟨hu01.1, this⟩
  have hle1 : ENNReal.ofReal c ≤ volume B := by
    have := measure_mono (μ := volume) hAB
    rwa [Real.volume_Ioo, sub_zero] at this
  have hle2 : volume B ≤ ENNReal.ofReal c := by
    refine le_trans (measure_mono hBA) ?_
    refine le_trans (measure_union_le _ _) ?_
    rw [Real.volume_Ioc, sub_zero, Real.volume_singleton, add_zero]
  have : volume B = ENNReal.ofReal c := le_antisymm hle2 hle1
  rw [this, hc, ofReal_cdf]

end Quantile

section Rearrangement

/-- **Existence of the nondecreasing rearrangement.**  Every integrable function on `(0,1]` admits
a nondecreasing integrable rearrangement with the same distribution, namely the quantile of its
pushforward. -/
theorem exists_integrable_monotone_rearrangement {f : ℝ → ℝ}
    (hfint : Integrable f nu) :
    ∃ q : ℝ → ℝ,
      AEMeasurable q nu ∧
      MonotoneOn q (Set.Ioo (0 : ℝ) 1) ∧
      IntervalIntegrable q volume 0 1 ∧
      Measure.map q nu = Measure.map f nu := by
  have hfmeas : AEMeasurable f nu := hfint.aestronglyMeasurable.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map f nu) := Measure.isProbabilityMeasure_map hfmeas
  set q : ℝ → ℝ := quantile (Measure.map f nu) with hq
  have hqmeas : AEMeasurable q nu := aemeasurable_quantile
  have hmap : Measure.map q nu = Measure.map f nu := map_quantile_eq
  have hqint : Integrable q nu := by
    have h1 : Integrable (id : ℝ → ℝ) (Measure.map f nu) := by
      rw [MeasureTheory.integrable_map_measure
        (measurable_id.aestronglyMeasurable) hfmeas]
      exact hfint
    rw [← hmap, MeasureTheory.integrable_map_measure
      (measurable_id.aestronglyMeasurable) hqmeas] at h1
    exact h1
  refine ⟨q, hqmeas, monotoneOn_quantile, ?_, hmap⟩
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact hqint

/-- The functional of the printed problem equals the quantile functional of the rearrangement. -/
theorem phiF_eq_Phi_of_map_eq {n : ℕ} [Nonempty (Fin n)] {f q : ℝ → ℝ} (x : Fin n → ℝ)
    (hf : AEMeasurable f nu) (hqm : AEMeasurable q nu)
    (hmap : Measure.map q nu = Measure.map f nu) :
    phiF f x = Phi q x :=
  Phi_eq_of_map_eq x hf hqm hmap.symm

end Rearrangement

section Convexity

variable {q : ℝ → ℝ}

/-- **Convexity of the primitive.**  If `q` is nondecreasing and integrable on `(0,1)`, then
`H q = ∫₀ˢ q` is convex on `[0,1]`. -/
theorem convexOn_H (hmono : MonotoneOn q (Set.Ioo (0:ℝ) 1))
    (hint : IntervalIntegrable q volume 0 1) : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (H q) := by
  refine convexOn_of_slope_mono_adjacent (convex_Icc _ _) ?_
  intro a b c ha hc hab hbc
  have ha0 : 0 ≤ a := ha.1
  have hc1 : c ≤ 1 := hc.2
  have hbIoo : b ∈ Set.Ioo (0:ℝ) 1 := ⟨lt_of_le_of_lt ha0 hab, lt_of_lt_of_le hbc hc1⟩
  have h1 : (∫ u in a..b, q u) ≤ (b - a) * q b := by
    have h := intervalIntegral.integral_mono_on_of_le_Ioo hab.le
      (intInt_sub hint ha0 hbIoo.2.le hab.le)
      (_root_.intervalIntegrable_const (c := q b))
      (fun u hu => hmono ⟨lt_of_le_of_lt ha0 hu.1, lt_trans hu.2 hbIoo.2⟩ hbIoo hu.2.le)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  have h2 : (c - b) * q b ≤ ∫ u in b..c, q u := by
    have h := intervalIntegral.integral_mono_on_of_le_Ioo hbc.le
      (_root_.intervalIntegrable_const (c := q b))
      (intInt_sub hint (le_trans ha0 hab.le) hc1 hbc.le)
      (fun u hu => hmono hbIoo ⟨lt_trans hbIoo.1 hu.1, lt_of_lt_of_le hu.2 hc1⟩ hu.1.le)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  have hHab : (∫ u in a..b, q u) = H q b - H q a :=
    H_sub hint ha0 hbIoo.2.le hab.le
  have hHbc : (∫ u in b..c, q u) = H q c - H q b :=
    H_sub hint (le_trans ha0 hab.le) hc1 hbc.le
  rw [hHab] at h1
  rw [hHbc] at h2
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [h1, h2]

end Convexity

section ConstantCase

/-- **The constant case.**  If `f` is constant equal to `c`, a tuple of centres is optimal iff one
of its coordinates equals `c`; the minimum is `0`. -/
theorem phiF_const_argmin {n : ℕ} [Nonempty (Fin n)] (c : ℝ) (x : Fin n → ℝ) :
    (∀ y : Fin n → ℝ, phiF (fun _ => c) x ≤ phiF (fun _ => c) y) ↔ ∃ k, x k = c := by
  have hval : ∀ z : Fin n → ℝ, phiF (fun _ => c) z = nearest z c := by
    intro z
    simp [phiF]
  constructor
  · intro h
    have h0 : phiF (fun _ => c) (fun _ : Fin n => c) = 0 := by
      rw [hval]
      refine le_antisymm ?_ nearest_nonneg
      simpa using nearest_le (x := fun _ : Fin n => c) (y := c) (Classical.arbitrary (Fin n))
    have hx0 : nearest x c = 0 := by
      have := h (fun _ => c)
      rw [hval, h0] at this
      exact le_antisymm this nearest_nonneg
    obtain ⟨k, hk⟩ := exists_nearest (x := x) (y := c)
    refine ⟨k, ?_⟩
    have : |c - x k| = 0 := by rw [← hk, hx0]
    have := abs_eq_zero.1 this
    linarith [sub_eq_zero.1 this]
  · rintro ⟨k, hk⟩ y
    have hx0 : nearest x c = 0 := by
      refine le_antisymm ?_ nearest_nonneg
      simpa [hk] using nearest_le (x := x) (y := c) k
    rw [hval, hval, hx0]
    exact nearest_nonneg

/-- In the constant case the minimum value is `0`. -/
theorem phiF_const_min_eq_zero {n : ℕ} [Nonempty (Fin n)] (c : ℝ) :
    phiF (fun _ => c) (fun _ : Fin n => c) = 0 := by
  have : phiF (fun _ => c) (fun _ : Fin n => c) = nearest (fun _ : Fin n => c) c := by
    simp [phiF]
  rw [this]
  refine le_antisymm ?_ nearest_nonneg
  simpa using nearest_le (x := fun _ : Fin n => c) (y := c) (Classical.arbitrary (Fin n))

end ConstantCase

section ContinuityOfRearrangement

variable {f q : ℝ → ℝ}

lemma nu_eq_restrict_Ioo : nu = volume.restrict (Set.Ioo (0:ℝ) 1) := by
  rw [nu]
  exact (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm

lemma aemeasurable_of_continuousOn (hfcont : ContinuousOn f (Set.Ioo (0:ℝ) 1)) :
    AEMeasurable f nu := by
  rw [nu_eq_restrict_Ioo]
  exact hfcont.aemeasurable measurableSet_Ioo

lemma nu_apply (s : Set ℝ) : nu s = volume (s ∩ Set.Ioc (0:ℝ) 1) :=
  Measure.restrict_apply' measurableSet_Ioc

/-- A value attained by the continuous function `f` on `(0,1)` lies in the support of its
distribution: every open interval around it has positive mass. -/
lemma map_Ioo_pos_of_mem_image (hfcont : ContinuousOn f (Set.Ioo (0:ℝ) 1))
    {α β : ℝ} {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1) (hft : f t ∈ Set.Ioo α β) :
    0 < Measure.map f nu (Set.Ioo α β) := by
  have hfm : AEMeasurable f nu := aemeasurable_of_continuousOn hfcont
  rw [Measure.map_apply_of_aemeasurable hfm measurableSet_Ioo, nu_apply]
  obtain ⟨V, hVopen, hV⟩ := (continuousOn_iff'.1 hfcont) (Set.Ioo α β) isOpen_Ioo
  have htV : t ∈ V ∩ Set.Ioo (0:ℝ) 1 := by
    rw [← hV]; exact ⟨hft, ht⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hVopen.inter isOpen_Ioo) t htV
  have hsub : Set.Ioo (t - r) (t + r) ⊆ f ⁻¹' Set.Ioo α β ∩ Set.Ioc (0:ℝ) 1 := by
    intro w hw
    have hwball : w ∈ Metric.ball t r := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> [linarith [hw.1]; linarith [hw.2]]
    have hwV := hball hwball
    have hw' : w ∈ f ⁻¹' Set.Ioo α β ∩ Set.Ioo (0:ℝ) 1 := by rw [hV]; exact hwV
    exact ⟨hw'.1, ⟨hw'.2.1, hw'.2.2.le⟩⟩
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  simp only [ENNReal.ofReal_pos]
  linarith

/-- If the distribution charges `Iic α` and `Ici β` with `α < β`, then, `f` being continuous, it
charges the interval `(α,β)` as well: the support has no gap. -/
lemma map_Ioo_pos_of_both_sides (hfcont : ContinuousOn f (Set.Ioo (0:ℝ) 1))
    {α β : ℝ} (hab : α < β)
    (h1 : 0 < Measure.map f nu (Set.Iic α)) (h2 : 0 < Measure.map f nu (Set.Ici β)) :
    0 < Measure.map f nu (Set.Ioo α β) := by
  have hfm : AEMeasurable f nu := aemeasurable_of_continuousOn hfcont
  have hex : ∀ {s : Set ℝ}, MeasurableSet s → 0 < Measure.map f nu s →
      ∃ t ∈ Set.Ioo (0:ℝ) 1, f t ∈ s := by
    intro s hs hpos
    by_contra hcon
    push_neg at hcon
    rw [Measure.map_apply_of_aemeasurable hfm hs, nu_apply] at hpos
    have hsub : f ⁻¹' s ∩ Set.Ioc (0:ℝ) 1 ⊆ {(1:ℝ)} := by
      rintro w ⟨hw, hw01⟩
      by_cases h1' : w = 1
      · simp [h1']
      · exact absurd hw (hcon w ⟨hw01.1, lt_of_le_of_ne hw01.2 h1'⟩)
    have hle := measure_mono (μ := volume) hsub
    rw [Real.volume_singleton] at hle
    exact absurd (le_antisymm hle (zero_le _)) (ne_of_gt hpos)
  obtain ⟨t₁, ht₁, hft₁⟩ := hex measurableSet_Iic h1
  obtain ⟨t₂, ht₂, hft₂⟩ := hex measurableSet_Ici h2
  have hsubI : Set.uIcc t₁ t₂ ⊆ Set.Ioo (0:ℝ) 1 := by
    intro w hw
    rw [Set.mem_uIcc] at hw
    rcases hw with ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
    · exact ⟨lt_of_lt_of_le ht₁.1 hw1, lt_of_le_of_lt hw2 ht₂.2⟩
    · exact ⟨lt_of_lt_of_le ht₂.1 hw1, lt_of_le_of_lt hw2 ht₁.2⟩
  have hIVT := intermediate_value_uIcc (f := f) (a := t₁) (b := t₂) (hfcont.mono hsubI)
  have hmid : (α + β) / 2 ∈ Set.uIcc (f t₁) (f t₂) := by
    have hle1 : f t₁ ≤ α := hft₁
    have hle2 : β ≤ f t₂ := hft₂
    rw [Set.mem_uIcc]
    left
    constructor <;> linarith
  obtain ⟨t, htmem, htval⟩ := hIVT hmid
  refine map_Ioo_pos_of_mem_image hfcont (hsubI htmem) ?_
  rw [htval]
  constructor <;> linarith

/-- **Continuity of the rearrangement (§5).**  A monotone function with the same distribution as a
continuous `f` is itself continuous on `(0,1)`: an internal jump would create a gap in the support,
which the intermediate value theorem forbids.  (The nonconstancy hypothesis `hfne`, present in the
printed discussion, turns out not to be needed.) -/
theorem rearrangement_continuous_of_continuous_nonconstant
    (hfcont : ContinuousOn f (Set.Ioo (0:ℝ) 1))
    (hfne : ∃ u ∈ Set.Ioo (0:ℝ) 1, ∃ v ∈ Set.Ioo (0:ℝ) 1, f u ≠ f v)
    (hmap : Measure.map q nu = Measure.map f nu)
    (hqmono : MonotoneOn q (Set.Ioo (0:ℝ) 1)) :
    ContinuousOn q (Set.Ioo (0:ℝ) 1) := by
  clear hfne
  have hqm : AEMeasurable q nu := by
    rw [nu_eq_restrict_Ioo]
    exact aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hqmono
  have key : ∀ u₀ ∈ Set.Ioo (0:ℝ) 1, ∀ ε > 0,
      (∃ u₁ ∈ Set.Ioo (0:ℝ) 1, u₁ < u₀ ∧ q u₀ - ε < q u₁) ∧
      (∃ u₂ ∈ Set.Ioo (0:ℝ) 1, u₀ < u₂ ∧ q u₂ < q u₀ + ε) := by
    intro u₀ hu₀ ε hε
    constructor
    · by_contra hcon
      push_neg at hcon
      have hleft : ∀ u ∈ Set.Ioo (0:ℝ) u₀, q u ≤ q u₀ - ε := by
        intro u hu
        exact hcon u ⟨hu.1, lt_trans hu.2 hu₀.2⟩ hu.2
      have h1 : 0 < Measure.map q nu (Set.Iic (q u₀ - ε)) := by
        rw [Measure.map_apply_of_aemeasurable hqm measurableSet_Iic, nu_apply]
        have hsub : Set.Ioo (0:ℝ) u₀ ⊆ q ⁻¹' Set.Iic (q u₀ - ε) ∩ Set.Ioc (0:ℝ) 1 :=
          fun u hu => ⟨hleft u hu, ⟨hu.1, le_of_lt (lt_trans hu.2 hu₀.2)⟩⟩
        refine lt_of_lt_of_le ?_ (measure_mono hsub)
        rw [Real.volume_Ioo, sub_zero]
        simp only [ENNReal.ofReal_pos]
        exact hu₀.1
      have h2 : 0 < Measure.map q nu (Set.Ici (q u₀)) := by
        rw [Measure.map_apply_of_aemeasurable hqm measurableSet_Ici, nu_apply]
        have hsub : Set.Ico u₀ 1 ⊆ q ⁻¹' Set.Ici (q u₀) ∩ Set.Ioc (0:ℝ) 1 :=
          fun u hu => ⟨hqmono hu₀ ⟨lt_of_lt_of_le hu₀.1 hu.1, hu.2⟩ hu.1,
            ⟨lt_of_lt_of_le hu₀.1 hu.1, hu.2.le⟩⟩
        refine lt_of_lt_of_le ?_ (measure_mono hsub)
        rw [Real.volume_Ico]
        simp only [ENNReal.ofReal_pos]
        linarith [hu₀.2]
      rw [hmap] at h1 h2
      have hpos := map_Ioo_pos_of_both_sides hfcont (by linarith : q u₀ - ε < q u₀) h1 h2
      rw [← hmap, Measure.map_apply_of_aemeasurable hqm measurableSet_Ioo, nu_apply] at hpos
      have hempty : q ⁻¹' Set.Ioo (q u₀ - ε) (q u₀) ∩ Set.Ioc (0:ℝ) 1 ⊆ {(1:ℝ)} := by
        rintro u ⟨hu, hu01⟩
        by_cases h1' : u = 1
        · simp [h1']
        · have humem : u ∈ Set.Ioo (0:ℝ) 1 := ⟨hu01.1, lt_of_le_of_ne hu01.2 h1'⟩
          rcases lt_or_ge u u₀ with hlt | hge
          · exact absurd hu.1 (not_lt.2 (hleft u ⟨hu01.1, hlt⟩))
          · exact absurd hu.2 (not_lt.2 (hqmono hu₀ humem hge))
      have hle := measure_mono (μ := volume) hempty
      rw [Real.volume_singleton] at hle
      exact absurd (le_antisymm hle (zero_le _)) (ne_of_gt hpos)
    · by_contra hcon
      push_neg at hcon
      have hright : ∀ u ∈ Set.Ioo u₀ (1:ℝ), q u₀ + ε ≤ q u := by
        intro u hu
        exact hcon u ⟨lt_trans hu₀.1 hu.1, hu.2⟩ hu.1
      have h1 : 0 < Measure.map q nu (Set.Iic (q u₀)) := by
        rw [Measure.map_apply_of_aemeasurable hqm measurableSet_Iic, nu_apply]
        have hsub : Set.Ioc (0:ℝ) u₀ ⊆ q ⁻¹' Set.Iic (q u₀) ∩ Set.Ioc (0:ℝ) 1 :=
          fun u hu => ⟨hqmono ⟨hu.1, lt_of_le_of_lt hu.2 hu₀.2⟩ hu₀ hu.2,
            ⟨hu.1, le_of_lt (lt_of_le_of_lt hu.2 hu₀.2)⟩⟩
        refine lt_of_lt_of_le ?_ (measure_mono hsub)
        rw [Real.volume_Ioc, sub_zero]
        simp only [ENNReal.ofReal_pos]
        exact hu₀.1
      have h2 : 0 < Measure.map q nu (Set.Ici (q u₀ + ε)) := by
        rw [Measure.map_apply_of_aemeasurable hqm measurableSet_Ici, nu_apply]
        have hsub : Set.Ioo u₀ (1:ℝ) ⊆ q ⁻¹' Set.Ici (q u₀ + ε) ∩ Set.Ioc (0:ℝ) 1 :=
          fun u hu => ⟨hright u hu, ⟨lt_trans hu₀.1 hu.1, hu.2.le⟩⟩
        refine lt_of_lt_of_le ?_ (measure_mono hsub)
        rw [Real.volume_Ioo]
        simp only [ENNReal.ofReal_pos]
        linarith [hu₀.2]
      rw [hmap] at h1 h2
      have hpos := map_Ioo_pos_of_both_sides hfcont (by linarith : q u₀ < q u₀ + ε) h1 h2
      rw [← hmap, Measure.map_apply_of_aemeasurable hqm measurableSet_Ioo, nu_apply] at hpos
      have hempty : q ⁻¹' Set.Ioo (q u₀) (q u₀ + ε) ∩ Set.Ioc (0:ℝ) 1 ⊆ {(1:ℝ)} := by
        rintro u ⟨hu, hu01⟩
        by_cases h1' : u = 1
        · simp [h1']
        · have humem : u ∈ Set.Ioo (0:ℝ) 1 := ⟨hu01.1, lt_of_le_of_ne hu01.2 h1'⟩
          rcases lt_or_ge u₀ u with hlt | hge
          · exact absurd hu.2 (not_lt.2 (hright u ⟨hlt, humem.2⟩))
          · exact absurd hu.1 (not_lt.2 (hqmono humem hu₀ hge))
      have hle := measure_mono (μ := volume) hempty
      rw [Real.volume_singleton] at hle
      exact absurd (le_antisymm hle (zero_le _)) (ne_of_gt hpos)
  intro u₀ hu₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨⟨u₁, hu₁mem, hu₁lt, hu₁val⟩, ⟨u₂, hu₂mem, hu₂lt, hu₂val⟩⟩ := key u₀ hu₀ ε hε
  refine ⟨min (u₀ - u₁) (u₂ - u₀), by simp only [lt_min_iff]; constructor <;> linarith, ?_⟩
  intro w hw hdist
  rw [Real.dist_eq, abs_lt] at hdist
  have hd1 : min (u₀ - u₁) (u₂ - u₀) ≤ u₀ - u₁ := min_le_left _ _
  have hd2 : min (u₀ - u₁) (u₂ - u₀) ≤ u₂ - u₀ := min_le_right _ _
  have hw1 : u₁ ≤ w := by linarith [hdist.1]
  have hw2 : w ≤ u₂ := by linarith [hdist.2]
  have hq1 : q u₁ ≤ q w := hqmono hu₁mem hw hw1
  have hq2 : q w ≤ q u₂ := hqmono hw hu₂mem hw2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end ContinuityOfRearrangement

end Q766

