import RMS.Q766Rearrangement

/-!
# Q766, Stages 1–2 for the printed function `f`

Everything proved at the level of the quantile `q` is transported here to the function `f` of the
printed statement, through the rearrangement constructed in `RequestProject.Q766Rearrangement`.

* `Q766.printed_nonconstant` : the complete answer for a continuous nonconstant integrable `f`;
* `Q766.printed_constant` : the constant case.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral Set Filter Topology

namespace Q766

section Printed

variable {f q : ℝ → ℝ}

/-- A rearrangement of a nonconstant continuous function is nonconstant. -/
lemma rearrangement_nonconstant (hfcont : ContinuousOn f (Set.Ioo (0:ℝ) 1))
    (hfne : ∃ u ∈ Set.Ioo (0:ℝ) 1, ∃ v ∈ Set.Ioo (0:ℝ) 1, f u ≠ f v)
    (hqm : AEMeasurable q nu) (hmap : Measure.map q nu = Measure.map f nu) :
    ∃ u ∈ Set.Ioo (0:ℝ) 1, ∃ v ∈ Set.Ioo (0:ℝ) 1, q u ≠ q v := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨u₀, hu₀, v₀, hv₀, hne⟩ := hfne
  set c : ℝ := q (1/2) with hc
  have hhalf : (1/2 : ℝ) ∈ Set.Ioo (0:ℝ) 1 := by norm_num
  have hqc : ∀ u ∈ Set.Ioo (0:ℝ) 1, q u = c := fun u hu => hcon u hu (1/2) hhalf
  -- one of the two values of `f` differs from `c`
  obtain ⟨w, hw, hwc⟩ : ∃ w ∈ Set.Ioo (0:ℝ) 1, f w ≠ c := by
    by_cases h : f u₀ = c
    · exact ⟨v₀, hv₀, fun h' => hne (h.trans h'.symm)⟩
    · exact ⟨u₀, hu₀, h⟩
  -- an interval around `f w` avoiding `c`
  obtain ⟨α, β, hab, hmem, hcnot⟩ : ∃ α β : ℝ, α < β ∧ f w ∈ Set.Ioo α β ∧ c ∉ Set.Ioo α β := by
    rcases lt_or_gt_of_ne hwc with h | h
    · exact ⟨f w - 1, (f w + c) / 2, by linarith, ⟨by linarith, by linarith⟩,
        fun hmem => absurd hmem.2 (by simp only [not_lt]; linarith)⟩
    · exact ⟨(f w + c) / 2, f w + 1, by linarith, ⟨by linarith, by linarith⟩,
        fun hmem => absurd hmem.1 (by simp only [not_lt]; linarith)⟩
  have hpos := map_Ioo_pos_of_mem_image hfcont hw hmem
  rw [← hmap, Measure.map_apply_of_aemeasurable hqm measurableSet_Ioo, nu_apply] at hpos
  have hempty : q ⁻¹' Set.Ioo α β ∩ Set.Ioc (0:ℝ) 1 ⊆ {(1:ℝ)} := by
    rintro u ⟨hu, hu01⟩
    by_cases h1 : u = 1
    · simp [h1]
    · have humem : u ∈ Set.Ioo (0:ℝ) 1 := ⟨hu01.1, lt_of_le_of_ne hu01.2 h1⟩
      have hu' : q u ∈ Set.Ioo α β := hu
      rw [hqc u humem] at hu'
      exact absurd hu' hcnot
  have hle := measure_mono (μ := volume) hempty
  rw [Real.volume_singleton] at hle
  exact absurd (le_antisymm hle (zero_le _)) (ne_of_gt hpos)

/-- **The printed problem, nonconstant continuous case.**  For a continuous, integrable and
nonconstant `f : (0,1) → ℝ` and `n > 0` centres, there is a continuous nondecreasing rearrangement
`q` with `φ_f = Φ_q`, for which:

* the minimum of `φ_f` is the optimal partition cost `J`, attained at the block midpoint values of
  an optimal partition;
* every optimal partition is strict;
* a tuple is optimal iff it is a permutation of the block midpoint values of a strict optimal
  partition;
* optimal centres are pairwise distinct;
* the set of minimizers is compact;
* the optimal distortions are positive, strictly decreasing and tend to `0`. -/
theorem printed_nonconstant {n : ℕ} (hn : 0 < n)
    (hfcont : ContinuousOn f (Set.Ioo (0:ℝ) 1)) (hfint : Integrable f nu)
    (hfne : ∃ u ∈ Set.Ioo (0:ℝ) 1, ∃ v ∈ Set.Ioo (0:ℝ) 1, f u ≠ f v) :
    ∃ q : ℝ → ℝ,
      MonotoneOn q (Set.Ioo (0:ℝ) 1) ∧ ContinuousOn q (Set.Ioo (0:ℝ) 1) ∧
      IntervalIntegrable q volume 0 1 ∧
      (∀ x : Fin n → ℝ, phiF f x = Phi q x) ∧
      (∃ s ∈ Partitions n, (∀ t ∈ Partitions n, J q n s ≤ J q n t) ∧
        (∀ k < n, s k < s (k + 1)) ∧
        (∀ x : Fin n → ℝ, phiF f (medians q n s) ≤ phiF f x) ∧
        phiF f (medians q n s) = J q n s ∧ quantError q n = J q n s) ∧
      (∀ x : Fin n → ℝ, (∀ y : Fin n → ℝ, phiF f x ≤ phiF f y) ↔
        ∃ s ∈ Partitions n, (∀ t ∈ Partitions n, J q n s ≤ J q n t) ∧
          (∀ k < n, s k < s (k + 1)) ∧ ∃ σ : Equiv.Perm (Fin n), x = medians q n s ∘ σ) ∧
      (∀ x : Fin n → ℝ, (∀ y : Fin n → ℝ, phiF f x ≤ phiF f y) → Function.Injective x) ∧
      IsCompact {x : Fin n → ℝ | ∀ y : Fin n → ℝ, phiF f x ≤ phiF f y} ∧
      (∀ m : ℕ, 0 < m → 0 < quantError q m ∧ quantError q (m + 1) < quantError q m) ∧
      Tendsto (fun m : ℕ => quantError q (m + 1)) atTop (𝓝 0) := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hfmeas : AEMeasurable f nu := aemeasurable_of_continuousOn hfcont
  obtain ⟨q, hqm, hqmono, hqint, hmap⟩ := exists_integrable_monotone_rearrangement hfint
  have hqcont : ContinuousOn q (Set.Ioo (0:ℝ) 1) :=
    rearrangement_continuous_of_continuous_nonconstant hfcont hfne hmap hqmono
  have hqne : ∃ u ∈ Set.Ioo (0:ℝ) 1, ∃ v ∈ Set.Ioo (0:ℝ) 1, q u ≠ q v :=
    rearrangement_nonconstant hfcont hfne hqm hmap
  have htransfer : ∀ x : Fin n → ℝ, phiF f x = Phi q x := fun x =>
    phiF_eq_Phi_of_map_eq x hfmeas hqm hmap
  have hargmin : {x : Fin n → ℝ | ∀ y : Fin n → ℝ, phiF f x ≤ phiF f y} = PhiArgmin q n := by
    ext x
    simp only [Set.mem_setOf_eq, mem_PhiArgmin, IsPhiMin, htransfer]
  refine ⟨q, hqmono, hqcont, hqint, htransfer, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, hs, hsmin, hmin, hval⟩ := quantError_eq_min_J hn hqmono hqint
    refine ⟨s, hs, hsmin, optimal_partition_strict hn hqmono hqcont hqint hqne hs hsmin,
      fun x => ?_, ?_, hval⟩
    · rw [htransfer, htransfer]; exact hmin x
    · rw [htransfer, ← hval, quantError_eq_of_isMin hmin]
  · intro x
    have := isPhiMin_iff_perm_medians hn hqmono hqcont hqint hqne x
    simp only [IsPhiMin] at this
    simp only [htransfer]
    exact this
  · intro x hx
    refine optimal_centres_injective hn hqmono hqcont hqint hqne (x := x) ?_
    intro y
    rw [← htransfer, ← htransfer]
    exact hx y
  · rw [hargmin]
    exact isCompact_PhiArgmin hn hqmono hqcont hqint hqne
  · intro m hm
    exact ⟨quantError_pos hm hqmono hqcont hqint hqne,
      quantError_succ_lt hm hqmono hqcont hqint hqne⟩
  · exact quantError_tendsto_zero hqmono hqint

/-- **The printed problem, constant case.**  If `f` is constant equal to `c`, the minimum of `φ_f`
is `0` and the minimizers are exactly the tuples one of whose coordinates equals `c`. -/
theorem printed_constant {n : ℕ} [Nonempty (Fin n)] (c : ℝ) :
    phiF (fun _ => c) (fun _ : Fin n => c) = 0 ∧
      ∀ x : Fin n → ℝ,
        (∀ y : Fin n → ℝ, phiF (fun _ => c) x ≤ phiF (fun _ => c) y) ↔ ∃ k, x k = c :=
  ⟨phiF_const_min_eq_zero c, fun x => phiF_const_argmin c x⟩

end Printed

end Q766
