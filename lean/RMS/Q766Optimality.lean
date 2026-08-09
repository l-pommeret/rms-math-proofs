import RMS.Q766Strict

/-!
# Q766, Stage 2b : strict optimal partitions and distinct optimal centres

Consequences of the strict improvement `e_{n+1} < eₙ` proved in `RequestProject.Q766Strict`:

* `Q766.optimal_partition_strict` : an optimal partition has no degenerate block;
* `Q766.optimal_centres_injective` : the coordinates of an optimal tuple are pairwise distinct.

Both are obtained by exhibiting an `(n-1)`-point configuration of the same cost.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral Set

namespace Q766

section Surgery

variable {q : ℝ → ℝ} {n : ℕ}

lemma K_self (a : ℝ) : K q a a = 0 := by
  simp only [K]
  have : (a + a) / 2 = a := by ring
  rw [this]; ring

/-- The index map `ℕ → ℕ` skipping the value `k+1`, used to delete a degenerate block. -/
def dropIdx (k j : ℕ) : ℕ := if j ≤ k then j else j + 1

lemma dropIdx_mono (k : ℕ) : Monotone (dropIdx k) := by
  intro a b hab
  simp only [dropIdx]
  split_ifs <;> omega

lemma partition_drop {s : ℕ → ℝ} (hs : s ∈ Partitions n) {k : ℕ} (hk : k < n)
    (hdeg : s k = s (k + 1)) : (fun j => s (dropIdx k j)) ∈ Partitions (n - 1) := by
  refine ⟨by simp [dropIdx, hs.1], ?_, hs.2.2.comp (dropIdx_mono k)⟩
  intro j hj
  by_cases h : j ≤ k
  · have hjk : j = k := by omega
    subst hjk
    simp only [dropIdx, if_pos h]
    rw [hdeg]
    exact hs.2.1 (j + 1) (by omega)
  · simp only [dropIdx, if_neg h]
    exact hs.2.1 (j + 1) (by omega)

lemma J_drop {s : ℕ → ℝ} {k : ℕ} (hk : k < n) (hdeg : s k = s (k + 1)) :
    J q (n - 1) (fun j => s (dropIdx k j)) = J q n s := by
  classical
  set T : ℕ → ℝ := fun i => K q (s i) (s (i + 1)) with hT
  have hσ : ∀ j : ℕ, K q (s (dropIdx k j)) (s (dropIdx k (j + 1)))
      = T (if j < k then j else j + 1) := by
    intro j
    by_cases h : j < k
    · simp only [dropIdx, hT, if_pos h, if_pos (show j ≤ k by omega),
        if_pos (show j + 1 ≤ k by omega)]
    · push_neg at h
      rcases eq_or_lt_of_le h with heq | hlt
      · subst heq
        simp only [dropIdx, hT, if_neg (lt_irrefl k), if_pos (le_refl k),
          if_neg (by omega : ¬ k + 1 ≤ k)]
        rw [hdeg]
      · simp only [dropIdx, hT, if_neg (by omega : ¬ j < k), if_neg (by omega : ¬ j ≤ k),
          if_neg (by omega : ¬ j + 1 ≤ k)]
  have h1 : J q (n - 1) (fun j => s (dropIdx k j))
      = ∑ j ∈ Finset.range (n - 1), T (if j < k then j else j + 1) := by
    rw [J]
    exact Finset.sum_congr rfl fun j _ => hσ j
  have h2 : ∑ j ∈ Finset.range (n - 1), T (if j < k then j else j + 1)
      = ∑ i ∈ (Finset.range n).erase k, T i := by
    refine Finset.sum_nbij' (i := fun j => if j < k then j else j + 1)
      (j := fun i => if i < k then i else i - 1) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_range] at ha
      simp only [Finset.mem_erase, Finset.mem_range]
      split_ifs <;> omega
    · intro a ha
      simp only [Finset.mem_erase, Finset.mem_range] at ha
      simp only [Finset.mem_range]
      split_ifs <;> omega
    · intro a ha
      simp only [Finset.mem_range] at ha
      dsimp only
      split_ifs <;> omega
    · intro a ha
      simp only [Finset.mem_erase, Finset.mem_range] at ha
      dsimp only
      split_ifs <;> omega
    · intro a _; rfl
  have h3 : T k = 0 := by rw [hT]; simp only []; rw [← hdeg]; exact K_self _
  rw [h1, h2, Finset.sum_erase _ h3, J]

end Surgery

section Consequences

variable {q : ℝ → ℝ} {n : ℕ}

/-- **Strict optimal partitions (5.3).**  For a continuous nonconstant nondecreasing `q`, an
optimal partition has no degenerate block. -/
theorem optimal_partition_strict (hn : 0 < n)
    (hmono : MonotoneOn q (Set.Ioo (0:ℝ) 1)) (hcont : ContinuousOn q (Set.Ioo (0:ℝ) 1))
    (hint : IntervalIntegrable q volume 0 1)
    (hqne : ∃ u ∈ Set.Ioo (0:ℝ) 1, ∃ v ∈ Set.Ioo (0:ℝ) 1, q u ≠ q v)
    {s : ℕ → ℝ} (hs : s ∈ Partitions n) (hsmin : ∀ t ∈ Partitions n, J q n s ≤ J q n t) :
    ∀ k < n, s k < s (k + 1) := by
  intro k hk
  rcases lt_or_eq_of_le (Partitions.mono hs (Nat.le_succ k)) with h | hdeg
  · exact h
  -- a degenerate block would give an `(n-1)`-point configuration of the same cost
  exfalso
  by_cases hn1 : n = 1
  · -- `n = 1`: the only block is `[0,1]`, which is nondegenerate
    subst hn1
    have hk0 : k = 0 := by omega
    subst hk0
    rw [hs.1, hs.2.1 1 le_rfl] at hdeg
    norm_num at hdeg
  · -- `n ≥ 2`
    have hm : 0 < n - 1 := by omega
    have hdrop := partition_drop hs hk hdeg
    have hcost := J_drop (q := q) hk hdeg
    obtain ⟨s', hs', hs'min, _, hval'⟩ := quantError_eq_min_J (q := q) (n := n - 1) hm hmono hint
    obtain ⟨s₀, hs₀, hs₀min, _, hval₀⟩ := quantError_eq_min_J (q := q) (n := n) hn hmono hint
    have hJeq : J q n s₀ = J q n s := le_antisymm (hs₀min s hs) (hsmin s₀ hs₀)
    have hlt : quantError q n < quantError q (n - 1) := by
      have := quantError_succ_lt (q := q) (n := n - 1) hm hmono hcont hint hqne
      rwa [show n - 1 + 1 = n by omega] at this
    have : quantError q (n - 1) ≤ quantError q n := by
      rw [hval', hval₀, hJeq, ← hcost]
      exact hs'min _ hdrop
    linarith

/-- `nearest` only depends on the set of centres. -/
lemma nearest_congr_range {m : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)] {x : Fin n → ℝ}
    {x' : Fin m → ℝ} (h : Set.range x' = Set.range x) (z : ℝ) : nearest x' z = nearest x z := by
  refine le_antisymm (le_nearest fun k => ?_) (le_nearest fun k => ?_)
  · have : x k ∈ Set.range x' := by rw [h]; exact ⟨k, rfl⟩
    obtain ⟨k', hk'⟩ := this
    rw [← hk']
    exact nearest_le k'
  · have : x' k ∈ Set.range x := by rw [← h]; exact ⟨k, rfl⟩
    obtain ⟨k', hk'⟩ := this
    rw [← hk']
    exact nearest_le k'

lemma Phi_congr_range {m : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)] {x : Fin n → ℝ}
    {x' : Fin m → ℝ} (h : Set.range x' = Set.range x) : Phi q x' = Phi q x := by
  simp only [Phi]
  exact intervalIntegral.integral_congr fun u _ => nearest_congr_range h (q u)

/-- **Distinct optimal centres.**  For a continuous nonconstant nondecreasing `q`, the coordinates
of a minimizing tuple are pairwise distinct. -/
theorem optimal_centres_injective (hn : 0 < n)
    (hmono : MonotoneOn q (Set.Ioo (0:ℝ) 1)) (hcont : ContinuousOn q (Set.Ioo (0:ℝ) 1))
    (hint : IntervalIntegrable q volume 0 1)
    (hqne : ∃ u ∈ Set.Ioo (0:ℝ) 1, ∃ v ∈ Set.Ioo (0:ℝ) 1, q u ≠ q v)
    {x : Fin n → ℝ} (hx : IsPhiMin q x) : Function.Injective x := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  intro i j hij
  by_contra hne
  -- there are at least two indices, so `n = m + 1` with `m ≥ 1`
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd (Fin.ext (by have := i.isLt; have := j.isLt; omega)) hne
    · exact h
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  set x' : Fin m → ℝ := x ∘ i.succAbove with hx'
  have hrange : Set.range x' = Set.range x := by
    apply Set.Subset.antisymm (Set.range_comp_subset_range _ _)
    rintro y ⟨k, rfl⟩
    by_cases hk : k = i
    · have hji : j ≠ i := fun h => hne h.symm
      obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq (x := j) (y := i) hji
      refine ⟨l, ?_⟩
      simp only [hx', Function.comp_apply, hl]
      rw [hk, hij]
    · obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq (x := k) (y := i) hk
      exact ⟨l, by simp only [hx', Function.comp_apply, hl]⟩
  have hPhi : Phi q x' = Phi q x := Phi_congr_range hrange
  have h1 : quantError q m ≤ Phi q x' := quantError_le hm hmono hint x'
  have h2 : quantError q (m + 1) = Phi q x := quantError_eq_of_isMin hx
  have h3 : quantError q (m + 1) < quantError q m := quantError_succ_lt hm hmono hcont hint hqne
  rw [hPhi] at h1
  linarith

end Consequences

end Q766
