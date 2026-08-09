import RMS.Q766Optimality

/-!
# Q766, Stage 2c : compactness of the attainment set

* `Q766.continuous_Phi` : `Φ` is `1`-Lipschitz, hence continuous, in the tuple of centres;
* `Q766.isClosed_PhiArgmin` : the attainment set is closed;
* `Q766.exists_uniform_block_length` : optimal partitions have a uniform positive lower bound on
  their block lengths (the compact set of optimal partitions avoids every zero-block face);
* `Q766.isCompact_PhiArgmin` : the attainment set is compact.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral Set

namespace Q766

section Continuity

variable {q : ℝ → ℝ} {n : ℕ}

/-- `nearest` is `1`-Lipschitz in the tuple of centres, uniformly in the point. -/
lemma nearest_dist_le [Nonempty (Fin n)] (x y : Fin n → ℝ) (z : ℝ) :
    nearest x z - nearest y z ≤ dist x y := by
  have : nearest x z - dist x y ≤ nearest y z := by
    refine le_nearest fun k => ?_
    have h1 : nearest x z ≤ |z - x k| := nearest_le k
    have h2 : |z - x k| ≤ |z - y k| + |y k - x k| := abs_sub_le z (y k) (x k)
    have h3 : |y k - x k| ≤ dist x y := by
      rw [abs_sub_comm]
      simpa [Real.dist_eq] using dist_le_pi_dist x y k
    linarith
  linarith

/-- `Φ q` is `1`-Lipschitz on the tuples of centres. -/
lemma Phi_dist_le [Nonempty (Fin n)] (hint : IntervalIntegrable q volume 0 1) (x y : Fin n → ℝ) :
    |Phi q x - Phi q y| ≤ dist x y := by
  have key : ∀ u v : Fin n → ℝ, Phi q u - Phi q v ≤ dist u v := by
    intro u v
    have hu := intInt_nearest (q := q) (x := u) hint le_rfl le_rfl (by norm_num : (0:ℝ) ≤ 1)
    have hv := intInt_nearest (q := q) (x := v) hint le_rfl le_rfl (by norm_num : (0:ℝ) ≤ 1)
    have hsub : Phi q u - Phi q v = ∫ w in (0:ℝ)..1, (nearest u (q w) - nearest v (q w)) := by
      rw [Phi, Phi, intervalIntegral.integral_sub hu hv]
    rw [hsub]
    have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) (hu.sub hv)
      (_root_.intervalIntegrable_const (c := dist u v))
      (fun w _ => nearest_dist_le u v (q w))
    simpa using h
  have h1 := key x y
  have h2 := key y x
  rw [dist_comm y x] at h2
  rw [abs_le]
  constructor <;> linarith

lemma continuous_Phi [Nonempty (Fin n)] (hint : IntervalIntegrable q volume 0 1) :
    Continuous (fun x : Fin n → ℝ => Phi q x) := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => ?_)
  simpa [Real.dist_eq] using Phi_dist_le hint x y

end Continuity

section Closed

variable {q : ℝ → ℝ} {n : ℕ}

lemma PhiArgmin_eq (hn : 0 < n) (hmono : MonotoneOn q (Set.Ioo (0:ℝ) 1))
    (hint : IntervalIntegrable q volume 0 1) :
    PhiArgmin q n = (fun x : Fin n → ℝ => Phi q x) ⁻¹' (Set.Iic (quantError q n)) := by
  ext x
  constructor
  · intro hx
    exact le_of_eq (quantError_eq_of_isMin hx).symm
  · intro hx y
    exact le_trans hx (quantError_le hn hmono hint y)

theorem isClosed_PhiArgmin (hn : 0 < n) (hmono : MonotoneOn q (Set.Ioo (0:ℝ) 1))
    (hint : IntervalIntegrable q volume 0 1) : IsClosed (PhiArgmin q n) := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [PhiArgmin_eq hn hmono hint]
  exact isClosed_Iic.preimage (continuous_Phi hint)

end Closed

section UniformBlocks

variable {q : ℝ → ℝ} {n : ℕ}

/-- The set of optimal partitions. -/
def OptParts (q : ℝ → ℝ) (n : ℕ) : Set (ℕ → ℝ) :=
  {s | s ∈ Partitions n ∧ ∀ t ∈ Partitions n, J q n s ≤ J q n t}

lemma isCompact_OptParts (hn : 0 < n) (hint : IntervalIntegrable q volume 0 1) :
    IsCompact (OptParts q n) := by
  obtain ⟨s₀, hs₀, hs₀min⟩ := exists_min_J (q := q) (n := n) hn hint
  have hset : OptParts q n = Partitions n ∩ (J q n) ⁻¹' (Set.Iic (J q n s₀)) := by
    ext s
    constructor
    · rintro ⟨hs, hmin⟩
      exact ⟨hs, hmin s₀ hs₀⟩
    · rintro ⟨hs, hle⟩
      exact ⟨hs, fun t ht => le_trans hle (hs₀min t ht)⟩
  refine (isCompact_Partitions (n := n)).of_isClosed_subset ?_ ?_
  · rw [hset]
    exact (continuousOn_J hint).preimage_isClosed_of_isClosed isClosed_Partitions isClosed_Iic
  · rw [hset]; exact Set.inter_subset_left

lemma OptParts_nonempty (hn : 0 < n) (hint : IntervalIntegrable q volume 0 1) :
    (OptParts q n).Nonempty := by
  obtain ⟨s₀, hs₀, hs₀min⟩ := exists_min_J (q := q) (n := n) hn hint
  exact ⟨s₀, hs₀, hs₀min⟩

/-- **Uniform positive block lengths.**  For a continuous nonconstant nondecreasing `q`, all
optimal partitions have block lengths bounded below by a fixed positive constant. -/
theorem exists_uniform_block_length (hn : 0 < n)
    (hmono : MonotoneOn q (Set.Ioo (0:ℝ) 1)) (hcont : ContinuousOn q (Set.Ioo (0:ℝ) 1))
    (hint : IntervalIntegrable q volume 0 1)
    (hqne : ∃ u ∈ Set.Ioo (0:ℝ) 1, ∃ v ∈ Set.Ioo (0:ℝ) 1, q u ≠ q v) :
    ∃ l : ℝ, 0 < l ∧ ∀ s ∈ OptParts q n, ∀ k < n, l ≤ s (k + 1) - s k := by
  have hcpt := isCompact_OptParts (q := q) (n := n) hn hint
  have hne := OptParts_nonempty (q := q) (n := n) hn hint
  have hex : ∀ k, k < n → ∃ l : ℝ, 0 < l ∧ ∀ s ∈ OptParts q n, l ≤ s (k + 1) - s k := by
    intro k hk
    obtain ⟨s₁, hs₁, hmin⟩ := hcpt.exists_isMinOn hne
      (Continuous.continuousOn ((continuous_apply (k + 1)).sub (continuous_apply k)))
    refine ⟨s₁ (k + 1) - s₁ k, ?_, fun s hs => hmin hs⟩
    have := optimal_partition_strict hn hmono hcont hint hqne hs₁.1 hs₁.2 k hk
    linarith
  choose! L hLpos hLle using hex
  have hrange : (Finset.range n).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  refine ⟨Finset.inf' (Finset.range n) hrange L, ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    intro k hk
    exact hLpos k (Finset.mem_range.1 hk)
  · intro s hs k hk
    exact le_trans (Finset.inf'_le L (Finset.mem_range.2 hk)) (hLle k hk s hs)

end UniformBlocks

section Compactness

variable {q : ℝ → ℝ} {n : ℕ}

/-- **Compactness of the attainment set.**  For a continuous nonconstant nondecreasing `q`, the
set of minimizers of `Φ` is compact. -/
theorem isCompact_PhiArgmin (hn : 0 < n)
    (hmono : MonotoneOn q (Set.Ioo (0:ℝ) 1)) (hcont : ContinuousOn q (Set.Ioo (0:ℝ) 1))
    (hint : IntervalIntegrable q volume 0 1)
    (hqne : ∃ u ∈ Set.Ioo (0:ℝ) 1, ∃ v ∈ Set.Ioo (0:ℝ) 1, q u ≠ q v) :
    IsCompact (PhiArgmin q n) := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨l, hlpos, hl⟩ := exists_uniform_block_length hn hmono hcont hint hqne
  -- `l ≤ 1`
  obtain ⟨s₀, hs₀⟩ := OptParts_nonempty (q := q) (n := n) hn hint
  have hl1 : l ≤ 1 := by
    have := hl s₀ hs₀ 0 hn
    have h1 := hs₀.1.1
    have h2 := Partitions.le_one hs₀.1 1
    linarith
  set a : ℝ := l / 2 with ha
  set b : ℝ := 1 - l / 2 with hb
  have haIoo : a ∈ Set.Ioo (0:ℝ) 1 := ⟨by simp only [ha]; linarith, by simp only [ha]; linarith⟩
  have hbIoo : b ∈ Set.Ioo (0:ℝ) 1 := ⟨by simp only [hb]; linarith, by simp only [hb]; linarith⟩
  set M : ℝ := max |q a| |q b| with hM
  have hsub : PhiArgmin q n ⊆ Set.univ.pi (fun _ : Fin n => Set.Icc (-M) M) := by
    intro x hx j _
    -- sort the tuple
    obtain ⟨σ, hσmono, hσPhi⟩ := exists_monotone_perm (q := q) x
    have hy : IsPhiMin q (x ∘ σ) := by
      intro z
      rw [hσPhi]
      exact hx z
    obtain ⟨s, hs, hsmin, hblocks⟩ := optimal_partition_of_isMin hmono hint hσmono hy
    have hstrict := optimal_partition_strict hn hmono hcont hint hqne hs hsmin
    have hlb := hl s ⟨hs, hsmin⟩
    -- every coordinate of the sorted tuple is a midpoint value in `[a,b]`
    have hcoord : ∀ k : Fin n, (x ∘ σ) k ∈ Set.Icc (-M) M := by
      intro k
      have hk : (k : ℕ) < n := k.isLt
      have hval : (x ∘ σ) k = q ((s (k : ℕ) + s ((k : ℕ) + 1)) / 2) :=
        median_unique_of_continuousOn hcont hint (Partitions.nonneg hs _)
          (hstrict (k : ℕ) hk) (Partitions.le_one hs _) (hblocks k)
      set m : ℝ := (s (k : ℕ) + s ((k : ℕ) + 1)) / 2 with hm
      have hs1 : l ≤ s 1 := by
        have := hlb 0 hn
        have := hs.1
        linarith
      have hkey1 : a ≤ m := by
        have h0 : 0 ≤ s (k : ℕ) := Partitions.nonneg hs _
        have h1 : s 1 ≤ s ((k : ℕ) + 1) := hs.2.2 (by omega)
        simp only [hm, ha]
        linarith
      have hkey2 : m ≤ b := by
        have h1 : s (k : ℕ) ≤ s (n - 1) := hs.2.2 (by omega)
        have h2 : l ≤ s n - s (n - 1) := by
          have := hlb (n - 1) (by omega)
          rwa [show n - 1 + 1 = n by omega] at this
        have h3 : s n = 1 := hs.2.1 n le_rfl
        have h4 : s ((k : ℕ) + 1) ≤ 1 := Partitions.le_one hs _
        simp only [hm, hb]
        linarith
      have hmIoo : m ∈ Set.Ioo (0:ℝ) 1 := ⟨lt_of_lt_of_le haIoo.1 hkey1,
        lt_of_le_of_lt hkey2 hbIoo.2⟩
      have hqa : q a ≤ q m := hmono haIoo hmIoo hkey1
      have hqb : q m ≤ q b := hmono hmIoo hbIoo hkey2
      have hMa : -M ≤ q a := by
        have : |q a| ≤ M := le_max_left _ _
        rw [abs_le] at this; linarith [this.1]
      have hMb : q b ≤ M := by
        have : |q b| ≤ M := le_max_right _ _
        rw [abs_le] at this; linarith [this.2]
      rw [hval]
      exact ⟨by linarith, by linarith⟩
    have := hcoord (σ.symm j)
    simpa using this
  refine IsCompact.of_isClosed_subset ?_ (isClosed_PhiArgmin hn hmono hint) hsub
  exact isCompact_univ_pi fun _ => isCompact_Icc

end Compactness

section Classification

variable {q : ℝ → ℝ} {n : ℕ}

/-- **Exact form of (5.4).**  For a continuous nonconstant nondecreasing `q`, an arbitrary tuple
of centres minimizes `Φ` if and only if it is a permutation of the tuple of block midpoint values
of a *strict* optimal partition. -/
theorem isPhiMin_iff_perm_medians (hn : 0 < n)
    (hmono : MonotoneOn q (Set.Ioo (0:ℝ) 1)) (hcont : ContinuousOn q (Set.Ioo (0:ℝ) 1))
    (hint : IntervalIntegrable q volume 0 1)
    (hqne : ∃ u ∈ Set.Ioo (0:ℝ) 1, ∃ v ∈ Set.Ioo (0:ℝ) 1, q u ≠ q v)
    (x : Fin n → ℝ) :
    IsPhiMin q x ↔ ∃ s ∈ Partitions n, (∀ t ∈ Partitions n, J q n s ≤ J q n t) ∧
      (∀ k < n, s k < s (k + 1)) ∧ ∃ σ : Equiv.Perm (Fin n), x = medians q n s ∘ σ := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  constructor
  · intro hx
    obtain ⟨σ, hσmono, hσPhi⟩ := exists_monotone_perm (q := q) x
    have hy : IsPhiMin q (x ∘ σ) := by
      intro z; rw [hσPhi]; exact hx z
    obtain ⟨s, hs, hsmin, hblocks⟩ := optimal_partition_of_isMin hmono hint hσmono hy
    have hstrict := optimal_partition_strict hn hmono hcont hint hqne hs hsmin
    have hval : x ∘ σ = medians q n s := by
      funext k
      exact median_unique_of_continuousOn hcont hint (Partitions.nonneg hs _)
        (hstrict (k : ℕ) k.isLt) (Partitions.le_one hs _) (hblocks k)
    refine ⟨s, hs, hsmin, hstrict, σ.symm, ?_⟩
    funext j
    have := congrFun hval (σ.symm j)
    simpa using this
  · rintro ⟨s, hs, hsmin, -, σ, rfl⟩
    intro y
    rw [Phi_comp_perm (medians q n s) σ]
    exact isMin_medians hmono hint hs hsmin y

end Classification

end Q766
