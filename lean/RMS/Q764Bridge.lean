/-
# Q764 — Stage 1: threshold graphs, the finite optimum, and monotonicity

Simple mathematical bridges used by both the algorithms and the hardness proof:

* `Q764.covRad_le_iff_dominates` — covering radius `≤ r` is exactly domination in the
  threshold graph at scale `r`;
* `Q764.optimalRadius` — the optimum radius over all `k`-element subsets, together with
  the fact that it is attained (`Q764.optimalRadius_attained`);
* `Q764.covRad'_mono` — adding centers cannot increase the covering radius, whence
  `Q764.optimalRadius_eq_optimalRadiusLe`: optimizing over "exactly `k`" and over
  "at most `k`" centers gives the same value when `k ≤ |X|`.
-/
import RMS.Q764Cost

open Finset

namespace Q764

variable {α : Type*} [PseudoMetricSpace α]

/-! ## Threshold graph and domination -/

/-- The threshold graph at scale `r` on a finite set: two points are adjacent when their
distance is at most `r`. -/
def ThresholdAdj (r : ℝ) (a b : α) : Prop := dist a b ≤ r

/-- `F` dominates `X` in the threshold graph at scale `r`: every point of `X` is at
distance at most `r` from some element of `F`. -/
def Dominates (X F : Finset α) (r : ℝ) : Prop := ∀ x ∈ X, ∃ f ∈ F, ThresholdAdj r x f

/-- **Stage 1.1**: the covering radius of `F` for `X` is at most `r` if and only if `F`
dominates `X` in the threshold graph at scale `r`. -/
theorem covRad_le_iff_dominates {X F : Finset α} (hX : X.Nonempty) (hF : F.Nonempty) (r : ℝ) :
    covRad X F hX hF ≤ r ↔ Dominates X F r :=
  covRad_le_iff hX hF r

/-! ## Monotonicity in the set of centers -/

lemma covRad'_nonneg (X F : Finset α) : 0 ≤ covRad' X F := by
  rw [covRad']
  split_ifs with hX hF
  · obtain ⟨x, hx⟩ := hX
    exact le_trans (Finset.le_inf' hF (fun f => dist x f) fun f _ => dist_nonneg)
      (Finset.le_sup' (fun y => F.inf' hF fun f => dist y f) hx)
  · obtain ⟨x, hx⟩ := hX
    exact Finset.le_sup' (fun _ => (0 : ℝ)) hx
  · exact le_rfl

lemma covRad'_le_iff {X F : Finset α} (hX : X.Nonempty) (hF : F.Nonempty) (r : ℝ) :
    covRad' X F ≤ r ↔ ∀ x ∈ X, ∃ f ∈ F, dist x f ≤ r := by
  rw [covRad'_eq_covRad hX hF, covRad_le_iff]

/-- **Stage 1.3**: adding centers cannot increase the covering radius. -/
theorem covRad'_mono {X F G : Finset α} (hF : F.Nonempty) (hFG : F ⊆ G) :
    covRad' X G ≤ covRad' X F := by
  by_cases hX : X.Nonempty
  · have hG : G.Nonempty := hF.mono hFG
    rw [covRad'_le_iff hX hG]
    intro x hx
    obtain ⟨f, hf, hfle⟩ := (covRad'_le_iff hX hF _).1 (le_refl (covRad' X F)) x hx
    exact ⟨f, hFG hf, hfle⟩
  · simp [covRad', hX]

/-! ## The finite optimum -/

/-- The optimal covering radius achievable with exactly `k` centers chosen in `X`
(junk value `0` when there is no such subset). -/
noncomputable def optimalRadius (X : Finset α) (k : ℕ) : ℝ :=
  if h : (X.powersetCard k).Nonempty then (X.powersetCard k).inf' h (covRad' X) else 0

lemma optimalRadius_le {X F : Finset α} {k : ℕ} (hF : F ⊆ X) (hcard : F.card = k) :
    optimalRadius X k ≤ covRad' X F := by
  have hmem : F ∈ X.powersetCard k := Finset.mem_powersetCard.2 ⟨hF, hcard⟩
  have hne : (X.powersetCard k).Nonempty := ⟨F, hmem⟩
  rw [optimalRadius, dif_pos hne]
  exact Finset.inf'_le _ hmem

/-- **Stage 1.2**: the optimum is attained. -/
theorem optimalRadius_attained {X : Finset α} {k : ℕ} (hk : k ≤ X.card) :
    ∃ F ⊆ X, F.card = k ∧ covRad' X F = optimalRadius X k ∧
      ∀ G ⊆ X, G.card = k → covRad' X F ≤ covRad' X G := by
  have hne : (X.powersetCard k).Nonempty := Finset.powersetCard_nonempty.2 hk
  obtain ⟨F, hFmem, hFval⟩ := Finset.exists_mem_eq_inf' hne (covRad' X)
  obtain ⟨hFX, hFcard⟩ := Finset.mem_powersetCard.1 hFmem
  refine ⟨F, hFX, hFcard, ?_, ?_⟩
  · rw [optimalRadius, dif_pos hne]
    exact hFval.symm
  · intro G hGX hGcard
    rw [← hFval]
    exact Finset.inf'_le _ (Finset.mem_powersetCard.2 ⟨hGX, hGcard⟩)

lemma optimalRadius_nonneg (X : Finset α) (k : ℕ) : 0 ≤ optimalRadius X k := by
  rw [optimalRadius]
  split_ifs with h
  · exact Finset.le_inf' _ _ fun F _ => covRad'_nonneg X F
  · exact le_rfl

/-- The optimum over sets of at most `k` centers. -/
noncomputable def optimalRadiusLe (X : Finset α) (k : ℕ) : ℝ :=
  if h : ((X.powerset.filter fun F => F.card ≤ k ∧ F.Nonempty)).Nonempty then
    ((X.powerset.filter fun F => F.card ≤ k ∧ F.Nonempty)).inf' h (covRad' X) else 0

/-- Padding: any nonempty subset of `X` of size at most `k ≤ |X|` can be enlarged to a
subset of size exactly `k` without increasing the covering radius. -/
theorem exists_card_eq_covRad'_le [DecidableEq α] {X F : Finset α} {k : ℕ} (hFX : F ⊆ X)
    (hF : F.Nonempty) (hFk : F.card ≤ k) (hk : k ≤ X.card) :
    ∃ G, F ⊆ G ∧ G ⊆ X ∧ G.card = k ∧ covRad' X G ≤ covRad' X F := by
  obtain ⟨G, hFG, hGX, hGcard⟩ := Finset.exists_subsuperset_card_eq hFX hFk hk
  exact ⟨G, hFG, hGX, hGcard, covRad'_mono hF hFG⟩

/-- **Stage 1.3**: "at most `k`" and "exactly `k`" centers give the same optimum
when `1 ≤ k ≤ |X|`. -/
theorem optimalRadius_eq_optimalRadiusLe [DecidableEq α] {X : Finset α} {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ X.card) : optimalRadius X k = optimalRadiusLe X k := by
  have hXne : X.Nonempty := Finset.card_pos.1 (lt_of_lt_of_le hk1 hk)
  set S := X.powerset.filter fun F => F.card ≤ k ∧ F.Nonempty with hS
  obtain ⟨F₀, hF₀X, hF₀card, hF₀val, -⟩ := optimalRadius_attained hk
  have hF₀ne : F₀.Nonempty := Finset.card_pos.1 (by omega)
  have hSne : S.Nonempty := ⟨F₀, by
    simp only [hS, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hF₀X, by omega, hF₀ne⟩⟩
  rw [optimalRadiusLe, dif_pos hSne]
  refine le_antisymm ?_ ?_
  · -- every "at most k" set can be padded to a "= k" set with no larger radius
    refine Finset.le_inf' _ _ fun G hG => ?_
    simp only [Finset.mem_filter, Finset.mem_powerset] at hG
    obtain ⟨hGX, hGk, hGne⟩ := hG
    obtain ⟨H, -, hHX, hHcard, hHle⟩ := exists_card_eq_covRad'_le hGX hGne hGk hk
    exact le_trans (optimalRadius_le hHX hHcard) hHle
  · rw [← hF₀val]
    exact Finset.inf'_le _ (by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hF₀X, by omega, hF₀ne⟩)

end Q764
