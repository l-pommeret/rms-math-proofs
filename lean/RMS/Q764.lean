/-
# Q764 — the discrete `k`-center problem

Formalization of the mathematical core of the accepted solution to Q764
(source: https://lucpommeret.com/assets/Qsansreponse260405.pdf).

Given a finite set `X` of points, a set of centers `F` and
`δ(X,F) = max_{x ∈ X} min_{f ∈ F} d(x,f)`, one looks for a `k`-element `F ⊆ X`
minimizing `δ(X,F)`, on the real line (part (a)) and in an arbitrary finite metric
space (part (b)).

## What is formalized

Part (b), arbitrary finite metric space:

* `Q764.exists_optimal_center_set` — an optimal `k`-element set of centers exists
  (the mathematical content of the exhaustive algorithm of §11);
* `Q764.FarthestFirst.two_approx` and `Q764.FarthestFirst.covRad_le_two_mul` —
  **Theorem 12**: the farthest-first traversal returns `F` with `δ(X,F) ≤ 2 δ_opt`;
* `Q764.oneTwo_triangle` — **Lemma 9**: the `1`–`2` distance functions used in the
  NP-hardness reduction really do satisfy the triangle inequality.

Part (a), `n` points on the real line:

* `Q764.blockRadius_eq_max`, `Q764.blockRadius_eq_mid`, `Q764.blockCost_eq` —
  **Lemma 1**: the one-center cost of a consecutive block, and the fact that an optimal
  center of a block is a point of the block nearest to the midpoint of its endpoints;
* `Q764.exists_center_in_block`, `Q764.blockCost_mono_left`, `Q764.blockCost_mono_right` —
  **Lemma 5**: monotonicity of the block costs;
* `Q764.coverPrefix_succ_iff` — **Lemma 4**: the bottleneck dynamic-programming
  recurrence, in decision (feasibility) form;
* `Q764.coverPrefix_iff_exists_centers` — the dictionary between the index formulation
  used for the recurrence and the original `k`-center feasibility problem.

## Mismatches between the printed solution and the formal statements

* The printed answer is largely a statement about *algorithms and their complexity*
  (`O(n² + kn)` running time, NP-completeness, "no polynomial factor `2 - ε`
  algorithm unless P = NP"). Complexity-theoretic claims are not formalized here: they
  would require a formal model of computation, which mathlib does not provide. What is
  formalized is the mathematical content on which those algorithms rest.
* `Q764.coverPrefix_succ_iff` is the decision (feasibility) form of the recurrence
  `ρ_p(j) = min_i max(ρ_{p-1}(i-1), c(i,j))`: for a fixed radius `r`, a prefix is
  coverable by `p + 1` centers iff it splits into a last block of one-center cost `≤ r`
  and a shorter prefix coverable by `p` centers. This is equivalent to the displayed
  recurrence between real-valued optima (both sides describe the same sublevel sets),
  and avoids introducing the value `+∞` used in the informal text.
* In the recurrence the centers are allowed to be arbitrary points of `X`; that the
  center of a block may always be taken inside the block is `exists_center_in_block`.
* The points on the line are given by an indexing `x : ℕ → ℝ` which is assumed
  `Monotone` (rather than strictly increasing); injectivity of `x` is only used in
  `coverPrefix_iff_exists_centers`, where indices are translated into points.
* `k ≥ 1` is assumed wherever the informal statement implicitly needs it.

## Versions

Lean 4.28.0 (`leanprover/lean4:v4.28.0`);
mathlib at commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (tag `v4.28.0`).
-/
import Mathlib

open Finset

namespace Q764

/-! ## Covering radius -/

variable {α : Type*} [PseudoMetricSpace α]

/-- Distance from `x` to a nonempty finite set `F`. -/
noncomputable def distTo (F : Finset α) (hF : F.Nonempty) (x : α) : ℝ :=
  F.inf' hF fun f => dist x f

/-- `δ(X, F) = max_{x ∈ X} min_{f ∈ F} d(x, f)`, the covering radius of `F` for `X`. -/
noncomputable def covRad (X F : Finset α) (hX : X.Nonempty) (hF : F.Nonempty) : ℝ :=
  X.sup' hX fun x => distTo F hF x

lemma distTo_le_iff {F : Finset α} (hF : F.Nonempty) (x : α) (r : ℝ) :
    distTo F hF x ≤ r ↔ ∃ f ∈ F, dist x f ≤ r := by
  simp [distTo, Finset.inf'_le_iff]

lemma covRad_le_iff {X F : Finset α} (hX : X.Nonempty) (hF : F.Nonempty) (r : ℝ) :
    covRad X F hX hF ≤ r ↔ ∀ x ∈ X, ∃ f ∈ F, dist x f ≤ r := by
  simp [covRad, Finset.sup'_le_iff, distTo_le_iff]

lemma exists_dist_le_covRad {X F : Finset α} (hX : X.Nonempty) (hF : F.Nonempty)
    {x : α} (hx : x ∈ X) : ∃ f ∈ F, dist x f ≤ covRad X F hX hF :=
  (covRad_le_iff hX hF _).1 le_rfl x hx

/-- Sanity check (`k = n`): taking every point as a center gives covering radius `0`. -/
lemma covRad_self {X : Finset α} (hX : X.Nonempty) : covRad X X hX hX = 0 := by
  have h : ∀ y ∈ X, distTo X hX y = 0 := by
    intro y hy
    rw [distTo]
    refine le_antisymm ?_ (Finset.le_inf' _ _ fun f _ => dist_nonneg)
    exact le_trans (Finset.inf'_le (fun f => dist y f) hy) (by simp)
  rw [covRad, Finset.sup'_congr hX rfl h]
  simp

/-- A total (junk-valued) version of `covRad`, convenient for optimizing over all
`k`-element subsets at once. -/
noncomputable def covRad' (X F : Finset α) : ℝ :=
  if hX : X.Nonempty then
    X.sup' hX fun x => if hF : F.Nonempty then F.inf' hF (fun f => dist x f) else 0
  else 0

lemma covRad'_eq_covRad {X F : Finset α} (hX : X.Nonempty) (hF : F.Nonempty) :
    covRad' X F = covRad X F hX hF := by
  simp [covRad', covRad, distTo, hX, hF]

/-- **Section 11** (correctness of the exhaustive algorithm): for `k ≤ |X|` there exists a
`k`-element subset of `X` minimizing the covering radius. -/
theorem exists_optimal_center_set [DecidableEq α] {X : Finset α} {k : ℕ} (hk : k ≤ X.card) :
    ∃ F ⊆ X, F.card = k ∧ ∀ G ⊆ X, G.card = k → covRad' X F ≤ covRad' X G := by
  obtain ⟨F, hF, hmin⟩ :=
    (X.powersetCard k).exists_min_image (covRad' X) (Finset.powersetCard_nonempty.2 hk)
  obtain ⟨hFX, hFcard⟩ := Finset.mem_powersetCard.1 hF
  exact ⟨F, hFX, hFcard, fun G hGX hGcard =>
    hmin G (Finset.mem_powersetCard.2 ⟨hGX, hGcard⟩)⟩

/-! ## Farthest-first traversal -/

/-- `nd c t x` is the distance from `x` to the first `t+1` chosen centers
`c 0, …, c t`. -/
noncomputable def nd (c : ℕ → α) (t : ℕ) (x : α) : ℝ :=
  (range (t + 1)).inf' (nonempty_range_add_one) fun s => dist x (c s)

lemma nd_le_dist (c : ℕ → α) {t s : ℕ} (hs : s ≤ t) (x : α) : nd c t x ≤ dist x (c s) :=
  Finset.inf'_le _ (by simp [hs])

lemma nd_antitone (c : ℕ → α) {t t' : ℕ} (h : t ≤ t') (x : α) : nd c t' x ≤ nd c t x := by
  refine Finset.le_inf' _ _ ?_
  intro s hs
  have hst : s ≤ t := by simpa using hs
  exact nd_le_dist c (hst.trans h) x

/-- The defining property of the farthest-first traversal: all the `k` chosen centers
lie in `X`, and each new center is a point of `X` farthest away from the previously
chosen ones. -/
structure FarthestFirst (X : Finset α) (k : ℕ) (c : ℕ → α) : Prop where
  mem : ∀ i < k, c i ∈ X
  greedy : ∀ t, t + 1 < k → ∀ x ∈ X, nd c t x ≤ nd c t (c (t + 1))

/-- Key separation property: if `x ∈ X` then the `k + 1` points
`c 0, …, c (k-1), x` are pairwise at distance at least `nd c (k-1) x`. -/
lemma FarthestFirst.dist_center_ge {X : Finset α} {k : ℕ} {c : ℕ → α}
    (hff : FarthestFirst X k c) {x : α} (hx : x ∈ X) {i j : ℕ} (hij : i < j) (hj : j < k) :
    nd c (k - 1) x ≤ dist (c j) (c i) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  calc nd c (k - 1) x ≤ nd c m x := nd_antitone c (by omega) x
    _ ≤ nd c m (c (m + 1)) := hff.greedy m (by omega) x hx
    _ ≤ dist (c (m + 1)) (c i) := nd_le_dist c (by omega) _

/-- **Theorem 12** (farthest-first is a factor-2 approximation), covering form:
if some set `F` of at most `k` points covers `X` with radius `R`, then the `k`
farthest-first centers cover `X` with radius `2R`. -/
theorem FarthestFirst.two_approx {X : Finset α} {k : ℕ} {c : ℕ → α}
    (hk : 0 < k) (hff : FarthestFirst X k c) {F : Finset α} (hcard : F.card ≤ k) {R : ℝ}
    (hcov : ∀ x ∈ X, ∃ f ∈ F, dist x f ≤ R) :
    ∀ x ∈ X, ∃ s < k, dist x (c s) ≤ 2 * R := by
  intro x hx
  -- the `k + 1` points `c 0, …, c (k-1), x`
  set p : Fin (k + 1) → α := fun i => if (i : ℕ) < k then c i else x with hp
  have hpX : ∀ i, p i ∈ X := by
    intro i
    by_cases h : (i : ℕ) < k
    · simpa [hp, h] using hff.mem _ h
    · simpa [hp, h] using hx
  -- pairwise separation
  have hsep : ∀ i j : Fin (k + 1), (i : ℕ) < (j : ℕ) → nd c (k - 1) x ≤ dist (p i) (p j) := by
    intro i j hij
    have hjk : (j : ℕ) ≤ k := Fin.is_le j
    have hik : (i : ℕ) < k := lt_of_lt_of_le hij hjk
    by_cases hj : (j : ℕ) < k
    · have := hff.dist_center_ge hx hij hj
      simpa [hp, hik, hj, dist_comm] using this
    · have : nd c (k - 1) x ≤ dist x (c i) := nd_le_dist c (by omega) x
      simpa [hp, hik, hj, dist_comm] using this
  -- pigeonhole: two of the `k + 1` points share a center of `F`
  choose g hgF hgR using fun i : Fin (k + 1) => hcov (p i) (hpX i)
  have hcard' : F.card < (Finset.univ : Finset (Fin (k + 1))).card := by
    simpa using lt_of_le_of_lt hcard (Nat.lt_succ_self k)
  obtain ⟨i, -, j, -, hne, hgij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard' (fun i _ => hgF i)
  have key : nd c (k - 1) x ≤ 2 * R := by
    have main : ∀ a b : Fin (k + 1), (a : ℕ) < (b : ℕ) → g a = g b → nd c (k - 1) x ≤ 2 * R := by
      intro a b hab hg
      have h1 : dist (p a) (p b) ≤ dist (p a) (g a) + dist (g b) (p b) := by
        rw [hg]; exact dist_triangle _ _ _
      have h2 : dist (g b) (p b) = dist (p b) (g b) := dist_comm _ _
      have := hsep a b hab
      have hb := hgR b
      have ha := hgR a
      linarith
    rcases lt_or_gt_of_ne (fun h : (i : ℕ) = (j : ℕ) => hne (Fin.ext h)) with h | h
    · exact main i j h hgij
    · exact main j i h hgij.symm
  rw [nd, Finset.inf'_le_iff] at key
  obtain ⟨s, hs, hle⟩ := key
  refine ⟨s, ?_, hle⟩
  simp only [Finset.mem_range] at hs
  omega

/-- **Theorem 12**, covering-radius form: the set of `k` farthest-first centers has
covering radius at most twice the covering radius of *any* set of at most `k` points. -/
theorem FarthestFirst.covRad_le_two_mul [DecidableEq α] {X : Finset α} {k : ℕ} {c : ℕ → α}
    (hk : 0 < k) (hff : FarthestFirst X k c) (hX : X.Nonempty)
    (hG : ((range k).image c).Nonempty) {F : Finset α} (hF : F.Nonempty) (hcard : F.card ≤ k) :
    covRad X ((range k).image c) hX hG ≤ 2 * covRad X F hX hF := by
  rw [covRad_le_iff]
  intro y hy
  obtain ⟨s, hs, hle⟩ :=
    hff.two_approx hk hcard (fun z hz => exists_dist_le_covRad hX hF hz) y hy
  exact ⟨c s, Finset.mem_image_of_mem _ (Finset.mem_range.2 hs), hle⟩

/-! ## Lemma 9: the `1`–`2` distance functions of the NP-hardness reduction are metrics -/

/-- Any function vanishing on the diagonal, with all nonzero values in
`[1, 2]`, satisfies the triangle inequality (hence is a metric). -/
theorem oneTwo_triangle {β : Type*} (D : β → β → ℝ) (hdiag : ∀ a, D a a = 0)
    (hlb : ∀ a b, a ≠ b → 1 ≤ D a b) (hub : ∀ a b, D a b ≤ 2) (a b c : β) :
    D a c ≤ D a b + D b c := by
  rcases eq_or_ne a b with rfl | hab
  · have := hdiag a; linarith
  rcases eq_or_ne b c with rfl | hbc
  · have := hdiag b; linarith
  have h1 := hlb a b hab
  have h2 := hlb b c hbc
  have h3 := hub a c
  linarith

/-! ## Part (a): `n` points on the real line

Throughout, the points are `x 0 ≤ x 1 ≤ ⋯ ≤ x (n-1)` (`Monotone x`; strict monotonicity,
i.e. distinctness of the points, is only needed for the dictionary between index sets and
point sets at the very end).
-/

section Line

variable {x : ℕ → ℝ} {i j l : ℕ}

/-- Cost of covering the block of indices `[i, j]` by the single center `x l`. -/
noncomputable def blockRadius (x : ℕ → ℝ) (i j l : ℕ) (h : i ≤ j) : ℝ :=
  (Icc i j).sup' (nonempty_Icc.2 h) fun t => |x t - x l|

/-- `c(i,j)`: the optimal cost of covering the block `[i, j]` by one center of the block. -/
noncomputable def blockCost (x : ℕ → ℝ) (i j : ℕ) (h : i ≤ j) : ℝ :=
  (Icc i j).inf' (nonempty_Icc.2 h) fun l => blockRadius x i j l h

lemma inf'_const_add {ι : Type*} (s : Finset ι) (H : s.Nonempty) (C : ℝ) (g : ι → ℝ) :
    (s.inf' H fun l => C + g l) = C + s.inf' H g := by
  refine le_antisymm ?_ (Finset.le_inf' _ _ fun b hb => by
    have := Finset.inf'_le g hb; linarith)
  obtain ⟨l₀, hl₀, hval⟩ := Finset.exists_mem_eq_inf' H g
  rw [hval]
  exact Finset.inf'_le _ hl₀

/-- The point of a block farthest from a center of the block is one of the two endpoints. -/
lemma blockRadius_eq_max (hx : Monotone x) (h : i ≤ j) (hil : i ≤ l) (hlj : l ≤ j) :
    blockRadius x i j l h = max (x l - x i) (x j - x l) := by
  have hxi : x i ≤ x l := hx hil
  have hxj : x l ≤ x j := hx hlj
  refine le_antisymm (Finset.sup'_le _ _ fun t ht => ?_) ?_
  · obtain ⟨ht1, ht2⟩ := mem_Icc.1 ht
    have h1 : x i ≤ x t := hx ht1
    have h2 : x t ≤ x j := hx ht2
    refine abs_le.2 ⟨?_, ?_⟩
    · have := le_max_left (x l - x i) (x j - x l); linarith
    · have := le_max_right (x l - x i) (x j - x l); linarith
  · refine max_le ?_ ?_
    · have := Finset.le_sup' (fun t => |x t - x l|) (mem_Icc.2 ⟨le_rfl, h⟩ : i ∈ Icc i j)
      rw [abs_sub_comm, abs_of_nonneg (by linarith)] at this
      exact this
    · have := Finset.le_sup' (fun t => |x t - x l|) (mem_Icc.2 ⟨h, le_rfl⟩ : j ∈ Icc i j)
      rwa [abs_of_nonneg (by linarith)] at this

/-- **Lemma 1**: the one-center cost of the block `[i, j]` with center `x l` equals
`(x j - x i)/2 + |x l - (x i + x j)/2|`. -/
lemma blockRadius_eq_mid (hx : Monotone x) (h : i ≤ j) (hil : i ≤ l) (hlj : l ≤ j) :
    blockRadius x i j l h = (x j - x i) / 2 + |x l - (x i + x j) / 2| := by
  rw [blockRadius_eq_max hx h hil hlj]
  rcases le_total (x l - x i) (x j - x l) with hc | hc
  · rw [max_eq_right hc, abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left hc, abs_of_nonneg (by linarith)]; ring

/-- **Lemma 1**: an optimal one-center location for a block is a point of the block nearest
to the midpoint of its two endpoints, and the optimal cost is
`c(i,j) = (x j - x i)/2 + min_{i ≤ l ≤ j} |x l - (x i + x j)/2|`. -/
theorem blockCost_eq (hx : Monotone x) (h : i ≤ j) :
    blockCost x i j h
      = (x j - x i) / 2 + (Icc i j).inf' (nonempty_Icc.2 h) fun l => |x l - (x i + x j) / 2| := by
  rw [blockCost, ← inf'_const_add]
  refine Finset.inf'_congr _ rfl fun l hl => ?_
  obtain ⟨hl1, hl2⟩ := mem_Icc.1 hl
  exact blockRadius_eq_mid hx h hl1 hl2

lemma blockCost_le_iff (h : i ≤ j) (r : ℝ) :
    blockCost x i j h ≤ r ↔ ∃ l ∈ Icc i j, ∀ t ∈ Icc i j, |x t - x l| ≤ r := by
  simp [blockCost, blockRadius, Finset.inf'_le_iff, Finset.sup'_le_iff]

/-- A center outside a block can always be replaced by a center of the block, without
increasing any distance to a point of the block: the restriction "the center belongs to
the block" is harmless. -/
lemma exists_center_in_block (hx : Monotone x) (h : i ≤ j) (l : ℕ) :
    ∃ l' ∈ Icc i j, ∀ t ∈ Icc i j, |x t - x l'| ≤ |x t - x l| := by
  rcases lt_trichotomy l i with hli | rfl | hil
  · refine ⟨i, mem_Icc.2 ⟨le_rfl, h⟩, fun t ht => ?_⟩
    obtain ⟨ht1, ht2⟩ := mem_Icc.1 ht
    have h1 : x l ≤ x i := hx hli.le
    have h2 : x i ≤ x t := hx ht1
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · exact ⟨l, mem_Icc.2 ⟨le_rfl, h⟩, fun t _ => le_rfl⟩
  · rcases le_or_gt l j with hlj | hjl
    · -- the center already lies in the block
      exact ⟨l, mem_Icc.2 ⟨hil.le, hlj⟩, fun t _ => le_rfl⟩
    · refine ⟨j, mem_Icc.2 ⟨h, le_rfl⟩, fun t ht => ?_⟩
      obtain ⟨ht1, ht2⟩ := mem_Icc.1 ht
      have h1 : x j ≤ x l := hx hjl.le
      have h2 : x t ≤ x j := hx ht2
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith

/-- **Lemma 5**: removing the leftmost point of a block cannot increase its one-center cost. -/
lemma blockCost_mono_left (hx : Monotone x) (h : i + 1 ≤ j) :
    blockCost x (i + 1) j h ≤ blockCost x i j (by omega) := by
  obtain ⟨l, hl, hlcov⟩ := (blockCost_le_iff (x := x) (by omega : i ≤ j) _).1 le_rfl
  obtain ⟨l', hl', hl'le⟩ := exists_center_in_block (i := i + 1) (j := j) hx h l
  refine (blockCost_le_iff h _).2 ⟨l', hl', fun t ht => ?_⟩
  obtain ⟨ht1, ht2⟩ := mem_Icc.1 ht
  exact le_trans (hl'le t ht) (hlcov t (mem_Icc.2 ⟨by omega, ht2⟩))

/-- **Lemma 5**: adding a point on the right cannot decrease the one-center cost of a block. -/
lemma blockCost_mono_right (hx : Monotone x) (h : i ≤ j) :
    blockCost x i j h ≤ blockCost x i (j + 1) (by omega) := by
  obtain ⟨l, hl, hlcov⟩ := (blockCost_le_iff (x := x) (by omega : i ≤ j + 1) _).1 le_rfl
  obtain ⟨l', hl', hl'le⟩ := exists_center_in_block (i := i) (j := j) hx h l
  refine (blockCost_le_iff h _).2 ⟨l', hl', fun t ht => ?_⟩
  obtain ⟨ht1, ht2⟩ := mem_Icc.1 ht
  exact le_trans (hl'le t ht) (hlcov t (mem_Icc.2 ⟨ht1, by omega⟩))

/-- `CoverPrefix x n j p r` says that the first `j` of the `n` points can be covered with
radius `r` by at most `p` centers chosen among the `n` points. -/
def CoverPrefix (x : ℕ → ℝ) (n j p : ℕ) (r : ℝ) : Prop :=
  ∃ F ⊆ range n, F.card ≤ p ∧ ∀ t < j, ∃ l ∈ F, |x t - x l| ≤ r

/-- **Lemma 4** (dynamic-programming recurrence), in decision form: the prefix
`x 0, …, x m` can be covered with radius `r` by `p + 1` centers if and only if it splits
into a last consecutive block `[i, m]` of one-center cost at most `r` and a prefix
`x 0, …, x (i-1)` coverable with radius `r` by `p` centers. -/
theorem coverPrefix_succ_iff (hx : Monotone x) {n m p : ℕ} (hmn : m < n) (r : ℝ) :
    CoverPrefix x n (m + 1) (p + 1) r ↔
      ∃ i, ∃ him : i ≤ m, blockCost x i m him ≤ r ∧ CoverPrefix x n i p r := by
  constructor
  · rintro ⟨F, hFn, hcard, hcov⟩
    obtain ⟨l₀, hl₀F, hl₀⟩ := hcov m (Nat.lt_succ_self m)
    have hr0 : 0 ≤ r := le_trans (abs_nonneg _) hl₀
    set l := min l₀ m with hldef
    have hlm : l ≤ m := min_le_right _ _
    have hll₀ : l ≤ l₀ := min_le_left _ _
    have hxl : x l ≤ x l₀ := hx hll₀
    have hml : x m - x l ≤ r := by
      rcases le_total l₀ m with hc | hc
      · have : l = l₀ := min_eq_left hc
        rw [this]
        exact le_trans (le_abs_self _) hl₀
      · have : l = m := min_eq_right hc
        rw [this]; linarith
    -- the leftmost point still covered by the center `x l`
    set S := (range (m + 1)).filter fun t => x l - x t ≤ r with hS
    have hlS : l ∈ S := by
      simp only [hS, mem_filter, mem_range]
      exact ⟨by omega, by linarith⟩
    have hSne : S.Nonempty := ⟨l, hlS⟩
    set i := S.min' hSne with hi
    have hiS : i ∈ S := S.min'_mem hSne
    have hil : i ≤ l := S.min'_le l hlS
    have him : i ≤ m := le_trans hil hlm
    have hxi : x l - x i ≤ r := by
      have := (mem_filter.1 hiS).2; simpa using this
    refine ⟨i, him, ?_, ?_⟩
    · refine (blockCost_le_iff him r).2 ⟨l, mem_Icc.2 ⟨hil, hlm⟩, fun t ht => ?_⟩
      obtain ⟨ht1, ht2⟩ := mem_Icc.1 ht
      have h1 : x i ≤ x t := hx ht1
      have h2 : x t ≤ x m := hx ht2
      exact abs_le.2 ⟨by linarith, by linarith⟩
    · refine ⟨F.erase l₀, (F.erase_subset l₀).trans hFn, ?_, ?_⟩
      · have := Finset.card_erase_of_mem hl₀F
        have hpos : 1 ≤ F.card := Finset.card_pos.2 ⟨l₀, hl₀F⟩
        omega
      · intro t ht
        obtain ⟨f, hfF, hf⟩ := hcov t (by omega)
        have hfne : f ≠ l₀ := by
          intro hfe
          subst hfe
          have hts : t ∈ S := by
            simp only [hS, mem_filter, mem_range]
            refine ⟨by omega, ?_⟩
            have : x f - x t ≤ r := by
              rw [abs_sub_comm] at hf
              exact le_trans (le_abs_self _) hf
            linarith
          have := S.min'_le t hts
          omega
        exact ⟨f, Finset.mem_erase.2 ⟨hfne, hfF⟩, hf⟩
  · rintro ⟨i, him, hblock, F₀, hF₀n, hcard₀, hcov₀⟩
    obtain ⟨l, hlmem, hl⟩ := (blockCost_le_iff him r).1 hblock
    obtain ⟨hli, hlm⟩ := mem_Icc.1 hlmem
    refine ⟨insert l F₀, ?_, ?_, ?_⟩
    · exact Finset.insert_subset (mem_range.2 (lt_of_le_of_lt hlm hmn)) hF₀n
    · exact le_trans (Finset.card_insert_le _ _) (by omega)
    · intro t ht
      rcases lt_or_ge t i with htc | htc
      · obtain ⟨f, hf, hfle⟩ := hcov₀ t htc
        exact ⟨f, Finset.mem_insert_of_mem hf, hfle⟩
      · exact ⟨l, Finset.mem_insert_self _ _, hl t (mem_Icc.2 ⟨htc, by omega⟩)⟩

/-- The index formulation `CoverPrefix x n n k r` is exactly the `k`-center feasibility
problem for the point set `X = {x 0, …, x (n-1)}` with radius `r`. -/
theorem coverPrefix_iff_exists_centers (hinj : Function.Injective x) {n k : ℕ} (r : ℝ) :
    CoverPrefix x n n k r ↔
      ∃ F ⊆ (range n).image x, F.card ≤ k ∧
        ∀ y ∈ (range n).image x, ∃ f ∈ F, dist y f ≤ r := by
  constructor
  · rintro ⟨F, hFn, hcard, hcov⟩
    refine ⟨F.image x, Finset.image_subset_image hFn, le_trans (Finset.card_image_le) hcard, ?_⟩
    rintro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨l, hlF, hl⟩ := hcov t (mem_range.1 ht)
    exact ⟨x l, Finset.mem_image_of_mem _ hlF, by rwa [Real.dist_eq]⟩
  · rintro ⟨F, hFsub, hcard, hcov⟩
    refine ⟨(range n).filter fun t => x t ∈ F, Finset.filter_subset _ _, ?_, ?_⟩
    · refine le_trans (Finset.card_le_card_of_injOn x ?_ (fun a _ b _ hab => hinj hab)) hcard
      intro a ha
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
      exact ha.2
    · intro t ht
      obtain ⟨f, hfF, hf⟩ := hcov (x t) (Finset.mem_image_of_mem _ (mem_range.2 ht))
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 (hFsub hfF)
      exact ⟨s, mem_filter.2 ⟨hs, hfF⟩, by rwa [Real.dist_eq] at hf⟩

end Line

end Q764
