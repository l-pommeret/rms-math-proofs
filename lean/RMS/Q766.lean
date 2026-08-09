import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Q766 : optimal `n`-point `L¹` approximation of the values of an integrable function

Let `q : ℝ → ℝ` be nondecreasing on `(0,1)` and integrable on `(0,1)` (the *nondecreasing
rearrangement*, or quantile function, of the integrable function `f` of the problem).  For a
tuple `x : Fin n → ℝ` of centres put

  `Φ(x) = ∫₀¹ min_k |q u - x k| du`.

The main theorem below states that

  `min_x Φ(x) = min_{0 = s₀ ≤ s₁ ≤ ⋯ ≤ sₙ = 1} ∑_{i<n} K(sᵢ, sᵢ₊₁)`,

where `K a b = H a + H b - 2 H ((a+b)/2)` and `H s = ∫₀ˢ q`, both minima being attained, together
with the complete classification of the minimizers: a tuple is optimal iff (after sorting) it is
the tuple of block medians of an optimal partition.

## Contents

* `Q766.min_Phi_eq_min_J` : existence of both minima and equality of their values (Theorem 1,
  formulas (3.1) / (5.2)); the minimum is attained at the block medians `q ((sᵢ₋₁+sᵢ)/2)`.
* `Q766.isMin_of_optimal_partition` / `Q766.optimal_partition_of_isMin` /
  `Q766.monotone_isMin_iff` : the complete classification of the minimizers (§4.4).
* `Q766.Phi_comp_perm`, `Q766.exists_monotone_perm` : permutation invariance, so that the
  classification of monotone minimizers describes all of them.
* `Q766.median_unique_of_continuousOn`, `Q766.isMin_eq_midpoint_values_of_continuous` : for a
  continuous `q`, every nondegenerate block has the *unique* median `q ((a+b)/2)` (§5).
* `Q766.Phi_eq_of_map_eq` : the interface with the original problem — `φ` computed from `f`
  coincides with `Φ` computed from any `q` with the same distribution.
* `Q766.min_Phi_one`, `Q766.min_Phi_one_id` : the case `n = 1` (§8.1) and the affine test case
  (§8.2), where the minimum equals `1/4` for the uniform distribution.

## Relation to the printed statement, and scope

* The printed problem concerns a continuous integrable `f : (0,1) → ℝ`.  Following the audit's
  target, everything is stated for a nondecreasing rearrangement `q` (hypotheses:
  `MonotoneOn q (Ioo 0 1)` and `IntervalIntegrable q volume 0 1`).  The reduction from `f` to `q`
  is provided as the interface lemma `Phi_eq_of_map_eq`, which assumes that `f` and `q` have the
  same pushforward of Lebesgue measure on `(0,1]`; the *construction* of such a `q` from `f`
  (the quantile function) is not formalized here.
* Ordered partitions `0 = s₀ ≤ ⋯ ≤ sₙ = 1` are encoded as nondecreasing sequences `s : ℕ → ℝ`
  with `s 0 = 0` and `s k = 1` for `k ≥ n` (`Q766.Partitions n`), a compact set in the product
  topology.
* "`c` is a median of the block `[a,b]`" is expressed by the (equivalent) equality
  `∫_a^b |q u - c| du = K q a b`, rather than by one-sided limits `q(θ−) ≤ c ≤ q(θ+)`; the
  midpoint value `q ((a+b)/2)` always satisfies it (`integral_abs_sub_median`), and for continuous
  `q` it is the only such `c` on a nondegenerate block (`median_unique_of_continuousOn`).
* Not formalized (explicitly excluded from the audit's first target): the strictness statements
  (5.3) and distinctness of the optimal centres for nonconstant continuous `f`, the decay
  `eₙ → 0` (§8.3), the high-resolution asymptotic (§9) and the nonuniqueness example (§10).

## Versions

Lean `4.28.0`; Mathlib commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
-/

namespace Q766

open MeasureTheory intervalIntegral Set

/-! ## Definitions -/

/-- `H q s = ∫₀ˢ q`. -/
noncomputable def H (q : ℝ → ℝ) (s : ℝ) : ℝ := ∫ u in (0:ℝ)..s, q u

/-- The block cost `K q a b = H a + H b - 2 H ((a+b)/2)`. -/
noncomputable def K (q : ℝ → ℝ) (a b : ℝ) : ℝ := H q a + H q b - 2 * H q ((a + b) / 2)

/-- Distance from `y` to the nearest of the centres `x 0, …, x (n-1)`. -/
noncomputable def nearest {n : ℕ} (x : Fin n → ℝ) (y : ℝ) : ℝ := ⨅ k, |y - x k|

/-- The functional to be minimized: `Φ(x) = ∫₀¹ min_k |q u - x k| du`. -/
noncomputable def Phi (q : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ := ∫ u in (0:ℝ)..1, nearest x (q u)

/-- Ordered partitions `0 = s₀ ≤ s₁ ≤ ⋯ ≤ sₙ = 1` of `[0,1]`, encoded as nondecreasing sequences
`s : ℕ → ℝ` with `s 0 = 0` and `s k = 1` for `k ≥ n`. -/
def Partitions (n : ℕ) : Set (ℕ → ℝ) :=
  {s | s 0 = 0 ∧ (∀ k, n ≤ k → s k = 1) ∧ Monotone s}

/-- The partition cost `J q n s = ∑_{k<n} K q (s k) (s (k+1))`. -/
noncomputable def J (q : ℝ → ℝ) (n : ℕ) (s : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, K q (s k) (s (k + 1))

/-! ## Elementary facts about `nearest` -/

section Nearest

variable {n : ℕ} {x : Fin n → ℝ} {y : ℝ}

lemma nearest_le [Nonempty (Fin n)] (k : Fin n) : nearest x y ≤ |y - x k| :=
  ciInf_le (Finite.bddBelow_range _) k

lemma le_nearest [Nonempty (Fin n)] {c : ℝ} (h : ∀ k, c ≤ |y - x k|) : c ≤ nearest x y := le_ciInf h

lemma nearest_nonneg [Nonempty (Fin n)] : 0 ≤ nearest x y := le_nearest fun _ => abs_nonneg _

lemma exists_nearest [Nonempty (Fin n)] : ∃ k, nearest x y = |y - x k| := by
  obtain ⟨k, hk⟩ := Finite.exists_min fun k => |y - x k|
  exact ⟨k, le_antisymm (nearest_le k) (le_nearest hk)⟩

lemma nearest_lipschitz [Nonempty (Fin n)] (y z : ℝ) :
    |nearest x y - nearest x z| ≤ |y - z| := by
  have key : ∀ u v : ℝ, nearest x u - nearest x v ≤ |u - v| := by
    intro u v
    obtain ⟨k, hk⟩ := exists_nearest (x := x) (y := v)
    have h1 : nearest x u ≤ |u - x k| := nearest_le k
    have h2 : |u - x k| ≤ |u - v| + |v - x k| :=
      calc |u - x k| = |(u - v) + (v - x k)| := by ring_nf
        _ ≤ |u - v| + |v - x k| := abs_add_le _ _
    rw [hk]; linarith
  rw [abs_sub_le_iff]
  exact ⟨key y z, by rw [abs_sub_comm]; exact key z y⟩

lemma continuous_nearest [Nonempty (Fin n)] : Continuous (nearest x) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simpa [Real.dist_eq] using nearest_lipschitz (x := x) u v

/-- `Φ` only depends on the set of centres: it is invariant under permutations. -/
lemma nearest_comp_perm (σ : Equiv.Perm (Fin n)) : nearest (x ∘ σ) y = nearest x y := by
  simp only [nearest, Function.comp_apply]
  exact σ.iInf_comp (g := fun k => |y - x k|)

end Nearest

/-! ## Integrability -/

section Integrability

variable {q : ℝ → ℝ}

lemma intInt_sub (hint : IntervalIntegrable q volume 0 1) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) : IntervalIntegrable q volume a b := by
  apply hint.mono_set
  rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact Set.Icc_subset_Icc ha hb

lemma intInt_abs_sub (hint : IntervalIntegrable q volume 0 1) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    IntervalIntegrable (fun t => |q t - c|) volume a b :=
  ((intInt_sub hint ha hb hab).sub _root_.intervalIntegrable_const).abs

lemma intInt_nearest {n : ℕ} [Nonempty (Fin n)] {x : Fin n → ℝ}
    (hint : IntervalIntegrable q volume 0 1) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    IntervalIntegrable (fun u => nearest x (q u)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hq : IntegrableOn q (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 (intInt_sub hint ha hb hab)
  apply MeasureTheory.Integrable.mono' (g := fun u => |q u - x (Classical.arbitrary (Fin n))|)
  · exact (hq.sub (by apply integrableOn_const <;> simp)).abs
  · exact continuous_nearest.comp_aestronglyMeasurable hq.aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg nearest_nonneg]
    exact nearest_le _

end Integrability

/-! ## The one-centre (median) problem on a block -/

section Block

variable {q : ℝ → ℝ}

lemma H_sub (hint : IntervalIntegrable q volume 0 1) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) : (∫ u in a..b, q u) = H q b - H q a := by
  have := intervalIntegral.integral_add_adjacent_intervals
    (a := (0:ℝ)) (b := a) (c := b) (f := q) (μ := volume)
    (intInt_sub hint le_rfl hb (le_trans ha hab) |>.mono_set (by
      rw [Set.uIcc_of_le ha, Set.uIcc_of_le (le_trans ha hab)]
      exact Set.Icc_subset_Icc le_rfl hab))
    (intInt_sub hint ha hb hab)
  simp only [H] at this ⊢
  linarith [this]

/-- Splitting of the block cost at the midpoint. -/
lemma split_K (hint : IntervalIntegrable q volume 0 1) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (c : ℝ) :
    (∫ u in a..(a + b) / 2, (c - q u)) + (∫ u in (a + b) / 2..b, (q u - c)) = K q a b := by
  set m := (a + b) / 2 with hm
  have ham : a ≤ m := by rw [hm]; linarith
  have hmb : m ≤ b := by rw [hm]; linarith
  have hm0 : 0 ≤ m := le_trans ha ham
  have hm1 : m ≤ 1 := le_trans hmb hb
  have iam : IntervalIntegrable q volume a m := intInt_sub hint ha hm1 ham
  have imb : IntervalIntegrable q volume m b := intInt_sub hint hm0 hb hmb
  have e1 : (∫ u in a..m, (c - q u)) = c * (m - a) - (H q m - H q a) := by
    rw [intervalIntegral.integral_sub _root_.intervalIntegrable_const iam, H_sub hint ha hm1 ham]
    simp [mul_comm]
  have e2 : (∫ u in m..b, (q u - c)) = (H q b - H q m) - c * (b - m) := by
    rw [intervalIntegral.integral_sub imb _root_.intervalIntegrable_const, H_sub hint hm0 hb hmb]
    simp [mul_comm]
  have hlen : c * (m - a) = c * (b - m) := by rw [hm]; ring
  have hK : K q a b = H q a + H q b - 2 * H q m := by rw [K, ← hm]
  rw [e1, e2, hK]
  linarith

/-- Lower bound for the one-centre cost on a block: **no** monotonicity is needed. -/
lemma K_le_integral (hint : IntervalIntegrable q volume 0 1) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (c : ℝ) :
    K q a b ≤ ∫ u in a..b, |q u - c| := by
  set m := (a + b) / 2 with hm
  have ham : a ≤ m := by rw [hm]; linarith
  have hmb : m ≤ b := by rw [hm]; linarith
  have hm0 : 0 ≤ m := le_trans ha ham
  have hm1 : m ≤ 1 := le_trans hmb hb
  have iam : IntervalIntegrable q volume a m := intInt_sub hint ha hm1 ham
  have imb : IntervalIntegrable q volume m b := intInt_sub hint hm0 hb hmb
  have h1 : (∫ u in a..m, (c - q u)) ≤ ∫ u in a..m, |q u - c| := by
    apply intervalIntegral.integral_mono_on ham
      (IntervalIntegrable.sub _root_.intervalIntegrable_const iam) (intInt_abs_sub hint ha hm1 ham)
    intro u _
    linarith [neg_le_abs (q u - c)]
  have h2 : (∫ u in m..b, (q u - c)) ≤ ∫ u in m..b, |q u - c| := by
    apply intervalIntegral.integral_mono_on hmb
      (IntervalIntegrable.sub imb _root_.intervalIntegrable_const) (intInt_abs_sub hint hm0 hb hmb)
    intro u _
    exact le_abs_self _
  have hsplit : (∫ u in a..m, |q u - c|) + (∫ u in m..b, |q u - c|) = ∫ u in a..b, |q u - c| :=
    intervalIntegral.integral_add_adjacent_intervals (intInt_abs_sub hint ha hm1 ham)
      (intInt_abs_sub hint hm0 hb hmb)
  have hK := split_K hint ha hab hb c
  rw [← hm] at hK
  rw [← hK, ← hsplit]
  linarith

/-- The midpoint value `q ((a+b)/2)` is a median of the block `[a,b]`: it realises the value
`K q a b`. -/
lemma integral_abs_sub_median (hmono : MonotoneOn q (Set.Ioo 0 1))
    (hint : IntervalIntegrable q volume 0 1) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ u in a..b, |q u - q ((a + b) / 2)|) = K q a b := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp only [K]
    ring_nf
    simp
  set m := (a + b) / 2 with hm
  have ham : a < m := by rw [hm]; linarith
  have hmb : m < b := by rw [hm]; linarith
  have hm0 : (0:ℝ) < m := lt_of_le_of_lt ha ham
  have hm1 : m < 1 := lt_of_lt_of_le hmb hb
  have hmIoo : m ∈ Set.Ioo (0:ℝ) 1 := ⟨hm0, hm1⟩
  set c := q m with hc
  have iam : IntervalIntegrable q volume a m := intInt_sub hint ha hm1.le ham.le
  have imb : IntervalIntegrable q volume m b := intInt_sub hint hm0.le hb hmb.le
  have e1 : (∫ u in a..m, |q u - c|) = ∫ u in a..m, (c - q u) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with u hu
    rw [Set.uIoc_of_le ham.le] at hu
    have huIoo : u ∈ Set.Ioo (0:ℝ) 1 := ⟨lt_of_le_of_lt ha hu.1, lt_of_le_of_lt hu.2 hm1⟩
    have : q u ≤ c := hmono huIoo hmIoo hu.2
    rw [abs_of_nonpos (by linarith)]
    ring
  have e2 : (∫ u in m..b, |q u - c|) = ∫ u in m..b, (q u - c) := by
    apply intervalIntegral.integral_congr_ae
    have h1ne : ∀ᵐ u : ℝ, u ≠ 1 := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [h1ne] with u hu1 hu
    rw [Set.uIoc_of_le hmb.le] at hu
    have huIoo : u ∈ Set.Ioo (0:ℝ) 1 :=
      ⟨lt_trans hm0 hu.1, lt_of_le_of_ne (le_trans hu.2 hb) hu1⟩
    have : c ≤ q u := hmono hmIoo huIoo hu.1.le
    rw [abs_of_nonneg (by linarith)]
  have hsplit : (∫ u in a..m, |q u - c|) + (∫ u in m..b, |q u - c|) = ∫ u in a..b, |q u - c| :=
    intervalIntegral.integral_add_adjacent_intervals
      ((iam.sub _root_.intervalIntegrable_const).abs)
      ((imb.sub _root_.intervalIntegrable_const).abs)
  have f1 : (∫ u in a..m, (c - q u)) = c * (m - a) - (H q m - H q a) := by
    rw [intervalIntegral.integral_sub _root_.intervalIntegrable_const iam,
      H_sub hint ha hm1.le ham.le]
    simp [mul_comm]
  have f2 : (∫ u in m..b, (q u - c)) = (H q b - H q m) - c * (b - m) := by
    rw [intervalIntegral.integral_sub imb _root_.intervalIntegrable_const,
      H_sub hint hm0.le hb hmb.le]
    simp [mul_comm]
  have hlen : c * (m - a) = c * (b - m) := by rw [hm]; ring
  have hK : K q a b = H q a + H q b - 2 * H q m := by rw [K, ← hm]
  rw [← hsplit, e1, e2, f1, f2, hK]
  linarith

/-- For a **continuous** nondecreasing `q`, the median of a nondegenerate block is unique: the only
centre realising the block cost `K q a b` is the midpoint value `q ((a+b)/2)` (§5). -/
theorem median_unique_of_continuousOn (hcont : ContinuousOn q (Set.Ioo 0 1))
    (hint : IntervalIntegrable q volume 0 1) {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : (∫ u in a..b, |q u - c|) = K q a b) : c = q ((a + b) / 2) := by
  set m := (a + b) / 2 with hm
  have ham : a < m := by rw [hm]; linarith
  have hmb : m < b := by rw [hm]; linarith
  have hm0 : (0:ℝ) < m := lt_of_le_of_lt ha ham
  have hm1 : m < 1 := lt_of_lt_of_le hmb hb
  have hmIoo : m ∈ Set.Ioo (0:ℝ) 1 := ⟨hm0, hm1⟩
  have hdelta : ∀ ε > 0, ∃ δ > 0, ∀ u ∈ Set.Ioo (0:ℝ) 1, |u - m| < δ → |q u - q m| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := Metric.continuousWithinAt_iff.1 (hcont m hmIoo) ε hε
    exact ⟨δ, hδ, fun u hu hd => by
      simpa [Real.dist_eq] using h hu (by simpa [Real.dist_eq] using hd)⟩
  have iam : IntervalIntegrable q volume a m := intInt_sub hint ha hm1.le ham.le
  have imb : IntervalIntegrable q volume m b := intInt_sub hint hm0.le hb hmb.le
  have habs_am := intInt_abs_sub (c := c) hint ha hm1.le ham.le
  have habs_mb := intInt_abs_sub (c := c) hint hm0.le hb hmb.le
  have hsplit : (∫ u in a..m, |q u - c|) + (∫ u in m..b, |q u - c|) = ∫ u in a..b, |q u - c| :=
    intervalIntegral.integral_add_adjacent_intervals habs_am habs_mb
  have hK := split_K hint ha hab.le hb c
  rw [← hm] at hK
  have hL1 : (∫ u in a..m, (c - q u)) ≤ ∫ u in a..m, |q u - c| := by
    apply intervalIntegral.integral_mono_on ham.le
      (IntervalIntegrable.sub _root_.intervalIntegrable_const iam) habs_am
    intro u _
    linarith [neg_le_abs (q u - c)]
  have hL2 : (∫ u in m..b, (q u - c)) ≤ ∫ u in m..b, |q u - c| := by
    apply intervalIntegral.integral_mono_on hmb.le
      (IntervalIntegrable.sub imb _root_.intervalIntegrable_const) habs_mb
    intro u _
    exact le_abs_self _
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `c < q m` : a strictly positive deficit appears just to the left of the midpoint
    obtain ⟨δ, hδ, hδp⟩ := hdelta ((q m - c) / 2) (by linarith)
    set e := m - min (δ / 2) ((m - a) / 2) with he
    have hminpos : 0 < min (δ / 2) ((m - a) / 2) := lt_min (by linarith) (by linarith)
    have hem : e < m := by rw [he]; linarith
    have hae : a < e := by
      have h2 : min (δ / 2) ((m - a) / 2) ≤ (m - a) / 2 := min_le_right _ _
      rw [he]; linarith
    have hpt : ∀ u ∈ Set.Icc e m, (q m - c) ≤ |q u - c| - (c - q u) := by
      intro u hu
      have huIoo : u ∈ Set.Ioo (0:ℝ) 1 :=
        ⟨lt_of_lt_of_le (lt_of_le_of_lt ha hae) hu.1, lt_of_le_of_lt hu.2 hm1⟩
      have hdist : |u - m| < δ := by
        have h1 : m - u ≤ m - e := by linarith [hu.1]
        have h2 : m - e ≤ δ / 2 := by
          have : min (δ / 2) ((m - a) / 2) ≤ δ / 2 := min_le_left _ _
          rw [he]; linarith
        rw [abs_of_nonpos (by linarith [hu.2])]
        linarith
      have hb2 := abs_lt.1 (hδp u huIoo hdist)
      have hqu : c < q u := by linarith [hb2.1]
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ q u - c)]
      linarith [hb2.1]
    have hgap : (m - e) * (q m - c) ≤ ∫ u in e..m, (|q u - c| - (c - q u)) := by
      have h1 : (∫ _u in e..m, (q m - c)) ≤ ∫ u in e..m, (|q u - c| - (c - q u)) := by
        refine intervalIntegral.integral_mono_on hem.le _root_.intervalIntegrable_const ?_ hpt
        exact (intInt_abs_sub hint (le_of_lt (lt_of_le_of_lt ha hae)) hm1.le hem.le).sub
          (IntervalIntegrable.sub _root_.intervalIntegrable_const
            (intInt_sub hint (le_of_lt (lt_of_le_of_lt ha hae)) hm1.le hem.le))
      have h2 : (∫ _u in e..m, (q m - c)) = (m - e) * (q m - c) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      linarith
    have hrest : 0 ≤ ∫ u in a..e, (|q u - c| - (c - q u)) :=
      intervalIntegral.integral_nonneg hae.le fun u _ => by linarith [neg_le_abs (q u - c)]
    have hadd : (∫ u in a..e, (|q u - c| - (c - q u))) + (∫ u in e..m, (|q u - c| - (c - q u)))
        = ∫ u in a..m, (|q u - c| - (c - q u)) := by
      refine intervalIntegral.integral_add_adjacent_intervals ?_ ?_
      · exact (intInt_abs_sub hint ha (hem.trans hm1).le hae.le).sub
          (IntervalIntegrable.sub _root_.intervalIntegrable_const
            (intInt_sub hint ha (hem.trans hm1).le hae.le))
      · exact (intInt_abs_sub hint (le_of_lt (lt_of_le_of_lt ha hae)) hm1.le hem.le).sub
          (IntervalIntegrable.sub _root_.intervalIntegrable_const
            (intInt_sub hint (le_of_lt (lt_of_le_of_lt ha hae)) hm1.le hem.le))
    have hsub : (∫ u in a..m, (|q u - c| - (c - q u)))
        = (∫ u in a..m, |q u - c|) - ∫ u in a..m, (c - q u) :=
      intervalIntegral.integral_sub habs_am
        (IntervalIntegrable.sub _root_.intervalIntegrable_const iam)
    have hpos : 0 < (m - e) * (q m - c) := mul_pos (by linarith) (by linarith)
    have : K q a b < ∫ u in a..b, |q u - c| := by
      rw [← hK, ← hsplit]
      linarith
    linarith [hc.ge, hc.le, this]
  · -- `c > q m` : a strictly positive deficit appears just to the right of the midpoint
    obtain ⟨δ, hδ, hδp⟩ := hdelta ((c - q m) / 2) (by linarith)
    set e := m + min (δ / 2) ((b - m) / 2) with he
    have hminpos : 0 < min (δ / 2) ((b - m) / 2) := lt_min (by linarith) (by linarith)
    have hme : m < e := by rw [he]; linarith
    have heb : e < b := by
      have h2 : min (δ / 2) ((b - m) / 2) ≤ (b - m) / 2 := min_le_right _ _
      rw [he]; linarith
    have hpt : ∀ u ∈ Set.Icc m e, (c - q m) ≤ |q u - c| - (q u - c) := by
      intro u hu
      have huIoo : u ∈ Set.Ioo (0:ℝ) 1 :=
        ⟨lt_of_lt_of_le hm0 hu.1, lt_of_lt_of_le (lt_of_le_of_lt hu.2 heb) hb⟩
      have hdist : |u - m| < δ := by
        have h1 : u - m ≤ e - m := by linarith [hu.2]
        have h2 : e - m ≤ δ / 2 := by
          have : min (δ / 2) ((b - m) / 2) ≤ δ / 2 := min_le_left _ _
          rw [he]; linarith
        rw [abs_of_nonneg (by linarith [hu.1])]
        linarith
      have hb2 := abs_lt.1 (hδp u huIoo hdist)
      have hqu : q u < c := by linarith [hb2.2]
      rw [abs_of_nonpos (by linarith : q u - c ≤ 0)]
      linarith [hb2.2]
    have hgap : (e - m) * (c - q m) ≤ ∫ u in m..e, (|q u - c| - (q u - c)) := by
      have h1 : (∫ _u in m..e, (c - q m)) ≤ ∫ u in m..e, (|q u - c| - (q u - c)) := by
        refine intervalIntegral.integral_mono_on hme.le _root_.intervalIntegrable_const ?_ hpt
        exact (intInt_abs_sub hint hm0.le (le_trans heb.le hb) hme.le).sub
          (IntervalIntegrable.sub (intInt_sub hint hm0.le (le_trans heb.le hb) hme.le)
            _root_.intervalIntegrable_const)
      have h2 : (∫ _u in m..e, (c - q m)) = (e - m) * (c - q m) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      linarith
    have hrest : 0 ≤ ∫ u in e..b, (|q u - c| - (q u - c)) :=
      intervalIntegral.integral_nonneg heb.le fun u _ => by linarith [le_abs_self (q u - c)]
    have hadd : (∫ u in m..e, (|q u - c| - (q u - c))) + (∫ u in e..b, (|q u - c| - (q u - c)))
        = ∫ u in m..b, (|q u - c| - (q u - c)) := by
      refine intervalIntegral.integral_add_adjacent_intervals ?_ ?_
      · exact (intInt_abs_sub hint hm0.le (le_trans heb.le hb) hme.le).sub
          (IntervalIntegrable.sub (intInt_sub hint hm0.le (le_trans heb.le hb) hme.le)
            _root_.intervalIntegrable_const)
      · exact (intInt_abs_sub hint (le_of_lt (lt_trans hm0 hme)) hb heb.le).sub
          (IntervalIntegrable.sub (intInt_sub hint (le_of_lt (lt_trans hm0 hme)) hb heb.le)
            _root_.intervalIntegrable_const)
    have hsub : (∫ u in m..b, (|q u - c| - (q u - c)))
        = (∫ u in m..b, |q u - c|) - ∫ u in m..b, (q u - c) :=
      intervalIntegral.integral_sub habs_mb
        (IntervalIntegrable.sub imb _root_.intervalIntegrable_const)
    have hpos : 0 < (e - m) * (c - q m) := mul_pos (by linarith) (by linarith)
    have : K q a b < ∫ u in a..b, |q u - c| := by
      rw [← hK, ← hsplit]
      linarith
    linarith [hc.ge, hc.le, this]

end Block

/-! ## Partitions -/

section PartitionBasics

variable {n : ℕ} {s : ℕ → ℝ}

lemma Partitions.nonneg (hs : s ∈ Partitions n) (k : ℕ) : 0 ≤ s k := by
  have := hs.2.2 (Nat.zero_le k)
  rw [hs.1] at this
  exact this

lemma Partitions.le_one (hs : s ∈ Partitions n) (k : ℕ) : s k ≤ 1 := by
  have h1 : s k ≤ s (max k n) := hs.2.2 (le_max_left _ _)
  rw [hs.2.1 _ (le_max_right k n)] at h1
  exact h1

lemma Partitions.mono (hs : s ∈ Partitions n) : Monotone s := hs.2.2

end PartitionBasics

/-! ## The two inequalities -/

section Main

variable {q : ℝ → ℝ} {n : ℕ}

/-- Upper bound (§4.3 of the solution): for any partition and any choice of one centre per block,
`Φ` is at most the sum of the block costs. -/
lemma Phi_eq_sum_blocks [Nonempty (Fin n)] (hint : IntervalIntegrable q volume 0 1)
    {s : ℕ → ℝ} (hs : s ∈ Partitions n) (c : Fin n → ℝ) :
    Phi q c = ∑ k ∈ Finset.range n, ∫ u in s k..s (k + 1), nearest c (q u) := by
  rw [Phi, intervalIntegral.sum_integral_adjacent_intervals
    (f := fun u => nearest c (q u)) (a := s) (n := n) (μ := volume)
    (fun k _ => intInt_nearest hint (Partitions.nonneg hs _) (Partitions.le_one hs _)
      (Partitions.mono hs (Nat.le_succ _))), hs.1, hs.2.1 n le_rfl]

lemma Phi_le_sum_blocks [Nonempty (Fin n)] (hint : IntervalIntegrable q volume 0 1)
    {s : ℕ → ℝ} (hs : s ∈ Partitions n) (c : Fin n → ℝ) :
    Phi q c ≤ ∑ k : Fin n, ∫ u in s k..s ((k : ℕ) + 1), |q u - c k| := by
  rw [Phi_eq_sum_blocks hint hs c,
    ← Fin.sum_univ_eq_sum_range (fun k => ∫ u in s k..s (k + 1), nearest c (q u))]
  refine Finset.sum_le_sum fun k _ => ?_
  refine intervalIntegral.integral_mono_on (Partitions.mono hs (Nat.le_succ _))
    (intInt_nearest hint (Partitions.nonneg hs _) (Partitions.le_one hs _)
      (Partitions.mono hs (Nat.le_succ _)))
    (intInt_abs_sub hint (Partitions.nonneg hs _) (Partitions.le_one hs _)
      (Partitions.mono hs (Nat.le_succ _))) (fun u _ => nearest_le k)

lemma abs_le_abs_left_of_mid {a c y : ℝ} (hac : a ≤ c) (hy : (a + c) / 2 ≤ y) :
    |y - c| ≤ |y - a| := by
  rcases abs_cases (y - c) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases abs_cases (y - a) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> rw [h1, h2] <;> linarith

lemma abs_le_abs_right_of_mid {c b y : ℝ} (hcb : c ≤ b) (hy : y ≤ (c + b) / 2) :
    |y - c| ≤ |y - b| := by
  rcases abs_cases (y - c) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases abs_cases (y - b) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> rw [h1, h2] <;> linarith

/-- If `y` lies in the Voronoi cell of the centre `x k` (for a nondecreasing tuple of centres),
then the nearest centre to `y` is `x k`. -/
lemma nearest_eq_of_between [Nonempty (Fin n)] {x : Fin n → ℝ} (hx : Monotone x)
    (k : Fin n) (y : ℝ)
    (hleft : ∀ j : Fin n, (j : ℕ) < (k : ℕ) → (x j + x k) / 2 ≤ y)
    (hright : ∀ j : Fin n, (k : ℕ) < (j : ℕ) → y ≤ (x k + x j) / 2) :
    nearest x y = |y - x k| := by
  refine le_antisymm (nearest_le k) (le_nearest fun j => ?_)
  rcases lt_trichotomy (j : ℕ) (k : ℕ) with h | h | h
  · exact abs_le_abs_left_of_mid (hx (Fin.le_def.2 h.le)) (hleft j h)
  · have : j = k := Fin.ext h
    rw [this]
  · exact abs_le_abs_right_of_mid (hx (Fin.le_def.2 h.le)) (hright j h)

/-- The crossing level `cross q b = sup {u ∈ (0,1) : q u ≤ b}` (with the convention that the
supremum is at least `0`). -/
noncomputable def cross (q : ℝ → ℝ) (b : ℝ) : ℝ :=
  sSup (insert (0:ℝ) {u | u ∈ Set.Ioo (0:ℝ) 1 ∧ q u ≤ b})

lemma cross_bddAbove (b : ℝ) :
    BddAbove (insert (0:ℝ) {u | u ∈ Set.Ioo (0:ℝ) 1 ∧ q u ≤ b}) := by
  refine ⟨1, ?_⟩
  rintro u hu
  rcases hu with rfl | ⟨hu, _⟩
  · norm_num
  · exact hu.2.le

lemma cross_nonneg (b : ℝ) : 0 ≤ cross q b :=
  le_csSup (cross_bddAbove b) (Set.mem_insert _ _)

lemma cross_le_one (b : ℝ) : cross q b ≤ 1 := by
  refine csSup_le ⟨0, Set.mem_insert _ _⟩ ?_
  rintro u (rfl | ⟨hu, _⟩)
  · norm_num
  · exact hu.2.le

lemma cross_mono {b b' : ℝ} (h : b ≤ b') : cross q b ≤ cross q b' := by
  refine csSup_le_csSup (cross_bddAbove b') ⟨0, Set.mem_insert _ _⟩ ?_
  rintro u (rfl | ⟨hu, hqu⟩)
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨hu, le_trans hqu h⟩

lemma le_of_lt_cross (hmono : MonotoneOn q (Set.Ioo 0 1)) {b u : ℝ}
    (hu : u ∈ Set.Ioo (0:ℝ) 1) (h : u < cross q b) : q u ≤ b := by
  obtain ⟨v, hv, huv⟩ := exists_lt_of_lt_csSup ⟨0, Set.mem_insert _ _⟩ h
  rcases hv with rfl | ⟨hv, hqv⟩
  · exact absurd huv (not_lt.2 hu.1.le)
  · exact le_trans (hmono hu hv huv.le) hqv

lemma lt_of_cross_lt {b u : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) 1) (h : cross q b < u) : b < q u := by
  by_contra hcon
  push_neg at hcon
  exact absurd (le_csSup (cross_bddAbove b) (Set.mem_insert_of_mem _ ⟨hu, hcon⟩)) (not_le.2 h)

/-- Sharp decomposition (§4.2): for a nondecreasing tuple of centres, `Φ` is exactly the sum of the
one-centre costs over the blocks of the induced (nearest-centre) partition. -/
lemma exists_partition_blocks [Nonempty (Fin n)] (hmono : MonotoneOn q (Set.Ioo 0 1))
    (hint : IntervalIntegrable q volume 0 1) {x : Fin n → ℝ} (hx : Monotone x) :
    ∃ s ∈ Partitions n, Phi q x = ∑ k : Fin n, ∫ u in s k..s ((k : ℕ) + 1), |q u - x k| := by
  have hn : 0 < n := Fin.pos'
  -- the centres, extended to a nondecreasing sequence indexed by `ℕ`
  set xe : ℕ → ℝ := fun k => x ⟨min k (n - 1), by omega⟩ with hxe
  have hxe_mono : Monotone xe := by
    intro i j hij
    exact hx (Fin.le_def.2 (by simp; omega))
  have hxe_eq : ∀ k : Fin n, xe (k : ℕ) = x k := by
    intro k
    have hk : min (k : ℕ) (n - 1) = (k : ℕ) := by omega
    simp only [hxe]
    congr 1
    exact Fin.ext hk
  -- the Voronoi boundaries and the induced partition
  set bd : ℕ → ℝ := fun k => (xe (k - 1) + xe k) / 2 with hbd
  have hbd_mono : Monotone bd := by
    intro i j hij
    have h1 : xe (i - 1) ≤ xe (j - 1) := hxe_mono (by omega)
    have h2 : xe i ≤ xe j := hxe_mono hij
    simp only [hbd]
    linarith
  set s : ℕ → ℝ := fun k => if k = 0 then 0 else if n ≤ k then 1 else cross q (bd k) with hsdef
  have hs0 : s 0 = 0 := by simp [hsdef]
  have hs_nonneg : ∀ k, 0 ≤ s k := by
    intro k
    simp only [hsdef]
    split_ifs
    · exact le_rfl
    · norm_num
    · exact cross_nonneg _
  have hs_le_one : ∀ k, s k ≤ 1 := by
    intro k
    simp only [hsdef]
    split_ifs
    · norm_num
    · exact le_rfl
    · exact cross_le_one _
  have hs_top : ∀ k, n ≤ k → s k = 1 := by
    intro k hk
    have hk0 : k ≠ 0 := by omega
    simp [hsdef, hk0, hk]
  have hs_mono : Monotone s := by
    intro i j hij
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [hs0]; exact hs_nonneg j
    have hi0 : i ≠ 0 := by omega
    have hj0 : j ≠ 0 := by omega
    by_cases hin : n ≤ i
    · rw [hs_top i hin, hs_top j (le_trans hin hij)]
    by_cases hjn : n ≤ j
    · rw [hs_top j hjn]; exact hs_le_one i
    · simp only [hsdef, if_neg hi0, if_neg hj0, if_neg hin, if_neg hjn]
      exact cross_mono (hbd_mono hij)
  have hs : s ∈ Partitions n := ⟨hs0, hs_top, hs_mono⟩
  refine ⟨s, hs, ?_⟩
  rw [Phi_eq_sum_blocks hint hs x,
    ← Fin.sum_univ_eq_sum_range (fun k => ∫ u in s k..s (k + 1), nearest x (q u))]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine intervalIntegral.integral_congr_ae ?_
  have hne1 : ∀ᵐ u : ℝ, u ≠ s ((k : ℕ) + 1) := by rw [MeasureTheory.ae_iff]; simp
  have hne2 : ∀ᵐ u : ℝ, u ≠ (1:ℝ) := by rw [MeasureTheory.ae_iff]; simp
  filter_upwards [hne1, hne2] with u hu1 hu2 humem
  rw [Set.uIoc_of_le (hs_mono (Nat.le_succ (k : ℕ)))] at humem
  have hult : u < s ((k : ℕ) + 1) := lt_of_le_of_ne humem.2 hu1
  have huIoo : u ∈ Set.Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_lt (hs_nonneg (k : ℕ)) humem.1,
      lt_of_le_of_ne (le_trans humem.2 (hs_le_one _)) hu2⟩
  refine nearest_eq_of_between hx k (q u) ?_ ?_
  · intro j hjk
    have hk0 : (k : ℕ) ≠ 0 := by omega
    have hkn : ¬ n ≤ (k : ℕ) := by omega
    have hsk : s (k : ℕ) = cross q (bd (k : ℕ)) := by simp [hsdef, hk0, hkn]
    have hqu : bd (k : ℕ) < q u := lt_of_cross_lt huIoo (by rw [← hsk]; exact humem.1)
    have hxj : x j ≤ xe ((k : ℕ) - 1) := by
      rw [← hxe_eq j]
      exact hxe_mono (by omega)
    have hxk : x k = xe (k : ℕ) := (hxe_eq k).symm
    simp only [hbd] at hqu
    rw [hxk]
    linarith
  · intro j hkj
    have hk1n : (k : ℕ) + 1 < n := by omega
    have hk10 : (k : ℕ) + 1 ≠ 0 := by omega
    have hsk1 : s ((k : ℕ) + 1) = cross q (bd ((k : ℕ) + 1)) := by
      simp [hsdef, Nat.not_le.2 hk1n]
    have hqu : q u ≤ bd ((k : ℕ) + 1) := le_of_lt_cross hmono huIoo (by rw [← hsk1]; exact hult)
    have hxj : xe ((k : ℕ) + 1) ≤ x j := by
      rw [← hxe_eq j]
      exact hxe_mono (by omega)
    have hxk : x k = xe (k : ℕ) := (hxe_eq k).symm
    simp only [hbd] at hqu
    simp only [Nat.add_sub_cancel] at hqu
    rw [hxk]
    linarith

/-- Every block cost is bounded below by `K`, hence `J q n s ≤ Φ` along any decomposition. -/
lemma J_le_sum_blocks (hint : IntervalIntegrable q volume 0 1) {s : ℕ → ℝ}
    (hs : s ∈ Partitions n) (c : Fin n → ℝ) :
    J q n s ≤ ∑ k : Fin n, ∫ u in s k..s ((k : ℕ) + 1), |q u - c k| := by
  rw [J, ← Fin.sum_univ_eq_sum_range fun k => K q (s k) (s (k + 1))]
  refine Finset.sum_le_sum fun k _ => K_le_integral hint (Partitions.nonneg hs _)
    (Partitions.mono hs (Nat.le_succ _)) (Partitions.le_one hs _) _
end Main

/-! ## Existence of an optimal partition -/

section Compactness

variable {q : ℝ → ℝ} {n : ℕ}

lemma isClosed_Partitions : IsClosed (Partitions n) := by
  have h1 : IsClosed {s : ℕ → ℝ | s 0 = 0} := isClosed_eq (continuous_apply 0) continuous_const
  have h2 : IsClosed {s : ℕ → ℝ | ∀ k, n ≤ k → s k = 1} := by
    have he : {s : ℕ → ℝ | ∀ k, n ≤ k → s k = 1}
        = ⋂ k : ℕ, ⋂ _ : n ≤ k, {s : ℕ → ℝ | s k = 1} := by
      ext s; simp
    rw [he]
    exact isClosed_iInter fun k => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply k) continuous_const
  have h3 : IsClosed {s : ℕ → ℝ | Monotone s} := by
    have he : {s : ℕ → ℝ | Monotone s}
        = ⋂ i : ℕ, ⋂ j : ℕ, ⋂ _ : i ≤ j, {s : ℕ → ℝ | s i ≤ s j} := by
      ext s; simp [Monotone]
    rw [he]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply i) (continuous_apply j)
  have he : Partitions n
      = {s : ℕ → ℝ | s 0 = 0} ∩ ({s : ℕ → ℝ | ∀ k, n ≤ k → s k = 1} ∩ {s : ℕ → ℝ | Monotone s}) := by
    ext s; simp [Partitions]
  rw [he]
  exact h1.inter (h2.inter h3)

lemma isCompact_Partitions : IsCompact (Partitions n) := by
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ : ℕ => isCompact_Icc
    (a := (0:ℝ)) (b := 1)) isClosed_Partitions ?_
  intro s hs i _
  exact ⟨Partitions.nonneg hs i, Partitions.le_one hs i⟩

lemma continuousOn_H (hint : IntervalIntegrable q volume 0 1) :
    ContinuousOn (H q) (Set.Icc 0 1) := by
  have hI : IntegrableOn q (Set.uIcc (0:ℝ) 1) volume := (intervalIntegrable_iff' (by simp)).1 hint
  have h := intervalIntegral.continuousOn_primitive_interval (a := (0:ℝ)) (b := 1)
    (f := q) (μ := volume) hI
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h
  exact h

lemma continuousOn_J (hint : IntervalIntegrable q volume 0 1) :
    ContinuousOn (J q n) (Partitions n) := by
  have key : ∀ g : (ℕ → ℝ) → ℝ, ContinuousOn g (Partitions n) →
      (∀ s ∈ Partitions n, g s ∈ Set.Icc (0:ℝ) 1) →
      ContinuousOn (fun s => H q (g s)) (Partitions n) := by
    intro g hg hmaps
    exact (continuousOn_H hint).comp hg hmaps
  refine continuousOn_finset_sum _ fun k _ => ?_
  simp only [K]
  have hA : ContinuousOn (fun s : ℕ → ℝ => H q (s k)) (Partitions n) :=
    key _ (Continuous.continuousOn (continuous_apply k))
      (fun s hs => ⟨Partitions.nonneg hs k, Partitions.le_one hs k⟩)
  have hB : ContinuousOn (fun s : ℕ → ℝ => H q (s (k + 1))) (Partitions n) :=
    key _ (Continuous.continuousOn (continuous_apply (k + 1)))
      (fun s hs => ⟨Partitions.nonneg hs _, Partitions.le_one hs _⟩)
  have hC : ContinuousOn (fun s : ℕ → ℝ => H q ((s k + s (k + 1)) / 2)) (Partitions n) := by
    refine key _ (((continuous_apply k).add (continuous_apply (k + 1))).div_const 2).continuousOn ?_
    intro s hs
    have h1 := Partitions.nonneg hs k
    have h2 := Partitions.nonneg hs (k + 1)
    have h3 := Partitions.le_one hs k
    have h4 := Partitions.le_one hs (k + 1)
    exact ⟨by linarith, by linarith⟩
  exact (hA.add hB).sub (continuousOn_const.mul hC)

lemma exists_min_J (hn : 0 < n) (hint : IntervalIntegrable q volume 0 1) :
    ∃ s ∈ Partitions n, ∀ t ∈ Partitions n, J q n s ≤ J q n t := by
  have hne : (Partitions n).Nonempty := by
    refine ⟨fun k => if k = 0 then 0 else 1, by simp, ?_, ?_⟩
    · intro k hk
      have hk0 : k ≠ 0 := by omega
      simp [hk0]
    · intro i j hij
      dsimp only
      split_ifs with h1 h2 h2
      · exact le_rfl
      · norm_num
      · exact absurd hij (by omega)
      · exact le_rfl
  obtain ⟨s, hs, hmin⟩ := (isCompact_Partitions (n := n)).exists_isMinOn hne (continuousOn_J hint)
  exact ⟨s, hs, fun t ht => hmin ht⟩

end Compactness

/-! ## Main theorem -/

section Theorem

variable {q : ℝ → ℝ} {n : ℕ}

/-- The tuple of block medians of a partition. -/
noncomputable def medians (q : ℝ → ℝ) (n : ℕ) (s : ℕ → ℝ) : Fin n → ℝ :=
  fun k => q ((s k + s ((k : ℕ) + 1)) / 2)

lemma sum_blocks_medians (hmono : MonotoneOn q (Set.Ioo 0 1))
    (hint : IntervalIntegrable q volume 0 1) {s : ℕ → ℝ} (hs : s ∈ Partitions n) :
    (∑ k : Fin n, ∫ u in s k..s ((k : ℕ) + 1), |q u - medians q n s k|) = J q n s := by
  rw [J, ← Fin.sum_univ_eq_sum_range fun k => K q (s k) (s (k + 1))]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact integral_abs_sub_median hmono hint (Partitions.nonneg hs _)
    (Partitions.mono hs (Nat.le_succ _)) (Partitions.le_one hs _)

/-- `Φ` is invariant under permutations of the centres. -/
theorem Phi_comp_perm [Nonempty (Fin n)] (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    Phi q (x ∘ σ) = Phi q x := by
  simp only [Phi]
  exact intervalIntegral.integral_congr fun u _ => nearest_comp_perm σ

/-- Any tuple of centres can be sorted without changing the value of `Φ`. -/
theorem exists_monotone_perm [Nonempty (Fin n)] (x : Fin n → ℝ) :
    ∃ σ : Equiv.Perm (Fin n), Monotone (x ∘ σ) ∧ Phi q (x ∘ σ) = Phi q x :=
  ⟨Tuple.sort x, Tuple.monotone_sort x, Phi_comp_perm x _⟩

/-- The cost of an optimal partition is a lower bound for `Φ` (§4.2–4.3). -/
theorem min_J_le_Phi [Nonempty (Fin n)] (hmono : MonotoneOn q (Set.Ioo 0 1))
    (hint : IntervalIntegrable q volume 0 1) {s : ℕ → ℝ}
    (hsmin : ∀ t ∈ Partitions n, J q n s ≤ J q n t) (y : Fin n → ℝ) : J q n s ≤ Phi q y := by
  obtain ⟨σ, hσ, hPhi⟩ := exists_monotone_perm (q := q) y
  obtain ⟨t, ht, hteq⟩ := exists_partition_blocks hmono hint hσ
  calc J q n s ≤ J q n t := hsmin t ht
    _ ≤ ∑ k : Fin n, ∫ u in t k..t ((k : ℕ) + 1), |q u - (y ∘ σ) k| := J_le_sum_blocks hint ht _
    _ = Phi q (y ∘ σ) := hteq.symm
    _ = Phi q y := hPhi

/-- **Main theorem (Theorem 1).** For a nondecreasing integrable quantile `q`, the minimum of `Φ`
over all `n`-tuples of centres exists, equals the minimum of the partition cost `J` over the
simplex of ordered partitions, and is attained at the block medians of any optimal partition. -/
theorem min_Phi_eq_min_J [Nonempty (Fin n)] (hmono : MonotoneOn q (Set.Ioo 0 1))
    (hint : IntervalIntegrable q volume 0 1) :
    ∃ s ∈ Partitions n, (∀ t ∈ Partitions n, J q n s ≤ J q n t) ∧
      (∀ y : Fin n → ℝ, Phi q (medians q n s) ≤ Phi q y) ∧
      Phi q (medians q n s) = J q n s := by
  obtain ⟨s, hs, hsmin⟩ := exists_min_J (q := q) (n := n) Fin.pos' hint
  have hup : Phi q (medians q n s) ≤ J q n s := by
    calc Phi q (medians q n s) ≤ ∑ k : Fin n, ∫ u in s k..s ((k : ℕ) + 1),
          |q u - medians q n s k| := Phi_le_sum_blocks hint hs _
      _ = J q n s := sum_blocks_medians hmono hint hs
  have hlow : ∀ y : Fin n → ℝ, J q n s ≤ Phi q y := min_J_le_Phi hmono hint hsmin
  exact ⟨s, hs, hsmin, fun y => le_trans hup (hlow y), le_antisymm hup (hlow (medians q n s))⟩

/-! ### Complete classification of the minimizers -/

/-- **Sufficiency (§4.3).** If `s` is an optimal partition and each `c k` is a median of the
`k`-th block (i.e. realises the block cost `K`), then `c` minimizes `Φ`. -/
theorem isMin_of_optimal_partition [Nonempty (Fin n)] (hmono : MonotoneOn q (Set.Ioo 0 1))
    (hint : IntervalIntegrable q volume 0 1) {s : ℕ → ℝ} (hs : s ∈ Partitions n)
    (hsmin : ∀ t ∈ Partitions n, J q n s ≤ J q n t) {c : Fin n → ℝ}
    (hc : ∀ k : Fin n, (∫ u in s k..s ((k : ℕ) + 1), |q u - c k|) = K q (s k) (s ((k : ℕ) + 1))) :
    ∀ y : Fin n → ℝ, Phi q c ≤ Phi q y := by
  intro y
  refine le_trans ?_ (min_J_le_Phi hmono hint hsmin y)
  calc Phi q c ≤ ∑ k : Fin n, ∫ u in s k..s ((k : ℕ) + 1), |q u - c k| :=
        Phi_le_sum_blocks hint hs c
    _ = ∑ k : Fin n, K q (s k) (s ((k : ℕ) + 1)) := Finset.sum_congr rfl fun k _ => hc k
    _ = J q n s := (Fin.sum_univ_eq_sum_range (fun k => K q (s k) (s (k + 1))) n)

/-- **Necessity (§4.4).** A nondecreasing minimizing tuple arises from an optimal partition, each
coordinate being a median of the corresponding block. -/
theorem optimal_partition_of_isMin [Nonempty (Fin n)] (hmono : MonotoneOn q (Set.Ioo 0 1))
    (hint : IntervalIntegrable q volume 0 1) {x : Fin n → ℝ} (hx : Monotone x)
    (hxmin : ∀ y : Fin n → ℝ, Phi q x ≤ Phi q y) :
    ∃ s ∈ Partitions n, (∀ t ∈ Partitions n, J q n s ≤ J q n t) ∧
      ∀ k : Fin n, (∫ u in s k..s ((k : ℕ) + 1), |q u - x k|) = K q (s k) (s ((k : ℕ) + 1)) := by
  obtain ⟨s₀, hs₀, hs₀min, _, hs₀val⟩ := min_Phi_eq_min_J (q := q) (n := n) hmono hint
  obtain ⟨t, ht, hteq⟩ := exists_partition_blocks hmono hint hx
  have hJt : J q n t ≤ ∑ k : Fin n, ∫ u in t k..t ((k : ℕ) + 1), |q u - x k| :=
    J_le_sum_blocks hint ht x
  have h1 : J q n s₀ ≤ J q n t := hs₀min t ht
  have h2 : Phi q x ≤ J q n s₀ := by
    rw [← hs₀val]; exact hxmin _
  have heq : (∑ k : Fin n, ∫ u in t k..t ((k : ℕ) + 1), |q u - x k|) = J q n t :=
    le_antisymm (by rw [← hteq]; linarith) hJt
  refine ⟨t, ht, fun r hr => ?_, ?_⟩
  · have hts : J q n t = J q n s₀ :=
      le_antisymm (by rw [← heq, ← hteq]; exact h2) h1
    rw [hts]
    exact hs₀min r hr
  · have hle : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        K q (t k) (t ((k : ℕ) + 1)) ≤ ∫ u in t k..t ((k : ℕ) + 1), |q u - x k| := by
      intro k _
      exact K_le_integral hint (Partitions.nonneg ht _) (Partitions.mono ht (Nat.le_succ _))
        (Partitions.le_one ht _) _
    have hsum : (∑ k : Fin n, K q (t k) (t ((k : ℕ) + 1)))
        = ∑ k : Fin n, ∫ u in t k..t ((k : ℕ) + 1), |q u - x k| := by
      rw [heq, J, ← Fin.sum_univ_eq_sum_range (fun k => K q (t k) (t (k + 1)))]
    intro k
    exact ((Finset.sum_eq_sum_iff_of_le hle).1 hsum k (Finset.mem_univ k)).symm

/-- For **any** optimal partition, the tuple of block midpoint values is a minimizer of `Φ`. -/
theorem isMin_medians [Nonempty (Fin n)] (hmono : MonotoneOn q (Set.Ioo 0 1))
    (hint : IntervalIntegrable q volume 0 1) {s : ℕ → ℝ} (hs : s ∈ Partitions n)
    (hsmin : ∀ t ∈ Partitions n, J q n s ≤ J q n t) :
    ∀ y : Fin n → ℝ, Phi q (medians q n s) ≤ Phi q y :=
  isMin_of_optimal_partition hmono hint hs hsmin fun _ =>
    integral_abs_sub_median hmono hint (Partitions.nonneg hs _)
      (Partitions.mono hs (Nat.le_succ _)) (Partitions.le_one hs _)

/-- **Complete classification.** For a nondecreasing tuple of centres, minimality of `Φ` is
equivalent to being the tuple of block medians of an optimal partition. -/
theorem monotone_isMin_iff [Nonempty (Fin n)] (hmono : MonotoneOn q (Set.Ioo 0 1))
    (hint : IntervalIntegrable q volume 0 1) {x : Fin n → ℝ} (hx : Monotone x) :
    (∀ y : Fin n → ℝ, Phi q x ≤ Phi q y) ↔
      ∃ s ∈ Partitions n, (∀ t ∈ Partitions n, J q n s ≤ J q n t) ∧
        ∀ k : Fin n, (∫ u in s k..s ((k : ℕ) + 1), |q u - x k|)
          = K q (s k) (s ((k : ℕ) + 1)) := by
  refine ⟨fun h => optimal_partition_of_isMin hmono hint hx h, ?_⟩
  rintro ⟨s, hs, hsmin, hblocks⟩
  exact isMin_of_optimal_partition hmono hint hs hsmin hblocks

/-- **Continuous case (§5).** If moreover `q` is continuous, then on every nondegenerate block of
the optimal partition the corresponding centre is exactly the midpoint value
`q ((sᵢ₋₁ + sᵢ)/2)`; the block medians are unique. -/
theorem isMin_eq_midpoint_values_of_continuous [Nonempty (Fin n)]
    (hmono : MonotoneOn q (Set.Ioo 0 1)) (hcont : ContinuousOn q (Set.Ioo 0 1))
    (hint : IntervalIntegrable q volume 0 1) {x : Fin n → ℝ} (hx : Monotone x)
    (hxmin : ∀ y : Fin n → ℝ, Phi q x ≤ Phi q y) :
    ∃ s ∈ Partitions n, (∀ t ∈ Partitions n, J q n s ≤ J q n t) ∧
      ∀ k : Fin n, s (k : ℕ) < s ((k : ℕ) + 1) →
        x k = q ((s (k : ℕ) + s ((k : ℕ) + 1)) / 2) := by
  obtain ⟨s, hs, hsmin, hblocks⟩ := optimal_partition_of_isMin hmono hint hx hxmin
  refine ⟨s, hs, hsmin, fun k hk => ?_⟩
  exact median_unique_of_continuousOn hcont hint (Partitions.nonneg hs _) hk
    (Partitions.le_one hs _) (hblocks k)

end Theorem

/-! ## Interface with the original problem

The problem is stated for a continuous integrable `f : (0,1) → ℝ` and
`φ(X) = ∫₀¹ min_k |f t - x k| dt`.  Since `φ` only depends on the distribution of `f`, it agrees
with `Φ` computed from any nondecreasing rearrangement `q` of `f`, i.e. any `q` with the same
pushforward of Lebesgue measure on `(0,1]`.  This is the interface lemma. -/

section Interface

variable {q : ℝ → ℝ} {n : ℕ}

theorem Phi_eq_of_map_eq [Nonempty (Fin n)] {f : ℝ → ℝ} (x : Fin n → ℝ)
    (hf : AEMeasurable f (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hq : AEMeasurable q (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hmap : Measure.map f (volume.restrict (Set.Ioc (0:ℝ) 1))
      = Measure.map q (volume.restrict (Set.Ioc (0:ℝ) 1))) :
    (∫ t in (0:ℝ)..1, nearest x (f t)) = Phi q x := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  rw [Phi, intervalIntegral.integral_of_le h01, intervalIntegral.integral_of_le h01,
    ← MeasureTheory.integral_map hf (continuous_nearest.aestronglyMeasurable),
    ← MeasureTheory.integral_map hq (continuous_nearest.aestronglyMeasurable), hmap]

end Interface

/-! ## The case `n = 1` (§8.1) and the affine test case (§8.2) -/

section OneCentre

variable {q : ℝ → ℝ}

lemma J_one_eq {s : ℕ → ℝ} (hs : s ∈ Partitions 1) : J q 1 s = K q 0 1 := by
  have h0 : s 0 = 0 := hs.1
  have h1 : s 1 = 1 := hs.2.1 1 le_rfl
  simp [J, h0, h1]

/-- For a single centre the unique optimal partition is `(0,1)` and the minimum of `Φ` is
`K q 0 1 = ∫_{1/2}^1 q - ∫_0^{1/2} q`, attained at the median `q (1/2)`. -/
theorem min_Phi_one (hmono : MonotoneOn q (Set.Ioo 0 1)) (hint : IntervalIntegrable q volume 0 1) :
    (∀ y : Fin 1 → ℝ, Phi q (fun _ : Fin 1 => q (1/2)) ≤ Phi q y) ∧
      Phi q (fun _ : Fin 1 => q (1/2)) = K q 0 1 := by
  obtain ⟨s, hs, _, hmin, hval⟩ := min_Phi_eq_min_J (q := q) (n := 1) hmono hint
  have hmed : medians q 1 s = fun _ : Fin 1 => q (1/2) := by
    funext k
    have hk : (k : ℕ) = 0 := by omega
    simp only [medians, hk, hs.1, hs.2.1 1 le_rfl]
    norm_num
  rw [hmed] at hmin hval
  exact ⟨hmin, by rw [hval, J_one_eq hs]⟩

/-- Test case: for the identity quantile (i.e. `f` affine with slope `1`, uniform distribution)
the one-centre minimum is `1/4`, in accordance with the general formula `|α|/(4n)`. -/
theorem min_Phi_one_id :
    (∀ y : Fin 1 → ℝ, Phi (fun u => u) (fun _ : Fin 1 => (1/2 : ℝ)) ≤ Phi (fun u => u) y) ∧
      Phi (fun u => u) (fun _ : Fin 1 => (1/2 : ℝ)) = 1 / 4 := by
  have hmono : MonotoneOn (fun u : ℝ => u) (Set.Ioo 0 1) := fun a _ b _ h => h
  have hint : IntervalIntegrable (fun u : ℝ => u) volume 0 1 :=
    (continuous_id.intervalIntegrable 0 1)
  have hK : K (fun u : ℝ => u) 0 1 = 1 / 4 := by
    simp [K, H, integral_id]
    norm_num
  obtain ⟨hmin, hval⟩ := min_Phi_one hmono hint
  refine ⟨?_, ?_⟩
  · simpa using hmin
  · rw [← hK, ← hval]

end OneCentre

end Q766
