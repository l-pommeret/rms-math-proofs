import RMS.Q766Core

/-!
# Q766, Stage 2a : strict improvement and positivity

For a nondecreasing, continuous and **nonconstant** quantile `q` we prove

* `Q766.quantError_pos` : `0 < eₙ` for every `n`;
* `Q766.quantError_succ_lt` : `e_{n+1} < eₙ`.

The mechanism is the direct formal version of (5.6): the value set of `q` contains a
nondegenerate interval, hence a point `y₀` at positive distance `d` from the (finite) set of
centres; by continuity `q` stays within `d/4` of `y₀` on a nondegenerate parameter interval, on
which adding `y₀` as an extra centre decreases the nearest-centre distance by at least `d/2`.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral Set

namespace Q766

section Strict

variable {q : ℝ → ℝ} {n : ℕ}

/-! ### Adding one centre -/

lemma nearest_snoc_le_last (x : Fin n → ℝ) (y₀ z : ℝ) :
    nearest (Fin.snoc x y₀ : Fin (n + 1) → ℝ) z ≤ |z - y₀| := by
  simpa using nearest_le (x := (Fin.snoc x y₀ : Fin (n + 1) → ℝ)) (y := z) (Fin.last n)

lemma nearest_snoc_le [Nonempty (Fin n)] (x : Fin n → ℝ) (y₀ z : ℝ) :
    nearest (Fin.snoc x y₀ : Fin (n + 1) → ℝ) z ≤ nearest x z := by
  refine le_nearest fun k => ?_
  simpa using nearest_le (x := (Fin.snoc x y₀ : Fin (n + 1) → ℝ)) (y := z) k.castSucc

/-! ### Splitting `Φ` -/

lemma Phi_split [Nonempty (Fin n)] (hint : IntervalIntegrable q volume 0 1) (x : Fin n → ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Phi q x = (∫ u in (0:ℝ)..a, nearest x (q u)) + (∫ u in a..b, nearest x (q u))
      + ∫ u in b..1, nearest x (q u) := by
  have h1 : (∫ u in (0:ℝ)..a, nearest x (q u)) + (∫ u in a..b, nearest x (q u))
      = ∫ u in (0:ℝ)..b, nearest x (q u) :=
    intervalIntegral.integral_add_adjacent_intervals
      (intInt_nearest hint le_rfl (hab.trans hb) ha)
      (intInt_nearest hint ha hb hab)
  have h2 : (∫ u in (0:ℝ)..b, nearest x (q u)) + (∫ u in b..1, nearest x (q u))
      = ∫ u in (0:ℝ)..1, nearest x (q u) :=
    intervalIntegral.integral_add_adjacent_intervals
      (intInt_nearest hint le_rfl hb (ha.trans hab))
      (intInt_nearest hint (ha.trans hab) le_rfl hb)
  rw [Phi, ← h2, ← h1]

lemma integral_nearest_nonneg [Nonempty (Fin n)] (x : Fin n → ℝ) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ ∫ u in a..b, nearest x (q u) :=
  intervalIntegral.integral_nonneg hab fun _ _ => nearest_nonneg

/-! ### The gap interval -/

/-- **The key geometric step.**  If `q` is nondecreasing, continuous and nonconstant on `(0,1)`,
then for any finite family of centres `x` there are a value `y₀`, a gap `d > 0` and a
nondegenerate parameter interval `[a,b] ⊆ [0,1]` on which `q` is `d/4`-close to `y₀` while every
centre is at distance at least `3d/4`. -/
lemma exists_gap_interval [Nonempty (Fin n)]
    (hmono : MonotoneOn q (Set.Ioo (0:ℝ) 1)) (hcont : ContinuousOn q (Set.Ioo (0:ℝ) 1))
    (hqne : ∃ u ∈ Set.Ioo (0:ℝ) 1, ∃ v ∈ Set.Ioo (0:ℝ) 1, q u ≠ q v)
    (x : Fin n → ℝ) :
    ∃ y₀ a b d : ℝ, 0 < d ∧ 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      ∀ u ∈ Set.Icc a b, |q u - y₀| ≤ d / 4 ∧ 3 * d / 4 ≤ nearest x (q u) := by
  -- first produce two parameters with `q u < q v`
  obtain ⟨u₁, hu₁, v₁, hv₁, hne⟩ := hqne
  obtain ⟨u, hu, v, hv, hlt⟩ : ∃ u ∈ Set.Ioo (0:ℝ) 1, ∃ v ∈ Set.Ioo (0:ℝ) 1, q u < q v := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨u₁, hu₁, v₁, hv₁, h⟩
    · exact ⟨v₁, hv₁, u₁, hu₁, h⟩
  have huv : u < v := by
    by_contra hcon
    exact absurd (hmono hv hu (not_lt.1 hcon)) (not_le.2 hlt)
  have hsub : Set.Icc u v ⊆ Set.Ioo (0:ℝ) 1 := Set.Icc_subset_Ioo hu.1 hv.2
  have hcontIcc : ContinuousOn q (Set.Icc u v) := hcont.mono hsub
  have hIVT : Set.Icc (q u) (q v) ⊆ q '' Set.Icc u v :=
    intermediate_value_Icc huv.le hcontIcc
  -- pick a value in the image that is not one of the centres
  have hinf : (Set.Icc (q u) (q v) \ Set.range x).Infinite :=
    (Set.Icc_infinite hlt).diff (Set.finite_range x)
  obtain ⟨y₀, hy₀mem, hy₀not⟩ := hinf.nonempty
  obtain ⟨u₀, hu₀mem, hu₀⟩ := hIVT hy₀mem
  have hu₀Ioo : u₀ ∈ Set.Ioo (0:ℝ) 1 := hsub hu₀mem
  -- the gap
  set d := nearest x y₀ with hd
  have hdpos : 0 < d := by
    obtain ⟨k, hk⟩ := exists_nearest (x := x) (y := y₀)
    rw [hd, hk]
    have : y₀ ≠ x k := by
      intro h; exact hy₀not ⟨k, h.symm⟩
    exact abs_pos.2 (sub_ne_zero.2 this)
  -- continuity at `u₀`
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hcont u₀ hu₀Ioo) (d / 4) (by linarith)
  set r := min (δ / 2) (min (u₀ / 2) ((1 - u₀) / 2)) with hr
  have hrpos : 0 < r := by
    have h1 : 0 < u₀ / 2 := by linarith [hu₀Ioo.1]
    have h2 : 0 < (1 - u₀) / 2 := by linarith [hu₀Ioo.2]
    simp only [hr, lt_min_iff]
    exact ⟨by linarith, h1, h2⟩
  have hrδ : r ≤ δ / 2 := min_le_left _ _
  have hru : r ≤ u₀ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hr1 : r ≤ (1 - u₀) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨y₀, u₀ - r, u₀ + r, d, hdpos, by linarith, by linarith, by linarith, ?_⟩
  intro w hw
  have hwIoo : w ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hclose : |q w - y₀| < d / 4 := by
    have hdist : dist w u₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> [linarith [hw.1]; linarith [hw.2]]
    have := hball hwIoo hdist
    rw [Real.dist_eq, hu₀] at this
    exact this
  refine ⟨hclose.le, le_nearest fun k => ?_⟩
  have h1 : d ≤ |y₀ - x k| := nearest_le k
  have h2 : |y₀ - x k| ≤ |y₀ - q w| + |q w - x k| := abs_sub_le _ _ _
  have h3 : |y₀ - q w| = |q w - y₀| := abs_sub_comm _ _
  linarith

/-! ### Positivity and strict improvement -/

/-- For a continuous nonconstant nondecreasing `q`, every finite family of centres has positive
distortion. -/
theorem Phi_pos [Nonempty (Fin n)]
    (hmono : MonotoneOn q (Set.Ioo (0:ℝ) 1)) (hcont : ContinuousOn q (Set.Ioo (0:ℝ) 1))
    (hint : IntervalIntegrable q volume 0 1)
    (hqne : ∃ u ∈ Set.Ioo (0:ℝ) 1, ∃ v ∈ Set.Ioo (0:ℝ) 1, q u ≠ q v)
    (x : Fin n → ℝ) : 0 < Phi q x := by
  obtain ⟨y₀, a, b, d, hdpos, ha, hab, hb, hgap⟩ := exists_gap_interval hmono hcont hqne x
  have hmid : 3 * d / 4 * (b - a) ≤ ∫ u in a..b, nearest x (q u) := by
    have h := intervalIntegral.integral_mono_on hab.le
      (_root_.intervalIntegrable_const (c := 3 * d / 4))
      (intInt_nearest hint ha hb hab.le) (fun u hu => (hgap u hu).2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    calc 3 * d / 4 * (b - a) = (b - a) * (3 * d / 4) := by ring
      _ ≤ _ := h
  have hpos : 0 < 3 * d / 4 * (b - a) := by
    have : 0 < b - a := by linarith
    positivity
  rw [Phi_split hint x ha hab.le hb]
  have hA := integral_nearest_nonneg (q := q) x ha
  have hB := integral_nearest_nonneg (q := q) x hb
  linarith

/-- `0 < eₙ` for continuous nonconstant nondecreasing `q`. -/
theorem quantError_pos (hn : 0 < n)
    (hmono : MonotoneOn q (Set.Ioo (0:ℝ) 1)) (hcont : ContinuousOn q (Set.Ioo (0:ℝ) 1))
    (hint : IntervalIntegrable q volume 0 1)
    (hqne : ∃ u ∈ Set.Ioo (0:ℝ) 1, ∃ v ∈ Set.Ioo (0:ℝ) 1, q u ≠ q v) :
    0 < quantError q n := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨s, _, _, hmin, _⟩ := quantError_eq_min_J hn hmono hint
  rw [quantError_eq_of_isMin hmin]
  exact Phi_pos hmono hcont hint hqne _

/-- **Strict improvement (5.6).**  Adding one more centre strictly decreases the optimal
distortion, for a continuous nonconstant nondecreasing quantile. -/
theorem quantError_succ_lt (hn : 0 < n)
    (hmono : MonotoneOn q (Set.Ioo (0:ℝ) 1)) (hcont : ContinuousOn q (Set.Ioo (0:ℝ) 1))
    (hint : IntervalIntegrable q volume 0 1)
    (hqne : ∃ u ∈ Set.Ioo (0:ℝ) 1, ∃ v ∈ Set.Ioo (0:ℝ) 1, q u ≠ q v) :
    quantError q (n + 1) < quantError q n := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨s, _, _, hmin, _⟩ := quantError_eq_min_J hn hmono hint
  set x : Fin n → ℝ := medians q n s with hx
  obtain ⟨y₀, a, b, d, hdpos, ha, hab, hb, hgap⟩ := exists_gap_interval hmono hcont hqne x
  set x' : Fin (n + 1) → ℝ := Fin.snoc x y₀ with hx'
  -- pointwise comparison
  have hle : ∀ u : ℝ, nearest x' (q u) ≤ nearest x (q u) := fun u => nearest_snoc_le x y₀ (q u)
  -- outer blocks
  have hout1 : (∫ u in (0:ℝ)..a, nearest x' (q u)) ≤ ∫ u in (0:ℝ)..a, nearest x (q u) :=
    intervalIntegral.integral_mono_on ha (intInt_nearest hint le_rfl (hab.le.trans hb) ha)
      (intInt_nearest hint le_rfl (hab.le.trans hb) ha) (fun u _ => hle u)
  have hout2 : (∫ u in b..1, nearest x' (q u)) ≤ ∫ u in b..1, nearest x (q u) :=
    intervalIntegral.integral_mono_on hb (intInt_nearest hint (ha.trans hab.le) le_rfl hb)
      (intInt_nearest hint (ha.trans hab.le) le_rfl hb) (fun u _ => hle u)
  -- middle block
  have hmid' : (∫ u in a..b, nearest x' (q u)) ≤ d / 4 * (b - a) := by
    have h := intervalIntegral.integral_mono_on hab.le
      (intInt_nearest hint ha hb hab.le) (_root_.intervalIntegrable_const (c := d / 4))
      (fun u hu => le_trans (nearest_snoc_le_last x y₀ (q u)) (hgap u hu).1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    calc (∫ u in a..b, nearest x' (q u)) ≤ (b - a) * (d / 4) := h
      _ = d / 4 * (b - a) := by ring
  have hmid : 3 * d / 4 * (b - a) ≤ ∫ u in a..b, nearest x (q u) := by
    have h := intervalIntegral.integral_mono_on hab.le
      (_root_.intervalIntegrable_const (c := 3 * d / 4))
      (intInt_nearest hint ha hb hab.le) (fun u hu => (hgap u hu).2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    calc 3 * d / 4 * (b - a) = (b - a) * (3 * d / 4) := by ring
      _ ≤ _ := h
  have hgapval : 0 < d / 2 * (b - a) := by
    have : 0 < b - a := by linarith
    positivity
  have hstrict : Phi q x' < Phi q x := by
    rw [Phi_split hint x ha hab.le hb, Phi_split hint x' ha hab.le hb]
    linarith
  calc quantError q (n + 1) ≤ Phi q x' := quantError_le (Nat.succ_pos n) hmono hint x'
    _ < Phi q x := hstrict
    _ = quantError q n := (quantError_eq_of_isMin hmin).symm

end Strict

end Q766
