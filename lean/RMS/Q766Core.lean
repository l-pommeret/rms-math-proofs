import RMS.Q766

/-!
# Q766, extension layer 0 : the minimum value, the argmin set, and the printed functional

This module freezes the completed core of `RequestProject.Main` and introduces the stable
additional definitions used by all later layers:

* `Q766.quantError q n = ⨅ x, Φ q x`, the optimal `n`-point distortion;
* `Q766.IsPhiMin q x`, `Q766.PhiArgmin q n`, the minimality predicate and the attainment set;
* `Q766.phiF f x = ∫₀¹ min_k |f t - x k| dt`, the functional of the printed problem.

The main results here are that the infimum is attained and equals the optimal partition cost
(`Q766.quantError_eq_min_J`).
-/

open scoped BigOperators
open MeasureTheory intervalIntegral Set Filter Topology

namespace Q766

/-! ## Stage 0 : the core results still elaborate -/

section Stage0

example [Nonempty (Fin 3)] {q : ℝ → ℝ} (hmono : MonotoneOn q (Set.Ioo 0 1))
    (hint : IntervalIntegrable q volume 0 1) :
    ∃ s ∈ Partitions 3, (∀ t ∈ Partitions 3, J q 3 s ≤ J q 3 t) ∧
      (∀ y : Fin 3 → ℝ, Phi q (medians q 3 s) ≤ Phi q y) ∧
      Phi q (medians q 3 s) = J q 3 s :=
  min_Phi_eq_min_J hmono hint

end Stage0

/-! ## Stable definitions -/

/-- The optimal `n`-point distortion `eₙ = inf_x Φ(x)`. -/
noncomputable def quantError (q : ℝ → ℝ) (n : ℕ) : ℝ :=
  ⨅ x : Fin n → ℝ, Phi q x

/-- `x` minimizes `Φ q`. -/
def IsPhiMin (q : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ y : Fin n → ℝ, Phi q x ≤ Phi q y

/-- The set of minimizers of `Φ q` among `n`-tuples. -/
def PhiArgmin (q : ℝ → ℝ) (n : ℕ) : Set (Fin n → ℝ) :=
  {x | IsPhiMin q x}

/-- The functional of the printed problem, for the original function `f`. -/
noncomputable def phiF (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, nearest x (f t)

lemma mem_PhiArgmin {q : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ} :
    x ∈ PhiArgmin q n ↔ IsPhiMin q x := Iff.rfl

/-- If `x` is a minimizer then the infimum is its value. -/
lemma quantError_eq_of_isMin {q : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ} (hx : IsPhiMin q x) :
    quantError q n = Phi q x := by
  refine le_antisymm (ciInf_le ⟨Phi q x, ?_⟩ x) (le_ciInf hx)
  rintro z ⟨y, rfl⟩
  exact hx y

/-- The infimum defining `quantError` is attained at the block medians of an optimal partition,
and equals the optimal partition cost. -/
theorem quantError_eq_min_J {q : ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    (hmono : MonotoneOn q (Set.Ioo 0 1)) (hint : IntervalIntegrable q volume 0 1) :
    ∃ s ∈ Partitions n, (∀ t ∈ Partitions n, J q n s ≤ J q n t) ∧
      IsPhiMin q (medians q n s) ∧ quantError q n = J q n s := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨s, hs, hsmin, hmin, hval⟩ := min_Phi_eq_min_J (q := q) (n := n) hmono hint
  exact ⟨s, hs, hsmin, hmin, by rw [quantError_eq_of_isMin hmin, hval]⟩

/-- The minimum is attained. -/
theorem exists_isPhiMin {q : ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    (hmono : MonotoneOn q (Set.Ioo 0 1)) (hint : IntervalIntegrable q volume 0 1) :
    ∃ x : Fin n → ℝ, IsPhiMin q x := by
  obtain ⟨s, _, _, hmin, _⟩ := quantError_eq_min_J hn hmono hint
  exact ⟨medians q n s, hmin⟩

lemma quantError_le {q : ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    (hmono : MonotoneOn q (Set.Ioo 0 1)) (hint : IntervalIntegrable q volume 0 1)
    (y : Fin n → ℝ) : quantError q n ≤ Phi q y := by
  obtain ⟨_, _, _, hmin, _⟩ := quantError_eq_min_J hn hmono hint
  rw [quantError_eq_of_isMin hmin]
  exact hmin y

/-- `Φ` is nonnegative. -/
lemma Phi_nonneg {q : ℝ → ℝ} {n : ℕ} [Nonempty (Fin n)] (x : Fin n → ℝ) : 0 ≤ Phi q x := by
  rw [Phi, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact MeasureTheory.integral_nonneg fun u => nearest_nonneg

lemma quantError_nonneg {q : ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    (hmono : MonotoneOn q (Set.Ioo 0 1)) (hint : IntervalIntegrable q volume 0 1) :
    0 ≤ quantError q n := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨_, _, _, hmin, _⟩ := quantError_eq_min_J hn hmono hint
  rw [quantError_eq_of_isMin hmin]
  exact Phi_nonneg _

/-- `phiF` agrees with `Φ` computed from any function with the same distribution. -/
theorem phiF_eq_Phi {q : ℝ → ℝ} {n : ℕ} [Nonempty (Fin n)] {f : ℝ → ℝ} (x : Fin n → ℝ)
    (hf : AEMeasurable f (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hq : AEMeasurable q (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hmap : Measure.map f (volume.restrict (Set.Ioc (0:ℝ) 1))
      = Measure.map q (volume.restrict (Set.Ioc (0:ℝ) 1))) :
    phiF f x = Phi q x :=
  Phi_eq_of_map_eq x hf hq hmap

end Q766
