import RMS.Q766Printed

/-!
# Q766, canonical completion : the printed functional of the original function `f`

This module closes the last gap between `RequestProject.Main` (everything stated for a
nondecreasing rearrangement `q`) and the printed problem (everything stated for the given
function `f`).

* `Q766.exists_integrable_monotone_rearrangement_canonical` : from `Integrable f` on `(0,1]`
  alone — no measurability, boundedness, continuity or atomlessness assumption — there is a
  nondecreasing, interval integrable `q` with the same pushforward.
* `Q766.IsPhiFMin` : `x` minimizes the printed functional `φ_f (x) = ∫₀¹ minₖ |f t − x k| dt`.
* `Q766.phiF_min_and_argmin` : for `0 < n` and integrable `f`, a single `q` such that
  `φ_f = Φ_q`, the minimum of `φ_f` is the optimal partition cost `J q n s`, attained at the
  block medians `medians q n s`; every block-median tuple of every optimal partition minimizes
  `φ_f`; and, for *every* tuple `x`, `x` minimizes `φ_f` iff some ordering `x ∘ σ` of it consists
  of block medians of an optimal partition.
* `Q766.phiF_canonical` : the same statement under the canonical hypotheses of the printed
  problem (`f` continuous on `(0,1)`, integrable, `n > 0`).

No hypothesis beyond integrability of `f` and `0 < n` is used; in particular the statements apply
verbatim to a constant `f` (block-median equality on a zero-length block is vacuous, and repeated
or unused centres are allowed).
-/

open scoped BigOperators
open MeasureTheory intervalIntegral Set Filter Topology

namespace Q766

section Canonical

variable {f : ℝ → ℝ} {n : ℕ} (hfcont : ContinuousOn f (Set.Ioo (0 : ℝ) 1))

/-- **Existence of the nondecreasing rearrangement**, stated with the measure written out.
Only integrability of `f` on `(0,1]` is assumed; monotonicity, interval integrability and the
equality of pushforwards are conclusions. -/
theorem exists_integrable_monotone_rearrangement_canonical
    (hfint : Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    ∃ q : ℝ → ℝ,
      AEMeasurable q (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
      MonotoneOn q (Set.Ioo (0 : ℝ) 1) ∧
      IntervalIntegrable q volume 0 1 ∧
      Measure.map q (volume.restrict (Set.Ioc (0 : ℝ) 1)) =
        Measure.map f (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  exists_integrable_monotone_rearrangement (f := f) hfint

/-- `x` minimizes the functional `φ_f` of the printed problem. -/
def IsPhiFMin (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ y : Fin n → ℝ, phiF f x ≤ phiF f y

/-- **The printed problem, in full, for the original function `f`.**

For every integrable `f : (0,1) → ℝ` and every `n > 0` there is a nondecreasing integrable
rearrangement `q` of `f` with `φ_f = Φ_q`, and:

1. some `s ∈ Partitions n` minimizes `J q n`, the tuple `medians q n s` of its block midpoint
   values minimizes `φ_f`, and the minimum value is `J q n s`;
2. for every optimal partition `t` and every tuple `c` realizing the block-median equality on
   each block of `t`, `c` minimizes `φ_f`;
3. for *every* tuple `x`, `x` minimizes `φ_f` iff some rearrangement `x ∘ σ` of it is
   nondecreasing and consists of block medians of an optimal partition.

Continuity of `f` is not needed. -/
theorem phiF_min_and_argmin (hn : 0 < n)
    (hfint : Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    ∃ q : ℝ → ℝ,
      MonotoneOn q (Set.Ioo (0 : ℝ) 1) ∧
      IntervalIntegrable q volume 0 1 ∧
      (∀ x : Fin n → ℝ, phiF f x = Phi q x) ∧
      (∃ s ∈ Partitions n, (∀ t ∈ Partitions n, J q n s ≤ J q n t) ∧
        IsPhiFMin f (medians q n s) ∧ phiF f (medians q n s) = J q n s) ∧
      (∀ t ∈ Partitions n, (∀ r ∈ Partitions n, J q n t ≤ J q n r) →
        ∀ c : Fin n → ℝ,
          (∀ k : Fin n, (∫ u in t k..t ((k : ℕ) + 1), |q u - c k|)
            = K q (t k) (t ((k : ℕ) + 1))) →
          IsPhiFMin f c) ∧
      (∀ x : Fin n → ℝ,
        IsPhiFMin f x ↔
          ∃ σ : Equiv.Perm (Fin n),
            Monotone (x ∘ σ) ∧
            ∃ t ∈ Partitions n,
              (∀ r ∈ Partitions n, J q n t ≤ J q n r) ∧
              ∀ k : Fin n,
                (∫ u in t k..t ((k : ℕ) + 1), |q u - (x ∘ σ) k|)
                  = K q (t k) (t ((k : ℕ) + 1))) := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hfmeas : AEMeasurable f nu := hfint.aestronglyMeasurable.aemeasurable
  obtain ⟨q, hqm, hqmono, hqint, hmap⟩ := exists_integrable_monotone_rearrangement (f := f) hfint
  have htransfer : ∀ x : Fin n → ℝ, phiF f x = Phi q x := fun x =>
    phiF_eq_Phi_of_map_eq x hfmeas hqm hmap
  have hminiff : ∀ x : Fin n → ℝ, IsPhiFMin f x ↔ IsPhiMin q x := by
    intro x
    simp only [IsPhiFMin, IsPhiMin, htransfer]
  refine ⟨q, hqmono, hqint, htransfer, ?_, ?_, ?_⟩
  · obtain ⟨s, hs, hsmin, hmin, _⟩ := quantError_eq_min_J hn hqmono hqint
    obtain ⟨s', hs', hs'min, _, hval⟩ := min_Phi_eq_min_J (q := q) (n := n) hqmono hqint
    refine ⟨s, hs, hsmin, (hminiff _).2 hmin, ?_⟩
    rw [htransfer]
    have h1 : Phi q (medians q n s) = J q n s := by
      have hle : Phi q (medians q n s) ≤ J q n s := by
        calc Phi q (medians q n s)
            ≤ ∑ k : Fin n, ∫ u in s k..s ((k : ℕ) + 1), |q u - medians q n s k| :=
              Phi_le_sum_blocks hqint hs _
          _ = J q n s := sum_blocks_medians hqmono hqint hs
      have hge : J q n s ≤ Phi q (medians q n s) := min_J_le_Phi hqmono hqint hsmin _
      exact le_antisymm hle hge
    exact h1
  · intro t ht htmin c hc
    exact (hminiff c).2 (isMin_of_optimal_partition hqmono hqint ht htmin hc)
  · intro x
    rw [hminiff]
    constructor
    · intro hx
      obtain ⟨σ, hσ, hPhi⟩ := exists_monotone_perm (q := q) x
      have hxσ : ∀ y : Fin n → ℝ, Phi q (x ∘ σ) ≤ Phi q y := by
        intro y; rw [hPhi]; exact hx y
      obtain ⟨t, ht, htmin, hblocks⟩ := optimal_partition_of_isMin hqmono hqint hσ hxσ
      exact ⟨σ, hσ, t, ht, htmin, hblocks⟩
    · rintro ⟨σ, _, t, ht, htmin, hblocks⟩
      intro y
      have h := isMin_of_optimal_partition hqmono hqint ht htmin hblocks y
      have hPhi : Phi q (x ∘ σ) = Phi q x := Phi_comp_perm x σ
      rw [hPhi] at h
      exact h

include hfcont in
/-- **The printed problem under its canonical hypotheses.**  `f` continuous on `(0,1)`,
integrable on `(0,1]`, and `n > 0`: the exact minimum of `φ_f`, its attainment at the block
medians of an optimal partition, the sufficiency of block-median tuples, and the complete
characterisation of *all* minimizing tuples.  (Continuity is not used; it is kept because it is
part of the printed statement.) -/
theorem phiF_canonical (hn : 0 < n)
    (hfint : Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    ∃ q : ℝ → ℝ,
      MonotoneOn q (Set.Ioo (0 : ℝ) 1) ∧
      IntervalIntegrable q volume 0 1 ∧
      (∀ x : Fin n → ℝ, phiF f x = Phi q x) ∧
      (∃ s ∈ Partitions n, (∀ t ∈ Partitions n, J q n s ≤ J q n t) ∧
        IsPhiFMin f (medians q n s) ∧ phiF f (medians q n s) = J q n s) ∧
      (∀ t ∈ Partitions n, (∀ r ∈ Partitions n, J q n t ≤ J q n r) →
        ∀ c : Fin n → ℝ,
          (∀ k : Fin n, (∫ u in t k..t ((k : ℕ) + 1), |q u - c k|)
            = K q (t k) (t ((k : ℕ) + 1))) →
          IsPhiFMin f c) ∧
      (∀ x : Fin n → ℝ,
        IsPhiFMin f x ↔
          ∃ σ : Equiv.Perm (Fin n),
            Monotone (x ∘ σ) ∧
            ∃ t ∈ Partitions n,
              (∀ r ∈ Partitions n, J q n t ≤ J q n r) ∧
              ∀ k : Fin n,
                (∫ u in t k..t ((k : ℕ) + 1), |q u - (x ∘ σ) k|)
                  = K q (t k) (t ((k : ℕ) + 1))) :=
  phiF_min_and_argmin hn hfint

/-- Regression check: the aggregate theorem applies unchanged to a constant `f`. -/
example (c : ℝ) :
    ∃ q : ℝ → ℝ, ∀ x : Fin 3 → ℝ, phiF (fun _ => c) x = Phi q x := by
  obtain ⟨q, _, _, hbridge, _⟩ :=
    phiF_canonical (f := fun _ => c) (n := 3) continuousOn_const (by norm_num)
      (integrable_const c)
  exact ⟨q, hbridge⟩

end Canonical

end Q766
