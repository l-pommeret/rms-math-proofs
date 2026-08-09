import Mathlib

/-!
# Q857 — the distance from a matrix to the determinant-one matrices

This file formalizes problem Q857: for `A` an `n × n` matrix over `ℝ` or `ℂ` (`n ≥ 1`),
determine

```
d(A) = inf { ‖A - M‖ : det M = 1 }
```

where `‖·‖` is the operator norm subordinate to the Euclidean norm on `ℝⁿ` (resp. the standard
Hermitian norm on `ℂⁿ`).

## Contents

* **The scalar package.**  For a finite nonnegative vector `σ` we define `Q857.Rplus σ`,
  `Q857.Rminus σ` and `Q857.cmin σ η`, and prove attainment together with the complete
  characterizations
  `Q857.scalar_pos_isLeast`, `Q857.scalar_neg_isLeast`, `Q857.cmin_isLeast`, `Q857.cmin_one`.
* **Singular values and the SVD.**  `Q857.svals` is defined by the Courant–Fischer max-min
  formula; `Q857.exists_svd`, `Q857.exists_svd_svals` produce a sorted singular value
  decomposition, `Q857.svals_le_add` is Weyl's perturbation inequality and
  `Q857.prod_svals` is `∏ σ i = |det A|`.
* **The matrix bridge.**  `Q857.exists_svd_eta` normalizes the determinant phase of an SVD,
  `Q857.exists_matrix_of_scalars` reconstructs a determinant-one matrix from admissible
  scalars, and `Q857.exists_nearest` proves that the distance is attained.
* **The aggregate theorems.**  `Q857.real_dist` is the complete real answer
  (`R₊(σ(A))` for `det A ≥ 0` and `R₋(σ(A))` for `det A < 0`);
  `Q857.complex_isLeast_of_eta_one` is the complex answer whenever the determinant phase
  `η_A` is trivial (in particular for singular `A` and for `A` with positive real
  determinant), and `Q857.complex_upper` is the complex upper bound for an arbitrary phase.

## Status

Everything stated below is proved: the file contains no `sorry`, no `axiom`, and no appeal to
`native_decide`.

The formalization is **not** complete Q857 coverage: the complex lower bound for an *arbitrary*
determinant phase is missing.  Concretely, the first missing theorem is

```
theorem complex_isLeast (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ) :
    IsLeast {r : ℝ | ∃ M : Matrix (Fin n) (Fin n) ℂ, M.det = 1 ∧ ‖A - M‖ ≤ r}
      (cmin (svals A) (etaOf A))
```

whose `≤`-half (membership) is `Q857.complex_upper` below, and whose lower-bound half is the
arbitrary-phase case of Proposition 4.1 of the source note ("no non-diagonal matrix beats the
scalar optimum").  The published proof of that proposition goes through a nonsmooth Lagrange
multiplier argument for the spectral norm (a description of the subdifferential of `‖·‖₂`
through nuclear-norm duality); none of that theory is available in mathlib, and it is not
formalized here.  What *is* proved for arbitrary complex `A` is the upper bound
`Q857.complex_upper`, the attainment statement `Q857.exists_nearest`, and the exact value
`Q857.complex_isLeast_of_eta_one` in the case `η_A = 1`.

Lean version: 4.28.0.  Mathlib version: the release tagged `v4.28.0`
(commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`).
-/

open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexOrder

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace Q857

section Max

variable {n : ℕ}

/-- Maximum of a finite family of reals (junk value `0` for the empty family). -/
noncomputable def mx (f : Fin n → ℝ) : ℝ := ⨆ i, f i

lemma le_mx (f : Fin n → ℝ) (i : Fin n) : f i ≤ mx f :=
  le_ciSup (Finite.bddAbove_range f) i

lemma mx_le {f : Fin n → ℝ} {r : ℝ} (hn : 0 < n) (h : ∀ i, f i ≤ r) : mx f ≤ r := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ciSup_le h

lemma mx_le_iff {f : Fin n → ℝ} {r : ℝ} (hn : 0 < n) : mx f ≤ r ↔ ∀ i, f i ≤ r :=
  ⟨fun h i => le_trans (le_mx f i) h, mx_le hn⟩

end Max

section Scalar

variable {n : ℕ} {σ : Fin n → ℝ}

/-- The smallest entry of `σ` (junk value `0` for the empty family). -/
noncomputable def sigmaMin (σ : Fin n → ℝ) : ℝ := ⨅ i, σ i

lemma sigmaMin_le (σ : Fin n → ℝ) (i : Fin n) : sigmaMin σ ≤ σ i :=
  ciInf_le (Finite.bddBelow_range σ) i

lemma exists_eq_sigmaMin (hn : 0 < n) (σ : Fin n → ℝ) : ∃ i, σ i = sigmaMin σ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, hi⟩ := Finite.exists_min σ
  refine ⟨i, le_antisymm ?_ (sigmaMin_le σ i)⟩
  exact le_ciInf hi

lemma sigmaMin_nonneg (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) : 0 ≤ sigmaMin σ := by
  obtain ⟨i, hi⟩ := exists_eq_sigmaMin hn σ
  exact hi ▸ hσ i

/-- `t ↦ ∏ i, (σ i + t)`, the function whose root at value `1` defines `R₊`. -/
noncomputable def Fpos (σ : Fin n → ℝ) (t : ℝ) : ℝ := ∏ i, (σ i + t)

/-- The unique `t > -min σ` with `∏ i, (σ i + t) = 1`. -/
noncomputable def tstar (σ : Fin n → ℝ) : ℝ := sInf {t : ℝ | -sigmaMin σ ≤ t ∧ 1 ≤ Fpos σ t}

/-- `R₊(σ)`, the value of the positive-product scalar minimax problem. -/
noncomputable def Rplus (σ : Fin n → ℝ) : ℝ := |tstar σ|

/-- `G₋(σ, r) = (r - min σ) * ∏_{i ≠ i_min} (r + σ i)`, written in a
permutation-invariant way. -/
noncomputable def Gneg (σ : Fin n → ℝ) (r : ℝ) : ℝ :=
  (r - sigmaMin σ) / (r + sigmaMin σ) * ∏ i, (r + σ i)

/-- `R₋(σ)`, the value of the negative-product scalar minimax problem: the unique
`r > min σ` with `(r - min σ) * ∏_{i ≠ i_min} (r + σ i) = 1`. -/
noncomputable def Rminus (σ : Fin n → ℝ) : ℝ := sInf {r : ℝ | sigmaMin σ ≤ r ∧ 1 ≤ Gneg σ r}

/-! ### Basic properties of `Fpos` -/

lemma Fpos_continuous (σ : Fin n → ℝ) : Continuous (Fpos σ) := by
  unfold Fpos; fun_prop

lemma Fpos_pos {t : ℝ} (ht : -sigmaMin σ < t) : 0 < Fpos σ t := by
  refine Finset.prod_pos ?_
  intro i _
  have : -σ i ≤ -sigmaMin σ := neg_le_neg (sigmaMin_le σ i)
  linarith

lemma Fpos_neg_sigmaMin (hn : 0 < n) : Fpos σ (-sigmaMin σ) = 0 := by
  obtain ⟨i, hi⟩ := exists_eq_sigmaMin hn σ
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [hi]; ring

lemma Fpos_strictMonoOn (hn : 0 < n) {s t : ℝ}
    (hs : -sigmaMin σ ≤ s) (hst : s < t) : Fpos σ s < Fpos σ t := by
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, Fpos_neg_sigmaMin hn]
    exact Fpos_pos (by rw [← h] at hst; exact hst)
  · refine Finset.prod_lt_prod_of_nonempty ?_ ?_ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    · intro i _
      have : -σ i ≤ -sigmaMin σ := neg_le_neg (sigmaMin_le σ i)
      linarith
    · intro i _; linarith

lemma Fpos_one_ge (hσ : ∀ i, 0 ≤ σ i) : 1 ≤ Fpos σ 1 := by
  have : (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
  rw [this]
  refine Finset.prod_le_prod (by intro i _; norm_num) ?_
  intro i _; linarith [hσ i]

/-- Existence and uniqueness of the root `t*`. -/
lemma tstar_spec (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) :
    -sigmaMin σ < tstar σ ∧ Fpos σ (tstar σ) = 1 ∧ tstar σ ≤ 1 := by
  have hm : (0:ℝ) ≤ sigmaMin σ := sigmaMin_nonneg hn hσ
  have hle : -sigmaMin σ ≤ 1 := by linarith
  -- a root exists in `[-min σ, 1]`
  have hIVT : (1:ℝ) ∈ Set.Icc (Fpos σ (-sigmaMin σ)) (Fpos σ 1) := by
    refine ⟨?_, Fpos_one_ge hσ⟩
    rw [Fpos_neg_sigmaMin hn]; norm_num
  obtain ⟨t₀, ht₀mem, ht₀⟩ :=
    intermediate_value_Icc hle (Fpos_continuous σ).continuousOn hIVT
  have ht₀pos : -sigmaMin σ < t₀ := by
    rcases eq_or_lt_of_le ht₀mem.1 with h | h
    · exfalso; rw [← h, Fpos_neg_sigmaMin hn] at ht₀; norm_num at ht₀
    · exact h
  -- the set whose infimum defines `tstar` is `[t₀, ∞)`
  have hset : {t : ℝ | -sigmaMin σ ≤ t ∧ 1 ≤ Fpos σ t} = Set.Ici t₀ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    constructor
    · rintro ⟨ht1, ht2⟩
      by_contra hlt
      push_neg at hlt
      have := Fpos_strictMonoOn hn ht1 hlt
      rw [ht₀] at this; linarith
    · intro ht
      refine ⟨le_trans ht₀mem.1 ht, ?_⟩
      rcases eq_or_lt_of_le ht with h | h
      · rw [← h, ht₀]
      · have := Fpos_strictMonoOn hn (le_of_lt ht₀pos) h
        rw [ht₀] at this; linarith
  have : tstar σ = t₀ := by
    unfold tstar; rw [hset]; exact csInf_Ici
  rw [this]
  exact ⟨ht₀pos, ht₀, ht₀mem.2⟩

lemma tstar_unique (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) {t : ℝ}
    (ht : -sigmaMin σ < t) (ht1 : Fpos σ t = 1) : t = tstar σ := by
  obtain ⟨h1, h2, -⟩ := tstar_spec hn hσ
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := Fpos_strictMonoOn hn (le_of_lt ht) h; rw [ht1, h2] at this; linarith
  · have := Fpos_strictMonoOn hn (le_of_lt h1) h; rw [ht1, h2] at this; linarith

/-! ### The positive-product scalar problem -/

lemma Fpos_zero (σ : Fin n → ℝ) : Fpos σ 0 = ∏ i, σ i := by
  unfold Fpos; simp

lemma Rplus_nonneg (σ : Fin n → ℝ) : 0 ≤ Rplus σ := abs_nonneg _

/-- Case `∏ σ < 1`: `R₊ > 0` is the unique root of `∏ (σ i + r) = 1`. -/
lemma Rplus_of_prod_lt_one (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) (hp : ∏ i, σ i < 1) :
    0 < Rplus σ ∧ ∏ i, (σ i + Rplus σ) = 1 := by
  obtain ⟨h1, h2, -⟩ := tstar_spec hn hσ
  have hpos : 0 < tstar σ := by
    by_contra h
    push_neg at h
    rcases eq_or_lt_of_le h with h' | h'
    · rw [h'] at h2; rw [Fpos_zero] at h2; linarith
    · have := Fpos_strictMonoOn hn (le_of_lt h1) h'
      rw [h2, Fpos_zero] at this; linarith
  have : Rplus σ = tstar σ := abs_of_pos hpos
  rw [this]
  exact ⟨hpos, h2⟩

/-- Case `∏ σ = 1`: the distance is `0`. -/
lemma Rplus_of_prod_eq_one (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) (hp : ∏ i, σ i = 1) :
    Rplus σ = 0 := by
  have hm : (0:ℝ) ≤ sigmaMin σ := sigmaMin_nonneg hn hσ
  have hmpos : -sigmaMin σ < 0 := by
    rcases eq_or_lt_of_le hm with h | h
    · exfalso
      obtain ⟨i, hi⟩ := exists_eq_sigmaMin hn σ
      have : ∏ j, σ j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, ← h])
      rw [this] at hp; norm_num at hp
    · linarith
  have := tstar_unique hn hσ hmpos (by rw [Fpos_zero]; exact hp)
  unfold Rplus; rw [← this]; simp

/-- Case `∏ σ > 1`: `R₊ ∈ (0, min σ)` is the unique root of `∏ (σ i - r) = 1`. -/
lemma Rplus_of_one_lt_prod (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) (hp : 1 < ∏ i, σ i) :
    0 < Rplus σ ∧ Rplus σ < sigmaMin σ ∧ ∏ i, (σ i - Rplus σ) = 1 := by
  obtain ⟨h1, h2, -⟩ := tstar_spec hn hσ
  have hneg : tstar σ < 0 := by
    by_contra h
    push_neg at h
    rcases eq_or_lt_of_le h with h' | h'
    · rw [← h', Fpos_zero] at h2; linarith
    · have hm : (0:ℝ) ≤ sigmaMin σ := sigmaMin_nonneg hn hσ
      have := Fpos_strictMonoOn hn (by linarith : -sigmaMin σ ≤ (0:ℝ)) h'
      rw [h2, Fpos_zero] at this; linarith
  have hR : Rplus σ = -tstar σ := abs_of_neg hneg
  refine ⟨by rw [hR]; linarith, by rw [hR]; linarith, ?_⟩
  have : ∀ i, σ i - Rplus σ = σ i + tstar σ := by intro i; rw [hR]; ring
  simp only [this]
  exact h2

/-- The scalar minimax value for the constraint `∏ x = 1` is `R₊(σ)`, and it is attained. -/
theorem scalar_pos_isLeast (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) :
    IsLeast {r : ℝ | ∃ x : Fin n → ℝ, (∏ i, x i) = 1 ∧ ∀ i, |σ i - x i| ≤ r} (Rplus σ) := by
  obtain ⟨h1, h2, -⟩ := tstar_spec hn hσ
  constructor
  · refine ⟨fun i => σ i + tstar σ, h2, ?_⟩
    intro i
    have : σ i - (σ i + tstar σ) = -tstar σ := by ring
    rw [this, abs_neg]
    exact le_of_eq rfl
  · rintro r ⟨x, hx, hxd⟩
    have hr0 : 0 ≤ r := le_trans (abs_nonneg _) (hxd ⟨0, hn⟩)
    have hm : (0:ℝ) ≤ sigmaMin σ := sigmaMin_nonneg hn hσ
    by_contra hlt
    push_neg at hlt
    rcases le_or_gt 0 (tstar σ) with hts | hts
    · -- `R₊ = tstar σ > r`
      have hR : Rplus σ = tstar σ := abs_of_nonneg hts
      have hbound : (1:ℝ) ≤ Fpos σ r := by
        have : (1:ℝ) = ∏ i, |x i| := by rw [← Finset.abs_prod, hx]; norm_num
        rw [this]
        refine Finset.prod_le_prod (fun i _ => abs_nonneg _) ?_
        intro i _
        have := hxd i
        have h1 : |x i| - |σ i| ≤ |σ i - x i| := by
          have := abs_sub_abs_le_abs_sub (x i) (σ i)
          rwa [abs_sub_comm (x i) (σ i)] at this
        have h2 : |σ i| = σ i := abs_of_nonneg (hσ i)
        linarith
      have := Fpos_strictMonoOn hn (by linarith : -sigmaMin σ ≤ r) (by rw [hR] at hlt; exact hlt)
      rw [h2] at this; linarith
    · -- `R₊ = -tstar σ > r`
      have hR : Rplus σ = -tstar σ := abs_of_neg hts
      rw [hR] at hlt
      have hrm : -r > -sigmaMin σ := by linarith
      have hbound : Fpos σ (-r) ≤ 1 := by
        rw [← hx]
        refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
        · have : -σ i ≤ -sigmaMin σ := neg_le_neg (sigmaMin_le σ i)
          linarith
        · have := hxd i
          have := abs_le.mp (hxd i)
          linarith [this.1, this.2]
      have := Fpos_strictMonoOn hn (le_of_lt h1) (by linarith : tstar σ < -r)
      rw [h2] at this; linarith

/-! ### The negative-product scalar problem -/

/-- `Gneg` written with an explicit index realizing the minimum. -/
lemma Gneg_eq_erase (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) {j : Fin n} (hj : σ j = sigmaMin σ)
    {r : ℝ} (hr : sigmaMin σ < r) :
    Gneg σ r = (r - σ j) * ∏ i ∈ Finset.univ.erase j, (r + σ i) := by
  have hm : (0:ℝ) ≤ sigmaMin σ := sigmaMin_nonneg hn hσ
  have hrm : (0:ℝ) < r + sigmaMin σ := by linarith
  have hprod : ∏ i, (r + σ i) = (r + σ j) * ∏ i ∈ Finset.univ.erase j, (r + σ i) :=
    (Finset.mul_prod_erase Finset.univ (fun i => r + σ i) (Finset.mem_univ j)).symm
  unfold Gneg
  rw [hprod, hj]
  field_simp

/-- Putting the negative coordinate at a smallest singular value is optimal. -/
lemma Gneg_le_of_index (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) {k : Fin n} {r : ℝ}
    (hr : σ k < r) :
    (r - σ k) * ∏ i ∈ Finset.univ.erase k, (r + σ i) ≤ Gneg σ r := by
  have hm : (0:ℝ) ≤ sigmaMin σ := sigmaMin_nonneg hn hσ
  have hk : sigmaMin σ ≤ σ k := sigmaMin_le σ k
  have hr0 : 0 < r := lt_of_le_of_lt (hσ k) hr
  have hP : 0 ≤ ∏ i ∈ Finset.univ.erase k, (r + σ i) :=
    Finset.prod_nonneg (fun i _ => by linarith [hσ i])
  have hprod : ∏ i, (r + σ i) = (r + σ k) * ∏ i ∈ Finset.univ.erase k, (r + σ i) :=
    (Finset.mul_prod_erase Finset.univ (fun i => r + σ i) (Finset.mem_univ k)).symm
  have key : r - σ k ≤ (r - sigmaMin σ) / (r + sigmaMin σ) * (r + σ k) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : (0:ℝ) < r + sigmaMin σ)]
    nlinarith
  calc (r - σ k) * ∏ i ∈ Finset.univ.erase k, (r + σ i)
      ≤ ((r - sigmaMin σ) / (r + sigmaMin σ) * (r + σ k))
          * ∏ i ∈ Finset.univ.erase k, (r + σ i) := mul_le_mul_of_nonneg_right key hP
    _ = Gneg σ r := by unfold Gneg; rw [hprod]; ring

lemma Gneg_sigmaMin (σ : Fin n → ℝ) : Gneg σ (sigmaMin σ) = 0 := by
  unfold Gneg; simp

lemma Gneg_pos (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) {r : ℝ} (hr : sigmaMin σ < r) :
    0 < Gneg σ r := by
  obtain ⟨j, hj⟩ := exists_eq_sigmaMin hn σ
  have hm : (0:ℝ) ≤ sigmaMin σ := sigmaMin_nonneg hn hσ
  rw [Gneg_eq_erase hn hσ hj hr]
  have hP : 0 < ∏ i ∈ Finset.univ.erase j, (r + σ i) :=
    Finset.prod_pos (fun i _ => by linarith [hσ i])
  have : 0 < r - σ j := by rw [hj]; linarith
  positivity

lemma Gneg_strictMonoOn (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) {s t : ℝ}
    (hs : sigmaMin σ ≤ s) (hst : s < t) : Gneg σ s < Gneg σ t := by
  obtain ⟨j, hj⟩ := exists_eq_sigmaMin hn σ
  have hm : (0:ℝ) ≤ sigmaMin σ := sigmaMin_nonneg hn hσ
  have htm : sigmaMin σ < t := lt_of_le_of_lt hs hst
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, Gneg_sigmaMin σ]
    exact Gneg_pos hn hσ htm
  · rw [Gneg_eq_erase hn hσ hj h, Gneg_eq_erase hn hσ hj htm]
    have hPs : 0 < ∏ i ∈ Finset.univ.erase j, (s + σ i) :=
      Finset.prod_pos (fun i _ => by linarith [hσ i])
    have hPle : ∏ i ∈ Finset.univ.erase j, (s + σ i)
        ≤ ∏ i ∈ Finset.univ.erase j, (t + σ i) := by
      refine Finset.prod_le_prod (fun i _ => by linarith [hσ i]) (fun i _ => by linarith)
    have hsj : 0 < s - σ j := by rw [hj]; linarith
    nlinarith

lemma Rminus_spec (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) :
    sigmaMin σ < Rminus σ ∧ Gneg σ (Rminus σ) = 1 := by
  obtain ⟨j, hj⟩ := exists_eq_sigmaMin hn σ
  have hm : (0:ℝ) ≤ sigmaMin σ := sigmaMin_nonneg hn hσ
  set m := sigmaMin σ with hmdef
  -- the polynomial version of `Gneg`
  set H : ℝ → ℝ := fun r => (r - σ j) * ∏ i ∈ Finset.univ.erase j, (r + σ i) with hH
  have hHcont : Continuous H := by rw [hH]; fun_prop
  have hHm : H m = 0 := by
    show (m - σ j) * ∏ i ∈ Finset.univ.erase j, (m + σ i) = 0
    simp [hj]
  have hHm1 : 1 ≤ H (m + 1) := by
    show 1 ≤ (m + 1 - σ j) * ∏ i ∈ Finset.univ.erase j, (m + 1 + σ i)
    have h1 : (m + 1 - σ j) = 1 := by rw [hj]; ring
    rw [h1, one_mul]
    calc (1:ℝ) = ∏ _i ∈ Finset.univ.erase j, (1:ℝ) := by simp
      _ ≤ ∏ i ∈ Finset.univ.erase j, (m + 1 + σ i) := by
          refine Finset.prod_le_prod (fun i _ => by norm_num) (fun i _ => by linarith [hσ i])
  obtain ⟨r₀, hr₀mem, hr₀⟩ :=
    intermediate_value_Icc (by linarith : m ≤ m + 1) hHcont.continuousOn
      (show (1:ℝ) ∈ Set.Icc (H m) (H (m+1)) by rw [hHm]; exact ⟨by norm_num, hHm1⟩)
  have hr₀pos : m < r₀ := by
    rcases eq_or_lt_of_le hr₀mem.1 with h | h
    · exfalso; rw [← h, hHm] at hr₀; norm_num at hr₀
    · exact h
  have hGr₀ : Gneg σ r₀ = 1 := by rw [Gneg_eq_erase hn hσ hj hr₀pos]; exact hr₀
  have hset : {r : ℝ | m ≤ r ∧ 1 ≤ Gneg σ r} = Set.Ici r₀ := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    constructor
    · rintro ⟨h1, h2⟩
      by_contra hlt
      push_neg at hlt
      have := Gneg_strictMonoOn hn hσ h1 hlt
      rw [hGr₀] at this; linarith
    · intro hr
      refine ⟨le_trans hr₀mem.1 hr, ?_⟩
      rcases eq_or_lt_of_le hr with h | h
      · rw [← h, hGr₀]
      · have := Gneg_strictMonoOn hn hσ (le_of_lt hr₀pos) h
        rw [hGr₀] at this; linarith
  have hR : Rminus σ = r₀ := by unfold Rminus; rw [← hmdef, hset]; exact csInf_Ici
  exact ⟨by rw [hR]; exact hr₀pos, by rw [hR]; exact hGr₀⟩

lemma Rminus_unique (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) {r : ℝ}
    (hr : sigmaMin σ < r) (h1 : Gneg σ r = 1) : r = Rminus σ := by
  obtain ⟨hR1, hR2⟩ := Rminus_spec hn hσ
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := Gneg_strictMonoOn hn hσ (le_of_lt hr) h; rw [h1, hR2] at this; linarith
  · have := Gneg_strictMonoOn hn hσ (le_of_lt hR1) h; rw [h1, hR2] at this; linarith

lemma Rminus_pos (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) : 0 < Rminus σ :=
  lt_of_le_of_lt (sigmaMin_nonneg hn hσ) (Rminus_spec hn hσ).1

/-- The root equation for `R₋` in the form printed in the problem: for any index `j`
realizing the minimum, `(R₋ - σ j) * ∏_{i ≠ j} (R₋ + σ i) = 1`. -/
lemma Rminus_root (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) {j : Fin n} (hj : σ j = sigmaMin σ) :
    (Rminus σ - σ j) * ∏ i ∈ Finset.univ.erase j, (Rminus σ + σ i) = 1 := by
  obtain ⟨hR1, hR2⟩ := Rminus_spec hn hσ
  rw [← Gneg_eq_erase hn hσ hj hR1]; exact hR2

/-- The scalar minimax value for the constraint `∏ x = -1` is `R₋(σ)`, and it is attained. -/
theorem scalar_neg_isLeast (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) :
    IsLeast {r : ℝ | ∃ x : Fin n → ℝ, (∏ i, x i) = -1 ∧ ∀ i, |σ i - x i| ≤ r} (Rminus σ) := by
  obtain ⟨j, hj⟩ := exists_eq_sigmaMin hn σ
  obtain ⟨hR1, hR2⟩ := Rminus_spec hn hσ
  have hRpos : 0 < Rminus σ := Rminus_pos hn hσ
  constructor
  · -- the attaining vector
    refine ⟨Function.update (fun i => σ i + Rminus σ) j (σ j - Rminus σ), ?_, ?_⟩
    · have hupd : ∀ i ∈ Finset.univ.erase j,
          Function.update (fun i => σ i + Rminus σ) j (σ j - Rminus σ) i = σ i + Rminus σ := by
        intro i hi
        exact Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
        Finset.prod_congr rfl hupd, Function.update_self]
      have hroot := Rminus_root hn hσ hj
      have hcomm : ∏ i ∈ Finset.univ.erase j, (σ i + Rminus σ)
          = ∏ i ∈ Finset.univ.erase j, (Rminus σ + σ i) :=
        Finset.prod_congr rfl (fun i _ => add_comm _ _)
      rw [hcomm]
      have : (σ j - Rminus σ) * ∏ i ∈ Finset.univ.erase j, (Rminus σ + σ i)
          = -((Rminus σ - σ j) * ∏ i ∈ Finset.univ.erase j, (Rminus σ + σ i)) := by ring
      rw [this, hroot]
    · intro i
      by_cases hij : i = j
      · subst hij
        rw [Function.update_self]
        have : σ i - (σ i - Rminus σ) = Rminus σ := by ring
        rw [this, abs_of_pos hRpos]
      · rw [Function.update_of_ne hij]
        have : σ i - (σ i + Rminus σ) = -Rminus σ := by ring
        rw [this, abs_neg, abs_of_pos hRpos]
  · -- the lower bound
    rintro r ⟨x, hx, hxd⟩
    -- some coordinate is negative
    have hneg : ∃ k, x k < 0 := by
      by_contra h
      push_neg at h
      have : (0:ℝ) ≤ ∏ i, x i := Finset.prod_nonneg (fun i _ => h i)
      rw [hx] at this; linarith
    obtain ⟨k, hk⟩ := hneg
    have hxk : |x k| = -x k := abs_of_neg hk
    have hdk := abs_le.mp (hxd k)
    have hrk : σ k < r := by
      have : σ k - x k ≤ r := hdk.2
      linarith
    have habs : ∀ i, |x i| ≤ r + σ i := by
      intro i
      have := abs_le.mp (hxd i)
      rcases abs_cases (x i) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;>
        linarith [this.1, this.2, hσ i]
    have hprod1 : ∏ i, |x i| = 1 := by
      rw [← Finset.abs_prod, hx]; norm_num
    have hle : (1:ℝ) ≤ (r - σ k) * ∏ i ∈ Finset.univ.erase k, (r + σ i) := by
      rw [← hprod1, ← Finset.mul_prod_erase Finset.univ (fun i => |x i|) (Finset.mem_univ k)]
      refine mul_le_mul ?_ ?_ (Finset.prod_nonneg (fun i _ => abs_nonneg _)) (by linarith)
      · rw [hxk]; linarith [hdk.2]
      · exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => habs i)
    have hmem : r ∈ {r : ℝ | sigmaMin σ ≤ r ∧ 1 ≤ Gneg σ r} := by
      refine ⟨le_of_lt (lt_of_le_of_lt (sigmaMin_le σ k) hrk), ?_⟩
      exact le_trans hle (Gneg_le_of_index hn hσ hrk)
    refine csInf_le ⟨sigmaMin σ, ?_⟩ hmem
    rintro y ⟨hy, -⟩; exact hy

end Scalar

/-! ## The complex scalar minimax problem -/

section ComplexScalar

variable {n : ℕ} {σ : Fin n → ℝ}

/-- The complex scalar minimax value
`inf { max_i |σ i - z i| : z : Fin n → ℂ, ∏ i, z i = η }`. -/
noncomputable def cmin (σ : Fin n → ℝ) (η : ℂ) : ℝ :=
  sInf {r : ℝ | ∃ z : Fin n → ℂ, (∏ i, z i) = η ∧ ∀ i, ‖(σ i : ℂ) - z i‖ ≤ r}

lemma mx_lipschitz : LipschitzWith 1 (mx : (Fin n → ℝ) → ℝ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    intro u v
    simp [mx]
  refine LipschitzWith.of_dist_le_mul (fun u v => ?_)
  have key : ∀ a b : Fin n → ℝ, mx a ≤ mx b + dist a b := by
    intro a b
    refine mx_le hn (fun i => ?_)
    have h1 : a i - b i ≤ dist a b := by
      have := dist_le_pi_dist a b i
      have : |a i - b i| ≤ dist a b := by
        simpa [Real.dist_eq] using this
      cases abs_le.mp this with
      | intro h1 h2 => linarith
    have := le_mx b i
    linarith
  have h1 := key u v
  have h2 := key v u
  rw [dist_comm v u] at h2
  rw [Real.dist_eq, abs_le]
  simp only [NNReal.coe_one, one_mul]
  constructor <;> linarith

lemma mx_continuous : Continuous (mx : (Fin n → ℝ) → ℝ) :=
  mx_lipschitz.continuous

/-- The complex scalar minimax value is attained. -/
theorem cmin_isLeast (hn : 0 < n) (η : ℂ) :
    IsLeast {r : ℝ | ∃ z : Fin n → ℂ, (∏ i, z i) = η ∧ ∀ i, ‖(σ i : ℂ) - z i‖ ≤ r}
      (cmin σ η) := by
  classical
  set f : (Fin n → ℂ) → ℝ := fun z => mx (fun i => ‖(σ i : ℂ) - z i‖) with hf
  have hfcont : Continuous f := by
    refine mx_continuous.comp ?_
    refine continuous_pi (fun i => ?_)
    fun_prop
  -- a first feasible point
  set j₀ : Fin n := ⟨0, hn⟩ with hj₀
  set z₀ : Fin n → ℂ := Function.update (fun _ => (1 : ℂ)) j₀ η with hz₀
  have hz₀prod : (∏ i, z₀ i) = η := by
    rw [hz₀, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀), Function.update_self]
    have : ∀ i ∈ Finset.univ.erase j₀,
        Function.update (fun _ => (1:ℂ)) j₀ η i = 1 := fun i hi =>
      Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
    rw [Finset.prod_congr rfl this]
    simp
  set r₀ : ℝ := f z₀ with hr₀
  -- the compact feasible set
  set K : Set (Fin n → ℂ) := {z | (∏ i, z i) = η ∧ ∀ i, ‖(σ i : ℂ) - z i‖ ≤ r₀} with hK
  have hz₀K : z₀ ∈ K := ⟨hz₀prod, fun i => le_mx (fun i => ‖(σ i : ℂ) - z₀ i‖) i⟩
  have hKclosed : IsClosed K := by
    have h1 : IsClosed {z : Fin n → ℂ | (∏ i, z i) = η} :=
      isClosed_eq (by fun_prop) continuous_const
    have h2 : ∀ i : Fin n, IsClosed {z : Fin n → ℂ | ‖(σ i : ℂ) - z i‖ ≤ r₀} := by
      intro i
      exact isClosed_le (by fun_prop) continuous_const
    have : K = {z : Fin n → ℂ | (∏ i, z i) = η} ∩ ⋂ i, {z : Fin n → ℂ | ‖(σ i : ℂ) - z i‖ ≤ r₀} := by
      ext z; simp [hK, Set.mem_iInter]
    rw [this]
    exact h1.inter (isClosed_iInter h2)
  have hr₀nonneg : 0 ≤ r₀ := by
    have := le_mx (fun i => ‖(σ i : ℂ) - z₀ i‖) ⟨0, hn⟩
    exact le_trans (norm_nonneg _) this
  set C : ℝ := (mx fun i => |σ i|) + r₀ with hC
  have hKsub : K ⊆ Metric.closedBall (0 : Fin n → ℂ) C := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    refine pi_norm_le_iff_of_nonneg ?_ |>.mpr ?_
    · have : 0 ≤ mx fun i => |σ i| :=
        le_trans (abs_nonneg (σ ⟨0, hn⟩)) (le_mx (fun i => |σ i|) ⟨0, hn⟩)
      linarith
    · intro i
      have h1 : ‖z i‖ ≤ ‖(σ i : ℂ)‖ + ‖(σ i : ℂ) - z i‖ := by
        have heq : z i = (σ i : ℂ) - ((σ i : ℂ) - z i) := by ring
        calc ‖z i‖ = ‖(σ i : ℂ) - ((σ i : ℂ) - z i)‖ := by rw [← heq]
          _ ≤ ‖(σ i : ℂ)‖ + ‖(σ i : ℂ) - z i‖ := norm_sub_le _ _
      have h2 : ‖(σ i : ℂ)‖ = |σ i| := by simp
      have h3 := hz.2 i
      have h4 : |σ i| ≤ mx fun i => |σ i| := le_mx (fun i => |σ i|) i
      rw [h2] at h1
      linarith
  have hKcompact : IsCompact K :=
    (isCompact_closedBall (0 : Fin n → ℂ) C).of_isClosed_subset hKclosed hKsub
  obtain ⟨z₁, hz₁K, hz₁min⟩ := hKcompact.exists_isMinOn ⟨z₀, hz₀K⟩ hfcont.continuousOn
  have hleast : IsLeast {r : ℝ | ∃ z : Fin n → ℂ, (∏ i, z i) = η ∧ ∀ i, ‖(σ i : ℂ) - z i‖ ≤ r}
      (f z₁) := by
    constructor
    · exact ⟨z₁, hz₁K.1, fun i => le_mx (fun i => ‖(σ i : ℂ) - z₁ i‖) i⟩
    · rintro r ⟨z, hzp, hzd⟩
      have hfz : f z ≤ r := mx_le hn hzd
      by_cases hcase : r ≤ r₀
      · have hzK : z ∈ K := ⟨hzp, fun i => le_trans (hzd i) hcase⟩
        exact le_trans (hz₁min hzK) hfz
      · push_neg at hcase
        have : f z₁ ≤ r₀ := mx_le hn hz₁K.2
        linarith
  have : cmin σ η = f z₁ := hleast.csInf_eq
  rw [this]
  exact hleast

/-- For `η = 1` the complex scalar problem has the same value `R₊(σ)` as the real one,
including the case of zero singular values. -/
theorem cmin_one_isLeast (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) :
    IsLeast {r : ℝ | ∃ z : Fin n → ℂ, (∏ i, z i) = 1 ∧ ∀ i, ‖(σ i : ℂ) - z i‖ ≤ r}
      (Rplus σ) := by
  obtain ⟨⟨x, hx, hxd⟩, hlb⟩ := scalar_pos_isLeast hn hσ
  constructor
  · refine ⟨fun i => (x i : ℂ), ?_, ?_⟩
    · rw [← Complex.ofReal_prod, hx]; norm_num
    · intro i
      have hcast : ((σ i : ℂ) - (x i : ℂ)) = ((σ i - x i : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      exact hxd i
  · rintro r ⟨z, hzp, hzd⟩
    refine hlb ⟨fun i => ‖z i‖, ?_, ?_⟩
    · have : ∏ i, ‖z i‖ = ‖∏ i, z i‖ := by rw [norm_prod]
      rw [this, hzp]; norm_num
    · intro i
      have h1 : |σ i - ‖z i‖| ≤ ‖(σ i : ℂ) - z i‖ := by
        have h2 : ‖(σ i : ℂ)‖ = |σ i| := by simp
        have := abs_norm_sub_norm_le ((σ i : ℂ)) (z i)
        rw [h2, abs_of_nonneg (hσ i)] at this
        exact this
      exact le_trans h1 (hzd i)

theorem cmin_one (hn : 0 < n) (hσ : ∀ i, 0 ≤ σ i) : cmin σ 1 = Rplus σ :=
  (cmin_one_isLeast hn hσ).csInf_eq

end ComplexScalar

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-! ## The action of a matrix on Euclidean space -/

/-- The action of a square matrix on Euclidean space. -/
noncomputable def app (A : Matrix (Fin n) (Fin n) 𝕜) (x : EuclideanSpace 𝕜 (Fin n)) :
    EuclideanSpace 𝕜 (Fin n) :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) A x

lemma app_sub (A B : Matrix (Fin n) (Fin n) 𝕜) (x : EuclideanSpace 𝕜 (Fin n)) :
    app (A - B) x = app A x - app B x := by
  simp [app, map_sub]

lemma app_mul (A B : Matrix (Fin n) (Fin n) 𝕜) (x : EuclideanSpace 𝕜 (Fin n)) :
    app (A * B) x = app A (app B x) := by
  simp [app, map_mul]

lemma app_one (x : EuclideanSpace 𝕜 (Fin n)) : app (1 : Matrix (Fin n) (Fin n) 𝕜) x = x := by
  simp [app]

lemma norm_app_le (A : Matrix (Fin n) (Fin n) 𝕜) (x : EuclideanSpace 𝕜 (Fin n)) :
    ‖app A x‖ ≤ ‖A‖ * ‖x‖ := by
  rw [app, ← Matrix.l2_opNorm_toEuclideanCLM A]
  exact (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) A).le_opNorm x

lemma opNorm_le_of_forall {A : Matrix (Fin n) (Fin n) 𝕜} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : EuclideanSpace 𝕜 (Fin n), ‖app A x‖ ≤ c * ‖x‖) : ‖A‖ ≤ c := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM A]
  exact ContinuousLinearMap.opNorm_le_bound _ hc h

lemma app_eq_zero_of_mulVec (A : Matrix (Fin n) (Fin n) 𝕜) (x : EuclideanSpace 𝕜 (Fin n)) :
    app A x = WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) := rfl

/-! ## Operator norm toolkit -/

lemma norm_one_matrix (hn : 0 < n) : ‖(1 : Matrix (Fin n) (Fin n) 𝕜)‖ = 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← diagonal_one, Matrix.l2_opNorm_diagonal]
  simp

lemma norm_unitary (hn : 0 < n) {U : Matrix (Fin n) (Fin n) 𝕜}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) 𝕜) : ‖U‖ = 1 := by
  have h1 : Uᴴ * U = 1 := by
    have := hU.1
    rwa [Matrix.star_eq_conjTranspose] at this
  have h2 : ‖U‖ * ‖U‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self U, h1, norm_one_matrix hn]
  nlinarith [norm_nonneg U]

lemma norm_conjTranspose_unitary (hn : 0 < n) {U : Matrix (Fin n) (Fin n) 𝕜}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) 𝕜) : ‖Uᴴ‖ = 1 := by
  rw [Matrix.l2_opNorm_conjTranspose]; exact norm_unitary hn hU

lemma norm_app_unitary (hn : 0 < n) {U : Matrix (Fin n) (Fin n) 𝕜}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) 𝕜) (x : EuclideanSpace 𝕜 (Fin n)) :
    ‖app U x‖ = ‖x‖ := by
  have h1 : Uᴴ * U = 1 := by
    have := hU.1
    rwa [Matrix.star_eq_conjTranspose] at this
  have hle : ‖app U x‖ ≤ ‖x‖ := by
    have := norm_app_le U x
    rw [norm_unitary hn hU, one_mul] at this; exact this
  have hge : ‖x‖ ≤ ‖app U x‖ := by
    have hxx : app Uᴴ (app U x) = x := by rw [← app_mul, h1, app_one]
    have := norm_app_le Uᴴ (app U x)
    rw [hxx, norm_conjTranspose_unitary hn hU, one_mul] at this
    exact this
  linarith

lemma norm_unitary_mul (hn : 0 < n) {U : Matrix (Fin n) (Fin n) 𝕜}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜) :
    ‖U * A‖ = ‖A‖ := by
  have h1 : Uᴴ * U = 1 := by
    have := hU.1
    rwa [Matrix.star_eq_conjTranspose] at this
  have hle : ‖U * A‖ ≤ ‖A‖ := by
    have := Matrix.l2_opNorm_mul U A
    rw [norm_unitary hn hU, one_mul] at this; exact this
  have hge : ‖A‖ ≤ ‖U * A‖ := by
    have heq : Uᴴ * (U * A) = A := by rw [← mul_assoc, h1, one_mul]
    have := Matrix.l2_opNorm_mul Uᴴ (U * A)
    rw [heq, norm_conjTranspose_unitary hn hU, one_mul] at this
    exact this
  linarith

lemma norm_mul_unitary (hn : 0 < n) {V : Matrix (Fin n) (Fin n) 𝕜}
    (hV : V ∈ Matrix.unitaryGroup (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜) :
    ‖A * V‖ = ‖A‖ := by
  have h1 : V * Vᴴ = 1 := by
    have := hV.2
    rwa [Matrix.star_eq_conjTranspose] at this
  have hle : ‖A * V‖ ≤ ‖A‖ := by
    have := Matrix.l2_opNorm_mul A V
    rw [norm_unitary hn hV, mul_one] at this; exact this
  have hge : ‖A‖ ≤ ‖A * V‖ := by
    have heq : (A * V) * Vᴴ = A := by rw [mul_assoc, h1, mul_one]
    have := Matrix.l2_opNorm_mul (A * V) Vᴴ
    rw [heq, norm_conjTranspose_unitary hn hV, mul_one] at this
    exact this
  linarith

lemma pi_norm_eq_mx (hn : 0 < n) (v : Fin n → 𝕜) : ‖v‖ = mx (fun i => ‖v i‖) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg ?_).mpr (fun i => le_mx (fun i => ‖v i‖) i)
    exact le_trans (norm_nonneg (v ⟨0, hn⟩)) (le_mx (fun i => ‖v i‖) ⟨0, hn⟩)
  · exact mx_le hn (fun i => norm_le_pi_norm v i)

lemma norm_diagonal_eq_mx (hn : 0 < n) (v : Fin n → 𝕜) :
    ‖(diagonal v : Matrix (Fin n) (Fin n) 𝕜)‖ = mx (fun i => ‖v i‖) := by
  rw [Matrix.l2_opNorm_diagonal, pi_norm_eq_mx hn]

/-! ## Coordinate subspaces of Euclidean space -/

lemma le_of_sq_le_sq' {a b : ℝ} (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : a ≤ b := by
  nlinarith

variable (𝕜) in
/-- The subspace of vectors supported in the finite set `I`. -/
def coordSubspace (I : Finset (Fin n)) : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)) where
  carrier := {x | ∀ j ∉ I, x j = 0}
  add_mem' := by intro a b ha hb j hj; simp [ha j hj, hb j hj]
  zero_mem' := by intro j _; rfl
  smul_mem' := by intro c a ha j hj; simp [ha j hj]

lemma mem_coordSubspace {I : Finset (Fin n)} {x : EuclideanSpace 𝕜 (Fin n)} :
    x ∈ coordSubspace 𝕜 I ↔ ∀ j ∉ I, x j = 0 := Iff.rfl

lemma coord_sum (I : Finset (Fin n)) (x : EuclideanSpace 𝕜 (Fin n)) (j : Fin n) :
    (∑ i ∈ I, (x i) • EuclideanSpace.single (𝕜 := 𝕜) i (1 : 𝕜)) j
      = if j ∈ I then x j else 0 := by
  rw [WithLp.ofLp_sum]
  simp only [WithLp.ofLp_smul, EuclideanSpace.ofLp_single, Finset.sum_apply, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq I j (fun i => x i)]

lemma coordSubspace_eq_span (I : Finset (Fin n)) :
    coordSubspace 𝕜 I
      = Submodule.span 𝕜 (Set.range (fun i : I => EuclideanSpace.single (i : Fin n) (1 : 𝕜))) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxsum : x = ∑ i ∈ I, x i • EuclideanSpace.single i (1 : 𝕜) := by
      refine PiLp.ext (fun j => ?_)
      rw [coord_sum I x j]
      by_cases hj : j ∈ I
      · rw [if_pos hj]
      · rw [if_neg hj, (mem_coordSubspace.mp hx) j hj]
    rw [hxsum]
    refine Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    intro j hj
    have hne : j ≠ (i : Fin n) := fun h => hj (h ▸ i.2)
    simp [EuclideanSpace.single_apply, hne]

lemma finrank_coordSubspace (I : Finset (Fin n)) :
    Module.finrank 𝕜 (coordSubspace 𝕜 I) = I.card := by
  classical
  have hli : LinearIndependent 𝕜 (fun i : I => EuclideanSpace.single (i : Fin n) (1 : 𝕜)) := by
    have hcoe : (fun i : Fin n => EuclideanSpace.single i (1 : 𝕜))
        = ⇑(EuclideanSpace.basisFun (Fin n) 𝕜) := by
      funext i; rw [EuclideanSpace.basisFun_apply]
    have hb : LinearIndependent 𝕜 (fun i : Fin n => EuclideanSpace.single i (1 : 𝕜)) := by
      rw [hcoe]
      exact (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis.linearIndependent
    exact hb.comp (fun i : I => (i : Fin n)) Subtype.val_injective
  rw [coordSubspace_eq_span, finrank_span_eq_card hli, Fintype.card_coe]

lemma norm_sq_app_diagonal (v : Fin n → 𝕜) (x : EuclideanSpace 𝕜 (Fin n)) :
    ‖app (diagonal v) x‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 * ‖x i‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : (app (diagonal v) x).ofLp i = v i * x i := by
    simp [app, Matrix.mulVec_diagonal]
  rw [this, norm_mul, mul_pow]

/-! ## Singular values via the Courant–Fischer max-min formula -/

/-- The set of `c ≥ 0` which are dominated by `‖A x‖ / ‖x‖` on some `k`-dimensional subspace. -/
def svSet (A : Matrix (Fin n) (Fin n) 𝕜) (k : ℕ) : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ ∃ W : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)),
      Module.finrank 𝕜 W = k ∧ ∀ x ∈ W, c * ‖x‖ ≤ ‖app A x‖}

/-- The `k`-th singular value of `A` (Courant–Fischer). -/
noncomputable def sv (A : Matrix (Fin n) (Fin n) 𝕜) (k : ℕ) : ℝ := sSup (svSet A k)

/-- The singular values of `A`, listed in decreasing order. -/
noncomputable def svals (A : Matrix (Fin n) (Fin n) 𝕜) (i : Fin n) : ℝ := sv A (i.1 + 1)

lemma svSet_bddAbove (A : Matrix (Fin n) (Fin n) 𝕜) {k : ℕ} (hk : 0 < k) :
    BddAbove (svSet A k) := by
  refine ⟨‖A‖, ?_⟩
  rintro c ⟨hc0, W, hW, hWx⟩
  have hWne : W ≠ ⊥ := by
    intro h
    rw [h] at hW
    simp at hW
    omega
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have h1 := hWx x hxW
  have h2 := norm_app_le A x
  have : c * ‖x‖ ≤ ‖A‖ * ‖x‖ := le_trans h1 h2
  exact le_of_mul_le_mul_right (by linarith) hxpos

lemma svSet_nonempty (A : Matrix (Fin n) (Fin n) 𝕜) {k : ℕ} (hk : k ≤ n) :
    (svSet A k).Nonempty := by
  classical
  obtain ⟨I, -, hI⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (n := k) (by simpa using hk)
  refine ⟨0, le_refl 0, coordSubspace 𝕜 I, ?_, ?_⟩
  · rw [finrank_coordSubspace, hI]
  · intro x _
    simp

lemma sv_nonneg (A : Matrix (Fin n) (Fin n) 𝕜) {k : ℕ} (hk : k ≤ n) (hk' : 0 < k) :
    0 ≤ sv A k := by
  classical
  obtain ⟨c, hc⟩ := svSet_nonempty A hk
  exact le_trans hc.1 (le_csSup (svSet_bddAbove A hk') hc)

lemma le_sv {A : Matrix (Fin n) (Fin n) 𝕜} {k : ℕ} (hk : 0 < k) {c : ℝ}
    (hc : c ∈ svSet A k) : c ≤ sv A k :=
  le_csSup (svSet_bddAbove A hk) hc

lemma sv_le {A : Matrix (Fin n) (Fin n) 𝕜} {k : ℕ} (hk : k ≤ n) {b : ℝ}
    (hb : ∀ c ∈ svSet A k, c ≤ b) : sv A k ≤ b :=
  csSup_le (svSet_nonempty A hk) hb

lemma svals_nonneg (A : Matrix (Fin n) (Fin n) 𝕜) (i : Fin n) : 0 ≤ svals A i :=
  sv_nonneg A i.2 (Nat.succ_pos _)

/-- Weyl's perturbation inequality. -/
lemma sv_perturb (A B : Matrix (Fin n) (Fin n) 𝕜) {k : ℕ} (hk : k ≤ n) (hk' : 0 < k) :
    sv A k - ‖A - B‖ ≤ sv B k := by
  have key : ∀ c ∈ svSet A k, c - ‖A - B‖ ≤ sv B k := by
    rintro c ⟨hc0, W, hW, hWx⟩
    rcases le_or_gt c ‖A - B‖ with hcase | hcase
    · have := sv_nonneg B hk hk'
      linarith
    · refine le_sv hk' ⟨by linarith, W, hW, fun x hx => ?_⟩
      have h1 := hWx x hx
      have h2 : ‖app A x‖ ≤ ‖app B x‖ + ‖A - B‖ * ‖x‖ := by
        have h3 : app A x = app B x + app (A - B) x := by
          rw [app_sub]; abel
        calc ‖app A x‖ = ‖app B x + app (A - B) x‖ := by rw [h3]
          _ ≤ ‖app B x‖ + ‖app (A - B) x‖ := norm_add_le _ _
          _ ≤ ‖app B x‖ + ‖A - B‖ * ‖x‖ := by
              have := norm_app_le (A - B) x; linarith
      nlinarith [norm_nonneg x]
  have hle : sv A k - ‖A - B‖ ≤ sv B k := by
    have h2 : sSup (svSet A k) ≤ sv B k + ‖A - B‖ := by
      refine csSup_le (svSet_nonempty A hk) (fun c hc => ?_)
      have := key c hc; linarith
    simpa [sv] using h2
  exact hle

lemma svals_le_add (A B : Matrix (Fin n) (Fin n) 𝕜) (i : Fin n) :
    svals A i ≤ svals B i + ‖A - B‖ := by
  have := sv_perturb A B (k := i.1 + 1) i.2 (Nat.succ_pos _)
  simpa [svals] using this

/-! ## The singular value decomposition -/

/-- The `i`-th column of a matrix, as a vector of Euclidean space. -/
noncomputable def colVec (B : Matrix (Fin n) (Fin n) 𝕜) (i : Fin n) :
    EuclideanSpace 𝕜 (Fin n) := WithLp.toLp 2 (fun j => B j i)

lemma inner_colVec (B : Matrix (Fin n) (Fin n) 𝕜) (i k : Fin n) :
    inner 𝕜 (colVec B i) (colVec B k) = (Bᴴ * B) i k := by
  rw [PiLp.inner_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [colVec, RCLike.inner_apply, Matrix.conjTranspose_apply, mul_comm]

lemma unitary_of_orthonormal_cols {b : Fin n → EuclideanSpace 𝕜 (Fin n)}
    (hb : Orthonormal 𝕜 b) :
    (Matrix.of fun j i => (b i) j : Matrix (Fin n) (Fin n) 𝕜) ∈
      Matrix.unitaryGroup (Fin n) 𝕜 := by
  classical
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i k
  have hik : inner 𝕜 (b i) (b k) = (if i = k then (1 : 𝕜) else 0) :=
    (orthonormal_iff_ite.mp hb) i k
  rw [Matrix.mul_apply]
  have : ∑ j, (Matrix.of fun j i => (b i) j : Matrix (Fin n) (Fin n) 𝕜)ᴴ i j *
      (Matrix.of fun j i => (b i) j : Matrix (Fin n) (Fin n) 𝕜) j k
      = inner 𝕜 (b i) (b k) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [RCLike.inner_apply, Matrix.conjTranspose_apply, mul_comm]
  rw [this, hik, Matrix.one_apply]

lemma norm_det_unitary {U : Matrix (Fin n) (Fin n) 𝕜}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) 𝕜) : ‖U.det‖ = 1 := by
  have h1 : Uᴴ * U = 1 := by
    have := hU.1; rwa [Matrix.star_eq_conjTranspose] at this
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h2
  have h3 : ‖star U.det * U.det‖ = 1 := by rw [h2, norm_one]
  rw [norm_mul, norm_star] at h3
  nlinarith [norm_nonneg U.det]

/-- Diagonalization of a positive semidefinite matrix with decreasing nonnegative eigenvalues. -/
lemma exists_sorted_spectral (H : Matrix (Fin n) (Fin n) 𝕜) (hH : H.PosSemidef) :
    ∃ (V : Matrix (Fin n) (Fin n) 𝕜) (mu : Fin n → ℝ),
      V ∈ Matrix.unitaryGroup (Fin n) 𝕜 ∧ (∀ i, 0 ≤ mu i) ∧ Antitone mu ∧
      H = V * diagonal (fun i => ((mu i : ℝ) : 𝕜)) * Vᴴ := by
  classical
  have hHerm : H.IsHermitian := hH.1
  set W : Matrix (Fin n) (Fin n) 𝕜 := (hHerm.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) with hWdef
  have hW : W ∈ Matrix.unitaryGroup (Fin n) 𝕜 := (hHerm.eigenvectorUnitary).2
  have hspec : H = W * diagonal (fun i => ((hHerm.eigenvalues i : ℝ) : 𝕜)) * Wᴴ := by
    conv_lhs => rw [hHerm.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, hWdef,
      Function.comp_def]
  set sigma : Equiv.Perm (Fin n) := Tuple.sort (fun i => -(hHerm.eigenvalues i)) with hsigdef
  refine ⟨W.submatrix id sigma, fun i => hHerm.eigenvalues (sigma i), ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    have hWW : Wᴴ * W = 1 := by
      have := hW.1; rwa [Matrix.star_eq_conjTranspose] at this
    ext i k
    have hentry : ((W.submatrix id sigma)ᴴ * W.submatrix id sigma) i k
        = (Wᴴ * W) (sigma i) (sigma k) := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hentry, hWW, Matrix.one_apply, Matrix.one_apply]
    simp
  · exact fun i => hH.eigenvalues_nonneg _
  · have hmono : Monotone ((fun i => -(hHerm.eigenvalues i)) ∘ sigma) :=
      Tuple.monotone_sort (fun i => -(hHerm.eigenvalues i))
    intro i j hij
    have := hmono hij
    simp only [Function.comp_apply] at this
    linarith
  · have hstep : (W.submatrix id sigma) *
        diagonal (fun i => ((hHerm.eigenvalues (sigma i) : ℝ) : 𝕜)) *
        (W.submatrix id sigma)ᴴ
        = W * diagonal (fun i => ((hHerm.eigenvalues i : ℝ) : 𝕜)) * Wᴴ := by
      have hd : diagonal (fun i => ((hHerm.eigenvalues (sigma i) : ℝ) : 𝕜))
          = (diagonal (fun i => ((hHerm.eigenvalues i : ℝ) : 𝕜))).submatrix sigma sigma := by
        rw [Matrix.submatrix_diagonal_equiv]; rfl
      have hc : (W.submatrix id sigma)ᴴ = Wᴴ.submatrix sigma id := rfl
      rw [hd, hc, Matrix.submatrix_mul_equiv W _ id sigma sigma,
        Matrix.submatrix_mul_equiv _ Wᴴ id sigma id, Matrix.submatrix_id_id]
    rw [hstep]; exact hspec

/-- Existence of a singular value decomposition with decreasing nonnegative diagonal. -/
theorem exists_svd (A : Matrix (Fin n) (Fin n) 𝕜) :
    ∃ (U V : Matrix (Fin n) (Fin n) 𝕜) (s : Fin n → ℝ),
      U ∈ Matrix.unitaryGroup (Fin n) 𝕜 ∧ V ∈ Matrix.unitaryGroup (Fin n) 𝕜 ∧
      (∀ i, 0 ≤ s i) ∧ Antitone s ∧
      A = U * diagonal (fun i => ((s i : ℝ) : 𝕜)) * Vᴴ := by
  classical
  obtain ⟨V, mu, hV, hmu0, hmuanti, hH⟩ :=
    exists_sorted_spectral (Aᴴ * A) (Matrix.posSemidef_conjTranspose_mul_self A)
  set s : Fin n → ℝ := fun i => Real.sqrt (mu i) with hsdef
  have hs0 : ∀ i, 0 ≤ s i := fun i => Real.sqrt_nonneg _
  have hsanti : Antitone s := fun i j hij => Real.sqrt_le_sqrt (hmuanti hij)
  have hssq : ∀ i, s i ^ 2 = mu i := fun i => Real.sq_sqrt (hmu0 i)
  set B : Matrix (Fin n) (Fin n) 𝕜 := A * V with hBdef
  have hVV : Vᴴ * V = 1 := by
    have := hV.1; rwa [Matrix.star_eq_conjTranspose] at this
  have hVV' : V * Vᴴ = 1 := by
    have := hV.2; rwa [Matrix.star_eq_conjTranspose] at this
  have hBB : Bᴴ * B = diagonal (fun i => ((mu i : ℝ) : 𝕜)) := by
    have : Bᴴ * B = Vᴴ * (Aᴴ * A) * V := by
      rw [hBdef, Matrix.conjTranspose_mul]; noncomm_ring
    rw [this, hH]
    rw [show Vᴴ * (V * diagonal (fun i => ((mu i : ℝ) : 𝕜)) * Vᴴ) * V
        = (Vᴴ * V) * diagonal (fun i => ((mu i : ℝ) : 𝕜)) * (Vᴴ * V) by noncomm_ring,
      hVV, one_mul, mul_one]
  have hinner : ∀ i k, inner 𝕜 (colVec B i) (colVec B k)
      = (if i = k then ((mu i : ℝ) : 𝕜) else 0) := by
    intro i k
    rw [inner_colVec, hBB, Matrix.diagonal_apply]
  set v : Fin n → EuclideanSpace 𝕜 (Fin n) := fun i => ((s i)⁻¹ : 𝕜) • colVec B i with hvdef
  have hSorth : Orthonormal 𝕜 ({i | s i ≠ 0}.restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨k, hk⟩
    have hi' : s i ≠ 0 := hi
    have hk' : s k ≠ 0 := hk
    simp only [Set.restrict_apply, hvdef, inner_smul_left, inner_smul_right, hinner]
    by_cases hik : i = k
    · subst hik
      have hmui : ((mu i : ℝ) : 𝕜) = ((s i : ℝ) : 𝕜) * ((s i : ℝ) : 𝕜) := by
        rw [← RCLike.ofReal_mul]; norm_cast; nlinarith [hssq i]
      have hsi : ((s i : ℝ) : 𝕜) ≠ 0 := by
        simpa using hi'
      simp only [hmui, if_pos]
      rw [starRingEnd_apply, star_inv₀]
      simp only [RCLike.star_def, RCLike.conj_ofReal]
      field_simp
    · simp [hik]
  have hcard : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = Fintype.card (Fin n) :=
    finrank_euclideanSpace
  obtain ⟨b, hb⟩ := hSorth.exists_orthonormalBasis_extension_of_card_eq hcard
  refine ⟨Matrix.of fun j i => (b i) j, V, s, unitary_of_orthonormal_cols b.orthonormal,
    hV, hs0, hsanti, ?_⟩
  have hcol : ∀ i j, s i * (b i) j = B j i := by
    intro i j
    by_cases hi : s i = 0
    · have hz : colVec B i = 0 := by
        have h1 : inner 𝕜 (colVec B i) (colVec B i) = ((mu i : ℝ) : 𝕜) := by
          rw [hinner]; simp
        have h2 : mu i = 0 := by
          have := hssq i; rw [hi] at this; nlinarith
        have : ‖colVec B i‖ ^ 2 = 0 := by
          have hnorm := inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) (colVec B i)
          rw [h1, h2] at hnorm
          have : ((0 : ℝ) : 𝕜) = ((‖colVec B i‖ ^ 2 : ℝ) : 𝕜) := by
            simpa using hnorm
          exact_mod_cast this.symm
        have : ‖colVec B i‖ = 0 := by nlinarith [norm_nonneg (colVec B i)]
        exact norm_eq_zero.mp this
      have : B j i = 0 := by
        have := congrFun (congrArg WithLp.ofLp hz) j
        simpa [colVec] using this
      rw [hi, this]; simp
    · have hbi : b i = v i := hb i hi
      rw [hbi, hvdef]
      have : (((s i)⁻¹ : 𝕜) • colVec B i) j = ((s i)⁻¹ : 𝕜) * B j i := by
        simp [colVec]
      rw [this]
      have hsi : ((s i : ℝ) : 𝕜) ≠ 0 := by simpa using hi
      field_simp
  have hBeq : B = (Matrix.of fun j i => (b i) j : Matrix (Fin n) (Fin n) 𝕜) *
      diagonal (fun i => ((s i : ℝ) : 𝕜)) := by
    ext j i
    rw [Matrix.mul_diagonal]
    simp only [Matrix.of_apply]
    rw [mul_comm]
    exact (hcol i j).symm
  have : A = B * Vᴴ := by rw [hBdef, mul_assoc, hVV', mul_one]
  rw [this, hBeq]

lemma svSet_conj_subset (hn : 0 < n) {U V : Matrix (Fin n) (Fin n) 𝕜}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) 𝕜) (hV : V ∈ Matrix.unitaryGroup (Fin n) 𝕜)
    (A : Matrix (Fin n) (Fin n) 𝕜) (k : ℕ) : svSet A k ⊆ svSet (U * A * Vᴴ) k := by
  rintro c ⟨hc0, W, hW, hWx⟩
  refine ⟨hc0, W.map ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) V :
    EuclideanSpace 𝕜 (Fin n) →L[𝕜] EuclideanSpace 𝕜 (Fin n)).toLinearMap), ?_, ?_⟩
  · have hinj : Function.Injective
        ⇑((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) V :
          EuclideanSpace 𝕜 (Fin n) →L[𝕜] EuclideanSpace 𝕜 (Fin n)).toLinearMap) := by
      intro x y hxy
      have h0 : app V (x - y) = 0 := by
        have : app V x - app V y = 0 := by
          have hx : app V x = app V y := hxy
          rw [hx]; abel
        rw [show app V (x - y) = app V x - app V y from map_sub _ _ _]
        exact this
      have : ‖x - y‖ = 0 := by
        rw [← norm_app_unitary hn hV (x - y), h0, norm_zero]
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    rw [← hW]
    exact ((Submodule.equivMapOfInjective _ hinj W).finrank_eq).symm
  · rintro y ⟨x, hxW, rfl⟩
    have hy : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) V :
        EuclideanSpace 𝕜 (Fin n) →L[𝕜] EuclideanSpace 𝕜 (Fin n)).toLinearMap x = app V x := rfl
    rw [hy, norm_app_unitary hn hV]
    have hVV : Vᴴ * V = 1 := by
      have := hV.1; rwa [Matrix.star_eq_conjTranspose] at this
    have hcompute : app (U * A * Vᴴ) (app V x) = app U (app A x) := by
      rw [← app_mul, mul_assoc, mul_assoc, hVV, mul_one, app_mul]
    rw [hcompute, norm_app_unitary hn hU]
    exact hWx x hxW

lemma sv_conj (hn : 0 < n) {U V : Matrix (Fin n) (Fin n) 𝕜}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) 𝕜)
    (hV : V ∈ Matrix.unitaryGroup (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜) (k : ℕ) :
    sv (U * A * Vᴴ) k = sv A k := by
  have hU' : Uᴴ ∈ Matrix.unitaryGroup (Fin n) 𝕜 := by
    have := Unitary.star_mem hU; rwa [Matrix.star_eq_conjTranspose] at this
  have hV' : Vᴴ ∈ Matrix.unitaryGroup (Fin n) 𝕜 := by
    have := Unitary.star_mem hV; rwa [Matrix.star_eq_conjTranspose] at this
  have h1 : svSet A k ⊆ svSet (U * A * Vᴴ) k := svSet_conj_subset hn hU hV A k
  have h2 : svSet (U * A * Vᴴ) k ⊆ svSet A k := by
    have h3 := svSet_conj_subset hn hU' hV' (U * A * Vᴴ) k
    have hUU : Uᴴ * U = 1 := by
      have := hU.1; rwa [Matrix.star_eq_conjTranspose] at this
    have hVV : Vᴴ * V = 1 := by
      have := hV.1; rwa [Matrix.star_eq_conjTranspose] at this
    have heq : Uᴴ * (U * A * Vᴴ) * (Vᴴ)ᴴ = A := by
      rw [Matrix.conjTranspose_conjTranspose, ← mul_assoc, ← mul_assoc, hUU, one_mul,
        mul_assoc, hVV, mul_one]
    rwa [heq] at h3
  simp only [sv]
  rw [Set.Subset.antisymm h2 h1]

lemma sv_diagonal {s : Fin n → ℝ} (hs : ∀ i, 0 ≤ s i) (hmono : Antitone s) (i : Fin n) :
    sv (diagonal (fun i => ((s i : ℝ) : 𝕜))) (i.1 + 1) = s i := by
  classical
  have hnormsq : ∀ x : EuclideanSpace 𝕜 (Fin n),
      ‖app (diagonal (fun i => ((s i : ℝ) : 𝕜))) x‖ ^ 2 = ∑ j, (s j) ^ 2 * ‖x j‖ ^ 2 := by
    intro x
    rw [norm_sq_app_diagonal]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    rw [RCLike.norm_ofReal, abs_of_nonneg (hs j)]
  have hxsq : ∀ x : EuclideanSpace 𝕜 (Fin n), ‖x‖ ^ 2 = ∑ j, ‖x j‖ ^ 2 := fun x =>
    EuclideanSpace.norm_sq_eq x
  refine le_antisymm ?_ ?_
  · -- upper bound `sv ≤ s i`
    refine sv_le (by omega) ?_
    rintro c ⟨hc0, W, hW, hWx⟩
    set Z : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)) := coordSubspace 𝕜 (Finset.Ici i) with hZdef
    have hZ : Module.finrank 𝕜 Z = n - i.1 := by
      rw [hZdef, finrank_coordSubspace, Fin.card_Ici]
    have hsup : Module.finrank 𝕜 ((W ⊔ Z : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)))) ≤ n := by
      have := Submodule.finrank_le (W ⊔ Z)
      simpa [finrank_euclideanSpace] using this
    have hadd := Submodule.finrank_sup_add_finrank_inf_eq W Z
    have hipos : i.1 < n := i.2
    have hinf : 0 < Module.finrank 𝕜 ((W ⊓ Z : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)))) := by
      rw [hW, hZ] at hadd
      omega
    have hne : (W ⊓ Z : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))) ≠ ⊥ := by
      intro h
      rw [h] at hinf
      simp at hinf
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hupper : ‖app (diagonal (fun i => ((s i : ℝ) : 𝕜))) x‖ ≤ s i * ‖x‖ := by
      refine le_of_sq_le_sq' ?_ (mul_nonneg (hs i) (norm_nonneg _))
      rw [hnormsq, mul_pow, hxsq, Finset.mul_sum]
      refine Finset.sum_le_sum (fun j _ => ?_)
      by_cases hj : j ∈ Finset.Ici i
      · have hji : i ≤ j := Finset.mem_Ici.mp hj
        have : s j ≤ s i := hmono hji
        have h1 : (s j) ^ 2 ≤ (s i) ^ 2 := by nlinarith [hs j, hs i]
        nlinarith [sq_nonneg ‖x j‖, norm_nonneg (x j)]
      · have : x j = 0 := (mem_coordSubspace.mp hx.2) j hj
        rw [this]
        simp
    have h1 := hWx x hx.1
    have : c * ‖x‖ ≤ s i * ‖x‖ := le_trans h1 hupper
    exact le_of_mul_le_mul_right (by linarith) hxpos
  · -- lower bound `s i ≤ sv`
    refine le_sv (Nat.succ_pos _) ⟨hs i, coordSubspace 𝕜 (Finset.Iic i), ?_, ?_⟩
    · rw [finrank_coordSubspace, Fin.card_Iic]
    · intro x hx
      refine le_of_sq_le_sq' ?_ (norm_nonneg _)
      rw [hnormsq, mul_pow, hxsq, Finset.mul_sum]
      refine Finset.sum_le_sum (fun j _ => ?_)
      by_cases hj : j ∈ Finset.Iic i
      · have hji : j ≤ i := Finset.mem_Iic.mp hj
        have : s i ≤ s j := hmono hji
        have h1 : (s i) ^ 2 ≤ (s j) ^ 2 := by nlinarith [hs j, hs i]
        nlinarith [sq_nonneg ‖x j‖, norm_nonneg (x j)]
      · have : x j = 0 := (mem_coordSubspace.mp hx) j hj
        rw [this]
        simp

/-- The singular values of `A` are exactly the diagonal of any sorted singular value
decomposition of `A`. -/
lemma svals_eq_of_svd {A U V : Matrix (Fin n) (Fin n) 𝕜} {s : Fin n → ℝ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) 𝕜) (hV : V ∈ Matrix.unitaryGroup (Fin n) 𝕜)
    (hs : ∀ i, 0 ≤ s i) (hmono : Antitone s)
    (hA : A = U * diagonal (fun i => ((s i : ℝ) : 𝕜)) * Vᴴ) :
    svals A = s := by
  funext i
  have hn : 0 < n := i.pos
  rw [svals, hA, sv_conj hn hU hV, sv_diagonal hs hmono i]

/-- A singular value decomposition of `A` written with `svals A`. -/
theorem exists_svd_svals (A : Matrix (Fin n) (Fin n) 𝕜) :
    ∃ U V : Matrix (Fin n) (Fin n) 𝕜,
      U ∈ Matrix.unitaryGroup (Fin n) 𝕜 ∧ V ∈ Matrix.unitaryGroup (Fin n) 𝕜 ∧
      A = U * diagonal (fun i => ((svals A i : ℝ) : 𝕜)) * Vᴴ := by
  obtain ⟨U, V, s, hU, hV, hs, hmono, hA⟩ := exists_svd A
  exact ⟨U, V, hU, hV, by rw [svals_eq_of_svd hU hV hs hmono hA]; exact hA⟩

lemma svals_antitone (A : Matrix (Fin n) (Fin n) 𝕜) : Antitone (svals A) := by
  obtain ⟨U, V, s, hU, hV, hs, hmono, hA⟩ := exists_svd A
  rw [svals_eq_of_svd hU hV hs hmono hA]; exact hmono

/-- The product of the singular values is the absolute value of the determinant. -/
theorem prod_svals (A : Matrix (Fin n) (Fin n) 𝕜) : ∏ i, svals A i = ‖A.det‖ := by
  obtain ⟨U, V, hU, hV, hA⟩ := exists_svd_svals A
  have hdetU : ‖U.det‖ = 1 := norm_det_unitary hU
  have hdetV : ‖(Vᴴ).det‖ = 1 := by
    have hV' : Vᴴ ∈ Matrix.unitaryGroup (Fin n) 𝕜 := by
      have := Unitary.star_mem hV; rwa [Matrix.star_eq_conjTranspose] at this
    exact norm_det_unitary hV'
  have hdet : A.det = U.det * (∏ i, ((svals A i : ℝ) : 𝕜)) * (Vᴴ).det := by
    conv_lhs => rw [hA]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  rw [hdet, norm_mul, norm_mul, hdetU, hdetV, one_mul, mul_one, norm_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [RCLike.norm_ofReal, abs_of_nonneg (svals_nonneg A i)]

/-- The smallest singular value bounds `‖A x‖` from below. -/
lemma svals_last_mul_norm_le (hn : 0 < n) (A : Matrix (Fin n) (Fin n) 𝕜)
    (x : EuclideanSpace 𝕜 (Fin n)) :
    svals A ⟨n - 1, by omega⟩ * ‖x‖ ≤ ‖app A x‖ := by
  obtain ⟨U, V, hU, hV, hA⟩ := exists_svd_svals A
  set i0 : Fin n := ⟨n - 1, by omega⟩ with hi0
  have hlast : ∀ j : Fin n, svals A i0 ≤ svals A j := by
    intro j
    refine svals_antitone A ?_
    simp only [hi0, Fin.le_def]
    have := j.isLt
    omega
  have hV' : Vᴴ ∈ Matrix.unitaryGroup (Fin n) 𝕜 := by
    have := Unitary.star_mem hV; rwa [Matrix.star_eq_conjTranspose] at this
  set y : EuclideanSpace 𝕜 (Fin n) := app Vᴴ x with hy
  have hynorm : ‖y‖ = ‖x‖ := norm_app_unitary hn hV' x
  have hdiag : svals A i0 * ‖y‖ ≤ ‖app (diagonal (fun i => ((svals A i : ℝ) : 𝕜))) y‖ := by
    refine le_of_sq_le_sq' ?_ (norm_nonneg _)
    rw [norm_sq_app_diagonal, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have h1 : svals A i0 ≤ svals A j := hlast j
    have h2 : (svals A i0) ^ 2 ≤ ‖((svals A j : ℝ) : 𝕜)‖ ^ 2 := by
      rw [RCLike.norm_ofReal, abs_of_nonneg (svals_nonneg A j)]
      nlinarith [svals_nonneg A i0, svals_nonneg A j]
    nlinarith [sq_nonneg ‖y j‖, norm_nonneg (y j)]
  have hcompute : app A x = app U (app (diagonal (fun i => ((svals A i : ℝ) : 𝕜))) y) := by
    rw [hy, ← app_mul, ← app_mul]
    exact congrArg (fun M => app M x) hA
  rw [hcompute, norm_app_unitary hn hU]
  rw [← hynorm]
  exact hdiag

/-- `svals A ⟨n-1⟩` is the smallest singular value. -/
lemma svals_last_eq_sigmaMin (hn : 0 < n) (A : Matrix (Fin n) (Fin n) 𝕜) :
    svals A ⟨n - 1, by omega⟩ = sigmaMin (svals A) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine le_antisymm ?_ (sigmaMin_le _ _)
  refine le_ciInf (fun j => svals_antitone A ?_)
  simp only [Fin.le_def]
  have := j.isLt
  omega

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The determinant phase `η_A` of `A`: `conj (det A) / |det A|` for `det A ≠ 0`, and `1`
for singular `A`. -/
noncomputable def etaOf (A : Matrix (Fin n) (Fin n) 𝕜) : 𝕜 :=
  if A.det = 0 then 1 else star A.det / ((‖A.det‖ : ℝ) : 𝕜)

lemma norm_etaOf (A : Matrix (Fin n) (Fin n) 𝕜) : ‖etaOf A‖ = 1 := by
  unfold etaOf
  split_ifs with h
  · exact norm_one
  · rw [norm_div, norm_star, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    exact div_self (by simpa using h)

lemma etaOf_ne_zero (A : Matrix (Fin n) (Fin n) 𝕜) : etaOf A ≠ 0 := by
  intro h
  have := norm_etaOf A
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-! ## Weyl perturbation for singular values -/

lemma svals_dist_le (A M : Matrix (Fin n) (Fin n) 𝕜) (i : Fin n) :
    |svals A i - svals M i| ≤ ‖A - M‖ := by
  have h1 := svals_le_add A M i
  have h2 := svals_le_add M A i
  rw [norm_sub_rev] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

lemma prod_svals_eq_one (M : Matrix (Fin n) (Fin n) 𝕜) (hM : M.det = 1) :
    ∏ i, svals M i = 1 := by
  rw [prod_svals, hM, norm_one]

/-- Any matrix `M` obeys `|det M| ≤ ∏ (σ i + ‖A - M‖)` (Weyl). -/
lemma abs_det_le_prod (A M : Matrix (Fin n) (Fin n) 𝕜) :
    ‖M.det‖ ≤ ∏ i, (svals A i + ‖A - M‖) := by
  rw [← prod_svals M]
  refine Finset.prod_le_prod (fun i _ => svals_nonneg M i) (fun i _ => ?_)
  have := svals_dist_le A M i
  rw [abs_sub_le_iff] at this
  linarith [this.2]

/-- If `‖A - M‖` is smaller than every singular value of `A`, then
`∏ (σ i - ‖A - M‖) ≤ |det M|`. -/
lemma prod_sub_le_abs_det (A M : Matrix (Fin n) (Fin n) 𝕜)
    (h : ∀ i, ‖A - M‖ ≤ svals A i) :
    ∏ i, (svals A i - ‖A - M‖) ≤ ‖M.det‖ := by
  rw [← prod_svals M]
  refine Finset.prod_le_prod (fun i _ => by linarith [h i]) (fun i _ => ?_)
  have := svals_dist_le A M i
  rw [abs_sub_le_iff] at this
  linarith [this.1]

/-! ## Constructing nearby matrices from scalars -/

lemma diagonal_mem_unitaryGroup {u : Fin n → 𝕜} (hu : ∀ i, ‖u i‖ = 1) :
    (diagonal u : Matrix (Fin n) (Fin n) 𝕜) ∈ Matrix.unitaryGroup (Fin n) 𝕜 := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have hfun : (fun i => (star u) i * u i) = fun _ : Fin n => (1 : 𝕜) := by
    funext i
    have h := RCLike.conj_mul (u i)
    rw [starRingEnd_apply] at h
    show star (u i) * u i = 1
    rw [h, hu i]
    norm_num
  rw [hfun]
  simp

/-- A singular value decomposition of `A` whose determinant phase is normalized. -/
theorem exists_svd_eta (hn : 0 < n) (A : Matrix (Fin n) (Fin n) 𝕜) :
    ∃ U V : Matrix (Fin n) (Fin n) 𝕜,
      U ∈ Matrix.unitaryGroup (Fin n) 𝕜 ∧ V ∈ Matrix.unitaryGroup (Fin n) 𝕜 ∧
      A = U * diagonal (fun i => ((svals A i : ℝ) : 𝕜)) * Vᴴ ∧
      star U.det * V.det = etaOf A := by
  classical
  obtain ⟨U, V, hU, hV, hA⟩ := exists_svd_svals A
  set w : 𝕜 := star U.det * V.det with hwdef
  have hwnorm : ‖w‖ = 1 := by
    rw [hwdef, norm_mul, norm_star, norm_det_unitary hU, norm_det_unitary hV, one_mul]
  have hdetA : A.det = U.det * (∏ i, ((svals A i : ℝ) : 𝕜)) * star V.det := by
    conv_lhs => rw [hA]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_conjTranspose]
  by_cases hdet : A.det = 0
  · -- singular case: adjust the phase using a zero singular direction
    set i0 : Fin n := ⟨n - 1, by omega⟩ with hi0
    have hzero : svals A i0 = 0 := by
      have hprod : ∏ i, svals A i = 0 := by rw [prod_svals, hdet, norm_zero]
      obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hprod
      refine le_antisymm ?_ (svals_nonneg A i0)
      calc svals A i0 ≤ svals A j := by
            refine svals_antitone A ?_
            simp only [hi0, Fin.le_def]
            have := j.isLt
            omega
        _ = 0 := hj
    set u : Fin n → 𝕜 := fun j => if j = i0 then w else 1 with hudef
    have hunorm : ∀ j, ‖u j‖ = 1 := by
      intro j
      rw [hudef]
      by_cases hj : j = i0 <;> simp [hj, hwnorm]
    have hUdiag : U * diagonal u ∈ Matrix.unitaryGroup (Fin n) 𝕜 :=
      mul_mem hU (diagonal_mem_unitaryGroup hunorm)
    have hprodu : ∏ j, u j = w := by
      rw [hudef]
      rw [Finset.prod_eq_single i0]
      · simp
      · intro b _ hb; simp [hb]
      · intro hcon; exact absurd (Finset.mem_univ i0) hcon
    refine ⟨U * diagonal u, V, hUdiag, hV, ?_, ?_⟩
    · have hcancel : U * diagonal u * diagonal (fun i => ((svals A i : ℝ) : 𝕜))
          = U * diagonal (fun i => ((svals A i : ℝ) : 𝕜)) := by
        have hfun2 : (fun i => u i * ((svals A i : ℝ) : 𝕜))
            = (fun i => ((svals A i : ℝ) : 𝕜)) := by
          funext j
          show u j * ((svals A j : ℝ) : 𝕜) = ((svals A j : ℝ) : 𝕜)
          by_cases hj : j = i0
          · subst hj
            rw [hzero]
            simp
          · rw [hudef]
            simp only [if_neg hj, one_mul]
        rw [mul_assoc, Matrix.diagonal_mul_diagonal, hfun2]
      rw [hcancel]
      exact hA
    · rw [Matrix.det_mul, Matrix.det_diagonal, hprodu, star_mul']
      have hcalc : star U.det * star w * V.det = star w * w := by rw [hwdef]; ring
      rw [hcalc]
      have hsq : star w * w = ((‖w‖ : 𝕜)) ^ 2 := by
        rw [← RCLike.conj_mul w, starRingEnd_apply]
      rw [hsq, hwnorm, etaOf, if_pos hdet]
      norm_num
  · -- invertible case: the phase is automatic
    refine ⟨U, V, hU, hV, hA, ?_⟩
    have hprodnorm : ∏ i, ((svals A i : ℝ) : 𝕜) = ((‖A.det‖ : ℝ) : 𝕜) := by
      rw [← prod_svals A, RCLike.ofReal_prod]
    have hs : star ((‖A.det‖ : ℝ) : 𝕜) = ((‖A.det‖ : ℝ) : 𝕜) := by
      rw [RCLike.star_def, RCLike.conj_ofReal]
    have hstar : star A.det = w * ((‖A.det‖ : ℝ) : 𝕜) := by
      conv_lhs => rw [hdetA, hprodnorm, star_mul', star_mul', star_star, hs]
      rw [hwdef]
      ring
    have hne : ((‖A.det‖ : ℝ) : 𝕜) ≠ 0 := by
      simpa using hdet
    rw [etaOf, if_neg hdet, hstar, mul_div_assoc, div_self hne, mul_one]

/-- Reconstruction: any admissible family of scalars yields a determinant-one matrix at the
corresponding distance. -/
theorem exists_matrix_of_scalars (hn : 0 < n) (A : Matrix (Fin n) (Fin n) 𝕜)
    (z : Fin n → 𝕜) (hz : ∏ i, z i = etaOf A) :
    ∃ M : Matrix (Fin n) (Fin n) 𝕜, M.det = 1 ∧
      ‖A - M‖ = mx (fun i => ‖((svals A i : ℝ) : 𝕜) - z i‖) := by
  obtain ⟨U, V, hU, hV, hA, hphase⟩ := exists_svd_eta hn A
  have hV' : Vᴴ ∈ Matrix.unitaryGroup (Fin n) 𝕜 := by
    have := Unitary.star_mem hV; rwa [Matrix.star_eq_conjTranspose] at this
  refine ⟨U * diagonal z * Vᴴ, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_conjTranspose, hz,
      ← hphase]
    have h1 : U.det * (star U.det * V.det) * star V.det
        = (U.det * star U.det) * (V.det * star V.det) := by ring
    rw [h1]
    have h2 : ∀ x : 𝕜, ‖x‖ = 1 → x * star x = 1 := by
      intro x hx
      have hxx := RCLike.mul_conj x
      rw [starRingEnd_apply] at hxx
      rw [hxx, hx]
      norm_num
    rw [h2 _ (norm_det_unitary hU), h2 _ (norm_det_unitary hV), one_mul]
  · have hsub : A - U * diagonal z * Vᴴ
        = U * diagonal (fun i => ((svals A i : ℝ) : 𝕜) - z i) * Vᴴ := by
      rw [← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul, ← hA]
    rw [hsub, norm_mul_unitary hn hV', norm_unitary_mul hn hU, norm_diagonal_eq_mx hn]

/-- Lower bound valid for every field: the positive scalar value is a lower bound for the
distance to the determinant-one matrices. -/
theorem Rplus_le_of_det_one (hn : 0 < n) (A M : Matrix (Fin n) (Fin n) 𝕜) (hM : M.det = 1) :
    Rplus (svals A) ≤ ‖A - M‖ :=
  (scalar_pos_isLeast hn (svals_nonneg A)).2
    ⟨svals M, prod_svals_eq_one M hM, fun i => svals_dist_le A M i⟩

/-! ## Attainment of the distance -/

theorem exists_nearest (A : Matrix (Fin n) (Fin n) 𝕜) :
    ∃ M : Matrix (Fin n) (Fin n) 𝕜, M.det = 1 ∧
      IsLeast {r : ℝ | ∃ N : Matrix (Fin n) (Fin n) 𝕜, N.det = 1 ∧ ‖A - N‖ ≤ r} ‖A - M‖ := by
  classical
  haveI : ProperSpace (Matrix (Fin n) (Fin n) 𝕜) := FiniteDimensional.proper 𝕜 _
  have hcontnorm : Continuous fun N : Matrix (Fin n) (Fin n) 𝕜 => ‖A - N‖ := by fun_prop
  have hclosed : IsClosed
      {N : Matrix (Fin n) (Fin n) 𝕜 | N.det = 1 ∧ ‖A - N‖ ≤ ‖A - 1‖} := by
    have h1 : IsClosed {N : Matrix (Fin n) (Fin n) 𝕜 | N.det = 1} :=
      isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
    have h2 : IsClosed {N : Matrix (Fin n) (Fin n) 𝕜 | ‖A - N‖ ≤ ‖A - 1‖} :=
      isClosed_le hcontnorm continuous_const
    exact h1.inter h2
  have hsub : {N : Matrix (Fin n) (Fin n) 𝕜 | N.det = 1 ∧ ‖A - N‖ ≤ ‖A - 1‖}
      ⊆ Metric.closedBall A ‖A - 1‖ := by
    rintro N ⟨-, hN⟩
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact hN
  have hcompact : IsCompact {N : Matrix (Fin n) (Fin n) 𝕜 | N.det = 1 ∧ ‖A - N‖ ≤ ‖A - 1‖} :=
    Metric.isCompact_of_isClosed_isBounded hclosed
      (Metric.isBounded_closedBall.subset hsub)
  have hne : {N : Matrix (Fin n) (Fin n) 𝕜 | N.det = 1 ∧ ‖A - N‖ ≤ ‖A - 1‖}.Nonempty :=
    ⟨1, Matrix.det_one, le_refl _⟩
  obtain ⟨M, hMT, hMmin⟩ := hcompact.exists_isMinOn hne hcontnorm.continuousOn
  refine ⟨M, hMT.1, ⟨M, hMT.1, le_refl _⟩, ?_⟩
  rintro r ⟨N, hN1, hN2⟩
  by_cases hNball : ‖A - N‖ ≤ ‖A - 1‖
  · exact le_trans (hMmin ⟨hN1, hNball⟩) hN2
  · push_neg at hNball
    have := hMT.2
    linarith

/-! ## The `η = 1` case over any field -/

lemma norm_ofReal_sub (a b : ℝ) : ‖((a : ℝ) : 𝕜) - ((b : ℝ) : 𝕜)‖ = |a - b| := by
  rw [← RCLike.ofReal_sub, RCLike.norm_ofReal]

/-- If the determinant phase of `A` is trivial then the distance to the determinant-one
matrices is `R₊(σ(A))`.  This covers all singular matrices and all matrices whose determinant
is a positive real number. -/
theorem isLeast_Rplus_of_eta_one (hn : 0 < n) (A : Matrix (Fin n) (Fin n) 𝕜)
    (hA : etaOf A = 1) :
    IsLeast {r : ℝ | ∃ M : Matrix (Fin n) (Fin n) 𝕜, M.det = 1 ∧ ‖A - M‖ ≤ r}
      (Rplus (svals A)) := by
  constructor
  · obtain ⟨⟨x, hx1, hxd⟩, -⟩ := scalar_pos_isLeast hn (svals_nonneg A)
    have hprod : ∏ i, ((x i : ℝ) : 𝕜) = etaOf A := by
      rw [hA, ← RCLike.ofReal_prod, hx1, RCLike.ofReal_one]
    obtain ⟨M, hM1, hM2⟩ := exists_matrix_of_scalars hn A (fun i => ((x i : ℝ) : 𝕜)) hprod
    refine ⟨M, hM1, ?_⟩
    rw [hM2]
    refine mx_le hn (fun i => ?_)
    rw [norm_ofReal_sub]
    exact hxd i
  · rintro r ⟨M, hM1, hM2⟩
    exact le_trans (Rplus_le_of_det_one hn A M hM1) hM2

/-! ## The real case -/

lemma etaOf_eq_one_of_det_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (hA : 0 ≤ A.det) :
    etaOf A = 1 := by
  rw [etaOf]
  split_ifs with h
  · rfl
  · have hpos : 0 < A.det := lt_of_le_of_ne hA (Ne.symm h)
    show star A.det / ‖A.det‖ = 1
    rw [star_trivial, Real.norm_eq_abs, abs_of_pos hpos]
    exact div_self (ne_of_gt hpos)

lemma etaOf_eq_neg_one_of_det_neg (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det < 0) :
    etaOf A = -1 := by
  rw [etaOf, if_neg (ne_of_lt hA)]
  show star A.det / ‖A.det‖ = -1
  rw [star_trivial, Real.norm_eq_abs, abs_of_neg hA, div_neg, div_self (ne_of_lt hA)]

/-- Real matrices with nonnegative determinant: the distance to `SL_n(ℝ)` is `R₊(σ(A))`. -/
theorem real_isLeast_of_det_nonneg (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : 0 ≤ A.det) :
    IsLeast {r : ℝ | ∃ M : Matrix (Fin n) (Fin n) ℝ, M.det = 1 ∧ ‖A - M‖ ≤ r}
      (Rplus (svals A)) :=
  isLeast_Rplus_of_eta_one hn A (etaOf_eq_one_of_det_nonneg A hA)

/-- The key geometric fact behind the negative determinant case: if `det A < 0 < det M`, the
segment from `A` to `M` meets a singular matrix, which forces the two smallest singular values
to fit inside `‖A - M‖`. -/
lemma svals_last_add_le (hn : 0 < n) (A M : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det < 0) (hM : M.det = 1) :
    svals A ⟨n - 1, by omega⟩ + svals M ⟨n - 1, by omega⟩ ≤ ‖A - M‖ := by
  classical
  set f : ℝ → ℝ := fun t => ((1 - t) • A + t • M).det with hf
  have hcont : Continuous f := by
    rw [hf]
    exact Continuous.matrix_det (by fun_prop)
  have hf0 : f 0 = A.det := by simp [hf]
  have hf1 : f 1 = 1 := by simp [hf, hM]
  have hmem : (0 : ℝ) ∈ Set.Icc (f 0) (f 1) := by
    rw [hf0, hf1]
    exact ⟨le_of_lt hA, zero_le_one⟩
  obtain ⟨t, ht, hft⟩ :=
    intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hcont.continuousOn hmem
  have ht0 : 0 < t := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · exfalso; rw [← h, hf0] at hft; linarith
    · exact h
  have ht1 : t < 1 := by
    rcases eq_or_lt_of_le ht.2 with h | h
    · exfalso; rw [h, hf1] at hft; norm_num at hft
    · exact h
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hft
  set x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v with hx
  have hxne : x ≠ 0 := by
    intro h
    apply hv0
    funext i
    have := congrFun (congrArg WithLp.ofLp h) i
    simpa [hx] using this
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  set a : EuclideanSpace ℝ (Fin n) := app A x with ha
  set m : EuclideanSpace ℝ (Fin n) := app M x with hm
  have hlin : (1 - t) • a + t • m = 0 := by
    have hB : app ((1 - t) • A + t • M) x = (1 - t) • a + t • m := by
      rw [ha, hm, app_eq_zero_of_mulVec, app_eq_zero_of_mulVec, app_eq_zero_of_mulVec]
      simp [Matrix.add_mulVec, Matrix.smul_mulVec]
    rw [← hB, app_eq_zero_of_mulVec]
    have : ((1 - t) • A + t • M) *ᵥ WithLp.ofLp x = 0 := by
      simpa [hx] using hv
    rw [this]
    simp
  have hteq : a = (-(t / (1 - t))) • m := by
    have h1 : (1 - t) ≠ 0 := by linarith
    have h2 : (1 - t) • a = -(t • m) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hlin
    have h3 : a = (1 - t)⁻¹ • ((1 - t) • a) := by
      rw [smul_smul, inv_mul_cancel₀ h1, one_smul]
    rw [h3, h2, smul_neg, smul_smul]
    rw [show -(t / (1 - t)) = -((1 - t)⁻¹ * t) by field_simp]
    rw [neg_smul]
  set c : ℝ := t / (1 - t) with hc
  have hcpos : 0 < c := div_pos ht0 (by linarith)
  have hanorm : ‖a‖ = c * ‖m‖ := by
    rw [hteq, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos hcpos]
  have hsub : ‖a - m‖ = ‖a‖ + ‖m‖ := by
    have : a - m = (-(c + 1)) • m := by
      rw [hteq]
      module
    rw [this, norm_smul, hanorm]
    have : ‖(-(c + 1) : ℝ)‖ = c + 1 := by
      rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [this]
    ring
  have hAM : ‖a - m‖ ≤ ‖A - M‖ * ‖x‖ := by
    have : a - m = app (A - M) x := by rw [ha, hm, app_sub]
    rw [this]
    exact norm_app_le (A - M) x
  have hA' : svals A ⟨n - 1, by omega⟩ * ‖x‖ ≤ ‖a‖ := svals_last_mul_norm_le hn A x
  have hM' : svals M ⟨n - 1, by omega⟩ * ‖x‖ ≤ ‖m‖ := svals_last_mul_norm_le hn M x
  have hsum : (svals A ⟨n - 1, by omega⟩ + svals M ⟨n - 1, by omega⟩) * ‖x‖
      ≤ ‖A - M‖ * ‖x‖ := by
    calc (svals A ⟨n - 1, by omega⟩ + svals M ⟨n - 1, by omega⟩) * ‖x‖
        = svals A ⟨n - 1, by omega⟩ * ‖x‖ + svals M ⟨n - 1, by omega⟩ * ‖x‖ := by ring
      _ ≤ ‖a‖ + ‖m‖ := by linarith
      _ = ‖a - m‖ := hsub.symm
      _ ≤ ‖A - M‖ * ‖x‖ := hAM
  exact le_of_mul_le_mul_right hsum hxpos

/-- Real matrices with negative determinant: the distance to `SL_n(ℝ)` is `R₋(σ(A))`. -/
theorem real_isLeast_of_det_neg (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det < 0) :
    IsLeast {r : ℝ | ∃ M : Matrix (Fin n) (Fin n) ℝ, M.det = 1 ∧ ‖A - M‖ ≤ r}
      (Rminus (svals A)) := by
  classical
  set i0 : Fin n := ⟨n - 1, by omega⟩ with hi0
  constructor
  · obtain ⟨⟨x, hx1, hxd⟩, -⟩ := scalar_neg_isLeast hn (svals_nonneg A)
    have hprod : ∏ i, x i = etaOf A := by
      rw [etaOf_eq_neg_one_of_det_neg A hA, hx1]
    obtain ⟨M, hM1, hM2⟩ := exists_matrix_of_scalars hn A x hprod
    refine ⟨M, hM1, ?_⟩
    rw [hM2]
    refine mx_le hn (fun i => ?_)
    rw [Real.norm_eq_abs]
    exact hxd i
  · rintro r ⟨M, hM1, hM2⟩
    refine le_trans ?_ hM2
    refine (scalar_neg_isLeast hn (svals_nonneg A)).2
      ⟨Function.update (svals M) i0 (-(svals M i0)), ?_, ?_⟩
    · rw [Finset.prod_update_of_mem (Finset.mem_univ i0), ← Finset.erase_eq]
      have hsplit : svals M i0 * ∏ i ∈ Finset.univ.erase i0, svals M i = ∏ i, svals M i :=
        Finset.mul_prod_erase _ _ (Finset.mem_univ i0)
      have hp := prod_svals_eq_one M hM1
      rw [hp] at hsplit
      calc -(svals M i0) * ∏ i ∈ Finset.univ.erase i0, svals M i
          = -(svals M i0 * ∏ i ∈ Finset.univ.erase i0, svals M i) := by ring
        _ = -1 := by rw [hsplit]
    · intro i
      by_cases hi : i = i0
      · rw [hi, Function.update_self]
        have habs : |svals A i0 - -(svals M i0)| = svals A i0 + svals M i0 := by
          rw [sub_neg_eq_add,
            abs_of_nonneg (add_nonneg (svals_nonneg A i0) (svals_nonneg M i0))]
        rw [habs]
        exact svals_last_add_le hn A M hA hM1
      · rw [Function.update_of_ne hi]
        exact svals_dist_le A M i

/-- The complete real answer (2.2). -/
theorem real_dist (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) :
    IsLeast {r : ℝ | ∃ M : Matrix (Fin n) (Fin n) ℝ, M.det = 1 ∧ ‖A - M‖ ≤ r}
      (if 0 ≤ A.det then Rplus (svals A) else Rminus (svals A)) := by
  split_ifs with h
  · exact real_isLeast_of_det_nonneg hn A h
  · exact real_isLeast_of_det_neg hn A (by linarith [not_le.mp h])

/-! ## The complex case -/

/-- Complex matrices with `η_A = 1` (in particular singular matrices and matrices with
positive real determinant): the distance to `SL_n(ℂ)` is `R₊(σ(A))`. -/
theorem complex_isLeast_of_eta_one (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : etaOf A = 1) :
    IsLeast {r : ℝ | ∃ M : Matrix (Fin n) (Fin n) ℂ, M.det = 1 ∧ ‖A - M‖ ≤ r}
      (Rplus (svals A)) :=
  isLeast_Rplus_of_eta_one hn A hA

lemma etaOf_eq_one_of_det_zero (A : Matrix (Fin n) (Fin n) 𝕜) (hA : A.det = 0) :
    etaOf A = 1 := by
  rw [etaOf, if_pos hA]

/-- The `η_A = 1` case, written in the arbitrary-phase form (2.4). -/
theorem complex_isLeast_cmin_of_eta_one (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : etaOf A = 1) :
    IsLeast {r : ℝ | ∃ M : Matrix (Fin n) (Fin n) ℂ, M.det = 1 ∧ ‖A - M‖ ≤ r}
      (cmin (svals A) (etaOf A)) := by
  rw [hA, cmin_one hn (svals_nonneg A)]
  exact isLeast_Rplus_of_eta_one hn A hA

/-- Singular complex matrices (2.5): the distance is the unique `r > 0` with
`∏ (σ i + r) = 1`. -/
theorem complex_isLeast_of_det_zero (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.det = 0) :
    IsLeast {r : ℝ | ∃ M : Matrix (Fin n) (Fin n) ℂ, M.det = 1 ∧ ‖A - M‖ ≤ r}
      (Rplus (svals A)) ∧ 0 < Rplus (svals A) ∧ ∏ i, (svals A i + Rplus (svals A)) = 1 := by
  refine ⟨isLeast_Rplus_of_eta_one hn A (etaOf_eq_one_of_det_zero A hA), ?_⟩
  refine Rplus_of_prod_lt_one hn (svals_nonneg A) ?_
  rw [prod_svals, hA, norm_zero]
  norm_num

/-- Complex matrices with positive real determinant (2.6): the distance is `R₊(σ(A))`. -/
theorem complex_isLeast_of_det_pos_real (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ)
    {c : ℝ} (hc : 0 < c) (hA : A.det = (c : ℂ)) :
    IsLeast {r : ℝ | ∃ M : Matrix (Fin n) (Fin n) ℂ, M.det = 1 ∧ ‖A - M‖ ≤ r}
      (Rplus (svals A)) := by
  refine isLeast_Rplus_of_eta_one hn A ?_
  have hne : A.det ≠ 0 := by
    rw [hA]
    exact_mod_cast ne_of_gt hc
  rw [etaOf, if_neg hne, hA]
  rw [show star ((c : ℝ) : ℂ) = ((c : ℝ) : ℂ) by simp]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  exact div_self (by exact_mod_cast ne_of_gt hc)

/-- Upper bound in the complex case: the scalar minimax value is achieved by a matrix of
determinant one. -/
theorem complex_upper (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, M.det = 1 ∧ ‖A - M‖ ≤ cmin (svals A) (etaOf A) := by
  obtain ⟨⟨z, hz1, hzd⟩, -⟩ := cmin_isLeast (σ := svals A) hn (etaOf A)
  obtain ⟨M, hM1, hM2⟩ := exists_matrix_of_scalars hn A z hz1
  refine ⟨M, hM1, ?_⟩
  rw [hM2]
  exact mx_le hn (fun i => hzd i)

/-- What is proved for an arbitrary complex matrix: the distance is attained, it is at least
the positive scalar value `R₊(σ(A))`, and it is at most the arbitrary-phase scalar value
`cmin (σ(A)) η_A`.  (The two bounds coincide exactly when `η_A = 1`; the general lower bound
`cmin (σ(A)) η_A ≤ d(A)` is the missing theorem discussed in the file header.) -/
theorem complex_dist_between (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ d : ℝ, IsLeast {r : ℝ | ∃ M : Matrix (Fin n) (Fin n) ℂ, M.det = 1 ∧ ‖A - M‖ ≤ r} d ∧
      Rplus (svals A) ≤ d ∧ d ≤ cmin (svals A) (etaOf A) := by
  obtain ⟨M, hM1, hMleast⟩ := exists_nearest A
  refine ⟨‖A - M‖, hMleast, Rplus_le_of_det_one hn A M hM1, ?_⟩
  obtain ⟨N, hN1, hN2⟩ := complex_upper hn A
  exact le_trans (hMleast.2 ⟨N, hN1, le_refl _⟩) hN2

/-! ## Axiom audit

The four aggregate results depend only on the standard axioms of Lean/mathlib
(`propext`, `Classical.choice`, `Quot.sound`).
-/

#print axioms real_dist
#print axioms complex_isLeast_of_eta_one
#print axioms complex_upper
#print axioms exists_nearest
#print axioms complex_dist_between

end Q857
