/-
# Q788 — localization and the ellipsoidal sandwich in relative coordinates

Fixing the first angle to `0` and restricting the remaining ones to the period box
`[-π, π)^{n-1}`, we show that the event `Dₙ ≥ 2ⁿ(1-δ)` is sandwiched between two sublevel
sets of the quadratic form `relQuad` of the matrix `I_{n-1} - J_{n-1}/n`:

  `{relQuad ≤ 8δ(1-δ)} ⊆ {y : Dₙ(0,y) ≥ 2ⁿ(1-δ)} ∩ [-π,π)^{n-1} ⊆ {relQuad ≤ 8δ + C_n δ²}`.

The right-hand inclusion needs the localization step: a configuration with an almost extremal
chord maximum has all its points in one arc of size `O(√δ)`.
-/
import RMS.Q788Slice

set_option maxHeartbeats 1000000

open MeasureTheory Real Set
open scoped ENNReal

namespace Q788

/-! ## `quadDev` in the slice at first angle `0` -/

theorem quadDev_eq_sub {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) :
    quadDev θ = (∑ j, (θ j) ^ 2) - (∑ j, θ j) ^ 2 / n := by
  have hn' : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [quadDev]
  have hexp : ∀ j : Fin n, (θ j - (∑ i, θ i) / n) ^ 2
      = (θ j) ^ 2 - 2 * ((∑ i, θ i) / n) * θ j + ((∑ i, θ i) / n) ^ 2 := fun j => by ring
  rw [Finset.sum_congr rfl fun j _ => hexp j, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- In the slice at first angle `0` the quadratic energy is exactly the quadratic form
`relQuad` of the matrix `I_{n-1} - J_{n-1}/n`. -/
theorem quadDev_cons_zero {m : ℕ} (y : Fin m → ℝ) :
    quadDev (Fin.cons 0 y : Fin (m + 1) → ℝ) = relQuad m y := by
  rw [quadDev_eq_sub (Nat.succ_pos m), relQuad]
  have h1 : (∑ j : Fin (m + 1), ((Fin.cons 0 y : Fin (m + 1) → ℝ) j) ^ 2)
      = ∑ j, (y j) ^ 2 := by
    simp [Fin.sum_univ_succ]
  have h2 : (∑ j : Fin (m + 1), (Fin.cons 0 y : Fin (m + 1) → ℝ) j) = ∑ j, y j := by
    simp [Fin.sum_univ_succ]
  rw [h1, h2]
  norm_num

/-! ## Two coordinates cannot be far apart in a low-energy configuration -/

theorem sq_sub_le_two_mul_quadDev {n : ℕ} (θ : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    (θ i - θ j) ^ 2 ≤ 2 * quadDev θ := by
  classical
  set c : ℝ := (∑ k, θ k) / n with hc
  have hsub : ({i, j} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => (θ k - c) ^ 2) hsub
    (fun k _ _ => sq_nonneg _)
  rw [Finset.sum_pair hij] at h
  have h' : (θ i - c) ^ 2 + (θ j - c) ^ 2 ≤ quadDev θ := by
    rw [quadDev]; simpa using h
  nlinarith [h', sq_nonneg (θ i + θ j - 2 * c)]

theorem sq_le_two_mul_relQuad {m : ℕ} (y : Fin m → ℝ) (j : Fin m) :
    (y j) ^ 2 ≤ 2 * relQuad m y := by
  have hne : (0 : Fin (m + 1)) ≠ j.succ := by
    simp [Fin.ext_iff]
  have h := sq_sub_le_two_mul_quadDev (Fin.cons 0 y : Fin (m + 1) → ℝ) hne
  rw [quadDev_cons_zero] at h
  simpa using h

/-! ## Localization -/

/-- A configuration whose chord maximum is within `δ` of `2ⁿ` has all its points within
`π√(2δ)` of a common arithmetic progression of step `2π`. -/
theorem exists_shift_localization {n : ℕ} (θ : Fin n → ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h : 2 ^ n * (1 - δ) ≤ chordMax θ) :
    ∃ s : ℝ, ∀ j, ∃ k : ℤ, |(s - θ j) - 2 * π * k| ≤ π * Real.sqrt (2 * δ) := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  obtain ⟨t, ht⟩ := exists_chordProd_eq_chordMax θ
  refine ⟨t - π, fun j => ?_⟩
  have hcos : 1 - δ ≤ cosProd (fun i => (t - π) - θ i) := by
    rw [← ht, show t = (t - π) + π by ring, chordProd_add_pi θ (t - π)] at h
    exact le_of_mul_le_mul_left h h2
  refine exists_int_dist_le_of_abs_cos_ge _ δ hδ0 hδ1 ?_
  have hfac := cosProd_le_factor (fun i => (t - π) - θ i) j
  simp only at hfac
  linarith

/-- **Localization in the slice.**  If the first angle is `0`, the others lie in `[-π, π]`
and the chord maximum is within `δ ≤ 1/100` of `2ⁿ`, then all the angles are within `1`
of `0`. -/
theorem cluster_cons_zero {m : ℕ} (y : Fin m → ℝ) (hy : ∀ j, |y j| ≤ π) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 100)
    (h : 2 ^ (m + 1) * (1 - δ) ≤ chordMax (Fin.cons 0 y)) : ∀ j, |y j| ≤ 1 := by
  have hpi := Real.pi_pos
  have hpi4 : π ≤ 3.15 := by linarith [Real.pi_lt_d2]
  have hpi3 : 3 < π := Real.pi_gt_three
  have hsqrt : Real.sqrt (2 * δ) ≤ 1 / 7 := by
    have h1 : 2 * δ ≤ (1 / 7 : ℝ) ^ 2 := by norm_num; linarith
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by norm_num)] at this
  set ρ : ℝ := π * Real.sqrt (2 * δ) with hρ
  have hρnn : 0 ≤ ρ := by rw [hρ]; positivity
  have hρle : ρ ≤ 0.45 := by
    rw [hρ]
    nlinarith [Real.sqrt_nonneg (2 * δ)]
  obtain ⟨s, hs⟩ := exists_shift_localization (Fin.cons 0 y : Fin (m + 1) → ℝ) δ hδ0
    (by linarith) h
  obtain ⟨k0, hk0⟩ := hs 0
  rw [show (Fin.cons 0 y : Fin (m + 1) → ℝ) 0 = 0 from Fin.cons_zero _ _, sub_zero] at hk0
  have hk0' : |s - 2 * π * (k0 : ℝ)| ≤ ρ := hk0
  intro j
  obtain ⟨kj, hkj⟩ := hs j.succ
  rw [show (Fin.cons 0 y : Fin (m + 1) → ℝ) j.succ = y j from Fin.cons_succ _ _ _] at hkj
  have hkj' : |(s - y j) - 2 * π * (kj : ℝ)| ≤ ρ := hkj
  have hdiff : |y j - 2 * π * ((k0 : ℝ) - (kj : ℝ))| ≤ 2 * ρ := by
    have hexp : y j - 2 * π * ((k0 : ℝ) - (kj : ℝ))
        = (s - 2 * π * (k0 : ℝ)) - ((s - y j) - 2 * π * (kj : ℝ)) := by ring
    rw [hexp]
    calc |(s - 2 * π * (k0 : ℝ)) - ((s - y j) - 2 * π * (kj : ℝ))|
        ≤ |s - 2 * π * (k0 : ℝ)| + |(s - y j) - 2 * π * (kj : ℝ)| := abs_sub _ _
      _ ≤ 2 * ρ := by linarith
  have hzero : k0 = kj := by
    by_contra hne
    have hone : (1 : ℝ) ≤ |(k0 : ℝ) - (kj : ℝ)| := by
      have hcast : ((k0 : ℝ) - (kj : ℝ)) = ((k0 - kj : ℤ) : ℝ) := by push_cast; ring
      rw [hcast, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (sub_ne_zero.2 hne)
    have hbig : 2 * π ≤ |2 * π * ((k0 : ℝ) - (kj : ℝ))| := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * π)]
      nlinarith
    have hyj := hy j
    have := abs_sub_abs_le_abs_sub (2 * π * ((k0 : ℝ) - (kj : ℝ))) (y j)
    rw [abs_sub_comm] at this
    nlinarith [abs_nonneg (y j)]
  rw [hzero] at hdiff
  simp only [sub_self, mul_zero, sub_zero] at hdiff
  linarith

/-! ## The sandwich -/

/-- **Inner inclusion.**  A small quadratic energy forces an almost extremal chord maximum. -/
theorem chordMax_cons_ge_of_relQuad_le {m : ℕ} (y : Fin m → ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 8) (hQ : relQuad m y ≤ 8 * (δ - δ ^ 2)) :
    2 ^ (m + 1) * (1 - δ) ≤ chordMax (Fin.cons 0 y) := by
  set e : ℝ := δ - δ ^ 2 with he
  have he0 : 0 ≤ e := by rw [he]; nlinarith
  have he8 : e ≤ 1 / 8 := by rw [he]; nlinarith
  have hstep := two_pow_mul_le_chordMax (Fin.cons 0 y : Fin (m + 1) → ℝ) e he0 he8
    (by rw [quadDev_cons_zero]; exact hQ)
  have hcmp : 1 - δ ≤ 1 - e - e ^ 2 := by
    rw [he]; nlinarith
  have h2 : (0 : ℝ) < 2 ^ (m + 1) := by positivity
  nlinarith

/-- **Outer inclusion.**  An almost extremal chord maximum forces a small quadratic energy. -/
theorem relQuad_le_of_chordMax_cons_ge {m : ℕ} (y : Fin m → ℝ) (hy : ∀ j, |y j| ≤ π) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 100) (hδn : δ * ((m : ℝ) + 2) ≤ 1 / 4)
    (h : 2 ^ (m + 1) * (1 - δ) ≤ chordMax (Fin.cons 0 y)) :
    relQuad m y ≤ 8 * δ + (8 + 7 * ((m : ℝ) + 1)) * δ ^ 2 := by
  have hcl := cluster_cons_zero y hy δ hδ0 hδ h
  have hn : 0 < m + 1 := Nat.succ_pos m
  have hcl' : ∀ j : Fin (m + 1), |(Fin.cons 0 y : Fin (m + 1) → ℝ) j
      - (Fin.cons 0 y : Fin (m + 1) → ℝ) ⟨0, hn⟩| ≤ 1 := by
    intro j
    have hz : (Fin.cons 0 y : Fin (m + 1) → ℝ) ⟨0, hn⟩ = 0 := by
      show (Fin.cons 0 y : Fin (m + 1) → ℝ) 0 = 0
      simp
    rw [hz, sub_zero]
    refine Fin.cases ?_ ?_ j
    · simp
    · intro i; simpa using hcl i
  have hstep := quadDev_le_of_chordMax_ge hn (Fin.cons 0 y : Fin (m + 1) → ℝ) hcl' δ hδ0
    (by push_cast; linarith) (by linarith) h
  rw [quadDev_cons_zero] at hstep
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hstep
  exact hstep

end Q788
