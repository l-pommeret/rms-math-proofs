/-
# Q788 — Stage 4: the constructive lower bound for the exceptional probability

The regular polygon configuration `θ_j = 2πj/n` has `Dₙ = 2`.  We prove a quantitative
stability statement: a configuration whose points are within `η` of the vertices of the
regular `n`-gon still satisfies

`Dₙ ≤ (2 + nη) · exp (n η log (e n))`,

and deduce the constructive lower bound for `ℙ(Dₙ < α)` when `α > 2`.
-/
import RMS.Q788Endpoint

open Real Complex MeasureTheory Set Filter Polynomial
open scoped ENNReal Topology BigOperators Nat

namespace Q788

/-! ## The `n`-th roots of unity -/

/-- The primitive `n`-th root of unity `e^{2πi/n}`. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The vertices of the regular `n`-gon, as angles. -/
noncomputable def polyAngle (n : ℕ) (j : ℕ) : ℝ := 2 * π * j / n

theorem zeta_pow_eq (n : ℕ) (hn : 0 < n) (j : ℕ) :
    zeta n ^ j = Complex.exp ((polyAngle n j : ℂ) * Complex.I) := by
  rw [zeta, ← Complex.exp_nat_mul, polyAngle]
  congr 1
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  push_cast
  field_simp

theorem norm_zeta_pow (n : ℕ) (j : ℕ) : ‖zeta n ^ j‖ = 1 := by
  rw [norm_pow, zeta, Complex.norm_exp]
  simp

theorem poly_prod_range (n : ℕ) (hn : 0 < n) :
    ∏ j ∈ Finset.range n, (X - C (zeta n ^ j)) = X ^ n - 1 := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  have hprim : IsPrimitiveRoot (zeta n) n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hpoly : (X ^ n - 1 : ℂ[X]) = ∏ w ∈ nthRootsFinset n (1 : ℂ), (X - C w) :=
    X_pow_sub_one_eq_prod hn hprim
  have himg : nthRootsFinset n (1 : ℂ) = (Finset.range n).image (fun j => zeta n ^ j) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · intro hw
      obtain ⟨i, hi, rfl⟩ := hprim.eq_pow_of_pow_eq_one ((mem_nthRootsFinset hn 1).1 hw)
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact (mem_nthRootsFinset hn 1).2
        (by rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow])
  rw [hpoly, himg, Finset.prod_image
    (fun a ha b hb hab => hprim.pow_inj (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) hab)]

/-- The product of the distances from a point of the closed unit disc to all but one of the
`n`-th roots of unity is at most `n`. -/
theorem prod_erase_le (n : ℕ) (hn : 0 < n) (j0 : ℕ) (hj0 : j0 ∈ Finset.range n) (z : ℂ)
    (hz : ‖z‖ ≤ 1) :
    ∏ j ∈ (Finset.range n).erase j0, ‖z - zeta n ^ j‖ ≤ n := by
  classical
  have hprim : IsPrimitiveRoot (zeta n) n := Complex.isPrimitiveRoot_exp n hn.ne'
  set ω := zeta n ^ j0 with hω
  have hωn : ω ^ n = 1 := by rw [hω, ← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
  have hnorm : ‖ω‖ = 1 := norm_zeta_pow n j0
  have hA : (X - C ω) * ∏ j ∈ (Finset.range n).erase j0, (X - C (zeta n ^ j)) = X ^ n - 1 := by
    rw [hω, Finset.mul_prod_erase _ (fun j => X - C (zeta n ^ j)) hj0]
    exact poly_prod_range n hn
  set B : ℂ[X] := ∑ k ∈ Finset.range n, X ^ k * C (ω ^ (n - 1 - k)) with hB
  have hB2 : (X - C ω) * B = X ^ n - 1 := by
    rw [hB, show ((X : ℂ[X]) - C ω) * ∑ k ∈ Finset.range n, X ^ k * C (ω ^ (n - 1 - k))
        = (∑ i ∈ Finset.range n, X ^ i * (C ω) ^ (n - 1 - i)) * (X - C ω) by
      rw [mul_comm]; simp [C_pow]]
    rw [geom_sum₂_mul, ← C_pow, hωn, map_one]
  have heq : ∏ j ∈ (Finset.range n).erase j0, (X - C (zeta n ^ j)) = B :=
    mul_left_cancel₀ (X_sub_C_ne_zero ω) (hA.trans hB2.symm)
  have heval := congrArg (Polynomial.eval z) heq
  simp only [eval_prod, eval_sub, eval_X, eval_C, hB, eval_finset_sum, eval_mul, eval_pow] at heval
  calc ∏ j ∈ (Finset.range n).erase j0, ‖z - zeta n ^ j‖
      = ‖∏ j ∈ (Finset.range n).erase j0, (z - zeta n ^ j)‖ := by rw [norm_prod]
    _ = ‖∑ k ∈ Finset.range n, z ^ k * ω ^ (n - 1 - k)‖ := by rw [heval]
    _ ≤ ∑ k ∈ Finset.range n, ‖z ^ k * ω ^ (n - 1 - k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_pow, norm_pow, hnorm, one_pow, mul_one]
        exact pow_le_one₀ (norm_nonneg _) hz
    _ = n := by simp

/-- The full product of distances to the `n`-th roots of unity is `|zⁿ - 1| ≤ 2` on the unit
circle. -/
theorem prod_all_eq (n : ℕ) (hn : 0 < n) (z : ℂ) :
    ∏ j ∈ Finset.range n, ‖z - zeta n ^ j‖ = ‖z ^ n - 1‖ := by
  have heval := congrArg (Polynomial.eval z) (poly_prod_range n hn)
  simp only [eval_prod, eval_sub, eval_X, eval_C, eval_pow, eval_one] at heval
  rw [← norm_prod, heval]

/-! ## A lower bound for the distance to the nearest roots of unity -/

/-- Jordan's inequality in the form `|sin (π s)| ≥ 2 min (s, 1-s)` for `s ∈ [0,1]`. -/
theorem sin_pi_mul_ge (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    2 * min s (1 - s) ≤ Real.sin (π * s) := by
  have hpi := Real.pi_pos
  rcases le_total s (1 / 2) with h | h
  · have hmin : min s (1 - s) = s := min_eq_left (by linarith)
    rw [hmin]
    have := Real.mul_le_sin (x := π * s) (by positivity) (by nlinarith)
    calc 2 * s = 2 / π * (π * s) := by field_simp
      _ ≤ Real.sin (π * s) := this
  · have hmin : min s (1 - s) = 1 - s := min_eq_right (by linarith)
    rw [hmin]
    have hs : Real.sin (π * s) = Real.sin (π * (1 - s)) := by
      rw [show π * (1 - s) = π - π * s by ring, Real.sin_pi_sub]
    rw [hs]
    have := Real.mul_le_sin (x := π * (1 - s)) (by nlinarith) (by nlinarith)
    calc 2 * (1 - s) = 2 / π * (π * (1 - s)) := by field_simp
      _ ≤ Real.sin (π * (1 - s)) := this

theorem abs_sin_add_int_mul (x : ℝ) (n : ℕ) (hn : 0 < n) (k : ℤ) :
    |Real.sin (π * (x + n * k) / n)| = |Real.sin (π * x / n)| := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have : π * (x + n * k) / n = π * x / n + k * π := by field_simp
  rw [this, Real.sin_add_int_mul_pi, abs_mul]
  simp

/-- The key spacing estimate: if `|w| ≤ 1/2` and `1 ≤ l ≤ n-1`, the point at (rescaled)
distance `l - w` from a root of unity is at angular distance at least `min (l, n-l) / n`. -/
theorem abs_sin_ge_of_int_shift (n : ℕ) (w : ℝ) (hw : |w| ≤ 1 / 2) (l : ℕ)
    (h1 : 1 ≤ l) (h2 : l < n) :
    (min (l : ℝ) ((n : ℝ) - l)) / n ≤ |Real.sin (π * (w - l) / n)| := by
  have hpi := Real.pi_pos
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le l) h2
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast h1
  have hl2 : (l : ℝ) + 1 ≤ n := by exact_mod_cast h2
  have hwabs : -(1 / 2 : ℝ) ≤ w ∧ w ≤ 1 / 2 := abs_le.1 hw
  set s : ℝ := ((l : ℝ) - w) / n with hs
  have hs0 : 0 ≤ s := by
    rw [hs]; apply div_nonneg _ hn'.le; linarith [hwabs.2]
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one hn']; linarith [hwabs.1]
  have hrewrite : π * (w - l) / n = -(π * s) := by
    rw [hs]; field_simp; ring
  rw [hrewrite, Real.sin_neg, abs_neg, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
    (by positivity) (by nlinarith))]
  have hkey := sin_pi_mul_ge s hs0 hs1
  refine le_trans ?_ hkey
  set M : ℝ := min (l : ℝ) ((n : ℝ) - l) with hM
  have hM1 : (1 : ℝ) ≤ M := le_min hl1 (by linarith)
  have hMl : M ≤ (l : ℝ) := min_le_left _ _
  have hMn : M ≤ (n : ℝ) - l := min_le_right _ _
  have hs' : M / 2 ≤ (l : ℝ) - w := by linarith [hwabs.2]
  have hs'' : M / 2 ≤ (n : ℝ) - l + w := by linarith [hwabs.1]
  have h1' : M / n / 2 ≤ s := by
    rw [hs, show M / (n : ℝ) / 2 = (M / 2) / n by ring]
    gcongr
  have h2' : M / n / 2 ≤ 1 - s := by
    have hsub : 1 - s = ((n : ℝ) - l + w) / n := by
      rw [hs]; field_simp; ring
    rw [hsub, show M / (n : ℝ) / 2 = (M / 2) / n by ring]
    gcongr
  have : M / n / 2 ≤ min s (1 - s) := le_min h1' h2'
  linarith

/-! ## The harmonic bound for the sum of inverse distances -/

theorem sum_inv_Ico_le (n : ℕ) : ∑ i ∈ Finset.Ico 1 n, ((i : ℝ))⁻¹ ≤ 1 + Real.log n := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  have h := harmonic_le_one_add_log (n - 1)
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have hset : Finset.Ico 1 n = Finset.Icc 1 (n - 1) := by
    ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  rw [hset]
  refine h.trans ?_
  have hpos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    have h1 : 1 ≤ n - 1 := by omega
    exact_mod_cast lt_of_lt_of_le zero_lt_one h1
  have hmono : Real.log ((n - 1 : ℕ) : ℝ) ≤ Real.log n :=
    Real.log_le_log hpos (by exact_mod_cast Nat.sub_le n 1)
  linarith

theorem sum_inv_reflect (n : ℕ) :
    ∑ l ∈ Finset.Ico 1 n, (((n : ℝ) - l))⁻¹ = ∑ l ∈ Finset.Ico 1 n, ((l : ℝ))⁻¹ := by
  refine Finset.sum_nbij' (i := fun l => n - l) (j := fun l => n - l) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Ico] at *; omega
  · intro a ha; simp only [Finset.mem_Ico] at *; omega
  · intro a ha; simp only [Finset.mem_Ico] at *; omega
  · intro a ha; simp only [Finset.mem_Ico] at *; omega
  · intro a ha
    simp only [Finset.mem_Ico] at ha
    congr 1
    have hc : ((n - a : ℕ) : ℝ) = (n : ℝ) - a := by
      have hle : a ≤ n := ha.2.le
      push_cast [Nat.cast_sub hle]; ring
    rw [hc]

theorem sum_inv_min_le (n : ℕ) :
    ∑ l ∈ Finset.Ico 1 n, (min (l : ℝ) ((n : ℝ) - l))⁻¹ ≤ 2 * (1 + Real.log n) := by
  have hstep : ∀ l ∈ Finset.Ico 1 n,
      (min (l : ℝ) ((n : ℝ) - l))⁻¹ ≤ ((l : ℝ))⁻¹ + (((n : ℝ) - l))⁻¹ := by
    intro l hl
    simp only [Finset.mem_Ico] at hl
    have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.1
    have hl2 : (1 : ℝ) ≤ (n : ℝ) - l := by
      have : (l : ℝ) + 1 ≤ n := by exact_mod_cast hl.2
      linarith
    rcases le_total (l : ℝ) ((n : ℝ) - l) with h | h
    · rw [min_eq_left h]
      have hp : (0 : ℝ) < ((n : ℝ) - l)⁻¹ := by positivity
      linarith
    · rw [min_eq_right h]
      have hp : (0 : ℝ) < ((l : ℝ))⁻¹ := by positivity
      linarith
  calc ∑ l ∈ Finset.Ico 1 n, (min (l : ℝ) ((n : ℝ) - l))⁻¹
      ≤ ∑ l ∈ Finset.Ico 1 n, (((l : ℝ))⁻¹ + (((n : ℝ) - l))⁻¹) := Finset.sum_le_sum hstep
    _ = ∑ l ∈ Finset.Ico 1 n, ((l : ℝ))⁻¹ + ∑ l ∈ Finset.Ico 1 n, (((n : ℝ) - l))⁻¹ :=
        Finset.sum_add_distrib
    _ = 2 * ∑ l ∈ Finset.Ico 1 n, ((l : ℝ))⁻¹ := by rw [sum_inv_reflect]; ring
    _ ≤ 2 * (1 + Real.log n) := by linarith [sum_inv_Ico_le n]

/-- The distance from `e^{it}` to the `j`-th root of unity, in terms of the rescaled angle. -/
theorem norm_exp_sub_zeta (n : ℕ) (hn : 0 < n) (t : ℝ) (j : ℕ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - zeta n ^ j‖
      = 2 * |Real.sin (π * (t * n / (2 * π) - j) / n)| := by
  have hpi := Real.pi_pos
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [zeta_pow_eq n hn j, norm_exp_sub_exp]
  congr 2
  rw [polyAngle]
  field_simp

set_option maxHeartbeats 1000000 in
/-- **The harmonic estimate.**  For every point of the unit circle there is a nearest root of
unity `j₀` such that the sum of the inverse distances to all the other roots is at most
`n (1 + log n) = n log (e n)`. -/
theorem exists_sum_inv_dist_le (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ∃ j0 ∈ Finset.range n,
      (∀ j ∈ (Finset.range n).erase j0, 0 < ‖Complex.exp ((t : ℂ) * Complex.I) - zeta n ^ j‖) ∧
      ∑ j ∈ (Finset.range n).erase j0,
        (‖Complex.exp ((t : ℂ) * Complex.I) - zeta n ^ j‖)⁻¹ ≤ n * (1 + Real.log n) := by
  classical
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set u : ℝ := t * n / (2 * π) with hu
  set m : ℤ := round u with hm
  set w : ℝ := u - m with hw
  have hwabs : |w| ≤ 1 / 2 := abs_sub_round u
  set j0 : ℕ := (m % (n : ℤ)).toNat with hj0def
  have hmodnn : 0 ≤ m % (n : ℤ) := Int.emod_nonneg m (by exact_mod_cast hn.ne')
  have hmodlt : m % (n : ℤ) < n := Int.emod_lt_of_pos m (by exact_mod_cast hn)
  have hj0cast : (j0 : ℤ) = m % (n : ℤ) := Int.toNat_of_nonneg hmodnn
  have hj0lt : j0 < n := by omega
  have hj0len : j0 ≤ n := hj0lt.le
  obtain ⟨q, hq⟩ : ∃ q : ℤ, (m : ℤ) - j0 = n * q := by
    refine ⟨m / n, ?_⟩
    rw [hj0cast]
    have := Int.mul_ediv_add_emod m (n : ℤ)
    omega
  have hqR : (m : ℝ) - j0 = n * q := by exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) hq
  refine ⟨j0, Finset.mem_range.2 hj0lt, ?_⟩
  set L : ℕ → ℕ := fun j => (j + (n - j0)) % n with hL
  have hmaps : ∀ j ∈ (Finset.range n).erase j0, L j ∈ Finset.Ico 1 n := by
    intro j hj
    have hj' := Finset.mem_erase.1 hj
    have hjn : j < n := Finset.mem_range.1 hj'.2
    have hne : j ≠ j0 := hj'.1
    simp only [hL, Finset.mem_Ico]
    refine ⟨?_, Nat.mod_lt _ hn⟩
    rcases Nat.lt_or_ge (j + (n - j0)) n with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega
  have hinj : Set.InjOn L (((Finset.range n).erase j0 : Finset ℕ) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Finset.mem_range,
      Set.mem_singleton_iff] at hx hy
    have hxn : x < n := hx.1
    have hyn : y < n := hy.1
    simp only [hL] at hxy
    rcases Nat.lt_or_ge (x + (n - j0)) n with h1 | h1 <;>
      rcases Nat.lt_or_ge (y + (n - j0)) n with h2 | h2
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hxy; omega
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)] at hxy; omega
    · rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)] at hxy; omega
    · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_sub_mod h2,
        Nat.mod_eq_of_lt (by omega)] at hxy; omega
  have hboth : ∀ j ∈ (Finset.range n).erase j0,
      0 < ‖Complex.exp ((t : ℂ) * Complex.I) - zeta n ^ j‖ ∧
      (‖Complex.exp ((t : ℂ) * Complex.I) - zeta n ^ j‖)⁻¹
        ≤ (n : ℝ) / 2 * (min ((L j : ℝ)) ((n : ℝ) - L j))⁻¹ := by
    intro j hj
    have hj' := Finset.mem_erase.1 hj
    have hjn : j < n := Finset.mem_range.1 hj'.2
    have hLmem := hmaps j hj
    simp only [Finset.mem_Ico] at hLmem
    have hL1 : 1 ≤ L j := hLmem.1
    have hL2 : L j < n := hLmem.2
    have hminpos : (0 : ℝ) < min ((L j : ℝ)) ((n : ℝ) - L j) := by
      have h1 : (1 : ℝ) ≤ (L j : ℝ) := by exact_mod_cast hL1
      have h2 : (L j : ℝ) + 1 ≤ n := by exact_mod_cast hL2
      exact lt_min (by linarith) (by linarith)
    obtain ⟨b, hb⟩ : ∃ b : ℤ, (L j : ℝ) = (j : ℝ) + ((n : ℝ) - j0) - n * b := by
      rcases Nat.lt_or_ge (j + (n - j0)) n with h | h
      · refine ⟨0, ?_⟩
        simp only [hL, Nat.mod_eq_of_lt h]
        push_cast [Nat.cast_sub hj0len]
        ring
      · refine ⟨1, ?_⟩
        simp only [hL, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (show j + (n - j0) - n < n by omega)]
        rw [Nat.cast_sub h]
        push_cast [Nat.cast_sub hj0len]
        ring
    have hshift : u - j = (w - L j) + n * (((q + 1 - b : ℤ)) : ℝ) := by
      rw [hb, hw]
      push_cast
      linarith [hqR]
    have hdist : ‖Complex.exp ((t : ℂ) * Complex.I) - zeta n ^ j‖
        = 2 * |Real.sin (π * (w - L j) / n)| := by
      rw [norm_exp_sub_zeta n hn t j, ← hu, hshift]
      congr 1
      exact abs_sin_add_int_mul (w - L j) n hn ((q : ℤ) + 1 - b)
    have hge : (min ((L j : ℝ)) ((n : ℝ) - L j)) / n ≤ |Real.sin (π * (w - L j) / n)| :=
      abs_sin_ge_of_int_shift n w hwabs (L j) hL1 hL2
    have h1 : (0 : ℝ) < 2 * ((min ((L j : ℝ)) ((n : ℝ) - L j)) / n) := by positivity
    refine ⟨by rw [hdist]; linarith, ?_⟩
    rw [hdist]
    calc (2 * |Real.sin (π * (w - L j) / n)|)⁻¹
        ≤ (2 * ((min ((L j : ℝ)) ((n : ℝ) - L j)) / n))⁻¹ :=
          inv_anti₀ h1 (by linarith)
      _ = (n : ℝ) / 2 * (min ((L j : ℝ)) ((n : ℝ) - L j))⁻¹ := by field_simp
  refine ⟨fun j hj => (hboth j hj).1, ?_⟩
  calc ∑ j ∈ (Finset.range n).erase j0,
        (‖Complex.exp ((t : ℂ) * Complex.I) - zeta n ^ j‖)⁻¹
      ≤ ∑ j ∈ (Finset.range n).erase j0,
          (n : ℝ) / 2 * (min ((L j : ℝ)) ((n : ℝ) - L j))⁻¹ :=
        Finset.sum_le_sum fun j hj => (hboth j hj).2
    _ = ∑ l ∈ ((Finset.range n).erase j0).image L,
          (n : ℝ) / 2 * (min ((l : ℝ)) ((n : ℝ) - l))⁻¹ :=
        (Finset.sum_image (f := fun l : ℕ => (n : ℝ) / 2 * (min ((l : ℝ)) ((n : ℝ) - l))⁻¹)
          hinj).symm
    _ ≤ ∑ l ∈ Finset.Ico 1 n, (n : ℝ) / 2 * (min ((l : ℝ)) ((n : ℝ) - l))⁻¹ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun l hl _ => ?_)
        · intro l hl
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hl
          exact hmaps j hj
        · simp only [Finset.mem_Ico] at hl
          have h1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl.1
          have h2 : (l : ℝ) + 1 ≤ n := by exact_mod_cast hl.2
          have : (0 : ℝ) < min ((l : ℝ)) ((n : ℝ) - l) := lt_min (by linarith) (by linarith)
          positivity
    _ = (n : ℝ) / 2 * ∑ l ∈ Finset.Ico 1 n, (min ((l : ℝ)) ((n : ℝ) - l))⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (n : ℝ) / 2 * (2 * (1 + Real.log n)) := by
        have := sum_inv_min_le n
        nlinarith
    _ = n * (1 + Real.log n) := by ring

/-! ## Stability of the regular polygon configuration -/

set_option maxHeartbeats 1000000 in
/-- **Stability of the regular `n`-gon.**  If each vertex of the regular `n`-gon is moved by an
angle at most `η ≥ 0`, then

`Dₙ ≤ (2 + nη) · exp (n η log (e n))`,

with `log (e n) = 1 + log n`. -/
theorem chordMax_perturbed_le (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 ≤ η) (ε : ℕ → ℝ)
    (hε : ∀ j, |ε j| ≤ η) :
    chordMax (fun j : Fin n => polyAngle n j + ε j)
      ≤ (2 + n * η) * Real.exp (n * η * (1 + Real.log n)) := by
  classical
  rw [chordMax_eq_iSup]
  refine ciSup_le fun t => ?_
  set z : ℂ := Complex.exp ((t : ℂ) * Complex.I) with hzdef
  have hz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I t
  obtain ⟨j0, hj0, hpos, hsum⟩ := exists_sum_inv_dist_le n hn t
  set a : ℕ → ℝ := fun j => ‖z - zeta n ^ j‖ with hadef
  set b : ℕ → ℝ := fun j =>
    ‖z - Complex.exp (((polyAngle n j + ε j : ℝ) : ℂ) * Complex.I)‖ with hbdef
  have hbnn : ∀ j, 0 ≤ b j := fun j => norm_nonneg _
  have hann : ∀ j, 0 ≤ a j := fun j => norm_nonneg _
  have hb_le : ∀ j, b j ≤ a j + η := by
    intro j
    have hshift : ‖zeta n ^ j - Complex.exp (((polyAngle n j + ε j : ℝ) : ℂ) * Complex.I)‖ ≤ η := by
      rw [zeta_pow_eq n hn j, norm_exp_sub_exp]
      have hhalf : (polyAngle n j - (polyAngle n j + ε j)) / 2 = -(ε j / 2) := by ring
      rw [hhalf, Real.sin_neg, abs_neg]
      have h1 : |Real.sin (ε j / 2)| ≤ |ε j / 2| := Real.abs_sin_le_abs
      have h2 : |ε j / 2| = |ε j| / 2 := by rw [abs_div]; simp
      have h3 := hε j
      rw [h2] at h1
      linarith
    calc b j = ‖(z - zeta n ^ j) + (zeta n ^ j
              - Complex.exp (((polyAngle n j + ε j : ℝ) : ℂ) * Complex.I))‖ := by
          rw [hbdef]; ring_nf
      _ ≤ a j + ‖zeta n ^ j - Complex.exp (((polyAngle n j + ε j : ℝ) : ℂ) * Complex.I)‖ :=
          norm_add_le _ _
      _ ≤ a j + η := by linarith
  -- the product over one period
  have hchord : ∏ j : Fin n, ‖z - Complex.exp (((polyAngle n ↑j + ε ↑j : ℝ) : ℂ) * Complex.I)‖
      = ∏ j ∈ Finset.range n, b j := by
    rw [Fin.prod_univ_eq_prod_range (fun j => b j) n]
  set P : ℝ := ∏ j ∈ (Finset.range n).erase j0, a j with hP
  have hPpos : 0 < P := Finset.prod_pos fun j hj => hpos j hj
  have hPle : P ≤ n := prod_erase_le n hn j0 hj0 z hz.le
  have hall : a j0 * P = ‖z ^ n - 1‖ := by
    rw [hP, hadef, Finset.mul_prod_erase _ (fun j => ‖z - zeta n ^ j‖) hj0]
    exact prod_all_eq n hn z
  have hzn : ‖z ^ n - 1‖ ≤ 2 := by
    calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num
  -- exponential comparison
  have hexp : ∏ j ∈ (Finset.range n).erase j0, (a j + η)
      ≤ P * Real.exp (η * ∑ j ∈ (Finset.range n).erase j0, (a j)⁻¹) := by
    have hstep : ∀ j ∈ (Finset.range n).erase j0,
        a j + η ≤ a j * Real.exp (η * (a j)⁻¹) := by
      intro j hj
      have hj' : 0 < a j := hpos j hj
      have hne : a j ≠ 0 := ne_of_gt hj'
      have h1 : 1 + η * (a j)⁻¹ ≤ Real.exp (η * (a j)⁻¹) := by
        have := Real.add_one_le_exp (η * (a j)⁻¹)
        linarith
      have h2 : a j * (1 + η * (a j)⁻¹) = a j + η := by field_simp
      calc a j + η = a j * (1 + η * (a j)⁻¹) := h2.symm
        _ ≤ a j * Real.exp (η * (a j)⁻¹) := by
            exact mul_le_mul_of_nonneg_left h1 hj'.le
    calc ∏ j ∈ (Finset.range n).erase j0, (a j + η)
        ≤ ∏ j ∈ (Finset.range n).erase j0, (a j * Real.exp (η * (a j)⁻¹)) :=
          Finset.prod_le_prod (fun j _ => by positivity) hstep
      _ = P * ∏ j ∈ (Finset.range n).erase j0, Real.exp (η * (a j)⁻¹) := by
          rw [Finset.prod_mul_distrib]
      _ = P * Real.exp (η * ∑ j ∈ (Finset.range n).erase j0, (a j)⁻¹) := by
          rw [← Real.exp_sum, Finset.mul_sum]
  -- assembling
  have hmain : ∏ j ∈ Finset.range n, b j
      ≤ (2 + n * η) * Real.exp (η * ∑ j ∈ (Finset.range n).erase j0, (a j)⁻¹) := by
    have hsplit : ∏ j ∈ Finset.range n, b j = b j0 * ∏ j ∈ (Finset.range n).erase j0, b j :=
      (Finset.mul_prod_erase _ _ hj0).symm
    have h1 : ∏ j ∈ (Finset.range n).erase j0, b j ≤ ∏ j ∈ (Finset.range n).erase j0, (a j + η) :=
      Finset.prod_le_prod (fun j _ => hbnn j) (fun j _ => hb_le j)
    have h2 : b j0 * ∏ j ∈ (Finset.range n).erase j0, b j
        ≤ (a j0 + η) * ∏ j ∈ (Finset.range n).erase j0, (a j + η) := by
      refine mul_le_mul (hb_le j0) h1 (Finset.prod_nonneg fun j _ => hbnn j) (by
        have := hann j0; linarith)
    have hE : (0 : ℝ) < Real.exp (η * ∑ j ∈ (Finset.range n).erase j0, (a j)⁻¹) := Real.exp_pos _
    have h3 : (a j0 + η) * ∏ j ∈ (Finset.range n).erase j0, (a j + η)
        ≤ (a j0 + η) * (P * Real.exp (η * ∑ j ∈ (Finset.range n).erase j0, (a j)⁻¹)) :=
      mul_le_mul_of_nonneg_left hexp (by have := hann j0; linarith)
    have h4 : (a j0 + η) * P ≤ 2 + n * η := by
      have : (a j0 + η) * P = a j0 * P + η * P := by ring
      rw [this, hall]
      have : η * P ≤ η * n := mul_le_mul_of_nonneg_left hPle hη
      linarith
    calc ∏ j ∈ Finset.range n, b j = b j0 * ∏ j ∈ (Finset.range n).erase j0, b j := hsplit
      _ ≤ (a j0 + η) * ∏ j ∈ (Finset.range n).erase j0, (a j + η) := h2
      _ ≤ (a j0 + η) * (P * Real.exp (η * ∑ j ∈ (Finset.range n).erase j0, (a j)⁻¹)) := h3
      _ = ((a j0 + η) * P) * Real.exp (η * ∑ j ∈ (Finset.range n).erase j0, (a j)⁻¹) := by ring
      _ ≤ (2 + n * η) * Real.exp (η * ∑ j ∈ (Finset.range n).erase j0, (a j)⁻¹) :=
          mul_le_mul_of_nonneg_right h4 hE.le
  have hexpmono : Real.exp (η * ∑ j ∈ (Finset.range n).erase j0, (a j)⁻¹)
      ≤ Real.exp (n * η * (1 + Real.log n)) := by
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hsum hη
    calc η * ∑ j ∈ (Finset.range n).erase j0, (a j)⁻¹ ≤ η * ((n : ℝ) * (1 + Real.log n)) := this
      _ = n * η * (1 + Real.log n) := by ring
  have hfinal : (0 : ℝ) ≤ 2 + n * η := by positivity
  calc ∏ j : Fin n, ‖z - Complex.exp (((polyAngle n ↑j + ε ↑j : ℝ) : ℂ) * Complex.I)‖
      = ∏ j ∈ Finset.range n, b j := hchord
    _ ≤ (2 + n * η) * Real.exp (η * ∑ j ∈ (Finset.range n).erase j0, (a j)⁻¹) := hmain
    _ ≤ (2 + n * η) * Real.exp (n * η * (1 + Real.log n)) :=
        mul_le_mul_of_nonneg_left hexpmono hfinal

/-! ## The regular-polygon event and its probability -/

/-- The arc of length `η` starting at the `k`-th vertex of the regular `n`-gon. -/
noncomputable def arc (n : ℕ) (η : ℝ) (k : ℕ) : Set ℝ :=
  Set.Ico (polyAngle n k) (polyAngle n k + η)

theorem measurableSet_arc (n : ℕ) (η : ℝ) (k : ℕ) : MeasurableSet (arc n η k) :=
  measurableSet_Ico

theorem arc_subset (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : η ≤ 2 * π / n) (k : ℕ)
    (hk : k < n) : arc n η k ⊆ Set.Ico 0 (2 * π) := by
  have hpi := Real.pi_pos
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hkR : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  intro x hx
  simp only [arc, Set.mem_Ico, polyAngle] at hx ⊢
  constructor
  · have : (0 : ℝ) ≤ 2 * π * k / n := by positivity
    linarith [hx.1]
  · have hle : 2 * π * k / n + 2 * π / n ≤ 2 * π := by
      rw [← add_div, div_le_iff₀ hnR]
      nlinarith
    linarith [hx.2]

theorem arc_disjoint (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : η ≤ 2 * π / n) {k k' : ℕ}
    (hne : k ≠ k') : Disjoint (arc n η k) (arc n η k') := by
  have hpi := Real.pi_pos
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hmono : ∀ i j : ℕ, i < j → polyAngle n i + η ≤ polyAngle n j := by
    intro i j hij
    have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    simp only [polyAngle]
    have h1 : 2 * π * i / n + 2 * π / n ≤ 2 * π * j / n := by
      rw [← add_div, div_le_div_iff_of_pos_right hnR]
      nlinarith
    linarith
  rcases Nat.lt_or_ge k k' with h | h
  · refine Set.disjoint_left.2 fun x hx hx' => ?_
    simp only [arc, Set.mem_Ico] at hx hx'
    linarith [hmono k k' h, hx.2, hx'.1]
  · have h' : k' < k := by omega
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    simp only [arc, Set.mem_Ico] at hx hx'
    linarith [hmono k' k h', hx.1, hx'.2]

theorem angleLaw_arc (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : η ≤ 2 * π / n) (k : ℕ)
    (hk : k < n) : angleLaw (arc n η k) = ENNReal.ofReal (η / (2 * π)) := by
  have hpi := Real.pi_pos
  rw [angleLaw, Measure.smul_apply, Measure.restrict_apply (measurableSet_arc n η k), smul_eq_mul,
    Set.inter_eq_self_of_subset_left (arc_subset n hn η hη k hk), arc, Real.volume_Ico]
  rw [show polyAngle n k + η - polyAngle n k = η by ring]
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- The event that the `j`-th point lies in the arc attached to the vertex `σ j`. -/
noncomputable def permBox (n : ℕ) (η : ℝ) (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  Set.univ.pi fun j : Fin n => arc n η (σ j)

theorem measurableSet_permBox (n : ℕ) (η : ℝ) (σ : Equiv.Perm (Fin n)) :
    MeasurableSet (permBox n η σ) :=
  MeasurableSet.univ_pi fun _ => measurableSet_arc n η _

theorem measure_permBox (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : η ≤ 2 * π / n)
    (σ : Equiv.Perm (Fin n)) :
    angleLawN n (permBox n η σ) = ENNReal.ofReal (η / (2 * π)) ^ n := by
  rw [permBox, angleLawN, Measure.pi_pi]
  rw [Finset.prod_congr rfl (fun j _ => angleLaw_arc n hn η hη (σ j) (σ j).isLt)]
  simp

theorem permBox_disjoint (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : η ≤ 2 * π / n) :
    (Set.univ : Set (Equiv.Perm (Fin n))).PairwiseDisjoint (permBox n η) := by
  intro σ _ τ _ hne
  obtain ⟨j, hj⟩ : ∃ j : Fin n, σ j ≠ τ j := by
    by_contra h
    push_neg at h
    exact hne (Equiv.ext fun j => h j)
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  have h1 : x j ∈ arc n η (σ j) := hx j (Set.mem_univ j)
  have h2 : x j ∈ arc n η (τ j) := hx' j (Set.mem_univ j)
  have hdisj := arc_disjoint n hn η hη (fun h => hj (Fin.ext h))
  exact (Set.disjoint_left.1 hdisj h1) h2

/-- The union over all `n!` labellings of the points to the arcs. -/
noncomputable def polygonEvent (n : ℕ) (η : ℝ) : Set (Fin n → ℝ) :=
  ⋃ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), permBox n η σ

theorem measure_polygonEvent (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : η ≤ 2 * π / n) :
    angleLawN n (polygonEvent n η) = (n ! : ℝ≥0∞) * ENNReal.ofReal (η / (2 * π)) ^ n := by
  classical
  rw [polygonEvent,
    measure_biUnion_finset
      (by
        intro σ _ τ _ hne
        exact permBox_disjoint n hn η hη (Set.mem_univ σ) (Set.mem_univ τ) hne)
      (fun σ _ => measurableSet_permBox n η σ)]
  rw [Finset.sum_congr rfl (fun σ _ => measure_permBox n hn η hη σ), Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-! ## The lower bound for `ℙ(Dₙ < α)` -/

theorem polygonEvent_subset (n : ℕ) (hn : 0 < n) (η : ℝ) (hη0 : 0 ≤ η) :
    polygonEvent n η ⊆
      {θ : Fin n → ℝ | chordMax θ ≤ (2 + n * η) * Real.exp (n * η * (1 + Real.log n))} := by
  classical
  intro θ hθ
  simp only [polygonEvent, Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and] at hθ
  obtain ⟨σ, hσ⟩ := hθ
  set ε : ℕ → ℝ := fun k => if h : k < n then θ (σ.symm ⟨k, h⟩) - polyAngle n k else 0 with hε
  have hmem : ∀ k (h : k < n), θ (σ.symm ⟨k, h⟩) ∈ arc n η k := by
    intro k h
    have := hσ (σ.symm ⟨k, h⟩) (Set.mem_univ _)
    simpa using this
  have hεbound : ∀ k, |ε k| ≤ η := by
    intro k
    by_cases h : k < n
    · have hk := hmem k h
      simp only [arc, Set.mem_Ico] at hk
      simp only [hε, dif_pos h, abs_le]
      constructor <;> linarith [hk.1, hk.2]
    · simp only [hε, dif_neg h, abs_zero]
      exact hη0
  have hcfg : (θ ∘ σ.symm) = fun i : Fin n => polyAngle n ↑i + ε ↑i := by
    funext i
    simp only [Function.comp_apply, hε, dif_pos i.isLt]
    have : (⟨(i : ℕ), i.isLt⟩ : Fin n) = i := Fin.ext rfl
    rw [this]
    ring
  have hrewrite : chordMax θ = chordMax (fun i : Fin n => polyAngle n ↑i + ε ↑i) := by
    rw [← hcfg, chordMax_comp_equiv θ σ.symm]
  rw [Set.mem_setOf_eq, hrewrite]
  exact chordMax_perturbed_le n hn η hη0 ε hεbound

/-- The quantitative lower bound: whenever the stability bound at scale `η` is below `α`, the
regular-polygon event of `n!` arcs is contained in `{Dₙ < α}`. -/
theorem probLT_ge (n : ℕ) (hn : 0 < n) (η α : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 2 * π / n)
    (hbound : (2 + n * η) * Real.exp (n * η * (1 + Real.log n)) < α) :
    (n ! : ℝ) * (η / (2 * π)) ^ n ≤ probLT n α := by
  have hpi := Real.pi_pos
  have hsub : polygonEvent n η ⊆ {θ : Fin n → ℝ | chordMax θ < α} := by
    intro θ hθ
    exact lt_of_le_of_lt (polygonEvent_subset n hn η hη0 hθ) hbound
  have hmono : angleLawN n (polygonEvent n η) ≤ angleLawN n {θ : Fin n → ℝ | chordMax θ < α} :=
    measure_mono hsub
  rw [measure_polygonEvent n hn η hη] at hmono
  have htoReal := ENNReal.toReal_mono (measure_ne_top (angleLawN n) _) hmono
  refine le_trans (le_of_eq ?_) htoReal
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_natCast]

/-- **The constructive exceptional lower bound.**  For every `α > 2` there is `c > 0` with

`ℙ(Dₙ < α) ≥ n! (c / (π n log n))ⁿ`

for all large `n`. -/
theorem exceptional_lower_bound (α : ℝ) (hα : 2 < α) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (n ! : ℝ) * (c / (π * n * Real.log n)) ^ n ≤ probLT n α := by
  have hpi := Real.pi_pos
  set c : ℝ := Real.log (α / 2) / 4 with hc
  have hy : (1 : ℝ) < α / 2 := by linarith
  have hcpos : 0 < c := by
    rw [hc]
    have : 0 < Real.log (α / 2) := Real.log_pos hy
    linarith
  refine ⟨c, hcpos, ?_⟩
  -- the limit of the stability bound
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun n : ℕ => (Real.log n)⁻¹) atTop (nhds 0) :=
    hlog.inv_tendsto_atTop
  have hg : Filter.Tendsto
      (fun n : ℕ => (2 + 2 * c * (Real.log n)⁻¹) * Real.exp (2 * c * (Real.log n)⁻¹ + 2 * c))
      atTop (nhds ((2 + 2 * c * 0) * Real.exp (2 * c * 0 + 2 * c))) := by
    refine Filter.Tendsto.mul ?_ ?_
    · exact tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
    · exact (Real.continuous_exp.tendsto _).comp
        ((tendsto_const_nhds.mul hinv).add tendsto_const_nhds)
  have hlimit : (2 + 2 * c * 0) * Real.exp (2 * c * 0 + 2 * c) < α := by
    have hexp : Real.exp (2 * c) = Real.sqrt (α / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith)]
      congr 1
      rw [hc]; ring
    have hsqrt : Real.sqrt (α / 2) < α / 2 := by
      have h1 : Real.sqrt 1 < Real.sqrt (α / 2) * Real.sqrt (α / 2) := by
        rw [Real.mul_self_sqrt (by linarith)]; simpa using hy
      simp only [Real.sqrt_one] at h1
      nlinarith [Real.sq_sqrt (le_of_lt (lt_trans zero_lt_one hy)), Real.sqrt_nonneg (α / 2)]
    simp only [mul_zero, add_zero, zero_add]
    rw [hexp]
    linarith
  have hev1 : ∀ᶠ n : ℕ in atTop,
      (2 + 2 * c * (Real.log n)⁻¹) * Real.exp (2 * c * (Real.log n)⁻¹ + 2 * c) < α :=
    hg.eventually_lt_const hlimit
  have hev2 : ∀ᶠ n : ℕ in atTop, c ≤ π * Real.log n := by
    have : Filter.Tendsto (fun n : ℕ => π * Real.log n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hpi hlog
    exact this.eventually_ge_atTop c
  have hev3 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n := hlog.eventually_ge_atTop 1
  filter_upwards [hev1, hev2, hev3, Filter.eventually_gt_atTop 0] with n hn1 hn2 hn3 hn0
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hlogpos : (0 : ℝ) < Real.log n := lt_of_lt_of_le zero_lt_one hn3
  set η : ℝ := 2 * c / (n * Real.log n) with hη
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  have hηle : η ≤ 2 * π / n := by
    rw [hη, div_le_div_iff₀ (by positivity) hnR]
    have : c ≤ π * Real.log n := hn2
    nlinarith
  have hnη : (n : ℝ) * η = 2 * c / Real.log n := by
    rw [hη]; field_simp
  have hbound : (2 + n * η) * Real.exp (n * η * (1 + Real.log n)) < α := by
    rw [hnη]
    have harg : 2 * c / Real.log n * (1 + Real.log n)
        = 2 * c * (Real.log n)⁻¹ + 2 * c := by field_simp
    rw [harg, show 2 * c / Real.log n = 2 * c * (Real.log n)⁻¹ by ring]
    exact hn1
  have hkey := probLT_ge n hn0 η α hη0 hηle hbound
  have heq : η / (2 * π) = c / (π * n * Real.log n) := by
    rw [hη]; field_simp
  rwa [heq] at hkey

/-- **The exponential form of the lower bound.** -/
theorem exceptional_lower_bound_exp (α : ℝ) (hα : 2 < α) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      Real.exp (-(n : ℝ) * Real.log (Real.log n) - C * n) ≤ probLT n α := by
  have hpi := Real.pi_pos
  obtain ⟨c, hcpos, hev⟩ := exceptional_lower_bound α hα
  refine ⟨1 + Real.log π - Real.log c, ?_⟩
  filter_upwards [hev, Filter.eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with n hn hn0 hn1
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hlogpos : (0 : ℝ) < Real.log n := lt_of_lt_of_le zero_lt_one hn1
  -- Stirling lower bound for the factorial
  have hstirling : ((n : ℝ) / Real.exp 1) ^ n ≤ (n ! : ℝ) := by
    refine le_trans ?_ (Stirling.le_factorial_stirling n)
    have h1 : (1 : ℝ) ≤ Real.sqrt (2 * π * n) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      apply Real.sqrt_le_sqrt
      have h1n : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn0
      nlinarith [Real.pi_gt_three]
    have h2 : (0 : ℝ) ≤ ((n : ℝ) / Real.exp 1) ^ n := by positivity
    nlinarith
  have hxpos : 0 < c / (π * n * Real.log n) := by positivity
  have hmul : ((n : ℝ) / Real.exp 1) ^ n * (c / (π * n * Real.log n)) ^ n
      ≤ (n ! : ℝ) * (c / (π * n * Real.log n)) ^ n := by
    have : (0 : ℝ) ≤ (c / (π * n * Real.log n)) ^ n := by positivity
    nlinarith
  have hprod : ((n : ℝ) / Real.exp 1) ^ n * (c / (π * n * Real.log n)) ^ n
      = (c / (Real.exp 1 * π * Real.log n)) ^ n := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hexp_eq : (c / (Real.exp 1 * π * Real.log n)) ^ n
      = Real.exp ((n : ℝ) * Real.log (c / (Real.exp 1 * π * Real.log n))) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hlog_eq : Real.log (c / (Real.exp 1 * π * Real.log n))
      = Real.log c - 1 - Real.log π - Real.log (Real.log n) := by
    rw [Real.log_div (ne_of_gt hcpos) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_exp]
    ring
  have hfinal : Real.exp (-(n : ℝ) * Real.log (Real.log n) - (1 + Real.log π - Real.log c) * n)
      ≤ (c / (Real.exp 1 * π * Real.log n)) ^ n := by
    rw [hexp_eq, hlog_eq]
    apply Real.exp_le_exp.2
    apply le_of_eq
    ring
  calc Real.exp (-(n : ℝ) * Real.log (Real.log n) - (1 + Real.log π - Real.log c) * n)
      ≤ (c / (Real.exp 1 * π * Real.log n)) ^ n := hfinal
    _ = ((n : ℝ) / Real.exp 1) ^ n * (c / (π * n * Real.log n)) ^ n := hprod.symm
    _ ≤ (n ! : ℝ) * (c / (π * n * Real.log n)) ^ n := hmul
    _ ≤ probLT n α := hn

end Q788
