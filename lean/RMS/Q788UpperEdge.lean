/-
# Q788 — Stage 5: the local analysis at the upper edge `Dₙ ↑ 2ⁿ`

This module develops the deterministic analysis behind the upper-edge asymptotics of
`Q788.chordMax`.  Writing the free point of the circle as `e^{i(s+π)}` turns the chord
product into `2ⁿ ∏_j |cos((s - θ_j)/2)|`, so that

`Dₙ(θ) = 2ⁿ · sup_s ∏_j |cos((s - θ_j)/2)|`,

and the upper edge `Dₙ ↑ 2ⁿ` is the regime where all the points cluster.
-/
import RMS.Q788Probability

open Real Complex MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Q788

/-! ## The chord product in cosine form -/

/-- `cosProd x = ∏_j |cos (x_j / 2)|`. -/
noncomputable def cosProd {n : ℕ} (x : Fin n → ℝ) : ℝ := ∏ j, |Real.cos (x j / 2)|

theorem cosProd_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ cosProd x :=
  Finset.prod_nonneg fun _ _ => abs_nonneg _

theorem cosProd_le_one {n : ℕ} (x : Fin n → ℝ) : cosProd x ≤ 1 := by
  calc cosProd x ≤ ∏ _j : Fin n, (1 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun j _ => Real.abs_cos_le_one _
    _ = 1 := by simp

/-- Each factor of `cosProd` dominates the whole product. -/
theorem cosProd_le_factor {n : ℕ} (x : Fin n → ℝ) (j : Fin n) :
    cosProd x ≤ |Real.cos (x j / 2)| := by
  classical
  rw [cosProd, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  have h1 : ∏ k ∈ Finset.univ.erase j, |Real.cos (x k / 2)| ≤ 1 := by
    calc ∏ k ∈ Finset.univ.erase j, |Real.cos (x k / 2)|
        ≤ ∏ _k ∈ Finset.univ.erase j, (1 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun k _ => Real.abs_cos_le_one _
      _ = 1 := by simp
  nlinarith [Finset.prod_nonneg (fun k (_ : k ∈ Finset.univ.erase j) => abs_nonneg
    (Real.cos (x k / 2))), abs_nonneg (Real.cos (x j / 2))]

/-- Shifting the free point by `π` turns the chord product into `2ⁿ cosProd`. -/
theorem chordProd_add_pi {n : ℕ} (θ : Fin n → ℝ) (s : ℝ) :
    chordProd θ (s + π) = 2 ^ n * cosProd (fun j => s - θ j) := by
  unfold chordProd cosProd
  have h2 : (2 : ℝ) ^ n = ∏ _j : Fin n, (2 : ℝ) := by simp
  rw [h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [norm_exp_sub_exp]
  congr 1
  rw [show (s + π - θ j) / 2 = (s - θ j) / 2 + π / 2 by ring, Real.sin_add_pi_div_two]

/-- One half of `Dₙ(θ) = 2ⁿ sup_s cosProd`. -/
theorem two_pow_mul_cosProd_le_chordMax {n : ℕ} (θ : Fin n → ℝ) (s : ℝ) :
    2 ^ n * cosProd (fun j => s - θ j) ≤ chordMax θ := by
  rw [← chordProd_add_pi θ s]
  exact chordProd_le_chordMax θ (s + π)

/-- The other half: a uniform bound on `2ⁿ cosProd` bounds `Dₙ`. -/
theorem chordMax_le_of_cosProd_le {n : ℕ} (θ : Fin n → ℝ) (B : ℝ)
    (h : ∀ s : ℝ, 2 ^ n * cosProd (fun j => s - θ j) ≤ B) : chordMax θ ≤ B := by
  refine ciSup_le fun t => ?_
  have := h (t - π)
  rwa [← chordProd_add_pi θ (t - π), sub_add_cancel] at this

/-! ## Localization: a near-maximal configuration is clustered -/

/-- The elementary lower bound `|sin u| ≥ (2/π) · dist(u, πℤ)`. -/
theorem abs_sin_ge_dist (u : ℝ) :
    2 / π * |u - π * round (u / π)| ≤ |Real.sin u| := by
  have hpi := Real.pi_pos
  set k : ℤ := round (u / π) with hk
  have hdist : |u - π * k| ≤ π / 2 := by
    have hr : |u / π - (k : ℝ)| ≤ 1 / 2 := by rw [hk]; exact abs_sub_round (u / π)
    have h' : u - π * k = π * (u / π - (k : ℝ)) := by field_simp
    rw [h', abs_mul, abs_of_pos hpi]
    nlinarith [abs_nonneg (u / π - (k : ℝ))]
  have hsinshift : |Real.sin u| = |Real.sin (u - π * k)| := by
    rw [show u - π * k = u - k * π by ring, Real.sin_sub_int_mul_pi, abs_mul]
    simp
  rw [hsinshift]
  rcases le_or_gt 0 (u - π * (k : ℝ)) with hpos | hneg
  · have h1 : u - π * k ≤ π / 2 := by
      have := hdist; rw [abs_of_nonneg hpos] at this; linarith
    have hs := Real.mul_le_sin hpos (by linarith)
    rw [abs_of_nonneg hpos, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hpos (by linarith))]
    linarith
  · have hpos' : (0 : ℝ) ≤ -(u - π * k) := by linarith
    have h1 : -(u - π * k) ≤ π / 2 := by
      have := hdist; rw [abs_of_neg hneg] at this; linarith
    have hs := Real.mul_le_sin hpos' (by linarith)
    rw [Real.sin_neg] at hs
    rw [abs_of_nonpos (le_of_lt hneg),
      abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_lt hneg) (by linarith))]
    linarith

/-- If `|cos (y/2)| ≥ 1 - δ` then `y` is within `π√(2δ)` of `2πℤ`. -/
theorem exists_int_dist_le_of_abs_cos_ge (y δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h : 1 - δ ≤ |Real.cos (y / 2)|) :
    ∃ k : ℤ, |y - 2 * π * k| ≤ π * Real.sqrt (2 * δ) := by
  have hpi := Real.pi_pos
  set u := y / 2 with hu
  have hsin : |Real.sin u| ≤ Real.sqrt (2 * δ) := by
    have hpy : Real.sin u ^ 2 + Real.cos u ^ 2 = 1 := Real.sin_sq_add_cos_sq _
    have h2 : Real.sin u ^ 2 ≤ 2 * δ := by
      have habs : (1 - δ) ^ 2 ≤ Real.cos u ^ 2 := by
        rw [← sq_abs (Real.cos u)]
        exact pow_le_pow_left₀ (by linarith) h 2
      nlinarith
    have := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq_eq_abs] at this
  set k : ℤ := round (u / π) with hk
  have hlower := abs_sin_ge_dist u
  rw [← hk] at hlower
  have h3 : 2 / π * |u - π * (k : ℝ)| ≤ Real.sqrt (2 * δ) := hlower.trans hsin
  rw [div_mul_eq_mul_div, div_le_iff₀ hpi] at h3
  refine ⟨k, ?_⟩
  have hy : y - 2 * π * (k : ℝ) = 2 * (u - π * (k : ℝ)) := by rw [hu]; ring
  rw [hy, abs_mul, abs_two]
  linarith


/-! ## Elementary product inequalities -/

/-- Weierstrass' product inequality. -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ j ∈ s, 0 ≤ a j) (h1 : ∀ j ∈ s, a j ≤ 1) :
    1 - ∑ j ∈ s, a j ≤ ∏ j ∈ s, (1 - a j) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.sum_insert hx]
      have hax : 0 ≤ a x := h0 x (by simp)
      have hax1 : a x ≤ 1 := h1 x (by simp)
      have hih := ih (fun j hj => h0 j (by simp [hj])) (fun j hj => h1 j (by simp [hj]))
      have hprod : ∏ j ∈ s, (1 - a j) ≤ 1 :=
        Finset.prod_le_one (fun j hj => by have := h1 j (by simp [hj]); linarith)
          (fun j hj => by have := h0 j (by simp [hj]); linarith)
      nlinarith

/-- The matching second-order upper bound for a product of factors `1 - aⱼ`. -/
theorem prod_one_sub_le {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ j ∈ s, 0 ≤ a j) (h1 : ∀ j ∈ s, a j ≤ 1) :
    ∏ j ∈ s, (1 - a j) ≤ 1 - ∑ j ∈ s, a j + (∑ j ∈ s, a j) ^ 2 / 2 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.sum_insert hx]
      have hax : 0 ≤ a x := h0 x (by simp)
      have hax1 : a x ≤ 1 := h1 x (by simp)
      have hih := ih (fun j hj => h0 j (by simp [hj])) (fun j hj => h1 j (by simp [hj]))
      have hSnn : 0 ≤ ∑ j ∈ s, a j :=
        Finset.sum_nonneg fun j hj => h0 j (by simp [hj])
      have hprodnn : 0 ≤ ∏ j ∈ s, (1 - a j) :=
        Finset.prod_nonneg fun j hj => by have := h1 j (by simp [hj]); linarith
      nlinarith [sq_nonneg (∑ j ∈ s, a j), sq_nonneg (a x)]

/-! ## The quadratic expansion of the cosine product -/

/-- `1 - cos(u/2) = u²/8 + O(u⁴)`. -/
theorem abs_one_sub_cos_half_sub (u : ℝ) (hu : |u| ≤ 1) :
    |(1 - Real.cos (u / 2)) - u ^ 2 / 8| ≤ u ^ 4 / 100 := by
  have hu2 : |u / 2| ≤ 1 := by rw [abs_div]; simp only [abs_two]; linarith [abs_nonneg u]
  have hb := Real.cos_bound hu2
  have hxx : (u / 2) ^ 2 / 2 = u ^ 2 / 8 := by ring
  rw [hxx] at hb
  have habs : |u / 2| ^ 4 = u ^ 4 / 16 := by
    rw [abs_div]
    simp only [abs_two]
    rw [div_pow, ← abs_pow]
    have : |u ^ 4| = u ^ 4 := abs_of_nonneg (by positivity)
    rw [this]
    norm_num
  rw [habs] at hb
  have heq : (1 - Real.cos (u / 2)) - u ^ 2 / 8 = -(Real.cos (u / 2) - (1 - u ^ 2 / 8)) := by ring
  rw [heq, abs_neg]
  have h4 : (0:ℝ) ≤ u ^ 4 := by positivity
  linarith

theorem cos_half_pos (u : ℝ) (hu : |u| ≤ 1) : 0 < Real.cos (u / 2) := by
  have hpi := Real.pi_gt_three
  have h1 : -(π / 2) < u / 2 := by
    have := neg_abs_le u; linarith
  have h2 : u / 2 < π / 2 := by
    have := le_abs_self u; linarith
  exact Real.cos_pos_of_mem_Ioo ⟨h1, h2⟩

theorem cosProd_eq_prod_one_sub {n : ℕ} (x : Fin n → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    cosProd x = ∏ j, (1 - (1 - Real.cos (x j / 2))) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [show (1 : ℝ) - (1 - Real.cos (x j / 2)) = Real.cos (x j / 2) by ring]
  exact abs_of_pos (cos_half_pos (x j) (hx j))

/-- `sumSq x = ∑ⱼ xⱼ²`. -/
noncomputable def sumSq {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ j, (x j) ^ 2

theorem sumSq_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ sumSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sq_le_sumSq {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : (x j) ^ 2 ≤ sumSq x :=
  Finset.single_le_sum (f := fun k => (x k) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

/-- The deviation between `∑ⱼ (1 - cos(xⱼ/2))` and `sumSq x / 8`. -/
theorem abs_sum_one_sub_cos_sub (n : ℕ) (x : Fin n → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    |(∑ j, (1 - Real.cos (x j / 2))) - sumSq x / 8| ≤ (∑ j, (x j) ^ 4) / 100 := by
  have hsplit : (∑ j, (1 - Real.cos (x j / 2))) - sumSq x / 8
      = ∑ j, ((1 - Real.cos (x j / 2)) - (x j) ^ 2 / 8) := by
    rw [sumSq, Finset.sum_div, ← Finset.sum_sub_distrib]
  rw [hsplit]
  calc |∑ j, ((1 - Real.cos (x j / 2)) - (x j) ^ 2 / 8)|
      ≤ ∑ j, |(1 - Real.cos (x j / 2)) - (x j) ^ 2 / 8| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (x j) ^ 4 / 100 :=
        Finset.sum_le_sum fun j _ => abs_one_sub_cos_half_sub (x j) (hx j)
    _ = (∑ j, (x j) ^ 4) / 100 := by rw [Finset.sum_div]


/-! ## The two-sided quadratic sandwich for `cosProd` -/

theorem abs_le_one_of_sq_le_one {u : ℝ} (h : u ^ 2 ≤ 1) : |u| ≤ 1 := by
  nlinarith [sq_abs u, abs_nonneg u]

theorem sum_pow_four_le_sq_sumSq {n : ℕ} (x : Fin n → ℝ) :
    ∑ j, (x j) ^ 4 ≤ (sumSq x) ^ 2 := by
  have hcong : ∑ j, (x j) ^ 4 = ∑ j, ((x j) ^ 2) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [hcong, sumSq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => sq_nonneg _

/-- **Sufficient direction.**  A configuration with small quadratic energy has a large
cosine product. -/
theorem one_sub_le_cosProd {n : ℕ} (x : Fin n → ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8)
    (hsum : sumSq x ≤ 8 * δ) : 1 - δ - δ ^ 2 ≤ cosProd x := by
  have hx1 : ∀ j, |x j| ≤ 1 := fun j =>
    abs_le_one_of_sq_le_one (by have := sq_le_sumSq x j; linarith)
  have hanonneg : ∀ j : Fin n, 0 ≤ 1 - Real.cos (x j / 2) := fun j => by
    linarith [Real.cos_le_one (x j / 2)]
  have hale : ∀ j : Fin n, 1 - Real.cos (x j / 2) ≤ 1 := fun j => by
    linarith [cos_half_pos (x j) (hx1 j)]
  set S : ℝ := ∑ j, (1 - Real.cos (x j / 2)) with hS
  have hlow : 1 - S ≤ cosProd x := by
    rw [cosProd_eq_prod_one_sub x hx1, hS]
    exact one_sub_sum_le_prod_one_sub _ _ (fun j _ => hanonneg j) fun j _ => hale j
  have hdev := abs_sum_one_sub_cos_sub n x hx1
  have h4 : ∑ j, (x j) ^ 4 ≤ 64 * δ ^ 2 := by
    have := sum_pow_four_le_sq_sumSq x
    nlinarith [sumSq_nonneg x]
  have hSle : S ≤ sumSq x / 8 + (∑ j, (x j) ^ 4) / 100 := by
    have := abs_le.1 hdev
    linarith [this.2]
  have h4nn : (0:ℝ) ≤ ∑ j, (x j) ^ 4 := Finset.sum_nonneg fun j _ => by positivity
  nlinarith [hlow, hSle, h4, hsum]

/-- **Necessary direction.**  A configuration with a large cosine product has small
quadratic energy. -/
theorem sumSq_le_of_one_sub_le_cosProd {n : ℕ} (x : Fin n → ℝ) (hx : ∀ j, |x j| ≤ 1) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ * (n + 1) ≤ 1 / 4) (h : 1 - δ ≤ cosProd x) :
    sumSq x ≤ 8 * δ + (8 + 7 * n) * δ ^ 2 := by
  have hδ4 : δ ≤ 1 / 4 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hδn : δ * n ≤ 1 / 4 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  -- each factor is large
  have hfac : ∀ j, 1 - δ ≤ Real.cos (x j / 2) := by
    intro j
    have h1 := cosProd_le_factor x j
    have h2 : |Real.cos (x j / 2)| = Real.cos (x j / 2) :=
      abs_of_pos (cos_half_pos (x j) (hx j))
    rw [h2] at h1
    linarith
  -- hence each coordinate is small
  have hsq : ∀ j, (x j) ^ 2 ≤ 9 * δ := by
    intro j
    have hb := abs_one_sub_cos_half_sub (x j) (hx j)
    have hb2 := (abs_le.1 hb).1
    have hx2 : (x j) ^ 2 ≤ 1 := by
      have habs := hx j
      nlinarith [sq_abs (x j), abs_nonneg (x j)]
    have h4 : (x j) ^ 4 ≤ (x j) ^ 2 := by
      have h44 : (x j) ^ 4 = (x j) ^ 2 * (x j) ^ 2 := by ring
      rw [h44]
      nlinarith [sq_nonneg (x j)]
    have := hfac j
    nlinarith
  have hsumSq : sumSq x ≤ 9 * δ * n := by
    rw [sumSq]
    calc ∑ j, (x j) ^ 2 ≤ ∑ _j : Fin n, (9 * δ) := Finset.sum_le_sum fun j _ => hsq j
      _ = 9 * δ * n := by simp [mul_comm]
  have h4sum : ∑ j, (x j) ^ 4 ≤ 9 * δ * sumSq x := by
    rw [sumSq, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have := hsq j
    nlinarith [sq_nonneg (x j)]
  have h4nn : (0:ℝ) ≤ ∑ j, (x j) ^ 4 := Finset.sum_nonneg fun j _ => by positivity
  have hsumSqnn := sumSq_nonneg x
  -- the sum of the deviations
  have hanonneg : ∀ j : Fin n, 0 ≤ 1 - Real.cos (x j / 2) := fun j => by
    linarith [Real.cos_le_one (x j / 2)]
  have hale : ∀ j : Fin n, 1 - Real.cos (x j / 2) ≤ 1 := fun j => by
    linarith [cos_half_pos (x j) (hx j)]
  set S : ℝ := ∑ j, (1 - Real.cos (x j / 2)) with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun j _ => hanonneg j
  have hdev := abs_le.1 (abs_sum_one_sub_cos_sub n x hx)
  have hSlow : sumSq x / 8 - (∑ j, (x j) ^ 4) / 100 ≤ S := by linarith [hdev.1]
  have hSup : S ≤ sumSq x / 8 + (∑ j, (x j) ^ 4) / 100 := by linarith [hdev.2]
  -- a priori smallness of `S`
  have hSsmall : S ≤ 1 / 2 := by nlinarith
  -- the product upper bound
  have hupper : cosProd x ≤ 1 - S + S ^ 2 / 2 := by
    rw [cosProd_eq_prod_one_sub x hx, hS]
    exact prod_one_sub_le _ _ (fun j _ => hanonneg j) fun j _ => hale j
  have hkey : S - S ^ 2 / 2 ≤ δ := by linarith
  have hS43 : S ≤ 4 * δ / 3 := by nlinarith
  have hSfin : S ≤ δ + δ ^ 2 := by nlinarith
  nlinarith [hSlow, hSfin, h4sum, hsumSq]


/-! ## The sandwich in terms of `Dₙ` and the quadratic energy -/

/-- `quadDev θ = ∑_j (θ_j - θ̄)²`, the quadratic energy of the configuration. -/
noncomputable def quadDev {n : ℕ} (θ : Fin n → ℝ) : ℝ := ∑ j, (θ j - (∑ i, θ i) / n) ^ 2

theorem quadDev_nonneg {n : ℕ} (θ : Fin n → ℝ) : 0 ≤ quadDev θ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem quadDev_le_sumSq_sub {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (c : ℝ) :
    quadDev θ ≤ sumSq (fun j => c - θ j) := by
  have h := sum_sq_sub_mean_le hn θ c
  refine h.trans (le_of_eq ?_)
  rw [sumSq]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cosProd_sub_int_mul_two_pi {n : ℕ} (x : Fin n → ℝ) (k : ℤ) :
    cosProd (fun j => x j - 2 * π * k) = cosProd x := by
  refine Finset.prod_congr rfl fun j _ => ?_
  have : (x j - 2 * π * k) / 2 = x j / 2 - k * π := by ring
  rw [this, Real.cos_sub_int_mul_pi, abs_mul]
  simp

/-- **Sufficient direction for `Dₙ`.** -/
theorem two_pow_mul_le_chordMax {n : ℕ} (θ : Fin n → ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 8) (hQ : quadDev θ ≤ 8 * δ) :
    2 ^ n * (1 - δ - δ ^ 2) ≤ chordMax θ := by
  set c : ℝ := (∑ i, θ i) / n with hc
  have hsum : sumSq (fun j => c - θ j) ≤ 8 * δ := by
    have : sumSq (fun j => c - θ j) = quadDev θ := by
      rw [sumSq, quadDev]
      exact Finset.sum_congr rfl fun j _ => by rw [hc]; ring
    rw [this]; exact hQ
  have hcp := one_sub_le_cosProd (fun j => c - θ j) δ hδ0 hδ hsum
  have := two_pow_mul_cosProd_le_chordMax θ c
  have h2 : (0:ℝ) < 2 ^ n := by positivity
  nlinarith

/-- **Necessary direction for `Dₙ`.**  A clustered configuration whose maximal chord product
is within `δ` of the extreme value `2ⁿ` has quadratic energy at most `8δ + Cₙδ²`. -/
theorem quadDev_le_of_chordMax_ge {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (hcl : ∀ j, |θ j - θ ⟨0, hn⟩| ≤ 1) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ * (n + 1) ≤ 1 / 4)
    (hδ' : δ ≤ 1 / 50) (h : 2 ^ n * (1 - δ) ≤ chordMax θ) :
    quadDev θ ≤ 8 * δ + (8 + 7 * n) * δ ^ 2 := by
  have hpi := Real.pi_pos
  have hpi3 : 3 < π := Real.pi_gt_three
  have hpi4 : π ≤ 4 := Real.pi_le_four
  have h2 : (0:ℝ) < 2 ^ n := by positivity
  obtain ⟨t, ht⟩ := exists_chordProd_eq_chordMax θ
  set s : ℝ := t - π with hs
  have hts : t = s + π := by rw [hs]; ring
  rw [hts, chordProd_add_pi θ s] at ht
  have hcos : 1 - δ ≤ cosProd (fun j => s - θ j) := by
    rw [← ht] at h
    exact le_of_mul_le_mul_left h h2
  -- the small radius
  set ρ : ℝ := π * Real.sqrt (2 * δ) with hρ
  have hsqrt : Real.sqrt (2 * δ) ≤ 1 / 5 := by
    have h1 : 2 * δ ≤ (1 / 5 : ℝ) ^ 2 := by nlinarith
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by norm_num)] at this
  have hρle : ρ ≤ 4 / 5 := by
    rw [hρ]
    nlinarith [Real.sqrt_nonneg (2 * δ)]
  have hρnn : 0 ≤ ρ := by rw [hρ]; positivity
  -- each coordinate is close to a multiple of `2π`
  have hk : ∀ j, ∃ k : ℤ, |(s - θ j) - 2 * π * k| ≤ ρ := by
    intro j
    refine exists_int_dist_le_of_abs_cos_ge (s - θ j) δ hδ0 (by linarith) ?_
    have := cosProd_le_factor (fun j => s - θ j) j
    simp only at this
    linarith
  choose k hkspec using hk
  -- all these multiples agree
  have hkeq : ∀ j, k j = k ⟨0, hn⟩ := by
    intro j
    by_contra hne
    have h1 := hkspec j
    have h0 := hkspec ⟨0, hn⟩
    have hcl' := hcl j
    have hdiff : |2 * π * ((k j : ℝ) - (k ⟨0, hn⟩ : ℝ))| ≤ 2 * ρ + 1 := by
      have hexp : 2 * π * ((k j : ℝ) - (k ⟨0, hn⟩ : ℝ))
          = ((s - θ ⟨0, hn⟩) - 2 * π * (k ⟨0, hn⟩ : ℝ)) - ((s - θ j) - 2 * π * (k j : ℝ))
            + (θ ⟨0, hn⟩ - θ j) := by ring
      rw [hexp]
      have a1 := abs_le.1 h1
      have a0 := abs_le.1 h0
      have a2 := abs_le.1 hcl'
      rw [abs_le]
      constructor
      · linarith [a1.1, a1.2, a0.1, a0.2, a2.1, a2.2]
      · linarith [a1.1, a1.2, a0.1, a0.2, a2.1, a2.2]
    have hone : (1:ℝ) ≤ |(k j : ℝ) - (k ⟨0, hn⟩ : ℝ)| := by
      have : ((k j : ℝ) - (k ⟨0, hn⟩ : ℝ)) = ((k j - k ⟨0, hn⟩ : ℤ) : ℝ) := by push_cast; ring
      rw [this, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (sub_ne_zero.2 hne)
    rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * π)] at hdiff
    nlinarith
  -- pass to the common representative
  set K : ℤ := k ⟨0, hn⟩ with hK
  set x : Fin n → ℝ := fun j => (s - θ j) - 2 * π * K with hx
  have hxabs : ∀ j, |x j| ≤ 1 := by
    intro j
    have := hkspec j
    rw [hkeq j] at this
    calc |x j| ≤ ρ := this
      _ ≤ 1 := by linarith
  have hcosx : cosProd x = cosProd (fun j => s - θ j) := cosProd_sub_int_mul_two_pi _ K
  have hcosx' : 1 - δ ≤ cosProd x := by rw [hcosx]; exact hcos
  have hsumSq := sumSq_le_of_one_sub_le_cosProd x hxabs δ hδ0 hδ hcosx'
  have hquad : quadDev θ ≤ sumSq x := by
    have := quadDev_le_sumSq_sub hn θ (s - 2 * π * K)
    refine this.trans (le_of_eq ?_)
    rw [sumSq, sumSq]
    exact Finset.sum_congr rfl fun j _ => by rw [hx]; ring
  linarith

end Q788
