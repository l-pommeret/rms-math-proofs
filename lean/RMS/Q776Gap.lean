import RMS.Q776Multi

/-!
# Q776 — the dominant saddles and the off-saddle exponential gap

The real part of the torus phase at `r = R e^{iπ/m}` is `R * gfun m θ` with

`gfun m θ = ∑_j cos (θ_j + π/m) + cos (π/m - ∑_j θ_j)`.

We prove:

* `Q776.cos_lt_tangent` : a strict tangent line bound for `cos`;
* `Q776.cos_sum_lt` : the strict form of the extremal lemma `Q776.cos_sum_le` for `m ≥ 3`;
* `Q776.gfun_le` : `gfun m θ ≤ m cos (π/m)` (the extremal lemma in torus coordinates);
* `Q776.gfun_eq_max_iff` : for `m ≥ 3`, inside the cube `[-π,π]^{m-1}` equality holds
  *exactly* at the two dominant saddles `θ = 0` and `θ = (-2π/m, …, -2π/m)`;
* `Q776.offSaddle_gap` : consequently, off fixed neighbourhoods of the two saddles the
  phase is bounded away from the maximum, uniformly.
-/

open scoped Real Nat
open Complex MeasureTheory

namespace Q776

/-- Strict form of `Q776.mul_cos_le_sin`. -/
theorem mul_cos_lt_sin {p : ℝ} (hp0 : 0 < p) (hp : p < π / 2) :
    p * Real.cos p < Real.sin p := by
  have ht := Real.lt_tan hp0 hp
  have hc : 0 < Real.cos p := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hp⟩
  rw [Real.tan_eq_sin_div_cos] at ht
  have h3 : p * Real.cos p < Real.sin p / Real.cos p * Real.cos p :=
    mul_lt_mul_of_pos_right ht hc
  rwa [div_mul_cancel₀ _ (ne_of_gt hc)] at h3

/-- Strict tangent line bound: for `0 < a < π/2` the graph of `cos` lies *strictly* below its
tangent line at `a` on `(-∞, π - a]`, except at `u = a`. -/
theorem cos_lt_tangent {a u : ℝ} (ha0 : 0 < a) (ha : a < π / 2) (hu : u ≤ π - a)
    (hne : u ≠ a) : Real.cos u < Real.cos a - Real.sin a * (u - a) := by
  have hpi := Real.pi_pos
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith)
  have hca : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, ha⟩
  set p : ℝ := (u - a) / 2 with hpdef
  have h2p : u - a = 2 * p := by rw [hpdef]; ring
  have hpne : p ≠ 0 := by
    simp only [hpdef]
    intro h
    apply hne
    have : u - a = 0 := by linarith [h]
    linarith
  have hid : Real.cos a - Real.cos u = 2 * Real.sin (p + a) * Real.sin p := by
    have h := Real.cos_sub_cos a u
    have h1 : (a + u) / 2 = p + a := by rw [hpdef]; ring
    have h2 : (a - u) / 2 = -p := by rw [hpdef]; ring
    rw [h1, h2, Real.sin_neg] at h
    linarith
  have hkey : Real.sin a * (2 * p) < 2 * Real.sin (p + a) * Real.sin p := by
    rcases lt_or_gt_of_ne hpne with hp | hp
    · -- `p < 0` : use `sin x < x` for `x > 0`
      have hs : Real.sin (2*(-p)) < 2*(-p) := Real.sin_lt (by linarith)
      have hexp : 2 * Real.sin (p + a) * Real.sin p - Real.sin a * (2 * p)
          = Real.sin a * (2*(-p) - Real.sin (2*(-p))) + 2 * Real.cos a * (Real.sin (-p))^2 := by
        rw [Real.sin_add, Real.sin_two_mul, Real.sin_neg, Real.cos_neg]
        ring
      nlinarith [mul_pos hsa (by linarith : (0:ℝ) < 2*(-p) - Real.sin (2*(-p))),
        mul_nonneg hca.le (sq_nonneg (Real.sin (-p)))]
    · -- `0 < p ≤ π/2 - a`
      have hp2 : p ≤ π / 2 - a := by rw [hpdef]; linarith
      have hcap : 0 ≤ Real.cos (a + p) := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      rw [Real.cos_add] at hcap
      have hsp : 0 < Real.sin p := Real.sin_pos_of_pos_of_lt_pi hp (by linarith)
      have hmc : p * Real.cos p < Real.sin p := mul_cos_lt_sin hp (by linarith)
      have hs2 : Real.sin p * Real.cos p ≤ p := by
        have := Real.sin_le (x := 2 * p) (by linarith)
        rw [Real.sin_two_mul] at this; linarith
      have hpy := Real.sin_sq_add_cos_sq p
      set X : ℝ := 2 * (Real.sin p * Real.cos a + Real.cos p * Real.sin a) * Real.sin p
        - Real.sin a * (2 * p) with hX
      have h1 : 0 < 2 * (Real.cos a * (Real.sin p - p * Real.cos p)) := by
        have := mul_pos hca (sub_pos.2 hmc); linarith
      have h2 : 0 ≤ 2 * ((Real.cos a * Real.cos p - Real.sin a * Real.sin p) *
          (p - Real.sin p * Real.cos p)) := by
        have := mul_nonneg hcap (sub_nonneg.2 hs2); linarith
      have heq : Real.sin p * X = 2 * (Real.cos a * (Real.sin p - p * Real.cos p)) +
          2 * ((Real.cos a * Real.cos p - Real.sin a * Real.sin p) *
            (p - Real.sin p * Real.cos p)) := by
        rw [hX]; linear_combination (2 * Real.cos a * Real.sin p) * hpy
      have hmain : 0 < Real.sin p * X := by rw [heq]; linarith
      have hXpos : 0 < X := by nlinarith
      rw [hX] at hXpos
      rw [Real.sin_add]
      linarith
  rw [h2p]
  linarith


theorem cos_lt_tangent' {a u : ℝ} (ha0 : 0 < a) (ha : a < π / 2) (hu : -(π - a) ≤ u)
    (hne : u ≠ -a) : Real.cos u < Real.cos a + Real.sin a * (u + a) := by
  have := cos_lt_tangent (a := a) (u := -u) ha0 ha (by linarith)
    (by intro h; exact hne (by linarith))
  rw [Real.cos_neg] at this; linarith

/-- The boundary case `m = 3` of the strict extremal lemma, when one angle is far out. -/
theorem cos_sum_three_lt {u : Fin 3 → ℝ} (hu : ∀ j, |u j| ≤ π) {K : ℤ}
    (hK : ∑ j, u j = π + 2*π*K) {j0 : Fin 3} (hj0 : Real.cos (u j0) ≤ -(1/2)) :
    ∑ j, Real.cos (u j) < 3 * (1/2) := by
  have hpi := Real.pi_pos
  have hle : ∀ j, Real.cos (u j) ≤ 1 := fun j => Real.cos_le_one _
  have hzero : ∀ j, Real.cos (u j) = 1 → u j = 0 := by
    intro j h
    have h1 := abs_le.1 (hu j)
    exact (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) (by linarith)).1 h
  have hpm : ∀ j, u j = π + 2*π*K → Real.cos (u j) = -1 := by
    intro j h
    rw [h, show π + 2*π*(K:ℝ) = π + (K:ℝ)*(2*π) by ring, Real.cos_add_int_mul_two_pi, Real.cos_pi]
  rw [Fin.sum_univ_three] at hK ⊢
  have e0 := hle 0; have e1 := hle 1; have e2 := hle 2
  by_contra hcon
  push_neg at hcon
  fin_cases j0
  · have hj0 : Real.cos (u 0) ≤ -(1/2) := hj0
    have z1 : u 1 = 0 := hzero 1 (by linarith)
    have z2 : u 2 = 0 := hzero 2 (by linarith)
    have : Real.cos (u 0) = -1 := hpm 0 (by rw [z1, z2] at hK; linarith)
    rw [z1, z2, this] at hcon
    simp at hcon
    linarith
  · have hj0 : Real.cos (u 1) ≤ -(1/2) := hj0
    have z1 : u 0 = 0 := hzero 0 (by linarith)
    have z2 : u 2 = 0 := hzero 2 (by linarith)
    have : Real.cos (u 1) = -1 := hpm 1 (by rw [z1, z2] at hK; linarith)
    rw [z1, z2, this] at hcon
    simp at hcon
    linarith
  · have hj0 : Real.cos (u 2) ≤ -(1/2) := hj0
    have z1 : u 0 = 0 := hzero 0 (by linarith)
    have z2 : u 1 = 0 := hzero 1 (by linarith)
    have : Real.cos (u 2) = -1 := hpm 2 (by rw [z1, z2] at hK; linarith)
    rw [z1, z2, this] at hcon
    simp at hcon
    linarith

theorem sub_one_lt_cos_pi_div {M : ℕ} (hM : 4 ≤ M) :
    (M : ℝ) - 1 < ((M : ℝ) + 1) * Real.cos (π / M) := by
  have hpi0 := Real.pi_pos
  have hM4 : (4:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hb := Real.one_sub_sq_div_two_le_cos (x := π / (M:ℝ))
  have hsq : (π / (M:ℝ)) ^ 2 = π ^ 2 / (M:ℝ) ^ 2 := by field_simp
  rw [hsq] at hb
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hpi2 : π ^ 2 < 9.9225 := by nlinarith
  have h1 : ((M:ℝ) + 1) * (1 - π ^ 2 / (M:ℝ) ^ 2 / 2) ≤ ((M:ℝ) + 1) * Real.cos (π / (M:ℝ)) :=
    mul_le_mul_of_nonneg_left hb (by linarith)
  have hkey : 0 < 4 * (M:ℝ) ^ 2 - π ^ 2 * ((M:ℝ) + 1) := by nlinarith
  have heq : ((M:ℝ) + 1) * (1 - π ^ 2 / (M:ℝ) ^ 2 / 2) - ((M:ℝ) - 1)
      = (4 * (M:ℝ) ^ 2 - π ^ 2 * ((M:ℝ) + 1)) / (2 * (M:ℝ) ^ 2) := by field_simp; ring
  have := div_pos hkey (by positivity : (0:ℝ) < 2 * (M:ℝ) ^ 2)
  linarith

/-- **Strict extremal lemma.**  For `m ≥ 3`, if `∑ u j ≡ π (mod 2π)`, `|u j| ≤ π`, and the
angles are not all equal to `π/m` nor all equal to `-π/m`, then the bound of
`Q776.cos_sum_le` is strict. -/
theorem cos_sum_lt {m : ℕ} (hm : 3 ≤ m) {u : Fin m → ℝ} (hu : ∀ j, |u j| ≤ π)
    {K : ℤ} (hK : ∑ j, u j = π + 2 * π * K)
    (hn1 : ¬ (∀ j, u j = π / m)) (hn2 : ¬ (∀ j, u j = -(π / m))) :
    ∑ j, Real.cos (u j) < m * Real.cos (π / m) := by
  have hpi := Real.pi_pos
  have hmR : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  set a : ℝ := π / m with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha3 : a ≤ π / 3 := by
    rw [ha]; exact div_le_div_of_nonneg_left hpi.le (by norm_num) hmR
  have ha2 : a < π / 2 := by linarith
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith)
  have hca : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, ha2⟩
  have hma : (m:ℝ) * a = π := by rw [ha]; field_simp
  by_cases hbad : ∃ j, Real.cos (u j) ≤ -Real.cos a
  · obtain ⟨j0, hj0⟩ := hbad
    rcases eq_or_lt_of_le hm with hm3 | hm4
    · -- `m = 3` : the crude bound is not strict, an exact analysis is needed
      subst hm3
      have hacos : Real.cos a = 1/2 := by
        rw [ha]; norm_num [Real.cos_pi_div_three]
      rw [hacos] at hj0 ⊢
      have := cos_sum_three_lt hu hK (j0 := j0) (by linarith)
      push_cast
      linarith
    · -- `m ≥ 4` : the crude bound is strict
      have hm4' : 4 ≤ m := by exact_mod_cast hm4
      have hnum := sub_one_lt_cos_pi_div hm4'
      rw [← ha] at hnum
      have h1 := Finset.add_sum_erase Finset.univ (fun j => Real.cos (u j)) (Finset.mem_univ j0)
      have h2 : ∑ j ∈ Finset.univ.erase j0, Real.cos (u j)
          ≤ (Finset.univ.erase j0).card • (1:ℝ) :=
        Finset.sum_le_card_nsmul _ _ _ (fun j _ => Real.cos_le_one _)
      have h3 : (Finset.univ.erase j0).card = m - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ, Fintype.card_fin]
      rw [h3] at h2
      simp only [nsmul_eq_mul, mul_one] at h2
      have h4 : ((m - 1 : ℕ) : ℝ) = (m:ℝ) - 1 := by
        have h5 : 1 ≤ m := by omega
        push_cast [Nat.cast_sub h5]
        ring
      rw [h4] at h2
      linarith
  · push_neg at hbad
    have hrange : ∀ j, |u j| < π - a := by
      intro j
      by_contra hcon
      push_neg at hcon
      have h1 : Real.cos |u j| ≤ Real.cos (π - a) :=
        Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (hu j) hcon
      rw [Real.cos_abs, Real.cos_pi_sub] at h1
      exact absurd h1 (not_le.2 (hbad j))
    rcases le_or_gt 0 K with hK0 | hK0
    · push_neg at hn1
      obtain ⟨j1, hj1⟩ := hn1
      have hterm : ∀ j ∈ Finset.univ,
          Real.cos (u j) ≤ Real.cos a - Real.sin a * (u j - a) := by
        intro j _
        exact cos_le_tangent ha0.le ha2.le (by linarith [(abs_lt.1 (hrange j)).2])
      have hs : ∑ j, Real.cos (u j) < ∑ j, (Real.cos a - Real.sin a * (u j - a)) := by
        refine Finset.sum_lt_sum hterm ⟨j1, Finset.mem_univ j1, ?_⟩
        exact cos_lt_tangent ha0 ha2 (by linarith [(abs_lt.1 (hrange j1)).2]) hj1
      rw [sum_tangent u (Real.cos a) (Real.sin a) a, hK, hma] at hs
      have hKnn : (0:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK0
      nlinarith [mul_nonneg hsa.le hKnn]
    · push_neg at hn2
      obtain ⟨j2, hj2⟩ := hn2
      have hterm : ∀ j ∈ Finset.univ,
          Real.cos (u j) ≤ Real.cos a + Real.sin a * (u j + a) := by
        intro j _
        exact cos_le_tangent' ha0.le ha2.le (by linarith [(abs_lt.1 (hrange j)).1])
      have hs : ∑ j, Real.cos (u j) < ∑ j, (Real.cos a + Real.sin a * (u j + a)) := by
        refine Finset.sum_lt_sum hterm ⟨j2, Finset.mem_univ j2, ?_⟩
        exact cos_lt_tangent' ha0 ha2 (by linarith [(abs_lt.1 (hrange j2)).1]) hj2
      rw [sum_tangent' u (Real.cos a) (Real.sin a) a, hK, hma] at hs
      have hKle' : K ≤ -1 := by omega
      have hKle : (K:ℝ) ≤ -1 := by exact_mod_cast hKle'
      nlinarith [mul_nonneg hsa.le (by linarith : (0:ℝ) ≤ -1 - (K:ℝ))]

/-- Reduction of a family of angles modulo `2π` into `[-π, π]`. -/
theorem exists_reduction {m : ℕ} (u : Fin m → ℝ) {K : ℤ} (hK : ∑ j, u j = π + 2*π*K) :
    ∃ (w : Fin m → ℝ) (L : ℤ), (∀ j, |w j| ≤ π) ∧ (∀ j, Real.cos (w j) = Real.cos (u j)) ∧
      (∀ j, ∃ k : ℤ, u j = w j + 2*π*k) ∧ ∑ j, w j = π + 2*π*L := by
  have hpi := Real.pi_pos
  have h2pi : (0:ℝ) < 2*π := by linarith
  set w : Fin m → ℝ := fun j => toIocMod h2pi (-π) (u j) with hw
  set k : Fin m → ℤ := fun j => toIocDiv h2pi (-π) (u j) with hk
  have hkey : ∀ j, w j = u j - (k j : ℝ) * (2*π) := by
    intro j
    have := toIocMod_sub_self h2pi (-π) (u j)
    simp only [hw, hk] at this ⊢
    rw [zsmul_eq_mul] at this
    push_cast at this ⊢
    linarith
  refine ⟨w, K - ∑ j, k j, ?_, ?_, ?_, ?_⟩
  · intro j
    have h := toIocMod_mem_Ioc h2pi (-π) (u j)
    simp only [Set.mem_Ioc] at h
    rw [abs_le]
    constructor
    · linarith [h.1]
    · linarith [h.2]
  · intro j
    rw [hkey j, show u j - (k j : ℝ) * (2*π) = u j + ((-(k j) : ℤ) : ℝ) * (2*π) by push_cast; ring,
      Real.cos_add_int_mul_two_pi]
  · intro j
    exact ⟨k j, by rw [hkey j]; ring⟩
  · have : ∑ j, w j = (∑ j, u j) - (∑ j, (k j : ℝ)) * (2*π) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => hkey j
    rw [this, hK]
    push_cast
    ring

theorem cos_sum_le' {m : ℕ} (hm : 2 ≤ m) (u : Fin m → ℝ) {K : ℤ}
    (hK : ∑ j, u j = π + 2*π*K) :
    ∑ j, Real.cos (u j) ≤ m * Real.cos (π / m) := by
  obtain ⟨w, L, hw1, hw2, -, hw4⟩ := exists_reduction u hK
  have := cos_sum_le hm hw1 hw4
  calc ∑ j, Real.cos (u j) = ∑ j, Real.cos (w j) :=
        (Finset.sum_congr rfl fun j _ => hw2 j).symm
    _ ≤ m * Real.cos (π / m) := this

theorem cos_sum_lt' {m : ℕ} (hm : 3 ≤ m) (u : Fin m → ℝ) {K : ℤ}
    (hK : ∑ j, u j = π + 2*π*K)
    (hn1 : ¬ (∀ j, ∃ k : ℤ, u j = π/m + 2*π*k))
    (hn2 : ¬ (∀ j, ∃ k : ℤ, u j = -(π/m) + 2*π*k)) :
    ∑ j, Real.cos (u j) < m * Real.cos (π / m) := by
  obtain ⟨w, L, hw1, hw2, hw3, hw4⟩ := exists_reduction u hK
  have hg1 : ¬ (∀ j, w j = π/m) := by
    intro h
    refine hn1 fun j => ?_
    obtain ⟨kj, hkj⟩ := hw3 j
    exact ⟨kj, by rw [hkj, h j]⟩
  have hg2 : ¬ (∀ j, w j = -(π/m)) := by
    intro h
    refine hn2 fun j => ?_
    obtain ⟨kj, hkj⟩ := hw3 j
    exact ⟨kj, by rw [hkj, h j]⟩
  have := cos_sum_lt hm hw1 hw4 hg1 hg2
  calc ∑ j, Real.cos (u j) = ∑ j, Real.cos (w j) :=
        (Finset.sum_congr rfl fun j _ => hw2 j).symm
    _ < m * Real.cos (π / m) := this

/-! ## The torus coordinates -/

/-- The `(d+1)`-tuple of angles of the torus representation at the dominant saddle
direction: `(θ_0 + α, …, θ_{d-1} + α, α - ∑ θ_j)`.  Their sum is exactly `π`. -/
noncomputable def angles {d : ℕ} (θ : Fin d → ℝ) : Fin (d+1) → ℝ :=
  Fin.snoc (fun j => θ j + alpha (d+1)) (alpha (d+1) - coordSum θ)

theorem angles_castSucc {d : ℕ} (θ : Fin d → ℝ) (j : Fin d) :
    angles θ j.castSucc = θ j + alpha (d+1) := by
  simp [angles]

theorem angles_last {d : ℕ} (θ : Fin d → ℝ) :
    angles θ (Fin.last d) = alpha (d+1) - coordSum θ := by
  simp [angles]

theorem sum_angles {d : ℕ} (θ : Fin d → ℝ) : ∑ j, angles θ j = π + 2*π*((0:ℤ) : ℝ) := by
  have hma : ((d:ℝ)+1) * alpha (d+1) = π := by
    rw [alpha]; push_cast; field_simp
  rw [Fin.sum_univ_castSucc]
  simp only [angles_castSucc, angles_last]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [coordSum]
  push_cast
  linarith [hma]

theorem cos_sum_angles {d : ℕ} (θ : Fin d → ℝ) :
    ∑ j, Real.cos (angles θ j) = gfun (d+1) θ := by
  rw [Fin.sum_univ_castSucc, gfun]
  simp only [angles_castSucc, angles_last]

/-- The extremal bound in torus coordinates. -/
theorem gfun_le {d : ℕ} (hd : 1 ≤ d) (θ : Fin d → ℝ) :
    gfun (d+1) θ ≤ (d+1) * Real.cos (alpha (d+1)) := by
  have := cos_sum_le' (m := d+1) (by omega) (angles θ) (sum_angles θ)
  rw [cos_sum_angles] at this
  rw [alpha]
  push_cast at this ⊢
  exact this

/-- **Classification of the dominant saddles.**  For `d ≥ 2`, inside the cube the maximum of
`gfun` is attained exactly at `θ = 0` and at `θ = (-2π/m, …, -2π/m)`. -/
theorem gfun_eq_max_iff {d : ℕ} (hd : 2 ≤ d) {θ : Fin d → ℝ} (hθ : θ ∈ cube d)
    (h : gfun (d+1) θ = (d+1) * Real.cos (alpha (d+1))) :
    (∀ j, θ j = 0) ∨ (∀ j, θ j = -(2 * alpha (d+1))) := by
  have hpi := Real.pi_pos
  have ha0 : 0 < alpha (d+1) := alpha_pos (by omega)
  have ha3 : alpha (d+1) ≤ π/3 := alpha_le_pi_div_three (by omega)
  have hbd : ∀ j, |θ j| ≤ π := by
    intro j
    have := hθ j (Set.mem_univ j)
    simp only [Set.mem_Icc] at this
    rw [abs_le]
    exact ⟨this.1, this.2⟩
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.1 hcon
  have hlt := cos_sum_lt' (m := d+1) (by omega) (angles θ) (sum_angles θ) ?_ ?_
  · rw [cos_sum_angles, h, alpha] at hlt
    push_cast at hlt
    linarith
  · -- not all angles congruent to `+α`
    intro hall
    refine h1 fun j => ?_
    obtain ⟨k, hk⟩ := hall j.castSucc
    rw [angles_castSucc] at hk
    have halpha : (π / ((d:ℝ)+1)) = alpha (d+1) := by rw [alpha]; push_cast; ring
    push_cast at hk
    rw [halpha] at hk
    have hθk : θ j = 2*π*(k:ℝ) := by linarith
    have hb := abs_le.1 (hbd j)
    rw [hθk] at hb
    have hk1 : (k:ℝ) < 1 := by nlinarith [hb.2]
    have hk2 : (-1:ℝ) < (k:ℝ) := by nlinarith [hb.1]
    have : k < 1 := by exact_mod_cast hk1
    have : (-1:ℤ) < k := by exact_mod_cast hk2
    have hk0 : k = 0 := by omega
    rw [hθk, hk0]
    simp
  · -- not all angles congruent to `-α`
    intro hall
    refine h2 fun j => ?_
    obtain ⟨k, hk⟩ := hall j.castSucc
    rw [angles_castSucc] at hk
    have halpha : (π / ((d:ℝ)+1)) = alpha (d+1) := by rw [alpha]; push_cast; ring
    push_cast at hk
    rw [halpha] at hk
    have hθk : θ j = -(2 * alpha (d+1)) + 2*π*(k:ℝ) := by linarith
    have hb := abs_le.1 (hbd j)
    rw [hθk] at hb
    have hk1 : (k:ℝ) < 1 := by nlinarith [hb.2]
    have hk2 : (-1:ℝ) < (k:ℝ) := by nlinarith [hb.1]
    have : k < 1 := by exact_mod_cast hk1
    have : (-1:ℤ) < k := by exact_mod_cast hk2
    have hk0 : k = 0 := by omega
    rw [hθk, hk0]
    simp

theorem continuous_gfun {m d : ℕ} : Continuous (fun θ : Fin d → ℝ => gfun m θ) := by
  unfold gfun coordSum
  fun_prop

/-- **The off-saddle gap.**  Away from the two dominant saddles the phase is bounded away
from its maximum. -/
theorem offSaddle_gap {d : ℕ} (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ θ ∈ cube d, (∃ j, δ ≤ |θ j|) → (∃ j, δ ≤ |θ j + 2 * alpha (d+1)|) →
      gfun (d+1) θ ≤ (d+1) * Real.cos (alpha (d+1)) - η := by
  classical
  set A : Set (Fin d → ℝ) := {θ | ∃ j, δ ≤ |θ j|} with hA
  set B : Set (Fin d → ℝ) := {θ | ∃ j, δ ≤ |θ j + 2 * alpha (d+1)|} with hB
  have hAclosed : IsClosed A := by
    have : A = ⋃ j : Fin d, {θ : Fin d → ℝ | δ ≤ |θ j|} := by
      ext θ; simp [hA]
    rw [this]
    exact isClosed_iUnion_of_finite fun j =>
      isClosed_le continuous_const ((continuous_apply j).abs)
  have hBclosed : IsClosed B := by
    have : B = ⋃ j : Fin d, {θ : Fin d → ℝ | δ ≤ |θ j + 2 * alpha (d+1)|} := by
      ext θ; simp [hB]
    rw [this]
    exact isClosed_iUnion_of_finite fun j =>
      isClosed_le continuous_const (((continuous_apply j).add continuous_const).abs)
  set S : Set (Fin d → ℝ) := (cube d ∩ A) ∩ B with hS
  have hcube : IsCompact (cube d) := isCompact_univ_pi fun _ => isCompact_Icc
  have hScomp : IsCompact S :=
    (hcube.inter_right hAclosed).inter_right hBclosed
  rcases S.eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, fun θ hθ hθA hθB => ?_⟩
    exact absurd (show θ ∈ S from ⟨⟨hθ, hθA⟩, hθB⟩) (by rw [hemp]; simp)
  · obtain ⟨θ0, hθ0S, hmax⟩ :=
      hScomp.exists_isMaxOn hne (continuous_gfun (m := d+1)).continuousOn
    have hlt : gfun (d+1) θ0 < (d+1) * Real.cos (alpha (d+1)) := by
      rcases lt_or_eq_of_le (gfun_le (d := d) (by omega) θ0) with h | h
      · exact h
      · exfalso
        rcases gfun_eq_max_iff hd hθ0S.1.1 h with hz | hz
        · obtain ⟨j, hj⟩ := hθ0S.1.2
          rw [hz j] at hj
          simp at hj
          linarith
        · obtain ⟨j, hj⟩ := hθ0S.2
          rw [hz j] at hj
          simp at hj
          linarith
    refine ⟨(d+1) * Real.cos (alpha (d+1)) - gfun (d+1) θ0, by linarith, fun θ hθ hθA hθB => ?_⟩
    have := hmax (show θ ∈ S from ⟨⟨hθ, hθA⟩, hθB⟩)
    simp only [Set.mem_setOf_eq] at this
    linarith

end Q776
