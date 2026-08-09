import Mathlib

/-!
# Q776

For a fixed integer `m ≥ 2` let

  `f m x = ∑' n, x ^ n / (n !) ^ m`.

Q776 asks for the behaviour of `f m` as `x → -∞`.  The answer is an additive Poincaré
expansion whose leading term oscillates,

  `f m (-R^m) = A m R * (cos (Ψ m R) + O (1/R))`,
  `A m R = 2 (2π)^{(1-m)/2} m^{-1/2} R^{-(m-1)/2} e^{m R cos (π/m)}`,
  `Ψ m R = m R sin (π/m) - (m-1)π/(2m)`.

## Scope of this formalization (mismatch with the printed statement)

The amplitude, phase and error term of that expansion come from a genuinely
`(m-1)`-dimensional saddle point (Laplace) analysis.  Mathlib provides no
multidimensional Laplace/stationary phase theorem with uniform remainders, so the
full asymptotic expansion is *not* formalized here.  What is formalized is the
kernel-checkable core of the published proof, with no `sorry`, no added axioms and
no unproved hypotheses:

* `hadamard` : an exact one-dimensional integral (Hadamard product) representation of
  `f (m+1)` in terms of `f m`; iterating it is exactly the torus representation
  `f m (r^m) = (2π)^{-(m-1)} ∫_{[-π,π]^{m-1}} e^{r S(θ)} dθ` used in the solution;
* `re_sum_le_of_prod_eq_neg_one` : the extremal ("saddle point") lemma, i.e. if
  `‖z j‖ = 1` for `j = 1, …, m` and `∏ z j = -1` then `Re (∑ z j) ≤ m cos (π/m)`,
  together with `saddle_attained`, the fact that the bound is attained at the
  dominant saddle `z j = e^{iπ/m}`;
* `envelope` : the resulting sharp exponential envelope
  `‖f m (r ^ m)‖ ≤ exp (m R cos α)` for `r = R e^{iα}`, `R ≥ 0`, `|α| ≤ π/m`.
  On the negative axis (`envelope_neg`, `envelope_neg_axis`) this reads
  `|f m x| ≤ exp (m (-x)^{1/m} cos (π/m))` for `x ≤ 0`, which is precisely the
  exponential factor of the answer to Q776 with the optimal constant; on the positive
  axis (`envelope_pos`) it reads `|f m t| ≤ exp (m t^{1/m})`;
* `f_two_neg` : for `m = 2`, the identity `f 2 (-R²) = J₀ (2R)` (mathlib has no Bessel
  functions, so `J₀` is defined here by Hansen's integral), and the consequence
  `abs_besselJ0_le_one`.

The oscillating factor `cos (Ψ m R)`, the algebraic prefactor `R^{-(m-1)/2}`, the
constant `2 (2π)^{(1-m)/2} m^{-1/2}` and the correction coefficient `(m²-1)/(24m)`
are therefore *not* claimed here.  No statement below asserts a global ratio
equivalence (which, as the source notes, is false because the leading term has
infinitely many zeros).

## Versions

Lean 4.28.0, mathlib at commit 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
-/

open scoped Real Nat
open Complex intervalIntegral MeasureTheory

namespace Q776

/-! ## Part 1 : elementary trigonometric inequalities -/

theorem mul_cos_le_sin {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ π / 2) :
    p * Real.cos p ≤ Real.sin p := by
  rcases eq_or_lt_of_le hp0 with h | h
  · simp [← h]
  rcases eq_or_lt_of_le hp with h2 | h2
  · rw [h2]; simp
  · have ht := Real.lt_tan h h2
    have hc : 0 < Real.cos p := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩
    rw [Real.tan_eq_sin_div_cos] at ht
    have h3 : p * Real.cos p < Real.sin p / Real.cos p * Real.cos p :=
      mul_lt_mul_of_pos_right ht hc
    rw [div_mul_cancel₀ _ (ne_of_gt hc)] at h3
    linarith

/-- The graph of `cos` lies below its tangent line at `a ∈ [0, π/2]` on the half line
`u ≤ π - a`. -/
theorem cos_le_tangent {a u : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ π / 2) (hu : u ≤ π - a) :
    Real.cos u ≤ Real.cos a - Real.sin a * (u - a) := by
  have hpi := Real.pi_pos
  have hsa : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi ha0 (by linarith)
  have hca : 0 ≤ Real.cos a := Real.cos_nonneg_of_mem_Icc ⟨by linarith, ha⟩
  set p : ℝ := (u - a) / 2 with hpdef
  have h2p : u - a = 2 * p := by rw [hpdef]; ring
  have hid : Real.cos a - Real.cos u = 2 * Real.sin (p + a) * Real.sin p := by
    have h := Real.cos_sub_cos a u
    have h1 : (a + u) / 2 = p + a := by rw [hpdef]; ring
    have h2 : (a - u) / 2 = -p := by rw [hpdef]; ring
    rw [h1, h2, Real.sin_neg] at h
    linarith
  have hkey : Real.sin a * (2 * p) ≤ 2 * Real.sin (p + a) * Real.sin p := by
    rw [Real.sin_add]
    rcases le_or_gt p 0 with hp | hp
    · have h1 : 2 * p ≤ Real.sin (2 * p) := by
        have := Real.sin_le (x := -(2 * p)) (by linarith)
        rw [Real.sin_neg] at this; linarith
      rw [Real.sin_two_mul] at h1
      nlinarith [mul_nonneg hca (sq_nonneg (Real.sin p))]
    · have hp2 : p ≤ π / 2 - a := by rw [hpdef]; linarith
      have hcap : 0 ≤ Real.cos (a + p) := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      rw [Real.cos_add] at hcap
      have hsp : 0 < Real.sin p := Real.sin_pos_of_pos_of_lt_pi hp (by linarith)
      have hmc : p * Real.cos p ≤ Real.sin p := mul_cos_le_sin (le_of_lt hp) (by linarith)
      have hs2 : Real.sin p * Real.cos p ≤ p := by
        have := Real.sin_le (x := 2 * p) (by linarith)
        rw [Real.sin_two_mul] at this; linarith
      have hpy := Real.sin_sq_add_cos_sq p
      set X : ℝ := 2 * (Real.sin p * Real.cos a + Real.cos p * Real.sin a) * Real.sin p
        - Real.sin a * (2 * p) with hX
      have h1 : 0 ≤ 2 * (Real.cos a * (Real.sin p - p * Real.cos p)) := by
        have := mul_nonneg hca (sub_nonneg.2 hmc); linarith
      have h2 : 0 ≤ 2 * ((Real.cos a * Real.cos p - Real.sin a * Real.sin p) *
          (p - Real.sin p * Real.cos p)) := by
        have := mul_nonneg hcap (sub_nonneg.2 hs2); linarith
      have heq : Real.sin p * X = 2 * (Real.cos a * (Real.sin p - p * Real.cos p)) +
          2 * ((Real.cos a * Real.cos p - Real.sin a * Real.sin p) *
            (p - Real.sin p * Real.cos p)) := by
        rw [hX]; linear_combination (2 * Real.cos a * Real.sin p) * hpy
      have hmain : 0 ≤ Real.sin p * X := by rw [heq]; linarith
      have hXnn : 0 ≤ X := nonneg_of_mul_nonneg_right hmain hsp
      rw [hX] at hXnn; linarith
  rw [h2p]
  linarith

/-- Symmetric form of `cos_le_tangent`: the tangent line at `-a`. -/
theorem cos_le_tangent' {a u : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ π / 2) (hu : -(π - a) ≤ u) :
    Real.cos u ≤ Real.cos a + Real.sin a * (u + a) := by
  have := cos_le_tangent (a := a) (u := -u) ha0 ha (by linarith)
  rw [Real.cos_neg] at this; linarith

/-- The numerical inequality `M - 1 ≤ (M + 1) cos (π / M)` for `M ≥ 3`
(with equality for `M = 3`). -/
theorem sub_one_le_cos_pi_div {M : ℕ} (hM : 3 ≤ M) :
    (M : ℝ) - 1 ≤ ((M : ℝ) + 1) * Real.cos (π / M) := by
  have hpi0 := Real.pi_pos
  rcases eq_or_lt_of_le hM with h | h
  · rw [← h]
    norm_num [Real.cos_pi_div_three]
  · have hM4 : (4:ℝ) ≤ (M:ℝ) := by exact_mod_cast h
    have hMpos : (0:ℝ) < (M:ℝ) := by linarith
    have hb := Real.one_sub_sq_div_two_le_cos (x := π / (M:ℝ))
    have hsq : (π / (M:ℝ)) ^ 2 = π ^ 2 / (M:ℝ) ^ 2 := by field_simp
    rw [hsq] at hb
    have hpi : π < 3.15 := Real.pi_lt_d2
    have hpi2 : π ^ 2 < 9.9225 := by nlinarith
    have h1 : ((M:ℝ) + 1) * (1 - π ^ 2 / (M:ℝ) ^ 2 / 2) ≤ ((M:ℝ) + 1) * Real.cos (π / (M:ℝ)) :=
      mul_le_mul_of_nonneg_left hb (by linarith)
    have hkey : 0 ≤ 4 * (M:ℝ) ^ 2 - π ^ 2 * ((M:ℝ) + 1) := by nlinarith
    have heq : ((M:ℝ) + 1) * (1 - π ^ 2 / (M:ℝ) ^ 2 / 2) - ((M:ℝ) - 1)
        = (4 * (M:ℝ) ^ 2 - π ^ 2 * ((M:ℝ) + 1)) / (2 * (M:ℝ) ^ 2) := by field_simp; ring
    have := div_nonneg hkey (by positivity : (0:ℝ) ≤ 2 * (M:ℝ) ^ 2)
    linarith

/-- The extremal inequality behind the saddle point analysis, for `a ≥ 0`. -/
theorem key_ineq_nonneg {m : ℕ} (hm : 1 ≤ m) {a θ : ℝ} (ha0 : 0 ≤ a)
    (ha : a ≤ π / ((m : ℝ) + 1)) (hθ : |θ| ≤ π) :
    (m : ℝ) * Real.cos (θ / m) + Real.cos (((m : ℝ) + 1) * a - θ)
      ≤ ((m : ℝ) + 1) * Real.cos a := by
  have hpi := Real.pi_pos
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hMpos : (0:ℝ) < (m:ℝ) + 1 := by linarith
  have haMpi : ((m:ℝ) + 1) * a ≤ π := by rw [← le_div_iff₀' hMpos]; exact ha
  have hθabs := abs_le.1 hθ
  rcases eq_or_lt_of_le hmR with hm1 | hm2
  · -- the case `m = 1`
    have ha2 : a ≤ π / 2 := by rw [← hm1] at ha; linarith
    have hca : 0 ≤ Real.cos a := Real.cos_nonneg_of_mem_Icc ⟨by linarith, ha2⟩
    have hsum : Real.cos θ + Real.cos (2 * a - θ) = 2 * Real.cos a * Real.cos (θ - a) := by
      rw [Real.cos_add_cos]; ring_nf
    rw [← hm1]
    simp only [one_mul, div_one]
    have h2 : (1:ℝ) + 1 = 2 := by norm_num
    rw [h2, hsum]
    nlinarith [Real.cos_le_one (θ - a), hca]
  · -- the case `m ≥ 2`
    have hm2' : 2 ≤ m := by exact_mod_cast hm2
    have hmR2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm2'
    have ha3 : a ≤ π / 3 := by
      have : π / ((m:ℝ) + 1) ≤ π / 3 :=
        div_le_div_of_nonneg_left (le_of_lt hpi) (by norm_num) (by linarith)
      linarith
    have ha2 : a ≤ π / 2 := by linarith
    have hca : 0 ≤ Real.cos a := Real.cos_nonneg_of_mem_Icc ⟨by linarith, ha2⟩
    have hsa : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi ha0 (by linarith)
    have h0m : (0:ℝ) < (m:ℝ) := by linarith
    have habs : |θ / (m:ℝ)| ≤ π / 2 := by
      rw [abs_div, abs_of_nonneg (le_of_lt h0m), div_le_div_iff₀ h0m (by norm_num)]
      nlinarith [abs_le.1 hθ, abs_nonneg θ]
    obtain ⟨hθm2, hθm1⟩ := abs_le.1 habs
    set v : ℝ := ((m:ℝ) + 1) * a - θ with hv
    rcases le_or_gt v (π - a) with hA | hB
    · have t1 : Real.cos (θ / m) ≤ Real.cos a - Real.sin a * (θ / m - a) :=
        cos_le_tangent ha0 ha2 (by linarith)
      have t2 : Real.cos v ≤ Real.cos a - Real.sin a * (v - a) := cos_le_tangent ha0 ha2 hA
      have t1' : (m:ℝ) * Real.cos (θ / m) ≤ (m:ℝ) * (Real.cos a - Real.sin a * (θ / m - a)) :=
        mul_le_mul_of_nonneg_left t1 (by linarith)
      have hmul : (m:ℝ) * (θ / m) = θ := by field_simp
      nlinarith [t1', t2, hmul]
    · rcases le_or_gt (Real.cos v) (-Real.cos a) with hB1 | hB2
      · -- the crude bound suffices
        have hcosa_ge : Real.cos (π / ((m:ℝ) + 1)) ≤ Real.cos a :=
          Real.cos_le_cos_of_nonneg_of_le_pi ha0 (by rw [div_le_iff₀ hMpos]; nlinarith) ha
        have hnum := sub_one_le_cos_pi_div (M := m + 1) (by omega)
        have hcast : ((m + 1 : ℕ) : ℝ) = (m:ℝ) + 1 := by push_cast; ring
        rw [hcast] at hnum
        have hkey : (m:ℝ) ≤ ((m:ℝ) + 2) * Real.cos a := by
          nlinarith [mul_le_mul_of_nonneg_left hcosa_ge (by linarith : (0:ℝ) ≤ (m:ℝ) + 2)]
        nlinarith [Real.cos_le_one (θ / m)]
      · -- here `v > π + a`, and we use the tangent line at `-a`
        have hcosv : Real.cos v = -Real.cos (v - π) := by
          have hvv : v = v - π + π := by ring
          rw [hvv, Real.cos_add]
          simp
        have hvgt : π + a < v := by
          by_contra hcon
          push_neg at hcon
          have hcw : Real.cos a ≤ Real.cos (v - π) := by
            rcases le_or_gt 0 (v - π) with h3 | h3
            · exact Real.cos_le_cos_of_nonneg_of_le_pi h3 (by linarith) (by linarith)
            · rw [← Real.cos_neg (v - π)]
              exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
          rw [hcosv] at hB2
          linarith
        have hvle : v ≤ 2 * π := by rw [hv]; linarith
        have hv' : -(π - a) ≤ v - 2 * π := by linarith
        have t1 : Real.cos (θ / m) ≤ Real.cos a + Real.sin a * (θ / m + a) :=
          cos_le_tangent' ha0 ha2 (by linarith)
        have t2 : Real.cos (v - 2 * π) ≤ Real.cos a + Real.sin a * (v - 2 * π + a) :=
          cos_le_tangent' ha0 ha2 hv'
        have hcv : Real.cos (v - 2 * π) = Real.cos v := by rw [Real.cos_sub_two_pi]
        have t1' : (m:ℝ) * Real.cos (θ / m) ≤ (m:ℝ) * (Real.cos a + Real.sin a * (θ / m + a)) :=
          mul_le_mul_of_nonneg_left t1 (by linarith)
        have hmul : (m:ℝ) * (θ / m) = θ := by field_simp
        rw [hcv] at t2
        nlinarith [t1', t2, hmul,
          mul_nonneg hsa (by linarith : (0:ℝ) ≤ 2 * π - 2 * (((m:ℝ) + 1) * a))]

/-- The extremal inequality behind the saddle point analysis. -/
theorem key_ineq {m : ℕ} (hm : 1 ≤ m) {a θ : ℝ} (ha : |a| ≤ π / ((m : ℝ) + 1)) (hθ : |θ| ≤ π) :
    (m : ℝ) * Real.cos (θ / m) + Real.cos (((m : ℝ) + 1) * a - θ)
      ≤ ((m : ℝ) + 1) * Real.cos a := by
  obtain ⟨ha1, ha2⟩ := abs_le.1 ha
  rcases le_or_gt 0 a with h | h
  · exact key_ineq_nonneg hm h ha2 hθ
  · have := key_ineq_nonneg (a := -a) (θ := -θ) hm (by linarith) (by linarith)
      (by rwa [abs_neg])
    rw [Real.cos_neg a] at this
    have e1 : -θ / (m:ℝ) = -(θ / m) := by ring
    have e2 : ((m:ℝ) + 1) * -a - -θ = -(((m:ℝ) + 1) * a - θ) := by ring
    rw [e1, e2, Real.cos_neg, Real.cos_neg] at this
    exact this

/-! ## Part 2 : the function `f m` and its integral representation -/

/-- `f m x = ∑ x ^ n / (n !) ^ m`. -/
noncomputable def f (m : ℕ) (x : ℂ) : ℂ := ∑' n : ℕ, x ^ n / (n ! : ℂ) ^ m

theorem summable_term {m : ℕ} (hm : 1 ≤ m) (x : ℂ) :
    Summable fun n : ℕ => x ^ n / (n ! : ℂ) ^ m := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => ‖x‖ ^ n / n !)
  · exact Real.summable_pow_div_factorial ‖x‖
  · intro n
    rw [norm_div, norm_pow, norm_pow, Complex.norm_natCast]
    have h1 : (1:ℝ) ≤ (n ! : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n)
    have h2 : (n ! : ℝ) ≤ (n ! : ℝ) ^ m := by
      calc (n ! : ℝ) = (n ! : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (n ! : ℝ) ^ m := pow_le_pow_right₀ h1 hm
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) h2

theorem f_one (x : ℂ) : f 1 x = Complex.exp x := by
  rw [f, Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  simp

theorem f_zero {m : ℕ} : f m 0 = 1 := by
  rw [f, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

theorem cexp_tsum (z : ℂ) : Complex.exp z = ∑' n : ℕ, z ^ n / n ! := by
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

theorem integral_exp_int (d : ℤ) :
    (∫ θ in (-π)..π, Complex.exp ((d:ℂ) * θ * I)) = if d = 0 then (2 * π : ℂ) else 0 := by
  by_cases hd : d = 0
  · subst hd; simp; ring
  · rw [if_neg hd]
    have hc : ((d:ℂ) * I) ≠ 0 := by simp [hd, Complex.I_ne_zero]
    have hcong : (∫ θ in (-π)..π, Complex.exp ((d:ℂ) * θ * I))
        = ∫ θ in (-π)..π, Complex.exp ((d:ℂ) * I * θ) := by
      apply intervalIntegral.integral_congr
      intro x _
      ring_nf
    rw [hcong, integral_exp_mul_complex hc]
    have h1 : Complex.exp ((d:ℂ) * I * (π:ℂ)) = Complex.exp ((d:ℂ) * I * ((-π : ℝ):ℂ)) := by
      have h2 : (d:ℂ) * I * (π:ℂ) = (d:ℂ) * I * ((-π:ℝ):ℂ) + (d:ℂ) * (2 * π * I) := by
        push_cast; ring
      rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
      ring
    rw [h1]
    simp

/-- The `n`-th Fourier coefficient of `θ ↦ exp (w e^{-iθ})` is `w ^ n / n !`. -/
theorem integral_exp_fourier (n : ℕ) (w : ℂ) :
    (∫ θ in (-π)..π, Complex.exp ((n:ℂ) * θ * I) * Complex.exp (w * Complex.exp (-(θ * I))))
      = 2 * π * (w ^ n / n !) := by
  have hpi := Real.pi_pos
  set F : ℕ → ℝ → ℂ := fun k θ => w ^ k / k ! * Complex.exp ((((n:ℤ) - k : ℤ) : ℂ) * θ * I)
    with hFdef
  have hnorm : ∀ (k : ℕ) (θ : ℝ), ‖F k θ‖ = ‖w‖ ^ k / k ! := by
    intro k θ
    rw [hFdef]
    simp only
    rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_exp]
    have h0 : ((((n:ℤ) - k : ℤ) : ℂ) * θ * I).re = 0 := by simp
    rw [h0]
    simp
  have hcont : ∀ k : ℕ, Continuous (F k) := by
    intro k; rw [hFdef]; fun_prop
  have hint : ∀ k : ℕ, Integrable (F k) (volume.restrict (Set.Ioc (-π) π)) :=
    fun k => (hcont k).integrableOn_Ioc
  have hIk : ∀ k : ℕ, (∫ θ in Set.Ioc (-π) π, F k θ)
      = w ^ k / k ! * (if ((n:ℤ) - k) = 0 then (2 * π : ℂ) else 0) := by
    intro k
    rw [← intervalIntegral.integral_of_le (by linarith : (-π:ℝ) ≤ π), hFdef]
    simp only
    rw [intervalIntegral.integral_const_mul, integral_exp_int]
  have hsum : Summable fun k : ℕ => ∫ θ in Set.Ioc (-π) π, ‖F k θ‖ := by
    have heq : ∀ k : ℕ, (∫ θ in Set.Ioc (-π) π, ‖F k θ‖) = 2 * π * (‖w‖ ^ k / k !) := by
      intro k
      simp only [hnorm k]
      rw [setIntegral_const, MeasureTheory.Measure.real, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
      ring
    rw [funext heq]
    exact (Real.summable_pow_div_factorial ‖w‖).mul_left _
  rw [intervalIntegral.integral_of_le (by linarith : (-π:ℝ) ≤ π)]
  have hpt : ∀ θ : ℝ, Complex.exp ((n:ℂ) * θ * I) * Complex.exp (w * Complex.exp (-(θ * I)))
      = ∑' k : ℕ, F k θ := by
    intro θ
    rw [cexp_tsum (w * Complex.exp (-(θ * I))), ← tsum_mul_left]
    congr 1
    funext k
    rw [hFdef]
    simp only
    rw [mul_pow, ← Complex.exp_nat_mul]
    have h1 : Complex.exp ((n:ℂ) * θ * I) * (w ^ k * Complex.exp ((k:ℂ) * -(θ * I)) / k !)
        = w ^ k / k ! * (Complex.exp ((n:ℂ) * θ * I) * Complex.exp ((k:ℂ) * -(θ * I))) := by
      ring
    rw [h1, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hpt]
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm hint hsum, tsum_eq_single n]
  · rw [hIk n]
    simp
    ring
  · intro k hk
    rw [hIk k, if_neg (by omega), mul_zero]

theorem summable_real_term {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun n : ℕ => t ^ n / (n ! : ℝ) ^ m := by
  have hle : ∀ n : ℕ, t ^ n / (n ! : ℝ) ^ m ≤ t ^ n / n ! := by
    intro n
    have h1 : (1:ℝ) ≤ (n ! : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n)
    have h2 : (n ! : ℝ) ≤ (n ! : ℝ) ^ m := by
      calc (n ! : ℝ) = (n ! : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (n ! : ℝ) ^ m := pow_le_pow_right₀ h1 hm
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) h2
  exact Summable.of_nonneg_of_le (fun n => by positivity) hle
    (Real.summable_pow_div_factorial t)

/-- **Hadamard product representation.**  An exact one dimensional integral formula
expressing `f (m+1)` in terms of `f m`; iterating it produces the torus
representation of `f m` used in the solution of Q776. -/
theorem hadamard {m : ℕ} (hm : 1 ≤ m) {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    (∫ θ in (-π)..π, f m ((ρ:ℂ) * Complex.exp (θ * I)) *
        Complex.exp (z / ρ * Complex.exp (-(θ * I)))) = 2 * π * f (m + 1) z := by
  have hpi := Real.pi_pos
  have hle2 : (-π:ℝ) ≤ π := by linarith
  set w : ℂ := z / ρ with hw
  set G : ℕ → ℝ → ℂ := fun n θ => ((ρ:ℂ) ^ n / (n ! : ℂ) ^ m) *
    (Complex.exp ((n:ℂ) * θ * I) * Complex.exp (w * Complex.exp (-(θ * I)))) with hG
  have hcont : ∀ n : ℕ, Continuous (G n) := by
    intro n; rw [hG]; fun_prop
  have hint : ∀ n : ℕ, Integrable (G n) (volume.restrict (Set.Ioc (-π) π)) :=
    fun n => (hcont n).integrableOn_Ioc
  have hnormle : ∀ (n : ℕ) (θ : ℝ), ‖G n θ‖ ≤ Real.exp ‖w‖ * (ρ ^ n / (n ! : ℝ) ^ m) := by
    intro n θ
    rw [hG]
    simp only
    rw [norm_mul, norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, Complex.norm_exp]
    have h0 : ((n:ℂ) * θ * I).re = 0 := by simp
    rw [h0, Real.exp_zero, one_mul, abs_of_pos hρ]
    have hre : (w * Complex.exp (-(θ * I))).re ≤ ‖w‖ := by
      calc (w * Complex.exp (-(θ * I))).re ≤ ‖w * Complex.exp (-(θ * I))‖ := Complex.re_le_norm _
        _ = ‖w‖ := by
            rw [norm_mul, Complex.norm_exp]
            have h1 : (-((θ:ℂ) * I)).re = 0 := by simp
            rw [h1]; simp
    have hmono := Real.exp_le_exp.2 hre
    have hpos : (0:ℝ) ≤ ρ ^ n / (n ! : ℝ) ^ m := by positivity
    calc ρ ^ n / (n ! : ℝ) ^ m * Real.exp ((w * Complex.exp (-(θ * I))).re)
        ≤ ρ ^ n / (n ! : ℝ) ^ m * Real.exp ‖w‖ := mul_le_mul_of_nonneg_left hmono hpos
      _ = Real.exp ‖w‖ * (ρ ^ n / (n ! : ℝ) ^ m) := by ring
  have hsum : Summable fun n : ℕ => ∫ θ in Set.Ioc (-π) π, ‖G n θ‖ := by
    have hnn : ∀ n : ℕ, 0 ≤ ∫ θ in Set.Ioc (-π) π, ‖G n θ‖ :=
      fun n => setIntegral_nonneg measurableSet_Ioc (fun θ _ => norm_nonneg _)
    have hle : ∀ n : ℕ, (∫ θ in Set.Ioc (-π) π, ‖G n θ‖)
        ≤ 2 * π * (Real.exp ‖w‖ * (ρ ^ n / (n ! : ℝ) ^ m)) := by
      intro n
      calc (∫ θ in Set.Ioc (-π) π, ‖G n θ‖)
          ≤ ∫ _θ in Set.Ioc (-π) π, Real.exp ‖w‖ * (ρ ^ n / (n ! : ℝ) ^ m) := by
            apply setIntegral_mono_on ((hint n).norm)
              (integrableOn_const (by simp [Real.volume_Ioc])) measurableSet_Ioc
            intro θ _
            exact hnormle n θ
        _ = 2 * π * (Real.exp ‖w‖ * (ρ ^ n / (n ! : ℝ) ^ m)) := by
            rw [setIntegral_const, MeasureTheory.Measure.real, Real.volume_Ioc,
              ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
            ring
    exact Summable.of_nonneg_of_le hnn hle
      (((summable_real_term hm (le_of_lt hρ)).mul_left _).mul_left _)
  have hpt : ∀ θ : ℝ, f m ((ρ:ℂ) * Complex.exp (θ * I)) *
      Complex.exp (w * Complex.exp (-(θ * I))) = ∑' n : ℕ, G n θ := by
    intro θ
    rw [f, ← tsum_mul_right]
    congr 1
    funext n
    rw [hG]
    simp only
    rw [mul_pow, ← Complex.exp_nat_mul]
    have h1 : (n:ℂ) * ((θ:ℂ) * I) = (n:ℂ) * (θ:ℂ) * I := by ring
    rw [h1]
    ring
  have hIn : ∀ n : ℕ, (∫ θ in Set.Ioc (-π) π, G n θ)
      = ((ρ:ℂ) ^ n / (n ! : ℂ) ^ m) * (2 * π * (w ^ n / n !)) := by
    intro n
    rw [← intervalIntegral.integral_of_le hle2, hG]
    simp only
    rw [intervalIntegral.integral_const_mul, integral_exp_fourier]
  rw [intervalIntegral.integral_of_le hle2]
  simp_rw [hpt]
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [hIn]
  rw [f, ← tsum_mul_left]
  congr 1
  funext n
  have hρ0 : (ρ:ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hρ
  have hn0 : (n ! : ℂ) ≠ 0 := by simp [Nat.factorial_ne_zero]
  rw [hw, div_pow, pow_succ]
  field_simp

/-! ## Part 3 : the exponential envelope -/

theorem polar_pow (R α : ℝ) (k : ℕ) :
    ((R:ℂ) * Complex.exp ((α:ℂ) * I)) ^ k
      = ((R ^ k : ℝ) : ℂ) * Complex.exp ((((k : ℝ) * α : ℝ)) * I) := by
  rw [mul_pow, ← Complex.exp_nat_mul]; push_cast; ring_nf

theorem polar_re (R β : ℝ) : ((R:ℂ) * Complex.exp ((β:ℂ) * I)).re = R * Real.cos β := by
  rw [Complex.exp_mul_I]
  simp [Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem polar_div (R θ α : ℝ) (m : ℕ) (hR : 0 < R) :
    ((R:ℂ) * Complex.exp ((α:ℂ) * I)) ^ (m+1) / ((R^m : ℝ) : ℂ) * Complex.exp (-((θ:ℂ) * I))
      = (R : ℂ) * Complex.exp (((((m:ℝ)+1) * α - θ : ℝ)) * I) := by
  rw [polar_pow]
  have hR0 : ((R ^ m : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
  rw [div_mul_eq_mul_div, div_eq_iff hR0, mul_assoc, ← Complex.exp_add]
  have hexp : ((((m+1 : ℕ):ℝ) * α : ℝ) : ℂ) * I + -((θ:ℂ) * I)
      = ((((m:ℝ)+1) * α - θ : ℝ) : ℂ) * I := by push_cast; ring
  rw [hexp]; push_cast; ring

/-- **The sharp exponential envelope.**  For `r = R e^{iα}` with `R ≥ 0` and `|α| ≤ π/m`,
`‖f m (r ^ m)‖ ≤ exp (m R cos α)`.  This is the exponential factor of the asymptotic
expansion of Q776, with the optimal constant, and it is proved by iterating the
Hadamard representation together with the extremal (saddle point) inequality. -/
theorem envelope {m : ℕ} (hm : 1 ≤ m) : ∀ {R α : ℝ}, 0 ≤ R → |α| ≤ π / m →
    ‖f m (((R:ℂ) * Complex.exp ((α:ℂ) * I)) ^ m)‖ ≤ Real.exp (m * R * Real.cos α) := by
  have hpi := Real.pi_pos
  induction m, hm using Nat.le_induction with
  | base =>
      intro R α _ _
      rw [pow_one, f_one, Complex.norm_exp, polar_re]
      simp
  | succ m hm IH =>
      intro R α hR hα
      have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      rcases eq_or_lt_of_le hR with hR0 | hRpos
      · rw [← hR0, show ((0:ℝ):ℂ) * Complex.exp ((α:ℂ) * I) = 0 by simp,
          zero_pow (by omega), f_zero]
        simp
      · set ρ : ℝ := R ^ m with hρdef
        have hρ : 0 < ρ := by positivity
        set z : ℂ := ((R:ℂ) * Complex.exp ((α:ℂ) * I)) ^ (m+1) with hz
        have hh := hadamard hm hρ z
        have hbound : ∀ θ ∈ Set.uIoc (-π) π,
            ‖f m ((ρ:ℂ) * Complex.exp (θ * I)) * Complex.exp (z / ρ * Complex.exp (-(θ * I)))‖
              ≤ Real.exp (((m:ℝ) + 1) * R * Real.cos α) := by
          intro θ hθ
          have hθabs : |θ| ≤ π := by
            rw [Set.uIoc_of_le (by linarith : (-π:ℝ) ≤ π)] at hθ
            exact abs_le.2 ⟨le_of_lt hθ.1, hθ.2⟩
          have hmth : ((m:ℝ) * (θ / m)) = θ := by field_simp
          have h1 : ((ρ:ℂ) * Complex.exp ((θ:ℂ) * I))
              = ((R:ℂ) * Complex.exp (((θ / m : ℝ)) * I)) ^ m := by
            rw [polar_pow, hmth, hρdef]
          have hIH := IH (R := R) (α := θ / m) hR (by
            rw [abs_div, abs_of_nonneg (by linarith : (0:ℝ) ≤ (m:ℝ))]
            exact div_le_div_of_nonneg_right hθabs (by linarith))
          rw [← h1] at hIH
          have h2 : z / (ρ:ℂ) * Complex.exp (-((θ:ℂ) * I))
              = (R : ℂ) * Complex.exp (((((m:ℝ)+1) * α - θ : ℝ)) * I) := by
            rw [hz, hρdef]
            exact polar_div R θ α m hRpos
          rw [norm_mul, h2, Complex.norm_exp, polar_re]
          have hkey := key_ineq hm (a := α) (θ := θ) (by
            have hc : ((m+1 : ℕ):ℝ) = (m:ℝ) + 1 := by push_cast; ring
            rwa [hc] at hα) hθabs
          have hmul : Real.exp ((m:ℝ) * R * Real.cos (θ / m)) *
              Real.exp (R * Real.cos (((m:ℝ)+1) * α - θ))
              ≤ Real.exp (((m:ℝ)+1) * R * Real.cos α) := by
            rw [← Real.exp_add]
            exact Real.exp_le_exp.2 (by nlinarith [hkey, hR])
          calc ‖f m ((ρ:ℂ) * Complex.exp ((θ:ℂ) * I))‖ *
                Real.exp (R * Real.cos (((m:ℝ)+1) * α - θ))
              ≤ Real.exp ((m:ℝ) * R * Real.cos (θ / m)) *
                Real.exp (R * Real.cos (((m:ℝ)+1) * α - θ)) :=
                mul_le_mul_of_nonneg_right hIH (le_of_lt (Real.exp_pos _))
            _ ≤ Real.exp (((m:ℝ)+1) * R * Real.cos α) := hmul
        have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbound
        rw [hh] at hI
        have h2pi : |π - -π| = 2 * π := by
          rw [abs_of_nonneg (by linarith)]; ring
        rw [h2pi, norm_mul] at hI
        have hnn : ‖(2 * (π:ℂ))‖ = 2 * π := by
          simp [Complex.norm_real, abs_of_nonneg (le_of_lt hpi)]
        rw [hnn] at hI
        have hfin : ‖f (m+1) z‖ ≤ Real.exp (((m:ℝ)+1) * R * Real.cos α) := by
          nlinarith [hI, norm_nonneg (f (m+1) z)]
        rw [hz] at hfin
        convert hfin using 3
        push_cast
        ring

/-- The envelope on the negative real axis: this is exactly the exponential factor
`exp (m t^{1/m} cos (π/m))` of the asymptotic expansion of Q776. -/
theorem envelope_neg {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 ≤ t) :
    ‖f m (-(t:ℂ))‖ ≤ Real.exp (m * t ^ ((m:ℝ)⁻¹) * Real.cos (π / m)) := by
  have hm0 : m ≠ 0 := by omega
  set R : ℝ := t ^ ((m:ℝ)⁻¹) with hR
  have hRnn : 0 ≤ R := Real.rpow_nonneg ht _
  have hRm : R ^ m = t := Real.rpow_inv_natCast_pow ht hm0
  have harg : ((R:ℂ) * Complex.exp (((π / m : ℝ)) * I)) ^ m = -(t:ℂ) := by
    rw [polar_pow, hRm]
    have h1 : ((m:ℝ) * (π / m) : ℝ) = π := by
      have : (m:ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm0
      field_simp
    rw [h1]
    have h2 : Complex.exp (((π:ℝ):ℂ) * I) = -1 := Complex.exp_pi_mul_I
    rw [h2]
    ring
  have hmain := envelope hm (R := R) (α := π / m) hRnn (by
    rw [abs_of_nonneg (by positivity)])
  rwa [harg] at hmain

/-- Reformulation of `envelope_neg` for `x ≤ 0`. -/
theorem envelope_neg_axis {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : x ≤ 0) :
    ‖f m (x:ℂ)‖ ≤ Real.exp (m * (-x) ^ ((m:ℝ)⁻¹) * Real.cos (π / m)) := by
  have h := envelope_neg hm (t := -x) (by linarith)
  rwa [show (-((-x : ℝ) : ℂ)) = (x:ℂ) by push_cast; ring] at h

/-- The envelope on the positive real axis: `exp (m t^{1/m})`, matching the growth
`f m t ∼ c t^{(1-m)/(2m)} e^{m t^{1/m}}` recorded in the statement of Q776. -/
theorem envelope_pos {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 ≤ t) :
    ‖f m (t:ℂ)‖ ≤ Real.exp (m * t ^ ((m:ℝ)⁻¹)) := by
  have hm0 : m ≠ 0 := by omega
  set R : ℝ := t ^ ((m:ℝ)⁻¹) with hR
  have hRnn : 0 ≤ R := Real.rpow_nonneg ht _
  have hRm : R ^ m = t := Real.rpow_inv_natCast_pow ht hm0
  have harg : ((R:ℂ) * Complex.exp (((0 : ℝ)) * I)) ^ m = (t:ℂ) := by
    rw [polar_pow, hRm]; simp
  have hmain := envelope hm (R := R) (α := 0) hRnn (by
    simp
    positivity)
  rw [harg] at hmain
  simpa using hmain

/-! ## Part 4 : the case `m = 2` is the Bessel function `J₀` -/

theorem integral_odd_eq_zero {g : ℝ → ℝ} (hodd : ∀ x, g (-x) = -g x) (a : ℝ) :
    (∫ x in (-a)..a, g x) = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -a) (b := a) g
  simp only [neg_neg] at h
  have h2 : (∫ x in (-a)..a, g (-x)) = -∫ x in (-a)..a, g x := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr (fun x _ => hodd x)
  rw [h2] at h
  linarith

theorem integral_cexp_real_mul_I (y : ℝ) :
    (∫ θ in (-π)..π, Complex.exp (((y * Real.sin θ : ℝ)) * I))
      = ((∫ θ in (-π)..π, Real.cos (y * Real.sin θ) : ℝ) : ℂ) := by
  have hpt : ∀ θ : ℝ, Complex.exp (((y * Real.sin θ : ℝ)) * I)
      = ((Real.cos (y * Real.sin θ) : ℝ) : ℂ) + ((Real.sin (y * Real.sin θ) : ℝ) : ℂ) * I := by
    intro θ
    rw [Complex.exp_mul_I]
    norm_cast
  rw [intervalIntegral.integral_congr (g := fun θ => ((Real.cos (y * Real.sin θ) : ℝ) : ℂ)
      + ((Real.sin (y * Real.sin θ) : ℝ) : ℂ) * I) (fun θ _ => hpt θ)]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_mul_const]
    have h0 : (∫ θ in (-π)..π, ((Real.sin (y * Real.sin θ) : ℝ) : ℂ)) = 0 := by
      rw [intervalIntegral.integral_ofReal]
      have hz : (∫ θ in (-π)..π, Real.sin (y * Real.sin θ)) = 0 := by
        apply integral_odd_eq_zero
        intro x
        rw [Real.sin_neg, mul_neg, Real.sin_neg]
      rw [hz]
      simp
    rw [h0, intervalIntegral.integral_ofReal]
    ring
  · apply Continuous.intervalIntegrable
    fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop

/-- The Bessel function `J₀` in Hansen's integral form. -/
noncomputable def besselJ0 (y : ℝ) : ℝ := 1 / (2 * π) * ∫ θ in (-π)..π, Real.cos (y * Real.sin θ)

theorem besselJ0_zero : besselJ0 0 = 1 := by
  rw [besselJ0]
  simp
  field_simp
  ring

/-- **The case `m = 2`.**  `f 2 (-R^2) = J₀ (2R)`. -/
theorem f_two_neg {R : ℝ} (hR : 0 ≤ R) : f 2 (-((R:ℂ)^2)) = ((besselJ0 (2 * R) : ℝ) : ℂ) := by
  have hpi := Real.pi_pos
  rcases eq_or_lt_of_le hR with h0 | hRpos
  · rw [← h0]
    simp [f_zero, besselJ0_zero]
  · have hR0 : (R:ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hRpos
    have hpt : ∀ θ : ℝ, f 1 ((R:ℂ) * Complex.exp ((θ:ℂ) * I)) *
        Complex.exp ((-((R:ℂ)^2)) / (R:ℂ) * Complex.exp (-((θ:ℂ) * I)))
        = Complex.exp (((2 * R * Real.sin θ : ℝ)) * I) := by
      intro θ
      rw [f_one, ← Complex.exp_add]
      congr 1
      have he1 : Complex.exp ((θ:ℂ) * I) = Complex.cos θ + Complex.sin θ * I :=
        Complex.exp_mul_I _
      have he2 : Complex.exp (-((θ:ℂ) * I)) = Complex.cos θ - Complex.sin θ * I := by
        rw [show -((θ:ℂ) * I) = ((-θ : ℂ)) * I by ring, Complex.exp_mul_I, Complex.cos_neg,
          Complex.sin_neg]
        ring
      have hs : Complex.sin (θ:ℂ) = ((Real.sin θ : ℝ) : ℂ) := by rw [Complex.ofReal_sin]
      rw [he1, he2, hs]
      field_simp
      push_cast
      ring
    have hh := hadamard (m := 1) le_rfl hRpos (-((R:ℂ)^2))
    rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), integral_cexp_real_mul_I] at hh
    have hf : f 2 (-((R:ℂ)^2)) = 1 / (2 * (π:ℂ)) *
        ((∫ θ in (-π)..π, Real.cos (2 * R * Real.sin θ) : ℝ) : ℂ) := by
      rw [hh]
      field_simp
    rw [hf, besselJ0]
    push_cast
    ring

/-- `|J₀ y| ≤ 1`: the case `m = 2` of the envelope (`cos (π/2) = 0`). -/
theorem abs_besselJ0_le_one {y : ℝ} (hy : 0 ≤ y) : |besselJ0 y| ≤ 1 := by
  set R : ℝ := y / 2 with hR
  have hR0 : 0 ≤ R := by rw [hR]; linarith
  have h1 : f 2 (-((R:ℂ)^2)) = ((besselJ0 y : ℝ) : ℂ) := by
    rw [f_two_neg hR0]
    congr 2
    rw [hR]; ring
  have h2 := envelope_neg (m := 2) (by norm_num) (t := R^2) (by positivity)
  have h3 : (((R^2 : ℝ)) : ℂ) = ((R:ℂ))^2 := by push_cast; ring
  rw [h3, h1] at h2
  have h4 : ((R^2 : ℝ)) ^ (((2:ℕ):ℝ))⁻¹ = R := by
    rw [show ((2:ℕ):ℝ) = (2:ℝ) by norm_num, ← Real.rpow_natCast R 2, ← Real.rpow_mul hR0]
    norm_num
  have h5 : Real.cos (π / ((2:ℕ):ℝ)) = 0 := by norm_num
  rw [h4, h5] at h2
  simpa using h2

/-! ## Part 5 : identification of the dominant saddle points -/

theorem sum_tangent {m : ℕ} (u : Fin m → ℝ) (c s a : ℝ) :
    ∑ j, (c - s * (u j - a)) = m * c - s * ((∑ j, u j) - m * a) := by
  have h1 : ∑ j, (u j - a) = (∑ j, u j) - m * a := by
    simp [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
  calc ∑ j, (c - s * (u j - a)) = (∑ _j : Fin m, c) - ∑ j, s * (u j - a) := by
        rw [Finset.sum_sub_distrib]
    _ = m * c - s * ∑ j, (u j - a) := by
        rw [← Finset.mul_sum]
        simp [Finset.sum_const, Finset.card_univ]
    _ = m * c - s * ((∑ j, u j) - m * a) := by rw [h1]

theorem sum_tangent' {m : ℕ} (u : Fin m → ℝ) (c s a : ℝ) :
    ∑ j, (c + s * (u j + a)) = m * c + s * ((∑ j, u j) + m * a) := by
  have h := sum_tangent u c (-s) (-a)
  simp only [sub_neg_eq_add, neg_mul, mul_neg] at h
  convert h using 2

/-- The extremal lemma in terms of angles: if `∑ u j ≡ π (mod 2π)` and each `|u j| ≤ π`,
then `∑ cos (u j) ≤ m cos (π/m)`. -/
theorem cos_sum_le {m : ℕ} (hm : 2 ≤ m) {u : Fin m → ℝ} (hu : ∀ j, |u j| ≤ π)
    {K : ℤ} (hK : ∑ j, u j = π + 2 * π * K) :
    ∑ j, Real.cos (u j) ≤ m * Real.cos (π / m) := by
  have hpi := Real.pi_pos
  have hmR : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  set a : ℝ := π / m with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha2 : a ≤ π / 2 := by
    rw [ha]; exact div_le_div_of_nonneg_left (le_of_lt hpi) (by norm_num) hmR
  have hsa : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt ha0) (by linarith)
  have hca : 0 ≤ Real.cos a := Real.cos_nonneg_of_mem_Icc ⟨by linarith, ha2⟩
  have hma : (m:ℝ) * a = π := by rw [ha]; field_simp
  rcases eq_or_lt_of_le hm with hm2 | hm3
  · -- `m = 2`: the bound is `0` and the sum vanishes identically
    subst hm2
    rw [Fin.sum_univ_two] at hK ⊢
    have hsum : Real.cos (u 0) + Real.cos (u 1)
        = 2 * Real.cos ((u 0 + u 1) / 2) * Real.cos ((u 0 - u 1) / 2) := by
      rw [Real.cos_add_cos]
    have hhalf : (u 0 + u 1) / 2 = π / 2 + π * K := by rw [hK]; ring
    have hc0 : Real.cos ((u 0 + u 1) / 2) = 0 := by
      rw [hhalf, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
      have hs : Real.sin (π * K) = 0 := by
        rw [mul_comm]; exact Real.sin_int_mul_pi K
      rw [hs]; ring
    rw [hsum, hc0]
    norm_num
    exact hca
  · -- `m ≥ 3`
    have hm3' : 3 ≤ m := by exact_mod_cast hm3
    have hnum := sub_one_le_cos_pi_div hm3'
    rw [← ha] at hnum
    by_cases hbad : ∃ j, Real.cos (u j) ≤ -Real.cos a
    · -- one angle is far out; the crude bound suffices
      obtain ⟨j0, hj0⟩ := hbad
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
    · -- all angles lie in the region where both tangent lines are valid
      push_neg at hbad
      have hrange : ∀ j, |u j| < π - a := by
        intro j
        by_contra hcon
        push_neg at hcon
        have h1 : Real.cos |u j| ≤ Real.cos (π - a) :=
          Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (hu j) hcon
        rw [Real.cos_abs, Real.cos_pi_sub] at h1
        exact absurd h1 (not_le.2 (hbad j))
      rcases le_or_gt 0 K with hK0 | hK0
      · have hterm : ∀ j ∈ Finset.univ,
            Real.cos (u j) ≤ Real.cos a - Real.sin a * (u j - a) := by
          intro j _
          exact cos_le_tangent (le_of_lt ha0) ha2 (by linarith [(abs_lt.1 (hrange j)).2])
        have hs := Finset.sum_le_sum hterm
        rw [sum_tangent u (Real.cos a) (Real.sin a) a, hK, hma] at hs
        have hKnn : (0:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK0
        nlinarith [mul_nonneg hsa hKnn]
      · have hterm : ∀ j ∈ Finset.univ,
            Real.cos (u j) ≤ Real.cos a + Real.sin a * (u j + a) := by
          intro j _
          exact cos_le_tangent' (le_of_lt ha0) ha2 (by linarith [(abs_lt.1 (hrange j)).1])
        have hs := Finset.sum_le_sum hterm
        rw [sum_tangent' u (Real.cos a) (Real.sin a) a, hK, hma] at hs
        have hKle' : K ≤ -1 := by omega
        have hKle : (K:ℝ) ≤ -1 := by exact_mod_cast hKle'
        nlinarith [mul_nonneg hsa (by linarith : (0:ℝ) ≤ -1 - (K:ℝ))]

/-- **The extremal (saddle point) lemma.**  If `z 1, …, z m` have modulus `1` and product
`-1`, then `Re (z 1 + ⋯ + z m) ≤ m cos (π/m)`. -/
theorem re_sum_le_of_prod_eq_neg_one {m : ℕ} (hm : 2 ≤ m) {z : Fin m → ℂ}
    (hz : ∀ j, ‖z j‖ = 1) (hprod : ∏ j, z j = -1) :
    (∑ j, z j).re ≤ m * Real.cos (π / m) := by
  have hzne : ∀ j, z j ≠ 0 := by
    intro j h
    have hj := hz j
    rw [h] at hj
    simp at hj
  set u : Fin m → ℝ := fun j => Complex.arg (z j) with hu
  have hzexp : ∀ j, z j = Complex.exp ((u j : ℂ) * I) := by
    intro j
    have h := Complex.norm_mul_exp_arg_mul_I (z j)
    rw [hz j] at h
    simpa using h.symm
  have huabs : ∀ j, |u j| ≤ π := fun j => Complex.abs_arg_le_pi (z j)
  have hre : ∀ j, (z j).re = Real.cos (u j) := by
    intro j
    have h := Complex.cos_arg (hzne j)
    rw [hz j] at h
    simpa using h.symm
  have hprodexp : Complex.exp (((∑ j, u j : ℝ) : ℂ) * I) = -1 := by
    rw [← hprod, Finset.prod_congr rfl (fun j _ => hzexp j), ← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  obtain ⟨K, hK⟩ : ∃ K : ℤ, (∑ j, u j) = π + 2 * π * K := by
    have h1 : Complex.exp (((∑ j, u j : ℝ) : ℂ) * I - (π:ℂ) * I) = 1 := by
      rw [Complex.exp_sub, hprodexp, Complex.exp_pi_mul_I]
      norm_num
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    refine ⟨n, ?_⟩
    have h2 := congrArg Complex.im hn
    simp [Complex.sub_im, Complex.mul_im] at h2
    linarith [h2]
  have hfin := cos_sum_le hm huabs hK
  rw [Complex.re_sum]
  calc ∑ j, (z j).re = ∑ j, Real.cos (u j) := Finset.sum_congr rfl (fun j _ => hre j)
    _ ≤ m * Real.cos (π / m) := hfin

/-- The bound of `re_sum_le_of_prod_eq_neg_one` is attained at the dominant saddle
`z j = e^{iπ/m}` (and, by conjugation, at `e^{-iπ/m}`). -/
theorem saddle_attained {m : ℕ} (hm : 1 ≤ m) :
    (∏ _j : Fin m, Complex.exp (((π / m : ℝ) : ℂ) * I)) = -1 ∧
      (∀ _j : Fin m, ‖Complex.exp (((π / m : ℝ) : ℂ) * I)‖ = 1) ∧
      (∑ _j : Fin m, Complex.exp (((π / m : ℝ) : ℂ) * I)).re = m * Real.cos (π / m) := by
  have hm0C : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Complex.exp_nat_mul]
    have h1 : (m:ℂ) * (((π / m : ℝ) : ℂ) * I) = ((π:ℝ):ℂ) * I := by
      push_cast
      field_simp
    rw [h1]
    exact_mod_cast Complex.exp_pi_mul_I
  · intro _
    rw [Complex.norm_exp]
    simp
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Complex.mul_re,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.natCast_re,
      Complex.natCast_im]
    ring

end Q776
