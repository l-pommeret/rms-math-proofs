/-
# Q839 — completion module

This module builds on `RequestProject.Q839` and closes the remaining gaps between
the *exact* logarithmically periodic identities proved there and the actual
*asymptotic* statements asked for in the problem:

* the bridge `qPoch a q = (1 - a) * eulerProd q a` and continuity of
  `a ↦ (a;q)_∞` (`qPoch_eq_one_sub_mul_eulerProd`, `continuous_qPoch_left`);
* the denominator limit `(x⁻¹;q)_∞ → 1` as `x → +∞`, and its reciprocal version
  (`tendsto_qPoch_inv_atTop`, `tendsto_inv_qPoch_inv_atTop`);
* continuity of the two phase profiles (`continuous_phase`, `continuous_phaseNeg`);
* the exact description of the positive zeros of a nonzero solution
  (`zeros_pos_of_pos_q`, `zeros_pos_of_neg_q`);
* the bridge `envelope q x = x^(-1/2) exp((log x)²/(2 log(1/|q|)))` for `q < 0`
  (`envelope_eq_of_neg`);
* and the fixed-phase asymptotic equivalents along the geometric sequences
  `q^{-(n+u₀)}` (`isEquivalent_fixed_phase_pos`) and `(q²)^{-(n+u₀)}`
  (`isEquivalent_fixed_phase_neg`).
-/
import RMS.Q839

open Filter Topology Real

namespace Q839

/-! ## The continuity bridge for `qPoch` in its first argument -/

@[simp] theorem qPoch_zero (q : ℝ) : qPoch 0 q = 1 := by simp [qPoch]

/-- `(a;q)_∞ = (1 - a) (aq;q)_∞`, where `(aq;q)_∞ = eulerProd q a`. -/
theorem qPoch_eq_one_sub_mul_eulerProd {q : ℝ} (hq : |q| < 1) (a : ℝ) :
    qPoch a q = (1 - a) * eulerProd q a := by
  have h := qPoch_split hq a 1
  simp only [Finset.prod_range_one, pow_zero, mul_one, pow_one] at h
  rw [h, eulerProd_eq_qPoch, mul_comm q a]

/-- The infinite `q`-Pochhammer symbol is continuous in its first argument. -/
theorem continuous_qPoch_left {q : ℝ} (hq : |q| < 1) :
    Continuous (fun a : ℝ => qPoch a q) := by
  have h : (fun a : ℝ => qPoch a q) = fun a : ℝ => (1 - a) * eulerProd q a :=
    funext fun a => qPoch_eq_one_sub_mul_eulerProd hq a
  rw [h]
  exact (continuous_const.sub continuous_id).mul (continuous_eulerProd hq)

/-! ## The denominator limit -/

/-- The denominator `(x⁻¹;q)_∞` occurring in the exact formulas tends to `1` at `+∞`. -/
theorem tendsto_qPoch_inv_atTop {q : ℝ} (hq : |q| < 1) :
    Tendsto (fun x : ℝ => qPoch x⁻¹ q) atTop (𝓝 1) := by
  have h0 : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have := ((continuous_qPoch_left hq).tendsto 0).comp h0
  simpa using this

/-- The reciprocal of the denominator also tends to `1` at `+∞`. -/
theorem tendsto_inv_qPoch_inv_atTop {q : ℝ} (hq : |q| < 1) :
    Tendsto (fun x : ℝ => (qPoch x⁻¹ q)⁻¹) atTop (𝓝 1) := by
  simpa using (tendsto_qPoch_inv_atTop hq).inv₀ one_ne_zero

/-! ## Continuity of the phase profiles -/

private theorem continuous_const_rpow {b : ℝ} (hb : 0 < b) : Continuous fun u : ℝ => b ^ u := by
  have : (fun u : ℝ => b ^ u) = fun u : ℝ => Real.exp (Real.log b * u) :=
    funext fun u => Real.rpow_def_of_pos hb u
  rw [this]
  fun_prop

/-- The phase profile `Φ_q` is continuous (`0 < q < 1`). -/
theorem continuous_phase {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : Continuous (phase q) := by
  have hq : |q| < 1 := by rwa [abs_of_pos hq0]
  have hrp : Continuous fun u : ℝ => q ^ u := continuous_const_rpow hq0
  have h1 : Continuous fun u : ℝ => qPoch (q ^ u) q := (continuous_qPoch_left hq).comp hrp
  have h2 : Continuous fun u : ℝ => qPoch (q ^ (1 - u)) q :=
    (continuous_qPoch_left hq).comp (hrp.comp (continuous_const.sub continuous_id))
  have h3 : Continuous fun u : ℝ => q ^ ((u ^ 2 - u) / 2) :=
    (continuous_const_rpow hq0).comp (by fun_prop)
  simpa [phase] using (h3.mul h1).mul h2

/-- The phase profile `Ψ_q` is continuous (`|q| < 1`, `q ≠ 0`). -/
theorem continuous_phaseNeg {q : ℝ} (hq : |q| < 1) (hq0 : q ≠ 0) : Continuous (phaseNeg q) := by
  have hs0 : (0 : ℝ) < q ^ 2 := by positivity
  have hs : |q ^ 2| < 1 := by
    rw [abs_pow]
    nlinarith [abs_nonneg q]
  have hrp : Continuous fun u : ℝ => (q ^ 2) ^ u := continuous_const_rpow hs0
  have hP : Continuous fun a : ℝ => qPoch a (q ^ 2) := continuous_qPoch_left hs
  have h1 : Continuous fun u : ℝ => qPoch ((q ^ 2) ^ u) (q ^ 2) := hP.comp hrp
  have h2 : Continuous fun u : ℝ => qPoch ((q ^ 2) ^ (1 - u)) (q ^ 2) :=
    hP.comp (hrp.comp (continuous_const.sub continuous_id))
  have h3 : Continuous fun u : ℝ => qPoch (-((q ^ 2) ^ (u + (1 : ℝ) / 2))) (q ^ 2) :=
    hP.comp ((hrp.comp (continuous_id.add continuous_const)).neg)
  have h4 : Continuous fun u : ℝ => qPoch (-((q ^ 2) ^ ((1 : ℝ) / 2 - u))) (q ^ 2) :=
    hP.comp ((hrp.comp (continuous_const.sub continuous_id)).neg)
  have h5 : Continuous fun u : ℝ => (q ^ 2) ^ (u ^ 2 - u / 2) :=
    (continuous_const_rpow hs0).comp (by fun_prop)
  have hdef : phaseNeg q = fun u : ℝ =>
      (q ^ 2) ^ (u ^ 2 - u / 2) * qPoch ((q ^ 2) ^ u) (q ^ 2) *
        qPoch ((q ^ 2) ^ (1 - u)) (q ^ 2) * qPoch (-((q ^ 2) ^ (u + (1 : ℝ) / 2))) (q ^ 2) *
        qPoch (-((q ^ 2) ^ ((1 : ℝ) / 2 - u))) (q ^ 2) := rfl
  rw [hdef]
  exact (((h5.mul h1).mul h2).mul h3).mul h4

/-! ## Positivity of the envelope, and the negative-`q` envelope bridge -/

theorem envelope_pos {q x : ℝ} (hx : 0 < x) : 0 < envelope q x := by
  have h1 : (0 : ℝ) < x ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hx _
  have h2 : (0 : ℝ) < Real.exp ((Real.log x) ^ 2 / (2 * Real.log (1 / q))) := Real.exp_pos _
  simpa [envelope] using mul_pos h1 h2

/-- For `q < 0` the total `Real.log (1 / q)` appearing in the Lean definition of the
envelope is the intended real-mathematical `log (1 / |q|)`; the hypothesis `0 < x` is
recorded as requested although the proof does not need it. -/
theorem envelope_eq_of_neg {q : ℝ} (hq : q < 0) {x : ℝ} (hx : 0 < x) :
    envelope q x
      = x ^ (-(1 : ℝ) / 2) * Real.exp ((Real.log x) ^ 2 / (2 * Real.log (1 / |q|))) := by
  have _ := hx
  have h : Real.log (1 / |q|) = Real.log (1 / q) := by
    rw [abs_of_neg hq, one_div, one_div, Real.log_inv, Real.log_inv, Real.log_neg_eq_log]
  rw [envelope, h]

/-! ## Exact description of the positive zeros -/

/-- For `0 < q < 1` and a nonzero continuous solution, the zeros of `f` are exactly the
points `q⁻ʲ` with `j ≥ 1` (all of them positive). -/
theorem zeros_pos_of_pos_q {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {f : ℝ → ℝ}
    (hcont : Continuous f) (hf : ∀ x, f x = (1 - q * x) * f (q * x)) (h0 : f 0 ≠ 0) (x : ℝ) :
    f x = 0 ↔ ∃ j : ℕ, 1 ≤ j ∧ x = (q ^ j)⁻¹ := by
  have hq : |q| < 1 := by rwa [abs_of_pos hq0]
  have hqne : q ≠ 0 := ne_of_gt hq0
  constructor
  · intro hx
    have hE : eulerProd q x = 0 := by
      have := eq_eulerProd hq hcont hf x
      rw [hx] at this
      rcases mul_eq_zero.1 this.symm with h | h
      · exact absurd h h0
      · exact h
    by_contra hc
    push_neg at hc
    refine eulerProd_ne_zero hq (fun j hj => ?_) hE
    exact absurd (eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hj))
      (hc (j + 1) (by omega))
  · rintro ⟨j, hj, rfl⟩
    exact zero_at_inv_pow hqne hf j hj

/-- For `-1 < q < 0` and a nonzero continuous solution, the *positive* zeros of `f` are
exactly the points `|q|⁻²ʲ` with `j ≥ 1`. -/
theorem zeros_pos_of_neg_q {q : ℝ} (hq0 : q < 0) (hq1 : -1 < q) {f : ℝ → ℝ}
    (hcont : Continuous f) (hf : ∀ x, f x = (1 - q * x) * f (q * x)) (h0 : f 0 ≠ 0)
    {x : ℝ} (hx : 0 < x) :
    f x = 0 ↔ ∃ j : ℕ, 1 ≤ j ∧ x = (|q| ^ (2 * j))⁻¹ := by
  have hq : |q| < 1 := by rw [abs_of_neg hq0]; linarith
  have hqne : q ≠ 0 := ne_of_lt hq0
  have habs : ∀ j : ℕ, |q| ^ (2 * j) = q ^ (2 * j) := by
    intro j
    rw [mul_comm 2 j, pow_mul, pow_mul, ← abs_pow, sq_abs]
  constructor
  · intro hxz
    have hE : eulerProd q x = 0 := by
      have := eq_eulerProd hq hcont hf x
      rw [hxz] at this
      rcases mul_eq_zero.1 this.symm with h | h
      · exact absurd h h0
      · exact h
    have hex : ∃ m : ℕ, q ^ (m + 1) * x = 1 := by
      by_contra hc
      push_neg at hc
      exact eulerProd_ne_zero hq hc hE
    obtain ⟨m, hm⟩ := hex
    have hpow_pos : 0 < q ^ (m + 1) := by
      rcases lt_trichotomy (q ^ (m + 1)) 0 with h | h | h
      · nlinarith
      · rw [h] at hm; simp at hm
      · exact h
    have heven : Even (m + 1) := by
      rcases Nat.even_or_odd (m + 1) with h | h
      · exact h
      · exact absurd (h.pow_neg hq0) (not_lt.2 hpow_pos.le)
    obtain ⟨k, hk⟩ := heven
    have hk2 : m + 1 = 2 * k := by omega
    have hkpos : 1 ≤ k := by omega
    refine ⟨k, hkpos, ?_⟩
    rw [habs k, ← hk2]
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hm)
  · rintro ⟨j, hj, rfl⟩
    rw [habs j]
    exact zero_at_inv_pow hqne hf (2 * j) (by omega)

/-! ## Fixed-phase asymptotic equivalents -/

private theorem tendsto_rpow_shift {q u₀ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ => q ^ ((n : ℝ) + u₀)) atTop (𝓝 0) := by
  have h : (fun n : ℕ => q ^ ((n : ℝ) + u₀)) = fun n : ℕ => q ^ n * q ^ u₀ := by
    funext n
    rw [Real.rpow_add hq0, Real.rpow_natCast]
  rw [h]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).mul_const (q ^ u₀)

/-- The denominator limit along the geometric sequence `x_n = b^{-(n+u₀)}` (`0 < b < 1`). -/
private theorem tendsto_qPoch_seq {q b u₀ : ℝ} (hq : |q| < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    Tendsto (fun n : ℕ => qPoch (b ^ (-((n : ℝ) + u₀)))⁻¹ q) atTop (𝓝 1) := by
  have hinv : ∀ n : ℕ, (b ^ (-((n : ℝ) + u₀)))⁻¹ = b ^ ((n : ℝ) + u₀) := by
    intro n
    rw [Real.rpow_neg hb0.le, inv_inv]
  have h : (fun n : ℕ => qPoch (b ^ (-((n : ℝ) + u₀)))⁻¹ q)
      = fun n : ℕ => qPoch (b ^ ((n : ℝ) + u₀)) q := funext fun n => by rw [hinv n]
  rw [h]
  have := ((continuous_qPoch_left hq).tendsto 0).comp
    (tendsto_rpow_shift (q := b) (u₀ := u₀) hb0 hb1)
  simpa using this

/-- **Fixed-phase asymptotics, `0 < q < 1`.** Along the sequence `x_n = q^{-(n+u₀)}` with a
fixed `u₀ ∈ (0,1)`, a nonzero continuous solution satisfies
`f (x_n) / (f 0 (-1)^n Φ_q(u₀) E_q(x_n)) → 1`. -/
theorem tendsto_ratio_fixed_phase_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {f : ℝ → ℝ}
    (hcont : Continuous f) (hf : ∀ x, f x = (1 - q * x) * f (q * x)) (h0 : f 0 ≠ 0)
    {u₀ : ℝ} (hu0 : 0 < u₀) (hu1 : u₀ < 1) :
    Tendsto (fun n : ℕ => f (q ^ (-((n : ℝ) + u₀))) /
      (f 0 * (-1) ^ n * phase q u₀ * envelope q (q ^ (-((n : ℝ) + u₀))))) atTop (𝓝 1) := by
  have hq : |q| < 1 := by rwa [abs_of_pos hq0]
  have hphase : 0 < phase q u₀ := phase_pos hq0 hq1 hu0 hu1
  have key : ∀ n : ℕ, f (q ^ (-((n : ℝ) + u₀))) /
      (f 0 * (-1) ^ n * phase q u₀ * envelope q (q ^ (-((n : ℝ) + u₀))))
      = (qPoch (q ^ (-((n : ℝ) + u₀)))⁻¹ q)⁻¹ := by
    intro n
    set x : ℝ := q ^ (-((n : ℝ) + u₀)) with hxdef
    have hx1 : 1 < x := by
      rw [hxdef]
      exact (Real.one_lt_rpow_iff_of_pos hq0).2 (Or.inr ⟨hq1, by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith⟩)
    have hxpos : 0 < x := by linarith
    have henv : 0 < envelope q x := envelope_pos hxpos
    have hsign : ((-1 : ℝ)) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have hne : f 0 * (-1) ^ n * phase q u₀ * envelope q x ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero h0 hsign) (ne_of_gt hphase)) (ne_of_gt henv)
    have hform := exact_log_periodic_of_eq hq0 hq1 hcont hf hx1 (n := n) (u := u₀) hxdef
    rw [hform]
    have hden : qPoch x⁻¹ q ≠ 0 := by
      refine qPoch_ne_zero hq fun k hk => ?_
      have h2 : q ^ k ≤ 1 := pow_le_one₀ hq0.le hq1.le
      have h3 : x⁻¹ < 1 := by rw [inv_lt_one₀ hxpos]; exact hx1
      have h4 : (0 : ℝ) < x⁻¹ := by positivity
      have h1 : x⁻¹ * q ^ k < 1 := by nlinarith [pow_pos hq0 k]
      linarith [hk ▸ h1]
    field_simp
  have hlim := tendsto_qPoch_seq (q := q) (b := q) (u₀ := u₀) hq hq0 hq1
  have hlim' := hlim.inv₀ (one_ne_zero)
  rw [inv_one] at hlim'
  exact hlim'.congr fun n => (key n).symm

/-- **Fixed-phase asymptotics, `0 < q < 1`, `IsEquivalent` form.** -/
theorem isEquivalent_fixed_phase_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {f : ℝ → ℝ}
    (hcont : Continuous f) (hf : ∀ x, f x = (1 - q * x) * f (q * x)) (h0 : f 0 ≠ 0)
    {u₀ : ℝ} (hu0 : 0 < u₀) (hu1 : u₀ < 1) :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => f (q ^ (-((n : ℝ) + u₀))))
      (fun n : ℕ => f 0 * (-1) ^ n * phase q u₀ * envelope q (q ^ (-((n : ℝ) + u₀)))) := by
  have hphase : 0 < phase q u₀ := phase_pos hq0 hq1 hu0 hu1
  have hne : ∀ᶠ n : ℕ in atTop,
      f 0 * (-1) ^ n * phase q u₀ * envelope q (q ^ (-((n : ℝ) + u₀))) ≠ 0 := by
    filter_upwards with n
    have hx1 : (1 : ℝ) < q ^ (-((n : ℝ) + u₀)) :=
      (Real.one_lt_rpow_iff_of_pos hq0).2 (Or.inr ⟨hq1, by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith⟩)
    have henv : 0 < envelope q (q ^ (-((n : ℝ) + u₀))) := envelope_pos (by linarith)
    have hsign : ((-1 : ℝ)) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h0 hsign) (ne_of_gt hphase)) (ne_of_gt henv)
  rw [Asymptotics.isEquivalent_iff_tendsto_one hne]
  exact tendsto_ratio_fixed_phase_pos hq0 hq1 hcont hf h0 hu0 hu1

/-- **Fixed-phase asymptotics, `-1 < q < 0`.** Along the sequence `x_n = (q²)^{-(n+u₀)}`
with a fixed `u₀ ∈ (0,1)`, a nonzero continuous solution satisfies
`f (x_n) / (f 0 (-1)^n Ψ_q(u₀) E_q(x_n)) → 1`. -/
theorem tendsto_ratio_fixed_phase_neg {q : ℝ} (hq0 : q < 0) (hq1 : -1 < q) {f : ℝ → ℝ}
    (hcont : Continuous f) (hf : ∀ x, f x = (1 - q * x) * f (q * x)) (h0 : f 0 ≠ 0)
    {u₀ : ℝ} (hu0 : 0 < u₀) (hu1 : u₀ < 1) :
    Tendsto (fun n : ℕ => f ((q ^ 2) ^ (-((n : ℝ) + u₀))) /
      (f 0 * (-1) ^ n * phaseNeg q u₀ * envelope q ((q ^ 2) ^ (-((n : ℝ) + u₀))))) atTop
      (𝓝 1) := by
  have hqne : q ≠ 0 := ne_of_lt hq0
  have hq : |q| < 1 := by rw [abs_of_neg hq0]; linarith
  have hs0 : (0 : ℝ) < q ^ 2 := by positivity
  have hs1 : q ^ 2 < 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg q]
  have hphase : 0 < phaseNeg q u₀ := phaseNeg_pos hq hqne hu0 hu1
  have key : ∀ n : ℕ, f ((q ^ 2) ^ (-((n : ℝ) + u₀))) /
      (f 0 * (-1) ^ n * phaseNeg q u₀ * envelope q ((q ^ 2) ^ (-((n : ℝ) + u₀))))
      = (qPoch ((q ^ 2) ^ (-((n : ℝ) + u₀)))⁻¹ q)⁻¹ := by
    intro n
    set x : ℝ := (q ^ 2) ^ (-((n : ℝ) + u₀)) with hxdef
    have hx1 : 1 < x := by
      rw [hxdef]
      exact (Real.one_lt_rpow_iff_of_pos hs0).2 (Or.inr ⟨hs1, by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith⟩)
    have hxpos : 0 < x := by linarith
    have henv : 0 < envelope q x := envelope_pos hxpos
    have hsign : ((-1 : ℝ)) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have hne : f 0 * (-1) ^ n * phaseNeg q u₀ * envelope q x ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero h0 hsign) (ne_of_gt hphase)) (ne_of_gt henv)
    have hform := exact_log_periodic_neg_of_eq hq0 hq1 hcont hf hx1 (n := n) (u := u₀) hxdef
    rw [hform]
    have hden : qPoch x⁻¹ q ≠ 0 := by
      refine qPoch_ne_zero hq fun k hk => ?_
      have h4 : (0 : ℝ) < x⁻¹ := by positivity
      have h3 : x⁻¹ < 1 := by rw [inv_lt_one₀ hxpos]; exact hx1
      have habs : |x⁻¹ * q ^ k| < 1 := by
        rw [abs_mul, abs_pow, abs_of_pos h4]
        have h5 : |q| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg q) hq.le
        nlinarith [pow_pos (abs_pos.2 hqne) k]
      rw [hk] at habs
      simp at habs
    field_simp
  have hlim := tendsto_qPoch_seq (q := q) (b := q ^ 2) (u₀ := u₀) hq hs0 hs1
  have hlim' := hlim.inv₀ (one_ne_zero)
  rw [inv_one] at hlim'
  exact hlim'.congr fun n => (key n).symm

/-- **Fixed-phase asymptotics, `-1 < q < 0`, `IsEquivalent` form.** -/
theorem isEquivalent_fixed_phase_neg {q : ℝ} (hq0 : q < 0) (hq1 : -1 < q) {f : ℝ → ℝ}
    (hcont : Continuous f) (hf : ∀ x, f x = (1 - q * x) * f (q * x)) (h0 : f 0 ≠ 0)
    {u₀ : ℝ} (hu0 : 0 < u₀) (hu1 : u₀ < 1) :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => f ((q ^ 2) ^ (-((n : ℝ) + u₀))))
      (fun n : ℕ =>
        f 0 * (-1) ^ n * phaseNeg q u₀ * envelope q ((q ^ 2) ^ (-((n : ℝ) + u₀)))) := by
  have hqne : q ≠ 0 := ne_of_lt hq0
  have hq : |q| < 1 := by rw [abs_of_neg hq0]; linarith
  have hs0 : (0 : ℝ) < q ^ 2 := by positivity
  have hs1 : q ^ 2 < 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg q]
  have hphase : 0 < phaseNeg q u₀ := phaseNeg_pos hq hqne hu0 hu1
  have hne : ∀ᶠ n : ℕ in atTop,
      f 0 * (-1) ^ n * phaseNeg q u₀ * envelope q ((q ^ 2) ^ (-((n : ℝ) + u₀))) ≠ 0 := by
    filter_upwards with n
    have hx1 : (1 : ℝ) < (q ^ 2) ^ (-((n : ℝ) + u₀)) :=
      (Real.one_lt_rpow_iff_of_pos hs0).2 (Or.inr ⟨hs1, by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith⟩)
    have henv : 0 < envelope q ((q ^ 2) ^ (-((n : ℝ) + u₀))) := envelope_pos (by linarith)
    have hsign : ((-1 : ℝ)) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h0 hsign) (ne_of_gt hphase)) (ne_of_gt henv)
  rw [Asymptotics.isEquivalent_iff_tendsto_one hne]
  exact tendsto_ratio_fixed_phase_neg hq0 hq1 hcont hf h0 hu0 hu1

end Q839
