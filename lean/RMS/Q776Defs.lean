import RMS.Q776

/-!
# Q776 — the data of the asymptotic expansion

This module fixes, once and for all, the real-valued data occurring in the Poincaré
expansion of `f m` on the negative axis:

* `Q776.alpha m       = π / m`,
* `Q776.phase m R     = m R sin (α m) - (m-1) α m / 2`,
* `Q776.amplitude m R = 2 (2π)^{(1-m)/2} m^{-1/2} R^{-(m-1)/2} exp (m R cos (α m))`,
* `Q776.firstCoeff m  = (m² - 1)/(24 m)`,

together with elementary positivity facts and the explicit specialization at `m = 2`,
where `amplitude 2 R = (π R)^{-1/2}`, `phase 2 R = 2R - π/4` and `firstCoeff 2 = 1/16`.

It also records that `f m` takes real values at real arguments.
-/

open scoped Real Nat

namespace Q776

/-- The half-opening angle `π / m` of the sector of dominant saddles. -/
noncomputable def alpha (m : ℕ) : ℝ := π / m

/-- The oscillating phase `Ψ m R = m R sin (π/m) - (m-1) π/(2m)`. -/
noncomputable def phase (m : ℕ) (R : ℝ) : ℝ :=
  (m : ℝ) * R * Real.sin (alpha m) - ((m : ℝ) - 1) * alpha m / 2

/-- The amplitude `A m R = 2 (2π)^{(1-m)/2} m^{-1/2} R^{-(m-1)/2} exp (m R cos (π/m))`. -/
noncomputable def amplitude (m : ℕ) (R : ℝ) : ℝ :=
  2 * (2 * π) ^ ((1 - (m : ℝ)) / 2) / Real.sqrt m *
    R ^ (-((m : ℝ) - 1) / 2) * Real.exp ((m : ℝ) * R * Real.cos (alpha m))

/-- The first correction coefficient `c(m,1) = (m² - 1)/(24 m)`. -/
noncomputable def firstCoeff (m : ℕ) : ℝ := ((m : ℝ) ^ 2 - 1) / (24 * m)

section Basic

theorem alpha_pos {m : ℕ} (hm : 1 ≤ m) : 0 < alpha m := by
  have : (0 : ℝ) < m := by exact_mod_cast hm
  exact div_pos Real.pi_pos this

theorem alpha_le_pi_div_two {m : ℕ} (hm : 2 ≤ m) : alpha m ≤ π / 2 := by
  have h2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have : (0 : ℝ) < 2 := by norm_num
  exact div_le_div_of_nonneg_left Real.pi_pos.le this h2

theorem cos_alpha_pos {m : ℕ} (hm : 3 ≤ m) : 0 < Real.cos (alpha m) := by
  have h1 : 0 < alpha m := alpha_pos (by omega)
  have h3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : alpha m < π / 2 := by
    have : π / m < π / 2 := by
      apply div_lt_div_of_pos_left Real.pi_pos (by norm_num)
      linarith
    simpa [alpha] using this
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩

theorem amplitude_pos {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R) : 0 < amplitude m R := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : 0 < 2 * (2 * π) ^ ((1 - (m : ℝ)) / 2) / Real.sqrt m := by
    apply div_pos
    · positivity
    · exact Real.sqrt_pos.mpr hm0
  have h2 : (0 : ℝ) < R ^ (-((m : ℝ) - 1) / 2) := Real.rpow_pos_of_pos hR _
  have h3 : (0 : ℝ) < Real.exp ((m : ℝ) * R * Real.cos (alpha m)) := Real.exp_pos _
  unfold amplitude
  positivity

theorem amplitude_nonneg {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R) : 0 ≤ amplitude m R :=
  (amplitude_pos hm hR).le

end Basic

section TwoCase

theorem alpha_two : alpha 2 = π / 2 := by norm_num [alpha]

theorem phase_two (R : ℝ) : phase 2 R = 2 * R - π / 4 := by
  simp [phase, alpha_two, Real.sin_pi_div_two]
  ring

theorem firstCoeff_two : firstCoeff 2 = 1 / 16 := by norm_num [firstCoeff]

/-- For `x > 0` one has `x ^ (-(1/2) : ℝ) = (√x)⁻¹`. -/
theorem rpow_neg_half {x : ℝ} (hx : 0 < x) : x ^ (-(1/2) : ℝ) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.sqrt_eq_rpow]

theorem amplitude_two {R : ℝ} (hR : 0 < R) : amplitude 2 R = 1 / Real.sqrt (π * R) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hcos : Real.cos (alpha 2) = 0 := by rw [alpha_two, Real.cos_pi_div_two]
  have h1 : ((2:ℝ) * π) ^ ((1 - ((2:ℕ) : ℝ)) / 2) = (Real.sqrt (2 * π))⁻¹ := by
    rw [show ((1 - ((2:ℕ):ℝ))/2) = -(1/2) by norm_num]
    exact rpow_neg_half (by positivity)
  have h2 : R ^ (-(((2:ℕ) : ℝ) - 1) / 2) = (Real.sqrt R)⁻¹ := by
    rw [show (-(((2:ℕ):ℝ) - 1) / 2) = -(1/2) by norm_num]
    exact rpow_neg_half hR
  have h3 : Real.sqrt (2 * π) * Real.sqrt 2 = 2 * Real.sqrt π := by
    rw [Real.sqrt_mul (by norm_num)]
    rw [show Real.sqrt 2 * Real.sqrt π * Real.sqrt 2 = (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt π by
      ring, Real.mul_self_sqrt (by norm_num)]
  have h4 : Real.sqrt (π * R) = Real.sqrt π * Real.sqrt R := Real.sqrt_mul hpi.le R
  have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hpi
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hs2p : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  unfold amplitude
  rw [h1, h2, hcos, show ((2:ℕ):ℝ) * R * 0 = 0 by ring, Real.exp_zero, h4]
  rw [show Real.sqrt ((2:ℕ):ℝ) = Real.sqrt 2 by norm_num]
  field_simp
  linarith [h3]

theorem cos_phase_sub_pi_div_two (R : ℝ) :
    Real.cos (phase 2 R - 1 * π / 2) = Real.sin (phase 2 R) := by
  rw [show phase 2 R - 1 * π / 2 = -(π / 2 - phase 2 R) by ring, Real.cos_neg,
    Real.cos_pi_div_two_sub]

end TwoCase

section RealValued

/-- The real series defining `f m` at a real point. -/
noncomputable def fReal (m : ℕ) (x : ℝ) : ℝ := ∑' n : ℕ, x ^ n / (n ! : ℝ) ^ m

/-- `f m` maps real inputs to real values: it is the coercion of the real series `fReal`. -/
theorem f_ofReal (m : ℕ) (x : ℝ) : f m (x : ℂ) = ((fReal m x : ℝ) : ℂ) := by
  rw [fReal, Complex.ofReal_tsum, f]
  refine tsum_congr fun n => ?_
  push_cast
  ring

theorem f_im_eq_zero (m : ℕ) (x : ℝ) : (f m (x : ℂ)).im = 0 := by
  rw [f_ofReal]; simp

end RealValued

end Q776
