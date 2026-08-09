import RMS.Q776Taylor

/-!
# Q776 — the local (multidimensional Laplace) estimate at the dominant saddle

Near the dominant saddle `θ = 0` the torus phase expands as

`S θ = m - Q θ / 2 - i (∑_j v_j³)/6 + O(|θ|⁴)`,   `Q θ = ∑ θ_j² + (∑ θ_j)²`,

the cubic term integrating to zero by parity.  The resulting leading contribution is

`mainTerm d R = exp (r (d+1)) * ((π/(r/2))^{1/2})^d / √(d+1)`,  `r = R e^{iπ/(d+1)}`,

with an additive remainder `O(exp((d+1) R cos(π/(d+1))) R^{-d/2-1})`.
-/

open scoped Real Nat
open Complex MeasureTheory

namespace Q776

set_option maxHeartbeats 1000000

/-- The leading contribution of the dominant saddle `θ = 0`. -/
noncomputable def mainTerm (d : ℕ) (R : ℝ) : ℂ :=
  Complex.exp (rr (d+1) R * ((d : ℂ) + 1)) *
    (((((π : ℝ) : ℂ)/(rr (d+1) R/2)) ^ ((1 : ℂ)/2))^d / ((Real.sqrt (d+1) : ℝ) : ℂ))

/-- The box around the second dominant saddle `θ = (-2π/m, …, -2π/m)`. -/
def boxNeg (d : ℕ) (δ : ℝ) : Set (Fin d → ℝ) :=
  Set.univ.pi fun _ => Set.Icc (-(2 * alpha (d+1)) - δ) (-(2 * alpha (d+1)) + δ)

section Basic

theorem continuous_torusPhase {d : ℕ} : Continuous (fun θ : Fin d → ℝ => torusPhase θ) := by
  unfold torusPhase coordSum
  fun_prop

theorem continuous_integrand {d : ℕ} (r : ℂ) :
    Continuous (fun θ : Fin d → ℝ => Complex.exp (r * torusPhase θ)) :=
  Complex.continuous_exp.comp (continuous_const.mul continuous_torusPhase)

theorem norm_integrand (m : ℕ) (R : ℝ) {d : ℕ} (θ : Fin d → ℝ) :
    ‖Complex.exp (rr m R * torusPhase θ)‖ = Real.exp (R * gfun m θ) := by
  rw [Complex.norm_exp, re_rr_mul_torusPhase]

theorem isCompact_cube (d : ℕ) : IsCompact (cube d) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem measurableSet_cube (d : ℕ) : MeasurableSet (cube d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

theorem measurableSet_box (d : ℕ) (δ : ℝ) : MeasurableSet (box d δ) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

theorem measurableSet_boxNeg (d : ℕ) (δ : ℝ) : MeasurableSet (boxNeg d δ) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

end Basic

/-- The principal square root in polar coordinates. -/
theorem cpow_half_polar {rho w : ℝ} (hrho : 0 < rho) (hw : |w| < π) :
    ((rho : ℂ) * Complex.exp ((w : ℂ) * I)) ^ ((1:ℂ)/2)
      = (Real.sqrt rho : ℂ) * Complex.exp (((w/2 : ℝ) : ℂ) * I) := by
  have hz : ((rho : ℂ) * Complex.exp ((w : ℂ) * I)) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 hrho.ne') (Complex.exp_ne_zero _)
  rw [Complex.cpow_def_of_ne_zero hz]
  have hnorm : ‖(rho : ℂ) * Complex.exp ((w : ℂ) * I)‖ = rho := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrho, Complex.norm_exp]
    simp
  have hwlt := abs_lt.1 hw
  have harg : ((rho : ℂ) * Complex.exp ((w : ℂ) * I)).arg = w := by
    rw [Complex.arg_real_mul _ hrho, Complex.exp_mul_I]
    exact Complex.arg_cos_add_sin_mul_I (show w ∈ Set.Ioc (-π) π from ⟨hwlt.1, hwlt.2.le⟩)
  have hlog : Complex.log ((rho : ℂ) * Complex.exp ((w : ℂ) * I))
      = (Real.log rho : ℂ) + (w : ℝ) * I := by
    show (Real.log ‖(rho : ℂ) * Complex.exp ((w:ℂ) * I)‖ : ℂ)
      + ((((rho : ℂ) * Complex.exp ((w:ℂ)*I)).arg : ℝ) : ℂ) * I = _
    rw [hnorm, harg]
  rw [hlog]
  have hsplit : ((Real.log rho : ℂ) + ((w : ℝ) : ℂ) * I) * (1/2 : ℂ)
      = ((Real.log (Real.sqrt rho) : ℝ) : ℂ) + ((w/2 : ℝ) : ℂ) * I := by
    rw [Real.log_sqrt hrho.le]; push_cast; ring
  rw [hsplit, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (Real.sqrt_pos.2 hrho)]


/-- Twice the real part of the main term is exactly `(2π)^d` times the model
`amplitude · cos phase`. -/
theorem two_re_mainTerm {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) :
    2 * (mainTerm d R).re
      = (2*π)^d * (amplitude (d+1) R * Real.cos (phase (d+1) R)) := by
  have hpi := Real.pi_pos
  have hd1 : (0:ℝ) < (d:ℝ) + 1 := by positivity
  have ha : 0 < alpha (d+1) := alpha_pos (m := d+1) (by omega)
  have ha2 : alpha (d+1) ≤ π/2 := alpha_le_pi_div_two (m := d+1) (by omega)
  have hbase : ((π:ℝ):ℂ)/(rr (d+1) R/2)
      = ((2*π/R : ℝ) : ℂ) * Complex.exp (((-alpha (d+1) : ℝ) : ℂ) * I) := by
    rw [rr]
    have hexp : Complex.exp (((-alpha (d+1) : ℝ) : ℂ) * I)
        = (Complex.exp (((alpha (d+1) : ℝ) : ℂ) * I))⁻¹ := by
      rw [← Complex.exp_neg]
      congr 1
      push_cast
      ring
    rw [hexp]
    have hRne : ((R:ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hR)
    have hene : Complex.exp (((alpha (d+1) : ℝ) : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
    field_simp
    push_cast
    field_simp
  have hsqrt : (((π:ℝ):ℂ)/(rr (d+1) R/2)) ^ ((1:ℂ)/2)
      = ((Real.sqrt (2*π/R) : ℝ) : ℂ) * Complex.exp (((-alpha (d+1)/2 : ℝ) : ℂ) * I) := by
    rw [hbase]
    exact cpow_half_polar (by positivity) (by
      rw [abs_lt]
      constructor <;> linarith)
  have hpowd : ((((π:ℝ):ℂ)/(rr (d+1) R/2)) ^ ((1:ℂ)/2))^d
      = ((Real.sqrt (2*π/R)^d : ℝ) : ℂ)
        * Complex.exp (((-(d:ℝ)*alpha (d+1)/2 : ℝ) : ℂ) * I) := by
    rw [hsqrt, mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hexpmain : Complex.exp (rr (d+1) R * ((d:ℂ)+1))
      = ((Real.exp (((d:ℝ)+1) * R * Real.cos (alpha (d+1))) : ℝ) : ℂ)
        * Complex.exp (((((d:ℝ)+1) * R * Real.sin (alpha (d+1)) : ℝ)) * I) := by
    have hrw : rr (d+1) R * ((d:ℂ)+1)
        = ((((d:ℝ)+1) * R * Real.cos (alpha (d+1)) : ℝ) : ℂ)
          + ((((d:ℝ)+1) * R * Real.sin (alpha (d+1)) : ℝ) : ℂ) * I := by
      rw [rr, Complex.exp_mul_I]
      push_cast [Complex.ofReal_cos, Complex.ofReal_sin]
      ring
    rw [hrw, Complex.exp_add, ← Complex.ofReal_exp]
  have hphase : ((d:ℝ)+1) * R * Real.sin (alpha (d+1)) + (-(d:ℝ)*alpha (d+1)/2)
      = phase (d+1) R := by
    rw [phase]
    push_cast
    ring
  have hmain : mainTerm d R
      = ((Real.exp (((d:ℝ)+1)*R*Real.cos (alpha (d+1))) * Real.sqrt (2*π/R)^d
            / Real.sqrt ((d:ℝ)+1) : ℝ) : ℂ) * Complex.exp (((phase (d+1) R : ℝ)) * I) := by
    rw [mainTerm, hpowd, hexpmain, ← hphase,
      show ((((d:ℝ)+1) * R * Real.sin (alpha (d+1)) + (-(d:ℝ)*alpha (d+1)/2) : ℝ) : ℂ) * I
        = ((((d:ℝ)+1) * R * Real.sin (alpha (d+1)) : ℝ) : ℂ) * I
          + (((-(d:ℝ)*alpha (d+1)/2 : ℝ)) : ℂ) * I by push_cast; ring,
      Complex.exp_add]
    push_cast
    ring
  rw [hmain, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, amplitude_succ d R]
  have h2pi : (0:ℝ) < 2*π := by positivity
  have hsq : Real.sqrt (2*π/R)^d = (2*π)^(-(d:ℝ)/2) * R^(-(d:ℝ)/2) * (2*π)^(d:ℕ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((2*π/R) ^ ((1:ℝ)/2)) d,
      ← Real.rpow_mul (by positivity), Real.div_rpow h2pi.le hR.le,
      show ((1:ℝ)/2 * d) = (d:ℝ)/2 by ring,
      show (-(d:ℝ)/2) = -((d:ℝ)/2) by ring, Real.rpow_neg h2pi.le, Real.rpow_neg hR.le,
      ← Real.rpow_natCast (2*π) d]
    have hsplit2 : (2*π)^((d:ℝ)) = (2*π)^((d:ℝ)/2) * (2*π)^((d:ℝ)/2) := by
      rw [← Real.rpow_add h2pi]
      ring_nf
    rw [hsplit2]
    have h1 : (0:ℝ) < (2*π)^((d:ℝ)/2) := Real.rpow_pos_of_pos h2pi _
    have h2 : (0:ℝ) < R^((d:ℝ)/2) := Real.rpow_pos_of_pos hR _
    field_simp
  rw [hsq]
  field_simp


/-! ## The conjugation symmetry between the two dominant saddles -/

theorem torusPhase_shift {d : ℕ} (u : Fin d → ℝ) :
    torusPhase (u + fun _ => -(2 * alpha (d+1)))
      = Complex.exp ((-(2 * alpha (d+1)) : ℝ) * I) * torusPhase u := by
  have hma : ((d:ℝ)+1) * alpha (d+1) = π := by
    rw [alpha]
    push_cast
    field_simp
  have hsum : coordSum (u + fun _ => -(2 * alpha (d+1)))
      = coordSum u - (d:ℝ) * (2 * alpha (d+1)) := by
    simp [coordSum, Finset.sum_add_distrib]
    ring
  rw [torusPhase, torusPhase, hsum, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.exp_add]
    congr 1
    simp
    push_cast
    ring
  · rw [← Complex.exp_add]
    have hd2 : (d:ℝ) * (2*alpha (d+1)) = 2*π - 2*alpha (d+1) := by nlinarith [hma]
    have h2 : (-((coordSum u - (d:ℝ) * (2 * alpha (d+1)) : ℝ) : ℂ)) * I
        = (((-(2*alpha (d+1)) : ℝ) : ℂ) * I + (-((coordSum u : ℝ) : ℂ)) * I)
          + ((2*π : ℝ) : ℂ) * I := by
      rw [hd2]
      push_cast
      ring
    rw [h2, Complex.exp_add]
    have h3 : Complex.exp (((2*π : ℝ) : ℂ) * I) = 1 := by
      push_cast
      exact Complex.exp_two_pi_mul_I
    rw [h3, mul_one]


theorem torusPhase_conj {d : ℕ} (u : Fin d → ℝ) :
    (starRingEnd ℂ) (torusPhase u) = torusPhase (-u) := by
  have hsum : coordSum (-u) = -coordSum u := by
    simp [coordSum, Finset.sum_neg_distrib]
  rw [torusPhase, torusPhase, hsum, map_add, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.exp_conj]
    congr 1
    simp
  · rw [← Complex.exp_conj]
    congr 1
    simp

theorem rr_mul_exp_neg {d : ℕ} (R : ℝ) :
    rr (d+1) R * Complex.exp ((-(2 * alpha (d+1)) : ℝ) * I)
      = (starRingEnd ℂ) (rr (d+1) R) := by
  rw [rr, map_mul, ← Complex.exp_conj, mul_assoc, ← Complex.exp_add]
  congr 1
  · simp
  · congr 1
    simp [Complex.conj_I]
    push_cast
    ring

theorem integral_boxNeg_eq_conj {d : ℕ} (δ R : ℝ) :
    (∫ θ in boxNeg d δ, Complex.exp (rr (d+1) R * torusPhase θ))
      = (starRingEnd ℂ) (∫ θ in box d δ, Complex.exp (rr (d+1) R * torusPhase θ)) := by
  set c : Fin d → ℝ := fun _ => -(2 * alpha (d+1)) with hc
  set F : (Fin d → ℝ) → ℂ := fun θ => Complex.exp (rr (d+1) R * torusPhase θ) with hF
  have hpre : (fun y : Fin d → ℝ => y + c) ⁻¹' (boxNeg d δ) = box d δ := by
    ext u
    simp only [boxNeg, box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Icc,
      forall_true_left, hc, Pi.add_apply]
    constructor
    · intro h j
      have := h j
      constructor <;> linarith [this.1, this.2]
    · intro h j
      have := h j
      constructor <;> linarith [this.1, this.2]
  have h1 : (∫ θ in boxNeg d δ, F θ) = ∫ u in box d δ, F (u + c) := by
    have := (measurePreserving_add_right (volume : Measure (Fin d → ℝ)) c).setIntegral_preimage_emb
      (measurableEmbedding_addRight c) F (boxNeg d δ)
    rw [hpre] at this
    exact this.symm
  have h2 : ∀ u : Fin d → ℝ, F (u + c) = (starRingEnd ℂ) (F (-u)) := by
    intro u
    rw [hF]
    simp only
    rw [torusPhase_shift u, ← mul_assoc, rr_mul_exp_neg, ← Complex.exp_conj, map_mul,
      torusPhase_conj]
    simp
  have h3 : (∫ u in box d δ, F (u + c)) = ∫ u in box d δ, (starRingEnd ℂ) (F (-u)) := by
    exact setIntegral_congr_fun (measurableSet_box d δ) fun u _ => h2 u
  have h4 : (∫ u in box d δ, (starRingEnd ℂ) (F (-u)))
      = (starRingEnd ℂ) (∫ u in box d δ, F (-u)) := by
    rw [← integral_conj]
  have h5 : (∫ u in box d δ, F (-u)) = ∫ u in box d δ, F u := by
    have hpre2 : (fun y : Fin d → ℝ => -y) ⁻¹' (box d δ) = box d δ := by
      ext u
      simp only [box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Icc, Pi.neg_apply,
        forall_true_left]
      constructor
      · intro h j
        have := h j
        constructor <;> linarith [this.1, this.2]
      · intro h j
        have := h j
        constructor <;> linarith [this.1, this.2]
    have := (Measure.measurePreserving_neg (volume : Measure (Fin d → ℝ))).setIntegral_preimage_emb
      (measurableEmbedding_neg) F (box d δ)
    rw [hpre2] at this
    exact this
  rw [h1, h3, h4, h5]


/-! ## Constants for the local estimate -/

/-- The constant controlling the size of the correction `X` on the box. -/
noncomputable def cOne (d : ℕ) : ℝ := (1 + (d:ℝ)^2) * (1/6 + (d:ℝ)/12)

/-- The constant in front of `R² (sqNorm θ)³`. -/
noncomputable def kOne (d : ℕ) : ℝ := ((d:ℝ) + (d:ℝ)^3)/9 + (d:ℝ)*(1+(d:ℝ)^2)^2/72

/-- The constant in front of `R (sqNorm θ)²`. -/
noncomputable def kTwo (d : ℕ) : ℝ := (1 + (d:ℝ)^2)/12

theorem cOne_pos (d : ℕ) : 0 < cOne d := by
  rw [cOne]; positivity

theorem kOne_nonneg (d : ℕ) : 0 ≤ kOne d := by
  rw [kOne]; positivity

theorem kTwo_nonneg (d : ℕ) : 0 ≤ kTwo d := by
  rw [kTwo]; positivity

/-- **The pointwise Laplace estimate on the box.**  On `[-δ,δ]^d`, with `δ` small enough,
the integrand differs from the Gaussian times `1 + t` by a controlled amount. -/
theorem local_pointwise {d : ℕ} (hd : 2 ≤ d) {δ R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδd : (d:ℝ) * δ ≤ 1) (hδc : δ * cOne d ≤ Real.cos (alpha (d+1))/4) (hR : 0 < R)
    {θ : Fin d → ℝ} (hθ : ∀ j, |θ j| ≤ δ) :
    ‖Complex.exp (rr (d+1) R * (torusPhase θ - ((d:ℂ)+1)))
       - Complex.exp (-(rr (d+1) R/2) * ((quadForm θ : ℝ):ℂ))
          * (1 + -I * rr (d+1) R * ((cubForm θ:ℝ):ℂ)/6)‖
      ≤ (kOne d/2 * R^2 * (sqNorm θ)^3 + kTwo d * R * (sqNorm θ)^2)
          * Real.exp (-(R * Real.cos (alpha (d+1))/4) * sqNorm θ) := by
  have hpi := Real.pi_pos
  set κ := Real.cos (alpha (d+1)) with hκd
  have hκ : 0 < κ := cos_alpha_pos (by omega)
  have hκ1 : κ ≤ 1 := Real.cos_le_one _
  set r := rr (d+1) R with hrd
  have hrn : ‖r‖ = R := norm_rr _ hR.le
  have hrre : r.re = R * κ := rr_re _ _
  set s := sqNorm θ with hsd
  have hs0 : 0 ≤ s := sqNorm_nonneg θ
  have hsbox : s ≤ (d:ℝ) * δ^2 := sqNorm_le_of_box hθ
  have hQ : s ≤ quadForm θ := sqNorm_le_quadForm θ
  have hθ1 : ∀ j, |θ j| ≤ 1 := fun j => le_trans (hθ j) hδ1
  have hcs : |coordSum θ| ≤ 1 := le_trans (abs_coordSum_le hθ) hδd
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
  set E := torusPhase θ - ((d:ℂ)+1) + ((quadForm θ : ℝ):ℂ)/2 + I * ((cubForm θ:ℝ):ℂ)/6 with hEd
  have hE : ‖E‖ ≤ (1 + (d:ℝ)^2)/12 * s^2 := taylor_bound hθ1 hcs
  set w := -(r/2) * ((quadForm θ : ℝ):ℂ) with hwd
  set t := -I * r * ((cubForm θ:ℝ):ℂ)/6 with htd
  set X := t + r * E with hXd
  have hz : r * (torusPhase θ - ((d:ℂ)+1)) = w + X := by
    rw [hXd, htd, hwd, hEd]; ring
  -- norms
  have hnt : ‖t‖ = R * |cubForm θ| / 6 := by
    rw [htd, norm_div, norm_mul, norm_mul, norm_neg, Complex.norm_I, hrn,
      Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hnrE : ‖r * E‖ ≤ R * ((1 + (d:ℝ)^2)/12 * s^2) := by
    rw [norm_mul, hrn]
    exact mul_le_mul_of_nonneg_left hE hR.le
  have hcub : |cubForm θ| ≤ (1 + (d:ℝ)^2) * δ * s := abs_cubForm_le hδ.le hθ
  have hcub2 : (cubForm θ)^2 ≤ 2*((d:ℝ) + (d:ℝ)^3) * s^3 := cubForm_sq_le θ
  have hs2 : s^2 ≤ (d:ℝ) * δ * s := by
    have hδ2 : δ^2 ≤ δ := by nlinarith
    nlinarith [hs0, hsbox]
  have hδ2 : δ^2 ≤ 1 := by nlinarith
  have hsd' : s ≤ (d:ℝ) := le_trans hsbox (by nlinarith)
  have hs3 : s^4 ≤ (d:ℝ) * s^3 := by
    nlinarith [pow_nonneg hs0 3, hsd']
  -- bound on ‖X‖
  have hnX : ‖X‖ ≤ R * κ / 4 * s := by
    have h1 : ‖X‖ ≤ ‖t‖ + ‖r * E‖ := norm_add_le _ _
    have h2 : ‖t‖ ≤ R * ((1 + (d:ℝ)^2) * δ * s) / 6 := by
      rw [hnt]
      have := mul_le_mul_of_nonneg_left hcub hR.le
      linarith
    have h3 : ‖r * E‖ ≤ R * ((1 + (d:ℝ)^2)/12 * ((d:ℝ) * δ * s)) := by
      refine le_trans hnrE ?_
      have : (1 + (d:ℝ)^2)/12 * s^2 ≤ (1 + (d:ℝ)^2)/12 * ((d:ℝ) * δ * s) := by
        have hpos : (0:ℝ) ≤ (1 + (d:ℝ)^2)/12 := by positivity
        exact mul_le_mul_of_nonneg_left hs2 hpos
      exact mul_le_mul_of_nonneg_left this hR.le
    have h4 : R * ((1 + (d:ℝ)^2) * δ * s) / 6 + R * ((1 + (d:ℝ)^2)/12 * ((d:ℝ) * δ * s))
        = R * s * (δ * cOne d) := by rw [cOne]; ring
    have h5 : R * s * (δ * cOne d) ≤ R * s * (κ/4) := by
      have : (0:ℝ) ≤ R * s := by positivity
      exact mul_le_mul_of_nonneg_left hδc this
    calc ‖X‖ ≤ ‖t‖ + ‖r * E‖ := h1
      _ ≤ R * ((1 + (d:ℝ)^2) * δ * s) / 6 + R * ((1 + (d:ℝ)^2)/12 * ((d:ℝ) * δ * s)) := by
          linarith
      _ = R * s * (δ * cOne d) := h4
      _ ≤ R * s * (κ/4) := h5
      _ = R * κ / 4 * s := by ring
  -- bound on ‖X‖²
  have hnX2 : ‖X‖^2 ≤ kOne d * R^2 * s^3 := by
    have ht2 : ‖t‖^2 ≤ R^2 * (((d:ℝ) + (d:ℝ)^3)/18) * s^3 := by
      rw [hnt]
      have h1 : (R * |cubForm θ| / 6)^2 = R^2 * (cubForm θ)^2 / 36 := by
        rw [div_pow, mul_pow, sq_abs]; ring
      rw [h1]
      have h2 := mul_le_mul_of_nonneg_left hcub2 (sq_nonneg R)
      calc R^2 * (cubForm θ)^2 / 36 ≤ R^2 * (2*((d:ℝ) + (d:ℝ)^3) * s^3) / 36 := by linarith
        _ = R^2 * (((d:ℝ) + (d:ℝ)^3)/18) * s^3 := by ring
    have he2 : ‖r * E‖^2 ≤ R^2 * ((d:ℝ)*(1+(d:ℝ)^2)^2/144) * s^3 := by
      have h0 : (0:ℝ) ≤ ‖r * E‖ := norm_nonneg _
      have h1 : ‖r * E‖^2 ≤ (R * ((1 + (d:ℝ)^2)/12 * s^2))^2 := by
        have hrhs : (0:ℝ) ≤ R * ((1 + (d:ℝ)^2)/12 * s^2) := by positivity
        exact pow_le_pow_left₀ h0 hnrE 2
      have h2 : (R * ((1 + (d:ℝ)^2)/12 * s^2))^2 = R^2 * ((1+(d:ℝ)^2)^2/144) * s^4 := by ring
      rw [h2] at h1
      have h3 : R^2 * ((1+(d:ℝ)^2)^2/144) * s^4
          ≤ R^2 * ((1+(d:ℝ)^2)^2/144) * ((d:ℝ) * s^3) := by
        have hpos : (0:ℝ) ≤ R^2 * ((1+(d:ℝ)^2)^2/144) := by positivity
        exact mul_le_mul_of_nonneg_left hs3 hpos
      calc ‖r * E‖^2 ≤ R^2 * ((1+(d:ℝ)^2)^2/144) * s^4 := h1
        _ ≤ R^2 * ((1+(d:ℝ)^2)^2/144) * ((d:ℝ) * s^3) := h3
        _ = R^2 * ((d:ℝ)*(1+(d:ℝ)^2)^2/144) * s^3 := by ring
    have hsplit : ‖X‖^2 ≤ 2 * ‖t‖^2 + 2 * ‖r * E‖^2 := by
      have h1 : ‖X‖ ≤ ‖t‖ + ‖r * E‖ := norm_add_le _ _
      have h2 : ‖X‖^2 ≤ (‖t‖ + ‖r * E‖)^2 := pow_le_pow_left₀ (norm_nonneg X) h1 2
      nlinarith [h2, sq_nonneg (‖t‖ - ‖r * E‖)]
    have : 2 * (R^2 * (((d:ℝ) + (d:ℝ)^3)/18) * s^3)
        + 2 * (R^2 * ((d:ℝ)*(1+(d:ℝ)^2)^2/144) * s^3) = kOne d * R^2 * s^3 := by
      rw [kOne]; ring
    linarith [hsplit, ht2, he2, this]
  -- the Gaussian factor
  have hexpw : ‖Complex.exp w‖ ≤ Real.exp (-(R*κ/2) * s) := by
    rw [hwd, norm_cexp_quadForm]
    apply Real.exp_le_exp.2
    have hre2 : (r/2).re = R * κ / 2 := by
      rw [show r/2 = r * (2:ℂ)⁻¹ by ring]
      simp [Complex.mul_re, hrre]
      ring
    rw [hre2]
    have hp : (0:ℝ) ≤ R*κ/2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hQ hp]
  have hexpwpos : (0:ℝ) < ‖Complex.exp w‖ := by
    rw [norm_pos_iff]; exact Complex.exp_ne_zero _
  -- assembling
  have hfact : Complex.exp (w + X) - Complex.exp w * (1 + t)
      = Complex.exp w * (Complex.exp X - 1 - t) := by
    rw [Complex.exp_add]; ring
  have hXt : Complex.exp X - 1 - t = (Complex.exp X - 1 - X) + (X - t) := by ring
  have hXmt : X - t = r * E := by rw [hXd]; ring
  have hbnd : ‖Complex.exp X - 1 - t‖ ≤ ‖X‖^2/2 * Real.exp ‖X‖ + ‖r * E‖ := by
    rw [hXt]
    refine le_trans (norm_add_le _ _) ?_
    rw [hXmt]
    linarith [norm_exp_sub_one_sub_self_le X]
  rw [hz, hfact, norm_mul]
  have hlam : Real.exp ‖X‖ ≤ Real.exp (R * κ / 4 * s) := Real.exp_le_exp.2 hnX
  have hstep1 : ‖Complex.exp w‖ * ‖Complex.exp X - 1 - t‖
      ≤ Real.exp (-(R*κ/2) * s) * (‖X‖^2/2 * Real.exp (R * κ / 4 * s) + ‖r * E‖) := by
    refine mul_le_mul hexpw ?_ (norm_nonneg _) (Real.exp_pos _).le
    refine le_trans hbnd ?_
    have : ‖X‖^2/2 * Real.exp ‖X‖ ≤ ‖X‖^2/2 * Real.exp (R * κ / 4 * s) := by
      have : (0:ℝ) ≤ ‖X‖^2/2 := by positivity
      exact mul_le_mul_of_nonneg_left hlam this
    linarith
  refine le_trans hstep1 ?_
  have hexpsum : Real.exp (-(R*κ/2) * s) * Real.exp (R * κ / 4 * s)
      = Real.exp (-(R * κ/4) * s) := by
    rw [← Real.exp_add]; congr 1; ring
  have hmono : Real.exp (-(R*κ/2) * s) ≤ Real.exp (-(R * κ/4) * s) := by
    apply Real.exp_le_exp.2
    have hp : (0:ℝ) ≤ R*κ/4*s := by positivity
    linarith
  have hexpand : Real.exp (-(R*κ/2) * s) * (‖X‖^2/2 * Real.exp (R * κ / 4 * s) + ‖r * E‖)
      = (‖X‖^2/2) * (Real.exp (-(R*κ/2) * s) * Real.exp (R * κ / 4 * s))
        + ‖r * E‖ * Real.exp (-(R*κ/2) * s) := by ring
  rw [hexpand, hexpsum]
  have hA : (‖X‖^2/2) * Real.exp (-(R * κ/4) * s)
      ≤ (kOne d/2 * R^2 * s^3) * Real.exp (-(R * κ/4) * s) := by
    have : ‖X‖^2/2 ≤ kOne d/2 * R^2 * s^3 := by linarith [hnX2]
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  have hB : ‖r * E‖ * Real.exp (-(R*κ/2) * s)
      ≤ (kTwo d * R * s^2) * Real.exp (-(R * κ/4) * s) := by
    have h1 : ‖r * E‖ ≤ kTwo d * R * s^2 := by
      refine le_trans hnrE ?_
      rw [kTwo]; ring_nf; exact le_of_eq rfl
    have h2 : (0:ℝ) ≤ kTwo d * R * s^2 := by
      have := kTwo_nonneg d; positivity
    calc ‖r * E‖ * Real.exp (-(R*κ/2) * s)
        ≤ (kTwo d * R * s^2) * Real.exp (-(R*κ/2) * s) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ (kTwo d * R * s^2) * Real.exp (-(R * κ/4) * s) :=
          mul_le_mul_of_nonneg_left hmono h2
  have : (kOne d/2 * R^2 * s^3) * Real.exp (-(R * κ/4) * s)
      + (kTwo d * R * s^2) * Real.exp (-(R * κ/4) * s)
      = (kOne d/2 * R^2 * s^3 + kTwo d * R * s^2) * Real.exp (-(R * κ/4) * s) := by ring
  linarith [hA, hB, this]

/-! ## Assembling the local estimate

The integral over the box is compared with the full-space Gaussian in four steps:
factor out the saddle exponential, replace the integrand by the Gaussian model
(`local_pointwise`), kill the cubic correction by parity (`integral_box_cubForm_zero`),
and complete the truncated Gaussian to the full space (`integral_cgauss_quadForm`).
-/

/-- The norm of the saddle exponential factor. -/
theorem norm_exp_saddle (d : ℕ) (R : ℝ) :
    ‖Complex.exp (rr (d+1) R * ((d:ℂ)+1))‖
      = Real.exp (((d:ℝ)+1) * R * Real.cos (alpha (d+1))) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, rr_re, rr_im]
  ring

/-- Factoring the saddle exponential out of the box integral. -/
theorem integral_box_factor {d : ℕ} (δ R : ℝ) :
    (∫ θ in box d δ, Complex.exp (rr (d+1) R * torusPhase θ))
      = Complex.exp (rr (d+1) R * ((d:ℂ)+1)) *
        ∫ θ in box d δ, Complex.exp (rr (d+1) R * (torusPhase θ - ((d:ℂ)+1))) := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_box d δ) fun θ _ => ?_
  rw [← Complex.exp_add]
  congr 1
  ring

theorem rr_half_re {d : ℕ} (R : ℝ) :
    (rr (d+1) R / 2).re = R * Real.cos (alpha (d+1)) / 2 := by
  rw [show rr (d+1) R / 2 = rr (d+1) R * (2:ℂ)⁻¹ by ring]
  simp [Complex.mul_re, rr_re]
  ring

theorem rr_half_re_pos {d : ℕ} (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R) :
    0 < (rr (d+1) R / 2).re := by
  have hk : 0 < Real.cos (alpha (d+1)) := cos_alpha_pos (by omega)
  rw [rr_half_re]
  positivity

/-- The main term is the saddle exponential times the full-space Gaussian integral. -/
theorem mainTerm_eq_gauss {d : ℕ} (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R) :
    mainTerm d R = Complex.exp (rr (d+1) R * ((d:ℂ)+1)) *
      ∫ θ : Fin d → ℝ, Complex.exp (-(rr (d+1) R/2) * ((quadForm θ : ℝ):ℂ)) := by
  rw [integral_cgauss_quadForm d (rr_half_re_pos hd hR), mainTerm]

/-- The linear cubic correction integrates to zero over the box. -/
theorem integral_box_model {d : ℕ} (δ : ℝ) (r : ℂ) :
    (∫ θ in box d δ, Complex.exp (-(r/2) * ((quadForm θ:ℝ):ℂ))
        * (1 + -I * r * ((cubForm θ:ℝ):ℂ)/6))
      = ∫ θ in box d δ, Complex.exp (-(r/2) * ((quadForm θ:ℝ):ℂ)) := by
  have hcont1 : Continuous (fun θ : Fin d → ℝ => Complex.exp (-(r/2) * ((quadForm θ:ℝ):ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_quadForm))
  have hcont2 : Continuous (fun θ : Fin d → ℝ =>
      Complex.exp (-(r/2) * ((quadForm θ:ℝ):ℂ)) * ((cubForm θ:ℝ):ℂ)) := by
    refine hcont1.mul (Complex.continuous_ofReal.comp ?_)
    unfold cubForm coordSum
    fun_prop
  have hI1 : IntegrableOn (fun θ : Fin d → ℝ => Complex.exp (-(r/2) * ((quadForm θ:ℝ):ℂ)))
      (box d δ) :=
    hcont1.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)
  have hI2 : IntegrableOn (fun θ : Fin d → ℝ =>
      (-I*r/6) * (Complex.exp (-(r/2) * ((quadForm θ:ℝ):ℂ)) * ((cubForm θ:ℝ):ℂ))) (box d δ) :=
    ((hcont2.continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc)).const_mul _)
  have hsplit : (∫ θ in box d δ, Complex.exp (-(r/2) * ((quadForm θ:ℝ):ℂ))
        * (1 + -I * r * ((cubForm θ:ℝ):ℂ)/6))
      = (∫ θ in box d δ, Complex.exp (-(r/2) * ((quadForm θ:ℝ):ℂ)))
        + ∫ θ in box d δ, (-I*r/6) * (Complex.exp (-(r/2) * ((quadForm θ:ℝ):ℂ))
            * ((cubForm θ:ℝ):ℂ)) := by
    rw [← integral_add hI1 hI2]
    refine setIntegral_congr_fun (measurableSet_box d δ) fun θ _ => ?_
    ring
  rw [hsplit, integral_const_mul, integral_box_cubForm_zero δ (r/2), mul_zero, add_zero]

theorem integrable_box_bound (d : ℕ) (R : ℝ) {lam : ℝ} (hl : 0 < lam) :
    Integrable (fun θ : Fin d → ℝ =>
      (kOne d/2 * R^2 * (sqNorm θ)^3 + kTwo d * R * (sqNorm θ)^2)
        * Real.exp (-lam * sqNorm θ)) := by
  have h3 : Integrable (fun θ : Fin d → ℝ =>
      kOne d/2 * R^2 * ((sqNorm θ)^3 * Real.exp (-lam * sqNorm θ))) :=
    (integrable_pow_rgauss d 3 hl).const_mul _
  have h2 : Integrable (fun θ : Fin d → ℝ =>
      kTwo d * R * ((sqNorm θ)^2 * Real.exp (-lam * sqNorm θ))) :=
    (integrable_pow_rgauss d 2 hl).const_mul _
  have hBeq : (fun θ : Fin d → ℝ =>
      (kOne d/2 * R^2 * (sqNorm θ)^3 + kTwo d * R * (sqNorm θ)^2)
        * Real.exp (-lam * sqNorm θ))
      = fun θ : Fin d → ℝ => kOne d/2 * R^2 * ((sqNorm θ)^3 * Real.exp (-lam * sqNorm θ))
          + kTwo d * R * ((sqNorm θ)^2 * Real.exp (-lam * sqNorm θ)) := by
    funext θ; ring
  rw [hBeq]
  exact h3.add h2

/-- The two Gaussian moments occurring in the pointwise error both scale like
`R^{-d/2-1}`. -/
theorem gauss_moments_scaled (d : ℕ) {kap : ℝ} (hkap : 0 < kap) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      (∫ θ : Fin d → ℝ, (kOne d/2 * R^2 * (sqNorm θ)^3 + kTwo d * R * (sqNorm θ)^2)
          * Real.exp (-(R * kap/4) * sqNorm θ))
        ≤ C * R ^ (-((d:ℝ)/2) - 1) := by
  obtain ⟨C3, hC3, hm3⟩ := moment_bound d 3
  obtain ⟨C2, hC2, hm2⟩ := moment_bound d 2
  have hk4 : (0:ℝ) < kap/4 := by positivity
  refine ⟨kOne d/2 * C3 * (kap/4) ^ (-((d:ℝ) + 2*3)/2)
      + kTwo d * C2 * (kap/4) ^ (-((d:ℝ) + 2*2)/2), by
        have := kOne_nonneg d
        have := kTwo_nonneg d
        have h1 : (0:ℝ) < (kap/4) ^ (-((d:ℝ) + 2*3)/2) := Real.rpow_pos_of_pos hk4 _
        have h2 : (0:ℝ) < (kap/4) ^ (-((d:ℝ) + 2*2)/2) := Real.rpow_pos_of_pos hk4 _
        positivity, fun R hR => ?_⟩
  set lam : ℝ := R * kap/4 with hlam
  have hl : 0 < lam := by rw [hlam]; positivity
  have hI3 : Integrable (fun θ : Fin d → ℝ =>
      kOne d/2 * R^2 * ((sqNorm θ)^3 * Real.exp (-lam * sqNorm θ))) :=
    (integrable_pow_rgauss d 3 hl).const_mul _
  have hI2 : Integrable (fun θ : Fin d → ℝ =>
      kTwo d * R * ((sqNorm θ)^2 * Real.exp (-lam * sqNorm θ))) :=
    (integrable_pow_rgauss d 2 hl).const_mul _
  have hsplit : (∫ θ : Fin d → ℝ, (kOne d/2 * R^2 * (sqNorm θ)^3 + kTwo d * R * (sqNorm θ)^2)
          * Real.exp (-lam * sqNorm θ))
      = kOne d/2 * R^2 * (∫ θ : Fin d → ℝ, (sqNorm θ)^3 * Real.exp (-lam * sqNorm θ))
        + kTwo d * R * (∫ θ : Fin d → ℝ, (sqNorm θ)^2 * Real.exp (-lam * sqNorm θ)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hI3 hI2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    ring
  rw [hsplit]
  have hA : (0:ℝ) ≤ kOne d/2 * R^2 := by have := kOne_nonneg d; positivity
  have hB : (0:ℝ) ≤ kTwo d * R := by have := kTwo_nonneg d; positivity
  have h3 := mul_le_mul_of_nonneg_left (hm3 lam hl) hA
  have h2 := mul_le_mul_of_nonneg_left (hm2 lam hl) hB
  have hlampow : ∀ t : ℝ, lam ^ t = (kap/4) ^ t * R ^ t := by
    intro t
    rw [hlam, show R * kap/4 = (kap/4) * R by ring, Real.mul_rpow hk4.le hR.le]
  have hRpow3 : R^2 * R ^ (-((d:ℝ) + 2*3)/2) = R ^ (-((d:ℝ)/2) - 1) := by
    rw [show (R:ℝ)^2 = R ^ (2:ℝ) by rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast],
      ← Real.rpow_add hR]
    congr 1
    ring
  have hRpow2 : R * R ^ (-((d:ℝ) + 2*2)/2) = R ^ (-((d:ℝ)/2) - 1) := by
    nth_rewrite 1 [show (R:ℝ) = R ^ (1:ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hR]
    congr 1
    ring
  calc kOne d/2 * R^2 * (∫ θ : Fin d → ℝ, (sqNorm θ)^3 * Real.exp (-lam * sqNorm θ))
        + kTwo d * R * (∫ θ : Fin d → ℝ, (sqNorm θ)^2 * Real.exp (-lam * sqNorm θ))
      ≤ kOne d/2 * R^2 * (C3 * lam ^ (-((d:ℝ) + 2*3)/2))
        + kTwo d * R * (C2 * lam ^ (-((d:ℝ) + 2*2)/2)) := by linarith
    _ = (kOne d/2 * C3 * (kap/4) ^ (-((d:ℝ) + 2*3)/2)) * (R^2 * R ^ (-((d:ℝ) + 2*3)/2))
        + (kTwo d * C2 * (kap/4) ^ (-((d:ℝ) + 2*2)/2)) * (R * R ^ (-((d:ℝ) + 2*2)/2)) := by
          rw [hlampow, hlampow]; ring
    _ = (kOne d/2 * C3 * (kap/4) ^ (-((d:ℝ) + 2*3)/2)
        + kTwo d * C2 * (kap/4) ^ (-((d:ℝ) + 2*2)/2)) * R ^ (-((d:ℝ)/2) - 1) := by
          rw [hRpow3, hRpow2]; ring

/-- Integrating the pointwise Laplace estimate over the box. -/
theorem box_error_bound {d : ℕ} (hd : 2 ≤ d) {δ R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδd : (d:ℝ) * δ ≤ 1) (hδc : δ * cOne d ≤ Real.cos (alpha (d+1))/4) (hR : 0 < R) :
    ‖(∫ θ in box d δ, Complex.exp (rr (d+1) R * (torusPhase θ - ((d:ℂ)+1))))
      - ∫ θ in box d δ, (Complex.exp (-(rr (d+1) R/2) * ((quadForm θ:ℝ):ℂ))
          * (1 + -I * rr (d+1) R * ((cubForm θ:ℝ):ℂ)/6))‖
      ≤ ∫ θ : Fin d → ℝ, (kOne d/2 * R^2 * (sqNorm θ)^3 + kTwo d * R * (sqNorm θ)^2)
          * Real.exp (-(R * Real.cos (alpha (d+1))/4) * sqNorm θ) := by
  have hk : 0 < Real.cos (alpha (d+1)) := cos_alpha_pos (by omega)
  have hl : 0 < R * Real.cos (alpha (d+1))/4 := by positivity
  set F : (Fin d → ℝ) → ℂ :=
    fun θ => Complex.exp (rr (d+1) R * (torusPhase θ - ((d:ℂ)+1))) with hF
  set G : (Fin d → ℝ) → ℂ :=
    fun θ => Complex.exp (-(rr (d+1) R/2) * ((quadForm θ:ℝ):ℂ))
        * (1 + -I * rr (d+1) R * ((cubForm θ:ℝ):ℂ)/6) with hG
  have hcompact : IsCompact (box d δ) := isCompact_univ_pi fun _ => isCompact_Icc
  have hcF : Continuous F := by
    rw [hF]
    exact Complex.continuous_exp.comp (continuous_const.mul
      (continuous_torusPhase.sub continuous_const))
  have hcG : Continuous G := by
    rw [hG]
    refine (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_quadForm))).mul ?_
    refine continuous_const.add ((continuous_const.mul
      (Complex.continuous_ofReal.comp ?_)).div_const _)
    unfold cubForm coordSum
    fun_prop
  have hIF : IntegrableOn F (box d δ) := hcF.continuousOn.integrableOn_compact hcompact
  have hIG : IntegrableOn G (box d δ) := hcG.continuousOn.integrableOn_compact hcompact
  have hIB := integrable_box_bound d R hl
  rw [show (∫ θ in box d δ, F θ) - (∫ θ in box d δ, G θ)
      = ∫ θ in box d δ, (F θ - G θ) from (integral_sub hIF hIG).symm]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hstep1 : (∫ θ in box d δ, ‖F θ - G θ‖)
      ≤ ∫ θ in box d δ, (kOne d/2 * R^2 * (sqNorm θ)^3 + kTwo d * R * (sqNorm θ)^2)
          * Real.exp (-(R * Real.cos (alpha (d+1))/4) * sqNorm θ) := by
    refine setIntegral_mono_on ((hIF.sub hIG).norm) hIB.integrableOn
      (measurableSet_box d δ) fun θ hθ => ?_
    have hθb : ∀ j, |θ j| ≤ δ := by
      intro j
      have := hθ j (Set.mem_univ j)
      rw [Set.mem_Icc] at this
      rw [abs_le]
      exact ⟨this.1, this.2⟩
    exact local_pointwise hd hδ hδ1 hδd hδc hR hθb
  refine le_trans hstep1 (setIntegral_le_integral hIB
    (Filter.Eventually.of_forall fun θ => ?_))
  have := kOne_nonneg d
  have := kTwo_nonneg d
  have hs := sqNorm_nonneg θ
  positivity

/-- Completing the truncated Gaussian to the full space costs `O(R^{-d/2-1})`. -/
theorem gauss_tail_scaled {d : ℕ} (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧ ∀ R : ℝ, R0 ≤ R →
      ‖(∫ θ in box d δ, Complex.exp (-(rr (d+1) R/2) * ((quadForm θ:ℝ):ℂ)))
        - ∫ θ : Fin d → ℝ, Complex.exp (-(rr (d+1) R/2) * ((quadForm θ:ℝ):ℂ))‖
        ≤ C * R ^ (-((d:ℝ)/2) - 1) := by
  have hk : 0 < Real.cos (alpha (d+1)) := cos_alpha_pos (by omega)
  obtain ⟨Ct, hCt, htail⟩ := gauss_tail_bound d hδ
  obtain ⟨R1, hR1, hexp⟩ :=
    exists_exp_neg_le_rpow (η := Real.cos (alpha (d+1)) * δ^2/4) (s := (d:ℝ)/2 + 1) (by positivity)
  refine ⟨Ct, max (max 1 (2/Real.cos (alpha (d+1)))) R1, hCt,
    le_trans (le_max_left _ _) (le_max_left _ _), fun R hR => ?_⟩
  have hR1' : (1:ℝ) ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRpos : (0:ℝ) < R := by linarith
  have hRk : 2/Real.cos (alpha (d+1)) ≤ R :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hlam1 : (1:ℝ) ≤ R * Real.cos (alpha (d+1))/2 := by
    rw [div_le_iff₀ hk] at hRk
    linarith
  have hbre : 0 < (rr (d+1) R/2).re := by rw [rr_half_re]; positivity
  have hint : Integrable (fun θ : Fin d → ℝ =>
      Complex.exp (-(rr (d+1) R/2) * ((quadForm θ:ℝ):ℂ))) := integrable_cgauss d hbre
  have hsplit := integral_add_compl (measurableSet_box d δ) hint
  rw [show (∫ θ in box d δ, Complex.exp (-(rr (d+1) R/2) * ((quadForm θ:ℝ):ℂ)))
      - ∫ θ : Fin d → ℝ, Complex.exp (-(rr (d+1) R/2) * ((quadForm θ:ℝ):ℂ))
      = -(∫ θ in (box d δ)ᶜ, Complex.exp (-(rr (d+1) R/2) * ((quadForm θ:ℝ):ℂ))) by
    rw [← hsplit]; ring, norm_neg]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hstep : (∫ θ in (box d δ)ᶜ, ‖Complex.exp (-(rr (d+1) R/2) * ((quadForm θ:ℝ):ℂ))‖)
      ≤ ∫ θ in (box d δ)ᶜ, Real.exp (-(R * Real.cos (alpha (d+1))/2) * sqNorm θ) := by
    refine setIntegral_mono_on hint.norm.integrableOn
      (integrable_rgauss d (lam := R * Real.cos (alpha (d+1))/2) (by positivity)).integrableOn
      (measurableSet_box d δ).compl fun θ _ => ?_
    rw [norm_cexp_quadForm, rr_half_re]
    exact Real.exp_le_exp.2 (by nlinarith [sqNorm_le_quadForm θ])
  refine le_trans hstep ?_
  refine le_trans (htail (R * Real.cos (alpha (d+1))/2) hlam1) ?_
  have hkey : Real.exp (-(R * Real.cos (alpha (d+1))/2) * δ^2/2) ≤ R ^ (-((d:ℝ)/2) - 1) := by
    have hR1R := hexp R (le_trans (le_max_right _ _) hR)
    calc Real.exp (-(R * Real.cos (alpha (d+1))/2) * δ^2/2)
        = Real.exp (-(Real.cos (alpha (d+1)) * δ^2/4 * R)) := by congr 1; ring
      _ ≤ R ^ (-((d:ℝ)/2 + 1)) := hR1R
      _ = R ^ (-((d:ℝ)/2) - 1) := by congr 1; ring
  exact mul_le_mul_of_nonneg_left hkey hCt

/-- **The local Laplace estimate at the dominant saddle.**  For every sufficiently small
box radius `δ`, the integral over `[-δ,δ]^d` equals `mainTerm` up to a relative error
`O(1/R)`. -/
theorem local_estimate {d : ℕ} (hd : 2 ≤ d) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
      ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧ ∀ R : ℝ, R0 ≤ R →
        ‖(∫ θ in box d δ, Complex.exp (rr (d+1) R * torusPhase θ)) - mainTerm d R‖
          ≤ C * Real.exp (((d : ℝ)+1) * R * Real.cos (alpha (d+1))) * R ^ (-((d : ℝ)/2) - 1) := by
  have hk : 0 < Real.cos (alpha (d+1)) := cos_alpha_pos (by omega)
  have hc1 : 0 < cOne d := cOne_pos d
  have hdpos : (0:ℝ) < d := by
    have : (2:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨min 1 (min (1/(d:ℝ)) (Real.cos (alpha (d+1))/(4*cOne d))), by positivity,
    fun δ hδ hδ0 => ?_⟩
  have hδ1 : δ ≤ 1 := le_trans hδ0 (min_le_left _ _)
  have hδd : (d:ℝ) * δ ≤ 1 := by
    have h : δ ≤ 1/(d:ℝ) := le_trans hδ0 (le_trans (min_le_right _ _) (min_le_left _ _))
    rw [le_div_iff₀ hdpos] at h
    linarith
  have hδc : δ * cOne d ≤ Real.cos (alpha (d+1))/4 := by
    have h : δ ≤ Real.cos (alpha (d+1))/(4*cOne d) :=
      le_trans hδ0 (le_trans (min_le_right _ _) (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  obtain ⟨C1, hC1, hmom⟩ := gauss_moments_scaled d hk
  obtain ⟨C2, R2, hC2, hR2, htail⟩ := gauss_tail_scaled hd hδ
  refine ⟨C1 + C2, R2, by linarith, hR2, fun R hR => ?_⟩
  have hRpos : (0:ℝ) < R := by linarith
  set r := rr (d+1) R with hr
  have hkey : (∫ θ in box d δ, Complex.exp (r * torusPhase θ)) - mainTerm d R
      = Complex.exp (r * ((d:ℂ)+1)) *
          (((∫ θ in box d δ, Complex.exp (r * (torusPhase θ - ((d:ℂ)+1))))
            - ∫ θ in box d δ, (Complex.exp (-(r/2) * ((quadForm θ:ℝ):ℂ))
                * (1 + -I * r * ((cubForm θ:ℝ):ℂ)/6)))
          + ((∫ θ in box d δ, Complex.exp (-(r/2) * ((quadForm θ:ℝ):ℂ)))
            - ∫ θ : Fin d → ℝ, Complex.exp (-(r/2) * ((quadForm θ:ℝ):ℂ)))) := by
    rw [integral_box_factor δ R, mainTerm_eq_gauss hd hRpos, integral_box_model δ r]
    ring
  rw [hkey, norm_mul, norm_exp_saddle d R]
  have hbnd : ‖(((∫ θ in box d δ, Complex.exp (r * (torusPhase θ - ((d:ℂ)+1))))
            - ∫ θ in box d δ, (Complex.exp (-(r/2) * ((quadForm θ:ℝ):ℂ))
                * (1 + -I * r * ((cubForm θ:ℝ):ℂ)/6)))
          + ((∫ θ in box d δ, Complex.exp (-(r/2) * ((quadForm θ:ℝ):ℂ)))
            - ∫ θ : Fin d → ℝ, Complex.exp (-(r/2) * ((quadForm θ:ℝ):ℂ))))‖
      ≤ (C1 + C2) * R ^ (-((d:ℝ)/2) - 1) := by
    refine le_trans (norm_add_le _ _) ?_
    have h1 := le_trans (box_error_bound hd hδ hδ1 hδd hδc hRpos) (hmom R hRpos)
    have h2 := htail R hR
    rw [add_mul]
    exact add_le_add h1 h2
  calc Real.exp (((d:ℝ)+1) * R * Real.cos (alpha (d+1))) * _
      ≤ Real.exp (((d:ℝ)+1) * R * Real.cos (alpha (d+1))) * ((C1 + C2) * R ^ (-((d:ℝ)/2) - 1)) :=
        mul_le_mul_of_nonneg_left hbnd (Real.exp_pos _).le
    _ = (C1 + C2) * Real.exp (((d:ℝ)+1) * R * Real.cos (alpha (d+1))) * R ^ (-((d:ℝ)/2) - 1) := by
        ring

end Q776
