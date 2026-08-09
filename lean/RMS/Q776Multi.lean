import RMS.Q776Defs

/-!
# Q776 — the torus representation

Iterating the Hadamard product formula `Q776.hadamard` gives the exact `d`-dimensional
torus representation

`(2π)^d * f (d+1) (r^(d+1)) = ∫_{[-π,π]^d} exp (r * S θ) dθ`,

where `S θ = ∑_j exp (i θ_j) + exp (-i ∑_j θ_j)`.

This module sets up the notation (`Q776.coordSum`, `Q776.torusPhase`, `Q776.cube`,
`Q776.box`, `Q776.quadForm`, `Q776.cubForm`, `Q776.gfun`, `Q776.rr`) and proves the
representation.
-/

open scoped Real Nat
open Complex MeasureTheory

namespace Q776

/-- The sum of the coordinates of `θ : Fin d → ℝ`. -/
noncomputable def coordSum {d : ℕ} (θ : Fin d → ℝ) : ℝ := ∑ j, θ j

/-- The phase of the torus representation: `S θ = ∑_j e^{iθ_j} + e^{-i ∑_j θ_j}`. -/
noncomputable def torusPhase {d : ℕ} (θ : Fin d → ℝ) : ℂ :=
  (∑ j, Complex.exp ((θ j : ℂ) * I)) + Complex.exp (-((coordSum θ : ℝ) : ℂ) * I)

/-- The cube `[-π, π]^d`. -/
def cube (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi fun _ => Set.Icc (-π) π

/-- The box `[-δ, δ]^d`. -/
def box (d : ℕ) (δ : ℝ) : Set (Fin d → ℝ) := Set.univ.pi fun _ => Set.Icc (-δ) δ

/-- The quadratic form `Q θ = ∑_j θ_j² + (∑_j θ_j)²` appearing in the Taylor expansion
of the phase at the dominant saddle. -/
noncomputable def quadForm {d : ℕ} (θ : Fin d → ℝ) : ℝ := (∑ j, (θ j)^2) + (coordSum θ)^2

/-- The cubic form `∑_j θ_j³ - (∑_j θ_j)³` appearing in the Taylor expansion of the phase. -/
noncomputable def cubForm {d : ℕ} (θ : Fin d → ℝ) : ℝ := (∑ j, (θ j)^3) - (coordSum θ)^3

/-- The squared euclidean norm `∑_j θ_j²`. -/
noncomputable def sqNorm {d : ℕ} (θ : Fin d → ℝ) : ℝ := ∑ j, (θ j)^2

/-- The real part of `r S θ` divided by `R`, for `r = R e^{iπ/m}`. -/
noncomputable def gfun (m : ℕ) {d : ℕ} (θ : Fin d → ℝ) : ℝ :=
  (∑ j, Real.cos (θ j + alpha m)) + Real.cos (alpha m - coordSum θ)

/-- The dominant saddle direction `r = R e^{iπ/m}`. -/
noncomputable def rr (m : ℕ) (R : ℝ) : ℂ := (R : ℂ) * Complex.exp (((alpha m : ℝ) : ℂ) * I)

section Basic

theorem rr_pow {m : ℕ} (hm : 1 ≤ m) (R : ℝ) : (rr m R) ^ m = -((R : ℂ) ^ m) := by
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [rr, mul_pow, ← Complex.exp_nat_mul]
  have h1 : (m : ℂ) * (((alpha m : ℝ) : ℂ) * I) = ((π : ℝ) : ℂ) * I := by
    simp only [alpha]
    push_cast
    field_simp
  rw [h1]
  have : Complex.exp (((π : ℝ) : ℂ) * I) = -1 := by
    exact_mod_cast Complex.exp_pi_mul_I
  rw [this]
  ring

theorem rr_re (m : ℕ) (R : ℝ) : (rr m R).re = R * Real.cos (alpha m) := by
  rw [rr, Complex.exp_mul_I]
  simp [Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem rr_im (m : ℕ) (R : ℝ) : (rr m R).im = R * Real.sin (alpha m) := by
  rw [rr, Complex.exp_mul_I]
  simp [Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem norm_rr (m : ℕ) {R : ℝ} (hR : 0 ≤ R) : ‖rr m R‖ = R := by
  rw [rr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR, Complex.norm_exp]
  simp

/-- The real part of `r S θ` for `r = R e^{iπ/m}`. -/
theorem re_rr_mul_torusPhase (m : ℕ) (R : ℝ) {d : ℕ} (θ : Fin d → ℝ) :
    (rr m R * torusPhase θ).re = R * gfun m θ := by
  have key : ∀ t : ℝ, (rr m R * Complex.exp ((t : ℂ) * I)).re = R * Real.cos (t + alpha m) := by
    intro t
    rw [rr, mul_assoc, ← Complex.exp_add]
    have : ((alpha m : ℝ) : ℂ) * I + (t : ℂ) * I = (((t + alpha m : ℝ)) : ℂ) * I := by
      push_cast; ring
    rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [torusPhase, mul_add, Complex.add_re, Finset.mul_sum, Complex.re_sum]
  have h2 : (rr m R * Complex.exp (-((coordSum θ : ℝ) : ℂ) * I)).re
      = R * Real.cos (alpha m - coordSum θ) := by
    have := key (-(coordSum θ))
    rw [show ((-(coordSum θ) : ℝ) : ℂ) = -((coordSum θ : ℝ) : ℂ) by push_cast; ring] at this
    rw [this, show -coordSum θ + alpha m = alpha m - coordSum θ by ring]
  rw [h2, gfun, mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => key (θ j)

/-- The amplitude rewritten with the exponent `d = m - 1`. -/
theorem amplitude_succ (d : ℕ) (R : ℝ) :
    amplitude (d+1) R
      = 2 * (2*π) ^ (-(d:ℝ)/2) / Real.sqrt (d+1) * R ^ (-(d:ℝ)/2)
          * Real.exp (((d:ℝ)+1) * R * Real.cos (alpha (d+1))) := by
  unfold amplitude
  push_cast
  ring_nf

/-- `π/m ≤ π/3` for `m ≥ 3`. -/
theorem alpha_le_pi_div_three {m : ℕ} (hm : 3 ≤ m) : alpha m ≤ π/3 := by
  have h3 : (3:ℝ) ≤ m := by exact_mod_cast hm
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) h3

end Basic

/-! ## Periodicity and the Hadamard step -/

theorem coordSum_cons {d : ℕ} (t : ℝ) (u : Fin d → ℝ) :
    coordSum (Fin.cons t u : Fin (d+1) → ℝ) = t + coordSum u := by
  rw [coordSum, coordSum, Fin.sum_univ_succ]
  simp

theorem periodic_shift_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} (hp : Function.Periodic F (2*π)) (a : ℝ) :
    (∫ t in (-π)..π, F (t + a)) = ∫ t in (-π)..π, F t := by
  rw [intervalIntegral.integral_comp_add_right F a]
  have h := hp.intervalIntegral_add_eq (-π + a) (-π)
  rw [show -π + a + 2*π = π + a by ring, show -π + 2*π = π by ring] at h
  exact h

theorem periodic_exp_circle (c : ℂ) :
    Function.Periodic (fun t : ℝ => Complex.exp (c * Complex.exp ((t:ℂ) * I))) (2*π) := by
  intro t
  simp only
  congr 2
  rw [show ((t + 2*π : ℝ) : ℂ) * I = (t:ℂ)*I + ((2*π : ℝ) : ℂ)*I by push_cast; ring,
    Complex.exp_add]
  norm_num

theorem integral_exp_circle (r : ℂ) :
    (∫ t in (-π)..π, Complex.exp (r * Complex.exp ((t:ℂ) * I))) = 2*π := by
  have hpi := Real.pi_pos
  rcases eq_or_ne r 0 with rfl | hr
  · simp
    ring
  · have hrho : 0 < ‖r‖ := norm_pos_iff.2 hr
    have hh := hadamard (m := 1) le_rfl hrho 0
    simp only [f_one, zero_div, zero_mul, Complex.exp_zero, mul_one] at hh
    rw [f_zero] at hh
    have hpolar : ((‖r‖ : ℝ) : ℂ) * Complex.exp ((r.arg : ℂ) * I) = r :=
      Complex.norm_mul_exp_arg_mul_I r
    have hgoal : ∀ t : ℝ, Complex.exp (r * Complex.exp ((t:ℂ) * I))
        = (fun s : ℝ => Complex.exp ((‖r‖ : ℂ) * Complex.exp ((s:ℂ) * I))) (t + r.arg) := by
      intro t
      simp only
      congr 1
      rw [show ((t + r.arg : ℝ) : ℂ) * I = ((r.arg : ℝ) : ℂ)*I + (t:ℂ)*I by push_cast; ring,
        Complex.exp_add, ← mul_assoc, hpolar]
    rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      (fun s : ℝ => Complex.exp ((‖r‖ : ℂ) * Complex.exp ((s:ℂ) * I))) (t + r.arg))
      (fun t _ => hgoal t)]
    rw [periodic_shift_integral (periodic_exp_circle ((‖r‖ : ℝ) : ℂ)) r.arg]
    rw [show ((‖r‖:ℝ) : ℂ) = ((‖r‖ : ℂ)) from rfl] at hh
    rw [hh]
    push_cast
    ring

/-- `θ ↦ e^{iθ}` is `2π`-periodic. -/
theorem exp_circle_period (s : ℝ) :
    Complex.exp (((s + 2*π : ℝ) : ℂ) * I) = Complex.exp ((s:ℂ) * I) := by
  rw [show ((s + 2*π : ℝ) : ℂ) * I = (s:ℂ)*I + (2*(π:ℝ))*I by push_cast; ring, Complex.exp_add,
    show ((2*(π:ℝ) : ℂ))*I = 2*(π:ℝ)*I by push_cast; ring, Complex.exp_two_pi_mul_I, mul_one]

theorem exp_circle_period_neg (s : ℝ) :
    Complex.exp (-(((s + 2*π : ℝ) : ℂ) * I)) = Complex.exp (-((s:ℂ) * I)) := by
  rw [Complex.exp_neg, Complex.exp_neg, exp_circle_period]

/-- One step of the Hadamard recursion, in the form needed for the torus representation. -/
theorem hadamard_step {m : ℕ} (hm : 1 ≤ m) (c r : ℂ) :
    (∫ t in (-π)..π, f m (c * Complex.exp (-((t:ℂ)*I))) * Complex.exp (r * Complex.exp ((t:ℂ)*I)))
      = 2*π*f (m+1) (r*c) := by
  have hpi := Real.pi_pos
  set H : ℝ → ℂ := fun t =>
    f m (c * Complex.exp ((t:ℂ)*I)) * Complex.exp (r * Complex.exp (-((t:ℂ)*I))) with hH
  have hrefl : (∫ t in (-π)..π, f m (c * Complex.exp (-((t:ℂ)*I)))
      * Complex.exp (r * Complex.exp ((t:ℂ)*I))) = ∫ t in (-π)..π, H t := by
    have h := intervalIntegral.integral_comp_neg (a := -π) (b := π) H
    rw [neg_neg] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hH]
    push_cast
    ring_nf
  rw [hrefl]
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [hH, zero_mul, f_zero, one_mul, mul_zero]
    have h1 : (∫ t in (-π)..π, Complex.exp (r * Complex.exp (-((t:ℂ)*I))))
        = ∫ t in (-π)..π, Complex.exp (r * Complex.exp ((t:ℂ)*I)) := by
      have h := intervalIntegral.integral_comp_neg (a := -π) (b := π)
        (fun t : ℝ => Complex.exp (r * Complex.exp ((t:ℂ)*I)))
      rw [neg_neg] at h
      rw [← h]
      refine intervalIntegral.integral_congr fun t _ => ?_
      push_cast
      ring_nf
    rw [h1, integral_exp_circle]
    ring
  · have hrho : 0 < ‖c‖ := norm_pos_iff.2 hc
    have hrhone : ((‖c‖:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hrho)
    have hpolar : ((‖c‖ : ℝ) : ℂ) * Complex.exp ((c.arg : ℂ) * I) = c :=
      Complex.norm_mul_exp_arg_mul_I c
    have hinv : c * Complex.exp (-(((c.arg:ℝ):ℂ)*I)) = ((‖c‖:ℝ):ℂ) := by
      conv_lhs => rw [← hpolar]
      rw [mul_assoc, ← Complex.exp_add]
      simp
    set F : ℝ → ℂ := fun s => f m (((‖c‖:ℝ):ℂ) * Complex.exp ((s:ℂ)*I))
      * Complex.exp ((r*c)/((‖c‖:ℝ):ℂ) * Complex.exp (-((s:ℂ)*I))) with hF
    have hper : Function.Periodic F (2*π) := by
      intro s
      simp only [hF, exp_circle_period, exp_circle_period_neg]
    have hshift : ∀ t : ℝ, H t = F (t + c.arg) := by
      intro t
      simp only [hH, hF]
      congr 2
      · rw [show ((t + c.arg : ℝ) : ℂ) * I = ((c.arg : ℝ) : ℂ)*I + (t:ℂ)*I by push_cast; ring,
          Complex.exp_add, ← mul_assoc, hpolar]
      · rw [show (-(((t + c.arg : ℝ):ℂ) * I)) = -(((c.arg:ℝ):ℂ)*I) + -((t:ℂ)*I) by push_cast; ring,
          Complex.exp_add, ← mul_assoc]
        congr 1
        rw [div_mul_eq_mul_div, mul_assoc, hinv]
        field_simp
    rw [intervalIntegral.integral_congr (g := fun t => F (t + c.arg)) (fun t _ => hshift t),
      periodic_shift_integral hper c.arg]
    have hh := hadamard hm hrho (r*c)
    rw [hF]
    exact hh

/-! ## Fubini on the cube -/

theorem integral_pi_cons {d : ℕ} (ν : Measure ℝ) [IsFiniteMeasure ν] (F : (Fin (d+1) → ℝ) → ℂ)
    (hF : Integrable F (Measure.pi fun _ => ν)) :
    (∫ θ, F θ ∂(Measure.pi fun _ : Fin (d+1) => ν))
      = ∫ t, (∫ θ' , F (Fin.cons t θ') ∂(Measure.pi fun _ : Fin d => ν)) ∂ν := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (d+1) => ν) 0
  have he : MeasurableEmbedding (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).measurableEmbedding
  have he' : MeasurableEmbedding
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm.measurableEmbedding
  have h1 := hmp.integral_comp he
    (fun p : ℝ × (Fin d → ℝ) =>
      F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm p))
  simp only [MeasurableEquiv.symm_apply_apply] at h1
  rw [h1]
  have hint : Integrable
      (fun p : ℝ × (Fin d → ℝ) =>
        F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm p))
      (ν.prod (Measure.pi fun _ : Fin d => ν)) :=
    (hmp.symm.integrable_comp_emb he').2 hF
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hsymm : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm (t, u)
      = Fin.cons t u := by
    ext j; simp [MeasurableEquiv.piFinSuccAbove]
  dsimp only
  rw [hsymm]

theorem restrict_cube (d : ℕ) :
    (volume : Measure (Fin d → ℝ)).restrict (cube d)
      = Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict (Set.Icc (-π) π) := by
  rw [cube, show (volume : Measure (Fin d → ℝ)) = Measure.pi (fun _ => volume) from rfl,
    Measure.restrict_pi_pi]

theorem setIntegral_cube_cons {d : ℕ} (F : (Fin (d+1) → ℝ) → ℂ) (hF : Continuous F) :
    (∫ θ in cube (d+1), F θ) = ∫ t in Set.Icc (-π) π, ∫ θ' in cube d, F (Fin.cons t θ') := by
  have hpi := Real.pi_pos
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Icc (-π) π)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hint : Integrable F (Measure.pi fun _ : Fin (d+1) =>
      (volume : Measure ℝ).restrict (Set.Icc (-π) π)) := by
    rw [← restrict_cube (d+1)]
    exact hF.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)
  rw [show (∫ θ in cube (d+1), F θ)
      = ∫ θ, F θ ∂(Measure.pi fun _ : Fin (d+1) =>
        (volume : Measure ℝ).restrict (Set.Icc (-π) π)) by rw [← restrict_cube (d+1)],
    integral_pi_cons _ F hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  rw [← restrict_cube d]

/-! ## The torus representation -/

/-- The `d`-dimensional torus integral, in the two-parameter form which is stable under
the Hadamard recursion. -/
theorem torus_integral (d : ℕ) (r w : ℂ) :
    (∫ θ in cube d, Complex.exp (r * (∑ j, Complex.exp ((θ j : ℂ) * I))
        + w * Complex.exp (-((coordSum θ : ℝ) : ℂ) * I)))
      = (2*π)^d * f (d+1) (r^d * w) := by
  have hpi := Real.pi_pos
  induction d generalizing w with
  | zero =>
      simp only [cube, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, coordSum,
        Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one, zero_add,
        pow_zero, one_mul, integral_const]
      rw [measureReal_def, Measure.restrict_apply_univ,
        show ((volume : Measure (Fin 0 → ℝ)) (Set.univ.pi fun _ => Set.Icc (-π) π)) = 1 by
        rw [show (volume : Measure (Fin 0 → ℝ)) = Measure.pi (fun _ => volume) from rfl,
          Measure.pi_pi]
        simp]
      rw [f_one]
      simp
  | succ d ih =>
      set G : (Fin (d+1) → ℝ) → ℂ := fun θ => Complex.exp (r * (∑ j, Complex.exp ((θ j : ℂ) * I))
        + w * Complex.exp (-((coordSum θ : ℝ) : ℂ) * I)) with hG
      have hGcont : Continuous G := by
        rw [hG]
        unfold coordSum
        fun_prop
      rw [setIntegral_cube_cons G hGcont]
      have hstep : ∀ t : ℝ, (∫ θ' in cube d, G (Fin.cons t θ'))
          = Complex.exp (r * Complex.exp ((t:ℂ)*I))
            * ((2*π)^d * f (d+1) (r^d * (w * Complex.exp (-((t:ℂ)*I))))) := by
        intro t
        rw [← ih (w * Complex.exp (-((t:ℂ)*I))), ← integral_const_mul]
        refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Icc)
          fun u _ => ?_
        rw [hG]
        simp only [coordSum_cons, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
        rw [← Complex.exp_add]
        congr 1
        rw [show ((t + coordSum u : ℝ) : ℂ) = (t:ℂ) + ((coordSum u : ℝ) : ℂ) by push_cast; ring]
        rw [show -((t:ℂ) + ((coordSum u : ℝ) : ℂ)) * I
            = -((coordSum u : ℝ):ℂ) * I + -((t:ℂ)*I) by ring, Complex.exp_add]
        ring
      rw [setIntegral_congr_fun measurableSet_Icc (fun t _ => hstep t)]
      have hpull : (∫ t in Set.Icc (-π) π, Complex.exp (r * Complex.exp ((t:ℂ)*I))
            * ((2*π)^d * f (d+1) (r^d * (w * Complex.exp (-((t:ℂ)*I))))))
          = (2*π)^d * ∫ t in Set.Icc (-π) π,
              f (d+1) ((r^d * w) * Complex.exp (-((t:ℂ)*I)))
                * Complex.exp (r * Complex.exp ((t:ℂ)*I)) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
        rw [mul_assoc (r^d) w]
        ring
      rw [hpull]
      have hIcc : (∫ t in Set.Icc (-π) π,
            f (d+1) ((r^d * w) * Complex.exp (-((t:ℂ)*I)))
              * Complex.exp (r * Complex.exp ((t:ℂ)*I)))
          = ∫ t in (-π)..π, f (d+1) ((r^d * w) * Complex.exp (-((t:ℂ)*I)))
              * Complex.exp (r * Complex.exp ((t:ℂ)*I)) := by
        rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
      rw [hIcc, hadamard_step (m := d+1) (by omega) (r^d * w) r]
      rw [show r * (r^d * w) = r^(d+1) * w by ring]
      ring

/-- **The torus representation.** -/
theorem torus_rep (d : ℕ) (r : ℂ) :
    (∫ θ in cube d, Complex.exp (r * torusPhase θ)) = (2*π)^d * f (d+1) (r^(d+1)) := by
  have h := torus_integral d r r
  rw [show r ^ d * r = r ^ (d+1) by ring] at h
  rw [← h]
  refine setIntegral_congr_fun (by exact MeasurableSet.univ_pi fun _ => measurableSet_Icc)
    fun θ _ => ?_
  rw [torusPhase, mul_add]

end Q776
