import RMS.Q776Multi

/-!
# Q776 — multidimensional Gaussian integrals

The `d`-dimensional complex Gaussian integral attached to the quadratic form
`Q θ = ∑_j θ_j² + (∑_j θ_j)²` (whose matrix is `I + 𝟙𝟙ᵀ`, of determinant `d+1`):

`∫_{ℝ^d} exp (-b Q θ) dθ = ((π/b)^{1/2})^d / √(d+1)`  for `0 < Re b`,

together with the polynomial moment bounds and the Gaussian tail bounds needed for the
local saddle point analysis.
-/

open scoped Real Nat
open Complex MeasureTheory

namespace Q776


theorem sqNorm_nonneg {d : ℕ} (θ : Fin d → ℝ) : 0 ≤ sqNorm θ :=
  Finset.sum_nonneg fun j _ => sq_nonneg _

theorem sqNorm_le_quadForm {d : ℕ} (θ : Fin d → ℝ) : sqNorm θ ≤ quadForm θ := by
  have : (0:ℝ) ≤ (coordSum θ)^2 := sq_nonneg _
  simp only [quadForm, sqNorm]
  linarith

theorem norm_cexp_quadForm {d : ℕ} {b : ℂ} (θ : Fin d → ℝ) :
    ‖Complex.exp (-b * ((quadForm θ : ℝ) : ℂ))‖ = Real.exp (-b.re * quadForm θ) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]



theorem integral_fin_cons {d : ℕ} (F : (Fin (d+1) → ℝ) → ℂ) (hF : Integrable F) :
    ∫ θ : Fin (d+1) → ℝ, F θ = ∫ t : ℝ, ∫ θ' : Fin d → ℝ, F (Fin.cons t θ') := by
  have hmp := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0
  have he : MeasurableEmbedding (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).measurableEmbedding
  have h1 := hmp.integral_comp he
    (fun p : ℝ × (Fin d → ℝ) => F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm p))
  simp only [MeasurableEquiv.symm_apply_apply] at h1
  rw [h1]
  have he' : MeasurableEmbedding
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm.measurableEmbedding
  have hint : Integrable
      (fun p : ℝ × (Fin d → ℝ) =>
        F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm p)) volume :=
    (hmp.symm.integrable_comp_emb he').2 hF
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hsymm : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm (t, u)
      = Fin.cons t u := by
    ext j; simp [MeasurableEquiv.piFinSuccAbove]
  dsimp only
  rw [hsymm]

theorem integral_fin_cons' {d : ℕ} (F : (Fin (d+1) → ℝ) → ℂ) (hF : Integrable F) :
    ∫ θ : Fin (d+1) → ℝ, F θ = ∫ u : Fin d → ℝ, ∫ t : ℝ, F (Fin.cons t u) := by
  rw [integral_fin_cons F hF]
  refine integral_integral_swap ?_
  have hmp := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0
  have he' : MeasurableEmbedding
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm.measurableEmbedding
  have hint : Integrable
      (fun p : ℝ × (Fin d → ℝ) =>
        F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm p)) volume :=
    (hmp.symm.integrable_comp_emb he').2 hF
  rw [Measure.volume_eq_prod] at hint
  refine hint.congr (Filter.Eventually.of_forall fun p => ?_)
  have hsymm : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm (p.1, p.2)
      = Fin.cons p.1 p.2 := by
    ext j; simp [MeasurableEquiv.piFinSuccAbove]
  simpa using congrArg F hsymm

theorem continuous_sqNorm {d : ℕ} : Continuous (fun θ : Fin d → ℝ => sqNorm θ) := by
  unfold sqNorm; fun_prop

theorem continuous_quadForm {d : ℕ} : Continuous (fun θ : Fin d → ℝ => quadForm θ) := by
  unfold quadForm coordSum; fun_prop

theorem sqNorm_smul {d : ℕ} (r : ℝ) (θ : Fin d → ℝ) : sqNorm (r • θ) = r^2 * sqNorm θ := by
  simp only [sqNorm, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

/-- Integrability of the real Gaussian on `ℝ^d`. -/
theorem integrable_rgauss (d : ℕ) {lam : ℝ} (hl : 0 < lam) :
    Integrable (fun θ : Fin d → ℝ => Real.exp (-lam * sqNorm θ)) := by
  have h : (fun θ : Fin d → ℝ => Real.exp (-lam * sqNorm θ))
      = fun θ : Fin d → ℝ => ∏ j, Real.exp (-lam * (θ j)^2) := by
    ext θ; rw [← Real.exp_sum, sqNorm]; congr 1; rw [Finset.mul_sum]
  rw [h, show (volume : Measure (Fin d → ℝ)) = Measure.pi (fun _ => volume) from rfl]
  exact Integrable.fintype_prod (f := fun (_ : Fin d) (x : ℝ) => Real.exp (-lam * x^2))
    (fun _ => by simpa using (integrable_exp_neg_mul_sq hl))

/-- A polynomial bound for the Gaussian: `t^p e^{-lam t} ≤ C e^{-lam t/2}` for `t ≥ 0`. -/
theorem pow_mul_exp_le (p : ℕ) {lam t : ℝ} (hl : 0 < lam) (ht : 0 ≤ t) :
    t^p * Real.exp (-lam * t) ≤ ((p ! : ℝ) * (2/lam)^p) * Real.exp (-(lam/2) * t) := by
  have hx : 0 ≤ lam * t / 2 := by positivity
  have h := Real.pow_div_factorial_le_exp (lam*t/2) hx p
  have hfac : (0:ℝ) < (p ! : ℝ) := by exact_mod_cast Nat.factorial_pos p
  have h2 : (lam*t/2)^p ≤ (p ! : ℝ) * Real.exp (lam*t/2) := by
    rw [div_le_iff₀ hfac] at h
    linarith [h]
  have h3 : (lam/2)^p * t^p = (lam*t/2)^p := by rw [← mul_pow]; ring_nf
  have hpow : (0:ℝ) < (lam/2)^p := by positivity
  have h4 : t^p ≤ ((p ! : ℝ) * (2/lam)^p) * Real.exp (lam*t/2) := by
    refine le_of_mul_le_mul_left ?_ hpow
    rw [show (lam/2)^p * (((p ! : ℝ) * (2/lam)^p) * Real.exp (lam*t/2))
        = ((lam/2)*(2/lam))^p * ((p ! : ℝ) * Real.exp (lam*t/2)) by rw [mul_pow]; ring,
      show (lam/2)*(2/lam) = 1 by field_simp]
    simpa [h3] using h2
  calc t^p * Real.exp (-lam*t)
      ≤ (((p ! : ℝ) * (2/lam)^p) * Real.exp (lam*t/2)) * Real.exp (-lam*t) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = ((p ! : ℝ) * (2/lam)^p) * Real.exp (-(lam/2)*t) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- Integrability of a polynomial multiple of the real Gaussian on `ℝ^d`. -/
theorem integrable_pow_rgauss (d p : ℕ) {lam : ℝ} (hl : 0 < lam) :
    Integrable (fun θ : Fin d → ℝ => (sqNorm θ)^p * Real.exp (-lam * sqNorm θ)) := by
  refine Integrable.mono' (g := fun θ : Fin d → ℝ =>
      ((p ! : ℝ) * (2/lam)^p) * Real.exp (-(lam/2) * sqNorm θ))
    (((integrable_rgauss d (lam := lam/2) (by linarith)).const_mul _)) ?_ ?_
  · exact ((continuous_sqNorm.pow p).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_sqNorm))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun θ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (sqNorm_nonneg θ) p) (Real.exp_pos _).le)]
    exact pow_mul_exp_le p hl (sqNorm_nonneg θ)

/-- Integrability of the complex Gaussian attached to `quadForm`. -/
theorem integrable_cgauss (d : ℕ) {b : ℂ} (hb : 0 < b.re) :
    Integrable (fun θ : Fin d → ℝ => Complex.exp (-b * ((quadForm θ : ℝ) : ℂ))) := by
  refine Integrable.mono' (g := fun θ : Fin d → ℝ => Real.exp (-b.re * sqNorm θ))
    (integrable_rgauss d hb) ?_ ?_
  · exact (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_quadForm))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun θ => ?_
    rw [Complex.norm_exp]
    have hre : (-b * ((quadForm θ : ℝ) : ℂ)).re = -b.re * quadForm θ := by
      simp [Complex.mul_re]
    rw [hre]
    show Real.exp (-b.re * quadForm θ) ≤ Real.exp (-b.re * sqNorm θ)
    apply Real.exp_le_exp.2
    have h1 : sqNorm θ ≤ quadForm θ := by
      have : (0:ℝ) ≤ (coordSum θ)^2 := sq_nonneg _
      simp only [quadForm, sqNorm]; linarith
    nlinarith [hb]

/-- Polynomial moments of the Gaussian on `ℝ^d`, with the exact scaling in `lam`. -/
theorem moment_bound (d p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam →
      (∫ θ : Fin d → ℝ, (sqNorm θ)^p * Real.exp (-lam * sqNorm θ))
        ≤ C * lam ^ (-((d : ℝ) + 2*p)/2) := by
  set I : ℝ := ∫ θ : Fin d → ℝ, (sqNorm θ)^p * Real.exp (-(1:ℝ) * sqNorm θ) with hI
  have hI0 : 0 ≤ I := by
    rw [hI]
    exact integral_nonneg fun θ =>
      mul_nonneg (pow_nonneg (sqNorm_nonneg θ) p) (Real.exp_pos _).le
  refine ⟨I, hI0, fun lam hl => ?_⟩
  set r : ℝ := (Real.sqrt lam)⁻¹ with hr
  have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.2 hl
  have hrpos : 0 < r := by positivity
  have hr2 : r^2 = lam⁻¹ := by
    rw [hr, inv_pow, Real.sq_sqrt hl.le]
  set F : (Fin d → ℝ) → ℝ := fun θ => (sqNorm θ)^p * Real.exp (-lam * sqNorm θ) with hF
  have hscale : ∀ θ : Fin d → ℝ, F (r • θ) = lam⁻¹^p * ((sqNorm θ)^p * Real.exp (-(1:ℝ) * sqNorm θ)) := by
    intro θ
    show (sqNorm (r • θ))^p * Real.exp (-lam * sqNorm (r • θ)) = _
    rw [sqNorm_smul, hr2, show -lam * (lam⁻¹ * sqNorm θ) = -(1:ℝ) * sqNorm θ by field_simp,
      mul_pow]
    ring
  have hcomp := Measure.integral_comp_smul (volume : Measure (Fin d → ℝ)) F r
  simp only [Module.finrank_fin_fun] at hcomp
  rw [show (∫ θ : Fin d → ℝ, F (r • θ)) = lam⁻¹^p * I by
    rw [hI, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hscale)] at hcomp
  have hrd : |(r ^ d)⁻¹| = (Real.sqrt lam)^d := by
    rw [hr, ← inv_pow, inv_inv, abs_of_nonneg (by positivity)]
  rw [hrd, smul_eq_mul] at hcomp
  -- hcomp : lam⁻¹^p * I = (√lam)^d * ∫ F
  have hsd : (0:ℝ) < (Real.sqrt lam)^d := by positivity
  have hval : (∫ θ : Fin d → ℝ, F θ) = lam⁻¹^p * I / (Real.sqrt lam)^d := by
    rw [eq_div_iff (ne_of_gt hsd)]
    linarith [hcomp]
  rw [hF] at hval
  rw [hval]
  have e1 : (lam⁻¹:ℝ)^p = lam ^ (-(p:ℝ)) := by
    rw [Real.rpow_neg hl.le, Real.rpow_natCast, inv_pow]
  have e2 : (Real.sqrt lam)^d = lam ^ ((d:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (lam ^ ((1:ℝ)/2)) d, ← Real.rpow_mul hl.le]
    ring_nf
  have hrpow : lam ^ (-((d : ℝ) + 2*p)/2) = lam⁻¹^p / (Real.sqrt lam)^d := by
    rw [e1, e2, ← Real.rpow_sub hl]
    congr 1
    ring
  rw [hrpow]
  exact le_of_eq (by ring)

/-- Outside the box `[-δ,δ]^d` one has `sqNorm θ ≥ δ²`. -/
theorem sq_le_sqNorm_of_not_mem_box {d : ℕ} {δ : ℝ} (hδ : 0 < δ) {θ : Fin d → ℝ}
    (hθ : θ ∉ box d δ) : δ^2 ≤ sqNorm θ := by
  rw [box, Set.mem_pi] at hθ
  push_neg at hθ
  obtain ⟨j, -, hj⟩ := hθ
  rw [Set.mem_Icc] at hj
  push_neg at hj
  have habs : δ < |θ j| := by
    rcases le_or_gt (-δ) (θ j) with h | h
    · have := hj h
      rw [abs_of_pos (by linarith)]
      linarith
    · rw [abs_of_neg (by linarith)]
      linarith
  have h1 : δ^2 ≤ (θ j)^2 := by
    have := sq_abs (θ j)
    nlinarith
  have h2 : (θ j)^2 ≤ sqNorm θ :=
    Finset.single_le_sum (f := fun k => (θ k)^2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  linarith

/-- The Gaussian tail outside the box `[-δ, δ]^d` is exponentially small. -/
theorem gauss_tail_bound (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 1 ≤ lam →
      (∫ θ in (box d δ)ᶜ, Real.exp (-lam * sqNorm θ)) ≤ C * Real.exp (-lam * δ^2/2) := by
  refine ⟨∫ θ : Fin d → ℝ, Real.exp (-(1/2 : ℝ) * sqNorm θ),
    integral_nonneg fun θ => (Real.exp_pos _).le, fun lam hlam => ?_⟩
  have hlam0 : (0:ℝ) < lam := by linarith
  have hmeas : MeasurableSet ((box d δ)ᶜ) :=
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc).compl
  have hint1 : IntegrableOn (fun θ : Fin d → ℝ => Real.exp (-lam * sqNorm θ)) ((box d δ)ᶜ) :=
    (integrable_rgauss d hlam0).integrableOn
  have hint2 : Integrable (fun θ : Fin d → ℝ =>
      Real.exp (-lam*δ^2/2) * Real.exp (-(1/2:ℝ) * sqNorm θ)) :=
    (integrable_rgauss d (lam := 1/2) (by norm_num)).const_mul _
  have hpt : ∀ θ ∈ (box d δ)ᶜ, Real.exp (-lam * sqNorm θ)
      ≤ Real.exp (-lam*δ^2/2) * Real.exp (-(1/2:ℝ) * sqNorm θ) := by
    intro θ hθ
    have hsq : δ^2 ≤ sqNorm θ := sq_le_sqNorm_of_not_mem_box hδ hθ
    have hnn : 0 ≤ sqNorm θ := sqNorm_nonneg θ
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  calc (∫ θ in (box d δ)ᶜ, Real.exp (-lam*sqNorm θ))
      ≤ ∫ θ in (box d δ)ᶜ, Real.exp (-lam*δ^2/2) * Real.exp (-(1/2:ℝ) * sqNorm θ) :=
        setIntegral_mono_on hint1 hint2.integrableOn hmeas hpt
    _ ≤ ∫ θ : Fin d → ℝ, Real.exp (-lam*δ^2/2) * Real.exp (-(1/2:ℝ) * sqNorm θ) :=
        setIntegral_le_integral hint2
          (Filter.Eventually.of_forall fun θ => by positivity)
    _ = (∫ θ : Fin d → ℝ, Real.exp (-(1/2 : ℝ) * sqNorm θ)) * Real.exp (-lam * δ^2/2) := by
        rw [integral_const_mul]; ring

/-! ## The complex Gaussian integral -/

theorem cpow_half_ofReal_mul {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) :
    ((r:ℂ) * z) ^ ((1:ℂ)/2) = ((Real.sqrt r : ℝ) : ℂ) * z ^ ((1:ℂ)/2) := by
  have hrne : ((r:ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hrne hz),
    Complex.log_ofReal_mul hr hz, Complex.ofReal_log hr.le, add_mul, Complex.exp_add,
    ← Complex.cpow_def_of_ne_zero hrne, ← Complex.cpow_def_of_ne_zero hz]
  congr 1
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr.le]
  norm_num

theorem sum_sq_cons {d : ℕ} (t : ℝ) (u : Fin d → ℝ) :
    ∑ j, ((Fin.cons t u : Fin (d+1) → ℝ) j)^2 = t^2 + ∑ j, (u j)^2 := by
  rw [Fin.sum_univ_succ]
  simp

theorem integrable_cgauss_gen (d : ℕ) {b : ℂ} (hb : 0 < b.re) {c : ℝ} (hc : 0 ≤ c) :
    Integrable (fun θ : Fin d → ℝ =>
      Complex.exp (-b * (((∑ j, (θ j)^2) + c * (coordSum θ)^2 : ℝ) : ℂ))) := by
  refine Integrable.mono' (g := fun θ : Fin d → ℝ => Real.exp (-b.re * sqNorm θ))
    (integrable_rgauss d hb) ?_ ?_
  · refine (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp ?_))).aestronglyMeasurable
    unfold coordSum
    fun_prop
  · refine Filter.Eventually.of_forall fun θ => ?_
    rw [Complex.norm_exp]
    have hre : ∀ X : ℝ, (-b * ((X : ℝ) : ℂ)).re = -b.re * X := by
      intro X; simp [Complex.mul_re]
    rw [hre]
    show Real.exp _ ≤ Real.exp _
    apply Real.exp_le_exp.2
    have h1 : (0:ℝ) ≤ c * (coordSum θ)^2 := by positivity
    have : sqNorm θ = ∑ j, (θ j)^2 := rfl
    nlinarith [hb]

/-- The complex Gaussian integral for the one-parameter family of quadratic forms
`∑_j θ_j² + c (∑_j θ_j)²`, `c ≥ 0`. -/
theorem integral_cgauss_gen (d : ℕ) {b : ℂ} (hb : 0 < b.re) :
    ∀ c : ℝ, 0 ≤ c →
      (∫ θ : Fin d → ℝ, Complex.exp (-b * (((∑ j, (θ j)^2) + c * (coordSum θ)^2 : ℝ) : ℂ)))
        = (((π : ℂ)/b) ^ ((1 : ℂ)/2))^d / ((Real.sqrt (1 + d*c) : ℝ) : ℂ) := by
  have hbne : b ≠ 0 := fun h => by simp [h] at hb
  have hpb : ((π:ℂ)/b) ≠ 0 := div_ne_zero (by exact_mod_cast Real.pi_ne_zero) hbne
  induction d with
  | zero =>
      intro c hc
      simp only [coordSum, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
        mul_zero, integral_const, pow_zero, Nat.cast_zero, zero_mul, add_zero]
      rw [measureReal_def, show ((volume : Measure (Fin 0 → ℝ)) Set.univ) = 1 by
        rw [show (volume : Measure (Fin 0 → ℝ)) = Measure.pi (fun _ => volume) from rfl,
          Measure.pi_univ]
        simp]
      simp
  | succ d ih =>
      intro c hc
      have h1c : (0:ℝ) < 1 + c := by linarith
      set B : ℂ := b * (((1+c : ℝ)) : ℂ) with hBdef
      have hB : 0 < B.re := by
        rw [hBdef, Complex.mul_re]
        simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        positivity
      set c' : ℝ := c/(1+c) with hc'def
      have hc' : 0 ≤ c' := by positivity
      set F : (Fin (d+1) → ℝ) → ℂ := fun θ =>
        Complex.exp (-b * (((∑ j, (θ j)^2) + c * (coordSum θ)^2 : ℝ) : ℂ)) with hFdef
      have hint : Integrable F := integrable_cgauss_gen (d+1) hb hc
      rw [integral_fin_cons' F hint]
      have hinner : ∀ u : Fin d → ℝ, (∫ t : ℝ, F (Fin.cons t u))
          = ((π:ℂ)/B)^((1:ℂ)/2) *
            Complex.exp (-b * (((∑ j, (u j)^2) + c' * (coordSum u)^2 : ℝ) : ℂ)) := by
        intro u
        have hsplit : ∀ t : ℝ, F (Fin.cons t u)
            = Complex.exp (-B * (((t + c*(coordSum u)/(1+c) : ℝ) : ℂ))^2)
              * Complex.exp (-b * (((∑ j, (u j)^2) + c' * (coordSum u)^2 : ℝ) : ℂ)) := by
          intro t
          rw [hFdef]
          simp only [sum_sq_cons, coordSum_cons]
          rw [← Complex.exp_add]
          congr 1
          rw [hBdef, hc'def]
          have h1cC : (1 + (c:ℂ)) ≠ 0 := by
            have h := Complex.ofReal_ne_zero.2 (ne_of_gt h1c)
            push_cast at h
            exact h
          push_cast
          field_simp
          ring
        have hshift : (∫ t : ℝ, Complex.exp (-B * (((t + c*(coordSum u)/(1+c) : ℝ) : ℂ))^2))
            = ∫ t : ℝ, Complex.exp (-B * ((t : ℝ) : ℂ)^2) := by
          have := integral_add_right_eq_self (μ := (volume : Measure ℝ))
            (fun x : ℝ => Complex.exp (-B * ((x : ℝ) : ℂ)^2)) (c*(coordSum u)/(1+c))
          simpa using this
        rw [integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_mul_const, hshift,
          integral_gaussian_complex hB]
      rw [integral_congr_ae (Filter.Eventually.of_forall hinner), integral_const_mul, ih c' hc']
      -- the algebra
      have hpiB : ((π:ℂ)/B) = (((1+c)⁻¹ : ℝ) : ℂ) * ((π:ℂ)/b) := by
        rw [hBdef]
        have h1cC : ((1+c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt h1c)
        push_cast
        field_simp
      have hsq1 : Real.sqrt ((1+c)⁻¹) = (Real.sqrt (1+c))⁻¹ := Real.sqrt_inv _
      have hs1 : (0:ℝ) < Real.sqrt (1+c) := Real.sqrt_pos.2 h1c
      have hsq2 : Real.sqrt (1 + (d:ℝ)*c') * Real.sqrt (1+c) = Real.sqrt (1 + ((d:ℝ)+1)*c) := by
        rw [← Real.sqrt_mul (by positivity)]
        congr 1
        rw [hc'def]
        field_simp
        ring
      rw [hpiB, cpow_half_ofReal_mul (by positivity) hpb, hsq1]
      have hs2 : (0:ℝ) < Real.sqrt (1 + ((d:ℝ)+1)*c) := by
        apply Real.sqrt_pos.2
        nlinarith
      have hs3 : (0:ℝ) < Real.sqrt (1 + (d:ℝ)*c') := by
        apply Real.sqrt_pos.2
        positivity
      push_cast
      rw [pow_succ]
      field_simp
      have hfinal : Real.sqrt (1+c) * Real.sqrt (1+(d:ℝ)*c') = Real.sqrt (1 + c*((d:ℝ)+1)) := by
        rw [mul_comm, hsq2]
        congr 1
        ring
      rw [← Complex.ofReal_mul, hfinal]

/-- The `d`-dimensional complex Gaussian integral attached to `quadForm`. -/
theorem integral_cgauss_quadForm (d : ℕ) {b : ℂ} (hb : 0 < b.re) :
    (∫ θ : Fin d → ℝ, Complex.exp (-b * ((quadForm θ : ℝ) : ℂ)))
      = (((π : ℂ)/b) ^ ((1 : ℂ)/2))^d / ((Real.sqrt (d+1) : ℝ) : ℂ) := by
  have h := integral_cgauss_gen d hb 1 zero_le_one
  simp only [one_mul] at h
  rw [show ((1 : ℝ) + d*1) = (d+1 : ℝ) by ring] at h
  rw [← h]
  rfl


end Q776
