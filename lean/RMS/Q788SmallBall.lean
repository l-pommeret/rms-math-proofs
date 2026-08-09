/-
# Q788 — the small-ball estimate for the power-sum vector

Let `X_n(θ) = (∑_j cos(rθ_j), ∑_j sin(rθ_j))_{r ≤ K}` be the `2K`-dimensional vector of the first
`K` power sums of `n` independent uniform angles.  We prove the unconditional small-ball estimate

  `P(‖X_n‖ ≤ b) = O_{K,b}(n^{-K})`.

The proof is a Fourier (Esseen-type) argument with a *compactly supported* multiplier: with
`H = [-β/2, β/2]^{2K}` and `boxKer(x) = ∫_H e^{i⟨x,ξ⟩} dξ = ∏_i 2 sin(β x_i/2)/x_i`, the function
`boxKer²` is non-negative, bounded below on the ball of radius `2/β`, and

  `E[boxKer(X_n)²] = ∫_H ∫_H charTrig(ξ - η)^n dξ dη`.

Choosing `β` small enough that the characteristic-function gap applies on `H - H` and integrating
the resulting Gaussian bound gives the decay `n^{-K}`.
-/
import RMS.Q788CharFun

open MeasureTheory Real Set
open scoped ENNReal Topology

namespace Q788

set_option maxHeartbeats 1000000

/-! ## The compactly supported kernel -/

/-- The one-dimensional kernel `∫_{-b/2}^{b/2} e^{iuξ} dξ = 2 sin(ub/2)/u`. -/
noncomputable def sincKer (b u : ℝ) : ℝ := if u = 0 then b else 2 * Real.sin (u * b / 2) / u

/-- The box `[-b/2, b/2]^{2K}` of frequencies. -/
def halfBox (K : ℕ) (b : ℝ) : Set (trigIdx K → ℝ) :=
  Set.univ.pi fun _ => Set.Icc (-(b / 2)) (b / 2)

/-- The `2K`-dimensional kernel, a product of one-dimensional ones. -/
noncomputable def boxKer (K : ℕ) (b : ℝ) (x : trigIdx K → ℝ) : ℝ := ∏ i, sincKer b (x i)

theorem measurable_sincKer (b : ℝ) : Measurable (sincKer b) := by
  unfold sincKer
  refine Measurable.ite (measurableSet_eq_fun measurable_id measurable_const)
    measurable_const ?_
  fun_prop

theorem abs_sincKer_le (b : ℝ) (hb : 0 ≤ b) (u : ℝ) : |sincKer b u| ≤ b := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [sincKer, if_pos rfl, abs_of_nonneg hb]
  · rw [sincKer, if_neg hu, abs_div, abs_mul]
    rw [div_le_iff₀ (abs_pos.mpr hu)]
    have h1 : |Real.sin (u * b / 2)| ≤ |u * b / 2| := abs_sin_le_abs
    have h2 : |u * b / 2| = |u| * b / 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg hb, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    rw [h2] at h1
    have : |(2 : ℝ)| = 2 := by norm_num
    rw [this]
    nlinarith [abs_nonneg u, h1]

theorem sincKer_neg (b u : ℝ) : sincKer b (-u) = sincKer b u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · rw [sincKer, sincKer, if_neg hu, if_neg (by simpa using hu),
      show -u * b / 2 = -(u * b / 2) by ring, Real.sin_neg]
    field_simp

theorem sinc_lower {s : ℝ} (hs : s ≠ 0) (h1 : |s| ≤ 1) : (3 / 4 : ℝ) ≤ Real.sin s / s := by
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · have hp : 0 < -s := by linarith
    have h1' : -s ≤ 1 := by rw [abs_le] at h1; linarith [h1.1]
    have hc := Real.sin_gt_sub_cube hp h1'
    rw [show Real.sin s / s = Real.sin (-s) / (-s) by rw [Real.sin_neg]; field_simp,
      le_div_iff₀ hp]
    nlinarith [hc, sq_nonneg s]
  · have h1' : s ≤ 1 := by rw [abs_le] at h1; linarith [h1.2]
    have hc := Real.sin_gt_sub_cube hpos h1'
    rw [le_div_iff₀ hpos]
    nlinarith [hc, sq_nonneg s]

theorem sincKer_ge {b u : ℝ} (hb : 0 < b) (hu : |u| * b ≤ 2) : (3 / 4) * b ≤ sincKer b u := by
  rcases eq_or_ne u 0 with rfl | hne
  · rw [sincKer, if_pos rfl]; linarith
  · rw [sincKer, if_neg hne]
    set s := u * b / 2 with hs
    have hsne : s ≠ 0 := by rw [hs]; positivity
    have hsabs : |s| ≤ 1 := by
      rw [hs, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_pos hb]
      linarith [hu]
    have hkey := sinc_lower hsne hsabs
    have heq : 2 * Real.sin s / u = b * (Real.sin s / s) := by rw [hs]; field_simp
    rw [heq]
    nlinarith [hkey, hb]

theorem boxKer_neg (K : ℕ) (b : ℝ) (x : trigIdx K → ℝ) :
    boxKer K b (fun i => -x i) = boxKer K b x :=
  Finset.prod_congr rfl fun i _ => sincKer_neg b (x i)

theorem boxKer_ge (K : ℕ) {b : ℝ} (hb : 0 < b) {x : trigIdx K → ℝ}
    (hx : ∀ i, |x i| * b ≤ 2) :
    ((3 / 4) * b) ^ (2 * K) ≤ boxKer K b x := by
  have h := Finset.prod_le_prod (s := (Finset.univ : Finset (trigIdx K)))
    (f := fun _ => (3 / 4) * b) (g := fun i => sincKer b (x i))
    (fun i _ => by positivity) (fun i _ => sincKer_ge hb (hx i))
  rwa [Finset.prod_const, Finset.card_univ, card_trigIdx] at h

/-! ## The Fourier transform of the box -/

theorem expdiff (z : ℂ) :
    Complex.exp (z * Complex.I) - Complex.exp (-z * Complex.I)
      = 2 * Complex.I * Complex.sin z := by
  rw [Complex.sin]
  have h : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (Complex.exp (z * Complex.I) - Complex.exp (-z * Complex.I)) * h

theorem integral_exp_Icc (b u : ℝ) (hb : 0 ≤ b) :
    (∫ s in Set.Icc (-(b / 2)) (b / 2), Complex.exp (((u * s : ℝ) : ℂ) * Complex.I))
      = (sincKer b u : ℂ) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp only [zero_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero, sincKer]
    rw [MeasureTheory.setIntegral_const, Measure.real, Real.volume_Icc,
      show b / 2 - -(b / 2) = b by ring, ENNReal.toReal_ofReal hb]
    simp
  · have hc : (u : ℂ) * Complex.I ≠ 0 := by
      simp [hu, Complex.I_ne_zero, Complex.ofReal_eq_zero]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith)]
    have hcongr : ∀ s : ℝ, Complex.exp (((u * s : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((u : ℂ) * Complex.I) * (s : ℂ)) := by
      intro s; congr 1; push_cast; ring
    simp_rw [hcongr]
    rw [integral_exp_mul_complex hc, sincKer, if_neg hu]
    have h1 : ((u : ℂ) * Complex.I) * ((b / 2 : ℝ) : ℂ) = ((u * b / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    have h2 : ((u : ℂ) * Complex.I) * ((-(b / 2) : ℝ) : ℂ)
        = -(((u * b / 2 : ℝ) : ℂ)) * Complex.I := by push_cast; ring
    rw [h1, h2, expdiff, ← Complex.ofReal_sin]
    push_cast
    field_simp

theorem integral_halfBox_exp (K : ℕ) {b : ℝ} (hb : 0 ≤ b) (x : trigIdx K → ℝ) :
    (∫ ξ in halfBox K b, Complex.exp (((∑ i, x i * ξ i : ℝ) : ℂ) * Complex.I))
      = (boxKer K b x : ℂ) := by
  have hprod : ∀ ξ : trigIdx K → ℝ, Complex.exp (((∑ i, x i * ξ i : ℝ) : ℂ) * Complex.I)
      = ∏ i, Complex.exp (((x i * ξ i : ℝ) : ℂ) * Complex.I) := by
    intro ξ
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  simp_rw [hprod]
  rw [halfBox, MeasureTheory.volume_pi, Measure.restrict_pi_pi,
    MeasureTheory.integral_fintype_prod_eq_prod (fun i (s : ℝ) =>
      Complex.exp (((x i * s : ℝ) : ℂ) * Complex.I)), boxKer, Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun i _ => integral_exp_Icc b (x i) hb

theorem volume_halfBox (K : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    volume (halfBox K b) = ENNReal.ofReal (b ^ (2 * K)) := by
  rw [halfBox, MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
  simp only [Real.volume_Icc, show ∀ x : ℝ, x / 2 - -(x / 2) = x from fun x => by ring]
  rw [Finset.prod_const, Finset.card_univ, card_trigIdx, ← ENNReal.ofReal_pow hb]

/-! ## The characteristic function of the power-sum vector -/

theorem continuous_powerVec (K : ℕ) {n : ℕ} : Continuous fun θ : Fin n → ℝ => powerVec K θ := by
  refine continuous_pi fun i => continuous_finset_sum _ fun j _ => ?_
  exact (continuous_trigVec K i).comp (continuous_apply j)

/-- The characteristic function of the power-sum vector is the `n`-th power of the characteristic
function of one trigonometric vector. -/
theorem integral_exp_inner_powerVec (K n : ℕ) (ζ : trigIdx K → ℝ) :
    (∫ θ : Fin n → ℝ, Complex.exp (((∑ i, powerVec K θ i * ζ i : ℝ) : ℂ) * Complex.I)
        ∂angleLawN n) = (charTrig K ζ) ^ n := by
  have hpt : ∀ θ : Fin n → ℝ, Complex.exp (((∑ i, powerVec K θ i * ζ i : ℝ) : ℂ) * Complex.I)
      = ∏ j, Complex.exp (((trigPoly ζ (θ j) : ℝ) : ℂ) * Complex.I) := by
    intro θ
    rw [← Complex.exp_sum]
    congr 1
    have hsum : (∑ i, powerVec K θ i * ζ i) = ∑ j, trigPoly ζ (θ j) := by
      simp only [powerVec, trigPoly, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [hsum]
    push_cast
    rw [Finset.sum_mul]
  simp_rw [hpt]
  rw [angleLawN, MeasureTheory.integral_fintype_prod_eq_pow
    (fun t : ℝ => Complex.exp (((trigPoly ζ t : ℝ) : ℂ) * Complex.I))]
  simp [charTrig]

/-! ## The Gaussian integral over the box -/

theorem integral_gaussian_halfBox (K : ℕ) {b c : ℝ} (hc : 0 < c)
    (ξ : trigIdx K → ℝ) :
    (∫ η in halfBox K b, Real.exp (-(c * ∑ i, (ξ i - η i) ^ 2)))
      ≤ (Real.sqrt (π / c)) ^ (2 * K) := by
  have hpt : ∀ η : trigIdx K → ℝ, Real.exp (-(c * ∑ i, (ξ i - η i) ^ 2))
      = ∏ i, Real.exp (-(c * (ξ i - η i) ^ 2)) := by
    intro η
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum, neg_eq_neg_one_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hpt]
  rw [halfBox, MeasureTheory.volume_pi, Measure.restrict_pi_pi,
    MeasureTheory.integral_fintype_prod_eq_prod (fun i (s : ℝ) => Real.exp (-(c * (ξ i - s) ^ 2)))]
  have hone : ∀ i : trigIdx K,
      (∫ s in Set.Icc (-(b / 2)) (b / 2), Real.exp (-(c * (ξ i - s) ^ 2)))
        ≤ Real.sqrt (π / c) := by
    intro i
    have hintg : Integrable (fun s : ℝ => Real.exp (-(c * (ξ i - s) ^ 2))) volume := by
      have h0 : Integrable (fun u : ℝ => Real.exp (-c * u ^ 2)) volume :=
        integrable_exp_neg_mul_sq hc
      have := h0.comp_sub_left (ξ i)
      refine this.congr ?_
      filter_upwards with s
      congr 1
      ring
    have hfull : (∫ s : ℝ, Real.exp (-(c * (ξ i - s) ^ 2))) = Real.sqrt (π / c) := by
      have hshift : (∫ s : ℝ, Real.exp (-(c * (ξ i - s) ^ 2)))
          = ∫ u : ℝ, Real.exp (-c * u ^ 2) := by
        rw [← MeasureTheory.integral_sub_left_eq_self
          (fun u : ℝ => Real.exp (-c * u ^ 2)) volume (ξ i)]
        exact integral_congr_ae (by filter_upwards with s; congr 1; ring)
      rw [hshift, integral_gaussian]
    rw [← hfull]
    exact MeasureTheory.setIntegral_le_integral hintg
      (Filter.Eventually.of_forall fun s => (Real.exp_pos _).le)
  calc (∏ i : trigIdx K, ∫ s in Set.Icc (-(b / 2)) (b / 2), Real.exp (-(c * (ξ i - s) ^ 2)))
      ≤ ∏ _i : trigIdx K, Real.sqrt (π / c) :=
        Finset.prod_le_prod (fun i _ => integral_nonneg fun s => (Real.exp_pos _).le)
          fun i _ => hone i
    _ = (Real.sqrt (π / c)) ^ (2 * K) := by
        rw [Finset.prod_const, Finset.card_univ, card_trigIdx]

/-! ## The small-ball estimate -/

/-- **The unconditional small-ball estimate.**  For every truncation level `K` and every radius,
the probability that the first `K` power sums of `n` independent uniform angles all stay bounded
is `O(n^{-K})`. -/
theorem exists_smallBall (K : ℕ) (b2 : ℝ) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n →
      (angleLawN n {θ : Fin n → ℝ | sqNorm (powerVec K θ) ≤ b2}).toReal ≤ C / (n : ℝ) ^ K := by
  have hpi := Real.pi_pos
  set R : ℝ := max (Real.sqrt b2) (4 * K + 1) with hRdef
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hR4K : 4 * (K : ℝ) ≤ R := le_trans (by linarith) (le_max_right _ _)
  have hRb2 : Real.sqrt b2 ≤ R := le_max_left _ _
  set β : ℝ := 2 / R with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; positivity
  have hRβ : R * β = 2 := by rw [hβdef]; field_simp
  -- the constant
  refine ⟨(β ^ (2 * K) * (8 * π) ^ K) / (((3 / 4) * β) ^ (2 * (2 * K))), by positivity, ?_⟩
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set μ := angleLawN n with hμ
  set ν : Measure (trigIdx K → ℝ) := volume.restrict (halfBox K β) with hν
  haveI : IsFiniteMeasure ν := by
    constructor
    rw [hν, Measure.restrict_apply_univ, volume_halfBox K hβ0.le]
    exact ENNReal.ofReal_lt_top
  set E : Set (Fin n → ℝ) := {θ : Fin n → ℝ | sqNorm (powerVec K θ) ≤ b2} with hE
  -- (1) the kernel is bounded below on the event
  have hlow : ∀ θ ∈ E, ((3 / 4) * β) ^ (2 * K) ≤ boxKer K β (powerVec K θ) := by
    intro θ hθ
    refine boxKer_ge K hβ0 fun i => ?_
    have hi : (powerVec K θ i) ^ 2 ≤ b2 := by
      refine le_trans ?_ hθ
      exact Finset.single_le_sum (f := fun i => (powerVec K θ i) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have habs : |powerVec K θ i| ≤ R := by
      have h1 : |powerVec K θ i| ≤ Real.sqrt b2 := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt hi
      linarith
    calc |powerVec K θ i| * β ≤ R * β := by nlinarith [hβ0.le, abs_nonneg (powerVec K θ i)]
      _ = 2 := hRβ
  -- (2) the kernel squared is integrable
  have hmeas : Measurable fun θ : Fin n → ℝ => (boxKer K β (powerVec K θ)) ^ 2 := by
    refine Measurable.pow_const ?_ 2
    refine Finset.measurable_prod _ fun i _ => ?_
    exact (measurable_sincKer β).comp
      ((measurable_pi_apply i).comp (measurable_powerVec K))
  have hbd : ∀ θ : Fin n → ℝ, (boxKer K β (powerVec K θ)) ^ 2 ≤ (β ^ (2 * K)) ^ 2 := by
    intro θ
    have h1 : |boxKer K β (powerVec K θ)| ≤ β ^ (2 * K) := by
      rw [boxKer, Finset.abs_prod]
      have := Finset.prod_le_prod (s := (Finset.univ : Finset (trigIdx K)))
        (f := fun i => |sincKer β (powerVec K θ i)|) (g := fun _ => β)
        (fun i _ => abs_nonneg _) (fun i _ => abs_sincKer_le β hβ0.le _)
      rwa [Finset.prod_const, Finset.card_univ, card_trigIdx] at this
    nlinarith [abs_nonneg (boxKer K β (powerVec K θ)), sq_abs (boxKer K β (powerVec K θ)),
      pow_nonneg hβ0.le (2 * K)]
  have hint : Integrable (fun θ : Fin n → ℝ => (boxKer K β (powerVec K θ)) ^ 2) μ := by
    refine Integrable.mono' (g := fun _ => (β ^ (2 * K)) ^ 2) (integrable_const _)
      hmeas.aestronglyMeasurable ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbd θ
  set V : ℝ := ∫ θ, (boxKer K β (powerVec K θ)) ^ 2 ∂μ with hV
  -- (3) lower bound for `V`
  have hEmeas : MeasurableSet E := measurableSet_sqNorm_le K b2
  have hVlow : (μ E).toReal * (((3 / 4) * β) ^ (2 * K)) ^ 2 ≤ V := by
    have hstep : ∫ _θ in E, (((3 / 4) * β) ^ (2 * K)) ^ 2 ∂μ
        ≤ ∫ θ in E, (boxKer K β (powerVec K θ)) ^ 2 ∂μ := by
      refine MeasureTheory.setIntegral_mono_on (integrable_const _)
        (hint.restrict) hEmeas fun θ hθ => ?_
      have := hlow θ hθ
      nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ (3 / 4) * β) (2 * K)]
    have hle : ∫ θ in E, (boxKer K β (powerVec K θ)) ^ 2 ∂μ ≤ V :=
      MeasureTheory.setIntegral_le_integral hint
        (Filter.Eventually.of_forall fun θ => sq_nonneg _)
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, Measure.real] at hstep
    linarith
  -- (4) Fourier representation of `V`
  have hcont : Continuous fun z : (Fin n → ℝ) × ((trigIdx K → ℝ) × (trigIdx K → ℝ)) =>
      Complex.exp (((∑ i, powerVec K z.1 i * (z.2.1 i - z.2.2 i) : ℝ) : ℂ) * Complex.I) := by
    refine Complex.continuous_exp.comp ?_
    refine Continuous.mul ?_ continuous_const
    refine Complex.continuous_ofReal.comp ?_
    refine continuous_finset_sum _ fun i _ => ?_
    exact ((continuous_apply i).comp ((continuous_powerVec K).comp continuous_fst)).mul
      (((continuous_apply i).comp (continuous_fst.comp continuous_snd)).sub
        ((continuous_apply i).comp (continuous_snd.comp continuous_snd)))
  have hnorm1 : ∀ z : (Fin n → ℝ) × ((trigIdx K → ℝ) × (trigIdx K → ℝ)),
      ‖Complex.exp (((∑ i, powerVec K z.1 i * (z.2.1 i - z.2.2 i) : ℝ) : ℂ) * Complex.I)‖ = 1 :=
    fun z => Complex.norm_exp_ofReal_mul_I _
  have hintF : Integrable (Function.uncurry fun (θ : Fin n → ℝ)
      (p : (trigIdx K → ℝ) × (trigIdx K → ℝ)) =>
      Complex.exp (((∑ i, powerVec K θ i * (p.1 i - p.2 i) : ℝ) : ℂ) * Complex.I))
      (μ.prod (ν.prod ν)) := by
    refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const _)
      hcont.aestronglyMeasurable ?_
    filter_upwards with z
    simpa [Function.uncurry] using (hnorm1 z).le
  have hpointwise : ∀ θ : Fin n → ℝ, ((boxKer K β (powerVec K θ) : ℝ) ^ 2 : ℂ)
      = ∫ p : (trigIdx K → ℝ) × (trigIdx K → ℝ),
          Complex.exp (((∑ i, powerVec K θ i * (p.1 i - p.2 i) : ℝ) : ℂ) * Complex.I)
          ∂(ν.prod ν) := by
    intro θ
    have hsplit : ∀ p : (trigIdx K → ℝ) × (trigIdx K → ℝ),
        Complex.exp (((∑ i, powerVec K θ i * (p.1 i - p.2 i) : ℝ) : ℂ) * Complex.I)
          = Complex.exp (((∑ i, powerVec K θ i * p.1 i : ℝ) : ℂ) * Complex.I)
            * Complex.exp (((∑ i, (-(powerVec K θ i)) * p.2 i : ℝ) : ℂ) * Complex.I) := by
      intro p
      rw [← Complex.exp_add]
      congr 1
      push_cast
      rw [← add_mul]
      congr 1
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [hsplit]
    rw [MeasureTheory.integral_prod_mul
      (f := fun ξ : trigIdx K → ℝ =>
        Complex.exp (((∑ i, powerVec K θ i * ξ i : ℝ) : ℂ) * Complex.I))
      (g := fun η : trigIdx K → ℝ =>
        Complex.exp (((∑ i, (-(powerVec K θ i)) * η i : ℝ) : ℂ) * Complex.I))]
    rw [hν, integral_halfBox_exp K hβ0.le, integral_halfBox_exp K hβ0.le,
      boxKer_neg K β (powerVec K θ)]
    ring
  have hVc : (V : ℂ) = ∫ p : (trigIdx K → ℝ) × (trigIdx K → ℝ),
      (charTrig K (fun i => p.1 i - p.2 i)) ^ n ∂(ν.prod ν) := by
    rw [hV, ← integral_complex_ofReal]
    push_cast
    simp_rw [hpointwise]
    rw [MeasureTheory.integral_integral_swap hintF]
    refine integral_congr_ae ?_
    filter_upwards with p
    exact integral_exp_inner_powerVec K n (fun i => p.1 i - p.2 i)
  -- (5) upper bound for `V`
  have hgap : ∀ p ∈ halfBox K β ×ˢ halfBox K β,
      ‖(charTrig K (fun i => p.1 i - p.2 i)) ^ n‖
        ≤ Real.exp (-((n : ℝ) / 8 * ∑ i, (p.1 i - p.2 i) ^ 2)) := by
    rintro ⟨ξ, η⟩ hp
    have hmem1 : ξ ∈ halfBox K β := hp.1
    have hmem2 : η ∈ halfBox K β := hp.2
    have hcoord : ∀ i, (ξ i - η i) ^ 2 ≤ β ^ 2 := by
      intro i
      have h1 := (Set.mem_univ_pi.mp hmem1) i
      have h2 := (Set.mem_univ_pi.mp hmem2) i
      simp only [Set.mem_Icc] at h1 h2
      nlinarith [h1.1, h1.2, h2.1, h2.2]
    set ζ : trigIdx K → ℝ := fun i => ξ i - η i with hζ
    have hsq : sqNorm ζ ≤ 2 * K * β ^ 2 := by
      have := Finset.sum_le_sum (s := (Finset.univ : Finset (trigIdx K)))
        (f := fun i => (ζ i) ^ 2) (g := fun _ => β ^ 2) (fun i _ => hcoord i)
      rw [Finset.sum_const, Finset.card_univ, card_trigIdx, nsmul_eq_mul] at this
      simpa [sqNorm, hζ] using this
    have hsmall : sqNorm ζ * (2 * K) ≤ 1 := by
      have hKβ : (2 * (K : ℝ) * β ^ 2) * (2 * K) ≤ 1 := by
        have h4 : 4 * (K : ℝ) ^ 2 * β ^ 2 = (2 * K * β) ^ 2 := by ring
        have hb : 2 * (K : ℝ) * β ≤ 1 := by
          have hrw : 2 * (K : ℝ) * β = 4 * (K : ℝ) / R := by rw [hβdef]; field_simp; ring
          rw [hrw, div_le_one hR0]
          linarith [hR4K]
        nlinarith [hb, sq_nonneg (2 * (K:ℝ) * β), mul_nonneg (by positivity : (0:ℝ) ≤ 2 * (K:ℝ))
          hβ0.le]
      have hnn : (0 : ℝ) ≤ 2 * K := by positivity
      nlinarith [hsq, hnn, sqNorm_nonneg ζ]
    have hgapζ := norm_charTrig_le_of_small ζ hsmall
    have hexp : ‖charTrig K ζ‖ ≤ Real.exp (-(sqNorm ζ / 8)) := by
      have h1 : 1 - sqNorm ζ / 8 ≤ Real.exp (-(sqNorm ζ / 8)) := by
        have := Real.add_one_le_exp (-(sqNorm ζ / 8))
        linarith
      linarith
    calc ‖(charTrig K ζ) ^ n‖ = ‖charTrig K ζ‖ ^ n := by rw [norm_pow]
      _ ≤ (Real.exp (-(sqNorm ζ / 8))) ^ n := pow_le_pow_left₀ (norm_nonneg _) hexp n
      _ = Real.exp (-((n : ℝ) / 8 * ∑ i, (ξ i - η i) ^ 2)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          rw [sqNorm]
          ring
  have hmeasBox : MeasurableSet (halfBox K β) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hVup : V ≤ β ^ (2 * K) * (Real.sqrt (π / ((n : ℝ) / 8))) ^ (2 * K) := by
    have hV0 : 0 ≤ V := integral_nonneg fun θ => sq_nonneg _
    have hb1 : V ≤ ∫ p : (trigIdx K → ℝ) × (trigIdx K → ℝ),
        ‖(charTrig K (fun i => p.1 i - p.2 i)) ^ n‖ ∂(ν.prod ν) := by
      have h := hVc ▸ (norm_integral_le_integral_norm
        (μ := ν.prod ν)
        (f := fun p : (trigIdx K → ℝ) × (trigIdx K → ℝ) =>
          (charTrig K (fun i => p.1 i - p.2 i)) ^ n))
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hV0] using h
    have hmeasG : Measurable fun p : (trigIdx K → ℝ) × (trigIdx K → ℝ) =>
        Real.exp (-((n : ℝ) / 8 * ∑ i, (p.1 i - p.2 i) ^ 2)) := by fun_prop
    have hintG : Integrable (fun p : (trigIdx K → ℝ) × (trigIdx K → ℝ) =>
        Real.exp (-((n : ℝ) / 8 * ∑ i, (p.1 i - p.2 i) ^ 2))) (ν.prod ν) := by
      refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const _)
        hmeasG.aestronglyMeasurable ?_
      filter_upwards with p
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      refine Real.exp_le_one_iff.mpr ?_
      have hs : (0 : ℝ) ≤ ∑ i, (p.1 i - p.2 i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have : (0 : ℝ) ≤ (n : ℝ) / 8 * ∑ i, (p.1 i - p.2 i) ^ 2 := by positivity
      linarith
    -- the pointwise gap holds almost everywhere on the product of boxes
    have hprodrestrict : ν.prod ν
        = (volume : Measure ((trigIdx K → ℝ) × (trigIdx K → ℝ))).restrict
            (halfBox K β ×ˢ halfBox K β) := by
      rw [hν, Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
    have hae : ∀ᵐ p ∂(ν.prod ν),
        ‖(charTrig K (fun i => p.1 i - p.2 i)) ^ n‖
          ≤ Real.exp (-((n : ℝ) / 8 * ∑ i, (p.1 i - p.2 i) ^ 2)) := by
      rw [hprodrestrict]
      refine (MeasureTheory.ae_restrict_iff' (hmeasBox.prod hmeasBox)).mpr ?_
      exact Filter.Eventually.of_forall fun p hp => hgap p hp
    have hb2 : (∫ p : (trigIdx K → ℝ) × (trigIdx K → ℝ),
        ‖(charTrig K (fun i => p.1 i - p.2 i)) ^ n‖ ∂(ν.prod ν))
          ≤ ∫ p : (trigIdx K → ℝ) × (trigIdx K → ℝ),
              Real.exp (-((n : ℝ) / 8 * ∑ i, (p.1 i - p.2 i) ^ 2)) ∂(ν.prod ν) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => norm_nonneg _) hintG hae
    -- Fubini and the Gaussian bound
    have hsplit : (∫ p : (trigIdx K → ℝ) × (trigIdx K → ℝ),
        Real.exp (-((n : ℝ) / 8 * ∑ i, (p.1 i - p.2 i) ^ 2)) ∂(ν.prod ν))
          = ∫ ξ : trigIdx K → ℝ,
              (∫ η : trigIdx K → ℝ,
                Real.exp (-((n : ℝ) / 8 * ∑ i, (ξ i - η i) ^ 2)) ∂ν) ∂ν :=
      integral_prod _ hintG
    have hinner : ∀ ξ : trigIdx K → ℝ,
        (∫ η : trigIdx K → ℝ, Real.exp (-((n : ℝ) / 8 * ∑ i, (ξ i - η i) ^ 2)) ∂ν)
          ≤ (Real.sqrt (π / ((n : ℝ) / 8))) ^ (2 * K) := by
      intro ξ
      rw [hν]
      exact integral_gaussian_halfBox K (by positivity) ξ
    have hinner0 : ∀ ξ : trigIdx K → ℝ,
        0 ≤ ∫ η : trigIdx K → ℝ, Real.exp (-((n : ℝ) / 8 * ∑ i, (ξ i - η i) ^ 2)) ∂ν :=
      fun ξ => integral_nonneg fun η => (Real.exp_pos _).le
    have hout : (∫ ξ : trigIdx K → ℝ,
        (∫ η : trigIdx K → ℝ, Real.exp (-((n : ℝ) / 8 * ∑ i, (ξ i - η i) ^ 2)) ∂ν) ∂ν)
          ≤ ∫ _ξ : trigIdx K → ℝ, (Real.sqrt (π / ((n : ℝ) / 8))) ^ (2 * K) ∂ν :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall hinner0) (integrable_const _)
        (Filter.Eventually.of_forall hinner)
    have hconst : (∫ _ξ : trigIdx K → ℝ, (Real.sqrt (π / ((n : ℝ) / 8))) ^ (2 * K) ∂ν)
        = β ^ (2 * K) * (Real.sqrt (π / ((n : ℝ) / 8))) ^ (2 * K) := by
      rw [MeasureTheory.integral_const, smul_eq_mul, Measure.real, hν,
        Measure.restrict_apply_univ, volume_halfBox K hβ0.le,
        ENNReal.toReal_ofReal (by positivity)]
    linarith [hb1, hb2, hsplit.le, hsplit.ge, hout, hconst.le, hconst.ge]
  -- (6) conclusion
  have haeq : (((3 / 4 : ℝ) * β) ^ (2 * K)) ^ 2 = ((3 / 4 : ℝ) * β) ^ (2 * (2 * K)) := by
    rw [← pow_mul]
    congr 1
    ring
  have hsqrt : (Real.sqrt (π / ((n : ℝ) / 8))) ^ (2 * K) = (8 * π) ^ K / (n : ℝ) ^ K := by
    rw [pow_mul, Real.sq_sqrt (by positivity)]
    rw [show π / ((n : ℝ) / 8) = (8 * π) / (n : ℝ) by field_simp, div_pow]
  have ha : (0 : ℝ) < ((3 / 4 : ℝ) * β) ^ (2 * (2 * K)) := by positivity
  have hnK : (0 : ℝ) < (n : ℝ) ^ K := by positivity
  have key : (μ E).toReal * ((3 / 4 : ℝ) * β) ^ (2 * (2 * K))
      ≤ β ^ (2 * K) * (8 * π) ^ K / (n : ℝ) ^ K := by
    rw [← haeq]
    refine le_trans hVlow (le_trans hVup ?_)
    rw [hsqrt, mul_div_assoc]
  rw [div_div, le_div_iff₀ (by positivity : (0 : ℝ) < ((3 / 4 : ℝ) * β) ^ (2 * (2 * K))
    * (n : ℝ) ^ K), ← mul_assoc]
  rw [le_div_iff₀ hnK] at key
  linarith [key]

end Q788
