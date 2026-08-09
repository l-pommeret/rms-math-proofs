/-
# Q788 — the characteristic-function gap

`charTrig K ξ = E[exp(i ⟨ξ, V(t)⟩)]` is the characteristic function of one uniform trigonometric
vector `V(t) = (cos t, sin t, …, cos Kt, sin Kt)`.  We prove the quantitative non-degeneracy
statement needed for the small-ball estimate: for every frequency vector `ξ` with
`‖ξ‖² · 2K ≤ 1`,

  `‖charTrig K ξ‖ ≤ 1 - ‖ξ‖² / 8`.

The proof is the second-order expansion of the characteristic function, based on the exact
orthogonality relations of the trigonometric system.
-/
import RMS.Q788Vec

open MeasureTheory Real Set intervalIntegral
open scoped ENNReal Topology

namespace Q788

/-! ## Elementary trigonometric integrals over a period -/

theorem intcos (c : ℝ) (hc : c ≠ 0) :
    ∫ t in (0 : ℝ)..(2 * π), Real.cos (c * t) = Real.sin (2 * π * c) / c := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc]
  simp [integral_cos, mul_comm, div_eq_inv_mul]

theorem intsin (c : ℝ) (hc : c ≠ 0) :
    ∫ t in (0 : ℝ)..(2 * π), Real.sin (c * t) = (1 - Real.cos (2 * π * c)) / c := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hc]
  simp [integral_sin, mul_comm, div_eq_inv_mul]

theorem intcos_int (m : ℤ) :
    ∫ t in (0 : ℝ)..(2 * π), Real.cos ((m : ℝ) * t) = if m = 0 then 2 * π else 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rw [intcos _ (by exact_mod_cast hm)]
  have h : (2 * π * (m : ℝ)) = ((2 * m : ℤ) : ℝ) * π := by push_cast; ring
  rw [h, Real.sin_int_mul_pi]
  simp [hm]

theorem intsin_int (m : ℤ) : ∫ t in (0 : ℝ)..(2 * π), Real.sin ((m : ℝ) * t) = 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rw [intsin _ (by exact_mod_cast hm)]
  have h : (2 * π * (m : ℝ)) = ((m : ℤ) : ℝ) * (2 * π) := by ring
  rw [h, Real.cos_int_mul_two_pi]
  simp

theorem intcc (u v : ℝ) (c1 c2 : ℤ) :
    ∫ t in (0 : ℝ)..(2 * π), (u * Real.cos ((c1 : ℝ) * t) + v * Real.cos ((c2 : ℝ) * t))
      = u * (if c1 = 0 then 2 * π else 0) + v * (if c2 = 0 then 2 * π else 0) := by
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intcos_int, intcos_int]

theorem intss (u v : ℝ) (c1 c2 : ℤ) :
    ∫ t in (0 : ℝ)..(2 * π), (u * Real.sin ((c1 : ℝ) * t) + v * Real.sin ((c2 : ℝ) * t)) = 0 := by
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intsin_int, intsin_int]
  ring

/-! ## Continuity and orthogonality of the trigonometric system -/

theorem continuous_trigVec (K : ℕ) (i : trigIdx K) : Continuous fun t => trigVec K t i := by
  obtain ⟨r, b⟩ := i
  simp only [trigVec]
  cases b <;> simp <;> fun_prop

theorem continuous_trigPoly {K : ℕ} (ξ : trigIdx K → ℝ) : Continuous (trigPoly ξ) :=
  continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_trigVec K i)

theorem integral_trigVec_zero (K : ℕ) (i : trigIdx K) :
    ∫ t in (0 : ℝ)..(2 * π), trigVec K t i = 0 := by
  obtain ⟨r, b⟩ := i
  have hm : (((r : ℕ) : ℝ) + 1) = ((((r : ℕ) : ℤ) + 1 : ℤ) : ℝ) := by push_cast; ring
  have hmne : (((r : ℕ) : ℤ) + 1) ≠ 0 := by omega
  simp only [trigVec]
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> rw [hm]
  · rw [intcos_int, if_neg hmne]
  · rw [intsin_int]

/-- **Orthogonality of the trigonometric system** over one period. -/
theorem integral_trigVec_mul (K : ℕ) (i i' : trigIdx K) :
    ∫ t in (0 : ℝ)..(2 * π), trigVec K t i * trigVec K t i' = if i = i' then π else 0 := by
  obtain ⟨r, b⟩ := i
  obtain ⟨r', b'⟩ := i'
  set p : ℤ := ((r : ℕ) : ℤ) - ((r' : ℕ) : ℤ) with hpdef
  set q : ℤ := ((r : ℕ) : ℤ) + ((r' : ℕ) : ℤ) + 2 with hqdef
  have hqne : q ≠ 0 := by omega
  set a : ℝ := ((r : ℕ) : ℝ) + 1 with hadef
  set a' : ℝ := ((r' : ℕ) : ℝ) + 1 with ha'def
  have harg : ∀ t : ℝ, a * t - a' * t = (p : ℝ) * t := by
    intro t; rw [hadef, ha'def, hpdef]; push_cast; ring
  have harg2 : ∀ t : ℝ, a * t + a' * t = (q : ℝ) * t := by
    intro t; rw [hadef, ha'def, hqdef]; push_cast; ring
  have hpz : (p = 0) ↔ (r = r') := by
    rw [hpdef]
    constructor
    · intro h; ext; omega
    · intro h; simp [h]
  cases b <;> cases b' <;> simp only [trigVec, Bool.false_eq_true, if_false, if_true,
      Prod.mk.injEq, and_true, and_false, if_false] <;> rw [← hadef, ← ha'def]
  · have hpt : ∀ t : ℝ, Real.cos (a * t) * Real.cos (a' * t)
        = (1 / 2) * Real.cos ((p : ℝ) * t) + (1 / 2) * Real.cos ((q : ℝ) * t) := by
      intro t; rw [← harg t, ← harg2 t, Real.cos_sub, Real.cos_add]; ring
    simp_rw [hpt]
    rw [intcc, if_neg hqne]
    by_cases h : r = r'
    · rw [if_pos (hpz.mpr h), if_pos h]; ring
    · rw [if_neg (fun hc => h (hpz.mp hc)), if_neg h]; ring
  · have hpt : ∀ t : ℝ, Real.cos (a * t) * Real.sin (a' * t)
        = (1 / 2) * Real.sin ((q : ℝ) * t) + (-(1 / 2)) * Real.sin ((p : ℝ) * t) := by
      intro t; rw [← harg t, ← harg2 t, Real.sin_sub, Real.sin_add]; ring
    simp_rw [hpt]
    rw [intss]
  · have hpt : ∀ t : ℝ, Real.sin (a * t) * Real.cos (a' * t)
        = (1 / 2) * Real.sin ((q : ℝ) * t) + (1 / 2) * Real.sin ((p : ℝ) * t) := by
      intro t; rw [← harg t, ← harg2 t, Real.sin_sub, Real.sin_add]; ring
    simp_rw [hpt]
    rw [intss]
    simp
  · have hpt : ∀ t : ℝ, Real.sin (a * t) * Real.sin (a' * t)
        = (1 / 2) * Real.cos ((p : ℝ) * t) + (-(1 / 2)) * Real.cos ((q : ℝ) * t) := by
      intro t; rw [← harg t, ← harg2 t, Real.cos_sub, Real.cos_add]; ring
    simp_rw [hpt]
    rw [intcc, if_neg hqne]
    by_cases h : r = r'
    · rw [if_pos (hpz.mpr h), if_pos h]; ring
    · rw [if_neg (fun hc => h (hpz.mp hc)), if_neg h]; ring

/-! ## Integration against the uniform angle law -/

/-- Integrals against `angleLaw` are normalized integrals over one period. -/
theorem integral_angleLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    ∫ t, f t ∂angleLaw = (2 * π)⁻¹ • ∫ t in (0 : ℝ)..(2 * π), f t := by
  have hpi := Real.pi_pos
  rw [angleLaw_eq_Ioc, MeasureTheory.integral_smul_measure,
    intervalIntegral.integral_of_le (by positivity)]
  congr 1
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)]

theorem integrable_angleLaw {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (hf : Continuous f) :
    Integrable f angleLaw := by
  have hpi := Real.pi_pos
  rw [angleLaw_eq_Ioc]
  refine Integrable.smul_measure ?_
    (by simp [ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero]; positivity)
  exact hf.integrableOn_Ioc

/-- A trigonometric polynomial with no constant term has mean zero. -/
theorem integral_trigPoly {K : ℕ} (ξ : trigIdx K → ℝ) :
    ∫ t, trigPoly ξ t ∂angleLaw = 0 := by
  rw [integral_angleLaw]
  have hint : ∀ i ∈ (Finset.univ : Finset (trigIdx K)),
      IntervalIntegrable (fun t => ξ i * trigVec K t i) volume 0 (2 * π) :=
    fun i _ => (continuous_const.mul (continuous_trigVec K i)).intervalIntegrable _ _
  have h : ∫ t in (0 : ℝ)..(2 * π), trigPoly ξ t = 0 := by
    unfold trigPoly
    rw [intervalIntegral.integral_finset_sum hint]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_trigVec_zero, mul_zero]
  rw [h, smul_zero]

/-- The mean square of a trigonometric polynomial is half the squared norm of its coefficients. -/
theorem integral_trigPoly_sq {K : ℕ} (ξ : trigIdx K → ℝ) :
    ∫ t, (trigPoly ξ t) ^ 2 ∂angleLaw = sqNorm ξ / 2 := by
  have hpi := Real.pi_pos
  rw [integral_angleLaw]
  have hexp : ∀ t : ℝ, (trigPoly ξ t) ^ 2
      = ∑ i, ∑ i', (ξ i * ξ i') * (trigVec K t i * trigVec K t i') := by
    intro t
    rw [sq, trigPoly, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring
  have hint2 : ∀ i ∈ (Finset.univ : Finset (trigIdx K)),
      ∀ i' ∈ (Finset.univ : Finset (trigIdx K)),
      IntervalIntegrable (fun t => (ξ i * ξ i') * (trigVec K t i * trigVec K t i'))
        volume 0 (2 * π) :=
    fun i _ i' _ => (continuous_const.mul ((continuous_trigVec K i).mul
      (continuous_trigVec K i'))).intervalIntegrable _ _
  have hinner : ∀ i : trigIdx K, (∫ t in (0 : ℝ)..(2 * π),
      ∑ i', (ξ i * ξ i') * (trigVec K t i * trigVec K t i')) = π * (ξ i) ^ 2 := by
    intro i
    rw [intervalIntegral.integral_finset_sum (hint2 i (Finset.mem_univ i))]
    rw [Finset.sum_congr rfl (fun i' _ => by
      rw [intervalIntegral.integral_const_mul, integral_trigVec_mul])]
    rw [Finset.sum_eq_single i]
    · simp; ring
    · intro i' _ hne; simp [Ne.symm hne]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hint3 : ∀ i ∈ (Finset.univ : Finset (trigIdx K)),
      IntervalIntegrable (fun t => ∑ i', (ξ i * ξ i') * (trigVec K t i * trigVec K t i'))
        volume 0 (2 * π) := fun i _ =>
    (continuous_finset_sum _ fun i' _ => continuous_const.mul
      ((continuous_trigVec K i).mul (continuous_trigVec K i'))).intervalIntegrable _ _
  have h : ∫ t in (0 : ℝ)..(2 * π), (trigPoly ξ t) ^ 2 = π * sqNorm ξ := by
    simp_rw [hexp]
    rw [intervalIntegral.integral_finset_sum hint3]
    rw [Finset.sum_congr rfl (fun i _ => hinner i), ← Finset.mul_sum, sqNorm]
  rw [h, smul_eq_mul]
  field_simp

/-- A pointwise bound for a trigonometric polynomial in terms of its coefficients. -/
theorem sq_trigPoly_le {K : ℕ} (ξ : trigIdx K → ℝ) (t : ℝ) :
    (trigPoly ξ t) ^ 2 ≤ sqNorm ξ * (2 * K) := by
  have h1 : (trigPoly ξ t) ^ 2 ≤ (∑ i, (ξ i) ^ 2) * (∑ i : trigIdx K, (trigVec K t i) ^ 2) := by
    rw [trigPoly]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h2 : (∑ i : trigIdx K, (trigVec K t i) ^ 2) ≤ 2 * K := by
    calc (∑ i : trigIdx K, (trigVec K t i) ^ 2) ≤ ∑ _i : trigIdx K, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          nlinarith [abs_trigVec_le_one (K := K) t i, abs_nonneg (trigVec K t i),
            sq_abs (trigVec K t i)]
      _ = 2 * K := by simp [mul_comm]
  have h3 : (0 : ℝ) ≤ ∑ i, (ξ i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc (trigPoly ξ t) ^ 2 ≤ (∑ i, (ξ i) ^ 2) * (∑ i : trigIdx K, (trigVec K t i) ^ 2) := h1
    _ ≤ (∑ i, (ξ i) ^ 2) * (2 * K) := by nlinarith
    _ = sqNorm ξ * (2 * K) := by rw [sqNorm]

/-! ## The characteristic-function gap -/

/-- The real and imaginary parts of the characteristic function. -/
theorem charTrig_eq {K : ℕ} (ξ : trigIdx K → ℝ) :
    charTrig K ξ = ((∫ t, Real.cos (trigPoly ξ t) ∂angleLaw : ℝ) : ℂ)
      + ((∫ t, Real.sin (trigPoly ξ t) ∂angleLaw : ℝ) : ℂ) * Complex.I := by
  have hcg : Continuous (trigPoly ξ) := continuous_trigPoly ξ
  have hc : Integrable (fun t => ((Real.cos (trigPoly ξ t) : ℝ) : ℂ)) angleLaw :=
    integrable_angleLaw (by fun_prop)
  have hs : Integrable (fun t => ((Real.sin (trigPoly ξ t) : ℝ) : ℂ) * Complex.I) angleLaw :=
    integrable_angleLaw (by fun_prop)
  rw [charTrig]
  have hpt : ∀ t : ℝ, Complex.exp ((trigPoly ξ t : ℂ) * Complex.I)
      = ((Real.cos (trigPoly ξ t) : ℝ) : ℂ) + ((Real.sin (trigPoly ξ t) : ℝ) : ℂ) * Complex.I := by
    intro t
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp_rw [hpt]
  rw [MeasureTheory.integral_add hc hs, integral_complex_ofReal,
    MeasureTheory.integral_mul_const, integral_complex_ofReal]

/-- **The characteristic-function gap.**  For frequency vectors in the range where the
trigonometric polynomial `⟨ξ, V(·)⟩` is bounded by `1`, the characteristic function of one
uniform trigonometric vector is bounded away from `1` at a quadratic rate. -/
theorem norm_charTrig_le_of_small {K : ℕ} (ξ : trigIdx K → ℝ)
    (hsmall : sqNorm ξ * (2 * K) ≤ 1) :
    ‖charTrig K ξ‖ ≤ 1 - sqNorm ξ / 8 := by
  set g := trigPoly ξ with hgdef
  have hcg : Continuous g := continuous_trigPoly ξ
  have hgsq : ∀ t, (g t) ^ 2 ≤ 1 := fun t => le_trans (sq_trigPoly_le ξ t) hsmall
  have hgabs : ∀ t, |g t| ≤ 1 := fun t => by
    nlinarith [hgsq t, sq_abs (g t), abs_nonneg (g t)]
  have hint_cos : Integrable (fun t => Real.cos (g t)) angleLaw :=
    integrable_angleLaw (by fun_prop)
  have hint_sin : Integrable (fun t => Real.sin (g t)) angleLaw :=
    integrable_angleLaw (by fun_prop)
  have hint_g : Integrable g angleLaw := integrable_angleLaw hcg
  have hint_g2 : Integrable (fun t => (g t) ^ 2) angleLaw := integrable_angleLaw (by fun_prop)
  set E2 : ℝ := ∫ t, (g t) ^ 2 ∂angleLaw with hE2def
  have hE2 : E2 = sqNorm ξ / 2 := integral_trigPoly_sq ξ
  have hE2nn : 0 ≤ E2 := integral_nonneg fun t => sq_nonneg _
  have hE2le : E2 ≤ 1 := by
    calc E2 ≤ ∫ _t, (1 : ℝ) ∂angleLaw :=
          integral_mono hint_g2 (integrable_const 1) fun t => hgsq t
      _ = 1 := by simp
  set A : ℝ := ∫ t, Real.cos (g t) ∂angleLaw with hAdef
  set B : ℝ := ∫ t, Real.sin (g t) ∂angleLaw with hBdef
  -- upper bound for the real part
  have hsq4 : ∀ t, |g t| ^ 4 = ((g t) ^ 2) ^ 2 := fun t => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]
  have hsq44 : ∀ t, ((g t) ^ 2) ^ 2 ≤ (g t) ^ 2 := fun t => by
    nlinarith [hgsq t, sq_nonneg (g t)]
  have hAup : A ≤ 1 - (43 / 96) * E2 := by
    have hpt : ∀ t, Real.cos (g t) ≤ 1 - (43 / 96) * (g t) ^ 2 := by
      intro t
      have hb := Real.cos_bound (hgabs t)
      rw [abs_le] at hb
      nlinarith [hb.1, hb.2, hsq4 t, hsq44 t]
    calc A ≤ ∫ t, (1 - (43 / 96) * (g t) ^ 2) ∂angleLaw :=
          integral_mono hint_cos ((integrable_const 1).sub (hint_g2.const_mul _)) hpt
      _ = 1 - (43 / 96) * E2 := by
          rw [MeasureTheory.integral_sub (integrable_const 1) (hint_g2.const_mul _),
            MeasureTheory.integral_const_mul]
          simp
          exact hE2def.symm
  have hAlo : 1 - (53 / 96) * E2 ≤ A := by
    have hpt : ∀ t, 1 - (53 / 96) * (g t) ^ 2 ≤ Real.cos (g t) := by
      intro t
      have hb := Real.cos_bound (hgabs t)
      rw [abs_le] at hb
      nlinarith [hb.1, hb.2, hsq4 t, hsq44 t]
    calc (1 : ℝ) - (53 / 96) * E2 = ∫ t, (1 - (53 / 96) * (g t) ^ 2) ∂angleLaw := by
          rw [MeasureTheory.integral_sub (integrable_const 1) (hint_g2.const_mul _),
            MeasureTheory.integral_const_mul]
          simp
          exact hE2def
      _ ≤ A := integral_mono ((integrable_const 1).sub (hint_g2.const_mul _)) hint_cos hpt
  -- bound for the imaginary part
  have hBabs : |B| ≤ (21 / 96) * E2 := by
    have hzero : ∫ t, g t ∂angleLaw = 0 := integral_trigPoly ξ
    have hBeq : B = ∫ t, (Real.sin (g t) - g t) ∂angleLaw := by
      rw [MeasureTheory.integral_sub hint_sin hint_g, hzero, sub_zero]
    have hpt : ∀ t, |Real.sin (g t) - g t| ≤ (21 / 96) * (g t) ^ 2 := by
      intro t
      have hb := Real.sin_bound (hgabs t)
      have h3 : |(g t) ^ 3 / 6| ≤ (g t) ^ 2 / 6 := by
        rw [abs_div, abs_pow]
        have hc : |g t| ^ 3 ≤ (g t) ^ 2 := by
          nlinarith [sq_abs (g t), abs_nonneg (g t), hgabs t]
        simp only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (6 : ℝ))]
        linarith [hc]
      have key : |Real.sin (g t) - g t|
          ≤ |Real.sin (g t) - (g t - (g t) ^ 3 / 6)| + |(g t) ^ 3 / 6| := by
        have he : Real.sin (g t) - g t
            = (Real.sin (g t) - (g t - (g t) ^ 3 / 6)) + (-((g t) ^ 3 / 6)) := by ring
        rw [he]
        calc |(Real.sin (g t) - (g t - (g t) ^ 3 / 6)) + (-((g t) ^ 3 / 6))|
            ≤ |Real.sin (g t) - (g t - (g t) ^ 3 / 6)| + |-((g t) ^ 3 / 6)| := abs_add_le _ _
          _ = |Real.sin (g t) - (g t - (g t) ^ 3 / 6)| + |(g t) ^ 3 / 6| := by rw [abs_neg]
      linarith [hb, hsq4 t ▸ hb, h3, hsq44 t]
    have hint_diff : Integrable (fun t => Real.sin (g t) - g t) angleLaw := hint_sin.sub hint_g
    calc |B| = ‖∫ t, (Real.sin (g t) - g t) ∂angleLaw‖ := by rw [hBeq]; rfl
      _ ≤ ∫ t, ‖Real.sin (g t) - g t‖ ∂angleLaw := norm_integral_le_integral_norm _
      _ ≤ ∫ t, (21 / 96) * (g t) ^ 2 ∂angleLaw :=
          integral_mono hint_diff.norm (hint_g2.const_mul _) hpt
      _ = (21 / 96) * E2 := by rw [MeasureTheory.integral_const_mul]
  -- combine
  have hkey : A ^ 2 + B ^ 2 ≤ (1 - E2 / 4) ^ 2 := by
    have hA0 : 0 ≤ A := by nlinarith [hAlo, hE2le, hE2nn]
    have hB2 : B ^ 2 ≤ ((21 / 96) * E2) ^ 2 := by
      nlinarith [hBabs, abs_nonneg B, sq_abs B]
    nlinarith [hAup, hA0, hB2, hE2le, hE2nn, sq_nonneg E2]
  have hnn : 0 ≤ 1 - E2 / 4 := by linarith
  rw [charTrig_eq ξ, Complex.norm_add_mul_I, ← hAdef, ← hBdef]
  have := Real.sqrt_le_sqrt hkey
  rw [Real.sqrt_sq hnn] at this
  calc Real.sqrt (A ^ 2 + B ^ 2) ≤ 1 - E2 / 4 := this
    _ = 1 - sqNorm ξ / 8 := by rw [hE2]; ring

end Q788
