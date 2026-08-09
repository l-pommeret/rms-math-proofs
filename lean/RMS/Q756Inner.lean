/-
# Q756 — the inward extension

Given a smooth seed `phi` supported strictly inside the fundamental annulus
`1 < |t| < |lam|`, the outward extension `Wout` satisfies

  `Wout' t = Wout (lam t) - beta * Wout t - phi (lam t)`,

so a correction `V`, supported in `[-1,1]`, solving

  `V' t = V (lam t) - beta * V t + phi (lam t)`   (`t ≠ 0`)

turns `Wout + V` into a genuine solution away from the origin.  This file constructs `V`
as a (pointwise finite) sum of Picard iterates of a Volterra integral operator.
-/

import RMS.Q756Outward

namespace Q756

open Set Filter MeasureTheory intervalIntegral

/-- The outer endpoint of the shell containing `t`: `±1` for `0 < |t| ≤ 1`, and `t` itself
for `|t| ≥ 1` (so that integrals from `outer t` to `t` vanish there). -/
noncomputable def outer (t : ℝ) : ℝ :=
  if 0 < t then max t 1 else if t < 0 then min t (-1) else 0

theorem mem_uIcc_outer (t : ℝ) : ∀ s ∈ Set.uIcc (outer t) t,
    |t| ≤ |s| ∧ |s| ≤ max |t| 1 ∧ (t ≠ 0 → 0 < s * t) := by
  intro s hs
  rcases lt_trichotomy t 0 with h | h | h
  · rw [outer, if_neg (by linarith), if_pos h, Set.uIcc_of_le (min_le_left t (-1))] at hs
    obtain ⟨hs1, hs2⟩ := hs
    have hsneg : s < 0 := lt_of_le_of_lt hs2 h
    refine ⟨?_, ?_, fun _ => by nlinarith⟩
    · rw [abs_of_neg h, abs_of_neg hsneg]; linarith
    · rw [abs_of_neg h, abs_of_neg hsneg]
      rcases le_total t (-1) with h' | h'
      · rw [min_eq_left h'] at hs1; simp only [le_max_iff]; left; linarith
      · rw [min_eq_right h'] at hs1; simp only [le_max_iff]; right; linarith
  · subst h; simp [outer] at hs; simp [hs]
  · rw [outer, if_pos h, Set.uIcc_of_ge (le_max_left t 1)] at hs
    obtain ⟨hs1, hs2⟩ := hs
    have hspos : 0 < s := lt_of_lt_of_le h hs1
    refine ⟨by rw [abs_of_pos h, abs_of_pos hspos]; exact hs1, ?_, fun _ => by positivity⟩
    rw [abs_of_pos hspos, abs_of_pos h]
    exact hs2

theorem outer_of_abs_le_one {t : ℝ} (ht : t ≠ 0) (h1 : |t| ≤ 1) :
    outer t = if 0 < t then 1 else -1 := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [abs_of_neg h] at h1
    rw [outer, if_neg (by linarith), if_pos h, if_neg (by linarith), min_eq_right (by linarith)]
  · exact absurd h ht
  · rw [abs_of_pos h] at h1
    rw [outer, if_pos h, if_pos h, max_eq_right h1]

/-- The Volterra operator: `Vop beta lam psi u` is the solution of
`y' = u (lam t) + psi (lam t) - beta y` on each side of the origin that vanishes at the
outer endpoint of the unit shell. -/
noncomputable def Vop (beta lam : ℝ) (psi u : ℝ → ℝ) : ℝ → ℝ :=
  fun t => ∫ s in (outer t)..t, Real.exp (-beta * (t - s)) * (u (lam * s) + psi (lam * s))

/-- Margin parameter: the seed and all iterates vanish on `1 - dlt ≤ |t|`. -/
noncomputable def dlt (lam e : ℝ) : ℝ := min (1 / 2) (e / (2 * |lam|))

section Basic

variable {beta lam e : ℝ}

theorem dlt_pos (hlam : 1 < |lam|) (he : 0 < e) : 0 < dlt lam e := by
  have : (0:ℝ) < 2 * |lam| := by linarith
  exact lt_min (by norm_num) (by positivity)

theorem dlt_le_half : dlt lam e ≤ 1 / 2 := min_le_left _ _

theorem lam_mul_dlt_lt (hlam : 1 < |lam|) (he : 0 < e) : |lam| * dlt lam e < e := by
  have h2 : (0:ℝ) < |lam| := by linarith
  have : dlt lam e ≤ e / (2 * |lam|) := min_le_right _ _
  calc |lam| * dlt lam e ≤ |lam| * (e / (2 * |lam|)) := by nlinarith
    _ = e / 2 := by field_simp
    _ < e := by linarith

end Basic

section TopLemmas

variable {beta lam e K r : ℝ} {psi u : ℝ → ℝ}

theorem lam_ne_zero (hlam : 1 < |lam|) : lam ≠ 0 := by
  intro h; rw [h] at hlam; simp at hlam; linarith

/-- On the interval of integration the exponential factor is bounded by `exp (2|beta|)`. -/
theorem exp_factor_le {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1) :
    |Real.exp (-beta * (t - s))| ≤ Real.exp (2 * |beta|) := by
  rw [abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  have h1 : |t - s| ≤ 2 := by
    rw [abs_le] at ht hs ⊢
    constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
  have := abs_nonneg beta
  nlinarith [neg_abs_le (beta * (t - s)), abs_mul beta (t - s),
    mul_le_mul_of_nonneg_left h1 (abs_nonneg beta)]

/-- Integrability of the integrand on intervals avoiding the origin. -/
theorem Vop_integrable (hlam : 1 < |lam|) (hu : ∀ x ≠ (0:ℝ), ContinuousAt u x)
    (hpsi : ∀ x ≠ (0:ℝ), ContinuousAt psi x) (t : ℝ) {a b : ℝ}
    (hab : ∀ s ∈ Set.uIcc a b, s ≠ 0) :
    IntervalIntegrable (fun s => Real.exp (-beta * (t - s)) * (u (lam * s) + psi (lam * s)))
      MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  intro s hs
  have hs0 : lam * s ≠ 0 := mul_ne_zero (lam_ne_zero hlam) (hab s hs)
  refine ContinuousAt.continuousWithinAt ?_
  exact ((Real.continuous_exp.continuousAt).comp (by fun_prop)).mul
    (((hu _ hs0).comp (by fun_prop)).add ((hpsi _ hs0).comp (by fun_prop)))

/-- If both the input and the inhomogeneity vanish far out, so does the output. -/
theorem Vop_supp (hlam : 1 < |lam|) (he : 0 < e)
    (hpsi : ∀ x, |lam| - e < |x| → psi x = 0)
    (hu : ∀ x, 1 - dlt lam e ≤ |x| → u x = 0) (t : ℝ) (ht : 1 - dlt lam e ≤ |t|) :
    Vop beta lam psi u t = 0 := by
  rw [Vop, intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_,
    intervalIntegral.integral_zero]
  intro s hs
  obtain ⟨h1, _, _⟩ := mem_uIcc_outer t s hs
  have hs1 : 1 - dlt lam e ≤ |s| := le_trans ht h1
  have hdh : dlt lam e ≤ 1 / 2 := dlt_le_half
  have hlam0 : (0:ℝ) < |lam| := by linarith
  have h2 : |lam| - e < |lam * s| := by
    rw [abs_mul]
    have := lam_mul_dlt_lt hlam he
    nlinarith
  have h3 : 1 - dlt lam e ≤ |lam * s| := by
    rw [abs_mul]
    nlinarith [abs_nonneg s]
  simp [hpsi _ h2, hu _ h3]

/-- The base case of the previous lemma (`u = 0`). -/
theorem Vop_supp_base (hlam : 1 < |lam|) (he : 0 < e)
    (hpsi : ∀ x, |lam| - e < |x| → psi x = 0) (t : ℝ) (ht : 1 - dlt lam e ≤ |t|) :
    Vop beta lam psi 0 t = 0 :=
  Vop_supp hlam he hpsi (fun _ _ => rfl) t ht

/-- Near a nonzero point of the open unit interval the outer endpoint is locally constant. -/
theorem outer_eventuallyEq {t : ℝ} (ht : t ≠ 0) (h1 : |t| < 1) :
    ∀ᶠ x in nhds t, outer x = outer t := by
  have hS : IsOpen {x : ℝ | 0 < x * t ∧ |x| < 1} := by
    have h1 : IsOpen {x : ℝ | 0 < x * t} := isOpen_lt continuous_const (by fun_prop)
    have h2 : IsOpen {x : ℝ | |x| < 1} := isOpen_lt (by fun_prop) continuous_const
    exact h1.inter h2
  have htmem : t ∈ {x : ℝ | 0 < x * t ∧ |x| < 1} := ⟨mul_self_pos.2 ht, h1⟩
  filter_upwards [hS.mem_nhds htmem] with x hx
  obtain ⟨hx1, hx2⟩ := hx
  rcases lt_trichotomy t 0 with h | h | h
  · have hxneg : x < 0 := by nlinarith
    rw [outer_of_abs_le_one (ne_of_lt hxneg) hx2.le, outer_of_abs_le_one ht h1.le,
      if_neg (not_lt.2 hxneg.le), if_neg (not_lt.2 h.le)]
  · exact absurd h ht
  · have hxpos : 0 < x := by nlinarith
    rw [outer_of_abs_le_one (ne_of_gt hxpos) hx2.le, outer_of_abs_le_one ht h1.le,
      if_pos hxpos, if_pos h]

/-- If the input vanishes on `r ≤ |x|`, the output vanishes on `r / |lam| ≤ |t|`. -/
theorem Vop_supp_step (hlam : 1 < |lam|)
    (hu : ∀ x, r ≤ |x| → u x = 0) (t : ℝ) (ht : r / |lam| ≤ |t|) :
    Vop beta lam 0 u t = 0 := by
  rw [Vop, intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_,
    intervalIntegral.integral_zero]
  intro s hs
  obtain ⟨h1, _, _⟩ := mem_uIcc_outer t s hs
  have habs : r ≤ |lam * s| := by
    rw [abs_mul]
    have h2 : r / |lam| ≤ |s| := le_trans ht h1
    rw [div_le_iff₀ (by linarith)] at h2
    nlinarith [abs_nonneg s]
  simp [hu _ habs]

/-- Sup bound for the base iterate. -/
theorem Vop_bound_base (hlam : 1 < |lam|) (he : 0 < e)
    (hpsi : ∀ x, |lam| - e < |x| → psi x = 0) (hpsiK : ∀ x, |psi x| ≤ K) (t : ℝ) :
    |Vop beta lam psi 0 t| ≤ 2 * Real.exp (2 * |beta|) * K := by
  have hK : 0 ≤ K := le_trans (abs_nonneg (psi 0)) (hpsiK 0)
  have hexp : (0:ℝ) < Real.exp (2 * |beta|) := Real.exp_pos _
  rcases le_or_gt (1 - dlt lam e) |t| with ht | ht
  · rw [Vop_supp_base hlam he hpsi t ht]
    simp
    positivity
  · have hdpos := dlt_pos hlam he
    have ht1 : |t| ≤ 1 := by
      have := dlt_le_half (lam := lam) (e := e)
      linarith
    have houter : |outer t| ≤ 1 := by
      rcases eq_or_ne t 0 with rfl | h0
      · simp [outer]
      · rw [outer_of_abs_le_one h0 ht1]
        split <;> simp
    have hbound : ∀ s ∈ Set.uIoc (outer t) t,
        ‖Real.exp (-beta * (t - s)) * ((0:ℝ → ℝ) (lam * s) + psi (lam * s))‖
          ≤ Real.exp (2 * |beta|) * K := by
      intro s hs
      have hs' : s ∈ Set.uIcc (outer t) t := Set.uIoc_subset_uIcc hs
      obtain ⟨_, h2, _⟩ := mem_uIcc_outer t s hs'
      have hs1 : |s| ≤ 1 := le_trans h2 (by simp [ht1])
      have h3 := exp_factor_le (beta := beta) ht1 hs1
      rw [Real.norm_eq_abs, abs_mul]
      simp only [Pi.zero_apply, zero_add]
      exact mul_le_mul h3 (hpsiK _) (abs_nonneg _) hexp.le
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs] at this
    have hlen : |t - outer t| ≤ 2 := by
      rw [abs_le] at ht1 houter ⊢
      constructor <;> linarith [ht1.1, ht1.2, houter.1, houter.2]
    calc |Vop beta lam psi 0 t| ≤ Real.exp (2 * |beta|) * K * |t - outer t| := this
      _ ≤ Real.exp (2 * |beta|) * K * 2 := by
          apply mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = 2 * Real.exp (2 * |beta|) * K := by ring

/-- Sup bound for a step, exploiting the shrinking support. -/
theorem Vop_bound_step (hlam : 1 < |lam|) (hr : 0 < r) (hr1 : r ≤ 1)
    (hcont : ∀ x ≠ (0:ℝ), ContinuousAt u x)
    (hu : ∀ x, r ≤ |x| → u x = 0) (huK : ∀ x, |u x| ≤ K) (hK : 0 ≤ K) (t : ℝ) :
    |Vop beta lam 0 u t| ≤ Real.exp (2 * |beta|) * K * (r / |lam|) := by
  have hexp : (0:ℝ) < Real.exp (2 * |beta|) := Real.exp_pos _
  have hlam0 : (0:ℝ) < |lam| := by linarith
  have hmpos : 0 < r / |lam| := by positivity
  have hrho : r / |lam| < r := by
    rw [div_lt_iff₀ hlam0]; nlinarith
  have hm1 : r / |lam| ≤ 1 := le_of_lt (lt_of_lt_of_le hrho hr1)
  set F : ℝ → ℝ := fun s => Real.exp (-beta * (t - s)) * (u (lam * s) + (0:ℝ → ℝ) (lam * s))
    with hF
  rcases le_or_gt (r / |lam|) |t| with hbig | hsmall
  · rw [Vop_supp_step hlam hu t hbig, abs_zero]
    positivity
  · have ht1 : |t| ≤ 1 := le_of_lt (lt_of_lt_of_le hsmall hm1)
    -- the integrand vanishes where `|s| ≥ r / |lam|`
    have hFzero : ∀ s : ℝ, r / |lam| ≤ |s| → F s = 0 := by
      intro s hs
      have : r ≤ |lam * s| := by
        rw [abs_mul]
        rw [div_le_iff₀ hlam0] at hs
        nlinarith [abs_nonneg s]
      simp [hF, hu _ this]
    -- pointwise bound on the integrand
    have hFbound : ∀ s : ℝ, |s| ≤ 1 → |F s| ≤ Real.exp (2 * |beta|) * K := by
      intro s hs
      rw [hF]
      simp only [Pi.zero_apply, add_zero, abs_mul]
      exact mul_le_mul (exp_factor_le ht1 hs) (huK _) (abs_nonneg _) hexp.le
    have hcontF : ∀ s ≠ (0:ℝ), ContinuousAt F s := by
      intro s hs
      have hs0 : lam * s ≠ 0 := mul_ne_zero (lam_ne_zero hlam) hs
      exact ((Real.continuous_exp.continuousAt).comp (by fun_prop)).mul
        (((hcont _ hs0).comp (by fun_prop)).add (by fun_prop))
    have hintF : ∀ {a b : ℝ}, (∀ s ∈ Set.uIcc a b, s ≠ 0) →
        IntervalIntegrable F MeasureTheory.volume a b := by
      intro a b hab
      exact ContinuousOn.intervalIntegrable (fun s hs => (hcontF s (hab s hs)).continuousWithinAt)
    rcases lt_trichotomy t 0 with hneg | hzero | hpos
    · -- negative side
      have hout : outer t = -1 := by
        rw [outer_of_abs_le_one (ne_of_lt hneg) ht1, if_neg (not_lt.2 hneg.le)]
      have habst : -(r / |lam|) < t := by
        rw [abs_of_neg hneg] at hsmall; linarith
      have hsub1 : ∀ s ∈ Set.uIcc (-1 : ℝ) (-(r / |lam|)), s ≠ 0 := by
        intro s hs
        rw [Set.uIcc_of_le (by linarith)] at hs
        exact ne_of_lt (lt_of_le_of_lt hs.2 (by linarith))
      have hsub2 : ∀ s ∈ Set.uIcc (-(r / |lam|)) t, s ≠ 0 := by
        intro s hs
        rw [Set.uIcc_of_le habst.le] at hs
        exact ne_of_lt (lt_of_le_of_lt hs.2 hneg)
      have hzero1 : ∫ s in (-1 : ℝ)..(-(r / |lam|)), F s = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_,
          intervalIntegral.integral_zero]
        intro s hs
        rw [Set.uIcc_of_le (by linarith)] at hs
        refine hFzero s ?_
        rw [abs_of_neg (lt_of_le_of_lt hs.2 (by linarith))]
        linarith [hs.2]
      have hsplit : Vop beta lam 0 u t
          = (∫ s in (-1 : ℝ)..(-(r / |lam|)), F s) + ∫ s in (-(r / |lam|))..t, F s := by
        rw [Vop, hout]
        exact (intervalIntegral.integral_add_adjacent_intervals (hintF hsub1) (hintF hsub2)).symm
      rw [hsplit, hzero1, zero_add]
      have hbnd : ∀ s ∈ Set.uIoc (-(r / |lam|)) t, ‖F s‖ ≤ Real.exp (2 * |beta|) * K := by
        intro s hs
        have hs' : s ∈ Set.uIcc (-(r / |lam|)) t := Set.uIoc_subset_uIcc hs
        rw [Set.uIcc_of_le habst.le] at hs'
        refine hFbound s ?_
        rw [abs_le]
        constructor
        · linarith [hs'.1]
        · have : t ≤ 0 := hneg.le
          linarith [hs'.2]
      have := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
      rw [Real.norm_eq_abs] at this
      have hlen : |t - -(r / |lam|)| ≤ r / |lam| := by
        rw [abs_of_neg hneg] at hsmall
        rw [abs_le]
        constructor <;> linarith
      calc |∫ s in (-(r / |lam|))..t, F s| ≤ Real.exp (2 * |beta|) * K * |t - -(r / |lam|)| := this
        _ ≤ Real.exp (2 * |beta|) * K * (r / |lam|) := by
            apply mul_le_mul_of_nonneg_left hlen (by positivity)
    · subst hzero
      have : Vop beta lam 0 u 0 = 0 := by simp [Vop, outer]
      rw [this, abs_zero]
      positivity
    · -- positive side
      have hout : outer t = 1 := by
        rw [outer_of_abs_le_one (ne_of_gt hpos) ht1, if_pos hpos]
      have habst : t < r / |lam| := by
        rw [abs_of_pos hpos] at hsmall; linarith
      have hsub1 : ∀ s ∈ Set.uIcc (1 : ℝ) (r / |lam|), s ≠ 0 := by
        intro s hs
        rw [Set.uIcc_of_ge hm1] at hs
        exact ne_of_gt (lt_of_lt_of_le hmpos hs.1)
      have hsub2 : ∀ s ∈ Set.uIcc (r / |lam|) t, s ≠ 0 := by
        intro s hs
        rw [Set.uIcc_of_ge habst.le] at hs
        exact ne_of_gt (lt_of_lt_of_le hpos hs.1)
      have hzero1 : ∫ s in (1 : ℝ)..(r / |lam|), F s = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_,
          intervalIntegral.integral_zero]
        intro s hs
        rw [Set.uIcc_of_ge hm1] at hs
        refine hFzero s ?_
        rw [abs_of_pos (lt_of_lt_of_le hmpos hs.1)]
        exact hs.1
      have hsplit : Vop beta lam 0 u t
          = (∫ s in (1 : ℝ)..(r / |lam|), F s) + ∫ s in (r / |lam|)..t, F s := by
        rw [Vop, hout]
        exact (intervalIntegral.integral_add_adjacent_intervals (hintF hsub1) (hintF hsub2)).symm
      rw [hsplit, hzero1, zero_add]
      have hbnd : ∀ s ∈ Set.uIoc (r / |lam|) t, ‖F s‖ ≤ Real.exp (2 * |beta|) * K := by
        intro s hs
        have hs' : s ∈ Set.uIcc (r / |lam|) t := Set.uIoc_subset_uIcc hs
        rw [Set.uIcc_of_ge habst.le] at hs'
        refine hFbound s ?_
        rw [abs_le]
        constructor
        · linarith [hs'.1, hpos.le]
        · linarith [hs'.2]
      have := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
      rw [Real.norm_eq_abs] at this
      have hlen : abs (t - r / |lam|) ≤ r / |lam| := by
        rw [abs_le]
        constructor <;> linarith
      calc |∫ s in (r / |lam|)..t, F s| ≤ Real.exp (2 * |beta|) * K * abs (t - r / |lam|) := this
        _ ≤ Real.exp (2 * |beta|) * K * (r / |lam|) := by
            apply mul_le_mul_of_nonneg_left hlen (by positivity)

/-- The output solves the inhomogeneous equation away from the origin. -/
theorem Vop_hasDerivAt (hlam : 1 < |lam|) (he : 0 < e)
    (hcont : ∀ x ≠ (0:ℝ), ContinuousAt u x) (hpsic : ∀ x ≠ (0:ℝ), ContinuousAt psi x)
    (hpsi : ∀ x, |lam| - e < |x| → psi x = 0)
    (hu : ∀ x, 1 - dlt lam e ≤ |x| → u x = 0) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (Vop beta lam psi u)
      (u (lam * t) + psi (lam * t) - beta * Vop beta lam psi u t) t := by
  have hd := dlt_pos hlam he
  have hdh : dlt lam e ≤ 1 / 2 := dlt_le_half
  have hlam1 : (1:ℝ) < |lam| := hlam
  have hlam0 : lam ≠ 0 := lam_ne_zero hlam
  rcases le_or_gt |t| (1 - dlt lam e) with hsmall | hbig
  · -- inside the unit shell: differentiate the primitive
    have htlt1 : |t| < 1 := by linarith
    set c := outer t with hc
    set k : ℝ → ℝ := fun s => Real.exp (beta * s) * (u (lam * s) + psi (lam * s)) with hk
    -- the interval of integration avoids the origin
    have hne : ∀ {x : ℝ}, x ≠ 0 → (∀ s ∈ Set.uIcc (outer x) x, s ≠ 0) := by
      intro x hx s hs
      obtain ⟨h1, _, _⟩ := mem_uIcc_outer x s hs
      intro h0
      rw [h0, abs_zero] at h1
      exact hx (abs_eq_zero.1 (le_antisymm h1 (abs_nonneg x)))
    have hkcont : ∀ x ≠ (0:ℝ), ContinuousAt k x := by
      intro x hx
      have hx0 : lam * x ≠ 0 := mul_ne_zero hlam0 hx
      exact ((Real.continuous_exp.continuousAt).comp (by fun_prop)).mul
        (((hcont _ hx0).comp (by fun_prop)).add ((hpsic _ hx0).comp (by fun_prop)))
    -- `Vop` agrees with `exp (-beta x) * (primitive of k)` near `t`
    have hrewrite : ∀ x : ℝ, x ≠ 0 → outer x = c →
        Vop beta lam psi u x = Real.exp (-beta * x) * ∫ s in c..x, k s := by
      intro x hx hox
      rw [Vop, hox, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      rw [hk]
      simp only
      rw [← mul_assoc, ← Real.exp_add]
      ring_nf
    have hev : Vop beta lam psi u =ᶠ[nhds t] fun x => Real.exp (-beta * x) * ∫ s in c..x, k s := by
      have hne0 : ∀ᶠ x in nhds t, x ≠ 0 := eventually_ne_nhds ht
      filter_upwards [outer_eventuallyEq ht htlt1, hne0] with x hox hx
      exact hrewrite x hx hox
    -- FTC for the primitive
    have hSopen : IsOpen {x : ℝ | 0 < x * t} := isOpen_lt continuous_const (by fun_prop)
    have hStmem : t ∈ {x : ℝ | 0 < x * t} := mul_self_pos.2 ht
    have hSne : ∀ x ∈ {x : ℝ | 0 < x * t}, x ≠ 0 := by
      intro x hx h0
      rw [h0] at hx
      simp at hx
    have hmeas : StronglyMeasurableAtFilter k (nhds t) MeasureTheory.volume :=
      ContinuousOn.stronglyMeasurableAtFilter hSopen
        (fun x hx => (hkcont x (hSne x hx)).continuousWithinAt) t hStmem
    have hint : IntervalIntegrable k MeasureTheory.volume c t := by
      refine ContinuousOn.intervalIntegrable (fun s hs => ?_)
      exact (hkcont s (hne ht s hs)).continuousWithinAt
    have hA : HasDerivAt (fun x => ∫ s in c..x, k s) (k t) t :=
      intervalIntegral.integral_hasDerivAt_right hint hmeas (hkcont t ht)
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-beta * x))
        (Real.exp (-beta * t) * (-beta)) t := by
      simpa using ((hasDerivAt_id t).const_mul (-beta)).exp
    have hprod := hexp.mul hA
    rw [hev.hasDerivAt_iff]
    convert hprod using 1
    have hVt : Vop beta lam psi u t = Real.exp (-beta * t) * ∫ s in c..t, k s :=
      hrewrite t ht rfl
    rw [hVt, hk]
    simp only
    have hee : Real.exp (-beta * t) * Real.exp (beta * t) = 1 := by
      rw [← Real.exp_add]; simp
    linear_combination (-(u (lam * t) + psi (lam * t))) * hee
  · -- outside: everything vanishes near `t`
    have hzero : ∀ x ∈ {x : ℝ | 1 - dlt lam e < |x|}, Vop beta lam psi u x = 0 :=
      fun x hx => Vop_supp hlam he hpsi hu x (le_of_lt hx)
    have hopen : IsOpen {x : ℝ | 1 - dlt lam e < |x|} := isOpen_lt continuous_const (by fun_prop)
    have hev : Vop beta lam psi u =ᶠ[nhds t] fun _ => (0:ℝ) :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hbig) hzero
    have hderiv : HasDerivAt (Vop beta lam psi u) 0 t :=
      (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq hev
    have habs : 1 - dlt lam e < |lam * t| := by
      rw [abs_mul]
      nlinarith [abs_nonneg t]
    have h1 : u (lam * t) = 0 := hu _ habs.le
    have h2 : psi (lam * t) = 0 := by
      refine hpsi _ ?_
      rw [abs_mul]
      have := lam_mul_dlt_lt hlam he
      nlinarith [abs_nonneg t]
    have h3 : Vop beta lam psi u t = 0 := Vop_supp hlam he hpsi hu t hbig.le
    simpa [h1, h2, h3] using hderiv

/-- Continuity of the output away from the origin. -/
theorem Vop_continuousAt (hlam : 1 < |lam|) (he : 0 < e)
    (hcont : ∀ x ≠ (0:ℝ), ContinuousAt u x) (hpsic : ∀ x ≠ (0:ℝ), ContinuousAt psi x)
    (hpsi : ∀ x, |lam| - e < |x| → psi x = 0)
    (hu : ∀ x, 1 - dlt lam e ≤ |x| → u x = 0) {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt (Vop beta lam psi u) t :=
  (Vop_hasDerivAt hlam he hcont hpsic hpsi hu ht).continuousAt

end TopLemmas

section Iterates

variable {beta lam e K : ℝ} {phi : ℝ → ℝ}

/-- The Picard iterates of the Volterra operator. -/
noncomputable def Dseq (beta lam : ℝ) (phi : ℝ → ℝ) : ℕ → (ℝ → ℝ)
  | 0 => Vop beta lam phi 0
  | (n + 1) => Vop beta lam 0 (Dseq beta lam phi n)

/-- The support radius of the `n`-th iterate. -/
noncomputable def rad (lam e : ℝ) (n : ℕ) : ℝ := (1 - dlt lam e) / |lam| ^ n

/-- The sup bound of the `n`-th iterate. -/
noncomputable def bnd (beta lam e K : ℝ) : ℕ → ℝ
  | 0 => 2 * Real.exp (2 * |beta|) * K
  | (n + 1) => Real.exp (2 * |beta|) * bnd beta lam e K n * (rad lam e n / |lam|)

theorem rad_zero : rad lam e 0 = 1 - dlt lam e := by simp [rad]

theorem rad_succ (hlam : 1 < |lam|) (n : ℕ) : rad lam e (n + 1) = rad lam e n / |lam| := by
  have h : (0:ℝ) < |lam| := by linarith
  have hp : (0:ℝ) < |lam| ^ n := by positivity
  rw [rad, rad, pow_succ]
  field_simp

theorem rad_pos (hlam : 1 < |lam|) (n : ℕ) : 0 < rad lam e n := by
  have h1 : dlt lam e ≤ 1 / 2 := dlt_le_half
  have : (0:ℝ) < |lam| ^ n := by positivity
  exact div_pos (by linarith) this

theorem rad_le (hlam : 1 < |lam|) (n : ℕ) : rad lam e n ≤ 1 - dlt lam e := by
  have h1 : dlt lam e ≤ 1 / 2 := dlt_le_half
  have hp : (1:ℝ) ≤ |lam| ^ n := one_le_pow₀ (by linarith)
  rw [rad, div_le_iff₀ (by positivity)]
  nlinarith

theorem rad_le_one (hlam : 1 < |lam|) (he : 0 < e) (n : ℕ) : rad lam e n ≤ 1 := by
  have := rad_le (e := e) hlam n
  have := dlt_pos hlam he
  linarith

theorem rad_antitone (hlam : 1 < |lam|) {m n : ℕ} (h : m ≤ n) :
    rad lam e n ≤ rad lam e m := by
  have h1 : dlt lam e ≤ 1 / 2 := dlt_le_half
  have hp : |lam| ^ m ≤ |lam| ^ n := pow_le_pow_right₀ (by linarith) h
  have hpm : (0:ℝ) < |lam| ^ m := by positivity
  have hpn : (0:ℝ) < |lam| ^ n := by positivity
  rw [rad, rad, div_le_div_iff₀ hpn hpm]
  nlinarith

theorem Dseq_supp (hlam : 1 < |lam|) (he : 0 < e)
    (hphis : ∀ x, |lam| - e < |x| → phi x = 0) (n : ℕ) :
    ∀ x, rad lam e n ≤ |x| → Dseq beta lam phi n x = 0 := by
  induction n with
  | zero =>
      intro x hx
      rw [rad_zero] at hx
      exact Vop_supp_base hlam he hphis x hx
  | succ n ih =>
      intro x hx
      rw [rad_succ hlam n] at hx
      exact Vop_supp_step hlam ih x hx

theorem Dseq_continuousAt (hlam : 1 < |lam|) (he : 0 < e) (hphic : Continuous phi)
    (hphis : ∀ x, |lam| - e < |x| → phi x = 0) (n : ℕ) :
    ∀ x ≠ (0:ℝ), ContinuousAt (Dseq beta lam phi n) x := by
  induction n with
  | zero =>
      intro x hx
      exact Vop_continuousAt hlam he (fun y _ => continuousAt_const)
        (fun y _ => hphic.continuousAt) hphis (fun _ _ => rfl) hx
  | succ n ih =>
      intro x hx
      refine Vop_continuousAt hlam he ih (fun y _ => continuousAt_const) (fun y _ => rfl)
        (fun y hy => Dseq_supp hlam he hphis n y (le_trans (rad_le hlam n) hy)) hx

theorem Dseq_zero_hasDerivAt (hlam : 1 < |lam|) (he : 0 < e) (hphic : Continuous phi)
    (hphis : ∀ x, |lam| - e < |x| → phi x = 0) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (Dseq beta lam phi 0)
      (phi (lam * x) - beta * Dseq beta lam phi 0 x) x := by
  have := Vop_hasDerivAt (beta := beta) hlam he (u := 0) (psi := phi)
    (fun y _ => continuousAt_const) (fun y _ => hphic.continuousAt) hphis (fun _ _ => rfl) hx
  simpa [Dseq] using this

theorem Dseq_succ_hasDerivAt (hlam : 1 < |lam|) (he : 0 < e) (hphic : Continuous phi)
    (hphis : ∀ x, |lam| - e < |x| → phi x = 0) (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (Dseq beta lam phi (n + 1))
      (Dseq beta lam phi n (lam * x) - beta * Dseq beta lam phi (n + 1) x) x := by
  have := Vop_hasDerivAt (beta := beta) hlam he (u := Dseq beta lam phi n) (psi := 0)
    (Dseq_continuousAt hlam he hphic hphis n) (fun y _ => continuousAt_const) (fun y _ => rfl)
    (fun y hy => Dseq_supp hlam he hphis n y (le_trans (rad_le hlam n) hy)) hx
  simpa [Dseq] using this

theorem bnd_nonneg (hlam : 1 < |lam|) (hK : 0 ≤ K) (n : ℕ) :
    0 ≤ bnd beta lam e K n := by
  induction n with
  | zero => simp only [bnd]; positivity
  | succ n ih =>
      have h1 : 0 < rad lam e n := rad_pos hlam n
      have h2 : (0:ℝ) < |lam| := by linarith
      simp only [bnd]
      positivity

theorem Dseq_bound (hlam : 1 < |lam|) (he : 0 < e) (hphic : Continuous phi)
    (hphis : ∀ x, |lam| - e < |x| → phi x = 0) (hphiK : ∀ x, |phi x| ≤ K) (n : ℕ) :
    ∀ x, |Dseq beta lam phi n x| ≤ bnd beta lam e K n := by
  have hK : 0 ≤ K := le_trans (abs_nonneg (phi 0)) (hphiK 0)
  induction n with
  | zero =>
      intro x
      exact Vop_bound_base hlam he hphis hphiK x
  | succ n ih =>
      intro x
      exact Vop_bound_step hlam (rad_pos hlam n) (rad_le_one hlam he n)
        (Dseq_continuousAt hlam he hphic hphis n)
        (Dseq_supp hlam he hphis n) ih (bnd_nonneg hlam hK n) x

theorem bnd_summable (hlam : 1 < |lam|) (he : 0 < e) (hK : 0 ≤ K) :
    Summable (bnd beta lam e K) := by
  have hC : (0:ℝ) < Real.exp (2 * |beta|) := Real.exp_pos _
  have hlam0 : (0:ℝ) < |lam| := by linarith
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * Real.exp (2 * |beta|) < |lam| ^ N :=
    pow_unbounded_of_one_lt _ hlam
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hb0 : 0 ≤ bnd beta lam e K n := bnd_nonneg hlam hK n
  have hb1 : 0 ≤ bnd beta lam e K (n + 1) := bnd_nonneg hlam hK (n + 1)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hb0, abs_of_nonneg hb1]
  have hpow : |lam| ^ N ≤ |lam| ^ (n + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have hpowpos : (0:ℝ) < |lam| ^ (n + 1) := by positivity
  have hd1 : dlt lam e ≤ 1 / 2 := dlt_le_half
  have hratio : rad lam e n / |lam| ≤ 1 / (2 * Real.exp (2 * |beta|)) := by
    have hrad : rad lam e n / |lam| = (1 - dlt lam e) / |lam| ^ (n + 1) := by
      rw [rad, pow_succ]
      field_simp
    rw [hrad, div_le_div_iff₀ hpowpos (by positivity)]
    have h1 : 1 - dlt lam e ≤ 1 := by linarith [dlt_pos hlam he]
    nlinarith
  have : bnd beta lam e K (n + 1)
      = Real.exp (2 * |beta|) * bnd beta lam e K n * (rad lam e n / |lam|) := rfl
  rw [this]
  have hmul : Real.exp (2 * |beta|) * bnd beta lam e K n * (rad lam e n / |lam|)
      ≤ Real.exp (2 * |beta|) * bnd beta lam e K n * (1 / (2 * Real.exp (2 * |beta|))) := by
    apply mul_le_mul_of_nonneg_left hratio (by positivity)
  refine hmul.trans (le_of_eq ?_)
  field_simp

theorem Vop_at_zero (beta lam : ℝ) (psi u : ℝ → ℝ) : Vop beta lam psi u 0 = 0 := by
  simp [Vop, outer]

theorem Dseq_at_zero (n : ℕ) : Dseq beta lam phi n 0 = 0 := by
  cases n with
  | zero => exact Vop_at_zero _ _ _ _
  | succ n => exact Vop_at_zero _ _ _ _

theorem exists_rad_le (hlam : 1 < |lam|) {c : ℝ} (hc : 0 < c) : ∃ N : ℕ, rad lam e N ≤ c := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 - dlt lam e) / c < |lam| ^ N := pow_unbounded_of_one_lt _ hlam
  refine ⟨N, ?_⟩
  have hpos : (0:ℝ) < |lam| ^ N := by positivity
  rw [rad, div_le_iff₀ hpos]
  rw [div_lt_iff₀ hc] at hN
  nlinarith

/-- The inward correction: a pointwise finite sum of the Picard iterates. -/
noncomputable def Vin (beta lam : ℝ) (phi : ℝ → ℝ) : ℝ → ℝ :=
  fun t => ∑' n : ℕ, Dseq beta lam phi n t

variable {beta lam e K : ℝ} {phi : ℝ → ℝ}

theorem Vin_eq_sum (hlam : 1 < |lam|) (he : 0 < e)
    (hphis : ∀ x, |lam| - e < |x| → phi x = 0) {N : ℕ} {x : ℝ} (hx : rad lam e N ≤ |x|) :
    Vin beta lam phi x = ∑ n ∈ Finset.range N, Dseq beta lam phi n x := by
  refine tsum_eq_sum ?_
  intro n hn
  have hN : N ≤ n := by simpa using Finset.mem_range.not.1 hn
  exact Dseq_supp hlam he hphis n x (le_trans (rad_antitone hlam hN) hx)

theorem Vin_supp (hlam : 1 < |lam|) (he : 0 < e)
    (hphis : ∀ x, |lam| - e < |x| → phi x = 0) {x : ℝ} (hx : 1 - dlt lam e ≤ |x|) :
    Vin beta lam phi x = 0 := by
  rw [Vin_eq_sum hlam he hphis (N := 0) (by rwa [rad_zero])]
  simp

theorem Vin_at_zero : Vin beta lam phi 0 = 0 := by
  simp [Vin, Dseq_at_zero]

theorem Vin_bound (hlam : 1 < |lam|) (he : 0 < e) (hphic : Continuous phi)
    (hphis : ∀ x, |lam| - e < |x| → phi x = 0) (hphiK : ∀ x, |phi x| ≤ K) (x : ℝ) :
    |Vin beta lam phi x| ≤ ∑' n : ℕ, bnd beta lam e K n := by
  have hK : 0 ≤ K := le_trans (abs_nonneg (phi 0)) (hphiK 0)
  have hsummable := bnd_summable (beta := beta) hlam he hK
  have hnn : ∀ n, 0 ≤ bnd beta lam e K n := bnd_nonneg hlam hK
  rcases eq_or_ne x 0 with rfl | hx
  · rw [Vin_at_zero, abs_zero]
    exact tsum_nonneg hnn
  · obtain ⟨N, hN⟩ := exists_rad_le (e := e) hlam (abs_pos.2 hx)
    rw [Vin_eq_sum hlam he hphis hN]
    calc |∑ n ∈ Finset.range N, Dseq beta lam phi n x|
        ≤ ∑ n ∈ Finset.range N, |Dseq beta lam phi n x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range N, bnd beta lam e K n :=
          Finset.sum_le_sum (fun n _ => Dseq_bound hlam he hphic hphis hphiK n x)
      _ ≤ ∑' n : ℕ, bnd beta lam e K n :=
          hsummable.sum_le_tsum _ (fun n _ => hnn n)

theorem Vin_eventuallyEq (hlam : 1 < |lam|) (he : 0 < e)
    (hphis : ∀ x, |lam| - e < |x| → phi x = 0) {x : ℝ} (hx : x ≠ 0) {N : ℕ}
    (hN : rad lam e N ≤ |x| / 2) :
    Vin beta lam phi =ᶠ[nhds x] fun y => ∑ n ∈ Finset.range N, Dseq beta lam phi n y := by
  have hopen : IsOpen {y : ℝ | |x| / 2 < |y|} := isOpen_lt continuous_const (by fun_prop)
  have hmem : x ∈ {y : ℝ | |x| / 2 < |y|} := by
    have : 0 < |x| := abs_pos.2 hx
    simp only [Set.mem_setOf_eq]
    linarith
  refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) (fun y hy => ?_)
  exact Vin_eq_sum hlam he hphis (le_trans hN (le_of_lt hy))

theorem Dseq_sum_continuousAt (hlam : 1 < |lam|) (he : 0 < e) (hphic : Continuous phi)
    (hphis : ∀ x, |lam| - e < |x| → phi x = 0) (N : ℕ) {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt (fun y => ∑ n ∈ Finset.range N, Dseq beta lam phi n y) x := by
  induction N with
  | zero => simpa using continuousAt_const
  | succ N ih =>
      simp only [Finset.sum_range_succ]
      exact ih.add (Dseq_continuousAt hlam he hphic hphis N x hx)

theorem Vin_continuousAt (hlam : 1 < |lam|) (he : 0 < e) (hphic : Continuous phi)
    (hphis : ∀ x, |lam| - e < |x| → phi x = 0) {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt (Vin beta lam phi) x := by
  obtain ⟨N, hN⟩ := exists_rad_le (e := e) hlam (half_pos (abs_pos.2 hx))
  have hev := Vin_eventuallyEq (beta := beta) hlam he hphis hx hN
  exact ContinuousAt.congr (Dseq_sum_continuousAt hlam he hphic hphis N hx) hev.symm

/-- The inward correction solves the inhomogeneous equation away from the origin. -/
theorem Vin_hasDerivAt (hlam : 1 < |lam|) (he : 0 < e) (hphic : Continuous phi)
    (hphis : ∀ x, |lam| - e < |x| → phi x = 0) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (Vin beta lam phi)
      (Vin beta lam phi (lam * x) + phi (lam * x) - beta * Vin beta lam phi x) x := by
  have hlam0 : (0:ℝ) < |lam| := by linarith
  have hxpos : 0 < |x| := abs_pos.2 hx
  obtain ⟨M, hM⟩ := exists_rad_le (e := e) hlam (half_pos hxpos)
  have hM1 : rad lam e (M + 1) ≤ |x| / 2 := le_trans (rad_antitone hlam (Nat.le_succ M)) hM
  have hev := Vin_eventuallyEq (beta := beta) (N := M + 1) hlam he hphis hx hM1
  -- the derivative of the truncated sum
  set d : ℕ → ℝ := fun n =>
    Nat.rec (phi (lam * x) - beta * Dseq beta lam phi 0 x)
      (fun m _ => Dseq beta lam phi m (lam * x) - beta * Dseq beta lam phi (m + 1) x) n with hd
  have hterm : ∀ n : ℕ, HasDerivAt (Dseq beta lam phi n) (d n) x := by
    intro n
    cases n with
    | zero => exact Dseq_zero_hasDerivAt hlam he hphic hphis hx
    | succ m => exact Dseq_succ_hasDerivAt hlam he hphic hphis m hx
  have hsum := HasDerivAt.sum (u := Finset.range (M + 1))
    (A := fun n (y : ℝ) => Dseq beta lam phi n y) (A' := d) (fun n _ => hterm n)
  have hsum' : HasDerivAt (fun y => ∑ n ∈ Finset.range (M + 1), Dseq beta lam phi n y)
      (∑ n ∈ Finset.range (M + 1), d n) x :=
    hsum.congr_of_eventuallyEq (by filter_upwards with y; simp)
  rw [hev.hasDerivAt_iff]
  convert hsum' using 1
  -- identify the sum of derivatives
  have hVx : Vin beta lam phi x = ∑ n ∈ Finset.range (M + 1), Dseq beta lam phi n x :=
    Vin_eq_sum hlam he hphis (le_trans hM1 (by linarith))
  have hVlx : Vin beta lam phi (lam * x) = ∑ n ∈ Finset.range M, Dseq beta lam phi n (lam * x) := by
    refine Vin_eq_sum hlam he hphis ?_
    rw [abs_mul]
    have h1 : rad lam e M ≤ |x| := le_trans hM (by linarith)
    nlinarith
  rw [hVx, hVlx, Finset.sum_range_succ' d M, Finset.sum_range_succ' (fun n => Dseq beta lam phi n x) M]
  have hdsucc : ∀ n : ℕ, d (n + 1)
      = Dseq beta lam phi n (lam * x) - beta * Dseq beta lam phi (n + 1) x := fun n => rfl
  have hd0 : d 0 = phi (lam * x) - beta * Dseq beta lam phi 0 x := rfl
  simp only [hdsucc, hd0, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  ring

end Iterates

end Q756
