import Mathlib

/-!
# A convexity inequality behind the flat Clifford torus

This auxiliary module proves the scalar inequality

`cos (√((x² + y²)/2)) ≤ (cos x + cos y) / 2`  for `|x| ≤ π`, `|y| ≤ π`,

which is exactly the statement that, in the cone over the Clifford torus
`{(z, w) ∈ ℂ² : |z| = |w|}`, the chord between two points whose phases differ by `x` and `y`
is at most the chord between the corresponding points of the Euclidean plane in polar
coordinates with angular separation `√((x² + y²)/2)`.  In other words it encodes the
flat-torus factor `1/√2`.

The inequality is the midpoint case of the convexity of `t ↦ cos √t` on `[0, π²]`, which in
turn follows from the fact that `u ↦ sin u / u` is antitone on `(0, π]`.
-/

open Real Set

namespace Q748

/-- On `[0, π]` the tangent inequality gives `u cos u ≤ sin u`. -/
theorem mul_cos_le_sin {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ π) : u * Real.cos u ≤ Real.sin u := by
  rcases le_or_gt (π / 2) u with h | h
  · have h1 : Real.cos u ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith [Real.pi_pos])
    have h2 : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi hu hu'
    nlinarith
  · rcases eq_or_lt_of_le hu with rfl | hu0
    · simp
    · have hc : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨by linarith, h⟩
      have h2 := Real.lt_tan hu0 h
      rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hc] at h2
      nlinarith

/-- The unnormalized cardinal sine is antitone on `(0, π]`. -/
theorem sin_div_antitoneOn : AntitoneOn (fun u : ℝ => Real.sin u / u) (Ioc 0 π) := by
  have hint : interior (Ioc (0:ℝ) π) = Ioo 0 π := interior_Ioc
  refine antitoneOn_of_deriv_nonpos (convex_Ioc _ _) ?_ ?_ ?_
  · exact Real.continuousOn_sin.div continuousOn_id fun x hx => ne_of_gt hx.1
  · rw [hint]
    intro x hx
    exact ((Real.differentiable_sin x).div (differentiable_id x)
      (ne_of_gt hx.1)).differentiableWithinAt
  · rw [hint]
    intro x hx
    have hd : HasDerivAt (fun u : ℝ => Real.sin u / u)
        ((Real.cos x * x - Real.sin x * 1) / x ^ 2) x :=
      (Real.hasDerivAt_sin x).div (hasDerivAt_id x) (ne_of_gt hx.1)
    rw [hd.deriv]
    have h1 : x * Real.cos x ≤ Real.sin x := mul_cos_le_sin hx.1.le hx.2.le
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)

/-- `t ↦ cos √t` is convex on `[0, π²]`. -/
theorem cos_sqrt_convexOn : ConvexOn ℝ (Icc 0 (π ^ 2)) fun t : ℝ => Real.cos (Real.sqrt t) := by
  have hint : interior (Icc (0:ℝ) (π ^ 2)) = Ioo 0 (π ^ 2) := interior_Icc
  refine MonotoneOn.convexOn_of_deriv (convex_Icc _ _) ?_ ?_ ?_
  · exact Real.continuous_cos.comp_continuousOn Real.continuous_sqrt.continuousOn
  · rw [hint]
    intro x hx
    exact ((Real.hasDerivAt_cos (Real.sqrt x)).comp x
      (Real.hasDerivAt_sqrt (ne_of_gt hx.1))).differentiableAt.differentiableWithinAt
  · rw [hint]
    have hderiv : ∀ x ∈ Ioo (0:ℝ) (π ^ 2), deriv (fun t : ℝ => Real.cos (Real.sqrt t)) x
        = -(1 / 2) * (Real.sin (Real.sqrt x) / Real.sqrt x) := by
      intro x hx
      have hc : HasDerivAt (fun t : ℝ => Real.cos (Real.sqrt t))
          (-Real.sin (Real.sqrt x) * (1 / (2 * Real.sqrt x))) x :=
        (Real.hasDerivAt_cos (Real.sqrt x)).comp x (Real.hasDerivAt_sqrt (ne_of_gt hx.1))
      rw [hc.deriv]
      have hne : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx.1)
      field_simp
    intro a ha b hb hab
    rw [hderiv a ha, hderiv b hb]
    have hpi : π = Real.sqrt (π ^ 2) := by rw [Real.sqrt_sq Real.pi_pos.le]
    have hsa : Real.sqrt a ∈ Ioc 0 π :=
      ⟨Real.sqrt_pos.2 ha.1, by rw [hpi]; exact Real.sqrt_le_sqrt ha.2.le⟩
    have hsb : Real.sqrt b ∈ Ioc 0 π :=
      ⟨Real.sqrt_pos.2 hb.1, by rw [hpi]; exact Real.sqrt_le_sqrt hb.2.le⟩
    have h := sin_div_antitoneOn hsa hsb (Real.sqrt_le_sqrt hab)
    simp only at h
    linarith

/-- **The flat-torus inequality.**  For phases `x, y` of size at most `π`,
`cos √((x² + y²)/2) ≤ (cos x + cos y)/2`.  Geometrically: the chord in the cone over the
Clifford torus is at most the corresponding planar chord at angular separation
`√((x² + y²)/2)`. -/
theorem cos_quadraticMean_le_avg_cos {x y : ℝ} (hx : |x| ≤ π) (hy : |y| ≤ π) :
    Real.cos (Real.sqrt ((x ^ 2 + y ^ 2) / 2)) ≤ (Real.cos x + Real.cos y) / 2 := by
  have hxm : x ^ 2 ∈ Icc (0:ℝ) (π ^ 2) := by
    refine ⟨by positivity, ?_⟩
    nlinarith [abs_nonneg x, sq_abs x]
  have hym : y ^ 2 ∈ Icc (0:ℝ) (π ^ 2) := by
    refine ⟨by positivity, ?_⟩
    nlinarith [abs_nonneg y, sq_abs y]
  have h := cos_sqrt_convexOn.2 hxm hym (by norm_num : (0:ℝ) ≤ 1 / 2)
    (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have hcx : Real.cos (Real.sqrt (x ^ 2)) = Real.cos x := by
    rw [Real.sqrt_sq_eq_abs, Real.cos_abs]
  have hcy : Real.cos (Real.sqrt (y ^ 2)) = Real.cos y := by
    rw [Real.sqrt_sq_eq_abs, Real.cos_abs]
  rw [hcx, hcy] at h
  have harg : 1 / 2 * x ^ 2 + 1 / 2 * y ^ 2 = (x ^ 2 + y ^ 2) / 2 := by ring
  rw [harg] at h
  linarith

end Q748
