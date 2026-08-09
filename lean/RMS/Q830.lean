/-
# Q830 : the differential equation `y * y'' = f`

Formalization of the problem Q830:

* (a) determine the maximal solutions of `y y'' = 1`;
* (b) what can be said of the solutions of `y y'' = f` for an arbitrary map `f : ℝ → ℝ`?

Everything below uses the classical convention: a solution on a set `I ⊆ ℝ` is a `C²`
function `y` (given together with its first and second derivatives `y1`, `y2`) satisfying
`y x * y2 x = f x` for every `x ∈ I`.

## Contents

Part (a) (`y y'' = 1`):
* `IsSolutionOn.ne_zero_one`, `IsSolutionOn.sign_const` : a solution never vanishes and has
  constant sign on an interval;
* `IsSolutionOn.energy_const` : the first integral `½ y'² - log|y|` is constant;
* `IsSolutionOn.abs_ge` : `|y| ≥ |y(x₀)| exp(-y'(x₀)²/2)`;
* `Psi`, `PsiInv`, `sol` : the function `Ψ(q) = √2 ∫₀^q e^{s²} ds`, its inverse, and the
  explicit family `y(x) = ε a exp(Ψ⁻¹((x-τ)/a)²)`;
* `sol_isSolution` : each member of this family is an entire solution;
* `IsSolutionOn.exists_eq_sol` : conversely every solution on an interval is a restriction of
  such a function.  Together these say that the maximal solutions are exactly the `sol ε a τ`,
  `a > 0`, `τ ∈ ℝ`, `ε = ±1`, and that each of them is defined on all of `ℝ`.

Part (b) (arbitrary forcing `f`):
* `IsSolutionOn.continuousOn_forcing` : `f` is necessarily continuous;
* `IsSolutionOn.forcing_eq_zero` : `Z(y) ⊆ Z(f)`;
* `IsSolutionOn.hasDerivAt_forcing_of_zero` : at a zero of `y`, `f'(c) = y'(c) y''(c)`;
* `IsSolutionOn.tendsto_forcing_quadratic` : at a tangential zero, `f(x)/(x-c)² → ½ y''(c)²`;
* `IsSolutionOn.integral_forcing` and `IsSolutionOn.integral_forcing_nonpos_of_zeros` :
  the identity `∫ f = y y'|ₐᵇ - ∫ y'²` and its consequence between two zeros;
* `IsSolutionOn.affine_of_forcing_zero` : for `f ≡ 0` every solution on `ℝ` is affine;
* `exists_two_solutions_flat_zero` : nonuniqueness of the continuation through a flat zero.

## Notes on the formalization

* The printed problem does not specify the regularity or the domain of a "solution"; we use
  the classical convention recalled above, and "maximal" is rendered by the pair of theorems
  `sol_isSolution` (the displayed functions are solutions on all of `ℝ`) and
  `IsSolutionOn.exists_eq_sol` (every solution on an interval is a restriction of one of
  them), which is exactly the content of the claim "these and only these are maximal".
* An interval is formalized as a convex subset of `ℝ`; openness is only assumed where it is
  genuinely needed (pointwise statements at a zero).
* Rather than `y ∈ C²`, the derivatives are carried explicitly as data (`y1`, `y2`), with
  `HasDerivAt` at every point of the domain and continuity of `y2`; for open domains this is
  equivalent to the usual `C²` convention.
* Part (b) statements about local existence at simple/tangent zeros (contraction-mapping
  arguments) and the endpoint asymptotics of Theorems 5-6 of the source answer are not
  formalized here; the necessary conditions and the structural facts listed above are.

Lean 4.28.0, Mathlib (rev 8f9d9cff6bd728b17a24e163c9402775d9e6a365).
-/

import Mathlib

set_option maxHeartbeats 1000000

namespace Q830

open Set Filter Topology

/-- `IsSolutionOn y y1 y2 f I` says that `y` is a classical (`C²`) solution of `y·y'' = f`
on `I`, with first derivative `y1` and second derivative `y2`. -/
structure IsSolutionOn (y y1 y2 f : ℝ → ℝ) (I : Set ℝ) : Prop where
  /-- `y1` is the derivative of `y` on `I`. -/
  deriv1 : ∀ x ∈ I, HasDerivAt y (y1 x) x
  /-- `y2` is the derivative of `y1` on `I`. -/
  deriv2 : ∀ x ∈ I, HasDerivAt y1 (y2 x) x
  /-- the second derivative is continuous (classical `C²` convention). -/
  cont2 : ContinuousOn y2 I
  /-- the equation itself. -/
  eqn : ∀ x ∈ I, y x * y2 x = f x

variable {y y1 y2 f : ℝ → ℝ} {I : Set ℝ}

/-- A function with vanishing derivative on a convex set is constant there. -/
theorem const_of_hasDerivAt_zero (hI : Convex ℝ I) {F : ℝ → ℝ}
    (hF : ∀ x ∈ I, HasDerivAt F 0 x) {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) : F a = F b := by
  have key : ∀ x ∈ I, HasDerivWithinAt F 0 I x := fun x hx => (hF x hx).hasDerivWithinAt
  have hbound : ∀ x ∈ I, ‖(fun _ => (0:ℝ)) x‖ ≤ 0 := by simp
  have h := hI.norm_image_sub_le_of_norm_hasDerivWithin_le (f' := fun _ => (0:ℝ)) (C := 0)
    key hbound ha hb
  simp only [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  exact h.symm

/-! ## Elementary necessary conditions (part (b)) -/

theorem IsSolutionOn.continuousOn (h : IsSolutionOn y y1 y2 f I) : ContinuousOn y I :=
  fun x hx => ((h.deriv1 x hx).continuousAt).continuousWithinAt

theorem IsSolutionOn.continuousOn_deriv (h : IsSolutionOn y y1 y2 f I) : ContinuousOn y1 I :=
  fun x hx => ((h.deriv2 x hx).continuousAt).continuousWithinAt

/-- The forcing term of a classical solution is automatically continuous. -/
theorem IsSolutionOn.continuousOn_forcing (h : IsSolutionOn y y1 y2 f I) : ContinuousOn f I := by
  refine ContinuousOn.congr (h.continuousOn.mul h.cont2) ?_
  intro x hx
  exact (h.eqn x hx).symm

/-- Zeros of a solution are zeros of the forcing term: `Z(y) ⊆ Z(f)`. -/
theorem IsSolutionOn.forcing_eq_zero (h : IsSolutionOn y y1 y2 f I) {c : ℝ} (hc : c ∈ I)
    (hy : y c = 0) : f c = 0 := by
  rw [← h.eqn c hc, hy, zero_mul]

/-- Where the forcing term does not vanish, the solution does not vanish. -/
theorem IsSolutionOn.ne_zero (h : IsSolutionOn y y1 y2 f I) {c : ℝ} (hc : c ∈ I)
    (hf : f c ≠ 0) : y c ≠ 0 := by
  intro hy
  exact hf (h.forcing_eq_zero hc hy)

/-- At a zero of `y`, the forcing term is differentiable with `f'(c) = y'(c)·y''(c)`. -/
theorem IsSolutionOn.hasDerivAt_forcing_of_zero (h : IsSolutionOn y y1 y2 f I) (hI : IsOpen I)
    {c : ℝ} (hc : c ∈ I) (hy : y c = 0) : HasDerivAt f (y1 c * y2 c) c := by
  have hInhds : I ∈ 𝓝 c := hI.mem_nhds hc
  have hg : HasDerivAt (fun x => y x * y2 x) (y1 c * y2 c) c := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hs : Filter.Tendsto (slope y c) (𝓝[≠] c) (𝓝 (y1 c)) :=
      hasDerivAt_iff_tendsto_slope.1 (h.deriv1 c hc)
    have hc2 : Filter.Tendsto y2 (𝓝[≠] c) (𝓝 (y2 c)) :=
      ((h.cont2.continuousAt hInhds).tendsto).mono_left nhdsWithin_le_nhds
    refine (hs.mul hc2).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z - c ≠ 0 := sub_ne_zero.2 hz
    simp only [slope_def_field, hy]
    field_simp
    ring
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [hInhds] with x hx using (h.eqn x hx).symm

/-- At a zero `c` of `y` with `y'(c) = 0`, one has `y(x)/(x-c)² → y''(c)/2` (Taylor expansion
with Peano remainder). -/
theorem IsSolutionOn.tendsto_quadratic (h : IsSolutionOn y y1 y2 f I) (hI : IsOpen I)
    {c : ℝ} (hc : c ∈ I) (hy : y c = 0) (hy1 : y1 c = 0) :
    Filter.Tendsto (fun x => y x / (x - c) ^ 2) (𝓝[≠] c) (𝓝 (y2 c / 2)) := by
  have hInhds : I ∈ 𝓝 c := hI.mem_nhds hc
  have hderiv : ∀ᶠ x in 𝓝 c, HasDerivAt y (y1 x) x := by
    filter_upwards [hInhds] with x hx using h.deriv1 x hx
  have hg : ∀ x : ℝ, HasDerivAt (fun t => (t - c) ^ 2) (2 * (x - c)) x := by
    intro x
    have := ((hasDerivAt_id x).sub_const c).pow 2
    simpa using this
  have hy0 : Filter.Tendsto y (𝓝 c) (𝓝 0) := by
    have hcont : Filter.Tendsto y (𝓝 c) (𝓝 (y c)) := (h.deriv1 c hc).continuousAt
    rwa [hy] at hcont
  have hg0 : Filter.Tendsto (fun x : ℝ => (x - c) ^ 2) (𝓝 c) (𝓝 0) := by
    have hco : Continuous (fun x : ℝ => (x - c) ^ 2) := by fun_prop
    simpa using hco.tendsto c
  have hslope : Filter.Tendsto (fun x => y1 x / (2 * (x - c))) (𝓝[≠] c) (𝓝 (y2 c / 2)) := by
    have hs : Filter.Tendsto (slope y1 c) (𝓝[≠] c) (𝓝 (y2 c)) :=
      hasDerivAt_iff_tendsto_slope.1 (h.deriv2 c hc)
    refine (hs.div_const 2).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z - c ≠ 0 := sub_ne_zero.2 hz
    rw [slope_def_field, hy1]
    field_simp
    ring
  have hright : Filter.Tendsto (fun x => y x / (x - c) ^ 2) (𝓝[>] c) (𝓝 (y2 c / 2)) := by
    refine HasDerivAt.lhopital_zero_nhdsGT (hderiv.filter_mono nhdsWithin_le_nhds)
      (by filter_upwards with x using hg x) ?_ (hy0.mono_left nhdsWithin_le_nhds)
      (hg0.mono_left nhdsWithin_le_nhds)
      (hslope.mono_left (nhdsWithin_mono _ (fun z hz => ne_of_gt hz)))
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : x - c ≠ 0 := sub_ne_zero.2 (ne_of_gt hx)
    simpa using this
  have hleft : Filter.Tendsto (fun x => y x / (x - c) ^ 2) (𝓝[<] c) (𝓝 (y2 c / 2)) := by
    refine HasDerivAt.lhopital_zero_nhdsLT (hderiv.filter_mono nhdsWithin_le_nhds)
      (by filter_upwards with x using hg x) ?_ (hy0.mono_left nhdsWithin_le_nhds)
      (hg0.mono_left nhdsWithin_le_nhds)
      (hslope.mono_left (nhdsWithin_mono _ (fun z hz => ne_of_lt hz)))
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : x - c ≠ 0 := sub_ne_zero.2 (ne_of_lt hx)
    simpa using this
  rw [← nhdsLT_sup_nhdsGT]
  exact hleft.sup hright

/-- Necessary condition at a tangential zero: if `y(c) = y'(c) = 0` then
`f(x)/(x-c)² → ½ y''(c)²`. -/
theorem IsSolutionOn.tendsto_forcing_quadratic (h : IsSolutionOn y y1 y2 f I) (hI : IsOpen I)
    {c : ℝ} (hc : c ∈ I) (hy : y c = 0) (hy1 : y1 c = 0) :
    Filter.Tendsto (fun x => f x / (x - c) ^ 2) (𝓝[≠] c) (𝓝 ((y2 c) ^ 2 / 2)) := by
  have hInhds : I ∈ 𝓝 c := hI.mem_nhds hc
  have hq := h.tendsto_quadratic hI hc hy hy1
  have hc2 : Filter.Tendsto y2 (𝓝[≠] c) (𝓝 (y2 c)) :=
    ((h.cont2.continuousAt hInhds).tendsto).mono_left nhdsWithin_le_nhds
  have hmul := hq.mul hc2
  have hlim : y2 c / 2 * y2 c = (y2 c) ^ 2 / 2 := by ring
  rw [hlim] at hmul
  refine hmul.congr' ?_
  filter_upwards [nhdsWithin_le_nhds hInhds] with x hx
  rw [← h.eqn x hx]
  ring

/-! ## The fundamental integral identity (part (b)) -/

theorem IsSolutionOn.integral_forcing (h : IsSolutionOn y y1 y2 f I) {a b : ℝ}
    (hsub : Set.uIcc a b ⊆ I) :
    ∫ x in a..b, f x = y b * y1 b - y a * y1 a - ∫ x in a..b, (y1 x) ^ 2 := by
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun t => y t * y1 t) ((y1 x) ^ 2 + f x) x := by
    intro x hx
    have hx' : x ∈ I := hsub hx
    have := (h.deriv1 x hx').mul (h.deriv2 x hx')
    have heq : y1 x * y1 x + y x * y2 x = (y1 x) ^ 2 + f x := by
      rw [h.eqn x hx']; ring
    rwa [heq] at this
  have hcont1 : ContinuousOn y1 (Set.uIcc a b) := h.continuousOn_deriv.mono hsub
  have hcontf : ContinuousOn f (Set.uIcc a b) := h.continuousOn_forcing.mono hsub
  have hint1 : IntervalIntegrable (fun x => (y1 x) ^ 2) MeasureTheory.volume a b :=
    (hcont1.pow 2).intervalIntegrable
  have hintf : IntervalIntegrable f MeasureTheory.volume a b := hcontf.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint1.add hintf)
  rw [intervalIntegral.integral_add hint1 hintf] at hFTC
  linarith [hFTC]

/-- Between two zeros of a solution the forcing term has nonpositive integral. -/
theorem IsSolutionOn.integral_forcing_nonpos_of_zeros (h : IsSolutionOn y y1 y2 f I) {a b : ℝ}
    (hab : a ≤ b) (hsub : Set.uIcc a b ⊆ I) (ha : y a = 0) (hb : y b = 0) :
    ∫ x in a..b, f x ≤ 0 := by
  have hid := h.integral_forcing hsub
  have hnn : 0 ≤ ∫ x in a..b, (y1 x) ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
  rw [hid, ha, hb]
  simp only [zero_mul, sub_zero, zero_sub]
  linarith

/-! ## The case `f ≡ 0` : solutions are affine -/

theorem IsSolutionOn.second_deriv_eq_zero_of_forcing_zero
    (h : IsSolutionOn y y1 y2 (fun _ => 0) univ) (c : ℝ) : y2 c = 0 := by
  by_contra hne
  have hcont : ContinuousAt y2 c := (continuousOn_univ.mp h.cont2).continuousAt
  have hne' : ∀ᶠ x in 𝓝 c, y2 x ≠ 0 := hcont.eventually_ne hne
  have hy0 : ∀ᶠ x in 𝓝 c, y x = 0 := by
    filter_upwards [hne'] with x hx
    have := h.eqn x (mem_univ x)
    exact (mul_eq_zero.1 this).resolve_right hx
  have hy1 : ∀ᶠ x in 𝓝 c, y1 x = 0 := by
    filter_upwards [hy0.eventually_nhds] with x hx
    have h1 : HasDerivAt y (y1 x) x := h.deriv1 x (mem_univ x)
    have h2 : HasDerivAt y 0 x :=
      (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq (by filter_upwards [hx] with z hz using hz)
    exact h1.unique h2
  have h1 : HasDerivAt y1 (y2 c) c := h.deriv2 c (mem_univ c)
  have h2 : HasDerivAt y1 0 c :=
    (hasDerivAt_const c (0:ℝ)).congr_of_eventuallyEq (by filter_upwards [hy1] with z hz using hz)
  exact hne (h1.unique h2)

/-- Every classical solution of `y y'' = 0` on `ℝ` is affine. -/
theorem IsSolutionOn.affine_of_forcing_zero (h : IsSolutionOn y y1 y2 (fun _ => 0) univ) :
    ∃ A B : ℝ, ∀ x, y x = A * x + B := by
  have hy2 : ∀ x, y2 x = 0 := h.second_deriv_eq_zero_of_forcing_zero
  have hy1const : ∀ x, y1 x = y1 0 := by
    intro x
    refine const_of_hasDerivAt_zero (I := univ) (convex_univ) ?_ (mem_univ x) (mem_univ 0)
    intro w _
    have := h.deriv2 w (mem_univ w)
    rwa [hy2 w] at this
  refine ⟨y1 0, y 0, ?_⟩
  intro x
  have key : ∀ z : ℝ, y z - y1 0 * z = y 0 - y1 0 * 0 := by
    intro z
    refine const_of_hasDerivAt_zero (I := univ) (F := fun t => y t - y1 0 * t) convex_univ ?_
      (mem_univ z) (mem_univ 0)
    intro w _
    have hd : HasDerivAt (fun t => y t - y1 0 * t) (y1 w - y1 0 * 1) w :=
      (h.deriv1 w (mem_univ w)).sub ((hasDerivAt_id w).const_mul (y1 0))
    have : y1 w - y1 0 * 1 = 0 := by rw [hy1const w]; ring
    rwa [this] at hd
  have := key x
  simp only [mul_zero, sub_zero] at this
  linarith

/-! ## Part (a) : the equation `y y'' = 1` -/

/-- A solution of `y y'' = 1` never vanishes. -/
theorem IsSolutionOn.ne_zero_one (h : IsSolutionOn y y1 y2 (fun _ => 1) I) {c : ℝ} (hc : c ∈ I) :
    y c ≠ 0 :=
  h.ne_zero hc one_ne_zero

/-- A solution of `y y'' = 1` on an interval has constant sign. -/
theorem IsSolutionOn.sign_const (h : IsSolutionOn y y1 y2 (fun _ => 1) I) (hI : Convex ℝ I)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) : 0 < y a * y b := by
  have hsub : uIcc a b ⊆ I := hI.ordConnected.uIcc_subset ha hb
  rcases lt_trichotomy (y a * y b) 0 with hlt | heq | hgt
  · exfalso
    have h0 : (0:ℝ) ∈ uIcc (y a) (y b) := by
      rcases mul_neg_iff.1 hlt with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Set.mem_uIcc.2 (Or.inr ⟨h2.le, h1.le⟩)
      · exact Set.mem_uIcc.2 (Or.inl ⟨h1.le, h2.le⟩)
    obtain ⟨c, hc1, hc2⟩ := intermediate_value_uIcc ((h.continuousOn).mono hsub) h0
    exact h.ne_zero_one (hsub hc1) hc2
  · exact absurd heq (mul_ne_zero (h.ne_zero_one ha) (h.ne_zero_one hb))
  · exact hgt

/-- The first integral (conserved energy) `½ y'² - log|y|` of the equation `y y'' = 1`. -/
theorem IsSolutionOn.energy_const (h : IsSolutionOn y y1 y2 (fun _ => 1) I) (hI : Convex ℝ I)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) :
    (y1 a) ^ 2 / 2 - Real.log |y a| = (y1 b) ^ 2 / 2 - Real.log |y b| := by
  have key : ∀ x ∈ I, HasDerivWithinAt (fun t => (y1 t) ^ 2 / 2 - Real.log (y t)) 0 I x := by
    intro x hx
    have hy : y x ≠ 0 := h.ne_zero_one hx
    have h1 : HasDerivAt (fun t => (y1 t) ^ 2 / 2) (y1 x * y2 x) x := by
      have := ((h.deriv2 x hx).pow 2).div_const 2
      convert this using 1
      ring
    have h2 : HasDerivAt (fun t => Real.log (y t)) (y1 x / y x) x := (h.deriv1 x hx).log hy
    have heq : y1 x * y2 x - y1 x / y x = 0 := by
      have hy2 : y x * y2 x = 1 := h.eqn x hx
      have h3 : y2 x * y x = 1 := by rw [mul_comm]; exact hy2
      field_simp
      rw [h3]
      ring
    have := (h1.sub h2).hasDerivWithinAt (s := I)
    rwa [heq] at this
  have hbound : ∀ x ∈ I, ‖(0 : ℝ)‖ ≤ 0 := by simp
  have := hI.norm_image_sub_le_of_norm_hasDerivWithin_le (f' := fun _ => (0:ℝ)) key hbound ha hb
  simp only [zero_mul, norm_le_zero_iff, sub_eq_zero] at this
  rw [Real.log_abs, Real.log_abs]
  exact this.symm

/-- Consequence of the first integral: `|y|` is bounded below by
`a = |y(x₀)| exp(-y'(x₀)²/2)`, with equality exactly where `y'` vanishes. -/
theorem IsSolutionOn.abs_ge (h : IsSolutionOn y y1 y2 (fun _ => 1) I) (hI : Convex ℝ I)
    {x x₀ : ℝ} (hx : x ∈ I) (hx₀ : x₀ ∈ I) :
    |y x₀| * Real.exp (-(y1 x₀) ^ 2 / 2) ≤ |y x| := by
  have hx0 : |y x| > 0 := abs_pos.2 (h.ne_zero_one hx)
  have hx00 : |y x₀| > 0 := abs_pos.2 (h.ne_zero_one hx₀)
  have hE := h.energy_const hI hx₀ hx
  have hlog : Real.log |y x₀| - (y1 x₀) ^ 2 / 2 ≤ Real.log |y x| := by nlinarith [sq_nonneg (y1 x)]
  calc |y x₀| * Real.exp (-(y1 x₀) ^ 2 / 2)
      = Real.exp (Real.log |y x₀| - (y1 x₀) ^ 2 / 2) := by
        rw [Real.exp_sub, Real.exp_log hx00, neg_div, Real.exp_neg]
        ring
    _ ≤ Real.exp (Real.log |y x|) := Real.exp_le_exp.2 hlog
    _ = |y x| := Real.exp_log hx0

/-! ### The function `Ψ` and the explicit maximal solutions -/

/-- `Ψ q = √2 ∫₀^q exp(s²) ds`. -/
noncomputable def Psi (q : ℝ) : ℝ := Real.sqrt 2 * ∫ s in (0:ℝ)..q, Real.exp (s ^ 2)

theorem hasDerivAt_Psi (q : ℝ) : HasDerivAt Psi (Real.sqrt 2 * Real.exp (q ^ 2)) q := by
  have hc : Continuous fun s : ℝ => Real.exp (s ^ 2) := by fun_prop
  have := (intervalIntegral.integral_hasStrictDerivAt_right
    (hc.intervalIntegrable 0 q) (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).hasDerivAt
  exact this.const_mul _

theorem continuous_Psi : Continuous Psi :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_Psi x).continuousAt

theorem Psi_strictMono : StrictMono Psi := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_Psi x).deriv]
  positivity

theorem Psi_ge (q : ℝ) (hq : 0 ≤ q) : Real.sqrt 2 * q ≤ Psi q := by
  have h : (∫ _s in (0:ℝ)..q, (1:ℝ)) ≤ ∫ s in (0:ℝ)..q, Real.exp (s ^ 2) := by
    refine intervalIntegral.integral_mono_on hq (by simp)
      (Continuous.intervalIntegrable (by fun_prop) 0 q) ?_
    intro x _
    exact Real.one_le_exp (by positivity)
  have h2 : (∫ _s in (0:ℝ)..q, (1:ℝ)) = q := by simp
  simp only [Psi]
  nlinarith [Real.sqrt_nonneg 2, h, h2]

theorem Psi_le (q : ℝ) (hq : q ≤ 0) : Psi q ≤ Real.sqrt 2 * q := by
  have h : (∫ _s in q..(0:ℝ), (1:ℝ)) ≤ ∫ s in q..(0:ℝ), Real.exp (s ^ 2) := by
    refine intervalIntegral.integral_mono_on hq (by simp)
      (Continuous.intervalIntegrable (by fun_prop) q 0) ?_
    intro x _
    exact Real.one_le_exp (by positivity)
  have hsymm : (∫ s in (0:ℝ)..q, Real.exp (s ^ 2)) = -∫ s in q..(0:ℝ), Real.exp (s ^ 2) :=
    intervalIntegral.integral_symm _ _
  have h2 : (∫ _s in q..(0:ℝ), (1:ℝ)) = -q := by simp
  simp only [Psi, hsymm]
  nlinarith [Real.sqrt_nonneg 2, h, h2]

theorem Psi_surjective : Function.Surjective Psi := by
  refine continuous_Psi.surjective ?_ ?_
  · refine tendsto_atTop_mono' atTop ?_
      (Filter.Tendsto.const_mul_atTop (by positivity : (0:ℝ) < Real.sqrt 2) tendsto_id)
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with q hq using Psi_ge q hq
  · refine tendsto_atBot_mono' atBot ?_
      (Filter.Tendsto.const_mul_atBot (by positivity : (0:ℝ) < Real.sqrt 2) tendsto_id)
    filter_upwards [Filter.eventually_le_atBot (0:ℝ)] with q hq using Psi_le q hq

/-- `Ψ` as an order isomorphism of `ℝ`. -/
noncomputable def psiEquiv : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective Psi Psi_strictMono Psi_surjective

/-- The inverse function of `Ψ`. -/
noncomputable def PsiInv : ℝ → ℝ := fun x => psiEquiv.symm x

theorem Psi_PsiInv (x : ℝ) : Psi (PsiInv x) = x := psiEquiv.apply_symm_apply x

theorem PsiInv_Psi (q : ℝ) : PsiInv (Psi q) = q := psiEquiv.symm_apply_apply q

theorem continuous_PsiInv : Continuous PsiInv := psiEquiv.symm.continuous

theorem hasDerivAt_PsiInv (x : ℝ) :
    HasDerivAt PsiInv (1 / (Real.sqrt 2 * Real.exp ((PsiInv x) ^ 2))) x := by
  have h := HasDerivAt.of_local_left_inverse (f := Psi) (g := PsiInv) (a := x)
    continuous_PsiInv.continuousAt (hasDerivAt_Psi (PsiInv x)) (by positivity)
    (by filter_upwards with z using Psi_PsiInv z)
  simpa [one_div] using h

/-- The explicit entire solutions of `y y'' = 1`:
`y(x) = ε a exp (Ψ⁻¹((x-τ)/a)²)`, equivalently `x = τ + aΨ(q)`, `y = ε a exp(q²)`. -/
noncomputable def sol (eps a tau : ℝ) : ℝ → ℝ :=
  fun x => eps * a * Real.exp ((PsiInv ((x - tau) / a)) ^ 2)

/-- First derivative of `sol`. -/
noncomputable def solD (eps a tau : ℝ) : ℝ → ℝ :=
  fun x => eps * Real.sqrt 2 * PsiInv ((x - tau) / a)

/-- Second derivative of `sol`. -/
noncomputable def solDD (eps a tau : ℝ) : ℝ → ℝ :=
  fun x => eps / (a * Real.exp ((PsiInv ((x - tau) / a)) ^ 2))

theorem hasDerivAt_sol {eps a tau : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (sol eps a tau) (solD eps a tau x) x := by
  simp only [solD]
  set g : ℝ → ℝ := fun x => PsiInv ((x - tau) / a) with hg
  have hlin : HasDerivAt (fun x : ℝ => (x - tau) / a) (1 / a) x := by
    simpa using (((hasDerivAt_id x).sub_const tau).div_const a)
  have hgd : HasDerivAt g ((1 / (Real.sqrt 2 * Real.exp ((g x) ^ 2))) * (1 / a)) x :=
    (hasDerivAt_PsiInv ((x - tau) / a)).comp x hlin
  have hsq : HasDerivAt (fun x => (g x) ^ 2)
      (2 * g x * ((1 / (Real.sqrt 2 * Real.exp ((g x) ^ 2))) * (1 / a))) x := by
    simpa [mul_comm] using hgd.pow 2
  have hfin := (hsq.exp).const_mul (eps * a)
  convert hfin using 1
  have h2 : Real.exp ((g x) ^ 2) > 0 := Real.exp_pos _
  have hs : Real.sqrt 2 > 0 := by positivity
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  simp only [hg]
  ring

theorem hasDerivAt_solD {eps a tau : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (solD eps a tau) (solDD eps a tau x) x := by
  simp only [solDD]
  have hlin : HasDerivAt (fun x : ℝ => (x - tau) / a) (1 / a) x := by
    simpa using (((hasDerivAt_id x).sub_const tau).div_const a)
  have hgd : HasDerivAt (fun x : ℝ => PsiInv ((x - tau) / a))
      ((1 / (Real.sqrt 2 * Real.exp ((PsiInv ((x - tau) / a)) ^ 2))) * (1 / a)) x :=
    (hasDerivAt_PsiInv ((x - tau) / a)).comp x hlin
  have hfin := hgd.const_mul (eps * Real.sqrt 2)
  convert hfin using 1
  have h2 : Real.exp ((PsiInv ((x - tau) / a)) ^ 2) > 0 := Real.exp_pos _
  have hs : Real.sqrt 2 > 0 := by positivity
  field_simp

/-- **Part (a), existence.** For `a > 0`, `τ ∈ ℝ` and `ε = ±1`, the function
`x ↦ ε a exp(Ψ⁻¹((x-τ)/a)²)` is an entire solution of `y y'' = 1`. -/
theorem sol_isSolution {eps a tau : ℝ} (ha : 0 < a) (heps : eps ^ 2 = 1) :
    IsSolutionOn (sol eps a tau) (solD eps a tau) (solDD eps a tau) (fun _ => 1) univ where
  deriv1 x _ := hasDerivAt_sol ha x
  deriv2 x _ := hasDerivAt_solD ha x
  cont2 := by
    apply Continuous.continuousOn
    apply Continuous.div continuous_const
    · exact (continuous_const.mul (Real.continuous_exp.comp
        ((continuous_PsiInv.comp (by fun_prop)).pow 2)))
    · intro x
      have : Real.exp ((PsiInv ((x - tau) / a)) ^ 2) > 0 := Real.exp_pos _
      positivity
  eqn x _ := by
    simp only [sol, solDD]
    have h2 : Real.exp ((PsiInv ((x - tau) / a)) ^ 2) > 0 := Real.exp_pos _
    field_simp
    nlinarith [heps]

/-- Completeness for a positive solution of `y y'' = 1`. -/
theorem IsSolutionOn.exists_eq_sol_pos (h : IsSolutionOn y y1 y2 (fun _ => 1) I) (hI : Convex ℝ I)
    (hpos : ∀ x ∈ I, 0 < y x) {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    ∃ a tau : ℝ, 0 < a ∧ ∀ x ∈ I, y x = sol 1 a tau x := by
  have hs2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set a : ℝ := y x₀ * Real.exp (-(y1 x₀) ^ 2 / 2) with hadef
  have ha : 0 < a := by
    have := hpos x₀ hx₀
    positivity
  set tau : ℝ := x₀ - a * Psi (y1 x₀ / Real.sqrt 2) with htaudef
  -- the solution is recovered from its derivative through the first integral
  have hval : ∀ z ∈ I, y z = a * Real.exp ((y1 z / Real.sqrt 2) ^ 2) := by
    intro z hz
    have hE := h.energy_const hI hx₀ hz
    have hz0 : 0 < y z := hpos z hz
    have hx00 : 0 < y x₀ := hpos x₀ hx₀
    rw [abs_of_pos hz0, abs_of_pos hx00] at hE
    have hlog : Real.log (y z) = Real.log (y x₀) + ((y1 z) ^ 2 / 2 - (y1 x₀) ^ 2 / 2) := by
      linarith
    have hsplit : (y1 z / Real.sqrt 2) ^ 2 = (y1 z) ^ 2 / 2 := by
      rw [div_pow, hsq]
    rw [hsplit, hadef]
    have : y z = Real.exp (Real.log (y z)) := (Real.exp_log hz0).symm
    rw [this, hlog, Real.exp_add, Real.exp_log hx00, Real.exp_sub, neg_div, Real.exp_neg]
    field_simp
  -- the parametrisation constant `tau`
  have hconst : ∀ z ∈ I, z - a * Psi (y1 z / Real.sqrt 2) = tau := by
    intro z hz
    have key : ∀ w ∈ I, HasDerivAt (fun t => t - a * Psi (y1 t / Real.sqrt 2)) 0 w := by
      intro w hw
      have hd : HasDerivAt (fun t => y1 t / Real.sqrt 2) (y2 w / Real.sqrt 2) w :=
        (h.deriv2 w hw).div_const _
      have hcomp : HasDerivAt (fun t => Psi (y1 t / Real.sqrt 2))
          ((Real.sqrt 2 * Real.exp ((y1 w / Real.sqrt 2) ^ 2)) * (y2 w / Real.sqrt 2)) w :=
        (hasDerivAt_Psi _).comp w hd
      have hfin := (hasDerivAt_id w).sub (hcomp.const_mul a)
      have hzero :
          (1 : ℝ) - a * ((Real.sqrt 2 * Real.exp ((y1 w / Real.sqrt 2) ^ 2)) *
            (y2 w / Real.sqrt 2)) = 0 := by
        have h1 : y w * y2 w = 1 := h.eqn w hw
        have h2 : y w = a * Real.exp ((y1 w / Real.sqrt 2) ^ 2) := hval w hw
        set E : ℝ := Real.exp ((y1 w / Real.sqrt 2) ^ 2) with hEdef
        have h3 : a * (E * y2 w) = 1 := by rw [← mul_assoc, ← h2]; exact h1
        have hcancel : (Real.sqrt 2 * E) * (y2 w / Real.sqrt 2) = E * y2 w := by
          field_simp
        rw [hcancel]
        linarith [h3]
      simpa [hzero] using hfin
    have := const_of_hasDerivAt_zero hI key hz hx₀
    rw [this, htaudef]
  refine ⟨a, tau, ha, ?_⟩
  intro x hx
  have h1 : Psi (y1 x / Real.sqrt 2) = (x - tau) / a := by
    have := hconst x hx
    field_simp
    linarith [this]
  have h2 : y1 x / Real.sqrt 2 = PsiInv ((x - tau) / a) := by
    rw [← h1, PsiInv_Psi]
  rw [hval x hx, h2]
  simp [sol]

/-- **Part (a), completeness.** Every classical solution of `y y'' = 1` on an interval is
the restriction of one of the entire solutions `sol ε a τ`. Consequently the maximal solutions
are exactly the functions `sol ε a τ` with `a > 0`, `τ ∈ ℝ`, `ε = ±1`, all defined on `ℝ`. -/
theorem IsSolutionOn.exists_eq_sol (h : IsSolutionOn y y1 y2 (fun _ => 1) I) (hI : Convex ℝ I)
    (hne : I.Nonempty) :
    ∃ eps a tau : ℝ, eps ^ 2 = 1 ∧ 0 < a ∧ ∀ x ∈ I, y x = sol eps a tau x := by
  obtain ⟨x₀, hx₀⟩ := hne
  rcases lt_or_gt_of_ne (h.ne_zero_one hx₀) with hneg | hpos
  · -- negative branch : apply the positive case to `-y`
    have h' : IsSolutionOn (fun t => -y t) (fun t => -y1 t) (fun t => -y2 t) (fun _ => 1) I :=
      ⟨fun x hx => (h.deriv1 x hx).neg, fun x hx => (h.deriv2 x hx).neg, h.cont2.neg,
        fun x hx => by simpa using h.eqn x hx⟩
    have hpos' : ∀ x ∈ I, 0 < -y x := by
      intro x hx
      have := h.sign_const hI hx₀ hx
      nlinarith [this, hneg]
    obtain ⟨a, tau, ha, hEq⟩ := h'.exists_eq_sol_pos hI hpos' hx₀
    refine ⟨-1, a, tau, by norm_num, ha, ?_⟩
    intro x hx
    have := hEq x hx
    simp only [sol] at this ⊢
    linarith [this]
  · have hpos' : ∀ x ∈ I, 0 < y x := by
      intro x hx
      have := h.sign_const hI hx₀ hx
      nlinarith [this, hpos]
    obtain ⟨a, tau, ha, hEq⟩ := h.exists_eq_sol_pos hI hpos' hx₀
    exact ⟨1, a, tau, by norm_num, ha, hEq⟩

/-! ## Failure of uniqueness at a flat zero (part (b))

Using the standard smooth flat function `expNegInvGlue` (which vanishes on `(-∞, 0]` and is
positive on `(0, ∞)`) we build a single forcing term `f` admitting two entire classical
solutions which agree on `[0, ∞)` but differ on `(-∞, 0)`: continuation through a flat zero
is not unique. -/

/-- First derivative of the flat glue function. -/
noncomputable def glue1 : ℝ → ℝ := deriv expNegInvGlue

/-- Second derivative of the flat glue function. -/
noncomputable def glue2 : ℝ → ℝ := deriv (deriv expNegInvGlue)

theorem hasDerivAt_glue (x : ℝ) : HasDerivAt expNegInvGlue (glue1 x) x := by
  have hd : Differentiable ℝ expNegInvGlue :=
    (expNegInvGlue.contDiff (n := ⊤)).differentiable (by simp)
  exact (hd x).hasDerivAt

theorem hasDerivAt_glue1 (x : ℝ) : HasDerivAt glue1 (glue2 x) x := by
  have hcd := ContDiff.iterate_deriv 1 (expNegInvGlue.contDiff (n := ⊤))
  have hd : Differentiable ℝ (deriv expNegInvGlue) := by
    simpa using hcd.differentiable (by simp)
  exact (hd x).hasDerivAt

theorem continuous_glue2 : Continuous glue2 := by
  have hcd := ContDiff.iterate_deriv 2 (expNegInvGlue.contDiff (n := ⊤))
  simpa [glue2, Function.iterate_succ] using hcd.continuous

theorem glue1_eq_zero {x : ℝ} (hx : x < 0) : glue1 x = 0 := by
  have hev : expNegInvGlue =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
    filter_upwards [Iio_mem_nhds hx] with z hz using expNegInvGlue.zero_of_nonpos (le_of_lt hz)
  simp [glue1, hev.deriv_eq]

theorem glue2_eq_zero {x : ℝ} (hx : x < 0) : glue2 x = 0 := by
  have hev : (deriv expNegInvGlue) =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
    filter_upwards [Iio_mem_nhds hx] with z hz using glue1_eq_zero hz
  simp [glue2, hev.deriv_eq]

theorem hasDerivAt_glue_neg (x : ℝ) :
    HasDerivAt (fun t => expNegInvGlue (-t)) (-(glue1 (-x))) x := by
  have := (hasDerivAt_glue (-x)).comp x (hasDerivAt_neg x)
  simpa [Function.comp] using this

theorem hasDerivAt_glue1_neg (x : ℝ) :
    HasDerivAt (fun t => -(glue1 (-t))) (glue2 (-x)) x := by
  have := (hasDerivAt_glue1 (-x)).comp x (hasDerivAt_neg x)
  simpa [Function.comp] using this.neg

/-- The even flat solution `x ↦ φ(x) + φ(-x)`. -/
noncomputable def flatA : ℝ → ℝ := fun x => expNegInvGlue x + expNegInvGlue (-x)

/-- The odd flat solution `x ↦ φ(x) - φ(-x)`. -/
noncomputable def flatB : ℝ → ℝ := fun x => expNegInvGlue x - expNegInvGlue (-x)

/-- Common forcing term of `flatA` and `flatB`. -/
noncomputable def flatF : ℝ → ℝ := fun x => flatA x * (glue2 x + glue2 (-x))

/-- **Nonuniqueness through a flat zero.** There is a continuous forcing term `f` and two
entire classical solutions of `y y'' = f` which coincide on `[0, ∞)` but differ elsewhere. -/
theorem exists_two_solutions_flat_zero :
    IsSolutionOn flatA (fun x => glue1 x - glue1 (-x)) (fun x => glue2 x + glue2 (-x))
        flatF univ ∧
      IsSolutionOn flatB (fun x => glue1 x + glue1 (-x)) (fun x => glue2 x - glue2 (-x))
        flatF univ ∧
      (∀ x, 0 ≤ x → flatA x = flatB x) ∧ flatA (-1) ≠ flatB (-1) := by
  have hcont2 : Continuous (fun x : ℝ => glue2 x + glue2 (-x)) := by
    exact continuous_glue2.add (continuous_glue2.comp continuous_neg)
  have hcont2' : Continuous (fun x : ℝ => glue2 x - glue2 (-x)) := by
    exact continuous_glue2.sub (continuous_glue2.comp continuous_neg)
  have hAeq : ∀ x, flatB x * (glue2 x - glue2 (-x)) = flatF x := by
    intro x
    simp only [flatF, flatA, flatB]
    rcases lt_trichotomy x 0 with hx | hx | hx
    · have h1 : expNegInvGlue x = 0 := expNegInvGlue.zero_of_nonpos hx.le
      have h2 : glue2 x = 0 := glue2_eq_zero hx
      rw [h1, h2]
      ring
    · subst hx
      have h1 : expNegInvGlue (0:ℝ) = 0 := expNegInvGlue.zero_of_nonpos le_rfl
      simp [h1]
    · have h1 : expNegInvGlue (-x) = 0 := expNegInvGlue.zero_of_nonpos (by linarith)
      have h2 : glue2 (-x) = 0 := glue2_eq_zero (by linarith)
      rw [h1, h2]
      ring
  refine ⟨⟨?_, ?_, hcont2.continuousOn, ?_⟩, ⟨?_, ?_, hcont2'.continuousOn, ?_⟩, ?_, ?_⟩
  · intro x _
    exact (hasDerivAt_glue x).add (hasDerivAt_glue_neg x)
  · intro x _
    exact (hasDerivAt_glue1 x).add (hasDerivAt_glue1_neg x)
  · intro x _
    rfl
  · intro x _
    have := (hasDerivAt_glue x).sub (hasDerivAt_glue_neg x)
    simpa [flatB, sub_neg_eq_add] using this
  · intro x _
    have heq : (fun t : ℝ => glue1 t + glue1 (-t)) = fun t : ℝ => glue1 t - -(glue1 (-t)) := by
      funext t; ring
    rw [heq]
    exact (hasDerivAt_glue1 x).sub (hasDerivAt_glue1_neg x)
  · intro x _
    exact hAeq x
  · intro x hx
    have h1 : expNegInvGlue (-x) = 0 := expNegInvGlue.zero_of_nonpos (by linarith)
    simp [flatA, flatB, h1]
  · have h1 : expNegInvGlue (-1 : ℝ) = 0 := expNegInvGlue.zero_of_nonpos (by norm_num)
    have h2 : (0:ℝ) < expNegInvGlue 1 := expNegInvGlue.pos_of_pos one_pos
    simp only [flatA, flatB, h1, neg_neg]
    intro hcontra
    norm_num at hcontra
    linarith

end Q830
