/-
# Q839

Source: https://lucpommeret.com/assets/Qsansreponse260405.pdf , problem Q839.

Let `q ∈ (-1,1)` and let `f : ℝ → ℝ` be continuous with

  `f x = (1 - q * x) * f (q * x)`  for all `x`.

The question asks for the behaviour of `f` at `+∞`.  The key structural facts,
formalized below, are:

* the iteration identity `f x = (∏_{j<N} (1 - q^{j+1} x)) * f (q^N x)`;
* the classification `f x = f 0 * (qx;q)_∞` where `(qx;q)_∞ = ∏_{j≥1} (1 - q^j x)`
  is the Euler product, together with uniqueness and existence of solutions;
* the zeros `f (q^{-m}) = 0` for `m ≥ 1` (`q ≠ 0`), which is exactly the reason no
  ordinary asymptotic equivalent `f(x) ∼ g(x)` with `g` eventually nonzero can exist;
* the degenerate cases `q = 0` (constant solutions) and `q = ±1` (only the zero
  solution);
* (Part II) for `0 < q < 1`, the exact logarithmically periodic formula
  `f x = f 0 (-1)^n E_q(x) Φ_q(u) / (x⁻¹;q)_∞` for `x > 1`, together with the
  properties of the phase profile `Φ_q` and the resulting sign alternation;
* (Part III) for `-1 < q < 0`, the analogous formula
  `f x = f 0 (-1)^n E_q(x) Ψ_q(u) / (x⁻¹;q)_∞` for `x > 1`, obtained from the
  even/odd splitting of the product, with `s = q²`, together with the symmetry,
  positivity on `(0,1)` and endpoint vanishing of `Ψ_q`.

## Scope, and differences with the printed solution

* The printed solution assumes `f` continuous (only continuity at `0` is really used);
  the formal statements assume `Continuous f`, as in the source.
* Infinite products are mathlib's unordered `∏'`; the lemma `tendsto_partialProd`
  (resp. `tendsto_qPoch`) records that they are the limits of the partial products
  `∏_{j<N}`, which is the form in which they are used.
* Real powers such as `x^(-1/2)`, `q^u`, `q^(1-u)` are `Real.rpow`.
* The exact logarithmically periodic identities are formalized both in the case
  `0 < q < 1` (formula (2.1) of the solution) and in the case `-1 < q < 0`
  (formula (2.2), via the even/odd splitting of the product).  The classification,
  the zeros, the unboundedness at `+∞` and the non-existence of an asymptotic
  equivalent are proved for all `q` with `0 < |q| < 1`.
* The convergent inverse-power expansions (2.3)-(2.5) and the power-series expansion
  of the solution are not formalized.

Lean version: 4.28.0, mathlib: rev `v4.28.0`
(commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`).
-/
import Mathlib

open Filter Topology Real

namespace Q839

/-- The Euler ("q-Pochhammer") product `(qx; q)_∞ = ∏_{j ≥ 1} (1 - q^j x)`. -/
noncomputable def eulerProd (q x : ℝ) : ℝ := ∏' j : ℕ, (1 - q ^ (j + 1) * x)

/-- Iterating the functional equation `N` times. -/
theorem funeq_iterate {q : ℝ} {f : ℝ → ℝ} (hf : ∀ x, f x = (1 - q * x) * f (q * x))
    (N : ℕ) (x : ℝ) :
    f x = (∏ j ∈ Finset.range N, (1 - q ^ (j + 1) * x)) * f (q ^ N * x) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [ih, Finset.prod_range_succ, mul_assoc]
      congr 1
      rw [hf (q ^ N * x)]
      ring_nf

/-- For `|q| < 1` the Euler product converges. -/
theorem multipliable_eulerProd {q : ℝ} (hq : |q| < 1) (x : ℝ) :
    Multipliable fun j : ℕ => (1 - q ^ (j + 1) * x) := by
  have hs : Summable fun j : ℕ => |q| ^ j * (|q| * |x|) :=
    (summable_geometric_of_lt_one (abs_nonneg q) hq).mul_right _
  have h : Summable fun j : ℕ => ‖-(q ^ (j + 1) * x)‖ := by
    refine hs.congr fun n => ?_
    simp [pow_succ]
    ring
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable h

/-- The partial products converge to the Euler product. -/
theorem tendsto_partialProd {q : ℝ} (hq : |q| < 1) (x : ℝ) :
    Tendsto (fun n : ℕ => ∏ j ∈ Finset.range n, (1 - q ^ (j + 1) * x)) atTop
      (𝓝 (eulerProd q x)) :=
  (multipliable_eulerProd hq x).tendsto_prod_tprod_nat

@[simp] theorem eulerProd_zero (q : ℝ) : eulerProd q 0 = 1 := by simp [eulerProd]

/-- The Euler product satisfies the functional equation. -/
theorem eulerProd_funeq {q : ℝ} (hq : |q| < 1) (x : ℝ) :
    eulerProd q x = (1 - q * x) * eulerProd q (q * x) := by
  have h1 : Tendsto (fun n : ℕ => ∏ j ∈ Finset.range (n + 1), (1 - q ^ (j + 1) * x)) atTop
      (𝓝 (eulerProd q x)) :=
    (tendsto_partialProd hq x).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ => (1 - q * x) * ∏ j ∈ Finset.range n, (1 - q ^ (j + 1) * (q * x)))
      atTop (𝓝 ((1 - q * x) * eulerProd q (q * x))) :=
    (tendsto_partialProd hq (q * x)).const_mul _
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  rw [Finset.prod_range_succ']
  simp only [pow_zero, pow_succ, one_mul]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

/-- The Euler product is a continuous function of `x`. -/
theorem continuous_eulerProd {q : ℝ} (hq : |q| < 1) : Continuous (eulerProd q) := by
  rw [continuous_iff_continuousAt]
  intro x
  set R : ℝ := |x| + 1 with hR
  have hxR : x ∈ Metric.ball (0 : ℝ) R := by simp [hR]
  have hu : Summable fun j : ℕ => |q| ^ j * (|q| * R) :=
    (summable_geometric_of_lt_one (abs_nonneg q) hq).mul_right _
  have hbdd : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Metric.ball (0 : ℝ) R,
      ‖-(q ^ (n + 1) * y)‖ ≤ |q| ^ n * (|q| * R) := by
    filter_upwards with n y hy
    have hy' : |y| ≤ R := le_of_lt (by simpa [Real.dist_eq] using hy)
    have h1 : ‖-(q ^ (n + 1) * y)‖ = |q| ^ n * (|q| * |y|) := by
      simp [pow_succ]; ring
    have h2 : (0 : ℝ) ≤ |q| ^ n * |q| := by positivity
    rw [h1]
    nlinarith [abs_nonneg y]
  have hcts : ∀ n : ℕ, ContinuousOn (fun y : ℝ => -(q ^ (n + 1) * y)) (Metric.ball 0 R) :=
    fun _ => (by fun_prop : Continuous fun y : ℝ => -(q ^ (_ + 1) * y)).continuousOn
  have H := Summable.hasProdLocallyUniformlyOn_nat_one_add (K := Metric.ball (0 : ℝ) R)
      (f := fun n y => -(q ^ (n + 1) * y)) Metric.isOpen_ball hu hbdd hcts
  rw [HasProdLocallyUniformlyOn] at H
  have hcont : ContinuousOn (fun y : ℝ => ∏' i : ℕ, (1 + -(q ^ (i + 1) * y)))
      (Metric.ball 0 R) := by
    refine H.continuousOn (Filter.Eventually.frequently ?_)
    filter_upwards with s
    exact continuousOn_finset_prod _ fun i _ =>
      (by fun_prop : Continuous fun y : ℝ => 1 + -(q ^ (i + 1) * y)).continuousOn
  have hco : ContinuousOn (eulerProd q) (Metric.ball 0 R) := by
    simpa [eulerProd, sub_eq_add_neg] using hcont
  exact hco.continuousAt (Metric.isOpen_ball.mem_nhds hxR)

/-- Classification: every continuous solution is `f 0` times the Euler product. -/
theorem eq_eulerProd {q : ℝ} (hq : |q| < 1) {f : ℝ → ℝ} (hcont : Continuous f)
    (hf : ∀ x, f x = (1 - q * x) * f (q * x)) (x : ℝ) :
    f x = f 0 * eulerProd q x := by
  have hpow : Tendsto (fun n : ℕ => q ^ n * x) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq
    simpa using this.mul_const x
  have h1 : Tendsto (fun n : ℕ => (∏ j ∈ Finset.range n, (1 - q ^ (j + 1) * x)) * f (q ^ n * x))
      atTop (𝓝 (eulerProd q x * f 0)) :=
    (tendsto_partialProd hq x).mul ((hcont.tendsto 0).comp hpow)
  have h2 : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (eulerProd q x * f 0)) :=
    h1.congr fun n => (funeq_iterate hf n x).symm
  rw [tendsto_const_nhds_iff.1 h2, mul_comm]

/-- Uniqueness: two continuous solutions agreeing at `0` are equal. -/
theorem unique_of_eq_zero {q : ℝ} (hq : |q| < 1) {f g : ℝ → ℝ}
    (hfc : Continuous f) (hgc : Continuous g)
    (hf : ∀ x, f x = (1 - q * x) * f (q * x)) (hg : ∀ x, g x = (1 - q * x) * g (q * x))
    (h0 : f 0 = g 0) : f = g := by
  funext x
  rw [eq_eulerProd hq hfc hf x, eq_eulerProd hq hgc hg x, h0]

/-- Existence: for each `c`, `c * (qx;q)_∞` is a continuous solution with value `c` at `0`. -/
theorem exists_solution {q : ℝ} (hq : |q| < 1) (c : ℝ) :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∀ x, f x = (1 - q * x) * f (q * x)) ∧ f 0 = c := by
  refine ⟨fun x => c * eulerProd q x, continuous_const.mul (continuous_eulerProd hq),
    fun x => ?_, by simp⟩
  show c * eulerProd q x = (1 - q * x) * (c * eulerProd q (q * x))
  rw [eulerProd_funeq hq x]
  ring

/-- Consequently the set of continuous solutions is exactly the line spanned by the
Euler product. -/
theorem solutions_iff {q : ℝ} (hq : |q| < 1) (f : ℝ → ℝ) :
    (Continuous f ∧ ∀ x, f x = (1 - q * x) * f (q * x)) ↔
      ∃ c : ℝ, f = fun x => c * eulerProd q x := by
  constructor
  · rintro ⟨hcont, hf⟩
    exact ⟨f 0, funext fun x => eq_eulerProd hq hcont hf x⟩
  · rintro ⟨c, rfl⟩
    refine ⟨continuous_const.mul (continuous_eulerProd hq), fun x => ?_⟩
    show c * eulerProd q x = (1 - q * x) * (c * eulerProd q (q * x))
    rw [eulerProd_funeq hq x]
    ring

/-- The prescribed zeros: any solution vanishes at `q⁻ᵐ` for `m ≥ 1` (no continuity needed). -/
theorem zero_at_inv_pow {q : ℝ} (hq : q ≠ 0) {f : ℝ → ℝ}
    (hf : ∀ x, f x = (1 - q * x) * f (q * x)) (m : ℕ) (hm : 1 ≤ m) :
    f (q ^ m)⁻¹ = 0 := by
  rw [funeq_iterate hf m]
  have hz : (1 - q ^ (m - 1 + 1) * (q ^ m)⁻¹) = 0 := by
    have hm' : m - 1 + 1 = m := by omega
    rw [hm', mul_inv_cancel₀ (pow_ne_zero m hq), sub_self]
  rw [Finset.prod_eq_zero (i := m - 1) (by simp; omega) hz, zero_mul]

/-- Every solution has arbitrarily large positive zeros: the points `q^{-2m} = |q|^{-2m}`
tend to `+∞`.  (For `0 < q < 1` all the points `q^{-m}` are already positive zeros.) -/
theorem exists_zero_gt {q : ℝ} (hq : |q| < 1) (hq0 : q ≠ 0) {f : ℝ → ℝ}
    (hf : ∀ x, f x = (1 - q * x) * f (q * x)) (M : ℝ) :
    ∃ x > M, f x = 0 := by
  have hs0 : 0 < q ^ 2 := by positivity
  have hs1 : q ^ 2 < 1 := by
    have : |q| ^ 2 < 1 := by nlinarith [abs_nonneg q]
    rwa [sq_abs] at this
  have htend : Tendsto (fun m : ℕ => ((q ^ 2) ^ m)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_pow_atTop_nhdsWithin_zero_of_lt_one hs0 hs1)
  obtain ⟨m, hm⟩ := (htend.eventually_gt_atTop (max M 1)).and (eventually_ge_atTop 1) |>.exists
  refine ⟨((q ^ 2) ^ m)⁻¹, lt_of_le_of_lt (le_max_left _ _) hm.1, ?_⟩
  rw [← pow_mul]
  exact zero_at_inv_pow hq0 hf (2 * m) (by omega)

/-- The Euler product does not vanish at points that are not of the form `q^{-j}`. -/
theorem eulerProd_ne_zero {q : ℝ} (hq : |q| < 1) {x : ℝ} (hx : ∀ j : ℕ, q ^ (j + 1) * x ≠ 1) :
    eulerProd q x ≠ 0 := by
  have hs : Summable fun j : ℕ => |q| ^ j * (|q| * |x|) :=
    (summable_geometric_of_lt_one (abs_nonneg q) hq).mul_right _
  have h : Summable fun j : ℕ => ‖-(q ^ (j + 1) * x)‖ := by
    refine hs.congr fun n => ?_
    simp [pow_succ]
    ring
  have hne : ∀ j : ℕ, (1 : ℝ) + -(q ^ (j + 1) * x) ≠ 0 := fun j hj => hx j (by linarith [hj])
  simpa [eulerProd, sub_eq_add_neg] using tprod_one_add_ne_zero_of_summable hne h

private theorem lt_of_pow_lt_pow_of_lt_one {q : ℝ} (h0 : 0 < q) (h1 : q < 1) {m k : ℕ}
    (h : q ^ k < q ^ m) : m < k := by
  by_contra hc
  push_neg at hc
  exact absurd h (not_lt.2 (pow_le_pow_of_le_one h0.le h1.le hc))

/-- For `0 < q < 1` there is a point `y ≥ 3` which is not one of the zeros `q^{-j}`. -/
theorem exists_large_non_zero_point {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ y : ℝ, 3 ≤ y ∧ ∀ j : ℕ, q ^ (j + 1) * y ≠ 1 := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, q ^ m ≤ 1 / 3 := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
    exact (h.eventually (eventually_le_nhds (by norm_num))).exists
  have hpm : (0 : ℝ) < q ^ m := pow_pos hq0 m
  have hpm1 : (0 : ℝ) < q ^ (m + 1) := pow_pos hq0 (m + 1)
  have hlt : q ^ (m + 1) < q ^ m := by rw [pow_succ]; nlinarith
  have hinv : (q ^ m)⁻¹ < (q ^ (m + 1))⁻¹ := (inv_lt_inv₀ hpm hpm1).2 hlt
  refine ⟨((q ^ m)⁻¹ + (q ^ (m + 1))⁻¹) / 2, ?_, ?_⟩
  · have h3 : (3 : ℝ) ≤ (q ^ m)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hpm]; linarith
    linarith
  · intro j hj
    set k := j + 1 with hk
    have hpk : (0 : ℝ) < q ^ k := pow_pos hq0 k
    have hy : ((q ^ m)⁻¹ + (q ^ (m + 1))⁻¹) / 2 = (q ^ k)⁻¹ := by
      field_simp at hj ⊢
      linarith [hj]
    have h1 : (q ^ m)⁻¹ < (q ^ k)⁻¹ := by rw [← hy]; linarith
    have h2 : (q ^ k)⁻¹ < (q ^ (m + 1))⁻¹ := by rw [← hy]; linarith
    have e1 : m < k := lt_of_pow_lt_pow_of_lt_one hq0 hq1 ((inv_lt_inv₀ hpm hpk).1 h1)
    have e2 : k < m + 1 := lt_of_pow_lt_pow_of_lt_one hq0 hq1 ((inv_lt_inv₀ hpk hpm1).1 h2)
    omega

/-- Rescaling by `q^{-N}` multiplies the size of a solution by at least `2^N`, once the base
point is at least `3`.  (The true growth is much faster, but this suffices to see that the
solutions are unbounded at `+∞`.) -/
theorem abs_le_abs_scaled {q : ℝ} (hq : |q| < 1) (hq0 : q ≠ 0) {f : ℝ → ℝ}
    (hf : ∀ x, f x = (1 - q * x) * f (q * x)) {y : ℝ} (hy : 3 ≤ y) (N : ℕ) :
    |f y| * 2 ^ N ≤ |f ((q ^ N)⁻¹ * y)| := by
  have hqa : 0 < |q| := abs_pos.2 hq0
  have hpn : (0 : ℝ) < |q| ^ N := pow_pos hqa N
  have hkey := funeq_iterate hf N ((q ^ N)⁻¹ * y)
  have hsimp : q ^ N * ((q ^ N)⁻¹ * y) = y := by
    field_simp
  rw [hsimp] at hkey
  rw [hkey, abs_mul]
  have hbound : (2 : ℝ) ^ N ≤ |∏ j ∈ Finset.range N, (1 - q ^ (j + 1) * ((q ^ N)⁻¹ * y))| := by
    rw [Finset.abs_prod]
    calc (2 : ℝ) ^ N = ∏ _j ∈ Finset.range N, (2 : ℝ) := by simp
      _ ≤ _ := by
          refine Finset.prod_le_prod (fun i _ => by norm_num) ?_
          intro j hj
          simp only [Finset.mem_range] at hj
          have hle : |q| ^ N ≤ |q| ^ (j + 1) :=
            pow_le_pow_of_le_one hqa.le (le_of_lt hq) (by omega)
          have ht : (1 : ℝ) ≤ |q ^ (j + 1) * (q ^ N)⁻¹| := by
            rw [abs_mul, abs_inv, abs_pow, abs_pow, le_mul_inv_iff₀ hpn]
            simpa using hle
          have hy0 : (0 : ℝ) ≤ y := by linarith
          have habs : |q ^ (j + 1) * ((q ^ N)⁻¹ * y)| = |q ^ (j + 1) * (q ^ N)⁻¹| * y := by
            rw [← mul_assoc, abs_mul, abs_of_nonneg hy0]
          have h3 : (3 : ℝ) ≤ |q ^ (j + 1) * ((q ^ N)⁻¹ * y)| := by
            rw [habs]; nlinarith
          have := abs_sub_abs_le_abs_sub (q ^ (j + 1) * ((q ^ N)⁻¹ * y)) 1
          rw [abs_sub_comm] at this
          simp only [abs_one] at this
          linarith
  calc |f y| * 2 ^ N
      ≤ |f y| * |∏ j ∈ Finset.range N, (1 - q ^ (j + 1) * ((q ^ N)⁻¹ * y))| :=
        mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
    _ = |∏ j ∈ Finset.range N, (1 - q ^ (j + 1) * ((q ^ N)⁻¹ * y))| * |f y| := mul_comm _ _

/-- A nonzero continuous solution is unbounded at `+∞`. -/
theorem unbounded_atTop {q : ℝ} (hq : |q| < 1) (hq0 : q ≠ 0) {f : ℝ → ℝ} (hcont : Continuous f)
    (hf : ∀ x, f x = (1 - q * x) * f (q * x)) (hc : f 0 ≠ 0) (M : ℝ) :
    ∃ x > M, M < |f x| := by
  have hqa : 0 < |q| := abs_pos.2 hq0
  obtain ⟨y, hy3, hy⟩ := exists_large_non_zero_point hqa hq
  have hy0 : (0 : ℝ) < y := by linarith
  have hfy : f y ≠ 0 := by
    rw [eq_eulerProd hq hcont hf y]
    refine mul_ne_zero hc (eulerProd_ne_zero hq fun j hj => ?_)
    have : |q ^ (j + 1) * y| = |q| ^ (j + 1) * y := by
      rw [abs_mul, abs_pow, abs_of_nonneg hy0.le]
    rw [hj] at this
    simp only [abs_one] at this
    exact hy j this.symm
  have hay : 0 < |f y| := abs_pos.2 hfy
  have hs0 : 0 < q ^ 2 := by positivity
  have hs1 : q ^ 2 < 1 := by
    have : |q| ^ 2 < 1 := by nlinarith
    rwa [sq_abs] at this
  have h1 : Tendsto (fun n : ℕ => |f y| * 2 ^ (2 * n)) atTop atTop := by
    refine Filter.Tendsto.const_mul_atTop hay ?_
    have : Tendsto (fun n : ℕ => ((2 : ℝ) ^ 2) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    simpa [pow_mul] using this
  have hinv : Tendsto (fun n : ℕ => ((q ^ 2) ^ n)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_pow_atTop_nhdsWithin_zero_of_lt_one hs0 hs1)
  have h2 : Tendsto (fun n : ℕ => ((q ^ 2) ^ n)⁻¹ * y) atTop atTop :=
    hinv.atTop_mul_const hy0
  obtain ⟨n, hn1, hn2⟩ := ((h1.eventually_gt_atTop M).and (h2.eventually_gt_atTop M)).exists
  refine ⟨((q ^ 2) ^ n)⁻¹ * y, hn2, lt_of_lt_of_le hn1 ?_⟩
  rw [← pow_mul]
  exact abs_le_abs_scaled hq hq0 hf hy3 (2 * n)

/-- Because a nonzero solution keeps vanishing at the points `q^{-m}`, it admits no asymptotic
equivalent at `+∞` by a function that is eventually nonzero.  (This is why the answer to Q839
has to be given by an exact log-periodic formula rather than by an equivalent.) -/
theorem no_asymptotic_equivalent {q : ℝ} (hq : |q| < 1) (hq0 : q ≠ 0) {f : ℝ → ℝ}
    (hf : ∀ x, f x = (1 - q * x) * f (q * x)) :
    ¬ ∃ g : ℝ → ℝ, Tendsto (fun x => f x / g x) atTop (𝓝 1) := by
  rintro ⟨g, htend⟩
  have hne : ∀ᶠ x : ℝ in atTop, f x / g x ≠ 0 :=
    htend.eventually (eventually_ne_nhds (by norm_num))
  obtain ⟨X, hX⟩ := eventually_atTop.1 hne
  obtain ⟨x, hx, hfx⟩ := exists_zero_gt hq hq0 hf X
  exact hX x hx.le (by simp [hfx])

/-- Degenerate case `q = 0`: every solution is constant. -/
theorem const_of_q_eq_zero {f : ℝ → ℝ} (hf : ∀ x, f x = (1 - (0 : ℝ) * x) * f (0 * x)) (x : ℝ) :
    f x = f 0 := by
  simpa using hf x

/-- At `q = 1` the only continuous solution is `0`. -/
theorem eq_zero_of_q_eq_one {f : ℝ → ℝ} (hcont : Continuous f)
    (hf : ∀ x, f x = (1 - (1 : ℝ) * x) * f (1 * x)) (x : ℝ) : f x = 0 := by
  have key : ∀ y : ℝ, y ≠ 0 → f y = 0 := by
    intro y hy
    have h := hf y
    simp only [one_mul] at h
    have h' : y * f y = 0 := by nlinarith [h]
    rcases mul_eq_zero.1 h' with h1 | h1
    · exact absurd h1 hy
    · exact h1
  rcases eq_or_ne x 0 with rfl | hx
  · have hl : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 (f 0)) := hcont.continuousAt.continuousWithinAt.tendsto
    have hr : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (key y hy).symm
    exact tendsto_nhds_unique hl hr
  · exact key x hx

/-- At `q = -1` the only continuous solution is `0`. -/
theorem eq_zero_of_q_eq_neg_one {f : ℝ → ℝ} (hcont : Continuous f)
    (hf : ∀ x, f x = (1 - (-1 : ℝ) * x) * f (-1 * x)) (x : ℝ) : f x = 0 := by
  have key : ∀ y : ℝ, y ≠ 0 → f y = 0 := by
    intro y hy
    have h1 := hf y
    have h2 := hf (-y)
    simp only [neg_one_mul, neg_neg, sub_neg_eq_add] at h1 h2
    rw [h2] at h1
    have h' : y ^ 2 * f y = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h' with h3 | h3
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h3) hy
    · exact h3
  rcases eq_or_ne x 0 with rfl | hx
  · have hl : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 (f 0)) := hcont.continuousAt.continuousWithinAt.tendsto
    have hr : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (key y hy).symm
    exact tendsto_nhds_unique hl hr
  · exact key x hx

/-!
## Part II: the exact logarithmically periodic formula at `+∞` (case `0 < q < 1`)

With `a = log (1/q)`, `n = ⌊log x / a⌋`, `u = log x / a - n`,
`E_q x = x^(-1/2) exp((log x)^2 / (2a))` and
`Φ_q u = q^((u²-u)/2) (q^u;q)_∞ (q^(1-u);q)_∞`, one has for `x > 1`
`f x = f 0 (-1)^n E_q(x) Φ_q(u) / (x⁻¹;q)_∞`.
-/


/-- The infinite `q`-Pochhammer symbol `(a;q)_∞ = ∏_{k ≥ 0} (1 - a q^k)`. -/
noncomputable def qPoch (a q : ℝ) : ℝ := ∏' k : ℕ, (1 - a * q ^ k)

theorem multipliable_qPoch {q : ℝ} (hq : |q| < 1) (a : ℝ) :
    Multipliable fun k : ℕ => (1 - a * q ^ k) := by
  have hs : Summable fun k : ℕ => |q| ^ k * |a| :=
    (summable_geometric_of_lt_one (abs_nonneg q) hq).mul_right _
  have h : Summable fun k : ℕ => ‖-(a * q ^ k)‖ := by
    refine hs.congr fun n => ?_
    simp [mul_comm]
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable h

theorem tendsto_qPoch {q : ℝ} (hq : |q| < 1) (a : ℝ) :
    Tendsto (fun n : ℕ => ∏ k ∈ Finset.range n, (1 - a * q ^ k)) atTop (𝓝 (qPoch a q)) :=
  (multipliable_qPoch hq a).tendsto_prod_tprod_nat

/-- Splitting off the first `n` factors of an infinite `q`-Pochhammer symbol. -/
theorem qPoch_split {q : ℝ} (hq : |q| < 1) (a : ℝ) (n : ℕ) :
    qPoch a q = (∏ k ∈ Finset.range n, (1 - a * q ^ k)) * qPoch (a * q ^ n) q := by
  have hn : Tendsto (fun m : ℕ => n + m) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat n
  have h1 : Tendsto (fun m : ℕ => ∏ k ∈ Finset.range (n + m), (1 - a * q ^ k)) atTop
      (𝓝 (qPoch a q)) := (tendsto_qPoch hq a).comp hn
  have h2 : Tendsto (fun m : ℕ =>
      (∏ k ∈ Finset.range n, (1 - a * q ^ k)) * ∏ k ∈ Finset.range m, (1 - a * q ^ n * q ^ k))
      atTop (𝓝 ((∏ k ∈ Finset.range n, (1 - a * q ^ k)) * qPoch (a * q ^ n) q)) :=
    (tendsto_qPoch hq (a * q ^ n)).const_mul _
  refine tendsto_nhds_unique h1 (h2.congr fun m => ?_)
  rw [Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [pow_add]
  ring

theorem qPoch_ne_zero {q a : ℝ} (hq : |q| < 1) (h : ∀ k : ℕ, a * q ^ k ≠ 1) :
    qPoch a q ≠ 0 := by
  have hs : Summable fun k : ℕ => |q| ^ k * |a| :=
    (summable_geometric_of_lt_one (abs_nonneg q) hq).mul_right _
  have hsum : Summable fun k : ℕ => ‖-(a * q ^ k)‖ := by
    refine hs.congr fun n => ?_
    simp [mul_comm]
  have hne : ∀ k : ℕ, (1 : ℝ) + -(a * q ^ k) ≠ 0 := fun k hk => h k (by linarith [hk])
  simpa [qPoch, sub_eq_add_neg] using tprod_one_add_ne_zero_of_summable hne hsum

theorem eulerProd_eq_qPoch {q : ℝ} (x : ℝ) : eulerProd q x = qPoch (q * x) q := by
  refine tprod_congr fun j => ?_
  rw [pow_succ]
  ring

/-- The universal growth envelope `E_q x = x^{-1/2} exp((log x)²/(2 log(1/q)))`. -/
noncomputable def envelope (q x : ℝ) : ℝ :=
  x ^ (-(1 : ℝ) / 2) * Real.exp ((Real.log x) ^ 2 / (2 * Real.log (1 / q)))

/-- The logarithmic phase profile `Φ_q u = q^((u²-u)/2) (q^u;q)_∞ (q^{1-u};q)_∞`. -/
noncomputable def phase (q u : ℝ) : ℝ :=
  q ^ ((u ^ 2 - u) / 2) * qPoch (q ^ u) q * qPoch (q ^ (1 - u)) q

private theorem prod_rpow_eq {q : ℝ} (hq0 : 0 < q) (s : Finset ℕ) (g : ℕ → ℝ) :
    ∏ k ∈ s, q ^ (g k) = q ^ (∑ k ∈ s, g k) := by
  simp [Real.rpow_def_of_pos hq0, ← Real.exp_sum, Finset.mul_sum]

private theorem sum_range_cast (n : ℕ) : ∑ k ∈ Finset.range n, (k : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The elementary prefactor, rewritten through the envelope. -/
theorem prefactor_eq_envelope {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) (u x : ℝ)
    (hx : x = q ^ (-((n : ℝ) + u))) :
    q ^ (-(((n : ℝ) * (n - 1) / 2) + n * u)) = envelope q x * q ^ ((u ^ 2 - u) / 2) := by
  have hlogq : Real.log q < 0 := Real.log_neg hq0 hq1
  set A := Real.log (1 / q) with hA
  have hA' : A = -Real.log q := by rw [hA, one_div, Real.log_inv]
  have hApos : 0 < A := by rw [hA']; linarith
  have hxpos : 0 < x := by rw [hx]; positivity
  have hlogx : Real.log x = ((n : ℝ) + u) * A := by
    rw [hx, Real.log_rpow hq0, hA']
    ring
  rw [envelope, ← hA, Real.rpow_def_of_pos hq0, Real.rpow_def_of_pos hq0,
    Real.rpow_def_of_pos hxpos, hlogx, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [hA']
  field_simp
  ring

/-- Reversal of the finite product `∏_{j=1}^{n} (1 - q^j x)`. -/
theorem finite_prod_reflect {q : ℝ} (hq0 : 0 < q) (n : ℕ) (u x : ℝ)
    (hx : x = q ^ (-((n : ℝ) + u))) :
    ∏ k ∈ Finset.range n, (1 - q * x * q ^ k)
      = (-1) ^ n * q ^ (-(((n : ℝ) * (n - 1) / 2) + n * u)) *
        ∏ k ∈ Finset.range n, (1 - q ^ u * q ^ k) := by
  rw [← Finset.prod_range_reflect]
  have h1 : ∀ k ∈ Finset.range n, (1 - q * x * q ^ (n - 1 - k))
      = (-(q ^ (-((k : ℝ) + u)))) * (1 - q ^ u * q ^ k) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    obtain ⟨m, hm⟩ : ∃ m, n = k + 1 + m := ⟨n - k - 1, by omega⟩
    have hnk : n - 1 - k = m := by omega
    have hstep : q * x * q ^ (n - 1 - k) = q ^ (-((k : ℝ) + u)) := by
      rw [hnk, hx, ← Real.rpow_natCast q m, mul_assoc, ← Real.rpow_add hq0]
      nth_rewrite 1 [← Real.rpow_one q]
      rw [← Real.rpow_add hq0]
      congr 1
      rw [hm]
      push_cast
      ring
    have ht : q ^ u * q ^ (k : ℕ) = q ^ ((k : ℝ) + u) := by
      rw [← Real.rpow_natCast q k, ← Real.rpow_add hq0]
      ring_nf
    have htpos : (0 : ℝ) < q ^ ((k : ℝ) + u) := Real.rpow_pos_of_pos hq0 _
    rw [hstep, ht, Real.rpow_neg hq0.le]
    field_simp
    ring
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib]
  congr 1
  have h2 : ∀ k ∈ Finset.range n, (-(q ^ (-((k : ℝ) + u)))) = (-1) * q ^ (-((k : ℝ) + u)) :=
    fun k _ => by ring
  rw [Finset.prod_congr rfl h2, Finset.prod_mul_distrib, Finset.prod_const,
    prod_rpow_eq hq0, Finset.card_range]
  congr 1
  have h3 : ∑ k ∈ Finset.range n, (-((k : ℝ) + u)) = -(((n : ℝ) * (n - 1) / 2) + n * u) := by
    rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, sum_range_cast, Finset.sum_const,
      Finset.card_range]
    simp
  rw [h3]

/-- The exact logarithmically periodic formula, in the form valid for any splitting
`x = q^{-(n+u)}` with `n` a natural number. -/
theorem exact_log_periodic_of_eq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {f : ℝ → ℝ}
    (hcont : Continuous f) (hf : ∀ x, f x = (1 - q * x) * f (q * x))
    {x : ℝ} (hx : 1 < x) {n : ℕ} {u : ℝ} (hxeq : x = q ^ (-((n : ℝ) + u))) :
    f x = f 0 * (-1) ^ n * envelope q x * phase q u / qPoch x⁻¹ q := by
  have hq : |q| < 1 := by rwa [abs_of_pos hq0]
  have hxpos : (0 : ℝ) < x := by linarith
  have htail : q * x * q ^ n = q ^ (1 - u) := by
    rw [hxeq, ← Real.rpow_natCast q n, mul_assoc, ← Real.rpow_add hq0]
    nth_rewrite 1 [← Real.rpow_one q]
    rw [← Real.rpow_add hq0]
    congr 1
    ring
  have hhead : q ^ u * q ^ n = x⁻¹ := by
    rw [← Real.rpow_natCast q n, ← Real.rpow_add hq0, hxeq, Real.rpow_neg hq0.le, inv_inv]
    congr 1
    ring
  have hden : qPoch x⁻¹ q ≠ 0 := by
    refine qPoch_ne_zero hq fun k hk => ?_
    have h2 : q ^ k ≤ 1 := pow_le_one₀ hq0.le hq1.le
    have h3 : x⁻¹ < 1 := by rw [inv_lt_one₀ hxpos]; exact hx
    have h4 : (0 : ℝ) < x⁻¹ := by positivity
    have h1 : x⁻¹ * q ^ k < 1 := by nlinarith [pow_pos hq0 k]
    linarith [hk ▸ h1]
  have hsplit1 : qPoch (q * x) q
      = (∏ k ∈ Finset.range n, (1 - q * x * q ^ k)) * qPoch (q ^ (1 - u)) q := by
    rw [qPoch_split hq (q * x) n, htail]
  have hsplit2 : qPoch (q ^ u) q
      = (∏ k ∈ Finset.range n, (1 - q ^ u * q ^ k)) * qPoch x⁻¹ q := by
    rw [qPoch_split hq (q ^ u) n, hhead]
  have hmid : ∏ k ∈ Finset.range n, (1 - q ^ u * q ^ k) = qPoch (q ^ u) q / qPoch x⁻¹ q := by
    rw [hsplit2, mul_div_assoc, div_self hden, mul_one]
  have hfx : f x = f 0 * qPoch (q * x) q := by
    rw [eq_eulerProd hq hcont hf x, eulerProd_eq_qPoch]
  rw [hfx, hsplit1, finite_prod_reflect hq0 n u x hxeq, hmid,
    prefactor_eq_envelope hq0 hq1 n u x hxeq, phase]
  field_simp

/-- The exact logarithmically periodic formula for the behaviour of a continuous solution
at `+∞`, in the case `0 < q < 1`: writing `log x / log(1/q) = n + u` with `n` a natural
number and `u ∈ [0,1)` (see `frac_mem_Ico` below), one has
`f x = f 0 (-1)^n E_q(x) Φ_q(u) / (x⁻¹;q)_∞`. -/
theorem exact_log_periodic {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {f : ℝ → ℝ}
    (hcont : Continuous f) (hf : ∀ x, f x = (1 - q * x) * f (q * x))
    {x : ℝ} (hx : 1 < x) :
    f x = f 0 * (-1) ^ (⌊Real.log x / Real.log (1 / q)⌋₊) * envelope q x *
      phase q (Real.log x / Real.log (1 / q) - ⌊Real.log x / Real.log (1 / q)⌋₊) /
      qPoch x⁻¹ q := by
  have hlogq : Real.log q < 0 := Real.log_neg hq0 hq1
  have hA' : Real.log (1 / q) = -Real.log q := by rw [one_div, Real.log_inv]
  have hApos : 0 < Real.log (1 / q) := by rw [hA']; linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hxpos : (0 : ℝ) < x := by linarith
  set L := Real.log x / Real.log (1 / q) with hLdef
  set n := ⌊L⌋₊ with hn
  refine exact_log_periodic_of_eq hq0 hq1 hcont hf hx (n := n) (u := L - n) ?_
  have hsum : (n : ℝ) + (L - n) = L := by ring
  rw [hsum, Real.rpow_def_of_pos hq0, hLdef, hA']
  have h : Real.log q * -(Real.log x / -Real.log q) = Real.log x := by
    field_simp
    exact div_self hlogq.ne
  rw [h, Real.exp_log hxpos]

/-- The logarithmic phase `u` really lies in `[0,1)`. -/
theorem frac_mem_Ico {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hx : 1 < x) :
    0 ≤ Real.log x / Real.log (1 / q) - ⌊Real.log x / Real.log (1 / q)⌋₊ ∧
      Real.log x / Real.log (1 / q) - ⌊Real.log x / Real.log (1 / q)⌋₊ < 1 := by
  have hlogq : Real.log q < 0 := Real.log_neg hq0 hq1
  have hA' : Real.log (1 / q) = -Real.log q := by rw [one_div, Real.log_inv]
  have hApos : 0 < Real.log (1 / q) := by rw [hA']; linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx
  set L := Real.log x / Real.log (1 / q) with hLdef
  have hL0 : 0 ≤ L := by positivity
  exact ⟨by linarith [Nat.floor_le hL0], by linarith [Nat.lt_floor_add_one L]⟩

/-! ### Properties of the phase profile `Φ_q` -/

theorem qPoch_nonneg {q a : ℝ} (hq : |q| < 1) (h : ∀ k : ℕ, 0 ≤ 1 - a * q ^ k) :
    0 ≤ qPoch a q :=
  ge_of_tendsto (tendsto_qPoch hq a) (Eventually.of_forall fun _ =>
    Finset.prod_nonneg fun k _ => h k)

theorem qPoch_one {q : ℝ} (hq : |q| < 1) : qPoch 1 q = 0 := by
  refine tendsto_nhds_unique (tendsto_qPoch hq 1) ?_
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (Finset.prod_eq_zero (i := 0) (by simpa using hn) (by simp)).symm

/-- `Φ_q` is symmetric about `u = 1/2`. -/
theorem phase_symm (q u : ℝ) : phase q (1 - u) = phase q u := by
  have h1 : ((1 - u) ^ 2 - (1 - u)) / 2 = (u ^ 2 - u) / 2 := by ring
  have h2 : (1 : ℝ) - (1 - u) = u := by ring
  rw [phase, phase, h1, h2]
  ring

/-- An infinite `q`-Pochhammer symbol `(a;q)_∞` with `a < 1` and `0 < q < 1` is positive. -/
theorem qPoch_pos {q a : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (ha1 : a < 1) :
    0 < qPoch a q := by
  have hq : |q| < 1 := by rwa [abs_of_pos hq0]
  have hlt : ∀ k : ℕ, a * q ^ k < 1 := by
    intro k
    have h1 : q ^ k ≤ 1 := pow_le_one₀ hq0.le hq1.le
    have h2 : (0 : ℝ) < q ^ k := pow_pos hq0 k
    rcases le_or_gt a 0 with ha | ha
    · have : a * q ^ k ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha h2.le
      linarith
    nlinarith
  have hne : qPoch a q ≠ 0 := qPoch_ne_zero hq fun k hk => by linarith [hk ▸ hlt k]
  exact lt_of_le_of_ne (qPoch_nonneg hq fun k => by linarith [hlt k]) (Ne.symm hne)

/-- `Φ_q` is strictly positive on the open interval `(0,1)`. -/
theorem phase_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    0 < phase q u := by
  have key : ∀ v : ℝ, 0 < v → 0 < qPoch (q ^ v) q := fun v hv =>
    qPoch_pos hq0 hq1 (Real.rpow_lt_one hq0.le hq1 hv)
  have h1 := key u hu0
  have h2 := key (1 - u) (by linarith)
  have h3 : (0 : ℝ) < q ^ ((u ^ 2 - u) / 2) := Real.rpow_pos_of_pos hq0 _
  rw [phase]
  positivity

/-- `Φ_q` vanishes at the endpoints. -/
theorem phase_zero {q : ℝ} (hq : |q| < 1) : phase q 0 = 0 := by
  simp [phase, Real.rpow_zero, qPoch_one hq]

theorem phase_one {q : ℝ} (hq : |q| < 1) : phase q 1 = 0 := by
  simp [phase, Real.rpow_zero, qPoch_one hq]

/-- Sign alternation: for `0 < q < 1` a nonzero continuous solution has the sign of
`f 0 * (-1)^n` on the interval `(q^{-n}, q^{-(n+1)})` between two consecutive zeros. -/
theorem sign_alternating {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {f : ℝ → ℝ} (hcont : Continuous f)
    (hf : ∀ x, f x = (1 - q * x) * f (q * x)) (hc : f 0 ≠ 0) {n : ℕ} {x : ℝ}
    (h1 : (q ^ n)⁻¹ < x) (h2 : x < (q ^ (n + 1))⁻¹) :
    0 < (-1) ^ n * f 0 * f x := by
  have hlogq : Real.log q < 0 := Real.log_neg hq0 hq1
  have hA' : Real.log (1 / q) = -Real.log q := by rw [one_div, Real.log_inv]
  have hApos : 0 < Real.log (1 / q) := by rw [hA']; linarith
  have hpn : (0 : ℝ) < q ^ n := pow_pos hq0 n
  have hge1 : (1 : ℝ) ≤ (q ^ n)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hpn]
    simpa using pow_le_one₀ hq0.le hq1.le
  have hx1 : 1 < x := lt_of_le_of_lt hge1 h1
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogxlb : (n : ℝ) * Real.log (1 / q) < Real.log x := by
    have h := Real.log_lt_log (by positivity) h1
    rw [Real.log_inv, Real.log_pow] at h
    rw [hA']
    linarith
  have hlogxub : Real.log x < ((n : ℝ) + 1) * Real.log (1 / q) := by
    have h := Real.log_lt_log hxpos h2
    rw [Real.log_inv, Real.log_pow] at h
    rw [hA']
    push_cast at h
    linarith
  set L := Real.log x / Real.log (1 / q) with hL
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hLlb : (n : ℝ) < L := by rw [hL, lt_div_iff₀ hApos]; linarith
  have hLub : L < (n : ℝ) + 1 := by rw [hL, div_lt_iff₀ hApos]; linarith
  have hfloor : ⌊L⌋₊ = n := by
    rw [Nat.floor_eq_iff hL0]
    exact ⟨hLlb.le, by linarith⟩
  have hden : 0 < qPoch x⁻¹ q := by
    refine qPoch_pos hq0 hq1 ?_
    rw [inv_lt_one₀ hxpos]; exact hx1
  have hphase : 0 < phase q (L - (n : ℝ)) := phase_pos hq0 hq1 (by linarith) (by linarith)
  have henv : 0 < envelope q x := by
    rw [envelope]
    have hp : (0 : ℝ) < x ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hxpos _
    positivity
  have hfx := exact_log_periodic hq0 hq1 hcont hf hx1
  rw [← hL, hfloor] at hfx
  rw [hfx]
  have h4 : ((-1 : ℝ) ^ n) * ((-1) ^ n) = 1 := by rw [← mul_pow]; norm_num
  have hcsq : 0 < f 0 * f 0 := mul_self_pos.2 hc
  calc (-1 : ℝ) ^ n * f 0 * (f 0 * (-1) ^ n * envelope q x * phase q (L - n) / qPoch x⁻¹ q)
      = ((-1 : ℝ) ^ n * (-1) ^ n) * ((f 0 * f 0) * envelope q x * phase q (L - n)) /
          qPoch x⁻¹ q := by ring
    _ = (f 0 * f 0) * envelope q x * phase q (L - n) / qPoch x⁻¹ q := by rw [h4]; ring
    _ > 0 := div_pos (mul_pos (mul_pos hcsq henv) hphase) hden

/-!
## Part III: the case `-1 < q < 0`

With `s = q²`, `n = ⌊log x / log(1/s)⌋`, `u = log x / log(1/s) - n` and
`Ψ_q u = s^(u² - u/2) (s^u;s)_∞ (s^{1-u};s)_∞ (-s^{u+1/2};s)_∞ (-s^{1/2-u};s)_∞`,
one has for `x > 1`  `f x = f 0 (-1)^n E_q(x) Ψ_q(u) / (x⁻¹;q)_∞`.
-/

/-- Splitting an infinite `q`-Pochhammer symbol into its even and odd parts. -/
theorem qPoch_parity_split {q : ℝ} (hq : |q| < 1) (a : ℝ) :
    qPoch a q = qPoch a (q ^ 2) * qPoch (a * q) (q ^ 2) := by
  have hq2 : |q ^ 2| < 1 := by
    rw [abs_pow]
    calc |q| ^ 2 < 1 ^ 2 := by nlinarith [abs_nonneg q]
      _ = 1 := one_pow 2
  have hfin : ∀ N : ℕ, ∏ k ∈ Finset.range (2 * N), (1 - a * q ^ k)
      = (∏ m ∈ Finset.range N, (1 - a * (q ^ 2) ^ m)) *
        (∏ m ∈ Finset.range N, (1 - a * q * (q ^ 2) ^ m)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        have h2 : 2 * (N + 1) = (2 * N) + 1 + 1 := by ring
        rw [h2, Finset.prod_range_succ, Finset.prod_range_succ, ih, Finset.prod_range_succ,
          Finset.prod_range_succ]
        have e1 : a * q ^ (2 * N) = a * (q ^ 2) ^ N := by rw [← pow_mul, mul_comm 2 N]
        have e2 : a * q ^ (2 * N + 1) = a * q * (q ^ 2) ^ N := by
          rw [← pow_mul, mul_comm 2 N, pow_succ]
          ring
        rw [e1, e2]
        ring
  have h1 : Tendsto (fun N : ℕ => ∏ k ∈ Finset.range (2 * N), (1 - a * q ^ k)) atTop
      (𝓝 (qPoch a q)) := (tendsto_qPoch hq a).comp (by
        apply Filter.tendsto_atTop_atTop_of_monotone (fun m n h => by omega)
        intro b; exact ⟨b, by omega⟩)
  have h2 : Tendsto (fun N : ℕ => (∏ m ∈ Finset.range N, (1 - a * (q ^ 2) ^ m)) *
      (∏ m ∈ Finset.range N, (1 - a * q * (q ^ 2) ^ m))) atTop
      (𝓝 (qPoch a (q ^ 2) * qPoch (a * q) (q ^ 2))) :=
    (tendsto_qPoch hq2 a).mul (tendsto_qPoch hq2 (a * q))
  exact tendsto_nhds_unique h1 (h2.congr fun N => (hfin N).symm)

/-- The phase profile `Ψ_q` for negative `q`, written with `s = q²`. -/
noncomputable def phaseNeg (q u : ℝ) : ℝ :=
  (q ^ 2) ^ (u ^ 2 - u / 2) * qPoch ((q ^ 2) ^ u) (q ^ 2) * qPoch ((q ^ 2) ^ (1 - u)) (q ^ 2) *
    qPoch (-((q ^ 2) ^ (u + (1 : ℝ) / 2))) (q ^ 2) *
    qPoch (-((q ^ 2) ^ ((1 : ℝ) / 2 - u))) (q ^ 2)

/-- Reversal of the finite product `∏_{k<n} (1 + r x s^k)` occurring in the odd part. -/
theorem finite_prod_reflect_neg {s : ℝ} (hs0 : 0 < s) (n : ℕ) (u x : ℝ)
    (hx : x = s ^ (-((n : ℝ) + u))) :
    ∏ k ∈ Finset.range n, (1 - (-(s ^ ((1 : ℝ) / 2) * x)) * s ^ k)
      = s ^ (-(((n : ℝ) * (n - 1) / 2) + n * u + n / 2)) *
        ∏ k ∈ Finset.range n, (1 - (-(s ^ (u + (1 : ℝ) / 2))) * s ^ k) := by
  rw [← Finset.prod_range_reflect]
  have h1 : ∀ k ∈ Finset.range n, (1 - (-(s ^ ((1 : ℝ) / 2) * x)) * s ^ (n - 1 - k))
      = (s ^ (-((k : ℝ) + u + 1 / 2))) * (1 - (-(s ^ (u + (1 : ℝ) / 2))) * s ^ k) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    obtain ⟨m, hm⟩ : ∃ m, n = k + 1 + m := ⟨n - k - 1, by omega⟩
    have hnk : n - 1 - k = m := by omega
    have hstep : s ^ ((1 : ℝ) / 2) * x * s ^ (n - 1 - k) = s ^ (-((k : ℝ) + u + 1 / 2)) := by
      rw [hnk, hx, ← Real.rpow_natCast s m, ← Real.rpow_add hs0, ← Real.rpow_add hs0]
      congr 1
      rw [hm]
      push_cast
      ring
    have ht : (-(s ^ ((1 : ℝ) / 2) * x)) * s ^ (n - 1 - k) = -(s ^ (-((k : ℝ) + u + 1 / 2))) := by
      rw [← hstep]; ring
    have ht2 : s ^ (u + (1 : ℝ) / 2) * s ^ (k : ℕ) = s ^ ((k : ℝ) + u + 1 / 2) := by
      rw [← Real.rpow_natCast s k, ← Real.rpow_add hs0]
      ring_nf
    have ht3 : (-(s ^ (u + (1 : ℝ) / 2))) * s ^ (k : ℕ) = -(s ^ ((k : ℝ) + u + 1 / 2)) := by
      rw [← ht2]; ring
    have hpos : (0 : ℝ) < s ^ ((k : ℝ) + u + 1 / 2) := Real.rpow_pos_of_pos hs0 _
    rw [ht, ht3, Real.rpow_neg hs0.le]
    field_simp
    ring
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, prod_rpow_eq hs0]
  congr 2
  have h3 : ∑ k ∈ Finset.range n, (-((k : ℝ) + u + 1 / 2))
      = -(((n : ℝ) * (n - 1) / 2) + n * u + n / 2) := by
    rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_range_cast,
      Finset.sum_const, Finset.sum_const, Finset.card_range]
    simp
    ring
  rw [h3]

/-- The elementary prefactor for negative `q`, rewritten through the envelope. -/
theorem prefactor_eq_envelope_neg {q : ℝ} (hq0 : q < 0) (hq1 : -1 < q) (n : ℕ) (u x : ℝ)
    (hx : x = (q ^ 2) ^ (-((n : ℝ) + u))) :
    (q ^ 2) ^ (-(((n : ℝ) * (n - 1) / 2) + n * u)) *
        (q ^ 2) ^ (-(((n : ℝ) * (n - 1) / 2) + n * u + n / 2))
      = envelope q x * (q ^ 2) ^ (u ^ 2 - u / 2) := by
  have hqne : q ≠ 0 := ne_of_lt hq0
  have hs0 : (0 : ℝ) < q ^ 2 := by positivity
  have habs : |q| < 1 := by rw [abs_of_neg hq0]; linarith
  have hlogq : Real.log q < 0 := by
    rw [← Real.log_abs]
    exact Real.log_neg (by rw [abs_pos]; exact hqne) habs
  set A := Real.log (1 / q) with hA
  have hA' : A = -Real.log q := by rw [hA, one_div, Real.log_inv]
  have hApos : 0 < A := by rw [hA']; linarith
  have hlogs : Real.log (q ^ 2) = -2 * A := by
    rw [Real.log_pow, hA']
    push_cast
    ring
  have hxpos : 0 < x := by rw [hx]; exact Real.rpow_pos_of_pos hs0 _
  have hlogx : Real.log x = 2 * ((n : ℝ) + u) * A := by
    rw [hx, Real.log_rpow hs0, hlogs]
    ring
  rw [envelope, ← hA, Real.rpow_def_of_pos hs0, Real.rpow_def_of_pos hs0,
    Real.rpow_def_of_pos hs0, Real.rpow_def_of_pos hxpos, hlogs, hlogx,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- The exact logarithmically periodic formula for `-1 < q < 0`, in the form valid for any
splitting `x = (q²)^{-(n+u)}` with `n` a natural number. -/
theorem exact_log_periodic_neg_of_eq {q : ℝ} (hq0 : q < 0) (hq1 : -1 < q) {f : ℝ → ℝ}
    (hcont : Continuous f) (hf : ∀ x, f x = (1 - q * x) * f (q * x))
    {x : ℝ} (hx : 1 < x) {n : ℕ} {u : ℝ} (hxeq : x = (q ^ 2) ^ (-((n : ℝ) + u))) :
    f x = f 0 * (-1) ^ n * envelope q x * phaseNeg q u / qPoch x⁻¹ q := by
  have hqne : q ≠ 0 := ne_of_lt hq0
  have hq : |q| < 1 := by rw [abs_of_neg hq0]; linarith
  set s : ℝ := q ^ 2 with hs
  have hs0 : (0 : ℝ) < s := by rw [hs]; positivity
  have hs1 : s < 1 := by
    rw [hs, ← sq_abs]
    nlinarith [abs_nonneg q]
  have hsabs : |s| < 1 := by rwa [abs_of_pos hs0]
  have hxpos : (0 : ℝ) < x := by linarith
  have hrq : s ^ ((1 : ℝ) / 2) = -q := by
    rw [← Real.sqrt_eq_rpow, hs, Real.sqrt_sq_eq_abs, abs_of_neg hq0]
  -- the four boundary identities
  have htail1 : s * x * s ^ n = s ^ (1 - u) := by
    rw [hxeq, ← Real.rpow_natCast s n, mul_assoc, ← Real.rpow_add hs0]
    nth_rewrite 1 [← Real.rpow_one s]
    rw [← Real.rpow_add hs0]
    congr 1
    ring
  have hhead1 : s ^ u * s ^ n = x⁻¹ := by
    rw [← Real.rpow_natCast s n, ← Real.rpow_add hs0, hxeq, Real.rpow_neg hs0.le, inv_inv]
    congr 1
    ring
  have htail2 : (-(s ^ ((1 : ℝ) / 2) * x)) * s ^ n = -(s ^ ((1 : ℝ) / 2 - u)) := by
    have : s ^ ((1 : ℝ) / 2) * x * s ^ n = s ^ ((1 : ℝ) / 2 - u) := by
      rw [hxeq, ← Real.rpow_natCast s n, mul_assoc, ← Real.rpow_add hs0, ← Real.rpow_add hs0]
      congr 1
      ring
    rw [← this]; ring
  have hhead2 : (-(s ^ (u + (1 : ℝ) / 2))) * s ^ n = x⁻¹ * q := by
    have h1 : s ^ (u + (1 : ℝ) / 2) * s ^ n = x⁻¹ * (-q) := by
      rw [← Real.rpow_natCast s n, ← Real.rpow_add hs0, ← hrq, hxeq, Real.rpow_neg hs0.le,
        inv_inv, ← Real.rpow_add hs0]
      congr 1
      ring
    rw [neg_mul, h1]
    ring
  -- denominators
  have hden1 : qPoch x⁻¹ s ≠ 0 := by
    refine qPoch_ne_zero hsabs fun k hk => ?_
    have h2 : s ^ k ≤ 1 := pow_le_one₀ hs0.le hs1.le
    have h3 : x⁻¹ < 1 := by rw [inv_lt_one₀ hxpos]; exact hx
    have h4 : (0 : ℝ) < x⁻¹ := by positivity
    have h1 : x⁻¹ * s ^ k < 1 := by nlinarith [pow_pos hs0 k]
    linarith [hk ▸ h1]
  have hden2 : qPoch (x⁻¹ * q) s ≠ 0 := by
    refine qPoch_ne_zero hsabs fun k hk => ?_
    have h4 : (0 : ℝ) < x⁻¹ := by positivity
    have h5 : x⁻¹ * q < 0 := mul_neg_of_pos_of_neg h4 hq0
    have h6 : (0 : ℝ) < s ^ k := pow_pos hs0 k
    nlinarith [hk ▸ (mul_neg_of_neg_of_pos h5 h6)]
  -- the two halves, in multiplied form
  have hsplit_even : qPoch (s * x) s * qPoch x⁻¹ s
      = (-1) ^ n * s ^ (-(((n : ℝ) * (n - 1) / 2) + n * u)) *
          (qPoch (s ^ u) s * qPoch (s ^ (1 - u)) s) := by
    have hmid : (∏ k ∈ Finset.range n, (1 - s ^ u * s ^ k)) * qPoch x⁻¹ s = qPoch (s ^ u) s := by
      rw [qPoch_split hsabs (s ^ u) n, hhead1]
    rw [qPoch_split hsabs (s * x) n, htail1, finite_prod_reflect hs0 n u x hxeq]
    calc (-1) ^ n * s ^ (-(((n : ℝ) * (n - 1) / 2) + n * u)) *
          (∏ k ∈ Finset.range n, (1 - s ^ u * s ^ k)) * qPoch (s ^ (1 - u)) s * qPoch x⁻¹ s
        = (-1) ^ n * s ^ (-(((n : ℝ) * (n - 1) / 2) + n * u)) *
            ((∏ k ∈ Finset.range n, (1 - s ^ u * s ^ k)) * qPoch x⁻¹ s) *
            qPoch (s ^ (1 - u)) s := by ring
      _ = _ := by rw [hmid]; ring
  have hsplit_odd : qPoch (-(s ^ ((1 : ℝ) / 2) * x)) s * qPoch (x⁻¹ * q) s
      = s ^ (-(((n : ℝ) * (n - 1) / 2) + n * u + n / 2)) *
          (qPoch (-(s ^ (u + (1 : ℝ) / 2))) s * qPoch (-(s ^ ((1 : ℝ) / 2 - u))) s) := by
    have hmid : (∏ k ∈ Finset.range n, (1 - (-(s ^ (u + (1 : ℝ) / 2))) * s ^ k)) *
        qPoch (x⁻¹ * q) s = qPoch (-(s ^ (u + (1 : ℝ) / 2))) s := by
      rw [qPoch_split hsabs (-(s ^ (u + (1 : ℝ) / 2))) n, hhead2]
    rw [qPoch_split hsabs (-(s ^ ((1 : ℝ) / 2) * x)) n, htail2,
      finite_prod_reflect_neg hs0 n u x hxeq]
    calc s ^ (-(((n : ℝ) * (n - 1) / 2) + n * u + n / 2)) *
          (∏ k ∈ Finset.range n, (1 - (-(s ^ (u + (1 : ℝ) / 2))) * s ^ k)) *
          qPoch (-(s ^ ((1 : ℝ) / 2 - u))) s * qPoch (x⁻¹ * q) s
        = s ^ (-(((n : ℝ) * (n - 1) / 2) + n * u + n / 2)) *
            ((∏ k ∈ Finset.range n, (1 - (-(s ^ (u + (1 : ℝ) / 2))) * s ^ k)) *
              qPoch (x⁻¹ * q) s) * qPoch (-(s ^ ((1 : ℝ) / 2 - u))) s := by ring
      _ = _ := by rw [hmid]; ring
  -- assemble
  have hfx : f x = f 0 * qPoch (q * x) q := by
    rw [eq_eulerProd hq hcont hf x, eulerProd_eq_qPoch]
  have hparity : qPoch (q * x) q = qPoch (-(s ^ ((1 : ℝ) / 2) * x)) s * qPoch (s * x) s := by
    rw [qPoch_parity_split hq (q * x), ← hs, hrq]
    congr 2
    · ring
    · rw [hs]; ring
  have hdenom : qPoch x⁻¹ q = qPoch x⁻¹ s * qPoch (x⁻¹ * q) s := by
    rw [qPoch_parity_split hq x⁻¹, ← hs]
  have hpre := prefactor_eq_envelope_neg hq0 hq1 n u x (by rw [← hs]; exact hxeq)
  rw [hdenom, eq_div_iff (mul_ne_zero hden1 hden2), hfx, hparity]
  calc f 0 * (qPoch (-(s ^ ((1 : ℝ) / 2) * x)) s * qPoch (s * x) s) *
        (qPoch x⁻¹ s * qPoch (x⁻¹ * q) s)
      = f 0 * ((qPoch (-(s ^ ((1 : ℝ) / 2) * x)) s * qPoch (x⁻¹ * q) s) *
          (qPoch (s * x) s * qPoch x⁻¹ s)) := by ring
    _ = f 0 * ((s ^ (-(((n : ℝ) * (n - 1) / 2) + n * u + n / 2)) *
          (qPoch (-(s ^ (u + (1 : ℝ) / 2))) s * qPoch (-(s ^ ((1 : ℝ) / 2 - u))) s)) *
          ((-1) ^ n * s ^ (-(((n : ℝ) * (n - 1) / 2) + n * u)) *
            (qPoch (s ^ u) s * qPoch (s ^ (1 - u)) s))) := by
        rw [hsplit_even, hsplit_odd]
    _ = f 0 * (-1) ^ n *
          (s ^ (-(((n : ℝ) * (n - 1) / 2) + n * u)) *
            s ^ (-(((n : ℝ) * (n - 1) / 2) + n * u + n / 2))) *
          (qPoch (s ^ u) s * qPoch (s ^ (1 - u)) s * qPoch (-(s ^ (u + (1 : ℝ) / 2))) s *
            qPoch (-(s ^ ((1 : ℝ) / 2 - u))) s) := by ring
    _ = f 0 * (-1) ^ n * (envelope q x * s ^ (u ^ 2 - u / 2)) *
          (qPoch (s ^ u) s * qPoch (s ^ (1 - u)) s * qPoch (-(s ^ (u + (1 : ℝ) / 2))) s *
            qPoch (-(s ^ ((1 : ℝ) / 2 - u))) s) := by rw [hpre]
    _ = f 0 * (-1) ^ n * envelope q x * phaseNeg q u := by rw [phaseNeg, ← hs]; ring

/-- The exact logarithmically periodic formula at `+∞` for `-1 < q < 0`. -/
theorem exact_log_periodic_neg {q : ℝ} (hq0 : q < 0) (hq1 : -1 < q) {f : ℝ → ℝ}
    (hcont : Continuous f) (hf : ∀ x, f x = (1 - q * x) * f (q * x))
    {x : ℝ} (hx : 1 < x) :
    f x = f 0 * (-1) ^ (⌊Real.log x / Real.log (1 / q ^ 2)⌋₊) * envelope q x *
      phaseNeg q (Real.log x / Real.log (1 / q ^ 2) - ⌊Real.log x / Real.log (1 / q ^ 2)⌋₊) /
      qPoch x⁻¹ q := by
  have hqne : q ≠ 0 := ne_of_lt hq0
  have hs0 : (0 : ℝ) < q ^ 2 := by positivity
  have hs1 : q ^ 2 < 1 := by
    rw [← sq_abs]
    have : |q| < 1 := by rw [abs_of_neg hq0]; linarith
    nlinarith [abs_nonneg q]
  have hlogs : Real.log (q ^ 2) < 0 := Real.log_neg hs0 hs1
  have hA' : Real.log (1 / q ^ 2) = -Real.log (q ^ 2) := by rw [one_div, Real.log_inv]
  have hApos : 0 < Real.log (1 / q ^ 2) := by rw [hA']; linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hxpos : (0 : ℝ) < x := by linarith
  set L := Real.log x / Real.log (1 / q ^ 2) with hLdef
  set n := ⌊L⌋₊ with hn
  refine exact_log_periodic_neg_of_eq hq0 hq1 hcont hf hx (n := n) (u := L - n) ?_
  have hsum : (n : ℝ) + (L - n) = L := by ring
  rw [hsum, Real.rpow_def_of_pos hs0, hLdef, hA']
  have h : Real.log (q ^ 2) * -(Real.log x / -Real.log (q ^ 2)) = Real.log x := by
    field_simp
    exact div_self hlogs.ne
  rw [h, Real.exp_log hxpos]

/-- `Ψ_q` is symmetric about `u = 1/2`. -/
theorem phaseNeg_symm {q : ℝ} (hq : |q| < 1) (hq0 : q ≠ 0) (u : ℝ) :
    phaseNeg q (1 - u) = phaseNeg q u := by
  set s : ℝ := q ^ 2 with hs
  have hs0 : (0 : ℝ) < s := by rw [hs]; positivity
  have hsabs : |s| < 1 := by
    rw [abs_of_pos hs0, hs, ← sq_abs]
    nlinarith [abs_nonneg q]
  have step : ∀ a : ℝ, qPoch a s = (1 - a) * qPoch (a * s) s := by
    intro a
    simpa using qPoch_split hsabs a 1
  have hP2 : qPoch (-(s ^ ((1 : ℝ) / 2 - u))) s
      = (1 + s ^ ((1 : ℝ) / 2 - u)) * qPoch (-(s ^ ((3 : ℝ) / 2 - u))) s := by
    have e : (-(s ^ ((1 : ℝ) / 2 - u))) * s = -(s ^ ((3 : ℝ) / 2 - u)) := by
      rw [show (3 : ℝ) / 2 - u = ((1 : ℝ) / 2 - u) + 1 by ring, Real.rpow_add hs0, Real.rpow_one]
      ring
    have h := step (-(s ^ ((1 : ℝ) / 2 - u)))
    rw [e] at h
    rw [h]
    ring_nf
  have hP4 : qPoch (-(s ^ (u - (1 : ℝ) / 2))) s
      = (1 + s ^ (u - (1 : ℝ) / 2)) * qPoch (-(s ^ (u + (1 : ℝ) / 2))) s := by
    have e : (-(s ^ (u - (1 : ℝ) / 2))) * s = -(s ^ (u + (1 : ℝ) / 2)) := by
      rw [show u + (1 : ℝ) / 2 = (u - (1 : ℝ) / 2) + 1 by ring, Real.rpow_add hs0, Real.rpow_one]
      ring
    have h := step (-(s ^ (u - (1 : ℝ) / 2)))
    rw [e] at h
    rw [h]
    ring_nf
  have hinv : s ^ ((1 : ℝ) / 2 - u) * s ^ (u - (1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hs0]
    norm_num
  have hscal : s ^ ((1 - u) ^ 2 - (1 - u) / 2) * (1 + s ^ (u - (1 : ℝ) / 2))
      = s ^ (u ^ 2 - u / 2) * (1 + s ^ ((1 : ℝ) / 2 - u)) := by
    have hE : ((1 - u) ^ 2 - (1 - u) / 2) = (u ^ 2 - u / 2) + ((1 : ℝ) / 2 - u) := by ring
    rw [hE, Real.rpow_add hs0]
    calc s ^ (u ^ 2 - u / 2) * s ^ ((1 : ℝ) / 2 - u) * (1 + s ^ (u - (1 : ℝ) / 2))
        = s ^ (u ^ 2 - u / 2) *
            (s ^ ((1 : ℝ) / 2 - u) + s ^ ((1 : ℝ) / 2 - u) * s ^ (u - (1 : ℝ) / 2)) := by ring
      _ = s ^ (u ^ 2 - u / 2) * (1 + s ^ ((1 : ℝ) / 2 - u)) := by rw [hinv]; ring
  rw [phaseNeg, phaseNeg, ← hs, show (1 : ℝ) - (1 - u) = u from by ring,
    show (1 - u) + (1 : ℝ) / 2 = (3 : ℝ) / 2 - u from by ring,
    show (1 : ℝ) / 2 - (1 - u) = u - (1 : ℝ) / 2 from by ring, hP2, hP4]
  calc s ^ ((1 - u) ^ 2 - (1 - u) / 2) * qPoch (s ^ (1 - u)) s * qPoch (s ^ u) s *
        qPoch (-(s ^ ((3 : ℝ) / 2 - u))) s *
        ((1 + s ^ (u - (1 : ℝ) / 2)) * qPoch (-(s ^ (u + (1 : ℝ) / 2))) s)
      = (s ^ ((1 - u) ^ 2 - (1 - u) / 2) * (1 + s ^ (u - (1 : ℝ) / 2))) *
          (qPoch (s ^ u) s * qPoch (s ^ (1 - u)) s * qPoch (-(s ^ (u + (1 : ℝ) / 2))) s *
            qPoch (-(s ^ ((3 : ℝ) / 2 - u))) s) := by ring
    _ = (s ^ (u ^ 2 - u / 2) * (1 + s ^ ((1 : ℝ) / 2 - u))) *
          (qPoch (s ^ u) s * qPoch (s ^ (1 - u)) s * qPoch (-(s ^ (u + (1 : ℝ) / 2))) s *
            qPoch (-(s ^ ((3 : ℝ) / 2 - u))) s) := by rw [hscal]
    _ = s ^ (u ^ 2 - u / 2) * qPoch (s ^ u) s * qPoch (s ^ (1 - u)) s *
          qPoch (-(s ^ (u + (1 : ℝ) / 2))) s *
          ((1 + s ^ ((1 : ℝ) / 2 - u)) * qPoch (-(s ^ ((3 : ℝ) / 2 - u))) s) := by ring

/-- `Ψ_q` is strictly positive on the open interval `(0,1)`. -/
theorem phaseNeg_pos {q : ℝ} (hq : |q| < 1) (hq0 : q ≠ 0) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    0 < phaseNeg q u := by
  have hs0 : (0 : ℝ) < q ^ 2 := by positivity
  have hs1 : q ^ 2 < 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg q]
  have h1 : 0 < qPoch ((q ^ 2) ^ u) (q ^ 2) :=
    qPoch_pos hs0 hs1 (Real.rpow_lt_one hs0.le hs1 hu0)
  have h2 : 0 < qPoch ((q ^ 2) ^ (1 - u)) (q ^ 2) :=
    qPoch_pos hs0 hs1 (Real.rpow_lt_one hs0.le hs1 (by linarith))
  have h3 : 0 < qPoch (-((q ^ 2) ^ (u + (1 : ℝ) / 2))) (q ^ 2) :=
    qPoch_pos hs0 hs1 (by
      have := Real.rpow_pos_of_pos hs0 (u + (1 : ℝ) / 2)
      linarith)
  have h4 : 0 < qPoch (-((q ^ 2) ^ ((1 : ℝ) / 2 - u))) (q ^ 2) :=
    qPoch_pos hs0 hs1 (by
      have := Real.rpow_pos_of_pos hs0 ((1 : ℝ) / 2 - u)
      linarith)
  have h5 : (0 : ℝ) < (q ^ 2) ^ (u ^ 2 - u / 2) := Real.rpow_pos_of_pos hs0 _
  rw [phaseNeg]
  positivity

/-- `Ψ_q` vanishes at the endpoints. -/
theorem phaseNeg_zero {q : ℝ} (hq : |q| < 1) : phaseNeg q 0 = 0 := by
  have hs : |q ^ 2| < 1 := by
    rw [abs_pow]
    nlinarith [abs_nonneg q]
  simp [phaseNeg, Real.rpow_zero, qPoch_one hs]

theorem phaseNeg_one {q : ℝ} (hq : |q| < 1) : phaseNeg q 1 = 0 := by
  have hs : |q ^ 2| < 1 := by
    rw [abs_pow]
    nlinarith [abs_nonneg q]
  simp [phaseNeg, Real.rpow_zero, qPoch_one hs]

end Q839
