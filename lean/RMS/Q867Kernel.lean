import RMS.Q867Entire

/-!
# The Fejér kernel as an entire function

For `q : ℕ`, `fejer q` is the entire function

`fejer q u = (1/q²) (∑_{j<q} e^{2πi j u / q}) (∑_{j<q} e^{-2πi j u / q})`,

which for real `u` equals `sin²(π u) / (q² sin²(π u / q))`, the (normalised) Fejér kernel.

The three facts we need are:

* `fejer_intCast`: it takes the value `1` at integers divisible by `q`, and `0` at all
  other integers;
* `norm_fejer_le`: the global bound `‖fejer q u‖ ≤ exp (2π |Im u|)`;
* `norm_fejer_le_of_dist`: the decay `‖fejer q u‖ ≤ exp (2π |Im u|) / (4 d²)` when the
  real part of `u` is at distance at least `d` from the lattice `q ℤ`.

Everything is proved by elementary manipulation of geometric sums; in particular
`fejer_eq_sum` exhibits `fejer q` as an explicit finite exponential sum.
-/

noncomputable section

open Complex

namespace Q867

/-- The (normalised) Fejér kernel of order `q`, as an entire function. -/
def fejer (q : ℕ) (u : ℂ) : ℂ :=
  ((∑ j ∈ Finset.range q, Complex.exp (2 * Real.pi * I * j * u / q)) *
    (∑ j ∈ Finset.range q, Complex.exp (-(2 * Real.pi * I * j * u / q)))) / (q : ℂ) ^ 2

/-- Expansion of the Fejér kernel as a finite exponential sum. -/
lemma fejer_eq_sum (q : ℕ) (u : ℂ) :
    fejer q u = ∑ p ∈ Finset.range q ×ˢ Finset.range q,
      (((q : ℂ) ^ 2)⁻¹ * Complex.exp (2 * Real.pi * I * ((p.1 : ℂ) - p.2) * u / q)) := by
  rw [fejer, Finset.sum_mul_sum, Finset.sum_product, div_eq_inv_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [← Complex.exp_add]
  congr 2
  ring

lemma differentiable_fejer (q : ℕ) : Differentiable ℂ (fejer q) := by
  unfold fejer
  fun_prop

/-- Both sums in the definition of `fejer` are geometric series. -/
lemma fejer_geom (q : ℕ) (hq : 0 < q) (u : ℂ) :
    fejer q u = ((∑ j ∈ Finset.range q, (Complex.exp (2 * Real.pi * I * u / q)) ^ j) *
      (∑ j ∈ Finset.range q, ((Complex.exp (2 * Real.pi * I * u / q))⁻¹) ^ j)) / (q : ℂ) ^ 2 := by
  have hqc : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  rw [fejer]
  congr 2
  · exact Finset.sum_congr rfl fun j _ => by rw [← Complex.exp_nat_mul]; congr 1; field_simp
  · exact Finset.sum_congr rfl fun j _ => by
      rw [← Complex.exp_neg, ← Complex.exp_nat_mul]; congr 1; field_simp

/-- The Fejér kernel at an integer point: `1` if `q ∣ k`, and `0` otherwise. -/
lemma fejer_intCast {q : ℕ} (hq : 0 < q) (k : ℤ) :
    fejer q (k : ℂ) = if (q : ℤ) ∣ k then 1 else 0 := by
  have hqc : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  set ζ := Complex.exp (2 * (Real.pi : ℂ) * I * (k : ℂ) / q) with hzdef
  have hone : ζ = 1 ↔ (q : ℤ) ∣ k := by
    rw [hzdef, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      field_simp at hn
      exact_mod_cast hn
    · rintro ⟨n, rfl⟩
      exact ⟨n, by push_cast; field_simp⟩
  have hzq : ζ ^ q = 1 := by
    rw [hzdef, ← Complex.exp_nat_mul]
    have h2 : (q : ℂ) * (2 * (Real.pi : ℂ) * I * (k : ℂ) / q)
        = (k : ℂ) * (2 * (Real.pi : ℂ) * I) := by field_simp
    rw [h2]
    exact Complex.exp_int_mul_two_pi_mul_I k
  rw [fejer_geom q hq, ← hzdef]
  by_cases hd : (q : ℤ) ∣ k
  · rw [if_pos hd, hone.2 hd]
    simp
    field_simp
  · rw [if_neg hd]
    have h1 : ζ ≠ 1 := fun h => hd (hone.1 h)
    rw [geom_sum_eq h1, hzq]
    simp

/-! ### The global bound -/

lemma norm_termA (q j : ℕ) (u : ℂ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * I * (j : ℂ) * u / q)‖
      = Real.exp (-(2 * Real.pi * j / q * u.im)) := by
  rw [Complex.norm_exp]
  congr 1
  have h : 2 * (Real.pi : ℂ) * I * (j : ℂ) * u / q
      = ((2 * Real.pi * j / q : ℝ) : ℂ) * (I * u) := by push_cast; ring
  rw [h, Complex.re_ofReal_mul]
  simp [Complex.mul_re]

lemma norm_termB (q j : ℕ) (u : ℂ) :
    ‖Complex.exp (-(2 * (Real.pi : ℂ) * I * (j : ℂ) * u / q))‖
      = Real.exp (2 * Real.pi * j / q * u.im) := by
  rw [Complex.norm_exp]
  congr 1
  have h : -(2 * (Real.pi : ℂ) * I * (j : ℂ) * u / q)
      = ((-(2 * Real.pi * j / q) : ℝ) : ℂ) * (I * u) := by push_cast; ring
  rw [h, Complex.re_ofReal_mul]
  simp [Complex.mul_re]

/-- Crude global bound for the Fejér kernel: it is of exponential type `2π` in the
imaginary direction. -/
lemma norm_fejer_le {q : ℕ} (hq : 0 < q) (u : ℂ) :
    ‖fejer q u‖ ≤ Real.exp (2 * Real.pi * |u.im|) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set M := Real.exp (2 * Real.pi * |u.im|) with hM
  have hM1 : (1 : ℝ) ≤ M := Real.one_le_exp (by positivity)
  have hjq : ∀ j ∈ Finset.range q, (2 * Real.pi * (j : ℝ) / q) ≤ 2 * Real.pi := by
    intro j hj
    rw [Finset.mem_range] at hj
    have : (j : ℝ) ≤ q := by exact_mod_cast hj.le
    rw [div_le_iff₀ hq0]
    nlinarith [Real.pi_pos]
  have hjnn : ∀ j : ℕ, (0 : ℝ) ≤ 2 * Real.pi * (j : ℝ) / q := fun j => by positivity
  have hkey : ‖∑ j ∈ Finset.range q, Complex.exp (2 * (Real.pi : ℂ) * I * (j : ℂ) * u / q)‖ *
      ‖∑ j ∈ Finset.range q, Complex.exp (-(2 * (Real.pi : ℂ) * I * (j : ℂ) * u / q))‖
      ≤ (q : ℝ) ^ 2 * M := by
    rcases le_or_gt 0 u.im with hs | hs
    · have hAle : ‖∑ j ∈ Finset.range q,
          Complex.exp (2 * (Real.pi : ℂ) * I * (j : ℂ) * u / q)‖ ≤ (q : ℝ) := by
        refine le_trans (norm_sum_le _ _) ?_
        calc ∑ j ∈ Finset.range q, ‖Complex.exp (2 * (Real.pi : ℂ) * I * (j : ℂ) * u / q)‖
            ≤ ∑ _j ∈ Finset.range q, (1 : ℝ) := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [norm_termA, Real.exp_le_one_iff]
              nlinarith [hjnn j]
          _ = (q : ℝ) := by simp
      have hBle : ‖∑ j ∈ Finset.range q,
          Complex.exp (-(2 * (Real.pi : ℂ) * I * (j : ℂ) * u / q))‖ ≤ (q : ℝ) * M := by
        refine le_trans (norm_sum_le _ _) ?_
        calc ∑ j ∈ Finset.range q, ‖Complex.exp (-(2 * (Real.pi : ℂ) * I * (j : ℂ) * u / q))‖
            ≤ ∑ _j ∈ Finset.range q, M := by
              refine Finset.sum_le_sum fun j hj => ?_
              rw [norm_termB, hM]
              refine Real.exp_le_exp.2 ?_
              have h1 := hjq j hj
              rw [abs_of_nonneg hs]
              nlinarith
          _ = (q : ℝ) * M := by simp
      calc _ ≤ (q : ℝ) * ((q : ℝ) * M) := mul_le_mul hAle hBle (norm_nonneg _) hq0.le
        _ = (q : ℝ) ^ 2 * M := by ring
    · have hAle : ‖∑ j ∈ Finset.range q,
          Complex.exp (2 * (Real.pi : ℂ) * I * (j : ℂ) * u / q)‖ ≤ (q : ℝ) * M := by
        refine le_trans (norm_sum_le _ _) ?_
        calc ∑ j ∈ Finset.range q, ‖Complex.exp (2 * (Real.pi : ℂ) * I * (j : ℂ) * u / q)‖
            ≤ ∑ _j ∈ Finset.range q, M := by
              refine Finset.sum_le_sum fun j hj => ?_
              rw [norm_termA, hM]
              refine Real.exp_le_exp.2 ?_
              have h1 := hjq j hj
              rw [abs_of_neg hs]
              nlinarith
          _ = (q : ℝ) * M := by simp
      have hBle : ‖∑ j ∈ Finset.range q,
          Complex.exp (-(2 * (Real.pi : ℂ) * I * (j : ℂ) * u / q))‖ ≤ (q : ℝ) := by
        refine le_trans (norm_sum_le _ _) ?_
        calc ∑ j ∈ Finset.range q, ‖Complex.exp (-(2 * (Real.pi : ℂ) * I * (j : ℂ) * u / q))‖
            ≤ ∑ _j ∈ Finset.range q, (1 : ℝ) := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [norm_termB, Real.exp_le_one_iff]
              nlinarith [hjnn j]
          _ = (q : ℝ) := by simp
      calc _ ≤ ((q : ℝ) * M) * (q : ℝ) := mul_le_mul hAle hBle (norm_nonneg _) (by positivity)
        _ = (q : ℝ) ^ 2 * M := by ring
  rw [fejer, norm_div, norm_mul, norm_pow, Complex.norm_natCast]
  rw [div_le_iff₀ (by positivity)]
  linarith [hkey]

/-! ### The decay estimate -/

/-- A lower bound for `‖e^w - 1‖` in terms of the imaginary part of `w`. -/
lemma two_exp_abs_sin_le (w : ℂ) :
    2 * Real.exp (w.re / 2) * |Real.sin (w.im / 2)| ≤ ‖Complex.exp w - 1‖ := by
  have hfac : Complex.exp w - 1
      = Complex.exp (w / 2) * (Complex.exp (w / 2) - Complex.exp (-(w / 2))) := by
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add]
    norm_num
  have h1 : ‖Complex.exp w - 1‖
      = Real.exp (w.re / 2) * ‖Complex.exp (w / 2) - Complex.exp (-(w / 2))‖ := by
    rw [hfac, norm_mul, Complex.norm_exp]
    congr 2
    simp
  have h3 : (Complex.exp (w / 2) - Complex.exp (-(w / 2))).im
      = (Real.exp (w.re / 2) + Real.exp (-(w.re / 2))) * Real.sin (w.im / 2) := by
    simp [Complex.exp_im]
    ring
  have h2 : |(Complex.exp (w / 2) - Complex.exp (-(w / 2))).im|
      ≤ ‖Complex.exp (w / 2) - Complex.exp (-(w / 2))‖ := Complex.abs_im_le_norm _
  rw [h3, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.exp (w.re / 2) + Real.exp (-(w.re / 2)))] at h2
  have habs : (0 : ℝ) ≤ |Real.sin (w.im / 2)| := abs_nonneg _
  have hge2 : (2 : ℝ) ≤ Real.exp (w.re / 2) + Real.exp (-(w.re / 2)) := by
    have ht : Real.exp (-(w.re / 2)) = (Real.exp (w.re / 2))⁻¹ := by rw [Real.exp_neg]
    have hp : 0 < Real.exp (w.re / 2) := Real.exp_pos _
    have hmul : Real.exp (w.re / 2) * (Real.exp (w.re / 2))⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
    rw [ht]
    nlinarith [sq_nonneg (Real.exp (w.re / 2) - 1)]
  have hstep : 2 * |Real.sin (w.im / 2)| ≤ ‖Complex.exp (w / 2) - Complex.exp (-(w / 2))‖ :=
    le_trans (mul_le_mul_of_nonneg_right hge2 habs) h2
  rw [h1]
  calc 2 * Real.exp (w.re / 2) * |Real.sin (w.im / 2)|
      = Real.exp (w.re / 2) * (2 * |Real.sin (w.im / 2)|) := by ring
    _ ≤ Real.exp (w.re / 2) * ‖Complex.exp (w / 2) - Complex.exp (-(w / 2))‖ :=
        mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le

lemma abs_sin_pi_ge_half {y : ℝ} (hy : |y| ≤ 1 / 2) : 2 * |y| ≤ |Real.sin (Real.pi * y)| := by
  rcases le_or_gt 0 y with h | h
  · have hy2 : y ≤ 1 / 2 := by rw [abs_of_nonneg h] at hy; exact hy
    have h1 : 0 ≤ Real.pi * y := by positivity
    have h2 : Real.pi * y ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
    have hpi := Real.pi_pos
    have hsin : 2 * y ≤ Real.sin (Real.pi * y) := by
      have heq : 2 / Real.pi * (Real.pi * y) = 2 * y := by field_simp
      linarith [heq ▸ Real.mul_le_sin h1 h2]
    rw [abs_of_nonneg h, abs_of_nonneg (le_trans (by linarith) hsin)]
    linarith
  · have hy2 : -y ≤ 1 / 2 := by rw [abs_of_neg h] at hy; exact hy
    have h1 : 0 ≤ Real.pi * (-y) := by nlinarith [Real.pi_pos]
    have h2 : Real.pi * (-y) ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
    have hpi := Real.pi_pos
    have hsin : 2 * (-y) ≤ Real.sin (Real.pi * (-y)) := by
      have heq : 2 / Real.pi * (Real.pi * (-y)) = 2 * (-y) := by field_simp
      linarith [heq ▸ Real.mul_le_sin h1 h2]
    have hneg : Real.sin (Real.pi * (-y)) = -Real.sin (Real.pi * y) := by
      rw [show Real.pi * (-y) = -(Real.pi * y) by ring, Real.sin_neg]
    rw [hneg] at hsin
    rw [abs_of_neg h, abs_of_nonpos (by linarith)]
    linarith

lemma abs_sin_pi_int (x : ℝ) (r : ℤ) :
    |Real.sin (Real.pi * x)| = |Real.sin (Real.pi * (x - r))| := by
  have hx : Real.pi * x = Real.pi * (x - r) + (r : ℝ) * Real.pi := by ring
  rw [hx, Real.sin_add, Real.sin_int_mul_pi, mul_zero, add_zero, abs_mul]
  have hc : |Real.cos ((r : ℝ) * Real.pi)| = 1 := by
    have h1 : Real.sin ((r : ℝ) * Real.pi) ^ 2 + Real.cos ((r : ℝ) * Real.pi) ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq _
    rw [Real.sin_int_mul_pi] at h1
    nlinarith [abs_nonneg (Real.cos ((r : ℝ) * Real.pi)), sq_abs (Real.cos ((r : ℝ) * Real.pi))]
  rw [hc, mul_one]

lemma abs_sin_pi_ge_round (x : ℝ) : 2 * |x - round x| ≤ |Real.sin (Real.pi * x)| := by
  rw [abs_sin_pi_int x (round x)]
  exact abs_sin_pi_ge_half (abs_sub_round x)

lemma fejer_den_bound (w : ℂ) :
    4 * (Real.sin (w.im / 2)) ^ 2 ≤ ‖(Complex.exp w - 1) * ((Complex.exp w)⁻¹ - 1)‖ := by
  set s : ℝ := Real.sin (w.im / 2) with hs
  set ζ : ℂ := Complex.exp w with hzeta
  have hzne : ζ ≠ 0 := Complex.exp_ne_zero w
  have hzn : ‖ζ‖ = Real.exp w.re := Complex.norm_exp w
  have h1 : 2 * Real.exp (w.re / 2) * |s| ≤ ‖ζ - 1‖ := two_exp_abs_sin_le w
  have h2 : ‖ζ⁻¹ - 1‖ = ‖ζ - 1‖ / ‖ζ‖ := by
    have he : ζ⁻¹ - 1 = -((ζ - 1) / ζ) := by field_simp; ring
    rw [he, norm_neg, norm_div]
  rw [norm_mul, h2, hzn]
  have hexp : Real.exp (w.re / 2) * Real.exp (w.re / 2) = Real.exp w.re := by
    rw [← Real.exp_add]; congr 1; ring
  have hnn : 0 ≤ ‖ζ - 1‖ := norm_nonneg _
  have key : 4 * s ^ 2 * Real.exp w.re ≤ ‖ζ - 1‖ * ‖ζ - 1‖ := by
    have hmm := mul_le_mul h1 h1 (by positivity) hnn
    calc 4 * s ^ 2 * Real.exp w.re
        = (2 * Real.exp (w.re / 2) * |s|) * (2 * Real.exp (w.re / 2) * |s|) := by
          rw [← hexp, ← sq_abs s]; ring
      _ ≤ ‖ζ - 1‖ * ‖ζ - 1‖ := hmm
  rw [← mul_div_assoc, le_div_iff₀ (Real.exp_pos _)]
  exact key

/-- Decay of the Fejér kernel away from the lattice `q ℤ`, in terms of the distance `d`
from `Re u` to that lattice. -/
lemma norm_fejer_le_of_dist {q : ℕ} (hq : 0 < q) (u : ℂ) (d : ℝ) (hd : 0 < d)
    (hdist : ∀ k : ℤ, d ≤ |u.re - q * k|) :
    ‖fejer q u‖ ≤ Real.exp (2 * Real.pi * |u.im|) / (4 * d ^ 2) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqc : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  set w : ℂ := 2 * (Real.pi : ℂ) * I * u / (q : ℂ) with hw
  have hwe : w = ((2 * Real.pi / q : ℝ) : ℂ) * (I * u) := by rw [hw]; push_cast; ring
  have hre : w.re = -(2 * Real.pi / q * u.im) := by
    rw [hwe, Complex.re_ofReal_mul]; simp [Complex.mul_re]
  have him : w.im = 2 * Real.pi / q * u.re := by
    rw [hwe, Complex.im_ofReal_mul]; simp [Complex.mul_im]
  have hhalf : w.im / 2 = Real.pi * (u.re / q) := by rw [him]; field_simp
  set s : ℝ := Real.sin (w.im / 2) with hs
  -- the lower bound on `|sin|`
  have hsq : 4 * d ^ 2 ≤ (q : ℝ) ^ 2 * s ^ 2 := by
    have h1 : 2 * |u.re / q - round (u.re / q)| ≤ |s| := by
      rw [hs, hhalf]; exact abs_sin_pi_ge_round _
    have hab : u.re - (q : ℝ) * ((round (u.re / (q : ℝ)) : ℤ) : ℝ)
        = (u.re / q - ((round (u.re / q) : ℤ) : ℝ)) * q := by field_simp
    have h2 : d / q ≤ |u.re / q - round (u.re / q)| := by
      rw [div_le_iff₀ hq0]
      calc d ≤ |u.re - (q : ℝ) * ((round (u.re / (q : ℝ)) : ℤ) : ℝ)| := hdist _
        _ = |u.re / q - ((round (u.re / q) : ℤ) : ℝ)| * q := by
            rw [hab, abs_mul, abs_of_pos hq0]
    have h3 : 2 * (d / q) ≤ |s| := le_trans (by linarith) h1
    have h4 : (2 * d / q) ^ 2 ≤ |s| ^ 2 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      calc 2 * d / q = 2 * (d / q) := by ring
        _ ≤ |s| := h3
    rw [sq_abs, div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) ^ 2)] at h4
    nlinarith [h4]
  set ζ : ℂ := Complex.exp w with hzeta
  have hzne : ζ ≠ 0 := Complex.exp_ne_zero w
  have hzn : ‖ζ‖ = Real.exp w.re := Complex.norm_exp w
  have hden : 4 * s ^ 2 ≤ ‖(ζ - 1) * (ζ⁻¹ - 1)‖ := fejer_den_bound w
  set a : ℝ := 2 * Real.pi * u.im with ha
  have hzqn : ‖ζ ^ q‖ = Real.exp (-a) := by
    rw [norm_pow, hzn, ← Real.exp_nat_mul]
    congr 1
    rw [hre, ha]; field_simp
  have hziqn : ‖(ζ⁻¹) ^ q‖ = Real.exp a := by
    rw [norm_pow, norm_inv, hzn, ← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    rw [hre, ha]; field_simp
  have habs : |a| = 2 * Real.pi * |u.im| := by
    rw [ha, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hnum : ‖(ζ ^ q - 1) * ((ζ⁻¹) ^ q - 1)‖ ≤ 4 * Real.exp (2 * Real.pi * |u.im|) := by
    rw [norm_mul]
    have h1 : ‖ζ ^ q - 1‖ ≤ Real.exp (-a) + 1 := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [hzqn, norm_one]
    have h2 : ‖(ζ⁻¹) ^ q - 1‖ ≤ Real.exp a + 1 := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [hziqn, norm_one]
    have h3 : Real.exp a ≤ Real.exp |a| := Real.exp_le_exp.2 (le_abs_self a)
    have h4 : Real.exp (-a) ≤ Real.exp |a| := Real.exp_le_exp.2 (neg_le_abs a)
    have h5 : (1 : ℝ) ≤ Real.exp |a| := Real.one_le_exp (abs_nonneg a)
    calc ‖ζ ^ q - 1‖ * ‖(ζ⁻¹) ^ q - 1‖ ≤ (Real.exp (-a) + 1) * (Real.exp a + 1) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = Real.exp (-a) * Real.exp a + Real.exp (-a) + Real.exp a + 1 := by ring
      _ = 1 + Real.exp (-a) + Real.exp a + 1 := by rw [← Real.exp_add]; norm_num
      _ ≤ 4 * Real.exp |a| := by linarith
      _ = 4 * Real.exp (2 * Real.pi * |u.im|) := by rw [habs]
  have hprod : fejer q u * ((q : ℂ) ^ 2 * ((ζ - 1) * (ζ⁻¹ - 1)))
      = (ζ ^ q - 1) * ((ζ⁻¹) ^ q - 1) := by
    rw [fejer_geom q hq, ← hzeta, ← geom_sum_mul ζ q, ← geom_sum_mul ζ⁻¹ q]
    field_simp
  have hnorms : ‖fejer q u‖ * ((q : ℝ) ^ 2 * ‖(ζ - 1) * (ζ⁻¹ - 1)‖)
      = ‖(ζ ^ q - 1) * ((ζ⁻¹) ^ q - 1)‖ := by
    have h := congrArg norm hprod
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast] at h
    exact h
  have hfn : 0 ≤ ‖fejer q u‖ := norm_nonneg _
  have hstep : ‖fejer q u‖ * (16 * d ^ 2) ≤ 4 * Real.exp (2 * Real.pi * |u.im|) := by
    calc ‖fejer q u‖ * (16 * d ^ 2) ≤ ‖fejer q u‖ * ((q : ℝ) ^ 2 * (4 * s ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hfn
          nlinarith [hsq]
      _ ≤ ‖fejer q u‖ * ((q : ℝ) ^ 2 * ‖(ζ - 1) * (ζ⁻¹ - 1)‖) := by
          refine mul_le_mul_of_nonneg_left ?_ hfn
          exact mul_le_mul_of_nonneg_left hden (by positivity)
      _ = ‖(ζ ^ q - 1) * ((ζ⁻¹) ^ q - 1)‖ := hnorms
      _ ≤ 4 * Real.exp (2 * Real.pi * |u.im|) := hnum
  rw [le_div_iff₀ (by positivity)]
  linarith

end Q867
