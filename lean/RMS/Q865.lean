import Mathlib

/-!
# Q865 — a self-contained formalization

Source problem: Q865 (https://lucpommeret.com/assets/Qsansreponse260405.pdf).

For `n ≥ 2` let `P n (X) = X ^ n - ∑_{k < n} X ^ k`, let `ρ n` be its unique positive real
root, let `r m` be the smallest modulus of a complex root of `P m`, and `u n = 2 ^ (-n-1)`.

This file contains complete proofs of the three parts of the answer:

* **(a)** `A k (X) = (1 / (k+1)!) ∏_{j<k} ((k+1) X + j) = C((k+1)(X+1) - 2, k) / (k+1)`
  (`Q865.Acoef_formula`);
* **(b)** for every integer `n ≥ 2` the series `∑_k A k (n) u n ^ (k+1)` converges
  absolutely and `ρ n = 2 (1 - ∑_k A k (n) u n ^ (k+1))` (`Q865.summable_A`,
  `Q865.pos_root_eq_series`, and the explicit binomial form `Q865.pos_root_eq_series'`);
* **(c)** `(2n+1) (1 - r (2n+1)) → log 3` as `n → ∞` (`Q865.odd_limit`); in fact
  `m (1 - r m) → log 3` along all integers (`Q865.tendsto_rmin`).

Lean version: 4.28.0.  Mathlib: pinned at tag `v4.28.0`
(commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`).

Remarks on the formalization (differences with the printed statement):

* The printed answer also claims the sharper asymptotic expansion
  `r m = 1 - log 3 / m + ((log 3)^2/2 + (log 3)/3) / m^2 + O(m^{-3})`.  Only the limit
  statement of part (c) (which is what the question asks for) is formalized here.
* `ρ n` is not introduced as a function: the statement of part (b) is phrased for an
  arbitrary positive real root `x` of `P n`, which is legitimate since such a root exists
  and is unique (`Q865.exists_unique_pos_root`).
* `r m` is defined as the infimum `Q865.rmin m` of the moduli of the complex roots of
  `P m`; the infimum is attained but this is not needed.
-/



/-!
# Q865 : basic definitions and the algebraic reduction

For `n ≥ 2` we study the polynomial `P n (X) = X ^ n - ∑_{k<n} X ^ k`.
-/

namespace Q865

open Finset Polynomial

/-- `Pc n = X ^ n - ∑_{k < n} X ^ k`, as a complex polynomial. -/
noncomputable def Pc (n : ℕ) : Polynomial ℂ := X ^ n - ∑ k ∈ range n, X ^ k

@[simp] theorem eval_Pc (n : ℕ) (z : ℂ) :
    (Pc n).eval z = z ^ n - ∑ k ∈ range n, z ^ k := by
  simp [Pc]

/-- The algebraic reduction `(z - 1) * P n (z) = 1 - z ^ n * (2 - z)`. -/
theorem factor_identity {R : Type*} [CommRing R] (n : ℕ) (z : R) :
    (z - 1) * (z ^ n - ∑ k ∈ range n, z ^ k) = 1 - z ^ n * (2 - z) := by
  have h : (∑ k ∈ range n, z ^ k) * (z - 1) = z ^ n - 1 := geom_sum_mul z n
  have : (z - 1) * (∑ k ∈ range n, z ^ k) = z ^ n - 1 := by
    rw [mul_comm]; exact h
  rw [mul_sub, this]
  ring

/-- For `z ≠ 1`, `z` is a root of `P n` iff `z ^ n * (2 - z) = 1`. -/
theorem isRoot_Pc_iff (n : ℕ) (z : ℂ) (hz : z ≠ 1) :
    (Pc n).IsRoot z ↔ z ^ n * (2 - z) = 1 := by
  have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  constructor
  · intro h
    have h0 : (z - 1) * (z ^ n - ∑ k ∈ range n, z ^ k) = 0 := by
      rw [show (z ^ n - ∑ k ∈ range n, z ^ k) = (Pc n).eval z by simp, h.eq_zero, mul_zero]
    rw [factor_identity] at h0
    linear_combination -h0
  · intro h
    have h0 : (z - 1) * (z ^ n - ∑ k ∈ range n, z ^ k) = 0 := by
      rw [factor_identity, h]; ring
    have := mul_eq_zero.mp h0
    rcases this with h1 | h1
    · exact absurd h1 hz'
    · simpa [Polynomial.IsRoot, Pc] using h1

/-- Same reduction over the reals. -/
theorem real_root_iff (n : ℕ) (x : ℝ) (hx : x ≠ 1) :
    x ^ n = (∑ k ∈ range n, x ^ k) ↔ x ^ n * (2 - x) = 1 := by
  have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  constructor
  · intro h
    have h0 : (x - 1) * (x ^ n - ∑ k ∈ range n, x ^ k) = 0 := by
      rw [h]; ring
    rw [factor_identity] at h0
    linarith
  · intro h
    have h0 : (x - 1) * (x ^ n - ∑ k ∈ range n, x ^ k) = 0 := by
      rw [factor_identity, h]; ring
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hx'
    · linarith

/-- `u n = 2 ^ (-(n+1))`. -/
noncomputable def uu (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ (n + 1)

theorem uu_pos (n : ℕ) : 0 < uu n := by
  unfold uu; positivity

/-- The coefficients of the inverse series: `c_m = (1/m) * C((n+1)m-2, m-1)`. -/
noncomputable def cc (n m : ℕ) : ℝ := ((((n + 1) * m - 2).choose (m - 1) : ℕ) : ℝ) / m

@[simp] theorem cc_zero (n : ℕ) : cc n 0 = 0 := by simp [cc]

@[simp] theorem cc_one (n : ℕ) : cc n 1 = 1 := by
  simp [cc]

theorem cc_nonneg (n m : ℕ) : 0 ≤ cc n m := by
  unfold cc; positivity

/-- The polynomials `A k` of part (a):
`A k (X) = (1/(k+1)!) * ∏_{j<k} ((k+1) X + j)`. -/
noncomputable def Acoef (k : ℕ) : Polynomial ℚ :=
  C ((Nat.factorial (k + 1) : ℚ))⁻¹ * ∏ j ∈ range k, (C ((k : ℚ) + 1) * X + C (j : ℚ))

/-- The real value `A k (n)`. -/
noncomputable def Aval (k n : ℕ) : ℝ := Rat.cast ((Acoef k).eval (n : ℚ))

/-- Convolution of two sequences of reals. -/
noncomputable def conv (f g : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ Finset.antidiagonal m, f p.1 * g p.2

/-- Iterated convolution power of a sequence. -/
noncomputable def convPow (f : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun m => if m = 0 then 1 else 0
  | (p + 1) => conv (convPow f p) f

/-- The smallest modulus of a complex root of `P m`. -/
noncomputable def rmin (m : ℕ) : ℝ := sInf ((fun z : ℂ => ‖z‖) '' {z : ℂ | (Pc m).IsRoot z})

end Q865


/-!
# Q865 : existence and uniqueness of the positive real root

For `x > 0` we have `P n (x) = x ^ n * h n x` where `h n x = 1 - ∑_{k<n} x⁻¹ ^ (k+1)`,
and `h n` is strictly monotone on `(0, ∞)`; this gives existence and uniqueness at once.
-/

namespace Q865

open Finset

/-- The normalised polynomial `P n (x) / x ^ n`. -/
noncomputable def hfun (n : ℕ) (x : ℝ) : ℝ := 1 - ∑ k ∈ range n, x⁻¹ ^ (k + 1)

theorem geom_half (n : ℕ) : ∑ k ∈ range n, ((2 : ℝ)⁻¹) ^ (k + 1) = 1 - (2 : ℝ)⁻¹ ^ n := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

theorem hfun_one_neg (n : ℕ) (hn : 2 ≤ n) : hfun n 1 < 0 := by
  unfold hfun
  simp only [inv_one, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

theorem hfun_two_pos (n : ℕ) : 0 < hfun n 2 := by
  unfold hfun
  rw [geom_half]
  have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  linarith

theorem pow_mul_hfun (n : ℕ) {x : ℝ} (hx : 0 < x) :
    x ^ n * hfun n x = x ^ n - ∑ k ∈ range n, x ^ k := by
  unfold hfun
  rw [mul_sub, mul_one, Finset.mul_sum]
  congr 1
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp only [Finset.mem_range] at hk
  rw [inv_pow, ← pow_sub₀ x (ne_of_gt hx) (by omega)]
  congr 1
  omega

theorem hfun_strictMonoOn (n : ℕ) (hn : 1 ≤ n) :
    StrictMonoOn (hfun n) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  unfold hfun
  have hlt : ∑ k ∈ range n, b⁻¹ ^ (k + 1) < ∑ k ∈ range n, a⁻¹ ^ (k + 1) := by
    apply Finset.sum_lt_sum
    · intro k _
      exact pow_le_pow_left₀ (by positivity) (inv_anti₀ ha hab.le) _
    · refine ⟨0, Finset.mem_range.mpr hn, ?_⟩
      simpa using inv_strictAnti₀ ha hab
  linarith

theorem root_iff_hfun (n : ℕ) {x : ℝ} (hx : 0 < x) :
    x ^ n = (∑ k ∈ range n, x ^ k) ↔ hfun n x = 0 := by
  have h := pow_mul_hfun n hx
  constructor
  · intro h1
    have h2 : x ^ n * hfun n x = 0 := by rw [h, h1]; ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (by positivity)
    · exact h3
  · intro h1
    rw [h1, mul_zero] at h
    linarith

/-- Any positive root lies in `(1, 2)`. -/
theorem pos_root_mem (n : ℕ) (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x)
    (hroot : x ^ n = ∑ k ∈ range n, x ^ k) : 1 < x ∧ x < 2 := by
  have hz : hfun n x = 0 := (root_iff_hfun n hx).mp hroot
  have h1 : hfun n 1 < 0 := hfun_one_neg n hn
  have h2 : 0 < hfun n 2 := hfun_two_pos n
  have hmono := hfun_strictMonoOn n (by omega)
  constructor
  · by_contra hc
    push_neg at hc
    rcases lt_or_eq_of_le hc with h | h
    · have := hmono (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr (by norm_num : (0:ℝ) < 1)) h
      rw [hz] at this; linarith
    · rw [← h] at h1; rw [hz] at h1; linarith
  · by_contra hc
    push_neg at hc
    rcases lt_or_eq_of_le hc with h | h
    · have := hmono (Set.mem_Ioi.mpr (by norm_num : (0:ℝ) < 2)) (Set.mem_Ioi.mpr hx) h
      rw [hz] at this; linarith
    · rw [h] at h2; rw [hz] at h2; linarith

/-- `P n` has a unique positive real root. -/
theorem exists_unique_pos_root (n : ℕ) (hn : 2 ≤ n) :
    ∃! x : ℝ, 0 < x ∧ x ^ n = ∑ k ∈ range n, x ^ k := by
  have hcont : ContinuousOn (hfun n) (Set.Icc 1 2) := by
    unfold hfun
    apply ContinuousOn.sub continuousOn_const
    apply continuousOn_finset_sum
    intro k _
    apply ContinuousOn.pow
    apply ContinuousOn.inv₀ continuousOn_id
    intro x hx
    simp only [Set.mem_Icc] at hx
    simp only [id]
    linarith [hx.1]
  have h1 : hfun n 1 < 0 := hfun_one_neg n hn
  have h2 : 0 < hfun n 2 := hfun_two_pos n
  obtain ⟨x, hxmem, hx0⟩ : ∃ x ∈ Set.Icc (1 : ℝ) 2, hfun n x = 0 := by
    have hiv := intermediate_value_Icc (by norm_num : (1:ℝ) ≤ 2) hcont
    have hmem : (0 : ℝ) ∈ Set.Icc (hfun n 1) (hfun n 2) := by
      constructor <;> linarith
    obtain ⟨x, hx, hx'⟩ := hiv hmem
    exact ⟨x, hx, hx'⟩
  simp only [Set.mem_Icc] at hxmem
  have hxpos : 0 < x := by linarith [hxmem.1]
  refine ⟨x, ⟨hxpos, (root_iff_hfun n hxpos).mpr hx0⟩, ?_⟩
  rintro y ⟨hy, hyroot⟩
  have hy0 : hfun n y = 0 := (root_iff_hfun n hy).mp hyroot
  have hmono := hfun_strictMonoOn n (by omega)
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hmono (Set.mem_Ioi.mpr hy) (Set.mem_Ioi.mpr hxpos) h
    rw [hx0, hy0] at this; linarith
  · have := hmono (Set.mem_Ioi.mpr hxpos) (Set.mem_Ioi.mpr hy) h
    rw [hx0, hy0] at this; linarith

end Q865


/-!
# Q865 : the formal (Lagrange inversion) part

Let `F = X * (1 - X) ^ n ∈ ℚ[X]`.  We construct the truncated compositional inverse of `F`
and prove Lagrange's formula for its coefficients:
`m * a m = C ((n+1) * m - 2, m - 1)`.

The proof of Lagrange's formula is the classical residue computation, carried out with
`PowerSeries` and the units `(1 - X)⁻ᵈ = PowerSeries.invOneSubPow`.
-/

namespace Q865

open Finset Polynomial

/-- `F = X (1-X)^n`. -/
noncomputable def Fp (n : ℕ) : Polynomial ℚ := X * (1 - X) ^ n

/-- `(1 - X) ^ (-d)` as a power series. -/
noncomputable def Wser (d : ℕ) : PowerSeries ℚ := (PowerSeries.invOneSubPow ℚ d : PowerSeries ℚ)

/-- Truncated compositional left inverse of a polynomial `q` with `q(0) = 0`, `q'(0) = 1`:
`linv q K` is a polynomial of degree `≤ K` with `(linv q K).comp q ≡ X  [mod X^(K+1)]`. -/
noncomputable def linv (q : Polynomial ℚ) : ℕ → Polynomial ℚ
  | 0 => 0
  | (k + 1) =>
      (linv q k) +
        C ((if k + 1 = 1 then (1 : ℚ) else 0) - ((linv q k).comp q).coeff (k + 1)) * X ^ (k + 1)

/-! ### Elementary facts -/

theorem one_sub_pow_expand {R : Type*} [CommRing R] (S : R) (n : ℕ) :
    S * (1 - S) ^ n = ∑ j ∈ range (n + 1), ((-1) ^ j * (n.choose j : R)) * S ^ (j + 1) := by
  have h : (1 - S) = (-S) + 1 := by ring
  rw [h, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [neg_pow]
  ring

theorem coe_sum_range (K : ℕ) (f : ℕ → Polynomial ℚ) :
    ((∑ j ∈ range K, f j : Polynomial ℚ) : PowerSeries ℚ)
      = ∑ j ∈ range K, ((f j : PowerSeries ℚ)) := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih, Polynomial.coe_add]

theorem eq_X_mul_divX {q : Polynomial ℚ} (h0 : q.coeff 0 = 0) : q = X * q.divX := by
  conv_lhs => rw [← Polynomial.X_mul_divX_add q, h0]
  simp

theorem pow_coeff_lt {q : Polynomial ℚ} (h0 : q.coeff 0 = 0) (i k : ℕ) (h : k < i) :
    (q ^ i).coeff k = 0 := by
  have hq : q ^ i = X ^ i * (q.divX) ^ i := by
    conv_lhs => rw [eq_X_mul_divX h0]
    rw [mul_pow]
  have hdvd : (X : Polynomial ℚ) ^ i ∣ q ^ i := by rw [hq]; exact Dvd.intro _ rfl
  exact (Polynomial.X_pow_dvd_iff.mp hdvd) k h

theorem pow_coeff_self {q : Polynomial ℚ} (h0 : q.coeff 0 = 0) (h1 : q.coeff 1 = 1) (i : ℕ) :
    (q ^ i).coeff i = 1 := by
  have hq : q ^ i = X ^ i * (q.divX) ^ i := by
    conv_lhs => rw [eq_X_mul_divX h0]
    rw [mul_pow]
  rw [hq]
  have h := Polynomial.coeff_X_pow_mul ((q.divX) ^ i) i 0
  simp only [zero_add] at h
  rw [h, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow,
    ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_divX, h1, one_pow]

theorem Fp_coeff_zero (n : ℕ) : (Fp n).coeff 0 = 0 := by
  simp [Fp, coeff_zero_eq_eval_zero]

theorem Fp_coeff_one (n : ℕ) : (Fp n).coeff 1 = 1 := by
  simp [Fp, coeff_X_mul, coeff_zero_eq_eval_zero]

theorem Fp_pow (n i : ℕ) : (Fp n) ^ i = X ^ i * (1 - X) ^ (n * i) := by
  rw [Fp, mul_pow, ← pow_mul, mul_comm n i]

theorem derivative_Fp (n : ℕ) (hn : 1 ≤ n) :
    derivative (Fp n) = (1 - X) ^ (n - 1) * (1 - C ((n : ℚ) + 1) * X) := by
  unfold Fp
  rw [derivative_mul, derivative_X, derivative_pow]
  have h1 : (1 - X : Polynomial ℚ) ^ n = (1 - X) * (1 - X) ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [h1]
  simp only [derivative_sub, derivative_one, derivative_X, zero_sub, map_add, map_one]
  ring

/-! ### The truncated inverse -/

theorem linv_natDegree (q : Polynomial ℚ) (K : ℕ) : (linv q K).natDegree ≤ K := by
  induction K with
  | zero => simp [linv]
  | succ k ih =>
      rw [linv]
      refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      simp only [max_le_iff]
      refine ⟨le_trans ih (by omega), ?_⟩
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      have h1 : (C ((if k + 1 = 1 then (1 : ℚ) else 0)
          - ((linv q k).comp q).coeff (k + 1))).natDegree = 0 := Polynomial.natDegree_C _
      rw [h1, Polynomial.natDegree_X_pow]
      omega

theorem linv_coeff_stable (q : Polynomial ℚ) (K k : ℕ) (h : k ≤ K) :
    (linv q (K + 1)).coeff k = (linv q K).coeff k := by
  rw [linv, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    if_neg (show k ≠ K + 1 by omega), mul_zero, add_zero]

theorem linv_coeff_stable' (q : Polynomial ℚ) (K L k : ℕ) (h : k ≤ K) (hKL : K ≤ L) :
    (linv q L).coeff k = (linv q K).coeff k := by
  induction L with
  | zero =>
      have : K = 0 := by omega
      rw [this]
  | succ L ih =>
      rcases Nat.lt_or_ge K (L + 1) with h1 | h1
      · rw [linv_coeff_stable q L k (by omega), ih (by omega)]
      · have : K = L + 1 := by omega
        rw [this]

theorem linv_coeff_zero (q : Polynomial ℚ) (K : ℕ) : (linv q K).coeff 0 = 0 := by
  induction K with
  | zero => simp [linv]
  | succ K ih =>
      rw [linv, Polynomial.coeff_add, ih, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp

theorem linv_coeff_one (q : Polynomial ℚ) (K : ℕ) (hK : 1 ≤ K) : (linv q K).coeff 1 = 1 := by
  have h1 : (linv q 1).coeff 1 = 1 := by
    rw [linv]
    simp [linv]
  rw [linv_coeff_stable' q 1 K 1 le_rfl hK, h1]

/-- The left inverse composes to `X` in all degrees `≤ K`. -/
theorem comp_linv_coeff_gen {q : Polynomial ℚ} (h0 : q.coeff 0 = 0) (h1 : q.coeff 1 = 1)
    (K k : ℕ) (hk : k ≤ K) :
    ((linv q K).comp q).coeff k = if k = 1 then 1 else 0 := by
  induction K generalizing k with
  | zero =>
      have : k = 0 := by omega
      subst this
      simp [linv]
  | succ K ih =>
      rw [linv, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
        Polynomial.X_pow_comp, Polynomial.coeff_add, Polynomial.coeff_C_mul]
      rcases Nat.lt_or_ge k (K + 1) with hlt | hge
      · rw [pow_coeff_lt h0 (K + 1) k hlt, mul_zero, add_zero, ih k (by omega)]
      · have hk1 : k = K + 1 := by omega
        subst hk1
        rw [pow_coeff_self h0 h1]
        ring

theorem comp_linv_coeff (n K k : ℕ) (hk : k ≤ K) :
    ((linv (Fp n) K).comp (Fp n)).coeff k = if k = 1 then 1 else 0 :=
  comp_linv_coeff_gen (Fp_coeff_zero n) (Fp_coeff_one n) K k hk

/-! ### The residue computation -/

theorem coeffV (e k : ℕ) :
    PowerSeries.coeff k (Wser (e + 1)) = (((e + k).choose e : ℕ) : ℚ) := by
  rw [Wser, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]; simp

theorem Wmul (d e : ℕ) : ((1 : PowerSeries ℚ) - PowerSeries.X) ^ e * Wser (d + e) = Wser d := by
  rw [Wser, Wser]
  exact PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℚ d e

theorem choose_id (n d : ℕ) (hd : 1 ≤ d) :
    (n * d + d).choose (n * d) = (n + 1) * ((n * d + d - 1).choose (n * d)) := by
  have h := Nat.add_one_mul_choose_eq (n * d + d - 1) (d - 1)
  have e1 : n * d + d - 1 + 1 = n * d + d := by omega
  have e2 : d - 1 + 1 = d := by omega
  rw [e1, e2] at h
  have s1 : (n * d + d).choose (n * d) = (n * d + d).choose d := by
    have := Nat.choose_symm (show d ≤ n * d + d by omega); simpa using this
  have s2 : (n * d + d - 1).choose (n * d) = (n * d + d - 1).choose (d - 1) := by
    have h5 := Nat.choose_symm (show d - 1 ≤ n * d + d - 1 by omega)
    have e3 : n * d + d - 1 - (d - 1) = n * d := by omega
    rw [e3] at h5; exact h5
  rw [s1, s2]
  have hmul : d * ((n + 1) * ((n * d + d - 1).choose (d - 1)))
      = d * ((n * d + d).choose d) := by
    have h4 : d * ((n + 1) * ((n * d + d - 1).choose (d - 1)))
        = (n * d + d) * ((n * d + d - 1).choose (d - 1)) := by ring
    rw [h4, h]; ring
  exact (Nat.eq_of_mul_eq_mul_left (by omega) hmul).symm

/-- The key residue computation: `res (F ^ (i-m-1) F') = δ`. -/
theorem keyres (n m i : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    PowerSeries.coeff (m - 1)
      ((((Fp n) ^ i * derivative (Fp n) : Polynomial ℚ) : PowerSeries ℚ) * Wser (n * m))
      = if i + 1 = m then 1 else 0 := by
  have hpoly : ((Fp n) ^ i * derivative (Fp n) : Polynomial ℚ)
      = X ^ i * ((1 - X) ^ (n * i + (n - 1)) * (1 - C ((n : ℚ) + 1) * X)) := by
    rw [Fp_pow, derivative_Fp n hn, pow_add]; ring
  have hcoe : (((X : Polynomial ℚ) ^ i
        * ((1 - X) ^ (n * i + (n - 1)) * (1 - C ((n : ℚ) + 1) * X)) : Polynomial ℚ)
        : PowerSeries ℚ)
      = PowerSeries.X ^ i * (((1 - PowerSeries.X) ^ (n * i + (n - 1)) : PowerSeries ℚ)
          * (1 - PowerSeries.C ((n : ℚ) + 1) * PowerSeries.X)) := by
    push_cast; simp
  rw [hpoly, hcoe, mul_assoc]
  rcases Nat.lt_or_ge (m - 1) i with hlt | hge
  · have hdvd : PowerSeries.X ^ i ∣ (PowerSeries.X ^ i *
        ((((1 - PowerSeries.X) ^ (n * i + (n - 1)) : PowerSeries ℚ)
          * (1 - PowerSeries.C ((n : ℚ) + 1) * PowerSeries.X)) * Wser (n * m))) := Dvd.intro _ rfl
    rw [PowerSeries.X_pow_dvd_iff.mp hdvd (m - 1) hlt, if_neg (by omega)]
  · obtain ⟨d, hd⟩ : ∃ d, d = m - 1 - i := ⟨_, rfl⟩
    have hmd : m - 1 = d + i := by omega
    have hif : (if i + 1 = m then (1 : ℚ) else 0) = (if d = 0 then (1 : ℚ) else 0) := by
      by_cases h : i + 1 = m
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    rw [hmd, hif, PowerSeries.coeff_X_pow_mul]
    have he : n * m = (n * d + 1) + (n * i + (n - 1)) := by
      have hm' : m = d + i + 1 := by omega
      rw [hm']; cases n with
      | zero => omega
      | succ n' => ring_nf; omega
    have h9 : ((1 - PowerSeries.X) ^ (n * i + (n - 1)) : PowerSeries ℚ) * Wser (n * m)
        = Wser (n * d + 1) := by rw [he, Wmul]
    have hrearr : (((1 - PowerSeries.X) ^ (n * i + (n - 1)) : PowerSeries ℚ)
          * (1 - PowerSeries.C ((n : ℚ) + 1) * PowerSeries.X)) * Wser (n * m)
        = Wser (n * d + 1) * (1 - PowerSeries.C ((n : ℚ) + 1) * PowerSeries.X) := by
      rw [mul_right_comm, h9]
    rw [hrearr, mul_sub, mul_one, map_sub]
    clear hrearr h9 he hif hmd hd hcoe hpoly
    cases d with
    | zero =>
        rw [if_pos rfl]
        simp only [Nat.mul_zero]
        rw [show Wser (0 + 1) * (PowerSeries.C ((n : ℚ) + 1) * PowerSeries.X)
              = PowerSeries.C ((n : ℚ) + 1) * (Wser (0 + 1) * PowerSeries.X) by ring]
        rw [PowerSeries.coeff_C_mul]
        have hz : PowerSeries.coeff 0 (Wser (0 + 1) * PowerSeries.X) = 0 := by
          simp [PowerSeries.coeff_zero_eq_constantCoeff]
        rw [hz]
        have h0 : PowerSeries.coeff 0 (Wser (0 + 1)) = 1 := by
          rw [coeffV 0 0]; simp
        rw [h0]; ring
    | succ d' =>
        rw [if_neg (Nat.succ_ne_zero d')]
        rw [show Wser (n * (d' + 1) + 1) * (PowerSeries.C ((n : ℚ) + 1) * PowerSeries.X)
              = PowerSeries.C ((n : ℚ) + 1) * (Wser (n * (d' + 1) + 1) * PowerSeries.X) by ring]
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X, coeffV, coeffV]
        have hch := choose_id n (d' + 1) (by omega)
        have e4 : n * (d' + 1) + (d' + 1) - 1 = n * (d' + 1) + d' := by omega
        rw [e4] at hch
        rw [hch]
        push_cast
        ring

/-- **Lagrange inversion**: the coefficients of the compositional inverse. -/
theorem linv_coeff_eq (n K m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hK : m + 2 ≤ K) :
    (m : ℚ) * (linv (Fp n) K).coeff m = (((n + 1) * m - 2).choose (m - 1) : ℚ) := by
  set p := linv (Fp n) K with hp
  set F := Fp n with hF
  have hnm1 : 1 ≤ n * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hdvd1 : (X : Polynomial ℚ) ^ (K + 1) ∣ (p.comp F - X) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, comp_linv_coeff n K d (by omega), Polynomial.coeff_X]
    by_cases h : d = 1
    · simp [h]
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  have hdvd2 : (X : Polynomial ℚ) ^ K ∣ (derivative F * (derivative p).comp F - 1) := by
    have hderiv : derivative (p.comp F - X) = derivative F * (derivative p).comp F - 1 := by
      rw [derivative_sub, Polynomial.derivative_comp, derivative_X]
    obtain ⟨h1, hh⟩ := hdvd1
    have hx : derivative (p.comp F - X) = X ^ K * (C ((K : ℚ) + 1) * h1 + X * derivative h1) := by
      rw [hh, derivative_mul, derivative_X_pow]
      push_cast
      ring_nf
    rw [hderiv] at hx
    exact ⟨_, hx⟩
  have hps : PowerSeries.coeff (m - 1)
      ((↑(derivative F * (derivative p).comp F) : PowerSeries ℚ) * Wser (n * m))
      = PowerSeries.coeff (m - 1) (Wser (n * m)) := by
    obtain ⟨h2, hh2⟩ := hdvd2
    have hcoe : (↑(derivative F * (derivative p).comp F) : PowerSeries ℚ)
        = 1 + PowerSeries.X ^ K * (h2 : PowerSeries ℚ) := by
      have h3 := congrArg (fun t : Polynomial ℚ => (t : PowerSeries ℚ)) hh2
      simp only [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul,
        Polynomial.coe_pow, Polynomial.coe_X] at h3
      rw [Polynomial.coe_mul]
      linear_combination h3
    rw [hcoe, add_mul, one_mul, map_add]
    have hzero : PowerSeries.coeff (m - 1)
        (PowerSeries.X ^ K * (h2 : PowerSeries ℚ) * Wser (n * m)) = 0 := by
      have hdvd : PowerSeries.X ^ K ∣ (PowerSeries.X ^ K * (h2 : PowerSeries ℚ) * Wser (n * m)) :=
        ⟨(h2 : PowerSeries ℚ) * Wser (n * m), by ring⟩
      exact PowerSeries.X_pow_dvd_iff.mp hdvd (m - 1) (by omega)
    rw [hzero, add_zero]
  have hRHS : PowerSeries.coeff (m - 1) (Wser (n * m))
      = (((n + 1) * m - 2).choose (m - 1) : ℚ) := by
    have hnm : n * m = (n * m - 1) + 1 := by omega
    rw [hnm, coeffV]
    congr 1
    have hexp : (n + 1) * m = n * m + m := by ring
    rw [show n * m - 1 + (m - 1) = (n + 1) * m - 2 by omega]
    have hsymm := Nat.choose_symm (show m - 1 ≤ (n + 1) * m - 2 by omega)
    rw [show (n + 1) * m - 2 - (m - 1) = n * m - 1 by omega] at hsymm
    exact hsymm
  have hexpand : (derivative p).comp F = ∑ j ∈ range (K + 1), C (p.coeff j * j) * F ^ (j - 1) := by
    have hdeg : p.natDegree < K + 1 := lt_of_le_of_lt (linv_natDegree _ _) (by omega)
    have hp2 : derivative p
        = ∑ j ∈ range (K + 1), (Polynomial.monomial (j - 1)) (p.coeff j * j) := by
      conv_lhs => rw [Polynomial.as_sum_range' p (K + 1) hdeg]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => Polynomial.derivative_monomial _ _
    rw [hp2, Polynomial.sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_pow_comp]
  have hLHS : PowerSeries.coeff (m - 1)
      ((↑(derivative F * (derivative p).comp F) : PowerSeries ℚ) * Wser (n * m))
      = (m : ℚ) * p.coeff m := by
    rw [hexpand]
    have hsum : (derivative F * ∑ j ∈ range (K + 1), C (p.coeff j * j) * F ^ (j - 1) :
        Polynomial ℚ) = ∑ j ∈ range (K + 1), C (p.coeff j * j) * (F ^ (j - 1) * derivative F) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum, coe_sum_range, Finset.sum_mul, map_sum]
    have hterm : ∀ j ∈ range (K + 1),
        PowerSeries.coeff (m - 1)
            ((↑(C (p.coeff j * j) * (F ^ (j - 1) * derivative F)) : PowerSeries ℚ) * Wser (n * m))
          = (p.coeff j * j) * (if (j - 1) + 1 = m then 1 else 0) := by
      intro j _
      rw [Polynomial.coe_mul, Polynomial.coe_C, mul_assoc, PowerSeries.coeff_C_mul, hF,
        keyres n m (j - 1) hn hm]
    rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single m]
    · rw [if_pos (by omega)]; ring
    · intro j _ hjm
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0; simp
      · rw [if_neg (by omega)]; ring
    · intro hmr
      exact absurd (Finset.mem_range.mpr (by omega)) hmr
  rw [← hLHS, hps, hRHS]

/-! ### The inverse is two-sided -/

theorem comp_sub_dvd (g a b : Polynomial ℚ) : (a - b) ∣ (g.comp a - g.comp b) := by
  have h := Polynomial.sub_dvd_eval_sub a b (g.map C)
  rwa [Polynomial.eval_map, Polynomial.eval_map, ← Polynomial.comp, ← Polynomial.comp] at h

theorem dvd_comp_of_dvd {N : ℕ} {a b c : Polynomial ℚ} (hc : c.coeff 0 = 0)
    (h : (X : Polynomial ℚ) ^ N ∣ (a - b)) : (X : Polynomial ℚ) ^ N ∣ (a.comp c - b.comp c) := by
  obtain ⟨h1, hh⟩ := h
  have hsub : a.comp c - b.comp c = (a - b).comp c := by rw [Polynomial.sub_comp]
  rw [hsub, hh, Polynomial.mul_comp, Polynomial.X_pow_comp]
  have : (X : Polynomial ℚ) ^ N ∣ c ^ N := by
    rw [eq_X_mul_divX hc, mul_pow]
    exact Dvd.intro _ rfl
  exact Dvd.dvd.mul_right this _

/-- The compositional inverse is a two-sided inverse. -/
theorem Fp_comp_linv_coeff (n K k : ℕ) (hk : k ≤ K) (hK : 1 ≤ K) :
    ((Fp n).comp (linv (Fp n) K)).coeff k = if k = 1 then 1 else 0 := by
  set q := Fp n with hq
  set p := linv q K with hp
  set g := linv p K with hg
  have hp0 : p.coeff 0 = 0 := linv_coeff_zero q K
  have hp1 : p.coeff 1 = 1 := linv_coeff_one q K hK
  have hq0 : q.coeff 0 = 0 := Fp_coeff_zero n
  have hpq : (X : Polynomial ℚ) ^ (K + 1) ∣ (p.comp q - X) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, comp_linv_coeff n K d (by omega), Polynomial.coeff_X]
    by_cases h : d = 1
    · simp [h]
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  have hgp : (X : Polynomial ℚ) ^ (K + 1) ∣ (g.comp p - X) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, comp_linv_coeff_gen hp0 hp1 K d (by omega), Polynomial.coeff_X]
    by_cases h : d = 1
    · simp [h]
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  -- `g ≡ q`
  have h1 : (X : Polynomial ℚ) ^ (K + 1) ∣ (g.comp (p.comp q) - g) := by
    have := dvd_trans hpq (comp_sub_dvd g (p.comp q) X)
    rwa [Polynomial.comp_X] at this
  have h2 : (X : Polynomial ℚ) ^ (K + 1) ∣ ((g.comp p).comp q - q) := by
    have := dvd_comp_of_dvd (N := K + 1) (a := g.comp p) (b := X) hq0 hgp
    rwa [Polynomial.X_comp] at this
  have h3 : (X : Polynomial ℚ) ^ (K + 1) ∣ (g - q) := by
    have heq : g - q = (g.comp (p.comp q) - g) * (-1) + ((g.comp p).comp q - q) := by
      rw [Polynomial.comp_assoc]
      ring
    rw [heq]
    exact dvd_add (Dvd.dvd.mul_right h1 _) h2
  have h4 : (X : Polynomial ℚ) ^ (K + 1) ∣ (g.comp p - q.comp p) := dvd_comp_of_dvd hp0 h3
  have h5 : (X : Polynomial ℚ) ^ (K + 1) ∣ (X - q.comp p) := by
    have heq : (X : Polynomial ℚ) - q.comp p = (g.comp p - q.comp p) - (g.comp p - X) := by ring
    rw [heq]
    exact dvd_sub h4 hgp
  have h6 := Polynomial.X_pow_dvd_iff.mp h5 k (by omega)
  rw [Polynomial.coeff_sub, Polynomial.coeff_X] at h6
  by_cases h : k = 1
  · rw [if_pos h]
    rw [if_pos (Eq.symm h)] at h6
    linarith [h6]
  · rw [if_neg h]
    rw [if_neg (fun hh => h hh.symm)] at h6
    linarith [h6]

/-! ### Bridge to the analytic part -/

theorem convPow_eq (P : Polynomial ℚ) (f : ℕ → ℝ) (k : ℕ)
    (hf : ∀ i ≤ k, f i = ((P.coeff i : ℚ) : ℝ)) (r : ℕ) :
    ∀ i ≤ k, convPow f r i = (((P ^ r).coeff i : ℚ) : ℝ) := by
  induction r with
  | zero =>
      intro i _
      simp only [convPow, pow_zero, Polynomial.coeff_one]
      by_cases h : i = 0 <;> simp [h]
  | succ r ih =>
      intro i hi
      show conv (convPow f r) f i = _
      unfold conv
      rw [pow_succ, Polynomial.coeff_mul]
      push_cast
      refine Finset.sum_congr rfl ?_
      intro pr hpr
      have hmem := Finset.mem_antidiagonal.mp hpr
      rw [ih pr.1 (by omega), hf pr.2 (by omega)]

/-- The formal identity satisfied by the coefficients `cc n`. -/
theorem key_coeff (n k : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ range (n + 1), ((-1 : ℝ) ^ j * (n.choose j : ℝ)) * convPow (cc n) (j + 1) k
      = if k = 1 then 1 else 0 := by
  set K := k + 2 with hK
  set P := linv (Fp n) K with hP
  have hcoeff : ∀ i ≤ k, cc n i = ((P.coeff i : ℚ) : ℝ) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      rw [cc_zero, linv_coeff_zero]
      norm_num
    · have h := linv_coeff_eq n K i hn h0 (by omega)
      have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hPi : P.coeff i = (((n + 1) * i - 2).choose (i - 1) : ℚ) / i := by
        field_simp
        linarith [h]
      rw [hPi, cc]
      push_cast
      ring
  have hconv : ∀ r, convPow (cc n) r k = (((P ^ r).coeff k : ℚ) : ℝ) :=
    fun r => convPow_eq P (cc n) k hcoeff r k le_rfl
  have hexpand : ((Fp n).comp P) = ∑ j ∈ range (n + 1), C ((-1 : ℚ) ^ j * (n.choose j : ℚ))
      * P ^ (j + 1) := by
    have h1 : (Fp n).comp P = P * (1 - P) ^ n := by
      simp [Fp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp]
    rw [h1, one_sub_pow_expand]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, map_pow, map_neg, map_one, Polynomial.C_eq_natCast]
  have hval := Fp_comp_linv_coeff n K k (by omega) (by omega)
  rw [hexpand] at hval
  have hcoeffsum : ((∑ j ∈ range (n + 1), C ((-1 : ℚ) ^ j * (n.choose j : ℚ))
      * P ^ (j + 1)).coeff k)
      = ∑ j ∈ range (n + 1), ((-1 : ℚ) ^ j * (n.choose j : ℚ)) * ((P ^ (j + 1)).coeff k) := by
    rw [Polynomial.finset_sum_coeff]
    exact Finset.sum_congr rfl fun j _ => by rw [Polynomial.coeff_C_mul]
  rw [hcoeffsum] at hval
  have := congrArg (fun t : ℚ => (t : ℝ)) hval
  push_cast at this
  have hcast : ((if k = 1 then (1 : ℚ) else 0 : ℚ) : ℝ) = if k = 1 then (1 : ℝ) else 0 := by
    split <;> norm_num
  rw [hcast] at this
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hconv (j + 1)]

end Q865


/-!
# Q865 : elementary bounds on the coefficients `cc n m`

We prove the entropy bound `cc n m ≤ ((n+1)^(n+1) / n^n)^m` and the arithmetic inequality
`(n+1)^(n+1) < 2^(n+1) * n^n` (for `n ≥ 2`), which together give the summability of the
series `∑ cc n m u^m` for `0 ≤ u ≤ uu n`.
-/

namespace Q865

open Finset

/-- The elementary "entropy" bound `a^a * b^b * C(a+b, a) ≤ (a+b)^(a+b)`. -/
theorem choose_mul_pow_le (a b : ℕ) : a ^ a * b ^ b * (a + b).choose a ≤ (a + b) ^ (a + b) := by
  rw [add_pow a b (a + b)]
  have hmem : a ∈ range (a + b + 1) := by simp
  have := Finset.single_le_sum (f := fun k => a ^ k * b ^ (a + b - k) * (a + b).choose k)
    (fun i _ => Nat.zero_le _) hmem
  simpa using this

/-- `(n+1)^(n+1) < 2^(n+1) * n^n` for `n ≥ 2`. -/
theorem nat_pow_ineq (n : ℕ) (hn : 2 ≤ n) : (n + 1) ^ (n + 1) < 2 ^ (n + 1) * n ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hstar : n ^ n * (n + 2) ^ (n + 2) ≤ 2 * (n + 1) ^ (2 * n + 2) := by
        have h1 : (n * (n + 2)) ^ (n + 1) ≤ ((n + 1) ^ 2) ^ (n + 1) :=
          Nat.pow_le_pow_left (by nlinarith) _
        have h2 : ((n + 1) ^ 2) ^ (n + 1) = (n + 1) ^ (2 * n + 2) := by
          rw [← pow_mul]; ring_nf
        have h3 : (n * (n + 2)) ^ (n + 1) = n ^ (n + 1) * (n + 2) ^ (n + 1) := mul_pow _ _ _
        have h4 : n ^ n * (n + 2) ^ (n + 2) ≤ 2 * (n ^ (n + 1) * (n + 2) ^ (n + 1)) := by
          have e1 : n ^ (n + 1) * (n + 2) ^ (n + 1) = n * (n ^ n * (n + 2) ^ (n + 1)) := by ring
          rw [e1, pow_succ (n + 2) (n + 1)]
          have e2 : n ^ n * ((n + 2) ^ (n + 1) * (n + 2))
              = (n ^ n * (n + 2) ^ (n + 1)) * (n + 2) := by ring
          rw [e2]
          calc (n ^ n * (n + 2) ^ (n + 1)) * (n + 2)
              ≤ (n ^ n * (n + 2) ^ (n + 1)) * (2 * n) := Nat.mul_le_mul_left _ (by omega)
            _ = 2 * (n * (n ^ n * (n + 2) ^ (n + 1))) := by ring
        calc n ^ n * (n + 2) ^ (n + 2) ≤ 2 * (n ^ (n + 1) * (n + 2) ^ (n + 1)) := h4
          _ = 2 * (n * (n + 2)) ^ (n + 1) := by rw [h3]
          _ ≤ 2 * ((n + 1) ^ 2) ^ (n + 1) := Nat.mul_le_mul_left _ h1
          _ = 2 * (n + 1) ^ (2 * n + 2) := by rw [h2]
      have hmul : (n + 1) ^ (2 * n + 2) < 2 ^ (n + 1) * (n ^ n * (n + 1) ^ (n + 1)) := by
        have h5 := Nat.mul_lt_mul_of_lt_of_le ih (le_refl ((n + 1) ^ (n + 1))) (by positivity)
        calc (n + 1) ^ (2 * n + 2) = (n + 1) ^ (n + 1) * (n + 1) ^ (n + 1) := by
              rw [← pow_add]; ring_nf
          _ < (2 ^ (n + 1) * n ^ n) * (n + 1) ^ (n + 1) := h5
          _ = 2 ^ (n + 1) * (n ^ n * (n + 1) ^ (n + 1)) := by ring
      have hfin : n ^ n * (n + 2) ^ (n + 2) < n ^ n * (2 ^ (n + 2) * (n + 1) ^ (n + 1)) := by
        calc n ^ n * (n + 2) ^ (n + 2) ≤ 2 * (n + 1) ^ (2 * n + 2) := hstar
          _ < 2 * (2 ^ (n + 1) * (n ^ n * (n + 1) ^ (n + 1))) := by omega
          _ = n ^ n * (2 ^ (n + 2) * (n + 1) ^ (n + 1)) := by ring
      have := Nat.lt_of_mul_lt_mul_left hfin
      convert this using 2

theorem uu_lt_R (n : ℕ) (hn : 2 ≤ n) : uu n < (n : ℝ) ^ n / ((n : ℝ) + 1) ^ (n + 1) := by
  have hR : (((n : ℝ) + 1)) ^ (n + 1) < 2 ^ (n + 1) * (n : ℝ) ^ n := by
    have := (Nat.cast_lt (α := ℝ)).mpr (nat_pow_ineq n hn)
    push_cast at this
    exact this
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hden : (0 : ℝ) < ((n : ℝ) + 1) ^ (n + 1) := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
  rw [uu, inv_pow, lt_div_iff₀ hden, inv_mul_eq_div, div_lt_iff₀ h2]
  calc ((n : ℝ) + 1) ^ (n + 1) < 2 ^ (n + 1) * (n : ℝ) ^ n := hR
    _ = (n : ℝ) ^ n * 2 ^ (n + 1) := by ring

/-- Crude entropy bound on the coefficients. -/
theorem cc_le_geom (n m : ℕ) (hn : 1 ≤ n) :
    cc n m ≤ ((((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n)) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [cc]
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hchoose : ((n + 1) * m - 2).choose (m - 1) ≤ (m + n * m).choose m := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hpos : 1 ≤ (n + 1) * (k + 1) := by nlinarith
    obtain ⟨N, hN⟩ : ∃ N, (n + 1) * (k + 1) = N + 1 := ⟨(n + 1) * (k + 1) - 1, by omega⟩
    have hNsum : (k + 1) + n * (k + 1) = N + 1 := by rw [← hN]; ring
    simp only [Nat.add_sub_cancel, hNsum]
    have h1 : ((n + 1) * (k + 1) - 2).choose k ≤ N.choose k :=
      Nat.choose_le_choose _ (by omega)
    have h2 : N.choose k ≤ (N + 1).choose (k + 1) := by
      rw [Nat.choose_succ_succ]; omega
    exact le_trans h1 h2
  have hentR : (m : ℝ) ^ m * ((n : ℝ) * m) ^ (n * m) * (((m + n * m).choose m : ℕ) : ℝ)
      ≤ ((m : ℝ) + n * m) ^ (m + n * m) := by
    have := (Nat.cast_le (α := ℝ)).mpr (choose_mul_pow_le m (n * m))
    push_cast at this
    exact this
  have hD : (0 : ℝ) < (m : ℝ) ^ m * ((n : ℝ) * m) ^ (n * m) := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hEq : ((m : ℝ) + n * m) ^ (m + n * m)
      = (((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n) ^ m
        * ((m : ℝ) ^ m * ((n : ℝ) * m) ^ (n * m)) := by
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have he : m + n * m = (n + 1) * m := by ring
    have hb : ((m : ℝ) + n * m) = ((n : ℝ) + 1) * m := by ring
    have hm2 : (m : ℝ) ^ ((n + 1) * m) = (m : ℝ) ^ m * (m : ℝ) ^ (n * m) := by
      rw [← pow_add]; congr 1; ring
    rw [he, hb, mul_pow, mul_pow, div_pow, ← pow_mul, ← pow_mul, hm2]
    field_simp
  rw [hEq] at hentR
  have hfin : (((m + n * m).choose m : ℕ) : ℝ)
      ≤ (((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n) ^ m :=
    le_of_mul_le_mul_right (by linarith) hD
  have hnn : (0 : ℝ) ≤ ((((n + 1) * m - 2).choose (m - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  calc cc n m = ((((n + 1) * m - 2).choose (m - 1) : ℕ) : ℝ) / m := rfl
    _ ≤ ((((n + 1) * m - 2).choose (m - 1) : ℕ) : ℝ) := by
        rw [div_le_iff₀ hm0]; nlinarith
    _ ≤ (((m + n * m).choose m : ℕ) : ℝ) := by exact_mod_cast hchoose
    _ ≤ _ := hfin

theorem summable_ccu (n : ℕ) (hn : 2 ≤ n) {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ uu n) :
    Summable (fun m : ℕ => cc n m * u ^ m) := by
  set A : ℝ := ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n with hA
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hApos : 0 < A := by rw [hA]; positivity
  have hq : A * uu n < 1 := by
    have h := uu_lt_R n hn
    rw [hA, mul_comm, ← lt_div_iff₀ hApos]
    simpa [hA, div_div_eq_mul_div, one_div] using h
  have hq0 : 0 ≤ A * uu n := by
    have : 0 < uu n := uu_pos n
    positivity
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (cc_nonneg n m) (by positivity)) ?_
    (summable_geometric_of_lt_one hq0 hq)
  intro m
  calc cc n m * u ^ m ≤ A ^ m * (uu n) ^ m := by
        exact mul_le_mul (cc_le_geom n m (by omega)) (pow_le_pow_left₀ hu0 hu m) (by positivity)
          (by positivity)
    _ = (A * uu n) ^ m := (mul_pow _ _ _).symm

end Q865


/-!
# Q865 : the analytic part — the sum of the inverse series

`Sser n u = ∑' m, cc n m * u ^ m`.  We show that on `[0, uu n]` this series converges,
is continuous, satisfies the functional equation `S * (1 - S) ^ n = u`, and stays on the
small branch (`S < 1 / (n+1)`).
-/

namespace Q865

open Finset

/-- The sum of the inverse series. -/
noncomputable def Sser (n : ℕ) (u : ℝ) : ℝ := ∑' m : ℕ, cc n m * u ^ m

theorem convPow_nonneg (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (r m : ℕ) : 0 ≤ convPow f r m := by
  induction r generalizing m with
  | zero => unfold convPow; split <;> norm_num
  | succ r ih =>
      show 0 ≤ conv (convPow f r) f m
      unfold conv
      exact Finset.sum_nonneg fun p _ => mul_nonneg (ih p.1) (hf p.2)

theorem conv_pow_eq (a b : ℕ → ℝ) (u : ℝ) (k : ℕ) :
    ∑ p ∈ Finset.antidiagonal k, (a p.1 * u ^ p.1) * (b p.2 * u ^ p.2) = conv a b k * u ^ k := by
  unfold conv
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hk := Finset.mem_antidiagonal.mp hp
  subst hk
  rw [pow_add]
  ring

theorem conv_summable {a b : ℕ → ℝ} {u : ℝ} (hu : 0 ≤ u)
    (ha0 : ∀ k, 0 ≤ a k) (hb0 : ∀ k, 0 ≤ b k)
    (ha : Summable (fun k => a k * u ^ k)) (hb : Summable (fun k => b k * u ^ k)) :
    Summable (fun k => conv a b k * u ^ k) := by
  have h := summable_sum_mul_antidiagonal_of_summable_mul
    (Summable.mul_of_nonneg ha hb (fun k => mul_nonneg (ha0 k) (pow_nonneg hu k))
      (fun k => mul_nonneg (hb0 k) (pow_nonneg hu k)))
  exact h.congr fun k => conv_pow_eq a b u k

theorem conv_tsum {a b : ℕ → ℝ} {u : ℝ} (hu : 0 ≤ u)
    (ha0 : ∀ k, 0 ≤ a k) (hb0 : ∀ k, 0 ≤ b k)
    (ha : Summable (fun k => a k * u ^ k)) (hb : Summable (fun k => b k * u ^ k)) :
    (∑' k, a k * u ^ k) * (∑' k, b k * u ^ k) = ∑' k, conv a b k * u ^ k := by
  have hna : Summable (fun k => ‖a k * u ^ k‖) :=
    ha.congr fun k => (Real.norm_of_nonneg (mul_nonneg (ha0 k) (pow_nonneg hu k))).symm
  have hnb : Summable (fun k => ‖b k * u ^ k‖) :=
    hb.congr fun k => (Real.norm_of_nonneg (mul_nonneg (hb0 k) (pow_nonneg hu k))).symm
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hna hnb]
  exact tsum_congr fun k => conv_pow_eq a b u k

theorem summable_convPow (n : ℕ) (hn : 2 ≤ n) {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ uu n) (r : ℕ) :
    Summable (fun k : ℕ => convPow (cc n) r k * u ^ k) := by
  induction r with
  | zero =>
      refine summable_of_ne_finset_zero (s := {0}) ?_
      intro k hk
      simp only [Finset.mem_singleton] at hk
      show (if k = 0 then (1 : ℝ) else 0) * u ^ k = 0
      rw [if_neg hk, zero_mul]
  | succ r ih =>
      exact conv_summable hu0 (convPow_nonneg _ (cc_nonneg n) r) (cc_nonneg n) ih
        (summable_ccu n hn hu0 hu)

/-- Powers of the sum are given by the convolution powers of the coefficients. -/
theorem Sser_pow (n : ℕ) (hn : 2 ≤ n) {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ uu n) (r : ℕ) :
    Sser n u ^ r = ∑' k : ℕ, convPow (cc n) r k * u ^ k := by
  induction r with
  | zero =>
      rw [pow_zero]
      have : ∀ k : ℕ, convPow (cc n) 0 k * u ^ k = if k = 0 then (1 : ℝ) else 0 := by
        intro k
        show (if k = 0 then (1 : ℝ) else 0) * u ^ k = _
        by_cases h : k = 0 <;> simp [h]
      rw [tsum_congr this, tsum_ite_eq]
  | succ r ih =>
      rw [pow_succ, ih, Sser]
      exact conv_tsum hu0 (convPow_nonneg _ (cc_nonneg n) r) (cc_nonneg n)
        (summable_convPow n hn hu0 hu r) (summable_ccu n hn hu0 hu)

theorem Sser_zero (n : ℕ) : Sser n 0 = 0 := by
  rw [Sser]
  have h : ∀ m : ℕ, cc n m * (0 : ℝ) ^ m = 0 := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [zero_pow (by omega), mul_zero]
  simp [h]

theorem Sser_nonneg (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) : 0 ≤ Sser n u :=
  tsum_nonneg fun m => mul_nonneg (cc_nonneg n m) (pow_nonneg hu0 m)

theorem Sser_continuousOn (n : ℕ) (hn : 2 ≤ n) :
    ContinuousOn (Sser n) (Set.Icc 0 (uu n)) := by
  have hM : Summable (fun m : ℕ => cc n m * (uu n) ^ m) :=
    summable_ccu n hn (uu_pos n).le le_rfl
  have hbd : ∀ (m : ℕ), ∀ x ∈ Set.Icc (0 : ℝ) (uu n),
      ‖cc n m * x ^ m‖ ≤ cc n m * (uu n) ^ m := by
    intro m x hx
    rw [Real.norm_of_nonneg (mul_nonneg (cc_nonneg n m) (pow_nonneg hx.1 m))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hx.2 m) (cc_nonneg n m)
  have huni := tendstoUniformlyOn_tsum hM hbd
  refine huni.continuousOn (Filter.Eventually.frequently ?_)
  filter_upwards with t
  exact continuousOn_finset_sum _ fun m _ =>
    (continuous_const.mul (continuous_pow m)).continuousOn

/-- The functional equation `S (1 - S) ^ n = u`. -/
theorem Sser_funeq (n : ℕ) (hn : 2 ≤ n) {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ uu n) :
    Sser n u * (1 - Sser n u) ^ n = u := by
  rw [one_sub_pow_expand]
  have hterm : ∀ j ∈ range (n + 1),
      ((-1 : ℝ) ^ j * (n.choose j : ℝ)) * Sser n u ^ (j + 1)
        = ∑' k : ℕ, ((-1 : ℝ) ^ j * (n.choose j : ℝ)) * (convPow (cc n) (j + 1) k * u ^ k) := by
    intro j _
    rw [Sser_pow n hn hu0 hu (j + 1), ← tsum_mul_left]
  rw [Finset.sum_congr rfl hterm]
  rw [← Summable.tsum_finsetSum (fun j _ => ((summable_convPow n hn hu0 hu (j + 1)).mul_left _))]
  have hinner : ∀ k : ℕ,
      (∑ j ∈ range (n + 1), ((-1 : ℝ) ^ j * (n.choose j : ℝ)) * (convPow (cc n) (j + 1) k * u ^ k))
        = (if k = 1 then (1 : ℝ) else 0) * u ^ k := by
    intro k
    have := key_coeff n k (by omega)
    calc (∑ j ∈ range (n + 1),
            ((-1 : ℝ) ^ j * (n.choose j : ℝ)) * (convPow (cc n) (j + 1) k * u ^ k))
        = (∑ j ∈ range (n + 1),
            ((-1 : ℝ) ^ j * (n.choose j : ℝ)) * convPow (cc n) (j + 1) k) * u ^ k := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = (if k = 1 then (1 : ℝ) else 0) * u ^ k := by rw [this]
  rw [tsum_congr hinner]
  rw [tsum_eq_single 1]
  · simp
  · intro b hb
    rw [if_neg hb, zero_mul]

/-- The sum stays on the small branch. -/
theorem Sser_lt (n : ℕ) (hn : 2 ≤ n) : Sser n (uu n) < 1 / ((n : ℝ) + 1) := by
  by_contra hcon
  push_neg at hcon
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcont := Sser_continuousOn n hn
  have hmem : (1 : ℝ) / ((n : ℝ) + 1) ∈ Set.Icc (Sser n 0) (Sser n (uu n)) := by
    refine ⟨?_, hcon⟩
    rw [Sser_zero]
    positivity
  have hIVT := intermediate_value_Icc (uu_pos n).le hcont
  obtain ⟨u₁, hu₁mem, hu₁⟩ := hIVT hmem
  have hfe := Sser_funeq n hn hu₁mem.1 hu₁mem.2
  rw [hu₁] at hfe
  have hval : (1 : ℝ) / ((n : ℝ) + 1) * (1 - 1 / ((n : ℝ) + 1)) ^ n
      = (n : ℝ) ^ n / ((n : ℝ) + 1) ^ (n + 1) := by
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h1 : (1 : ℝ) - 1 / ((n : ℝ) + 1) = (n : ℝ) / ((n : ℝ) + 1) := by
      field_simp
      ring
    rw [h1, div_pow]
    field_simp
    ring
  rw [hval] at hfe
  have := uu_lt_R n hn
  linarith [hu₁mem.2, hfe]

/-- Part (a), binomial form. -/
theorem Acoef_eval_choose (k n : ℕ) (hn : 1 ≤ n) :
    (Acoef k).eval (n : ℚ) = (((k + 1) * (n + 1) - 2).choose k : ℚ) / (k + 1) := by
  have hprodnat : ∏ i ∈ range k, ((k + 1) * (n + 1) - 2 - i)
      = ∏ j ∈ range k, ((k + 1) * n + j) := by
    rw [← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl ?_
    intro i hi
    simp only [Finset.mem_range] at hi
    have : (k + 1) * (n + 1) - 2 = (k + 1) * n + (k - 1) := by
      cases k with
      | zero => simp; omega
      | succ k' => ring_nf; omega
    omega
  have hdesc : ((k + 1) * (n + 1) - 2).descFactorial k = ∏ j ∈ range k, ((k + 1) * n + j) := by
    rw [Nat.descFactorial_eq_prod_range, hprodnat]
  have hkey : (Nat.factorial k : ℚ) * (((k + 1) * (n + 1) - 2).choose k : ℚ)
      = ∏ j ∈ range k, (((k : ℚ) + 1) * n + j) := by
    have h1 := Nat.descFactorial_eq_factorial_mul_choose ((k + 1) * (n + 1) - 2) k
    rw [hdesc] at h1
    have h2 := congrArg (fun t : ℕ => (t : ℚ)) h1
    push_cast at h2
    rw [← h2]
  unfold Acoef
  simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_add]
  rw [← hkey, Nat.factorial_succ]
  push_cast
  field_simp

/-- Part (a): the coefficients of the series are the values of the polynomials `A k`. -/
theorem Acoef_eval_eq (k n : ℕ) (hn : 1 ≤ n) :
    Aval k n = cc n (k + 1) := by
  unfold Aval cc
  rw [Acoef_eval_choose k n hn]
  push_cast
  rw [Nat.mul_comm (k + 1) (n + 1)]

end Q865


/-!
# Q865 : construction of a small root by a contraction argument

For `m` large we construct a complex root of `P m` very close to `-1`, by finding a fixed
point of the map `T w = exp ((i a - log (2 + w)) / m)` (with `a = π` for `m` odd and `a = 0`
for `m` even) on the closed ball of centre `1` and radius `1/2`.  If `w` is such a fixed
point then `w ^ m * (2 + w) = (-1) ^ m`, so `z = -w` satisfies `z ^ m * (2 - z) = 1`, i.e.
`z` is a root of `P m`.
-/

namespace Q865

open Complex

/-- The phase: `π` for `m` odd, `0` for `m` even. -/
noncomputable def phase (m : ℕ) : ℝ := if m % 2 = 1 then Real.pi else 0

/-- The exponent of the contraction. -/
noncomputable def zeta (m : ℕ) (w : ℂ) : ℂ :=
  (Complex.I * (phase m : ℂ) - Complex.log (2 + w)) / (m : ℂ)

/-- The contraction whose fixed point produces a small root. -/
noncomputable def Tmap (m : ℕ) (w : ℂ) : ℂ := Complex.exp (zeta m w)

theorem two_add_bounds {w : ℂ} (hw : ‖w - 1‖ ≤ 1 / 2) :
    (5 : ℝ) / 2 ≤ ‖2 + w‖ ∧ ‖2 + w‖ ≤ 7 / 2 ∧ (2 + w) ∈ Complex.slitPlane := by
  have h1 : (2 : ℂ) + w = 3 + (w - 1) := by ring
  have hre : |(w - 1).re| ≤ ‖w - 1‖ := Complex.abs_re_le_norm _
  have hre' : |w.re - 1| ≤ 1 / 2 := by
    have h2 : (w - 1).re = w.re - 1 := by simp
    rw [h2] at hre; linarith
  have habs := abs_le.mp hre'
  have hn3 : ‖(3 : ℂ)‖ = 3 := by simp
  refine ⟨?_, ?_, ?_⟩
  · have key : ‖(3 : ℂ)‖ ≤ ‖(3 : ℂ) + (w - 1)‖ + ‖w - 1‖ := by
      have h3 : (3 : ℂ) = ((3 : ℂ) + (w - 1)) - (w - 1) := by ring
      calc ‖(3 : ℂ)‖ = ‖((3 : ℂ) + (w - 1)) - (w - 1)‖ := by rw [← h3]
        _ ≤ ‖(3 : ℂ) + (w - 1)‖ + ‖w - 1‖ := norm_sub_le _ _
    rw [h1, hn3] at *
    linarith
  · rw [h1]
    calc ‖(3 : ℂ) + (w - 1)‖ ≤ ‖(3 : ℂ)‖ + ‖w - 1‖ := norm_add_le _ _
      _ ≤ 7 / 2 := by rw [hn3]; linarith
  · rw [Complex.mem_slitPlane_iff]
    left
    have h4 : ((2 : ℂ) + w).re = 2 + w.re := by simp
    rw [h4]
    linarith

theorem norm_log_le_five {z : ℂ} (h1 : (5 : ℝ) / 2 ≤ ‖z‖) (h2 : ‖z‖ ≤ 7 / 2) :
    ‖Complex.log z‖ ≤ 5 := by
  rw [Complex.log]
  have hb : ‖(Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * Complex.I‖
      ≤ ‖(Real.log ‖z‖ : ℂ)‖ + ‖(Complex.arg z : ℂ) * Complex.I‖ := norm_add_le _ _
  have e1 : ‖(Real.log ‖z‖ : ℂ)‖ = |Real.log ‖z‖| := by simp
  have e2 : ‖(Complex.arg z : ℂ) * Complex.I‖ = |Complex.arg z| := by simp
  rw [e1, e2] at hb
  have hlog : |Real.log ‖z‖| ≤ 1.4 := by
    rw [abs_le]
    refine ⟨by linarith [Real.log_nonneg (show (1 : ℝ) ≤ ‖z‖ by linarith)], ?_⟩
    have h4 : Real.log ‖z‖ ≤ Real.log 4 := Real.log_le_log (by linarith) (by linarith)
    have e3 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have := Real.log_two_lt_d9
    linarith
  have harg : |Complex.arg z| ≤ Real.pi := Complex.abs_arg_le_pi z
  have hpi := Real.pi_lt_d2
  linarith

theorem abs_phase_le (m : ℕ) : |phase m| ≤ Real.pi := by
  unfold phase
  split
  · rw [abs_of_nonneg Real.pi_pos.le]
  · simpa using Real.pi_pos.le

theorem zeta_norm_le (m : ℕ) (hm : 40 ≤ m) {w : ℂ} (hw : ‖w - 1‖ ≤ 1 / 2) :
    ‖zeta m w‖ ≤ 9 / m := by
  obtain ⟨hlo, hhi, -⟩ := two_add_bounds hw
  have hlog : ‖Complex.log (2 + w)‖ ≤ 5 := norm_log_le_five hlo hhi
  have hph : ‖Complex.I * (phase m : ℂ)‖ ≤ Real.pi := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    exact abs_phase_le m
  have hpi := Real.pi_lt_d2
  have hnum : ‖Complex.I * (phase m : ℂ) - Complex.log (2 + w)‖ ≤ 9 := by
    calc ‖Complex.I * (phase m : ℂ) - Complex.log (2 + w)‖
        ≤ ‖Complex.I * (phase m : ℂ)‖ + ‖Complex.log (2 + w)‖ := norm_sub_le _ _
      _ ≤ 9 := by linarith
  have hmpos : (0 : ℝ) < m := by
    have : (40 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [zeta, norm_div, Complex.norm_natCast]
  gcongr

theorem Tmap_sub_one_le (m : ℕ) (hm : 40 ≤ m) {w : ℂ} (hw : ‖w - 1‖ ≤ 1 / 2) :
    ‖Tmap m w - 1‖ ≤ 18 / m := by
  have hmR : (40 : ℝ) ≤ m := by exact_mod_cast hm
  have hz := zeta_norm_le m hm hw
  have hz1 : ‖zeta m w‖ ≤ 1 := by
    have : (9 : ℝ) / m ≤ 9 / 40 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmR
    linarith
  have := Complex.norm_exp_sub_one_le hz1
  rw [Tmap]
  calc ‖Complex.exp (zeta m w) - 1‖ ≤ 2 * ‖zeta m w‖ := this
    _ ≤ 2 * (9 / m) := by linarith
    _ = 18 / m := by ring

theorem Tmap_mem (m : ℕ) (hm : 40 ≤ m) {w : ℂ} (hw : ‖w - 1‖ ≤ 1 / 2) :
    ‖Tmap m w - 1‖ ≤ 1 / 2 := by
  have hmR : (40 : ℝ) ≤ m := by exact_mod_cast hm
  have h := Tmap_sub_one_le m hm hw
  have : (18 : ℝ) / m ≤ 18 / 40 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmR
  linarith

theorem Tmap_hasDerivAt (m : ℕ) {w : ℂ} (hw : ‖w - 1‖ ≤ 1 / 2) :
    HasDerivAt (Tmap m) (Tmap m w * (-(1 / (2 + w)) / (m : ℂ))) w := by
  obtain ⟨hlo, -, hslit⟩ := two_add_bounds hw
  have h2w : (2 : ℂ) + w ≠ 0 := by
    intro h
    rw [h] at hlo
    simp at hlo
    linarith
  have hlin : HasDerivAt (fun t : ℂ => 2 + t) 1 w := by
    simpa using (hasDerivAt_id w).const_add 2
  have hlog : HasDerivAt (fun t : ℂ => Complex.log (2 + t)) (1 / (2 + w)) w :=
    hlin.clog hslit
  have hzeta : HasDerivAt (zeta m) ((-(1 / (2 + w))) / (m : ℂ)) w := by
    have := ((hlog.const_sub (Complex.I * (phase m : ℂ))).div_const (m : ℂ))
    simpa [zeta] using this
  simpa [Tmap] using hzeta.cexp

theorem Tmap_lipschitz (m : ℕ) (hm : 40 ≤ m) {w₁ w₂ : ℂ}
    (h₁ : ‖w₁ - 1‖ ≤ 1 / 2) (h₂ : ‖w₂ - 1‖ ≤ 1 / 2) :
    ‖Tmap m w₁ - Tmap m w₂‖ ≤ (1 / 2) * ‖w₁ - w₂‖ := by
  have hmR : (40 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  set s : Set ℂ := Metric.closedBall (1 : ℂ) (1 / 2) with hs
  have hmem : ∀ {v : ℂ}, ‖v - 1‖ ≤ 1 / 2 → v ∈ s := by
    intro v hv
    simpa [hs, Metric.mem_closedBall, dist_eq_norm] using hv
  have hmem' : ∀ {v : ℂ}, v ∈ s → ‖v - 1‖ ≤ 1 / 2 := by
    intro v hv
    simpa [hs, Metric.mem_closedBall, dist_eq_norm] using hv
  have hderiv : ∀ v ∈ s, HasFDerivWithinAt (Tmap m)
      (ContinuousLinearMap.toSpanSingleton ℂ (Tmap m v * (-(1 / (2 + v)) / (m : ℂ)))) s v := by
    intro v hv
    exact ((Tmap_hasDerivAt m (hmem' hv)).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ v ∈ s, ‖ContinuousLinearMap.toSpanSingleton ℂ
      (Tmap m v * (-(1 / (2 + v)) / (m : ℂ)))‖ ≤ 1 / 2 := by
    intro v hv
    rw [ContinuousLinearMap.norm_toSpanSingleton]
    obtain ⟨hlo, -, -⟩ := two_add_bounds (hmem' hv)
    have hT : ‖Tmap m v‖ ≤ 2 := by
      have h := Tmap_sub_one_le m hm (hmem' hv)
      have h18 : (18 : ℝ) / m ≤ 18 / 40 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmR
      have := norm_le_norm_add_norm_sub' (Tmap m v) (1 : ℂ)
      simp only [norm_one] at this
      calc ‖Tmap m v‖ ≤ ‖Tmap m v - 1‖ + 1 := by
            have h2 := norm_add_le (Tmap m v - 1) (1 : ℂ)
            simp at h2 ⊢
            linarith [h2]
        _ ≤ 2 := by linarith
    have hinv : ‖-(1 / (2 + v)) / (m : ℂ)‖ ≤ (2 / 5) / m := by
      rw [norm_div, norm_neg, norm_div, Complex.norm_natCast, norm_one]
      have h5 : (1 : ℝ) / ‖2 + v‖ ≤ 2 / 5 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith
      gcongr
    calc ‖Tmap m v * (-(1 / (2 + v)) / (m : ℂ))‖
        = ‖Tmap m v‖ * ‖-(1 / (2 + v)) / (m : ℂ)‖ := norm_mul _ _
      _ ≤ 2 * ((2 / 5) / m) := by
          apply mul_le_mul hT hinv (norm_nonneg _) (by norm_num)
      _ ≤ 1 / 2 := by
          have h40 : (2 / 5 : ℝ) / m ≤ (2 / 5) / 40 :=
            div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmR
          linarith
  have hconv : Convex ℝ s := (convex_closedBall (1 : ℂ) (1 / 2))
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound hconv
    (hmem h₂) (hmem h₁)
  exact this

/-- The contraction has a fixed point in the closed ball of centre `1`, radius `1/2`. -/
theorem exists_fixed (m : ℕ) (hm : 40 ≤ m) : ∃ w : ℂ, ‖w - 1‖ ≤ 1 / 2 ∧ Tmap m w = w := by
  set s : Set ℂ := Metric.closedBall (1 : ℂ) (1 / 2) with hs
  have hmem : ∀ {v : ℂ}, ‖v - 1‖ ≤ 1 / 2 → v ∈ s := by
    intro v hv; simpa [hs, Metric.mem_closedBall, dist_eq_norm] using hv
  have hmem' : ∀ {v : ℂ}, v ∈ s → ‖v - 1‖ ≤ 1 / 2 := by
    intro v hv; simpa [hs, Metric.mem_closedBall, dist_eq_norm] using hv
  haveI : IsClosed s := Metric.isClosed_closedBall
  haveI : CompleteSpace s := IsClosed.completeSpace_coe
  haveI : Nonempty s := ⟨⟨1, by simp [hs]⟩⟩
  let G : s → s := fun v => ⟨Tmap m v, hmem (Tmap_mem m hm (hmem' v.2))⟩
  have hG : ContractingWith (1 / 2 : NNReal) G := by
    constructor
    · norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      have h := Tmap_lipschitz m hm (hmem' x.2) (hmem' y.2)
      simp only [G, Subtype.dist_eq, dist_eq_norm]
      push_cast
      simpa using h
  obtain ⟨w0, hw0⟩ : ∃ v : s, G v = v := ⟨_, hG.fixedPoint_isFixedPt⟩
  exact ⟨(w0 : ℂ), hmem' w0.2, congrArg Subtype.val hw0⟩

theorem exp_I_phase (m : ℕ) :
    Complex.exp (Complex.I * (phase m : ℂ)) = if m % 2 = 1 then -1 else 1 := by
  unfold phase
  split
  · rw [mul_comm]
    exact Complex.exp_pi_mul_I
  · simp

/-- For `m` large there is a root of modulus at most `(3 - 18/m) ^ (-1/m)`. -/
theorem exists_root_small (m : ℕ) (hm : 40 ≤ m) :
    ∃ z : ℂ, (Pc m).IsRoot z ∧ ‖z‖ ≤ ((3 : ℝ) - 18 / m) ^ (-(1 : ℝ) / m) := by
  have hmR : (40 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  obtain ⟨w, hw, hfix⟩ := exists_fixed m hm
  obtain ⟨hlo, hhi, -⟩ := two_add_bounds hw
  have h2w : (2 : ℂ) + w ≠ 0 := by
    intro h
    rw [h] at hlo
    simp at hlo
    linarith
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- the fixed point solves the equation
  have hkey : w ^ m * (2 + w) = Complex.exp (Complex.I * (phase m : ℂ)) := by
    have h1 : w ^ m = Complex.exp ((m : ℂ) * zeta m w) := by
      rw [Complex.exp_nat_mul, ← Tmap, hfix]
    have h2 : (m : ℂ) * zeta m w = Complex.I * (phase m : ℂ) - Complex.log (2 + w) := by
      rw [zeta]; field_simp
    rw [h1, h2, Complex.exp_sub, Complex.exp_log h2w]
    field_simp
  rw [exp_I_phase m] at hkey
  -- the corresponding root
  refine ⟨-w, ?_, ?_⟩
  · have hne : (-w : ℂ) ≠ 1 := by
      intro h
      have hre : (-w).re = (1 : ℂ).re := by rw [h]
      simp only [Complex.neg_re, Complex.one_re] at hre
      have h1 : |w.re - 1| ≤ 1 / 2 := by
        have h2 : (w - 1).re = w.re - 1 := by simp
        have := Complex.abs_re_le_norm (w - 1)
        rw [h2] at this
        linarith
      have := abs_le.mp h1
      linarith [hre]
    refine (isRoot_Pc_iff m (-w) hne).mpr ?_
    have hpow : (-w : ℂ) ^ m = (-1) ^ m * w ^ m := by
      rw [← neg_one_mul w, mul_pow]
    have h2z : (2 : ℂ) - -w = 2 + w := by ring
    rw [hpow, h2z, mul_assoc, hkey]
    rcases Nat.even_or_odd m with he | ho
    · have h0 : m % 2 = 0 := Nat.even_iff.mp he
      rw [if_neg (by omega), he.neg_one_pow]
      ring
    · have h1 : m % 2 = 1 := Nat.odd_iff.mp ho
      rw [if_pos h1, ho.neg_one_pow]
      ring
  · -- the modulus bound
    have hnormeq : ‖w‖ ^ m * ‖2 + w‖ = 1 := by
      have := congrArg (fun t : ℂ => ‖t‖) hkey
      simp only [norm_mul, norm_pow] at this
      rw [this]
      split <;> simp
    have hw18 : ‖w - 1‖ ≤ 18 / m := by
      have h := Tmap_sub_one_le m hm hw
      rwa [hfix] at h
    have h3 : (3 : ℝ) - 18 / m ≤ ‖2 + w‖ := by
      have key : ‖(3 : ℂ)‖ ≤ ‖(2 : ℂ) + w‖ + ‖w - 1‖ := by
        have h3' : (3 : ℂ) = ((2 : ℂ) + w) - (w - 1) := by ring
        calc ‖(3 : ℂ)‖ = ‖((2 : ℂ) + w) - (w - 1)‖ := by rw [← h3']
          _ ≤ ‖(2 : ℂ) + w‖ + ‖w - 1‖ := norm_sub_le _ _
      have hn3 : ‖(3 : ℂ)‖ = 3 := by simp
      rw [hn3] at key
      linarith
    have hpos : (0 : ℝ) < 3 - 18 / m := by
      have : (18 : ℝ) / m ≤ 18 / 40 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmR
      linarith
    have hle : ‖w‖ ^ m ≤ ((3 : ℝ) - 18 / m)⁻¹ := by
      have hmul : ‖w‖ ^ m * (3 - 18 / m) ≤ ‖w‖ ^ m * ‖2 + w‖ :=
        mul_le_mul_of_nonneg_left h3 (pow_nonneg (norm_nonneg w) m)
      rw [hnormeq] at hmul
      rw [inv_eq_one_div, le_div_iff₀ hpos]
      linarith
    rw [norm_neg]
    by_contra hcon
    push_neg at hcon
    have hlt := pow_lt_pow_left₀ hcon (Real.rpow_nonneg hpos.le _) (by omega : m ≠ 0)
    rw [← Real.rpow_natCast ((3 - 18 / m) ^ (-(1 : ℝ) / m)) m, ← Real.rpow_mul hpos.le,
      div_mul_cancel₀ _ (ne_of_gt hmpos), Real.rpow_neg_one] at hlt
    linarith

end Q865


/-!
# Q865 : the smallest modulus of a complex root

We show `m * (1 - r m) → log 3`, where `r m` is the smallest modulus of a root of `P m`.
-/

namespace Q865

open Filter Topology

theorem rpow_neg_inv_pow (c : ℝ) (hc : 0 < c) (m : ℕ) (hm : 0 < m) :
    (c ^ (-(1 : ℝ) / m)) ^ m = c⁻¹ := by
  rw [← Real.rpow_natCast (c ^ (-(1 : ℝ) / m)) m, ← Real.rpow_mul hc.le]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [div_mul_cancel₀ _ hm0, Real.rpow_neg_one]

/-- Every root of `P m` has modulus at least `3 ^ (-1/m)`. -/
theorem le_norm_of_isRoot (m : ℕ) (hm : 2 ≤ m) {z : ℂ} (hz : (Pc m).IsRoot z) :
    (3 : ℝ) ^ (-(1 : ℝ) / m) ≤ ‖z‖ := by
  have hm0 : 0 < m := by omega
  have hne : z ≠ 1 := by
    intro h
    rw [h] at hz
    have h1 : (Pc m).eval 1 = 1 - (m : ℂ) := by simp [Pc]
    rw [Polynomial.IsRoot, h1] at hz
    have h2 : (m : ℂ) = 1 := by linear_combination -hz
    have h3 : (m : ℕ) = 1 := by exact_mod_cast h2
    omega
  have hroot := (isRoot_Pc_iff m z hne).mp hz
  have hnorm : ‖z‖ ^ m * ‖2 - z‖ = 1 := by
    have := congrArg (fun w : ℂ => ‖w‖) hroot
    simpa [norm_mul, norm_pow] using this
  have h3le : (3 : ℝ) ^ (-(1 : ℝ) / m) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : (0 : ℝ) < m := by exact_mod_cast hm0
    apply div_nonpos_of_nonpos_of_nonneg <;> linarith
  rcases le_or_gt 1 ‖z‖ with h | h
  · linarith
  · have hb : ‖2 - z‖ ≤ 3 := by
      calc ‖2 - z‖ ≤ ‖(2 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ 3 := by simp; linarith
    have hzpos : 0 ≤ ‖z‖ := norm_nonneg _
    have hpow : (1 : ℝ) / 3 ≤ ‖z‖ ^ m := by nlinarith [pow_nonneg hzpos m]
    by_contra hcon
    push_neg at hcon
    have hlt := pow_lt_pow_left₀ hcon hzpos (by omega : m ≠ 0)
    rw [rpow_neg_inv_pow 3 (by norm_num) m hm0] at hlt
    norm_num at hlt
    linarith

theorem rootSet_nonempty (m : ℕ) (hm : 40 ≤ m) :
    ((fun z : ℂ => ‖z‖) '' {z : ℂ | (Pc m).IsRoot z}).Nonempty := by
  obtain ⟨z, hz, -⟩ := exists_root_small m hm
  exact ⟨‖z‖, z, hz, rfl⟩

theorem rootSet_bddBelow (m : ℕ) :
    BddBelow ((fun z : ℂ => ‖z‖) '' {z : ℂ | (Pc m).IsRoot z}) := by
  refine ⟨0, ?_⟩
  rintro x ⟨z, -, rfl⟩
  exact norm_nonneg _

theorem le_rmin (m : ℕ) (hm : 40 ≤ m) : (3 : ℝ) ^ (-(1 : ℝ) / m) ≤ rmin m := by
  refine le_csInf (rootSet_nonempty m hm) ?_
  rintro x ⟨z, hz, rfl⟩
  exact le_norm_of_isRoot m (by omega) hz

theorem rmin_le (m : ℕ) (hm : 40 ≤ m) : rmin m ≤ ((3 : ℝ) - 18 / m) ^ (-(1 : ℝ) / m) := by
  obtain ⟨z, hz, hzle⟩ := exists_root_small m hm
  refine le_trans (csInf_le (rootSet_bddBelow m) ⟨z, hz, rfl⟩) hzle

/-- If `c m → 3` then `m * (1 - c m ^ (-1/m)) → log 3`. -/
theorem tendsto_root_scale (c : ℕ → ℝ) (hc : Tendsto c atTop (𝓝 3)) :
    Tendsto (fun m : ℕ => (m : ℝ) * (1 - (c m) ^ (-(1 : ℝ) / m))) atTop (𝓝 (Real.log 3)) := by
  have hL : Tendsto (fun m : ℕ => Real.log (c m)) atTop (𝓝 (Real.log 3)) :=
    ((Real.continuousAt_log (by norm_num)).tendsto).comp hc
  have hc1 : ∀ᶠ m : ℕ in atTop, 1 < c m := hc.eventually_const_lt (by norm_num)
  have hmpos : ∀ᶠ m : ℕ in atTop, 0 < m := eventually_gt_atTop 0
  set t : ℕ → ℝ := fun m => Real.log (c m) / m with ht
  have htend : Tendsto t atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop hL tendsto_natCast_atTop_atTop
  have htne : ∀ᶠ m : ℕ in atTop, -(t m) ∈ ({0}ᶜ : Set ℝ) := by
    filter_upwards [hc1, hmpos] with m h1 h2
    have hlog : 0 < Real.log (c m) := Real.log_pos h1
    have hm : (0 : ℝ) < m := by exact_mod_cast h2
    have hpos : 0 < t m := div_pos hlog hm
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcon
    linarith [hcon ▸ hpos]
  have ht0 : Tendsto (fun m : ℕ => -(t m)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (by simpa using htend.neg) htne
  have hslope : Tendsto (slope Real.exp 0) (𝓝[≠] 0) (𝓝 1) := by
    have h := Real.hasDerivAt_exp 0
    simp at h
    exact hasDerivAt_iff_tendsto_slope.mp h
  have hprod : Tendsto (fun m : ℕ => Real.log (c m) * slope Real.exp 0 (-(t m))) atTop
      (𝓝 (Real.log 3 * 1)) := hL.mul (hslope.comp ht0)
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [hc1, hmpos] with m h1 h2
  have hcm : 0 < c m := by linarith
  have hlog : 0 < Real.log (c m) := Real.log_pos h1
  have hm : (0 : ℝ) < m := by exact_mod_cast h2
  have htm : 0 < t m := div_pos hlog hm
  have hpow : (c m) ^ (-(1 : ℝ) / m) = Real.exp (-(t m)) := by
    rw [Real.rpow_def_of_pos hcm]
    congr 1
    rw [ht]
    field_simp
  rw [hpow, slope_def_field]
  simp only [Real.exp_zero, sub_zero]
  rw [ht]
  field_simp
  ring

/-- The main limit: `m (1 - r m) → log 3`. -/
theorem tendsto_rmin :
    Tendsto (fun m : ℕ => (m : ℝ) * (1 - rmin m)) atTop (𝓝 (Real.log 3)) := by
  have hupper : Tendsto (fun m : ℕ => (m : ℝ) * (1 - (3 : ℝ) ^ (-(1 : ℝ) / m))) atTop
      (𝓝 (Real.log 3)) := tendsto_root_scale (fun _ => 3) tendsto_const_nhds
  have hc : Tendsto (fun m : ℕ => (3 : ℝ) - 18 / m) atTop (𝓝 3) := by
    have h12 : Tendsto (fun m : ℕ => (18 : ℝ) / m) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 18
    simpa using tendsto_const_nhds.sub h12
  have hlower : Tendsto (fun m : ℕ => (m : ℝ) * (1 - ((3 : ℝ) - 18 / m) ^ (-(1 : ℝ) / m))) atTop
      (𝓝 (Real.log 3)) := tendsto_root_scale _ hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop 40] with m hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    exact mul_le_mul_of_nonneg_left (by linarith [rmin_le m hm]) hm0
  · filter_upwards [eventually_ge_atTop 40] with m hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    exact mul_le_mul_of_nonneg_left (by linarith [le_rmin m hm]) hm0

/-- Part (c): the odd-index limit. -/
theorem tendsto_rmin_odd :
    Tendsto (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ) * (1 - rmin (2 * n + 1))) atTop
      (𝓝 (Real.log 3)) := by
  have hmap : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
    apply tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ 2 * n + 1)
    exact tendsto_id
  exact tendsto_rmin.comp hmap

end Q865


/-!
# Q865 — main statements
-/

namespace Q865

open Finset Filter Topology

/-- **Part (a)** : closed formula for the polynomials `A k`. -/
theorem Acoef_formula (k n : ℕ) (hn : 1 ≤ n) :
    (Acoef k).eval (n : ℚ) = (((k + 1) * (n + 1) - 2).choose k : ℚ) / (k + 1) :=
  Acoef_eval_choose k n hn

/-- Summability of the series of part (b). -/
theorem summable_A (n : ℕ) (hn : 2 ≤ n) :
    Summable (fun k : ℕ => Aval k n * uu n ^ (k + 1)) := by
  have h := summable_ccu n hn (uu_pos n).le (le_refl (uu n))
  have h2 : Summable (fun k : ℕ => cc n (k + 1) * uu n ^ (k + 1)) :=
    (summable_nat_add_iff 1).mpr h
  refine h2.congr ?_
  intro k
  rw [Acoef_eval_eq k n (by omega)]

/-- **Part (b)** : the positive root is given exactly by the convergent series. -/
theorem pos_root_eq_series (n : ℕ) (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x)
    (hroot : x ^ n = ∑ k ∈ range n, x ^ k) :
    x = 2 * (1 - ∑' k : ℕ, Aval k n * uu n ^ (k + 1)) := by
  have hy0 : 0 ≤ Sser n (uu n) := Sser_nonneg n (uu_pos n).le
  have hy1 : Sser n (uu n) < 1 / ((n : ℝ) + 1) := Sser_lt n hn
  have hfe : Sser n (uu n) * (1 - Sser n (uu n)) ^ n = uu n :=
    Sser_funeq n hn (uu_pos n).le le_rfl
  set y := Sser n (uu n) with hy
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_of_lt hn
  have hylt : y < 1 / 3 := by
    have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    linarith
  set ρ := 2 * (1 - y) with hρ
  have hρpos : 0 < ρ := by
    have : y < 1 := by linarith
    simp only [hρ]; linarith
  have hρne : ρ ≠ 1 := by
    intro h
    have : y = 1 / 2 := by simp only [hρ] at h; linarith
    rw [this] at hylt; norm_num at hylt
  have hkey : ρ ^ n * (2 - ρ) = 1 := by
    have h2 : (2 : ℝ) - ρ = 2 * y := by simp only [hρ]; ring
    have h3 : ρ ^ n = 2 ^ n * (1 - y) ^ n := by
      simp only [hρ]; rw [mul_pow]
    rw [h2, h3]
    have : (2:ℝ) ^ n * (1 - y) ^ n * (2 * y) = 2 ^ (n + 1) * (y * (1 - y) ^ n) := by
      ring
    rw [this, hfe]
    unfold uu
    rw [inv_pow]
    field_simp
  have hroot' : ρ ^ n = ∑ k ∈ range n, ρ ^ k := (real_root_iff n ρ hρne).mpr hkey
  have huniq := exists_unique_pos_root n hn
  obtain ⟨z, hz, hzu⟩ := huniq
  have hx' : x = z := (hzu x ⟨hx, hroot⟩).symm ▸ rfl
  have hρ' : ρ = z := (hzu ρ ⟨hρpos, hroot'⟩).symm ▸ rfl
  have hxρ : x = ρ := by rw [hx', hρ']
  rw [hxρ, hρ]
  congr 1
  congr 1
  -- identify the two series
  have hsum : Summable (fun m : ℕ => cc n m * uu n ^ m) :=
    summable_ccu n hn (uu_pos n).le le_rfl
  have h0 : ∑' m : ℕ, cc n m * uu n ^ m
      = ∑' k : ℕ, cc n (k + 1) * uu n ^ (k + 1) := by
    rw [hsum.tsum_eq_zero_add]
    simp
  rw [hy, Sser, h0]
  refine tsum_congr ?_
  intro k
  rw [Acoef_eval_eq k n (by omega)]

/-- **Part (b)**, in the explicit binomial form. -/
theorem pos_root_eq_series' (n : ℕ) (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x)
    (hroot : x ^ n = ∑ k ∈ range n, x ^ k) :
    x = 2 * (1 - ∑' m : ℕ, (1 / (m : ℝ)) * ((((n + 1) * m - 2).choose (m - 1) : ℕ) : ℝ)
        * ((2 : ℝ) ^ (-((m * (n + 1) : ℕ) : ℤ)))) := by
  have := pos_root_eq_series n hn hx hroot
  rw [this]
  congr 1
  congr 1
  have hsum : Summable (fun m : ℕ => cc n m * uu n ^ m) :=
    summable_ccu n hn (uu_pos n).le le_rfl
  have h0 : ∑' m : ℕ, cc n m * uu n ^ m
      = ∑' k : ℕ, cc n (k + 1) * uu n ^ (k + 1) := by
    rw [hsum.tsum_eq_zero_add]; simp
  have h1 : ∑' k : ℕ, Aval k n * uu n ^ (k + 1)
      = ∑' m : ℕ, cc n m * uu n ^ m := by
    rw [h0]
    exact tsum_congr fun k => by rw [Acoef_eval_eq k n (by omega)]
  rw [h1]
  refine tsum_congr ?_
  intro m
  have : uu n ^ m = (2 : ℝ) ^ (-((m * (n + 1) : ℕ) : ℤ)) := by
    unfold uu
    rw [← pow_mul, inv_pow, ← zpow_natCast (2:ℝ) ((n+1) * m), ← zpow_neg]
    congr 1
    push_cast
    ring
  rw [this]
  unfold cc
  ring

/-- **Part (c)** : the odd-index limit equals `log 3`. -/
theorem odd_limit :
    Tendsto (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ) * (1 - rmin (2 * n + 1))) atTop
      (𝓝 (Real.log 3)) :=
  tendsto_rmin_odd

end Q865

