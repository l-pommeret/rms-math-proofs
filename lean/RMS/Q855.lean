/-
# Q855 — complete asymptotic expansion of the dominant solution of

  u_{n+2} = u_{n+1} + (λ / (n+2)) * u_n .

Main theorem (`Q855.dominant_expansion`): for every real `λ`, every solution `v` of the
recurrence with `v n ~ n ^ λ`, and every `N : ℕ`,

  v n = ∑_{k=0}^{N} α_k(λ) * n^(λ-k) + O(n^(λ-N-1)).

The coefficients `α_r(λ)` are the universal ones defined by the triangular recursion

  α_0 = 1,  α_r = (1/r) ∑_{k<r} α_k [ (2^{r+1-k} - 1) * C(λ-k, r+1-k) - λ (-2)^{r-k} ].

## Versions

Lean 4.28.0, Mathlib at commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (tag `v4.28.0`).

## Relation to the printed statement

* The printed problem concerns the *dominant* solution supplied by the earlier result R773.
  As suggested by the audit, R773 is imported as a hypothesis rather than re-proved: the theorem
  quantifies over every solution `v` of the recurrence satisfying `v n / n ^ λ → 1`.  Nothing is
  asserted about the existence of such a `v` (that is R773's content), so the statement is a
  faithful conditional form of the printed theorem.
* The error term is the stronger `O(n^{λ-N-1})` claimed in the answer, not merely `o(n^{λ-N})`.
* The stability step is proved here without the second, factorially small basis solution `W`
  of (2): instead of a Casoratian one uses directly the ratio `A n = y n / V n`, whose increments
  satisfy a contracting first order recursion.  Consequently the case `λ = 0`, where the printed
  description of `W` degenerates, needs no separate treatment, and no hypothesis on `W` appears.
* Real powers are `Real.rpow`; asymptotic statements use `Filter.Tendsto` and
  `Asymptotics.IsBigO` along `Filter.atTop` on `ℕ`.
-/
import Mathlib

open Filter Asymptotics Finset Polynomial
open scoped Topology

noncomputable section

namespace Q855

/-! ## Generalized binomial coefficients -/

/-- `gbinom x m = x (x-1) ⋯ (x-m+1) / m!`. -/
def gbinom (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => gbinom x m * (x - m) / (m + 1)

@[simp] lemma gbinom_zero (x : ℝ) : gbinom x 0 = 1 := by rw [gbinom]

lemma gbinom_succ (x : ℝ) (m : ℕ) :
    gbinom x (m + 1) = gbinom x m * (x - m) / (m + 1) := by rw [gbinom]

@[simp] lemma gbinom_one (x : ℝ) : gbinom x 1 = x := by
  rw [gbinom_succ]; norm_num

lemma gbinom_neg_one (j : ℕ) : gbinom (-1) j = (-1) ^ j := by
  induction j with
  | zero => simp
  | succ m ih =>
      rw [gbinom_succ, ih]
      have : ((m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring

/-- `(j+1) * C(x, j+1) = x * C(x-1, j)`. -/
lemma succ_mul_gbinom (x : ℝ) (j : ℕ) :
    ((j : ℝ) + 1) * gbinom x (j + 1) = x * gbinom (x - 1) j := by
  induction j generalizing x with
  | zero => simp
  | succ m ih =>
      have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
      have h1 : ((m : ℝ) + 1 + 1) ≠ 0 := by positivity
      have hx := ih x
      rw [gbinom_succ x (m + 1), gbinom_succ (x - 1) m]
      push_cast
      rw [show (x - ((m:ℝ) + 1)) = (x - 1 - m) by ring]
      field_simp
      rw [hx]
      ring

/-! ## The universal coefficients -/

/-- `alphaC l r` is the coefficient `α_r(λ)`. -/
def alphaC (l : ℝ) : ℕ → ℝ
  | 0 => 1
  | r + 1 => (1 / ((r : ℝ) + 1)) *
      ∑ k : Fin (r + 1), alphaC l k *
        (((2 : ℝ) ^ (r + 2 - (k : ℕ)) - 1) * gbinom (l - k) (r + 2 - (k : ℕ))
          - l * (-2 : ℝ) ^ (r + 1 - (k : ℕ)))
decreasing_by exact k.isLt

@[simp] lemma alphaC_zero (l : ℝ) : alphaC l 0 = 1 := by rw [alphaC]

lemma alphaC_succ (l : ℝ) (r : ℕ) :
    alphaC l (r + 1) = (1 / ((r : ℝ) + 1)) *
      ∑ k ∈ range (r + 1), alphaC l k *
        (((2 : ℝ) ^ (r + 2 - k) - 1) * gbinom (l - k) (r + 2 - k)
          - l * (-2 : ℝ) ^ (r + 1 - k)) := by
  rw [alphaC, Fin.sum_univ_eq_sum_range (fun k => alphaC l k *
        (((2 : ℝ) ^ (r + 2 - k) - 1) * gbinom (l - k) (r + 2 - k)
          - l * (-2 : ℝ) ^ (r + 1 - k))) (r + 1)]

/-- The defining cancellation property of the coefficients. -/
lemma alphaC_cancel (l : ℝ) (r : ℕ) :
    ∑ k ∈ range (r + 1), alphaC l k *
      (((2 : ℝ) ^ (r + 1 - k) - 1) * gbinom (l - k) (r + 1 - k)
        - l * (-2 : ℝ) ^ (r - k)) = 0 := by
  rw [Finset.sum_range_succ]
  have hlast : alphaC l r *
      (((2 : ℝ) ^ (r + 1 - r) - 1) * gbinom (l - r) (r + 1 - r) - l * (-2 : ℝ) ^ (r - r))
      = -(r : ℝ) * alphaC l r := by
    simp only [Nat.sub_self, Nat.add_sub_cancel_left]
    simp
    ring
  rw [hlast]
  cases r with
  | zero => simp
  | succ s =>
      have hs : ((s : ℝ) + 1) ≠ 0 := by positivity
      have hsum : ∑ k ∈ range (s + 1), alphaC l k *
          (((2 : ℝ) ^ (s + 1 + 1 - k) - 1) * gbinom (l - k) (s + 1 + 1 - k)
            - l * (-2 : ℝ) ^ (s + 1 - k)) = ((s : ℝ) + 1) * alphaC l (s + 1) := by
        rw [alphaC_succ l s]; field_simp
      rw [hsum]
      push_cast
      ring

lemma alphaC_one (l : ℝ) : alphaC l 1 = l * (3 * l + 1) / 2 := by
  simp [alphaC_succ, gbinom_succ]; ring

lemma alphaC_two (l : ℝ) : alphaC l 2 = l * (l - 1) * (27 * l ^ 2 + 5 * l + 2) / 24 := by
  simp [alphaC_succ, gbinom_succ, Finset.sum_range_succ]; ring

lemma alphaC_three (l : ℝ) :
    alphaC l 3 = l ^ 2 * (l - 1) * (l - 2) * (3 * l - 1) * (9 * l - 1) / 48 := by
  simp [alphaC_succ, gbinom_succ, Finset.sum_range_succ]; ring

lemma alphaC_four (l : ℝ) :
    alphaC l 4 = l * (l - 1) * (l - 2) * (l - 3) *
      (1215 * l ^ 4 - 1890 * l ^ 3 + 485 * l ^ 2 - 18 * l - 8) / 5760 := by
  simp [alphaC_succ, gbinom_succ, Finset.sum_range_succ]; ring

/-! ## Taylor expansion of `x ↦ (1 + c x) ^ μ` -/

lemma rpow_bdd (mu : ℝ) {s : ℝ} (h1 : 1 ≤ s) (h2 : s ≤ 3 / 2) :
    |s ^ mu| ≤ max 1 ((3 / 2 : ℝ) ^ mu) := by
  have hs : (0:ℝ) < s := lt_of_lt_of_le one_pos h1
  rw [abs_of_pos (Real.rpow_pos_of_pos hs mu)]
  rcases le_or_gt 0 mu with hmu | hmu
  · exact le_max_of_le_right (Real.rpow_le_rpow hs.le h2 hmu)
  · exact le_max_of_le_left (by simpa using Real.rpow_le_one_of_one_le_of_nonpos h1 hmu.le)

lemma rpow_taylor_bound (c : ℝ) (hc0 : 0 ≤ c) (hc2 : c ≤ 2) (M : ℕ) (mu : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc (0 : ℝ) (1 / 4),
      |(1 + c * x) ^ mu - ∑ j ∈ range M, gbinom mu j * (c * x) ^ j| ≤ C * x ^ M := by
  induction M generalizing mu with
  | zero =>
      refine ⟨max 1 ((3/2:ℝ)^mu), le_max_of_le_left zero_le_one, fun x hx => ?_⟩
      obtain ⟨hx0, hx1⟩ := hx
      have h1 : (1:ℝ) ≤ 1 + c*x := by nlinarith
      have h2 : 1 + c*x ≤ 3/2 := by nlinarith
      simpa using rpow_bdd mu h1 h2
  | succ M ih =>
      obtain ⟨C, hC0, hC⟩ := ih (mu - 1)
      refine ⟨|c*mu| * C, by positivity, ?_⟩
      rintro x ⟨hx0, hx1⟩
      set f : ℝ → ℝ := fun y => (1 + c*y)^mu - ∑ j ∈ range (M+1), gbinom mu j * (c*y)^j with hf
      have hderiv : ∀ y : ℝ, 0 ≤ y → y ≤ 1/4 →
          HasDerivAt f (c*mu*((1+c*y)^(mu-1) - ∑ i ∈ range M, gbinom (mu-1) i * (c*y)^i)) y := by
        intro y hy0 hy1
        have hpos : (0:ℝ) < 1 + c*y := by nlinarith
        have hA : HasDerivAt (fun z : ℝ => (1 + c*z)^mu) (c * mu * (1+c*y)^(mu-1)) y := by
          have h1 : HasDerivAt (fun z : ℝ => 1 + c*z) c y := by
            simpa using ((hasDerivAt_id y).const_mul c).const_add 1
          simpa using h1.rpow_const (Or.inl hpos.ne')
        have H : ∀ j ∈ range (M+1), HasDerivAt (fun z : ℝ => gbinom mu j * (c*z)^j)
            (gbinom mu j * ((j:ℝ) * (c*y)^(j-1) * c)) y := by
          intro j _
          have h1 : HasDerivAt (fun z : ℝ => c*z) c y := by
            simpa using (hasDerivAt_id y).const_mul c
          exact ((by simpa using h1.pow j :
            HasDerivAt (fun z : ℝ => (c*z)^j) ((j:ℝ) * (c*y)^(j-1) * c) y)).const_mul _
        have hB := HasDerivAt.sum H
        rw [show (∑ i ∈ range (M+1), fun z : ℝ => gbinom mu i * (c*z)^i)
            = (fun z : ℝ => ∑ j ∈ range (M+1), gbinom mu j * (c*z)^j) from
          funext fun z => by simp [Finset.sum_apply]] at hB
        have hsum : ∑ j ∈ range (M+1), gbinom mu j * ((j:ℝ) * (c*y)^(j-1) * c)
            = c*mu*∑ i ∈ range M, gbinom (mu-1) i * (c*y)^i := by
          rw [Finset.sum_range_succ']
          simp only [Nat.add_sub_cancel, Nat.cast_zero, Nat.cast_add, Nat.cast_one]
          rw [Finset.mul_sum]
          have key : ∀ i ∈ range M, gbinom mu (i+1) * (((i:ℝ)+1) * (c*y)^i * c)
              = c*mu*(gbinom (mu-1) i * (c*y)^i) := fun i _ => by
            linear_combination (c * (c*y)^i) * (succ_mul_gbinom mu i)
          rw [Finset.sum_congr rfl key]
          ring
        have hd := hA.sub hB
        rw [hsum] at hd
        convert hd using 1
        ring
      have hconv : Convex ℝ (Set.Icc (0:ℝ) x) := convex_Icc 0 x
      have hb : ∀ y ∈ Set.Icc (0:ℝ) x,
          ‖c*mu*((1+c*y)^(mu-1) - ∑ i ∈ range M, gbinom (mu-1) i * (c*y)^i)‖
          ≤ |c*mu| * (C * x^M) := by
        rintro y ⟨hy0, hyx⟩
        have hy := hC y ⟨hy0, le_trans hyx hx1⟩
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact le_trans hy (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy0 hyx M) hC0)
      have hmvt := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := f) (f' := fun y => c*mu*((1+c*y)^(mu-1) - ∑ i ∈ range M, gbinom (mu-1) i * (c*y)^i))
        (fun y hy => (hderiv y hy.1 (le_trans hy.2 hx1)).hasDerivWithinAt) hb
        (Set.left_mem_Icc.mpr hx0) (Set.right_mem_Icc.mpr hx0)
      have hf0 : f 0 = 0 := by
        simp [hf, Real.one_rpow, Finset.sum_range_succ']
      rw [hf0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
      calc |f x| ≤ |c*mu| * (C * x^M) * |x - 0| := hmvt
        _ = |c*mu| * C * x^(M+1) := by rw [sub_zero, abs_of_nonneg hx0]; ring

lemma rpow_taylor_isBigO (c : ℝ) (hc0 : 0 ≤ c) (hc2 : c ≤ 2) (M : ℕ) (mu : ℝ) :
    (fun x : ℝ => (1 + c * x) ^ mu - ∑ j ∈ range M, gbinom mu j * (c * x) ^ j)
      =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ M) := by
  obtain ⟨C, hC0, hC⟩ := rpow_taylor_bound c hc0 hc2 M mu
  rw [isBigO_iff]
  refine ⟨C, ?_⟩
  have hmem : Set.Ioo (0:ℝ) (1/4) ∈ 𝓝[>] (0:ℝ) :=
    Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [hmem] with x hx
  have hx0 : (0:ℝ) ≤ x := le_of_lt hx.1
  have := hC x ⟨hx0, le_of_lt hx.2⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ M)]
  exact this

/-! ## The truncated formal series and its residual -/

lemma coeff_sum_CX (a : ℕ → ℝ) (M i : ℕ) :
    (∑ j ∈ range M, C (a j) * X ^ j).coeff i = if i < M then a i else 0 := by
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (range M) i a]
  simp

/-- The polynomial collecting the Taylor coefficients of the residual. -/
def Gpoly (l : ℝ) (N : ℕ) : ℝ[X] :=
  ∑ k ∈ range (N + 1), C (alphaC l k) *
    ((∑ j ∈ range (N + 2 - k), C (((2 : ℝ) ^ j - 1) * gbinom (l - k) j) * X ^ j) * X ^ k
      - C l * ((∑ j ∈ range (N + 1 - k), C ((-2 : ℝ) ^ j) * X ^ j) * X ^ (k + 1)))

lemma Gpoly_coeff (l : ℝ) (N : ℕ) {m : ℕ} (hm : m < N + 2) :
    (Gpoly l N).coeff m = ∑ k ∈ range (N + 1), alphaC l k *
      ((if k ≤ m then ((2:ℝ) ^ (m - k) - 1) * gbinom (l - k) (m - k) else 0)
        - l * (if k + 1 ≤ m then (-2:ℝ) ^ (m - k - 1) else 0)) := by
  rw [Gpoly, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_range] at hk
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_mul_X_pow', Polynomial.coeff_mul_X_pow', coeff_sum_CX, coeff_sum_CX]
  congr 1
  congr 1
  · by_cases h : k ≤ m
    · simp only [h, if_true]
      have h2 : m - k < N + 2 - k := by omega
      simp [h2]
    · simp [h]
  · congr 1
    by_cases h : k + 1 ≤ m
    · simp only [h, if_true]
      have h2 : m - (k + 1) < N + 1 - k := by omega
      rw [Nat.sub_sub]
      simp [h2]
    · simp [h]

lemma Gpoly_coeff_eq_zero (l : ℝ) (N : ℕ) {m : ℕ} (hm : m < N + 2) :
    (Gpoly l N).coeff m = 0 := by
  rw [Gpoly_coeff l N hm]
  have hsub : range m ⊆ range (N + 1) := by
    intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
  rw [← Finset.sum_subset hsub]
  · cases m with
    | zero => simp
    | succ r =>
        rw [← alphaC_cancel l r]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        simp only [Finset.mem_range] at hk
        have h1 : k ≤ r + 1 := by omega
        have h2 : k + 1 ≤ r + 1 := by omega
        have h3 : r + 1 - k - 1 = r - k := by omega
        simp only [h1, h2, if_true, h3]
  · intro k hk hkn
    simp only [Finset.mem_range, not_lt] at hkn ⊢
    have hno : ¬ (k + 1 ≤ m) := by omega
    simp only [hno, if_false, mul_zero, sub_zero]
    by_cases h : k ≤ m
    · have hkm : k = m := by omega
      subst hkm
      simp
    · simp [h]

lemma Gpoly_isBigO (l : ℝ) (N : ℕ) :
    (fun x : ℝ => (Gpoly l N).eval x) =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (N + 2)) := by
  obtain ⟨H, hH⟩ : (X : ℝ[X]) ^ (N + 2) ∣ Gpoly l N :=
    Polynomial.X_pow_dvd_iff.mpr (fun d hd => Gpoly_coeff_eq_zero l N hd)
  have h0 : (fun x : ℝ => H.eval x) =O[𝓝 (0:ℝ)] (fun _ : ℝ => (1:ℝ)) :=
    ((H.continuous).tendsto 0).isBigO_one ℝ
  have h1 : (fun x : ℝ => H.eval x) =O[𝓝[>] (0:ℝ)] (fun _ : ℝ => (1:ℝ)) :=
    h0.mono nhdsWithin_le_nhds
  have h2 : (fun x : ℝ => x ^ (N + 2) * H.eval x) =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x ^ (N + 2)) := by
    simpa using (isBigO_refl (fun x : ℝ => x ^ (N + 2)) (𝓝[>] (0:ℝ))).mul h1
  refine h2.congr' ?_ EventuallyEq.rfl
  filter_upwards with x
  rw [hH]
  simp

/-- The residual function, in the variable `x = 1/n`. -/
def Ffun (l : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  (∑ k ∈ range (N + 1), alphaC l k * (x ^ k * ((1 + 2 * x) ^ (l - k) - (1 + x) ^ (l - k))))
    - (l * x / (1 + 2 * x)) * ∑ k ∈ range (N + 1), alphaC l k * x ^ k

lemma Ffun_isBigO (l : ℝ) (N : ℕ) :
    (fun x : ℝ => Ffun l N x) =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (N + 2)) := by
  set E1 : ℕ → ℝ → ℝ := fun k x =>
    ((1 + 2*x) ^ (l - k) - ∑ j ∈ range (N + 2 - k), gbinom (l - k) j * (2*x) ^ j)
      - ((1 + x) ^ (l - k) - ∑ j ∈ range (N + 2 - k), gbinom (l - k) j * x ^ j) with hE1
  set E2 : ℕ → ℝ → ℝ := fun k x =>
    (1 + 2*x) ^ (-1 : ℝ) - ∑ j ∈ range (N + 1 - k), gbinom (-1) j * (2*x) ^ j with hE2
  have hEq : ∀ x ∈ Set.Ioo (0:ℝ) (1/4), Ffun l N x - (Gpoly l N).eval x
      = ∑ k ∈ range (N+1), (alphaC l k * (x^k * E1 k x) - alphaC l k * l * (x^(k+1) * E2 k x)) := by
    rintro x ⟨hx0, hx1⟩
    have hpos : (0:ℝ) < 1 + 2*x := by linarith
    rw [Ffun, Gpoly]
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finset_sum]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hi : ∑ j ∈ range (N+2-k), gbinom (l-k) j * (2*x)^j
        - ∑ j ∈ range (N+2-k), gbinom (l-k) j * x^j
        = ∑ j ∈ range (N+2-k), ((2:ℝ)^j - 1) * gbinom (l-k) j * x^j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by rw [mul_pow]; ring)
    have hii : ∑ j ∈ range (N+1-k), gbinom (-1) j * (2*x)^j
        = ∑ j ∈ range (N+1-k), (-2:ℝ)^j * x^j :=
      Finset.sum_congr rfl (fun j _ => by
        rw [gbinom_neg_one, mul_pow, show (-2:ℝ) = (-1)*2 by norm_num, mul_pow]; ring)
    have hinv : (1 + 2*x) ^ (-1 : ℝ) = 1 / (1 + 2*x) := by
      rw [Real.rpow_neg_one]; ring
    simp only [hE1, hE2, hinv]
    rw [← hi, ← hii, pow_succ]
    field_simp
    ring
  have hO : ∀ k ∈ range (N+1),
      (fun x : ℝ => alphaC l k * (x^k * E1 k x) - alphaC l k * l * (x^(k+1) * E2 k x))
        =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x ^ (N+2)) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have h2 : (fun x : ℝ => E1 k x) =O[𝓝[>](0:ℝ)] (fun x : ℝ => x^(N+2-k)) := by
      have hA := rpow_taylor_isBigO 2 (by norm_num) (by norm_num) (N+2-k) (l-k)
      have hB := rpow_taylor_isBigO 1 (by norm_num) (by norm_num) (N+2-k) (l-k)
      simp only [one_mul] at hB
      rw [hE1]
      exact hA.sub hB
    have h3 : (fun x : ℝ => x^k * E1 k x) =O[𝓝[>](0:ℝ)] (fun x : ℝ => x^(N+2)) := by
      have h := (isBigO_refl (fun x:ℝ => x^k) (𝓝[>](0:ℝ))).mul h2
      refine h.congr' EventuallyEq.rfl ?_
      filter_upwards with x
      rw [← pow_add]
      congr 1
      omega
    have h4 : (fun x : ℝ => E2 k x) =O[𝓝[>](0:ℝ)] (fun x : ℝ => x^(N+1-k)) := by
      rw [hE2]
      exact rpow_taylor_isBigO 2 (by norm_num) (by norm_num) (N+1-k) (-1)
    have h5 : (fun x : ℝ => x^(k+1) * E2 k x) =O[𝓝[>](0:ℝ)] (fun x : ℝ => x^(N+2)) := by
      have h := (isBigO_refl (fun x:ℝ => x^(k+1)) (𝓝[>](0:ℝ))).mul h4
      refine h.congr' EventuallyEq.rfl ?_
      filter_upwards with x
      rw [← pow_add]
      congr 1
      omega
    exact (h3.const_mul_left _).sub (h5.const_mul_left _)
  have hsum : (fun x : ℝ => ∑ k ∈ range (N+1),
      (alphaC l k * (x^k * E1 k x) - alphaC l k * l * (x^(k+1) * E2 k x)))
        =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x ^ (N+2)) := IsBigO.sum hO
  have hdiff : (fun x : ℝ => Ffun l N x - (Gpoly l N).eval x)
      =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x ^ (N+2)) := by
    refine hsum.congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1/4)] with x hx
    exact (hEq x hx).symm
  simpa using hdiff.add (Gpoly_isBigO l N)

/-- The truncated expansion as a sequence. -/
def pSeq (l : ℝ) (N : ℕ) (n : ℕ) : ℝ := ∑ k ∈ range (N + 1), alphaC l k * (n : ℝ) ^ (l - k)

lemma rpow_nat_split (l : ℝ) {n : ℕ} (hn0 : (0:ℝ) < n) (k : ℕ) :
    (n:ℝ) ^ (l - (k:ℝ)) = (n:ℝ) ^ l * (1/(n:ℝ)) ^ k := by
  rw [Real.rpow_sub hn0, Real.rpow_natCast, div_eq_mul_inv, one_div, inv_pow]

lemma rpow_shift (l : ℝ) {n : ℕ} (hn : 1 ≤ n) (c : ℝ) (hc : 0 ≤ c) (k : ℕ) :
    ((n:ℝ) + c) ^ (l - k) = (n:ℝ) ^ l * ((1/(n:ℝ)) ^ k * (1 + c * (1/(n:ℝ))) ^ (l - k)) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have h1 : (n:ℝ) + c = (n:ℝ) * (1 + c * (1/(n:ℝ))) := by field_simp
  rw [h1, Real.mul_rpow hn0.le (by positivity), rpow_nat_split l hn0 k]
  ring

lemma resid_eq (l : ℝ) (N : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    pSeq l N (n + 2) - pSeq l N (n + 1) - l / ((n : ℝ) + 2) * pSeq l N n
      = (n : ℝ) ^ l * Ffun l N (1 / n) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hc : l / ((n:ℝ) + 2) = l * (1/(n:ℝ)) / (1 + 2 * (1/(n:ℝ))) := by field_simp
  rw [pSeq, pSeq, pSeq, Ffun, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show ((n+2:ℕ):ℝ) = (n:ℝ)+2 by push_cast; ring, show ((n+1:ℕ):ℝ) = (n:ℝ)+1 by push_cast; ring,
    rpow_shift l hn 2 (by norm_num) k, rpow_shift l hn 1 (by norm_num) k, hc,
    rpow_nat_split l hn0 k, show ((1:ℝ) + 1 * (1/(n:ℝ))) = 1 + 1/(n:ℝ) by ring]
  ring

lemma tendsto_one_div_nat : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝[>] (0:ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_one_div_atTop_nhds_zero_nat, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  have : (0:ℝ) < n := by exact_mod_cast hn
  simpa using by positivity

lemma resid_isBigO (l : ℝ) (N : ℕ) :
    (fun n : ℕ => pSeq l N (n + 2) - pSeq l N (n + 1) - l / ((n : ℝ) + 2) * pSeq l N n)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (l - N - 2)) := by
  have h1 : (fun n : ℕ => Ffun l N (1/(n:ℝ))) =O[atTop] (fun n : ℕ => (1/(n:ℝ)) ^ (N+2)) :=
    (Ffun_isBigO l N).comp_tendsto tendsto_one_div_nat
  have h2 : (fun n : ℕ => (n:ℝ) ^ l * Ffun l N (1/(n:ℝ)))
      =O[atTop] (fun n : ℕ => (n:ℝ) ^ l * (1/(n:ℝ)) ^ (N+2)) := (isBigO_refl _ _).mul h1
  refine h2.congr' ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (resid_eq l N hn).symm
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    rw [← rpow_nat_split l hn0 (N+2)]
    push_cast
    ring_nf

lemma pSeq_div_tendsto (l : ℝ) (N : ℕ) :
    Tendsto (fun n : ℕ => pSeq l N n / (n : ℝ) ^ l) atTop (𝓝 1) := by
  have key : ∀ n : ℕ, 0 < n → pSeq l N n / (n:ℝ) ^ l
      = (∑ i ∈ range N, alphaC l (i+1) * (1/(n:ℝ)) ^ (i+1)) + 1 := by
    intro n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    have hne : (n:ℝ) ^ l ≠ 0 := (Real.rpow_pos_of_pos hn0 l).ne'
    rw [pSeq, Finset.sum_div, Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [rpow_nat_split l hn0 (i+1)]
      field_simp
    · rw [alphaC_zero, Nat.cast_zero, sub_zero, one_mul, div_self hne]
  have h0 : Tendsto (fun n : ℕ => (∑ i ∈ range N, alphaC l (i+1) * (1/(n:ℝ)) ^ (i+1)) + 1)
      atTop (𝓝 (0 + 1)) := by
    refine Tendsto.add ?_ tendsto_const_nhds
    rw [show (0:ℝ) = ∑ i ∈ range N, (0:ℝ) by simp]
    refine tendsto_finset_sum _ (fun i _ => ?_)
    have hx : Tendsto (fun n : ℕ => (1/(n:ℝ)) ^ (i+1)) atTop (𝓝 0) := by
      have h : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
      have h2 := h.pow (i+1)
      simpa using h2
    simpa using Filter.Tendsto.const_mul (alphaC l (i+1)) hx
  rw [zero_add] at h0
  refine h0.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (key n hn).symm

/-! ## Stability of the recurrence -/

/-- Discrete Gronwall-type bound for a contracting first order recursion. -/
lemma bound_of_contract (D : ℕ → ℝ) (t : ℕ) (Cst : ℝ)
    (h : ∀ᶠ n : ℕ in atTop, |D (n + 1)| ≤ Cst / (n : ℝ) ^ t + |D n| / 2) :
    D =O[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ t) := by
  set A : ℝ := max Cst 0 with hAdef
  have hA : 0 ≤ A := le_max_right _ _
  have hCA : Cst ≤ A := le_max_left _ _
  have hpow : Tendsto (fun n : ℕ => (1 + 1/(n:ℝ)) ^ t) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => 1 + 1/(n:ℝ)) atTop (𝓝 1) := by
      have h2 : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
      simpa using tendsto_const_nhds.add h2
    have h3 := h1.pow t
    simpa using h3
  have hev : ∀ᶠ n : ℕ in atTop, (1 + 1/(n:ℝ)) ^ t < 4/3 :=
    hpow.eventually_lt_const (by norm_num)
  obtain ⟨n1, hn1⟩ := (h.and (hev.and (eventually_ge_atTop 2))).exists_forall_of_atTop
  have hn1two : 2 ≤ n1 := (hn1 n1 le_rfl).2.2
  set K : ℝ := max (4*A) (|D n1| * (n1:ℝ) ^ t) with hKdef
  have hK0 : 0 ≤ K := le_trans (by linarith) (le_max_left (4*A) _)
  have h4A : 4*A ≤ K := le_max_left _ _
  have hclaim : ∀ n, n1 ≤ n → |D n| ≤ K / (n:ℝ) ^ t := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        have hpos : (0:ℝ) < (n1:ℝ) ^ t := by
          have h5 : (0:ℝ) < n1 := by exact_mod_cast (by omega : 0 < n1)
          positivity
        rw [le_div_iff₀ hpos]
        exact le_max_right _ _
    | succ n hn ih =>
        obtain ⟨hrec, hsmall, hn2⟩ := hn1 n hn
        have hnpos : (0:ℝ) < n := by
          have h6 : (0:ℕ) < n := by omega
          exact_mod_cast h6
        have hnt : (0:ℝ) < (n:ℝ) ^ t := by positivity
        have hfac : ((n:ℝ)+1) ^ t = (n:ℝ) ^ t * (1 + 1/(n:ℝ)) ^ t := by
          rw [← mul_pow]; congr 1; field_simp
        have h1 : Cst / (n:ℝ) ^ t ≤ A / (n:ℝ) ^ t := by gcongr
        have h3 : (A + K/2)/(n:ℝ) ^ t = A/(n:ℝ) ^ t + (K/(n:ℝ) ^ t)/2 := by field_simp
        have hstep : |D (n+1)| ≤ (A + K/2) / (n:ℝ) ^ t := by
          rw [h3]; linarith [hrec, h1, ih]
        have hAK : (0:ℝ) ≤ A + K/2 := by linarith
        have hgoal : (A + K/2) / (n:ℝ) ^ t ≤ K / (((n:ℝ)+1) ^ t) := by
          rw [hfac, div_le_div_iff₀ hnt (by positivity)]
          have e2 : ((A+K/2)*(n:ℝ) ^ t)*((1 + 1/(n:ℝ)) ^ t) ≤ ((A+K/2)*(n:ℝ) ^ t)*(4/3) :=
            mul_le_mul_of_nonneg_left hsmall.le (by positivity)
          have e3 : ((A+K/2)*(n:ℝ) ^ t)*(4/3) ≤ K*(n:ℝ) ^ t := by nlinarith
          calc (A + K/2) * ((n:ℝ) ^ t * (1 + 1/(n:ℝ)) ^ t)
              = ((A+K/2)*(n:ℝ) ^ t)*((1 + 1/(n:ℝ)) ^ t) := by ring
            _ ≤ ((A+K/2)*(n:ℝ) ^ t)*(4/3) := e2
            _ ≤ K*(n:ℝ) ^ t := e3
        have hcast : ((n:ℝ)+1) = ((n+1 : ℕ) : ℝ) := by push_cast; ring
        rw [← hcast]
        linarith [hstep, hgoal]
  rw [isBigO_iff]
  refine ⟨K, ?_⟩
  filter_upwards [eventually_ge_atTop n1] with n hn
  have hnpos : (0:ℝ) < n := by
    have h7 : 2 ≤ n := le_trans hn1two hn
    have h8 : (0:ℕ) < n := by omega
    exact_mod_cast h8
  have h9 := hclaim n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(n:ℝ) ^ t),
    mul_one_div]
  exact h9

lemma tail_sum_aux (t : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    ∀ m, n ≤ m → ∑ j ∈ Finset.Ico n m, (1:ℝ)/(j:ℝ) ^ (t+2)
      ≤ (1/(n:ℝ) ^ t) * (1/((n:ℝ)-1) - 1/((m:ℝ)-1)) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
      have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
      have hm2 : (2:ℝ) ≤ m := le_trans hn2 (by exact_mod_cast hm)
      rw [Finset.sum_Ico_succ_top (by omega)]
      have hstep : (1:ℝ)/(m:ℝ) ^ (t+2) ≤ (1/(n:ℝ) ^ t) * (1/((m:ℝ)-1) - 1/(m:ℝ)) := by
        have h1 : (1:ℝ)/(m:ℝ) ^ t ≤ 1/(n:ℝ) ^ t := by
          apply one_div_le_one_div_of_le
          · positivity
          · exact pow_le_pow_left₀ (by linarith) (by exact_mod_cast hm) t
        have hm1 : (m:ℝ) - 1 ≠ 0 := by linarith
        have hm0 : (m:ℝ) ≠ 0 := by linarith
        have h2 : (1:ℝ)/((m:ℝ)-1) - 1/(m:ℝ) = 1/((m:ℝ)*((m:ℝ)-1)) := by field_simp; ring
        rw [h2]
        have h3 : (1:ℝ)/(m:ℝ) ^ (t+2) = (1/(m:ℝ) ^ t) * (1/(m:ℝ) ^ 2) := by
          rw [pow_add]; field_simp
        rw [h3]
        apply mul_le_mul h1 _ (by positivity) (by positivity)
        apply one_div_le_one_div_of_le
        · nlinarith
        · nlinarith
      have hcast : ((m:ℝ) + 1) - 1 = (m:ℝ) := by ring
      push_cast
      rw [hcast]
      linarith [ih]

/-- Tail estimate `∑_{j=n}^{m-1} j^{-(t+2)} ≤ 2 n^{-(t+1)}`. -/
lemma tail_sum_bound (t : ℕ) {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    ∑ j ∈ Finset.Ico n m, (1 : ℝ) / (j : ℝ) ^ (t + 2) ≤ 2 / (n : ℝ) ^ (t + 1) := by
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  rcases le_or_gt n m with hc | hc
  · have h1 := tail_sum_aux t hn m hc
    have hm2 : (2:ℝ) ≤ m := le_trans hn2 (by exact_mod_cast hc)
    have h2 : (1:ℝ)/((n:ℝ)-1) - 1/((m:ℝ)-1) ≤ 2/(n:ℝ) := by
      have hpos : (0:ℝ) < (m:ℝ) - 1 := by linarith
      have h3 : (1:ℝ)/((n:ℝ)-1) ≤ 2/(n:ℝ) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
      have h4 : (0:ℝ) ≤ 1/((m:ℝ)-1) := by positivity
      linarith
    calc ∑ j ∈ Finset.Ico n m, (1:ℝ)/(j:ℝ) ^ (t+2)
        ≤ (1/(n:ℝ) ^ t) * (1/((n:ℝ)-1) - 1/((m:ℝ)-1)) := h1
      _ ≤ (1/(n:ℝ) ^ t) * (2/(n:ℝ)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2/(n:ℝ) ^ (t+1) := by rw [pow_succ]; field_simp
  · rw [Finset.Ico_eq_empty (by omega)]
    simp
    positivity

/-- Telescoping of a sum of consecutive differences. -/
lemma sum_Ico_telescope (A : ℕ → ℝ) {n m : ℕ} (h : n ≤ m) :
    ∑ j ∈ Finset.Ico n m, (A (j + 1) - A j) = A m - A n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hm ih => rw [Finset.sum_Ico_succ_top hm, ih]; ring

lemma tendsto_ratio_rpow (l : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) / ((n : ℝ) + 2)) ^ l) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 1) := by
    have h2 : Tendsto (fun n : ℕ => 1 / (1 + 2 * (1 / (n : ℝ)))) atTop (𝓝 (1 / (1 + 2 * 0))) := by
      apply Filter.Tendsto.div tendsto_const_nhds
        (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat))
      norm_num
    norm_num at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    field_simp
  have h3 : ContinuousAt (fun x : ℝ => x ^ l) 1 :=
    Real.continuousAt_rpow_const 1 l (Or.inl one_ne_zero)
  simpa using h3.tendsto.comp h1

/-- The residual term, divided by the dominant solution, is `O(n^{-(N+2)})`. -/
lemma resid_div_bound (l : ℝ) (N n : ℕ) (Cg : ℝ) (hCg : 0 ≤ Cg) (Vn2 gn : ℝ) (hn2 : 2 ≤ n)
    (hlow : (1/2) * ((n:ℝ) + 2) ^ l ≤ Vn2) (hr : ((n:ℝ) / ((n:ℝ) + 2)) ^ l ≤ 2)
    (hgn : |gn| ≤ Cg * (n:ℝ) ^ (l - N - 2)) :
    |gn| / Vn2 ≤ 4 * Cg / (n:ℝ) ^ (N + 2) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h2pos : (0:ℝ) < (n:ℝ) + 2 := by linarith
  have hsplit : (n:ℝ) ^ (l - (N:ℝ) - 2) = (n:ℝ) ^ l * (1/(n:ℝ)) ^ (N + 2) := by
    have h := rpow_nat_split l hnpos (N + 2)
    rwa [show l - ((N + 2 : ℕ):ℝ) = l - (N:ℝ) - 2 by push_cast; ring] at h
  have hpow : ((1:ℝ)/(n:ℝ)) ^ (N + 2) = 1 / (n:ℝ) ^ (N + 2) := by rw [div_pow, one_pow]
  have hdiv : (n:ℝ) ^ l / ((n:ℝ) + 2) ^ l = ((n:ℝ) / ((n:ℝ) + 2)) ^ l :=
    (Real.div_rpow hnpos.le h2pos.le l).symm
  have step1 : |gn| / Vn2 ≤ (Cg * (n:ℝ) ^ (l - (N:ℝ) - 2)) / ((1/2) * ((n:ℝ) + 2) ^ l) :=
    div_le_div₀ (by positivity) hgn (by positivity) hlow
  rw [hsplit, hpow] at step1
  have heq : (Cg * ((n:ℝ) ^ l * (1 / (n:ℝ) ^ (N + 2)))) / ((1/2) * ((n:ℝ) + 2) ^ l)
      = 2 * Cg * (((n:ℝ) / ((n:ℝ) + 2)) ^ l) * (1 / (n:ℝ) ^ (N + 2)) := by
    rw [← hdiv]
    have h1 : ((n:ℝ) + 2) ^ l ≠ 0 := by positivity
    field_simp
  rw [heq] at step1
  refine step1.trans ?_
  have h3 : 2 * Cg * (((n:ℝ) / ((n:ℝ) + 2)) ^ l) ≤ 2 * Cg * 2 :=
    mul_le_mul_of_nonneg_left hr (by positivity)
  calc 2 * Cg * (((n:ℝ) / ((n:ℝ) + 2)) ^ l) * (1 / (n:ℝ) ^ (N + 2))
      ≤ (2 * Cg * 2) * (1 / (n:ℝ) ^ (N + 2)) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = 4 * Cg / (n:ℝ) ^ (N + 2) := by ring

/-- The coefficient of the first order recursion for the differences is eventually `≤ 1/2`. -/
lemma contract_coeff_bound (l : ℝ) (n : ℕ) (Vn Vn2 : ℝ) (hn2 : 2 ≤ n)
    (hup : Vn ≤ 2 * (n:ℝ) ^ l) (hlow : (1/2) * ((n:ℝ) + 2) ^ l ≤ Vn2)
    (hr : ((n:ℝ) / ((n:ℝ) + 2)) ^ l ≤ 2) (hl : 16 * |l| ≤ (n:ℝ) + 2) :
    |l| * Vn / (((n:ℝ) + 2) * Vn2) ≤ 1/2 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h2pos : (0:ℝ) < (n:ℝ) + 2 := by linarith
  have hVpos : (0:ℝ) < Vn2 := lt_of_lt_of_le (by positivity) hlow
  have hnum : |l| * Vn ≤ |l| * (2 * (n:ℝ) ^ l) := mul_le_mul_of_nonneg_left hup (abs_nonneg l)
  have step1 : |l| * Vn / (((n:ℝ) + 2) * Vn2)
      ≤ (|l| * (2 * (n:ℝ) ^ l)) / (((n:ℝ) + 2) * ((1/2) * ((n:ℝ) + 2) ^ l)) := by
    refine div_le_div₀ (by positivity) hnum (by positivity) ?_
    exact mul_le_mul_of_nonneg_left hlow h2pos.le
  refine step1.trans ?_
  have hdiv : (n:ℝ) ^ l / ((n:ℝ) + 2) ^ l = ((n:ℝ) / ((n:ℝ) + 2)) ^ l :=
    (Real.div_rpow hnpos.le h2pos.le l).symm
  have heq : (|l| * (2 * (n:ℝ) ^ l)) / (((n:ℝ) + 2) * ((1/2) * ((n:ℝ) + 2) ^ l))
      = 4 * |l| * (((n:ℝ) / ((n:ℝ) + 2)) ^ l) / ((n:ℝ) + 2) := by
    rw [← hdiv]
    have h1 : ((n:ℝ) + 2) ^ l ≠ 0 := by positivity
    field_simp
    ring
  rw [heq]
  have hb : 4 * |l| * (((n:ℝ) / ((n:ℝ) + 2)) ^ l) ≤ 8 * |l| := by
    have := mul_le_mul_of_nonneg_left hr (by positivity : (0:ℝ) ≤ 4 * |l|)
    linarith
  rw [div_le_iff₀ h2pos]
  linarith

/-- Stability lemma: an approximate solution that is `o(n^λ)` and has residual
`O(n^{λ-N-2})` is in fact `O(n^{λ-N-1})`. -/
lemma stability (l : ℝ) (V y g : ℕ → ℝ) (N : ℕ)
    (hV : ∀ n : ℕ, V (n + 2) = V (n + 1) + l / ((n : ℝ) + 2) * V n)
    (hVa : Tendsto (fun n : ℕ => V n / (n : ℝ) ^ l) atTop (𝓝 1))
    (hy : ∀ n : ℕ, y (n + 2) = y (n + 1) + l / ((n : ℝ) + 2) * y n + g n)
    (hg : g =O[atTop] fun n : ℕ => (n : ℝ) ^ (l - N - 2))
    (hyo : y =o[atTop] fun n : ℕ => (n : ℝ) ^ l) :
    y =O[atTop] fun n : ℕ => (n : ℝ) ^ (l - N - 1) := by
  obtain ⟨Cg0, hCg0⟩ := isBigO_iff.mp hg
  set Cg : ℝ := max Cg0 0 with hCgdef
  have hCgnn : (0:ℝ) ≤ Cg := le_max_right _ _
  have hgb : ∀ᶠ n : ℕ in atTop, |g n| ≤ Cg * (n:ℝ) ^ (l - (N:ℝ) - 2) := by
    filter_upwards [hCg0, eventually_gt_atTop 0] with n hn hn0
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn0
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) ^ (l - (N:ℝ) - 2))] at hn
    exact hn.trans (mul_le_mul_of_nonneg_right (le_max_left Cg0 0) (by positivity))
  have hVev : ∀ᶠ n : ℕ in atTop, (1/2) * (n:ℝ) ^ l ≤ V n ∧ V n ≤ 2 * (n:ℝ) ^ l := by
    have h1 : ∀ᶠ n : ℕ in atTop, 1/2 < V n / (n:ℝ) ^ l :=
      hVa.eventually (eventually_gt_nhds (by norm_num))
    have h2 : ∀ᶠ n : ℕ in atTop, V n / (n:ℝ) ^ l < 2 :=
      hVa.eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [h1, h2, eventually_gt_atTop 0] with n ha hb hn0
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn0
    have hp : (0:ℝ) < (n:ℝ) ^ l := Real.rpow_pos_of_pos hnpos l
    exact ⟨((lt_div_iff₀ hp).mp ha).le, ((div_lt_iff₀ hp).mp hb).le⟩
  have hVev2 : ∀ᶠ n : ℕ in atTop, (1/2) * ((n:ℝ) + 2) ^ l ≤ V (n + 2) := by
    have h := (tendsto_add_atTop_nat 2).eventually hVev
    filter_upwards [h] with n hn
    have := hn.1
    push_cast at this
    exact this
  have hrb : ∀ᶠ n : ℕ in atTop, ((n:ℝ) / ((n:ℝ) + 2)) ^ l ≤ 2 :=
    ((tendsto_ratio_rpow l).eventually_lt_const (by norm_num)).mono fun n hn => hn.le
  have hlb : ∀ᶠ n : ℕ in atTop, 16 * |l| ≤ (n:ℝ) + 2 := by
    filter_upwards [eventually_ge_atTop ⌈16 * |l|⌉₊] with n hn
    have h1 : 16 * |l| ≤ (⌈16 * |l|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈16 * |l|⌉₊ : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hall : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ |g n| ≤ Cg * (n:ℝ) ^ (l - (N:ℝ) - 2) ∧
      (1/2) * (n:ℝ) ^ l ≤ V n ∧ V n ≤ 2 * (n:ℝ) ^ l ∧
      (1/2) * ((n:ℝ) + 2) ^ l ≤ V (n + 2) ∧ ((n:ℝ) / ((n:ℝ) + 2)) ^ l ≤ 2 ∧
      16 * |l| ≤ (n:ℝ) + 2 := by
    filter_upwards [eventually_ge_atTop 2, hgb, hVev, hVev2, hrb, hlb] with n h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3.1, h3.2, h4, h5, h6⟩
  obtain ⟨n0, hn0⟩ := hall.exists_forall_of_atTop
  have hVpos : ∀ n : ℕ, n0 ≤ n → 0 < V n := by
    intro n hn
    obtain ⟨h2, -, hlowV, -⟩ := hn0 n hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hp : (0:ℝ) < (n:ℝ) ^ l := Real.rpow_pos_of_pos hnpos l
    linarith
  set A : ℕ → ℝ := fun n => y n / V n with hAdef
  set D : ℕ → ℝ := fun n => A (n + 1) - A n with hDdef
  have hkey : ∀ n : ℕ, n0 ≤ n →
      V (n + 2) * D (n + 1) = g n - (l * V n / ((n:ℝ) + 2)) * D n := by
    intro n hn
    have hp0 : V n ≠ 0 := (hVpos n hn).ne'
    have hp1 : V (n + 1) ≠ 0 := (hVpos (n + 1) (by omega)).ne'
    have hp2 : V (n + 2) ≠ 0 := (hVpos (n + 2) (by omega)).ne'
    have hnn : ((n:ℝ) + 2) ≠ 0 := by positivity
    simp only [hDdef, hAdef]
    have e1 : V (n + 2) * (y (n + 2) / V (n + 2)) = y (n + 2) := by field_simp
    rw [mul_sub, e1, hy n, hV n]
    field_simp
    ring
  have hcontract : ∀ n : ℕ, n0 ≤ n → |D (n + 1)| ≤ (4 * Cg) / (n:ℝ) ^ (N + 2) + |D n| / 2 := by
    intro n hn
    obtain ⟨hn2, hgn, -, hupV, hlow2, hr, hl16⟩ := hn0 n hn
    have hVp2 : 0 < V (n + 2) := hVpos (n + 2) (by omega)
    have hVn0 : 0 < V n := hVpos n hn
    have hnnpos : (0:ℝ) < (n:ℝ) + 2 := by positivity
    have habs : |D (n + 1)| ≤ (|g n| + (|l| * V n / ((n:ℝ) + 2)) * |D n|) / V (n + 2) := by
      rw [le_div_iff₀ hVp2]
      calc |D (n + 1)| * V (n + 2) = |V (n + 2) * D (n + 1)| := by
            rw [abs_mul, abs_of_pos hVp2]; ring
        _ = |g n - (l * V n / ((n:ℝ) + 2)) * D n| := by rw [hkey n hn]
        _ ≤ |g n| + |(l * V n / ((n:ℝ) + 2)) * D n| := by
            simpa [sub_eq_add_neg, abs_neg] using
              abs_add_le (g n) (-((l * V n / ((n:ℝ) + 2)) * D n))
        _ = |g n| + (|l| * V n / ((n:ℝ) + 2)) * |D n| := by
            rw [abs_mul, abs_div, abs_mul, abs_of_pos hVn0, abs_of_pos hnnpos]
    have hsplit : (|g n| + (|l| * V n / ((n:ℝ) + 2)) * |D n|) / V (n + 2)
        = |g n| / V (n + 2) + (|l| * V n / (((n:ℝ) + 2) * V (n + 2))) * |D n| := by
      field_simp
    rw [hsplit] at habs
    have hb1 : |g n| / V (n + 2) ≤ 4 * Cg / (n:ℝ) ^ (N + 2) :=
      resid_div_bound l N n Cg hCgnn (V (n + 2)) (g n) hn2 hlow2 hr hgn
    have hb2 : |l| * V n / (((n:ℝ) + 2) * V (n + 2)) ≤ 1/2 :=
      contract_coeff_bound l n (V n) (V (n + 2)) hn2 hupV hlow2 hr hl16
    have hb3 : (|l| * V n / (((n:ℝ) + 2) * V (n + 2))) * |D n| ≤ (1/2) * |D n| :=
      mul_le_mul_of_nonneg_right hb2 (abs_nonneg _)
    linarith
  have hDO : D =O[atTop] fun n : ℕ => 1 / (n:ℝ) ^ (N + 2) := by
    refine bound_of_contract D (N + 2) (4 * Cg) ?_
    filter_upwards [eventually_ge_atTop n0] with n hn
    exact hcontract n hn
  have hy0 : Tendsto (fun n : ℕ => y n / (n:ℝ) ^ l) atTop (𝓝 0) := by
    rw [isLittleO_iff_tendsto'] at hyo
    · exact hyo
    · filter_upwards [eventually_gt_atTop 0] with n hn h
      exact absurd h (by positivity)
  have hA0 : Tendsto A atTop (𝓝 0) := by
    have h1 := hy0.div hVa one_ne_zero
    rw [zero_div] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (max n0 1)] with n hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hVn : V n ≠ 0 := (hVpos n (le_trans (le_max_left _ _) hn)).ne'
    have hp : (n:ℝ) ^ l ≠ 0 := by positivity
    simp only [hAdef, Pi.div_apply]
    field_simp
  obtain ⟨KD, hKD⟩ := isBigO_iff.mp hDO
  set K : ℝ := max KD 0 with hKdef
  have hK0 : (0:ℝ) ≤ K := le_max_right _ _
  have hDb : ∀ᶠ n : ℕ in atTop, |D n| ≤ K / (n:ℝ) ^ (N + 2) := by
    filter_upwards [hKD, eventually_gt_atTop 0] with n hn hn0'
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn0'
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (n:ℝ) ^ (N + 2)), mul_one_div] at hn
    refine hn.trans ?_
    gcongr
    exact le_max_left _ _
  obtain ⟨n2, hn2b⟩ := (hDb.and (eventually_ge_atTop (max n0 2))).exists_forall_of_atTop
  have hAbound : ∀ n : ℕ, n2 ≤ n → |A n| ≤ 2 * K / (n:ℝ) ^ (N + 1) := by
    intro n hn
    obtain ⟨-, hge⟩ := hn2b n hn
    have hn2' : 2 ≤ n := le_trans (le_max_right n0 2) hge
    have hlim : Tendsto (fun m : ℕ => |A m - A n|) atTop (𝓝 |(0:ℝ) - A n|) :=
      (hA0.sub tendsto_const_nhds).abs
    have hbnd : ∀ᶠ m : ℕ in atTop, |A m - A n| ≤ 2 * K / (n:ℝ) ^ (N + 1) := by
      filter_upwards [eventually_ge_atTop n] with m hm
      have htel : ∑ j ∈ Finset.Ico n m, D j = A m - A n := by
        simp only [hDdef]
        exact sum_Ico_telescope A hm
      rw [← htel]
      calc |∑ j ∈ Finset.Ico n m, D j| ≤ ∑ j ∈ Finset.Ico n m, |D j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.Ico n m, K * (1 / (j:ℝ) ^ (N + 2)) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            have hjge : n2 ≤ j := le_trans hn (Finset.mem_Ico.mp hj).1
            rw [mul_one_div]
            exact (hn2b j hjge).1
        _ = K * ∑ j ∈ Finset.Ico n m, (1 / (j:ℝ) ^ (N + 2)) := by rw [Finset.mul_sum]
        _ ≤ K * (2 / (n:ℝ) ^ (N + 1)) :=
            mul_le_mul_of_nonneg_left (tail_sum_bound N hn2' m) hK0
        _ = 2 * K / (n:ℝ) ^ (N + 1) := by ring
    simpa using le_of_tendsto hlim hbnd
  rw [isBigO_iff]
  refine ⟨4 * K, ?_⟩
  filter_upwards [eventually_ge_atTop (max n2 n0)] with n hn
  have hnge2 : n2 ≤ n := le_trans (le_max_left _ _) hn
  have hnge0 : n0 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hn2, -, -, hupV, -⟩ := hn0 n hnge0
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hVn : 0 < V n := hVpos n hnge0
  have hAn := hAbound n hnge2
  have hyn : y n = A n * V n := by
    simp only [hAdef]
    field_simp
  have h3 : (n:ℝ) ^ (l - (N:ℝ) - 1) = (n:ℝ) ^ l * (1 / (n:ℝ) ^ (N + 1)) := by
    have h := rpow_nat_split l hnpos (N + 1)
    rwa [show l - ((N + 1 : ℕ):ℝ) = l - (N:ℝ) - 1 by push_cast; ring, div_pow, one_pow] at h
  have hmain : |y n| ≤ (2 * K / (n:ℝ) ^ (N + 1)) * (2 * (n:ℝ) ^ l) := by
    rw [hyn, abs_mul, abs_of_pos hVn]
    refine mul_le_mul hAn hupV hVn.le (by positivity)
  have heq : (2 * K / (n:ℝ) ^ (N + 1)) * (2 * (n:ℝ) ^ l) = 4 * K * (n:ℝ) ^ (l - (N:ℝ) - 1) := by
    rw [h3]
    field_simp
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) ^ (l - (N:ℝ) - 1))]
  rw [heq] at hmain
  exact hmain

/-! ## Main theorem -/

/-- **Q855.**  For every real `λ`, every solution `v` of
`u_{n+2} = u_{n+1} + λ/(n+2) * u_n` with `v n ~ n ^ λ`, and every `N`, one has
`v n = ∑_{k ≤ N} α_k(λ) n^{λ-k} + O(n^{λ-N-1})`. -/
theorem dominant_expansion (l : ℝ) (v : ℕ → ℝ)
    (hrec : ∀ n : ℕ, v (n + 2) = v (n + 1) + l / ((n : ℝ) + 2) * v n)
    (hasym : Tendsto (fun n : ℕ => v n / (n : ℝ) ^ l) atTop (𝓝 1)) (N : ℕ) :
    (fun n : ℕ => v n - ∑ k ∈ range (N + 1), alphaC l k * (n : ℝ) ^ (l - k))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (l - N - 1)) := by
  have key := stability l v (fun n => v n - pSeq l N n)
      (fun n => -(pSeq l N (n + 2) - pSeq l N (n + 1) - l / ((n : ℝ) + 2) * pSeq l N n)) N
      hrec hasym ?_ ?_ ?_
  · exact key
  · intro n
    simp only [pSeq]
    rw [hrec n]
    ring
  · exact (resid_isBigO l N).neg_left
  · rw [isLittleO_iff_tendsto']
    · have h1 : Tendsto (fun n : ℕ => v n / (n : ℝ) ^ l - pSeq l N n / (n : ℝ) ^ l) atTop
          (𝓝 (1 - 1)) := hasym.sub (pSeq_div_tendsto l N)
      simp only [sub_self] at h1
      refine h1.congr ?_
      intro n
      ring
    · filter_upwards [eventually_gt_atTop 0] with n hn h
      exact absurd h (by positivity)

/-- The hypotheses of `dominant_expansion` are satisfiable, so the theorem is not vacuous:
for `λ = 1` the explicit sequence `v n = n + 2` is a solution of the recurrence with
`v n / n ^ λ → 1`. -/
lemma dominant_solution_one :
    (∀ n : ℕ, ((n + 2 : ℕ) : ℝ) + 2
        = (((n + 1 : ℕ) : ℝ) + 2) + (1 : ℝ) / ((n : ℝ) + 2) * ((n : ℝ) + 2)) ∧
      Tendsto (fun n : ℕ => ((n : ℝ) + 2) / (n : ℝ) ^ (1 : ℝ)) atTop (𝓝 1) := by
  constructor
  · intro n
    have h : ((n : ℝ) + 2) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · have h1 : Tendsto (fun n : ℕ => 1 + 2 * (1 / (n : ℝ))) atTop (𝓝 (1 + 2 * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat)
    rw [show (1 : ℝ) + 2 * 0 = 1 by ring] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.rpow_one]
    field_simp

end Q855
