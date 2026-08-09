/-
# Q756

Source: https://lucpommeret.com/assets/Qsansreponse260405.pdf

Let `β, λ ∈ ℝ` with `|λ| > 1` and

  `F(β,λ) = { g ∈ C¹(ℝ,ℝ) : g'(t) = g(λ t) - β g(t) for all t }`.

This file formalizes the *classification of the polynomial solutions* (§4 and §8 of the
solution text), together with the automatic-regularity statements of §3.
-/

import Mathlib

namespace Q756

open Polynomial Finset

/-- `IsSol β lam g` says that `g : ℝ → ℝ` is a (global) solution of the pantograph-type
functional differential equation `g'(t) = g (lam * t) - β * g t`.

Since the right-hand side is continuous whenever `g` is, this condition is exactly
membership of `g` in the set `F(β,lam)` of the problem: a `C¹` function satisfying the
equation everywhere. -/
def IsSol (beta lam : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ t, HasDerivAt g (g (lam * t) - beta * g t) t

section Regularity

variable {beta lam : ℝ} {g : ℝ → ℝ}

/-- **Lemma 1 (automatic regularity).** Every solution is `C^∞`. -/
theorem sol_contDiff (h : IsSol beta lam g) (n : ℕ) : ContDiff ℝ n g := by
  induction n with
  | zero => exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (h t).continuousAt)
  | succ n ih =>
      have hd : deriv g = fun t => g (lam * t) - beta * g t := funext fun t => (h t).deriv
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; ring,
        contDiff_succ_iff_deriv]
      refine ⟨fun t => (h t).differentiableAt, by simp, ?_⟩
      rw [hd]
      exact (ih.comp (contDiff_const.mul contDiff_id)).sub (contDiff_const.mul ih)

/-- **Lemma 1, formula (3.1).** The `n`-th derivative of a solution satisfies
`g^{(n+1)}(t) = lam^n g^{(n)}(lam t) - β g^{(n)}(t)`. -/
theorem hasDerivAt_iteratedDeriv (h : IsSol beta lam g) (n : ℕ) (t : ℝ) :
    HasDerivAt (iteratedDeriv n g)
      (lam ^ n * iteratedDeriv n g (lam * t) - beta * iteratedDeriv n g t) t := by
  induction n generalizing t with
  | zero => simpa using h t
  | succ n ih =>
      have hF : iteratedDeriv (n + 1) g =
          fun t => lam ^ n * iteratedDeriv n g (lam * t) - beta * iteratedDeriv n g t := by
        rw [iteratedDeriv_succ]; exact funext fun t => (ih t).deriv
      rw [hF]
      have h1 : HasDerivAt (fun t : ℝ => iteratedDeriv n g (lam * t))
          (lam * (lam ^ n * iteratedDeriv n g (lam * (lam * t))
            - beta * iteratedDeriv n g (lam * t))) t := by
        have := (ih (lam * t)).comp t ((hasDerivAt_id t).const_mul lam)
        simpa [mul_comm] using this
      have h2 := (h1.const_mul (lam ^ n)).sub ((ih t).const_mul beta)
      convert h2 using 1
      ring

/-- **Formula (3.2).** `g^{(n+1)}(0) = (lam^n - β) g^{(n)}(0)`. -/
theorem iteratedDeriv_succ_zero (h : IsSol beta lam g) (n : ℕ) :
    iteratedDeriv (n + 1) g 0 = (lam ^ n - beta) * iteratedDeriv n g 0 := by
  rw [iteratedDeriv_succ, (hasDerivAt_iteratedDeriv h n 0).deriv]
  ring_nf

/-- **Formula (8.1).** `g^{(n)}(0) = g(0) ∏_{k<n} (lam^k - β)`. -/
theorem iteratedDeriv_zero (h : IsSol beta lam g) (n : ℕ) :
    iteratedDeriv n g 0 = g 0 * ∏ k ∈ range n, (lam ^ k - beta) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ_zero h n, ih, Finset.prod_range_succ]
      ring

/-- **Corollary 2.** A solution vanishing at the origin is flat at the origin. -/
theorem flat_of_sol_zero (h : IsSol beta lam g) (h0 : g 0 = 0) (n : ℕ) :
    iteratedDeriv n g 0 = 0 := by
  simp [iteratedDeriv_zero h n, h0]

end Regularity

section Polynomials

variable {beta lam : ℝ}

/-- The `n`-th derivative of a polynomial function is the polynomial function of the
`n`-th formal derivative. -/
theorem iteratedDeriv_polynomial (P : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (fun t => P.eval t) = fun t => ((⇑derivative)^[n] P).eval t := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
      exact funext fun t => Polynomial.deriv _

/-- The coefficients of a polynomial solution obey the recurrence
`n! * a_n = a_0 * ∏_{k<n} (lam^k - β)`. -/
theorem poly_coeff_eq (P : ℝ[X]) (h : IsSol beta lam (fun t => P.eval t)) (n : ℕ) :
    (Nat.factorial n : ℝ) * P.coeff n = P.coeff 0 * ∏ k ∈ range n, (lam ^ k - beta) := by
  have h1 := iteratedDeriv_zero h n
  rw [iteratedDeriv_polynomial P n] at h1
  simp only at h1
  rw [← coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative] at h1
  simpa [Nat.descFactorial_self, mul_comm, coeff_zero_eq_eval_zero] using h1

/-- A polynomial solution with vanishing constant term is zero. -/
theorem poly_eq_zero_of_coeff_zero (P : ℝ[X]) (h : IsSol beta lam (fun t => P.eval t))
    (h0 : P.coeff 0 = 0) : P = 0 := by
  ext n
  have := poly_coeff_eq P h n
  rw [h0, zero_mul] at this
  have hn : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  simpa using (mul_eq_zero.1 this).resolve_left hn

/-- **§4, resonance.** If a nonzero polynomial is a solution, then `β = lam ^ (deg P)`. -/
theorem resonance_of_poly_sol (P : ℝ[X]) (h : IsSol beta lam (fun t => P.eval t))
    (hP : P ≠ 0) : beta = lam ^ P.natDegree := by
  by_contra hne
  -- all the factors `lam ^ k - β` for `k ≤ deg P` would be needed to vanish
  have h0 : P.coeff 0 ≠ 0 := fun h0 => hP (poly_eq_zero_of_coeff_zero P h h0)
  have hd : P.coeff (P.natDegree + 1) = 0 :=
    Polynomial.coeff_natDegree_succ_eq_zero
  have := poly_coeff_eq P h (P.natDegree + 1)
  rw [hd, mul_zero] at this
  have hprod : ∏ k ∈ range (P.natDegree + 1), (lam ^ k - beta) = 0 :=
    ((mul_eq_zero.1 this.symm).resolve_left h0)
  obtain ⟨k, hk, hk0⟩ := Finset.prod_eq_zero_iff.1 hprod
  -- so `β = lam ^ k` for some `k ≤ deg P`; we show `k = deg P`
  have hbk : beta = lam ^ k := by linarith [sub_eq_zero.1 hk0]
  -- the coefficients vanish beyond index `k`
  have hzero : ∀ m, k < m → P.coeff m = 0 := by
    intro m hm
    have h2 := poly_coeff_eq P h m
    have : ∏ j ∈ range m, (lam ^ j - beta) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 hm) (by rw [hbk]; ring)
    rw [this, mul_zero] at h2
    have hn : (Nat.factorial m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
    exact (mul_eq_zero.1 h2).resolve_left hn
  have hle : P.natDegree ≤ k := by
    by_contra hlt
    exact hP (leadingCoeff_eq_zero.mp (hzero _ (by omega)))
  have : k = P.natDegree := le_antisymm (by simpa using Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hle
  exact hne (this ▸ hbk)

/-- The polynomial `P_p(t) = ∑_{n=0}^p (∏_{k<n}(lam^k - lam^p)) t^n / n!`. -/
noncomputable def Ppoly (lam : ℝ) (p : ℕ) : ℝ[X] :=
  ∑ n ∈ range (p + 1), C ((∏ k ∈ range n, (lam ^ k - lam ^ p)) / (Nat.factorial n : ℝ)) * X ^ n

theorem Ppoly_coeff (lam : ℝ) (p n : ℕ) :
    (Ppoly lam p).coeff n =
      if n ≤ p then (∏ k ∈ range n, (lam ^ k - lam ^ p)) / (Nat.factorial n : ℝ) else 0 := by
  rw [Ppoly, finset_sum_coeff]
  simp [coeff_C_mul, coeff_X_pow]

/-- Coefficients of a dilated polynomial. -/
theorem coeff_comp_C_mul_X (a : ℝ) (P : ℝ[X]) (n : ℕ) :
    (P.comp (C a * X)).coeff n = a ^ n * P.coeff n := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial k c =>
      rw [monomial_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, ← C_mul_X_pow_eq_monomial,
        coeff_C_mul, coeff_C_mul, coeff_X_pow]
      by_cases h : n = k <;> simp [h]; ring

/-- **§4, recurrence (4.2) is sufficient.** A polynomial whose coefficients satisfy the
recurrence `(n+1) a_{n+1} = (lam^n - β) a_n` is a solution. -/
theorem poly_isSol_of_coeff (P : ℝ[X])
    (hc : ∀ n : ℕ, ((n : ℝ) + 1) * P.coeff (n + 1) = (lam ^ n - beta) * P.coeff n) :
    IsSol beta lam (fun t => P.eval t) := by
  have hid : derivative P = P.comp (C lam * X) - C beta * P := by
    ext n
    rw [coeff_derivative, coeff_sub, coeff_comp_C_mul_X, coeff_C_mul]
    rw [mul_comm (P.coeff (n + 1))]
    rw [hc n]
    ring
  intro t
  have := P.hasDerivAt t
  rw [hid] at this
  simpa [eval_comp, mul_comm lam t] using this

theorem Ppoly_isSol (lam : ℝ) (p : ℕ) :
    IsSol (lam ^ p) lam (fun t => (Ppoly lam p).eval t) := by
  refine poly_isSol_of_coeff _ (fun n => ?_)
  rw [Ppoly_coeff, Ppoly_coeff]
  rcases lt_trichotomy n p with hn | hn | hn
  · rw [if_pos (by omega), if_pos (by omega), Finset.prod_range_succ, Nat.factorial_succ]
    have hfac : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    push_cast
    field_simp
  · subst hn
    rw [if_neg (by omega), if_pos le_rfl]
    simp
  · rw [if_neg (by omega), if_neg (by omega)]
    simp

theorem Ppoly_coeff_self_ne_zero (lam : ℝ) (hlam : 1 < |lam|) (p : ℕ) :
    (Ppoly lam p).coeff p ≠ 0 := by
  rw [Ppoly_coeff, if_pos le_rfl]
  have hfac : (Nat.factorial p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero p)
  refine div_ne_zero (Finset.prod_ne_zero_iff.2 fun k hk => ?_) hfac
  have hk' : k < p := Finset.mem_range.1 hk
  have : |lam ^ k| < |lam ^ p| := by
    rw [abs_pow, abs_pow]
    exact pow_lt_pow_right₀ hlam hk'
  intro hcon
  rw [sub_eq_zero] at hcon
  exact absurd (congrArg abs hcon) (ne_of_lt this)

theorem Ppoly_natDegree (lam : ℝ) (hlam : 1 < |lam|) (p : ℕ) :
    (Ppoly lam p).natDegree = p := by
  refine le_antisymm ?_ (le_natDegree_of_ne_zero (Ppoly_coeff_self_ne_zero lam hlam p))
  refine natDegree_le_iff_coeff_eq_zero.2 fun m hm => ?_
  rw [Ppoly_coeff, if_neg (by exact_mod_cast Nat.not_le.2 (by exact_mod_cast hm))]

theorem Ppoly_ne_zero (lam : ℝ) (hlam : 1 < |lam|) (p : ℕ) : Ppoly lam p ≠ 0 := fun h => by
  exact Ppoly_coeff_self_ne_zero lam hlam p (by rw [h, coeff_zero])

/-- **§4, classification at a resonant parameter.** If `β = lam ^ p` then every polynomial
solution is a scalar multiple of `P_p`. -/
theorem poly_sol_eq_smul_Ppoly (p : ℕ) (P : ℝ[X])
    (h : IsSol (lam ^ p) lam (fun t => P.eval t)) :
    P = C (P.coeff 0) * Ppoly lam p := by
  ext n
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have hrec := poly_coeff_eq P h n
  rw [coeff_C_mul, Ppoly_coeff]
  by_cases hn : n ≤ p
  · rw [if_pos hn]
    field_simp
    linarith [hrec]
  · rw [if_neg hn, mul_zero]
    have : ∏ k ∈ range n, (lam ^ k - lam ^ p) = 0 :=
      Finset.prod_eq_zero (i := p) (Finset.mem_range.2 (by omega)) (by ring)
    rw [this, mul_zero] at hrec
    exact (mul_eq_zero.1 hrec).resolve_left hfac

/-- **§4, non-resonant case.** If `β` is not a power of `lam`, the only polynomial solution
is `0`. -/
theorem poly_sol_eq_zero_of_nonresonant (P : ℝ[X]) (h : IsSol beta lam (fun t => P.eval t))
    (hb : ∀ p : ℕ, beta ≠ lam ^ p) : P = 0 := by
  by_contra hP
  exact hb P.natDegree (resonance_of_poly_sol P h hP)

end Polynomials

end Q756
