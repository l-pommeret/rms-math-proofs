import Mathlib

/-!
# Q850 : explicit decreasing lower bounds for the rational approximations of a Liouville number

Let
`x = ∑_{n ≥ 1} 10^{-n!} = 0.110001000000000000000001…`.

Q850 asks for explicit decreasing functions `ψ : ℕ* → (0,1)` such that
`|x - p/q| ≥ ψ q` for every `p ∈ ℤ` and every `q ∈ ℕ*`.

This file contains:

* `Q850.liou`, the number `x`, defined as `∑' k : ℕ, 1 / 10 ^ (k+1)!`;
* `Q850.abs_sub_rat_ge`: the elementary explicit answer `ψ q = 10^{-q}`, i.e.
  `10^{-q} ≤ |x - p/q|` for all `p : ℤ` and `q ≥ 1` (§7 of the solution);
* `Q850.psi_mem_Ioo` and `Q850.psi_strictAnti`: `ψ q = 10^{-q}` lies in `(0,1)` for `q ≥ 1`
  and is strictly decreasing;
* `Q850.exists_strictAnti_lower_bound`: the packaged answer to Q850;
* `Q850.psiStar` together with `Q850.psiStar_le_abs_sub_rat`, `Q850.psiStar_antitone`,
  `Q850.psiStar_mem_Ioo`: the sharper step function
  `ψ_*(q) = 10^{-(N(q)+1)!}`, `N(q) = min {n ≥ 1 : 19 q ≤ 9 · 10^{n·n!}}` (Theorem 2 of §5).

The intermediate estimates of the solution appear as `Q850.remainder_lower`,
`Q850.remainder_upper` (the two-sided tail estimate (2.1)), `Q850.trunc_rat` (the truncations
are rationals with denominator `10^{n!}`) and `Q850.key` (the separation dichotomy (3.1)).

## Remarks on the formalization

* Denominators are natural numbers `q` with the hypothesis `1 ≤ q`; this is the reading
  `q ∈ ℕ*` noted in the solution (the printed statement writes `q ∈ ℕ`, which is a typo since
  `p/q` and `ψ(q)` require `q ≥ 1`).  Numerators are arbitrary integers `p : ℤ`, and no
  reducedness of `p/q` is assumed.
* "Decreasing" is formalized in the strict sense (`StrictAnti`) for `ψ q = 10^{-q}` and in the
  non-strict sense (`Antitone`) for the step function `ψ_*`, exactly as in the solution.
* The optimized supremum `Ψ` of §4 is not formalized; the audit's recommended (and strongest
  cleanly closed-form) target, `ψ q = 10^{-q}`, is, together with the step function `ψ_*`.
* `Q850.liou` is related to Mathlib's `liouvilleNumber 10` by
  `liouvilleNumber 10 = 1/10 + liou` (`Q850.liouvilleNumber_eq`), since Mathlib's series starts
  at `n = 0`; the tail `x - x_n` is Mathlib's `LiouvilleNumber.remainder 10 n`.

## Versions

Lean 4.28.0 (toolchain `leanprover/lean4:v4.28.0`), Mathlib tag `v4.28.0`,
commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
-/

open Finset Nat LiouvilleNumber

namespace Q850

/-- The `k`-th term of the Liouville series (indexing from `k = 0`, i.e. exponent `(k+1)!`). -/
noncomputable def liouTerm (k : ℕ) : ℝ := 1 / (10 : ℝ) ^ (k + 1)!

/-- The Liouville number `x = ∑_{n ≥ 1} 10^{-n!}`. -/
noncomputable def liou : ℝ := ∑' k : ℕ, liouTerm k

/-- The `n`-th truncation `x_n = ∑_{k=1}^{n} 10^{-k!}`. -/
noncomputable def liouTrunc (n : ℕ) : ℝ := ∑ k ∈ range n, liouTerm k

/-- Our number is Mathlib's Liouville constant in base `10`, minus its first term. -/
lemma liouvilleNumber_eq : liouvilleNumber (10 : ℝ) = 1 / 10 + liou := by
  have h := (LiouvilleNumber.summable (m := (10 : ℝ)) (by norm_num)).sum_add_tsum_nat_add 1
  rw [liouvilleNumber, ← h]
  simp [liou, liouTerm, Nat.factorial]

lemma partialSum_eq (n : ℕ) : partialSum (10 : ℝ) n = 1 / 10 + liouTrunc n := by
  rw [partialSum, Finset.sum_range_succ']
  simp [liouTrunc, liouTerm, Nat.factorial, add_comm]

/-- `x - x_n` is Mathlib's remainder of the Liouville constant. -/
lemma liou_sub_trunc (n : ℕ) : liou - liouTrunc n = remainder (10 : ℝ) n := by
  have h := LiouvilleNumber.partialSum_add_remainder (m := (10 : ℝ)) (by norm_num) n
  rw [partialSum_eq, liouvilleNumber_eq] at h
  linarith

lemma remainder_lower (n : ℕ) : 1 / (10 : ℝ) ^ (n + 1)! ≤ remainder (10 : ℝ) n := by
  have hs := LiouvilleNumber.remainder_summable (m := (10 : ℝ)) (by norm_num) n
  have := hs.le_tsum 0 (fun i _ => by positivity)
  simpa [remainder] using this

lemma remainder_upper (n : ℕ) :
    remainder (10 : ℝ) n ≤ 10 / 9 * (1 / (10 : ℝ) ^ (n + 1)!) := by
  have h := LiouvilleNumber.remainder_lt' n (m := (10 : ℝ)) (by norm_num)
  have h9 : ((1 : ℝ) - 1 / 10)⁻¹ = 10 / 9 := by norm_num
  rw [h9] at h
  exact h.le

lemma remainder_nonneg (n : ℕ) : 0 ≤ remainder (10 : ℝ) n :=
  le_trans (by positivity) (remainder_lower n)

/-- The `n`-th truncation is a rational number with denominator `10^{n!}`. -/
lemma trunc_rat (n : ℕ) : ∃ A : ℤ, liouTrunc n = (A : ℝ) / (10 : ℝ) ^ n ! := by
  obtain ⟨p, hp⟩ := LiouvilleNumber.partialSum_eq_rat (m := 10) (by norm_num) n
  refine ⟨(p : ℤ) - 10 ^ (Nat.factorial n - 1), ?_⟩
  have hfac : 1 ≤ n ! := n.factorial_pos
  have h10 : (10 : ℝ) ^ (Nat.factorial n - 1) * 10 = (10 : ℝ) ^ n ! := by
    rw [← pow_succ, Nat.sub_add_cancel hfac]
  push_cast at hp
  have hps : (1 : ℝ) / 10 + liouTrunc n = (p : ℝ) / (10 : ℝ) ^ n ! := by
    rw [← partialSum_eq]; exact hp
  have hQ : (0 : ℝ) < (10 : ℝ) ^ n ! := by positivity
  push_cast
  field_simp at hps ⊢
  nlinarith [hps, h10, hQ]

/-- Key estimate (dichotomy (3.1)): separating `p/q` from the truncation `x_n` and using the
tail estimates shows that any `t` with `t ≤ 10^{-(n+1)!}` and
`t + (10/9) · 10^{-(n+1)!} ≤ 1/(q·10^{n!})` is a lower bound for `|x - p/q|`. -/
lemma key (t : ℝ) (p : ℤ) (q n : ℕ) (hq : 1 ≤ q) (hsmall : t ≤ 1 / (10 : ℝ) ^ (n + 1)!)
    (hcond : t + 10 / 9 * (1 / (10 : ℝ) ^ (n + 1)!) ≤ 1 / ((q : ℝ) * (10 : ℝ) ^ n !)) :
    t ≤ |liou - (p : ℝ) / (q : ℝ)| := by
  obtain ⟨A, hA⟩ := trunc_rat n
  have hQ0 : (0 : ℝ) < (10 : ℝ) ^ n ! := by positivity
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hrem : liou - liouTrunc n = remainder (10 : ℝ) n := liou_sub_trunc n
  by_cases h : p * (10 : ℤ) ^ (Nat.factorial n) = A * (q : ℤ)
  · have hpq : (p : ℝ) / (q : ℝ) = (A : ℝ) / (10 : ℝ) ^ n ! := by
      rw [div_eq_div_iff hq0.ne' hQ0.ne']
      exact_mod_cast h
    rw [hpq, ← hA, hrem, abs_of_nonneg (remainder_nonneg n)]
    exact hsmall.trans (remainder_lower n)
  · have hne : p * (10 : ℤ) ^ (Nat.factorial n) - A * (q : ℤ) ≠ 0 := sub_ne_zero.mpr h
    have h1 : (1 : ℤ) ≤ |p * (10 : ℤ) ^ (Nat.factorial n) - A * (q : ℤ)| := Int.one_le_abs hne
    have h1' : (1 : ℝ) ≤ |(p : ℝ) * (10 : ℝ) ^ (Nat.factorial n) - (A : ℝ) * (q : ℝ)| := by
      have := (Int.cast_le (R := ℝ)).mpr h1
      push_cast at this
      simpa using this
    have hsep : 1 / ((q : ℝ) * (10 : ℝ) ^ n !) ≤
        |(p : ℝ) / (q : ℝ) - (A : ℝ) / (10 : ℝ) ^ n !| := by
      have heq : (p : ℝ) / (q : ℝ) - (A : ℝ) / (10 : ℝ) ^ n ! =
          ((p : ℝ) * (10 : ℝ) ^ (Nat.factorial n) - (A : ℝ) * (q : ℝ)) / ((q : ℝ) * (10 : ℝ) ^ n !) := by
        field_simp
      rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (q : ℝ) * (10 : ℝ) ^ n !)]
      rw [div_le_div_iff_of_pos_right (by positivity)]
      exact h1'
    have habs : |(p : ℝ) / (q : ℝ) - (A : ℝ) / (10 : ℝ) ^ n !| ≤
        |(p : ℝ) / (q : ℝ) - liou| + |liou - (A : ℝ) / (10 : ℝ) ^ n !| := abs_sub_le _ _ _
    have htail : |liou - (A : ℝ) / (10 : ℝ) ^ n !| = remainder (10 : ℝ) n := by
      rw [← hA, hrem, abs_of_nonneg (remainder_nonneg n)]
    have hswap : |(p : ℝ) / (q : ℝ) - liou| = |liou - (p : ℝ) / (q : ℝ)| := abs_sub_comm _ _
    rw [htail, hswap] at habs
    have hupp := remainder_upper n
    linarith

/-- An auxiliary growth estimate: `19 (n+2)! ≤ 9 · 10^{n·n!}` for `n ≥ 2`. -/
lemma factorial_growth : ∀ n : ℕ, 2 ≤ n → 19 * (n + 2)! ≤ 9 * 10 ^ (n * n !) := by
  intro n hn
  induction n with
  | zero => exact absurd hn (by norm_num)
  | succ m ih =>
      rcases Nat.lt_or_ge m 2 with hm | hm
      · have hm1 : m = 1 := by omega
        subst hm1
        norm_num [Nat.factorial]
      · have IH := ih hm
        have hstep : (m + 1 + 2)! = (m + 3) * (m + 2)! := by
          rw [show m + 1 + 2 = (m + 2) + 1 by ring, Nat.factorial_succ]
        have h1 : 19 * (m + 1 + 2)! = (m + 3) * (19 * (m + 2)!) := by rw [hstep]; ring
        have h2 : (m + 3) * (19 * (m + 2)!) ≤ (m + 3) * (9 * 10 ^ (m * m !)) :=
          Nat.mul_le_mul_left _ IH
        have hb : m + 1 ≤ 10 ^ m := Nat.lt_pow_self (by norm_num)
        have h3 : m + 3 ≤ 10 ^ (m + 1) := by
          have : 10 ^ (m + 1) = 10 * 10 ^ m := by rw [pow_succ]; ring
          omega
        have hfac : 1 ≤ m ! := m.factorial_pos
        have hmul : (m + 1) * (m + 1)! = (m + 1) * (m + 1) * m ! := by
          rw [Nat.factorial_succ]; ring
        have hle1 : m + 1 ≤ (m + 1) * m ! := Nat.le_mul_of_pos_right _ (Nat.factorial_pos m)
        have hC : 2 * m + 1 ≤ (m + 1) * (m + 1) := by nlinarith
        have hexp : m * m ! + (m + 1) ≤ (m + 1) * (m + 1)! := by
          rw [hmul]
          calc m * m ! + (m + 1) ≤ m * m ! + (m + 1) * m ! := by omega
            _ = (2 * m + 1) * m ! := by ring
            _ ≤ (m + 1) * (m + 1) * m ! := Nat.mul_le_mul_right _ hC
        calc 19 * (m + 1 + 2)! = (m + 3) * (19 * (m + 2)!) := h1
          _ ≤ (m + 3) * (9 * 10 ^ (m * m !)) := h2
          _ ≤ 10 ^ (m + 1) * (9 * 10 ^ (m * m !)) := Nat.mul_le_mul_right _ h3
          _ = 9 * 10 ^ (m * m ! + (m + 1)) := by rw [pow_add]; ring
          _ ≤ 9 * 10 ^ ((m + 1) * (m + 1)!) :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hexp)

lemma liou_lower : 1 / 10 ≤ liou := by
  have h := liou_sub_trunc 1
  have h2 : liouTrunc 1 = 1 / 10 := by
    simp [liouTrunc, liouTerm, Nat.factorial]
  have := remainder_nonneg 1
  rw [h2] at h
  linarith

lemma liou_upper : liou ≤ 1 / 9 := by
  have h := liou_sub_trunc 1
  have h2 : liouTrunc 1 = 1 / 10 := by
    simp [liouTrunc, liouTerm, Nat.factorial]
  have h3 := remainder_upper 1
  rw [h2] at h
  norm_num [Nat.factorial] at h3
  linarith

/-- The numerical form of the separation condition: if `19 q ≤ 9 · 10^{n·n!}` then
`(19/9) · 10^{-(n+1)!} ≤ 1 / (q · 10^{n!})`. -/
lemma cond_ineq (q n : ℕ) (hq : 1 ≤ q) (h : 19 * q ≤ 9 * 10 ^ (n * n !)) :
    19 / 9 * (1 / (10 : ℝ) ^ (n + 1)!) ≤ 1 / ((q : ℝ) * (10 : ℝ) ^ n !) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq19' : 19 * (q : ℝ) ≤ 9 * (10 : ℝ) ^ (n * n !) := by exact_mod_cast h
  have hfacsplit : (n + 1)! = n ! + n * n ! := by
    rw [Nat.factorial_succ]; ring
  have hpow : (10 : ℝ) ^ (n + 1)! = (10 : ℝ) ^ n ! * (10 : ℝ) ^ (n * n !) := by
    rw [hfacsplit, pow_add]
  have hA : (0 : ℝ) < (10 : ℝ) ^ n ! := by positivity
  have hB : (0 : ℝ) < (10 : ℝ) ^ (n * n !) := by positivity
  rw [hpow]
  rw [show (19 : ℝ) / 9 * (1 / ((10 : ℝ) ^ (Nat.factorial n) * (10 : ℝ) ^ (n * n !)))
        = 19 / (9 * ((10 : ℝ) ^ (Nat.factorial n) * (10 : ℝ) ^ (n * n !))) by ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hq19' hA.le, hA, hB]

/-- **Main theorem.**  For every integer `p` and every positive integer `q`,
`|x - p/q| ≥ 10^{-q}`, where `x = ∑_{n ≥ 1} 10^{-n!}`. -/
theorem abs_sub_rat_ge (p : ℤ) (q : ℕ) (hq : 1 ≤ q) :
    1 / (10 : ℝ) ^ q ≤ |liou - (p : ℝ) / (q : ℝ)| := by
  rcases Nat.lt_or_ge q 6 with hq6 | hq6
  · interval_cases q
    · -- q = 1
      have hlow := liou_lower
      have hupp := liou_upper
      by_cases hp : p ≤ 0
      · have : (p : ℝ) ≤ 0 := by exact_mod_cast hp
        rw [abs_of_nonneg (by push_cast; nlinarith)]
        push_cast
        norm_num
        linarith
      · have hp' : 1 ≤ p := by omega
        have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'
        rw [abs_of_nonpos (by push_cast; nlinarith)]
        push_cast
        norm_num
        linarith
    all_goals
      · refine key _ p _ 1 (by norm_num) (by norm_num [Nat.factorial]) ?_
        norm_num [Nat.factorial]
  · -- q ≥ 6 : take `n` maximal with `(n+1)! ≤ q`
    set P : ℕ → Prop := fun n => (n + 1)! ≤ q with hP
    have hP2 : P 2 := by
      simpa [hP, Nat.factorial] using hq6
    have hle : 2 ≤ q := by omega
    set n := Nat.findGreatest P q with hn
    have hn2 : 2 ≤ n := Nat.le_findGreatest (by omega) hP2
    have hPn : P n := Nat.findGreatest_spec (m := 2) (by omega) hP2
    have hnq : (n + 1)! ≤ q := hPn
    have hnlt : n + 1 ≤ q := le_trans (Nat.self_le_factorial (n + 1)) hnq
    have hnot : ¬ P (n + 1) := by
      refine Nat.findGreatest_is_greatest ?_ (by omega)
      omega
    have hqlt : q < (n + 2)! := by
      have h' : ¬ ((n + 1 + 1)! ≤ q) := hnot
      rw [show n + 1 + 1 = n + 2 from rfl] at h'
      omega
    refine key _ p q n (by omega)
      (one_div_pow_le_one_div_pow_of_le (by norm_num) hnq) ?_
    -- the explicit numerical condition
    have hgrow : 19 * (n + 2)! ≤ 9 * 10 ^ (n * n !) := factorial_growth n hn2
    have hq19 : 19 * q ≤ 9 * 10 ^ (n * n !) := by omega
    have hsmall : 1 / (10 : ℝ) ^ q ≤ 1 / (10 : ℝ) ^ (n + 1)! :=
      one_div_pow_le_one_div_pow_of_le (by norm_num) hnq
    linarith [cond_ineq q n (by omega) hq19, hsmall]

/-- The function `ψ q = 10^{-q}` takes values in `(0,1)` for `q ≥ 1`. -/
theorem psi_mem_Ioo (q : ℕ) (hq : 1 ≤ q) : 1 / (10 : ℝ) ^ q ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · positivity
  · rw [div_lt_one (by positivity)]
    calc (1 : ℝ) < 10 ^ 1 := by norm_num
      _ ≤ 10 ^ q := by
          apply pow_le_pow_right₀ (by norm_num) hq

/-- `ψ q = 10^{-q}` is strictly decreasing. -/
theorem psi_strictAnti : StrictAnti (fun q : ℕ => 1 / (10 : ℝ) ^ q) := by
  intro a b hab
  simp only
  rw [div_lt_div_iff_of_pos_left (by norm_num) (by positivity) (by positivity)]
  exact pow_lt_pow_right₀ (by norm_num) hab

/-!
## The sharper step function `ψ_*` of Theorem 2

`N q` is the least `n ≥ 1` with `19 q ≤ 9 · 10^{n·n!}` and `ψ_* q = 10^{-(N q + 1)!}`.
-/

lemma exists_pow_bound (q : ℕ) : ∃ n : ℕ, 1 ≤ n ∧ 19 * q ≤ 9 * 10 ^ (n * n !) := by
  refine ⟨q + 1, by omega, ?_⟩
  have h1 : q ≤ 10 ^ q := le_of_lt (Nat.lt_pow_self (by norm_num))
  have hE : q + 1 ≤ (q + 1) * (q + 1)! := Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
  have h2 : 10 ^ (q + 1) ≤ 10 ^ ((q + 1) * (q + 1)!) := Nat.pow_le_pow_right (by norm_num) hE
  have h3 : 10 ^ (q + 1) = 10 * 10 ^ q := by rw [pow_succ]; ring
  omega

/-- `N q` is the least `n ≥ 1` such that `19 q ≤ 9 · 10^{n·n!}`. -/
def bigN (q : ℕ) : ℕ := Nat.find (exists_pow_bound q)

lemma bigN_spec (q : ℕ) : 1 ≤ bigN q ∧ 19 * q ≤ 9 * 10 ^ (bigN q * (bigN q)!) :=
  Nat.find_spec (exists_pow_bound q)

lemma bigN_mono : Monotone bigN := by
  intro a b hab
  refine Nat.find_le ⟨(bigN_spec b).1, ?_⟩
  have := (bigN_spec b).2
  omega

/-- The explicit step function `ψ_*(q) = 10^{-(N(q)+1)!}` of Theorem 2. -/
noncomputable def psiStar (q : ℕ) : ℝ := 1 / (10 : ℝ) ^ (bigN q + 1)!

/-- **Theorem 2.**  `|x - p/q| ≥ ψ_*(q)` for all `p ∈ ℤ` and `q ≥ 1`. -/
theorem psiStar_le_abs_sub_rat (p : ℤ) (q : ℕ) (hq : 1 ≤ q) :
    psiStar q ≤ |liou - (p : ℝ) / (q : ℝ)| := by
  refine key _ p q (bigN q) hq le_rfl ?_
  have h := cond_ineq q (bigN q) hq (bigN_spec q).2
  rw [psiStar]
  linarith

/-- `ψ_*` is non-increasing. -/
theorem psiStar_antitone : Antitone psiStar := by
  intro a b hab
  refine one_div_pow_le_one_div_pow_of_le (by norm_num) ?_
  exact Nat.factorial_le (by have := bigN_mono hab; omega)

/-- `ψ_*` takes its values in `(0,1)`. -/
theorem psiStar_mem_Ioo (q : ℕ) : psiStar q ∈ Set.Ioo (0 : ℝ) 1 := by
  have h1 : 1 ≤ bigN q := (bigN_spec q).1
  have h2 : 2 ≤ (bigN q + 1)! := by
    calc 2 = 2 ! := rfl
      _ ≤ (bigN q + 1)! := Nat.factorial_le (by omega)
  constructor
  · rw [psiStar]; positivity
  · rw [psiStar, div_lt_one (by positivity)]
    calc (1 : ℝ) < 10 ^ 1 := by norm_num
      _ ≤ 10 ^ (bigN q + 1)! := by
          exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- **Answer to Q850.**  There is an explicit strictly decreasing function
`ψ : ℕ* → (0,1)` with `|x - p/q| ≥ ψ q` for all `p ∈ ℤ`, `q ≥ 1`; one may take
`ψ q = 10^{-q}`. -/
theorem exists_strictAnti_lower_bound :
    ∃ psi : ℕ → ℝ, StrictAnti psi ∧ (∀ q : ℕ, 1 ≤ q → psi q ∈ Set.Ioo (0 : ℝ) 1) ∧
      ∀ (p : ℤ) (q : ℕ), 1 ≤ q → psi q ≤ |liou - (p : ℝ) / (q : ℝ)| :=
  ⟨fun q => 1 / (10 : ℝ) ^ q, psi_strictAnti, psi_mem_Ioo, abs_sub_rat_ge⟩

end Q850
