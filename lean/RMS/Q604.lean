/-
# Q604 — Powers of a Bézout pair for polynomials

Source: https://lucpommeret.com/assets/Qsansreponse260405.pdf , problem Q604.

**Printed statement.** Let `K` be a field, let `A, B ∈ K[X]` be coprime and let `U, V ∈ K[X]`
satisfy `deg U < deg B` and `A*U + B*V = 1`.  For positive integers `m, n`, determine explicitly
the pair `(U_{m,n}, V_{m,n})` with `deg U_{m,n} < deg Bⁿ` and `Aᵐ U_{m,n} + Bⁿ V_{m,n} = 1`.

**Answer formalized here.**  With

  `S r s T = ∑_{j<s} C(r+j-1, j) * T^j`,

put `Û = U^m * S m n (B*V)` and `V̂ = V^n * S n m (A*U)`.  Then

  `Aᵐ Û + Bⁿ V̂ = 1`   (`Q604.bezout_hat`),

and the normalized pair is obtained by Euclidean division of `Û` by `Bⁿ`:

  `U_{m,n} = Û % Bⁿ`,   `V_{m,n} = V̂ + Aᵐ * (Û / Bⁿ)`.

`Q604.Q604_printed` states, under exactly the printed hypotheses, that this pair satisfies the
two required conditions and that it is the *unique* such pair.  `Q604.all_bezout_pairs`
classifies all Bézout pairs without the degree restriction, `Q604.Vnorm_eq_div` gives the
alternative description `V_{m,n} = (1 - Aᵐ U_{m,n}) / Bⁿ`, `Q604.example_Unorm` /
`Q604.example_Vnorm` verify the worked example of §9 of the solution, and
`Q604.const_B_case` treats the degenerate case of a constant `B`.

Remarks on the formalization.

* Degrees are `Polynomial.degree`, valued in `WithBot ℕ` (so `deg 0 = ⊥`); the printed
  convention `deg 0 = -∞` is exactly this.  In particular the printed hypothesis
  `deg U < deg B` forces `B ≠ 0`, which is what makes the Euclidean division meaningful.
* The coprimality hypothesis `IsCoprime A B` is kept because it is part of the printed
  statement, although it is logically implied by `A*U + B*V = 1` and is not used.
* The binomial coefficients are natural numbers mapped into `K` by the canonical ring
  homomorphism, so the statement and proof are characteristic-free; the core identity
  (`Q604.S_bezout`) is proved over an arbitrary commutative ring.

Versions: Lean 4.28.0, Mathlib (rev 8f9d9cff6bd728b17a24e163c9402775d9e6a365, tag v4.28.0).
-/
import Mathlib

open Finset Polynomial

namespace Q604

/-! ## 1. The truncated binomial series and the universal Bézout identity -/

/-- `S r s T = ∑_{j<s} binom (r+j-1) j * T^j`, the degree `< s` truncation of `(1-T)^{-r}`. -/
def S {R : Type*} [CommRing R] (r s : ℕ) (T : R) : R :=
  ∑ j ∈ range s, (Nat.choose (r + j - 1) j : R) * T ^ j

/-- Shifted version of `S`, convenient for induction: `W r s T = S (r+1) (s+1) T`. -/
def W {R : Type*} [CommRing R] (r s : ℕ) (T : R) : R :=
  ∑ j ∈ range (s + 1), (Nat.choose (r + j) j : R) * T ^ j

variable {R : Type*} [CommRing R]

lemma S_succ_succ (r s : ℕ) (T : R) : S (r + 1) (s + 1) T = W r s T := by
  unfold S W
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show r + 1 + j - 1 = r + j from by omega]

lemma W_zero_right (r : ℕ) (T : R) : W r 0 T = 1 := by simp [W]

lemma W_pascal (r s : ℕ) (T : R) :
    W (r + 1) (s + 1) T = W r (s + 1) T + T * W (r + 1) s T := by
  unfold W
  rw [Finset.sum_range_succ' (fun j => (Nat.choose (r + 1 + j) j : R) * T ^ j) (s + 1),
      Finset.sum_range_succ' (fun j => (Nat.choose (r + j) j : R) * T ^ j) (s + 1),
      Finset.mul_sum]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
  rw [add_assoc, add_comm (1 : R), ← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : r + 1 + (j + 1) = (r + j + 1) + 1 := by ring
  have h2 : r + (j + 1) = (r + j) + 1 := by ring
  have h3 : r + 1 + j = (r + j) + 1 := by ring
  rw [h1, h2, h3, Nat.choose_succ_succ (r + j + 1) j]
  push_cast
  ring

lemma W_base (x y : R) (h : x + y = 1) (s : ℕ) :
    x ^ (0 + 1) * W 0 s y + y ^ (s + 1) * W s 0 x = 1 := by
  have hW0 : W 0 s y = ∑ j ∈ range (s + 1), y ^ j := by simp [W]
  have hW1 : W s 0 x = 1 := by simp [W]
  have hg := geom_sum_mul y (s + 1)
  have hx : x = 1 - y := by rw [← h]; ring
  rw [hW0, hW1, hx]
  linear_combination -hg

/-- **The universal binomial Bézout identity** (shifted form).  In any commutative ring,
if `x + y = 1` then `x^(r+1) * W r s y + y^(s+1) * W s r x = 1`. -/
lemma W_bezout (x y : R) (h : x + y = 1) :
    ∀ r s : ℕ, x ^ (r + 1) * W r s y + y ^ (s + 1) * W s r x = 1 := by
  intro r
  induction r with
  | zero => exact W_base x y h
  | succ r ihr =>
    intro s
    induction s with
    | zero =>
      have := W_base y x (by rw [← h]; ring) (r + 1)
      simpa [add_comm] using this
    | succ s ihs =>
      rw [W_pascal r s y, W_pascal s r x]
      linear_combination x * ihr (s + 1) + y * ihs + h

/-- **The universal binomial Bézout identity.**  In any commutative ring, if `x + y = 1`
and `r, s ≥ 1`, then `x^r * S r s y + y^s * S s r x = 1`. -/
theorem S_bezout (x y : R) (h : x + y = 1) {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    x ^ r * S r s y + y ^ s * S s r x = 1 := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  rw [S_succ_succ, S_succ_succ]
  exact W_bezout x y h r s

/-! ## 2. The explicit (unnormalized) Bézout pair for `Aᵐ` and `Bⁿ` -/

variable {K : Type*} [Field K]

/-- The unnormalized first Bézout coefficient `Û = U^m * S m n (B*V)`. -/
noncomputable def Uhat (B U V : K[X]) (m n : ℕ) : K[X] := U ^ m * S m n (B * V)

/-- The unnormalized second Bézout coefficient `V̂ = V^n * S n m (A*U)`. -/
noncomputable def Vhat (A U V : K[X]) (m n : ℕ) : K[X] := V ^ n * S n m (A * U)

/-- `Aᵐ Û + Bⁿ V̂ = 1`: the raw Bézout identity for the powers. -/
theorem bezout_hat (A B U V : K[X]) (hUV : A * U + B * V = 1) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    A ^ m * Uhat B U V m n + B ^ n * Vhat A U V m n = 1 := by
  have key := S_bezout (A * U) (B * V) hUV hm hn
  unfold Uhat Vhat
  rw [mul_pow, mul_pow] at key
  linear_combination key

/-! ## 3. The normalized pair -/

/-- The normalized first Bézout coefficient `U_{m,n} = Û % Bⁿ`. -/
noncomputable def Unorm (B U V : K[X]) (m n : ℕ) : K[X] := Uhat B U V m n % B ^ n

/-- The normalized second Bézout coefficient `V_{m,n} = V̂ + Aᵐ * (Û / Bⁿ)`. -/
noncomputable def Vnorm (A B U V : K[X]) (m n : ℕ) : K[X] :=
  Vhat A U V m n + A ^ m * (Uhat B U V m n / B ^ n)

/-- The normalized pair has the required degree bound. -/
theorem degree_Unorm_lt (B U V : K[X]) (hB : B ≠ 0) (m n : ℕ) :
    (Unorm B U V m n).degree < (B ^ n).degree :=
  Polynomial.degree_mod_lt _ (pow_ne_zero n hB)

/-- The normalized pair is a Bézout pair for `Aᵐ` and `Bⁿ`. -/
theorem bezout_norm (A B U V : K[X]) (hUV : A * U + B * V = 1) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    A ^ m * Unorm B U V m n + B ^ n * Vnorm A B U V m n = 1 := by
  have hdiv := EuclideanDomain.div_add_mod (Uhat B U V m n) (B ^ n)
  have h := bezout_hat A B U V hUV hm hn
  unfold Unorm Vnorm
  linear_combination h + A ^ m * hdiv

/-- `V_{m,n} = (1 - Aᵐ U_{m,n}) / Bⁿ`, the alternative description of the second coefficient. -/
theorem Vnorm_eq_div (A B U V : K[X]) (hB : B ≠ 0) (hUV : A * U + B * V = 1) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    Vnorm A B U V m n = (1 - A ^ m * Unorm B U V m n) / B ^ n := by
  have h := bezout_norm A B U V hUV hm hn
  have hBn : (B : K[X]) ^ n ≠ 0 := pow_ne_zero n hB
  have : (1 : K[X]) - A ^ m * Unorm B U V m n = B ^ n * Vnorm A B U V m n := by
    linear_combination -h
  rw [this, mul_div_cancel_left₀ _ hBn]

/-! ## 4. Uniqueness and the classification of all Bézout pairs -/

/-- If `P` and `P'` are first Bézout coefficients for `Aᵐ, Bⁿ`, then `Bⁿ ∣ P - P'`. -/
theorem dvd_sub_of_bezout (A B U V : K[X]) (hUV : A * U + B * V = 1) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) {P Q P' Q' : K[X]}
    (h : A ^ m * P + B ^ n * Q = 1) (h' : A ^ m * P' + B ^ n * Q' = 1) :
    B ^ n ∣ P - P' := by
  have hb := bezout_hat A B U V hUV hm hn
  refine ⟨Vhat A U V m n * (P - P') - Uhat B U V m n * (Q - Q'), ?_⟩
  linear_combination (P' - P) * hb + Uhat B U V m n * h - Uhat B U V m n * h'

/-- **Uniqueness.**  A Bézout pair for `Aᵐ, Bⁿ` whose first coefficient has degree `< deg Bⁿ`
is unique. -/
theorem bezout_unique (A B U V : K[X]) (hB : B ≠ 0) (hUV : A * U + B * V = 1) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) {P Q P' Q' : K[X]}
    (hP : P.degree < (B ^ n).degree) (hP' : P'.degree < (B ^ n).degree)
    (h : A ^ m * P + B ^ n * Q = 1) (h' : A ^ m * P' + B ^ n * Q' = 1) :
    P = P' ∧ Q = Q' := by
  have hBn : (B : K[X]) ^ n ≠ 0 := pow_ne_zero n hB
  have hdvd := dvd_sub_of_bezout A B U V hUV hm hn h h'
  have hdeg : (P - P').degree < (B ^ n).degree :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hP hP')
  have hzero : P - P' = 0 := Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hdeg
  have hPP : P = P' := by linear_combination hzero
  refine ⟨hPP, ?_⟩
  have : B ^ n * (Q - Q') = 0 := by rw [hPP] at h; linear_combination h - h'
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 hBn
  · linear_combination h1

/-- **Classification of all Bézout pairs** (no degree restriction): they are exactly
`(U_{m,n} + Bⁿ T, V_{m,n} - Aᵐ T)` for `T ∈ K[X]`. -/
theorem all_bezout_pairs (A B U V : K[X]) (hB : B ≠ 0) (hUV : A * U + B * V = 1) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (P Q : K[X]) :
    (A ^ m * P + B ^ n * Q = 1) ↔
      ∃ T : K[X], P = Unorm B U V m n + B ^ n * T ∧ Q = Vnorm A B U V m n - A ^ m * T := by
  have hBn : (B : K[X]) ^ n ≠ 0 := pow_ne_zero n hB
  have hnorm := bezout_norm A B U V hUV hm hn
  constructor
  · intro h
    obtain ⟨T, hT⟩ := dvd_sub_of_bezout A B U V hUV hm hn h hnorm
    refine ⟨T, by linear_combination hT, ?_⟩
    have : B ^ n * (Q - (Vnorm A B U V m n - A ^ m * T)) = 0 := by
      have hP : P = Unorm B U V m n + B ^ n * T := by linear_combination hT
      rw [hP] at h
      linear_combination h - hnorm
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 hBn
    · linear_combination h1
  · rintro ⟨T, rfl, rfl⟩
    linear_combination hnorm

/-! ## 5. The answer to Q604, under the printed hypotheses -/

/-- **Q604.**  Let `K` be a field, `A, B, U, V ∈ K[X]` with `A, B` coprime, `deg U < deg B`
and `A*U + B*V = 1`.  For `m, n ≥ 1` the pair

  `U_{m,n} = (U^m * ∑_{j<n} C(m+j-1,j) (BV)^j) % Bⁿ`,
  `V_{m,n} = V^n * ∑_{i<m} C(n+i-1,i) (AU)^i + Aᵐ * ((U^m * ∑_{j<n} C(m+j-1,j) (BV)^j) / Bⁿ)`

satisfies `deg U_{m,n} < deg Bⁿ` and `Aᵐ U_{m,n} + Bⁿ V_{m,n} = 1`, and it is the unique
such pair.

The hypothesis `IsCoprime A B` is part of the printed statement but is implied by
`A*U + B*V = 1`, and is not used in the proof. -/
theorem Q604_printed (A B U V : K[X]) (hcop : IsCoprime A B) (hdeg : U.degree < B.degree)
    (hUV : A * U + B * V = 1) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (Unorm B U V m n).degree < (B ^ n).degree ∧
    A ^ m * Unorm B U V m n + B ^ n * Vnorm A B U V m n = 1 ∧
    ∀ P Q : K[X], P.degree < (B ^ n).degree → A ^ m * P + B ^ n * Q = 1 →
      P = Unorm B U V m n ∧ Q = Vnorm A B U V m n := by
  have hB : B ≠ 0 := by
    rintro rfl
    simp only [Polynomial.degree_zero] at hdeg
    exact absurd hdeg (by simp)
  refine ⟨degree_Unorm_lt B U V hB m n, bezout_norm A B U V hUV hm hn, ?_⟩
  intro P Q hP h
  exact bezout_unique A B U V hB hUV hm hn hP (degree_Unorm_lt B U V hB m n) h
    (bezout_norm A B U V hUV hm hn)

/-! ## 6. The worked example of §9: `A = X²`, `B = X+1`, `U = 1`, `V = 1-X`, `m = 1`, `n = 2`. -/

/-- Characterization of the Euclidean remainder: if `P = B*Q + R` with `deg R < deg B`,
then `P % B = R`. -/
theorem mod_eq_of_eq_mul_add {B P Q R : K[X]} (hB : B ≠ 0) (h : P = B * Q + R)
    (hd : R.degree < B.degree) : P % B = R := by
  have hdvd : B ∣ (P % B - R) := by
    refine ⟨Q - P / B, ?_⟩
    have hdm := EuclideanDomain.div_add_mod P B
    linear_combination hdm + h
  have hdeg : (P % B - R).degree < B.degree :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt (Polynomial.degree_mod_lt _ hB) hd)
  have := Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hdeg
  linear_combination this

/-- The starting Bézout relation of the example. -/
example : (X ^ 2 : ℚ[X]) * 1 + (X + 1) * (1 - X) = 1 := by ring

/-- The unnormalized coefficient `Û_{1,2} = 2 - X²` fails the degree condition, since its
degree equals `deg (X+1)² = 2`. -/
theorem example_Uhat : Uhat ((X : ℚ[X]) + 1) 1 (1 - X) 1 2 = 2 - X ^ 2 := by
  unfold Uhat S
  simp [Finset.sum_range_succ]
  ring

theorem example_degree_Uhat :
    (Uhat ((X : ℚ[X]) + 1) 1 (1 - X) 1 2).degree = (((X : ℚ[X]) + 1) ^ 2).degree := by
  rw [example_Uhat]
  have h1 : (2 - X ^ 2 : ℚ[X]).degree = 2 := by compute_degree!
  have h2 : (((X : ℚ[X]) + 1) ^ 2).degree = 2 := by compute_degree!
  rw [h1, h2]

/-- The normalized coefficients of the example: `U_{1,2} = 2X + 3` and `V_{1,2} = 1 - 2X`. -/
theorem example_Unorm : Unorm ((X : ℚ[X]) + 1) 1 (1 - X) 1 2 = 2 * X + 3 := by
  have hb : ((X : ℚ[X]) + 1) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro hzero
    simpa using congrArg (Polynomial.eval (0 : ℚ)) hzero
  have hdeg : (2 * X + 3 : ℚ[X]).degree < (((X : ℚ[X]) + 1) ^ 2).degree := by
    have h1 : (2 * X + 3 : ℚ[X]).degree ≤ 1 := by compute_degree
    have h2 : (((X : ℚ[X]) + 1) ^ 2).degree = 2 := by compute_degree!
    rw [h2]
    exact lt_of_le_of_lt h1 (by norm_num)
  unfold Unorm
  rw [example_Uhat]
  exact mod_eq_of_eq_mul_add (Q := -1) hb (by ring) hdeg

theorem example_Vnorm : Vnorm (X ^ 2 : ℚ[X]) (X + 1) 1 (1 - X) 1 2 = 1 - 2 * X := by
  have hb : ((X : ℚ[X]) + 1) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro hzero
    simpa using congrArg (Polynomial.eval (0 : ℚ)) hzero
  have h := bezout_norm (X ^ 2 : ℚ[X]) (X + 1) 1 (1 - X) (by ring) one_pos two_pos
  rw [example_Unorm] at h
  have hne : (((X : ℚ[X]) + 1) ^ 2) * (Vnorm (X ^ 2 : ℚ[X]) (X + 1) 1 (1 - X) 1 2 - (1 - 2 * X))
      = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 hne with h1 | h1
  · exact absurd h1 hb
  · linear_combination h1

/-! ## 7. The degenerate case of a constant `B` -/

/-- If `B` is a nonzero constant, the normalized pair is `(0, B⁻ⁿ)`, i.e. `U_{m,n} = 0`
and `Bⁿ V_{m,n} = 1`. -/
theorem const_B_case (A B U V : K[X]) (hBdeg : B.degree = 0) (hUV : A * U + B * V = 1)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Unorm B U V m n = 0 ∧ B ^ n * Vnorm A B U V m n = 1 := by
  have hB : B ≠ 0 := fun h => by simp [h] at hBdeg
  have hdeg : (Unorm B U V m n).degree < (B ^ n).degree := degree_Unorm_lt B U V hB m n
  have hBn : (B ^ n).degree = 0 := by rw [Polynomial.degree_pow, hBdeg]; simp
  rw [hBn] at hdeg
  have hzero : Unorm B U V m n = 0 :=
    Polynomial.degree_eq_bot.1 (Nat.WithBot.lt_zero_iff.1 hdeg)
  refine ⟨hzero, ?_⟩
  have h := bezout_norm A B U V hUV hm hn
  rw [hzero] at h
  linear_combination h

end Q604
