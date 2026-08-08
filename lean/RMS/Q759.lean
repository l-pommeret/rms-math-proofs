import Mathlib

/-!
# Q759

Let `E = C^∞([-1,1];ℝ)` with the seminorms `h ↦ ‖h^{(k)}‖_∞`.  For a sequence `(f n)` in `E`
and `g ∈ E`, `(f n) ⇒ g` means `∀ k, ‖f n ^{(k)} - g ^{(k)}‖_∞ → 0`.

With
`α x = exp (-x^2/(1-x^2))` for `|x| < 1` and `α (±1) = 0`,
the two sequences

* `f_n^{(a)} x = exp (-(x^2 + x^4 + ⋯ + x^{2n}))`
* `f_n^{(b)} x = (1 - (x^2 + x^4 + ⋯ + x^{2n})/n)^n`

both satisfy `f_n ⇒ α`.

This file proves both statements: `Q759_a`/`Q759_a'` for the first sequence and
`Q759_b`/`Q759_b'` for the second.

## Versions

Lean `leanprover/lean4:v4.28.0`, mathlib revision `v4.28.0`
(commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`), as pinned by `lean-toolchain`
and `lake-manifest.json`.

## Formalization choices and mismatches with the printed statement

* The printed `α` is defined by cases on `[-1,1]`.  Here `alph` is defined on all of `ℝ` by
  `alph x = exp 1 * expNegInvGlue (1 - x^2)`, which is smooth on `ℝ`; the lemmas
  `alph_eq_of_abs_lt_one`, `alph_one` and `alph_neg_one` show that it agrees with the printed
  definition on `[-1,1]`.  This makes the smoothness of `α` on the closed interval available
  from mathlib rather than requiring a separate endpoint argument.
* Derivatives on the closed interval `[-1,1]` are expressed with
  `iteratedDerivWithin k · (Set.Icc (-1) 1)`, which is the standard mathlib notion of a
  derivative of a function defined on a closed interval; on `Icc (-1) 1` it coincides with the
  ordinary iterated derivative of the (globally smooth) functions involved.
* Convergence `f_n ⇒ α` is formalized as: for each fixed `k`, the `k`-th derivatives converge
  uniformly on `[-1,1]` (`Q759_a'`, `Q759_b'`), equivalently in the `ε`-form `Q759_a`, `Q759_b`.
  This is exactly the printed statement `∀ k, ‖f_n^{(k)} - α^{(k)}‖_∞ → 0`.
* The quantitative rates mentioned in the source discussion (`O_{k,M}(n^{-M})` for (a) and
  `O_k(n^{-1})` for (b), together with their sharpness) are *not* formalized here; only the
  convergence statements, which are the assertions of the problem, are proved.
-/

namespace Q759

open Real Set Filter Topology
open scoped BigOperators

/-! ## Definitions -/

/-- `S n x = x^2 + x^4 + ⋯ + x^{2n}`. -/
noncomputable def S (n : ℕ) (x : ℝ) : ℝ := ∑ j ∈ Finset.range n, x ^ (2 * (j + 1))

/-- The first sequence, `f_n^{(a)} x = exp (-(x^2 + ⋯ + x^{2n}))`. -/
noncomputable def fa (n : ℕ) (x : ℝ) : ℝ := Real.exp (-(S n x))

/-- The second sequence, `f_n^{(b)} x = (1 - (x^2 + ⋯ + x^{2n})/n)^n`. -/
noncomputable def fb (n : ℕ) (x : ℝ) : ℝ := (1 - S n x / n) ^ n

/-- The limit function `α`, written as a globally smooth function on `ℝ`. -/
noncomputable def alph (x : ℝ) : ℝ := Real.exp 1 * expNegInvGlue (1 - x ^ 2)

/-! ## The limit function agrees with the one in the statement -/

lemma alph_eq_of_abs_lt_one {x : ℝ} (hx : |x| < 1) :
    alph x = Real.exp (-(x ^ 2 / (1 - x ^ 2))) := by
  have h1 : x ^ 2 < 1 := by nlinarith [abs_nonneg x, sq_abs x, abs_lt.1 hx]
  have h2 : (0:ℝ) < 1 - x ^ 2 := by linarith
  unfold alph expNegInvGlue
  rw [if_neg (by linarith), ← Real.exp_add]
  congr 1
  field_simp
  ring

lemma alph_one : alph 1 = 0 := by
  unfold alph; rw [expNegInvGlue.zero_of_nonpos (by norm_num)]; ring

lemma alph_neg_one : alph (-1) = 0 := by
  unfold alph; rw [expNegInvGlue.zero_of_nonpos (by norm_num)]; ring

lemma alph_contDiff : ContDiff ℝ (⊤ : ℕ∞) alph := by
  unfold alph
  exact contDiff_const.mul (expNegInvGlue.contDiff.comp (by fun_prop))

lemma alph_nonneg (x : ℝ) : 0 ≤ alph x :=
  mul_nonneg (Real.exp_nonneg 1) (expNegInvGlue.nonneg _)

/-! ## Sums of the form `∑ j^r t^j` -/

/-- `Dsum r n t = ∑_{j=1}^n j^r t^j`. -/
noncomputable def Dsum (r n : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, ((j : ℝ) + 1) ^ r * t ^ (j + 1)

lemma Dsum_nonneg (r n : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Dsum r n t := by
  apply Finset.sum_nonneg; intro j _; positivity

lemma Dsum_mono_t (r n : ℕ) {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    Dsum r n t ≤ Dsum r n u := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht htu _) (by positivity)

lemma Dsum_succ (r n : ℕ) (t : ℝ) :
    Dsum r (n + 1) t = Dsum r n t + ((n : ℝ) + 1) ^ r * t ^ (n + 1) := by
  simp [Dsum, Finset.sum_range_succ]

lemma real_pow_ineq (N r : ℕ) :
    ((N : ℝ) + 1) ^ (r + 1) ≤ (N : ℝ) ^ (r + 1) + ((r : ℝ) + 1) * ((N : ℝ) + 1) ^ r := by
  have h : (N + 1) ^ (r + 1) ≤ N ^ (r + 1) + (r + 1) * (N + 1) ^ r := by
    induction r with
    | zero => simp
    | succ r ih =>
        calc (N + 1) ^ (r + 2) = (N + 1) * (N + 1) ^ (r + 1) := by ring
          _ ≤ (N + 1) * (N ^ (r + 1) + (r + 1) * (N + 1) ^ r) := Nat.mul_le_mul_left _ ih
          _ = N ^ (r + 2) + N ^ (r + 1) + (r + 1) * (N + 1) ^ (r + 1) := by ring
          _ ≤ N ^ (r + 2) + (N + 1) ^ (r + 1) + (r + 1) * (N + 1) ^ (r + 1) := by gcongr; omega
          _ = N ^ (r + 2) + (r + 2) * (N + 1) ^ (r + 1) := by ring
  have h2 : (((N + 1) ^ (r + 1) : ℕ) : ℝ) ≤ ((N ^ (r + 1) + (r + 1) * (N + 1) ^ r : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h2
  linarith

lemma Dsum_succ_le_aux (r n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) :
    (1 - t) * Dsum (r + 1) n t ≤ ((r : ℝ) + 1) * Dsum r n t - (n : ℝ) ^ (r + 1) * t ^ (n + 1) := by
  induction n with
  | zero => simp [Dsum]
  | succ n ih =>
      rw [Dsum_succ, Dsum_succ]
      have hp : (0:ℝ) ≤ t ^ (n + 1) := pow_nonneg ht0 _
      have h1 : ((n : ℝ) + 1) ^ (r + 1) - (n : ℝ) ^ (r + 1) ≤ ((r : ℝ) + 1) * ((n : ℝ) + 1) ^ r := by
        have := real_pow_ineq n r; linarith
      have h2 : (((n : ℝ) + 1) ^ (r + 1) - (n : ℝ) ^ (r + 1)) * t ^ (n + 1)
          ≤ ((r : ℝ) + 1) * ((n : ℝ) + 1) ^ r * t ^ (n + 1) :=
        mul_le_mul_of_nonneg_right h1 hp
      have h3 : t ^ (n + 1 + 1) = t * t ^ (n + 1) := by ring
      push_cast
      rw [h3]
      nlinarith [ih]

lemma Dsum_succ_le (r n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) :
    (1 - t) * Dsum (r + 1) n t ≤ ((r : ℝ) + 1) * Dsum r n t := by
  have := Dsum_succ_le_aux r n ht0
  have h : (0:ℝ) ≤ (n : ℝ) ^ (r + 1) * t ^ (n + 1) := by positivity
  linarith

lemma Dsum_zero_le_inv (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Dsum 0 n t ≤ 1 / (1 - t) := by
  have h : Dsum 0 n t = ∑ j ∈ Finset.range n, t ^ (j + 1) := by simp [Dsum]
  have h2 : ∑ j ∈ Finset.range n, t ^ (j + 1) = t * ∑ j ∈ Finset.range n, t ^ j := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have h3 : (t ^ n - 1) / (t - 1) = (1 - t ^ n) / (1 - t) := by
    rw [← neg_sub 1 (t ^ n), ← neg_sub 1 t, neg_div_neg_eq]
  rw [h, h2, geom_sum_eq (by linarith), h3]
  have hn : t ^ n ≤ 1 := pow_le_one₀ ht0 (le_of_lt ht1)
  have hn0 : (0:ℝ) ≤ t ^ n := pow_nonneg ht0 _
  rw [mul_div_assoc']
  gcongr
  · linarith
  · nlinarith

lemma Dsum_le_inv (r n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Dsum r n t ≤ (Nat.factorial r : ℝ) / (1 - t) ^ (r + 1) := by
  induction r with
  | zero => simpa using Dsum_zero_le_inv n ht0 ht1
  | succ r ih =>
      have h0 : (0:ℝ) < 1 - t := by linarith
      have h1 := Dsum_succ_le r n ht0
      have h2 : ((r : ℝ) + 1) * Dsum r n t
          ≤ ((r : ℝ) + 1) * ((Nat.factorial r : ℝ) / (1 - t) ^ (r + 1)) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      have h3 : (1 - t) * Dsum (r + 1) n t
          ≤ ((r : ℝ) + 1) * ((Nat.factorial r : ℝ) / (1 - t) ^ (r + 1)) := le_trans h1 h2
      rw [le_div_iff₀ (by positivity)]
      have hpow : (1 - t) ^ (r + 1 + 1) = (1 - t) ^ (r + 1) * (1 - t) := by ring
      rw [hpow]
      have hre : Dsum (r + 1) n t * ((1 - t) ^ (r + 1) * (1 - t))
          = ((1 - t) * Dsum (r + 1) n t) * (1 - t) ^ (r + 1) := by ring
      rw [hre]
      calc ((1 - t) * Dsum (r + 1) n t) * (1 - t) ^ (r + 1)
          ≤ (((r : ℝ) + 1) * ((Nat.factorial r : ℝ) / (1 - t) ^ (r + 1))) * (1 - t) ^ (r + 1) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = ((r : ℝ) + 1) * (Nat.factorial r : ℝ) := by field_simp
        _ = (Nat.factorial (r + 1) : ℝ) := by rw [Nat.factorial_succ]; push_cast; ring

lemma Dsum_le_pow (r n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Dsum r n t ≤ (n : ℝ) ^ (r + 1) := by
  have h : Dsum r n t ≤ ∑ _j ∈ Finset.range n, (n : ℝ) ^ r := by
    apply Finset.sum_le_sum
    intro j hj
    have hj' : (j : ℝ) + 1 ≤ n := by
      have := Finset.mem_range.1 hj; exact_mod_cast this
    have h1 : ((j : ℝ) + 1) ^ r ≤ (n : ℝ) ^ r := pow_le_pow_left₀ (by positivity) hj' _
    have h2 : t ^ (j + 1) ≤ 1 := pow_le_one₀ ht0 ht1
    calc ((j : ℝ) + 1) ^ r * t ^ (j + 1) ≤ ((j : ℝ) + 1) ^ r * 1 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ((j : ℝ) + 1) ^ r := by ring
      _ ≤ (n : ℝ) ^ r := h1
  simpa [Finset.sum_const, pow_succ, mul_comm] using h

lemma floor_ge_half {y : ℝ} (hy : 1 ≤ y) : y / 2 ≤ (⌊y⌋₊ : ℝ) := by
  rcases le_or_gt 2 y with h | h
  · have := Nat.lt_floor_add_one y
    linarith
  · have h1 : 1 ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast (Nat.one_le_floor_iff y).mpr hy
    linarith

lemma min_le_Dsum_zero (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    min (n : ℝ) (1 / (1 - t)) ≤ 8 * (1 + Dsum 0 n t) := by
  have hP : 0 ≤ Dsum 0 n t := Dsum_nonneg 0 n ht0
  set δ : ℝ := 1 - t with hδ
  have hδ0 : 0 < δ := by simp [hδ]; linarith
  rcases le_or_gt t (1 / 2) with hc | hc
  · have h2 : 1 / δ ≤ 2 := by
      rw [div_le_iff₀ hδ0]; simp [hδ]; linarith
    calc min (n : ℝ) (1 / δ) ≤ 1 / δ := min_le_right _ _
      _ ≤ 2 := h2
      _ ≤ 8 * (1 + Dsum 0 n t) := by linarith
  · have hδhalf : δ < 1 / 2 := by simp [hδ]; linarith
    set y : ℝ := 1 / (2 * δ) with hy
    have hy1 : 1 ≤ y := by
      rw [hy, le_div_iff₀ (by linarith)]; linarith
    set m : ℕ := ⌊y⌋₊ with hm
    have hmy : (m : ℝ) ≤ y := Nat.floor_le (by linarith)
    have hmy2 : y / 2 ≤ (m : ℝ) := floor_ge_half hy1
    set m' : ℕ := min m n with hm'
    have hm'm : (m' : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.min_le_left m n
    have hm'n : m' ≤ n := Nat.min_le_right m n
    have hbern : 1 - (m' : ℝ) * δ ≤ t ^ m' := by
      have h := one_add_mul_le_pow (a := -δ) (by linarith) m'
      have ht : (1 : ℝ) + -δ = t := by simp [hδ]
      rw [ht] at h
      linarith [h]
    have hmδ : (m' : ℝ) * δ ≤ 1 / 2 := by
      have hle : (m' : ℝ) ≤ y := le_trans hm'm hmy
      calc (m' : ℝ) * δ ≤ y * δ := by nlinarith
        _ = 1 / 2 := by rw [hy]; field_simp
    have htm : (1:ℝ) / 2 ≤ t ^ m' := by linarith
    have hsum : (m' : ℝ) * t ^ m' ≤ Dsum 0 n t := by
      have h1 : ∑ j ∈ Finset.range m', t ^ (j + 1) ≤ Dsum 0 n t := by
        have hD : Dsum 0 n t = ∑ j ∈ Finset.range n, t ^ (j + 1) := by simp [Dsum]
        rw [hD]
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hm'n)
        intro j _ _; positivity
      have h2 : (m' : ℝ) * t ^ m' ≤ ∑ j ∈ Finset.range m', t ^ (j + 1) := by
        have hterm : ∀ j ∈ Finset.range m', t ^ m' ≤ t ^ (j + 1) := by
          intro j hj
          apply pow_le_pow_of_le_one ht0 (le_of_lt ht1)
          have := Finset.mem_range.1 hj; omega
        calc (m' : ℝ) * t ^ m' = ∑ _j ∈ Finset.range m', t ^ m' := by
              rw [Finset.sum_const, Finset.card_range]; simp [mul_comm]
          _ ≤ ∑ j ∈ Finset.range m', t ^ (j + 1) := Finset.sum_le_sum hterm
      linarith
    have hPm : (m' : ℝ) / 2 ≤ Dsum 0 n t := by nlinarith [Nat.cast_nonneg (α := ℝ) m']
    have hmin : min (n : ℝ) (1 / δ) ≤ 4 * (m' : ℝ) := by
      rcases le_total m n with h | h
      · have hmm : (m' : ℝ) = m := by rw [hm', Nat.min_eq_left h]
        rw [hmm]
        calc min (n : ℝ) (1 / δ) ≤ 1 / δ := min_le_right _ _
          _ = 2 * y := by rw [hy]; field_simp
          _ ≤ 4 * (m : ℝ) := by linarith
      · have hmm : (m' : ℝ) = n := by rw [hm', Nat.min_eq_right h]
        rw [hmm]
        calc min (n : ℝ) (1 / δ) ≤ (n : ℝ) := min_le_left _ _
          _ ≤ 4 * (n : ℝ) := by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
    linarith

/-- The key estimate: `∑_{j≤n} j^r t^j ≤ C_r (1 + ∑_{j≤n} t^j)^{r+1}` on `[0,1]`. -/
lemma Dsum_key (r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 →
    Dsum r n t ≤ C * (1 + Dsum 0 n t) ^ (r + 1) := by
  refine ⟨(Nat.factorial r : ℝ) * 8 ^ (r + 1), by positivity, ?_⟩
  intro n t ht0 ht1
  have hfac : (1:ℝ) ≤ (Nat.factorial r : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero r)
  have hC1 : (1:ℝ) ≤ (Nat.factorial r : ℝ) * 8 ^ (r + 1) := by
    have : (1:ℝ) ≤ (8:ℝ) ^ (r + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hP : 0 ≤ Dsum 0 n t := Dsum_nonneg 0 n ht0
  have hPpow : (0:ℝ) ≤ (1 + Dsum 0 n t) ^ (r + 1) := by positivity
  rcases eq_or_lt_of_le ht1 with heq | hlt
  · subst heq
    have h1 : Dsum r n 1 ≤ (n : ℝ) ^ (r + 1) := Dsum_le_pow r n ht0 le_rfl
    have h2 : (n : ℝ) ^ (r + 1) ≤ (1 + Dsum 0 n 1) ^ (r + 1) := by
      apply pow_le_pow_left₀ (by positivity)
      have h3 : Dsum 0 n 1 = (n : ℝ) := by simp [Dsum]
      rw [h3]; linarith
    nlinarith
  · have h1t : (0:ℝ) < 1 - t := by linarith
    have hu0 : (0:ℝ) < 1 / (1 - t) := div_pos one_pos h1t
    have hL : Dsum r n t ≤ (Nat.factorial r : ℝ) * (min (n : ℝ) (1 / (1 - t))) ^ (r + 1) := by
      rcases le_total (1 / (1 - t)) (n : ℝ) with h | h
      · rw [min_eq_right h]
        have hd := Dsum_le_inv r n ht0 hlt
        have heq2 : (Nat.factorial r : ℝ) / (1 - t) ^ (r + 1)
            = (Nat.factorial r : ℝ) * (1 / (1 - t)) ^ (r + 1) := by
          rw [div_pow, one_pow]; field_simp
        linarith [heq2 ▸ hd]
      · rw [min_eq_left h]
        have hd := Dsum_le_pow r n ht0 ht1
        nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) n) (r + 1)]
    have hmin := min_le_Dsum_zero n ht0 hlt
    have hmin0 : 0 ≤ min (n : ℝ) (1 / (1 - t)) := le_min (Nat.cast_nonneg n) (le_of_lt hu0)
    have hpow : (min (n : ℝ) (1 / (1 - t))) ^ (r + 1) ≤ (8 * (1 + Dsum 0 n t)) ^ (r + 1) :=
      pow_le_pow_left₀ hmin0 hmin _
    calc Dsum r n t ≤ (Nat.factorial r : ℝ) * (min (n : ℝ) (1 / (1 - t))) ^ (r + 1) := hL
      _ ≤ (Nat.factorial r : ℝ) * (8 * (1 + Dsum 0 n t)) ^ (r + 1) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = ((Nat.factorial r : ℝ) * 8 ^ (r + 1)) * (1 + Dsum 0 n t) ^ (r + 1) := by
          rw [mul_pow]; ring

/-! ## Derivatives of `S` -/

/-- The `r`-th derivative of `S n`, explicitly. -/
noncomputable def Sd (n r : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (((2 * (j + 1)).descFactorial r : ℕ) : ℝ) * x ^ (2 * (j + 1) - r)

lemma Sd_zero (n : ℕ) : Sd n 0 = S n := by
  funext x; simp [Sd, S]

lemma contDiff_Sd (n r : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (Sd n r) := by
  unfold Sd
  exact ContDiff.sum fun i _ => by fun_prop

lemma contDiff_S (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (S n) := by
  rw [← Sd_zero]; exact contDiff_Sd n 0

lemma iteratedDeriv_S (n r : ℕ) : iteratedDeriv r (S n) = Sd n r := by
  induction r with
  | zero => rw [iteratedDeriv_zero, Sd_zero]
  | succ r ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      show deriv (fun y => ∑ j ∈ Finset.range n,
        (((2 * (j + 1)).descFactorial r : ℕ) : ℝ) * y ^ (2 * (j + 1) - r)) x = _
      rw [deriv_fun_sum (fun i _ => by fun_prop)]
      apply Finset.sum_congr rfl
      intro j _
      rw [deriv_const_mul _ (by fun_prop), deriv_pow_field, Nat.descFactorial_succ]
      push_cast
      rw [Nat.sub_sub]
      ring

lemma S_eq_Dsum (n : ℕ) (x : ℝ) : S n x = Dsum 0 n (x ^ 2) := by
  simp [S, Dsum, pow_mul]

lemma S_nonneg (n : ℕ) (x : ℝ) : 0 ≤ S n x := by
  apply Finset.sum_nonneg; intro j _
  rw [pow_mul]; positivity

lemma S_le_card {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (n : ℕ) : S n x ≤ n := by
  have h : ∀ j ∈ Finset.range n, x ^ (2 * (j + 1)) ≤ 1 := by
    intro j _
    rw [pow_mul]
    apply pow_le_one₀ (by positivity)
    obtain ⟨h1, h2⟩ := hx
    nlinarith
  calc S n x ≤ ∑ _j ∈ Finset.range n, (1:ℝ) := Finset.sum_le_sum h
    _ = n := by simp

lemma pow_sub_le (m r : ℕ) (u : ℝ) (h1 : (1:ℝ) / 2 ≤ u) : u ^ (m - r) ≤ 2 ^ r * u ^ m := by
  have h2r : (0:ℝ) < 2 ^ r := by positivity
  rcases le_total r m with h | h
  · have he : u ^ m = u ^ (m - r) * u ^ r := by rw [← pow_add]; congr 1; omega
    have hur : (1:ℝ) / 2 ^ r ≤ u ^ r := by
      have : ((1:ℝ) / 2) ^ r ≤ u ^ r := pow_le_pow_left₀ (by norm_num) h1 r
      simpa [div_pow, one_div] using this
    have hum : (0:ℝ) ≤ u ^ (m - r) := by positivity
    have h3 : u ^ (m - r) * (1 / 2 ^ r) ≤ u ^ (m - r) * u ^ r :=
      mul_le_mul_of_nonneg_left hur hum
    rw [he]
    calc u ^ (m - r) = 2 ^ r * (u ^ (m - r) * (1 / 2 ^ r)) := by field_simp
      _ ≤ 2 ^ r * (u ^ (m - r) * u ^ r) := by nlinarith
  · have hm : m - r = 0 := by omega
    rw [hm, pow_zero]
    have h4 : (0:ℝ) < 2 ^ m := by positivity
    have h2 : (1:ℝ) / 2 ^ m ≤ u ^ m := by
      have : ((1:ℝ) / 2) ^ m ≤ u ^ m := pow_le_pow_left₀ (by norm_num) h1 m
      simpa [div_pow, one_div] using this
    have h3 : (2:ℝ) ^ m ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) h
    have hum : (0:ℝ) ≤ u ^ m := le_trans (by positivity) h2
    calc (1:ℝ) = 2 ^ m * (1 / 2 ^ m) := by field_simp
      _ ≤ 2 ^ m * u ^ m := mul_le_mul_of_nonneg_left h2 (le_of_lt h4)
      _ ≤ 2 ^ r * u ^ m := mul_le_mul_of_nonneg_right h3 hum

lemma Sd_le_Dsum (n r : ℕ) (x u : ℝ) (hu : (1:ℝ) / 2 ≤ u) (hxu : |x| ≤ u) :
    |Sd n r x| ≤ 4 ^ r * Dsum r n (u ^ 2) := by
  have h1 : |Sd n r x| ≤ ∑ j ∈ Finset.range n,
      (((2 * (j + 1)).descFactorial r : ℕ) : ℝ) * |x| ^ (2 * (j + 1) - r) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro j _
    rw [abs_mul, abs_pow, Nat.abs_cast]
  refine le_trans h1 ?_
  have h2 : ∀ j ∈ Finset.range n,
      (((2 * (j + 1)).descFactorial r : ℕ) : ℝ) * |x| ^ (2 * (j + 1) - r)
      ≤ 4 ^ r * (((j : ℝ) + 1) ^ r * (u ^ 2) ^ (j + 1)) := by
    intro j _
    have hd : (((2 * (j + 1)).descFactorial r : ℕ) : ℝ) ≤ ((2 * (j + 1) : ℕ) : ℝ) ^ r := by
      exact_mod_cast Nat.descFactorial_le_pow (2 * (j + 1)) r
    have hx1 : |x| ^ (2 * (j + 1) - r) ≤ u ^ (2 * (j + 1) - r) :=
      pow_le_pow_left₀ (abs_nonneg x) hxu _
    have hx2 : u ^ (2 * (j + 1) - r) ≤ 2 ^ r * u ^ (2 * (j + 1)) := pow_sub_le _ _ _ hu
    have hu0 : (0:ℝ) ≤ u := by linarith
    calc (((2 * (j + 1)).descFactorial r : ℕ) : ℝ) * |x| ^ (2 * (j + 1) - r)
        ≤ ((2 * (j + 1) : ℕ) : ℝ) ^ r * (2 ^ r * u ^ (2 * (j + 1))) :=
          mul_le_mul hd (le_trans hx1 hx2) (by positivity) (by positivity)
      _ = 4 ^ r * (((j : ℝ) + 1) ^ r * (u ^ 2) ^ (j + 1)) := by
          have h4 : (4:ℝ) ^ r = 2 ^ r * 2 ^ r := by rw [← mul_pow]; norm_num
          push_cast
          rw [pow_mul, mul_pow, h4]
          ring
  refine le_trans (Finset.sum_le_sum h2) (le_of_eq ?_)
  rw [Dsum, Finset.mul_sum]

/-- Lemma 4.1: `|S_n^{(r)}(x)| ≤ C_r (1 + S_n(x))^{r+1}` on `[-1,1]`. -/
lemma Sd_bound (r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : ℝ), x ∈ Icc (-1 : ℝ) 1 →
    |Sd n r x| ≤ C * (1 + S n x) ^ (r + 1) := by
  obtain ⟨Ck, hCk0, hCk⟩ := Dsum_key r
  refine ⟨4 ^ r * Ck + 4 ^ r * ((Nat.factorial r : ℝ) / (3 / 4) ^ (r + 1)), by positivity, ?_⟩
  intro n x hx
  have hS0 : 0 ≤ S n x := S_nonneg n x
  have hSpow1 : (1:ℝ) ≤ (1 + S n x) ^ (r + 1) := one_le_pow₀ (by linarith)
  have hSpow0 : (0:ℝ) ≤ (1 + S n x) ^ (r + 1) := by positivity
  have hx1 : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
  rcases le_total |x| (1 / 2) with hc | hc
  · have h1 := Sd_le_Dsum n r x (1 / 2) le_rfl hc
    have h2 : Dsum r n (((1:ℝ) / 2) ^ 2) ≤ (Nat.factorial r : ℝ) / (1 - ((1:ℝ) / 2) ^ 2) ^ (r + 1) :=
      Dsum_le_inv r n (by norm_num) (by norm_num)
    have h3 : ((1:ℝ) - ((1:ℝ) / 2) ^ 2) = 3 / 4 := by norm_num
    rw [h3] at h2
    have h4 : |Sd n r x| ≤ 4 ^ r * ((Nat.factorial r : ℝ) / (3 / 4) ^ (r + 1)) := by
      refine le_trans h1 ?_
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : (0:ℝ) ≤ 4 ^ r * Ck := by positivity
    have hA : (0:ℝ) ≤ 4 ^ r * ((Nat.factorial r : ℝ) / (3 / 4) ^ (r + 1)) := by positivity
    calc |Sd n r x| ≤ 4 ^ r * ((Nat.factorial r : ℝ) / (3 / 4) ^ (r + 1)) := h4
      _ = 4 ^ r * ((Nat.factorial r : ℝ) / (3 / 4) ^ (r + 1)) * 1 := by ring
      _ ≤ 4 ^ r * ((Nat.factorial r : ℝ) / (3 / 4) ^ (r + 1)) * (1 + S n x) ^ (r + 1) :=
          mul_le_mul_of_nonneg_left hSpow1 hA
      _ ≤ (4 ^ r * Ck + 4 ^ r * ((Nat.factorial r : ℝ) / (3 / 4) ^ (r + 1)))
            * (1 + S n x) ^ (r + 1) := by nlinarith [mul_nonneg h5 hSpow0]
  · have h1 := Sd_le_Dsum n r x |x| (by linarith) le_rfl
    have habs : |x| ^ 2 = x ^ 2 := sq_abs x
    rw [habs] at h1
    have h2 : Dsum r n (x ^ 2) ≤ Ck * (1 + Dsum 0 n (x ^ 2)) ^ (r + 1) :=
      hCk n (x ^ 2) (by positivity) (by nlinarith)
    rw [← S_eq_Dsum] at h2
    have h3 : (0:ℝ) ≤ 4 ^ r * ((Nat.factorial r : ℝ) / (3 / 4) ^ (r + 1)) := by positivity
    calc |Sd n r x| ≤ 4 ^ r * Dsum r n (x ^ 2) := h1
      _ ≤ 4 ^ r * (Ck * (1 + S n x) ^ (r + 1)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (4 ^ r * Ck) * (1 + S n x) ^ (r + 1) := by ring
      _ ≤ (4 ^ r * Ck + 4 ^ r * ((Nat.factorial r : ℝ) / (3 / 4) ^ (r + 1)))
            * (1 + S n x) ^ (r + 1) := by nlinarith

/-! ## A class of families controlled by powers of `1 + S n` -/

/-- `Ctrl d F` says that the family `F n` is, uniformly in `n`, bounded on `[-1,1]` by
`C (1 + S n x)^d`, and that this remains true (with `d` increased) after differentiating. -/
inductive Ctrl : ℕ → (ℕ → ℝ → ℝ) → Prop
  | scalar (c : ℕ → ℝ) (C : ℝ) (hc : ∀ n, |c n| ≤ C) (F : ℕ → ℝ → ℝ)
      (hF : ∀ n x, F n x = c n) : Ctrl 0 F
  | Sderiv (r : ℕ) (F : ℕ → ℝ → ℝ) (hF : ∀ n x, F n x = Sd n (r + 1) x) : Ctrl (r + 2) F
  | add (d : ℕ) (F G H : ℕ → ℝ → ℝ) : Ctrl d F → Ctrl d G →
      (∀ n x, H n x = F n x + G n x) → Ctrl d H
  | mul (d e : ℕ) (F G H : ℕ → ℝ → ℝ) : Ctrl d F → Ctrl e G →
      (∀ n x, H n x = F n x * G n x) → Ctrl (d + e) H
  | mono (d e : ℕ) (F : ℕ → ℝ → ℝ) : Ctrl d F → d ≤ e → Ctrl e F

lemma Ctrl.bound {d : ℕ} {F : ℕ → ℝ → ℝ} (h : Ctrl d F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : ℝ), x ∈ Icc (-1 : ℝ) 1 →
      |F n x| ≤ C * (1 + S n x) ^ d := by
  induction h with
  | scalar c C hc F hF =>
      refine ⟨C, le_trans (abs_nonneg (c 0)) (hc 0), ?_⟩
      intro n x _
      rw [hF n x, pow_zero, mul_one]
      exact hc n
  | Sderiv r F hF =>
      obtain ⟨C, hC0, hC⟩ := Sd_bound (r + 1)
      refine ⟨C, hC0, ?_⟩
      intro n x hx
      rw [hF n x]
      exact hC n x hx
  | add d F G H _ _ hH ihF ihG =>
      obtain ⟨C1, hC10, hC1⟩ := ihF
      obtain ⟨C2, hC20, hC2⟩ := ihG
      refine ⟨C1 + C2, by linarith, ?_⟩
      intro n x hx
      have hS : (0:ℝ) ≤ (1 + S n x) ^ d := by
        have := S_nonneg n x; positivity
      rw [hH n x]
      calc |F n x + G n x| ≤ |F n x| + |G n x| := abs_add_le _ _
        _ ≤ C1 * (1 + S n x) ^ d + C2 * (1 + S n x) ^ d := add_le_add (hC1 n x hx) (hC2 n x hx)
        _ = (C1 + C2) * (1 + S n x) ^ d := by ring
  | mul d e F G H _ _ hH ihF ihG =>
      obtain ⟨C1, hC10, hC1⟩ := ihF
      obtain ⟨C2, hC20, hC2⟩ := ihG
      refine ⟨C1 * C2, by positivity, ?_⟩
      intro n x hx
      have hS0 : (0:ℝ) ≤ 1 + S n x := by have := S_nonneg n x; linarith
      rw [hH n x, abs_mul]
      calc |F n x| * |G n x| ≤ (C1 * (1 + S n x) ^ d) * (C2 * (1 + S n x) ^ e) :=
            mul_le_mul (hC1 n x hx) (hC2 n x hx) (abs_nonneg _) (by positivity)
        _ = (C1 * C2) * (1 + S n x) ^ (d + e) := by rw [pow_add]; ring
  | mono d e F _ hde ih =>
      obtain ⟨C, hC0, hC⟩ := ih
      refine ⟨C, hC0, ?_⟩
      intro n x hx
      have hS1 : (1:ℝ) ≤ 1 + S n x := by have := S_nonneg n x; linarith
      have : (1 + S n x) ^ d ≤ (1 + S n x) ^ e := pow_le_pow_right₀ hS1 hde
      calc |F n x| ≤ C * (1 + S n x) ^ d := hC n x hx
        _ ≤ C * (1 + S n x) ^ e := mul_le_mul_of_nonneg_left this hC0

lemma Ctrl.differentiable {d : ℕ} {F : ℕ → ℝ → ℝ} (h : Ctrl d F) (n : ℕ) :
    Differentiable ℝ (F n) := by
  induction h with
  | scalar c C hc F hF =>
      have : F n = fun _ => c n := funext (hF n)
      rw [this]; exact differentiable_const _
  | Sderiv r F hF =>
      have : F n = Sd n (r + 1) := funext (hF n)
      rw [this]
      exact (contDiff_Sd n (r + 1)).differentiable (by simp)
  | add d F G H _ _ hH ihF ihG =>
      have : H n = fun x => F n x + G n x := funext (hH n)
      rw [this]; exact ihF.add ihG
  | mul d e F G H _ _ hH ihF ihG =>
      have : H n = fun x => F n x * G n x := funext (hH n)
      rw [this]; exact ihF.mul ihG
  | mono d e F _ hde ih => exact ih

lemma Ctrl.deriv {d : ℕ} {F : ℕ → ℝ → ℝ} (h : Ctrl d F) :
    Ctrl (d + 1) (fun n x => _root_.deriv (F n) x) := by
  induction h with
  | scalar c C hc F hF =>
      have hz : ∀ n x, _root_.deriv (F n) x = 0 := by
        intro n x
        have : F n = fun _ => c n := funext (hF n)
        rw [this, deriv_const]
      exact Ctrl.mono 0 1 _ (Ctrl.scalar (fun _ => 0) 0 (by simp) _ hz) (by omega)
  | Sderiv r F hF =>
      have hz : ∀ n x, _root_.deriv (F n) x = Sd n (r + 2) x := by
        intro n x
        have hFn : F n = Sd n (r + 1) := funext (hF n)
        rw [hFn, ← iteratedDeriv_S n (r + 1), ← iteratedDeriv_succ, iteratedDeriv_S]
      exact Ctrl.Sderiv (r + 1) _ hz
  | add d F G H hF hG hH ihF ihG =>
      have hz : ∀ n x, _root_.deriv (H n) x = _root_.deriv (F n) x + _root_.deriv (G n) x := by
        intro n x
        have hHn : H n = fun y => F n y + G n y := funext (hH n)
        rw [hHn, deriv_fun_add (hF.differentiable n x) (hG.differentiable n x)]
      exact Ctrl.add (d + 1) _ _ _ ihF ihG hz
  | mul d e F G H hF hG hH ihF ihG =>
      have hz : ∀ n x, _root_.deriv (H n) x
          = _root_.deriv (F n) x * G n x + F n x * _root_.deriv (G n) x := by
        intro n x
        have hHn : H n = fun y => F n y * G n y := funext (hH n)
        rw [hHn, deriv_fun_mul (hF.differentiable n x) (hG.differentiable n x)]
      refine Ctrl.add (d + e + 1) _ _ _ ?_ ?_ hz
      · exact Ctrl.mono (d + 1 + e) (d + e + 1) _ (Ctrl.mul (d + 1) e _ _ _ ihF hG (fun _ _ => rfl))
          (by omega)
      · exact Ctrl.mono (d + (e + 1)) (d + e + 1) _ (Ctrl.mul d (e + 1) _ _ _ hF ihG (fun _ _ => rfl))
          (by omega)
  | mono d e F _ hde ih => exact Ctrl.mono (d + 1) (e + 1) _ ih (by omega)

/-! ## Uniform bounds for the derivatives of the first sequence -/

lemma poly_exp_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
    (1 + s) ^ d * Real.exp (-(s / 2)) ≤ C := by
  refine ⟨Real.exp (1 / 2) * (2 ^ d * Nat.factorial d), by positivity, ?_⟩
  intro s hs
  set w : ℝ := 1 + s with hw
  have hw0 : 0 ≤ w / 2 := by rw [hw]; linarith
  have h1 : (w / 2) ^ d / (Nat.factorial d) ≤ Real.exp (w / 2) := pow_div_factorial_le_exp _ hw0 d
  have hfac : (0:ℝ) < (Nat.factorial d : ℝ) := by positivity
  have h2 : w ^ d ≤ 2 ^ d * Nat.factorial d * Real.exp (w / 2) := by
    rw [div_le_iff₀ hfac] at h1
    have hdp : (w / 2) ^ d = w ^ d / 2 ^ d := by rw [div_pow]
    rw [hdp, div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ d)] at h1
    calc w ^ d ≤ Real.exp (w / 2) * (Nat.factorial d) * 2 ^ d := h1
      _ = 2 ^ d * Nat.factorial d * Real.exp (w / 2) := by ring
  have hexp : Real.exp (-(s / 2)) = Real.exp (1 / 2) * Real.exp (-(w / 2)) := by
    rw [← Real.exp_add]; congr 1; rw [hw]; ring
  rw [hexp]
  calc w ^ d * (Real.exp (1 / 2) * Real.exp (-(w / 2)))
      ≤ (2 ^ d * Nat.factorial d * Real.exp (w / 2)) * (Real.exp (1 / 2) * Real.exp (-(w / 2))) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = Real.exp (1 / 2) * (2 ^ d * Nat.factorial d) * (Real.exp (w / 2) * Real.exp (-(w / 2))) := by
        ring
    _ = Real.exp (1 / 2) * (2 ^ d * Nat.factorial d) := by rw [← Real.exp_add]; simp

lemma contDiff_fa (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fa n) := by
  unfold fa
  exact Real.contDiff_exp.comp (contDiff_S n).neg

lemma hasDerivAt_S (n : ℕ) (x : ℝ) : HasDerivAt (S n) (Sd n 1 x) x := by
  have hd : DifferentiableAt ℝ (S n) x := ((contDiff_S n).differentiable (by simp)).differentiableAt
  have hS1 : _root_.deriv (S n) x = Sd n 1 x := by rw [← iteratedDeriv_one, iteratedDeriv_S]
  rw [← hS1]; exact hd.hasDerivAt

lemma deriv_fa (n : ℕ) (x : ℝ) : _root_.deriv (fa n) x = -(Sd n 1 x) * fa n x := by
  have h3 : HasDerivAt (fun y => Real.exp (-(S n y))) (Real.exp (-(S n x)) * (-(Sd n 1 x))) x :=
    ((hasDerivAt_S n x).neg).exp
  unfold fa
  rw [h3.deriv]
  ring

lemma fa_iteratedDeriv (r : ℕ) : ∃ (d : ℕ) (g : ℕ → ℝ → ℝ), Ctrl d g ∧
    ∀ n x, iteratedDeriv r (fa n) x = fa n x * g n x := by
  induction r with
  | zero =>
      refine ⟨0, fun _ _ => 1, Ctrl.scalar (fun _ => 1) 1 (by simp) _ (fun _ _ => rfl), ?_⟩
      intro n x; simp
  | succ r ih =>
      obtain ⟨d, g, hg, hgeq⟩ := ih
      have hSd : Ctrl 2 (fun n x => -(Sd n 1 x)) := by
        have h1 : Ctrl 0 (fun (_ : ℕ) (_ : ℝ) => (-1:ℝ)) :=
          Ctrl.scalar (fun _ => -1) 1 (by simp) _ (fun _ _ => rfl)
        have h2 : Ctrl 2 (fun n x => Sd n 1 x) := Ctrl.Sderiv 0 _ (fun _ _ => rfl)
        exact Ctrl.mul 0 2 _ _ _ h1 h2 (fun n x => by ring)
      have hB : Ctrl (2 + d) (fun n x => -(Sd n 1 x) * g n x) :=
        Ctrl.mul 2 d _ _ _ hSd hg (fun _ _ => rfl)
      have hC : Ctrl (d + 1) (fun n x => _root_.deriv (g n) x) := hg.deriv
      have hnew : Ctrl (d + 2) (fun n x => -(Sd n 1 x) * g n x + _root_.deriv (g n) x) :=
        Ctrl.add (d + 2) _ _ _ (Ctrl.mono (2 + d) (d + 2) _ hB (by omega))
          (Ctrl.mono (d + 1) (d + 2) _ hC (by omega)) (fun _ _ => rfl)
      refine ⟨d + 2, _, hnew, ?_⟩
      intro n x
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv r (fa n) = fun y => fa n y * g n y := funext (hgeq n)
      rw [heq]
      have hfad : DifferentiableAt ℝ (fa n) x :=
        ((contDiff_fa n).differentiable (by simp)).differentiableAt
      have hgd : DifferentiableAt ℝ (g n) x := (hg.differentiable n).differentiableAt
      rw [deriv_fun_mul hfad hgd, deriv_fa]
      ring

lemma fa_deriv_bounded (r : ℕ) : ∃ C : ℝ, ∀ (n : ℕ) (x : ℝ), x ∈ Icc (-1 : ℝ) 1 →
    |iteratedDeriv r (fa n) x| ≤ C := by
  obtain ⟨d, g, hg, hgeq⟩ := fa_iteratedDeriv r
  obtain ⟨Cg, hCg0, hCg⟩ := hg.bound
  obtain ⟨Cp, hCp0, hCp⟩ := poly_exp_bound d
  refine ⟨Cg * Cp, ?_⟩
  intro n x hx
  have hS0 : 0 ≤ S n x := S_nonneg n x
  have hfa : fa n x = Real.exp (-(S n x)) := rfl
  have hfapos : 0 < fa n x := by rw [hfa]; exact Real.exp_pos _
  have hfale : fa n x ≤ Real.exp (-(S n x / 2)) := by
    rw [hfa]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [hgeq n x, abs_mul, abs_of_pos hfapos]
  calc fa n x * |g n x| ≤ Real.exp (-(S n x / 2)) * (Cg * (1 + S n x) ^ d) :=
        mul_le_mul hfale (hCg n x hx) (abs_nonneg _) (le_of_lt (Real.exp_pos _))
    _ = Cg * ((1 + S n x) ^ d * Real.exp (-(S n x / 2))) := by ring
    _ ≤ Cg * Cp := mul_le_mul_of_nonneg_left (hCp _ hS0) hCg0

/-! ## Uniform bounds for the derivatives of the second sequence -/

/-- A family which, for large `n`, is a finite sum of terms
`(1 - S n x / n)^{n-m} * g n x` with `g` controlled. -/
inductive CB : (ℕ → ℝ → ℝ) → Prop
  | gen (m d : ℕ) (g F : ℕ → ℝ → ℝ) : Ctrl d g →
      (∀ n, m < n → ∀ x, F n x = (1 - S n x / n) ^ (n - m) * g n x) → CB F
  | add (N : ℕ) (F G H : ℕ → ℝ → ℝ) : CB F → CB G →
      (∀ n, N < n → ∀ x, H n x = F n x + G n x) → CB H

/-- `W n x = 1 - S n x / n`. -/
lemma hasDerivAt_W (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => 1 - S n y / (n : ℝ)) (-(Sd n 1 x / (n : ℝ))) x :=
  ((hasDerivAt_S n x).div_const (n : ℝ)).const_sub 1

lemma W_mem {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 ≤ 1 - S n x / (n : ℝ) ∧ 1 - S n x / (n : ℝ) ≤ 1 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have h1 : 0 ≤ S n x := S_nonneg n x
  have h2 : S n x ≤ n := S_le_card hx n
  constructor
  · have : S n x / (n : ℝ) ≤ 1 := by rw [div_le_one hn']; exact h2
    linarith
  · have : 0 ≤ S n x / (n : ℝ) := by positivity
    linarith

lemma differentiable_W (n : ℕ) : Differentiable ℝ (fun y => 1 - S n y / (n : ℝ)) :=
  fun x => (hasDerivAt_W n x).differentiableAt

lemma CB.differentiable {F : ℕ → ℝ → ℝ} (h : CB F) :
    ∃ N : ℕ, ∀ n, N < n → Differentiable ℝ (F n) := by
  induction h with
  | gen m d g F hg hF =>
      refine ⟨m, fun n hn => ?_⟩
      have hFn : F n = fun x => (1 - S n x / (n : ℝ)) ^ (n - m) * g n x := funext (hF n hn)
      rw [hFn]
      exact ((differentiable_W n).pow _).mul (hg.differentiable n)
  | add N F G H _ _ hH ihF ihG =>
      obtain ⟨N1, h1⟩ := ihF
      obtain ⟨N2, h2⟩ := ihG
      refine ⟨max N (max N1 N2), fun n hn => ?_⟩
      have hn1 : N < n := lt_of_le_of_lt (le_max_left _ _) hn
      have hn2 : N1 < n := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right N _)) hn
      have hn3 : N2 < n := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right N _)) hn
      have hHn : H n = fun x => F n x + G n x := funext (hH n hn1)
      rw [hHn]
      exact (h1 n hn2).add (h2 n hn3)

lemma CB.bound {F : ℕ → ℝ → ℝ} (h : CB F) :
    ∃ (C : ℝ) (N : ℕ), ∀ n, N < n → ∀ x ∈ Icc (-1 : ℝ) 1, |F n x| ≤ C := by
  induction h with
  | gen m d g F hg hF =>
      obtain ⟨Cg, hCg0, hCg⟩ := hg.bound
      obtain ⟨Cp, hCp0, hCp⟩ := poly_exp_bound d
      refine ⟨Cg * Cp, 2 * m, fun n hn x hx => ?_⟩
      have hn0 : 0 < n := by omega
      have hnm : m < n := by omega
      have hn' : (0:ℝ) < n := by exact_mod_cast hn0
      obtain ⟨hW0, hW1⟩ := W_mem hn0 hx
      have hS0 : 0 ≤ S n x := S_nonneg n x
      have hstep : (1 - S n x / (n : ℝ)) ^ (n - m) ≤ Real.exp (-(S n x / 2)) := by
        have h1 : (1 - S n x / (n : ℝ)) ≤ Real.exp (-(S n x / (n : ℝ))) := by
          have := Real.add_one_le_exp (-(S n x / (n : ℝ)))
          linarith
        have h2 : (1 - S n x / (n : ℝ)) ^ (n - m)
            ≤ (Real.exp (-(S n x / (n : ℝ)))) ^ (n - m) := pow_le_pow_left₀ hW0 h1 _
        have h3 : (Real.exp (-(S n x / (n : ℝ)))) ^ (n - m)
            = Real.exp (((n - m : ℕ) : ℝ) * (-(S n x / (n : ℝ)))) := by
          rw [← Real.exp_nat_mul]
        have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := Nat.cast_sub (le_of_lt hnm)
        have h4 : ((n - m : ℕ) : ℝ) * (-(S n x / (n : ℝ))) ≤ -(S n x / 2) := by
          rw [hcast]
          have hm2 : (m : ℝ) ≤ (n : ℝ) / 2 := by
            have : 2 * m ≤ n := by omega
            have : (2 : ℝ) * m ≤ n := by exact_mod_cast this
            linarith
          have hhalf : (n : ℝ) / 2 ≤ (n : ℝ) - (m : ℝ) := by linarith
          have hSdiv : 0 ≤ S n x / (n : ℝ) := by positivity
          have := mul_le_mul_of_nonneg_right hhalf hSdiv
          have hfin : (n : ℝ) / 2 * (S n x / (n : ℝ)) = S n x / 2 := by field_simp
          rw [hfin] at this
          nlinarith
        calc (1 - S n x / (n : ℝ)) ^ (n - m) ≤ (Real.exp (-(S n x / (n : ℝ)))) ^ (n - m) := h2
          _ = Real.exp (((n - m : ℕ) : ℝ) * (-(S n x / (n : ℝ)))) := h3
          _ ≤ Real.exp (-(S n x / 2)) := Real.exp_le_exp.mpr h4
      rw [hF n hnm x, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 - S n x / (n : ℝ)) ^ (n - m))]
      calc (1 - S n x / (n : ℝ)) ^ (n - m) * |g n x|
          ≤ Real.exp (-(S n x / 2)) * (Cg * (1 + S n x) ^ d) :=
            mul_le_mul hstep (hCg n x hx) (abs_nonneg _) (le_of_lt (Real.exp_pos _))
        _ = Cg * ((1 + S n x) ^ d * Real.exp (-(S n x / 2))) := by ring
        _ ≤ Cg * Cp := mul_le_mul_of_nonneg_left (hCp _ hS0) hCg0
  | add N F G H _ _ hH ihF ihG =>
      obtain ⟨C1, N1, h1⟩ := ihF
      obtain ⟨C2, N2, h2⟩ := ihG
      refine ⟨C1 + C2, max N (max N1 N2), fun n hn x hx => ?_⟩
      have hn1 : N < n := lt_of_le_of_lt (le_max_left _ _) hn
      have hn2 : N1 < n := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right N _)) hn
      have hn3 : N2 < n := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right N _)) hn
      rw [hH n hn1 x]
      exact (abs_add_le _ _).trans (add_le_add (h1 n hn2 x hx) (h2 n hn3 x hx))

lemma CB.deriv {F : ℕ → ℝ → ℝ} (h : CB F) : CB (fun n x => _root_.deriv (F n) x) := by
  induction h with
  | gen m d g F hg hF =>
      have hc : ∀ n : ℕ, |((n - m : ℕ) : ℝ) / (n : ℝ)| ≤ 1 := by
        intro n
        rcases Nat.eq_zero_or_pos n with hn | hn
        · simp [hn]
        · have hn' : (0:ℝ) < n := by exact_mod_cast hn
          have h1 : ((n - m : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast Nat.sub_le n m
          have h0 : (0:ℝ) ≤ ((n - m : ℕ) : ℝ) := Nat.cast_nonneg _
          rw [abs_of_nonneg (by positivity)]
          rw [div_le_one hn']
          exact h1
      have hg1 : Ctrl (0 + 2 + d) (fun n x => (((n - m : ℕ) : ℝ) / (n : ℝ)) * -(Sd n 1 x) * g n x) := by
        have hs : Ctrl 0 (fun (n : ℕ) (_ : ℝ) => ((n - m : ℕ) : ℝ) / (n : ℝ)) :=
          Ctrl.scalar (fun n => ((n - m : ℕ) : ℝ) / (n : ℝ)) 1 hc _ (fun _ _ => rfl)
        have hSd : Ctrl 2 (fun n x => -(Sd n 1 x)) := by
          have h1 : Ctrl 0 (fun (_ : ℕ) (_ : ℝ) => (-1:ℝ)) :=
            Ctrl.scalar (fun _ => -1) 1 (by simp) _ (fun _ _ => rfl)
          have h2 : Ctrl 2 (fun n x => Sd n 1 x) := Ctrl.Sderiv 0 _ (fun _ _ => rfl)
          exact Ctrl.mul 0 2 _ _ _ h1 h2 (fun n x => by ring)
        exact Ctrl.mul (0 + 2) d _ _ _ (Ctrl.mul 0 2 _ _ _ hs hSd (fun _ _ => rfl)) hg
          (fun _ _ => rfl)
      have hCB1 : CB (fun n x => (1 - S n x / (n : ℝ)) ^ (n - (m + 1)) *
          ((((n - m : ℕ) : ℝ) / (n : ℝ)) * -(Sd n 1 x) * g n x)) :=
        CB.gen (m + 1) (0 + 2 + d) _ _ hg1 (fun n _ x => rfl)
      have hCB2 : CB (fun n x => (1 - S n x / (n : ℝ)) ^ (n - m) * _root_.deriv (g n) x) :=
        CB.gen m (d + 1) _ _ hg.deriv (fun n _ x => rfl)
      refine CB.add (m + 1) _ _ _ hCB1 hCB2 ?_
      intro n hn x
      have hnm : m < n := by omega
      have hFn : F n = fun y => (1 - S n y / (n : ℝ)) ^ (n - m) * g n y := funext (hF n hnm)
      have hW := hasDerivAt_W n x
      have hpow : HasDerivAt (fun y => (1 - S n y / (n : ℝ)) ^ (n - m))
          (((n - m : ℕ) : ℝ) * (1 - S n x / (n : ℝ)) ^ (n - m - 1) *
            (-(Sd n 1 x / (n : ℝ)))) x := hW.pow _
      have hgd : HasDerivAt (g n) (_root_.deriv (g n) x) x :=
        ((hg.differentiable n) x).hasDerivAt
      have hmul2 : HasDerivAt (fun y => (1 - S n y / (n : ℝ)) ^ (n - m) * g n y)
          (((n - m : ℕ) : ℝ) * (1 - S n x / (n : ℝ)) ^ (n - m - 1) * (-(Sd n 1 x / (n : ℝ)))
            * g n x + (1 - S n x / (n : ℝ)) ^ (n - m) * _root_.deriv (g n) x) x := hpow.mul hgd
      rw [hFn, hmul2.deriv]
      have hexp : n - m - 1 = n - (m + 1) := by omega
      rw [hexp]
      ring
  | add N F G H hF hG hH ihF ihG =>
      obtain ⟨N1, h1⟩ := hF.differentiable
      obtain ⟨N2, h2⟩ := hG.differentiable
      refine CB.add (max N (max N1 N2)) _ _ _ ihF ihG ?_
      intro n hn x
      have hn1 : N < n := lt_of_le_of_lt (le_max_left _ _) hn
      have hn2 : N1 < n := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right N _)) hn
      have hn3 : N2 < n := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right N _)) hn
      have hHn : H n = fun y => F n y + G n y := funext (hH n hn1)
      rw [hHn, deriv_fun_add ((h1 n hn2) x) ((h2 n hn3) x)]

lemma contDiff_fb (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fb n) := by
  unfold fb
  exact ((contDiff_const.sub ((contDiff_S n).div_const _)).pow n)

lemma CB_fb : CB fb := by
  refine CB.gen 0 0 (fun _ _ => 1) fb (Ctrl.scalar (fun _ => 1) 1 (by simp) _ (fun _ _ => rfl)) ?_
  intro n _ x
  simp [fb]

lemma CB_iteratedDeriv_fb (r : ℕ) : CB (fun n x => iteratedDeriv r (fb n) x) := by
  induction r with
  | zero => simpa using CB_fb
  | succ r ih =>
      have h := ih.deriv
      have heq : (fun n x => _root_.deriv (fun y => iteratedDeriv r (fb n) y) x)
          = fun n x => iteratedDeriv (r + 1) (fb n) x := by
        funext n x
        rw [iteratedDeriv_succ]
      rwa [heq] at h

lemma fb_deriv_bounded (r : ℕ) : ∃ (C : ℝ) (N : ℕ), ∀ n, N < n → ∀ x ∈ Icc (-1 : ℝ) 1,
    |iteratedDeriv r (fb n) x| ≤ C := (CB_iteratedDeriv_fb r).bound

/-! ## Uniform convergence of the functions themselves -/

lemma Dsum_zero_eq (n : ℕ) {t : ℝ} (ht : t ≠ 1) :
    Dsum 0 n t = (t - t ^ (n + 1)) / (1 - t) := by
  have hne1 : (1:ℝ) - t ≠ 0 := by intro h; apply ht; linarith
  have hne2 : t - 1 ≠ 0 := by intro h; apply ht; linarith
  have h6 : Dsum 0 n t = ∑ j ∈ Finset.range n, t ^ (j + 1) := by simp [Dsum]
  have h4 : ∑ j ∈ Finset.range n, t ^ (j + 1) = t * ∑ j ∈ Finset.range n, t ^ j := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  rw [h6, h4, geom_sum_eq ht]
  field_simp
  ring

lemma S_tail {x : ℝ} (hx : x ^ 2 < 1) (n : ℕ) :
    x ^ 2 / (1 - x ^ 2) - S n x = (x ^ 2) ^ (n + 1) / (1 - x ^ 2) := by
  have h1 : (0:ℝ) < 1 - x ^ 2 := by linarith
  have hnet : x ^ 2 ≠ 1 := by intro h; rw [h] at hx; linarith
  rw [S_eq_Dsum, Dsum_zero_eq n hnet, div_sub_div_same]
  congr 1
  ring

lemma S_le_alph_exponent {x : ℝ} (hx : x ^ 2 < 1) (n : ℕ) :
    S n x ≤ x ^ 2 / (1 - x ^ 2) := by
  have h := S_tail hx n
  have h1 : (0:ℝ) < 1 - x ^ 2 := by linarith
  have h2 : (0:ℝ) ≤ (x ^ 2) ^ (n + 1) / (1 - x ^ 2) := by positivity
  linarith

lemma exp_sub_exp_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp (-a) - Real.exp (-b) ≤ b - a := by
  have h1 : Real.exp (-a) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have h2 : 1 - (b - a) ≤ Real.exp (-(b - a)) := by
    have := Real.add_one_le_exp (-(b - a)); linarith
  have h3 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
    rw [← Real.exp_add]; ring_nf
  have h4 : (0:ℝ) < Real.exp (-a) := Real.exp_pos _
  rw [h3]
  nlinarith

lemma fa_sub_alph_le_tail {x : ℝ} (hx : x ^ 2 < 1) (n : ℕ) :
    fa n x - alph x ≤ (x ^ 2) ^ (n + 1) / (1 - x ^ 2) := by
  have habs : |x| < 1 := by
    rw [abs_lt]; constructor <;> nlinarith
  rw [alph_eq_of_abs_lt_one habs]
  have h := exp_sub_exp_le (S_nonneg n x) (S_le_alph_exponent hx n)
  rw [← S_tail hx n]
  exact h

lemma alph_le_fa (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : alph x ≤ fa n x := by
  rcases lt_or_eq_of_le (abs_le.mpr ⟨hx.1, hx.2⟩ : |x| ≤ 1) with h | h
  · have hx2 : x ^ 2 < 1 := by
      have := abs_lt.1 h; nlinarith [this.1, this.2]
    rw [alph_eq_of_abs_lt_one h]
    exact Real.exp_le_exp.mpr (by
      have := S_le_alph_exponent hx2 n
      linarith)
  · have hx2 : x ^ 2 = 1 := by
      rw [← sq_abs, h]; norm_num
    have : alph x = 0 := by
      unfold alph
      rw [expNegInvGlue.zero_of_nonpos (by rw [hx2]; norm_num)]
      ring
    rw [this]
    exact le_of_lt (Real.exp_pos _)

/-- Uniform convergence `f_n^{(a)} → α` on `[-1,1]`. -/
lemma fa_unif (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ Icc (-1 : ℝ) 1, |fa n x - alph x| ≤ ε := by
  set K : ℝ := max 1 (-Real.log ε) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKe : Real.exp (-K) ≤ ε := by
    have h1 : -Real.log ε ≤ K := le_max_right _ _
    have : Real.exp (-K) ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr (by linarith)
    rwa [Real.exp_log hε] at this
  set θ : ℝ := 2 * K / (2 * K + 1) with hθ
  have hKpos : (0:ℝ) < 2 * K + 1 := by linarith
  have hKne : (2 * K + 1 : ℝ) ≠ 0 := ne_of_gt hKpos
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθ1 : θ < 1 := by
    rw [hθ, div_lt_one hKpos]; linarith
  have hθK : θ / (1 - θ) = 2 * K := by
    have : 1 - θ = 1 / (2 * K + 1) := by rw [hθ]; field_simp; ring
    rw [this, hθ]
    field_simp
  have htend : Tendsto (fun n : ℕ => θ ^ (n + 1) / (1 - θ)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => θ ^ (n + 1)) atTop (nhds 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hθ0) hθ1
      exact this.comp (tendsto_add_atTop_nat 1)
    simpa using h1.div_const (1 - θ)
  have hev : ∀ᶠ n in atTop, θ ^ (n + 1) / (1 - θ) ≤ min ε K := by
    have hmin : 0 < min ε K := lt_min hε (by linarith)
    exact (htend.eventually (gt_mem_nhds hmin)).mono (fun n hn => le_of_lt hn)
  filter_upwards [hev] with n hn x hx
  have hxabs : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
  have hnn : 0 ≤ fa n x - alph x := by linarith [alph_le_fa n hx]
  rw [abs_of_nonneg hnn]
  rcases le_total (x ^ 2) θ with hc | hc
  · have hx2lt : x ^ 2 < 1 := lt_of_le_of_lt hc hθ1
    have h1 := fa_sub_alph_le_tail hx2lt n
    have h2 : (x ^ 2) ^ (n + 1) / (1 - x ^ 2) ≤ θ ^ (n + 1) / (1 - θ) := by
      apply div_le_div₀ (by positivity) (pow_le_pow_left₀ (by positivity) hc _) (by linarith)
        (by linarith)
    have h3 : θ ^ (n + 1) / (1 - θ) ≤ ε := le_trans hn (min_le_left _ _)
    linarith
  · have hSge : K ≤ S n x := by
      have h1 : Dsum 0 n θ ≤ Dsum 0 n (x ^ 2) := Dsum_mono_t 0 n (le_of_lt hθ0) hc
      have h2 : Dsum 0 n θ = θ / (1 - θ) - θ ^ (n + 1) / (1 - θ) := by
        rw [Dsum_zero_eq n (ne_of_lt hθ1), div_sub_div_same]
      rw [S_eq_Dsum]
      have h7 : θ ^ (n + 1) / (1 - θ) ≤ K := le_trans hn (min_le_right _ _)
      rw [h2, hθK] at h1
      linarith
    have h8 : fa n x ≤ Real.exp (-K) := by
      unfold fa
      exact Real.exp_le_exp.mpr (by linarith)
    have h9 : 0 ≤ alph x := alph_nonneg x
    linarith

/-- If `0 ≤ b ≤ a` then `a^(m+1) - b^(m+1) ≤ (m+1)(a-b)a^m`. -/
lemma pow_sub_pow_le_mul (m : ℕ) {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) :
    a ^ (m + 1) - b ^ (m + 1) ≤ (m + 1) * (a - b) * a ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ha : 0 ≤ a := le_trans hb hba
    have hbp : b ^ (m + 1) ≤ a ^ (m + 1) := pow_le_pow_left₀ hb hba _
    have key : a ^ (m + 2) - b ^ (m + 2)
        = a * (a ^ (m + 1) - b ^ (m + 1)) + b ^ (m + 1) * (a - b) := by ring
    rw [key]
    have h1 : a * (a ^ (m + 1) - b ^ (m + 1)) ≤ a * ((m + 1) * (a - b) * a ^ m) :=
      mul_le_mul_of_nonneg_left ih ha
    have h2 : b ^ (m + 1) * (a - b) ≤ a ^ (m + 1) * (a - b) :=
      mul_le_mul_of_nonneg_right hbp (by linarith)
    have h3 : a * ((m + 1) * (a - b) * a ^ m) = ((m : ℝ) + 1) * (a - b) * a ^ (m + 1) := by ring
    push_cast
    nlinarith [h1, h2, h3]

/-- `(1 - y/n)^n` is within `C/n` of `exp (-y)` for `0 ≤ y ≤ n`. -/
lemma pow_sub_exp_bound {y : ℝ} {n : ℕ} (hn : 2 ≤ n) (hy : 0 ≤ y) (hyn : y ≤ n) :
    |Real.exp (-y) - (1 - y / n) ^ n| ≤ (y ^ 2 * Real.exp (-(y / 2))) / n := by
  have hN : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hNpos : (0:ℝ) < n := by linarith
  set z : ℝ := y / n with hz
  have hz0 : 0 ≤ z := by positivity
  have hz1 : z ≤ 1 := by rw [hz, div_le_one hNpos]; exact hyn
  set a : ℝ := Real.exp (-z) with ha
  set b : ℝ := 1 - z with hb
  have hb0 : 0 ≤ b := by simp only [hb]; linarith
  have hba : b ≤ a := by
    have := Real.add_one_le_exp (-z)
    simp only [ha, hb]; linarith
  have ha1 : a ≤ 1 := by
    rw [ha]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hexp : Real.exp (-y) = a ^ n := by
    rw [ha, ← Real.exp_nat_mul]
    congr 1
    rw [hz]; field_simp
  have hpow : (1 - y / n) ^ n = b ^ n := by rw [hb, hz]
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmR : (m : ℝ) = (n : ℝ) - 1 := by rw [hm]; push_cast; ring
  have hnonneg : 0 ≤ a ^ n - b ^ n := by
    have := pow_le_pow_left₀ hb0 hba n
    linarith
  rw [hexp, hpow, abs_of_nonneg hnonneg]
  have hkey : a ^ n - b ^ n ≤ (n : ℝ) * (a - b) * a ^ m := by
    have h := pow_sub_pow_le_mul m hb0 hba
    rw [← hm] at h
    calc a ^ n - b ^ n ≤ ((m:ℝ) + 1) * (a - b) * a ^ m := h
      _ = (n:ℝ) * (a - b) * a ^ m := by rw [hmR]; ring
  have hab : a - b ≤ z ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := -z)
      (by rw [abs_neg, abs_of_nonneg hz0]; exact hz1)
    have h2 : Real.exp (-z) - 1 - (-z) ≤ (-z) ^ 2 := (abs_le.1 h).2
    simp only [ha, hb]
    nlinarith
  have ham : a ^ m ≤ Real.exp (-(y / 2)) := by
    have hpe : a ^ m = Real.exp (-(z * m)) := by
      rw [ha, ← Real.exp_nat_mul]; congr 1; ring
    rw [hpe]
    apply Real.exp_le_exp.mpr
    have hzm : y / 2 ≤ z * m := by
      rw [hz, hmR, div_mul_eq_mul_div, le_div_iff₀ hNpos]
      nlinarith
    linarith
  have hapos : 0 ≤ a ^ m := le_of_lt (pow_pos (Real.exp_pos _) m)
  have hstep : (n:ℝ) * (a - b) * a ^ m ≤ (n:ℝ) * z ^ 2 * Real.exp (-(y / 2)) := by
    have h1 : (n:ℝ) * (a - b) ≤ (n:ℝ) * z ^ 2 := by nlinarith
    have h2 : (0:ℝ) ≤ (n:ℝ) * (a - b) := by nlinarith [hba]
    calc (n:ℝ) * (a - b) * a ^ m ≤ (n:ℝ) * (a - b) * Real.exp (-(y / 2)) :=
          mul_le_mul_of_nonneg_left ham h2
      _ ≤ (n:ℝ) * z ^ 2 * Real.exp (-(y / 2)) :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos _))
  have hfin : (n:ℝ) * z ^ 2 * Real.exp (-(y / 2)) = (y ^ 2 * Real.exp (-(y / 2))) / n := by
    rw [hz]; field_simp
  linarith [hkey, hstep, hfin.le, hfin.ge]

lemma fb_sub_fa_unif (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ Icc (-1 : ℝ) 1, |fb n x - fa n x| ≤ ε := by
  obtain ⟨C, hC0, hC⟩ := poly_exp_bound 2
  have htend : Tendsto (fun n : ℕ => C / n) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hev : ∀ᶠ n : ℕ in atTop, C / n ≤ ε :=
    (htend.eventually (gt_mem_nhds hε)).mono fun n hn => hn.le
  filter_upwards [hev, eventually_ge_atTop 2] with n hn hn2 x hx
  have hnR : (0:ℝ) < n := by
    have : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
    linarith
  have hy0 : 0 ≤ S n x := S_nonneg n x
  have hyn : S n x ≤ n := S_le_card hx n
  have h := pow_sub_exp_bound hn2 hy0 hyn
  have hnum : S n x ^ 2 * Real.exp (-(S n x / 2)) ≤ C := by
    refine le_trans ?_ (hC (S n x) hy0)
    have h1 : S n x ^ 2 ≤ (1 + S n x) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos _))
  have hfin : S n x ^ 2 * Real.exp (-(S n x / 2)) / n ≤ C / n := by gcongr
  have hgoal : |Real.exp (-(S n x)) - (1 - S n x / n) ^ n| ≤ ε :=
    le_trans (le_trans h hfin) hn
  show |fb n x - fa n x| ≤ ε
  rw [abs_sub_comm]
  exact hgoal

/-- Uniform convergence `f_n^{(b)} → α` on `[-1,1]`. -/
lemma fb_unif (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ Icc (-1 : ℝ) 1, |fb n x - alph x| ≤ ε := by
  filter_upwards [fb_sub_fa_unif (ε / 2) (by linarith), fa_unif (ε / 2) (by linarith)]
    with n h1 h2 x hx
  have hsum : |fb n x - alph x| ≤ |fb n x - fa n x| + |fa n x - alph x| := by
    have := abs_add_le (fb n x - fa n x) (fa n x - alph x)
    simpa using this
  linarith [h1 x hx, h2 x hx]

/-! ## From uniform convergence to convergence of all derivatives -/

/-- Landau-type interpolation inequality on `[-1,1]`. -/
lemma interp (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v) {ε M h : ℝ} (hM : 0 ≤ M)
    (hh : 0 < h) (hh2 : h ≤ 1)
    (hvb : ∀ x ∈ Icc (-1 : ℝ) 1, |v x| ≤ ε)
    (hv2 : ∀ x ∈ Icc (-1 : ℝ) 1, |_root_.deriv (_root_.deriv v) x| ≤ M) :
    ∀ x ∈ Icc (-1 : ℝ) 1, |_root_.deriv v x| ≤ 2 * ε / h + M * h := by
  have hd : Differentiable ℝ v := hv.differentiable (by simp)
  have hdv : ContDiff ℝ (⊤ : ℕ∞) (_root_.deriv v) :=
    ContDiff.deriv' (n := (⊤ : ℕ∞)) (by simpa using hv)
  have hdd : Differentiable ℝ (_root_.deriv v) := hdv.differentiable (by simp)
  have key : ∀ a b : ℝ, -1 ≤ a → b ≤ 1 → b = a + h → ∀ x, a ≤ x → x ≤ b →
      |_root_.deriv v x| ≤ 2 * ε / h + M * h := by
    intro a b ha hb hab x hxa hxb
    have hlt : a < b := by rw [hab]; linarith
    obtain ⟨c, hc, hceq⟩ := exists_deriv_eq_slope v hlt hd.continuous.continuousOn
      hd.differentiableOn
    have hsub : Icc a b ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc ha hb
    have hcmem : c ∈ Icc (-1 : ℝ) 1 := hsub (Ioo_subset_Icc_self hc)
    have hxmem : x ∈ Icc (-1 : ℝ) 1 := hsub ⟨hxa, hxb⟩
    have hamem : a ∈ Icc (-1 : ℝ) 1 := hsub ⟨le_rfl, le_of_lt hlt⟩
    have hbmem : b ∈ Icc (-1 : ℝ) 1 := hsub ⟨le_of_lt hlt, le_rfl⟩
    have h1 : |_root_.deriv v c| ≤ 2 * ε / h := by
      have hba : b - a = h := by rw [hab]; ring
      have hnum : |v b - v a| ≤ 2 * ε := by
        calc |v b - v a| ≤ |v b| + |v a| := abs_sub _ _
          _ ≤ ε + ε := add_le_add (hvb b hbmem) (hvb a hamem)
          _ = 2 * ε := by ring
      rw [hceq, abs_div, hba, abs_of_pos hh]
      gcongr
    have h2 : |_root_.deriv v x - _root_.deriv v c| ≤ M * h := by
      have hstep : ‖_root_.deriv v x - _root_.deriv v c‖ ≤ M * ‖x - c‖ :=
        Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
          (f' := fun y => _root_.deriv (_root_.deriv v) y)
          (fun y _ => (hdd y).hasDerivAt.hasDerivWithinAt)
          (fun y hy => by simpa [Real.norm_eq_abs] using hv2 y hy)
          (convex_Icc _ _) hcmem hxmem
      have hxc : |x - c| ≤ h := by
        rcases hc with ⟨hc1, hc2⟩
        rw [abs_le]
        constructor <;> [linarith; linarith]
      calc |_root_.deriv v x - _root_.deriv v c| ≤ M * |x - c| := by
            simpa [Real.norm_eq_abs] using hstep
        _ ≤ M * h := by nlinarith
    calc |_root_.deriv v x| ≤ |_root_.deriv v c| + |_root_.deriv v x - _root_.deriv v c| := by
          have := abs_add_le (_root_.deriv v c) (_root_.deriv v x - _root_.deriv v c)
          simpa using this
      _ ≤ 2 * ε / h + M * h := add_le_add h1 h2
  intro x hx
  rcases le_or_gt (x + h) 1 with hcase | hcase
  · exact key x (x + h) hx.1 hcase rfl x le_rfl (by linarith)
  · exact key (x - h) x (by linarith) hx.2 (by ring) x (by linarith) le_rfl

lemma C0_to_Ck (u : ℕ → ℝ → ℝ) (hu : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u n))
    (hbd : ∀ r : ℕ, ∃ M : ℝ, ∀ᶠ n in atTop, ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv r (u n) x| ≤ M)
    (h0 : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ Icc (-1 : ℝ) 1, |u n x| ≤ ε) :
    ∀ (k : ℕ), ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv k (u n) x| ≤ ε := by
  have hcd : ∀ (n k : ℕ), ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv k (u n)) := by
    intro n k
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv k (hu n)
  intro k
  induction k with
  | zero =>
    intro ε hε
    filter_upwards [h0 ε hε] with n hn x hx
    simpa [iteratedDeriv_zero] using hn x hx
  | succ k ih =>
    intro ε hε
    obtain ⟨M, hM⟩ := hbd (k + 2)
    set M' : ℝ := max M 1 with hM'def
    have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
    set h : ℝ := min 1 (ε / (2 * M')) with hhdef
    have hhpos : 0 < h := lt_min one_pos (by positivity)
    have hhle : h ≤ 1 := min_le_left _ _
    have hMh : M' * h ≤ ε / 2 := by
      have : h ≤ ε / (2 * M') := min_le_right _ _
      calc M' * h ≤ M' * (ε / (2 * M')) := by nlinarith
        _ = ε / 2 := by field_simp
    have hε' : 0 < ε * h / 4 := by positivity
    filter_upwards [hM, ih (ε * h / 4) hε'] with n hn hnk x hx
    have hbound := interp (iteratedDeriv k (u n)) (hcd n k) (le_of_lt hM'pos) hhpos hhle
      hnk
      (fun y hy => by
        have : |iteratedDeriv (k + 2) (u n) y| ≤ M := hn y hy
        have heq : iteratedDeriv (k + 2) (u n)
            = _root_.deriv (_root_.deriv (iteratedDeriv k (u n))) := by
          rw [show k + 2 = (k + 1) + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ]
        rw [heq] at this
        exact this.trans (le_max_left _ _))
      x hx
    have heq2 : iteratedDeriv (k + 1) (u n) x = _root_.deriv (iteratedDeriv k (u n)) x := by
      rw [iteratedDeriv_succ]
    rw [heq2]
    have : 2 * (ε * h / 4) / h = ε / 2 := by field_simp; ring
    rw [this] at hbound
    linarith

/-! ## Main results -/

lemma alph_iteratedDeriv_bounded (r : ℕ) :
    ∃ M : ℝ, ∀ x ∈ Icc (-1 : ℝ) 1, |iteratedDeriv r alph x| ≤ M := by
  have hcont : Continuous (iteratedDeriv r alph) :=
    alph_contDiff.continuous_iteratedDeriv r (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩

lemma iteratedDeriv_sub_eq {f g : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (r : ℕ) (x : ℝ) :
    iteratedDeriv r (fun y => f y - g y) x = iteratedDeriv r f x - iteratedDeriv r g x := by
  have h1 : ContDiffAt ℝ (r : ℕ) f x := (hf.of_le (by exact_mod_cast le_top)).contDiffAt
  have h2 : ContDiffAt ℝ (r : ℕ) g x := (hg.of_le (by exact_mod_cast le_top)).contDiffAt
  have := iteratedDeriv_sub h1 h2
  simpa [Pi.sub_def] using this

lemma iteratedDerivWithin_eq_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    iteratedDerivWithin k f (Icc (-1 : ℝ) 1) x = iteratedDeriv k f x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    ((hf.of_le (by exact_mod_cast le_top)).contDiffAt) hx

/-- Generic form of the two main results. -/
lemma main_aux (f : ℕ → ℝ → ℝ) (hf : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (hbd : ∀ r : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ n, N < n → ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv r (f n) x| ≤ C)
    (h0 : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ Icc (-1 : ℝ) 1, |f n x - alph x| ≤ ε) (k : ℕ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDerivWithin k (f n) (Icc (-1 : ℝ) 1) x
        - iteratedDerivWithin k alph (Icc (-1 : ℝ) 1) x| ≤ ε := by
  intro ε hε
  have hu : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (fun x => f n x - alph x) := fun n =>
    (hf n).sub alph_contDiff
  have hbd' : ∀ r : ℕ, ∃ M : ℝ, ∀ᶠ n in atTop, ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv r (fun x => f n x - alph x) x| ≤ M := by
    intro r
    obtain ⟨C, N, hC⟩ := hbd r
    obtain ⟨M, hM⟩ := alph_iteratedDeriv_bounded r
    refine ⟨C + M, ?_⟩
    filter_upwards [eventually_gt_atTop N] with n hn x hx
    rw [iteratedDeriv_sub_eq (hf n) alph_contDiff r x]
    exact (abs_sub _ _).trans (add_le_add (hC n hn x hx) (hM x hx))
  have key := C0_to_Ck (fun n x => f n x - alph x) hu hbd' h0 k ε hε
  filter_upwards [key] with n hn x hx
  rw [iteratedDerivWithin_eq_of_contDiff (hf n) k hx,
    iteratedDerivWithin_eq_of_contDiff alph_contDiff k hx]
  have := hn x hx
  rwa [iteratedDeriv_sub_eq (hf n) alph_contDiff k x] at this

/-- The `k`-th derivatives of `f_n^{(a)}` converge uniformly on `[-1,1]` to those of `α`. -/
theorem Q759_a (k : ℕ) : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ Icc (-1 : ℝ) 1,
    |iteratedDerivWithin k (fa n) (Icc (-1 : ℝ) 1) x
      - iteratedDerivWithin k alph (Icc (-1 : ℝ) 1) x| ≤ ε :=
  main_aux fa contDiff_fa
    (fun r => by
      obtain ⟨C, hC⟩ := fa_deriv_bounded r
      exact ⟨C, 0, fun n _ x hx => hC n x hx⟩)
    fa_unif k

/-- The `k`-th derivatives of `f_n^{(b)}` converge uniformly on `[-1,1]` to those of `α`. -/
theorem Q759_b (k : ℕ) : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ Icc (-1 : ℝ) 1,
    |iteratedDerivWithin k (fb n) (Icc (-1 : ℝ) 1) x
      - iteratedDerivWithin k alph (Icc (-1 : ℝ) 1) x| ≤ ε :=
  main_aux fb contDiff_fb fb_deriv_bounded fb_unif k

/-- Restatement of part (a) as uniform convergence. -/
theorem Q759_a' (k : ℕ) :
    TendstoUniformlyOn (fun n x => iteratedDerivWithin k (fa n) (Icc (-1 : ℝ) 1) x)
      (iteratedDerivWithin k alph (Icc (-1 : ℝ) 1)) atTop (Icc (-1 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Q759_a k (ε / 2) (by linarith)] with n hn x hx
  have := hn x hx
  rw [Real.dist_eq, abs_sub_comm]
  linarith

/-- Restatement of part (b) as uniform convergence. -/
theorem Q759_b' (k : ℕ) :
    TendstoUniformlyOn (fun n x => iteratedDerivWithin k (fb n) (Icc (-1 : ℝ) 1) x)
      (iteratedDerivWithin k alph (Icc (-1 : ℝ) 1)) atTop (Icc (-1 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Q759_b k (ε / 2) (by linarith)] with n hn x hx
  have := hn x hx
  rw [Real.dist_eq, abs_sub_comm]
  linarith

end Q759
