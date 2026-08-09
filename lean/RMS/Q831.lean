import Mathlib

/-!
# Q831 : elementary symmetric polynomials of the `m`-th powers

Formalization of the solution of problem **Q831**:

> Let `Σ₁, …, Σₙ` be the elementary symmetric polynomials in `X₁, …, Xₙ`.
> For each integer `m ≥ 2`, express explicitly `Σᵢ(X₁^m, …, Xₙ^m)` in terms of
> `Σ₁(X), …, Σₙ(X)`.

The elementary symmetric functions are Mathlib's `Multiset.esymm`: for a multiset `s` of
elements of a commutative ring, `s.esymm k = Σₖ` (and `s.esymm k = 0` for `k` larger than the
cardinality of `s`), and `s.map (· ^ m)` is the multiset of `m`-th powers.  Stating the results
for a multiset over an arbitrary commutative ring is exactly the universal statement over `ℤ`
(cf. §6 of the solution: all the formulas are universal polynomial identities over `ℤ`, hence
remain valid after any specialization, in any characteristic).

Main results:

* `Q831.exists_unique_esymm_pow_poly` : the theorem of §2 — for all `n`, `m`, `i` there is a
  *unique* polynomial `Φ ∈ ℤ[Y₁, …, Yₙ]` with `Σᵢ(X₁^m, …, Xₙ^m) = Φ(Σ₁, …, Σₙ)`.
* `Q831.esymm_map_pow_eq_coeff_prod` : formula (2.2),
  `Σᵢ(x^m) = (-1)^{(m+1)i} [z^{mi}] ∏_{r<m} E(ζ^r z)` with `E(z) = ∏ⱼ(1 + xⱼ z) = ∑ₖ Σₖ zᵏ`.
* `Q831.esymm_map_pow_eq_root_of_unity_sum` : formula (2.1), the expansion of (2.2) as a finite
  sum over the tuples `(k₀, …, k_{m-1})` with `k₀ + ⋯ + k_{m-1} = m i`.
* `Q831.esymm_map_sq` and `Q831.esymm_map_sq_card` : the explicit formula (5.1) for `m = 2`,
  the second in exactly the printed form with the summation range `1 ≤ j ≤ min (i, n - i)`.
* `Q831.esymm_map_pow_card`, `Q831.esymm_map_pow_one`, `Q831.esymm_map_pow_char` : the boundary
  cases `Φ_{m,n} = Yₙ^m` and `Φ_{1,i} = Yᵢ`, and the positive characteristic statement of §6.
* `Q831.esymm_one_map_sq`, `Q831.esymm_one_map_cube`, `Q831.esymm_two_map_cube_four` : the
  worked examples of §5 and of the `n = 4`, `m = 3` computation of §7.

Mismatches between the printed solution and the formal statements:

* Formulas (2.1) and (2.2) involve a primitive `m`-th root of unity, so they are stated over a
  commutative ring that is an integral domain and contains such a root `ζ` (`IsPrimitiveRoot ζ m`,
  `0 < m`).  The *integrality* of the resulting universal polynomial is not obtained from them but
  from `exists_unique_esymm_pow_poly`, which is stated over `ℤ`.
* The companion-matrix and resultant presentations (2.3)–(2.5) and the Newton/partition expansion
  (4.1)–(4.2) are not formalized: Mathlib has no companion matrix, and (4.2) has rational
  coefficients termwise.  Their mathematical content, namely that `Σᵢ(X^m)` is a (unique) polynomial
  with *integer* coefficients in `Σ₁, …, Σₙ`, is `exists_unique_esymm_pow_poly`.
* The problem asks for `m ≥ 2` and `1 ≤ i ≤ n`; as in the solution, the statements below are proved
  for all `m` and `i` (with `m > 0` where a primitive `m`-th root of unity is used).

Lean version: 4.28.0.  Mathlib: commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (tag `v4.28.0`).
-/

namespace Q831

open Finset

/-! ## The generating polynomial `E(z) = ∏ (1 + xᵢ z) = ∑ eₖ zᵏ` -/

section GF

open Polynomial

variable {R : Type*} [CommRing R]

theorem esymm_zero' (s : Multiset R) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

theorem esymm_cons (a : R) (s : Multiset R) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Function.comp,
    Multiset.sum_map_mul_left]

theorem esymm_empty_succ (k : ℕ) : (0 : Multiset R).esymm (k + 1) = 0 := by
  simp [Multiset.esymm]

theorem esymm_eq_zero_of_card_lt {s : Multiset R} {k : ℕ} (h : Multiset.card s < k) :
    s.esymm k = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty k h]

/-- The generating polynomial `E(z) = ∏_{x ∈ s} (1 + x z)`. -/
noncomputable def gf (s : Multiset R) : R[X] := (s.map fun r => 1 + C r * X).prod

@[simp] theorem gf_zero : gf (0 : Multiset R) = 1 := by simp [gf]

theorem gf_cons (a : R) (s : Multiset R) : gf (a ::ₘ s) = (1 + C a * X) * gf s := by
  simp [gf]

/-- The coefficients of `E(z) = ∏_{x ∈ s} (1 + x z)` are the elementary symmetric functions. -/
theorem coeff_gf (s : Multiset R) (k : ℕ) : (gf s).coeff k = s.esymm k := by
  induction s using Multiset.induction generalizing k with
  | empty =>
      cases k with
      | zero => simp [esymm_zero']
      | succ k => simp [esymm_empty_succ, Polynomial.coeff_one]
  | cons a s ih =>
      rw [gf_cons]
      cases k with
      | zero => simp [esymm_zero', ih]
      | succ k =>
          rw [add_mul, one_mul, coeff_add, ih, mul_assoc, Polynomial.coeff_C_mul,
            Polynomial.coeff_X_mul, ih, esymm_cons]

end GF

/-! ## The case `m = 2` : formula (5.1) -/

section Squares

open Polynomial

variable {R : Type*} [CommRing R]

theorem gf_mul_gf_neg (s : Multiset R) :
    gf s * gf (s.map (fun x => -x))
      = expand R 2 (gf ((s.map (fun x => x ^ 2)).map (fun x => -x))) := by
  simp only [gf, Multiset.map_map, Function.comp_def, map_multiset_prod, Multiset.map_map]
  rw [← Multiset.prod_map_mul]
  refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
  intro x _
  simp [Polynomial.expand_C]
  ring

/-- Coefficient form of `E(z) E(-z) = ∏ (1 - xᵢ² z²)`. -/
theorem esymm_sq_antidiagonal (s : Multiset R) (i : ℕ) :
    ∑ p ∈ Finset.antidiagonal (2 * i), s.esymm p.1 * ((-1) ^ p.2 * s.esymm p.2)
      = (-1) ^ i * (s.map (fun x => x ^ 2)).esymm i := by
  have h := congrArg (fun p : R[X] => p.coeff (2 * i)) (gf_mul_gf_neg s)
  simp only [Polynomial.coeff_mul, coeff_gf, Multiset.esymm_neg,
    Polynomial.coeff_expand (by norm_num : 0 < 2)] at h
  rw [if_pos ⟨i, rfl⟩, Nat.mul_div_cancel_left i (by norm_num : 0 < 2)] at h
  exact h

theorem sum_range_two_mul_succ_split (f : ℕ → R) (i : ℕ) :
    ∑ k ∈ Finset.range (2 * i + 1), f k
      = f i + ∑ j ∈ Finset.range i, (f (i - (j + 1)) + f (i + (j + 1))) := by
  have h2 : 2 * i + 1 = i + (i + 1) := by ring
  rw [h2, Finset.sum_range_add, Finset.sum_range_succ', Finset.sum_add_distrib]
  rw [← Finset.sum_range_reflect f i]
  have h3 : ∀ j ∈ Finset.range i, f (i - 1 - j) = f (i - (j + 1)) := by
    intro j _; congr 1; omega
  rw [Finset.sum_congr rfl h3]
  simp [add_comm, add_assoc]

/-- **Formula (5.1)**, unrestricted form: for a multiset `s` in a commutative ring,
`Σᵢ(x²) = Σᵢ² + 2 ∑_{j ≥ 1} (-1)^j Σ_{i-j} Σ_{i+j}`. -/
theorem esymm_map_sq (s : Multiset R) (i : ℕ) :
    (s.map (fun x => x ^ 2)).esymm i
      = (s.esymm i) ^ 2 + 2 * ∑ j ∈ Finset.range i,
          (-1) ^ (j + 1) * (s.esymm (i - (j + 1)) * s.esymm (i + (j + 1))) := by
  have key := esymm_sq_antidiagonal s i
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at key
  simp only [Nat.succ_eq_add_one] at key
  rw [sum_range_two_mul_succ_split
    (fun k => s.esymm k * ((-1) ^ (2 * i - k) * s.esymm (2 * i - k))) i] at key
  have hstep : ∀ j ∈ Finset.range i,
      (s.esymm (i - (j + 1)) * ((-1 : R) ^ (2 * i - (i - (j + 1))) * s.esymm (2 * i - (i - (j + 1)))))
        + (s.esymm (i + (j + 1)) *
            ((-1 : R) ^ (2 * i - (i + (j + 1))) * s.esymm (2 * i - (i + (j + 1)))))
      = (-1) ^ i * (2 * ((-1) ^ (j + 1) * (s.esymm (i - (j + 1)) * s.esymm (i + (j + 1))))) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have e1 : 2 * i - (i - (j + 1)) = i + (j + 1) := by omega
    have e2 : 2 * i - (i + (j + 1)) = i - (j + 1) := by omega
    have e3 : (-1 : R) ^ (i - (j + 1)) = (-1) ^ (i + (j + 1)) := by
      have h : i + (j + 1) = (i - (j + 1)) + 2 * (j + 1) := by omega
      rw [h, pow_add, pow_mul]
      norm_num
    rw [e1, e2, e3, pow_add]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum] at key
  rw [show 2 * i - i = i by omega] at key
  have hsq : ((-1 : R) ^ i) * ((-1) ^ i) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have h5 := congrArg (fun z => (-1 : R) ^ i * z) key
  simp only [mul_add, ← mul_assoc, hsq, one_mul] at h5
  have hs2 : ((-1 : R) ^ i * s.esymm i * (-1) ^ i * s.esymm i) = s.esymm i ^ 2 := by
    calc ((-1 : R) ^ i * s.esymm i * (-1) ^ i * s.esymm i)
        = ((-1 : R) ^ i * (-1) ^ i) * (s.esymm i * s.esymm i) := by ring
      _ = s.esymm i ^ 2 := by rw [hsq]; ring
  rw [← h5, hs2, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => by ring)

/-- **Formula (5.1)** exactly as printed: for a multiset `s` of cardinality `n` and `i ≤ n`,
`Σᵢ(x₁², …, xₙ²) = Σᵢ² + 2 ∑_{j=1}^{min (i, n-i)} (-1)^j Σ_{i-j} Σ_{i+j}`.

The hypothesis `i ≤ n` is part of the printed statement; it turns out to be unnecessary. -/
theorem esymm_map_sq_card (s : Multiset R) (n i : ℕ) (hn : Multiset.card s = n) (hi : i ≤ n) :
    (s.map (fun x => x ^ 2)).esymm i
      = (s.esymm i) ^ 2 + 2 * ∑ j ∈ Finset.Icc 1 (min i (n - i)),
          (-1) ^ j * (s.esymm (i - j) * s.esymm (i + j)) := by
  rw [esymm_map_sq s i]
  congr 2
  rw [show Finset.Icc 1 (min i (n - i)) = Finset.Ico 1 (min i (n - i) + 1) from
      (Finset.Ico_add_one_right_eq_Icc _ _).symm,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]
  refine (Finset.sum_subset (Finset.range_mono (min_le_left i (n - i))) ?_).symm
  intro j hj hj'
  simp only [Finset.mem_range, not_lt] at hj hj'
  rw [esymm_eq_zero_of_card_lt (by omega : Multiset.card s < i + (j + 1)), mul_zero, mul_zero]

end Squares

/-! ## Existence and uniqueness of the universal polynomial `Φ` (§2) -/

section Universal

open MvPolynomial

variable {R : Type*} [CommRing R]

theorem isSymmetric_aeval_pow {σ : Type*} {p : MvPolynomial σ R} (hp : p.IsSymmetric) (m : ℕ) :
    (aeval (fun j : σ => (X j : MvPolynomial σ R) ^ m) p).IsSymmetric := by
  intro e
  have h1 : (rename (e : σ → σ)).comp (aeval (fun j : σ => (X j : MvPolynomial σ R) ^ m))
      = aeval (fun j : σ => (X (e j) : MvPolynomial σ R) ^ m) := by
    ext j; simp
  have h2 := congrArg (fun g : MvPolynomial σ R →ₐ[R] MvPolynomial σ R => g p) h1
  simp only [AlgHom.comp_apply] at h2
  rw [h2, show (fun j : σ => (X (e j) : MvPolynomial σ R) ^ m)
        = (fun j : σ => (X j : MvPolynomial σ R) ^ m) ∘ (e : σ → σ) from rfl,
    ← MvPolynomial.aeval_rename, hp e]

/-- **Theorem of §2.** For every `n`, `m` and `i` there is a unique polynomial
`Φ ∈ ℤ[Y₁, …, Yₙ]` (here indexed by `Fin n`, with `Y_{j}` corresponding to `Σ_{j+1}`) such that
`Σᵢ(X₁^m, …, Xₙ^m) = Φ(Σ₁, …, Σₙ)`. -/
theorem exists_unique_esymm_pow_poly (n m i : ℕ) :
    ∃! Φ : MvPolynomial (Fin n) ℤ,
      aeval (fun j : Fin n => esymm (Fin n) ℤ (j + 1)) Φ
        = aeval (fun j : Fin n => (X j : MvPolynomial (Fin n) ℤ) ^ m) (esymm (Fin n) ℤ i) := by
  have hsym : (aeval (fun j : Fin n => (X j : MvPolynomial (Fin n) ℤ) ^ m)
      (esymm (Fin n) ℤ i)).IsSymmetric := isSymmetric_aeval_pow (esymm_isSymmetric _ _ i) m
  obtain ⟨Φ, hΦ⟩ := esymmAlgHom_surjective (σ := Fin n) (R := ℤ) (n := n)
    (by simp) ⟨_, hsym⟩
  have hex : aeval (fun j : Fin n => esymm (Fin n) ℤ (j + 1)) Φ
      = aeval (fun j : Fin n => (X j : MvPolynomial (Fin n) ℤ) ^ m) (esymm (Fin n) ℤ i) := by
    have := congrArg Subtype.val hΦ
    rwa [esymmAlgHom_apply] at this
  refine ⟨Φ, hex, fun Ψ hΨ => ?_⟩
  refine esymmAlgHom_injective (σ := Fin n) (R := ℤ) (n := n) (by simp) (Subtype.ext ?_)
  rw [esymmAlgHom_apply, esymmAlgHom_apply, hΨ, hex]

end Universal

/-! ## The root-of-unity formulas (2.1) and (2.2) -/

section RootOfUnity

open Polynomial

variable {R : Type*} [CommRing R]

theorem prod_finset_multiset_prod {M ι α : Type*} [CommMonoid M] [DecidableEq ι]
    (t : Finset ι) (s : Multiset α) (f : ι → α → M) :
    ∏ r ∈ t, (s.map (f r)).prod = (s.map (fun x => ∏ r ∈ t, f r x)).prod := by
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, ih, ← Multiset.prod_map_mul]
      exact congrArg Multiset.prod
        (Multiset.map_congr rfl (fun x _ => by rw [Finset.prod_insert ha]))

theorem coeff_finset_prod {ι : Type*} [DecidableEq ι] (f : ι → R[X]) (d : ℕ) (t : Finset ι) :
    (∏ j ∈ t, f j).coeff d = ∑ l ∈ Finset.finsuppAntidiag t d, ∏ i ∈ t, (f i).coeff (l i) := by
  have e : ((∏ j ∈ t, f j : R[X]) : PowerSeries R) = ∏ j ∈ t, ((f j : PowerSeries R)) :=
    map_prod (Polynomial.coeToPowerSeries.ringHom (R := R)) f t
  have h := PowerSeries.coeff_prod (fun j => ((f j : R[X]) : PowerSeries R)) d t
  rw [← e] at h
  simpa using h

theorem prod_one_sub_pow_mul {S : Type*} [CommRing S] [IsDomain S] {m : ℕ} {ζ : S}
    (hζ : IsPrimitiveRoot ζ m) (hm : 0 < m) (α : S) :
    ∏ r ∈ Finset.range m, (1 - ζ ^ r * α) = 1 - α ^ m := by
  have h := X_pow_sub_C_eq_prod hζ hm (rfl : α ^ m = α ^ m)
  have h2 := congrArg (fun p : S[X] => p.eval 1) h
  simp [Polynomial.eval_prod] at h2
  exact h2.symm

/-- `∏_{r<m} (1 + ζ^r x z) = 1 + (-1)^{m+1} x^m z^m`. -/
theorem prod_one_add_pow_mul_X [IsDomain R] {m : ℕ} {ζ : R}
    (hζ : IsPrimitiveRoot ζ m) (hm : 0 < m) (x : R) :
    ∏ r ∈ Finset.range m, (1 + C (ζ ^ r * x) * X : R[X])
      = 1 + C ((-1) ^ (m + 1) * x ^ m) * X ^ m := by
  have hζ' : IsPrimitiveRoot (C ζ : R[X]) m := hζ.map_of_injective Polynomial.C_injective
  have h := prod_one_sub_pow_mul hζ' hm (-(C x * X))
  have h2 : ∀ r ∈ Finset.range m,
      (1 : R[X]) - (C ζ) ^ r * (-(C x * X)) = 1 + C (ζ ^ r * x) * X := by
    intro r _; rw [map_mul, map_pow]; ring
  rw [Finset.prod_congr rfl h2] at h
  have hC : (C ((-1 : R) ^ (m + 1) * x ^ m) : R[X]) = (-1) ^ (m + 1) * C x ^ m := by
    simp [map_mul, map_pow]
  rw [h, hC, neg_pow, mul_pow, ← C_pow]
  ring

/-- The generating-function identity behind (2.2):
`∏_{r<m} E(ζ^r z) = ∑_i (-1)^{(m+1)i} Σ_i(x^m) z^{mi}`. -/
theorem prod_gf_smul_eq_expand [IsDomain R] {m : ℕ} {ζ : R}
    (hζ : IsPrimitiveRoot ζ m) (hm : 0 < m) (s : Multiset R) :
    ∏ r ∈ Finset.range m, gf (s.map (fun x => ζ ^ r * x))
      = expand R m (gf (s.map (fun x => (-1) ^ (m + 1) * x ^ m))) := by
  have h1 : ∀ r : ℕ, gf (s.map (fun x => ζ ^ r * x))
      = (s.map (fun x => 1 + C (ζ ^ r * x) * X)).prod := by
    intro r; simp [gf, Multiset.map_map]
  simp only [h1]
  rw [prod_finset_multiset_prod]
  have h2 : ∀ x ∈ s, ∏ r ∈ Finset.range m, (1 + C (ζ ^ r * x) * X : R[X])
      = expand R m (1 + C ((-1) ^ (m + 1) * x ^ m) * X) := by
    intro x _
    rw [prod_one_add_pow_mul_X hζ hm x]
    simp [Polynomial.expand_C]
  rw [Multiset.map_congr rfl h2, gf, Multiset.map_map, Function.comp_def, map_multiset_prod,
    Multiset.map_map]
  rfl

/-- **Formula (2.2)**: over a domain containing a primitive `m`-th root of unity `ζ`,
`Σ_i(x₁^m, …, xₙ^m) = (-1)^{(m+1)i} [z^{mi}] ∏_{r<m} E(ζ^r z)`, where
`E(z) = ∏_j (1 + x_j z) = ∑_k Σ_k z^k`. -/
theorem esymm_map_pow_eq_coeff_prod [IsDomain R] {m : ℕ} {ζ : R}
    (hζ : IsPrimitiveRoot ζ m) (hm : 0 < m) (s : Multiset R) (i : ℕ) :
    (s.map (fun x => x ^ m)).esymm i
      = (-1) ^ ((m + 1) * i) *
          (∏ r ∈ Finset.range m, gf (s.map (fun x => ζ ^ r * x))).coeff (m * i) := by
  have h := congrArg (fun p : R[X] => p.coeff (m * i)) (prod_gf_smul_eq_expand hζ hm s)
  simp only [Polynomial.coeff_expand hm, coeff_gf] at h
  rw [if_pos (Nat.dvd_mul_right m i), Nat.mul_div_cancel_left i hm] at h
  have hmap : s.map (fun x => (-1 : R) ^ (m + 1) * x ^ m)
      = (s.map (fun x => x ^ m)).map (fun y => (-1 : R) ^ (m + 1) * y) := by
    rw [Multiset.map_map]; rfl
  rw [hmap] at h
  have hsm : ((s.map (fun x => x ^ m)).map (fun y => (-1 : R) ^ (m + 1) * y)).esymm i
      = ((-1 : R) ^ (m + 1)) ^ i * (s.map (fun x => x ^ m)).esymm i := by
    have := Multiset.pow_smul_esymm ((-1 : R) ^ (m + 1)) i (s.map (fun x => x ^ m))
    simpa [smul_eq_mul] using this.symm
  rw [hsm] at h
  rw [h, ← pow_mul, ← mul_assoc, ← pow_add]
  have hone : (-1 : R) ^ ((m + 1) * i + (m + 1) * i) = 1 := by
    rw [← two_mul, pow_mul]; norm_num
  rw [hone, one_mul]

/-- **Formula (2.1)**: the fully expanded root-of-unity formula.  Here `l` runs over the
functions `{0, …, m-1} → ℕ` with `l 0 + ⋯ + l (m-1) = m i`, and `Σ_k = 0` for `k > n`. -/
theorem esymm_map_pow_eq_root_of_unity_sum [IsDomain R] {m : ℕ} {ζ : R}
    (hζ : IsPrimitiveRoot ζ m) (hm : 0 < m) (s : Multiset R) (i : ℕ) :
    (s.map (fun x => x ^ m)).esymm i
      = (-1) ^ ((m + 1) * i) *
          ∑ l ∈ Finset.finsuppAntidiag (Finset.range m) (m * i),
            (∏ r ∈ Finset.range m, ζ ^ (r * l r)) * ∏ r ∈ Finset.range m, s.esymm (l r) := by
  rw [esymm_map_pow_eq_coeff_prod hζ hm s i, coeff_finset_prod]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun r _ => ?_)
  rw [coeff_gf]
  have := Multiset.pow_smul_esymm (ζ ^ r) (l r) s
  simp only [smul_eq_mul] at this
  rw [← this, ← pow_mul]

end RootOfUnity

/-! ## Boundary cases and positive characteristic (§6) -/

section Boundary

variable {R : Type*} [CommRing R]

theorem esymm_map_ringHom {S : Type*} [CommRing S] (f : R →+* S) (s : Multiset R) (k : ℕ) :
    (s.map f).esymm k = f (s.esymm k) := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, map_multiset_sum,
    Function.comp_def]
  exact congrArg Multiset.sum (Multiset.map_congr rfl (fun t _ => (map_multiset_prod f t).symm))

theorem esymm_card (t : Multiset R) : t.esymm (Multiset.card t) = t.prod := by
  induction t using Multiset.induction with
  | empty => simp [esymm_zero']
  | cons a s ih =>
      rw [Multiset.card_cons, esymm_cons, esymm_eq_zero_of_card_lt (by omega), ih, zero_add,
        Multiset.prod_cons]

/-- `Φ_{m,n} = Yₙ^m` : the top elementary symmetric polynomial of the `m`-th powers. -/
theorem esymm_map_pow_card (s : Multiset R) (m : ℕ) :
    (s.map (fun x => x ^ m)).esymm (Multiset.card s) = (s.esymm (Multiset.card s)) ^ m := by
  have hcard : Multiset.card (s.map (fun x => x ^ m)) = Multiset.card s := by simp
  have h := esymm_card (s.map (fun x => x ^ m))
  rw [hcard] at h
  rw [h, esymm_card, Multiset.prod_map_pow]
  simp

/-- `Φ_{1,i} = Y_i` : the case `m = 1`. -/
theorem esymm_map_pow_one (s : Multiset R) (i : ℕ) :
    (s.map (fun x => x ^ 1)).esymm i = s.esymm i := by
  simp

/-- **Positive characteristic (§6).** In characteristic `p`,
`Σ_i(x₁^{p^a q}, …, xₙ^{p^a q}) = (Σ_i(x₁^q, …, xₙ^q))^{p^a}`. -/
theorem esymm_map_pow_char (p : ℕ) [Fact (Nat.Prime p)] [CharP R p] (a q i : ℕ)
    (s : Multiset R) :
    (s.map (fun x => x ^ (p ^ a * q))).esymm i = ((s.map (fun x => x ^ q)).esymm i) ^ (p ^ a) := by
  have hmap : s.map (fun x => x ^ (p ^ a * q))
      = (s.map (fun x => x ^ q)).map (iterateFrobenius R p a) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl (fun x _ => ?_)
    rw [Function.comp_apply, iterateFrobenius_def, ← pow_mul, mul_comm q (p ^ a)]
  rw [hmap, esymm_map_ringHom, iterateFrobenius_def]

end Boundary

/-! ## Worked examples from the solution -/

section Examples

variable {R : Type*} [CommRing R]

/-- `Σ₁(x₁², …, xₙ²) = Σ₁² - 2Σ₂` (§5.1). -/
theorem esymm_one_map_sq (s : Multiset R) :
    (s.map (fun x => x ^ 2)).esymm 1 = (s.esymm 1) ^ 2 - 2 * s.esymm 2 := by
  rw [esymm_map_sq s 1]
  simp [esymm_zero']
  ring

/-- `Σ₁(x₁³, …, xₙ³) = Σ₁³ - 3Σ₁Σ₂ + 3Σ₃` (§5.2). -/
theorem esymm_one_map_cube (s : Multiset R) :
    (s.map (fun x => x ^ 3)).esymm 1
      = (s.esymm 1) ^ 3 - 3 * s.esymm 1 * s.esymm 2 + 3 * s.esymm 3 := by
  induction s using Multiset.induction with
  | empty => simp [Multiset.esymm]
  | cons a s ih =>
      have h1 : ∀ (b : R) (t : Multiset R), (b ::ₘ t).esymm 1 = t.esymm 1 + b := by
        intro b t; have := esymm_cons b t 0; rwa [esymm_zero', mul_one] at this
      have h2 : ∀ (b : R) (t : Multiset R), (b ::ₘ t).esymm 2 = t.esymm 2 + b * t.esymm 1 :=
        fun b t => esymm_cons b t 1
      have h3 : ∀ (b : R) (t : Multiset R), (b ::ₘ t).esymm 3 = t.esymm 3 + b * t.esymm 2 :=
        fun b t => esymm_cons b t 2
      rw [Multiset.map_cons, h1, h1, h2, h3, ih]
      ring

/-- The computation of §7 for `n = 4`, `m = 3`, `i = 2`:
`Σ₂(x₁³, …, x₄³) = Σ₂³ - 3Σ₁Σ₂Σ₃ + 3Σ₁²Σ₄ - 3Σ₂Σ₄ + 3Σ₃²`. -/
theorem esymm_two_map_cube_four (x1 x2 x3 x4 : R) :
    ((({x1, x2, x3, x4} : Multiset R)).map (fun x => x ^ 3)).esymm 2
      = (({x1, x2, x3, x4} : Multiset R).esymm 2) ^ 3
        - 3 * ({x1, x2, x3, x4} : Multiset R).esymm 1 * ({x1, x2, x3, x4} : Multiset R).esymm 2
            * ({x1, x2, x3, x4} : Multiset R).esymm 3
        + 3 * (({x1, x2, x3, x4} : Multiset R).esymm 1) ^ 2
            * ({x1, x2, x3, x4} : Multiset R).esymm 4
        - 3 * ({x1, x2, x3, x4} : Multiset R).esymm 2 * ({x1, x2, x3, x4} : Multiset R).esymm 4
        + 3 * (({x1, x2, x3, x4} : Multiset R).esymm 3) ^ 2 := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.insert_eq_cons,
    Multiset.powersetCard_zero_left, Multiset.powersetCard_one]
  ring

end Examples

end Q831
