import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Q655 — the maximal dimension of a sum of two commutants

Let `K` be an arbitrary field and let `E` be a `K`-vector space of dimension `n ≥ 2`,
realized here as `Fin n → K`, so that `End K E` is `Matrix (Fin n) (Fin n) K`.
For an endomorphism `f`, let `C(f)` denote its commutant.  If neither `f` nor `g`
is a scalar endomorphism, the largest possible value of `dim (C(f) + C(g))` is `n² - 1`.

This file formalizes **Theorem A** of the candidate answer:

* `Q655.commutant_sup_ne_top` / `Q655.finrank_commutant_sup_le` : the universal upper bound
  `dim (C f + C g) ≤ n² - 1` for non-scalar `f`, `g`;
* `Q655.exists_extremal_pair` : an explicit pair of non-scalar matrices attaining `n² - 1`,
  over every field (including `𝔽₂`) and in every dimension `n ≥ 2`;
* `Q655.isGreatest_finrank_commutant_sup` : the combination of the two, stating that
  `n² - 1` is the greatest element of the set of achievable dimensions.

The general equality classification (*which* pairs attain the maximum) is deliberately **not**
formalized: the candidate answer only settles it in small dimensions or under a rank-one
hypothesis, so no complete classification is claimed here.

## Proof outline

*Upper bound.*  If `X` commutes with `f` then `tr ((f Y - Y f) X) = 0`.  Hence it suffices to
produce a nonzero matrix lying simultaneously in the image of `ad f` and of `ad g`; the
functional `X ↦ tr (h X)` then vanishes on `C(f) + C(g)` without being identically zero.
Such an `h` exists: if `f g ≠ g f` take `h = [f, g]`; if `f` and `g` commute and
`ad g ∘ ad f ≠ 0` take any nonzero value of that composite (which equals `ad f ∘ ad g`);
and if `ad g ∘ ad f = 0`, evaluating on the matrices `single j k 1` forces
`g = c • f + d • 1` with `c ≠ 0`, so the two commutator images coincide.

*Attainment.*  Take `f = E a a` and `g = (e a + e b) ⊗ (ε a + ε b)` for two distinct indices
`a ≠ b`.  Then `C(f) + C(g)` is exactly the hyperplane `{X | X a b = X b a}`, of dimension
`n² - 1`.

## Relation to the printed statement

The printed problem speaks of an abstract `n`-dimensional `K`-vector space `E` and of
`𝓛(E)`.  Here `E` is taken to be `Fin n → K` and `𝓛(E)` is `Matrix (Fin n) (Fin n) K`;
since every `n`-dimensional space over `K` is isomorphic to `Fin n → K` and the statement is
invariant under such an isomorphism, this is not a weakening.  "Scalar endomorphism" is
rendered by `IsScalarMat f : ∃ c, f = c • 1`, and `C(f) + C(g)` by the submodule join
`commutant f ⊔ commutant g`.  The maximum is expressed as `IsGreatest`, i.e. `n² - 1` is
attained and is an upper bound.  (The natural-number subtraction `n ^ 2 - 1` is harmless
because `n ≥ 2`.)  No other mismatch arises.

## Versions

Lean 4 toolchain `leanprover/lean4:v4.28.0`; Mathlib at commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365` (tag `v4.28.0`).
-/

namespace Q655

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- The commutant `C(f) = {X | X f = f X}` of a square matrix, as a `K`-submodule. -/
def commutant (f : Matrix (Fin n) (Fin n) K) : Submodule K (Matrix (Fin n) (Fin n) K) where
  carrier := {X | X * f = f * X}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    rw [add_mul, mul_add, hx, hy]
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.smul_mul, Matrix.mul_smul, hx]

@[simp] lemma mem_commutant_iff {f X : Matrix (Fin n) (Fin n) K} :
    X ∈ commutant f ↔ X * f = f * X := Iff.rfl

/-- `f` is a scalar matrix. -/
def IsScalarMat (f : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ c : K, f = c • (1 : Matrix (Fin n) (Fin n) K)

/-! ### Elementary facts about `Matrix.single` -/

lemma mul_single_one_apply (M : Matrix (Fin n) (Fin n) K) (i j p q : Fin n) :
    (M * Matrix.single i j (1 : K)) p q = if q = j then M p i else 0 := by
  by_cases h : q = j
  · subst h; simp
  · simp [h]

lemma single_one_mul_apply (M : Matrix (Fin n) (Fin n) K) (i j p q : Fin n) :
    (Matrix.single i j (1 : K) * M) p q = if p = i then M j q else 0 := by
  by_cases h : p = i
  · subst h; simp
  · simp [h]

lemma mul_single_mul_apply (A B : Matrix (Fin n) (Fin n) K) (j k p q : Fin n) :
    (A * Matrix.single j k (1 : K) * B) p q = A p j * B k q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · rw [mul_single_one_apply]; simp
  · intro c _ hc; rw [mul_single_one_apply]; simp [hc]
  · simp

/-! ### The trace pairing -/

/-- The linear functional `X ↦ tr (h X)`. -/
def traceMulLin (h : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K →ₗ[K] K where
  toFun X := Matrix.trace (h * X)
  map_add' := by intro X Y; simp [mul_add]
  map_smul' := by intro c X; simp

@[simp] lemma traceMulLin_apply (h X : Matrix (Fin n) (Fin n) K) :
    traceMulLin h X = Matrix.trace (h * X) := rfl

lemma trace_single_mul (h : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    Matrix.trace (h * Matrix.single j i (1 : K)) = h i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single, Matrix.diag, ite_and, Finset.sum_ite_eq]

/-- A commutator `[f, Y]` is trace-orthogonal to the whole commutant of `f`. -/
lemma trace_commutator_mem_commutant (f Y X : Matrix (Fin n) (Fin n) K)
    (hX : X ∈ commutant f) : Matrix.trace ((f * Y - Y * f) * X) = 0 := by
  rw [mem_commutant_iff] at hX
  have h1 : (f * Y - Y * f) * X = f * (Y * X) - Y * f * X := by noncomm_ring
  rw [h1, Matrix.trace_sub, Matrix.trace_mul_comm f (Y * X), mul_assoc, hX, ← mul_assoc]
  simp

/-! ### Non-scalar matrices -/

lemma isScalarMat_iff_mem_range_scalar {f : Matrix (Fin n) (Fin n) K} :
    IsScalarMat f ↔ f ∈ Set.range (Matrix.scalar (Fin n)) := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by simp [Matrix.scalar_apply, smul_one_eq_diagonal]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by simp [Matrix.scalar_apply, smul_one_eq_diagonal]⟩

/-- A non-scalar matrix fails to commute with some matrix. -/
lemma exists_noncomm {f : Matrix (Fin n) (Fin n) K} (hf : ¬ IsScalarMat f) :
    ∃ Y, f * Y - Y * f ≠ 0 := by
  by_contra hc
  push_neg at hc
  refine hf (isScalarMat_iff_mem_range_scalar.2
    (Matrix.mem_range_scalar_iff_commute_single'.2 fun i j => ?_))
  exact (sub_eq_zero.1 (hc (Matrix.single i j 1))).symm

/-! ### The key structural lemma -/

/-- If the iterated commutator map `ad g ∘ ad f` vanishes identically and `f` is not scalar,
then `g` is an affine combination of `f` and the identity. -/
lemma exists_affine_of_ad_comp_eq_zero {f g : Matrix (Fin n) (Fin n) K}
    (hf : ¬ IsScalarMat f)
    (hψ : ∀ X : Matrix (Fin n) (Fin n) K, g * (f * X - X * f) - (f * X - X * f) * g = 0) :
    ∃ c d : K, g = c • f + d • (1 : Matrix (Fin n) (Fin n) K) := by
  -- the entrywise form of the hypothesis, obtained by testing on `single j k 1`
  have key : ∀ j k p q : Fin n,
      (if q = k then (g * f) p j else 0) - g p j * f k q - f p j * g k q
        + (if p = j then (f * g) k q else 0) = 0 := by
    intro j k p q
    have h := congrFun (congrFun (hψ (Matrix.single j k 1)) p) q
    have e1 : g * (f * Matrix.single j k (1 : K)) = g * f * Matrix.single j k 1 := by
      rw [mul_assoc]
    have e2 : g * (Matrix.single j k (1 : K) * f) = g * Matrix.single j k 1 * f := by
      rw [mul_assoc]
    have e3 : f * Matrix.single j k (1 : K) * g = f * (Matrix.single j k 1 * g) := by
      rw [mul_assoc]
    have e4 : Matrix.single j k (1 : K) * f * g = Matrix.single j k 1 * (f * g) := by
      rw [mul_assoc]
    simp only [Matrix.sub_apply, Matrix.zero_apply, Matrix.mul_sub, Matrix.sub_mul,
      e1, e2, e3, e4, mul_single_one_apply, single_one_mul_apply] at h
    rw [← mul_assoc, mul_single_mul_apply, mul_single_mul_apply] at h
    linear_combination h
  -- the off-diagonal relations
  have offdiag : ∀ k q : Fin n, k ≠ q →
      f k q • g + g k q • f = (f * g) k q • (1 : Matrix (Fin n) (Fin n) K) := by
    intro k q hkq
    ext p j
    have h := key j k p q
    rw [if_neg (fun hc : q = k => hkq hc.symm)] at h
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    split_ifs at h ⊢ with hpj
    · linear_combination -h
    · linear_combination -h
  -- the diagonal relations
  have diagrel : ∀ k : Fin n,
      g * f - f k k • g - g k k • f + (f * g) k k • (1 : Matrix (Fin n) (Fin n) K) = 0 := by
    intro k
    ext p j
    have h := key j k p k
    rw [if_pos rfl] at h
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, Matrix.zero_apply]
    split_ifs at h ⊢ with hpj
    · linear_combination h
    · linear_combination h
  by_cases hoff : ∃ k q : Fin n, k ≠ q ∧ f k q ≠ 0
  · -- `f` has a nonzero off-diagonal entry
    obtain ⟨k, q, hkq, hfkq⟩ := hoff
    refine ⟨-(g k q) / f k q, (f * g) k q / f k q, ?_⟩
    have h := offdiag k q hkq
    have h2 : f k q • g = f k q • ((-(g k q) / f k q) • f
        + ((f * g) k q / f k q) • (1 : Matrix (Fin n) (Fin n) K)) := by
      rw [smul_add, smul_smul, smul_smul]
      field_simp
      linear_combination (norm := module) h
    exact smul_right_injective _ hfkq h2
  · -- `f` is diagonal
    push_neg at hoff
    have hgoff : ∀ k q : Fin n, k ≠ q → g k q = 0 := by
      intro k q hkq
      by_contra hgkq
      refine hf ⟨(f * g) k q / g k q, ?_⟩
      have h := offdiag k q hkq
      rw [hoff k q hkq, zero_smul, zero_add] at h
      have h2 : g k q • f = g k q • (((f * g) k q / g k q) • (1 : Matrix (Fin n) (Fin n) K)) := by
        rw [smul_smul]
        field_simp
        linear_combination (norm := module) h
      exact smul_right_injective _ hgkq h2
    -- two diagonal entries of `f` must differ
    have hdiag : ∃ k k' : Fin n, f k k ≠ f k' k' := by
      by_contra hc
      push_neg at hc
      rcases isEmpty_or_nonempty (Fin n) with _ | ⟨⟨k₀⟩⟩
      · exact hf ⟨0, Subsingleton.elim _ _⟩
      · refine hf ⟨f k₀ k₀, ?_⟩
        ext p j
        simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
        split_ifs with hpj
        · subst hpj; simp [hc p k₀]
        · simp [hoff p j hpj]
    obtain ⟨k, k', hkk'⟩ := hdiag
    have ht : f k' k' - f k k ≠ 0 := sub_ne_zero.2 (Ne.symm hkk')
    refine ⟨(g k k - g k' k') / (f k' k' - f k k),
      ((f * g) k' k' - (f * g) k k) / (f k' k' - f k k), ?_⟩
    have h1 := diagrel k
    have h2 := diagrel k'
    have h3 : (f k' k' - f k k) • g
        = (f k' k' - f k k) • (((g k k - g k' k') / (f k' k' - f k k)) • f
            + (((f * g) k' k' - (f * g) k k) / (f k' k' - f k k)) •
              (1 : Matrix (Fin n) (Fin n) K)) := by
      rw [smul_add, smul_smul, smul_smul]
      field_simp
      linear_combination (norm := module) h1 - h2
    exact smul_right_injective _ ht h3

/-- For non-scalar `f` and `g` there is a nonzero matrix lying in the image of `ad f`
and in the image of `ad g`. -/
lemma exists_common_commutator {f g : Matrix (Fin n) (Fin n) K}
    (hf : ¬ IsScalarMat f) (hg : ¬ IsScalarMat g) :
    ∃ h : Matrix (Fin n) (Fin n) K, h ≠ 0 ∧ (∃ Y, h = f * Y - Y * f) ∧
      (∃ Z, h = g * Z - Z * g) := by
  by_cases hcomm : f * g = g * f
  · by_cases hψ : ∀ X : Matrix (Fin n) (Fin n) K, g * (f * X - X * f) - (f * X - X * f) * g = 0
    · -- degenerate case: `g` is an affine function of `f`, so the two images coincide
      obtain ⟨c, d, hgcd⟩ := exists_affine_of_ad_comp_eq_zero hf hψ
      have hc : c ≠ 0 := by
        rintro rfl
        exact hg ⟨d, by simpa using hgcd⟩
      obtain ⟨Y, hY⟩ := exists_noncomm hf
      refine ⟨f * Y - Y * f, hY, ⟨Y, rfl⟩, ⟨c⁻¹ • Y, ?_⟩⟩
      subst hgcd
      rw [Matrix.mul_smul, Matrix.smul_mul, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
      match_scalars <;> field_simp
      ring
    · -- `ad f ∘ ad g = ad g ∘ ad f` is nonzero
      push_neg at hψ
      obtain ⟨X, hX⟩ := hψ
      refine ⟨g * (f * X - X * f) - (f * X - X * f) * g, hX, ⟨g * X - X * g, ?_⟩,
        ⟨f * X - X * f, rfl⟩⟩
      have h1 : f * (g * X - X * g) - (g * X - X * g) * f
          = f * g * X - f * X * g - (g * X * f - X * (g * f)) := by noncomm_ring
      have h2 : g * (f * X - X * f) - (f * X - X * f) * g
          = g * f * X - g * X * f - (f * X * g - X * (f * g)) := by noncomm_ring
      rw [h1, h2, hcomm]
      abel
  · exact ⟨f * g - g * f, sub_ne_zero.2 hcomm, ⟨g, rfl⟩, ⟨-f, by noncomm_ring⟩⟩

/-! ### The universal upper bound -/

/-- **Theorem A, upper bound.**  If neither `f` nor `g` is scalar, then `C(f) + C(g)` is a
proper subspace of the full matrix algebra. -/
theorem commutant_sup_ne_top {f g : Matrix (Fin n) (Fin n) K}
    (hf : ¬ IsScalarMat f) (hg : ¬ IsScalarMat g) :
    commutant f ⊔ commutant g ≠ ⊤ := by
  obtain ⟨h, hne, ⟨Y, hY⟩, ⟨Z, hZ⟩⟩ := exists_common_commutator hf hg
  intro htop
  obtain ⟨i, j, hij⟩ : ∃ i j, h i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (by ext i j; simp [hc i j])
  have hle : commutant f ⊔ commutant g ≤ LinearMap.ker (traceMulLin h) := by
    refine sup_le (fun X hX => ?_) (fun X hX => ?_)
    · simp only [LinearMap.mem_ker, traceMulLin_apply, hY]
      exact trace_commutator_mem_commutant f Y X hX
    · simp only [LinearMap.mem_ker, traceMulLin_apply, hZ]
      exact trace_commutator_mem_commutant g Z X hX
  rw [htop, top_le_iff, LinearMap.ker_eq_top] at hle
  have hzero := congrFun (congrArg (fun L : Matrix (Fin n) (Fin n) K →ₗ[K] K => L.toFun) hle)
    (Matrix.single j i 1)
  exact hij (by rw [← trace_single_mul h i j]; exact hzero)

/-- **Theorem A, upper bound (dimension form).** -/
theorem finrank_commutant_sup_le {f g : Matrix (Fin n) (Fin n) K}
    (hf : ¬ IsScalarMat f) (hg : ¬ IsScalarMat g) :
    Module.finrank K ↥(commutant f ⊔ commutant g) ≤ n ^ 2 - 1 := by
  have h := Submodule.finrank_lt (K := K) (V := Matrix (Fin n) (Fin n) K)
    (commutant_sup_ne_top hf hg)
  rw [Module.finrank_matrix] at h
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at h
  have hn : n * n = n ^ 2 := by ring
  omega

/-! ### The extremal pair -/

/-- The vector `u = e a + e b`, as a function `Fin n → K`. -/
def uvec (a b : Fin n) : Fin n → K :=
  fun i => (if i = a then 1 else 0) + (if i = b then 1 else 0)

/-- The rank-one idempotent `e a ⊗ ε a`. -/
def fmat (a : Fin n) : Matrix (Fin n) (Fin n) K := Matrix.single a a (1 : K)

/-- The rank-one map `(e a + e b) ⊗ (ε a + ε b)`. -/
def gmat (a b : Fin n) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => uvec (K := K) a b i * uvec (K := K) a b j

lemma uvec_a {a b : Fin n} (hab : a ≠ b) : uvec (K := K) a b a = 1 := by simp [uvec, hab]

lemma uvec_b {a b : Fin n} (hab : a ≠ b) : uvec (K := K) a b b = 1 := by simp [uvec, Ne.symm hab]

lemma sum_mul_uvec (a b : Fin n) (Z : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    ∑ k, Z i k * uvec (K := K) a b k = Z i a + Z i b := by
  simp only [uvec, mul_add, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ a (fun k => Z i k),
    Finset.sum_ite_eq' Finset.univ b (fun k => Z i k)]
  simp

lemma sum_uvec_mul (a b : Fin n) (Z : Matrix (Fin n) (Fin n) K) (j : Fin n) :
    ∑ k, uvec (K := K) a b k * Z k j = Z a j + Z b j := by
  simp only [uvec, add_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ a (fun k => Z k j),
    Finset.sum_ite_eq' Finset.univ b (fun k => Z k j)]
  simp

lemma mul_gmat_apply (a b : Fin n) (Z : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (Z * gmat (K := K) a b) i j = (Z i a + Z i b) * uvec (K := K) a b j := by
  rw [Matrix.mul_apply, ← sum_mul_uvec a b Z i, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by simp [gmat, mul_assoc]

lemma gmat_mul_apply (a b : Fin n) (Z : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (gmat (K := K) a b * Z) i j = uvec (K := K) a b i * (Z a j + Z b j) := by
  rw [Matrix.mul_apply, ← sum_uvec_mul a b Z j, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by simp [gmat, mul_assoc]

lemma mem_commutant_gmat_iff (a b : Fin n) (Z : Matrix (Fin n) (Fin n) K) :
    Z ∈ commutant (gmat (K := K) a b) ↔
      ∀ i j, (Z i a + Z i b) * uvec (K := K) a b j
        = uvec (K := K) a b i * (Z a j + Z b j) := by
  rw [mem_commutant_iff, ← Matrix.ext_iff]
  constructor
  · intro h i j; rw [← mul_gmat_apply, ← gmat_mul_apply]; exact h i j
  · intro h i j; rw [mul_gmat_apply, gmat_mul_apply]; exact h i j

lemma mem_commutant_fmat_iff (a : Fin n) (Y : Matrix (Fin n) (Fin n) K) :
    Y ∈ commutant (fmat (K := K) a) ↔
      (∀ j, j ≠ a → Y a j = 0) ∧ (∀ i, i ≠ a → Y i a = 0) := by
  rw [mem_commutant_iff, fmat, ← Matrix.ext_iff]
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun i hi => ?_⟩
    · have hcell := h a j
      rw [mul_single_one_apply, single_one_mul_apply, if_neg hj, if_pos rfl] at hcell
      exact hcell.symm
    · have hcell := h i a
      rw [mul_single_one_apply, single_one_mul_apply, if_pos rfl, if_neg hi] at hcell
      exact hcell
  · rintro ⟨h1, h2⟩ p q
    rw [mul_single_one_apply, single_one_mul_apply]
    by_cases hp : p = a <;> by_cases hq : q = a
    · subst hp; subst hq; simp
    · subst hp; simp [hq, h1 q hq]
    · subst hq; simp [hp, h2 p hp]
    · simp [hp, hq]

/-- The linear functional `X ↦ X a b - X b a`, whose kernel is the extremal hyperplane. -/
def evalSub (a b : Fin n) : Matrix (Fin n) (Fin n) K →ₗ[K] K where
  toFun X := X a b - X b a
  map_add' := by intro X Y; simp; ring
  map_smul' := by intro c X; simp [mul_sub]

@[simp] lemma evalSub_apply (a b : Fin n) (X : Matrix (Fin n) (Fin n) K) :
    evalSub (K := K) a b X = X a b - X b a := rfl

/-- The explicit `C(g)`-part in the decomposition of an element of the hyperplane. -/
def Zof (a b : Fin n) (X : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j =>
    if i = a then (if j = a then 0 else X a j)
    else if j = a then X i a
    else if i = b then (if j = b then 0 else -(X a j))
    else if j = b then -(X i a)
    else 0

lemma Zof_row_sum {a b : Fin n} (hab : a ≠ b) (X : Matrix (Fin n) (Fin n) K)
    (hX : X a b = X b a) (i : Fin n) :
    Zof a b X i a + Zof a b X i b = (X a b) * uvec (K := K) a b i := by
  by_cases hia : i = a
  · subst hia; simp [Zof, uvec, hab, Ne.symm hab]
  · by_cases hib : i = b
    · subst hib; simp [Zof, uvec, hia, hX]
    · simp [Zof, uvec, hia, hib, Ne.symm hab]

lemma Zof_col_sum {a b : Fin n} (hab : a ≠ b) (X : Matrix (Fin n) (Fin n) K)
    (hX : X a b = X b a) (j : Fin n) :
    Zof a b X a j + Zof a b X b j = (X a b) * uvec (K := K) a b j := by
  by_cases hja : j = a
  · subst hja; simp [Zof, uvec, hab, Ne.symm hab, hX]
  · by_cases hjb : j = b
    · subst hjb; simp [Zof, uvec, hja]
    · simp [Zof, uvec, hja, hjb, Ne.symm hab]

lemma Zof_mem_commutant_gmat {a b : Fin n} (hab : a ≠ b) (X : Matrix (Fin n) (Fin n) K)
    (hX : X a b = X b a) : Zof a b X ∈ commutant (gmat (K := K) a b) := by
  rw [mem_commutant_gmat_iff]
  intro i j
  rw [Zof_row_sum hab X hX i, Zof_col_sum hab X hX j]
  ring

lemma sub_Zof_mem_commutant_fmat {a b : Fin n} (X : Matrix (Fin n) (Fin n) K) :
    X - Zof a b X ∈ commutant (fmat (K := K) a) := by
  rw [mem_commutant_fmat_iff]
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · simp [Zof, hj]
  · simp [Zof, hi]

lemma fmat_not_scalar {a b : Fin n} (hab : a ≠ b) : ¬ IsScalarMat (fmat (K := K) a) := by
  rintro ⟨c, hc⟩
  have h1 : (fmat (K := K) a) a a = 1 := by simp [fmat]
  have h2 : (fmat (K := K) a) b b = 0 := by simp [fmat, hab]
  rw [hc] at h1 h2
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1 h2
  exact one_ne_zero (h1.symm.trans h2)

lemma gmat_not_scalar {a b : Fin n} (hab : a ≠ b) : ¬ IsScalarMat (gmat (K := K) a b) := by
  rintro ⟨c, hc⟩
  have h1 : (gmat (K := K) a b) a b = 1 := by
    simp [gmat, uvec_a (K := K) hab, uvec_b (K := K) hab]
  rw [hc] at h1
  simp only [Matrix.smul_apply, Matrix.one_apply_ne hab, smul_eq_mul, mul_zero] at h1
  exact one_ne_zero h1.symm

/-- For the extremal pair, the sum of the two commutants is exactly the hyperplane
`{X | X a b = X b a}`. -/
theorem commutant_sup_eq_ker {a b : Fin n} (hab : a ≠ b) :
    commutant (fmat (K := K) a) ⊔ commutant (gmat (K := K) a b)
      = LinearMap.ker (evalSub (K := K) a b) := by
  apply le_antisymm
  · refine sup_le (fun Y hY => ?_) (fun Z hZ => ?_)
    · rw [mem_commutant_fmat_iff] at hY
      simp only [LinearMap.mem_ker, evalSub_apply, hY.1 b (Ne.symm hab), hY.2 b (Ne.symm hab),
        sub_self]
    · rw [mem_commutant_gmat_iff] at hZ
      have h := hZ a a
      rw [uvec_a (K := K) hab] at h
      simp only [mul_one, one_mul] at h
      simp only [LinearMap.mem_ker, evalSub_apply, sub_eq_zero]
      linear_combination h
  · intro X hX
    simp only [LinearMap.mem_ker, evalSub_apply, sub_eq_zero] at hX
    have h1 : X = (X - Zof a b X) + Zof a b X := by abel
    rw [h1]
    exact Submodule.add_mem_sup (sub_Zof_mem_commutant_fmat X) (Zof_mem_commutant_gmat hab X hX)

theorem finrank_ker_evalSub {a b : Fin n} (hab : a ≠ b) :
    Module.finrank K ↥(LinearMap.ker (evalSub (K := K) a b)) = n ^ 2 - 1 := by
  have hsurj : Function.Surjective (evalSub (K := K) a b) := by
    intro c
    refine ⟨c • Matrix.single a b (1 : K), ?_⟩
    simp [evalSub, hab, Ne.symm hab]
  have hrange : Module.finrank K ↥(LinearMap.range (evalSub (K := K) a b)) = 1 := by
    rw [LinearMap.range_eq_top.2 hsurj]; simp
  have h := LinearMap.finrank_range_add_finrank_ker (evalSub (K := K) a b)
  rw [hrange, Module.finrank_matrix] at h
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at h
  have hn : n * n = n ^ 2 := by ring
  omega

/-- **Theorem A, attainment.**  In every dimension `n ≥ 2` and over every field there is a pair
of non-scalar matrices whose commutants span a hyperplane. -/
theorem exists_extremal_pair (hn : 2 ≤ n) :
    ∃ f g : Matrix (Fin n) (Fin n) K, ¬ IsScalarMat f ∧ ¬ IsScalarMat g ∧
      Module.finrank K ↥(commutant f ⊔ commutant g) = n ^ 2 - 1 := by
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  have hab : (⟨0, h0⟩ : Fin n) ≠ ⟨1, h1⟩ := by simp [Fin.ext_iff]
  refine ⟨fmat (K := K) ⟨0, h0⟩, gmat (K := K) ⟨0, h0⟩ ⟨1, h1⟩, fmat_not_scalar hab,
    gmat_not_scalar hab, ?_⟩
  rw [commutant_sup_eq_ker hab]
  exact finrank_ker_evalSub hab

/-- **Theorem A of Q655.**  Over an arbitrary field `K` and for `n ≥ 2`, the largest possible
dimension of `C(f) + C(g)`, where `f` and `g` are non-scalar endomorphisms of an
`n`-dimensional space, is exactly `n² - 1`. -/
theorem isGreatest_finrank_commutant_sup (K : Type*) [Field K] (n : ℕ) (hn : 2 ≤ n) :
    IsGreatest {d : ℕ | ∃ f g : Matrix (Fin n) (Fin n) K,
        ¬ IsScalarMat f ∧ ¬ IsScalarMat g ∧
        Module.finrank K ↥(commutant f ⊔ commutant g) = d} (n ^ 2 - 1) :=
  ⟨exists_extremal_pair hn, by rintro d ⟨f, g, hf, hg, rfl⟩; exact finrank_commutant_sup_le hf hg⟩

end Q655
