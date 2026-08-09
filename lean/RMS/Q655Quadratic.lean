import RMS.Q655Stage2

/-!
# Q655 — Stage 3 assembly: the three quadratic types

We package the split, irreducible and repeated-root conditions into a single predicate
`QuadraticEqualityCase`, prove the trichotomy for monic quadratics over an arbitrary field
(with no division by two, so characteristic two is covered), and show that for a non-scalar
`f` satisfying a monic quadratic the pair action is extremal exactly in the classified cases.
-/

namespace Q655

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

/-! ## The three cases -/

/-- `f = a•1 + (b-a)•P` for an idempotent `P ≠ 0, 1` with `a ≠ b`, both blocks good. -/
def SplitQuadraticCase (f : Matrix (Fin n) (Fin n) K) (u phi : Vec K n) : Prop :=
  ∃ (a b : K) (P : Matrix (Fin n) (Fin n) K), a ≠ b ∧ P * P = P ∧ P ≠ 0 ∧ P ≠ 1 ∧
    f = a • 1 + (b - a) • P ∧ BlockGood P u phi ∧ BlockGood (1 - P) u phi

/-- `f` satisfies a monic quadratic with no root in `K`. -/
def IrreducibleQuadraticCase (f : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ c d : K, f * f + c • f + d • (1 : Matrix (Fin n) (Fin n) K) = 0 ∧
    ∀ x : K, x * x + c * x + d ≠ 0

/-- `f = a•1 + N` with `N ≠ 0`, `N² = 0`, and the audited nondegeneracy table. -/
def RepeatedRootCase (f : Matrix (Fin n) (Fin n) K) (u phi : Vec K n) : Prop :=
  ∃ (a : K) (N : Matrix (Fin n) (Fin n) K), f = a • 1 + N ∧ N ≠ 0 ∧ N * N = 0 ∧
    ((N *ᵥ u ≠ 0 ∧ phi ᵥ* N ≠ 0) ∨
     (N *ᵥ u = 0 ∧ phi ᵥ* N ≠ 0 ∧ IsRankOneMat N ∧ ¬ ∃ x, N *ᵥ x = u) ∨
     (N *ᵥ u ≠ 0 ∧ phi ᵥ* N = 0 ∧ IsRankOneMat N ∧ ∃ x, N *ᵥ x = 0 ∧ phi ⬝ᵥ x ≠ 0))

/-- The disjunction of the three classified quadratic cases. -/
def QuadraticEqualityCase (f : Matrix (Fin n) (Fin n) K) (u phi : Vec K n) : Prop :=
  SplitQuadraticCase f u phi ∨ IrreducibleQuadraticCase f ∨ RepeatedRootCase f u phi

/-! ## Sufficiency: each case is extremal -/

theorem pairAction_rank_of_quadraticEqualityCase (hn : 3 ≤ n)
    {f : Matrix (Fin n) (Fin n) K} {u phi : Vec K n} (hu : u ≠ 0) (hphi : phi ≠ 0)
    (h : QuadraticEqualityCase f u phi) :
    finrank K ↥(LinearMap.range (pairAction f u phi)) = 2 * n - 2 := by
  rcases h with ⟨a, b, P, hab, hP, hP0, hP1, hf, hg1, hg2⟩ | ⟨c, d, hq, hnoroot⟩ |
    ⟨a, N, hf, hN0, hN2, hcases⟩
  · exact (pairAction_rank_split_iff hab hP hP0 hP1 hf u phi).2 ⟨hg1, hg2⟩
  · exact pairAction_rank_irreducible_quadratic hq hnoroot hu hphi
  · have hcom : commutant f = commutant N := by rw [hf, commutant_smul_one_add]
    rw [range_pairAction_congr hcom u phi]
    exact (pairAction_rank_squareZero_iff hn hN0 hN2 hu hphi).2 hcases

/-! ## The trichotomy for monic quadratics -/

/-- A monic quadratic with a root `a` factors as `(X - a)(X - b)` with `b = -c - a`. -/
lemma quadratic_factor {c d a : K} (ha : a * a + c * a + d = 0)
    {f : Matrix (Fin n) (Fin n) K}
    (hq : f * f + c • f + d • (1 : Matrix (Fin n) (Fin n) K) = 0) :
    (f - a • 1) * (f - (-c - a) • 1) = 0 := by
  have hd : d = -(a * a) - c * a := by linear_combination ha
  have : (f - a • 1) * (f - (-c - a) • 1) = f * f + c • f + d • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [hd]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul,
      mul_one, smul_smul]
    module
  rw [this, hq]

/-! ## Necessity, given a quadratic relation -/

/-- If `f` is non-scalar and satisfies a monic quadratic, then an extremal pair action forces
one of the three classified cases. -/
theorem quadraticEqualityCase_of_pairAction_rank (hn : 3 ≤ n)
    {f : Matrix (Fin n) (Fin n) K} {u phi : Vec K n} (hf : ¬ IsScalarMat f)
    (hu : u ≠ 0) (hphi : phi ≠ 0)
    (hrank : finrank K ↥(LinearMap.range (pairAction f u phi)) = 2 * n - 2) :
    QuadraticEqualityCase f u phi := by
  obtain ⟨c, d, hq⟩ := exists_quadratic_of_pairAction_extremal hn hf hu hphi hrank
  by_cases hnoroot : ∀ x : K, x * x + c * x + d ≠ 0
  · exact Or.inr (Or.inl ⟨c, d, hq, hnoroot⟩)
  push_neg at hnoroot
  obtain ⟨a, ha⟩ := hnoroot
  set b : K := -c - a with hb
  have hfac := quadratic_factor ha hq
  rw [← hb] at hfac
  by_cases hab : a = b
  · -- repeated root
    refine Or.inr (Or.inr ⟨a, f - a • 1, by module, ?_, ?_, ?_⟩)
    · intro h
      exact hf ⟨a, by linear_combination (norm := module) h⟩
    · rw [← hab] at hfac; exact hfac
    · have hN0 : f - a • (1 : Matrix (Fin n) (Fin n) K) ≠ 0 := by
        intro h
        exact hf ⟨a, by linear_combination (norm := module) h⟩
      have hN2 : (f - a • 1) * (f - a • (1 : Matrix (Fin n) (Fin n) K)) = 0 := by
        rw [← hab] at hfac; exact hfac
      have hcom : commutant f = commutant (f - a • (1 : Matrix (Fin n) (Fin n) K)) := by
        have : f = a • (1 : Matrix (Fin n) (Fin n) K) + (f - a • 1) := by module
        rw [this, commutant_smul_one_add]
        congr 1
        module
      rw [range_pairAction_congr hcom u phi] at hrank
      exact (pairAction_rank_squareZero_iff hn hN0 hN2 hu hphi).1 hrank
  · -- two distinct roots
    have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
    set P : Matrix (Fin n) (Fin n) K := (b - a)⁻¹ • (f - a • 1) with hP
    have hfP : f = a • 1 + (b - a) • P := by
      rw [hP, smul_smul, mul_inv_cancel₀ hba, one_smul]
      module
    have hsq : (f - a • (1 : Matrix (Fin n) (Fin n) K)) * (f - a • 1) =
        (b - a) • (f - a • 1) := by
      have hexp : (f - a • (1 : Matrix (Fin n) (Fin n) K)) * (f - b • 1) = 0 := hfac
      have : (f - a • (1 : Matrix (Fin n) (Fin n) K)) * (f - a • 1) -
          (b - a) • (f - a • (1 : Matrix (Fin n) (Fin n) K)) =
          (f - a • 1) * (f - b • 1) := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul,
          mul_one, smul_smul]
        module
      rw [hexp] at this
      linear_combination (norm := module) this
    have hPidem : P * P = P := by
      rw [hP, Matrix.smul_mul, Matrix.mul_smul, hsq, smul_smul, smul_smul,
        inv_mul_cancel_right₀ hba]
    have hP0 : P ≠ 0 := by
      intro h
      have h2 : f - a • (1 : Matrix (Fin n) (Fin n) K) = 0 := by
        have hcg := congrArg (fun M : Matrix (Fin n) (Fin n) K => (b - a) • M) h
        simp only [hP, smul_smul, mul_inv_cancel₀ hba, one_smul, smul_zero] at hcg
        exact hcg
      exact hf ⟨a, by linear_combination (norm := module) h2⟩
    have hP1 : P ≠ 1 := by
      intro h
      rw [h] at hfP
      exact hf ⟨b, by rw [hfP]; module⟩
    exact Or.inl ⟨a, b, P, hab, hPidem, hP0, hP1, hfP,
      ((pairAction_rank_split_iff hab hPidem hP0 hP1 hfP u phi).1 hrank).1,
      ((pairAction_rank_split_iff hab hPidem hP0 hP1 hfP u phi).1 hrank).2⟩

/-- **Stage 3 completion gate.**  For a non-scalar `f` and nonzero `u, phi`, the pair action is
extremal exactly in the three classified quadratic cases. -/
theorem pairAction_extremal_iff_quadraticEquality (hn : 3 ≤ n)
    {f : Matrix (Fin n) (Fin n) K} {u phi : Vec K n} (hf : ¬ IsScalarMat f)
    (hu : u ≠ 0) (hphi : phi ≠ 0) :
    finrank K ↥(LinearMap.range (pairAction f u phi)) = 2 * n - 2 ↔
      QuadraticEqualityCase f u phi :=
  ⟨quadraticEqualityCase_of_pairAction_rank hn hf hu hphi,
    pairAction_rank_of_quadraticEqualityCase hn hu hphi⟩

end Q655
