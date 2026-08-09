import RMS.Q655Descent

/-!
# Q655 — Stage 6: extremality forces a scalar-plus-rank-one member

This file sets up the geometric scalar rank over an algebraic closure, proves that it exists and
is positive for a non-scalar matrix, and derives the Stage 6 conclusion

  extremal pair  ⟹  one member is a scalar plus a rank one matrix

*from* the Stage 5 inequality `dim (C(f) ⊔ C(g)) ≤ n² - min r s`, which is stated here as the
predicate `ScalarRankBound`.  Stage 5 itself is **not** proved in this development; it is the one
remaining input, and it is carried explicitly as a hypothesis of the theorems below.
-/

namespace Q655

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

/-- Entrywise extension of a matrix to the algebraic closure of the base field. -/
noncomputable def extend (A : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) (AlgebraicClosure K) :=
  A.map (algebraMap K (AlgebraicClosure K))

/-- `r` is the geometric scalar rank of `f`: the minimum, over all scalars `μ` of the algebraic
closure, of the rank of `f - μ`. -/
def IsGeometricScalarRank (f : Matrix (Fin n) (Fin n) K) (r : ℕ) : Prop :=
  (∃ lam : AlgebraicClosure K,
      (extend f - lam • (1 : Matrix (Fin n) (Fin n) (AlgebraicClosure K))).rank = r) ∧
    (∀ mu : AlgebraicClosure K,
      r ≤ (extend f - mu • (1 : Matrix (Fin n) (Fin n) (AlgebraicClosure K))).rank)

/-- The geometric scalar rank exists. -/
theorem exists_isGeometricScalarRank (f : Matrix (Fin n) (Fin n) K) :
    ∃ r, IsGeometricScalarRank f r := by
  classical
  have h : ∃ r : ℕ, ∃ lam : AlgebraicClosure K,
      (extend f - lam • (1 : Matrix (Fin n) (Fin n) (AlgebraicClosure K))).rank = r :=
    ⟨_, 0, rfl⟩
  exact ⟨Nat.find h, Nat.find_spec h, fun mu => Nat.find_le ⟨mu, rfl⟩⟩

/-- A non-scalar matrix has positive geometric scalar rank. -/
theorem one_le_geometricScalarRank_of_not_scalar (hn : 1 ≤ n)
    {f : Matrix (Fin n) (Fin n) K} {r : ℕ} (hf : ¬ IsScalarMat f)
    (hr : IsGeometricScalarRank f r) : 1 ≤ r := by
  rcases Nat.eq_zero_or_pos r with h0 | h; swap
  · exact h
  subst h0
  obtain ⟨⟨lam, hlam⟩, -⟩ := hr
  exfalso
  set B := extend f - lam • (1 : Matrix (Fin n) (Fin n) (AlgebraicClosure K)) with hBdef
  have hB : B = 0 := by
    by_contra hne
    have := one_le_rank_of_ne_zero hne
    omega
  have hoff : ∀ i j : Fin n, i ≠ j → f i j = 0 := by
    intro i j hij
    have : B i j = 0 := by rw [hB]; rfl
    rw [hBdef] at this
    simp only [extend, Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply,
      Matrix.one_apply_ne hij, smul_zero, sub_zero] at this
    exact (map_eq_zero_iff _ (algebraMap K (AlgebraicClosure K)).injective).1 this
  have hdiag : ∀ i : Fin n, algebraMap K (AlgebraicClosure K) (f i i) = lam := by
    intro i
    have : B i i = 0 := by rw [hB]; rfl
    rw [hBdef] at this
    simp only [extend, Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
    exact sub_eq_zero.1 this
  have h0 : 0 < n := hn
  refine hf ⟨f ⟨0, h0⟩ ⟨0, h0⟩, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst hij
    have := (hdiag i).trans (hdiag ⟨0, h0⟩).symm
    have := (algebraMap K (AlgebraicClosure K)).injective this
    simp [Matrix.one_apply_eq, this]
  · simp [hoff i j hij, Matrix.one_apply_ne hij]

/-- The Stage 5 inequality, as a predicate.  **This is the one statement of the classification
programme that is not proved in this development.** -/
def ScalarRankBound (K : Type*) [Field K] (n : ℕ) : Prop :=
  ∀ (f g : Matrix (Fin n) (Fin n) K) (r s : ℕ), IsGeometricScalarRank f r →
    IsGeometricScalarRank g s → finrank K ↥(commutant f ⊔ commutant g) ≤ n ^ 2 - min r s

/-- **Stage 6, relative to Stage 5.**  Granting the scalar-rank inequality, an extremal pair has
a member that is a scalar plus a rank one matrix. -/
theorem extremal_forces_scalarPlusRankOne_of_bound (hn : 3 ≤ n) (hbound : ScalarRankBound K n)
    {f g : Matrix (Fin n) (Fin n) K} (hf : ¬ IsScalarMat f) (hg : ¬ IsScalarMat g)
    (hext : finrank K ↥(commutant f ⊔ commutant g) = n ^ 2 - 1) :
    IsScalarPlusRankOne f ∨ IsScalarPlusRankOne g := by
  obtain ⟨r, hr⟩ := exists_isGeometricScalarRank f
  obtain ⟨s, hs⟩ := exists_isGeometricScalarRank g
  have hr1 : 1 ≤ r := one_le_geometricScalarRank_of_not_scalar (by omega) hf hr
  have hs1 : 1 ≤ s := one_le_geometricScalarRank_of_not_scalar (by omega) hg hs
  have hle := hbound f g r s hr hs
  have hnn : 2 ≤ n ^ 2 := by nlinarith [hn]
  have hmin : min r s = 1 := by
    rcases Nat.lt_or_ge (min r s) 2 with h | h
    · omega
    · exfalso; omega
  -- one of the two matrices differs from a scalar of the closure by a rank one matrix
  have main : ∀ {a : Matrix (Fin n) (Fin n) K} {t : ℕ}, IsGeometricScalarRank a t → t = 1 →
      IsScalarPlusRankOne a := by
    intro a t ht ht1
    obtain ⟨⟨lam, hlam⟩, -⟩ := ht
    rw [ht1] at hlam
    have hrank1 : IsRankOneMat
        (extend a - lam • (1 : Matrix (Fin n) (Fin n) (AlgebraicClosure K))) :=
      isRankOneMat_iff_rank_eq_one.2 hlam
    obtain ⟨lam0, -, hR⟩ := rank_one_scalar_descends (K := K) (L := AlgebraicClosure K) hn hrank1
    exact ⟨lam0, a - lam0 • 1, hR, by abel⟩
  rcases Nat.le_total r s with h | h
  · exact Or.inl (main hr (by omega))
  · exact Or.inr (main hs (by omega))

/-- **The equality classification, relative to the Stage 5 inequality.**  For `3 ≤ n` and
non-scalar `f, g` over an arbitrary field, granting `ScalarRankBound`, extremality is equivalent
to the explicit split / irreducible / repeated-root conditions. -/
theorem Q655_equality_classification_of_scalarRankBound (hn : 3 ≤ n)
    (hbound : ScalarRankBound K n) {f g : Matrix (Fin n) (Fin n) K}
    (hf : ¬ IsScalarMat f) (hg : ¬ IsScalarMat g) :
    finrank K ↥(commutant f ⊔ commutant g) = n ^ 2 - 1 ↔
      RankOneSideClass f g ∨ RankOneSideClass g f :=
  Q655_equality_classification_of_scalarPlusRankOne hn hf hg
    (fun hext => extremal_forces_scalarPlusRankOne_of_bound hn hbound hf hg hext)

end Q655
