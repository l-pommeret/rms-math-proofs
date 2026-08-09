import RMS.Q655GenPos

/-!
# Q655 — Stage 5: the scalar-rank inequality

Combining the centralizer estimate of Stage 5B (large rank sum) with the generic-position
computation of Stages 5C–5E (small rank sum) gives the decisive inequality

  `dim (C(f) ⊔ C(g)) ≤ n ^ 2 - min r s`,

where `r`, `s` are the geometric scalar ranks of `f` and `g`, i.e. the minimal ranks of
`f - λ` and `g - μ` over scalars `λ, μ` of an algebraic closure.
-/

namespace Q655

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

/-- The commutant is unchanged by subtracting a scalar matrix. -/
lemma commutant_sub_smul_one (A : Matrix (Fin n) (Fin n) K) (lam : K) :
    commutant (A - lam • (1 : Matrix (Fin n) (Fin n) K)) = commutant A := by
  have : A - lam • (1 : Matrix (Fin n) (Fin n) K) = (-lam) • (1 : Matrix (Fin n) (Fin n) K) + A := by
    rw [neg_smul]; abel
  rw [this, commutant_smul_one_add]

/-- The kernel of `a - λ` is small when the rank of every scalar shift is at least `r`. -/
lemma finrank_ker_le_of_rank_ge {r : ℕ} {a : Matrix (Fin n) (Fin n) K}
    (h : ∀ lam : K, r ≤ (a - lam • (1 : Matrix (Fin n) (Fin n) K)).rank) (lam : K) :
    finrank K ↥(LinearMap.ker (a - lam • (1 : Matrix (Fin n) (Fin n) K)).mulVecLin) ≤ n - r := by
  have h1 := LinearMap.finrank_range_add_finrank_ker
    (a - lam • (1 : Matrix (Fin n) (Fin n) K)).mulVecLin
  have h2 : (a - lam • (1 : Matrix (Fin n) (Fin n) K)).rank
      = finrank K ↥(LinearMap.range (a - lam • (1 : Matrix (Fin n) (Fin n) K)).mulVecLin) := rfl
  have h3 : finrank K (Fin n → K) = n := by simp [Module.finrank_pi]
  have h4 := h lam
  omega

/-- **The core inequality over an algebraically closed field.** -/
theorem core_scalar_rank_bound [IsAlgClosed K] {r s : ℕ} {F G : Matrix (Fin n) (Fin n) K}
    (hF : F.rank = r) (hFmin : ∀ lam : K, r ≤ (F - lam • (1 : Matrix (Fin n) (Fin n) K)).rank)
    (hG : G.rank = s) (hGmin : ∀ lam : K, s ≤ (G - lam • (1 : Matrix (Fin n) (Fin n) K)).rank)
    (hle : r ≤ s) :
    finrank K ↥(commutant F ⊔ commutant G) + r ≤ n ^ 2 := by
  classical
  have hrn : r ≤ n := by
    have := Matrix.rank_le_card_width F
    simp only [Fintype.card_fin] at this
    omega
  have hsn : s ≤ n := by
    have := Matrix.rank_le_card_width G
    simp only [Fintype.card_fin] at this
    omega
  rcases le_or_gt (r + s) n with hsum | hsum
  · exact finrank_sup_commutant_add_le hsum hle hF hG
  -- large rank sum: the centralizer estimate of Stage 5B
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : finrank K ↥(commutant F ⊔ commutant G) = 0 := by
      have hle' : finrank K ↥(commutant F ⊔ commutant G)
          ≤ finrank K (Matrix (Fin 0) (Fin 0) K) := Submodule.finrank_le _
      simpa [Module.finrank_matrix] using hle'
    omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hcF : finrank K ↥(commutant F) ≤ (m + 1) * ((m + 1) - r) :=
    finrank_commutant_le_mul (m + 1) F (finrank_ker_le_of_rank_ge hFmin)
  have hcG : finrank K ↥(commutant G) ≤ (m + 1) * ((m + 1) - s) :=
    finrank_commutant_le_mul (m + 1) G (finrank_ker_le_of_rank_ge hGmin)
  have hone : (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) ∈ commutant F ⊓ commutant G :=
    ⟨by show (1 : Matrix _ _ K) * F = F * 1; simp,
      by show (1 : Matrix _ _ K) * G = G * 1; simp⟩
  have hinf : 1 ≤ finrank K ↥(commutant F ⊓ commutant G) := by
    rcases Nat.eq_zero_or_pos (finrank K ↥(commutant F ⊓ commutant G)) with h0 | h
    · exfalso
      have hbot : commutant F ⊓ commutant G = ⊥ := Submodule.finrank_eq_zero.1 h0
      rw [hbot] at hone
      have h1 : (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 0 := hone
      exact one_ne_zero h1
    · exact h
  have hsupinf := Submodule.finrank_sup_add_finrank_inf_eq (commutant F) (commutant G)
  -- arithmetic
  have hab : ((m + 1) - r) + ((m + 1) - s) ≤ m := by omega
  have hmul : (m + 1) * ((m + 1) - r) + (m + 1) * ((m + 1) - s) ≤ (m + 1) * m := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ hab
  have hid : (m + 1) * m + (m + 1) = (m + 1) ^ 2 := by ring
  omega

/-- **Stage 5, ordered form.** -/
theorem scalar_rank_bound_aux {f g : Matrix (Fin n) (Fin n) K} {r s : ℕ}
    (hr : IsGeometricScalarRank f r) (hs : IsGeometricScalarRank g s) (hle : r ≤ s) :
    finrank K ↥(commutant f ⊔ commutant g) + r ≤ n ^ 2 := by
  classical
  obtain ⟨⟨lam, hlam⟩, hrmin⟩ := hr
  obtain ⟨⟨mu, hmu⟩, hsmin⟩ := hs
  set F : Matrix (Fin n) (Fin n) (AlgebraicClosure K) :=
    extend f - lam • (1 : Matrix (Fin n) (Fin n) (AlgebraicClosure K)) with hFdef
  set G : Matrix (Fin n) (Fin n) (AlgebraicClosure K) :=
    extend g - mu • (1 : Matrix (Fin n) (Fin n) (AlgebraicClosure K)) with hGdef
  have hFmin : ∀ nu : AlgebraicClosure K,
      r ≤ (F - nu • (1 : Matrix (Fin n) (Fin n) (AlgebraicClosure K))).rank := by
    intro nu
    have he : F - nu • (1 : Matrix (Fin n) (Fin n) (AlgebraicClosure K))
        = extend f - (lam + nu) • (1 : Matrix (Fin n) (Fin n) (AlgebraicClosure K)) := by
      rw [hFdef, add_smul]; abel
    rw [he]
    exact hrmin (lam + nu)
  have hGmin : ∀ nu : AlgebraicClosure K,
      s ≤ (G - nu • (1 : Matrix (Fin n) (Fin n) (AlgebraicClosure K))).rank := by
    intro nu
    have he : G - nu • (1 : Matrix (Fin n) (Fin n) (AlgebraicClosure K))
        = extend g - (mu + nu) • (1 : Matrix (Fin n) (Fin n) (AlgebraicClosure K)) := by
      rw [hGdef, add_smul]; abel
    rw [he]
    exact hsmin (mu + nu)
  have hcore := core_scalar_rank_bound hlam hFmin hmu hGmin hle
  rw [hFdef, hGdef, commutant_sub_smul_one, commutant_sub_smul_one] at hcore
  rw [← finrank_sup_commutant_map (algebraMap K (AlgebraicClosure K)) f g]
  exact hcore

/-- **Stage 5.**  The scalar-rank inequality over an arbitrary field. -/
theorem finrank_commutant_sup_le_scalarRank {f g : Matrix (Fin n) (Fin n) K} {r s : ℕ}
    (hr : IsGeometricScalarRank f r) (hs : IsGeometricScalarRank g s) :
    finrank K ↥(commutant f ⊔ commutant g) ≤ n ^ 2 - min r s := by
  rcases le_total r s with hle | hle
  · have h := scalar_rank_bound_aux hr hs hle
    rw [min_eq_left hle]
    omega
  · have h := scalar_rank_bound_aux hs hr hle
    rw [min_eq_right hle, sup_comm]
    omega

/-- The Stage 5 inequality in the packaged form used by Stage 6. -/
theorem scalarRankBound_holds (K : Type*) [Field K] (n : ℕ) : ScalarRankBound K n :=
  fun _ _ _ _ hr hs => finrank_commutant_sup_le_scalarRank hr hs

end Q655
