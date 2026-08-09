import RMS.Q655Witness

/-!
# Q655 — Stage 5D, part 2: the block identification

Let `F = U₁ V₁` and `G = U₂ V₂` be rank factorisations through `Fin r` and `Fin s`, and suppose
that the combined matrices `U = [U₁ | U₂]` and `V = [V₁ ; V₂]` are injective resp. surjective.
Then a matrix commuting with both `F` and `G` intertwines `U` and `V` through a *block diagonal*
multiplier, and the pair of diagonal blocks lies in the two-arrow space of

  `V * U = [[A₀, B], [C, D₀]]`,   `A₀ = V₁ U₁`, `B = V₁ U₂`, `C = V₂ U₁`, `D₀ = V₂ U₂`.

Combined with the exact sequence of Stage 5C this computes `dim (C(F) ⊓ C(G))`.
-/

namespace Q655

open Matrix Module

variable {K : Type*} [Field K] {n r s : ℕ}

/-- The block diagonal embedding of a pair of square matrices. -/
def blockDiagLin (K : Type*) [Field K] (r s : ℕ) :
    (Matrix (Fin r) (Fin r) K × Matrix (Fin s) (Fin s) K) →ₗ[K]
      Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) K where
  toFun PQ := Matrix.fromBlocks PQ.1 0 0 PQ.2
  map_add' := by intro x y; ext (i | i) (j | j) <;> simp
  map_smul' := by intro c x; ext (i | i) (j | j) <;> simp

@[simp] lemma blockDiagLin_apply (P : Matrix (Fin r) (Fin r) K) (Q : Matrix (Fin s) (Fin s) K) :
    blockDiagLin K r s (P, Q) = Matrix.fromBlocks P 0 0 Q := rfl

lemma blockDiagLin_injective : Function.Injective (blockDiagLin K r s) := by
  rintro ⟨P, Q⟩ ⟨P', Q'⟩ h
  obtain ⟨h1, -, -, h4⟩ := Matrix.fromBlocks_inj.1 h
  exact Prod.ext h1 h4

/-- The image of the two-arrow space under the block diagonal embedding. -/
def blockDiagSpace (A₀ : Matrix (Fin r) (Fin r) K) (D₀ : Matrix (Fin s) (Fin s) K)
    (B : Matrix (Fin r) (Fin s) K) (C : Matrix (Fin s) (Fin r) K) :
    Submodule K (Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) K) :=
  (twoArrow A₀ D₀ B C).map (blockDiagLin K r s)

lemma finrank_blockDiagSpace (A₀ : Matrix (Fin r) (Fin r) K) (D₀ : Matrix (Fin s) (Fin s) K)
    (B : Matrix (Fin r) (Fin s) K) (C : Matrix (Fin s) (Fin r) K) :
    finrank K ↥(blockDiagSpace A₀ D₀ B C) = finrank K ↥(twoArrow A₀ D₀ B C) :=
  ((Submodule.equivMapOfInjective _ blockDiagLin_injective _).finrank_eq).symm

lemma mem_blockDiagSpace_iff {A₀ : Matrix (Fin r) (Fin r) K} {D₀ : Matrix (Fin s) (Fin s) K}
    {B : Matrix (Fin r) (Fin s) K} {C : Matrix (Fin s) (Fin r) K}
    {Z : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) K} :
    Z ∈ blockDiagSpace A₀ D₀ B C ↔
      ∃ P Q, (P, Q) ∈ twoArrow A₀ D₀ B C ∧ Z = Matrix.fromBlocks P 0 0 Q := by
  constructor
  · rintro ⟨⟨P, Q⟩, hPQ, rfl⟩
    exact ⟨P, Q, hPQ, rfl⟩
  · rintro ⟨P, Q, hPQ, rfl⟩
    exact ⟨(P, Q), hPQ, rfl⟩

/-- A block diagonal matrix commutes with a `2 × 2` block matrix exactly when the two diagonal
entries form a member of the two-arrow space. -/
lemma blockDiag_comm_iff {A₀ : Matrix (Fin r) (Fin r) K} {D₀ : Matrix (Fin s) (Fin s) K}
    {B : Matrix (Fin r) (Fin s) K} {C : Matrix (Fin s) (Fin r) K}
    {P : Matrix (Fin r) (Fin r) K} {Q : Matrix (Fin s) (Fin s) K} :
    Matrix.fromBlocks P 0 0 Q * Matrix.fromBlocks A₀ B C D₀
        = Matrix.fromBlocks A₀ B C D₀ * Matrix.fromBlocks P 0 0 Q ↔
      (P, Q) ∈ twoArrow A₀ D₀ B C := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.fromBlocks_inj, mem_twoArrow_iff]
  tauto

/-! ## The main block computation -/

section

variable {U₁ : Matrix (Fin n) (Fin r) K} {U₂ : Matrix (Fin n) (Fin s) K}
  {V₁ : Matrix (Fin r) (Fin n) K} {V₂ : Matrix (Fin s) (Fin n) K}
  {U' : Matrix (Fin r ⊕ Fin s) (Fin n) K} {W : Matrix (Fin n) (Fin r ⊕ Fin s) K}

/-- The first block of a left inverse of `[U₁ | U₂]` is a left inverse of `U₁`. -/
lemma toRows₁_mul_left (hU : U' * Matrix.fromCols U₁ U₂ = 1) : U'.toRows₁ * U₁ = 1 := by
  ext i j
  have h := congrFun (congrFun hU (Sum.inl i)) (Sum.inl j)
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

lemma toRows₂_mul_left (hU : U' * Matrix.fromCols U₁ U₂ = 1) : U'.toRows₂ * U₂ = 1 := by
  ext i j
  have h := congrFun (congrFun hU (Sum.inr i)) (Sum.inr j)
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

lemma mul_toCols₁_right (hW : Matrix.fromRows V₁ V₂ * W = 1) : V₁ * W.toCols₁ = 1 := by
  ext i j
  have h := congrFun (congrFun hW (Sum.inl i)) (Sum.inl j)
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

lemma mul_toCols₂_right (hW : Matrix.fromRows V₁ V₂ * W = 1) : V₂ * W.toCols₂ = 1 := by
  ext i j
  have h := congrFun (congrFun hW (Sum.inr i)) (Sum.inr j)
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

/-- The common commutant of two matrices given by compatible rank factorisations is the
intertwining space of the combined factorisation, with block diagonal multipliers. -/
theorem inf_commutant_eq_interSpace (hU : U' * Matrix.fromCols U₁ U₂ = 1)
    (hW : Matrix.fromRows V₁ V₂ * W = 1) :
    commutant (U₁ * V₁) ⊓ commutant (U₂ * V₂)
      = interSpace (Matrix.fromCols U₁ U₂) (Matrix.fromRows V₁ V₂)
          (blockDiagSpace (V₁ * U₁) (V₂ * U₂) (V₁ * U₂) (V₂ * U₁)) := by
  have hU1 := toRows₁_mul_left hU
  have hU2 := toRows₂_mul_left hU
  have hW1 := mul_toCols₁_right hW
  have hW2 := mul_toCols₂_right hW
  ext X
  constructor
  · rintro ⟨hX1, hX2⟩
    obtain ⟨P, -, hP1, hP2⟩ :=
      (mem_interSpace_iff (U := U₁) (V := V₁)).1
        ((commutant_eq_interSpace hU1 hW1) ▸ hX1)
    obtain ⟨Q, -, hQ1, hQ2⟩ :=
      (mem_interSpace_iff (U := U₂) (V := V₂)).1
        ((commutant_eq_interSpace hU2 hW2) ▸ hX2)
    have hXU : X * Matrix.fromCols U₁ U₂
        = Matrix.fromCols U₁ U₂ * Matrix.fromBlocks P 0 0 Q := by
      rw [Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, hP1, hQ1]
      simp
    have hVX : Matrix.fromRows V₁ V₂ * X
        = Matrix.fromBlocks P 0 0 Q * Matrix.fromRows V₁ V₂ := by
      rw [Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows, hP2, hQ2]
      simp
    have hcomm : Matrix.fromBlocks P 0 0 Q * (Matrix.fromRows V₁ V₂ * Matrix.fromCols U₁ U₂)
        = (Matrix.fromRows V₁ V₂ * Matrix.fromCols U₁ U₂) * Matrix.fromBlocks P 0 0 Q := by
      rw [← Matrix.mul_assoc, ← hVX, Matrix.mul_assoc, hXU, ← Matrix.mul_assoc]
    rw [Matrix.fromRows_mul_fromCols] at hcomm
    refine ⟨Matrix.fromBlocks P 0 0 Q, ?_, hXU, hVX⟩
    exact mem_blockDiagSpace_iff.2 ⟨P, Q, blockDiag_comm_iff.1 hcomm, rfl⟩
  · rintro ⟨Z, hZ, h1, h2⟩
    obtain ⟨P, Q, -, rfl⟩ := mem_blockDiagSpace_iff.1 hZ
    rw [Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks] at h1
    rw [Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows] at h2
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.fromCols_inj.eq_iff, Matrix.fromRows_inj.eq_iff] at h1 h2
    obtain ⟨hb1, hb2⟩ := h1
    obtain ⟨hc1, hc2⟩ := h2
    constructor
    · show X * (U₁ * V₁) = (U₁ * V₁) * X
      rw [← Matrix.mul_assoc, hb1, Matrix.mul_assoc, ← hc1, Matrix.mul_assoc]
    · show X * (U₂ * V₂) = (U₂ * V₂) * X
      rw [← Matrix.mul_assoc, hb2, Matrix.mul_assoc, ← hc2, Matrix.mul_assoc]

/-- **The block dimension formula.** -/
theorem finrank_inf_commutant_block (hU : U' * Matrix.fromCols U₁ U₂ = 1)
    (hW : Matrix.fromRows V₁ V₂ * W = 1) :
    finrank K ↥(commutant (U₁ * V₁) ⊓ commutant (U₂ * V₂))
      = (n - (r + s)) ^ 2 + finrank K ↥(twoArrow (V₁ * U₁) (V₂ * U₂) (V₁ * U₂) (V₂ * U₁)) := by
  rw [inf_commutant_eq_interSpace hU hW,
    finrank_interSpace hU hW _ (fun Z hZ => by
      obtain ⟨P, Q, hPQ, rfl⟩ := mem_blockDiagSpace_iff.1 hZ
      rw [Matrix.fromRows_mul_fromCols]
      exact blockDiag_comm_iff.2 hPQ),
    finrank_blockDiagSpace]
  simp

end

end Q655
