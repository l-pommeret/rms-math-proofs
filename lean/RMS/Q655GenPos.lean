import RMS.Q655Pair

/-!
# Q655 — Stage 5D: generic relative position

Let `F, G` be `n × n` matrices of ranks `r ≤ s` with `r + s ≤ n`.  Write rank factorisations
`F = U₁ V₁`, `G = U₂ V₂`.  For an invertible `h`, conjugating `G` by `h` does not change
`dim C(G)`, and the common centralizer `C(F) ⊓ C(h G h⁻¹)` is isomorphic to the kernel of the
coefficient matrix `pairMat F G h`, whose entries depend polynomially on `h`; hence the
intersection at `h = 1` is at least as large as at a generic `h`.  For a generic `h` the combined
matrices `U = [U₁, h U₂]` and `V = [V₁; V₂ h⁻¹]` are injective resp. surjective, so the block
identification applies: the common centralizer is the intertwining space of `U, V` with block
diagonal multipliers, which is the two-arrow space of Stage 5E.  Combining the dimension counts
gives

  `dim (C(F) ⊔ C(G)) + r ≤ n ^ 2`.
-/

namespace Q655

open Matrix Module Polynomial

variable {K : Type*} [Field K] {n : ℕ}

/-! ## Rank, injectivity and surjectivity -/

lemma injective_of_card_le_rank {p : Type*} [Fintype p] [DecidableEq p]
    {U : Matrix (Fin n) p K} (h : Fintype.card p ≤ U.rank) :
    Function.Injective U.mulVecLin := by
  have h2 := LinearMap.finrank_range_add_finrank_ker U.mulVecLin
  have h3 : finrank K (p → K) = Fintype.card p := by simp [Module.finrank_pi]
  have h4 : U.rank = finrank K ↥(LinearMap.range U.mulVecLin) := rfl
  have h5 : finrank K ↥(LinearMap.ker U.mulVecLin) = 0 := by omega
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.1 h5

lemma surjective_of_card_le_rank {p : Type*} [Fintype p] [DecidableEq p]
    {V : Matrix p (Fin n) K} (h : Fintype.card p ≤ V.rank) :
    Function.Surjective V.mulVecLin := by
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_of_finrank_eq ?_
  have h4 : V.rank = finrank K ↥(LinearMap.range V.mulVecLin) := rfl
  have h5 : finrank K (p → K) = Fintype.card p := by simp [Module.finrank_pi]
  have h6 : finrank K ↥(LinearMap.range V.mulVecLin) ≤ finrank K (p → K) :=
    Submodule.finrank_le _
  omega

lemma card_le_rank_of_leftInv {p : Type*} [Fintype p] [DecidableEq p]
    {U : Matrix (Fin n) p K} {U' : Matrix p (Fin n) K} (h : U' * U = 1) :
    Fintype.card p ≤ U.rank := by
  have h1 : (U' * U).rank ≤ U.rank := Matrix.rank_mul_le_right _ _
  rw [h, Matrix.rank_one] at h1
  exact h1

lemma card_le_rank_of_rightInv {p : Type*} [Fintype p] [DecidableEq p]
    {V : Matrix p (Fin n) K} {W : Matrix (Fin n) p K} (h : V * W = 1) :
    Fintype.card p ≤ V.rank := by
  have h1 : (V * W).rank ≤ V.rank := Matrix.rank_mul_le_left _ _
  rw [h, Matrix.rank_one] at h1
  exact h1

/-! ## The row witness -/

lemma rank_fromCols_comm {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (A : Matrix (Fin n) p K) (B : Matrix (Fin n) q K) :
    (Matrix.fromCols B A).rank = (Matrix.fromCols A B).rank := by
  have h : Matrix.fromCols B A
      = (Matrix.fromCols A B).submatrix ⇑(Equiv.refl (Fin n)) ⇑(Equiv.sumComm q p) := by
    ext i (j | j) <;> rfl
  rw [h, Matrix.rank_submatrix]

lemma exists_unit_fromRows_rank {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] (V₁ : Matrix p (Fin n) K) (V₂ : Matrix q (Fin n) K)
    (h1 : Fintype.card p ≤ V₁.rank) (h2 : Fintype.card q ≤ V₂.rank)
    (hpq : Fintype.card p + Fintype.card q ≤ n) :
    ∃ M : Matrix (Fin n) (Fin n) K, IsUnit M.det ∧
      Fintype.card p + Fintype.card q ≤ (Matrix.fromRows (V₁ * M) V₂).rank := by
  have hi1 : Function.Injective (V₁ᵀ).mulVecLin :=
    injective_of_card_le_rank (by rwa [Matrix.rank_transpose])
  have hi2 : Function.Injective (V₂ᵀ).mulVecLin :=
    injective_of_card_le_rank (by rwa [Matrix.rank_transpose])
  obtain ⟨M, hMunit, hM⟩ :=
    exists_unit_fromCols_rank (V₂ᵀ) (V₁ᵀ) hi2 hi1 (by omega)
  refine ⟨Mᵀ, by rwa [Matrix.det_transpose], ?_⟩
  have hEq : (Matrix.fromRows (V₁ * Mᵀ) V₂).rank = (Matrix.fromCols V₂ᵀ (M * V₁ᵀ)).rank := by
    rw [← Matrix.rank_transpose (Matrix.fromRows (V₁ * Mᵀ) V₂), Matrix.transpose_fromRows,
      Matrix.transpose_mul, Matrix.transpose_transpose, rank_fromCols_comm]
  rw [hEq]
  omega

/-! ## Polynomial families -/

lemma map_C_map_eval {m' p' : Type*} (A : Matrix m' p' K) (c : K) :
    (A.map (Polynomial.C : K →+* K[X])).map (Polynomial.evalRingHom c) = A := by
  ext i j; simp

/-- Three distinct elements of an infinite field. -/
lemma exists_three_nodes (K : Type*) [Field K] [Infinite K] :
    ∃ node : Fin 3 → K, Function.Injective node := by
  refine ⟨fun i => (Infinite.natEmbedding K) (i : ℕ), ?_⟩
  intro i j hij
  exact Fin.ext ((Infinite.natEmbedding K).injective hij)

/-! ## The generic position lemma -/

section

variable [Infinite K]

/-- **Choice of a generic conjugator.**  Given rank factorisations of `F` and `G` with
`r + s ≤ n`, there is an invertible `h` for which the two combined matrices have full rank and
the conjugated common commutant is no larger than the original one. -/
theorem exists_good_conjugator {r s : ℕ} {F G : Matrix (Fin n) (Fin n) K}
    {U₁ : Matrix (Fin n) (Fin r) K} {V₁ : Matrix (Fin r) (Fin n) K}
    {U₂ : Matrix (Fin n) (Fin s) K} {V₂ : Matrix (Fin s) (Fin n) K}
    {U₁' : Matrix (Fin r) (Fin n) K} {W₁ : Matrix (Fin n) (Fin r) K}
    {U₂' : Matrix (Fin s) (Fin n) K} {W₂ : Matrix (Fin n) (Fin s) K}
    (hU₁ : U₁' * U₁ = 1) (hW₁ : V₁ * W₁ = 1) (hU₂ : U₂' * U₂ = 1) (hW₂ : V₂ * W₂ = 1)
    (hrs : r + s ≤ n) :
    ∃ h : Matrix (Fin n) (Fin n) K, IsUnit h.det ∧
      (r + s ≤ (Matrix.fromCols U₁ (h * U₂)).rank) ∧
      (r + s ≤ (Matrix.fromRows (V₁ * h) V₂).rank) ∧
      finrank K ↥(pairSpace F G h) ≤ finrank K ↥(pairSpace F G 1) := by
  classical
  -- the two witnesses
  have hiU₁ : Function.Injective U₁.mulVecLin := by
    refine injective_of_card_le_rank ?_
    simpa using card_le_rank_of_leftInv hU₁
  have hiU₂ : Function.Injective U₂.mulVecLin := by
    refine injective_of_card_le_rank ?_
    simpa using card_le_rank_of_leftInv hU₂
  have hrV₁ : Fintype.card (Fin r) ≤ V₁.rank := card_le_rank_of_rightInv hW₁
  have hrV₂ : Fintype.card (Fin s) ≤ V₂.rank := card_le_rank_of_rightInv hW₂
  obtain ⟨hb, hbunit, hbrank⟩ :=
    exists_unit_fromCols_rank U₁ U₂ hiU₁ hiU₂ (by simpa using hrs)
  obtain ⟨hc, hcunit, hcrank⟩ :=
    exists_unit_fromRows_rank V₁ V₂ hrV₁ hrV₂ (by simpa using hrs)
  simp only [Fintype.card_fin] at hbrank hcrank
  -- the interpolating family
  obtain ⟨node, hnode⟩ := exists_three_nodes K
  set val : Fin 3 → Matrix (Fin n) (Fin n) K := ![1, hb, hc] with hval
  set H : Matrix (Fin n) (Fin n) K[X] := interpMatrix Finset.univ node val with hH
  have hHeval : ∀ i : Fin 3, H.map (Polynomial.evalRingHom (node i)) = val i := by
    intro i
    exact interpMatrix_eval (hnode.injOn) val (Finset.mem_univ i)
  -- the four polynomial matrices
  set Pcols : Matrix (Fin n) (Fin r ⊕ Fin s) K[X] :=
    Matrix.fromCols (U₁.map (Polynomial.C : K →+* K[X]))
      (H * U₂.map (Polynomial.C : K →+* K[X])) with hPcols
  set Prows : Matrix (Fin r ⊕ Fin s) (Fin n) K[X] :=
    Matrix.fromRows (V₁.map (Polynomial.C : K →+* K[X]) * H)
      (V₂.map (Polynomial.C : K →+* K[X])) with hProws
  set Ppair := pairMat (F.map (Polynomial.C : K →+* K[X])) (G.map (Polynomial.C : K →+* K[X])) H
    with hPpair
  have hPcols_eval : ∀ c : K, Pcols.map (Polynomial.evalRingHom c)
      = Matrix.fromCols U₁ ((H.map (Polynomial.evalRingHom c)) * U₂) := by
    intro c
    rw [hPcols, Matrix.fromCols_map, Matrix.map_mul, map_C_map_eval, map_C_map_eval]
  have hProws_eval : ∀ c : K, Prows.map (Polynomial.evalRingHom c)
      = Matrix.fromRows (V₁ * (H.map (Polynomial.evalRingHom c))) V₂ := by
    intro c
    rw [hProws, Matrix.fromRows_map, Matrix.map_mul, map_C_map_eval, map_C_map_eval]
  have hPpair_eval : ∀ c : K, Ppair.map (Polynomial.evalRingHom c)
      = pairMat F G (H.map (Polynomial.evalRingHom c)) := by
    intro c
    rw [hPpair, pairMat_map, map_C_map_eval, map_C_map_eval]
  -- the four bad sets are finite
  have hfin1 : {c : K | (H.map (Polynomial.evalRingHom c)).rank < n}.Finite := by
    refine finite_setOf_rank_lt H (c₀ := node 0) ?_
    rw [hHeval 0]
    simp [hval, Matrix.rank_one]
  have hfin2 : {c : K | (Pcols.map (Polynomial.evalRingHom c)).rank < r + s}.Finite := by
    refine finite_setOf_rank_lt Pcols (c₀ := node 1) ?_
    rw [hPcols_eval, hHeval 1]
    simpa [hval] using hbrank
  have hfin3 : {c : K | (Prows.map (Polynomial.evalRingHom c)).rank < r + s}.Finite := by
    refine finite_setOf_rank_lt Prows (c₀ := node 2) ?_
    rw [hProws_eval, hHeval 2]
    simpa [hval] using hcrank
  have hfin4 : {c : K | (Ppair.map (Polynomial.evalRingHom c)).rank
      < (pairMat F G 1).rank}.Finite := by
    refine finite_setOf_rank_lt Ppair (c₀ := node 0) ?_
    rw [hPpair_eval, hHeval 0]
    simp [hval]
  have hfin : ({c : K | (H.map (Polynomial.evalRingHom c)).rank < n} ∪
      {c : K | (Pcols.map (Polynomial.evalRingHom c)).rank < r + s} ∪
      {c : K | (Prows.map (Polynomial.evalRingHom c)).rank < r + s} ∪
      {c : K | (Ppair.map (Polynomial.evalRingHom c)).rank
        < (pairMat F G 1).rank}).Finite :=
    ((hfin1.union hfin2).union hfin3).union hfin4
  obtain ⟨c, hc⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hc
  obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := hc
  refine ⟨H.map (Polynomial.evalRingHom c), ?_, ?_, ?_, ?_⟩
  · have hrk : (H.map (Polynomial.evalRingHom c)).rank = n := by
      have hle := Matrix.rank_le_card_width (H.map (Polynomial.evalRingHom c))
      simp only [Fintype.card_fin] at hle
      omega
    exact (isUnit_iff_ne_zero).2 (det_ne_zero_of_rank_eq _ hrk)
  · rw [hPcols_eval] at g2; exact g2
  · rw [hProws_eval] at g3; exact g3
  · rw [hPpair_eval] at g4
    have e1 := finrank_pairSpace_add_rank F G (H.map (Polynomial.evalRingHom c))
    have e2 := finrank_pairSpace_add_rank F G 1
    omega

/-! ## The generic-position dimension bound -/

/-- The dimension bound for a pair of matrices presented by rank factorisations. -/
theorem finrank_sup_commutant_add_le_of_factorization {r s : ℕ} {F G : Matrix (Fin n) (Fin n) K}
    {U₁ : Matrix (Fin n) (Fin r) K} {V₁ : Matrix (Fin r) (Fin n) K}
    {U₂ : Matrix (Fin n) (Fin s) K} {V₂ : Matrix (Fin s) (Fin n) K}
    {U₁' : Matrix (Fin r) (Fin n) K} {W₁ : Matrix (Fin n) (Fin r) K}
    {U₂' : Matrix (Fin s) (Fin n) K} {W₂ : Matrix (Fin n) (Fin s) K}
    (hFfac : F = U₁ * V₁) (hGfac : G = U₂ * V₂)
    (hU₁ : U₁' * U₁ = 1) (hW₁ : V₁ * W₁ = 1) (hU₂ : U₂' * U₂ = 1) (hW₂ : V₂ * W₂ = 1)
    (hrs : r + s ≤ n) (hle : r ≤ s) :
    finrank K ↥(commutant F ⊔ commutant G) + r ≤ n ^ 2 := by
  classical
  obtain ⟨h, hunit, hcols, hrows, hpair⟩ :=
    exists_good_conjugator (F := F) (G := G) hU₁ hW₁ hU₂ hW₂ hrs
  have hinv : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h hunit
  have hinv' : h⁻¹ * h = 1 := Matrix.nonsing_inv_mul h hunit
  -- the conjugated factorisation
  set U₂c : Matrix (Fin n) (Fin s) K := h * U₂ with hU₂c
  set V₂c : Matrix (Fin s) (Fin n) K := V₂ * h⁻¹ with hV₂c
  have hGc : h * G * h⁻¹ = U₂c * V₂c := by
    rw [hU₂c, hV₂c, hGfac]
    simp [Matrix.mul_assoc]
  -- left inverse of the combined injection
  have hUinj : Function.Injective (Matrix.fromCols U₁ U₂c).mulVecLin := by
    refine injective_of_card_le_rank ?_
    simpa [hU₂c, Fintype.card_sum] using hcols
  obtain ⟨U', hU'⟩ := exists_leftInv hUinj
  -- right inverse of the combined surjection
  have hVrank : r + s ≤ (Matrix.fromRows V₁ V₂c).rank := by
    have hEq : Matrix.fromRows V₁ V₂c * h = Matrix.fromRows (V₁ * h) V₂ := by
      rw [Matrix.fromRows_mul, hV₂c, Matrix.mul_assoc, hinv', Matrix.mul_one]
    have hmul := Matrix.rank_mul_le_left (Matrix.fromRows V₁ V₂c) h
    rw [hEq] at hmul
    omega
  have hVsurj : Function.Surjective (Matrix.fromRows V₁ V₂c).mulVecLin := by
    refine surjective_of_card_le_rank ?_
    simpa [Fintype.card_sum] using hVrank
  obtain ⟨W, hW⟩ := exists_rightInv hVsurj
  -- the block computation
  have hblock := finrank_inf_commutant_block (U₁ := U₁) (U₂ := U₂c) (V₁ := V₁) (V₂ := V₂c)
    (U' := U') (W := W) hU' hW
  have hD₀ : V₂c * U₂c = V₂ * U₂ := by
    rw [hV₂c, hU₂c, Matrix.mul_assoc, ← Matrix.mul_assoc h⁻¹ h U₂, hinv', Matrix.one_mul]
  rw [hD₀, ← hFfac, ← hGc] at hblock
  -- the dimension identities
  have hcF : finrank K ↥(commutant F) = (n - r) ^ 2 + finrank K ↥(gcommutant (V₁ * U₁)) := by
    have hfac := finrank_commutant_factor hU₁ hW₁
    rw [← hFfac] at hfac
    simpa using hfac
  have hcG : finrank K ↥(commutant G) = (n - s) ^ 2 + finrank K ↥(gcommutant (V₂ * U₂)) := by
    have hfac := finrank_commutant_factor hU₂ hW₂
    rw [← hGfac] at hfac
    simpa using hfac
  have harrow := twoArrow_finrank_bound hle (V₁ * U₁) (V₂ * U₂) (V₁ * U₂c) (V₂c * U₁)
  have hsupinf := Submodule.finrank_sup_add_finrank_inf_eq (commutant F) (commutant G)
  have hmono : finrank K ↥(commutant F ⊓ commutant (h * G * h⁻¹))
      ≤ finrank K ↥(commutant F ⊓ commutant G) := by
    rw [← finrank_pairSpace_eq F G h hunit, ← finrank_pairSpace_one F G]
    exact hpair
  -- arithmetic
  obtain ⟨m, hm⟩ : ∃ m, n = m + r + s := ⟨n - r - s, by omega⟩
  have e1 : n - (r + s) = m := by omega
  have e2 : n - r = m + s := by omega
  have e3 : n - s = m + r := by omega
  rw [e1] at hblock
  rw [e2] at hcF
  rw [e3] at hcG
  have hid : (m + s) ^ 2 + (m + r) ^ 2 + 2 * r * s = n ^ 2 + m ^ 2 := by
    subst hm; ring
  linarith [hblock, hcF, hcG, harrow, hsupinf, hmono]

/-- **Stage 5D (combined with 5C and 5E).**  For matrices whose ranks satisfy `r + s ≤ n`,
the sum of the commutants has codimension at least `min r s`. -/
theorem finrank_sup_commutant_add_le {r s : ℕ} {F G : Matrix (Fin n) (Fin n) K}
    (hrs : r + s ≤ n) (hle : r ≤ s) (hF : F.rank = r) (hG : G.rank = s) :
    finrank K ↥(commutant F ⊔ commutant G) + r ≤ n ^ 2 := by
  obtain ⟨U₁, V₁, U₁', W₁, hFfac, hU₁, hW₁⟩ := exists_rank_factorization F
  obtain ⟨U₂, V₂, U₂', W₂, hGfac, hU₂, hW₂⟩ := exists_rank_factorization G
  have hmain := finrank_sup_commutant_add_le_of_factorization hFfac hGfac hU₁ hW₁ hU₂ hW₂
    (by omega) (by omega)
  omega

end

end Q655
