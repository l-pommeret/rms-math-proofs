import RMS.Q655Arrow

/-!
# Q655 — Stage 5D, part 1: moving subspaces by an invertible matrix

Given two injective matrices `A : n × p` and `B : n × q` with `card p + card q ≤ n`, there is an
invertible matrix `M` with `[A | M B]` of full column rank: it suffices to move the column space
of `B` into a complement of the column space of `A`.  This provides the witnesses used in the
genericity argument of Stage 5D.
-/

namespace Q655

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

/-! ## Subspaces of prescribed dimension -/

/-- A subspace of prescribed dimension inside a given subspace. -/
lemma exists_submodule_le_finrank_eq {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V) {k : ℕ} (hk : k ≤ finrank K ↥W) :
    ∃ T : Submodule K V, T ≤ W ∧ finrank K ↥T = k := by
  classical
  let b : Basis (Fin (finrank K ↥W)) K ↥W := Module.finBasis K ↥W
  set f : Fin k → V := fun i => (b (Fin.castLE hk i) : V) with hf
  have hli : LinearIndependent K f := by
    have h1 : LinearIndependent K (fun i : Fin k => b (Fin.castLE hk i)) :=
      b.linearIndependent.comp _ (Fin.castLE_injective hk)
    exact h1.map' W.subtype (by simp)
  refine ⟨Submodule.span K (Set.range f), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (b (Fin.castLE hk i)).2
  · rw [finrank_span_eq_card hli, Fintype.card_fin]

/-! ## Automorphisms carrying one subspace onto another -/

lemma exists_linearEquiv_map_eq {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S T : Submodule K V) (h : finrank K ↥S = finrank K ↥T) :
    ∃ e : V ≃ₗ[K] V, S.map (e : V →ₗ[K] V) = T := by
  classical
  obtain ⟨S', hS'⟩ := Submodule.exists_isCompl S
  obtain ⟨T', hT'⟩ := Submodule.exists_isCompl T
  have h1 : finrank K ↥S + finrank K ↥S' = finrank K V :=
    Submodule.finrank_add_eq_of_isCompl hS'
  have h2 : finrank K ↥T + finrank K ↥T' = finrank K V :=
    Submodule.finrank_add_eq_of_isCompl hT'
  have h3 : finrank K ↥S' = finrank K ↥T' := by omega
  let e1 : ↥S ≃ₗ[K] ↥T := LinearEquiv.ofFinrankEq _ _ h
  let e2 : ↥S' ≃ₗ[K] ↥T' := LinearEquiv.ofFinrankEq _ _ h3
  let e : V ≃ₗ[K] V :=
    ((Submodule.prodEquivOfIsCompl S S' hS').symm.trans (e1.prodCongr e2)).trans
      (Submodule.prodEquivOfIsCompl T T' hT')
  refine ⟨e, ?_⟩
  have hle : S.map (e : V →ₗ[K] V) ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    have hsymm : (Submodule.prodEquivOfIsCompl S S' hS').symm x = (⟨x, hx⟩, 0) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hS' ⟨x, hx⟩
    show e x ∈ T
    have : e x = ((e1 ⟨x, hx⟩ : ↥T) : V) + ((e2 0 : ↥T') : V) := by
      show (Submodule.prodEquivOfIsCompl T T' hT')
        ((e1.prodCongr e2) ((Submodule.prodEquivOfIsCompl S S' hS').symm x)) = _
      rw [hsymm]
      simp [Submodule.coe_prodEquivOfIsCompl]
    rw [this]
    simpa using (e1 ⟨x, hx⟩).2
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [LinearEquiv.finrank_map_eq, h]

/-- An invertible matrix carrying one subspace of the coordinate space onto another of the same
dimension. -/
lemma exists_unit_matrix_map_eq (S T : Submodule K (Fin n → K))
    (h : finrank K ↥S = finrank K ↥T) :
    ∃ M : Matrix (Fin n) (Fin n) K, IsUnit M.det ∧ S.map M.mulVecLin = T := by
  obtain ⟨e, he⟩ := exists_linearEquiv_map_eq S T h
  refine ⟨LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)), ?_, ?_⟩
  · have hmul : LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) *
        LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
      rw [← LinearMap.toMatrix'_comp]
      simp
    have hunit : IsUnit (LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K))) :=
      IsUnit.of_mul_eq_one _ hmul
    exact (Matrix.isUnit_iff_isUnit_det _).1 hunit
  · rw [toMatrix'_mulVecLin]
    exact he

/-! ## The witness matrix -/

lemma range_fromCols {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (A : Matrix (Fin n) p K) (B : Matrix (Fin n) q K) :
    LinearMap.range (Matrix.fromCols A B).mulVecLin =
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    have hv : Matrix.fromCols A B *ᵥ v = A *ᵥ (v ∘ Sum.inl) + B *ᵥ (v ∘ Sum.inr) := by
      have := Matrix.fromCols_mulVec_sumElim A B (v ∘ Sum.inl) (v ∘ Sum.inr)
      have hsum : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) = v := by
        funext x; cases x <;> rfl
      rw [hsum] at this
      exact this
    show Matrix.fromCols A B *ᵥ v ∈ _
    rw [hv]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right ⟨_, rfl⟩)
  · refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨Sum.elim x 0, by
        show Matrix.fromCols A B *ᵥ Sum.elim x 0 = A *ᵥ x
        rw [Matrix.fromCols_mulVec_sumElim]
        simp⟩
    · rintro _ ⟨y, rfl⟩
      exact ⟨Sum.elim 0 y, by
        show Matrix.fromCols A B *ᵥ Sum.elim 0 y = B *ᵥ y
        rw [Matrix.fromCols_mulVec_sumElim]
        simp⟩

/-- **The witness for the generic-position argument.**  If `A` and `B` are injective and there is
room for their column spaces, some invertible `M` puts them in direct sum. -/
lemma exists_unit_fromCols_rank {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] (A : Matrix (Fin n) p K) (B : Matrix (Fin n) q K)
    (hA : Function.Injective A.mulVecLin) (hB : Function.Injective B.mulVecLin)
    (hpq : Fintype.card p + Fintype.card q ≤ n) :
    ∃ M : Matrix (Fin n) (Fin n) K, IsUnit M.det ∧
      Fintype.card p + Fintype.card q ≤ (Matrix.fromCols A (M * B)).rank := by
  classical
  set S := LinearMap.range A.mulVecLin with hS
  set T := LinearMap.range B.mulVecLin with hT
  have hSdim : finrank K ↥S = Fintype.card p := by
    rw [hS, LinearMap.finrank_range_of_inj hA, Module.finrank_pi]
  have hTdim : finrank K ↥T = Fintype.card q := by
    rw [hT, LinearMap.finrank_range_of_inj hB, Module.finrank_pi]
  obtain ⟨S', hS'⟩ := Submodule.exists_isCompl S
  have hS'dim : finrank K ↥S + finrank K ↥S' = n := by
    have := Submodule.finrank_add_eq_of_isCompl hS'
    rw [this, Module.finrank_pi]
    simp
  obtain ⟨T₀, hT₀le, hT₀dim⟩ :=
    exists_submodule_le_finrank_eq S' (k := Fintype.card q) (by omega)
  obtain ⟨M, hMunit, hMmap⟩ := exists_unit_matrix_map_eq T T₀ (by rw [hTdim, hT₀dim])
  refine ⟨M, hMunit, ?_⟩
  have hrange : LinearMap.range (M * B).mulVecLin = T.map M.mulVecLin := by
    rw [hT, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul]
  have hdisj : S ⊓ T₀ = ⊥ := by
    have : S ⊓ T₀ ≤ S ⊓ S' := inf_le_inf_left _ hT₀le
    rw [hS'.inf_eq_bot] at this
    exact le_bot_iff.1 this
  have hsupdim : finrank K ↥(S ⊔ T₀) = Fintype.card p + Fintype.card q := by
    have := Submodule.finrank_sup_add_finrank_inf_eq S T₀
    rw [hdisj] at this
    simp only [finrank_bot, add_zero] at this
    rw [this, hSdim, hT₀dim]
  have hrk : (Matrix.fromCols A (M * B)).rank = finrank K ↥(S ⊔ T₀) := by
    show finrank K ↥(LinearMap.range (Matrix.fromCols A (M * B)).mulVecLin) = _
    rw [range_fromCols, hrange, hMmap]
  rw [hrk, hsupdim]

end Q655
