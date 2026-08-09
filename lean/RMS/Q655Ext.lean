import RMS.Q655Rank

/-!
# Q655 — Stage 5A: commutant dimensions and scalar extension

The commutant of `f` is the kernel of an explicit coefficient matrix `adMat f`, whose entries are
(linear) polynomial expressions in the entries of `f`.  Consequently all the dimensions occurring
in the problem are unchanged by a field extension.
-/

namespace Q655

open Matrix Module

variable {K L : Type*} [Field K] [Field L] {n : ℕ}

/-- Matrices as vectors indexed by pairs. -/
noncomputable def vecMat (K : Type*) [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n) K ≃ₗ[K] (Fin n × Fin n → K) :=
  (LinearEquiv.curry K K (Fin n) (Fin n)).symm

@[simp] lemma vecMat_apply (X : Matrix (Fin n) (Fin n) K) (ij : Fin n × Fin n) :
    vecMat K n X ij = X ij.1 ij.2 := rfl

/-- A submodule of matrices cut out by a system of linear equations has the expected dimension. -/
lemma finrank_add_rank_of_ker {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι (Fin n × Fin n) K) (S : Submodule K (Matrix (Fin n) (Fin n) K))
    (hS : ∀ X : Matrix (Fin n) (Fin n) K, X ∈ S ↔ A *ᵥ (vecMat K n X) = 0) :
    finrank K ↥S + A.rank = n ^ 2 := by
  have hmap : S.map ((vecMat K n : Matrix (Fin n) (Fin n) K →ₗ[K] (Fin n × Fin n → K)))
      = LinearMap.ker A.mulVecLin := by
    ext v
    constructor
    · rintro ⟨X, hX, rfl⟩
      simpa [Matrix.mulVecLin] using (hS X).1 hX
    · intro hv
      refine ⟨(vecMat K n).symm v, ?_, by simp⟩
      show (vecMat K n).symm v ∈ S
      rw [hS]
      simpa [Matrix.mulVecLin] using hv
  have h1 : finrank K ↥S = finrank K ↥(LinearMap.ker A.mulVecLin) := by
    rw [← hmap, LinearEquiv.finrank_map_eq]
  have h2 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h3 : finrank K (Fin n × Fin n → K) = n ^ 2 := by
    simp [Module.finrank_pi, sq]
  have h4 : A.rank = finrank K ↥(LinearMap.range A.mulVecLin) := rfl
  omega

/-- The coefficient matrix of the commutator map `X ↦ f * X - X * f`, acting on matrices viewed
as vectors indexed by pairs. -/
def adMat {R : Type*} [CommRing R] (f : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) R :=
  Matrix.of fun ij kl =>
    (if ij.2 = kl.2 then f ij.1 kl.1 else 0) - (if ij.1 = kl.1 then f kl.2 ij.2 else 0)

lemma adMat_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : Matrix (Fin n) (Fin n) R) :
    (adMat f).map φ = adMat (f.map φ) := by
  ext ij kl
  simp only [adMat, Matrix.map_apply, Matrix.of_apply, map_sub, apply_ite φ, map_zero]

lemma adMat_mulVec (f X : Matrix (Fin n) (Fin n) K) :
    adMat f *ᵥ (vecMat K n X) = vecMat K n (f * X - X * f) := by
  funext ij
  obtain ⟨i, j⟩ := ij
  simp only [Matrix.mulVec, dotProduct, adMat, Matrix.of_apply, vecMat_apply,
    Matrix.sub_apply, Matrix.mul_apply, sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Finset.sum_ite_eq' Finset.univ j]
  · rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [Finset.sum_ite_eq' Finset.univ i, mul_comm]

/-- The stacked coefficient matrix cutting out `commutant f ⊓ commutant g`. -/
def adMat₂ (f g : Matrix (Fin n) (Fin n) K) :
    Matrix ((Fin n × Fin n) ⊕ (Fin n × Fin n)) (Fin n × Fin n) K :=
  Matrix.of fun ij kl => Sum.elim (fun ij => adMat f ij kl) (fun ij => adMat g ij kl) ij

lemma adMat₂_map (φ : K →+* L) (f g : Matrix (Fin n) (Fin n) K) :
    (adMat₂ f g).map φ = adMat₂ (f.map φ) (g.map φ) := by
  ext ij kl
  cases ij with
  | inl a =>
      have := congrFun (congrFun (adMat_map φ f) a) kl
      simpa [adMat₂] using this
  | inr a =>
      have := congrFun (congrFun (adMat_map φ g) a) kl
      simpa [adMat₂] using this

lemma adMat₂_mulVec (f g X : Matrix (Fin n) (Fin n) K) :
    adMat₂ f g *ᵥ (vecMat K n X) =
      Sum.elim (vecMat K n (f * X - X * f)) (vecMat K n (g * X - X * g)) := by
  funext ij
  cases ij with
  | inl a =>
      have := congrFun (adMat_mulVec f X) a
      simpa [adMat₂, Matrix.mulVec, dotProduct] using this
  | inr a =>
      have := congrFun (adMat_mulVec g X) a
      simpa [adMat₂, Matrix.mulVec, dotProduct] using this

/-- `dim C(f)` from the rank of the coefficient matrix. -/
theorem finrank_commutant_add_rank (f : Matrix (Fin n) (Fin n) K) :
    finrank K ↥(commutant f) + (adMat f).rank = n ^ 2 := by
  refine finrank_add_rank_of_ker _ _ fun X => ?_
  rw [adMat_mulVec]
  constructor
  · intro hX
    have hX' : X * f = f * X := hX
    have h0 : f * X - X * f = 0 := by rw [hX']; abel
    rw [h0, map_zero]
  · intro h
    have h0 : f * X - X * f = 0 := (vecMat K n).map_eq_zero_iff.1 h
    show X * f = f * X
    exact (sub_eq_zero.1 h0).symm

/-- `dim (C(f) ⊓ C(g))` from the rank of the stacked coefficient matrix. -/
theorem finrank_inf_commutant_add_rank (f g : Matrix (Fin n) (Fin n) K) :
    finrank K ↥(commutant f ⊓ commutant g) + (adMat₂ f g).rank = n ^ 2 := by
  refine finrank_add_rank_of_ker _ _ fun X => ?_
  rw [adMat₂_mulVec]
  constructor
  · rintro ⟨hf, hg⟩
    have hf' : X * f = f * X := hf
    have hg' : X * g = g * X := hg
    have h1 : f * X - X * f = 0 := by rw [hf']; abel
    have h2 : g * X - X * g = 0 := by rw [hg']; abel
    rw [h1, h2, map_zero]
    funext ij; cases ij <;> simp
  · intro h
    have h1 : f * X - X * f = 0 := by
      refine (vecMat K n).map_eq_zero_iff.1 ?_
      funext ij
      simpa using congrFun h (Sum.inl ij)
    have h2 : g * X - X * g = 0 := by
      refine (vecMat K n).map_eq_zero_iff.1 ?_
      funext ij
      simpa using congrFun h (Sum.inr ij)
    exact ⟨show X * f = f * X from (sub_eq_zero.1 h1).symm,
      show X * g = g * X from (sub_eq_zero.1 h2).symm⟩

/-! ## Invariance under a field extension -/

theorem finrank_commutant_map (φ : K →+* L) (f : Matrix (Fin n) (Fin n) K) :
    finrank L ↥(commutant (f.map φ)) = finrank K ↥(commutant f) := by
  have h1 := finrank_commutant_add_rank (f.map φ)
  have h2 := finrank_commutant_add_rank f
  have h3 : (adMat (f.map φ)).rank = (adMat f).rank := by
    rw [← adMat_map φ f, rank_map_eq]
  omega

theorem finrank_inf_commutant_map (φ : K →+* L) (f g : Matrix (Fin n) (Fin n) K) :
    finrank L ↥(commutant (f.map φ) ⊓ commutant (g.map φ)) =
      finrank K ↥(commutant f ⊓ commutant g) := by
  have h1 := finrank_inf_commutant_add_rank (f.map φ) (g.map φ)
  have h2 := finrank_inf_commutant_add_rank f g
  have h3 : (adMat₂ (f.map φ) (g.map φ)).rank = (adMat₂ f g).rank := by
    rw [← adMat₂_map φ f g, rank_map_eq]
  omega

theorem finrank_sup_commutant_map (φ : K →+* L) (f g : Matrix (Fin n) (Fin n) K) :
    finrank L ↥(commutant (f.map φ) ⊔ commutant (g.map φ)) =
      finrank K ↥(commutant f ⊔ commutant g) := by
  have hK := Submodule.finrank_sup_add_finrank_inf_eq (commutant f) (commutant g)
  have hL := Submodule.finrank_sup_add_finrank_inf_eq (commutant (f.map φ)) (commutant (g.map φ))
  have h1 := finrank_commutant_map φ f
  have h2 := finrank_commutant_map φ g
  have h3 := finrank_inf_commutant_map φ f g
  omega

end Q655
