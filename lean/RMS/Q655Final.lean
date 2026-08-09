import RMS.Q655Quadratic

/-!
# Q655 — the equality classification: the classified cases and their dimensions

`RankOneSideClass f g` says that `g` is a scalar plus a rank-one matrix `outer u phi` and that
`f` sits in one of the three classified quadratic cases relative to that `(u, phi)`.

This file proves, over an arbitrary field and for `3 ≤ n`:

* every pair in `RankOneSideClass` (in either order) is extremal, i.e. attains `n² - 1`;
* the advertised dimension formulas for `C(g)` and `C(f) ⊓ C(g)` in that situation;
* the converse implication, *given* the one input that is still open in this development,
  namely that one member of an extremal pair is a scalar plus a rank-one matrix.
-/

namespace Q655

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

/-- `g` is a scalar plus the rank-one matrix `outer u phi`, and `f` satisfies one of the three
classified quadratic conditions with respect to `(u, phi)`. -/
def RankOneSideClass (f g : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ (lam : K) (u phi : Vec K n), u ≠ 0 ∧ phi ≠ 0 ∧ g = lam • 1 + outer u phi ∧
    QuadraticEqualityCase f u phi

/-! ## Sufficiency -/

theorem extremal_of_rankOneSideClass (hn : 3 ≤ n) {f g : Matrix (Fin n) (Fin n) K}
    (h : RankOneSideClass f g) :
    finrank K ↥(commutant f ⊔ commutant g) = n ^ 2 - 1 := by
  obtain ⟨lam, u, phi, hu, hphi, rfl, hcase⟩ := h
  rw [commutant_smul_one_add]
  exact (extremal_with_outer_iff_pairAction (by omega) hu hphi).2
    (pairAction_rank_of_quadraticEqualityCase hn hu hphi hcase)

/-- **Reverse implication of the classification.** -/
theorem extremal_of_rankOneSideClass_or (hn : 3 ≤ n) {f g : Matrix (Fin n) (Fin n) K}
    (h : RankOneSideClass f g ∨ RankOneSideClass g f) :
    finrank K ↥(commutant f ⊔ commutant g) = n ^ 2 - 1 := by
  rcases h with h | h
  · exact extremal_of_rankOneSideClass hn h
  · rw [sup_comm]
    exact extremal_of_rankOneSideClass hn h

/-! ## The dimension consequences -/

/-- `dim C(λ•1 + u φᵀ) = n² - 2n + 2`, in addition-only form. -/
theorem finrank_commutant_scalar_add_outer {u phi : Vec K n} (hu : u ≠ 0) (hphi : phi ≠ 0)
    (lam : K) :
    finrank K ↥(commutant (lam • (1 : Matrix (Fin n) (Fin n) K) + outer u phi)) + 2 * n =
      n ^ 2 + 2 := by
  rw [commutant_smul_one_add]
  exact finrank_commutant_outer_add hu hphi

/-- In an extremal configuration, `dim (C(f) ⊓ C(g)) = dim C(f) - 2n + 3`. -/
theorem finrank_inf_commutant_of_extremal (hn : 2 ≤ n) {f : Matrix (Fin n) (Fin n) K}
    {u phi : Vec K n} (hu : u ≠ 0) (hphi : phi ≠ 0) (lam : K)
    (hext : finrank K ↥(commutant f ⊔
      commutant (lam • (1 : Matrix (Fin n) (Fin n) K) + outer u phi)) = n ^ 2 - 1) :
    finrank K ↥(commutant f ⊓
        commutant (lam • (1 : Matrix (Fin n) (Fin n) K) + outer u phi)) + 2 * n =
      finrank K ↥(commutant f) + 3 := by
  rw [commutant_smul_one_add] at hext ⊢
  have hrank := (extremal_with_outer_iff_pairAction hn hu hphi).1 hext
  have hinf := finrank_inf_commutant_outer (f := f) hu hphi
  have hrn := LinearMap.finrank_range_add_finrank_ker (pairAction f u phi)
  have hle : 2 ≤ 2 * n := by omega
  omega

/-! ## Necessity, given the two inputs that remain open -/

/-- **Forward implication of the classification, relative to the one remaining input.**

The hypothesis `hstruct` is the conclusion of the (not yet formalized) descent step showing
that an extremal pair has a scalar-plus-rank-one member.  Everything else — the exact sum
formula, the existence of a monic quadratic relation for the other member, and the complete
case analysis of the three quadratic types — is proved in this development. -/
theorem rankOneSideClass_of_extremal (hn : 3 ≤ n) {f g : Matrix (Fin n) (Fin n) K}
    (hf : ¬ IsScalarMat f) (hstruct : IsScalarPlusRankOne g)
    (hext : finrank K ↥(commutant f ⊔ commutant g) = n ^ 2 - 1) :
    RankOneSideClass f g := by
  obtain ⟨lam, R, ⟨u, phi, hu, hphi, rfl⟩, rfl⟩ := hstruct
  rw [commutant_smul_one_add] at hext
  have hrank := (extremal_with_outer_iff_pairAction (by omega) hu hphi).1 hext
  exact ⟨lam, u, phi, hu, hphi, rfl,
    quadraticEqualityCase_of_pairAction_rank hn hf hu hphi hrank⟩

/-- **The classification, relative to the one remaining input.**  For `3 ≤ n` and non-scalar
`f, g`, extremality is equivalent to the classified conditions, given that an extremal pair has
a scalar-plus-rank-one member. -/
theorem Q655_equality_classification_of_scalarPlusRankOne (hn : 3 ≤ n)
    {f g : Matrix (Fin n) (Fin n) K} (hf : ¬ IsScalarMat f) (hg : ¬ IsScalarMat g)
    (hstruct : finrank K ↥(commutant f ⊔ commutant g) = n ^ 2 - 1 →
      IsScalarPlusRankOne f ∨ IsScalarPlusRankOne g) :
    finrank K ↥(commutant f ⊔ commutant g) = n ^ 2 - 1 ↔
      RankOneSideClass f g ∨ RankOneSideClass g f := by
  refine ⟨fun hext => ?_, extremal_of_rankOneSideClass_or hn⟩
  rcases hstruct hext with h | h
  · refine Or.inr (rankOneSideClass_of_extremal hn hg h ?_)
    rw [sup_comm]; exact hext
  · exact Or.inl (rankOneSideClass_of_extremal hn hf h hext)

end Q655
