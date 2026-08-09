import RMS.Q655Stage5

/-!
# Q655 — Stage 7: the complete answer

This file assembles the unconditional results:

* `Q655.extremal_forces_scalarPlusRankOne` — an extremal pair in dimension `≥ 3` has a member
  that is a scalar plus a rank one matrix;
* `Q655.Q655_equality_classification` — the equality classification for `3 ≤ n`;
* `Q655.extremal_fin_two_iff_noncommute` (proved earlier) — the two-dimensional case;
* `Q655.Q655_complete` — the maximum together with both classification statements.
-/

namespace Q655

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

/-- **Stage 6, unconditionally.** -/
theorem extremal_forces_scalarPlusRankOne (hn : 3 ≤ n) {f g : Matrix (Fin n) (Fin n) K}
    (hf : ¬ IsScalarMat f) (hg : ¬ IsScalarMat g)
    (hext : finrank K ↥(commutant f ⊔ commutant g) = n ^ 2 - 1) :
    IsScalarPlusRankOne f ∨ IsScalarPlusRankOne g :=
  extremal_forces_scalarPlusRankOne_of_bound hn (scalarRankBound_holds K n) hf hg hext

/-- **The equality classification in dimension at least three.** -/
theorem Q655_equality_classification (hn : 3 ≤ n) {f g : Matrix (Fin n) (Fin n) K}
    (hf : ¬ IsScalarMat f) (hg : ¬ IsScalarMat g) :
    finrank K ↥(commutant f ⊔ commutant g) = n ^ 2 - 1 ↔
      RankOneSideClass f g ∨ RankOneSideClass g f :=
  Q655_equality_classification_of_scalarRankBound hn (scalarRankBound_holds K n) hf hg

/-- **The complete answer to Q655.** -/
theorem Q655_complete (K : Type*) [Field K] (n : ℕ) (hn : 2 ≤ n) :
    IsGreatest
      {d : ℕ | ∃ f g : Matrix (Fin n) (Fin n) K,
        ¬ IsScalarMat f ∧ ¬ IsScalarMat g ∧
        Module.finrank K ↥(commutant f ⊔ commutant g) = d}
      (n ^ 2 - 1)
    ∧
    (n = 2 → ∀ f g : Matrix (Fin n) (Fin n) K, ¬ IsScalarMat f → ¬ IsScalarMat g →
      (Module.finrank K ↥(commutant f ⊔ commutant g) = 3 ↔ f * g ≠ g * f))
    ∧
    (3 ≤ n → ∀ f g : Matrix (Fin n) (Fin n) K, ¬ IsScalarMat f → ¬ IsScalarMat g →
      (Module.finrank K ↥(commutant f ⊔ commutant g) = n ^ 2 - 1 ↔
        RankOneSideClass f g ∨ RankOneSideClass g f)) := by
  refine ⟨isGreatest_finrank_commutant_sup K n hn, ?_, ?_⟩
  · rintro rfl f g hf hg
    exact extremal_fin_two_iff_noncommute hf hg
  · intro h3 f g hf hg
    exact Q655_equality_classification h3 hf hg

end Q655
