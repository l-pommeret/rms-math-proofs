/-
# Q781 — Separation by translations in a compact group

Let `G` be a compact topological group and `(U i)` a family of open subsets of `G`
indexed by an arbitrary type `I`.  Call the family *separable by translations* if
there are `t i ∈ G` such that the left translates `t i • U i` are pairwise disjoint.

**Theorem.** If every finite subfamily is separable by translations, then the whole
family is separable by translations.

The proof is the compactness argument: for `i ≠ j`, disjointness of `s • U i` and
`t • U j` is a *closed* condition on `(s, t)` (because `U i * (U j)⁻¹` is open, and
the two translates meet exactly when `s⁻¹ * t` lies in that set).  The corresponding
closed subsets of the compact product `I → G` have the finite intersection property,
so their total intersection is nonempty.

Lean version: 4.28.0.  Mathlib: commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
(tag `v4.28.0`).
-/
import Mathlib

open Pointwise Set

namespace Q781

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Two left translates of sets meet exactly when `s⁻¹ * t ∈ A * B⁻¹`. -/
theorem not_disjoint_smul_iff (A B : Set G) (s t : G) :
    ¬ Disjoint (s • A) (t • B) ↔ s⁻¹ * t ∈ A * B⁻¹ := by
  constructor
  · intro h
    obtain ⟨x, hx1, hx2⟩ := Set.not_disjoint_iff.mp h
    obtain ⟨a, ha, rfl⟩ := hx1
    obtain ⟨b, hb, hbx⟩ := hx2
    have hst : s * a = t * b := by simpa [smul_eq_mul] using hbx.symm
    have : s⁻¹ * t = a * b⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← hst, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact Set.mul_mem_mul ha (Set.inv_mem_inv.mpr hb)
  · intro h
    obtain ⟨a, ha, c, hc, hac⟩ := h
    rw [Set.mem_inv] at hc
    refine Set.not_disjoint_iff.mpr ⟨s * a, ⟨a, ha, rfl⟩, ⟨c⁻¹, hc, ?_⟩⟩
    have hst : a * c = s⁻¹ * t := hac
    simp only [smul_eq_mul]
    calc t * c⁻¹ = s * (s⁻¹ * t) * c⁻¹ := by group
      _ = s * (a * c) * c⁻¹ := by rw [hst]
      _ = s * a := by group

/-- For open sets `A`, `B`, the set of pairs of translation parameters giving disjoint
translates is closed. -/
theorem isClosed_disjoint_smul {A B : Set G} (hA : IsOpen A) :
    IsClosed {p : G × G | Disjoint (p.1 • A) (p.2 • B)} := by
  rw [← isOpen_compl_iff]
  have hset : {p : G × G | Disjoint (p.1 • A) (p.2 • B)}ᶜ
      = (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' (A * B⁻¹) := by
    ext p
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_preimage]
    exact not_disjoint_smul_iff A B p.1 p.2
  rw [hset]
  exact (hA.mul_right).preimage (by fun_prop)

/-- **Q781.** Let `G` be a compact topological group and `U : I → Set G` a family of
open subsets indexed by an arbitrary type `I`.  If for every finite set `F` of indices
there are translations making the sets `U i`, `i ∈ F`, pairwise disjoint after
translation, then there is a single family of translations making all the `U i`
pairwise disjoint after translation. -/
theorem separable_by_translations [CompactSpace G] {I : Type*} (U : I → Set G)
    (hU : ∀ i, IsOpen (U i))
    (hfin : ∀ F : Finset I, ∃ t : I → G,
      ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (t i • U i) (t j • U j)) :
    ∃ t : I → G, ∀ i j, i ≠ j → Disjoint (t i • U i) (t j • U j) := by
  classical
  -- the closed constraint sets in the compact product `I → G`
  set K : I × I → Set (I → G) := fun p =>
    {x | p.1 = p.2 ∨ Disjoint (x p.1 • U p.1) (x p.2 • U p.2)} with hK
  have hKclosed : ∀ p, IsClosed (K p) := by
    intro p
    by_cases h : p.1 = p.2
    · have : K p = Set.univ := by
        ext x; simp [hK, h]
      rw [this]; exact isClosed_univ
    · have : K p = (fun x : I → G => (x p.1, x p.2)) ⁻¹'
          {q : G × G | Disjoint (q.1 • U p.1) (q.2 • U p.2)} := by
        ext x
        simp only [hK, Set.mem_setOf_eq, Set.mem_preimage, h, false_or]
      rw [this]
      exact (isClosed_disjoint_smul (hU p.1)).preimage (by fun_prop)
  -- the total intersection is nonempty
  have hne : (⋂ p, K p).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hcompact : IsCompact (Set.univ : Set (I → G)) := isCompact_univ
    obtain ⟨u, hu⟩ := hcompact.elim_finite_subfamily_closed K hKclosed (by
      rw [Set.univ_inter, hempty])
    -- build a point in the finite intersection from the finite hypothesis
    set F : Finset I := u.image Prod.fst ∪ u.image Prod.snd with hF
    obtain ⟨t, ht⟩ := hfin F
    have hmem : t ∈ Set.univ ∩ ⋂ p ∈ u, K p := by
      refine ⟨Set.mem_univ _, ?_⟩
      simp only [Set.mem_iInter]
      intro p hp
      by_cases h : p.1 = p.2
      · exact Or.inl h
      · refine Or.inr (ht p.1 ?_ p.2 ?_ h)
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    rw [hu] at hmem
    exact hmem.elim
  obtain ⟨t, ht⟩ := hne
  refine ⟨t, fun i j hij => ?_⟩
  have := Set.mem_iInter.mp ht (i, j)
  simpa [hK, hij] using this

end Q781

#print axioms Q781.separable_by_translations
