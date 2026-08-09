/-
# Q587 — the arbitrary-interval layer: ordered node tuples

The printed problem presents the nodes as a strictly increasing tuple `x₀ < x₁ < ⋯ < x_r` of
points of `I`, whereas the formalization uses a `Finset ℝ` of cardinality `r+1`.  This module
proves that the two formulations are equivalent: the divided difference of an ordered tuple is
the divided difference of the finset of its values (`ddiffTuple_eq_ddiff`), the divided
difference is symmetric in the nodes (`ddiffTuple_comp_equiv`), and the relative limits defined
with strictly increasing tuples coincide with the relative limits defined with finsets
(`DDLimOnTuple_iff`, `HasDITOnTuple_iff`).  Distinctness and the cardinality `r+1` are part of
both formulations.
-/

import RMS.Q587Interval

open Polynomial Finset

namespace Q587

/-- The divided difference over an (injective) tuple of nodes `z₀, …, z_r`. -/
noncomputable def ddiffTuple (f : ℝ → ℝ) {r : ℕ} (z : Fin (r+1) → ℝ) : ℝ :=
  ∑ i : Fin (r+1), f (z i) / ∏ j ∈ Finset.univ.erase i, (z i - z j)

lemma ddiffTuple_eq_ddiff (f : ℝ → ℝ) {r : ℕ} (z : Fin (r+1) → ℝ) (hz : Function.Injective z) :
    ddiffTuple f z = ddiff f (Finset.image z Finset.univ) := by
  classical
  rw [ddiff, Finset.sum_image (fun a _ b _ hab => hz hab), ddiffTuple]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [← Finset.image_erase hz, Finset.prod_image (fun a _ b _ hab => hz hab)]

lemma card_image_tuple {r : ℕ} (z : Fin (r+1) → ℝ) (hz : Function.Injective z) :
    (Finset.image z Finset.univ).card = r + 1 := by
  rw [Finset.card_image_of_injective _ hz, Finset.card_univ, Fintype.card_fin]

/-- **Symmetry of the divided difference in the nodes**: reordering the tuple by any permutation
does not change it.  In particular the ordered (increasing) and the unordered formulations agree. -/
lemma ddiffTuple_comp_equiv (f : ℝ → ℝ) {r : ℕ} (z : Fin (r+1) → ℝ) (hz : Function.Injective z)
    (σ : Equiv.Perm (Fin (r+1))) : ddiffTuple f (z ∘ σ) = ddiffTuple f z := by
  have hzσ : Function.Injective (z ∘ σ) := hz.comp σ.injective
  rw [ddiffTuple_eq_ddiff f _ hzσ, ddiffTuple_eq_ddiff f z hz]
  congr 1
  ext t
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨σ i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨σ.symm i, by simp⟩

/-- The relative divided-difference limit, with the nodes presented as **strictly increasing
tuples** `x₀ < ⋯ < x_r` of points of `I`, exactly as in the printed statement. -/
def DDLimOnTuple (I : Set ℝ) (f : ℝ → ℝ) (r : ℕ) (x L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ z : Fin (r+1) → ℝ, StrictMono z → (∀ i, z i ∈ I) →
    (∀ i, |z i - x| < δ) → |ddiffTuple f z - L| < ε

/-- `DIT(n)` at `x` relative to `I`, in the ordered-tuple formulation. -/
def HasDITOnTuple (I : Set ℝ) (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : Prop := ∃ L, DDLimOnTuple I f n x L

variable {I : Set ℝ}

lemma image_orderIsoOfFin {s : Finset ℝ} {r : ℕ} (hs : s.card = r + 1) :
    Finset.image (fun i : Fin (r+1) => ((s.orderIsoOfFin hs i : ℝ))) Finset.univ = s := by
  ext t
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact (s.orderIsoOfFin hs i).2
  · intro ht
    exact ⟨(s.orderIsoOfFin hs).symm ⟨t, ht⟩, by simp⟩

/-- **Equivalence of the ordered-tuple and the finset formulations** of the relative limits. -/
theorem DDLimOnTuple_iff (f : ℝ → ℝ) (r : ℕ) (x L : ℝ) :
    DDLimOnTuple I f r x L ↔ DDLimOn I f r x L := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h ε hε
    refine ⟨δ, hδ, fun s hs hsI hsx => ?_⟩
    set z : Fin (r+1) → ℝ := fun i => ((s.orderIsoOfFin hs i : ℝ)) with hzdef
    have hzmem : ∀ i, z i ∈ s := fun i => (s.orderIsoOfFin hs i).2
    have hzmono : StrictMono z := by
      intro i j hij
      exact_mod_cast (s.orderIsoOfFin hs).strictMono hij
    have himg : Finset.image z Finset.univ = s := image_orderIsoOfFin hs
    have := hδ' z hzmono (fun i => hsI (hzmem i)) (fun i => hsx _ (hzmem i))
    rwa [ddiffTuple_eq_ddiff f z hzmono.injective, himg] at this
  · intro h ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h ε hε
    refine ⟨δ, hδ, fun z hzmono hzI hzx => ?_⟩
    have hinj : Function.Injective z := hzmono.injective
    have hcard : (Finset.image z Finset.univ).card = r + 1 := card_image_tuple z hinj
    have hsub : ((↑(Finset.image z Finset.univ)) : Set ℝ) ⊆ I := by
      intro t ht
      have ht' : t ∈ Finset.image z Finset.univ := ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht'
      exact hzI i
    have hnear : ∀ t ∈ Finset.image z Finset.univ, |t - x| < δ := by
      intro t ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht
      exact hzx i
    have := hδ' _ hcard hsub hnear
    rwa [← ddiffTuple_eq_ddiff f z hinj] at this

theorem HasDITOnTuple_iff (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    HasDITOnTuple I f n x ↔ HasDITOn I f n x :=
  exists_congr fun L => DDLimOnTuple_iff f n x L

end Q587
