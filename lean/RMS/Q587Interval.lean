/-
# Q587 — the arbitrary-interval (relative) layer, part 1: definitions and basic theory

This module builds the *relative* (interval) version of the theory developed on the whole line
in `RequestProject.Q587`.  Throughout, `I : Set ℝ` is an order-connected set (an arbitrary real
interval), `x ∈ I`, and all node configurations are required to lie in `I`; limits quantify only
over configurations tending to `x` inside `I`, so at a finite endpoint of `I` they are the
one-sided (relative) limits of the printed problem.

Ambient functions are represented as `f : ℝ → ℝ`; all the notions defined here depend only on
the restriction of `f` to `I` (see the `..._congr` lemmas), and the final, source-facing
statements in `RequestProject.Q587IntervalMain` are quantified over genuine functions
`f : ↥I → ℝ`.
-/

import RMS.Q587

open Polynomial Finset

namespace Q587

/-! ## Relative definitions -/

/-- `DDLimOn I f r x L`: the divided differences of order `r` of `f` over configurations of
`r+1` distinct nodes **of `I`** tend to `L` as all the nodes tend to `x` inside `I`. -/
def DDLimOn (I : Set ℝ) (f : ℝ → ℝ) (r : ℕ) (x L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ s : Finset ℝ, s.card = r + 1 → (↑s ⊆ I) → (∀ t ∈ s, |t - x| < δ) →
    |ddiff f s - L| < ε

/-- `f` admits an interpolated Taylor expansion of order `n` at `x` relative to `I`. -/
def HasDITOn (I : Set ℝ) (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : Prop := ∃ L, DDLimOn I f n x L

/-- Auxiliary: the value described by a predicate on `ℝ`, with junk value `0`. -/
noncomputable def theVal (P : ℝ → Prop) : ℝ := by
  classical
  exact if h : ∃ L, P L then h.choose else 0

lemma theVal_spec {P : ℝ → Prop} (h : ∃ L, P L) : P (theVal P) := by
  classical
  simp only [theVal, dif_pos h]
  exact h.choose_spec

lemma theVal_congr {P Q : ℝ → Prop} (h : ∀ L, P L ↔ Q L) : theVal P = theVal Q := by
  have : P = Q := funext fun L => propext (h L)
  rw [this]

/-- The relative limit `λ_r(f;x)` of the divided differences of order `r` (junk value `0` when
it does not exist). -/
noncomputable def ddLimValOn (I : Set ℝ) (f : ℝ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  theVal (fun L => DDLimOn I f r x L)

/-- `f^{[r]}(x)` relative to `I`: `r !` times the relative limit of the divided differences. -/
noncomputable def ditTopOn (I : Set ℝ) (f : ℝ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  (Nat.factorial r : ℝ) * ddLimValOn I f r x

/-- The monomial coefficient `c_q` of the interpolation polynomials at nodes of `I` converges
to `L` as all `n+1` nodes tend to `x` inside `I`. -/
def CoeffLimOn (I : Set ℝ) (f : ℝ → ℝ) (n q : ℕ) (x L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ s : Finset ℝ, s.card = n + 1 → (↑s ⊆ I) → (∀ t ∈ s, |t - x| < δ) →
    |(interpPoly f s).coeff q - L| < ε

/-- The literal definition of `DIT(n)` relative to `I`: every coefficient `c_q`, `q ≤ n`, of the
Lagrange interpolation polynomial has a finite limit as all the nodes tend to `x` inside `I`. -/
def HasDITcoeffOn (I : Set ℝ) (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : Prop :=
  ∀ q ≤ n, ∃ L, CoeffLimOn I f n q x L

/-! ## Dependence only on the restriction of `f` to `I` -/

variable {I : Set ℝ}

lemma ddiff_congr {f g : ℝ → ℝ} {s : Finset ℝ} (h : Set.EqOn f g I) (hs : ↑s ⊆ I) :
    ddiff f s = ddiff g s := by
  unfold ddiff
  exact Finset.sum_congr rfl fun t ht => by rw [h (hs ht)]

lemma lagrEval_congr {f g : ℝ → ℝ} {s : Finset ℝ} (h : Set.EqOn f g I) (hs : ↑s ⊆ I) (y : ℝ) :
    lagrEval f s y = lagrEval g s y := by
  unfold lagrEval
  exact Finset.sum_congr rfl fun t ht => by rw [h (hs ht)]

lemma interpPoly_congr {f g : ℝ → ℝ} {s : Finset ℝ} (h : Set.EqOn f g I) (hs : ↑s ⊆ I) :
    interpPoly f s = interpPoly g s := by
  unfold interpPoly Lagrange.interpolate
  exact Finset.sum_congr rfl fun t ht => by rw [h (hs ht)]

lemma DDLimOn_congr {f g : ℝ → ℝ} (h : Set.EqOn f g I) (r : ℕ) (x L : ℝ) :
    DDLimOn I f r x L ↔ DDLimOn I g r x L := by
  constructor <;> intro H ε hε <;> obtain ⟨δ, hδ, hδ'⟩ := H ε hε <;>
    refine ⟨δ, hδ, fun s hs hsI hsx => ?_⟩
  · rw [← ddiff_congr h hsI]; exact hδ' s hs hsI hsx
  · rw [ddiff_congr h hsI]; exact hδ' s hs hsI hsx

lemma HasDITOn_congr {f g : ℝ → ℝ} (h : Set.EqOn f g I) (n : ℕ) (x : ℝ) :
    HasDITOn I f n x ↔ HasDITOn I g n x :=
  exists_congr fun L => DDLimOn_congr h n x L

lemma ddLimValOn_congr {f g : ℝ → ℝ} (h : Set.EqOn f g I) (r : ℕ) (x : ℝ) :
    ddLimValOn I f r x = ddLimValOn I g r x :=
  theVal_congr fun L => DDLimOn_congr h r x L

lemma ditTopOn_congr {f g : ℝ → ℝ} (h : Set.EqOn f g I) (r : ℕ) (x : ℝ) :
    ditTopOn I f r x = ditTopOn I g r x := by
  rw [ditTopOn, ditTopOn, ddLimValOn_congr h r x]

lemma CoeffLimOn_congr {f g : ℝ → ℝ} (h : Set.EqOn f g I) (n q : ℕ) (x L : ℝ) :
    CoeffLimOn I f n q x L ↔ CoeffLimOn I g n q x L := by
  constructor <;> intro H ε hε <;> obtain ⟨δ, hδ, hδ'⟩ := H ε hε <;>
    refine ⟨δ, hδ, fun s hs hsI hsx => ?_⟩
  · rw [← interpPoly_congr h hsI]; exact hδ' s hs hsI hsx
  · rw [interpPoly_congr h hsI]; exact hδ' s hs hsI hsx

lemma HasDITcoeffOn_congr {f g : ℝ → ℝ} (h : Set.EqOn f g I) (n : ℕ) (x : ℝ) :
    HasDITcoeffOn I f n x ↔ HasDITcoeffOn I g n x :=
  forall₂_congr fun q _ => exists_congr fun L => CoeffLimOn_congr h n q x L

/-! ## Existence of relative node configurations -/

lemma exists_ne_of_nontrivial (hne : I.Nontrivial) {x : ℝ} : ∃ y ∈ I, y ≠ x := by
  obtain ⟨a, ha, b, hb, hab⟩ := hne
  by_cases h : a = x
  · exact ⟨b, hb, fun hc => hab (h.trans hc.symm)⟩
  · exact ⟨a, ha, h⟩

/-- In a nondegenerate interval, every relative neighborhood of a point (**including an
endpoint**) contains a nonempty open interval contained in `I`. -/
lemma exists_Ioo_subset (hI : I.OrdConnected) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) (hyx : y ≠ x)
    {δ : ℝ} (hδ : 0 < δ) : ∃ a b : ℝ, a < b ∧ Set.Ioo a b ⊆ I ∩ Metric.ball x δ := by
  rcases lt_or_gt_of_ne hyx with hlt | hlt
  · -- `y < x`: use an interval to the left of `x`
    refine ⟨max y (x - δ), x, ?_, ?_⟩
    · exact max_lt hlt (by linarith)
    · rintro t ⟨h1, h2⟩
      have h1' : y ≤ t := le_of_lt (lt_of_le_of_lt (le_max_left _ _) h1)
      have h1'' : x - δ < t := lt_of_le_of_lt (le_max_right _ _) h1
      refine ⟨hI.out hy hx ⟨h1', h2.le⟩, ?_⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith
  · -- `x < y`: use an interval to the right of `x`
    refine ⟨x, min y (x + δ), ?_, ?_⟩
    · exact lt_min hlt (by linarith)
    · rintro t ⟨h1, h2⟩
      have h2' : t ≤ y := le_of_lt (lt_of_lt_of_le h2 (min_le_left _ _))
      have h2'' : t < x + δ := lt_of_lt_of_le h2 (min_le_right _ _)
      refine ⟨hI.out hx hy ⟨h1.le, h2'⟩, ?_⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith

/-- **Nondegeneracy.**  A nondegenerate interval has arbitrarily many fresh nodes in every
relative neighborhood of each of its points, including its endpoints. -/
lemma exists_nodesOn (hI : I.OrdConnected) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) (hyx : y ≠ x)
    {δ : ℝ} (hδ : 0 < δ) (m : ℕ) (A : Finset ℝ) :
    ∃ s : Finset ℝ, s.card = m ∧ ↑s ⊆ I ∧ (∀ t ∈ s, |t - x| < δ) ∧ Disjoint s A := by
  obtain ⟨a, b, hab, hsub⟩ := exists_Ioo_subset hI hx hy hyx hδ
  have hinf : (Set.Ioo a b \ (A : Set ℝ)).Infinite :=
    (Set.Ioo_infinite hab).diff A.finite_toSet
  obtain ⟨s, hsub', hcard⟩ := hinf.exists_subset_card_eq m
  refine ⟨s, hcard, fun t ht => (hsub (hsub' ht).1).1, fun t ht => ?_, ?_⟩
  · have := (hsub (hsub' ht).1).2
    rw [Metric.mem_ball, Real.dist_eq] at this
    exact this
  · rw [Finset.disjoint_left]
    intro c hc hcA
    exact (hsub' hc).2 hcA

/-- Same, in the form used to produce configurations of a prescribed order. -/
lemma exists_nodesOn' (hI : I.OrdConnected) (hne : I.Nontrivial) {x : ℝ} (hx : x ∈ I)
    {δ : ℝ} (hδ : 0 < δ) (m : ℕ) (A : Finset ℝ) :
    ∃ s : Finset ℝ, s.card = m ∧ ↑s ⊆ I ∧ (∀ t ∈ s, |t - x| < δ) ∧ Disjoint s A := by
  obtain ⟨y, hy, hyx⟩ := exists_ne_of_nontrivial hne (x := x)
  exact exists_nodesOn hI hx hy hyx hδ m A

/-! ## Uniqueness of relative limits -/

theorem DDLimOn.unique (hI : I.OrdConnected) (hne : I.Nontrivial) {f : ℝ → ℝ} {r : ℕ}
    {x L1 L2 : ℝ} (hx : x ∈ I) (h1 : DDLimOn I f r x L1) (h2 : DDLimOn I f r x L2) : L1 = L2 := by
  by_contra hne'
  set ε := |L1 - L2| / 2 with hε
  have hεpos : 0 < ε := by
    have : L1 - L2 ≠ 0 := sub_ne_zero.2 hne'
    positivity
  obtain ⟨δ1, hδ1, hδ1'⟩ := h1 ε hεpos
  obtain ⟨δ2, hδ2, hδ2'⟩ := h2 ε hεpos
  obtain ⟨s, hs, hsI, hsx, -⟩ :=
    exists_nodesOn' hI hne hx (lt_min hδ1 hδ2) (r + 1) ∅
  have e1 := hδ1' s hs hsI (fun t ht => lt_of_lt_of_le (hsx t ht) (min_le_left _ _))
  have e2 := hδ2' s hs hsI (fun t ht => lt_of_lt_of_le (hsx t ht) (min_le_right _ _))
  have htri : |L1 - L2| ≤ |ddiff f s - L1| + |ddiff f s - L2| := by
    calc |L1 - L2| = |(ddiff f s - L2) - (ddiff f s - L1)| := by ring_nf
      _ ≤ |ddiff f s - L2| + |ddiff f s - L1| := abs_sub _ _
      _ = |ddiff f s - L1| + |ddiff f s - L2| := by ring
  rw [hε] at e1 e2
  linarith

lemma ddLimOn_spec {f : ℝ → ℝ} {r : ℕ} {x : ℝ} (h : ∃ L, DDLimOn I f r x L) :
    DDLimOn I f r x (ddLimValOn I f r x) := theVal_spec h

lemma ddLimValOn_eq (hI : I.OrdConnected) (hne : I.Nontrivial) {f : ℝ → ℝ} {r : ℕ} {x L : ℝ}
    (hx : x ∈ I) (h : DDLimOn I f r x L) : ddLimValOn I f r x = L :=
  DDLimOn.unique hI hne hx (ddLimOn_spec ⟨L, h⟩) h

/-! ## The degenerate case

If `I` is a single point, no configuration of two or more distinct nodes exists inside `I`, so
every real number is a relative limit of the (empty family of) divided differences of order
`r ≥ 1`; this is why the nondegeneracy hypothesis `I.Nontrivial` is exactly the implicit
assumption of the printed definition for `n ≥ 1`.  (At order `0` the definition is meaningful
even then: see `hasDITOn_zero_iff`.) -/
theorem DDLimOn_of_subsingleton {f : ℝ → ℝ} {r : ℕ} (hr : 1 ≤ r) {x : ℝ}
    (hI : ∀ y ∈ I, y = x) (L : ℝ) : DDLimOn I f r x L := by
  refine fun ε hε => ⟨1, one_pos, fun s hs hsI _ => ?_⟩
  exfalso
  have h2 : 2 ≤ s.card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (show 1 < s.card by omega)
  exact hab ((hI a (hsI ha)).trans (hI b (hsI hb)).symm)

theorem not_unique_of_subsingleton {f : ℝ → ℝ} {r : ℕ} (hr : 1 ≤ r) {x : ℝ}
    (hI : ∀ y ∈ I, y = x) : ¬ ∀ L1 L2 : ℝ, DDLimOn I f r x L1 → DDLimOn I f r x L2 → L1 = L2 := by
  intro h
  have := h 0 1 (DDLimOn_of_subsingleton hr hI 0) (DDLimOn_of_subsingleton hr hI 1)
  norm_num at this

/-! ## Order zero: the continuity convention -/

lemma ddiff_singleton' (f : ℝ → ℝ) (a : ℝ) : ddiff f {a} = f a := by simp [ddiff]

/-- With the finset (continuity) convention, relative `DIT(0)` at `x ∈ I` is exactly relative
continuity of `f` at `x`, and the limit value is `f x`. -/
theorem hasDITOn_zero_iff {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ I) :
    HasDITOn I f 0 x ↔ ContinuousWithinAt f I x := by
  constructor
  · rintro ⟨L, hL⟩
    have hLx : L = f x := by
      by_contra hc
      have hpos : 0 < |f x - L| := by
        simpa [sub_eq_zero] using fun h => hc h.symm
      obtain ⟨δ, hδ, hδ'⟩ := hL _ hpos
      have := hδ' {x} (by simp) (by simpa using hx) (by simp [hδ])
      rw [ddiff_singleton'] at this
      linarith
    subst hLx
    rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hL ε hε
    refine ⟨δ, hδ, fun y hy hdist => ?_⟩
    have := hδ' {y} (by simp) (by simpa using hy) (by
      intro u hu
      simp only [Finset.mem_singleton] at hu; subst hu
      rwa [Real.dist_eq] at hdist)
    rw [ddiff_singleton'] at this
    rwa [Real.dist_eq]
  · intro hc
    refine ⟨f x, fun ε hε => ?_⟩
    rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds] at hc
    obtain ⟨δ, hδ, hδ'⟩ := hc ε hε
    refine ⟨δ, hδ, fun s hs hsI hsx => ?_⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hs
    rw [ddiff_singleton']
    have ha : a ∈ I := hsI (by simp)
    have hax : |a - x| < δ := hsx a (by simp)
    have := hδ' ha (by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at this

lemma ddLimValOn_zero {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ I) (h : HasDITOn I f 0 x) :
    ddLimValOn I f 0 x = f x := by
  have hL : DDLimOn I f 0 x (ddLimValOn I f 0 x) := ddLimOn_spec h
  by_contra hc
  have hpos : 0 < |f x - ddLimValOn I f 0 x| := by
    simpa [sub_eq_zero] using fun h' => hc h'.symm
  obtain ⟨δ, hδ, hδ'⟩ := hL _ hpos
  have := hδ' {x} (by simp) (by simpa using hx) (by simp [hδ])
  rw [ddiff_singleton'] at this
  linarith

/-! ## Compatibility with the whole-line theory -/

lemma DDLimOn_univ (f : ℝ → ℝ) (r : ℕ) (x L : ℝ) :
    DDLimOn Set.univ f r x L ↔ DDLim f r x L := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h ε hε
    exact ⟨δ, hδ, fun s hs hsx => hδ' s hs (by simp) hsx⟩
  · intro h ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h ε hε
    exact ⟨δ, hδ, fun s hs _ hsx => hδ' s hs hsx⟩

lemma HasDITOn_univ (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    HasDITOn Set.univ f n x ↔ HasDIT f n x :=
  exists_congr fun L => DDLimOn_univ f n x L

lemma CoeffLimOn_univ (f : ℝ → ℝ) (n q : ℕ) (x L : ℝ) :
    CoeffLimOn Set.univ f n q x L ↔ CoeffLim f n q x L := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h ε hε
    exact ⟨δ, hδ, fun s hs hsx => hδ' s hs (by simp) hsx⟩
  · intro h ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h ε hε
    exact ⟨δ, hδ, fun s hs _ hsx => hδ' s hs hsx⟩

lemma HasDITcoeffOn_univ (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    HasDITcoeffOn Set.univ f n x ↔ HasDITcoeff f n x :=
  forall₂_congr fun q _ => exists_congr fun L => CoeffLimOn_univ f n q x L

lemma univ_ordConnected : (Set.univ : Set ℝ).OrdConnected := ⟨fun _ _ _ _ _ _ => trivial⟩

lemma univ_nontrivial : (Set.univ : Set ℝ).Nontrivial :=
  ⟨0, trivial, 1, trivial, by norm_num⟩

lemma ddLimValOn_univ (f : ℝ → ℝ) (r : ℕ) (x : ℝ) :
    ddLimValOn Set.univ f r x = ddLimVal f r x := by
  by_cases h : ∃ L, DDLim f r x L
  · obtain ⟨L, hL⟩ := h
    rw [ddLimVal_eq hL,
      ddLimValOn_eq univ_ordConnected univ_nontrivial (Set.mem_univ x)
        ((DDLimOn_univ f r x L).2 hL)]
  · have h' : ¬ ∃ L, DDLimOn Set.univ f r x L := fun ⟨L, hL⟩ => h ⟨L, (DDLimOn_univ f r x L).1 hL⟩
    simp only [ddLimValOn, ddLimVal, theVal, dif_neg h', dif_neg h]

lemma ditTopOn_univ (f : ℝ → ℝ) (r : ℕ) (x : ℝ) :
    ditTopOn Set.univ f r x = ditTop f r x := by
  rw [ditTopOn, ditTop, ddLimValOn_univ]

end Q587
