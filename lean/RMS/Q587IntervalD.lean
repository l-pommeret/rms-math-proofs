/-
# Q587 — the arbitrary-interval layer, part 5 (Gate 5): part (d)

Part (d) on an arbitrary nondegenerate interval `I`.  Relative `DIT(p)` at **every point of `I`**
(endpoints included) forces the relative regularity `ContDiffOn ℝ p f I`, identifies
`f^{[p]} = ditTopOn I f p` with the relative `p`-th derivative on `I`, and yields
`DIT(p+k)` for `f` ⟺ `DIT(k)` for `f^{[p]}`.

The order-zero conventions are treated separately at the end: under the continuity convention the
statement is the tautological relative case, while under the punctured convention the §8
counterexample of the baseline is generalized to an arbitrary nondegenerate interval containing
the origin.
-/

import RMS.Q587IntervalC

open Polynomial Finset

namespace Q587

variable {I : Set ℝ}

/-! ## From relative `DIT` to relative regularity -/

lemma continuousOn_of_hasDITOn_zero (f : ℝ → ℝ) (h : ∀ y ∈ I, HasDITOn I f 0 y) :
    ContinuousOn f I := fun y hy => (hasDITOn_zero_iff hy).1 (h y hy)

/-- Lemma 7.1, first half, relative version: relative `DIT(1)` at `x ∈ I` implies relative
differentiability at `x`, with the relative derivative equal to the limit of the relative
divided differences of order one. -/
lemma hasDerivWithinAt_of_ddLimOn_one (f : ℝ → ℝ) (x L : ℝ) (hx : x ∈ I)
    (h : DDLimOn I f 1 x L) : HasDerivWithinAt f L I x := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := h ε hε
  refine ⟨δ, hδ, fun t ht hdist => ?_⟩
  have htI : t ∈ I := ht.1
  have hxt : x ≠ t := fun hc => ht.2 (by simp [hc])
  have hcard : ({x, t} : Finset ℝ).card = 1 + 1 := Finset.card_pair hxt
  have hsub : ((↑({x, t} : Finset ℝ)) : Set ℝ) ⊆ I := by
    intro z hz
    have hz' : z ∈ ({x, t} : Finset ℝ) := hz
    rcases Finset.mem_insert.1 hz' with rfl | hz2
    · exact hx
    · simp only [Finset.mem_singleton] at hz2; subst hz2; exact htI
  have hnodes : ∀ u ∈ ({x, t} : Finset ℝ), |u - x| < δ := by
    intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · simpa using hδ
    · simp only [Finset.mem_singleton] at hu
      subst hu
      simpa [Real.dist_eq] using hdist
  have := hδ' {x, t} hcard hsub hnodes
  rw [ddiff_pair f x t hxt] at this
  rw [Real.dist_eq, slope_def_field]
  simpa using this

/-- Lemma 7.1, second half, relative version: if `f` has relative `DIT(1)` at every point of `I`,
the relative limits `λ₁(f;·)` depend continuously on the point, relatively to `I`. -/
lemma continuousOn_ddLimValOn_one (hI : I.OrdConnected) (hne : I.Nontrivial) (f : ℝ → ℝ)
    (h : ∀ y ∈ I, HasDITOn I f 1 y) : ContinuousOn (fun y => ddLimValOn I f 1 y) I := by
  intro x hx
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hL : DDLimOn I f 1 x (ddLimValOn I f 1 x) := ddLimOn_spec (h x hx)
  obtain ⟨δ, hδ, hδ'⟩ := hL (ε/2) (by linarith)
  refine ⟨δ/2, by linarith, fun y hy hdist => ?_⟩
  have hyI : y ∈ I := hy
  have hyx : |y - x| < δ/2 := by rwa [Real.dist_eq] at hdist
  have hM : DDLimOn I f 1 y (ddLimValOn I f 1 y) := ddLimOn_spec (h y hyI)
  obtain ⟨δ2, hδ2, hδ2'⟩ := hM (ε/2) (by linarith)
  obtain ⟨s, hscard, hsI, hsy, hsdisj⟩ :=
    exists_nodesOn' hI hne hyI (lt_min hδ2 (by linarith : (0:ℝ) < δ/2)) 1 {y}
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 hscard
  have hvI : v ∈ I := hsI (by simp)
  have hvy : |v - y| < min δ2 (δ/2) := hsy v (by simp)
  have hyv : y ≠ v := by
    intro hc
    exact (Finset.disjoint_left.1 hsdisj (by simp : v ∈ ({v} : Finset ℝ)))
      (by simp [hc])
  have hcard : ({y, v} : Finset ℝ).card = 1 + 1 := Finset.card_pair hyv
  have hsub : ((↑({y, v} : Finset ℝ)) : Set ℝ) ⊆ I := by
    intro z hz
    have hz' : z ∈ ({y, v} : Finset ℝ) := hz
    rcases Finset.mem_insert.1 hz' with rfl | hz2
    · exact hyI
    · simp only [Finset.mem_singleton] at hz2; subst hz2; exact hvI
  have h1 : |ddiff f {y, v} - ddLimValOn I f 1 y| < ε/2 := by
    refine hδ2' {y, v} hcard hsub ?_
    intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · simpa using hδ2
    · simp only [Finset.mem_singleton] at hu; subst hu
      exact lt_of_lt_of_le hvy (min_le_left _ _)
  have h2 : |ddiff f {y, v} - ddLimValOn I f 1 x| < ε/2 := by
    refine hδ' {y, v} hcard hsub ?_
    intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · linarith [hyx]
    · simp only [Finset.mem_singleton] at hu; subst hu
      have hvy2 : |u - y| < δ/2 := lt_of_lt_of_le hvy (min_le_right _ _)
      calc |u - x| = |(u - y) + (y - x)| := by ring_nf
        _ ≤ |u - y| + |y - x| := abs_add_le _ _
        _ < δ/2 + δ/2 := by linarith
        _ = δ := by ring
  rw [Real.dist_eq]
  have e : ddLimValOn I f 1 y - ddLimValOn I f 1 x
      = (ddiff f {y, v} - ddLimValOn I f 1 x) - (ddiff f {y, v} - ddLimValOn I f 1 y) := by ring
  rw [e]
  calc |(ddiff f {y, v} - ddLimValOn I f 1 x) - (ddiff f {y, v} - ddLimValOn I f 1 y)|
      ≤ |ddiff f {y, v} - ddLimValOn I f 1 x| + |ddiff f {y, v} - ddLimValOn I f 1 y| :=
        abs_sub _ _
    _ < ε := by linarith

/-- **Lemma 7.1 on an interval.**  If `f` has relative `DIT(1)` at every point of `I` then `f` is
differentiable within `I` with relative derivative `λ₁(f;·)`. -/
theorem ditOn_one_derivWithin_eq (hI : I.OrdConnected) (hne : I.Nontrivial) (f : ℝ → ℝ)
    (h : ∀ y ∈ I, HasDITOn I f 1 y) :
    (∀ y ∈ I, HasDerivWithinAt f (ddLimValOn I f 1 y) I y) ∧
      ∀ y ∈ I, derivWithin f I y = ddLimValOn I f 1 y := by
  have huniq : UniqueDiffOn ℝ I := uniqueDiffOn_of_ordConnected hI hne
  have hd : ∀ y ∈ I, HasDerivWithinAt f (ddLimValOn I f 1 y) I y := fun y hy =>
    hasDerivWithinAt_of_ddLimOn_one f y _ hy (ddLimOn_spec (h y hy))
  exact ⟨hd, fun y hy => (hd y hy).derivWithin (huniq y hy)⟩

/-- **Proposition 7.2 on an interval**, regularity part: relative `DIT(p)` at every point of a
nondegenerate interval `I` forces the exact relative regularity `ContDiffOn ℝ p f I`. -/
theorem contDiffOn_of_hasDITOn (hI : I.OrdConnected) (hne : I.Nontrivial) (p : ℕ) :
    ∀ f : ℝ → ℝ, (∀ y ∈ I, HasDITOn I f p y) → ContDiffOn ℝ (p : ℕ) f I := by
  have huniq : UniqueDiffOn ℝ I := uniqueDiffOn_of_ordConnected hI hne
  induction p with
  | zero =>
    intro f h
    have hc : ContinuousOn f I := continuousOn_of_hasDITOn_zero f h
    simpa using (contDiffOn_zero (𝕜 := ℝ) (f := f) (s := I)).2 hc
  | succ p ih =>
    intro f h
    have hone : ∀ y ∈ I, HasDITOn I f 1 y := fun y hy =>
      exists_ddLimOn_of_le hI hne f y hy (p+1) (h y hy) 1 (by omega)
    obtain ⟨hd, hderiv⟩ := ditOn_one_derivWithin_eq hI hne f hone
    have hd' : ∀ y ∈ I, HasDerivWithinAt f (derivWithin f I y) I y := by
      intro y hy; rw [hderiv y hy]; exact hd y hy
    have hDeriv : ∀ y ∈ I, HasDITOn I (derivWithin f I) p y := fun y hy =>
      (hasDITOn_deriv_iff hI hne f (derivWithin f I) hd' y p).1 (h y hy)
    have hcast : ((p+1 : ℕ) : WithTop ℕ∞) = (p : WithTop ℕ∞) + 1 := by push_cast; ring
    rw [hcast, contDiffOn_succ_iff_derivWithin huniq]
    refine ⟨fun y hy => (hd' y hy).differentiableWithinAt, ?_, ih (derivWithin f I) hDeriv⟩
    intro htop
    exact absurd htop (by exact_mod_cast (by simp : ((p : ℕ) : WithTop ℕ∞) ≠ ⊤))

/-- **Proposition 7.2 on an interval**, identity (7.1): if `f` has relative `DIT(p)` at every
point of `I` then `f^{[p]} = ditTopOn I f p` is the relative `p`-th derivative, at every point of
`I`, finite endpoints included. -/
theorem ditTopOn_eq_intervalIteratedDeriv (hI : I.OrdConnected) (hne : I.Nontrivial) (p : ℕ)
    (f : ℝ → ℝ) (h : ∀ y ∈ I, HasDITOn I f p y) (x : ℝ) (hx : x ∈ I) :
    ditTopOn I f p x = intervalIteratedDeriv I p f x := by
  have hf : ContDiffOn ℝ (p : ℕ) f I := contDiffOn_of_hasDITOn hI hne p f h
  have hx0 : HasDITOn I f (p + 0) x := by simpa using h x hx
  have h0 : HasDITOn I (intervalIteratedDeriv I p f) 0 x :=
    (part_c_hasDITOn hI hne p f hf x hx 0).1 hx0
  have key := part_c_ddLimValOn hI hne p f hf x hx 0 hx0
  rw [ddLimValOn_zero hx h0] at key
  simpa [ditTopOn] using key.symm

/-- **Part (d) on an arbitrary nondegenerate interval** (endpoints included).  If `f` has
relative `DIT(p)` at every point of `I`, then for every `k` and every `x ∈ I`, `f` has relative
`DIT(p+k)` at `x` if and only if `f^{[p]} = ditTopOn I f p` has relative `DIT(k)` at `x`. -/
theorem part_d_On (hI : I.OrdConnected) (hne : I.Nontrivial) (p k : ℕ) (f : ℝ → ℝ)
    (h : ∀ y ∈ I, HasDITOn I f p y) (x : ℝ) (hx : x ∈ I) :
    HasDITOn I f (p + k) x ↔ HasDITOn I (fun y => ditTopOn I f p y) k x := by
  have hf : ContDiffOn ℝ (p : ℕ) f I := contDiffOn_of_hasDITOn hI hne p f h
  have he : Set.EqOn (fun y => ditTopOn I f p y) (intervalIteratedDeriv I p f) I :=
    fun y hy => ditTopOn_eq_intervalIteratedDeriv hI hne p f h y hy
  rw [HasDITOn_congr he k x]
  exact part_c_hasDITOn hI hne p f hf x hx k

/-! ## The order-zero conventions -/

/-- The relative tautological case of part (d) at `p = 0`, under the continuity convention:
`f^{[0]} = f` on `I`, so the equivalence holds trivially. -/
theorem part_d_zeroOn (f : ℝ → ℝ) (x : ℝ) (k : ℕ)
    (h : ∀ y ∈ I, HasDITOn I f 0 y) :
    HasDITOn I f (0 + k) x ↔ HasDITOn I (fun y => ditTopOn I f 0 y) k x := by
  have he : Set.EqOn (fun y => ditTopOn I f 0 y) f I := by
    intro y hy
    simp only [ditTopOn, Nat.factorial_zero, Nat.cast_one, one_mul]
    exact ddLimValOn_zero hy (h y hy)
  rw [HasDITOn_congr he k x, Nat.zero_add]

/-- The punctured-limit convention at order zero, relative to `I`. -/
def PunctLimOn (I : Set ℝ) (f : ℝ → ℝ) (x L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t ∈ I, t ≠ x → |t - x| < δ → |f t - L| < ε

lemma hasDITOn_zero_fun (n : ℕ) (x : ℝ) : HasDITOn I (fun _ : ℝ => (0:ℝ)) n x := by
  refine ⟨0, fun ε hε => ⟨1, one_pos, fun s _ _ _ => ?_⟩⟩
  simp [ddiff, hε]

/-- **The order-zero counterexample of §8, on an arbitrary nondegenerate interval containing the
origin.**  Under the *punctured* convention the relative limit of the indicator `cex` of `{0}`
exists at every point of `I` and is `0`, so `cex^{[0]}` would be the zero function, which has
relative `DIT(1)` at `0`; but `cex` itself does not have relative `DIT(1)` at `0`.  Hence part (d)
fails at `p = 0` under that convention, on every such interval. -/
theorem order_zero_counterexampleOn (hI : I.OrdConnected) (hne : I.Nontrivial) (h0 : (0:ℝ) ∈ I) :
    (∀ x ∈ I, PunctLimOn I cex x 0) ∧ HasDITOn I (fun _ : ℝ => (0:ℝ)) 1 0 ∧
      ¬ HasDITOn I cex 1 0 := by
  refine ⟨?_, hasDITOn_zero_fun 1 0, ?_⟩
  · intro x _ ε hε
    obtain ⟨δ, hδ, hδ'⟩ := cex_punctLim x ε hε
    exact ⟨δ, hδ, fun t _ ht hdist => hδ' t ht hdist⟩
  · rintro ⟨L, hL⟩
    obtain ⟨δ, hδ, hδ'⟩ := hL 1 one_pos
    have hLpos : (0:ℝ) < |L| + 1 := by positivity
    obtain ⟨s, hscard, hsI, hst, hsdisj⟩ :=
      exists_nodesOn' hI hne h0 (lt_min hδ (by positivity : (0:ℝ) < 1/(|L|+1))) 1 {0}
    obtain ⟨t, rfl⟩ := Finset.card_eq_one.1 hscard
    have htI : t ∈ I := hsI (by simp)
    have ht0 : t ≠ 0 := by
      intro hc
      exact (Finset.disjoint_left.1 hsdisj (by simp : t ∈ ({t} : Finset ℝ))) (by simp [hc])
    have habs : |t - 0| < min δ (1/(|L|+1)) := hst t (by simp)
    rw [sub_zero] at habs
    have htδ : |t| < δ := lt_of_lt_of_le habs (min_le_left _ _)
    have htb : |t| ≤ 1/(|L|+1) := (lt_of_lt_of_le habs (min_le_right _ _)).le
    have hne0 : (0:ℝ) ≠ t := fun hc => ht0 hc.symm
    have hcard : (({0, t} : Finset ℝ)).card = 1 + 1 := Finset.card_pair hne0
    have hsub : ((↑({0, t} : Finset ℝ)) : Set ℝ) ⊆ I := by
      intro z hz
      have hz' : z ∈ ({0, t} : Finset ℝ) := hz
      rcases Finset.mem_insert.1 hz' with rfl | hz2
      · exact h0
      · simp only [Finset.mem_singleton] at hz2; subst hz2; exact htI
    have hnodes : ∀ u ∈ ({0, t} : Finset ℝ), |u - 0| < δ := by
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · simpa using hδ
      · simp only [Finset.mem_singleton] at hu; subst hu
        rwa [sub_zero]
    have hdd := hδ' {0, t} hcard hsub hnodes
    rw [ddiff_pair cex 0 t hne0] at hdd
    have hcex : cex t = 0 := by simp [cex, ht0]
    have hcex0 : cex 0 = 1 := by simp [cex]
    rw [hcex, hcex0, sub_zero, zero_sub, neg_div] at hdd
    have htpos : 0 < |t| := abs_pos.2 ht0
    have h1t : |L| + 1 ≤ 1/|t| := by
      rw [le_div_iff₀ htpos]
      calc (|L|+1) * |t| ≤ (|L|+1) * (1/(|L|+1)) :=
            mul_le_mul_of_nonneg_left htb (le_of_lt hLpos)
        _ = 1 := by field_simp
    have hfin : |(1:ℝ)/t| - |L| ≤ |(-(1/t)) - L| := by
      have := abs_sub_abs_le_abs_sub (-(1/t)) L
      rwa [abs_neg] at this
    rw [abs_one_div] at hfin
    linarith

end Q587
