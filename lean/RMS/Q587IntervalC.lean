/-
# Q587 — the arbitrary-interval layer, part 4 (Gate 4): relative differentiation and part (c)

The differentiation theorem (Lemma 5.1) and part (c) on an arbitrary nondegenerate interval `I`,
with *relative* (one-sided at the endpoints) derivatives: `f` is only assumed differentiable
*within* `I`, `C^p` means `ContDiffOn ℝ p f I`, and the iterated derivative is the iterate of
`derivWithin · I`.  No two-sided extension of `f` past an endpoint is used.
-/

import RMS.Q587IntervalB

open Polynomial Finset

namespace Q587

variable {I : Set ℝ}

/-! ## The relative iterated derivative -/

/-- The `p`-th derivative of `f` relative to `I`: the `p`-th iterate of `derivWithin · I`.
At an interior point this is the usual iterated derivative; at a finite endpoint of `I` it is
the iterated one-sided derivative. -/
noncomputable def intervalIteratedDeriv (I : Set ℝ) (p : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (fun g => derivWithin g I)^[p] f

@[simp] lemma intervalIteratedDeriv_zero (f : ℝ → ℝ) : intervalIteratedDeriv I 0 f = f := rfl

lemma intervalIteratedDeriv_succ' (p : ℕ) (f : ℝ → ℝ) :
    intervalIteratedDeriv I (p + 1) f = intervalIteratedDeriv I p (derivWithin f I) :=
  Function.iterate_succ_apply _ _ _

lemma intervalIteratedDeriv_univ (p : ℕ) (f : ℝ → ℝ) :
    intervalIteratedDeriv Set.univ p f = iteratedDeriv p f := by
  induction p generalizing f with
  | zero => simp [iteratedDeriv_zero]
  | succ p ih =>
    rw [intervalIteratedDeriv_succ', ih, iteratedDeriv_succ']
    congr 1
    funext y
    rw [derivWithin_univ]

/-- The relative iterated derivative depends only on the restriction of the function to `I`. -/
lemma intervalIteratedDeriv_congr {F G : ℝ → ℝ} (h : Set.EqOn F G I) :
    ∀ p : ℕ, Set.EqOn (intervalIteratedDeriv I p F) (intervalIteratedDeriv I p G) I := by
  intro p
  induction p generalizing F G with
  | zero => simpa using h
  | succ p ih =>
    have h1 : Set.EqOn (derivWithin F I) (derivWithin G I) I := fun y hy =>
      derivWithin_congr h (h hy)
    simpa [intervalIteratedDeriv_succ'] using ih h1

/-- A nondegenerate interval has a nonempty interior, hence is a set of unique differentiability. -/
lemma uniqueDiffOn_of_ordConnected (hI : I.OrdConnected) (hne : I.Nontrivial) :
    UniqueDiffOn ℝ I := by
  obtain ⟨a, ha, b, hb, hab⟩ := hne
  rcases lt_or_gt_of_ne hab with h | h
  · refine uniqueDiffOn_convex hI.convex ⟨(a + b)/2, ?_⟩
    have hsub : Set.Ioo a b ⊆ I := fun z hz => hI.out ha hb ⟨hz.1.le, hz.2.le⟩
    exact interior_maximal hsub isOpen_Ioo ⟨by linarith, by linarith⟩
  · refine uniqueDiffOn_convex hI.convex ⟨(a + b)/2, ?_⟩
    have hsub : Set.Ioo b a ⊆ I := fun z hz => hI.out hb ha ⟨hz.1.le, hz.2.le⟩
    exact interior_maximal hsub isOpen_Ioo ⟨by linarith, by linarith⟩

/-! ## The telescoping estimate, relative version -/

/-- Relative telescoping estimate: shifting all the nodes of a configuration inside `I` by `h`
(so that the shifted nodes still lie in `I`) changes the divided difference of order `r-1` by
approximately `r * h * L`. -/
theorem ddiff_shift_telescopeOn (f : ℝ → ℝ) (x L δ ε h : ℝ) (r : ℕ)
    (hbd : ∀ w : Finset ℝ, w.card = r + 1 → (↑w ⊆ I) → (∀ u ∈ w, |u - x| < δ) →
      |ddiff f w - L| < ε)
    (hh : h ≠ 0) (hhδ : |h| < δ/2) :
    ∀ t s : Finset ℝ, Disjoint t s → ((t ∪ s).card = r) →
      (↑(t ∪ s) ⊆ I) → (∀ u ∈ t, u + h ∈ I) →
      (∀ u ∈ t ∪ s, |u - x| < δ/2) →
      (∀ a ∈ t ∪ s, ∀ b ∈ t ∪ s, a + h ≠ b) →
      |ddiff f (t.image (· + h) ∪ s) - ddiff f (t ∪ s) - t.card * h * L| ≤ t.card * ε * |h| := by
  have hinj : Function.Injective (fun z : ℝ => z + h) := fun a b hab => by simpa using hab
  intro t
  induction t using Finset.induction_on with
  | empty => intro s _ _ _ _ _ _; simp
  | insert a t' ha ih =>
    intro s hdisj hcard hIsub hshift hnear hsep
    have hunion : insert a t' ∪ s = t' ∪ insert a s := by
      ext z; simp [Finset.mem_insert, Finset.mem_union]
    have hdisj' : Disjoint t' (insert a s) := by
      rw [Finset.disjoint_insert_right]
      exact ⟨ha, (Finset.disjoint_insert_left.1 hdisj).2⟩
    have has : a ∉ s := (Finset.disjoint_insert_left.1 hdisj).1
    set A : Finset ℝ := t'.image (· + h) ∪ s with hA
    have himg : (insert a t').image (· + h) ∪ s = insert (a + h) A := by
      rw [Finset.image_insert]
      ext z; simp [hA, Finset.mem_union, Finset.mem_insert]
    have hins : insert a A = t'.image (· + h) ∪ insert a s := by
      ext z; simp [hA, Finset.mem_union, Finset.mem_insert]
    have haK : a ∈ insert a t' ∪ s := by simp
    have haA : a ∉ A := by
      intro hmem
      rcases Finset.mem_union.1 hmem with hmem | hmem
      · obtain ⟨b, hb, hb'⟩ := Finset.mem_image.1 hmem
        exact hsep b (by simp [hb]) a haK hb'
      · exact has hmem
    have hahA : a + h ∉ A := by
      intro hmem
      rcases Finset.mem_union.1 hmem with hmem | hmem
      · obtain ⟨b, hb, hb'⟩ := Finset.mem_image.1 hmem
        exact ha ((hinj hb') ▸ hb)
      · exact hsep a haK (a + h) (by simp [hmem]) rfl
    have hane : a + h ≠ a := by intro hc; exact hh (by linarith [hc])
    have hdisjimg : Disjoint (t'.image (· + h)) s := by
      rw [Finset.disjoint_left]
      intro z hz hzs
      obtain ⟨b, hb, hb'⟩ := Finset.mem_image.1 hz
      exact hsep b (by simp [hb]) z (by simp [hzs]) hb'
    have hcards : (insert a t' ∪ s).card = t'.card + 1 + s.card := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_insert_of_notMem ha]
    have hcardA : A.card + 2 = r + 1 := by
      rw [hA, Finset.card_union_of_disjoint hdisjimg, Finset.card_image_of_injective _ hinj]
      omega
    have hcardbig : (insert (a + h) (insert a A)).card = r + 1 := by
      rw [Finset.card_insert_of_notMem (by simp [hane, hahA]), Finset.card_insert_of_notMem haA]
      omega
    have hAI : (↑A : Set ℝ) ⊆ I := by
      intro z hz
      have hz' : z ∈ A := hz
      rcases Finset.mem_union.1 hz' with hz2 | hz2
      · obtain ⟨b, hb, hb'⟩ := Finset.mem_image.1 hz2
        rw [← hb']
        exact hshift b (by simp [hb])
      · exact hIsub (by simp [hz2] : z ∈ insert a t' ∪ s)
    have hnearA : ∀ u ∈ A, |u - x| < δ := by
      intro u hu
      rcases Finset.mem_union.1 hu with hu | hu
      · obtain ⟨b, hb, hb'⟩ := Finset.mem_image.1 hu
        have h1 : |b - x| < δ/2 := hnear b (by simp [hb])
        have h2 : u - x = (b - x) + h := by rw [← hb']; ring
        rw [h2]
        calc |(b - x) + h| ≤ |b - x| + |h| := abs_add_le _ _
          _ < δ := by linarith
      · exact lt_trans (hnear u (by simp [hu])) (by linarith [abs_nonneg h, hhδ])
    have hbig : |ddiff f (insert (a + h) (insert a A)) - L| < ε := by
      refine hbd _ hcardbig ?_ ?_
      · intro z hz
        have hz' : z ∈ insert (a + h) (insert a A) := hz
        rcases Finset.mem_insert.1 hz' with rfl | hz2
        · exact hshift a (by simp)
        · rcases Finset.mem_insert.1 hz2 with rfl | hz3
          · exact hIsub haK
          · exact hAI hz3
      · intro u hu
        rcases Finset.mem_insert.1 hu with rfl | hu
        · have h1 : |a - x| < δ/2 := hnear a haK
          have h2 : a + h - x = (a - x) + h := by ring
          rw [h2]
          calc |(a - x) + h| ≤ |a - x| + |h| := abs_add_le _ _
            _ < δ := by linarith
        · rcases Finset.mem_insert.1 hu with rfl | hu
          · exact lt_trans (hnear u haK) (by linarith [abs_nonneg h, hhδ])
          · exact hnearA u hu
    have hrep : ddiff f (insert (a + h) A) - ddiff f (insert a A)
        = h * ddiff f (insert (a + h) (insert a A)) := by
      rw [ddiff_replace f A (a + h) a hahA haA hane]
      ring_nf
    have hIH := ih (insert a s) hdisj' (by rw [← hunion]; exact hcard)
      (by rw [← hunion]; exact hIsub) (fun u hu => hshift u (by simp [hu]))
      (by rw [← hunion]; exact hnear) (by rw [← hunion]; exact hsep)
    rw [← hins, ← hunion] at hIH
    rw [himg, Finset.card_insert_of_notMem ha]
    have hstep : |h * ddiff f (insert (a + h) (insert a A)) - h * L| ≤ |h| * ε := by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left hbig.le (abs_nonneg _)
    have hdecomp : ddiff f (insert (a+h) A) - ddiff f (insert a t' ∪ s)
          - ((t'.card : ℝ) + 1) * h * L
        = (ddiff f (insert a A) - ddiff f (insert a t' ∪ s) - (t'.card : ℝ) * h * L)
          + (h * ddiff f (insert (a + h) (insert a A)) - h * L) := by
      rw [← hrep]; ring
    push_cast
    rw [hdecomp]
    calc |(ddiff f (insert a A) - ddiff f (insert a t' ∪ s) - (t'.card : ℝ) * h * L)
          + (h * ddiff f (insert (a + h) (insert a A)) - h * L)| ≤ _ := abs_add_le _ _
      _ ≤ (t'.card : ℝ) * ε * |h| + |h| * ε := by
          have h9 := hIH
          push_cast at h9
          linarith
      _ = ((t'.card : ℝ) + 1) * ε * |h| := by ring

/-! ## The differentiation theorem, relative version -/

/-- Lemma 5.1, forward half, relative version: if `f` is differentiable *within `I`* and has
relative `DIT(m+1)` at `x ∈ I` with limit `L`, then the relative derivative has relative
`DIT(m)` at `x` with limit `(m+1) L`.  The node configurations are shifted only inside `I`, so
the argument works at the endpoints of `I` as well. -/
theorem ddLimOn_deriv_forward (hI : I.OrdConnected) (hne : I.Nontrivial) (f f' : ℝ → ℝ)
    (hderiv : ∀ y ∈ I, HasDerivWithinAt f (f' y) I y) (x L : ℝ) (m : ℕ)
    (hL : DDLimOn I f (m+1) x L) : DDLimOn I f' m x (((m:ℝ)+1) * L) := by
  intro ε hε
  set ε' : ℝ := ε / (2*((m:ℝ)+1)) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := hL ε' hε'pos
  obtain ⟨y0, hy0, hy0x⟩ := exists_ne_of_nontrivial hne (x := x)
  set d : ℝ := |y0 - x| with hd
  have hdpos : 0 < d := abs_pos.2 (sub_ne_zero.2 hy0x)
  refine ⟨min (δ/2) (d/2), lt_min (by linarith) (by linarith), fun K hK hKI hKx => ?_⟩
  have hKδ : ∀ u ∈ K, |u - x| < δ/2 := fun u hu =>
    lt_of_lt_of_le (hKx u hu) (min_le_left _ _)
  have hKd : ∀ u ∈ K, |u - x| < d/2 := fun u hu =>
    lt_of_lt_of_le (hKx u hu) (min_le_right _ _)
  -- the set of admissible shifts
  set T : Set ℝ := {hh : ℝ | ∀ u ∈ K, u + hh ∈ I} with hT
  have h0T : (0:ℝ) ∈ T := fun u hu => by simpa using hKI hu
  -- a one-sided interval of admissible shifts
  have hTside : ∀ hh : ℝ, (0 ≤ (y0 - x) * hh ∧ |hh| ≤ d/2) → hh ∈ T := by
    intro hh ⟨hsign, hsmall⟩ u hu
    have huI : u ∈ I := hKI hu
    have hux : |u - x| < d/2 := hKd u hu
    rcases lt_or_gt_of_ne (sub_ne_zero.2 hy0x) with hneg | hpos
    · -- `y0 < x`, so `hh ≤ 0`
      have hd' : d = x - y0 := by rw [hd, abs_of_neg hneg]; ring
      have hh0 : hh ≤ 0 := by nlinarith
      have h1 : y0 ≤ u + hh := by
        rw [abs_le] at hsmall
        rw [abs_lt] at hux
        linarith [hsmall.1, hux.1]
      have h2 : u + hh ≤ u := by linarith
      exact hI.out hy0 huI ⟨h1, h2⟩
    · -- `x < y0`, so `0 ≤ hh`
      have hd' : d = y0 - x := by rw [hd, abs_of_pos hpos]
      have hh0 : 0 ≤ hh := by nlinarith
      have h1 : u ≤ u + hh := by linarith
      have h2 : u + hh ≤ y0 := by
        rw [abs_le] at hsmall
        rw [abs_lt] at hux
        linarith [hsmall.2, hux.2]
      exact hI.out huI hy0 ⟨h1, h2⟩
  set G : ℝ → ℝ := fun hh => ∑ v ∈ K, f (v + hh) / ∏ u ∈ K.erase v, (v - u) with hG
  have hG0 : G 0 = ddiff f K := by simp [hG, ddiff]
  have hGd : HasDerivWithinAt G (ddiff f' K) T 0 := by
    rw [hG, show (fun hh : ℝ => ∑ v ∈ K, f (v + hh) / ∏ u ∈ K.erase v, (v - u))
        = ∑ v ∈ K, (fun hh : ℝ => f (v + hh) / ∏ u ∈ K.erase v, (v - u)) from by
      funext hh; simp]
    rw [ddiff]
    apply HasDerivWithinAt.sum
    intro v hv
    have hvI : v ∈ I := hKI hv
    have h1 : HasDerivWithinAt (fun hh : ℝ => v + hh) 1 T 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).const_add v).hasDerivWithinAt
    have hmaps : Set.MapsTo (fun hh : ℝ => v + hh) T I := fun hh hhT => hhT v hv
    have h2 : HasDerivWithinAt (fun hh : ℝ => f (v + hh)) (f' v) T 0 := by
      have := HasDerivWithinAt.comp (0:ℝ) (by simpa using hderiv (v + 0) (by simpa using hvI))
        h1 hmaps
      simpa using this
    exact h2.div_const _
  have hslope := hasDerivWithinAt_iff_tendsto_slope.1 hGd
  have hsubT : T \ {(0:ℝ)} ⊆ {(0:ℝ)}ᶜ := fun z hz => hz.2
  have hball : Metric.ball (0:ℝ) (δ/2) ∈ nhds (0:ℝ) := Metric.ball_mem_nhds _ (by linarith)
  have hev : ∀ᶠ hh in nhdsWithin (0:ℝ) (T \ {0}),
      |slope G 0 hh - (((m:ℝ)+1) * L)| ≤ ((m:ℝ)+1) * ε' := by
    filter_upwards [(eventually_sep K).filter_mono (nhdsWithin_mono _ hsubT),
      nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with hh hsep h1 h2
    have hhne : hh ≠ 0 := h2.2
    have hhT : hh ∈ T := h2.1
    have hhabs : |hh| < δ/2 := by simpa [Real.dist_eq] using Metric.mem_ball.1 h1
    have htel := ddiff_shift_telescopeOn f x L δ ε' hh (m+1) hδ' hhne hhabs K ∅
      (by simp) (by simpa using hK) (by simpa using hKI) (fun u hu => hhT u hu)
      (by simpa using hKδ) (by simpa using hsep)
    simp only [Finset.union_empty] at htel
    rw [hK] at htel
    have hGhh : G hh = ddiff f (K.image (· + hh)) := (ddiff_image_add f K hh).symm
    rw [← hGhh, ← hG0] at htel
    have hslope_eq : slope G 0 hh = (G hh - G 0) / hh := by rw [slope_def_field, sub_zero]
    rw [hslope_eq]
    have habs : |(G hh - G 0)/hh - (((m:ℝ)+1) * L)|
        = |G hh - G 0 - (((m:ℝ)+1) * L) * hh| / |hh| := by
      rw [← abs_div]; congr 1; field_simp
    rw [habs, div_le_iff₀ (abs_pos.2 hhne)]
    push_cast at htel
    have heq : G hh - G 0 - (((m:ℝ)+1) * L) * hh = G hh - G 0 - ((m:ℝ)+1) * hh * L := by ring
    rw [heq]
    linarith [htel]
  have hNeBot : (nhdsWithin (0:ℝ) (T \ {0})).NeBot := by
    rcases lt_or_gt_of_ne (sub_ne_zero.2 hy0x) with hneg | hpos
    · have hd' : d = x - y0 := by rw [hd, abs_of_neg hneg]; ring
      refine Filter.neBot_of_le (f := nhdsWithin (0:ℝ) (Set.Iio 0)) ?_
      rw [nhdsWithin_le_iff]
      filter_upwards [Ioo_mem_nhdsLT (show -(d/2) < (0:ℝ) by linarith)] with z hz
      obtain ⟨hz1, hz2⟩ := hz
      refine ⟨hTside z ⟨by nlinarith, ?_⟩, ?_⟩
      · rw [abs_le]; constructor <;> linarith
      · simp only [Set.mem_singleton_iff]
        exact ne_of_lt hz2
    · have hd' : d = y0 - x := by rw [hd, abs_of_pos hpos]
      refine Filter.neBot_of_le (f := nhdsWithin (0:ℝ) (Set.Ioi 0)) ?_
      rw [nhdsWithin_le_iff]
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < d/2 by linarith)] with z hz
      obtain ⟨hz1, hz2⟩ := hz
      refine ⟨hTside z ⟨by nlinarith, ?_⟩, ?_⟩
      · rw [abs_le]; constructor <;> linarith
      · simp only [Set.mem_singleton_iff]
        exact ne_of_gt hz1
  have hlim : Filter.Tendsto (fun hh => |slope G 0 hh - (((m:ℝ)+1) * L)|)
      (nhdsWithin (0:ℝ) (T \ {0})) (nhds |ddiff f' K - ((m:ℝ)+1) * L|) :=
    (hslope.sub_const _).abs
  have hfin := le_of_tendsto hlim hev
  have hlt : ((m:ℝ)+1) * ε' < ε := by
    rw [hε', mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- Rolle's theorem inside `I`: between consecutive interpolation nodes of `I` there is a zero of
the relative derivative of the interpolation error, and it lies in `I`. -/
lemma exists_rolle_nodesOn (hI : I.OrdConnected) (H H' : ℝ → ℝ)
    (hH : ∀ y ∈ I, HasDerivWithinAt H (H' y) I y) (s : Finset ℝ) (m : ℕ)
    (hs : s.card = m + 2) (hsI : ↑s ⊆ I) (hz : ∀ v ∈ s, H v = 0) :
    ∃ S' : Finset ℝ, S'.card = m + 1 ∧ (↑S' ⊆ I) ∧ (∀ w ∈ S', H' w = 0) ∧
      (∀ w ∈ S', ∃ a ∈ s, ∃ b ∈ s, a < w ∧ w < b) := by
  classical
  set z := s.orderIsoOfFin hs with hzdef
  set zz : Fin (m+2) → ℝ := fun i => (z i : ℝ) with hzz
  have hzzmem : ∀ i, zz i ∈ s := fun i => (z i).2
  have hzzI : ∀ i, zz i ∈ I := fun i => hsI (hzzmem i)
  have hzzmono : StrictMono zz := by
    intro i j hij
    exact_mod_cast (z.strictMono hij)
  have hrolle : ∀ i : Fin (m+1), ∃ c ∈ Set.Ioo (zz i.castSucc) (zz i.succ), H' c = 0 := by
    intro i
    have hlt : zz i.castSucc < zz i.succ := hzzmono Fin.castSucc_lt_succ
    have hIcc : Set.Icc (zz i.castSucc) (zz i.succ) ⊆ I :=
      fun w hw => hI.out (hzzI _) (hzzI _) hw
    have hIoo : Set.Ioo (zz i.castSucc) (zz i.succ) ⊆ I :=
      fun w hw => hIcc ⟨hw.1.le, hw.2.le⟩
    have hcont : ContinuousOn H (Set.Icc (zz i.castSucc) (zz i.succ)) := by
      intro w hw
      exact ((hH w (hIcc hw)).continuousWithinAt).mono hIcc
    refine exists_hasDerivAt_eq_zero hlt hcont ?_ ?_
    · rw [hz _ (hzzmem _), hz _ (hzzmem _)]
    · intro y hy
      have hmem : I ∈ nhds y := mem_nhds_iff.2 ⟨_, hIoo, isOpen_Ioo, hy⟩
      exact (hH y (hIoo hy)).hasDerivAt hmem
  choose ξ hξ hξ0 using hrolle
  have hξmono : StrictMono ξ := by
    intro i j hij
    have h1 : ξ i < zz i.succ := (hξ i).2
    have h2 : zz j.castSucc < ξ j := (hξ j).1
    have h3 : zz i.succ ≤ zz j.castSucc := by
      apply hzzmono.monotone
      rw [Fin.le_def]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    linarith
  refine ⟨Finset.image ξ Finset.univ, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hξmono.injective, Finset.card_univ, Fintype.card_fin]
  · intro w hw
    have hw' : w ∈ Finset.image ξ Finset.univ := hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw'
    exact hI.out (hzzI i.castSucc) (hzzI i.succ) ⟨(hξ i).1.le, (hξ i).2.le⟩
  · intro w hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw
    exact hξ0 i
  · intro w hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw
    exact ⟨zz i.castSucc, hzzmem _, zz i.succ, hzzmem _, (hξ i).1, (hξ i).2⟩

/-- Lemma 5.1, backward half, relative version. -/
theorem ddLimOn_deriv_backward (hI : I.OrdConnected) (f f' : ℝ → ℝ)
    (hderiv : ∀ y ∈ I, HasDerivWithinAt f (f' y) I y) (x M : ℝ) (m : ℕ)
    (hM : DDLimOn I f' m x M) : DDLimOn I f (m+1) x (M / ((m:ℝ)+1)) := by
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hM (((m:ℝ)+1) * ε) (by positivity)
  refine ⟨δ, hδ, fun s hs hsI hsx => ?_⟩
  set P := interpPoly f s with hP
  set H : ℝ → ℝ := fun y => f y - P.eval y with hH
  set H' : ℝ → ℝ := fun y => f' y - (derivative P).eval y with hH'
  have hHd : ∀ y ∈ I, HasDerivWithinAt H (H' y) I y := fun y hy =>
    (hderiv y hy).sub (P.hasDerivAt y).hasDerivWithinAt
  have hHz : ∀ v ∈ s, H v = 0 := by
    intro v hv
    have hev : P.eval v = f v := by
      have := Lagrange.eval_interpolate_at_node (v := (id : ℝ → ℝ)) (s := s) (i := v) f
        (fun _ _ _ _ h => h) hv
      simpa [hP, interpPoly] using this
    simp [hH, hev]
  obtain ⟨S', hS'card, hS'I, hS'zero, hS'loc⟩ :=
    exists_rolle_nodesOn hI H H' hHd s m (by omega) hsI hHz
  have hS'x : ∀ w ∈ S', |w - x| < δ := by
    intro w hw
    obtain ⟨a, ha, b, hb, hab1, hab2⟩ := hS'loc w hw
    have h1 := hsx a ha
    have h2 := hsx b hb
    rw [abs_sub_lt_iff] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hPdeg : P.degree < ((m + 2 : ℕ) : WithBot ℕ) := by
    have hd := Lagrange.degree_interpolate_lt (v := (id : ℝ → ℝ)) (s := s) f (fun _ _ _ _ h => h)
    rw [hs] at hd
    exact_mod_cast hd
  have hPnd : P.natDegree ≤ m + 1 := by
    rw [Polynomial.natDegree_le_iff_degree_le]
    exact Order.le_of_lt_succ (by exact_mod_cast hPdeg)
  have hdPdeg : (derivative P).degree < (S'.card : WithBot ℕ) := by
    rw [hS'card]
    have h1 : (derivative P).natDegree ≤ m :=
      le_trans (Polynomial.natDegree_derivative_le P) (by omega)
    calc (derivative P).degree ≤ ((derivative P).natDegree : WithBot ℕ) := degree_le_natDegree
      _ ≤ (m : WithBot ℕ) := by exact_mod_cast h1
      _ < ((m+1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self m
  have heq : derivative P = interpPoly f' S' := by
    refine Lagrange.eq_interpolate_of_eval_eq f' (fun _ _ _ _ h => h) hdPdeg ?_
    intro w hw
    have hzero := hS'zero w hw
    rw [hH'] at hzero
    simp only [id]
    linarith [hzero]
  have hcoeff : ddiff f' S' = ((m:ℝ)+1) * ddiff f s := by
    rw [← coeff_top_interpPoly f' S' m hS'card, ← heq, Polynomial.coeff_derivative,
      coeff_top_interpPoly f s (m+1) hs]
    ring
  have hfin := hδ' S' hS'card hS'I hS'x
  rw [hcoeff] at hfin
  have hsplit : ddiff f s - M / ((m:ℝ)+1) = (((m:ℝ)+1) * ddiff f s - M) / ((m:ℝ)+1) := by
    field_simp
  rw [hsplit, abs_div, abs_of_pos (show (0:ℝ) < (m:ℝ)+1 by positivity),
    div_lt_iff₀ (by positivity)]
  linarith [hfin]

/-- **Lemma 5.1 on an arbitrary nondegenerate interval.**  For `f` differentiable within `I`,
relative `DIT(r)` for `f` at `x ∈ I` is equivalent to relative `DIT(r-1)` for the relative
derivative at `x` (here `r = m+1`). -/
theorem hasDITOn_deriv_iff (hI : I.OrdConnected) (hne : I.Nontrivial) (f f' : ℝ → ℝ)
    (hderiv : ∀ y ∈ I, HasDerivWithinAt f (f' y) I y) (x : ℝ) (m : ℕ) :
    HasDITOn I f (m+1) x ↔ HasDITOn I f' m x := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨((m:ℝ)+1) * L, ddLimOn_deriv_forward hI hne f f' hderiv x L m hL⟩
  · rintro ⟨M, hM⟩
    exact ⟨M / ((m:ℝ)+1), ddLimOn_deriv_backward hI f f' hderiv x M m hM⟩

/-- The relation `λ_{r-1}(f';x) = r λ_r(f;x)` between the relative top limits. -/
theorem ddLimValOn_deriv (hI : I.OrdConnected) (hne : I.Nontrivial) (f f' : ℝ → ℝ)
    (hderiv : ∀ y ∈ I, HasDerivWithinAt f (f' y) I y) (x : ℝ) (hx : x ∈ I) (m : ℕ)
    (hD : HasDITOn I f (m+1) x) :
    ddLimValOn I f' m x = ((m:ℝ)+1) * ddLimValOn I f (m+1) x := by
  obtain ⟨L, hL⟩ := hD
  rw [ddLimValOn_eq hI hne hx hL,
    ddLimValOn_eq hI hne hx (ddLimOn_deriv_forward hI hne f f' hderiv x L m hL)]

/-! ## Part (c) on an arbitrary interval -/

/-- **Part (c) on an arbitrary nondegenerate interval** (endpoints included): if `f` is `C^p` on
`I` (in the relative sense `ContDiffOn ℝ p f I`), then `f` has relative `DIT(p+k)` at `x ∈ I` if
and only if the relative `p`-th derivative has relative `DIT(k)` at `x`. -/
theorem part_c_hasDITOn (hI : I.OrdConnected) (hne : I.Nontrivial) (p : ℕ) :
    ∀ (f : ℝ → ℝ), ContDiffOn ℝ (p : ℕ) f I → ∀ x ∈ I, ∀ (k : ℕ),
      (HasDITOn I f (p + k) x ↔ HasDITOn I (intervalIteratedDeriv I p f) k x) := by
  have huniq : UniqueDiffOn ℝ I := uniqueDiffOn_of_ordConnected hI hne
  induction p with
  | zero => intro f _ x _ k; simp
  | succ p ih =>
    intro f hf x hx k
    have hdiff : DifferentiableOn ℝ f I :=
      hf.differentiableOn (by exact_mod_cast Nat.succ_ne_zero p)
    have hd : ∀ y ∈ I, HasDerivWithinAt f (derivWithin f I y) I y := fun y hy =>
      (hdiff y hy).hasDerivWithinAt
    have h1 : HasDITOn I f (p + 1 + k) x ↔ HasDITOn I (derivWithin f I) (p + k) x := by
      have h := hasDITOn_deriv_iff hI hne f (derivWithin f I) hd x (p + k)
      have e : p + 1 + k = (p + k) + 1 := by omega
      rw [e]; exact h
    have hcd : ContDiffOn ℝ (p : ℕ) (derivWithin f I) I := by
      refine hf.derivWithin huniq ?_
      norm_cast
    rw [h1, ih (derivWithin f I) hcd x hx k, intervalIteratedDeriv_succ']

/-- **Part (c) on an interval**, quantitative form (6.1). -/
theorem part_c_ddLimValOn (hI : I.OrdConnected) (hne : I.Nontrivial) (p : ℕ) :
    ∀ (f : ℝ → ℝ), ContDiffOn ℝ (p : ℕ) f I → ∀ x ∈ I, ∀ (k : ℕ), HasDITOn I f (p + k) x →
      (Nat.factorial k : ℝ) * ddLimValOn I (intervalIteratedDeriv I p f) k x
        = (Nat.factorial (p + k) : ℝ) * ddLimValOn I f (p + k) x := by
  have huniq : UniqueDiffOn ℝ I := uniqueDiffOn_of_ordConnected hI hne
  induction p with
  | zero => intro f _ x _ k _; simp
  | succ p ih =>
    intro f hf x hx k hD
    have hdiff : DifferentiableOn ℝ f I :=
      hf.differentiableOn (by exact_mod_cast Nat.succ_ne_zero p)
    have hd : ∀ y ∈ I, HasDerivWithinAt f (derivWithin f I y) I y := fun y hy =>
      (hdiff y hy).hasDerivWithinAt
    have e : p + 1 + k = (p + k) + 1 := by omega
    rw [e] at hD
    have hD' : HasDITOn I (derivWithin f I) (p + k) x :=
      (hasDITOn_deriv_iff hI hne f (derivWithin f I) hd x (p + k)).1 hD
    have h2 := ddLimValOn_deriv hI hne f (derivWithin f I) hd x hx (p + k) hD
    have hcd : ContDiffOn ℝ (p : ℕ) (derivWithin f I) I := by
      refine hf.derivWithin huniq ?_
      norm_cast
    have h3 := ih (derivWithin f I) hcd x hx k hD'
    rw [intervalIteratedDeriv_succ', e, h3, h2, Nat.factorial_succ]
    push_cast
    ring

/-- **Part (c) on an interval**, identity (6.2): `(f^{(p)})^{[k]}(x) = f^{[p+k]}(x)`, with all
derivatives and limits relative to `I`. -/
theorem part_c_ditTopOn (hI : I.OrdConnected) (hne : I.Nontrivial) (p k : ℕ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ (p : ℕ) f I) (x : ℝ) (hx : x ∈ I) (hD : HasDITOn I f (p + k) x) :
    ditTopOn I (intervalIteratedDeriv I p f) k x = ditTopOn I f (p + k) x :=
  part_c_ddLimValOn hI hne p f hf x hx k hD

end Q587
