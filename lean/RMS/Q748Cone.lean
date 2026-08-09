import RMS.Q748

/-!
# Q748 — metric cones over a link, and the cone lower bound

For a subset `Y` of the unit sphere of a real inner product space `E` (the *link*), we consider

* `Q748.puncturedConeOfLink Y = {r • y | r > 0, y ∈ Y}`,
* `Q748.coneOfLink Y = {0} ∪ puncturedConeOfLink Y`,

and the *capped angular distance* `Q748.cappedAngularDistance Y u v`, equal to `π` when the
intrinsic distance of the link is infinite and to `min π (intrinsicEDist Y u v).toReal` otherwise.

The main result of this file is the **cone lower bound**: any path inside the cone joining
`r • u` to `s • v` has length at least

`√(r² + s² − 2 r s cos (cappedAngularDistance Y u v))`,

both for the punctured cone (`Q748.intrinsicEDist_puncturedCone_ge`) and for the closed cone
(`Q748.intrinsicEDist_cone_ge`), together with the matching upper bound through the apex when the
capped angle equals `π` (`Q748.intrinsicEDist_cone_le_of_angle_pi`).
-/

open Set Metric
open scoped ENNReal NNReal

namespace Q748

/-! ## The two-parameter chord function of a Euclidean cone -/

/-- The Euclidean distance between two points of a plane at distances `r`, `s` from the origin and
making an angle `a`. -/
noncomputable def coneChord (r s a : ℝ) : ℝ := Real.sqrt (r ^ 2 + s ^ 2 - 2 * r * s * Real.cos a)

theorem coneChord_nonneg (r s a : ℝ) : 0 ≤ coneChord r s a := Real.sqrt_nonneg _

theorem coneChord_eq_norm (r s a : ℝ) :
    coneChord r s a = ‖(r : ℂ) - s * Complex.exp ((a : ℝ) * Complex.I)‖ := by
  have hre : (Complex.exp ((a : ℝ) * Complex.I)).re = Real.cos a := Complex.exp_ofReal_mul_I_re a
  have him : (Complex.exp ((a : ℝ) * Complex.I)).im = Real.sin a := Complex.exp_ofReal_mul_I_im a
  have hnormsq : Complex.normSq ((r : ℂ) - s * Complex.exp ((a : ℝ) * Complex.I)) =
      r ^ 2 + s ^ 2 - 2 * r * s * Real.cos a := by
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      hre, him]
    nlinarith [Real.sin_sq_add_cos_sq a]
  rw [coneChord, ← hnormsq, ← Complex.sq_norm]
  exact Real.sqrt_sq (norm_nonneg _)

theorem coneChord_triangle (r s t a b : ℝ) :
    coneChord r t (a + b) ≤ coneChord r s a + coneChord s t b := by
  have hsplit : Complex.exp (((a + b : ℝ)) * Complex.I)
      = Complex.exp ((a : ℝ) * Complex.I) * Complex.exp ((b : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  have h2 : ‖(s : ℂ) * Complex.exp ((a : ℝ) * Complex.I)
      - t * Complex.exp (((a + b : ℝ)) * Complex.I)‖ = coneChord s t b := by
    rw [hsplit, coneChord_eq_norm]
    rw [show (s : ℂ) * Complex.exp ((a : ℝ) * Complex.I)
        - t * (Complex.exp ((a : ℝ) * Complex.I) * Complex.exp ((b : ℝ) * Complex.I))
        = Complex.exp ((a : ℝ) * Complex.I) * ((s : ℂ) - t * Complex.exp ((b : ℝ) * Complex.I)) by
        ring, norm_mul, Complex.norm_exp]
    simp
  rw [coneChord_eq_norm r t (a + b),
    show ((r : ℂ) - t * Complex.exp (((a + b : ℝ)) * Complex.I))
      = ((r : ℂ) - s * Complex.exp ((a : ℝ) * Complex.I))
        + ((s : ℂ) * Complex.exp ((a : ℝ) * Complex.I)
            - t * Complex.exp (((a + b : ℝ)) * Complex.I)) by ring]
  refine le_trans (norm_add_le _ _) ?_
  rw [h2, coneChord_eq_norm r s a]

theorem coneChord_mono_angle {r s a b : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ Real.pi) : coneChord r s a ≤ coneChord r s b := by
  apply Real.sqrt_le_sqrt
  have hcos : Real.cos b ≤ Real.cos a :=
    Real.cos_le_cos_of_nonneg_of_le_pi ha hb hab
  nlinarith [mul_nonneg hr hs]

theorem coneChord_pi {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) : coneChord r s Real.pi = r + s := by
  rw [coneChord, Real.cos_pi]
  rw [show r ^ 2 + s ^ 2 - 2 * r * s * (-1) = (r + s) ^ 2 by ring]
  exact Real.sqrt_sq (by linarith)

theorem coneChord_zero (r s : ℝ) : coneChord r s 0 = |r - s| := by
  rw [coneChord, Real.cos_zero]
  rw [show r ^ 2 + s ^ 2 - 2 * r * s * 1 = (r - s) ^ 2 by ring]
  exact Real.sqrt_sq_eq_abs _

theorem abs_sub_le_coneChord {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (a : ℝ) :
    |r - s| ≤ coneChord r s a := by
  rw [coneChord, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.cos_le_one a, mul_nonneg hr hs]

theorem continuous_coneChord (r s : ℝ) : Continuous fun a => coneChord r s a := by
  unfold coneChord
  fun_prop

/-- The two-step inequality behind the polygonal comparison in a Euclidean cone. -/
theorem coneChord_step {r s t A a : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (ha : 0 ≤ a) (hapi : a ≤ Real.pi) :
    coneChord r t (min Real.pi (A + a)) ≤
      coneChord r s (min Real.pi A) + coneChord s t a := by
  rcases le_or_gt (A + a) Real.pi with hle | hgt
  · have hA' : min Real.pi A = A := min_eq_right (by linarith)
    have : min Real.pi (A + a) = A + a := min_eq_right hle
    rw [this, hA']
    exact coneChord_triangle r s t A a
  · rcases le_or_gt A Real.pi with hAle | hAgt
    · have hA' : min Real.pi A = A := min_eq_right hAle
      have htop : min Real.pi (A + a) = Real.pi := min_eq_left (by linarith)
      rw [htop, hA']
      set b := Real.pi - A with hb
      have hb0 : 0 ≤ b := by simp [hb]; linarith
      have hba : b ≤ a := by simp [hb]; linarith
      have h1 : coneChord s t b ≤ coneChord s t a :=
        coneChord_mono_angle hs ht hb0 hba hapi
      have h2 : coneChord r t (A + b) ≤ coneChord r s A + coneChord s t b :=
        coneChord_triangle r s t A b
      have h3 : A + b = Real.pi := by simp [hb]
      rw [h3] at h2
      linarith
    · have htop : min Real.pi (A + a) = Real.pi := min_eq_left (by linarith)
      have hA' : min Real.pi A = Real.pi := min_eq_left hAgt.le
      rw [htop, hA', coneChord_pi hr ht, coneChord_pi hr hs]
      have := abs_sub_le_coneChord hs ht a
      have h4 : s - t ≥ -(coneChord s t a) := by
        cases' abs_cases (s - t) with h h <;> linarith [this, h.1]
      linarith

/-- **Polygonal comparison in a Euclidean cone.** For radii `r i ≥ 0` and angles
`a i ∈ [0, π]`, the polygonal chord sum dominates the chord corresponding to the total angle,
capped at `π`. -/
theorem coneChord_polygon (r : ℕ → ℝ) (a : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i) (ha : ∀ i, 0 ≤ a i)
    (hapi : ∀ i, a i ≤ Real.pi) :
    ∀ N : ℕ, coneChord (r 0) (r N) (min Real.pi (∑ i ∈ Finset.range N, a i)) ≤
      ∑ i ∈ Finset.range N, coneChord (r i) (r (i + 1)) (a i) := by
  intro N
  induction N with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      rw [min_eq_right Real.pi_nonneg, coneChord_zero]
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      refine le_trans ?_ (add_le_add ih (le_refl (coneChord (r n) (r (n + 1)) (a n))))
      exact coneChord_step (hr 0) (hr n) (hr (n + 1)) (ha n) (hapi n)

/-! ## Cones over a link -/

section ConeSets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The punctured cone over a link `Y`: all positive multiples of points of `Y`. -/
def puncturedConeOfLink (Y : Set E) : Set E := {x | ∃ r : ℝ, 0 < r ∧ ∃ y ∈ Y, x = r • y}

/-- The closed cone over a link `Y`: the punctured cone together with its apex. -/
def coneOfLink (Y : Set E) : Set E := insert 0 (puncturedConeOfLink Y)

theorem smul_mem_puncturedConeOfLink {Y : Set E} {y : E} (hy : y ∈ Y) {r : ℝ} (hr : 0 < r) :
    r • y ∈ puncturedConeOfLink Y := ⟨r, hr, y, hy, rfl⟩

theorem puncturedConeOfLink_subset_coneOfLink (Y : Set E) :
    puncturedConeOfLink Y ⊆ coneOfLink Y := subset_insert _ _

/-- The **capped angular distance** of the link: the intrinsic distance of `Y`, truncated at `π`,
and equal to `π` when the link distance is infinite. -/
noncomputable def cappedAngularDistance (Y : Set E) (u v : E) : ℝ :=
  if intrinsicEDist Y u v = ⊤ then Real.pi else min Real.pi (intrinsicEDist Y u v).toReal

theorem cappedAngularDistance_nonneg (Y : Set E) (u v : E) :
    0 ≤ cappedAngularDistance Y u v := by
  unfold cappedAngularDistance
  split
  · exact Real.pi_nonneg
  · exact le_min Real.pi_nonneg ENNReal.toReal_nonneg

theorem cappedAngularDistance_le_pi (Y : Set E) (u v : E) :
    cappedAngularDistance Y u v ≤ Real.pi := by
  unfold cappedAngularDistance
  split
  · exact le_rfl
  · exact min_le_left _ _

theorem ofReal_cappedAngularDistance_le (Y : Set E) (u v : E) :
    ENNReal.ofReal (cappedAngularDistance Y u v) ≤ intrinsicEDist Y u v := by
  unfold cappedAngularDistance
  split
  · next h => rw [h]; exact le_top
  · next h =>
      refine le_trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)) ?_
      rw [ENNReal.ofReal_toReal h]

/-! ## Chords, norms and angles -/

theorem norm_sub_eq_coneChord (x y : E) :
    ‖x - y‖ = coneChord ‖x‖ ‖y‖ (InnerProductGeometry.angle x y) := by
  have h := InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
    x y
  rw [coneChord, ← Real.sqrt_sq (norm_nonneg (x - y))]
  congr 1
  nlinarith [h]

theorem norm_sub_le_angle_of_unit {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖ ≤ InnerProductGeometry.angle x y := by
  have h := norm_sub_eq_coneChord x y
  rw [hx, hy] at h
  rw [h, coneChord]
  have hb : (1 : ℝ) ^ 2 + 1 ^ 2 - 2 * 1 * 1 * Real.cos (InnerProductGeometry.angle x y) ≤
      (InnerProductGeometry.angle x y) ^ 2 := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := InnerProductGeometry.angle x y)]
  calc Real.sqrt ((1 : ℝ) ^ 2 + 1 ^ 2 - 2 * 1 * 1 * Real.cos (InnerProductGeometry.angle x y))
      ≤ Real.sqrt ((InnerProductGeometry.angle x y) ^ 2) := Real.sqrt_le_sqrt hb
    _ = InnerProductGeometry.angle x y :=
        Real.sqrt_sq (InnerProductGeometry.angle_nonneg _ _)

/-! ## The cone lower bound -/

/-- Every path inside the punctured cone over a link `Y` joining `r • u` to `s • v` is at least as
long as the corresponding Euclidean cone chord. -/
theorem le_eVariationOn_of_isPathIn_puncturedCone {Y : Set E} (hY : Y ⊆ Metric.sphere 0 1)
    {u v : E} (hu : u ∈ Y) (hv : v ∈ Y) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {γ : ℝ → E} (hγ : IsPathIn (puncturedConeOfLink Y) (r • u) (s • v) γ) :
    ENNReal.ofReal (coneChord r s (cappedAngularDistance Y u v)) ≤ eVariationOn γ (Icc 0 1) := by
  obtain ⟨hcont, hmaps, hγ0, hγ1⟩ := hγ
  set θ := cappedAngularDistance Y u v with hθdef
  have hθ0 : 0 ≤ θ := cappedAngularDistance_nonneg Y u v
  have hθpi : θ ≤ Real.pi := cappedAngularDistance_le_pi Y u v
  have hnormY : ∀ y ∈ Y, ‖y‖ = 1 := by
    intro y hy
    have := hY hy
    simpa [Metric.mem_sphere, dist_eq_norm] using this
  have hunorm : ‖u‖ = 1 := hnormY u hu
  have hvnorm : ‖v‖ = 1 := hnormY v hv
  -- the radial and angular parts of the path
  have hpos : ∀ t ∈ Icc (0:ℝ) 1, 0 < ‖γ t‖ ∧ (‖γ t‖)⁻¹ • γ t ∈ Y := by
    intro t ht
    obtain ⟨c, hc, y, hy, hxy⟩ := hmaps ht
    have hn : ‖γ t‖ = c := by rw [hxy, norm_smul, hnormY y hy, Real.norm_eq_abs, abs_of_pos hc,
      mul_one]
    refine ⟨by rw [hn]; exact hc, ?_⟩
    rw [hn, hxy, smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
    exact hy
  set g : ℝ → E := fun t => (‖γ t‖)⁻¹ • γ t with hgdef
  have hgY : ∀ t ∈ Icc (0:ℝ) 1, g t ∈ Y := fun t ht => (hpos t ht).2
  have hgnorm : ∀ t ∈ Icc (0:ℝ) 1, ‖g t‖ = 1 := fun t ht => hnormY _ (hgY t ht)
  have hg0 : g 0 = u := by
    have h1 : ‖γ 0‖ = r := by rw [hγ0, norm_smul, hunorm, Real.norm_eq_abs, abs_of_pos hr, mul_one]
    show (‖γ 0‖)⁻¹ • γ 0 = u
    rw [h1, hγ0, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul]
  have hg1 : g 1 = v := by
    have h1 : ‖γ 1‖ = s := by rw [hγ1, norm_smul, hvnorm, Real.norm_eq_abs, abs_of_pos hs, mul_one]
    show (‖γ 1‖)⁻¹ • γ 1 = v
    rw [h1, hγ1, smul_smul, inv_mul_cancel₀ (ne_of_gt hs), one_smul]
  have hgcont : ContinuousOn g (Icc 0 1) := by
    apply ContinuousOn.smul _ hcont
    exact ContinuousOn.inv₀ (hcont.norm) (fun t ht => ne_of_gt (hpos t ht).1)
  have hgpath : IsPathIn Y u v g := ⟨hgcont, fun t ht => hgY t ht, hg0, hg1⟩
  have hlink : ENNReal.ofReal θ ≤ eVariationOn g (Icc 0 1) :=
    le_trans (ofReal_cappedAngularDistance_le Y u v) (intrinsicEDist_le hgpath)
  -- radii at the endpoints
  have hr0 : ‖γ 0‖ = r := by rw [hγ0, norm_smul, hunorm, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  have hr1 : ‖γ 1‖ = s := by rw [hγ1, norm_smul, hvnorm, Real.norm_eq_abs, abs_of_pos hs, mul_one]
  rcases eq_or_ne (eVariationOn γ (Icc 0 1)) ⊤ with hTop | hTop
  · rw [hTop]; exact le_top
  have hLtoReal : ∀ c : ℝ, 0 ≤ c → c < θ →
      coneChord r s c ≤ (eVariationOn γ (Icc 0 1)).toReal := by
    intro c hc0 hcθ
    -- a partition of the link path with total chord length more than `c`
    have hlt : ENNReal.ofReal c < eVariationOn g (Icc 0 1) :=
      lt_of_lt_of_le (by
        exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc0 |>.2 hcθ) hlink
    rw [eVariationOn, lt_iSup_iff] at hlt
    obtain ⟨⟨n, ⟨w, hwmono, hwmem⟩⟩, hlt⟩ := hlt
    -- augment the partition with the endpoints `0` and `1`
    set w' : ℕ → ℝ := fun i => if i = 0 then 0 else if i ≤ n + 1 then w (i - 1) else 1 with hw'def
    have hwmem01 : ∀ i, w i ∈ Icc (0:ℝ) 1 := hwmem
    have hw'mem : ∀ i, w' i ∈ Icc (0:ℝ) 1 := by
      intro i
      rw [hw'def]
      by_cases h0 : i = 0
      · simp [h0]
      · by_cases h1 : i ≤ n + 1
        · simp only [h0, h1, if_false, if_true, if_neg h0]
          exact hwmem01 _
        · simp [h0, h1]
    have hw'mono : Monotone w' := by
      apply monotone_nat_of_le_succ
      intro i
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · have : w' 1 = w 0 := by simp [hw'def]
        rw [show w' 0 = 0 by simp [hw'def], this]
        exact (hwmem01 0).1
      · have hi0 : i ≠ 0 := by omega
        have hisucc : i + 1 ≠ 0 := Nat.succ_ne_zero i
        by_cases hle : i + 1 ≤ n + 1
        · have h1 : w' i = w (i - 1) := by
            simp [hw'def, hi0, show i ≤ n + 1 by omega]
          have h2 : w' (i + 1) = w (i + 1 - 1) := by
            simp [hw'def, hisucc, hle]
          rw [h1, h2]
          exact hwmono (by omega)
        · by_cases hle2 : i ≤ n + 1
          · have h1 : w' i = w (i - 1) := by simp [hw'def, hi0, hle2]
            have h2 : w' (i + 1) = 1 := by simp [hw'def, hisucc, hle]
            rw [h1, h2]
            exact (hwmem01 _).2
          · have h1 : w' i = 1 := by simp [hw'def, hi0, hle2]
            have h2 : w' (i + 1) = 1 := by simp [hw'def, hisucc, hle]
            rw [h1, h2]
    set N := n + 2 with hN
    have hw'0 : w' 0 = 0 := by simp [hw'def]
    have hw'N : w' N = 1 := by
      simp [hw'def, hN]
    set R : ℕ → ℝ := fun i => ‖γ (w' i)‖ with hRdef
    set A : ℕ → ℝ := fun i => InnerProductGeometry.angle (γ (w' i)) (γ (w' (i + 1))) with hAdef
    have hRnonneg : ∀ i, 0 ≤ R i := fun i => norm_nonneg _
    have hAnonneg : ∀ i, 0 ≤ A i := fun i => InnerProductGeometry.angle_nonneg _ _
    have hApi : ∀ i, A i ≤ Real.pi := fun i => InnerProductGeometry.angle_le_pi _ _
    -- the polygonal sum of the cone path
    have hsum_eq : ∀ i, coneChord (R i) (R (i + 1)) (A i) = ‖γ (w' i) - γ (w' (i + 1))‖ :=
      fun i => (norm_sub_eq_coneChord _ _).symm
    have hsum_le_var :
        ENNReal.ofReal (∑ i ∈ Finset.range N, ‖γ (w' i) - γ (w' (i + 1))‖) ≤
          eVariationOn γ (Icc 0 1) := by
      have h1 : ENNReal.ofReal (∑ i ∈ Finset.range N, ‖γ (w' i) - γ (w' (i + 1))‖) =
          ∑ i ∈ Finset.range N, edist (γ (w' (i + 1))) (γ (w' i)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [edist_dist, dist_eq_norm, ← norm_neg]
        congr 1
        abel
      rw [h1]
      exact eVariationOn.sum_le γ N hw'mono (fun i => hw'mem i)
    have hreal_le : ∑ i ∈ Finset.range N, ‖γ (w' i) - γ (w' (i + 1))‖ ≤
        (eVariationOn γ (Icc 0 1)).toReal := by
      rw [← ENNReal.ofReal_le_iff_le_toReal hTop]
      exact hsum_le_var
    -- the angular sum dominates `c`
    have hangle_ge : c ≤ ∑ i ∈ Finset.range N, A i := by
      have hchord_le_angle : ∀ i, ‖g (w' i) - g (w' (i + 1))‖ ≤ A i := by
        intro i
        have h1 : InnerProductGeometry.angle (g (w' i)) (g (w' (i + 1))) = A i := by
          rw [hAdef, hgdef]
          rw [InnerProductGeometry.angle_smul_left_of_pos _ _
              (inv_pos.2 (hpos _ (hw'mem i)).1),
            InnerProductGeometry.angle_smul_right_of_pos _ _
              (inv_pos.2 (hpos _ (hw'mem (i + 1))).1)]
        rw [← h1]
        exact norm_sub_le_angle_of_unit (hgnorm _ (hw'mem i)) (hgnorm _ (hw'mem (i + 1)))
      have hdrop : ∑ i ∈ Finset.range n, ‖g (w i) - g (w (i + 1))‖ ≤
          ∑ i ∈ Finset.range N, ‖g (w' i) - g (w' (i + 1))‖ := by
        have hshift : ∀ i < n, ‖g (w' (i + 1)) - g (w' (i + 1 + 1))‖ =
            ‖g (w i) - g (w (i + 1))‖ := by
          intro i hi
          have h1 : w' (i + 1) = w i := by
            simp [hw'def, show i + 1 ≤ n + 1 by omega]
          have h2 : w' (i + 1 + 1) = w (i + 1) := by
            simp [hw'def, show i + 1 + 1 ≤ n + 1 by omega]
          rw [h1, h2]
        calc ∑ i ∈ Finset.range n, ‖g (w i) - g (w (i + 1))‖
            = ∑ i ∈ Finset.range n, ‖g (w' (i + 1)) - g (w' (i + 1 + 1))‖ :=
              Finset.sum_congr rfl fun i hi => (hshift i (Finset.mem_range.1 hi)).symm
          _ ≤ ∑ i ∈ Finset.range (n + 1), ‖g (w' (i + 1)) - g (w' (i + 1 + 1))‖ := by
              rw [Finset.sum_range_succ]
              have := norm_nonneg (g (w' (n + 1)) - g (w' (n + 1 + 1)))
              linarith
          _ ≤ ∑ i ∈ Finset.range N, ‖g (w' i) - g (w' (i + 1))‖ := by
              rw [hN, Finset.sum_range_succ' (fun i => ‖g (w' i) - g (w' (i + 1))‖) (n + 1)]
              have := norm_nonneg (g (w' 0) - g (w' (0 + 1)))
              linarith
      have hcsum : c < ∑ i ∈ Finset.range n, ‖g (w i) - g (w (i + 1))‖ := by
        have h1 : ENNReal.ofReal (∑ i ∈ Finset.range n, ‖g (w i) - g (w (i + 1))‖) =
            ∑ i ∈ Finset.range n, edist (g (w (i + 1))) (g (w i)) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [edist_dist, dist_eq_norm, ← norm_neg]
          congr 1
          abel
        rw [← h1] at hlt
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc0).1 hlt
      calc c ≤ ∑ i ∈ Finset.range n, ‖g (w i) - g (w (i + 1))‖ := hcsum.le
        _ ≤ ∑ i ∈ Finset.range N, ‖g (w' i) - g (w' (i + 1))‖ := hdrop
        _ ≤ ∑ i ∈ Finset.range N, A i :=
            Finset.sum_le_sum fun i _ => hchord_le_angle i
    -- conclude by the polygonal comparison
    have hpoly := coneChord_polygon R A hRnonneg hAnonneg hApi N
    have hmin : c ≤ min Real.pi (∑ i ∈ Finset.range N, A i) :=
      le_min (le_of_lt (lt_of_lt_of_le hcθ hθpi)) hangle_ge
    have hmono : coneChord r s c ≤ coneChord (R 0) (R N)
        (min Real.pi (∑ i ∈ Finset.range N, A i)) := by
      have hR0 : R 0 = r := by rw [hRdef]; simp only [hw'0]; exact hr0
      have hRN : R N = s := by rw [hRdef]; simp only [hw'N]; exact hr1
      rw [hR0, hRN]
      exact coneChord_mono_angle hr.le hs.le hc0 hmin (min_le_left _ _)
    have hpoly' : coneChord (R 0) (R N) (min Real.pi (∑ i ∈ Finset.range N, A i)) ≤
        ∑ i ∈ Finset.range N, ‖γ (w' i) - γ (w' (i + 1))‖ := by
      refine le_trans hpoly (le_of_eq (Finset.sum_congr rfl fun i _ => hsum_eq i))
    linarith [hmono, hpoly', hreal_le]
  -- pass to the limit `c → θ`
  rcases eq_or_lt_of_le hθ0 with hθzero | hθpos
  · have hzero : coneChord r s θ = |r - s| := by rw [← hθzero, coneChord_zero]
    rw [hzero]
    calc ENNReal.ofReal |r - s| ≤ edist (r • u) (s • v) := by
          rw [edist_dist, dist_eq_norm]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : ‖r • u‖ = r := by
            rw [norm_smul, hunorm, Real.norm_eq_abs, abs_of_pos hr, mul_one]
          have h2 : ‖s • v‖ = s := by
            rw [norm_smul, hvnorm, Real.norm_eq_abs, abs_of_pos hs, mul_one]
          have := abs_norm_sub_norm_le (r • u) (s • v)
          rw [h1, h2] at this
          exact this
      _ = edist (γ 0) (γ 1) := by rw [hγ0, hγ1]
      _ ≤ eVariationOn γ (Icc 0 1) :=
          eVariationOn.edist_le γ (by norm_num) (by norm_num)
  · have hfinal : coneChord r s θ ≤ (eVariationOn γ (Icc 0 1)).toReal := by
      have hcont : ContinuousWithinAt (fun c => coneChord r s c) (Iio θ) θ :=
        (continuous_coneChord r s).continuousWithinAt
      refine le_of_tendsto hcont ?_
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hθpos)] with c hc hc0
      exact hLtoReal c (le_of_lt hc0) hc
    rw [← ENNReal.ofReal_le_iff_le_toReal hTop] at hfinal
    exact hfinal

/-- The **cone lower bound** for the intrinsic distance of a punctured cone. -/
theorem intrinsicEDist_puncturedCone_ge {Y : Set E} (hY : Y ⊆ Metric.sphere 0 1)
    {u v : E} (hu : u ∈ Y) (hv : v ∈ Y) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ENNReal.ofReal (coneChord r s (cappedAngularDistance Y u v)) ≤
      intrinsicEDist (puncturedConeOfLink Y) (r • u) (s • v) :=
  le_iInf₂ fun _ hγ => le_eVariationOn_of_isPathIn_puncturedCone hY hu hv hr hs hγ

/-- Every path inside the closed cone over a link `Y` joining `r • u` to `s • v` is at least as
long as the corresponding Euclidean cone chord: a path through the apex has length at least
`r + s`, which is the value of the chord at angle `π`. -/
theorem le_eVariationOn_of_isPathIn_cone {Y : Set E} (hY : Y ⊆ Metric.sphere 0 1)
    {u v : E} (hu : u ∈ Y) (hv : v ∈ Y) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {γ : ℝ → E} (hγ : IsPathIn (coneOfLink Y) (r • u) (s • v) γ) :
    ENNReal.ofReal (coneChord r s (cappedAngularDistance Y u v)) ≤ eVariationOn γ (Icc 0 1) := by
  obtain ⟨hcont, hmaps, hγ0, hγ1⟩ := hγ
  have hnormY : ∀ y ∈ Y, ‖y‖ = 1 := by
    intro y hy
    simpa [Metric.mem_sphere, dist_eq_norm] using hY hy
  have hru : ‖r • u‖ = r := by
    rw [norm_smul, hnormY u hu, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  have hsv : ‖s • v‖ = s := by
    rw [norm_smul, hnormY v hv, Real.norm_eq_abs, abs_of_pos hs, mul_one]
  by_cases hzero : ∃ t ∈ Icc (0:ℝ) 1, γ t = 0
  · obtain ⟨t₀, ht₀, hγt₀⟩ := hzero
    set w : ℕ → ℝ := fun i => if i = 0 then 0 else if i = 1 then t₀ else 1 with hwdef
    have hwmem : ∀ i, w i ∈ Icc (0:ℝ) 1 := by
      intro i
      rw [hwdef]
      by_cases h0 : i = 0
      · simp [h0]
      · by_cases h1 : i = 1
        · simpa [h0, h1] using ht₀
        · simp [h0, h1]
    have hwmono : Monotone w := by
      apply monotone_nat_of_le_succ
      intro i
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simpa [hwdef] using ht₀.1
      · by_cases h1 : i = 1
        · simp only [hwdef, h1]
          norm_num
          exact ht₀.2
        · have h0 : i ≠ 0 := by omega
          simp [hwdef, h0, h1, show i + 1 ≠ 0 by omega, show i + 1 ≠ 1 by omega]
    have hsum := eVariationOn.sum_le γ 2 hwmono hwmem
    have hval : ∑ i ∈ Finset.range 2, edist (γ (w (i + 1))) (γ (w i)) =
        ENNReal.ofReal r + ENNReal.ofReal s := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      have e0 : w 0 = 0 := by simp [hwdef]
      have e1 : w 1 = t₀ := by simp [hwdef]
      have e2 : w 2 = 1 := by simp [hwdef]
      rw [e0, e1, e2, hγ0, hγ1, hγt₀]
      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
      simp [hru, hsv]
    rw [hval] at hsum
    refine le_trans ?_ hsum
    rw [← ENNReal.ofReal_add hr.le hs.le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc coneChord r s (cappedAngularDistance Y u v)
        ≤ coneChord r s Real.pi :=
          coneChord_mono_angle hr.le hs.le (cappedAngularDistance_nonneg Y u v)
            (cappedAngularDistance_le_pi Y u v) le_rfl
      _ = r + s := coneChord_pi hr.le hs.le
  · push_neg at hzero
    refine le_eVariationOn_of_isPathIn_puncturedCone hY hu hv hr hs
      ⟨hcont, fun t ht => ?_, hγ0, hγ1⟩
    rcases hmaps ht with h | h
    · exact absurd h (hzero t ht)
    · exact h

/-- The **cone lower bound** for the intrinsic distance of a closed cone. -/
theorem intrinsicEDist_cone_ge {Y : Set E} (hY : Y ⊆ Metric.sphere 0 1)
    {u v : E} (hu : u ∈ Y) (hv : v ∈ Y) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ENNReal.ofReal (coneChord r s (cappedAngularDistance Y u v)) ≤
      intrinsicEDist (coneOfLink Y) (r • u) (s • v) :=
  le_iInf₂ fun _ hγ => le_eVariationOn_of_isPathIn_cone hY hu hv hr hs hγ

/-- In the closed cone one can always travel through the apex. -/
theorem intrinsicEDist_cone_le_add {Y : Set E} (hY : Y ⊆ Metric.sphere 0 1)
    {u v : E} (hu : u ∈ Y) (hv : v ∈ Y) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    intrinsicEDist (coneOfLink Y) (r • u) (s • v) ≤ ENNReal.ofReal (r + s) := by
  have hnormY : ∀ y ∈ Y, ‖y‖ = 1 := by
    intro y hy
    simpa [Metric.mem_sphere, dist_eq_norm] using hY hy
  have hstar : ∀ x ∈ coneOfLink Y, ∀ c : ℝ, 0 ≤ c → c ≤ 1 → c • x ∈ coneOfLink Y := by
    rintro x (rfl | ⟨t, ht, y, hy, rfl⟩) c hc0 _
    · simp [coneOfLink]
    · rcases eq_or_lt_of_le hc0 with rfl | hc
      · simp [coneOfLink]
      · exact Or.inr ⟨c * t, mul_pos hc ht, y, hy, by rw [smul_smul]⟩
  have h := intrinsicEDist_le_norm_add_norm hstar
    (Or.inr (smul_mem_puncturedConeOfLink hu hr)) (Or.inr (smul_mem_puncturedConeOfLink hv hs))
  rwa [norm_smul, norm_smul, hnormY u hu, hnormY v hv, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hr, abs_of_pos hs, mul_one, mul_one] at h

/-- When the link points are at capped angular distance `π`, the cone distance is exactly the
broken distance through the apex. -/
theorem intrinsicEDist_cone_eq_of_angle_pi {Y : Set E} (hY : Y ⊆ Metric.sphere 0 1)
    {u v : E} (hu : u ∈ Y) (hv : v ∈ Y) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hpi : cappedAngularDistance Y u v = Real.pi) :
    intrinsicEDist (coneOfLink Y) (r • u) (s • v) =
      ENNReal.ofReal (coneChord r s (cappedAngularDistance Y u v)) := by
  refine le_antisymm ?_ (intrinsicEDist_cone_ge hY hu hv hr hs)
  rw [hpi, coneChord_pi hr.le hs.le]
  exact intrinsicEDist_cone_le_add hY hu hv hr hs

end ConeSets

/-! ## The loci of `Mₙ(ℝ)` as cones over their unit links -/

section MatrixCones

variable {n : ℕ}

/-- The unit link of the positive-determinant locus. -/
def posDetLink (n : ℕ) : Set (MatSpace n) := posDetLocus n ∩ Metric.sphere 0 1

/-- The unit link of the singular locus. -/
def singularLink (n : ℕ) : Set (MatSpace n) := singularLocus n ∩ Metric.sphere 0 1

theorem singularLink_subset_sphere (n : ℕ) : singularLink n ⊆ Metric.sphere 0 1 :=
  fun _ hx => hx.2

theorem posDetLink_subset_sphere (n : ℕ) : posDetLink n ⊆ Metric.sphere 0 1 :=
  fun _ hx => hx.2

theorem norm_smul_mem_singularLink {x : MatSpace n} (hx : x ∈ singularLocus n) (hx0 : x ≠ 0) :
    (‖x‖)⁻¹ • x ∈ singularLink n := by
  have hnorm : 0 < ‖x‖ := norm_pos_iff.2 hx0
  refine ⟨smul_mem_singularLocus hx _, ?_⟩
  simp [Metric.mem_sphere, dist_eq_norm, norm_smul, abs_of_pos (inv_pos.2 hnorm),
    inv_mul_cancel₀ (ne_of_gt hnorm)]

theorem norm_smul_mem_posDetLink {x : MatSpace n} (hx : x ∈ posDetLocus n) (hx0 : x ≠ 0) :
    (‖x‖)⁻¹ • x ∈ posDetLink n := by
  have hnorm : 0 < ‖x‖ := norm_pos_iff.2 hx0
  refine ⟨?_, ?_⟩
  · show 0 < (toMat ((‖x‖)⁻¹ • x)).det
    rw [toMat_smul, Matrix.det_smul]
    exact mul_pos (pow_pos (inv_pos.2 hnorm) _) hx
  · simp [Metric.mem_sphere, dist_eq_norm, norm_smul, abs_of_pos (inv_pos.2 hnorm),
      inv_mul_cancel₀ (ne_of_gt hnorm)]

theorem zero_mem_singularLocus (hn : 0 < n) : (0 : MatSpace n) ∈ singularLocus n := by
  show (toMat (0 : MatSpace n)).det = 0
  have h0 : toMat (0 : MatSpace n) = 0 := rfl
  rw [h0, Matrix.det_zero]
  exact ⟨⟨0, hn⟩⟩

/-- The singular locus is the closed cone over its unit link. -/
theorem singularLocus_eq_coneOfLink (hn : 0 < n) :
    singularLocus n = coneOfLink (singularLink n) := by
  ext x
  constructor
  · intro hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Or.inl rfl
    · refine Or.inr ⟨‖x‖, norm_pos_iff.2 hx0, (‖x‖)⁻¹ • x, norm_smul_mem_singularLink hx hx0, ?_⟩
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (norm_pos_iff.2 hx0)), one_smul]
  · rintro (rfl | ⟨r, hr, y, hy, rfl⟩)
    · exact zero_mem_singularLocus hn
    · exact smul_mem_singularLocus hy.1 r

/-- The positive-determinant locus is the punctured cone over its unit link. -/
theorem posDetLocus_eq_puncturedConeOfLink (hn : 0 < n) :
    posDetLocus n = puncturedConeOfLink (posDetLink n) := by
  ext x
  constructor
  · intro hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      have : (0 : Matrix (Fin n) (Fin n) ℝ).det = 0 := by
        rw [Matrix.det_zero]; exact ⟨⟨0, hn⟩⟩
      have hx' : (0:ℝ) < (toMat (0 : MatSpace n)).det := hx
      rw [show toMat (0 : MatSpace n) = 0 from rfl, this] at hx'
      exact lt_irrefl _ hx'
    refine ⟨‖x‖, norm_pos_iff.2 hx0, (‖x‖)⁻¹ • x, norm_smul_mem_posDetLink hx hx0, ?_⟩
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (norm_pos_iff.2 hx0)), one_smul]
  · rintro ⟨r, hr, y, hy, rfl⟩
    show 0 < (toMat (r • y)).det
    rw [toMat_smul, Matrix.det_smul]
    exact mul_pos (pow_pos hr _) hy.1

set_option maxHeartbeats 1000000 in
/-- **Theorem 1, lower half, for `Σₙ`.** The intrinsic distance in the singular locus is at least
the Euclidean cone chord built from the capped angular distance of the unit link. -/
theorem intrinsicEDist_singularLocus_cone_lower (hn : 0 < n) {x y : MatSpace n}
    (hx : x ∈ singularLocus n) (hy : y ∈ singularLocus n) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    ENNReal.ofReal (coneChord ‖x‖ ‖y‖
        (cappedAngularDistance (singularLink n) ((‖x‖)⁻¹ • x) ((‖y‖)⁻¹ • y))) ≤
      intrinsicEDist (singularLocus n) x y := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hxe : x = ‖x‖ • ((‖x‖)⁻¹ • x) := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hxn), one_smul]
  have hye : y = ‖y‖ • ((‖y‖)⁻¹ • y) := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hyn), one_smul]
  have h := intrinsicEDist_cone_ge (singularLink_subset_sphere n)
    (norm_smul_mem_singularLink hx hx0) (norm_smul_mem_singularLink hy hy0) hxn hyn
  rw [← hxe, ← hye, ← singularLocus_eq_coneOfLink hn] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- **Theorem 1, lower half, for `GLₙ⁺`.** -/
theorem intrinsicEDist_posDetLocus_cone_lower (hn : 0 < n) {x y : MatSpace n}
    (hx : x ∈ posDetLocus n) (hy : y ∈ posDetLocus n) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    ENNReal.ofReal (coneChord ‖x‖ ‖y‖
        (cappedAngularDistance (posDetLink n) ((‖x‖)⁻¹ • x) ((‖y‖)⁻¹ • y))) ≤
      intrinsicEDist (posDetLocus n) x y := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hxe : x = ‖x‖ • ((‖x‖)⁻¹ • x) := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hxn), one_smul]
  have hye : y = ‖y‖ • ((‖y‖)⁻¹ • y) := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hyn), one_smul]
  have h := intrinsicEDist_puncturedCone_ge (posDetLink_subset_sphere n)
    (norm_smul_mem_posDetLink hx hx0) (norm_smul_mem_posDetLink hy hy0) hxn hyn
  rw [← hxe, ← hye, ← posDetLocus_eq_puncturedConeOfLink hn] at h
  exact h

end MatrixCones

end Q748
