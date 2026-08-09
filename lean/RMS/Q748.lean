import Mathlib

/-!
# Q748 — Geodesic (intrinsic) distance inside the singular locus of `Mₙ(ℝ)`

This file formalizes the part of the Q748 answer that the audit selects: the **chord criterion in
the singular locus** together with its **determinant-pencil equivalence** (Theorem 4 of the
answer), plus the general lower bound `‖A - B‖_F ≤ d(A,B)` and the quantitative obstacle bound
behind the strictness statement (Lemma 5 / Corollary 7 of the answer).

## Setting

The ambient space is `Mₙ(ℝ) ≅ ℝ^{n²}` with the Frobenius inner product
`⟪X, Y⟫ = tr(Xᵀ Y)`; it is modelled here as `EuclideanSpace ℝ (Fin n × Fin n)`, and
`Q748.norm_ofMat_eq_sqrt_trace` records that its norm is indeed the Frobenius norm
`‖X‖ = √(tr (Xᵀ X))`.

For a subset `S` of a Euclidean space, `Q748.intrinsicEDist S A B` is the infimum of the lengths
of continuous paths inside `S` joining `A` to `B`, the length of a path being its total variation
`eVariationOn`. The infimum is taken in `ℝ≥0∞`, so it is `⊤` when there is no such path.

## Statement mismatch with the printed answer

The printed answer measures lengths of *piecewise `C¹`* curves via `∫₀¹ ‖γ'(t)‖ dt`. Here lengths
are measured as total variations of *continuous* curves, which is the standard rectifiable-length
notion; the two notions agree for piecewise `C¹` curves, and the infimum over continuous curves is
a priori no larger. The results proved below are stated for this (a priori smaller) infimum: the
lower bounds proved here are therefore at least as strong as those claimed, and the upper bound
used in the equality case comes from a straight segment, which is smooth. So no strength is lost.

## Main results

* `Q748.edist_le_intrinsicEDist` : `‖A - B‖_F ≤ d_S(A, B)` for every set `S`.
* `Q748.intrinsicEDist_singularLocus_bounds` : bound `(4)` of the answer inside `Σₙ`, namely
  `‖A - B‖_F ≤ d_{Σₙ}(A, B) ≤ ‖A‖_F + ‖B‖_F`.
* `Q748.obstacle_bound`, `Q748.edist_lt_intrinsicEDist_of_obstacle` : the quantitative obstacle
  bound and the resulting strict inequality.
* `Q748.pencil_singular_tfae` : the determinant-pencil criterion.
* `Q748.intrinsicEDist_singularLocus_eq_edist_iff` : **Theorem 4**, the chord criterion in the
  singular locus.
* `Q748.intrinsicEDist_posDetLocus_eq_edist`, `Q748.edist_lt_intrinsicEDist_posDetLocus` : the two
  directions of Theorem 3 (in `GLₙ⁺`) that do not need the local bypass construction.
* `Q748.dist_skew_pencil_example`, `Q748.dist_E11_E22_gt`, `Q748.dist_GL2_example` : the worked
  examples of the answer.

## Scope

Following the audit, the target is the chord criterion in the singular locus and its
determinant-polynomial equivalence. The metric-cone formula (Theorem 1), the exact `Σ₂` distance
via the Clifford torus (Theorem 9) and the variational description of `GL₂⁺` (Theorem 10) are not
formalized here, nor is the local bypass construction (Lemma 8) needed for the remaining direction
of Theorem 3.

Lean version: 4.28.0.  Mathlib commit: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
-/

open Set Metric Matrix Polynomial
open scoped ENNReal NNReal

namespace Q748

/-! ## 1. Intrinsic (length) distance -/

section Intrinsic

variable {E : Type*} [NormedAddCommGroup E]

/-- `γ` is a continuous path inside `S`, parameterised by `[0,1]`, running from `A` to `B`. -/
def IsPathIn (S : Set E) (A B : E) (γ : ℝ → E) : Prop :=
  ContinuousOn γ (Icc 0 1) ∧ MapsTo γ (Icc 0 1) S ∧ γ 0 = A ∧ γ 1 = B

/-- The intrinsic (length) distance of a subset `S` of a normed space: the infimum of the lengths
(total variations) of continuous paths inside `S` joining `A` to `B`. It equals `⊤` when no such
path exists. -/
noncomputable def intrinsicEDist (S : Set E) (A B : E) : ℝ≥0∞ :=
  ⨅ γ ∈ {γ : ℝ → E | IsPathIn S A B γ}, eVariationOn γ (Icc 0 1)

theorem intrinsicEDist_le {S : Set E} {A B : E} {γ : ℝ → E} (hγ : IsPathIn S A B γ) :
    intrinsicEDist S A B ≤ eVariationOn γ (Icc 0 1) :=
  iInf₂_le γ hγ

/-- Any path is at least as long as its chord: the intrinsic distance dominates the ambient
(Frobenius) distance. This is the lower bound in `(4)` of the answer. -/
theorem edist_le_intrinsicEDist (S : Set E) (A B : E) : edist A B ≤ intrinsicEDist S A B := by
  refine le_iInf₂ fun γ hγ => ?_
  obtain ⟨-, -, h0, h1⟩ := hγ
  calc edist A B = edist (γ 0) (γ 1) := by rw [h0, h1]
    _ ≤ eVariationOn γ (Icc 0 1) := eVariationOn.edist_le γ (by norm_num) (by norm_num)

variable [NormedSpace ℝ E]

/-- If the straight segment from `A` to `B` stays inside `S`, then the intrinsic distance is the
ambient chord. -/
theorem intrinsicEDist_eq_edist_of_segment_subset {S : Set E} {A B : E}
    (h : segment ℝ A B ⊆ S) : intrinsicEDist S A B = edist A B := by
  refine le_antisymm ?_ (edist_le_intrinsicEDist S A B)
  set γ : ℝ → E := fun t => A + t • (B - A) with hγdef
  have hlip : LipschitzWith ‖B - A‖₊ γ := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [hγdef, dist_eq_norm]
    rw [show A + s • (B - A) - (A + t • (B - A)) = (s - t) • (B - A) by module, norm_smul]
    simp [Real.norm_eq_abs, mul_comm]
  have hpath : IsPathIn S A B γ := by
    refine ⟨hlip.continuous.continuousOn, ?_, by simp [hγdef], by simp [hγdef]⟩
    intro t ht
    exact h (by rw [segment_eq_image' ℝ A B]; exact ⟨t, ht, rfl⟩)
  refine le_trans (intrinsicEDist_le hpath) ?_
  have h1 : eVariationOn γ (Icc (0:ℝ) 1) ≤ ‖B - A‖₊ * eVariationOn (id : ℝ → ℝ) (Icc (0:ℝ) 1) := by
    have := (hlip.lipschitzOnWith (s := (univ : Set ℝ))).comp_eVariationOn_le
      (g := (id : ℝ → ℝ)) (s := Icc (0:ℝ) 1) fun x _ => mem_univ _
    simpa [Function.comp] using this
  have h2 : eVariationOn (id : ℝ → ℝ) (Icc (0:ℝ) 1) ≤ 1 := by
    have := (monotone_id.monotoneOn (univ : Set ℝ)).eVariationOn_le (a := (0:ℝ)) (b := 1)
      (mem_univ _) (mem_univ _)
    simpa using this
  calc eVariationOn γ (Icc (0:ℝ) 1) ≤ (‖B - A‖₊ : ℝ≥0∞) * 1 := le_trans h1 (by gcongr)
    _ = edist A B := by
        rw [mul_one, edist_eq_enorm_sub, ← enorm_neg (A - B)]
        simp [enorm_eq_nnnorm]

omit [NormedSpace ℝ E] in
/-- The length of a `K`-Lipschitz curve on `[a,b]` is at most `K (b - a)`. -/
theorem eVariationOn_le_of_lipschitz {f : ℝ → E} {K : ℝ≥0} (hf : LipschitzWith K f) {a b : ℝ} :
    eVariationOn f (Icc a b) ≤ K * ENNReal.ofReal (b - a) := by
  have h1 : eVariationOn f (Icc a b) ≤ K * eVariationOn (id : ℝ → ℝ) (Icc a b) := by
    have := (hf.lipschitzOnWith (s := (univ : Set ℝ))).comp_eVariationOn_le
      (g := (id : ℝ → ℝ)) (s := Icc a b) fun x _ => mem_univ _
    simpa [Function.comp] using this
  have h2 : eVariationOn (id : ℝ → ℝ) (Icc a b) ≤ ENNReal.ofReal (b - a) := by
    have := (monotone_id.monotoneOn (univ : Set ℝ)).eVariationOn_le (a := a) (b := b)
      (mem_univ _) (mem_univ _)
    simpa using this
  exact le_trans h1 (by gcongr)

/-- **Upper bound through the apex** (the upper bound in `(4)` of the answer). If `S` is
star-shaped about the origin, the broken path `A → 0 → B` gives `d_S(A,B) ≤ ‖A‖ + ‖B‖`. -/
theorem intrinsicEDist_le_norm_add_norm {S : Set E} {A B : E}
    (hstar : ∀ x ∈ S, ∀ c : ℝ, 0 ≤ c → c ≤ 1 → c • x ∈ S) (hA : A ∈ S) (hB : B ∈ S) :
    intrinsicEDist S A B ≤ ENNReal.ofReal (‖A‖ + ‖B‖) := by
  set γ : ℝ → E := fun t => (max (1 - 2 * t) 0) • A + (max (2 * t - 1) 0) • B with hγ
  have hcont : Continuous γ := by
    apply Continuous.add <;> apply Continuous.smul (by fun_prop) continuous_const
  have hval1 : ∀ t ≤ (1:ℝ)/2, γ t = (1 - 2 * t) • A := by
    intro t ht
    have h1 : max (1 - 2 * t) 0 = 1 - 2 * t := max_eq_left (by linarith)
    have h2 : max (2 * t - 1) 0 = 0 := max_eq_right (by linarith)
    simp [hγ, h1, h2]
  have hval2 : ∀ t, (1:ℝ)/2 ≤ t → γ t = (2 * t - 1) • B := by
    intro t ht
    have h1 : max (1 - 2 * t) 0 = 0 := max_eq_right (by linarith)
    have h2 : max (2 * t - 1) 0 = 2 * t - 1 := max_eq_left (by linarith)
    simp [hγ, h1, h2]
  have hpath : IsPathIn S A B γ := by
    refine ⟨hcont.continuousOn, ?_, by rw [hval1 0 (by norm_num)]; simp, by
      rw [hval2 1 (by norm_num)]; norm_num⟩
    intro t ht
    rcases le_or_gt t (1/2) with h | h
    · rw [hval1 t h]
      exact hstar A hA _ (by linarith [ht.1]) (by linarith [ht.1])
    · rw [hval2 t h.le]
      exact hstar B hB _ (by linarith) (by linarith [ht.2])
  refine le_trans (intrinsicEDist_le hpath) ?_
  have hsplit : eVariationOn γ (Icc 0 1 ∩ Icc 0 (1/2)) + eVariationOn γ (Icc 0 1 ∩ Icc (1/2) 1)
      = eVariationOn γ (Icc (0:ℝ) 1 ∩ Icc 0 1) :=
    eVariationOn.Icc_add_Icc γ (by norm_num) (by norm_num) (by norm_num)
  have hset1 : Icc (0:ℝ) 1 ∩ Icc 0 (1/2) = Icc (0:ℝ) (1/2) := by
    rw [Set.Icc_inter_Icc]; norm_num
  have hset2 : Icc (0:ℝ) 1 ∩ Icc (1/2) 1 = Icc (1/2 : ℝ) 1 := by
    rw [Set.Icc_inter_Icc]; norm_num
  rw [Set.inter_self, hset1, hset2] at hsplit
  rw [← hsplit, ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  gcongr ?_ + ?_
  · have heq : eVariationOn γ (Icc (0:ℝ) (1/2))
        = eVariationOn (fun t => (1 - 2 * t) • A) (Icc (0:ℝ) (1/2)) :=
      eVariationOn.eq_of_eqOn (fun t ht => hval1 t ht.2)
    have hlip : LipschitzWith (2 * ‖A‖₊) (fun t : ℝ => (1 - 2 * t) • A) := by
      apply LipschitzWith.of_dist_le_mul
      intro s t
      rw [dist_eq_norm, show (1 - 2 * s) • A - (1 - 2 * t) • A = (2 * (t - s)) • A by module,
        norm_smul, Real.dist_eq, Real.norm_eq_abs, abs_mul, abs_sub_comm]
      push_cast
      simp
      exact le_of_eq (by ring)
    rw [heq]
    refine le_trans (eVariationOn_le_of_lipschitz hlip) ?_
    rw [show ((2 * ‖A‖₊ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (2 * ‖A‖) by
      rw [ENNReal.ofReal_mul (by norm_num)]; simp [ENNReal.ofReal_ofNat, enorm_eq_nnnorm],
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · have heq : eVariationOn γ (Icc (1/2 : ℝ) 1)
        = eVariationOn (fun t => (2 * t - 1) • B) (Icc (1/2 : ℝ) 1) :=
      eVariationOn.eq_of_eqOn (fun t ht => hval2 t ht.1)
    have hlip : LipschitzWith (2 * ‖B‖₊) (fun t : ℝ => (2 * t - 1) • B) := by
      apply LipschitzWith.of_dist_le_mul
      intro s t
      rw [dist_eq_norm, show (2 * s - 1) • B - (2 * t - 1) • B = (2 * (s - t)) • B by module,
        norm_smul, Real.dist_eq, Real.norm_eq_abs, abs_mul]
      push_cast
      simp
      exact le_of_eq (by ring)
    rw [heq]
    refine le_trans (eVariationOn_le_of_lipschitz hlip) ?_
    rw [show ((2 * ‖B‖₊ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (2 * ‖B‖) by
      rw [ENNReal.ofReal_mul (by norm_num)]; simp [ENNReal.ofReal_ofNat, enorm_eq_nnnorm],
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- Sanity check: in the whole space the intrinsic distance is the ambient distance. -/
theorem intrinsicEDist_univ (A B : E) : intrinsicEDist (univ : Set E) A B = edist A B :=
  intrinsicEDist_eq_edist_of_segment_subset (subset_univ _)

end Intrinsic

section Obstacle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Obstacle lemma** (Lemma 5 of the answer). If the open ball of radius `ρ` centred at the point
`(1-t)A + tB` of the segment avoids `S`, then every path in `S` from `A` to `B` has length at
least `√(t²D² + ρ²) + √((1-t)²D² + ρ²)`, where `D = ‖A - B‖`. -/
theorem obstacle_bound {S : Set E} {A B : E} {t ρ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hρ : 0 ≤ ρ)
    (hball : ∀ x ∈ S, ρ ≤ dist x ((1 - t) • A + t • B)) :
    ENNReal.ofReal (Real.sqrt (t ^ 2 * ‖B - A‖ ^ 2 + ρ ^ 2)
        + Real.sqrt ((1 - t) ^ 2 * ‖B - A‖ ^ 2 + ρ ^ 2)) ≤ intrinsicEDist S A B := by
  refine le_iInf₂ fun γ hγ => ?_
  obtain ⟨hcont, hmaps, h0, h1⟩ := hγ
  set D := ‖B - A‖ with hD
  set f : ℝ → ℝ := fun s => inner ℝ (γ s - A) (B - A) with hf
  have hfcont : ContinuousOn f (Icc 0 1) :=
    ContinuousOn.inner (hcont.sub continuousOn_const) continuousOn_const
  have hf0 : f 0 = 0 := by simp [hf, h0]
  have hf1 : f 1 = D ^ 2 := by simp [hf, h1, hD]
  have hmem : t * D ^ 2 ∈ Icc (f 0) (f 1) := by
    rw [hf0, hf1]
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg D]
  obtain ⟨s, hs, hps⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hfcont hmem
  set p := γ s with hp
  have hps' : inner ℝ (p - A) (B - A) = t * D ^ 2 := hps
  set v := p - ((1 - t) • A + t • B) with hv
  have hvρ : ρ ≤ ‖v‖ := by
    have := hball p (hmaps hs)
    rwa [dist_eq_norm] at this
  have hvo : inner ℝ v (B - A) = 0 := by
    have hrw : v = (p - A) - t • (B - A) := by rw [hv]; module
    rw [hrw, inner_sub_left, real_inner_smul_left, hps', real_inner_self_eq_norm_sq, ← hD]
    ring
  have hpA : ‖p - A‖ ^ 2 = ‖v‖ ^ 2 + t ^ 2 * D ^ 2 := by
    have hpa : p - A = v + t • (B - A) := by rw [hv]; module
    rw [hpa, norm_add_sq_real, real_inner_smul_right, hvo, norm_smul]
    simp [Real.norm_eq_abs, mul_pow, sq_abs, hD]
  have hBp : ‖B - p‖ ^ 2 = ‖v‖ ^ 2 + (1 - t) ^ 2 * D ^ 2 := by
    have hbp : B - p = (1 - t) • (B - A) - v := by rw [hv]; module
    rw [hbp, norm_sub_sq_real, real_inner_smul_left, real_inner_comm, hvo, norm_smul]
    simp [Real.norm_eq_abs, mul_pow, sq_abs, hD]
    ring
  have e1 : Real.sqrt (t ^ 2 * D ^ 2 + ρ ^ 2) ≤ ‖p - A‖ := by
    rw [show ‖p - A‖ = Real.sqrt (‖p - A‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [norm_nonneg v])
  have e2 : Real.sqrt ((1 - t) ^ 2 * D ^ 2 + ρ ^ 2) ≤ ‖B - p‖ := by
    rw [show ‖B - p‖ = Real.sqrt (‖B - p‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [norm_nonneg v])
  have h0mem : (0:ℝ) ∈ Icc (0:ℝ) 1 ∩ Icc (0:ℝ) s := ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, hs.1⟩⟩
  have hsmem1 : s ∈ Icc (0:ℝ) 1 ∩ Icc (0:ℝ) s := ⟨hs, ⟨hs.1, le_rfl⟩⟩
  have hsmem2 : s ∈ Icc (0:ℝ) 1 ∩ Icc s 1 := ⟨hs, ⟨le_rfl, hs.2⟩⟩
  have h1mem : (1:ℝ) ∈ Icc (0:ℝ) 1 ∩ Icc s 1 := ⟨⟨zero_le_one, le_rfl⟩, ⟨hs.2, le_rfl⟩⟩
  have hsplit : eVariationOn γ (Icc 0 1 ∩ Icc 0 s) + eVariationOn γ (Icc 0 1 ∩ Icc s 1)
      = eVariationOn γ (Icc (0:ℝ) 1 ∩ Icc 0 1) :=
    eVariationOn.Icc_add_Icc γ hs.1 hs.2 hs
  have hleft : edist A p ≤ eVariationOn γ (Icc (0:ℝ) 1 ∩ Icc 0 s) := by
    have := eVariationOn.edist_le γ h0mem hsmem1
    rwa [h0] at this
  have hright : edist p B ≤ eVariationOn γ (Icc (0:ℝ) 1 ∩ Icc s 1) := by
    have := eVariationOn.edist_le γ hsmem2 h1mem
    rwa [h1] at this
  have hsum : edist A p + edist p B ≤ eVariationOn γ (Icc (0:ℝ) 1) := by
    rw [← Set.inter_self (Icc (0:ℝ) 1), ← hsplit]
    exact add_le_add hleft hright
  refine le_trans ?_ hsum
  rw [edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
  apply ENNReal.ofReal_le_ofReal
  rw [dist_eq_norm, dist_eq_norm, norm_sub_rev A p, norm_sub_rev p B]
  linarith

private theorem lt_sqrt_add_sqrt {t ρ D : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hρ : 0 < ρ)
    (hD : 0 ≤ D) :
    D < Real.sqrt (t ^ 2 * D ^ 2 + ρ ^ 2) + Real.sqrt ((1 - t) ^ 2 * D ^ 2 + ρ ^ 2) := by
  have h1 : t * D < Real.sqrt (t ^ 2 * D ^ 2 + ρ ^ 2) := by
    rw [show t * D = |t * D| from (abs_of_nonneg (by positivity)).symm, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
  have h2 : (1 - t) * D ≤ Real.sqrt ((1 - t) ^ 2 * D ^ 2 + ρ ^ 2) := by
    rw [show (1 - t) * D = |(1 - t) * D| from (abs_of_nonneg (by nlinarith)).symm,
      ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith)
  nlinarith

/-- **Quantitative strictness** (Corollary 7 of the answer). An obstacle sitting on the segment
forces the intrinsic distance to exceed the chord. -/
theorem edist_lt_intrinsicEDist_of_obstacle {S : Set E} {A B : E} {t ρ : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hρ : 0 < ρ) (hball : ∀ x ∈ S, ρ ≤ dist x ((1 - t) • A + t • B)) :
    edist A B < intrinsicEDist S A B := by
  refine lt_of_lt_of_le ?_ (obstacle_bound ht0 ht1 hρ.le hball)
  rw [edist_dist, dist_eq_norm, ← norm_neg (A - B), neg_sub]
  refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).2 ?_
  exact lt_sqrt_add_sqrt ht0 ht1 hρ (norm_nonneg _)

end Obstacle

/-! ## 2. `Mₙ(ℝ)` with its Frobenius Euclidean structure -/

/-- `Mₙ(ℝ)` viewed as a Euclidean space via the Frobenius inner product. -/
abbrev MatSpace (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin n)

/-- The matrix underlying a point of `MatSpace n`. -/
def toMat {n : ℕ} (x : MatSpace n) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => x.ofLp (i, j)

/-- The point of `MatSpace n` underlying a matrix. -/
def ofMat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : MatSpace n := WithLp.toLp 2 fun p => M p.1 p.2

@[simp] theorem toMat_ofMat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : toMat (ofMat M) = M := rfl

theorem ofMat_add {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ) :
    ofMat (M + N) = ofMat M + ofMat N := by
  simp [ofMat, ← WithLp.toLp_add]
  rfl

theorem ofMat_smul {n : ℕ} (c : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    ofMat (c • M) = c • ofMat M := by
  simp [ofMat, ← WithLp.toLp_smul]
  rfl

theorem ofMat_sub {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ) :
    ofMat (M - N) = ofMat M - ofMat N := by
  simp [ofMat, ← WithLp.toLp_sub]
  rfl

@[simp] theorem ofMat_toMat {n : ℕ} (x : MatSpace n) : ofMat (toMat x) = x := rfl

/-- The norm of `MatSpace n` is the Frobenius norm. -/
theorem norm_ofMat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    ‖ofMat M‖ = Real.sqrt (∑ i, ∑ j, (M i j) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [ofMat, Fintype.sum_prod_type]

/-- The norm of `MatSpace n` is the Frobenius norm `‖X‖ = √(tr (Xᵀ X))`. -/
theorem norm_ofMat_eq_sqrt_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    ‖ofMat M‖ = Real.sqrt (Matrix.trace (Mᵀ * M)) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [ofMat, Matrix.trace, Matrix.mul_apply, Matrix.diag, Fintype.sum_prod_type, sq]
  rw [Finset.sum_comm]

/-- The singular locus `Σₙ = {X : det X = 0}` ("matrices non régulières"). -/
def singularLocus (n : ℕ) : Set (MatSpace n) := {x | (toMat x).det = 0}

theorem isClosed_singularLocus (n : ℕ) : IsClosed (singularLocus n) := by
  have hc : Continuous fun x : MatSpace n => (toMat x).det :=
    Continuous.matrix_det (continuous_matrix fun i j => (EuclideanSpace.proj (i, j)).continuous)
  exact isClosed_eq hc continuous_const

theorem ofMat_mem_singularLocus_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    ofMat M ∈ singularLocus n ↔ M.det = 0 := by
  simp [singularLocus]

theorem toMat_smul {n : ℕ} (c : ℝ) (x : MatSpace n) : toMat (c • x) = c • toMat x := rfl

theorem smul_mem_singularLocus {n : ℕ} {x : MatSpace n} (hx : x ∈ singularLocus n) (c : ℝ) :
    c • x ∈ singularLocus n := by
  have hx' : (toMat x).det = 0 := hx
  simp [singularLocus, toMat_smul, hx']

/-- **Bound (4) of the answer** in the singular locus: the intrinsic distance lies between the
Frobenius chord and `‖A‖_F + ‖B‖_F`, the latter being realised by the broken path `A → 0 → B`. -/
theorem intrinsicEDist_singularLocus_bounds {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det = 0) (hB : B.det = 0) :
    edist (ofMat A) (ofMat B) ≤ intrinsicEDist (singularLocus n) (ofMat A) (ofMat B) ∧
      intrinsicEDist (singularLocus n) (ofMat A) (ofMat B)
        ≤ ENNReal.ofReal (‖ofMat A‖ + ‖ofMat B‖) := by
  refine ⟨edist_le_intrinsicEDist _ _ _, intrinsicEDist_le_norm_add_norm ?_ ?_ ?_⟩
  · exact fun x hx c _ _ => smul_mem_singularLocus hx c
  · exact (ofMat_mem_singularLocus_iff A).2 hA
  · exact (ofMat_mem_singularLocus_iff B).2 hB

/-! ## 3. The determinant pencil -/

/-- The matrix pencil `A + λB`, with entries in `ℝ[λ]`. -/
noncomputable def pencil {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) (Polynomial ℝ) :=
  A.map (Polynomial.C : ℝ → ℝ[X]) + (Polynomial.X : ℝ[X]) • B.map (Polynomial.C : ℝ → ℝ[X])

theorem pencil_det_eval {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (l : ℝ) :
    (pencil A B).det.eval l = (A + l • B).det := by
  have h : (Polynomial.evalRingHom l) (pencil A B).det
      = ((Polynomial.evalRingHom l).mapMatrix (pencil A B)).det := RingHom.map_det _ _
  simp only [Polynomial.coe_evalRingHom] at h
  rw [h]
  congr 1
  ext i j
  simp [pencil, RingHom.mapMatrix_apply, Matrix.map_apply]
  ring

/-- **Determinant-pencil criterion** (conditions (11), (12), (13) of the answer). For matrices `A`,
`B` with `det B = 0` the following are equivalent:
1. every matrix on the segment `[A, B]` is singular;
2. the determinant of the pencil `A + λB` vanishes identically as a polynomial;
3. `A + λB` is singular for every real `λ`;
4. the pencil has a nonzero polynomial kernel vector. -/
theorem pencil_singular_tfae {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det = 0) :
    List.TFAE
      [ ∀ t ∈ Icc (0 : ℝ) 1, ((1 - t) • A + t • B).det = 0,
        (pencil A B).det = 0,
        ∀ l : ℝ, (A + l • B).det = 0,
        ∃ v : Fin n → Polynomial ℝ, v ≠ 0 ∧ (pencil A B) *ᵥ v = 0 ] := by
  tfae_have 1 → 2 := by
    intro h
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := Ici (0:ℝ)) ?_ (Set.Ici_infinite 0)
    intro l hl
    simp only [mem_Ici] at hl
    have hpos : (0:ℝ) < 1 + l := by linarith
    have hne0 : (1 + l) ≠ 0 := ne_of_gt hpos
    have ht : (1 + l)⁻¹ • (A + l • B) = (1 - l / (1 + l)) • A + (l / (1 + l)) • B := by
      match_scalars
      · field_simp
        ring
      · field_simp
    have hmem : l / (1 + l) ∈ Icc (0:ℝ) 1 :=
      ⟨by positivity, by rw [div_le_one hpos]; linarith⟩
    have hzero := h _ hmem
    rw [← ht, Matrix.det_smul] at hzero
    have hne : ((1 + l)⁻¹ : ℝ) ^ Fintype.card (Fin n) ≠ 0 := by positivity
    have hdet : (A + l • B).det = 0 := by
      rcases mul_eq_zero.1 hzero with h' | h'
      · exact absurd h' hne
      · exact h'
    simp [Polynomial.IsRoot, pencil_det_eval, hdet]
  tfae_have 2 → 3 := by
    intro h l
    rw [← pencil_det_eval, h]
    simp
  tfae_have 3 → 1 := by
    intro h t ht
    rcases eq_or_lt_of_le ht.2 with rfl | ht1
    · simpa using hB
    · have hpos : (0:ℝ) < 1 - t := by linarith
      have hne0 : (1 - t) ≠ 0 := ne_of_gt hpos
      have hrw : (1 - t) • A + t • B = (1 - t) • (A + (t / (1 - t)) • B) := by
        match_scalars <;> field_simp
      rw [hrw, Matrix.det_smul, h]
      ring
  tfae_have 2 ↔ 4 := by rw [← Matrix.exists_mulVec_eq_zero_iff]
  tfae_finish

/-! ## 4. Theorem 4: the chord criterion in the singular locus -/

/-- **Theorem 4.** For singular matrices `A` and `B`, the intrinsic distance inside the singular
locus `Σₙ` equals the Frobenius chord `‖A - B‖_F` if and only if the whole segment `[A, B]`
consists of singular matrices. -/
theorem intrinsicEDist_singularLocus_eq_edist_iff {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    intrinsicEDist (singularLocus n) (ofMat A) (ofMat B) = edist (ofMat A) (ofMat B) ↔
      ∀ t ∈ Icc (0 : ℝ) 1, ((1 - t) • A + t • B).det = 0 := by
  constructor
  · intro heq
    by_contra hcon
    push_neg at hcon
    obtain ⟨t, ht, hdet⟩ := hcon
    -- the point `(1-t)A + tB` lies off the (closed) singular locus, hence a ball around it does
    set c : MatSpace n := ofMat ((1 - t) • A + t • B) with hc
    have hcnot : c ∉ singularLocus n := by
      rw [hc, ofMat_mem_singularLocus_iff]
      exact hdet
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (isClosed_singularLocus n).isOpen_compl c hcnot
    have hballs : ∀ x ∈ singularLocus n, ρ ≤ dist x ((1 - t) • ofMat A + t • ofMat B) := by
      intro x hx
      have hcc : (1 - t) • ofMat A + t • ofMat B = c := by
        rw [hc, ofMat_add, ofMat_smul, ofMat_smul]
      rw [hcc]
      by_contra hlt
      push_neg at hlt
      exact (hball (by simpa [Metric.mem_ball] using hlt)) hx
    have := edist_lt_intrinsicEDist_of_obstacle (S := singularLocus n) (A := ofMat A)
      (B := ofMat B) ht.1 ht.2 hρ hballs
    rw [heq] at this
    exact lt_irrefl _ this
  · intro h
    apply intrinsicEDist_eq_edist_of_segment_subset
    rintro x hx
    rw [segment_eq_image ℝ] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    dsimp only
    have : (1 - t) • ofMat A + t • ofMat B = ofMat ((1 - t) • A + t • B) := by
      rw [ofMat_add, ofMat_smul, ofMat_smul]
    rw [this, ofMat_mem_singularLocus_iff]
    exact h t ht

/-- **Theorem 4, pencil form.** For singular `A`, `B`, the intrinsic distance in `Σₙ` is the
Frobenius chord exactly when the pencil `A + λB` is singular identically. -/
theorem intrinsicEDist_singularLocus_eq_edist_iff_pencil {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.det = 0) :
    intrinsicEDist (singularLocus n) (ofMat A) (ofMat B) = edist (ofMat A) (ofMat B) ↔
      (pencil A B).det = 0 := by
  rw [intrinsicEDist_singularLocus_eq_edist_iff A B]
  exact (pencil_singular_tfae A B hB).out 0 1

/-! ## 5. Partial results for `GLₙ⁺(ℝ)`

Theorem 3 of the answer characterises equality `d_{Ωₙ}(A,B) = ‖A - B‖_F` on
`Ωₙ = GLₙ⁺(ℝ) = {det > 0}` by nonnegativity of `t ↦ det((1-t)A + tB)` on `[0,1]`. The direction
that needs the local bypass construction (Lemma 8 of the answer) is not formalized here; the two
directions that follow from the material above are. -/

/-- `Ωₙ = GLₙ⁺(ℝ) = {X : det X > 0}`. -/
def posDetLocus (n : ℕ) : Set (MatSpace n) := {x | 0 < (toMat x).det}

theorem isOpen_posDetLocus (n : ℕ) : IsOpen (posDetLocus n) := by
  have hc : Continuous fun x : MatSpace n => (toMat x).det :=
    Continuous.matrix_det (continuous_matrix fun i j => (EuclideanSpace.proj (i, j)).continuous)
  exact isOpen_lt continuous_const hc

/-- If the whole open segment stays in `GLₙ⁺`, the intrinsic distance is the Frobenius chord. -/
theorem intrinsicEDist_posDetLocus_eq_edist {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ((1 - t) • A + t • B).det) :
    intrinsicEDist (posDetLocus n) (ofMat A) (ofMat B) = edist (ofMat A) (ofMat B) := by
  apply intrinsicEDist_eq_edist_of_segment_subset
  rintro x hx
  rw [segment_eq_image ℝ] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  dsimp only
  have hrw : (1 - t) • ofMat A + t • ofMat B = ofMat ((1 - t) • A + t • B) := by
    rw [ofMat_add, ofMat_smul, ofMat_smul]
  rw [hrw]
  exact h t ht

/-- **Corollary 7 in `GLₙ⁺`** (estimate `(17)`, qualitative form). If some matrix on the segment
`[A, B]` has negative determinant, then inside `GLₙ⁺` the intrinsic distance is strictly larger
than the Frobenius chord. -/
theorem edist_lt_intrinsicEDist_posDetLocus {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hneg : ((1 - t) • A + t • B).det < 0) :
    edist (ofMat A) (ofMat B) < intrinsicEDist (posDetLocus n) (ofMat A) (ofMat B) := by
  set c : MatSpace n := ofMat ((1 - t) • A + t • B) with hc
  have hopen : IsOpen {x : MatSpace n | (toMat x).det < 0} := by
    have hcont : Continuous fun x : MatSpace n => (toMat x).det :=
      Continuous.matrix_det (continuous_matrix fun i j => (EuclideanSpace.proj (i, j)).continuous)
    exact isOpen_lt hcont continuous_const
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen c (by simpa [hc] using hneg)
  have hballs : ∀ x ∈ posDetLocus n, ρ ≤ dist x ((1 - t) • ofMat A + t • ofMat B) := by
    intro x hx
    have hcc : (1 - t) • ofMat A + t • ofMat B = c := by
      rw [hc, ofMat_add, ofMat_smul, ofMat_smul]
    rw [hcc]
    by_contra hlt
    push_neg at hlt
    have := hball (by simpa [Metric.mem_ball] using hlt)
    exact absurd hx (by simpa [posDetLocus, not_lt] using this.le)
  exact edist_lt_intrinsicEDist_of_obstacle ht.1 ht.2 hρ hballs

/-! ## 6. The two worked examples -/

section Examples

/-- `A = e₂ ∧ e₃`-type skew matrix of the answer. -/
def skewA : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, -1; 0, 1, 0]

/-- `B = e₃ ∧ e₁`-type skew matrix of the answer. -/
def skewB : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 0, 0, 0; -1, 0, 0]

/-- A singular pencil without a common kernel vector: every real combination of `skewA` and
`skewB` is a `3 × 3` skew matrix, hence singular, so the intrinsic distance inside `Σ₃` is the
Frobenius chord — even though `ker skewA ≠ ker skewB`. -/
theorem dist_skew_pencil_example :
    intrinsicEDist (singularLocus 3) (ofMat skewA) (ofMat skewB)
      = edist (ofMat skewA) (ofMat skewB) := by
  rw [intrinsicEDist_singularLocus_eq_edist_iff]
  intro t _
  simp [skewA, skewB, Matrix.det_fin_three]

/-- The kernels of `skewA` and `skewB` are different lines, so there is no common null vector. -/
theorem skew_no_common_kernel :
    ∀ v : Fin 3 → ℝ, skewA *ᵥ v = 0 → skewB *ᵥ v = 0 → v = 0 := by
  intro v hA hB
  have h1 := congrFun hA 1
  have h2 := congrFun hA 2
  have h3 := congrFun hB 2
  simp [skewA, skewB, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2 h3
  funext i
  fin_cases i <;> simp [h1, h2, h3]

/-- `E₁₁` and `E₂₂`. -/
def E11 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- `E₂₂`. -/
def E22 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]

/-- The Frobenius distance from `(1/2)•I` to any singular `2×2` matrix is at least `1/2`
(this is `σ_min((1/2)•I) = 1/2`, the content of Lemma 6 in this special case). -/
theorem half_le_dist_singular (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.det = 0) :
    (1:ℝ)/2 ≤ dist (ofMat S) (ofMat ((1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) := by
  rw [dist_eq_norm, ← ofMat_sub, norm_ofMat]
  rw [Matrix.det_fin_two] at hS
  rw [show (1:ℝ)/2 = Real.sqrt ((1/2)^2) by rw [Real.sqrt_sq]; norm_num]
  apply Real.sqrt_le_sqrt
  simp [Fin.sum_univ_two, Matrix.one_apply]
  nlinarith [sq_nonneg (S 0 0 + S 1 1 - 1/2), sq_nonneg (S 0 1 - S 1 0)]

theorem midpoint_E11_E22 :
    (1 - (1/2 : ℝ)) • ofMat E11 + (1/2 : ℝ) • ofMat E22
      = ofMat ((1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [← ofMat_smul, ← ofMat_smul, ← ofMat_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [E11, E22, Matrix.one_apply]

theorem obstacle_E11_E22 :
    ∀ x ∈ singularLocus 2, (1/2 : ℝ) ≤ dist x ((1 - (1/2 : ℝ)) • ofMat E11 + (1/2 : ℝ) • ofMat E22) := by
  intro x hx
  rw [midpoint_E11_E22, ← ofMat_toMat x]
  exact half_le_dist_singular (toMat x) hx

theorem norm_ofMat_E22_sub_E11 : ‖ofMat E22 - ofMat E11‖ = Real.sqrt 2 := by
  rw [← ofMat_sub, norm_ofMat]
  congr 1
  simp [E11, E22, Fin.sum_univ_two]
  norm_num

/-- The `E₁₁`, `E₂₂` example, quantitative form: the obstacle bound at the midpoint gives
`d_{Σ₂}(E₁₁, E₂₂) ≥ √3`, while the Frobenius chord is only `√2`. -/
theorem sqrt_three_le_dist_E11_E22 :
    ENNReal.ofReal (Real.sqrt 3)
      ≤ intrinsicEDist (singularLocus 2) (ofMat E11) (ofMat E22) := by
  have h := obstacle_bound (S := singularLocus 2) (A := ofMat E11) (B := ofMat E22)
    (t := 1/2) (ρ := 1/2) (by norm_num) (by norm_num) (by norm_num) obstacle_E11_E22
  have hD : ‖ofMat E22 - ofMat E11‖ ^ 2 = 2 := by
    rw [norm_ofMat_E22_sub_E11]
    exact Real.sq_sqrt (by norm_num)
  rw [hD] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  rw [show ((1:ℝ)/2) ^ 2 * 2 + (1/2) ^ 2 = 3/4 by norm_num,
    show (1 - (1:ℝ)/2) ^ 2 * 2 + (1/2) ^ 2 = 3/4 by norm_num]
  have h34 : Real.sqrt (3/4) = Real.sqrt 3 / 2 := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3)]
    norm_num [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]
  rw [h34]
  ring

/-- The `E₁₁`, `E₂₂` example: since the midpoint `(1/2)•I` is invertible, the intrinsic distance
inside `Σ₂` is strictly larger than the Frobenius chord `√2`. -/
theorem dist_E11_E22_gt :
    edist (ofMat E11) (ofMat E22) < intrinsicEDist (singularLocus 2) (ofMat E11) (ofMat E22) :=
  edist_lt_intrinsicEDist_of_obstacle (t := 1/2) (ρ := 1/2) (by norm_num) (by norm_num)
    (by norm_num) obstacle_E11_E22

/-- The `GL₂⁺` example of the answer: `A = I`, `B = diag(-1,-2)`, whose segment has negative
determinant at `t = 2/5`, so the intrinsic distance inside `GL₂⁺` exceeds the chord `√13`. -/
def negDiag : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, -2]

theorem dist_GL2_example :
    edist (ofMat 1) (ofMat negDiag)
      < intrinsicEDist (posDetLocus 2) (ofMat 1) (ofMat negDiag) := by
  refine edist_lt_intrinsicEDist_posDetLocus _ _ (t := 2/5) (by norm_num) ?_
  simp [negDiag, Matrix.det_fin_two]
  norm_num

end Examples

end Q748
