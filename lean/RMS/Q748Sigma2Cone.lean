import RMS.Q748Sigma2
import RMS.Q748FlatTorus

/-!
# Q748 — the exact distance in `Σ₂`: the cone upper bound

This module builds the explicit geodesic of the metric cone `Σ₂` over the Clifford torus and
derives the upper bound

`d_{Σ₂}(A, B) ≤ √(‖A‖² + ‖B‖² - 2‖A‖‖B‖ cos (sigma2Theta A B))`

for nonzero singular `2 × 2` matrices.  The path is `t ↦ ρ(t) • γ(t)`, where `γ` is the
Clifford-torus geodesic of `RequestProject.Q748Sigma2` and `ρ` is the radial coordinate of the
straight segment of the Euclidean plane joining the two endpoints written in polar coordinates.
The comparison between the two is exactly the flat-torus inequality of
`RequestProject.Q748FlatTorus`.
-/

open Set Metric Matrix
open scoped ENNReal NNReal Real

namespace Q748

noncomputable section Sigma2Cone

/-! ### Comparison lemmas for total variation -/

/-- If a path has everywhere smaller chords than another one, it has smaller total variation. -/
theorem eVariationOn_le_of_edist_le {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    {f : ℝ → E} {g : ℝ → F} {s : Set ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) ≤ edist (g x) (g y)) :
    eVariationOn f s ≤ eVariationOn g s := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, us⟩
  refine le_trans (Finset.sum_le_sum ?_) (eVariationOn.sum_le g n hu us)
  intro i _
  exact h _ (us _) _ (us _)

/-- A monotone reparametrisation of a straight segment has total variation at most the length of
the segment. -/
theorem eVariationOn_segment_reparam_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P Q : E) {lam : ℝ → ℝ} (hmono : MonotoneOn lam (Icc 0 1)) (h0 : lam 0 = 0) (h1 : lam 1 = 1) :
    eVariationOn (fun t => P + lam t • (Q - P)) (Icc (0:ℝ) 1) ≤ ENNReal.ofReal ‖Q - P‖ := by
  set g : ℝ → ℝ := fun t => lam t * ‖Q - P‖ with hg
  have hchord : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      edist (P + lam x • (Q - P)) (P + lam y • (Q - P)) ≤ edist (g x) (g y) := by
    intro x _ y _
    have hsub : (P + lam x • (Q - P)) - (P + lam y • (Q - P)) = (lam x - lam y) • (Q - P) := by
      module
    have hgxy' : lam x * ‖Q - P‖ - lam y * ‖Q - P‖ = (lam x - lam y) * ‖Q - P‖ := by ring
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, hsub, norm_smul]
    simp only [Real.norm_eq_abs, hg]
    rw [hgxy', abs_mul, abs_of_nonneg (norm_nonneg (Q - P))]
  refine le_trans (eVariationOn_le_of_edist_le hchord) ?_
  have hmono' : MonotoneOn g (Icc (0:ℝ) 1) := fun x hx y hy hxy =>
    mul_le_mul_of_nonneg_right (hmono hx hy hxy) (norm_nonneg _)
  have hvar : eVariationOn g (Icc (0:ℝ) 1) ≤ ENNReal.ofReal (g 1 - g 0) := by
    simpa [Set.inter_self] using hmono'.eVariationOn_le (a := 0) (b := 1)
      (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1) (by norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1)
  refine le_trans hvar ?_
  rw [hg]
  simp [h0, h1]

/-! ### The planar segment in polar coordinates -/

/-- Denominator of the polar reparametrisation of a planar segment. -/
def segD (r s σ t : ℝ) : ℝ := r * Real.sin (σ * t) + s * Real.sin (σ * (1 - t))

/-- Affine parameter of the point of the planar segment at polar angle `σ t`. -/
def segLam (r s σ t : ℝ) : ℝ := r * Real.sin (σ * t) / segD r s σ t

/-- Radial coordinate of the point of the planar segment at polar angle `σ t`. -/
def segRad (r s σ t : ℝ) : ℝ := r * s * Real.sin σ / segD r s σ t

theorem segD_pos {r s σ : ℝ} (hr : 0 < r) (hs : 0 < s) (hσ0 : 0 < σ) (hσ : σ < π)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : 0 < segD r s σ t := by
  have h1 : 0 ≤ Real.sin (σ * t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [ht.1]) (by nlinarith [ht.1, ht.2])
  have h2 : 0 ≤ Real.sin (σ * (1 - t)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [ht.2]) (by nlinarith [ht.1])
  rcases eq_or_lt_of_le ht.1 with h | h
  · have hpos : 0 < Real.sin (σ * (1 - t)) := by
      rw [← h]; simpa using Real.sin_pos_of_pos_of_lt_pi hσ0 hσ
    unfold segD; nlinarith
  · have hpos : 0 < Real.sin (σ * t) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [ht.2])
    unfold segD; nlinarith

theorem segLam_monotoneOn {r s σ : ℝ} (hr : 0 < r) (hs : 0 < s) (hσ0 : 0 < σ) (hσ : σ < π) :
    MonotoneOn (segLam r s σ) (Icc 0 1) := by
  intro t ht t' ht' htt
  have hD := segD_pos hr hs hσ0 hσ ht
  have hD' := segD_pos hr hs hσ0 hσ ht'
  rw [segLam, segLam, div_le_div_iff₀ hD hD']
  have key : Real.sin (σ * t) * Real.sin (σ * (1 - t')) - Real.sin (σ * t') * Real.sin (σ * (1 - t))
      = -(Real.sin σ * Real.sin (σ * (t' - t))) := by
    simp only [mul_sub, mul_one, Real.sin_sub]
    ring
  have hsσ : 0 < Real.sin σ := Real.sin_pos_of_pos_of_lt_pi hσ0 hσ
  have hw : 0 ≤ Real.sin (σ * (t' - t)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith [ht.1, ht'.2])
  have hexp : r * Real.sin (σ * t') * segD r s σ t - r * Real.sin (σ * t) * segD r s σ t'
      = r * s * (Real.sin σ * Real.sin (σ * (t' - t))) := by
    unfold segD
    linear_combination (-(r * s)) * key
  have hpos : 0 ≤ r * s * (Real.sin σ * Real.sin (σ * (t' - t))) := by positivity
  linarith

theorem segLam_zero (r s σ : ℝ) : segLam r s σ 0 = 0 := by
  unfold segLam segD
  simp

theorem segLam_one {r s σ : ℝ} (hr : r ≠ 0) (hσ : Real.sin σ ≠ 0) : segLam r s σ 1 = 1 := by
  unfold segLam segD
  simp
  exact ⟨hr, hσ⟩

theorem segRad_nonneg {r s σ : ℝ} (hr : 0 < r) (hs : 0 < s) (hσ0 : 0 < σ) (hσ : σ < π)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : 0 ≤ segRad r s σ t := by
  have hD := segD_pos hr hs hσ0 hσ ht
  have hsσ : 0 < Real.sin σ := Real.sin_pos_of_pos_of_lt_pi hσ0 hσ
  unfold segRad
  positivity

theorem segRad_zero {r s σ : ℝ} (hs : s ≠ 0) (hσ : Real.sin σ ≠ 0) : segRad r s σ 0 = r := by
  unfold segRad segD
  simp
  field_simp

theorem segRad_one {r s σ : ℝ} (hr : r ≠ 0) (hσ : Real.sin σ ≠ 0) : segRad r s σ 1 = s := by
  unfold segRad segD
  simp
  field_simp

/-- The trigonometric identity behind the polar parametrisation of a segment. -/
theorem trig_polar_id (σ t : ℝ) :
    ((Real.sin σ : ℝ) : ℂ) * Complex.exp (((σ * t : ℝ) : ℂ) * Complex.I)
      = ((Real.sin (σ * (1 - t)) : ℝ) : ℂ)
        + ((Real.sin (σ * t) : ℝ) : ℂ) * Complex.exp (((σ : ℝ) : ℂ) * Complex.I) := by
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]
    rw [mul_sub, mul_one, Real.sin_sub]
    ring
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, add_zero, zero_add]
    ring

/-- The point of polar coordinates `(segRad r s σ t, σ t)` is the point of affine parameter
`segLam r s σ t` on the segment joining `r` to `s e^{iσ}`. -/
theorem segPolar {r s σ t : ℝ} (hD : segD r s σ t ≠ 0) :
    ((segRad r s σ t : ℝ) : ℂ) * Complex.exp (((σ * t : ℝ) : ℂ) * Complex.I)
      = (r : ℂ) + ((segLam r s σ t : ℝ) : ℂ) *
          (((s : ℂ) * Complex.exp (((σ : ℝ) : ℂ) * Complex.I)) - (r : ℂ)) := by
  have hDne : ((segD r s σ t : ℝ) : ℂ) ≠ 0 := by simpa using hD
  have hid := trig_polar_id σ t
  set X := Complex.exp (((σ * t : ℝ) : ℂ) * Complex.I) with hX
  set Y := Complex.exp (((σ : ℝ) : ℂ) * Complex.I) with hY
  have key : ((r * s * Real.sin σ : ℝ) : ℂ) * X
      = ((segD r s σ t : ℝ) : ℂ) * (r : ℂ)
        + ((r * Real.sin (σ * t) : ℝ) : ℂ) * ((s : ℂ) * Y - (r : ℂ)) := by
    simp only [segD, Complex.ofReal_add, Complex.ofReal_mul]
    linear_combination ((r : ℂ) * (s : ℂ)) * hid
  rw [segRad, segLam, Complex.ofReal_div, Complex.ofReal_div]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_comm, ← sub_eq_zero]
  field_simp
  linear_combination -key

/-! ### Chords in the cone over the Clifford torus -/

theorem norm_sq_polar_sub (r s u v : ℝ) :
    ‖(r : ℂ) * Complex.exp ((u : ℂ) * Complex.I) - (s : ℂ) * Complex.exp ((v : ℂ) * Complex.I)‖ ^ 2
      = r ^ 2 + s ^ 2 - 2 * r * s * Real.cos (u - v) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re, Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq u, Real.sin_sq_add_cos_sq v]

/-- Squared norm in the Clifford model of `M₂(ℝ)`. -/
theorem norm_sq_cliffordSpace (v : CliffordSpace) : ‖v‖ ^ 2 = ‖v.ofLp 0‖ ^ 2 + ‖v.ofLp 1‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sq_sqrt (by positivity)]

/-- **The cone chord estimate.**  In the cone over the Clifford torus, the chord between two
points of radii `x, y` whose phases differ by `(t - t') d₁` and `(t - t') d₂` is at most the
planar chord between the points of the same radii with angular separation
`σ |t - t'|`, `σ = √(d₁² + d₂²)/√2`. -/
theorem norm_cone_torus_sub_le {a b : ℂ} (ha : ‖a‖ = 1 / Real.sqrt 2) (hb : ‖b‖ = 1 / Real.sqrt 2)
    {d1 d2 σ : ℝ} (hd1 : |d1| ≤ π) (hd2 : |d2| ≤ π)
    (hσ : σ = Real.sqrt (d1 ^ 2 + d2 ^ 2) / Real.sqrt 2)
    {x y t t' : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (htt : |t - t'| ≤ 1) :
    ‖x • (WithLp.toLp 2 ![a * Complex.exp (((t * d1 : ℝ) : ℂ) * Complex.I),
            b * Complex.exp (((t * d2 : ℝ) : ℂ) * Complex.I)] : CliffordSpace)
        - y • (WithLp.toLp 2 ![a * Complex.exp (((t' * d1 : ℝ) : ℂ) * Complex.I),
            b * Complex.exp (((t' * d2 : ℝ) : ℂ) * Complex.I)] : CliffordSpace)‖
      ≤ ‖(x : ℂ) * Complex.exp (((σ * t : ℝ) : ℂ) * Complex.I)
          - (y : ℂ) * Complex.exp (((σ * t' : ℝ) : ℂ) * Complex.I)‖ := by
  have hna : ‖a‖ ^ 2 = 1 / 2 := by
    rw [ha, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hnb : ‖b‖ ^ 2 = 1 / 2 := by
    rw [hb, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  set V : CliffordSpace :=
    x • (WithLp.toLp 2 ![a * Complex.exp (((t * d1 : ℝ) : ℂ) * Complex.I),
            b * Complex.exp (((t * d2 : ℝ) : ℂ) * Complex.I)] : CliffordSpace)
        - y • (WithLp.toLp 2 ![a * Complex.exp (((t' * d1 : ℝ) : ℂ) * Complex.I),
            b * Complex.exp (((t' * d2 : ℝ) : ℂ) * Complex.I)] : CliffordSpace) with hV
  have hc0 : V.ofLp 0 = a * ((x : ℂ) * Complex.exp (((t * d1 : ℝ) : ℂ) * Complex.I)
      - (y : ℂ) * Complex.exp (((t' * d1 : ℝ) : ℂ) * Complex.I)) := by
    rw [hV]; simp [Complex.real_smul]; ring
  have hc1 : V.ofLp 1 = b * ((x : ℂ) * Complex.exp (((t * d2 : ℝ) : ℂ) * Complex.I)
      - (y : ℂ) * Complex.exp (((t' * d2 : ℝ) : ℂ) * Complex.I)) := by
    rw [hV]; simp [Complex.real_smul]; ring
  have hlhs : ‖V‖ ^ 2 = x ^ 2 + y ^ 2
      - x * y * (Real.cos ((t - t') * d1) + Real.cos ((t - t') * d2)) := by
    rw [norm_sq_cliffordSpace, hc0, hc1, norm_mul, norm_mul, mul_pow, mul_pow, hna, hnb,
      norm_sq_polar_sub, norm_sq_polar_sub,
      show t * d1 - t' * d1 = (t - t') * d1 by ring, show t * d2 - t' * d2 = (t - t') * d2 by ring]
    ring
  have hrhs : ‖(x : ℂ) * Complex.exp (((σ * t : ℝ) : ℂ) * Complex.I)
      - (y : ℂ) * Complex.exp (((σ * t' : ℝ) : ℂ) * Complex.I)‖ ^ 2
      = x ^ 2 + y ^ 2 - 2 * x * y * Real.cos (σ * (t - t')) := by
    rw [norm_sq_polar_sub, show σ * t - σ * t' = σ * (t - t') by ring]
  have hkey : Real.cos (σ * (t - t')) ≤
      (Real.cos ((t - t') * d1) + Real.cos ((t - t') * d2)) / 2 := by
    have habs1 : |(t - t') * d1| ≤ π := by
      rw [abs_mul]
      calc |t - t'| * |d1| ≤ 1 * π := mul_le_mul htt hd1 (abs_nonneg _) (by norm_num)
        _ = π := one_mul _
    have habs2 : |(t - t') * d2| ≤ π := by
      rw [abs_mul]
      calc |t - t'| * |d2| ≤ 1 * π := mul_le_mul htt hd2 (abs_nonneg _) (by norm_num)
        _ = π := one_mul _
    have harg : Real.sqrt ((((t - t') * d1) ^ 2 + ((t - t') * d2) ^ 2) / 2) = σ * |t - t'| := by
      rw [hσ, show (((t - t') * d1) ^ 2 + ((t - t') * d2) ^ 2) / 2
            = (t - t') ^ 2 * ((d1 ^ 2 + d2 ^ 2) / 2) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
        Real.sqrt_div (by positivity : (0:ℝ) ≤ d1 ^ 2 + d2 ^ 2)]
      ring
    have h := cos_quadraticMean_le_avg_cos habs1 habs2
    rw [harg] at h
    have hcosabs : Real.cos (σ * |t - t'|) = Real.cos (σ * (t - t')) := by
      rcases abs_cases (t - t') with hc | hc
      · rw [hc.1]
      · rw [hc.1, mul_neg, Real.cos_neg]
    rwa [hcosabs] at h
  have hsq : ‖V‖ ^ 2 ≤ ‖(x : ℂ) * Complex.exp (((σ * t : ℝ) : ℂ) * Complex.I)
      - (y : ℂ) * Complex.exp (((σ * t' : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
    rw [hlhs, hrhs]
    nlinarith [mul_nonneg hx hy]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

/-! ### Clifford data of a pair of nonzero singular matrices -/

/-- Normalising two nonzero singular `2 × 2` matrices and passing to Clifford coordinates, the
two endpoints are `(a, b)` and `(a e^{i d₁}, b e^{i d₂})` on the Clifford torus, with principal
phase shifts `d₁, d₂ ∈ [-π, π]` computing `sigma2Theta`. -/
theorem exists_cliffordTorus_data (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.det = 0) (hB : B.det = 0) (hA0 : ofMat A ≠ 0) (hB0 : ofMat B ≠ 0) :
    ∃ (a b : ℂ) (d1 d2 : ℝ), ‖a‖ = 1 / Real.sqrt 2 ∧ ‖b‖ = 1 / Real.sqrt 2 ∧
      |d1| ≤ π ∧ |d2| ≤ π ∧
      sigma2Theta A B = Real.sqrt (d1 ^ 2 + d2 ^ 2) / Real.sqrt 2 ∧
      cliffordPhiEquiv ((‖ofMat A‖)⁻¹ • ofMat A) = WithLp.toLp 2 ![a, b] ∧
      cliffordPhiEquiv ((‖ofMat B‖)⁻¹ • ofMat B) =
        WithLp.toLp 2 ![a * Complex.exp ((d1 : ℂ) * Complex.I),
          b * Complex.exp ((d2 : ℂ) * Complex.I)] := by
  have hnA : (0:ℝ) < ‖ofMat A‖ := norm_pos_iff.2 hA0
  have hnB : (0:ℝ) < ‖ofMat B‖ := norm_pos_iff.2 hB0
  have hAmem : ofMat A ∈ singularLocus 2 := (ofMat_mem_singularLocus_iff A).2 hA
  have hBmem : ofMat B ∈ singularLocus 2 := (ofMat_mem_singularLocus_iff B).2 hB
  set uA : MatSpace 2 := (‖ofMat A‖)⁻¹ • ofMat A with huAdef
  set uB : MatSpace 2 := (‖ofMat B‖)⁻¹ • ofMat B with huBdef
  have huA : uA ∈ singularLink 2 := norm_smul_mem_singularLink hAmem hA0
  have huB : uB ∈ singularLink 2 := norm_smul_mem_singularLink hBmem hB0
  set pA : CliffordSpace := cliffordPhiEquiv uA with hpAdef
  set pB : CliffordSpace := cliffordPhiEquiv uB with hpBdef
  have hpA : pA ∈ cliffordTorus := by
    rw [← cliffordPhi_maps_singularLink]; exact ⟨uA, huA, rfl⟩
  have hpB : pB ∈ cliffordTorus := by
    rw [← cliffordPhi_maps_singularLink]; exact ⟨uB, huB, rfl⟩
  set a := pA.ofLp 0 with hadef
  set b := pA.ofLp 1 with hbdef
  set a' := pB.ofLp 0 with ha'def
  set b' := pB.ofLp 1 with hb'def
  have hna : ‖a‖ = 1 / Real.sqrt 2 := hpA.1
  have hnb : ‖b‖ = 1 / Real.sqrt 2 := hpA.2
  have hna' : ‖a'‖ = 1 / Real.sqrt 2 := hpB.1
  have hnb' : ‖b'‖ = 1 / Real.sqrt 2 := hpB.2
  have ha0 : a ≠ 0 := norm_pos_iff.1 (by rw [hna]; positivity)
  have hb0 : b ≠ 0 := norm_pos_iff.1 (by rw [hnb]; positivity)
  have ha'0 : a' ≠ 0 := norm_pos_iff.1 (by rw [hna']; positivity)
  have hb'0 : b' ≠ 0 := norm_pos_iff.1 (by rw [hnb']; positivity)
  refine ⟨a, b, Complex.arg (a' / a), Complex.arg (b' / b), hna, hnb, ?_, ?_, ?_, ?_, ?_⟩
  · exact abs_le.2 ⟨by linarith [Complex.neg_pi_lt_arg (a' / a)], Complex.arg_le_pi _⟩
  · exact abs_le.2 ⟨by linarith [Complex.neg_pi_lt_arg (b' / b)], Complex.arg_le_pi _⟩
  · -- the angle
    have habs1 : |Complex.arg (a' / a)| = complexPrincipalAngle a a' :=
      abs_arg_div_eq_complexPrincipalAngle ha0 ha'0
    have habs2 : |Complex.arg (b' / b)| = complexPrincipalAngle b b' :=
      abs_arg_div_eq_complexPrincipalAngle hb0 hb'0
    have hcoordA : ∀ i, pA.ofLp i = ((‖ofMat A‖)⁻¹ : ℝ) * (cliffordPhi A).ofLp i := by
      intro i
      have hp : pA = ((‖ofMat A‖)⁻¹ : ℝ) • cliffordPhi A := by
        rw [hpAdef, huAdef, map_smul, cliffordPhiEquiv_apply]
      rw [hp]
      simp [Complex.real_smul]
    have hcoordB : ∀ i, pB.ofLp i = ((‖ofMat B‖)⁻¹ : ℝ) * (cliffordPhi B).ofLp i := by
      intro i
      have hp : pB = ((‖ofMat B‖)⁻¹ : ℝ) • cliffordPhi B := by
        rw [hpBdef, huBdef, map_smul, cliffordPhiEquiv_apply]
      rw [hp]
      simp [Complex.real_smul]
    have hangle0 : complexPrincipalAngle a a' =
        complexPrincipalAngle ((cliffordPhi A).ofLp 0) ((cliffordPhi B).ofLp 0) := by
      rw [hadef, ha'def, hcoordA 0, hcoordB 0,
        complexPrincipalAngle_smul_left (inv_pos.2 hnA),
        complexPrincipalAngle_smul_right (inv_pos.2 hnB)]
    have hangle1 : complexPrincipalAngle b b' =
        complexPrincipalAngle ((cliffordPhi A).ofLp 1) ((cliffordPhi B).ofLp 1) := by
      rw [hbdef, hb'def, hcoordA 1, hcoordB 1,
        complexPrincipalAngle_smul_left (inv_pos.2 hnA),
        complexPrincipalAngle_smul_right (inv_pos.2 hnB)]
    rw [sigma2Theta, ← hangle0, ← hangle1, ← habs1, ← habs2, sq_abs, sq_abs]
  · exact (cliffordSpace_eta pA).symm
  · have he : ∀ (x y : ℂ), x ≠ 0 → ‖y‖ = ‖x‖ →
        x * Complex.exp (((Complex.arg (y / x) : ℝ) : ℂ) * Complex.I) = y := by
      intro x y hx hxy
      have hn : ‖y / x‖ = 1 := by
        rw [norm_div, hxy]
        exact div_self (by simpa using hx)
      have h := Complex.norm_mul_exp_arg_mul_I (y / x)
      rw [hn] at h
      simp only [Complex.ofReal_one, one_mul] at h
      rw [h]
      field_simp
    have h1 : a * Complex.exp (((Complex.arg (a' / a) : ℝ) : ℂ) * Complex.I) = a' :=
      he a a' ha0 (by rw [hna, hna'])
    have h2 : b * Complex.exp (((Complex.arg (b' / b) : ℝ) : ℂ) * Complex.I) = b' :=
      he b b' hb0 (by rw [hnb, hnb'])
    rw [h1, h2]
    exact (cliffordSpace_eta pB).symm

/-! ### The cone upper bound in `Σ₂` -/

set_option maxHeartbeats 1000000 in
/-- **Theorem 9, upper bound.**  For nonzero singular `2 × 2` matrices the intrinsic distance in
`Σ₂` is at most the metric-cone chord over the Clifford torus. -/
theorem intrinsicEDist_singularLocus_two_le (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.det = 0) (hB : B.det = 0) (hA0 : ofMat A ≠ 0) (hB0 : ofMat B ≠ 0) :
    intrinsicEDist (singularLocus 2) (ofMat A) (ofMat B) ≤
      ENNReal.ofReal (Real.sqrt (‖ofMat A‖ ^ 2 + ‖ofMat B‖ ^ 2 -
        2 * ‖ofMat A‖ * ‖ofMat B‖ * Real.cos (sigma2Theta A B))) := by
  obtain ⟨a, b, d1, d2, hna, hnb, hd1, hd2, hL, hEA, hEB⟩ :=
    exists_cliffordTorus_data A B hA hB hA0 hB0
  have hr : 0 < ‖ofMat A‖ := norm_pos_iff.2 hA0
  have hs : 0 < ‖ofMat B‖ := norm_pos_iff.2 hB0
  set r := ‖ofMat A‖ with hrdef
  set s := ‖ofMat B‖ with hsdef
  set σ := sigma2Theta A B with hσdef
  have hσ0 : 0 ≤ σ := sigma2Theta_nonneg A B
  have hσpi : σ ≤ π := sigma2Theta_le_pi A B
  have hAmem : ofMat A ∈ singularLocus 2 := (ofMat_mem_singularLocus_iff A).2 hA
  have hBmem : ofMat B ∈ singularLocus 2 := (ofMat_mem_singularLocus_iff B).2 hB
  set uA : MatSpace 2 := r⁻¹ • ofMat A with huAdef
  set uB : MatSpace 2 := s⁻¹ • ofMat B with huBdef
  have huA : uA ∈ singularLink 2 := norm_smul_mem_singularLink hAmem hA0
  have huB : uB ∈ singularLink 2 := norm_smul_mem_singularLink hBmem hB0
  have hAeq : r • uA = ofMat A := by
    rw [huAdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  have hBeq : s • uB = ofMat B := by
    rw [huBdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul]
  rcases eq_or_lt_of_le hσ0 with hzero | hpos
  · -- degenerate case: the two normalisations agree, the segment is radial
    have hdd : d1 = 0 ∧ d2 = 0 := by
      have h2 : Real.sqrt (d1 ^ 2 + d2 ^ 2) / Real.sqrt 2 = 0 := by rw [← hL]; exact hzero.symm
      have h3 : d1 ^ 2 + d2 ^ 2 = 0 := by
        rcases div_eq_zero_iff.1 h2 with h4 | h4
        · exact (Real.sqrt_eq_zero (by positivity)).1 h4
        · exact absurd h4 (by positivity)
      constructor <;> nlinarith [sq_nonneg d1, sq_nonneg d2]
    have huAB : uA = uB := by
      apply cliffordPhiEquiv.injective
      rw [hEA, hEB, hdd.1, hdd.2]
      norm_num
    have hseg : segment ℝ (ofMat A) (ofMat B) ⊆ singularLocus 2 := by
      intro x hx
      rw [segment_eq_image' ℝ (ofMat A) (ofMat B)] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      have hxe : ofMat A + t • (ofMat B - ofMat A) = (r + t * (s - r)) • uA := by
        rw [← hAeq, ← hBeq, ← huAB]
        module
      show ofMat A + t • (ofMat B - ofMat A) ∈ singularLocus 2
      rw [hxe]
      exact smul_mem_singularLocus huA.1 _
    have heq := intrinsicEDist_eq_edist_of_segment_subset hseg
    rw [heq]
    have hcos : Real.cos σ = 1 := by rw [← hzero, Real.cos_zero]
    have hnorm : ‖ofMat A - ofMat B‖ = |r - s| := by
      rw [← hAeq, ← hBeq, ← huAB, ← sub_smul, norm_smul, Real.norm_eq_abs]
      have : ‖uA‖ = 1 := by
        have := huA.2
        simpa [Metric.mem_sphere, dist_eq_norm] using this
      rw [this, mul_one]
    have hval : Real.sqrt (r ^ 2 + s ^ 2 - 2 * r * s * Real.cos σ) = |r - s| := by
      rw [hcos, show r ^ 2 + s ^ 2 - 2 * r * s * 1 = (r - s) ^ 2 by ring, Real.sqrt_sq_eq_abs]
    rw [hval, edist_dist, dist_eq_norm, hnorm]
  rcases eq_or_lt_of_le hσpi with hpi | hlt
  · -- antipodal case: the broken path through the apex
    have hstar : ∀ x ∈ singularLocus 2, ∀ c : ℝ, 0 ≤ c → c ≤ 1 → c • x ∈ singularLocus 2 :=
      fun x hx c _ _ => smul_mem_singularLocus hx c
    have hbound := intrinsicEDist_le_norm_add_norm hstar hAmem hBmem
    have hval : Real.sqrt (r ^ 2 + s ^ 2 - 2 * r * s * Real.cos σ) = r + s := by
      rw [hpi, Real.cos_pi, show r ^ 2 + s ^ 2 - 2 * r * s * (-1) = (r + s) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    rw [hval]
    exact hbound
  -- the main case `0 < σ < π`
  have hsinσ : Real.sin σ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hlt)
  set q : ℝ → CliffordSpace := fun t =>
    WithLp.toLp 2 ![a * Complex.exp (((t * d1 : ℝ) : ℂ) * Complex.I),
      b * Complex.exp (((t * d2 : ℝ) : ℂ) * Complex.I)] with hqdef
  set γ : ℝ → MatSpace 2 := fun t => cliffordPhiEquiv.symm (q t) with hγdef
  have hq0 : q 0 = cliffordPhiEquiv uA := by
    rw [hqdef, hEA]
    norm_num
  have hq1 : q 1 = cliffordPhiEquiv uB := by
    rw [hqdef, hEB]
    norm_num
  have hγ0 : γ 0 = uA := by
    rw [hγdef]
    simp only [hq0, LinearIsometryEquiv.symm_apply_apply]
  have hγ1 : γ 1 = uB := by
    rw [hγdef]
    simp only [hq1, LinearIsometryEquiv.symm_apply_apply]
  have hqtorus : ∀ t, q t ∈ cliffordTorus := by
    intro t
    constructor
    · show ‖(q t).ofLp 0‖ = 1 / Real.sqrt 2
      have h0 : (q t).ofLp 0 = a * Complex.exp (((t * d1 : ℝ) : ℂ) * Complex.I) := by
        rw [hqdef]; simp
      rw [h0, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, hna]
    · show ‖(q t).ofLp 1‖ = 1 / Real.sqrt 2
      have h1 : (q t).ofLp 1 = b * Complex.exp (((t * d2 : ℝ) : ℂ) * Complex.I) := by
        rw [hqdef]; simp
      rw [h1, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, hnb]
  have hγmem : ∀ t, γ t ∈ singularLink 2 := by
    intro t
    have hmem : q t ∈ cliffordPhiEquiv '' (singularLink 2) := by
      rw [cliffordPhi_maps_singularLink]; exact hqtorus t
    obtain ⟨x, hx, hxq⟩ := hmem
    have hgx : γ t = x := by
      show cliffordPhiEquiv.symm (q t) = x
      rw [← hxq, LinearIsometryEquiv.symm_apply_apply]
    rw [hgx]; exact hx
  -- continuity
  have hqlip : LipschitzWith ⟨Real.sqrt (‖a‖ ^ 2 * d1 ^ 2 + ‖b‖ ^ 2 * d2 ^ 2), by positivity⟩ q := by
    apply LipschitzWith.of_dist_le_mul
    intro t t'
    rw [dist_eq_norm, Real.dist_eq]
    exact norm_torus_path_sub_le a b d1 d2 t t'
  have hγcont : Continuous γ := by
    rw [hγdef]
    exact cliffordPhiEquiv.symm.continuous.comp hqlip.continuous
  have hDcont : Continuous (segD r s σ) := by
    unfold segD
    fun_prop
  have hρcont : ContinuousOn (segRad r s σ) (Icc 0 1) := by
    have hc : ContinuousOn (fun t => r * s * Real.sin σ / segD r s σ t) (Icc (0:ℝ) 1) :=
      ContinuousOn.div continuousOn_const hDcont.continuousOn
        fun t ht => ne_of_gt (segD_pos hr hs hpos hlt ht)
    exact hc
  set h : ℝ → MatSpace 2 := fun t => segRad r s σ t • γ t with hhdef
  have hhcont : ContinuousOn h (Icc 0 1) := hρcont.smul hγcont.continuousOn
  have hhmem : ∀ t ∈ Icc (0:ℝ) 1, h t ∈ singularLocus 2 := fun t _ =>
    smul_mem_singularLocus (hγmem t).1 _
  have hh0 : h 0 = ofMat A := by
    rw [hhdef]
    simp only [hγ0, segRad_zero (ne_of_gt hs) hsinσ]
    exact hAeq
  have hh1 : h 1 = ofMat B := by
    rw [hhdef]
    simp only [hγ1, segRad_one (ne_of_gt hr) hsinσ]
    exact hBeq
  have hpath : IsPathIn (singularLocus 2) (ofMat A) (ofMat B) h := ⟨hhcont, hhmem, hh0, hh1⟩
  -- the planar comparison path
  set p : ℝ → ℂ := fun t =>
    ((segRad r s σ t : ℝ) : ℂ) * Complex.exp (((σ * t : ℝ) : ℂ) * Complex.I) with hpdef
  have hchord : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, edist (h x) (h y) ≤ edist (p x) (p y) := by
    intro x hx y hy
    have hclif : ∀ t, cliffordPhiEquiv (h t) = (segRad r s σ t) • q t := by
      intro t
      rw [hhdef, hγdef]
      simp only [map_smul, LinearIsometryEquiv.apply_symm_apply]
    have hnormeq : ‖h x - h y‖ = ‖(segRad r s σ x) • q x - (segRad r s σ y) • q y‖ := by
      rw [← hclif x, ← hclif y, ← map_sub, cliffordPhiEquiv.norm_map]
    have hxy : |x - y| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have hb := norm_cone_torus_sub_le (a := a) (b := b) hna hnb hd1 hd2 hL
      (segRad_nonneg hr hs hpos hlt hx) (segRad_nonneg hr hs hpos hlt hy) hxy
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, hnormeq, hpdef]
    exact ENNReal.ofReal_le_ofReal (by simpa [hqdef] using hb)
  have hvar1 : eVariationOn h (Icc (0:ℝ) 1) ≤ eVariationOn p (Icc (0:ℝ) 1) :=
    eVariationOn_le_of_edist_le hchord
  -- the planar path is a monotone reparametrisation of a segment
  set P : ℂ := (r : ℂ) with hPdef
  set Q : ℂ := (s : ℂ) * Complex.exp (((σ : ℝ) : ℂ) * Complex.I) with hQdef
  have hpseg : ∀ t ∈ Icc (0:ℝ) 1, edist (p t) (P + segLam r s σ t • (Q - P)) = 0 := by
    intro t ht
    have hD : segD r s σ t ≠ 0 := ne_of_gt (segD_pos hr hs hpos hlt ht)
    have := segPolar (r := r) (s := s) (σ := σ) (t := t) hD
    rw [hpdef, hPdef, hQdef]
    simp only [Complex.real_smul]
    rw [this]
    simp
  have hvar2 : eVariationOn p (Icc (0:ℝ) 1)
      = eVariationOn (fun t => P + segLam r s σ t • (Q - P)) (Icc (0:ℝ) 1) :=
    eVariationOn.eq_of_edist_zero_on hpseg
  have hvar3 : eVariationOn (fun t => P + segLam r s σ t • (Q - P)) (Icc (0:ℝ) 1)
      ≤ ENNReal.ofReal ‖Q - P‖ :=
    eVariationOn_segment_reparam_le P Q (segLam_monotoneOn hr hs hpos hlt)
      (segLam_zero r s σ) (segLam_one (ne_of_gt hr) hsinσ)
  have hQP : ‖Q - P‖ = Real.sqrt (r ^ 2 + s ^ 2 - 2 * r * s * Real.cos σ) := by
    have hP : P = (r : ℂ) * Complex.exp ((((0:ℝ) : ℝ) : ℂ) * Complex.I) := by
      rw [hPdef]; simp
    have hsq : ‖Q - P‖ ^ 2 = r ^ 2 + s ^ 2 - 2 * r * s * Real.cos σ := by
      rw [hQdef, hP, norm_sq_polar_sub, sub_zero]
      ring
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  calc intrinsicEDist (singularLocus 2) (ofMat A) (ofMat B) ≤ eVariationOn h (Icc 0 1) :=
        intrinsicEDist_le hpath
    _ ≤ eVariationOn p (Icc 0 1) := hvar1
    _ ≤ ENNReal.ofReal ‖Q - P‖ := by rw [hvar2]; exact hvar3
    _ = _ := by rw [hQP]

end Sigma2Cone

end Q748
