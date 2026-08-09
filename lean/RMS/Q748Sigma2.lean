import RMS.Q748Clifford
import RMS.Q748Cone

/-!
# Q748 — the singular locus `Σ₂` in Clifford coordinates

This module identifies, inside the Clifford coordinates of `RequestProject.Q748Clifford`, the
unit link of the singular locus `Σ₂ ⊆ M₂(ℝ)` with the **Clifford torus**
`{(z,w) ∈ ℂ² : |z| = |w| = 1/√2}`, and introduces the angular quantity `Q748.sigma2Theta`
computing the flat-torus link angle of two nonzero singular matrices.

It also records the exact intrinsic distances in `Σₙ` when one of the endpoints is the origin
(the apex of the cone `Σₙ`).
-/

open Set Metric Matrix
open scoped ENNReal NNReal

namespace Q748

noncomputable section Sigma2

/-! ### The apex of the cone `Σₙ` -/

/-- Exact intrinsic distance in `Σₙ` from the origin: the straight segment from `0` to a singular
matrix consists of singular matrices, so the intrinsic distance is the Frobenius norm. -/
theorem intrinsicEDist_singularLocus_zero_left {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det = 0) :
    intrinsicEDist (singularLocus n) 0 (ofMat A) = edist (0 : MatSpace n) (ofMat A) := by
  refine intrinsicEDist_eq_edist_of_segment_subset ?_
  intro x hx
  rw [segment_eq_image' ℝ (0 : MatSpace n) (ofMat A)] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  show (0 : MatSpace n) + t • (ofMat A - 0) ∈ singularLocus n
  rw [show (0 : MatSpace n) + t • (ofMat A - 0) = t • ofMat A by module]
  exact smul_mem_singularLocus ((ofMat_mem_singularLocus_iff A).2 hA) t

/-- Exact intrinsic distance in `Σₙ` to the origin. -/
theorem intrinsicEDist_singularLocus_zero_right {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det = 0) :
    intrinsicEDist (singularLocus n) (ofMat A) 0 = edist (ofMat A) (0 : MatSpace n) := by
  refine intrinsicEDist_eq_edist_of_segment_subset ?_
  intro x hx
  rw [segment_eq_image' ℝ (ofMat A) (0 : MatSpace n)] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  show ofMat A + t • ((0 : MatSpace n) - ofMat A) ∈ singularLocus n
  rw [show ofMat A + t • ((0 : MatSpace n) - ofMat A) = (1 - t) • ofMat A by module]
  exact smul_mem_singularLocus ((ofMat_mem_singularLocus_iff A).2 hA) (1 - t)

/-! ### The Clifford torus -/

private theorem eq_of_sq_eq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) :
    a = b := by
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb, h]

theorem normSq_cliffordPhi_zero (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Complex.normSq ((cliffordPhi A).ofLp 0) = ‖(cliffordPhi A).ofLp 0‖ ^ 2 :=
  (Complex.sq_norm _).symm

theorem normSq_cliffordPhi_one (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Complex.normSq ((cliffordPhi A).ofLp 1) = ‖(cliffordPhi A).ofLp 1‖ ^ 2 :=
  (Complex.sq_norm _).symm

/-- A `2 × 2` matrix is singular exactly when its two Clifford coordinates have equal modulus. -/
theorem cliffordPhi_singular_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.det = 0 ↔ ‖(cliffordPhi A).ofLp 0‖ = ‖(cliffordPhi A).ofLp 1‖ := by
  rw [cliffordPhi_det A, normSq_cliffordPhi_zero, normSq_cliffordPhi_one]
  constructor
  · intro h
    have h' : ‖(cliffordPhi A).ofLp 0‖ ^ 2 = ‖(cliffordPhi A).ofLp 1‖ ^ 2 := by
      have h1 : ‖(cliffordPhi A).ofLp 0‖ ^ 2 - ‖(cliffordPhi A).ofLp 1‖ ^ 2 = 0 := by
        field_simp at h
        linarith
      linarith
    exact eq_of_sq_eq_of_nonneg (norm_nonneg _) (norm_nonneg _) h'
  · intro h
    rw [h]
    ring

theorem norm_sq_cliffordPhi_add (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖(cliffordPhi A).ofLp 0‖ ^ 2 + ‖(cliffordPhi A).ofLp 1‖ ^ 2 = ‖ofMat A‖ ^ 2 := by
  rw [← normSq_cliffordPhi_zero, ← normSq_cliffordPhi_one, cliffordPhi_normSq, norm_ofMat,
    Real.sq_sqrt (by positivity)]

/-- A **unit** singular matrix has both Clifford coordinates of modulus `1/√2`: its image lies on
the Clifford torus. -/
theorem cliffordPhi_unit_singular (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 0)
    (hnorm : ‖ofMat A‖ = 1) :
    ‖(cliffordPhi A).ofLp 0‖ = 1 / Real.sqrt 2 ∧ ‖(cliffordPhi A).ofLp 1‖ = 1 / Real.sqrt 2 := by
  have heq := (cliffordPhi_singular_iff A).1 hdet
  have hsum := norm_sq_cliffordPhi_add A
  rw [hnorm, heq] at hsum
  have hval : ‖(cliffordPhi A).ofLp 1‖ ^ 2 = (1 / Real.sqrt 2) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [hsum]
  have h1 : ‖(cliffordPhi A).ofLp 1‖ = 1 / Real.sqrt 2 :=
    eq_of_sq_eq_of_nonneg (norm_nonneg _) (by positivity) hval
  exact ⟨by rw [heq, h1], h1⟩

/-- The Clifford torus `{(z,w) : |z| = |w| = 1/√2}` in `ℂ²`. -/
def cliffordTorus : Set CliffordSpace :=
  {p | ‖p.ofLp 0‖ = 1 / Real.sqrt 2 ∧ ‖p.ofLp 1‖ = 1 / Real.sqrt 2}

/-- The Clifford coordinates map the unit link of `Σ₂` **onto** the Clifford torus. -/
theorem cliffordPhi_maps_singularLink :
    cliffordPhiEquiv '' (singularLink 2) = cliffordTorus := by
  ext p
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    have hA : (toMat x).det = 0 := hx1
    have hnorm : ‖ofMat (toMat x)‖ = 1 := by
      rw [ofMat_toMat]
      simpa [Metric.mem_sphere, dist_eq_norm] using hx2
    have := cliffordPhi_unit_singular (toMat x) hA hnorm
    have hxp : cliffordPhiEquiv x = cliffordPhi (toMat x) := by
      rw [← ofMat_toMat x, cliffordPhiEquiv_apply, toMat_ofMat]
    rw [hxp]
    exact ⟨this.1, this.2⟩
  · intro hp
    refine ⟨ofMat (cliffordPsi p), ⟨?_, ?_⟩, ?_⟩
    · show (toMat (ofMat (cliffordPsi p))).det = 0
      rw [toMat_ofMat]
      rw [cliffordPhi_singular_iff, cliffordPhi_cliffordPsi]
      rw [hp.1, hp.2]
    · have hnorm : ‖cliffordPhi (cliffordPsi p)‖ = ‖ofMat (cliffordPsi p)‖ :=
        norm_cliffordPhi _
      rw [cliffordPhi_cliffordPsi] at hnorm
      have hpn : ‖p‖ = 1 := by
        rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, hp.1, hp.2]
        rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      simp [← hnorm, hpn]
    · rw [cliffordPhiEquiv_apply, cliffordPhi_cliffordPsi]

/-! ### The principal angle between complex numbers, and the `Σ₂` link angle -/

/-- The principal angle in `[0,π]` between two nonzero complex numbers, defined through the
normalized real part of the Hermitian product. -/
def complexPrincipalAngle (z w : ℂ) : ℝ :=
  Real.arccos ((((starRingEnd ℂ) z) * w).re / (‖z‖ * ‖w‖))

theorem complexPrincipalAngle_nonneg (z w : ℂ) : 0 ≤ complexPrincipalAngle z w :=
  Real.arccos_nonneg _

theorem complexPrincipalAngle_le_pi (z w : ℂ) : complexPrincipalAngle z w ≤ Real.pi :=
  Real.arccos_le_pi _

/-- Cauchy–Schwarz for the real part of the Hermitian product of two complex numbers. -/
theorem abs_re_conj_mul_le (z w : ℂ) : |(((starRingEnd ℂ) z) * w).re| ≤ ‖z‖ * ‖w‖ := by
  have h1 : |(((starRingEnd ℂ) z) * w).re| ≤ ‖((starRingEnd ℂ) z) * w‖ :=
    Complex.abs_re_le_norm _
  simpa [norm_mul] using h1

/-- The cosine of the principal angle is the normalized real Hermitian product. -/
theorem cos_complexPrincipalAngle {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    Real.cos (complexPrincipalAngle z w) = (((starRingEnd ℂ) z) * w).re / (‖z‖ * ‖w‖) := by
  have hzn : (0:ℝ) < ‖z‖ := norm_pos_iff.2 hz
  have hwn : (0:ℝ) < ‖w‖ := norm_pos_iff.2 hw
  have hb := abs_re_conj_mul_le z w
  have hle : (((starRingEnd ℂ) z) * w).re / (‖z‖ * ‖w‖) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact le_trans (le_abs_self _) hb
  have hge : (-1 : ℝ) ≤ (((starRingEnd ℂ) z) * w).re / (‖z‖ * ‖w‖) := by
    rw [le_div_iff₀ (by positivity)]
    have := neg_abs_le (((starRingEnd ℂ) z) * w).re
    linarith [hb, this]
  exact Real.cos_arccos hge hle

/-- The flat-torus link angle attached to two nonzero singular `2 × 2` matrices: the two Clifford
phases contribute their principal angles, combined with the flat-torus factor `1/√2`. -/
def sigma2Theta (A B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Real.sqrt
      ((complexPrincipalAngle ((cliffordPhi A).ofLp 0) ((cliffordPhi B).ofLp 0)) ^ 2 +
        (complexPrincipalAngle ((cliffordPhi A).ofLp 1) ((cliffordPhi B).ofLp 1)) ^ 2) /
    Real.sqrt 2

theorem sigma2Theta_nonneg (A B : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ sigma2Theta A B := by
  unfold sigma2Theta
  positivity

theorem sigma2Theta_le_pi (A B : Matrix (Fin 2) (Fin 2) ℝ) : sigma2Theta A B ≤ Real.pi := by
  have hpi : (0:ℝ) ≤ Real.pi := Real.pi_nonneg
  have h0 := complexPrincipalAngle_le_pi ((cliffordPhi A).ofLp 0) ((cliffordPhi B).ofLp 0)
  have h1 := complexPrincipalAngle_le_pi ((cliffordPhi A).ofLp 1) ((cliffordPhi B).ofLp 1)
  have h0' := complexPrincipalAngle_nonneg ((cliffordPhi A).ofLp 0) ((cliffordPhi B).ofLp 0)
  have h1' := complexPrincipalAngle_nonneg ((cliffordPhi A).ofLp 1) ((cliffordPhi B).ofLp 1)
  have hsum :
      (complexPrincipalAngle ((cliffordPhi A).ofLp 0) ((cliffordPhi B).ofLp 0)) ^ 2 +
        (complexPrincipalAngle ((cliffordPhi A).ofLp 1) ((cliffordPhi B).ofLp 1)) ^ 2 ≤
        2 * Real.pi ^ 2 := by nlinarith
  have hsqrt :
      Real.sqrt
          ((complexPrincipalAngle ((cliffordPhi A).ofLp 0) ((cliffordPhi B).ofLp 0)) ^ 2 +
            (complexPrincipalAngle ((cliffordPhi A).ofLp 1) ((cliffordPhi B).ofLp 1)) ^ 2) ≤
        Real.sqrt (2 * Real.pi ^ 2) := Real.sqrt_le_sqrt hsum
  have h2 : Real.sqrt (2 * Real.pi ^ 2) = Real.sqrt 2 * Real.pi := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hpi]
  rw [sigma2Theta, div_le_iff₀ (by positivity)]
  calc _ ≤ Real.sqrt (2 * Real.pi ^ 2) := hsqrt
    _ = Real.pi * Real.sqrt 2 := by rw [h2]; ring

/-! ### The Clifford-torus geodesic: the link upper bound -/

/-- The map `x ↦ exp (i x)` is `1`-Lipschitz. -/
theorem norm_exp_mul_I_sub_exp_mul_I_le (u v : ℝ) :
    ‖Complex.exp ((u : ℂ) * Complex.I) - Complex.exp ((v : ℂ) * Complex.I)‖ ≤ |u - v| := by
  have hsq : ‖Complex.exp ((u : ℂ) * Complex.I) - Complex.exp ((v : ℂ) * Complex.I)‖ ^ 2
      = 2 - 2 * Real.cos (u - v) := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Real.cos_sub]
    ring_nf
    nlinarith [Real.sin_sq_add_cos_sq u, Real.sin_sq_add_cos_sq v]
  have hb : 2 - 2 * Real.cos (u - v) ≤ (u - v) ^ 2 := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := u - v)]
  have h := Real.sqrt_le_sqrt hb
  rw [← hsq] at h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq_eq_abs] at h

private theorem sq_le_of_le_mul_abs {X c d t : ℝ} (hX : 0 ≤ X) (h : X ≤ c * (|d| * |t|)) :
    X ^ 2 ≤ c ^ 2 * d ^ 2 * t ^ 2 := by
  have h2 := mul_self_le_mul_self hX h
  have e : (c * (|d| * |t|)) * (c * (|d| * |t|)) = c ^ 2 * d ^ 2 * t ^ 2 := by
    rw [show (c * (|d| * |t|)) * (c * (|d| * |t|)) = c ^ 2 * (|d| ^ 2) * (|t| ^ 2) by ring,
      sq_abs, sq_abs]
  rw [sq]
  linarith

/-- The two-phase path on a product of two circles is Lipschitz with the flat-product constant. -/
theorem norm_torus_path_sub_le (z w : ℂ) (d1 d2 t t' : ℝ) :
    ‖(WithLp.toLp 2 ![z * Complex.exp (((t * d1 : ℝ) : ℂ) * Complex.I),
        w * Complex.exp (((t * d2 : ℝ) : ℂ) * Complex.I)] : CliffordSpace)
      - WithLp.toLp 2 ![z * Complex.exp (((t' * d1 : ℝ) : ℂ) * Complex.I),
        w * Complex.exp (((t' * d2 : ℝ) : ℂ) * Complex.I)]‖
      ≤ Real.sqrt (‖z‖ ^ 2 * d1 ^ 2 + ‖w‖ ^ 2 * d2 ^ 2) * |t - t'| := by
  have key : ∀ (u : ℂ) (d : ℝ), ‖u * Complex.exp (((t * d : ℝ) : ℂ) * Complex.I)
      - u * Complex.exp (((t' * d : ℝ) : ℂ) * Complex.I)‖ ≤ ‖u‖ * (|d| * |t - t'|) := by
    intro u d
    rw [← mul_sub, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg u)
    refine le_trans (norm_exp_mul_I_sub_exp_mul_I_le _ _) ?_
    rw [show t * d - t' * d = d * (t - t') by ring, abs_mul]
  have hnorm : ‖(WithLp.toLp 2 ![z * Complex.exp (((t * d1 : ℝ) : ℂ) * Complex.I),
        w * Complex.exp (((t * d2 : ℝ) : ℂ) * Complex.I)] : CliffordSpace)
      - WithLp.toLp 2 ![z * Complex.exp (((t' * d1 : ℝ) : ℂ) * Complex.I),
        w * Complex.exp (((t' * d2 : ℝ) : ℂ) * Complex.I)]‖
      = Real.sqrt (‖z * Complex.exp (((t * d1 : ℝ) : ℂ) * Complex.I)
          - z * Complex.exp (((t' * d1 : ℝ) : ℂ) * Complex.I)‖ ^ 2
        + ‖w * Complex.exp (((t * d2 : ℝ) : ℂ) * Complex.I)
          - w * Complex.exp (((t' * d2 : ℝ) : ℂ) * Complex.I)‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp
  rw [hnorm]
  have b1 := sq_le_of_le_mul_abs (norm_nonneg _) (key z d1)
  have b2 := sq_le_of_le_mul_abs (norm_nonneg _) (key w d2)
  have hsq : ‖z * Complex.exp (((t * d1 : ℝ) : ℂ) * Complex.I)
          - z * Complex.exp (((t' * d1 : ℝ) : ℂ) * Complex.I)‖ ^ 2
        + ‖w * Complex.exp (((t * d2 : ℝ) : ℂ) * Complex.I)
          - w * Complex.exp (((t' * d2 : ℝ) : ℂ) * Complex.I)‖ ^ 2
      ≤ (Real.sqrt (‖z‖ ^ 2 * d1 ^ 2 + ‖w‖ ^ 2 * d2 ^ 2) * |t - t'|) ^ 2 := by
    have e : (Real.sqrt (‖z‖ ^ 2 * d1 ^ 2 + ‖w‖ ^ 2 * d2 ^ 2) * |t - t'|) ^ 2
        = ‖z‖ ^ 2 * d1 ^ 2 * (t - t') ^ 2 + ‖w‖ ^ 2 * d2 ^ 2 * (t - t') ^ 2 := by
      rw [mul_pow, sq_abs, Real.sq_sqrt (by positivity)]
      ring
    rw [e]
    linarith
  calc _ ≤ Real.sqrt ((Real.sqrt (‖z‖ ^ 2 * d1 ^ 2 + ‖w‖ ^ 2 * d2 ^ 2) * |t - t'|) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = _ := Real.sqrt_sq (by positivity)

theorem complexPrincipalAngle_smul_left {c : ℝ} (hc : 0 < c) (z w : ℂ) :
    complexPrincipalAngle ((c : ℂ) * z) w = complexPrincipalAngle z w := by
  unfold complexPrincipalAngle
  congr 1
  have h1 : (((starRingEnd ℂ) ((c : ℂ) * z)) * w).re = c * (((starRingEnd ℂ) z) * w).re := by
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have h2 : ‖(c : ℂ) * z‖ = c * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  rw [h1, h2, mul_assoc, mul_div_mul_left _ _ (ne_of_gt hc)]

theorem complexPrincipalAngle_smul_right {c : ℝ} (hc : 0 < c) (z w : ℂ) :
    complexPrincipalAngle z ((c : ℂ) * w) = complexPrincipalAngle z w := by
  unfold complexPrincipalAngle
  congr 1
  have h1 : (((starRingEnd ℂ) z) * ((c : ℂ) * w)).re = c * (((starRingEnd ℂ) z) * w).re := by
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have h2 : ‖(c : ℂ) * w‖ = c * ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  rw [h1, h2, show ‖z‖ * (c * ‖w‖) = c * (‖z‖ * ‖w‖) by ring,
    mul_div_mul_left _ _ (ne_of_gt hc)]

/-- The principal angle is the absolute value of the argument of the quotient: the phase change
along the shortest arc (the winding-number-minimizing choice). -/
theorem abs_arg_div_eq_complexPrincipalAngle {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    |Complex.arg (w / z)| = complexPrincipalAngle z w := by
  have hq : w / z ≠ 0 := div_ne_zero hw hz
  have hz' : ‖z‖ ≠ 0 := by simpa using hz
  have hw' : ‖w‖ ≠ 0 := by simpa using hw
  have hcos : Real.cos (Complex.arg (w / z)) = (((starRingEnd ℂ) z) * w).re / (‖z‖ * ‖w‖) := by
    rw [Complex.cos_arg hq]
    have h1 : (w / z).re = (((starRingEnd ℂ) z) * w).re / ‖z‖ ^ 2 := by
      rw [Complex.div_re, Complex.normSq_eq_norm_sq, Complex.mul_re]
      simp
      ring
    have h2 : ‖w / z‖ = ‖w‖ / ‖z‖ := norm_div w z
    rw [h1, h2]
    field_simp
  have hcos' : Real.cos |Complex.arg (w / z)| = (((starRingEnd ℂ) z) * w).re / (‖z‖ * ‖w‖) := by
    rcases abs_cases (Complex.arg (w / z)) with h | h
    · rw [h.1]; exact hcos
    · rw [h.1, Real.cos_neg]; exact hcos
  have hle : |Complex.arg (w / z)| ≤ Real.pi :=
    abs_le.2 ⟨by linarith [Complex.neg_pi_lt_arg (w / z)], Complex.arg_le_pi _⟩
  rw [complexPrincipalAngle, ← hcos', Real.arccos_cos (abs_nonneg _) hle]

/-- Every element of `ℂ²` is the `toLp` of its two coordinates. -/
theorem cliffordSpace_eta (p : CliffordSpace) : WithLp.toLp 2 ![p.ofLp 0, p.ofLp 1] = p := by
  refine WithLp.ofLp_injective (p := 2) ?_
  funext i
  fin_cases i <;> simp

set_option maxHeartbeats 1000000 in
/-- **The Clifford-torus geodesic (upper bound of Theorem 9 at the level of the link).** For
nonzero singular `2 × 2` matrices, the intrinsic distance inside the unit link `singularLink 2`
between their normalizations is at most `sigma2Theta A B`: the two shortest principal-angle arcs,
combined with the flat-torus factor `1/√2`. -/
theorem intrinsicEDist_singularLink_two_le (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.det = 0) (hB : B.det = 0) (hA0 : ofMat A ≠ 0) (hB0 : ofMat B ≠ 0) :
    intrinsicEDist (singularLink 2) ((‖ofMat A‖)⁻¹ • ofMat A) ((‖ofMat B‖)⁻¹ • ofMat B) ≤
      ENNReal.ofReal (sigma2Theta A B) := by
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
  set d1 := Complex.arg (a' / a) with hd1def
  set d2 := Complex.arg (b' / b) with hd2def
  have habs1 : |d1| = complexPrincipalAngle a a' := abs_arg_div_eq_complexPrincipalAngle ha0 ha'0
  have habs2 : |d2| = complexPrincipalAngle b b' := abs_arg_div_eq_complexPrincipalAngle hb0 hb'0
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
  have hL : sigma2Theta A B = Real.sqrt (d1 ^ 2 + d2 ^ 2) / Real.sqrt 2 := by
    rw [sigma2Theta, ← hangle0, ← hangle1, ← habs1, ← habs2, sq_abs, sq_abs]
  set L := sigma2Theta A B with hLdef
  have hLnonneg : 0 ≤ L := sigma2Theta_nonneg A B
  set q : ℝ → CliffordSpace := fun t =>
    WithLp.toLp 2 ![a * Complex.exp (((t * d1 : ℝ) : ℂ) * Complex.I),
      b * Complex.exp (((t * d2 : ℝ) : ℂ) * Complex.I)] with hqdef
  set γ : ℝ → MatSpace 2 := fun t => cliffordPhiEquiv.symm (q t) with hγdef
  have hq0 : q 0 = pA := by
    have : q 0 = WithLp.toLp 2 ![a, b] := by
      rw [hqdef]
      norm_num
    rw [this, hadef, hbdef, cliffordSpace_eta]
  have hq1 : q 1 = pB := by
    have he : ∀ (x y : ℂ), x ≠ 0 → ‖y‖ = ‖x‖ →
        x * Complex.exp (((1 * Complex.arg (y / x) : ℝ) : ℂ) * Complex.I) = y := by
      intro x y hx hxy
      have hn : ‖y / x‖ = 1 := by
        rw [norm_div, hxy]
        exact div_self (by simpa using hx)
      have h := Complex.norm_mul_exp_arg_mul_I (y / x)
      rw [hn] at h
      simp only [Complex.ofReal_one, one_mul] at h
      rw [one_mul, h]
      field_simp
    have h1 : a * Complex.exp (((1 * d1 : ℝ) : ℂ) * Complex.I) = a' :=
      he a a' ha0 (by rw [hna, hna'])
    have h2 : b * Complex.exp (((1 * d2 : ℝ) : ℂ) * Complex.I) = b' :=
      he b b' hb0 (by rw [hnb, hnb'])
    have : q 1 = WithLp.toLp 2 ![a', b'] := by
      rw [hqdef]
      simp only [h1, h2]
    rw [this, ha'def, hb'def, cliffordSpace_eta]
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
  set K : ℝ≥0 := ⟨L, hLnonneg⟩ with hKdef
  have hlip : LipschitzWith K γ := by
    apply LipschitzWith.of_dist_le_mul
    intro t t'
    have hdist : dist (γ t) (γ t') = ‖q t - q t'‖ := by
      show dist (cliffordPhiEquiv.symm (q t)) (cliffordPhiEquiv.symm (q t')) = ‖q t - q t'‖
      rw [LinearIsometryEquiv.dist_map, dist_eq_norm]
    have hbound := norm_torus_path_sub_le a b d1 d2 t t'
    rw [hna, hnb] at hbound
    have hcoef : Real.sqrt ((1 / Real.sqrt 2) ^ 2 * d1 ^ 2 + (1 / Real.sqrt 2) ^ 2 * d2 ^ 2)
        = L := by
      rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), hL]
      have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      rw [eq_div_iff (ne_of_gt h2), ← Real.sqrt_mul (by positivity)]
      congr 1
      ring
    rw [hcoef] at hbound
    rw [hdist, Real.dist_eq]
    simpa using le_trans (le_of_eq (by rw [hqdef])) hbound
  have hpath : IsPathIn (singularLink 2) uA uB γ := by
    refine ⟨hlip.continuous.continuousOn, fun t _ => hγmem t, ?_, ?_⟩
    · show cliffordPhiEquiv.symm (q 0) = uA
      rw [hq0, hpAdef, LinearIsometryEquiv.symm_apply_apply]
    · show cliffordPhiEquiv.symm (q 1) = uB
      rw [hq1, hpBdef, LinearIsometryEquiv.symm_apply_apply]
  calc intrinsicEDist (singularLink 2) uA uB ≤ eVariationOn γ (Icc 0 1) :=
        intrinsicEDist_le hpath
    _ ≤ (K : ℝ≥0∞) * ENNReal.ofReal (1 - 0) :=
        eVariationOn_le_of_lipschitz hlip
    _ = ENNReal.ofReal L := by
        rw [sub_zero, ENNReal.ofReal_one, mul_one, ENNReal.ofReal_eq_coe_nnreal hLnonneg]

end Sigma2

end Q748
