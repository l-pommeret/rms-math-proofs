import RMS.Q748

/-!
# Q748 — Clifford coordinates on `M₂(ℝ)`

This module develops the complex ("Clifford") coordinates on `2 × 2` real matrices used by the
Q748 answer:

`Φ(A) = ( (a₀₀ + a₁₁) + i (a₁₀ - a₀₁) , (a₀₀ - a₁₁) + i (a₁₀ + a₀₁) ) / √2`.

It is a real linear isometry of the Frobenius space `M₂(ℝ)` onto `ℂ² = EuclideanSpace ℂ (Fin 2)`
(`Q748.cliffordPhiEquiv`) under which

* the Frobenius norm becomes the Hermitian norm (`Q748.cliffordPhi_normSq`), and
* the determinant becomes `(|z|² - |w|²)/2` (`Q748.cliffordPhi_det`).

Consequently the singular locus `Σ₂` becomes the cone `{|z| = |w|}` over the Clifford torus
(`Q748.cliffordPhi_maps_singularLink`) and the positive-determinant locus becomes `{|z| > |w|}`.
-/

open Set Metric Matrix
open scoped ENNReal NNReal

namespace Q748

noncomputable section Clifford

/-- `ℂ²` with its Hermitian (Euclidean) norm, the target of the Clifford coordinate map. -/
abbrev CliffordSpace := EuclideanSpace ℂ (Fin 2)

/-- The Clifford coordinate map on `2 × 2` real matrices. -/
def cliffordPhi (A : Matrix (Fin 2) (Fin 2) ℝ) : CliffordSpace :=
  WithLp.toLp 2 ![
    (Complex.ofReal (A 0 0 + A 1 1) +
        Complex.I * Complex.ofReal (A 1 0 - A 0 1)) /
      Complex.ofReal (Real.sqrt 2),
    (Complex.ofReal (A 0 0 - A 1 1) +
        Complex.I * Complex.ofReal (A 1 0 + A 0 1)) /
      Complex.ofReal (Real.sqrt 2)]

/-- The inverse of the Clifford coordinate map. -/
def cliffordPsi (z : CliffordSpace) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![((z.ofLp 0).re + (z.ofLp 1).re) / Real.sqrt 2,
       ((z.ofLp 1).im - (z.ofLp 0).im) / Real.sqrt 2;
     ((z.ofLp 0).im + (z.ofLp 1).im) / Real.sqrt 2,
       ((z.ofLp 0).re - (z.ofLp 1).re) / Real.sqrt 2]

/-- The Clifford coordinates carry the Frobenius norm to the Hermitian norm. -/
theorem cliffordPhi_normSq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Complex.normSq ((cliffordPhi A).ofLp 0) +
        Complex.normSq ((cliffordPhi A).ofLp 1) =
      ∑ i, ∑ j, (A i j) ^ 2 := by
  simp [cliffordPhi, Complex.normSq_apply, Fin.sum_univ_succ]
  ring_nf

/-- The Clifford coordinates turn the determinant into `(|z|² - |w|²)/2`. -/
theorem cliffordPhi_det (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.det =
      (Complex.normSq ((cliffordPhi A).ofLp 0) -
        Complex.normSq ((cliffordPhi A).ofLp 1)) / 2 := by
  simp [cliffordPhi, Complex.normSq_apply, Matrix.det_fin_two]
  ring_nf

theorem cliffordPsi_cliffordPhi (A : Matrix (Fin 2) (Fin 2) ℝ) :
    cliffordPsi (cliffordPhi A) = A := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cliffordPsi, cliffordPhi, Complex.div_re, Complex.div_im, Complex.normSq_apply] <;>
    field_simp <;> ring

theorem cliffordPhi_cliffordPsi (z : CliffordSpace) : cliffordPhi (cliffordPsi z) = z := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine WithLp.ofLp_injective (p := 2) ?_
  funext i
  fin_cases i <;>
  · apply Complex.ext <;>
    · simp [cliffordPhi, cliffordPsi, Complex.div_re, Complex.div_im, Complex.normSq_apply]
      field_simp
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      ring

theorem cliffordPhi_add (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    cliffordPhi (A + B) = cliffordPhi A + cliffordPhi B := by
  refine WithLp.ofLp_injective (p := 2) ?_
  funext i
  fin_cases i <;>
  · simp [cliffordPhi]
    ring

theorem cliffordPhi_smul (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    cliffordPhi (c • A) = c • cliffordPhi A := by
  refine WithLp.ofLp_injective (p := 2) ?_
  funext i
  fin_cases i <;>
  · simp [cliffordPhi, Complex.real_smul]
    ring

theorem norm_cliffordPhi (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖cliffordPhi A‖ = ‖ofMat A‖ := by
  rw [EuclideanSpace.norm_eq, norm_ofMat]
  congr 1
  rw [Fin.sum_univ_two, Complex.sq_norm, Complex.sq_norm, cliffordPhi_normSq A]

/-- The Clifford coordinate map, packaged as a real linear isometric equivalence
`M₂(ℝ) ≃ ℂ²`. -/
def cliffordPhiEquiv : MatSpace 2 ≃ₗᵢ[ℝ] CliffordSpace where
  toFun x := cliffordPhi (toMat x)
  invFun z := ofMat (cliffordPsi z)
  map_add' x y := by
    have : toMat (x + y) = toMat x + toMat y := rfl
    rw [this, cliffordPhi_add]
  map_smul' c x := by
    have : toMat (c • x) = c • toMat x := rfl
    rw [this, cliffordPhi_smul]
    rfl
  left_inv x := by
    simp only [cliffordPsi_cliffordPhi]
    exact ofMat_toMat x
  right_inv z := by
    simp only [toMat_ofMat]
    exact cliffordPhi_cliffordPsi z
  norm_map' x := by
    simpa [ofMat_toMat] using norm_cliffordPhi (toMat x)

@[simp] theorem cliffordPhiEquiv_apply (A : Matrix (Fin 2) (Fin 2) ℝ) :
    cliffordPhiEquiv (ofMat A) = cliffordPhi A := by
  simp [cliffordPhiEquiv, toMat_ofMat]

end Clifford

end Q748
