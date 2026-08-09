/-
# Q788 — the volume of the relative-coordinate ellipsoid

For the fixed-`n` upper-edge asymptotic we need the exact Lebesgue volume of the sublevel
sets of the quadratic form

  `Q(x) = ∑_j x_j² - (∑_j x_j)² / (m+1)`   (`x ∈ ℝ^m`, `m = n - 1`),

which is the quadratic form of the matrix `I_m - J_m/(m+1)` appearing in the relative
coordinates of a configuration of `n = m+1` points.  Its determinant is `1/(m+1)`
(`Q788.det_one_sub_smul_ones`), so the sublevel set `{Q ≤ r}` is an ellipsoid of volume
`√(m+1) · ω_m · r^{m/2}` with `ω_m = √π^m / Γ(m/2+1)` the volume of the unit ball.

The proof is by the explicit linear change of variables `x ↦ x + c (∑_j x_j) 𝟙` with
`c = (√(m+1) - 1)/m`, which turns `Q` into the Euclidean square norm and has determinant
`1 + c m = √(m+1)`.
-/
import RMS.Q788Volume

open MeasureTheory Real Set
open scoped ENNReal

namespace Q788

/-- `relQuad m x = ∑_j x_j² - (∑_j x_j)²/(m+1)`: the quadratic form of the matrix
`I_m - J_m/(m+1)`. -/
noncomputable def relQuad (m : ℕ) (x : Fin m → ℝ) : ℝ :=
  (∑ j, (x j) ^ 2) - (∑ j, x j) ^ 2 / ((m : ℝ) + 1)

theorem relQuad_nonneg (m : ℕ) (x : Fin m → ℝ) : 0 ≤ relQuad m x := by
  have hcs : (∑ j, x j) ^ 2 ≤ (m : ℝ) * ∑ j, (x j) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
      (fun _ => (1 : ℝ)) x
    simpa [Finset.card_univ] using h
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hs : 0 ≤ ∑ j, (x j) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [relQuad, sub_nonneg, div_le_iff₀ hm]
  nlinarith

/-! ## The linear change of variables -/

/-- The shear `x ↦ x + c (∑ x_j) 𝟙`. -/
noncomputable def shear (m : ℕ) (c : ℝ) : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) where
  toFun x := fun i => x i + c * ∑ j, x j
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' a x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

theorem shear_apply (m : ℕ) (c : ℝ) (x : Fin m → ℝ) (i : Fin m) :
    shear m c x i = x i + c * ∑ j, x j := rfl

theorem sum_shear (m : ℕ) (c : ℝ) (x : Fin m → ℝ) :
    (∑ i, shear m c x i) = (1 + c * m) * ∑ j, x j := by
  simp only [shear_apply, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The shear turns `Q` into the Euclidean square norm, provided `2c + c²m = 1`. -/
theorem relQuad_shear (m : ℕ) (c : ℝ) (hc : 2 * c + c ^ 2 * m = 1) (x : Fin m → ℝ) :
    relQuad m (shear m c x) = ∑ j, (x j) ^ 2 := by
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  set S : ℝ := ∑ j, x j with hS
  have hsq : (∑ i, (shear m c x i) ^ 2)
      = (∑ j, (x j) ^ 2) + (2 * c + c ^ 2 * m) * S ^ 2 := by
    have hpt : ∀ i ∈ (Finset.univ : Finset (Fin m)), (shear m c x i) ^ 2
        = (x i) ^ 2 + (2 * c * S) * x i + c ^ 2 * S ^ 2 := by
      intro i _; rw [shear_apply, ← hS]; ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← hS]
    ring
  have hcm : (1 + c * m) ^ 2 = (m : ℝ) + 1 := by nlinarith
  rw [relQuad, hsq, sum_shear, ← hS, mul_pow, hcm, hc]
  field_simp
  ring

/-- The explicit inverse shear. -/
theorem shear_surjective (m : ℕ) (c : ℝ) (h : (1 : ℝ) + c * m ≠ 0) :
    Function.Surjective (shear m c) := by
  intro y
  refine ⟨fun i => y i - c * (∑ j, y j) / (1 + c * m), ?_⟩
  have h2 : (1 : ℝ) + (m : ℝ) * c ≠ 0 := by rw [mul_comm]; exact h
  have hs : (∑ j, (y j - c * (∑ j, y j) / (1 + c * m))) = (∑ j, y j) / (1 + c * m) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    ring
  funext i
  rw [shear_apply, hs]
  field_simp
  ring

/-- The determinant of the shear. -/
theorem det_shear (m : ℕ) (c : ℝ) : LinearMap.det (shear m c) = 1 + c * m := by
  classical
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin m))]
  have hmat : (LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin m)))
      (shear m c)
      = (1 : Matrix (Fin m) (Fin m) ℝ) + Matrix.replicateCol (Fin 1) (fun _ : Fin m => c)
          * Matrix.replicateRow (Fin 1) (fun _ : Fin m => (1 : ℝ)) := by
    ext i j
    simp [shear_apply, Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [hmat, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, mul_comm]

/-! ## The volume of the ellipsoid -/

/-- The Euclidean ball, written with the square sum. -/
theorem volume_sum_sq_le {m : ℕ} (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r) :
    volume {x : Fin m → ℝ | ∑ j, (x j) ^ 2 ≤ r}
      = ENNReal.ofReal (√r) ^ m * ENNReal.ofReal (√π ^ m / Real.Gamma (m / 2 + 1)) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hset : {x : Fin m → ℝ | ∑ j, (x j) ^ 2 ≤ r}
      = {x : Fin m → ℝ | (∑ j, |x j| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ √r} := by
    ext x
    have hs : (∑ j, |x j| ^ (2 : ℝ)) = ∑ j, (x j) ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have hnn : 0 ≤ ∑ j, (x j) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h2 : (∑ j, (x j) ^ 2) ^ (1 / (2 : ℝ)) = √(∑ j, (x j) ^ 2) :=
      (Real.sqrt_eq_rpow _).symm
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hs, h2]
    refine ⟨fun h => Real.sqrt_le_sqrt h, fun h => ?_⟩
    nlinarith [Real.sq_sqrt hnn, Real.sq_sqrt hr, Real.sqrt_nonneg (∑ j, (x j) ^ 2),
      Real.sqrt_nonneg r]
  rw [hset, MeasureTheory.volume_sum_rpow_le (Fin m) (p := 2) one_le_two (√r)]
  congr 1
  · simp
  · rw [Fintype.card_fin]
    congr 2
    rw [show (1 : ℝ) / 2 + 1 = 3 / 2 by norm_num,
      show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring

/-- **The volume of the relative-coordinate ellipsoid**:
`vol {x ∈ ℝ^m : Q(x) ≤ r} = √(m+1) · √π^m / Γ(m/2+1) · r^{m/2}`. -/
theorem volume_relQuad_le {m : ℕ} (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r) :
    volume {x : Fin m → ℝ | relQuad m x ≤ r}
      = ENNReal.ofReal (√((m : ℝ) + 1)) * (ENNReal.ofReal (√r) ^ m
        * ENNReal.ofReal (√π ^ m / Real.Gamma (m / 2 + 1))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set c : ℝ := (√((m : ℝ) + 1) - 1) / m with hc
  have hsq : √((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hcm : 1 + c * m = √((m : ℝ) + 1) := by
    rw [hc]; field_simp; ring
  have hc2 : 2 * c + c ^ 2 * m = 1 := by
    have h1 : c * m = √((m : ℝ) + 1) - 1 := by rw [hc]; field_simp
    have : c ^ 2 * m = c * (c * m) := by ring
    rw [this, h1]
    have : 2 * c + c * (√((m : ℝ) + 1) - 1) = c * (√((m : ℝ) + 1) + 1) := by ring
    rw [this, hc]
    field_simp
    nlinarith
  have hne : (1 : ℝ) + c * m ≠ 0 := by
    rw [hcm]
    positivity
  have himg : (shear m c) '' {x : Fin m → ℝ | ∑ j, (x j) ^ 2 ≤ r}
      = {y : Fin m → ℝ | relQuad m y ≤ r} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Set.mem_setOf_eq, relQuad_shear m c hc2 x]
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := shear_surjective m c hne y
      exact ⟨x, by rw [Set.mem_setOf_eq, ← relQuad_shear m c hc2 x]; exact hy, rfl⟩
  rw [← himg, Measure.addHaar_image_linearMap, det_shear, hcm,
    abs_of_nonneg (Real.sqrt_nonneg _), volume_sum_sq_le hm r hr]

end Q788
