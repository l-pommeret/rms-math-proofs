import RMS.Q857

/-!
# Q857 — auxiliary toolkit for the arbitrary-phase complex lower bound

This module collects the technical ingredients needed for the structural theorem on a nearest
determinant-`τ` matrix (Lemma 3.1 of the source note):

* elementary facts on the singular values `Q857.svals` (comparison with the operator norm, the
  top singular value, unitary invariance, and the fact that a matrix all of whose singular
  values are equal to `r` is `r` times a unitary matrix);
* perturbation bounds for the determinant: `‖det (B + t • C) - det B‖ = O(t)`, improved to
  `O(t²)` when the direction `C` is tangent to the determinant level set at `B`;
* an exact rank-one determinant correction lemma, used to restore the determinant after moving
  in a descent direction.
-/

namespace Q857

open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexOrder

section Svals

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The operator norm is the largest singular value. -/
lemma norm_eq_mx_svals (hn : 0 < n) (A : Matrix (Fin n) (Fin n) 𝕜) : ‖A‖ = mx (svals A) := by
  obtain ⟨U, V, hU, hV, hA⟩ := exists_svd_svals A
  have hV' : Vᴴ ∈ Matrix.unitaryGroup (Fin n) 𝕜 := by
    have := Unitary.star_mem hV; rwa [Matrix.star_eq_conjTranspose] at this
  have h1 : ‖A‖ = ‖(diagonal (fun i => ((svals A i : ℝ) : 𝕜)))‖ := by
    conv_lhs => rw [hA]
    rw [norm_mul_unitary hn hV', norm_unitary_mul hn hU]
  rw [h1, norm_diagonal_eq_mx hn]
  congr 1
  funext i
  rw [RCLike.norm_ofReal, abs_of_nonneg (svals_nonneg A i)]

/-- Every singular value is at most the operator norm. -/
lemma svals_le_norm (hn : 0 < n) (A : Matrix (Fin n) (Fin n) 𝕜) (i : Fin n) :
    svals A i ≤ ‖A‖ := by
  rw [norm_eq_mx_svals hn]; exact le_mx _ i

/-- The largest singular value is the operator norm. -/
lemma svals_zero_eq_norm (hn : 0 < n) (A : Matrix (Fin n) (Fin n) 𝕜) :
    svals A ⟨0, hn⟩ = ‖A‖ := by
  rw [norm_eq_mx_svals hn]
  refine le_antisymm (le_mx _ _) (mx_le hn (fun i => svals_antitone A ?_))
  simp [Fin.le_def]

/-- Singular values are invariant under multiplication by a unitary matrix on the left. -/
lemma svals_unitary_mul {Q : Matrix (Fin n) (Fin n) 𝕜}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜) :
    svals (Q * A) = svals A := by
  obtain ⟨U, V, hU, hV, hA⟩ := exists_svd_svals A
  refine svals_eq_of_svd (U := Q * U) (V := V) (mul_mem hQ hU) hV
    (svals_nonneg A) (svals_antitone A) ?_
  conv_lhs => rw [hA]
  noncomm_ring

/-- Singular values are invariant under a two-sided unitary change of basis. -/
lemma svals_conj (hn : 0 < n) {U V : Matrix (Fin n) (Fin n) 𝕜}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) 𝕜) (hV : V ∈ Matrix.unitaryGroup (Fin n) 𝕜)
    (A : Matrix (Fin n) (Fin n) 𝕜) : svals (U * A * Vᴴ) = svals A := by
  funext i
  simp only [svals]
  exact sv_conj hn hU hV A _

/-- If all singular values of `A` equal `r` then `A = r • Q` for a unitary `Q`. -/
lemma exists_unitary_of_svals_const (A : Matrix (Fin n) (Fin n) 𝕜) {r : ℝ}
    (h : ∀ i, svals A i = r) :
    ∃ Q : Matrix (Fin n) (Fin n) 𝕜, Q ∈ Matrix.unitaryGroup (Fin n) 𝕜 ∧
      A = ((r : ℝ) : 𝕜) • Q := by
  obtain ⟨U, V, hU, hV, hA⟩ := exists_svd_svals A
  have hV' : Vᴴ ∈ Matrix.unitaryGroup (Fin n) 𝕜 := by
    have := Unitary.star_mem hV; rwa [Matrix.star_eq_conjTranspose] at this
  refine ⟨U * Vᴴ, mul_mem hU hV', ?_⟩
  have hd : (diagonal (fun i => ((svals A i : ℝ) : 𝕜)))
      = ((r : ℝ) : 𝕜) • (1 : Matrix (Fin n) (Fin n) 𝕜) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul]
    congr 1
    funext i
    simp [h i]
  rw [hA, hd, Matrix.mul_smul, Matrix.smul_mul, mul_one]

end Svals

section Det

variable {n : ℕ}

/-- Expansion of the determinant along a direction: the error after the linear term is `O(t²)`
uniformly for `t ∈ [0, 1]`. -/
lemma det_add_smul_expand (B C : Matrix (Fin n) (Fin n) ℂ) (hB : B.det ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖(B + (t : ℂ) • C).det - B.det - (B⁻¹ * C).trace * B.det * (t : ℂ)‖ ≤ K * t ^ 2 := by
  classical
  set Z : Matrix (Fin n) (Fin n) ℂ := B⁻¹ * C with hZ
  have hBinv : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB)
  have hfac : ∀ t : ℝ, B + (t : ℂ) • C = B * (1 + (t : ℂ) • Z) := by
    intro t
    rw [Matrix.mul_add, mul_one, Matrix.mul_smul, hZ, ← Matrix.mul_assoc, hBinv, one_mul]
  set p : Polynomial ℂ :=
    ((1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) +
      (Polynomial.X : Polynomial ℂ) • Z.map (⇑(Polynomial.C (R := ℂ)))).det.divX.divX with hp
  have hdet : ∀ t : ℝ, (B + (t : ℂ) • C).det
      = B.det * (1 + Z.trace * (t : ℂ) + Polynomial.eval ((t : ℝ) : ℂ) p * ((t : ℝ) : ℂ) ^ 2) := by
    intro t
    rw [hfac t, Matrix.det_mul, Matrix.det_one_add_smul]
  have hcont : ContinuousOn (fun t : ℝ => ‖Polynomial.eval ((t : ℝ) : ℂ) p‖) (Set.Icc 0 1) := by
    fun_prop
  obtain ⟨t₀, ht₀, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    ⟨0, by norm_num⟩ hcont
  refine ⟨‖B.det‖ * ‖Polynomial.eval ((t₀ : ℝ) : ℂ) p‖, by positivity, ?_⟩
  intro t ht0 ht1
  have h1 : (B + (t : ℂ) • C).det - B.det - Z.trace * B.det * (t : ℂ)
      = B.det * (Polynomial.eval ((t : ℝ) : ℂ) p * ((t : ℝ) : ℂ) ^ 2) := by
    rw [hdet t]; ring
  rw [h1, norm_mul, norm_mul, norm_pow]
  have h2 : ‖Polynomial.eval ((t : ℝ) : ℂ) p‖ ≤ ‖Polynomial.eval ((t₀ : ℝ) : ℂ) p‖ :=
    hmax ⟨ht0, ht1⟩
  have h3 : ‖((t : ℝ) : ℂ)‖ = t := by simp [abs_of_nonneg ht0]
  rw [h3, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (by positivity))
    (norm_nonneg B.det)

/-- A first-order perturbation bound for the determinant. -/
lemma det_add_smul_bound (B C : Matrix (Fin n) (Fin n) ℂ) (hB : B.det ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖(B + (t : ℂ) • C).det - B.det‖ ≤ K * t := by
  obtain ⟨K, hK0, hK⟩ := det_add_smul_expand B C hB
  refine ⟨K + ‖(B⁻¹ * C).trace * B.det‖, by positivity, ?_⟩
  intro t ht0 ht1
  have h1 := hK t ht0 ht1
  have h2 : ‖(B + (t : ℂ) • C).det - B.det‖ ≤
      ‖(B + (t : ℂ) • C).det - B.det - (B⁻¹ * C).trace * B.det * (t : ℂ)‖
        + ‖(B⁻¹ * C).trace * B.det * ((t : ℝ) : ℂ)‖ := by
    have := norm_add_le ((B + (t : ℂ) • C).det - B.det - (B⁻¹ * C).trace * B.det * (t : ℂ))
      ((B⁻¹ * C).trace * B.det * ((t : ℝ) : ℂ))
    simpa using this
  have h3 : ‖(B⁻¹ * C).trace * B.det * ((t : ℝ) : ℂ)‖ = ‖(B⁻¹ * C).trace * B.det‖ * t := by
    rw [norm_mul]; congr 1; simp [abs_of_nonneg ht0]
  have h4 : t ^ 2 ≤ t := by nlinarith
  nlinarith [norm_nonneg ((B + (t : ℂ) • C).det - B.det)]

/-- A second-order perturbation bound for the determinant in a tangent direction. -/
lemma det_add_smul_bound_tangent (B C : Matrix (Fin n) (Fin n) ℂ) (hB : B.det ≠ 0)
    (htr : (B⁻¹ * C).trace = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖(B + (t : ℂ) • C).det - B.det‖ ≤ K * t ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := det_add_smul_expand B C hB
  refine ⟨K, hK0, fun t ht0 ht1 => ?_⟩
  have := hK t ht0 ht1
  rwa [htr, zero_mul, zero_mul, sub_zero] at this

end Det

section RankOne

variable {n : ℕ}

lemma mul_vecMulVec (Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) :
    Y * vecMulVec a b = vecMulVec (Y *ᵥ a) b := by
  ext i j
  simp [Matrix.mul_apply, vecMulVec, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

lemma smul_vecMulVec (c : ℂ) (a b : Fin n → ℂ) :
    c • vecMulVec a b = vecMulVec (c • a) b := by
  ext i j
  simp [vecMulVec, mul_assoc]

lemma vecMulVec_mulVec (a b w : Fin n → ℂ) :
    (vecMulVec a b) *ᵥ w = (b ⬝ᵥ w) • a := by
  ext i
  simp [vecMulVec, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

lemma det_one_add_vecMulVec (a b : Fin n → ℂ) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + vecMulVec a b).det = 1 + b ⬝ᵥ a := by
  rw [Matrix.vecMulVec_eq (Fin 1)]
  exact det_one_add_replicateCol_mul_replicateRow a b

lemma dotProduct_star_self (y : Fin n → ℂ) :
    (star y ⬝ᵥ y) = ((‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n))‖ ^ 2 : ℝ) : ℂ) := by
  have h : ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n))‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  rw [h]
  push_cast
  simp [dotProduct, Complex.conj_mul']

/-- Exact rank-one determinant correction: the determinant of an invertible matrix `Y` can be
multiplied by any factor `1 + β` by adding a rank-one matrix whose range is the line spanned by
a prescribed unit vector `v`, at a cost `‖β‖ * ‖Y‖` in operator norm. -/
lemma exists_det_fix (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.det ≠ 0)
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖ = 1) (β : ℂ) :
    ∃ (z : EuclideanSpace ℂ (Fin n)) (D : Matrix (Fin n) (Fin n) ℂ),
      (Y + D).det = Y.det * (1 + β) ∧ ‖z‖ ≤ ‖β‖ * ‖Y‖ ∧
      ∀ w : EuclideanSpace ℂ (Fin n), app D w = (inner ℂ z w : ℂ) • v := by
  classical
  set yv : Fin n → ℂ := Y⁻¹ *ᵥ (WithLp.ofLp v) with hyv
  set y : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 yv with hy
  have hYyv : Y *ᵥ yv = WithLp.ofLp v := by
    rw [hyv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Y (isUnit_iff_ne_zero.mpr hY),
      Matrix.one_mulVec]
  have hYy : app Y y = v := by
    rw [app_eq_zero_of_mulVec]
    show WithLp.toLp 2 (Y *ᵥ yv) = v
    rw [hYyv]
  have h1 : (1 : ℝ) ≤ ‖Y‖ * ‖y‖ := by
    have := norm_app_le Y y
    rw [hYy, hv] at this
    exact this
  have hynorm : 0 < ‖y‖ := by
    rcases eq_or_lt_of_le (norm_nonneg y) with h | h
    · exfalso; rw [← h, mul_zero] at h1; linarith
    · exact h
  set c : ℂ := β / ((‖y‖ ^ 2 : ℝ) : ℂ) with hc
  have hnormsq : ((‖y‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  refine ⟨(starRingEnd ℂ) c • y, c • vecMulVec (WithLp.ofLp v) (star yv), ?_, ?_, ?_⟩
  · have hfac : Y + c • vecMulVec (WithLp.ofLp v) (star yv)
        = Y * (1 + c • vecMulVec yv (star yv)) := by
      rw [Matrix.mul_add, mul_one, Matrix.mul_smul, mul_vecMulVec, hYyv]
    rw [hfac, Matrix.det_mul, smul_vecMulVec, det_one_add_vecMulVec]
    congr 1
    have hh : star yv ⬝ᵥ (c • yv) = c * (star yv ⬝ᵥ yv) := by
      rw [dotProduct, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    rw [hh, dotProduct_star_self, ← hy, hc]
    field_simp
  · rw [norm_smul]
    simp only [RCLike.norm_conj]
    have hcnorm : ‖c‖ = ‖β‖ / ‖y‖ ^ 2 := by
      rw [hc, norm_div]
      congr 1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hcnorm, div_mul_eq_mul_div, pow_two, mul_div_assoc]
    have h2 : ‖y‖ / (‖y‖ * ‖y‖) = 1 / ‖y‖ := by field_simp
    rw [h2, mul_one_div, div_le_iff₀ hynorm]
    calc ‖β‖ = ‖β‖ * 1 := by ring
      _ ≤ ‖β‖ * (‖Y‖ * ‖y‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg β)
      _ = ‖β‖ * ‖Y‖ * ‖y‖ := by ring
  · intro w
    rw [app_eq_zero_of_mulVec]
    show WithLp.toLp 2 ((c • vecMulVec (WithLp.ofLp v) (star yv)) *ᵥ (WithLp.ofLp w)) = _
    rw [smul_mulVec, vecMulVec_mulVec]
    have hinner : (inner ℂ ((starRingEnd ℂ) c • y) w : ℂ) = c * (star yv ⬝ᵥ WithLp.ofLp w) := by
      rw [inner_smul_left]
      simp only [starRingEnd_self_apply, PiLp.inner_apply, RCLike.inner_apply,
        dotProduct, Finset.mul_sum, hy]
      exact Finset.sum_congr rfl (fun i _ => by simp [mul_comm])
    rw [hinner, smul_smul]
    rfl

end RankOne

end Q857
