import RMS.Q730

/-!
# Q730, part d : the `2 × 2` building block

The singular values of `!![lam, mu; 0, d]` and the singular value decomposition of a matrix
which is a `2 × 2` block in the top-left corner and diagonal elsewhere.
-/

namespace Q730

open Matrix Finset BigOperators
open scoped ComplexOrder

variable {n m : ℕ}

/-- A `2 × 2` upper triangular matrix has singular values `x, y` as soon as the modulus of its
determinant is `x * y` and the trace of `AᴴA` is `x² + y²`. -/
theorem hasSV_two (lam : ℂ) (mu d x y : ℝ) (hd : 0 ≤ d) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h1 : ‖lam‖ * d = x * y) (h2 : ‖lam‖ ^ 2 + mu ^ 2 + d ^ 2 = x ^ 2 + y ^ 2) :
    HasSV !![lam, (mu : ℂ); 0, (d : ℂ)] ![x, y] := by
  set H : Matrix (Fin 2) (Fin 2) ℂ := !![lam, (mu : ℂ); 0, (d : ℂ)] with hH
  obtain ⟨z, hz0, hz⟩ := exists_hasSV H
  have hdet : z 0 * z 1 = x * y := by
    have h := hz.norm_det
    rw [hH] at h
    simp [Fin.prod_univ_two, Matrix.det_fin_two_of, abs_of_nonneg (hz0 0),
      abs_of_nonneg (hz0 1)] at h
    rw [abs_of_nonneg hd] at h
    rw [← h, h1]
  have htr : z 0 ^ 2 + z 1 ^ 2 = x ^ 2 + y ^ 2 := by
    have h := hz.trace_conjTranspose_mul_self
    rw [hH] at h
    simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_succ] at h
    have hc : (starRingEnd ℂ) lam * lam = ((‖lam‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj]
      norm_cast
      exact Complex.normSq_eq_norm_sq _
    rw [hc] at h
    have h' : (‖lam‖ ^ 2 : ℝ) + (mu * mu + d * d) = z 0 ^ 2 + z 1 ^ 2 := by exact_mod_cast h
    nlinarith [h', h2]
  have hcase : (z 0 = x ∧ z 1 = y) ∨ (z 0 = y ∧ z 1 = x) := by
    have hfac : (z 0 ^ 2 - x ^ 2) * (z 0 ^ 2 - y ^ 2) = 0 := by
      linear_combination (z 0 ^ 2) * htr - (z 0 * z 1 + x * y) * hdet
    rcases mul_eq_zero.1 hfac with h | h
    · left
      have hzx : z 0 = x := by nlinarith [hz0 0, hx, h]
      refine ⟨hzx, ?_⟩
      have hz1 : z 1 ^ 2 = y ^ 2 := by nlinarith [htr, hzx]
      nlinarith [hz0 1, hy, hz1]
    · right
      have hzy : z 0 = y := by nlinarith [hz0 0, hy, h]
      refine ⟨hzy, ?_⟩
      have hz1 : z 1 ^ 2 = x ^ 2 := by nlinarith [htr, hzy]
      nlinarith [hz0 1, hx, hz1]
  rcases hcase with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · have hzv : z = ![x, y] := by
      funext i
      fin_cases i <;> simpa using ‹_›
    rwa [hzv] at hz
  · have hp := hz.perm (Equiv.swap 0 1)
    have hzv : z ∘ (Equiv.swap (0 : Fin 2) 1) = ![x, y] := by
      funext i
      fin_cases i <;> simp [e0, e1]
    rwa [hzv] at hp

@[simp] lemma vecMulVec_zero_right (v : Fin m → ℂ) : vecMulVec v (0 : Fin m → ℂ) = 0 := by
  ext i j; simp [vecMulVec_apply]

lemma diagonal_split (s : Fin (m + 1) → ℂ) :
    diagonal s = blk (s 0) 0 0 (diagonal fun i => s i.succ) := by
  conv_lhs => rw [← Fin.cons_self_tail s]
  rw [blk_diagonal]
  rfl

/-- Multiplying a diagonal matrix on both sides by `2 × 2` unitaries acting on the first two
coordinates. -/
lemma emb2_mul_diagonal_mul_emb2 (U V : Matrix (Fin 2) (Fin 2) ℂ) (s : Fin (m + 2) → ℂ) :
    emb2 m U * diagonal s * emb2 m V =
      blk ((U * !![s 0, 0; 0, s 1] * V) 0 0) (Fin.cons ((U * !![s 0, 0; 0, s 1] * V) 0 1) 0)
        (Fin.cons ((U * !![s 0, 0; 0, s 1] * V) 1 0) 0)
        (blk ((U * !![s 0, 0; 0, s 1] * V) 1 1) 0 0 (diagonal fun i => s i.succ.succ)) := by
  have h1 : diagonal s = blk (s 0) 0 0 (blk (s 1) 0 0 (diagonal fun i => s i.succ.succ)) := by
    rw [diagonal_split s, diagonal_split (fun i : Fin (m + 1) => s i.succ)]
    rfl
  have e00 : (U * !![s 0, 0; 0, s 1] * V) 0 0 = U 0 0 * s 0 * V 0 0 + U 0 1 * s 1 * V 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (U * !![s 0, 0; 0, s 1] * V) 0 1 = U 0 0 * s 0 * V 0 1 + U 0 1 * s 1 * V 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (U * !![s 0, 0; 0, s 1] * V) 1 0 = V 0 0 * (s 0 * U 1 0) + U 1 1 * s 1 * V 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  have e11 : (U * !![s 0, 0; 0, s 1] * V) 1 1 = s 0 * U 1 0 * V 0 1 + U 1 1 * s 1 * V 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm, mul_left_comm]
  rw [h1, emb2, emb2, blk_mul, e00, e01, e10, e11]
  simp only [dotProduct_zero, smul_zero, zero_add, add_zero, Matrix.mulVec_zero,
    vecMulVec_zero_right, blk_mul, Matrix.zero_vecMul, Matrix.one_mul, Matrix.mul_one,
    cons_vecMul_blk, smul_cons, cons_dotProduct_cons, blk_mulVec_cons, cons_add_cons,
    vecMulVec_cons, blk_add]

/-- A matrix which has a `2 × 2` block `H` in the top-left corner and is diagonal (with
entries `e`) elsewhere has as singular values those of `H` followed by `e`. -/
theorem hasSV_blk_two (H : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℝ) (hH : HasSV H x)
    (e : Fin m → ℝ) (s : Fin (m + 2) → ℝ) (hs0 : s 0 = x 0) (hs1 : s 1 = x 1)
    (hse : ∀ i : Fin m, s i.succ.succ = e i) :
    HasSV (blk (H 0 0) (Fin.cons (H 0 1) 0) (Fin.cons (H 1 0) 0)
      (blk (H 1 1) 0 0 (diagonal fun i => (e i : ℂ)))) s := by
  obtain ⟨U, V, hU, hV, hHeq⟩ := hH
  refine ⟨emb2 m U, emb2 m V, emb2_unitary hU, emb2_unitary hV, ?_⟩
  rw [emb2_mul_diagonal_mul_emb2 U V (fun i => (s i : ℂ))]
  have hK : U * !![((s 0 : ℝ) : ℂ), 0; 0, ((s 1 : ℝ) : ℂ)] * V = H := by
    rw [hHeq, hs0, hs1]
    congr 1
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hK]
  congr 1
  ext i j
  simp [hse]

end Q730
