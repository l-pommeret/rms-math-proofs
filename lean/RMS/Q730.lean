/-
# Q730

Let `M ∈ M_n(ℂ)` be of rank `r` and let `t₁, …, t_r > 0`.  When do there exist unitary
matrices `U, V` such that

`U * M * V = ⎡T B⎤`
`          ⎣0 0⎦`

with `T ∈ M_r(ℂ)` upper triangular with diagonal `(t₁, …, t_r)`?

The answer (Weyl–Horn):  writing `σ₁ ≥ … ≥ σ_r > 0` for the nonzero singular values of `M`
and `τ₁ ≥ … ≥ τ_r` for the decreasing rearrangement of `t₁, …, t_r`, such `U, V` exist iff

* `∏_{i≤k} τ_i ≤ ∏_{i≤k} σ_i` for all `k ≤ r`, and
* if `r = n` moreover `∏_{i≤n} t_i = |det M|`.

This file develops the required theory (singular value decomposition, the Weyl–Horn theorem,
Cauchy–Binet) from scratch and proves the classification.
-/

import Mathlib

open Matrix Finset BigOperators
open scoped ComplexOrder

namespace Q730

/-! ## Section 1 : one-row/one-column block decomposition of matrices over `Fin (n+1)` -/

variable {n m : ℕ}

/-- The matrix with corner entry `c`, first row `u` (right of the corner), first column `v`
(below the corner) and remaining block `C`. -/
def blk (c : ℂ) (u v : Fin n → ℂ) (C : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i j => Fin.cases (Fin.cases c u j) (fun i' => Fin.cases (v i') (C i') j) i

@[simp] lemma blk_zero_zero (c : ℂ) (u v : Fin n → ℂ) (C : Matrix (Fin n) (Fin n) ℂ) :
    blk c u v C 0 0 = c := rfl

@[simp] lemma blk_zero_succ (c : ℂ) (u v : Fin n → ℂ) (C : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    blk c u v C 0 j.succ = u j := rfl

@[simp] lemma blk_succ_zero (c : ℂ) (u v : Fin n → ℂ) (C : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    blk c u v C i.succ 0 = v i := rfl

@[simp] lemma blk_succ_succ (c : ℂ) (u v : Fin n → ℂ) (C : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) : blk c u v C i.succ j.succ = C i j := rfl

lemma blk_mul (c c' : ℂ) (u v u' v' : Fin n → ℂ) (C C' : Matrix (Fin n) (Fin n) ℂ) :
    blk c u v C * blk c' u' v' C' =
      blk (c * c' + u ⬝ᵥ v') (c • u' + u ᵥ* C') (c' • v + C *ᵥ v')
        (vecMulVec v u' + C * C') := by
  ext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · simp [Matrix.mul_apply, Fin.sum_univ_succ, dotProduct]
    · intro j'; simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct]
  · intro i'
    refine Fin.cases ?_ ?_ j
    · simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]; ring
    · intro j'; simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMulVec_apply]

lemma blk_conjTranspose (c : ℂ) (u v : Fin n → ℂ) (C : Matrix (Fin n) (Fin n) ℂ) :
    (blk c u v C)ᴴ = blk (starRingEnd ℂ c) (star v) (star u) Cᴴ := by
  ext i j
  refine Fin.cases ?_ ?_ i <;> [skip; intro i'] <;> refine Fin.cases ?_ ?_ j <;> intros <;>
    simp [Matrix.conjTranspose_apply]

@[simp] lemma blk_one : blk (1 : ℂ) 0 0 (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i j
  refine Fin.cases ?_ ?_ i <;> [skip; intro i'] <;> refine Fin.cases ?_ ?_ j <;> intros <;>
    simp [Matrix.one_apply, Fin.ext_iff]

lemma blk_add (c c' : ℂ) (u v u' v' : Fin n → ℂ) (C C' : Matrix (Fin n) (Fin n) ℂ) :
    blk c u v C + blk c' u' v' C' = blk (c + c') (u + u') (v + v') (C + C') := by
  ext i j
  refine Fin.cases ?_ ?_ i <;> [skip; intro i'] <;> refine Fin.cases ?_ ?_ j <;> intros <;> simp

lemma blk_diagonal (x : ℂ) (s : Fin n → ℂ) :
    diagonal (Fin.cons x s : Fin (n + 1) → ℂ) = blk x 0 0 (diagonal s) := by
  ext i j
  refine Fin.cases ?_ ?_ i <;> [skip; intro i'] <;> refine Fin.cases ?_ ?_ j <;> intros <;>
    simp [Matrix.diagonal_apply, Fin.ext_iff]

lemma blk_blockTriangular (c : ℂ) (u : Fin n → ℂ) (C : Matrix (Fin n) (Fin n) ℂ) :
    (blk c u 0 C).BlockTriangular id ↔ C.BlockTriangular id := by
  constructor
  · intro h i j hij
    have := h (i := i.succ) (j := j.succ) (by simpa [Fin.succ_lt_succ_iff] using hij)
    simpa using this
  · intro h i j hij
    induction i using Fin.cases with
    | zero => exact absurd hij (by simp)
    | succ i' =>
      induction j using Fin.cases with
      | zero => simp
      | succ j' => exact h (by simpa [Fin.succ_lt_succ_iff] using hij)

@[simp] lemma vecMulVec_zero_zero : vecMulVec (0 : Fin n → ℂ) (0 : Fin n → ℂ) = 0 := by
  ext i j; simp [vecMulVec_apply]

lemma blk_unitary {P : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ unitaryGroup (Fin n) ℂ) :
    blk 1 0 0 P ∈ unitaryGroup (Fin (n + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hP ⊢
  rw [Matrix.star_eq_conjTranspose] at hP ⊢
  rw [blk_conjTranspose, blk_mul]
  simp [hP]

/-! ### Vectors of the form `Fin.cons x 0` -/

lemma cons_dotProduct_cons (x y : ℂ) :
    (Fin.cons x 0 : Fin (n + 1) → ℂ) ⬝ᵥ (Fin.cons y 0 : Fin (n + 1) → ℂ) = x * y := by
  simp [dotProduct, Fin.sum_univ_succ]

lemma cons_vecMul_blk (x c : ℂ) (D : Matrix (Fin n) (Fin n) ℂ) :
    (Fin.cons x 0 : Fin (n + 1) → ℂ) ᵥ* blk c 0 0 D = Fin.cons (x * c) 0 := by
  funext j
  refine Fin.cases ?_ ?_ j <;> intros <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

lemma blk_mulVec_cons (y c : ℂ) (D : Matrix (Fin n) (Fin n) ℂ) :
    blk c 0 0 D *ᵥ (Fin.cons y 0 : Fin (n + 1) → ℂ) = Fin.cons (c * y) 0 := by
  funext j
  refine Fin.cases ?_ ?_ j <;> intros <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma vecMulVec_cons (x y : ℂ) :
    vecMulVec (Fin.cons x 0 : Fin (n + 1) → ℂ) (Fin.cons y 0 : Fin (n + 1) → ℂ)
      = blk (x * y) 0 0 0 := by
  ext i j
  refine Fin.cases ?_ ?_ i <;> [skip; intro i'] <;> refine Fin.cases ?_ ?_ j <;> intros <;>
    simp [vecMulVec_apply]

lemma smul_cons (c x : ℂ) : c • (Fin.cons x 0 : Fin (n + 1) → ℂ) = Fin.cons (c * x) 0 := by
  funext j; refine Fin.cases ?_ ?_ j <;> intros <;> simp

lemma cons_add_cons (x y : ℂ) :
    (Fin.cons x 0 : Fin (n + 1) → ℂ) + (Fin.cons y 0 : Fin (n + 1) → ℂ) = Fin.cons (x + y) 0 := by
  funext j; refine Fin.cases ?_ ?_ j <;> intros <;> simp

@[simp] lemma cons_zero_eq_zero : (Fin.cons (0 : ℂ) 0 : Fin (n + 1) → ℂ) = 0 := by
  funext j; refine Fin.cases ?_ ?_ j <;> intros <;> simp

lemma star_cons (x : ℂ) :
    star (Fin.cons x 0 : Fin (n + 1) → ℂ) = Fin.cons (starRingEnd ℂ x) 0 := by
  funext j; refine Fin.cases ?_ ?_ j <;> intros <;> simp

/-! ### Embedding a `2 × 2` matrix in the top-left corner -/

/-- The block matrix `W ⊕ 1`, with `W` a `2 × 2` matrix sitting in the top left corner. -/
def emb2 (m : ℕ) (W : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ :=
  blk (W 0 0) (Fin.cons (W 0 1) 0) (Fin.cons (W 1 0) 0) (blk (W 1 1) 0 0 1)

lemma emb2_mul (W W' : Matrix (Fin 2) (Fin 2) ℂ) :
    emb2 m (W * W') = emb2 m W * emb2 m W' := by
  rw [emb2, emb2, emb2, blk_mul, cons_dotProduct_cons, smul_cons, cons_vecMul_blk,
    cons_add_cons, smul_cons, blk_mulVec_cons, cons_add_cons, vecMulVec_cons, blk_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two, blk_add, mul_comm]

@[simp] lemma emb2_one : emb2 m 1 = 1 := by
  rw [emb2]
  simp

lemma emb2_conjTranspose (W : Matrix (Fin 2) (Fin 2) ℂ) : (emb2 m W)ᴴ = emb2 m Wᴴ := by
  rw [emb2, emb2, blk_conjTranspose, star_cons, star_cons, blk_conjTranspose]
  simp

lemma emb2_unitary {W : Matrix (Fin 2) (Fin 2) ℂ} (hW : W ∈ unitaryGroup (Fin 2) ℂ) :
    emb2 m W ∈ unitaryGroup (Fin (m + 2)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hW ⊢
  rw [emb2_conjTranspose, ← emb2_mul, hW, emb2_one]

/-! ## Section 2 : singular value decompositions -/

/-- `HasSV A s` says that `A = U * diagonal s * V` for unitary matrices `U`, `V`; that is,
the entries of `s` are the singular values of `A` (in the order given by `s`). -/
def HasSV (A : Matrix (Fin n) (Fin n) ℂ) (s : Fin n → ℝ) : Prop :=
  ∃ U V : Matrix (Fin n) (Fin n) ℂ, U ∈ unitaryGroup (Fin n) ℂ ∧ V ∈ unitaryGroup (Fin n) ℂ ∧
    A = U * diagonal (fun i => (s i : ℂ)) * V

lemma diagonal_comp_perm (d : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    diagonal (d ∘ σ) = σ.permMatrix ℂ * diagonal d * (σ⁻¹).permMatrix ℂ := by
  rw [Equiv.Perm.permMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  simp only [Equiv.Perm.inv_def, Equiv.symm_symm]
  exact (submatrix_diagonal_equiv d σ).symm

lemma permMatrix_unitary (σ : Equiv.Perm (Fin n)) : σ.permMatrix ℂ ∈ unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, conjTranspose_permMatrix,
    ← Matrix.permMatrix_mul]
  simp

lemma unitary_conjTranspose {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    Uᴴ ∈ unitaryGroup (Fin n) ℂ := by
  simpa [Matrix.star_eq_conjTranspose] using (Unitary.star_mem hU)

lemma HasSV.perm {A : Matrix (Fin n) (Fin n) ℂ} {s : Fin n → ℝ} (h : HasSV A s)
    (σ : Equiv.Perm (Fin n)) : HasSV A (s ∘ σ) := by
  obtain ⟨U, V, hU, hV, hA⟩ := h
  refine ⟨U * (σ.permMatrix ℂ)ᴴ, σ.permMatrix ℂ * V,
    Submonoid.mul_mem _ hU (unitary_conjTranspose (permMatrix_unitary σ)),
    Submonoid.mul_mem _ (permMatrix_unitary σ) hV, ?_⟩
  have h1 : (fun i => (((s ∘ σ) i : ℝ) : ℂ)) = (fun i => ((s i : ℝ) : ℂ)) ∘ σ := rfl
  have e1 : ((σ⁻¹).permMatrix ℂ) * (σ.permMatrix ℂ) = 1 := by
    rw [← Matrix.permMatrix_mul]; simp
  rw [h1, diagonal_comp_perm, conjTranspose_permMatrix, hA]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((σ⁻¹).permMatrix ℂ) (σ.permMatrix ℂ), e1, Matrix.one_mul,
    ← Matrix.mul_assoc ((σ⁻¹).permMatrix ℂ) (σ.permMatrix ℂ), e1, Matrix.one_mul]

lemma HasSV.mul_unitary {A : Matrix (Fin n) (Fin n) ℂ} {s : Fin n → ℝ} (h : HasSV A s)
    {P Q : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ unitaryGroup (Fin n) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) : HasSV (P * A * Q) s := by
  obtain ⟨U, V, hU, hV, hA⟩ := h
  exact ⟨P * U, V * Q, Submonoid.mul_mem _ hP hU, Submonoid.mul_mem _ hV hQ, by
    rw [hA]; simp [Matrix.mul_assoc]⟩

lemma norm_det_of_unitary {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    ‖U.det‖ = 1 := by
  have h := hU
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
  have : U.det * (starRingEnd ℂ) U.det = 1 := by
    have := congrArg Matrix.det h
    rwa [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this
  have h2 : ‖U.det‖ ^ 2 = 1 := by
    rw [sq]
    calc ‖U.det‖ * ‖U.det‖ = ‖U.det * (starRingEnd ℂ) U.det‖ := by
          rw [norm_mul, RCLike.norm_conj]
      _ = 1 := by rw [this]; simp
  nlinarith [norm_nonneg U.det, h2]

lemma HasSV.norm_det {A : Matrix (Fin n) (Fin n) ℂ} {s : Fin n → ℝ} (h : HasSV A s) :
    ‖A.det‖ = ∏ i, ‖s i‖ := by
  obtain ⟨U, V, hU, hV, hA⟩ := h
  rw [hA]
  rw [Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, norm_det_of_unitary hU,
    norm_det_of_unitary hV, Matrix.det_diagonal]
  simp [norm_prod]

lemma HasSV.trace_conjTranspose_mul_self {A : Matrix (Fin n) (Fin n) ℂ} {s : Fin n → ℝ}
    (h : HasSV A s) : (Aᴴ * A).trace = ((∑ i, (s i) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨U, V, hU, hV, hA⟩ := h
  have hU' : Uᴴ * U = 1 := by
    have := hU
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at this
    exact this
  have hV' : V * Vᴴ = 1 := by
    have := hV
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at this
    exact this
  have hd : (diagonal fun i => ((s i : ℝ) : ℂ))ᴴ * (diagonal fun i => ((s i : ℝ) : ℂ))
      = diagonal fun i => (((s i) ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; simp [sq]
  have key : Aᴴ * A = Vᴴ * ((diagonal fun i => (((s i) ^ 2 : ℝ) : ℂ)) * V) := by
    subst hA
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU', Matrix.one_mul, ← Matrix.mul_assoc _ _ V, hd]
  rw [key, Matrix.trace_mul_comm, Matrix.mul_assoc, hV', Matrix.mul_one, Matrix.trace_diagonal]
  push_cast
  ring

/-- If `Aᴴ * A` is unitarily diagonalized with nonnegative diagonal `e`, then the square roots
of the `e i` are the singular values of `A`.  (Construction of the singular value
decomposition.) -/
theorem hasSV_of_conjTranspose_mul_self {A U : Matrix (Fin n) (Fin n) ℂ} {e : Fin n → ℝ}
    (hU : U ∈ unitaryGroup (Fin n) ℂ) (he : ∀ i, 0 ≤ e i)
    (h : Aᴴ * A = U * diagonal (fun i => ((e i : ℝ) : ℂ)) * Uᴴ) :
    HasSV A (fun i => Real.sqrt (e i)) := by
  classical
  have hUU : Uᴴ * U = 1 := by
    have := hU; rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at this; exact this
  have hUU' : U * Uᴴ = 1 := by
    have := hU; rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at this; exact this
  set s : Fin n → ℝ := fun i => Real.sqrt (e i) with hs
  set B := A * U with hB
  have hBB : Bᴴ * B = diagonal (fun i => ((e i : ℝ) : ℂ)) := by
    rw [hB, Matrix.conjTranspose_mul]
    calc Uᴴ * Aᴴ * (A * U) = Uᴴ * (Aᴴ * A) * U := by simp [Matrix.mul_assoc]
      _ = Uᴴ * (U * diagonal (fun i => ((e i : ℝ) : ℂ)) * Uᴴ) * U := by rw [h]
      _ = (Uᴴ * U) * diagonal (fun i => ((e i : ℝ) : ℂ)) * (Uᴴ * U) := by
            simp [Matrix.mul_assoc]
      _ = diagonal (fun i => ((e i : ℝ) : ℂ)) := by rw [hUU]; simp
  have hcol : ∀ i j, ∑ p, (starRingEnd ℂ) (B p i) * B p j
      = if i = j then ((e i : ℝ) : ℂ) else 0 := by
    intro i j
    have := congrFun (congrFun hBB i) j
    rw [Matrix.mul_apply] at this
    simpa [Matrix.conjTranspose_apply, Matrix.diagonal_apply] using this
  have hzero : ∀ i, e i = 0 → ∀ p, B p i = 0 := by
    intro i hei p
    have h1 := hcol i i
    simp [hei] at h1
    have h2 : ∑ q, ‖B q i‖ ^ 2 = 0 := by
      have : ((∑ q, ‖B q i‖ ^ 2 : ℝ) : ℂ) = 0 := by rw [← h1]; push_cast; simp [RCLike.conj_mul]
      exact_mod_cast this
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => sq_nonneg ‖B q i‖)).1 h2 p (mem_univ p)
    simpa using this
  set S : Set (Fin n) := {i | e i ≠ 0} with hS
  set w : Fin n → EuclideanSpace ℂ (Fin n) :=
    fun i => (WithLp.toLp 2 (fun p => B p i / ((s i : ℝ) : ℂ))) with hw
  have hspos : ∀ i ∈ S, 0 < s i := fun i hi => Real.sqrt_pos.2 (lt_of_le_of_ne (he i) (Ne.symm hi))
  have hsq : ∀ i, ((s i : ℝ) : ℂ) * ((s i : ℝ) : ℂ) = ((e i : ℝ) : ℂ) := by
    intro i
    have : s i * s i = e i := by rw [hs]; simp [Real.mul_self_sqrt (he i)]
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this
  have horth : Orthonormal ℂ (S.restrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hsi := hspos i hi
    have hsj := hspos j hj
    have hsi' : ((s i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hsi
    have hsj' : ((s j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hsj
    rw [PiLp.inner_apply]
    simp only [Set.restrict_apply, hw, WithLp.ofLp_toLp, RCLike.inner_apply]
    have key : ∀ p : Fin n, B p j / ((s j : ℝ) : ℂ) * (starRingEnd ℂ) (B p i / ((s i : ℝ) : ℂ))
        = ((starRingEnd ℂ) (B p i) * B p j) / (((s i : ℝ) : ℂ) * ((s j : ℝ) : ℂ)) := by
      intro p
      rw [map_div₀, Complex.conj_ofReal]
      field_simp
    rw [Finset.sum_congr rfl (fun p _ => key p), ← Finset.sum_div, hcol i j]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, ← hsq i, div_self (mul_ne_zero hsi' hsi')]
      simp
    · rw [if_neg hij, zero_div]
      have : (⟨i, hi⟩ : S) ≠ ⟨j, hj⟩ := by simpa [Subtype.ext_iff] using hij
      rw [if_neg this]
  obtain ⟨bb, hbb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq (ι := Fin n) (by simp)
  set W : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun p i => (bb i) p) with hW
  have hWu : W ∈ unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext i j
    rw [Matrix.mul_apply]
    have : ∑ p, Wᴴ i p * W p j = (inner ℂ (bb i) (bb j) : ℂ) := by
      rw [PiLp.inner_apply]
      exact Finset.sum_congr rfl (fun p _ => by
        simp [hW, Matrix.conjTranspose_apply, RCLike.inner_apply, mul_comm])
    rw [this, bb.inner_eq_ite]
    simp [Matrix.one_apply]
  have hBW : B = W * diagonal (fun i => ((s i : ℝ) : ℂ)) := by
    ext p i
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single i (fun q _ hq => by rw [Matrix.diagonal_apply_ne _ hq, mul_zero])
      (by simp)]
    simp only [Matrix.diagonal_apply_eq, hW, Matrix.of_apply]
    by_cases hei : e i = 0
    · have hsi0 : s i = 0 := by rw [hs]; simp [hei]
      rw [hsi0, hzero i hei p]
      simp
    · have hiS : i ∈ S := hei
      have hsi' : ((s i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hspos i hiS)
      rw [hbb i hiS]
      simp only [hw, WithLp.ofLp_toLp]
      field_simp
  refine ⟨W, Uᴴ, hWu, ?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using (Unitary.star_mem hU)
  · rw [← hBW, hB, Matrix.mul_assoc, hUU', Matrix.mul_one]

/-- Every square complex matrix has a singular value decomposition. -/
theorem exists_hasSV (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ s : Fin n → ℝ, (∀ i, 0 ≤ s i) ∧ HasSV A s := by
  have hpsd := Matrix.posSemidef_conjTranspose_mul_self A
  have hH := hpsd.isHermitian
  refine ⟨fun i => Real.sqrt (hH.eigenvalues i), fun i => Real.sqrt_nonneg _, ?_⟩
  refine hasSV_of_conjTranspose_mul_self (U := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ))
    hH.eigenvectorUnitary.2 hpsd.eigenvalues_nonneg ?_
  conv_lhs => rw [hH.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]

/-! ## Section 3 : the Cauchy–Binet formula -/

section CauchyBinet

variable {R : Type*} [CommRing R] {k : ℕ}

lemma det_mul_expand_aux (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ p : Fin k → Fin n, ∑ σ : Equiv.Perm (Fin k),
      ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, A (σ i) (p i) * B (p i) i := by
  simp only [det_apply', Matrix.mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]

lemma det_mul_aux' {A : Matrix (Fin k) (Fin n) R} {B : Matrix (Fin n) (Fin k) R}
    {p : Fin k → Fin n} (H : ¬ Function.Injective p) :
    (∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : R) * ∏ x, A (σ x) (p x) * B (p x) x)
      = 0 := by
  obtain ⟨i, j, hpij, hij⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
    rw [Function.Injective] at H
    push_neg at H
    exact H
  exact Finset.sum_involution (fun σ _ => σ * Equiv.swap i j)
    (fun σ _ => by
      have : (∏ x, A (σ x) (p x)) = ∏ x, A ((σ * Equiv.swap i j) x) (p x) :=
        Fintype.prod_equiv (Equiv.swap i j) _ _ (by simp [Equiv.apply_swap_eq_self hpij])
      simp [this, Equiv.Perm.sign_swap hij, -Equiv.Perm.sign_swap', Finset.prod_mul_distrib])
    (fun σ _ _ => (not_congr Equiv.mul_swap_eq_iff).mpr hij) (fun _ _ => mem_univ _)
    fun σ _ => Equiv.mul_swap_involutive i j σ

lemma strictMono_ext {g g' : Fin k → Fin n} (hg : StrictMono g) (hg' : StrictMono g')
    (h : Finset.image g univ = Finset.image g' univ) : g = g' := by
  have hc : (Finset.image g univ).card = k := by
    rw [Finset.card_image_of_injective _ hg.injective]; simp
  have h1 : g = (Finset.image g univ).orderEmbOfFin hc :=
    Finset.orderEmbOfFin_unique hc (fun x => by simp) hg
  have h2 : g' = (Finset.image g univ).orderEmbOfFin hc :=
    Finset.orderEmbOfFin_unique hc (fun x => by rw [h]; simp) hg'
  rw [h1, h2]

lemma exists_strictMono_comp_perm {p : Fin k → Fin n} (hp : Function.Injective p) :
    ∃ (g : Fin k → Fin n) (τ : Equiv.Perm (Fin k)), StrictMono g ∧ p = g ∘ τ := by
  classical
  have hc : (Finset.image p univ).card = k := by
    rw [Finset.card_image_of_injective _ hp]; simp
  set g : Fin k → Fin n := ⇑((Finset.image p univ).orderEmbOfFin hc) with hg
  have hgmono : StrictMono g := (Finset.orderEmbOfFin _ hc).strictMono
  have hrange : ∀ i, ∃ j, g j = p i := by
    intro i
    have h1 : p i ∈ Finset.image g univ := by rw [hg, Finset.image_orderEmbOfFin_univ]; simp
    obtain ⟨j, _, hj⟩ := Finset.mem_image.1 h1
    exact ⟨j, hj⟩
  choose t ht using hrange
  have htinj : Function.Injective t := by
    intro a b hab; apply hp; rw [← ht a, ← ht b, hab]
  refine ⟨g, Equiv.ofBijective t (Finite.injective_iff_bijective.1 htinj), hgmono, ?_⟩
  funext i
  simp [Equiv.ofBijective, ht i]

lemma image_comp_perm (g : Fin k → Fin n) (τ : Equiv.Perm (Fin k)) :
    Finset.image (g ∘ τ) univ = Finset.image g univ := by
  rw [← Finset.image_image]
  congr 1
  exact Finset.image_univ_of_surjective τ.surjective

lemma sum_injective_eq_sum_strictMono {M : Type*} [AddCommMonoid M] (F : (Fin k → Fin n) → M) :
    ∑ p ∈ univ.filter (fun p : Fin k → Fin n => Function.Injective p), F p
      = ∑ g ∈ univ.filter (fun g : Fin k → Fin n => StrictMono g),
          ∑ τ : Equiv.Perm (Fin k), F (g ∘ τ) := by
  classical
  rw [← Finset.sum_product' (s := univ.filter (fun g : Fin k → Fin n => StrictMono g))
    (t := (univ : Finset (Equiv.Perm (Fin k)))) (f := fun g τ => F (g ∘ τ))]
  refine (Finset.sum_bij (fun x _ => x.1 ∘ x.2) ?_ ?_ ?_ ?_).symm
  · rintro ⟨g, τ⟩ hx
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hx.1.injective.comp τ.injective
  · rintro ⟨g, τ⟩ hx ⟨g', τ'⟩ hx' hh
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    simp only at hh
    have himg : Finset.image g univ = Finset.image g' univ := by
      rw [← image_comp_perm g τ, ← image_comp_perm g' τ', hh]
    have hgg : g = g' := strictMono_ext hx.1 hx'.1 himg
    subst hgg
    have hτ : ⇑τ = ⇑τ' := by
      funext i
      exact hx.1.injective (congrFun hh i)
    simp only [Prod.mk.injEq, true_and]
    exact Equiv.coe_fn_injective hτ
  · rintro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨g, τ, hg, hgt⟩ := exists_strictMono_comp_perm hp
    exact ⟨⟨g, τ⟩, by simp [Finset.mem_product, hg], hgt.symm⟩
  · rintro ⟨g, τ⟩ _
    rfl

lemma strictMono_self_eq_id {g : Fin k → Fin k} (hg : StrictMono g) : g = id := by
  refine strictMono_ext hg strictMono_id ?_
  have h1 : (Finset.image g univ).card = Fintype.card (Fin k) := by
    rw [Finset.card_image_of_injective _ hg.injective]; simp
  rw [Finset.eq_univ_of_card _ h1, Finset.image_id]

lemma filter_strictMono_fin :
    univ.filter (fun g : Fin k → Fin k => StrictMono g) = {id} := by
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨strictMono_self_eq_id, fun h => h ▸ strictMono_id⟩

lemma det_mul_expand_perm (M N : Matrix (Fin k) (Fin k) R) :
    (∑ τ : Equiv.Perm (Fin k), ∑ σ : Equiv.Perm (Fin k),
      ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, M (σ i) (τ i) * N (τ i) i) = M.det * N.det := by
  classical
  rw [← Matrix.det_mul, det_mul_expand_aux M N]
  rw [← Finset.sum_subset (Finset.filter_subset
      (fun p : Fin k → Fin k => Function.Injective p) univ)
    (fun p _ hp => det_mul_aux' (by simpa using hp))]
  rw [sum_injective_eq_sum_strictMono, filter_strictMono_fin]
  simp

/-- **Cauchy–Binet formula**. -/
theorem cauchy_binet (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ g ∈ univ.filter (fun g : Fin k → Fin n => StrictMono g),
      (A.submatrix id g).det * (B.submatrix g id).det := by
  classical
  rw [det_mul_expand_aux A B]
  rw [← Finset.sum_subset (Finset.filter_subset
      (fun p : Fin k → Fin n => Function.Injective p) univ)
    (fun p _ hp => det_mul_aux' (by simpa using hp))]
  rw [sum_injective_eq_sum_strictMono]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [← det_mul_expand_perm (A.submatrix id g) (B.submatrix g id)]
  rfl

end CauchyBinet

end Q730
