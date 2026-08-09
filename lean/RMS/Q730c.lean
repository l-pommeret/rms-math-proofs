import RMS.Q730

/-!
# Q730, part c : reordering the diagonal of an upper triangular matrix

Any prescribed permutation of the diagonal of an upper triangular matrix can be achieved by a
unitary conjugation which preserves upper triangularity (a Schur-type rotation).
-/

namespace Q730

open Matrix Finset BigOperators
open scoped ComplexOrder

variable {n m : ℕ}

/-! ### The `2 × 2` rotation -/

theorem swap_two_aux (a p q : ℂ) (t : ℝ)
    (hnorm : (t : ℂ) ^ 2 * ((starRingEnd ℂ) p * p + (starRingEnd ℂ) q * q) = 1) :
    (!![(t : ℂ) * p, -((t : ℂ) * (starRingEnd ℂ) q); (t : ℂ) * q, (t : ℂ) * (starRingEnd ℂ) p] :
      Matrix (Fin 2) (Fin 2) ℂ) ∈ unitaryGroup (Fin 2) ℂ ∧
    (!![(t : ℂ) * p, -((t : ℂ) * (starRingEnd ℂ) q); (t : ℂ) * q, (t : ℂ) * (starRingEnd ℂ) p] :
        Matrix (Fin 2) (Fin 2) ℂ)ᴴ * !![a, p; 0, a + q] *
      !![(t : ℂ) * p, -((t : ℂ) * (starRingEnd ℂ) q); (t : ℂ) * q, (t : ℂ) * (starRingEnd ℂ) p]
      = !![a + q, (starRingEnd ℂ) p; 0, a] := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
      first
        | ring1
        | linear_combination hnorm
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
      first
        | ring1
        | linear_combination (a + q) * hnorm
        | linear_combination a * hnorm
        | linear_combination ((starRingEnd ℂ) p) * hnorm

/-- The `2 × 2` case: the diagonal of an upper triangular `2 × 2` matrix can be swapped by a
unitary conjugation. -/
theorem exists_unitary_swap_two (a b c : ℂ) :
    ∃ W ∈ unitaryGroup (Fin 2) ℂ, ∃ b' : ℂ, Wᴴ * !![a, b; 0, c] * W = !![c, b'; 0, a] := by
  by_cases hN : b = 0 ∧ c = a
  · refine ⟨1, Submonoid.one_mem _, b, ?_⟩
    rw [hN.1, hN.2]
    simp
  · have hNpos : 0 < ‖b‖ ^ 2 + ‖c - a‖ ^ 2 := by
      rcases not_and_or.1 hN with h | h
      · have : ‖b‖ ≠ 0 := by simpa using h
        positivity
      · have : ‖c - a‖ ≠ 0 := by
          simp only [ne_eq, norm_eq_zero, sub_eq_zero]
          exact h
        positivity
    have hnorm : ((1 / Real.sqrt (‖b‖ ^ 2 + ‖c - a‖ ^ 2) : ℝ) : ℂ) ^ 2 *
        ((starRingEnd ℂ) b * b + (starRingEnd ℂ) (c - a) * (c - a)) = 1 := by
      have hbb : (starRingEnd ℂ) b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj]; norm_cast; exact Complex.normSq_eq_norm_sq _
      have hqq : (starRingEnd ℂ) (c - a) * (c - a) = ((‖c - a‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj]; norm_cast; exact Complex.normSq_eq_norm_sq _
      rw [hbb, hqq]
      have h1 : (1 / Real.sqrt (‖b‖ ^ 2 + ‖c - a‖ ^ 2)) ^ 2 * (‖b‖ ^ 2 + ‖c - a‖ ^ 2) = 1 := by
        field_simp
        rw [Real.sq_sqrt hNpos.le]
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h1
    obtain ⟨hu, heq⟩ := swap_two_aux a b (c - a) (1 / Real.sqrt (‖b‖ ^ 2 + ‖c - a‖ ^ 2)) hnorm
    refine ⟨_, hu, (starRingEnd ℂ) b, ?_⟩
    have hac : a + (c - a) = c := by ring
    rw [hac] at heq
    exact heq

/-! ### More block calculus -/

lemma cons_dotProduct_cons' (x y : ℂ) (u v : Fin m → ℂ) :
    (Fin.cons x u : Fin (m + 1) → ℂ) ⬝ᵥ (Fin.cons y v : Fin (m + 1) → ℂ) = x * y + u ⬝ᵥ v := by
  simp [dotProduct, Fin.sum_univ_succ]

lemma cons_vecMul_blk' (x : ℂ) (u : Fin m → ℂ) (c : ℂ) (w z : Fin m → ℂ)
    (D : Matrix (Fin m) (Fin m) ℂ) :
    (Fin.cons x u : Fin (m + 1) → ℂ) ᵥ* blk c w z D
      = Fin.cons (x * c + u ⬝ᵥ z) (x • w + u ᵥ* D) := by
  funext j
  refine Fin.cases ?_ ?_ j <;> intros <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

lemma blk_mulVec_cons' (y : ℂ) (v : Fin m → ℂ) (c : ℂ) (w z : Fin m → ℂ)
    (D : Matrix (Fin m) (Fin m) ℂ) :
    blk c w z D *ᵥ (Fin.cons y v : Fin (m + 1) → ℂ)
      = Fin.cons (c * y + w ⬝ᵥ v) (y • z + D *ᵥ v) := by
  funext j
  refine Fin.cases ?_ ?_ j <;> intros <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]

lemma vecMulVec_cons' (x y : ℂ) (u v : Fin m → ℂ) :
    vecMulVec (Fin.cons x u : Fin (m + 1) → ℂ) (Fin.cons y v : Fin (m + 1) → ℂ)
      = blk (x * y) (x • v) (y • u) (vecMulVec u v) := by
  ext i j
  refine Fin.cases ?_ ?_ i <;> [skip; intro i'] <;> refine Fin.cases ?_ ?_ j <;> intros <;>
    simp [vecMulVec_apply, mul_comm]

lemma smul_cons' (c x : ℂ) (u : Fin m → ℂ) :
    c • (Fin.cons x u : Fin (m + 1) → ℂ) = Fin.cons (c * x) (c • u) := by
  funext j; refine Fin.cases ?_ ?_ j <;> intros <;> simp

lemma cons_add_cons' (x y : ℂ) (u v : Fin m → ℂ) :
    (Fin.cons x u : Fin (m + 1) → ℂ) + (Fin.cons y v : Fin (m + 1) → ℂ)
      = Fin.cons (x + y) (u + v) := by
  funext j; refine Fin.cases ?_ ?_ j <;> intros <;> simp

@[simp] lemma vecMulVec_zero_left (v : Fin m → ℂ) : vecMulVec (0 : Fin m → ℂ) v = 0 := by
  ext i j; simp [vecMulVec_apply]

/-- Block form with a `2 × 2` corner `H`, top-right block `B`, bottom-right block `D` and zero
bottom-left block. -/
def blkTR (H : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin m) ℂ)
    (D : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ :=
  blk (H 0 0) (Fin.cons (H 0 1) (B 0)) (Fin.cons (H 1 0) 0) (blk (H 1 1) (B 1) 0 D)

lemma blkTR_mul (H H' : Matrix (Fin 2) (Fin 2) ℂ) (B B' : Matrix (Fin 2) (Fin m) ℂ)
    (D D' : Matrix (Fin m) (Fin m) ℂ) :
    blkTR H B D * blkTR H' B' D' = blkTR (H * H') (H * B' + B * D') (D * D') := by
  have e : ∀ i j : Fin 2, (H * H') i j = H i 0 * H' 0 j + H i 1 * H' 1 j := by
    intro i j; simp [Matrix.mul_apply, Fin.sum_univ_two]
  have f : ∀ i : Fin 2, (H * B' + B * D') i = H i 0 • B' 0 + (H i 1 • B' 1 + B i ᵥ* D') := by
    intro i; funext j
    simp [Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    ring
  rw [blkTR, blkTR, blkTR, blk_mul]
  simp only [cons_dotProduct_cons', cons_vecMul_blk', smul_cons', cons_add_cons',
    blk_mulVec_cons', vecMulVec_cons', blk_mul, blk_add, dotProduct_zero, add_zero,
    smul_zero, Matrix.mulVec_zero, vecMulVec_zero_left, zero_add, e, f, mul_comm]

lemma emb2_eq_blkTR (W : Matrix (Fin 2) (Fin 2) ℂ) : emb2 m W = blkTR W 0 1 := rfl

lemma emb2_conj_blkTR (W W' H : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin m) ℂ)
    (D : Matrix (Fin m) (Fin m) ℂ) :
    emb2 m W * blkTR H B D * emb2 m W' = blkTR (W * H * W') (W * B) D := by
  rw [emb2_eq_blkTR, emb2_eq_blkTR, blkTR_mul, blkTR_mul]
  simp

@[simp] lemma blkTR_zero_zero (H : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin m) ℂ)
    (D : Matrix (Fin m) (Fin m) ℂ) : blkTR H B D 0 0 = H 0 0 := rfl

@[simp] lemma blkTR_one_one (H : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin m) ℂ)
    (D : Matrix (Fin m) (Fin m) ℂ) : blkTR H B D 1 1 = H 1 1 := rfl

@[simp] lemma blkTR_succ_succ (H : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin m) ℂ)
    (D : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    blkTR H B D i.succ.succ j.succ.succ = D i j := rfl

lemma blkTR_blockTriangular {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H 1 0 = 0)
    (B : Matrix (Fin 2) (Fin m) ℂ) {D : Matrix (Fin m) (Fin m) ℂ} (hD : D.BlockTriangular id) :
    (blkTR H B D).BlockTriangular id := by
  rw [blkTR, hH, cons_zero_eq_zero, blk_blockTriangular, blk_blockTriangular]
  exact hD

/-- Every upper triangular matrix of size `m + 2` is in `blkTR` form. -/
lemma blkTR_decomp (A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) (htri : A.BlockTriangular id) :
    A = blkTR !![A 0 0, A 0 1; 0, A 1 1] (Matrix.of fun i j => A (![0, 1] i) j.succ.succ)
      (A.submatrix (fun i : Fin m => i.succ.succ) fun j : Fin m => j.succ.succ) := by
  ext i j
  refine Fin.cases ?_ ?_ i <;> [skip; intro i₁] <;>
    [refine Fin.cases ?_ ?_ j; refine Fin.cases ?_ ?_ i₁] <;> intros
  · rfl
  · rename_i j₁
    refine Fin.cases ?_ ?_ j₁ <;> intros <;> rfl
  · refine Fin.cases ?_ ?_ j <;> [skip; intro j₁]
    · exact htri (by simp [Fin.lt_def])
    · refine Fin.cases ?_ ?_ j₁ <;> intros <;> rfl
  · rename_i i₂
    refine Fin.cases ?_ ?_ j <;> [skip; intro j₁]
    · exact htri (by simp [Fin.lt_def])
    · refine Fin.cases ?_ ?_ j₁ <;> intros
      · exact htri (by simp [Fin.lt_def, Fin.val_succ])
      · rfl

/-! ### Swapping two adjacent diagonal entries -/

lemma blk_decomp (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (h : ∀ k : Fin m, A k.succ 0 = 0) :
    A = blk (A 0 0) (fun k => A 0 k.succ) 0 (A.submatrix Fin.succ Fin.succ) := by
  ext i j
  refine Fin.cases ?_ ?_ i <;> [skip; intro i'] <;> refine Fin.cases ?_ ?_ j <;> intros
  · rfl
  · rfl
  · exact h i'
  · rfl

lemma swap_succ_succ (i j k : Fin m) :
    Equiv.swap i.succ j.succ k.succ = (Equiv.swap i j k).succ := by
  by_cases h1 : k = i
  · subst h1; simp
  · by_cases h2 : k = j
    · subst h2; simp
    · rw [Equiv.swap_apply_of_ne_of_ne (by simpa using h1) (by simpa using h2),
        Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem exists_unitary_conj_swap_adj : ∀ (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ),
    A.BlockTriangular id → ∀ i j : Fin N, (j : ℕ) = (i : ℕ) + 1 →
    ∃ W ∈ unitaryGroup (Fin N) ℂ, (Wᴴ * A * W).BlockTriangular id ∧
      ∀ k, (Wᴴ * A * W) k k = A (Equiv.swap i j k) (Equiv.swap i j k) := by
  intro N
  induction N with
  | zero => intro A _ i; exact i.elim0
  | succ p ih =>
    intro A htri i j hij
    induction i using Fin.cases with
    | zero =>
      -- `j = 1`, so `p = m + 1`
      have hj1 : (j : ℕ) = 1 := by simpa using hij
      obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := j.2; omega⟩
      have hjeq : j = 1 := by
        apply Fin.ext
        simp [hj1]
      subst hjeq
      obtain ⟨W₂, hW₂, b', hW₂eq⟩ := exists_unitary_swap_two (A 0 0) (A 0 1) (A 1 1)
      have hA10 : A 1 0 = 0 := htri (by simp [Fin.lt_def])
      set B : Matrix (Fin 2) (Fin m) ℂ := Matrix.of fun i j => A (![0, 1] i) j.succ.succ with hB
      set D : Matrix (Fin m) (Fin m) ℂ :=
        A.submatrix (fun i : Fin m => i.succ.succ) (fun j : Fin m => j.succ.succ) with hD
      have hAdec : A = blkTR !![A 0 0, A 0 1; 0, A 1 1] B D := blkTR_decomp A htri
      have hDtri : D.BlockTriangular id := by
        intro a b hab
        exact htri (Fin.succ_lt_succ_iff.2 (Fin.succ_lt_succ_iff.2 hab))
      refine ⟨emb2 m W₂, emb2_unitary hW₂, ?_⟩
      rw [emb2_conjTranspose] at *
      have hprod : (emb2 m W₂ᴴ) * A * (emb2 m W₂) = blkTR !![A 1 1, b'; 0, A 0 0] (W₂ᴴ * B) D := by
        conv_lhs => rw [hAdec]
        rw [emb2_conj_blkTR, hW₂eq]
      rw [hprod]
      refine ⟨blkTR_blockTriangular (by simp) _ hDtri, ?_⟩
      intro k
      refine Fin.cases ?_ ?_ k
      · rw [blkTR_zero_zero]
        simp [Equiv.swap_apply_left]
      · intro k₁
        refine Fin.cases ?_ ?_ k₁
        · rw [show (Fin.succ (0 : Fin (m + 1))) = 1 from rfl, blkTR_one_one]
          simp [Equiv.swap_apply_right]
        · intro k₂
          rw [blkTR_succ_succ]
          have hne0 : k₂.succ.succ ≠ (0 : Fin (m + 2)) := Fin.succ_ne_zero _
          have hne1 : k₂.succ.succ ≠ (1 : Fin (m + 2)) := by
            simp [Fin.ext_iff, Fin.val_succ]
          rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]
          rfl
    | succ i' =>
      have hj0 : j ≠ 0 := by
        intro h
        rw [h] at hij
        simp at hij
      obtain ⟨j', rfl⟩ : ∃ j', j = j'.succ := ⟨j.pred hj0, by simp⟩
      have hij' : (j' : ℕ) = (i' : ℕ) + 1 := by
        simpa [Fin.val_succ] using hij
      have hzero : ∀ k : Fin p, A k.succ 0 = 0 := fun k => htri (by simp [Fin.lt_def])
      set C : Matrix (Fin p) (Fin p) ℂ := A.submatrix Fin.succ Fin.succ with hC
      have hCtri : C.BlockTriangular id := by
        intro a b hab
        exact htri (Fin.succ_lt_succ_iff.2 hab)
      obtain ⟨W', hW', hW'tri, hW'diag⟩ := ih C hCtri i' j' hij'
      refine ⟨blk 1 0 0 W', blk_unitary hW', ?_⟩
      have hAdec : A = blk (A 0 0) (fun k => A 0 k.succ) 0 C := blk_decomp A hzero
      have hprod : (blk 1 0 0 W')ᴴ * A * (blk 1 0 0 W')
          = blk (A 0 0) ((fun k => A 0 k.succ) ᵥ* W') 0 (W'ᴴ * C * W') := by
        rw [blk_conjTranspose]
        conv_lhs => rw [hAdec]
        rw [blk_mul, blk_mul]
        simp
      rw [hprod]
      constructor
      · rw [blk_blockTriangular]
        exact hW'tri
      · intro k
        refine Fin.cases ?_ ?_ k
        · have h0 : Equiv.swap i'.succ j'.succ 0 = 0 :=
            Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _).symm (Fin.succ_ne_zero _).symm
          rw [h0]
          rfl
        · intro k'
          rw [blk_succ_succ, hW'diag k', swap_succ_succ]
          rfl

/-! ### Arbitrary permutations of the diagonal -/

/-- `CanReorder e` says that conjugating any upper triangular matrix by a suitable unitary
permutes its diagonal by `e`, preserving upper triangularity. -/
def CanReorder (e : Equiv.Perm (Fin n)) : Prop :=
  ∀ A : Matrix (Fin n) (Fin n) ℂ, A.BlockTriangular id →
    ∃ W ∈ unitaryGroup (Fin n) ℂ, (Wᴴ * A * W).BlockTriangular id ∧
      ∀ i, (Wᴴ * A * W) i i = A (e i) (e i)

lemma canReorder_one : CanReorder (1 : Equiv.Perm (Fin n)) := by
  intro A htri
  exact ⟨1, Submonoid.one_mem _, by simpa using htri, by simp⟩

lemma CanReorder.mul {e₁ e₂ : Equiv.Perm (Fin n)} (h₁ : CanReorder e₁) (h₂ : CanReorder e₂) :
    CanReorder (e₁ * e₂) := by
  intro A htri
  obtain ⟨W₁, hW₁, htri₁, hd₁⟩ := h₁ A htri
  obtain ⟨W₂, hW₂, htri₂, hd₂⟩ := h₂ _ htri₁
  refine ⟨W₁ * W₂, mul_mem hW₁ hW₂, ?_, ?_⟩
  · have h : (W₁ * W₂)ᴴ * A * (W₁ * W₂) = W₂ᴴ * (W₁ᴴ * A * W₁) * W₂ := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [h]; exact htri₂
  · intro i
    have h : (W₁ * W₂)ᴴ * A * (W₁ * W₂) = W₂ᴴ * (W₁ᴴ * A * W₁) * W₂ := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [h, hd₂ i, hd₁ (e₂ i)]
    rfl

/-- Conjugating an upper triangular matrix by a suitable unitary permutes its diagonal by any
prescribed permutation, preserving upper triangularity. -/
theorem exists_unitary_conj_perm_diag {A : Matrix (Fin n) (Fin n) ℂ}
    (htri : A.BlockTriangular id) (e : Equiv.Perm (Fin n)) :
    ∃ W ∈ unitaryGroup (Fin n) ℂ, (Wᴴ * A * W).BlockTriangular id ∧
      ∀ i, (Wᴴ * A * W) i i = A (e i) (e i) := by
  have key : CanReorder e := by
    match n, e with
    | 0, e =>
      intro A _
      exact ⟨1, Submonoid.one_mem _, by simpa using ‹A.BlockTriangular id›, fun i => i.elim0⟩
    | (p + 1), e =>
      let S : Submonoid (Equiv.Perm (Fin (p + 1))) :=
        { carrier := {e | CanReorder e}
          one_mem' := canReorder_one
          mul_mem' := fun h₁ h₂ => CanReorder.mul h₁ h₂ }
      have hgen : ∀ g ∈ Set.range fun i : Fin p => Equiv.swap i.castSucc i.succ, g ∈ S := by
        rintro _ ⟨i, rfl⟩
        intro A htri
        exact exists_unitary_conj_swap_adj (p + 1) A htri i.castSucc i.succ (by simp)
      have hclosure : Submonoid.closure (Set.range fun i : Fin p => Equiv.swap i.castSucc i.succ)
          ≤ S := Submonoid.closure_le.2 hgen
      have : e ∈ S := by
        apply hclosure
        rw [Equiv.Perm.mclosure_swap_castSucc_succ p]
        exact Submonoid.mem_top e
      exact this
  exact key A htri

end Q730
