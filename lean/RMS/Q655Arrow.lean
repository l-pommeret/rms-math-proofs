import RMS.Q655Factor

/-!
# Q655 — Stage 5E: the two-arrow estimate

Fix `A₀ : Matrix (Fin r) (Fin r) K`, `D₀ : Matrix (Fin s) (Fin s) K`, `B : Matrix (Fin r) (Fin s) K`
and `C : Matrix (Fin s) (Fin r) K`, and consider

  `twoArrow A₀ D₀ B C = {(P, Q) | P ∈ C(A₀), Q ∈ C(D₀), P * B = B * Q, Q * C = C * P}`.

It contains the intersection of the product of the two commutants with the *full* two-arrow
intertwining space

  `twoArrowFull B C = {(P, Q) | P * B = B * Q, Q * C = C * P}`,

which is the kernel of `Φ (P, Q) = (P * B - B * Q, Q * C - C * P)`, a linear map into
`Matrix (Fin r) (Fin s) K × Matrix (Fin s) (Fin r) K`, a space of dimension `2 * r * s`.
The estimate to be proved is `rank Φ ≤ 2 * r * s - r` (for `r ≤ s`), i.e. in addition-only form

  `dim C(A₀) + dim C(D₀) + r ≤ dim (twoArrow A₀ D₀ B C) + 2 * r * s`.

The reason is that the image of `Φ` is annihilated by the `r` linear forms

  `λ i (δB, δC) = trace (δB * (C * (B * C) ^ i)) + trace (δC * ((B * C) ^ i * B))`,

which are the differentials of the characteristic polynomial coefficients of `B * C`; the
verification is a pure trace-cyclicity computation, valid in every characteristic.  At the point
`B = (1 0)`, `C = (J, 0)` with `J` the cyclic permutation matrix, these `r` forms are independent;
a genericity argument along a line then transports the rank bound to an arbitrary `(B, C)`.
-/

namespace Q655

open Matrix Module

variable {K : Type*} [Field K] {r s : ℕ}

/-! ## Vectorising pairs of matrices -/

/-- A pair of matrices, viewed as a vector indexed by the disjoint union of the index pairs. -/
def vecPair (K : Type*) [Field K] (a b c d : ℕ) :
    (Matrix (Fin a) (Fin b) K × Matrix (Fin c) (Fin d) K) ≃ₗ[K]
      ((Fin a × Fin b) ⊕ (Fin c × Fin d) → K) where
  toFun M := Sum.elim (fun ij => M.1 ij.1 ij.2) (fun ij => M.2 ij.1 ij.2)
  map_add' M N := by
    funext x; cases x <;> simp
  map_smul' c M := by
    funext x; cases x <;> simp
  invFun v := (Matrix.of fun i j => v (Sum.inl (i, j)), Matrix.of fun i j => v (Sum.inr (i, j)))
  left_inv M := by
    ext <;> simp
  right_inv v := by
    funext x; cases x <;> simp

@[simp] lemma vecPair_inl {a b c d : ℕ} (M : Matrix (Fin a) (Fin b) K × Matrix (Fin c) (Fin d) K)
    (ij : Fin a × Fin b) : vecPair K a b c d M (Sum.inl ij) = M.1 ij.1 ij.2 := rfl

@[simp] lemma vecPair_inr {a b c d : ℕ} (M : Matrix (Fin a) (Fin b) K × Matrix (Fin c) (Fin d) K)
    (ij : Fin c × Fin d) : vecPair K a b c d M (Sum.inr ij) = M.2 ij.1 ij.2 := rfl

/-- Rank–nullity for a submodule cut out by a linear system, in an arbitrary coordinatised
space. -/
lemma finrank_add_rank_of_ker' {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] {V : Type*} [AddCommGroup V] [Module K V] (E : V ≃ₗ[K] (κ → K))
    (A : Matrix ι κ K) (S : Submodule K V) (hS : ∀ X : V, X ∈ S ↔ A *ᵥ (E X) = 0) :
    finrank K ↥S + A.rank = Fintype.card κ := by
  have hmap : S.map (E : V →ₗ[K] (κ → K)) = LinearMap.ker A.mulVecLin := by
    ext v
    constructor
    · rintro ⟨X, hX, rfl⟩
      simpa [Matrix.mulVecLin] using (hS X).1 hX
    · intro hv
      refine ⟨E.symm v, ?_, by simp⟩
      show E.symm v ∈ S
      rw [hS]
      simpa [Matrix.mulVecLin] using hv
  have h1 : finrank K ↥S = finrank K ↥(LinearMap.ker A.mulVecLin) := by
    rw [← hmap, LinearEquiv.finrank_map_eq]
  have h2 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h3 : finrank K (κ → K) = Fintype.card κ := by simp [Module.finrank_pi]
  have h4 : A.rank = finrank K ↥(LinearMap.range A.mulVecLin) := rfl
  omega

/-! ## The two-arrow spaces -/

/-- The two-arrow endomorphism space. -/
def twoArrow (A₀ : Matrix (Fin r) (Fin r) K) (D₀ : Matrix (Fin s) (Fin s) K)
    (B : Matrix (Fin r) (Fin s) K) (C : Matrix (Fin s) (Fin r) K) :
    Submodule K (Matrix (Fin r) (Fin r) K × Matrix (Fin s) (Fin s) K) where
  carrier := {PQ | PQ.1 * A₀ = A₀ * PQ.1 ∧ PQ.2 * D₀ = D₀ * PQ.2 ∧
    PQ.1 * B = B * PQ.2 ∧ PQ.2 * C = C * PQ.1}
  add_mem' := by
    rintro x y ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Matrix.add_mul, Matrix.mul_add,
        h1, h1', h2, h2', h3, h3', h4, h4']
  zero_mem' := by simp
  smul_mem' := by
    rintro c x ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Prod.smul_fst, Prod.smul_snd, Matrix.smul_mul, Matrix.mul_smul,
        h1, h2, h3, h4]

lemma mem_twoArrow_iff {A₀ : Matrix (Fin r) (Fin r) K} {D₀ : Matrix (Fin s) (Fin s) K}
    {B : Matrix (Fin r) (Fin s) K} {C : Matrix (Fin s) (Fin r) K}
    {P : Matrix (Fin r) (Fin r) K} {Q : Matrix (Fin s) (Fin s) K} :
    (P, Q) ∈ twoArrow A₀ D₀ B C ↔
      P * A₀ = A₀ * P ∧ Q * D₀ = D₀ * Q ∧ P * B = B * Q ∧ Q * C = C * P := Iff.rfl

/-- The full two-arrow intertwining space, with no condition at the vertices. -/
def twoArrowFull (B : Matrix (Fin r) (Fin s) K) (C : Matrix (Fin s) (Fin r) K) :
    Submodule K (Matrix (Fin r) (Fin r) K × Matrix (Fin s) (Fin s) K) where
  carrier := {PQ | PQ.1 * B = B * PQ.2 ∧ PQ.2 * C = C * PQ.1}
  add_mem' := by
    rintro x y ⟨h3, h4⟩ ⟨h3', h4'⟩
    refine ⟨?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Matrix.add_mul, Matrix.mul_add, h3, h3', h4, h4']
  zero_mem' := by simp
  smul_mem' := by
    rintro c x ⟨h3, h4⟩
    refine ⟨?_, ?_⟩ <;>
      simp only [Prod.smul_fst, Prod.smul_snd, Matrix.smul_mul, Matrix.mul_smul, h3, h4]

lemma mem_twoArrowFull_iff {B : Matrix (Fin r) (Fin s) K} {C : Matrix (Fin s) (Fin r) K}
    {P : Matrix (Fin r) (Fin r) K} {Q : Matrix (Fin s) (Fin s) K} :
    (P, Q) ∈ twoArrowFull B C ↔ P * B = B * Q ∧ Q * C = C * P := Iff.rfl

/-! ## The coefficient matrix of the two-arrow map -/

/-- The coefficient matrix of `Φ (P, Q) = (P * B - B * Q, Q * C - C * P)`. -/
def arrowMat {R : Type*} [CommRing R] {r s : ℕ} (B : Matrix (Fin r) (Fin s) R)
    (C : Matrix (Fin s) (Fin r) R) :
    Matrix ((Fin r × Fin s) ⊕ (Fin s × Fin r)) ((Fin r × Fin r) ⊕ (Fin s × Fin s)) R :=
  Matrix.of fun x y =>
    match x, y with
    | Sum.inl (i, j), Sum.inl (a, b) => if a = i then B b j else 0
    | Sum.inl (i, j), Sum.inr (a, b) => -(if b = j then B i a else 0)
    | Sum.inr (i, j), Sum.inl (a, b) => -(if b = j then C i a else 0)
    | Sum.inr (i, j), Sum.inr (a, b) => if a = i then C b j else 0

lemma arrowMat_mulVec (B : Matrix (Fin r) (Fin s) K) (C : Matrix (Fin s) (Fin r) K)
    (P : Matrix (Fin r) (Fin r) K) (Q : Matrix (Fin s) (Fin s) K) :
    arrowMat B C *ᵥ (vecPair K r r s s (P, Q)) =
      vecPair K r s s r (P * B - B * Q, Q * C - C * P) := by
  funext x
  cases x with
  | inl ij =>
      obtain ⟨i, j⟩ := ij
      have hS1 : ∑ ab : Fin r × Fin r, (if ab.1 = i then B ab.2 j else 0) * P ab.1 ab.2
          = (P * B) i j := by
        rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
        · simp [Matrix.mul_apply, mul_comm]
        · intro a _ ha; simp [ha]
        · simp
      have hS2 : ∑ ab : Fin s × Fin s, -(if ab.2 = j then B i ab.1 else 0) * Q ab.1 ab.2
          = -((B * Q) i j) := by
        have hin : ∀ a : Fin s, ∑ b : Fin s, (if b = j then B i a else 0) * Q a b
            = B i a * Q a j := by
          intro a
          rw [Finset.sum_eq_single j]
          · simp
          · intro b _ hb; simp [hb]
          · simp
        rw [Fintype.sum_prod_type]
        simp only [neg_mul, Finset.sum_neg_distrib, hin]
        rw [Matrix.mul_apply]
      rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
      simp only [arrowMat, Matrix.of_apply, vecPair_inl, vecPair_inr]
      rw [hS1, hS2]
      simp [Matrix.sub_apply]
      abel
  | inr ij =>
      obtain ⟨i, j⟩ := ij
      have hS1 : ∑ ab : Fin s × Fin s, (if ab.1 = i then C ab.2 j else 0) * Q ab.1 ab.2
          = (Q * C) i j := by
        rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
        · simp [Matrix.mul_apply, mul_comm]
        · intro a _ ha; simp [ha]
        · simp
      have hS2 : ∑ ab : Fin r × Fin r, -(if ab.2 = j then C i ab.1 else 0) * P ab.1 ab.2
          = -((C * P) i j) := by
        have hin : ∀ a : Fin r, ∑ b : Fin r, (if b = j then C i a else 0) * P a b
            = C i a * P a j := by
          intro a
          rw [Finset.sum_eq_single j]
          · simp
          · intro b _ hb; simp [hb]
          · simp
        rw [Fintype.sum_prod_type]
        simp only [neg_mul, Finset.sum_neg_distrib, hin]
        rw [Matrix.mul_apply]
      rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
      simp only [arrowMat, Matrix.of_apply, vecPair_inl, vecPair_inr]
      rw [hS2, hS1]
      simp [Matrix.sub_apply]
      abel

/-- The `r` linear forms annihilating the image of the two-arrow map. -/
def arrowFun {R : Type*} [CommRing R] {r s : ℕ} (B : Matrix (Fin r) (Fin s) R)
    (C : Matrix (Fin s) (Fin r) R) :
    Matrix (Fin r) ((Fin r × Fin s) ⊕ (Fin s × Fin r)) R :=
  Matrix.of fun i x =>
    match x with
    | Sum.inl (a, b) => (C * (B * C) ^ (i : ℕ)) b a
    | Sum.inr (a, b) => ((B * C) ^ (i : ℕ) * B) b a

/-- The trace identity behind the estimate: the forms kill every commutator variation. -/
lemma trace_arrow_identity (B : Matrix (Fin r) (Fin s) K) (C : Matrix (Fin s) (Fin r) K)
    (P : Matrix (Fin r) (Fin r) K) (Q : Matrix (Fin s) (Fin s) K) (i : ℕ) :
    trace ((P * B - B * Q) * (C * (B * C) ^ i)) +
      trace ((Q * C - C * P) * ((B * C) ^ i * B)) = 0 := by
  set X := (B * C) ^ i with hX
  have hcomm : B * C * X = X * (B * C) := by
    rw [hX]; exact ((Commute.refl (B * C)).pow_right i)
  have e1 : (P * B - B * Q) * (C * X) = P * (B * C * X) - B * (Q * (C * X)) := by
    rw [Matrix.sub_mul]
    congr 1 <;> simp [Matrix.mul_assoc]
  have e2 : (Q * C - C * P) * (X * B) = Q * (C * (X * B)) - C * (P * (X * B)) := by
    rw [Matrix.sub_mul]
    congr 1 <;> simp [Matrix.mul_assoc]
  rw [e1, e2, Matrix.trace_sub, Matrix.trace_sub]
  have h1 : trace (B * (Q * (C * X))) = trace (Q * (C * (X * B))) := by
    rw [Matrix.trace_mul_comm]
    congr 1
    simp [Matrix.mul_assoc]
  have h2 : trace (P * (B * C * X)) = trace (C * (P * (X * B))) := by
    rw [Matrix.trace_mul_comm C (P * (X * B))]
    congr 1
    rw [hcomm]
    simp [Matrix.mul_assoc]
  rw [h1, h2]
  abel

/-- The pairing of the `i`-th form with a variation, in trace form. -/
lemma arrowFun_dotProduct (B : Matrix (Fin r) (Fin s) K) (C : Matrix (Fin s) (Fin r) K)
    (i : Fin r) (D : Matrix (Fin r) (Fin s) K) (E : Matrix (Fin s) (Fin r) K) :
    ∑ x, arrowFun B C i x * (vecPair K r s s r (D, E)) x
      = trace (D * (C * (B * C) ^ (i : ℕ))) + trace (E * ((B * C) ^ (i : ℕ) * B)) := by
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [Matrix.trace, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [arrowFun, Matrix.diag, Matrix.mul_apply, mul_comm]
  · rw [Matrix.trace, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [arrowFun, Matrix.diag, Matrix.mul_apply, mul_comm]

/-- The forms annihilate the image of the two-arrow map. -/
lemma arrowFun_mul_arrowMat (B : Matrix (Fin r) (Fin s) K) (C : Matrix (Fin s) (Fin r) K) :
    arrowFun B C * arrowMat B C = 0 := by
  refine matrix_ext_of_mulVec fun v => ?_
  obtain ⟨PQ, rfl⟩ := (vecPair K r r s s).surjective v
  obtain ⟨P, Q⟩ := PQ
  rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, arrowMat_mulVec]
  funext i
  have h := arrowFun_dotProduct B C i (P * B - B * Q) (Q * C - C * P)
  have h2 := trace_arrow_identity B C P Q (i : ℕ)
  simp only [Matrix.mulVec, dotProduct]
  rw [h, h2]
  rfl

/-- The rank of the two-arrow map plus the number of independent forms is at most `2 r s`. -/
lemma arrowMat_rank_add_arrowFun_rank_le (B : Matrix (Fin r) (Fin s) K)
    (C : Matrix (Fin s) (Fin r) K) :
    (arrowMat B C).rank + (arrowFun B C).rank ≤ 2 * r * s := by
  have hcard : Fintype.card ((Fin r × Fin s) ⊕ (Fin s × Fin r)) = 2 * r * s := by
    simp [Fintype.card_sum, Fintype.card_prod]
    ring
  have hsub : LinearMap.range (arrowMat B C).mulVecLin ≤
      LinearMap.ker (arrowFun B C).mulVecLin := by
    rintro _ ⟨x, rfl⟩
    show arrowFun B C *ᵥ (arrowMat B C *ᵥ x) = 0
    rw [Matrix.mulVec_mulVec, arrowFun_mul_arrowMat, Matrix.zero_mulVec]
  have h1 : (arrowMat B C).rank ≤ finrank K ↥(LinearMap.ker (arrowFun B C).mulVecLin) :=
    Submodule.finrank_mono hsub
  have h2 := LinearMap.finrank_range_add_finrank_ker (arrowFun B C).mulVecLin
  have h3 : finrank K (((Fin r × Fin s) ⊕ (Fin s × Fin r)) → K) = 2 * r * s := by
    rw [Module.finrank_pi, hcard]
  have h4 : (arrowFun B C).rank = finrank K ↥(LinearMap.range (arrowFun B C).mulVecLin) := rfl
  omega

/-! ## The witness point -/

/-- The cyclic permutation matrix. -/
def cycMat (K : Type*) [Field K] (r : ℕ) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun i j => if (j : ℕ) = ((i : ℕ) + 1) % r then 1 else 0

lemma succ_mod_eq {r : ℕ} {i : ℕ} (hi : i < r) :
    (i + 1) % r = if i + 1 = r then 0 else i + 1 := by
  by_cases h : i + 1 = r
  · simp [h]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

lemma succ_mod_inj {r : ℕ} {i i' : ℕ} (hi : i < r) (hi' : i' < r)
    (h : (i + 1) % r = (i' + 1) % r) : i = i' := by
  rw [succ_mod_eq hi, succ_mod_eq hi'] at h
  split_ifs at h <;> omega

lemma cycMat_pow_apply (hr : 0 < r) (k : ℕ) :
    ∀ i j : Fin r, ((cycMat K r) ^ k) i j = if (j : ℕ) = ((i : ℕ) + k) % r then 1 else 0 := by
  induction k with
  | zero =>
      intro i j
      simp only [pow_zero, Matrix.one_apply, Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
      by_cases h : i = j
      · simp [h]
      · rw [if_neg h, if_neg (fun hc : (j : ℕ) = (i : ℕ) => h (Fin.ext hc.symm))]
  | succ k ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply,
        Finset.sum_eq_single (⟨((i : ℕ) + k) % r, Nat.mod_lt _ hr⟩ : Fin r)]
      · rw [ih i ⟨((i : ℕ) + k) % r, Nat.mod_lt _ hr⟩]
        simp only [cycMat, Matrix.of_apply]
        rw [Nat.mod_add_mod, ← Nat.add_assoc]
        simp
      · intro l _ hl
        rw [ih i l]
        have hne : (l : ℕ) ≠ ((i : ℕ) + k) % r := fun hc => hl (Fin.ext hc)
        rw [if_neg hne, zero_mul]
      · simp

/-- The powers `cyc ^ (i+1)`, `i < r`, are linearly independent: a linear relation is trivial. -/
lemma cycMat_pow_indep (hr : 0 < r) (g : Fin r → K)
    (h : ∀ a b : Fin r, ∑ i : Fin r, g i * ((cycMat K r) ^ ((i : ℕ) + 1)) b a = 0) :
    ∀ i, g i = 0 := by
  intro i
  have hsum := h ⟨((i : ℕ) + 1) % r, Nat.mod_lt _ hr⟩ ⟨0, hr⟩
  rw [Finset.sum_eq_single i] at hsum
  · rw [cycMat_pow_apply hr] at hsum
    rw [if_pos (by simp)] at hsum
    simpa using hsum
  · intro i' _ hne
    rw [cycMat_pow_apply hr]
    have hnn : ((i : ℕ) + 1) % r ≠ (0 + ((i' : ℕ) + 1)) % r := by
      intro hc
      rw [Nat.zero_add] at hc
      exact hne (Fin.ext (succ_mod_inj i'.isLt i.isLt hc.symm))
    show (g i' * if (((⟨((i : ℕ) + 1) % r, Nat.mod_lt _ hr⟩ : Fin r) : ℕ))
        = ((0 : ℕ) + ((i' : ℕ) + 1)) % r then (1 : K) else 0) = 0
    rw [if_neg hnn, mul_zero]
  · simp

/-- The first witness matrix `B₀ = (I 0)`. -/
def witB (K : Type*) [Field K] {r s : ℕ} (hrs : r ≤ s) : Matrix (Fin r) (Fin s) K :=
  Matrix.of fun i j => if j = Fin.castLE hrs i then 1 else 0

/-- The second witness matrix `C₀ = (J; 0)` with `J` the cyclic permutation matrix. -/
def witC (K : Type*) [Field K] {r s : ℕ} (hrs : r ≤ s) : Matrix (Fin s) (Fin r) K :=
  Matrix.of fun i j => ∑ b : Fin r, if i = Fin.castLE hrs b then cycMat K r b j else 0

lemma witB_mul_witC (hrs : r ≤ s) : witB K hrs * witC K hrs = cycMat K r := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE hrs i)]
  · simp only [witB, witC, Matrix.of_apply, if_pos rfl, one_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have : Fin.castLE hrs i ≠ Fin.castLE hrs b := fun hc =>
        hb ((Fin.castLE_injective hrs) hc).symm
      simp [this]
    · simp
  · intro k _ hk
    simp [witB, hk]
  · simp

lemma witC_mul_pow (hrs : r ≤ s) (i : ℕ) (b : Fin r) (a : Fin r) :
    (witC K hrs * (cycMat K r) ^ i) (Fin.castLE hrs b) a = ((cycMat K r) ^ (i + 1)) b a := by
  rw [Matrix.mul_apply]
  have hrow : ∀ c : Fin r, witC K hrs (Fin.castLE hrs b) c = cycMat K r b c := by
    intro c
    simp only [witC, Matrix.of_apply]
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      have : Fin.castLE hrs b ≠ Fin.castLE hrs b' := fun hc =>
        hb' ((Fin.castLE_injective hrs) hc).symm
      simp [this]
    · simp
  simp only [hrow]
  rw [pow_succ']
  rw [Matrix.mul_apply]

/-- At the witness point the `r` forms are independent, so the form matrix has rank `r`. -/
lemma le_rank_arrowFun_witness (hrs : r ≤ s) : r ≤ (arrowFun (witB K hrs) (witC K hrs)).rank := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  set N := arrowFun (witB K hrs) (witC K hrs) with hN
  have hli : LinearIndependent K (fun i : Fin r => (Nᵀ).col i) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    refine cycMat_pow_indep hr g (fun a b => ?_) i
    have hgc := congrFun hg (Sum.inl (a, Fin.castLE hrs b))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
      Matrix.transpose_apply, Pi.zero_apply] at hgc
    rw [← hgc]
    refine Finset.sum_congr rfl fun i' _ => ?_
    congr 1
    rw [hN]
    show ((cycMat K r) ^ ((i' : ℕ) + 1)) b a
      = (witC K hrs * (witB K hrs * witC K hrs) ^ (i' : ℕ)) (Fin.castLE hrs b) a
    rw [witB_mul_witC, witC_mul_pow]
  have hrank : (Nᵀ).rank = r := by
    rw [Matrix.rank_eq_finrank_span_cols]
    have : Set.range (Nᵀ).col = Set.range (fun i : Fin r => (Nᵀ).col i) := rfl
    rw [this, finrank_span_eq_card hli, Fintype.card_fin]
  rw [← Matrix.rank_transpose (A := N)] at *
  omega

/-! ## Genericity -/

lemma arrowMat_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (B : Matrix (Fin r) (Fin s) R) (C : Matrix (Fin s) (Fin r) R) :
    (arrowMat B C).map φ = arrowMat (B.map φ) (C.map φ) := by
  ext x y
  cases x with
  | inl ij =>
      obtain ⟨i, j⟩ := ij
      cases y with
      | inl ab =>
          obtain ⟨a, b⟩ := ab
          show φ (if a = i then B b j else 0) = if a = i then (B.map φ) b j else 0
          by_cases h : a = i <;> simp [h]
      | inr ab =>
          obtain ⟨a, b⟩ := ab
          show φ (-(if b = j then B i a else 0)) = -(if b = j then (B.map φ) i a else 0)
          by_cases h : b = j <;> simp [h]
  | inr ij =>
      obtain ⟨i, j⟩ := ij
      cases y with
      | inl ab =>
          obtain ⟨a, b⟩ := ab
          show φ (-(if b = j then C i a else 0)) = -(if b = j then (C.map φ) i a else 0)
          by_cases h : b = j <;> simp [h]
      | inr ab =>
          obtain ⟨a, b⟩ := ab
          show φ (if a = i then C b j else 0) = if a = i then (C.map φ) b j else 0
          by_cases h : a = i <;> simp [h]

lemma arrowFun_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (B : Matrix (Fin r) (Fin s) R) (C : Matrix (Fin s) (Fin r) R) :
    (arrowFun B C).map φ = arrowFun (B.map φ) (C.map φ) := by
  have hpow : ∀ i : ℕ, ((B * C) ^ i).map φ = ((B.map φ) * (C.map φ)) ^ i := by
    intro i
    have h1 : ((B * C) ^ i).map φ = (φ.mapMatrix ((B * C) ^ i)) := rfl
    rw [h1, map_pow]
    congr 1
    show (B * C).map φ = (B.map φ) * (C.map φ)
    exact Matrix.map_mul
  ext i x
  cases x with
  | inl ab =>
      obtain ⟨a, b⟩ := ab
      show φ ((C * (B * C) ^ (i : ℕ)) b a)
        = ((C.map φ) * ((B.map φ) * (C.map φ)) ^ (i : ℕ)) b a
      rw [← hpow]
      have : (C * (B * C) ^ (i : ℕ)).map φ = (C.map φ) * (((B * C) ^ (i : ℕ)).map φ) :=
        Matrix.map_mul
      exact congrFun (congrFun this b) a
  | inr ab =>
      obtain ⟨a, b⟩ := ab
      show φ (((B * C) ^ (i : ℕ) * B) b a)
        = (((B.map φ) * (C.map φ)) ^ (i : ℕ) * (B.map φ)) b a
      rw [← hpow]
      have : ((B * C) ^ (i : ℕ) * B).map φ = (((B * C) ^ (i : ℕ)).map φ) * (B.map φ) :=
        Matrix.map_mul
      exact congrFun (congrFun this b) a

open Polynomial in
/-- The rank of the two-arrow map is at most `2 r s - r`, for every `B` and `C`. -/
lemma arrowMat_rank_add_le [Infinite K] (hrs : r ≤ s) (B : Matrix (Fin r) (Fin s) K)
    (C : Matrix (Fin s) (Fin r) K) :
    (arrowMat B C).rank + r ≤ 2 * r * s := by
  classical
  set B₀ := witB K hrs with hB₀
  set C₀ := witC K hrs with hC₀
  set BX : Matrix (Fin r) (Fin s) K[X] :=
    Matrix.of fun i j => Polynomial.C (B i j) + Polynomial.X * Polynomial.C (B₀ i j - B i j)
    with hBX
  set CX : Matrix (Fin s) (Fin r) K[X] :=
    Matrix.of fun i j => Polynomial.C (C i j) + Polynomial.X * Polynomial.C (C₀ i j - C i j)
    with hCX
  have hB0 : BX.map (Polynomial.evalRingHom (0 : K)) = B := by
    ext i j; simp [hBX]
  have hC0 : CX.map (Polynomial.evalRingHom (0 : K)) = C := by
    ext i j; simp [hCX]
  have hB1 : BX.map (Polynomial.evalRingHom (1 : K)) = B₀ := by
    ext i j; simp [hBX]
  have hC1 : CX.map (Polynomial.evalRingHom (1 : K)) = C₀ := by
    ext i j; simp [hCX]
  set k := (arrowMat B C).rank with hk
  have hMev : ∀ t : K, (arrowMat BX CX).map (Polynomial.evalRingHom t)
      = arrowMat (BX.map (Polynomial.evalRingHom t)) (CX.map (Polynomial.evalRingHom t)) :=
    fun t => arrowMat_map _ _ _
  have hNev : ∀ t : K, (arrowFun BX CX).map (Polynomial.evalRingHom t)
      = arrowFun (BX.map (Polynomial.evalRingHom t)) (CX.map (Polynomial.evalRingHom t)) :=
    fun t => arrowFun_map _ _ _
  have hfin1 : {c : K | ((arrowMat BX CX).map (Polynomial.evalRingHom c)).rank < k}.Finite := by
    refine finite_setOf_rank_lt (M := arrowMat BX CX) (c₀ := (0 : K)) ?_
    rw [hMev, hB0, hC0]
  have hfin2 : {c : K | ((arrowFun BX CX).map (Polynomial.evalRingHom c)).rank < r}.Finite := by
    refine finite_setOf_rank_lt (M := arrowFun BX CX) (c₀ := (1 : K)) ?_
    rw [hNev, hB1, hC1]
    exact le_rank_arrowFun_witness hrs
  obtain ⟨t, ht⟩ := (hfin1.union hfin2).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at ht
  obtain ⟨ht1, ht2⟩ := ht
  rw [hMev] at ht1
  rw [hNev] at ht2
  have hle := arrowMat_rank_add_arrowFun_rank_le
    (BX.map (Polynomial.evalRingHom t)) (CX.map (Polynomial.evalRingHom t))
  omega

/-! ## The dimension of the two-arrow space -/

/-- A submodule of a product, as the product of submodules. -/
def prodSubmoduleEquiv {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (p : Submodule K V) (q : Submodule K W) : ↥(p.prod q) ≃ₗ[K] (↥p × ↥q) where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  map_add' x y := rfl
  map_smul' c x := rfl
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  left_inv x := by ext <;> rfl
  right_inv y := by ext <;> rfl

lemma finrank_twoArrowFull_add_rank (B : Matrix (Fin r) (Fin s) K)
    (C : Matrix (Fin s) (Fin r) K) :
    finrank K ↥(twoArrowFull B C) + (arrowMat B C).rank = r ^ 2 + s ^ 2 := by
  have hkey := finrank_add_rank_of_ker' (vecPair K r r s s) (arrowMat B C) (twoArrowFull B C)
    (by
      rintro ⟨P, Q⟩
      rw [arrowMat_mulVec]
      constructor
      · rintro ⟨h1, h2⟩
        have : (P * B - B * Q, Q * C - C * P)
            = (0 : Matrix (Fin r) (Fin s) K × Matrix (Fin s) (Fin r) K) := by
          rw [h1, h2]; simp
        rw [this, map_zero]
      · intro h
        have h0 := (vecPair K r s s r).map_eq_zero_iff.1 h
        have h1 : P * B - B * Q = 0 := congrArg Prod.fst h0
        have h2 : Q * C - C * P = 0 := congrArg Prod.snd h0
        exact ⟨sub_eq_zero.1 h1, sub_eq_zero.1 h2⟩)
  rw [hkey]
  simp [Fintype.card_sum, Fintype.card_prod, sq]

/-- **Stage 5E.**  The two-arrow estimate, in addition-only form. -/
theorem twoArrow_finrank_bound [Infinite K] (hrs : r ≤ s)
    (A₀ : Matrix (Fin r) (Fin r) K) (D₀ : Matrix (Fin s) (Fin s) K)
    (B : Matrix (Fin r) (Fin s) K) (C : Matrix (Fin s) (Fin r) K) :
    finrank K ↥(gcommutant A₀) + finrank K ↥(gcommutant D₀) + r ≤
      finrank K ↥(twoArrow A₀ D₀ B C) + 2 * r * s := by
  have hEq : twoArrow A₀ D₀ B C
      = ((gcommutant A₀).prod (gcommutant D₀)) ⊓ twoArrowFull B C := by
    ext ⟨P, Q⟩
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2, h3, h4⟩
  have hprod : finrank K ↥((gcommutant A₀).prod (gcommutant D₀))
      = finrank K ↥(gcommutant A₀) + finrank K ↥(gcommutant D₀) := by
    rw [(prodSubmoduleEquiv (gcommutant A₀) (gcommutant D₀)).finrank_eq, Module.finrank_prod]
  have hamb : finrank K (Matrix (Fin r) (Fin r) K × Matrix (Fin s) (Fin s) K) = r ^ 2 + s ^ 2 := by
    rw [Module.finrank_prod]
    simp [Module.finrank_matrix, sq]
  have hsup : finrank K ↥(((gcommutant A₀).prod (gcommutant D₀)) ⊔ twoArrowFull B C)
      ≤ r ^ 2 + s ^ 2 := by
    rw [← hamb]
    exact Submodule.finrank_le _
  have hinf := Submodule.finrank_sup_add_finrank_inf_eq
    ((gcommutant A₀).prod (gcommutant D₀)) (twoArrowFull B C)
  have h1 := finrank_twoArrowFull_add_rank B C
  have h2 := arrowMat_rank_add_le hrs B C
  rw [hEq]
  omega

end Q655
