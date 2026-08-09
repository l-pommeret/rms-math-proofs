import RMS.Q655Stage6

/-!
# Q655 — Stage 5 toolkit: minors, rank and genericity

This file collects the elementary rank technology needed for Stage 5:

* `Q655.rank_submatrix_le'` — passing to a submatrix does not increase the rank;
* `Q655.le_rank_of_det_ne_zero` / `Q655.exists_det_ne_zero_of_le_rank` — the minor criterion
  for the rank of a matrix over a field;
* `Q655.rank_map_eq` — the rank of a matrix is unchanged by a field extension;
* `Q655.finite_setOf_rank_lt` — for a polynomial family of matrices, the rank drops on a finite
  set of parameters only (lower semicontinuity along a curve);
* `Q655.interpMatrix` — entrywise Lagrange interpolation, used to build a polynomial curve
  through finitely many prescribed matrices.
-/

namespace Q655

open Matrix Module

variable {K : Type*} [Field K]
variable {m p : Type*} [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]

/-! ## Extracting an independent subfamily -/

/-- A spanning set of a space of dimension at least `k` contains `k` independent vectors. -/
lemma exists_linearIndependent_of_le_finrank_span {V : Type*} [AddCommGroup V] [Module K V]
    (s : Set V) (k : ℕ) (h : k ≤ Module.finrank K (Submodule.span K s)) :
    ∃ f : Fin k → V, (∀ i, f i ∈ s) ∧ LinearIndependent K f := by
  classical
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent K s
  have hcard : ∃ g : Fin k → b, Function.Injective g := by
    rcases finite_or_infinite b with hb | hb
    · have hft : Fintype b := Fintype.ofFinite b
      have hfin : Module.finrank K (Submodule.span K b) = Fintype.card b := by
        have := finrank_span_eq_card (R := K) (b := (Subtype.val : b → V)) hli
        rw [Subtype.range_coe] at this
        exact this
      have hk : k ≤ Fintype.card b := by rw [← hfin, hspan]; exact h
      obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le (α := Fin k) (β := b) (by simpa using hk)
      exact ⟨g, g.injective⟩
    · exact ⟨fun i => ((⟨Fin.val, Fin.val_injective⟩ : Fin k ↪ ℕ).trans
        (Infinite.natEmbedding b)) i, ((⟨Fin.val, Fin.val_injective⟩ : Fin k ↪ ℕ).trans
        (Infinite.natEmbedding b)).injective⟩
  obtain ⟨g, hg⟩ := hcard
  exact ⟨fun i => (g i : V), fun i => hbs (g i).2, hli.comp g hg⟩

/-! ## Submatrices and minors -/

/-- Selecting rows is multiplication by a `0-1` matrix on the left. -/
lemma submatrix_rows_eq_mul {m' : Type*} (A : Matrix m p K) (ri : m' → m) :
    A.submatrix ri id =
      (Matrix.of fun (i : m') (i' : m) => if i' = ri i then (1 : K) else 0) * A := by
  ext i j
  simp [Matrix.mul_apply, Matrix.submatrix_apply, Finset.sum_ite_eq' Finset.univ (ri i)]

/-- Selecting columns is multiplication by a `0-1` matrix on the right. -/
lemma submatrix_cols_eq_mul {p' : Type*} [Fintype p'] (A : Matrix m p K) (ci : p' → p) :
    A.submatrix id ci =
      A * (Matrix.of fun (j' : p) (j : p') => if j' = ci j then (1 : K) else 0) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.submatrix_apply, Finset.sum_ite_eq' Finset.univ (ci j)]

/-- The rank of a submatrix is at most the rank of the matrix. -/
lemma rank_submatrix_le' {m' p' : Type*} [Fintype m'] [Fintype p'] (A : Matrix m p K)
    (ri : m' → m) (ci : p' → p) : (A.submatrix ri ci).rank ≤ A.rank := by
  classical
  have h : A.submatrix ri ci =
      (Matrix.of fun (i : m') (i' : m) => if i' = ri i then (1 : K) else 0) *
        (A * (Matrix.of fun (j' : p) (j : p') => if j' = ci j then (1 : K) else 0)) := by
    rw [← submatrix_cols_eq_mul A ci, ← submatrix_rows_eq_mul (A.submatrix id ci) ri]
    rfl
  rw [h]
  exact le_trans (Matrix.rank_mul_le_right _ _) (Matrix.rank_mul_le_left _ _)

/-- A square matrix of full rank has nonzero determinant. -/
lemma det_ne_zero_of_rank_eq {k : ℕ} (M : Matrix (Fin k) (Fin k) K) (h : M.rank = k) :
    M.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hker : v ∈ LinearMap.ker M.mulVecLin := by simpa [Matrix.mulVecLin] using hv
  have h1 : 0 < finrank K ↥(LinearMap.ker M.mulVecLin) := by
    have hnt : Nontrivial ↥(LinearMap.ker M.mulVecLin) := ⟨⟨⟨v, hker⟩, 0, by simpa using hv0⟩⟩
    exact Module.finrank_pos
  have h2 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [show finrank K (Fin k → K) = k by simp] at h2
  have h3 : M.rank = finrank K ↥(LinearMap.range M.mulVecLin) := rfl
  omega

/-- A nonzero `k × k` minor forces the rank to be at least `k`. -/
lemma le_rank_of_det_ne_zero {k : ℕ} {A : Matrix m p K}
    {ri : Fin k → m} {ci : Fin k → p} (h : (A.submatrix ri ci).det ≠ 0) :
    k ≤ A.rank := by
  have hunit : IsUnit (A.submatrix ri ci) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have : (A.submatrix ri ci).rank = k := by
    simpa using Matrix.rank_of_isUnit (A.submatrix ri ci) hunit
  calc k = (A.submatrix ri ci).rank := this.symm
    _ ≤ A.rank := rank_submatrix_le' A ri ci

/-- If the rank is at least `k` then some `k` columns are independent. -/
lemma exists_cols_rank_eq {k : ℕ} (A : Matrix m p K) (hk : k ≤ A.rank) :
    ∃ ci : Fin k → p, (A.submatrix id ci).rank = k := by
  classical
  have hspan : k ≤ Module.finrank K (Submodule.span K (Set.range A.col)) := by
    rw [← Matrix.rank_eq_finrank_span_cols]; exact hk
  obtain ⟨f, hmem, hli⟩ := exists_linearIndependent_of_le_finrank_span (Set.range A.col) k hspan
  choose ci hci using hmem
  refine ⟨ci, ?_⟩
  have hcol : (A.submatrix id ci).col = f := by
    funext j
    simpa [Matrix.col, Matrix.submatrix_apply] using hci j
  rw [Matrix.rank_eq_finrank_span_cols, hcol, finrank_span_eq_card hli, Fintype.card_fin]

/-- If the rank is at least `k` then some `k × k` minor is nonzero. -/
lemma exists_det_ne_zero_of_le_rank {k : ℕ} {A : Matrix m p K} (h : k ≤ A.rank) :
    ∃ (ri : Fin k → m) (ci : Fin k → p), (A.submatrix ri ci).det ≠ 0 := by
  classical
  obtain ⟨ci, hci⟩ := exists_cols_rank_eq A h
  set B : Matrix m (Fin k) K := A.submatrix id ci with hB
  have hBT : k ≤ Bᵀ.rank := by rw [Matrix.rank_transpose, hci]
  obtain ⟨ri, hri⟩ := exists_cols_rank_eq Bᵀ hBT
  refine ⟨ri, ci, ?_⟩
  have hEq : (Bᵀ.submatrix id ri) = (A.submatrix ri ci)ᵀ := by
    ext i j; rfl
  have := det_ne_zero_of_rank_eq _ hri
  rw [hEq, Matrix.det_transpose] at this
  exact this

/-! ## Rank and field extensions -/

/-- The rank of a matrix is unchanged under a homomorphism of fields. -/
lemma rank_map_eq {L : Type*} [Field L] (φ : K →+* L) (A : Matrix m p K) :
    (A.map φ).rank = A.rank := by
  classical
  have key : ∀ {k : ℕ} (ri : Fin k → m) (ci : Fin k → p),
      ((A.map φ).submatrix ri ci).det = φ ((A.submatrix ri ci).det) := by
    intro k ri ci
    rw [RingHom.map_det]
    congr 1
  refine le_antisymm ?_ ?_
  · obtain ⟨ri, ci, hdet⟩ := exists_det_ne_zero_of_le_rank (A := A.map φ) (le_refl _)
    rw [key ri ci] at hdet
    exact le_rank_of_det_ne_zero (fun h => hdet (by rw [h, map_zero]))
  · obtain ⟨ri, ci, hdet⟩ := exists_det_ne_zero_of_le_rank (A := A) (le_refl _)
    refine le_rank_of_det_ne_zero (A := A.map φ) (ri := ri) (ci := ci) ?_
    rw [key ri ci]
    exact fun h => hdet ((map_eq_zero_iff φ φ.injective).1 h)

/-! ## Genericity along a polynomial curve -/

open Polynomial

/-- Along a polynomial family of matrices, the locus where the rank drops below a value that is
attained somewhere is finite. -/
lemma finite_setOf_rank_lt {k : ℕ} (M : Matrix m p K[X]) {c₀ : K}
    (h : k ≤ (M.map (Polynomial.evalRingHom c₀)).rank) :
    {c : K | (M.map (Polynomial.evalRingHom c)).rank < k}.Finite := by
  classical
  obtain ⟨ri, ci, hdet⟩ := exists_det_ne_zero_of_le_rank h
  set q : K[X] := (M.submatrix ri ci).det with hq
  have hkey : ∀ c : K, ((M.map (Polynomial.evalRingHom c)).submatrix ri ci).det = q.eval c := by
    intro c
    show ((M.submatrix ri ci).map (Polynomial.evalRingHom c)).det
      = (Polynomial.evalRingHom c) (M.submatrix ri ci).det
    rw [RingHom.map_det]
    congr 1
  have hq0 : q ≠ 0 := by
    intro h0
    rw [hkey c₀, h0] at hdet
    simp at hdet
  have hfin : {c : K | q.eval c = 0}.Finite := by
    have : {c : K | q.IsRoot c}.Finite := by
      by_contra hinf
      exact hq0 (Polynomial.eq_zero_of_infinite_isRoot q (Set.not_finite.mp hinf))
    exact this
  refine Set.Finite.subset hfin ?_
  intro c hc
  simp only [Set.mem_setOf_eq] at hc ⊢
  by_contra hne
  exact absurd (le_rank_of_det_ne_zero (A := M.map (Polynomial.evalRingHom c)) (ri := ri) (ci := ci)
    (by rw [hkey c]; exact hne)) (by omega)

/-- Entrywise Lagrange interpolation through prescribed matrices. -/
noncomputable def interpMatrix {ι : Type*} [DecidableEq ι] (S : Finset ι) (node : ι → K)
    (val : ι → Matrix m p K) : Matrix m p K[X] :=
  Matrix.of fun i j => Lagrange.interpolate S node (fun t => val t i j)

lemma interpMatrix_eval {ι : Type*} [DecidableEq ι] {S : Finset ι} {node : ι → K}
    (hnode : Set.InjOn node S) (val : ι → Matrix m p K) {i : ι} (hi : i ∈ S) :
    (interpMatrix S node val).map (Polynomial.evalRingHom (node i)) = val i := by
  ext a b
  simpa [interpMatrix] using Lagrange.eval_interpolate_at_node (v := node) (s := S) (i := i)
    (fun t => val t a b) hnode hi

end Q655
