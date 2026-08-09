/-
# Q706 : extreme values of the ordered eigenvalues of a symmetric matrix with entries in `[a,b]`

Lean version: `leanprover/lean4:v4.28.0`
Mathlib version: `v4.28.0` (commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`)

For `a ≤ b` let `S n [a,b]` be the set of real symmetric `n × n` matrices all of whose entries
lie in `[a,b]`, and let `λ₁(A) ≥ λ₂(A) ≥ … ≥ λₙ(A)` be the eigenvalues of a symmetric matrix `A`
in decreasing order.  Q706 asks for the extreme values of `λₖ(A)` for `A ∈ S n [a,b]`.

This file formalizes the parts of the answer that are exact:

* the four outer endpoints `L₁, U₁, Lₙ, Uₙ` (formulas (2.1)–(2.4) of the answer);
* the complete range of `λ₂` for `0 ≤ a ≤ b`: the lower endpoint `L₂ = a - b` (formula (2.5))
  and the upper endpoint `U₂ = φ(a,b,n)` (formulas (2.6)–(2.7)), together with the dual
  statements for `λ_{n-1}` when `a ≤ b ≤ 0` (formulas (2.8)–(2.9));
* the fact that every range `eigRange n a b k` is an interval, and the exceptional case `n = 1`;
* the exact density-matrix minimax characterizations of `U_k` and `L_k` for arbitrary `k`
  (formulas (2.10)–(2.11)), their centered specialization `U_k(n;-r,r) = r·η_{n,k}` and the
  sign duality `L_k(n;-r,r) = -U_{n-k+1}(n;-r,r)` (formulas (2.12)–(2.13));
* the self-contained order-statistic/variance and spectral-projection bounds
  (formulas (2.14)–(2.17)).

The numerical value of the constants `η_{n,k}` for intermediate `k` is *not* claimed: they are
carried as the exact minimax constants `etaConst n k`.  Formulas (2.18)–(2.19) of the source are
not included, since they depend on an external sharp projection theorem that is not formalized
here.

Eigenvalues are indexed from `0`, i.e. `eigVal A k` is the `(k+1)`-st largest eigenvalue; so
`λ₁ = eigVal A 0`, `λ₂ = eigVal A 1`, `λₙ = eigVal A (Fin.last _)`.
-/
import Mathlib

open Matrix Unitary

namespace Q706

variable {n : ℕ}

/-! ## Ordered eigenvalues -/

/-- `eigVal A k` is the `(k+1)`-st largest eigenvalue of the real symmetric matrix `A`
(so `eigVal A 0 = λ₁(A)`).  It is junk (`0`) if `A` is not symmetric. -/
noncomputable def eigVal (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : ℝ :=
  if h : A.IsHermitian then h.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm k) else 0

theorem eigVal_antitone (A : Matrix (Fin n) (Fin n) ℝ) : Antitone (eigVal A) := by
  intro i j hij
  unfold eigVal
  split
  · exact (by assumption : A.IsHermitian).eigenvalues₀_antitone (by exact hij)
  · exact le_refl _

/-- Diagonalization in the form we use it: there is an orthogonal matrix `W` such that, writing
`c = Wᵀ x` for the coordinates of `x` in the eigenbasis, the euclidean norm and the quadratic
form of `A` are given by `∑ cₖ²` and `∑ λₖ cₖ²`. -/
theorem spectral_coords {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    ∃ W : Matrix (Fin n) (Fin n) ℝ, Wᵀ * W = 1 ∧ W * Wᵀ = 1 ∧
      (∀ x : Fin n → ℝ, x ⬝ᵥ x = ∑ k, ((Wᵀ *ᵥ x) k) ^ 2) ∧
      (∀ x : Fin n → ℝ, x ⬝ᵥ A *ᵥ x = ∑ k, eigVal A k * ((Wᵀ *ᵥ x) k) ^ 2) := by
  classical
  set U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hUdef
  have hUt : Uᵀ * U = 1 := by
    have := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
    rw [star_eq_conjTranspose] at this
    simpa [hUdef] using this
  have hUt' : U * Uᵀ = 1 := mul_eq_one_comm.2 hUt
  have hspec : A = U * diagonal hA.eigenvalues * Uᵀ := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [conjStarAlgAut_apply, star_eq_conjTranspose]
    simp [hUdef]
  set σ : Fin n ≃ Fin (Fintype.card (Fin n)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm with hσ
  set τ : Equiv.Perm (Fin n) := σ.trans (finCongr (Fintype.card_fin n)) with hτ
  have heig : ∀ i, hA.eigenvalues i = eigVal A (τ i) := by
    intro i
    simp [eigVal, hA, Matrix.IsHermitian.eigenvalues, hτ, hσ]
  have hcoord : ∀ (x : Fin n → ℝ) (k : Fin n),
      (((U.submatrix id τ.symm))ᵀ *ᵥ x) k = (Uᵀ *ᵥ x) (τ.symm k) := by
    intro x k; simp [mulVec, dotProduct]
  refine ⟨U.submatrix id τ.symm, ?_, ?_, ?_, ?_⟩
  · ext i j
    have : (Uᵀ * U) (τ.symm i) (τ.symm j)
        = (1 : Matrix (Fin n) (Fin n) ℝ) (τ.symm i) (τ.symm j) := by rw [hUt]
    simpa [Matrix.mul_apply, Matrix.one_apply, (τ.symm).injective.eq_iff] using this
  · ext i j
    have : (U * Uᵀ) i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by rw [hUt']
    simpa [Matrix.mul_apply, Matrix.one_apply, Equiv.sum_comp τ.symm (fun k => U i k * U j k)]
      using this
  · intro x
    have h1 : (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ x) = x ⬝ᵥ x := by
      rw [dotProduct_mulVec, ← mulVec_transpose, transpose_transpose, mulVec_mulVec, hUt',
        one_mulVec]
    simp only [hcoord]
    rw [Equiv.sum_comp τ.symm (fun k => ((Uᵀ *ᵥ x) k) ^ 2), ← h1]
    simp [dotProduct, sq]
  · intro x
    have key : ∀ d : Fin n → ℝ, x ⬝ᵥ (U * diagonal d * Uᵀ) *ᵥ x = ∑ i, d i * ((Uᵀ *ᵥ x) i) ^ 2 := by
      intro d
      rw [show U * diagonal d * Uᵀ = U * (diagonal d * Uᵀ) by rw [mul_assoc]]
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
      simp [dotProduct, Matrix.mulVec_diagonal, sq, mul_left_comm]
    have h2 := key hA.eigenvalues
    rw [← hspec] at h2
    simp only [hcoord]
    have hstep : ∀ k : Fin n, eigVal A k * ((Uᵀ *ᵥ x) (τ.symm k)) ^ 2
        = (fun i => eigVal A (τ i) * ((Uᵀ *ᵥ x) i) ^ 2) (τ.symm k) := by
      intro k; simp
    rw [Finset.sum_congr rfl (fun k _ => hstep k),
      Equiv.sum_comp τ.symm (fun i => eigVal A (τ i) * ((Uᵀ *ᵥ x) i) ^ 2), h2]
    exact Finset.sum_congr rfl fun i _ => by rw [heig i]

/-! ## Courant–Fischer -/

/-- The subspace of vectors vanishing on a given finite set of coordinates. -/
noncomputable def coordKer (s : Finset (Fin n)) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker
    (LinearMap.pi (fun j : s => LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (j : Fin n)))

lemma mem_coordKer {s : Finset (Fin n)} {c : Fin n → ℝ} :
    c ∈ coordKer s ↔ ∀ i ∈ s, c i = 0 := by
  simp [coordKer, LinearMap.mem_ker, funext_iff, Subtype.forall]

lemma finrank_coordKer (s : Finset (Fin n)) : n - s.card ≤ Module.finrank ℝ (coordKer s) := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.pi (fun j : s => LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (j : Fin n)))
  have h2 : Module.finrank ℝ (LinearMap.range (LinearMap.pi
      (fun j : s => LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (j : Fin n)))) ≤ s.card := by
    calc _ ≤ Module.finrank ℝ (s → ℝ) := Submodule.finrank_le _
    _ = s.card := by simp
  simp only [Module.finrank_pi, Fintype.card_fin] at h
  simp only [coordKer]
  omega

/-- **Courant–Fischer, lower bound.**  If `V` is a subspace of dimension at least `k+1` on which
the quadratic form of `A` is at least `t`, then `t ≤ λ_{k+1}(A)`. -/
theorem le_eigVal_of_subspace {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : Fin n)
    (V : Submodule ℝ (Fin n → ℝ)) (hV : (k : ℕ) + 1 ≤ Module.finrank ℝ V) (t : ℝ)
    (hVt : ∀ x ∈ V, t * (x ⬝ᵥ x) ≤ x ⬝ᵥ A *ᵥ x) : t ≤ eigVal A k := by
  classical
  obtain ⟨W, hWt, hWt', hnorm, hquad⟩ := spectral_coords hA
  set e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    LinearEquiv.ofLinear (Matrix.mulVecLin Wᵀ) (Matrix.mulVecLin W)
      (by rw [← Matrix.mulVecLin_mul, hWt, Matrix.mulVecLin_one])
      (by rw [← Matrix.mulVecLin_mul, hWt', Matrix.mulVecLin_one]) with he
  set s : Finset (Fin n) := Finset.Iio k with hs
  have hcard : s.card = (k : ℕ) := Fin.card_Iio k
  have hVmap : Module.finrank ℝ (V.map (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) = Module.finrank ℝ V :=
    LinearEquiv.finrank_map_eq e V
  have hinf : 0 < Module.finrank ℝ
      ((V.map (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) ⊓ coordKer s : Submodule ℝ (Fin n → ℝ)) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq
      (V.map (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) (coordKer s)
    have h2 : Module.finrank ℝ ((V.map (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) ⊔ coordKer s
        : Submodule ℝ (Fin n → ℝ)) ≤ n := by
      simpa using Submodule.finrank_le
        ((V.map (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) ⊔ coordKer s : Submodule ℝ (Fin n → ℝ))
    have h3 := finrank_coordKer s
    have h4 : (k : ℕ) < n := k.isLt
    omega
  obtain ⟨c, hc, hc0⟩ :
      ∃ c ∈ (V.map (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) ⊓ coordKer s, c ≠ 0 := by
    have : Nontrivial ((V.map (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) ⊓ coordKer s
      : Submodule ℝ (Fin n → ℝ)) := Module.nontrivial_of_finrank_pos hinf
    obtain ⟨⟨x, hx⟩, hx0⟩ := exists_ne (0 : ((V.map (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
      ⊓ coordKer s : Submodule ℝ (Fin n → ℝ)))
    exact ⟨x, hx, by simpa using hx0⟩
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨y, hyV, hy⟩ := hc1
  have hy' : Wᵀ *ᵥ y = c := hy
  set x : Fin n → ℝ := W *ᵥ c with hx
  have hxV : x ∈ V := by
    have hxy : x = y := by rw [hx, ← hy', Matrix.mulVec_mulVec, hWt', Matrix.one_mulVec]
    rw [hxy]; exact hyV
  have hWx : Wᵀ *ᵥ x = c := by rw [hx, Matrix.mulVec_mulVec, hWt, Matrix.one_mulVec]
  have hpos : 0 < x ⬝ᵥ x := by
    rw [hnorm x, hWx]
    obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := Function.ne_iff.1 hc0
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, by positivity⟩
  have hup : x ⬝ᵥ A *ᵥ x ≤ eigVal A k * (x ⬝ᵥ x) := by
    rw [hquad x, hnorm x, hWx, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hik : (i : ℕ) < (k : ℕ)
    · have : c i = 0 := (mem_coordKer.1 hc2) i (by simp [hs]; exact hik)
      simp [this]
    · have : eigVal A i ≤ eigVal A k := eigVal_antitone A (by simpa using Nat.not_lt.1 hik)
      nlinarith [sq_nonneg (c i)]
  have := hVt x hxV
  nlinarith

/-- **Courant–Fischer, upper bound.**  If `V` is a subspace of dimension at least `n-k` on which
the quadratic form of `A` is at most `t`, then `λ_{k+1}(A) ≤ t`. -/
theorem eigVal_le_of_subspace {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : Fin n)
    (V : Submodule ℝ (Fin n → ℝ)) (hV : n - (k : ℕ) ≤ Module.finrank ℝ V) (t : ℝ)
    (hVt : ∀ x ∈ V, x ⬝ᵥ A *ᵥ x ≤ t * (x ⬝ᵥ x)) : eigVal A k ≤ t := by
  classical
  obtain ⟨W, hWt, hWt', hnorm, hquad⟩ := spectral_coords hA
  set e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    LinearEquiv.ofLinear (Matrix.mulVecLin Wᵀ) (Matrix.mulVecLin W)
      (by rw [← Matrix.mulVecLin_mul, hWt, Matrix.mulVecLin_one])
      (by rw [← Matrix.mulVecLin_mul, hWt', Matrix.mulVecLin_one]) with he
  set s : Finset (Fin n) := Finset.Ioi k with hs
  have hcard : s.card = n - 1 - (k : ℕ) := Fin.card_Ioi k
  have hVmap : Module.finrank ℝ (V.map (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) = Module.finrank ℝ V :=
    LinearEquiv.finrank_map_eq e V
  have hinf : 0 < Module.finrank ℝ
      ((V.map (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) ⊓ coordKer s : Submodule ℝ (Fin n → ℝ)) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq
      (V.map (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) (coordKer s)
    have h2 : Module.finrank ℝ ((V.map (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) ⊔ coordKer s
        : Submodule ℝ (Fin n → ℝ)) ≤ n := by
      simpa using Submodule.finrank_le
        ((V.map (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) ⊔ coordKer s : Submodule ℝ (Fin n → ℝ))
    have h3 := finrank_coordKer s
    have h4 : (k : ℕ) < n := k.isLt
    omega
  obtain ⟨c, hc, hc0⟩ :
      ∃ c ∈ (V.map (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) ⊓ coordKer s, c ≠ 0 := by
    have : Nontrivial ((V.map (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) ⊓ coordKer s
      : Submodule ℝ (Fin n → ℝ)) := Module.nontrivial_of_finrank_pos hinf
    obtain ⟨⟨x, hx⟩, hx0⟩ := exists_ne (0 : ((V.map (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
      ⊓ coordKer s : Submodule ℝ (Fin n → ℝ)))
    exact ⟨x, hx, by simpa using hx0⟩
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨y, hyV, hy⟩ := hc1
  have hy' : Wᵀ *ᵥ y = c := hy
  set x : Fin n → ℝ := W *ᵥ c with hx
  have hxV : x ∈ V := by
    have hxy : x = y := by rw [hx, ← hy', Matrix.mulVec_mulVec, hWt', Matrix.one_mulVec]
    rw [hxy]; exact hyV
  have hWx : Wᵀ *ᵥ x = c := by rw [hx, Matrix.mulVec_mulVec, hWt, Matrix.one_mulVec]
  have hpos : 0 < x ⬝ᵥ x := by
    rw [hnorm x, hWx]
    obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := Function.ne_iff.1 hc0
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, by positivity⟩
  have hlow : eigVal A k * (x ⬝ᵥ x) ≤ x ⬝ᵥ A *ᵥ x := by
    rw [hquad x, hnorm x, hWx, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hik : (k : ℕ) < (i : ℕ)
    · have : c i = 0 := (mem_coordKer.1 hc2) i (by simp [hs]; exact hik)
      simp [this]
    · have : eigVal A k ≤ eigVal A i := eigVal_antitone A (by simpa using Nat.not_lt.1 hik)
      nlinarith [sq_nonneg (c i)]
  have := hVt x hxV
  nlinarith

/-! ### Convenient corollaries -/

lemma quad_form (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ A *ᵥ x = ∑ i, ∑ j, A i j * x i * x j := by
  simp [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma quad_form_smul (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (c : ℝ) :
    (c • x) ⬝ᵥ A *ᵥ (c • x) = c ^ 2 * (x ⬝ᵥ A *ᵥ x) := by
  simp [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, sq, mul_assoc]

lemma dot_smul (x : Fin n → ℝ) (c : ℝ) : (c • x) ⬝ᵥ (c • x) = c ^ 2 * (x ⬝ᵥ x) := by
  simp [smul_dotProduct, dotProduct_smul, sq, mul_assoc]

/-- If the quadratic form of `A` is everywhere at most `t`, then every eigenvalue is at most
`t`. -/
lemma eigVal_le_of_forall {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : Fin n) (t : ℝ)
    (h : ∀ x : Fin n → ℝ, x ⬝ᵥ A *ᵥ x ≤ t * (x ⬝ᵥ x)) : eigVal A k ≤ t := by
  refine eigVal_le_of_subspace hA k ⊤ ?_ t (fun x _ => h x)
  simp

/-- If the quadratic form of `A` is everywhere at least `t`, then every eigenvalue is at least
`t`. -/
lemma le_eigVal_of_forall {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : Fin n) (t : ℝ)
    (h : ∀ x : Fin n → ℝ, t * (x ⬝ᵥ x) ≤ x ⬝ᵥ A *ᵥ x) : t ≤ eigVal A k := by
  refine le_eigVal_of_subspace hA k ⊤ ?_ t (fun x _ => h x)
  simp

/-- A single vector gives a lower bound for the largest eigenvalue. -/
lemma le_eigVal_top_of_vector {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : Fin n)
    (hk : (k : ℕ) = 0) (x : Fin n → ℝ) (hx : x ≠ 0) (t : ℝ)
    (h : t * (x ⬝ᵥ x) ≤ x ⬝ᵥ A *ᵥ x) : t ≤ eigVal A k := by
  refine le_eigVal_of_subspace hA k (Submodule.span ℝ {x}) (by rw [hk, finrank_span_singleton hx])
    t ?_
  rintro y hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rw [quad_form_smul, dot_smul]
  nlinarith [sq_nonneg c]

/-- A single vector gives an upper bound for the smallest eigenvalue. -/
lemma eigVal_last_le_of_vector {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : Fin n)
    (hk : (k : ℕ) = n - 1) (x : Fin n → ℝ) (hx : x ≠ 0) (t : ℝ)
    (h : x ⬝ᵥ A *ᵥ x ≤ t * (x ⬝ᵥ x)) : eigVal A k ≤ t := by
  refine eigVal_le_of_subspace hA k (Submodule.span ℝ {x}) ?_ t ?_
  · rw [finrank_span_singleton hx, hk]
    have := k.isLt
    omega
  · rintro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [quad_form_smul, dot_smul]
    nlinarith [sq_nonneg c]

/-! ### Uniqueness of the ordered spectrum, and behaviour under negation -/

/-- If an orthogonal change of coordinates diagonalizes `A` with an antitone list of diagonal
entries `g`, then `g` is the list of ordered eigenvalues of `A`. -/
theorem eigVal_eq_of_coords {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (W : Matrix (Fin n) (Fin n) ℝ) (hWt : Wᵀ * W = 1) (hWt' : W * Wᵀ = 1) (g : Fin n → ℝ)
    (hg : Antitone g) (hnorm : ∀ x : Fin n → ℝ, x ⬝ᵥ x = ∑ k, ((Wᵀ *ᵥ x) k) ^ 2)
    (hquad : ∀ x : Fin n → ℝ, x ⬝ᵥ A *ᵥ x = ∑ k, g k * ((Wᵀ *ᵥ x) k) ^ 2) :
    eigVal A = g := by
  classical
  set eW : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    LinearEquiv.ofLinear (Matrix.mulVecLin W) (Matrix.mulVecLin Wᵀ)
      (by rw [← Matrix.mulVecLin_mul, hWt', Matrix.mulVecLin_one])
      (by rw [← Matrix.mulVecLin_mul, hWt, Matrix.mulVecLin_one]) with heW
  have hmem : ∀ (s : Finset (Fin n)) (x : Fin n → ℝ),
      x ∈ (coordKer s).map (eW : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) → ∀ i ∈ s, (Wᵀ *ᵥ x) i = 0 := by
    rintro s x ⟨c, hc, rfl⟩ i hi
    have hWc : Wᵀ *ᵥ ((eW : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) c) = c := by
      show Wᵀ *ᵥ (W *ᵥ c) = c
      rw [Matrix.mulVec_mulVec, hWt, Matrix.one_mulVec]
    rw [hWc]
    exact (mem_coordKer.1 hc) i hi
  have hrank : ∀ s : Finset (Fin n),
      n - s.card ≤ Module.finrank ℝ ((coordKer s).map (eW : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) := by
    intro s
    rw [LinearEquiv.finrank_map_eq eW]
    exact finrank_coordKer s
  funext k
  refine le_antisymm ?_ ?_
  · refine eigVal_le_of_subspace hA k ((coordKer (Finset.Iio k)).map
      (eW : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) ?_ (g k) ?_
    · simpa [Fin.card_Iio] using hrank (Finset.Iio k)
    · intro x hx
      have hx0 := hmem _ x hx
      rw [hquad x, hnorm x, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hik : i < k
      · rw [hx0 i (Finset.mem_Iio.2 hik)]; simp
      · have : g i ≤ g k := hg (not_lt.1 hik)
        nlinarith [sq_nonneg ((Wᵀ *ᵥ x) i)]
  · refine le_eigVal_of_subspace hA k ((coordKer (Finset.Ioi k)).map
      (eW : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) ?_ (g k) ?_
    · have h := hrank (Finset.Ioi k)
      rw [Fin.card_Ioi] at h
      have := k.isLt
      omega
    · intro x hx
      have hx0 := hmem _ x hx
      rw [hquad x, hnorm x, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hik : k < i
      · rw [hx0 i (Finset.mem_Ioi.2 hik)]; simp
      · have : g k ≤ g i := hg (not_lt.1 hik)
        nlinarith [sq_nonneg ((Wᵀ *ᵥ x) i)]

/-- Reversing the sign of a symmetric matrix reverses the order of its eigenvalues. -/
theorem eigVal_neg {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : Fin n) :
    eigVal (-A) k = - eigVal A (Fin.rev k) := by
  classical
  have hnegA : (-A).IsHermitian := hA.neg
  obtain ⟨W, hWt, hWt', hnorm, hquad⟩ := spectral_coords hA
  set W' : Matrix (Fin n) (Fin n) ℝ := W.submatrix id Fin.rev with hW'
  have hcoord : ∀ (x : Fin n → ℝ) (k : Fin n), (W'ᵀ *ᵥ x) k = (Wᵀ *ᵥ x) (Fin.rev k) := by
    intro x k; simp [hW', mulVec, dotProduct]
  have hW'1 : W'ᵀ * W' = 1 := by
    ext i j
    have : (Wᵀ * W) (Fin.rev i) (Fin.rev j)
        = (1 : Matrix (Fin n) (Fin n) ℝ) (Fin.rev i) (Fin.rev j) := by rw [hWt]
    simpa [hW', Matrix.mul_apply, Matrix.one_apply, Fin.rev_inj] using this
  have hW'2 : W' * W'ᵀ = 1 := mul_eq_one_comm.2 hW'1
  have hgm : eigVal (-A) = fun k => - eigVal A (Fin.rev k) := by
    refine eigVal_eq_of_coords hnegA W' hW'1 hW'2 _ ?_ ?_ ?_
    · intro i j hij
      simpa using eigVal_antitone A (Fin.rev_le_rev.2 hij)
    · intro x
      rw [hnorm x]
      simp only [hcoord]
      exact (Equiv.sum_comp Fin.revPerm (fun i => ((Wᵀ *ᵥ x) i) ^ 2)).symm
    · intro x
      have : x ⬝ᵥ (-A) *ᵥ x = - (x ⬝ᵥ A *ᵥ x) := by
        simp [Matrix.neg_mulVec, dotProduct_neg]
      rw [this, hquad x]
      simp only [hcoord]
      rw [← Equiv.sum_comp Fin.revPerm (fun i => eigVal A i * ((Wᵀ *ᵥ x) i) ^ 2), ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp
  rw [hgm]

/-! ### Explicit quadratic forms -/

lemma dotProduct_self (x : Fin n → ℝ) : x ⬝ᵥ x = ∑ i, (x i) ^ 2 := by simp [dotProduct, sq]

lemma dotProduct_self_nonneg (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x := by
  rw [dotProduct_self]; positivity

lemma sq_sum_le_card (x : Fin n → ℝ) : (∑ i, x i) ^ 2 ≤ (n : ℝ) * (x ⬝ᵥ x) := by
  rw [dotProduct_self]
  simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := x)

lemma sum_supported_pair {p q : Fin n} (hpq : p ≠ q) (f : Fin n → ℝ)
    (hf : ∀ j, j ≠ p → j ≠ q → f j = 0) : ∑ j, f j = f p + f q := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ ({p, q} : Finset (Fin n)))
    (fun j _ hj => hf j (by simp at hj; tauto) (by simp at hj; tauto))]
  rw [Finset.sum_pair hpq]

/-- The quadratic form of `A` at a vector supported on two coordinates. -/
lemma quad_form_pair (A : Matrix (Fin n) (Fin n) ℝ) {p q : Fin n} (hpq : p ≠ q) (u v : ℝ) :
    (fun t => if t = p then u else if t = q then v else 0) ⬝ᵥ A *ᵥ
      (fun t => if t = p then u else if t = q then v else 0)
      = A p p * u ^ 2 + (A p q + A q p) * u * v + A q q * v ^ 2 := by
  classical
  rw [quad_form]
  rw [sum_supported_pair hpq _ (fun i hip hiq => by
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hip, hiq])]
  rw [sum_supported_pair hpq _ (fun j hjp hjq => by simp [hjp, hjq]),
    sum_supported_pair hpq _ (fun j hjp hjq => by simp [hjp, hjq])]
  simp [Ne.symm hpq]
  ring

lemma dot_pair {p q : Fin n} (hpq : p ≠ q) (u v : ℝ) :
    (fun t => if t = p then u else if t = q then v else 0) ⬝ᵥ
      (fun t => if t = p then u else if t = q then v else 0) = u ^ 2 + v ^ 2 := by
  classical
  rw [dotProduct]
  rw [sum_supported_pair hpq _ (fun j hjp hjq => by simp [hjp, hjq])]
  simp [Ne.symm hpq]
  ring

/-- `twoParam n d e` is the `n × n` matrix with `d` on the diagonal and `e` off it. -/
def twoParam (n : ℕ) (d e : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i = j then d else e

lemma twoParam_herm (d e : ℝ) : (twoParam n d e).IsHermitian := by
  ext i j
  simp [twoParam, Matrix.conjTranspose_apply, eq_comm]

lemma quad_form_twoParam (d e : ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (twoParam n d e) *ᵥ x = (d - e) * (x ⬝ᵥ x) + e * (∑ i, x i) ^ 2 := by
  rw [quad_form, dotProduct_self]
  have key : ∀ i, ∑ j, (twoParam n d e) i j * x i * x j
      = (d - e) * (x i) ^ 2 + e * (x i * ∑ j, x j) := by
    intro i
    simp only [twoParam, Matrix.of_apply]
    have h1 : ∀ j, (if i = j then d else e) * x i * x j
        = e * x i * x j + (if i = j then (d - e) * x i * x j else 0) := by
      intro j; split <;> ring
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true, ← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-! ### Eigenvectors -/

/-- Diagonalization with the *ordered* eigenvalues: `A = W * diagonal (eigVal A) * Wᵀ` for an
orthogonal matrix `W`. -/
theorem spectral_diag {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    ∃ W : Matrix (Fin n) (Fin n) ℝ, Wᵀ * W = 1 ∧ W * Wᵀ = 1 ∧
      A = W * diagonal (eigVal A) * Wᵀ := by
  classical
  set U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hUdef
  have hUt : Uᵀ * U = 1 := by
    have := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
    rw [star_eq_conjTranspose] at this
    simpa [hUdef] using this
  have hUt' : U * Uᵀ = 1 := mul_eq_one_comm.2 hUt
  have hspec : A = U * diagonal hA.eigenvalues * Uᵀ := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [conjStarAlgAut_apply, star_eq_conjTranspose]
    simp [hUdef]
  set σ : Fin n ≃ Fin (Fintype.card (Fin n)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm with hσ
  set τ : Equiv.Perm (Fin n) := σ.trans (finCongr (Fintype.card_fin n)) with hτ
  have heig : ∀ i, hA.eigenvalues i = eigVal A (τ i) := by
    intro i
    simp [eigVal, hA, Matrix.IsHermitian.eigenvalues, hτ, hσ]
  refine ⟨U.submatrix id τ.symm, ?_, ?_, ?_⟩
  · ext i j
    have h : (Uᵀ * U) (τ.symm i) (τ.symm j)
        = (1 : Matrix (Fin n) (Fin n) ℝ) (τ.symm i) (τ.symm j) := by rw [hUt]
    simpa [Matrix.mul_apply, Matrix.one_apply, (τ.symm).injective.eq_iff] using h
  · ext i j
    have h : (U * Uᵀ) i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by rw [hUt']
    simpa [Matrix.mul_apply, Matrix.one_apply, Equiv.sum_comp τ.symm (fun k => U i k * U j k)]
      using h
  · ext i j
    have hR : (U.submatrix id τ.symm * diagonal (eigVal A) * (U.submatrix id τ.symm)ᵀ) i j
        = ∑ k, U i (τ.symm k) * eigVal A k * U j (τ.symm k) := by
      simp [Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq', mul_comm, mul_assoc]
    rw [hR, ← Equiv.sum_comp τ (fun k => U i (τ.symm k) * eigVal A k * U j (τ.symm k))]
    simp only [Equiv.symm_apply_apply]
    conv_lhs => rw [hspec]
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq', heig, mul_comm,
      mul_left_comm]

lemma quad_of_diag {A W : Matrix (Fin n) (Fin n) ℝ} (d : Fin n → ℝ)
    (h3 : A = W * diagonal d * Wᵀ) (x : Fin n → ℝ) :
    x ⬝ᵥ A *ᵥ x = ∑ j, d j * ((Wᵀ *ᵥ x) j)^2 := by
  subst h3
  rw [show W * diagonal d * Wᵀ = W * (diagonal d * Wᵀ) by rw [mul_assoc]]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  simp [dotProduct, Matrix.mulVec_diagonal, sq, mul_left_comm]

lemma norm_of_orth {W : Matrix (Fin n) (Fin n) ℝ} (h2 : W * Wᵀ = 1) (x : Fin n → ℝ) :
    x ⬝ᵥ x = ∑ j, ((Wᵀ *ᵥ x) j)^2 := by
  have h : (Wᵀ *ᵥ x) ⬝ᵥ (Wᵀ *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, ← mulVec_transpose, transpose_transpose, mulVec_mulVec, h2, one_mulVec]
  rw [← h, dotProduct_self]

/-- Every ordered eigenvalue has a unit eigenvector. -/
theorem exists_eigenvector {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : Fin n) :
    ∃ v : Fin n → ℝ, v ⬝ᵥ v = 1 ∧ A *ᵥ v = eigVal A k • v := by
  obtain ⟨W, h1, h2, h3⟩ := spectral_diag hA
  set e : Fin n → ℝ := Pi.single k 1 with he
  have hd : (diagonal (eigVal A)) *ᵥ e = eigVal A k • e := by
    funext i
    rw [Matrix.mulVec_diagonal]
    by_cases h : i = k
    · subst h; simp [he]
    · simp [he, Pi.single_eq_of_ne h]
  refine ⟨W *ᵥ e, ?_, ?_⟩
  · rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, h1, one_mulVec]
    simp [he, dotProduct, Pi.single_apply]
  · rw [mulVec_mulVec]
    conv_lhs => rw [h3]
    rw [mul_assoc, mul_assoc, h1, mul_one, ← mulVec_mulVec, hd, mulVec_smul]

/-- A maximizer of the Rayleigh quotient is an eigenvector for the largest eigenvalue. -/
theorem eigenvector_of_max {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : Fin n)
    (hk : (k : ℕ) = 0) (x : Fin n → ℝ) (h : eigVal A k * (x ⬝ᵥ x) ≤ x ⬝ᵥ A *ᵥ x) :
    A *ᵥ x = eigVal A k • x := by
  classical
  obtain ⟨W, h1, h2, h3⟩ := spectral_diag hA
  set c : Fin n → ℝ := Wᵀ *ᵥ x with hc
  have hle : ∀ j, eigVal A j ≤ eigVal A k :=
    fun j => eigVal_antitone A (by rw [Fin.le_def, hk]; exact Nat.zero_le _)
  have hq := quad_of_diag (eigVal A) h3 x
  have hn := norm_of_orth h2 x
  have hsum : ∑ j, (eigVal A k - eigVal A j) * (c j)^2 ≤ 0 := by
    have hrw : ∑ j, (eigVal A k - eigVal A j) * (c j)^2
        = eigVal A k * (x ⬝ᵥ x) - x ⬝ᵥ A *ᵥ x := by
      rw [hq, hn, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hrw]; linarith
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (eigVal A k - eigVal A j) * (c j)^2 :=
    fun j _ => mul_nonneg (by linarith [hle j]) (sq_nonneg _)
  have hzero : ∀ j, (eigVal A k - eigVal A j) * (c j)^2 = 0 := by
    intro j
    have h0 : ∑ j, (eigVal A k - eigVal A j) * (c j)^2 = 0 :=
      le_antisymm hsum (Finset.sum_nonneg hnn)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)
  have hdc : ∀ j, eigVal A j * c j = eigVal A k * c j := by
    intro j
    rcases mul_eq_zero.1 (hzero j) with h' | h'
    · have heq : eigVal A j = eigVal A k := by linarith
      rw [heq]
    · have hcj : c j = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h'
      rw [hcj]; ring
  have hx : W *ᵥ c = x := by rw [hc, mulVec_mulVec, h2, one_mulVec]
  have hAx : A *ᵥ x = W *ᵥ (diagonal (eigVal A) *ᵥ c) := by
    conv_lhs => rw [h3]
    rw [hc, mulVec_mulVec, mulVec_mulVec, mul_assoc]
  rw [hAx, show (diagonal (eigVal A)) *ᵥ c = eigVal A k • c by
    funext j; rw [Matrix.mulVec_diagonal]; exact hdc j, mulVec_smul, hx]

/-- Two distinct ordered eigenvalues have orthonormal eigenvectors. -/
theorem exists_eigenvector_pair {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k l : Fin n)
    (hkl : k ≠ l) :
    ∃ v w : Fin n → ℝ, v ⬝ᵥ v = 1 ∧ w ⬝ᵥ w = 1 ∧ v ⬝ᵥ w = 0 ∧
      A *ᵥ v = eigVal A k • v ∧ A *ᵥ w = eigVal A l • w := by
  obtain ⟨W, h1, h2, h3⟩ := spectral_diag hA
  set e : Fin n → Fin n → ℝ := fun j => Pi.single j 1 with he
  have key : ∀ j : Fin n, A *ᵥ (W *ᵥ (e j)) = eigVal A j • (W *ᵥ e j) := by
    intro j
    have hd : (diagonal (eigVal A)) *ᵥ (e j) = eigVal A j • (e j) := by
      funext i
      rw [Matrix.mulVec_diagonal]
      by_cases h : i = j
      · subst h; simp [he]
      · simp [he, Pi.single_eq_of_ne h]
    rw [mulVec_mulVec]
    conv_lhs => rw [h3]
    rw [mul_assoc, mul_assoc, h1, mul_one, ← mulVec_mulVec, hd, mulVec_smul]
  have hdot : ∀ j j' : Fin n, (W *ᵥ (e j)) ⬝ᵥ (W *ᵥ (e j')) = if j = j' then 1 else 0 := by
    intro j j'
    rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, h1, one_mulVec]
    simp [he, dotProduct, Pi.single_apply, eq_comm]
  refine ⟨W *ᵥ e k, W *ᵥ e l, ?_, ?_, ?_, key k, key l⟩
  · simpa using hdot k k
  · simpa using hdot l l
  · rw [hdot k l, if_neg hkl]

lemma symm_dot {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (x y : Fin n → ℝ) :
    x ⬝ᵥ A *ᵥ y = (A *ᵥ x) ⬝ᵥ y := by
  have hsym : Aᵀ = A := by
    ext i j
    have := congrFun (congrFun hA i) j
    simpa [Matrix.conjTranspose_apply] using this
  rw [dotProduct_mulVec, ← mulVec_transpose, hsym]

lemma mixed_of_sum_zero {x : Fin n → ℝ} (hx : x ≠ 0) (hs : ∑ i, x i = 0) :
    (∃ i, 0 < x i) ∧ (∃ j, x j < 0) := by
  constructor
  · by_contra h
    push_neg at h
    exact hx (funext fun i =>
      (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => h i)).1 hs i (Finset.mem_univ i))
  · by_contra h
    push_neg at h
    exact hx (funext fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h i)).1 hs i (Finset.mem_univ i))

lemma sum_pos_of_dot_one {z : Fin n → ℝ} (hz : ∀ i, 0 ≤ z i) (h1 : z ⬝ᵥ z = 1) :
    0 < ∑ i, z i := by
  rcases lt_or_eq_of_le (Finset.sum_nonneg (fun i _ => hz i)) with h | h
  · exact h
  · exfalso
    have hall : ∀ i, z i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hz i)).1 h.symm i (Finset.mem_univ i)
    rw [dotProduct_self] at h1
    simp [hall] at h1

/-! ## The set `S n [a,b]` and the extremal values -/

/-- `SymIcc n a b` is the set `S_n([a,b])` of real symmetric `n × n` matrices all of whose
entries lie in `[a,b]`. -/
def SymIcc (n : ℕ) (a b : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | A.IsHermitian ∧ ∀ i j, A i j ∈ Set.Icc a b}

/-- The set of values of the `(k+1)`-st largest eigenvalue on `S_n([a,b])`. -/
noncomputable def eigRange (n : ℕ) (a b : ℝ) (k : Fin n) : Set ℝ :=
  (fun A => eigVal A k) '' SymIcc n a b

/-- The minimum of `λ₁` on `S_n([a,b])`, formula (2.1). -/
noncomputable def L1 (n : ℕ) (a b : ℝ) : ℝ :=
  if 0 ≤ a then n * a else if 0 ≤ b then a else a - b

/-- The maximum of `λ₁` on `S_n([a,b])`, formula (2.3). -/
noncomputable def U1 (n : ℕ) (a b : ℝ) : ℝ :=
  if 0 ≤ a + b then n * b
  else if Even n then n * (b - a) / 2
  else (n * b + Real.sqrt (((n : ℝ) ^ 2 - 1) * a ^ 2 + b ^ 2)) / 2

/-- The maximum of `λₙ` on `S_n([a,b])`, formula (2.2). -/
noncomputable def Un (n : ℕ) (a b : ℝ) : ℝ :=
  if 0 ≤ a then b - a else if 0 ≤ b then b else n * b

/-- The minimum of `λₙ` on `S_n([a,b])`, formula (2.4). -/
noncomputable def Ln (n : ℕ) (a b : ℝ) : ℝ :=
  if a + b ≤ 0 then n * a
  else if Even n then n * (a - b) / 2
  else (n * a - Real.sqrt (a ^ 2 + ((n : ℝ) ^ 2 - 1) * b ^ 2)) / 2

/-! ### Duality under `A ↦ -A` -/

lemma neg_mem_SymIcc {n : ℕ} {a b : ℝ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ SymIcc n a b) :
    -A ∈ SymIcc n (-b) (-a) := by
  obtain ⟨h1, h2⟩ := hA
  refine ⟨h1.neg, fun i j => ?_⟩
  have := h2 i j
  simp only [Set.mem_Icc] at this ⊢
  simp only [Matrix.neg_apply]
  constructor <;> linarith [this.1, this.2]

lemma eigRange_neg (n : ℕ) (a b : ℝ) (k : Fin n) :
    eigRange n a b k = (fun t : ℝ => -t) '' eigRange n (-b) (-a) (Fin.rev k) := by
  ext t
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨-(eigVal A k), ⟨-A, neg_mem_SymIcc hA, ?_⟩, by ring⟩
    show eigVal (-A) (Fin.rev k) = -eigVal A k
    rw [eigVal_neg hA.1, Fin.rev_rev]
  · rintro ⟨s, ⟨B, hB, rfl⟩, rfl⟩
    refine ⟨-B, ?_, ?_⟩
    · have := neg_mem_SymIcc hB
      simpa using this
    · show eigVal (-B) k = -eigVal B (Fin.rev k)
      rw [eigVal_neg hB.1]

lemma twoParam_mem {a b d e : ℝ} (hd : d ∈ Set.Icc a b) (he : e ∈ Set.Icc a b) :
    twoParam n d e ∈ SymIcc n a b := by
  refine ⟨twoParam_herm d e, fun i j => ?_⟩
  simp only [twoParam, Matrix.of_apply]
  split <;> assumption

lemma eigRange_neg' (n : ℕ) (a b : ℝ) (k : Fin n) :
    (fun t : ℝ => -t) '' eigRange n a b k = eigRange n (-b) (-a) (Fin.rev k) := by
  have h := eigRange_neg n (-b) (-a) (Fin.rev k)
  rw [neg_neg, neg_neg, Fin.rev_rev] at h
  exact h.symm

lemma Un_eq {n : ℕ} {a b : ℝ} (hab : a ≤ b) : Un n a b = - L1 n (-b) (-a) := by
  unfold Un L1
  split_ifs <;> nlinarith

lemma Ln_eq {n : ℕ} {a b : ℝ} : Ln n a b = - U1 n (-b) (-a) := by
  unfold Ln U1
  split_ifs <;> first | (exfalso; linarith) | ring_nf

lemma isGreatest_of_isLeast_neg {S : Set ℝ} {u : ℝ}
    (h : IsLeast ((fun t : ℝ => -t) '' S) (-u)) : IsGreatest S u := by
  obtain ⟨⟨x, hx, hxu⟩, hlb⟩ := h
  constructor
  · have : x = u := by linarith [hxu]
    exact this ▸ hx
  · intro y hy
    have := hlb ⟨y, hy, rfl⟩
    linarith

lemma isLeast_of_isGreatest_neg {S : Set ℝ} {u : ℝ}
    (h : IsGreatest ((fun t : ℝ => -t) '' S) (-u)) : IsLeast S u := by
  obtain ⟨⟨x, hx, hxu⟩, hub⟩ := h
  constructor
  · have : x = u := by linarith [hxu]
    exact this ▸ hx
  · intro y hy
    have := hub ⟨y, hy, rfl⟩
    linarith

/-! ## The minimum of `λ₁`, formula (2.1) -/

lemma L1_le_eigVal {m : ℕ} {a b : ℝ} {A : Matrix (Fin (m+2)) (Fin (m+2)) ℝ}
    (hA : A ∈ SymIcc (m+2) a b) : L1 (m+2) a b ≤ eigVal A 0 := by
  have hp : (0 : Fin (m+2)) ≠ 1 := by simp
  unfold L1
  split_ifs with ha hb
  · -- `0 ≤ a`: test with the all-ones vector
    refine le_eigVal_top_of_vector hA.1 0 rfl (fun _ : Fin (m+2) => (1:ℝ)) (by
      intro h; have := congrFun h 0; simp at this) _ ?_
    have h1 : (fun _ : Fin (m+2) => (1:ℝ)) ⬝ᵥ (fun _ => (1:ℝ)) = ((m+2 : ℕ) : ℝ) := by
      simp [dotProduct]
    have h2 : (fun _ : Fin (m+2) => (1:ℝ)) ⬝ᵥ A *ᵥ (fun _ => (1:ℝ)) = ∑ i, ∑ j, A i j := by
      rw [quad_form]; simp
    rw [h1, h2]
    calc (((m+2:ℕ):ℝ) * a) * ((m+2:ℕ):ℝ) = ∑ _i : Fin (m+2), ∑ _j : Fin (m+2), a := by
          simp [Finset.sum_const]; ring
    _ ≤ ∑ i : Fin (m+2), ∑ j : Fin (m+2), A i j :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => (hA.2 i j).1
  · -- `a ≤ 0 ≤ b`: test with a coordinate vector
    refine le_eigVal_top_of_vector hA.1 0 rfl
      (fun t => if t = 0 then (1:ℝ) else if t = 1 then 0 else 0) (by
        intro h; have := congrFun h 0; simp at this) _ ?_
    rw [quad_form_pair A hp 1 0, dot_pair hp 1 0]
    have := (hA.2 0 0).1
    nlinarith
  · -- `b ≤ 0`: test with a difference of two coordinate vectors
    refine le_eigVal_top_of_vector hA.1 0 rfl
      (fun t => if t = 0 then (1:ℝ) else if t = 1 then -1 else 0) (by
        intro h; have := congrFun h 0; simp at this) _ ?_
    rw [quad_form_pair A hp 1 (-1), dot_pair hp 1 (-1)]
    have h1 := (hA.2 0 0).1
    have h2 := (hA.2 1 1).1
    have h3 := (hA.2 0 1).2
    have h4 := (hA.2 1 0).2
    nlinarith

lemma L1_mem {m : ℕ} {a b : ℝ} (hab : a ≤ b) : L1 (m+2) a b ∈ eigRange (m+2) a b 0 := by
  have key : ∀ e : ℝ, e ∈ Set.Icc a b →
      eigVal (twoParam (m+2) a e) 0 ≤ L1 (m+2) a b →
      L1 (m+2) a b ∈ eigRange (m+2) a b 0 := by
    intro e he hle
    refine ⟨twoParam (m+2) a e, twoParam_mem ⟨le_refl a, hab⟩ he, ?_⟩
    exact le_antisymm hle (L1_le_eigVal (twoParam_mem ⟨le_refl a, hab⟩ he))
  by_cases ha : 0 ≤ a
  · refine key a ⟨le_refl a, hab⟩ ?_
    rw [show L1 (m+2) a b = ((m+2:ℕ):ℝ) * a by unfold L1; simp [ha]]
    refine eigVal_le_of_forall (twoParam_herm a a) 0 _ (fun x => ?_)
    rw [quad_form_twoParam]
    have := sq_sum_le_card (n := m+2) x
    nlinarith [dotProduct_self_nonneg x]
  · by_cases hb : 0 ≤ b
    · refine key 0 ⟨(not_le.1 ha).le, hb⟩ ?_
      rw [show L1 (m+2) a b = a by unfold L1; simp [ha, hb]]
      refine eigVal_le_of_forall (twoParam_herm a 0) 0 _ (fun x => ?_)
      rw [quad_form_twoParam]
      simp
    · refine key b ⟨hab, le_refl b⟩ ?_
      rw [show L1 (m+2) a b = a - b by unfold L1; simp [ha, hb]]
      refine eigVal_le_of_forall (twoParam_herm a b) 0 _ (fun x => ?_)
      rw [quad_form_twoParam]
      have hb' : b ≤ 0 := (not_le.1 hb).le
      nlinarith [sq_nonneg (∑ i, x i)]

/-! ## A general upper bound for the quadratic form on `S_N([a,b])` -/

/-- A nonnegative quadratic form criterion. -/
theorem quad_nonneg' {A B C u v : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (h : B ^ 2 ≤ 4 * A * C) :
    0 ≤ A * u ^ 2 + B * u * v + C * v ^ 2 := by
  rcases eq_or_lt_of_le hA with hA0 | hA0
  · have hB : B = 0 := by nlinarith [sq_nonneg B]
    subst hB
    nlinarith [sq_nonneg v]
  · nlinarith [sq_nonneg (2*A*u + B*v), sq_nonneg v, mul_pos hA0 hA0]

/-- The two-block estimate: the maximum of `b(u²+v²) + 2auv` under the constraints
`u² ≤ ps`, `v² ≤ qt` is controlled by any `L` dominating the relevant `2 × 2` spectrum. -/
theorem key_alg {a b L : ℝ} (p q u v s t : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hu2 : u ^ 2 ≤ p * s) (hv2 : v ^ 2 ≤ q * t) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hL0 : 0 ≤ L) (hbp : b * p ≤ L) (hbq : b * q ≤ L)
    (hG : a ^ 2 * (p * q) ≤ (L - b * p) * (L - b * q)) :
    b * (u ^ 2 + v ^ 2) + 2 * a * u * v ≤ L * (s + t) := by
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · have hu : u = 0 := by nlinarith [sq_nonneg u]
    subst hu
    rcases le_or_gt 0 b with hb | hb
    · nlinarith
    · nlinarith [sq_nonneg v]
  rcases eq_or_lt_of_le hq with hq0 | hq0
  · have hv : v = 0 := by nlinarith [sq_nonneg v]
    subst hv
    rcases le_or_gt 0 b with hb | hb
    · nlinarith
    · nlinarith [sq_nonneg u]
  have h1 : (0:ℝ) ≤ q * (L - b*p) := mul_nonneg hq (by linarith)
  have h2 : (0:ℝ) ≤ p * (L - b*q) := mul_nonneg hp (by linarith)
  have h3 : (-(2*a*(p*q))) ^ 2 ≤ 4 * (q*(L - b*p)) * (p*(L - b*q)) := by nlinarith [mul_pos hp0 hq0]
  have hE := quad_nonneg' (u := u) (v := v) h1 h2 h3
  nlinarith [mul_pos hp0 hq0, mul_nonneg hL0 (sub_nonneg.2 hu2), mul_nonneg hL0 (sub_nonneg.2 hv2)]

/-- Splitting a vector into its positive and negative parts bounds the quadratic form of any
`A ∈ S_N([a,b])` by a two-variable expression. -/
theorem quad_le_blocks {a b : ℝ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ SymIcc n a b)
    (x : Fin n → ℝ) :
    x ⬝ᵥ A *ᵥ x ≤ b * ((∑ i ∈ Finset.univ.filter (fun i : Fin n => 0 < x i), x i) ^ 2
        + (∑ i ∈ Finset.univ.filter (fun i : Fin n => x i < 0), x i) ^ 2)
        + 2*a*((∑ i ∈ Finset.univ.filter (fun i : Fin n => 0 < x i), x i)
            * (∑ i ∈ Finset.univ.filter (fun i : Fin n => x i < 0), x i)) := by
  classical
  set P := Finset.univ.filter (fun i : Fin n => 0 < x i) with hP
  set Q := Finset.univ.filter (fun i : Fin n => x i < 0) with hQ
  have hPQ : Disjoint P Q := by
    rw [hP, hQ, Finset.disjoint_filter]
    intro i _ hi
    simp only [not_lt]
    linarith
  have hblock : ∀ (S T : Finset (Fin n)) (c : ℝ),
      (∀ i ∈ S, ∀ j ∈ T, A i j * x i * x j ≤ c * (x i * x j)) →
      ∑ i ∈ S, ∑ j ∈ T, A i j * x i * x j ≤ c * ((∑ i ∈ S, x i) * (∑ j ∈ T, x j)) := by
    intro S T c h
    calc ∑ i ∈ S, ∑ j ∈ T, A i j * x i * x j
        ≤ ∑ i ∈ S, ∑ j ∈ T, c * (x i * x j) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => h i hi j hj
      _ = c * ((∑ i ∈ S, x i) * (∑ j ∈ T, x j)) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  have hmem : ∀ i, i ∉ P ∪ Q → x i = 0 := by
    intro i hi
    simp only [hP, hQ, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or,
      not_lt] at hi
    linarith [hi.1, hi.2]
  have hPpos : ∀ i ∈ P, 0 < x i := by intro i hi; rw [hP] at hi; simpa using hi
  have hQneg : ∀ i ∈ Q, x i < 0 := by intro i hi; rw [hQ] at hi; simpa using hi
  rw [quad_form]
  rw [← Finset.sum_subset (Finset.subset_univ (P ∪ Q)) (fun i _ hi => by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hmem i hi]; ring)]
  rw [Finset.sum_congr rfl (fun i _ => (Finset.sum_subset (Finset.subset_univ (P ∪ Q))
    (fun j _ hj => by rw [hmem j hj]; ring)).symm)]
  rw [Finset.sum_union hPQ]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_union hPQ (f := fun j => A i j * x i * x j)),
    Finset.sum_congr rfl (fun i _ => Finset.sum_union hPQ (f := fun j => A i j * x i * x j))]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have b1 : ∑ i ∈ P, ∑ j ∈ P, A i j * x i * x j ≤ b * ((∑ i ∈ P, x i) * (∑ j ∈ P, x j)) :=
    hblock P P b (fun i hi j hj => by
      have hw : (0:ℝ) ≤ x i * x j := le_of_lt (mul_pos (hPpos i hi) (hPpos j hj))
      calc A i j * x i * x j = A i j * (x i * x j) := by ring
        _ ≤ b * (x i * x j) := mul_le_mul_of_nonneg_right (hA.2 i j).2 hw)
  have b2 : ∑ i ∈ Q, ∑ j ∈ Q, A i j * x i * x j ≤ b * ((∑ i ∈ Q, x i) * (∑ j ∈ Q, x j)) :=
    hblock Q Q b (fun i hi j hj => by
      have hw : (0:ℝ) ≤ x i * x j := le_of_lt (mul_pos_of_neg_of_neg (hQneg i hi) (hQneg j hj))
      calc A i j * x i * x j = A i j * (x i * x j) := by ring
        _ ≤ b * (x i * x j) := mul_le_mul_of_nonneg_right (hA.2 i j).2 hw)
  have b3 : ∑ i ∈ P, ∑ j ∈ Q, A i j * x i * x j ≤ a * ((∑ i ∈ P, x i) * (∑ j ∈ Q, x j)) :=
    hblock P Q a (fun i hi j hj => by
      have hw : x i * x j ≤ 0 := le_of_lt (mul_neg_of_pos_of_neg (hPpos i hi) (hQneg j hj))
      calc A i j * x i * x j = A i j * (x i * x j) := by ring
        _ ≤ a * (x i * x j) := mul_le_mul_of_nonpos_right (hA.2 i j).1 hw)
  have b4 : ∑ i ∈ Q, ∑ j ∈ P, A i j * x i * x j ≤ a * ((∑ i ∈ Q, x i) * (∑ j ∈ P, x j)) :=
    hblock Q P a (fun i hi j hj => by
      have hw : x i * x j ≤ 0 := le_of_lt (mul_neg_of_neg_of_pos (hQneg i hi) (hPpos j hj))
      calc A i j * x i * x j = A i j * (x i * x j) := by ring
        _ ≤ a * (x i * x j) := mul_le_mul_of_nonpos_right (hA.2 i j).1 hw)
  nlinarith [b1, b2, b3, b4]

/-- Master upper bound for the quadratic form of an arbitrary `A ∈ S_N([a,b])`. -/
theorem quad_le_of_bounds {a b L : ℝ} (hL0 : 0 ≤ L)
    (hbp : ∀ j : ℕ, j ≤ n → b * (j : ℝ) ≤ L)
    (hG : ∀ i j : ℕ, i + j ≤ n → a ^ 2 * ((i : ℝ) * (j : ℝ)) ≤ (L - b * (i : ℝ)) * (L - b * (j : ℝ)))
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ SymIcc n a b) (x : Fin n → ℝ) :
    x ⬝ᵥ A *ᵥ x ≤ L * (x ⬝ᵥ x) := by
  classical
  set P := Finset.univ.filter (fun i : Fin n => 0 < x i) with hP
  set Q := Finset.univ.filter (fun i : Fin n => x i < 0) with hQ
  have hPQ : Disjoint P Q := by
    rw [hP, hQ, Finset.disjoint_filter]; intro i _ hi; simp only [not_lt]; linarith
  have hcard : P.card + Q.card ≤ n := by
    have h1 := Finset.card_union_of_disjoint hPQ
    have h2 := Finset.card_le_univ (P ∪ Q)
    rw [h1] at h2
    simpa using h2
  set u : ℝ := ∑ i ∈ P, x i with hu
  set v : ℝ := ∑ i ∈ Q, x i with hv
  set s : ℝ := ∑ i ∈ P, (x i) ^ 2 with hs
  set t : ℝ := ∑ i ∈ Q, (x i) ^ 2 with ht
  have hu2 : u ^ 2 ≤ (P.card : ℝ) * s := sq_sum_le_card_mul_sum_sq
  have hv2 : v ^ 2 ≤ (Q.card : ℝ) * t := sq_sum_le_card_mul_sum_sq
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => sq_nonneg _
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hst : s + t ≤ x ⬝ᵥ x := by
    rw [dotProduct_self, hs, ht, ← Finset.sum_union hPQ]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)
  have hkey := key_alg (a := a) (b := b) (L := L) (P.card : ℝ) (Q.card : ℝ) u v s t
    (by positivity) (by positivity) hu2 hv2 hs0 ht0 hL0
    (hbp P.card (by omega)) (hbp Q.card (by omega)) (hG P.card Q.card hcard)
  calc x ⬝ᵥ A *ᵥ x ≤ b*(u^2+v^2) + 2*a*(u*v) := quad_le_blocks hA x
    _ = b*(u^2+v^2) + 2*a*u*v := by ring
    _ ≤ L*(s+t) := hkey
    _ ≤ L * (x ⬝ᵥ x) := by nlinarith

/-! ## Two-block endpoint matrices -/

/-- `signMat n c r w` is the matrix with entries `c + r * w i * w j`. -/
def signMat (n : ℕ) (c r : ℝ) (w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => c + r * (w i * w j)

lemma signMat_herm (c r : ℝ) (w : Fin n → ℝ) : (signMat n c r w).IsHermitian := by
  ext i j
  simp only [signMat, Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
  ring

lemma quad_form_signMat (c r : ℝ) (w x : Fin n → ℝ) :
    x ⬝ᵥ (signMat n c r w) *ᵥ x = c * (∑ i, x i) ^ 2 + r * (∑ i, w i * x i) ^ 2 := by
  rw [quad_form]
  have h : ∀ i, ∑ j, (signMat n c r w) i j * x i * x j
      = c * (x i * ∑ j, x j) + r * ((w i * x i) * ∑ j, w j * x j) := by
    intro i
    simp only [signMat, Matrix.of_apply, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]
  ring

lemma signMat_mem {a b : ℝ} (hab : a ≤ b) (w : Fin n → ℝ) (hw : ∀ i, w i = 1 ∨ w i = -1) :
    signMat n ((a+b)/2) ((b-a)/2) w ∈ SymIcc n a b := by
  refine ⟨signMat_herm _ _ _, fun i j => ?_⟩
  simp only [signMat, Matrix.of_apply, Set.mem_Icc]
  rcases hw i with h1 | h1 <;> rcases hw j with h2 | h2 <;> rw [h1, h2] <;>
    constructor <;> linarith

/-- The two-block endpoint matrix `B_ε` of the solution, with `p` plus signs: its `(i,j)` entry
is `b` when `i` and `j` lie in the same block and `a` otherwise. -/
noncomputable def blockSign (N p : ℕ) (a b : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  signMat N ((a+b)/2) ((b-a)/2) (fun i => if (i:ℕ) < p then 1 else -1)

lemma blockSign_mem {N p : ℕ} {a b : ℝ} (hab : a ≤ b) : blockSign N p a b ∈ SymIcc N a b :=
  signMat_mem hab _ (fun i => by by_cases h : (i:ℕ) < p <;> simp [h])

lemma card_filter_lt (N p : ℕ) (hp : p ≤ N) :
    (Finset.univ.filter (fun i : Fin N => (i:ℕ) < p)).card = p := by
  classical
  have h : (Finset.univ.filter (fun i : Fin N => (i:ℕ) < p))
      = (Finset.range p).attachFin (fun m hm => lt_of_lt_of_le (Finset.mem_range.1 hm) hp) := by
    ext i; simp [Finset.mem_attachFin]
  rw [h, Finset.card_attachFin, Finset.card_range]

lemma card_filter_not_lt (N p : ℕ) (hp : p ≤ N) :
    (Finset.univ.filter (fun i : Fin N => ¬ (i:ℕ) < p)).card = N - p := by
  classical
  have h2 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin N))) (p := fun i : Fin N => (i:ℕ) < p)
  rw [card_filter_lt N p hp, Finset.card_univ, Fintype.card_fin] at h2
  omega

lemma sum_ite_lt (N p : ℕ) (hp : p ≤ N) (u v : ℝ) :
    ∑ i : Fin N, (if (i:ℕ) < p then u else v) = p * u + ((N:ℝ) - p) * v := by
  classical
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, card_filter_lt N p hp,
    card_filter_not_lt N p hp, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub hp]

/-! ## The maximum of `λ₁`, formula (2.3) -/

/-- The key algebraic step: nonnegativity of `L² - bL(p+q) + (b²-a²)pq` for the extremal `L`. -/
theorem G_nonneg {Nr a b L K : ℝ} (hL0 : 0 ≤ L) (hLN : Nr*b ≤ L)
    (hquad : L^2 - Nr*b*L + (b^2-a^2)*K = 0) (hD : b^2-a^2 ≤ 0)
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p+q ≤ Nr) (hqK : q*(Nr-q) ≤ K) :
    0 ≤ L^2 - b*L*(p+q) + (b^2-a^2)*(p*q) := by
  have hbq : b*q ≤ L := by rcases le_or_gt 0 b with hb|hb <;> nlinarith
  have hG0 : 0 ≤ L^2 - b*L*q := by nlinarith
  have hG1 : 0 ≤ L^2 - b*L*Nr + (b^2-a^2)*(q*(Nr-q)) := by nlinarith
  rcases eq_or_lt_of_le (show q ≤ Nr by linarith) with h|h
  · have hp0 : p = 0 := by linarith
    subst hp0; simpa [← h] using hG0
  · nlinarith [mul_nonneg hp (le_of_lt (sub_pos.2 h))]

/-- The quadratic form bound in the case `a + b ≤ 0`. -/
theorem quad_le_U1_aux {N : ℕ} {a b L K : ℝ} (hL0 : 0 ≤ L) (hLN : (N:ℝ)*b ≤ L)
    (hD : b^2 - a^2 ≤ 0)
    (hquad : L^2 - (N:ℝ)*b*L + (b^2-a^2)*K = 0)
    (hK : ∀ j : ℕ, j ≤ N → (j:ℝ)*((N:ℝ)-j) ≤ K)
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A ∈ SymIcc N a b) (x : Fin N → ℝ) :
    x ⬝ᵥ A *ᵥ x ≤ L * (x ⬝ᵥ x) := by
  refine quad_le_of_bounds hL0 ?_ ?_ hA x
  · intro j hj
    have hjN : (j:ℝ) ≤ (N:ℝ) := by exact_mod_cast hj
    have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    rcases le_or_gt 0 b with hb|hb
    · nlinarith
    · nlinarith
  · intro i j hij
    have hi0 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
    have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    have hijN : (i:ℝ) + (j:ℝ) ≤ (N:ℝ) := by exact_mod_cast hij
    have := G_nonneg hL0 hLN hquad hD (i:ℝ) (j:ℝ) hi0 hj0 hijN (hK j (by omega))
    nlinarith

lemma K_bound_even (N j : ℕ) : (j:ℝ)*((N:ℝ)-j) ≤ (N:ℝ)^2/4 := by
  nlinarith [sq_nonneg ((N:ℝ) - 2*j)]

lemma K_bound_odd {N : ℕ} (hN : ¬ Even N) (j : ℕ) : (j:ℝ)*((N:ℝ)-j) ≤ ((N:ℝ)^2-1)/4 := by
  have hNodd : N % 2 = 1 := Nat.not_even_iff.1 hN
  have hne : ((N:ℤ) - 2*(j:ℤ)) ≠ 0 := by omega
  have h1 : (1:ℤ) ≤ ((N:ℤ) - 2*(j:ℤ))^2 := by
    rcases lt_trichotomy ((N:ℤ) - 2*(j:ℤ)) 0 with h|h|h
    · nlinarith
    · exact absurd h hne
    · nlinarith
  have h2 : (1:ℝ) ≤ ((N:ℝ) - 2*(j:ℝ))^2 := by exact_mod_cast h1
  nlinarith

/-- Every eigenvalue of a matrix in `S_N([a,b])` is at most `U₁`. -/
theorem eigVal_le_U1 {N : ℕ} (hN : 1 ≤ N) {a b : ℝ} (hab : a ≤ b)
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A ∈ SymIcc N a b) (k : Fin N) :
    eigVal A k ≤ U1 N a b := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hN2 : (1:ℝ) ≤ (N:ℝ)^2 := by nlinarith
  refine eigVal_le_of_forall hA.1 k _ (fun x => ?_)
  unfold U1
  split_ifs with h1 h2
  · have hb : 0 ≤ b := by linarith
    refine quad_le_of_bounds (by positivity) ?_ ?_ hA x
    · intro j hj
      have hjN : (j:ℝ) ≤ (N:ℝ) := by exact_mod_cast hj
      nlinarith
    · intro i j hij
      have hi0 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
      have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      have hijN : (i:ℝ) + (j:ℝ) ≤ (N:ℝ) := by exact_mod_cast hij
      have ha2 : a^2 ≤ b^2 := by nlinarith
      have h3 : (i:ℝ)*(j:ℝ) ≤ ((N:ℝ)-i)*((N:ℝ)-j) := by nlinarith
      calc a^2 * ((i:ℝ)*(j:ℝ)) ≤ b^2 * ((i:ℝ)*(j:ℝ)) := by nlinarith [mul_nonneg hi0 hj0]
        _ ≤ b^2 * (((N:ℝ)-i)*((N:ℝ)-j)) := by nlinarith [sq_nonneg b]
        _ = ((N:ℝ)*b - b*i) * ((N:ℝ)*b - b*j) := by ring
  · have hD : b^2 - a^2 ≤ 0 := by nlinarith
    refine quad_le_U1_aux (K := (N:ℝ)^2/4) (by nlinarith) (by nlinarith) hD (by ring) ?_ hA x
    intro j _; exact K_bound_even N j
  · have hD : b^2 - a^2 ≤ 0 := by nlinarith
    set S : ℝ := Real.sqrt (((N:ℝ)^2 - 1)*a^2 + b^2) with hS
    have harg : 0 ≤ ((N:ℝ)^2 - 1)*a^2 + b^2 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hS0 : 0 ≤ S := Real.sqrt_nonneg _
    have hS2 : S^2 = ((N:ℝ)^2 - 1)*a^2 + b^2 := Real.sq_sqrt harg
    have hsq : ((N:ℝ)*b)^2 ≤ S^2 := by nlinarith [sq_nonneg b, sq_nonneg a]
    have hNb : (N:ℝ)*b ≤ S := by nlinarith
    have hL0 : 0 ≤ ((N:ℝ)*b + S)/2 := by nlinarith
    refine quad_le_U1_aux (K := ((N:ℝ)^2-1)/4) hL0 (by nlinarith)
      hD (by linear_combination (1/4) * hS2) ?_ hA x
    intro j _; exact K_bound_odd h2 j

/-- The two-block matrix attains the value `L` of the top eigenvalue whenever `L` solves the
characteristic equation of its nonzero `2 × 2` block. -/
lemma le_eigVal_blockSign {N p : ℕ} {a b L : ℝ} (ha : a < 0)
    (hp1 : 1 ≤ p) (hpN : p < N)
    (hkey : L^2 - b*L*(N:ℝ) + (b^2-a^2)*((p:ℝ)*((N:ℝ)-p)) = 0)
    (k : Fin N) (hk : (k:ℕ) = 0) :
    L ≤ eigVal (blockSign N p a b) k := by
  classical
  set q : ℝ := (N:ℝ) - (p:ℝ) with hq
  set al : ℝ := a * q with hal
  set be : ℝ := L - b * p with hbe
  set x : Fin N → ℝ := fun i => if (i:ℕ) < p then al else be with hx
  have hqpos : 0 < q := by
    rw [hq]; have : (p:ℝ) < (N:ℝ) := by exact_mod_cast hpN
    linarith
  have halne : al ≠ 0 := by
    rw [hal]; exact mul_ne_zero (ne_of_lt ha) (ne_of_gt hqpos)
  have hNpos : 0 < N := by omega
  have hxne : x ≠ 0 := by
    intro h
    have h0 : x ⟨0, hNpos⟩ = 0 := by rw [h]; rfl
    rw [hx] at h0
    simp only [] at h0
    rw [if_pos (by omega : (0:ℕ) < p)] at h0
    exact halne h0
  refine le_eigVal_top_of_vector (signMat_herm _ _ _) k hk x hxne L ?_
  have hpN' : p ≤ N := le_of_lt hpN
  have hsum : ∑ i, x i = (p:ℝ) * al + q * be := sum_ite_lt N p hpN' al be
  have hwsum : ∑ i : Fin N, (if (i:ℕ) < p then (1:ℝ) else -1) * x i = (p:ℝ) * al + q * (-be) := by
    rw [← sum_ite_lt N p hpN' al (-be)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx]; by_cases h : (i:ℕ) < p <;> simp [h]
  have hdot : x ⬝ᵥ x = (p:ℝ) * al ^ 2 + q * be ^ 2 := by
    rw [dotProduct_self, ← sum_ite_lt N p hpN' (al^2) (be^2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx]; by_cases h : (i:ℕ) < p <;> simp [h]
  show L * (x ⬝ᵥ x) ≤ x ⬝ᵥ (blockSign N p a b) *ᵥ x
  rw [blockSign, quad_form_signMat, hsum, hwsum, hdot]
  have hz : ((a+b)/2) * ((p:ℝ) * al + q * be) ^ 2 + ((b-a)/2) * ((p:ℝ) * al + q * (-be)) ^ 2
      - L * ((p:ℝ) * al ^ 2 + q * be ^ 2) = 0 := by
    rw [hal, hbe]
    have hNq : (N:ℝ) = (p:ℝ) + q := by rw [hq]; ring
    rw [hNq] at hkey
    linear_combination (-q*(L - b*p)) * hkey
  linarith

/-- The value `U₁` is attained. -/
theorem U1_mem {m : ℕ} {a b : ℝ} (hab : a ≤ b) : U1 (m+2) a b ∈ eigRange (m+2) a b 0 := by
  set N := m + 2 with hNdef
  have hN2 : 2 ≤ N := by omega
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by rw [hNdef]; push_cast; linarith
  have hNsq : (1:ℝ) ≤ (N:ℝ)^2 := by nlinarith
  rcases le_or_gt 0 (a+b) with h1 | h1
  · have hU : U1 N a b = (N:ℝ)*b := by unfold U1; rw [if_pos h1]
    have hmem : twoParam N b b ∈ SymIcc N a b := twoParam_mem ⟨hab, le_rfl⟩ ⟨hab, le_rfl⟩
    refine ⟨twoParam N b b, hmem, ?_⟩
    show eigVal (twoParam N b b) 0 = U1 N a b
    refine le_antisymm (eigVal_le_U1 (by omega) hab hmem 0) ?_
    rw [hU]
    refine le_eigVal_top_of_vector (twoParam_herm b b) 0 rfl (fun _ => (1:ℝ)) ?_ _ ?_
    · intro h
      have h0 : (1:ℝ) = 0 := congrFun h ⟨0, by omega⟩
      norm_num at h0
    · rw [quad_form_twoParam, dotProduct_self]
      simp
      linarith
  · have ha : a < 0 := by linarith
    have hmem : blockSign N (N/2) a b ∈ SymIcc N a b := blockSign_mem hab
    refine ⟨blockSign N (N/2) a b, hmem, ?_⟩
    show eigVal (blockSign N (N/2) a b) 0 = U1 N a b
    refine le_antisymm (eigVal_le_U1 (by omega) hab hmem 0) ?_
    refine le_eigVal_blockSign ha (by omega) (by omega) ?_ 0 rfl
    unfold U1
    rw [if_neg (by linarith)]
    rcases Nat.even_or_odd N with he | ho
    · rw [if_pos he]
      obtain ⟨t, ht⟩ := he
      have hp : N / 2 = t := by omega
      have hNr : ((N:ℕ):ℝ) = 2*(t:ℝ) := by rw [ht]; push_cast; ring
      rw [hp, hNr]
      ring
    · rw [if_neg (by simpa [Nat.not_even_iff_odd] using ho)]
      obtain ⟨t, ht⟩ := ho
      have hp : N / 2 = t := by omega
      have hNr : ((N:ℕ):ℝ) = 2*(t:ℝ) + 1 := by rw [ht]; push_cast; ring
      have harg : 0 ≤ ((N:ℝ)^2 - 1)*a^2 + b^2 := by nlinarith [sq_nonneg a, sq_nonneg b]
      have hS2 : (Real.sqrt (((N:ℝ)^2 - 1)*a^2 + b^2))^2 = ((N:ℝ)^2 - 1)*a^2 + b^2 :=
        Real.sq_sqrt harg
      rw [hp]
      rw [hNr] at hS2 ⊢
      linear_combination (1/4) * hS2

/-- **Formula (2.1)**: for `n ≥ 2` and `a ≤ b`, the minimum of `λ₁` over `S_n([a,b])` is
`na` if `a ≥ 0`, `a` if `a ≤ 0 ≤ b`, and `a - b` if `b ≤ 0`. -/
theorem isLeast_eigRange_first {m : ℕ} {a b : ℝ} (hab : a ≤ b) :
    IsLeast (eigRange (m+2) a b 0) (L1 (m+2) a b) :=
  ⟨L1_mem hab, by rintro t ⟨A, hA, rfl⟩; exact L1_le_eigVal hA⟩

/-- **Formula (2.2)**: for `n ≥ 2` and `a ≤ b`, the maximum of `λₙ` over `S_n([a,b])` is
`b - a` if `a ≥ 0`, `b` if `a ≤ 0 ≤ b`, and `nb` if `b ≤ 0`. -/
theorem isGreatest_eigRange_last {m : ℕ} {a b : ℝ} (hab : a ≤ b) :
    IsGreatest (eigRange (m+2) a b (Fin.last (m+1))) (Un (m+2) a b) := by
  refine isGreatest_of_isLeast_neg ?_
  rw [eigRange_neg' (m+2) a b (Fin.last (m+1)), show Fin.rev (Fin.last (m+1)) = (0 : Fin (m+2)) by simp,
    Un_eq hab, neg_neg]
  exact isLeast_eigRange_first (by linarith)

/-- **Formula (2.3)**: for `n ≥ 2` and `a ≤ b`, the maximum of `λ₁` over `S_n([a,b])` is
`nb` if `a + b ≥ 0`, and otherwise `n(b-a)/2` for `n` even and
`(nb + √((n²-1)a² + b²))/2` for `n` odd. -/
theorem isGreatest_eigRange_first {m : ℕ} {a b : ℝ} (hab : a ≤ b) :
    IsGreatest (eigRange (m+2) a b 0) (U1 (m+2) a b) :=
  ⟨U1_mem hab, by rintro t ⟨A, hA, rfl⟩; exact eigVal_le_U1 (by omega) hab hA 0⟩

/-- **Formula (2.4)**: for `n ≥ 2` and `a ≤ b`, the minimum of `λₙ` over `S_n([a,b])` is
`na` if `a + b ≤ 0`, and otherwise `n(a-b)/2` for `n` even and
`(na - √(a² + (n²-1)b²))/2` for `n` odd. -/
theorem isLeast_eigRange_last {m : ℕ} {a b : ℝ} (hab : a ≤ b) :
    IsLeast (eigRange (m+2) a b (Fin.last (m+1))) (Ln (m+2) a b) := by
  refine isLeast_of_isGreatest_neg ?_
  rw [eigRange_neg' (m+2) a b (Fin.last (m+1)),
    show Fin.rev (Fin.last (m+1)) = (0 : Fin (m+2)) by simp, Ln_eq, neg_neg]
  exact isGreatest_eigRange_first (by linarith)

/-! ## The minimum of `λ₂` for a nonnegative interval, formula (2.5) -/

/-- The subspace of vectors whose coordinates sum to zero. -/
noncomputable def sumKer (n : ℕ) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (∑ i : Fin n, (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ))

lemma mem_sumKer {x : Fin n → ℝ} : x ∈ sumKer n ↔ ∑ i, x i = 0 := by
  simp [sumKer, LinearMap.mem_ker, LinearMap.sum_apply]

lemma finrank_sumKer (n : ℕ) : n - 1 ≤ Module.finrank ℝ (sumKer n) := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (∑ i : Fin n, (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ))
  have h2 : Module.finrank ℝ (LinearMap.range
      (∑ i : Fin n, (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ))) ≤ 1 := by
    calc _ ≤ Module.finrank ℝ ℝ := Submodule.finrank_le _
      _ = 1 := Module.finrank_self ℝ
  simp only [Module.finrank_pi, Fintype.card_fin] at h
  simp only [sumKer]
  omega

/-- For a nonnegative interval, `λ₂(A) ≥ a - b` for every `A ∈ S_n([a,b])`. -/
lemma L2_lower {m : ℕ} {a b : ℝ} (ha : 0 ≤ a) {A : Matrix (Fin (m+2)) (Fin (m+2)) ℝ}
    (hA : A ∈ SymIcc (m+2) a b) : a - b ≤ eigVal A 1 := by
  classical
  set p : Fin (m+2) := 0 with hp
  set q : Fin (m+2) := 1 with hq
  have hpq : p ≠ q := by
    rw [hp, hq]; intro h; have h' := congrArg Fin.val h; simp at h'
  set s : Finset (Fin (m+2)) := ({p, q} : Finset (Fin (m+2)))ᶜ with hs
  have hval : ((1 : Fin (m+2)) : ℕ) = 1 := by simp
  refine le_eigVal_of_subspace hA.1 1 (coordKer s) ?_ (a-b) ?_
  · have hcard : s.card = (m+2) - 2 := by
      rw [hs, Finset.card_compl, Finset.card_insert_of_notMem (by simpa using hpq),
        Finset.card_singleton, Fintype.card_fin]
    have h2 := finrank_coordKer s
    rw [hval, hcard] at *
    omega
  · intro x hx
    set u := x p with hu
    set v := x q with hv
    have hxeq : x = fun t => if t = p then u else if t = q then v else 0 := by
      funext t
      by_cases h1 : t = p
      · rw [if_pos h1, hu, h1]
      · by_cases h2 : t = q
        · rw [if_neg h1, if_pos h2, hv, h2]
        · rw [if_neg h1, if_neg h2]
          exact (mem_coordKer.1 hx) t (by simp [hs, h1, h2])
    rw [hxeq, quad_form_pair A hpq, dot_pair hpq]
    have h1 := (hA.2 p p).1
    have h2 := (hA.2 q q).1
    have h3 := (hA.2 p q).1
    have h3' := (hA.2 p q).2
    have h4 := (hA.2 q p).1
    have h4' := (hA.2 q p).2
    have hb : 0 ≤ b := le_trans ha (le_trans h3 h3')
    nlinarith [mul_nonneg hb (sq_nonneg (u+v)), mul_nonneg hb (sq_nonneg (u-v)),
      sq_nonneg u, sq_nonneg v, mul_nonneg ha (sq_nonneg u), mul_nonneg ha (sq_nonneg v)]

/-- The matrix `(a-b)I + bJ` has `λ₂ ≤ a - b`. -/
lemma eigVal_twoParam_second_le {m : ℕ} {a b : ℝ} :
    eigVal (twoParam (m+2) a b) 1 ≤ a - b := by
  have hval : ((1 : Fin (m+2)) : ℕ) = 1 := by simp
  refine eigVal_le_of_subspace (twoParam_herm a b) 1 (sumKer (m+2)) ?_ (a-b) ?_
  · rw [hval]; exact finrank_sumKer (m+2)
  · intro x hx
    rw [quad_form_twoParam, mem_sumKer.1 hx]
    simp

/-- **Formula (2.5)**: for `n ≥ 2` and `0 ≤ a ≤ b`, the minimum of `λ₂` over `S_n([a,b])`
is `a - b`. -/
theorem isLeast_eigRange_second {m : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IsLeast (eigRange (m+2) a b 1) (a - b) := by
  refine ⟨⟨twoParam (m+2) a b, twoParam_mem ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩, ?_⟩, ?_⟩
  · exact le_antisymm eigVal_twoParam_second_le
      (L2_lower ha (twoParam_mem ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩))
  · rintro t ⟨A, hA, rfl⟩
    exact L2_lower ha hA

/-- **Formula (2.8)**: for `n ≥ 2` and `a ≤ b ≤ 0`, the maximum of `λ_{n-1}` over `S_n([a,b])`
is `b - a`. -/
theorem isGreatest_eigRange_penultimate {m : ℕ} {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) :
    IsGreatest (eigRange (m+2) a b ⟨m, by omega⟩) (b - a) := by
  refine isGreatest_of_isLeast_neg ?_
  have hrev : Fin.rev (⟨m, by omega⟩ : Fin (m+2)) = 1 := by
    refine Fin.ext ?_
    simp [Fin.val_rev]
  rw [eigRange_neg' (m+2) a b ⟨m, by omega⟩, hrev, show -(b-a) = (-b) - (-a) by ring]
  exact isLeast_eigRange_second (by linarith) (by linarith)

/-! ## Towards the maximum of `λ₂` for a nonnegative interval

The Perron-type ingredients: for a matrix with all entries `≥ a > 0` the top eigenvalue has a
strictly positive eigenvector, and consequently `λ₂` has an eigenvector with both a positive and
a negative coordinate. -/

/-- **Perron positivity**: if all entries of `A` are at least `a > 0`, then the largest
eigenvalue of `A` has a strictly positive eigenvector. -/
lemma perron_pos {N : ℕ} {a b : ℝ} (ha : 0 < a) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A ∈ SymIcc N a b) (k : Fin N) (hk : (k:ℕ) = 0) :
    ∃ z : Fin N → ℝ, (∀ i, 0 < z i) ∧ A *ᵥ z = eigVal A k • z := by
  obtain ⟨v, hv1, hv2⟩ := exists_eigenvector hA.1 k
  set z : Fin N → ℝ := fun i => |v i| with hzdef
  have hz0 : ∀ i, 0 ≤ z i := fun i => abs_nonneg _
  have hz2 : z ⬝ᵥ z = 1 := by
    rw [dotProduct_self, ← hv1, dotProduct_self]
    exact Finset.sum_congr rfl fun i _ => by rw [hzdef]; simp [sq_abs]
  have hvA : v ⬝ᵥ A *ᵥ v = eigVal A k := by
    rw [hv2, dotProduct_smul, smul_eq_mul, hv1, mul_one]
  have hcmp : v ⬝ᵥ A *ᵥ v ≤ z ⬝ᵥ A *ᵥ z := by
    rw [quad_form, quad_form]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hij : 0 ≤ A i j := le_trans ha.le (hA.2 i j).1
    have hvz : v i * v j ≤ z i * z j := by
      rw [hzdef]; simpa using (le_abs_self (v i * v j)).trans (by rw [abs_mul])
    calc A i j * v i * v j = A i j * (v i * v j) := by ring
      _ ≤ A i j * (z i * z j) := by nlinarith
      _ = A i j * z i * z j := by ring
  have hmax : eigVal A k * (z ⬝ᵥ z) ≤ z ⬝ᵥ A *ᵥ z := by rw [hz2, mul_one, ← hvA]; exact hcmp
  have hz := eigenvector_of_max hA.1 k hk z hmax
  have hsum : 0 < ∑ i, z i := sum_pos_of_dot_one hz0 hz2
  have hlow : ∀ i, a * (∑ j, z j) ≤ (A *ᵥ z) i := by
    intro i
    rw [mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      have := (hA.2 i j).1
      nlinarith [hz0 j]
  have hlam : 0 < eigVal A k := by
    have h1 := hlow k
    rw [hz] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    nlinarith [hz0 k, mul_pos ha hsum]
  refine ⟨z, fun i => ?_, hz⟩
  have h1 := hlow i
  rw [hz] at h1
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  nlinarith [mul_pos ha hsum]

/-- For a positive interval, `λ₂` has an eigenvector with both signs. -/
lemma exists_mixed_eigenvector {m : ℕ} {a b : ℝ} (ha : 0 < a)
    {A : Matrix (Fin (m+2)) (Fin (m+2)) ℝ} (hA : A ∈ SymIcc (m+2) a b) :
    ∃ x : Fin (m+2) → ℝ, A *ᵥ x = eigVal A 1 • x ∧ (∃ i, 0 < x i) ∧ (∃ j, x j < 0) := by
  classical
  have h01 : (0 : Fin (m+2)) ≠ 1 := by
    intro h; have h' := congrArg Fin.val h; simp at h'
  by_cases hEq : eigVal A 0 = eigVal A 1
  · obtain ⟨v, w, hv1, hw1, hvw, hv2, hw2⟩ := exists_eigenvector_pair hA.1 0 1 h01
    have hv2' : A *ᵥ v = eigVal A 1 • v := by rw [hv2, hEq]
    by_cases hsv : ∑ i, v i = 0
    · have hvne : v ≠ 0 := by intro h; rw [h] at hv1; simp at hv1
      exact ⟨v, hv2', mixed_of_sum_zero hvne hsv⟩
    · set x : Fin (m+2) → ℝ := (∑ i, w i) • v - (∑ i, v i) • w with hx
      have hAx : A *ᵥ x = eigVal A 1 • x := by
        rw [hx, mulVec_sub, mulVec_smul, mulVec_smul, hv2', hw2]
        module
      have hsx : ∑ i, x i = 0 := by
        rw [hx]
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
      have hxne : x ≠ 0 := by
        intro h
        have h0 : x ⬝ᵥ w = 0 := by rw [h]; simp
        rw [hx] at h0
        simp [sub_dotProduct, smul_dotProduct, hvw, hw1] at h0
        exact hsv h0
      exact ⟨x, hAx, mixed_of_sum_zero hxne hsx⟩
  · obtain ⟨z, hzpos, hz⟩ := perron_pos ha hA 0 rfl
    obtain ⟨v, hv1, hv2⟩ := exists_eigenvector hA.1 1
    have horth : z ⬝ᵥ v = 0 := by
      have h1 : z ⬝ᵥ A *ᵥ v = (A *ᵥ z) ⬝ᵥ v := symm_dot hA.1 z v
      rw [hv2, hz] at h1
      simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
      rcases mul_eq_zero.1 (show (eigVal A 0 - eigVal A 1) * (z ⬝ᵥ v) = 0 by linarith) with h|h
      · exact absurd (by linarith : eigVal A 0 = eigVal A 1) hEq
      · exact h
    have hvne : v ≠ 0 := by intro h; rw [h] at hv1; simp at hv1
    refine ⟨v, hv2, ?_, ?_⟩
    · by_contra hc
      push_neg at hc
      have hall : ∀ i, z i * v i = 0 := by
        refine fun i => (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => ?_)).1 horth i
          (Finset.mem_univ i)
        exact mul_nonpos_of_nonneg_of_nonpos (hzpos i).le (hc i)
      exact hvne (funext fun i => by
        rcases mul_eq_zero.1 (hall i) with h|h
        · exact absurd h (ne_of_gt (hzpos i))
        · exact h)
    · by_contra hc
      push_neg at hc
      have hall : ∀ i, z i * v i = 0 := by
        refine fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ?_)).1 horth i
          (Finset.mem_univ i)
        exact mul_nonneg (hzpos i).le (hc i)
      exact hvne (funext fun i => by
        rcases mul_eq_zero.1 (hall i) with h|h
        · exact absurd h (ne_of_gt (hzpos i))
        · exact h)

/-! ### The function `φ` and its monotonicity -/

/-- `phi a b m` is the quantity `φ_m` of the solution:
`m(b-a)/2` for `m` even and `(mb - √((m²-1)a²+b²))/2` for `m` odd. -/
noncomputable def phi (a b : ℝ) (m : ℕ) : ℝ :=
  ((m : ℝ)*b - Real.sqrt (a^2*(m:ℝ)^2 + (b^2-a^2)*(if Even m then 0 else 1)))/2

lemma phi_even {a b : ℝ} (ha : 0 ≤ a) {m : ℕ} (hm : Even m) :
    phi a b m = (m:ℝ)*(b-a)/2 := by
  have h : a^2*(m:ℝ)^2 + (b^2-a^2)*(if Even m then 0 else 1) = (a*(m:ℝ))^2 := by
    rw [if_pos hm]; ring
  rw [phi, h, Real.sqrt_sq (by positivity)]
  ring

lemma phi_odd {a b : ℝ} {m : ℕ} (hm : ¬ Even m) :
    phi a b m = ((m:ℝ)*b - Real.sqrt (((m:ℝ)^2-1)*a^2 + b^2))/2 := by
  rw [phi, if_neg hm]
  norm_num
  ring_nf

lemma phi_succ_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (m : ℕ) :
    phi a b m ≤ phi a b (m+1) := by
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hprod : 0 ≤ a * (m:ℝ) * (b - a) :=
    mul_nonneg (mul_nonneg ha hm0) (sub_nonneg.2 hab)
  rcases Nat.even_or_odd m with he | ho
  · have h1 : ¬ Even (m+1) := by simp [Nat.even_add_one, he]
    rw [phi_even ha he, phi_odd h1]
    have hle : ((((m:ℝ)+1))^2-1)*a^2 + b^2 ≤ (b + a*(m:ℝ))^2 := by nlinarith
    have hs : Real.sqrt (((((m:ℝ)+1))^2-1)*a^2 + b^2) ≤ b + a*(m:ℝ) := by
      calc Real.sqrt (((((m:ℝ)+1))^2-1)*a^2 + b^2) ≤ Real.sqrt ((b + a*(m:ℝ))^2) :=
            Real.sqrt_le_sqrt hle
        _ = b + a*(m:ℝ) := Real.sqrt_sq (by nlinarith)
    push_cast
    push_cast at hs
    linarith
  · have hne : ¬ Even m := by simpa [Nat.not_even_iff_odd] using ho
    have h1 : Even (m+1) := by simpa [Nat.even_add_one] using hne
    rw [phi_odd hne, phi_even ha h1]
    have hs : ((m:ℝ)+1)*a - b ≤ Real.sqrt (((m:ℝ)^2-1)*a^2 + b^2) := by
      rcases le_or_gt (((m:ℝ)+1)*a - b) 0 with h|h
      · exact le_trans h (Real.sqrt_nonneg _)
      · calc ((m:ℝ)+1)*a - b = Real.sqrt ((((m:ℝ)+1)*a - b)^2) := (Real.sqrt_sq h.le).symm
          _ ≤ Real.sqrt (((m:ℝ)^2-1)*a^2 + b^2) := by
              refine Real.sqrt_le_sqrt ?_
              nlinarith
    push_cast
    push_cast at hs
    linarith

lemma phi_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : Monotone (phi a b) :=
  monotone_nat_of_le_succ (phi_succ_le ha hab)

lemma phi_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (m : ℕ) : 0 ≤ phi a b m := by
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hab2 : a^2 ≤ b^2 := by nlinarith
  rw [phi]
  have hle : a^2*(m:ℝ)^2 + (b^2-a^2)*(if Even m then 0 else 1) ≤ ((m:ℝ)*b)^2 := by
    rcases Nat.even_or_odd m with he|ho
    · rw [if_pos he]
      nlinarith [mul_le_mul_of_nonneg_right hab2 (sq_nonneg (m:ℝ))]
    · have hne : ¬ Even m := by simpa [Nat.not_even_iff_odd] using ho
      have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast ho.pos
      rw [if_neg hne]
      nlinarith [mul_le_mul_of_nonneg_left hab2 (show (0:ℝ) ≤ (m:ℝ)^2 - 1 by nlinarith)]
  have hs := Real.sqrt_le_sqrt hle
  rw [Real.sqrt_sq (by nlinarith)] at hs
  linarith

/-! ### The `λ₂` upper bound for a positive interval -/

/-- The two block inequalities (5.1)–(5.2) of the solution. -/
lemma eig_block_ineq {N : ℕ} {a b lam : ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A ∈ SymIcc N a b) {x : Fin N → ℝ} (hx : A *ᵥ x = lam • x) :
    (lam * (∑ i ∈ Finset.univ.filter (fun i : Fin N => 0 < x i), x i)
        ≤ (Finset.univ.filter (fun i : Fin N => 0 < x i)).card *
          (b * (∑ i ∈ Finset.univ.filter (fun i : Fin N => 0 < x i), x i)
            + a * (∑ j ∈ Finset.univ.filter (fun j : Fin N => x j < 0), x j)))
      ∧ ((Finset.univ.filter (fun j : Fin N => x j < 0)).card *
          (a * (∑ i ∈ Finset.univ.filter (fun i : Fin N => 0 < x i), x i)
            + b * (∑ j ∈ Finset.univ.filter (fun j : Fin N => x j < 0), x j))
        ≤ lam * (∑ j ∈ Finset.univ.filter (fun j : Fin N => x j < 0), x j)) := by
  classical
  set P := Finset.univ.filter (fun i : Fin N => 0 < x i) with hP
  set Q := Finset.univ.filter (fun j : Fin N => x j < 0) with hQ
  set U : ℝ := ∑ i ∈ P, x i with hU
  set W : ℝ := ∑ j ∈ Q, x j with hW
  have hupper : ∀ i, (A *ᵥ x) i ≤ b * U + a * W := by
    intro i
    have hstep : ∑ j, A i j * x j
        ≤ ∑ j, ((if 0 < x j then b * x j else 0) + (if x j < 0 then a * x j else 0)) := by
      refine Finset.sum_le_sum fun j _ => ?_
      rcases lt_trichotomy (x j) 0 with h|h|h
      · rw [if_neg (by linarith), if_pos h, zero_add]
        nlinarith [(hA.2 i j).1]
      · rw [if_neg (by linarith), if_neg (by linarith), h]
        simp
      · rw [if_pos h, if_neg (by linarith), add_zero]
        nlinarith [(hA.2 i j).2]
    have hsum : ∑ j, ((if 0 < x j then b * x j else 0) + (if x j < 0 then a * x j else 0))
        = b * U + a * W := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, hU, hW,
        Finset.mul_sum, Finset.mul_sum]
    rw [mulVec, dotProduct]
    calc ∑ j, A i j * x j ≤ _ := hstep
      _ = b * U + a * W := hsum
  have hlower : ∀ i, a * U + b * W ≤ (A *ᵥ x) i := by
    intro i
    have hstep : ∑ j, ((if 0 < x j then a * x j else 0) + (if x j < 0 then b * x j else 0))
        ≤ ∑ j, A i j * x j := by
      refine Finset.sum_le_sum fun j _ => ?_
      rcases lt_trichotomy (x j) 0 with h|h|h
      · rw [if_neg (by linarith), if_pos h, zero_add]
        nlinarith [(hA.2 i j).2]
      · rw [if_neg (by linarith), if_neg (by linarith), h]
        simp
      · rw [if_pos h, if_neg (by linarith), add_zero]
        nlinarith [(hA.2 i j).1]
    have hsum : ∑ j, ((if 0 < x j then a * x j else 0) + (if x j < 0 then b * x j else 0))
        = a * U + b * W := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, hU, hW,
        Finset.mul_sum, Finset.mul_sum]
    rw [mulVec, dotProduct]
    calc a * U + b * W = _ := hsum.symm
      _ ≤ ∑ j, A i j * x j := hstep
  constructor
  · have h1 : ∑ i ∈ P, (lam * x i) ≤ ∑ i ∈ P, (b * U + a * W) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hi := hupper i
      rw [hx] at hi
      simpa using hi
    rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at h1
    exact h1
  · have h1 : ∑ i ∈ Q, (a * U + b * W) ≤ ∑ i ∈ Q, (lam * x i) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hi := hlower i
      rw [hx] at hi
      simpa using hi
    rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at h1
    exact h1

/-- Solving the quadratic inequality (5.3) of the solution. -/
lemma lam_le_root {a b lam U V pr qr : ℝ} (ha : 0 < a) (hab : a ≤ b) (hU : 0 < U) (hV : 0 < V)
    (hpr1 : 1 ≤ pr) (hqr1 : 1 ≤ qr)
    (h1 : lam * U ≤ pr * (b*U - a*V)) (h2 : lam * V ≤ qr * (b*V - a*U)) :
    2*lam ≤ b*(pr+qr) - Real.sqrt (a^2*(pr+qr)^2 + (b^2-a^2)*(pr-qr)^2) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hba : 0 ≤ b^2 - a^2 := by nlinarith
  have hprpos : 0 < pr := by linarith
  have hqrpos : 0 < qr := by linarith
  have hbp : lam < b * pr := by nlinarith [mul_pos (mul_pos ha hprpos) hV]
  have hbq : lam < b * qr := by nlinarith [mul_pos (mul_pos ha hqrpos) hU]
  have e1 : a*pr*V ≤ (b*pr - lam)*U := by nlinarith
  have e2 : a*qr*U ≤ (b*qr - lam)*V := by nlinarith
  have hkey : a^2*(pr*qr) ≤ (b*pr - lam)*(b*qr - lam) := by
    have hm := mul_le_mul e1 e2 (by positivity) (by nlinarith)
    have huv : 0 < U*V := mul_pos hU hV
    nlinarith
  have hD0 : 0 ≤ a^2*(pr+qr)^2 + (b^2-a^2)*(pr-qr)^2 := by
    nlinarith [sq_nonneg (pr-qr), sq_nonneg (pr+qr), mul_nonneg hba (sq_nonneg (pr-qr))]
  have hc0 : 0 ≤ b*(pr+qr) - 2*lam := by nlinarith
  have hsq : a^2*(pr+qr)^2 + (b^2-a^2)*(pr-qr)^2 ≤ (b*(pr+qr) - 2*lam)^2 := by nlinarith
  have hs := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hc0] at hs
  linarith

lemma lam_le_phi {N p q : ℕ} {a b lam U V : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hU : 0 < U) (hV : 0 < V) (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p + q ≤ N)
    (h1 : lam * U ≤ (p:ℝ) * (b*U - a*V)) (h2 : lam * V ≤ (q:ℝ) * (b*V - a*U)) :
    lam ≤ phi a b N := by
  have hba : 0 ≤ b^2 - a^2 := by nlinarith
  have hpr1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hqr1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hroot := lam_le_root ha hab hU hV hpr1 hqr1 h1 h2
  have hdelta : ((if Even (p+q) then (0:ℝ) else 1)) ≤ ((p:ℝ)-(q:ℝ))^2 := by
    rcases Nat.even_or_odd (p+q) with he|ho
    · rw [if_pos he]; positivity
    · have hne : ¬ Even (p+q) := by simpa [Nat.not_even_iff_odd] using ho
      rw [if_neg hne]
      have hz : ((p:ℤ) - (q:ℤ)) ≠ 0 := by
        have h2' : (p+q) % 2 = 1 := Nat.not_even_iff.1 hne
        omega
      have h1' : (1:ℤ) ≤ ((p:ℤ) - (q:ℤ))^2 := by
        rcases lt_trichotomy ((p:ℤ) - (q:ℤ)) 0 with h|h|h
        · nlinarith
        · exact absurd h hz
        · nlinarith
      exact_mod_cast h1'
  have hphi : lam ≤ phi a b (p+q) := by
    rw [phi]
    have hcast : ((p+q : ℕ):ℝ) = (p:ℝ) + (q:ℝ) := by push_cast; ring
    rw [hcast]
    have hle2 : a^2*((p:ℝ)+(q:ℝ))^2 + (b^2-a^2)*(if Even (p+q) then (0:ℝ) else 1)
        ≤ a^2*((p:ℝ)+(q:ℝ))^2 + (b^2-a^2)*((p:ℝ)-(q:ℝ))^2 := by nlinarith
    have hs := Real.sqrt_le_sqrt hle2
    linarith
  exact le_trans hphi (phi_mono ha.le hab hpq)

/-- **The `λ₂` upper bound for a positive interval.** -/
theorem eigVal_second_le_phi_pos {m : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {A : Matrix (Fin (m+2)) (Fin (m+2)) ℝ} (hA : A ∈ SymIcc (m+2) a b) :
    eigVal A 1 ≤ phi a b (m+2) := by
  classical
  obtain ⟨x, hx, ⟨i0, hi0⟩, ⟨j0, hj0⟩⟩ := exists_mixed_eigenvector ha hA
  set P := Finset.univ.filter (fun i : Fin (m+2) => 0 < x i) with hP
  set Q := Finset.univ.filter (fun j : Fin (m+2) => x j < 0) with hQ
  have hPne : P.Nonempty := ⟨i0, by simp [hP, hi0]⟩
  have hQne : Q.Nonempty := ⟨j0, by simp [hQ, hj0]⟩
  have hU : 0 < ∑ i ∈ P, x i := Finset.sum_pos (fun i hi => by
    rw [hP] at hi; simpa using (Finset.mem_filter.1 hi).2) hPne
  have hW : ∑ j ∈ Q, x j < 0 := Finset.sum_neg (fun j hj => by
    rw [hQ] at hj; simpa using (Finset.mem_filter.1 hj).2) hQne
  have hp1 : 1 ≤ P.card := Finset.card_pos.2 hPne
  have hq1 : 1 ≤ Q.card := Finset.card_pos.2 hQne
  have hdisj : Disjoint P Q := by
    rw [hP, hQ, Finset.disjoint_filter]
    intro i _ hi
    simp only [not_lt]; linarith
  have hcard : P.card + Q.card ≤ m + 2 := by
    have h1 := Finset.card_union_of_disjoint hdisj
    have h2 := Finset.card_le_univ (P ∪ Q)
    rw [h1] at h2
    simpa using h2
  obtain ⟨e1, e2⟩ := eig_block_ineq hA hx
  refine lam_le_phi (U := ∑ i ∈ P, x i) (V := -(∑ j ∈ Q, x j)) ha hab hU (by linarith)
    hp1 hq1 hcard ?_ ?_
  · nlinarith [e1]
  · nlinarith [e2]

/-! ### Monotonicity of eigenvalues, and the case `a = 0` -/

/-- There is a subspace of dimension at least `n - k` on which the quadratic form of `A`
is at most `λ_{k+1}(A)`. -/
theorem exists_subspace_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : Fin n) :
    ∃ V : Submodule ℝ (Fin n → ℝ), n - (k : ℕ) ≤ Module.finrank ℝ V ∧
      ∀ x ∈ V, x ⬝ᵥ A *ᵥ x ≤ eigVal A k * (x ⬝ᵥ x) := by
  classical
  obtain ⟨W, hWt, hWt', hnorm, hquad⟩ := spectral_coords hA
  set eW : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    LinearEquiv.ofLinear (Matrix.mulVecLin W) (Matrix.mulVecLin Wᵀ)
      (by rw [← Matrix.mulVecLin_mul, hWt', Matrix.mulVecLin_one])
      (by rw [← Matrix.mulVecLin_mul, hWt, Matrix.mulVecLin_one]) with heW
  refine ⟨(coordKer (Finset.Iio k)).map (eW : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)), ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq eW]
    simpa [Fin.card_Iio] using finrank_coordKer (Finset.Iio k)
  · rintro x ⟨c, hc, rfl⟩
    have hWc : Wᵀ *ᵥ ((eW : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) c) = c := by
      show Wᵀ *ᵥ (W *ᵥ c) = c
      rw [Matrix.mulVec_mulVec, hWt, Matrix.one_mulVec]
    set x := (eW : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) c
    rw [hquad x, hnorm x, hWc, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hik : i < k
    · rw [(mem_coordKer.1 hc) i (Finset.mem_Iio.2 hik)]; simp
    · have : eigVal A i ≤ eigVal A k := eigVal_antitone A (not_lt.1 hik)
      nlinarith [sq_nonneg (c i)]

/-- Monotonicity of the ordered eigenvalues in the quadratic form. -/
theorem eigVal_mono_quad {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (k : Fin n) (h : ∀ x : Fin n → ℝ, x ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ B *ᵥ x) :
    eigVal A k ≤ eigVal B k := by
  obtain ⟨V, hV, hVt⟩ := exists_subspace_le hB k
  exact eigVal_le_of_subspace hA k V hV _ (fun x hx => le_trans (h x) (hVt x hx))

lemma quad_form_add (A B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (A + B) *ᵥ x = x ⬝ᵥ A *ᵥ x + x ⬝ᵥ B *ᵥ x := by
  rw [Matrix.add_mulVec, dotProduct_add]

lemma phi_shift {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (N : ℕ) :
    phi t (b+t) N ≤ phi 0 b N + (N:ℝ)*t/2 := by
  have hN : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hle : (0:ℝ)^2*(N:ℝ)^2 + (b^2-0^2)*(if Even N then (0:ℝ) else 1)
      ≤ t^2*(N:ℝ)^2 + ((b+t)^2-t^2)*(if Even N then (0:ℝ) else 1) := by
    rcases Nat.even_or_odd N with he|ho
    · rw [if_pos he]; nlinarith
    · have hne : ¬ Even N := by simpa [Nat.not_even_iff_odd] using ho
      rw [if_neg hne]; nlinarith
  have hs := Real.sqrt_le_sqrt hle
  rw [phi, phi]
  set s0 := Real.sqrt ((0:ℝ)^2*(N:ℝ)^2 + (b^2-0^2)*(if Even N then (0:ℝ) else 1)) with hs0
  set s1 := Real.sqrt (t^2*(N:ℝ)^2 + ((b+t)^2-t^2)*(if Even N then (0:ℝ) else 1)) with hs1
  have hexp : (N:ℝ)*(b+t) = (N:ℝ)*b + (N:ℝ)*t := by ring
  rw [hexp]
  linarith

/-- **The `λ₂` upper bound for a nonnegative interval**, including the case `a = 0`. -/
theorem eigVal_second_le_phi {m : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {A : Matrix (Fin (m+2)) (Fin (m+2)) ℝ} (hA : A ∈ SymIcc (m+2) a b) :
    eigVal A 1 ≤ phi a b (m+2) := by
  rcases lt_or_eq_of_le ha with ha' | ha'
  · exact eigVal_second_le_phi_pos ha' hab hA
  · subst ha'
    have hb : (0:ℝ) ≤ b := hab
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hNpos : (0:ℝ) < ((m+2:ℕ):ℝ) := by positivity
    have ht : 0 < ε / ((m+2:ℕ):ℝ) := by positivity
    set t : ℝ := ε / ((m+2:ℕ):ℝ) with htdef
    have hBmem : A + twoParam (m+2) t t ∈ SymIcc (m+2) t (b+t) := by
      refine ⟨(hA.1.add (twoParam_herm t t)), fun i j => ?_⟩
      have h1 := (hA.2 i j).1
      have h2 := (hA.2 i j).2
      simp only [Matrix.add_apply, twoParam, Matrix.of_apply]
      refine ⟨?_, ?_⟩ <;> split <;> linarith
    have hmono : eigVal A 1 ≤ eigVal (A + twoParam (m+2) t t) 1 := by
      refine eigVal_mono_quad hA.1 hBmem.1 1 fun x => ?_
      rw [quad_form_add, quad_form_twoParam]
      nlinarith [sq_nonneg (∑ i, x i)]
    have hup : eigVal (A + twoParam (m+2) t t) 1 ≤ phi t (b+t) (m+2) :=
      eigVal_second_le_phi_pos ht (by linarith) hBmem
    have hsh := phi_shift hb ht.le (m+2)
    have hfin : ((m+2:ℕ):ℝ) * t / 2 ≤ ε := by
      rw [htdef]; field_simp; linarith
    linarith


/-! ## Stage 2 -/

lemma phi_root {a b : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    (phi a b N)^2 - b*(N:ℝ)*(phi a b N)
      + (b^2-a^2)*(((N/2 : ℕ):ℝ) * ((N:ℝ) - ((N/2:ℕ):ℝ))) = 0 := by
  rcases Nat.even_or_odd N with he | ho
  · obtain ⟨t, ht⟩ := id he
    have hdiv : N/2 = t := by omega
    have hcast : (N:ℝ) = 2*(t:ℝ) := by rw [ht]; push_cast; ring
    rw [phi_even ha he, hdiv, hcast]
    ring
  · have hne : ¬ Even N := by simpa [Nat.not_even_iff_odd] using ho
    obtain ⟨t, ht⟩ := ho
    have hdiv : N/2 = t := by omega
    have hcast : (N:ℝ) = 2*(t:ℝ)+1 := by rw [ht]; push_cast; ring
    have hN1 : (1:ℝ) ≤ (N:ℝ)^2 := by rw [hcast]; nlinarith [Nat.cast_nonneg (α := ℝ) t]
    have hnn : (0:ℝ) ≤ ((N:ℝ)^2-1)*a^2 + b^2 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hs := Real.sq_sqrt hnn
    have h4 : ((t:ℝ))*((N:ℝ)-(t:ℝ)) = ((N:ℝ)^2-1)/4 := by rw [hcast]; ring
    rw [phi_odd hne, hdiv, h4]
    linear_combination hs/4

lemma phi_le_b_half {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (N : ℕ) :
    phi a b N ≤ b * ((N/2 : ℕ):ℝ) := by
  have hb : (0:ℝ) ≤ b := le_trans ha hab
  rcases Nat.even_or_odd N with he | ho
  · obtain ⟨t, ht⟩ := id he
    have hdiv : N/2 = t := by omega
    have hcast : (N:ℝ) = 2*(t:ℝ) := by rw [ht]; push_cast; ring
    rw [phi_even ha he, hdiv, hcast]
    nlinarith [Nat.cast_nonneg (α := ℝ) t]
  · have hne : ¬ Even N := by simpa [Nat.not_even_iff_odd] using ho
    obtain ⟨t, ht⟩ := ho
    have hdiv : N/2 = t := by omega
    have hcast : (N:ℝ) = 2*(t:ℝ)+1 := by rw [ht]; push_cast; ring
    have hN1 : (1:ℝ) ≤ (N:ℝ)^2 := by rw [hcast]; nlinarith [Nat.cast_nonneg (α := ℝ) t]
    have hnn : (0:ℝ) ≤ ((N:ℝ)^2-1)*a^2 + b^2 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hbs : b ≤ Real.sqrt (((N:ℝ)^2-1)*a^2 + b^2) := by
      have h1 : b = Real.sqrt (b^2) := (Real.sqrt_sq hb).symm
      rw [h1]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg a])
    rw [phi_odd hne, hdiv]
    have hNt : (N:ℝ) * b - 2*(t:ℝ)*b = b := by rw [hcast]; ring
    linarith [hbs, hNt]

/-- The linear map sending `(u,v)` to the vector equal to `u` on the first block of size `p`
and `v` on the complementary block. -/
def blockEmb (N p : ℕ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin N → ℝ) where
  toFun c := fun i => if (i:ℕ) < p then c 0 else c 1
  map_add' c d := by funext i; by_cases h : (i:ℕ) < p <;> simp [h]
  map_smul' r c := by funext i; by_cases h : (i:ℕ) < p <;> simp [h]

lemma blockEmb_apply (N p : ℕ) (c : Fin 2 → ℝ) (i : Fin N) :
    blockEmb N p c i = if (i:ℕ) < p then c 0 else c 1 := rfl

/-- The two-dimensional subspace of vectors constant on each of the two blocks. -/
def blockSpace (N p : ℕ) : Submodule ℝ (Fin N → ℝ) := LinearMap.range (blockEmb N p)

lemma blockEmb_injective {N p : ℕ} (hp1 : 1 ≤ p) (hpN : p < N) :
    Function.Injective (blockEmb N p) := by
  intro c d h
  have h0 := congrFun h ⟨0, by omega⟩
  have h1 := congrFun h ⟨p, hpN⟩
  simp only [blockEmb_apply] at h0 h1
  rw [if_pos (show 0 < p from hp1), if_pos (show 0 < p from hp1)] at h0
  rw [if_neg (lt_irrefl p), if_neg (lt_irrefl p)] at h1
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1

lemma finrank_blockSpace {N p : ℕ} (hp1 : 1 ≤ p) (hpN : p < N) :
    Module.finrank ℝ (blockSpace N p) = 2 := by
  rw [blockSpace, LinearMap.finrank_range_of_inj (blockEmb_injective hp1 hpN)]
  simp

lemma dot_blockEmb {N p : ℕ} (hp : p ≤ N) (c : Fin 2 → ℝ) :
    (blockEmb N p c) ⬝ᵥ (blockEmb N p c)
      = (p:ℝ)*(c 0)^2 + ((N:ℝ)-(p:ℝ))*(c 1)^2 := by
  rw [dotProduct_self, ← sum_ite_lt N p hp ((c 0)^2) ((c 1)^2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [blockEmb_apply]
  by_cases h : (i:ℕ) < p <;> simp [h]

lemma quad_blockEmb {N p : ℕ} {a b : ℝ} (hp : p ≤ N) (c : Fin 2 → ℝ) :
    (blockEmb N p c) ⬝ᵥ (blockSign N p a b) *ᵥ (blockEmb N p c)
      = b*(p:ℝ)^2*(c 0)^2 + 2*a*(p:ℝ)*((N:ℝ)-(p:ℝ))*(c 0)*(c 1)
        + b*((N:ℝ)-(p:ℝ))^2*(c 1)^2 := by
  have h1 : ∑ i : Fin N, (blockEmb N p c) i = (p:ℝ)*(c 0) + ((N:ℝ)-(p:ℝ))*(c 1) := by
    rw [← sum_ite_lt N p hp (c 0) (c 1)]
    exact Finset.sum_congr rfl fun i _ => rfl
  have h2 : ∑ i : Fin N, (if (i:ℕ) < p then (1:ℝ) else -1) * (blockEmb N p c) i
      = (p:ℝ)*(c 0) + ((N:ℝ)-(p:ℝ))*(-(c 1)) := by
    rw [← sum_ite_lt N p hp (c 0) (-(c 1))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [blockEmb_apply]
    by_cases h : (i:ℕ) < p <;> simp [h]
  rw [blockSign, quad_form_signMat, h1, h2]
  ring

/-- **Stage 2 milestone**: the balanced two-block matrix attains `phi` at the second
eigenvalue. -/
lemma phi_le_eigVal_blockSign {m : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    phi a b (m+2) ≤ eigVal (blockSign (m+2) ((m+2)/2) a b) 1 := by
  set N := m + 2 with hN
  set p := N / 2 with hp
  have hp1 : 1 ≤ p := by omega
  have hpN : p < N := by omega
  have hpN' : p ≤ N := le_of_lt hpN
  have hb : (0:ℝ) ≤ b := le_trans ha hab
  set pr : ℝ := (p:ℝ) with hpr
  set qr : ℝ := (N:ℝ) - pr with hqr
  have hpr0 : 0 < pr := by
    rw [hpr]; exact_mod_cast hp1
  have hqr0 : 0 < qr := by
    rw [hqr, hpr]
    have : (p:ℝ) < (N:ℝ) := by exact_mod_cast hpN
    linarith
  have hprq : pr ≤ qr := by
    rw [hqr, hpr]
    have : 2 * p ≤ N := by omega
    have h2 : (2:ℝ) * (p:ℝ) ≤ (N:ℝ) := by exact_mod_cast this
    linarith
  set lam := phi a b N with hlam
  have hlam0 : 0 ≤ lam := phi_nonneg ha hab N
  have hlamp : lam ≤ b * pr := phi_le_b_half ha hab N
  have hlamq : lam ≤ b * qr := le_trans hlamp (by nlinarith)
  have hroot : lam^2 - b*(N:ℝ)*lam + (b^2-a^2)*(pr*qr) = 0 := phi_root ha N
  have hval : ((1 : Fin (m+2)) : ℕ) = 1 := by simp
  refine le_eigVal_of_subspace (blockSign_mem hab).1 1 (blockSpace N p) ?_ lam ?_
  · rw [hval, finrank_blockSpace hp1 hpN]
  · rintro x ⟨c, rfl⟩
    rw [dot_blockEmb hpN', quad_blockEmb hpN']
    have hA : 0 ≤ pr * (b*pr - lam) := mul_nonneg hpr0.le (by linarith)
    have hC : 0 ≤ qr * (b*qr - lam) := mul_nonneg hqr0.le (by linarith)
    have hsum : pr + qr = (N:ℝ) := by rw [hqr]; ring
    have hprod : (b*pr - lam)*(b*qr - lam) = a^2*(pr*qr) := by
      linear_combination hroot - b*lam*hsum
    have hD : (2*a*pr*qr)^2 ≤ 4 * (pr * (b*pr - lam)) * (qr * (b*qr - lam)) :=
      le_of_eq (by linear_combination (-4*pr*qr)*hprod)
    have := quad_nonneg' hA hC hD (u := c 0) (v := c 1)
    rw [← hpr, ← hqr]
    nlinarith [this]


/-! ## Stage 3: the complete formulas (2.5)–(2.9) -/

/-- The value `phi a b n` is attained by the balanced two-block matrix. -/
lemma phi_mem {m : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    phi a b (m+2) ∈ eigRange (m+2) a b 1 :=
  ⟨blockSign (m+2) ((m+2)/2) a b, blockSign_mem hab,
    le_antisymm (eigVal_second_le_phi ha hab (blockSign_mem hab))
      (phi_le_eigVal_blockSign ha hab)⟩

/-- **Formula (2.6)**: for `n ≥ 2` and `0 ≤ a ≤ b`, the maximum of `λ₂` over `S_n([a,b])`
is `phi a b n`. -/
theorem isGreatest_eigRange_second {m : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IsGreatest (eigRange (m+2) a b 1) (phi a b (m+2)) := by
  refine ⟨phi_mem ha hab, ?_⟩
  rintro t ⟨A, hA, rfl⟩
  exact eigVal_second_le_phi ha hab hA

/-- **Formula (2.6), even case**: `U₂ = n(b-a)/2`. -/
theorem isGreatest_eigRange_second_even {m : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hm : Even (m+2)) :
    IsGreatest (eigRange (m+2) a b 1) (((m+2 : ℕ):ℝ)*(b-a)/2) := by
  rw [← phi_even ha hm]
  exact isGreatest_eigRange_second ha hab

/-- **Formula (2.6), odd case**: `U₂ = (nb - √((n²-1)a² + b²))/2`. -/
theorem isGreatest_eigRange_second_odd {m : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hm : ¬ Even (m+2)) :
    IsGreatest (eigRange (m+2) a b 1)
      ((((m+2 : ℕ):ℝ)*b - Real.sqrt ((((m+2:ℕ):ℝ)^2-1)*a^2 + b^2))/2) := by
  rw [← phi_odd hm]
  exact isGreatest_eigRange_second ha hab

/-- **Formula (2.7)**: `U₂(n;0,b) = b ⌊n/2⌋`. -/
lemma phi_zero {b : ℝ} (hb : 0 ≤ b) (N : ℕ) : phi 0 b N = b * ((N/2 : ℕ):ℝ) := by
  rcases Nat.even_or_odd N with he | ho
  · obtain ⟨t, ht⟩ := id he
    have hdiv : N/2 = t := by omega
    have hcast : (N:ℝ) = 2*(t:ℝ) := by rw [ht]; push_cast; ring
    rw [phi_even le_rfl he, hdiv, hcast]; ring
  · have hne : ¬ Even N := by simpa [Nat.not_even_iff_odd] using ho
    obtain ⟨t, ht⟩ := ho
    have hdiv : N/2 = t := by omega
    have hcast : (N:ℝ) = 2*(t:ℝ)+1 := by rw [ht]; push_cast; ring
    rw [phi_odd hne, hdiv]
    have : Real.sqrt (((N:ℝ)^2-1)*0^2 + b^2) = b := by
      rw [show ((N:ℝ)^2-1)*0^2 + b^2 = b^2 by ring, Real.sqrt_sq hb]
    rw [this, hcast]; ring

theorem isGreatest_eigRange_second_zero {m : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    IsGreatest (eigRange (m+2) 0 b 1) (b * (((m+2)/2 : ℕ):ℝ)) := by
  rw [← phi_zero hb]
  exact isGreatest_eigRange_second le_rfl hb

/-! ### The nonpositive dual, formula (2.9) -/

/-- **Formula (2.9)**: for `n ≥ 2` and `a ≤ b ≤ 0`, the minimum of `λ_{n-1}` over `S_n([a,b])`
is `-phi (-b) (-a) n`. -/
theorem isLeast_eigRange_penultimate {m : ℕ} {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) :
    IsLeast (eigRange (m+2) a b ⟨m, by omega⟩) (- phi (-b) (-a) (m+2)) := by
  refine isLeast_of_isGreatest_neg ?_
  have hrev : Fin.rev (⟨m, by omega⟩ : Fin (m+2)) = 1 := by
    refine Fin.ext ?_
    simp [Fin.val_rev]
  rw [eigRange_neg' (m+2) a b ⟨m, by omega⟩, hrev, neg_neg]
  exact isGreatest_eigRange_second (by linarith) (by linarith)

/-- **Formula (2.9), even case**: `L_{n-1} = n(a-b)/2`. -/
theorem isLeast_eigRange_penultimate_even {m : ℕ} {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0)
    (hm : Even (m+2)) :
    IsLeast (eigRange (m+2) a b ⟨m, by omega⟩) (((m+2 : ℕ):ℝ)*(a-b)/2) := by
  have h := isLeast_eigRange_penultimate hab hb (m := m)
  rw [phi_even (by linarith : (0:ℝ) ≤ -b) hm] at h
  rw [show ((m+2 : ℕ):ℝ)*(a-b)/2 = -(((m+2 : ℕ):ℝ)*(-a - -b)/2) by ring]
  exact h

/-- **Formula (2.9), odd case**: `L_{n-1} = (na + √(a² + (n²-1)b²))/2`. -/
theorem isLeast_eigRange_penultimate_odd {m : ℕ} {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0)
    (hm : ¬ Even (m+2)) :
    IsLeast (eigRange (m+2) a b ⟨m, by omega⟩)
      ((((m+2 : ℕ):ℝ)*a + Real.sqrt (a^2 + (((m+2:ℕ):ℝ)^2-1)*b^2))/2) := by
  have h := isLeast_eigRange_penultimate hab hb (m := m)
  rw [phi_odd hm] at h
  rw [show ((((m+2 : ℕ):ℝ)*a + Real.sqrt (a^2 + (((m+2:ℕ):ℝ)^2-1)*b^2))/2)
      = -((((m+2 : ℕ):ℝ)*(-a) - Real.sqrt ((((m+2:ℕ):ℝ)^2-1)*(-b)^2 + (-a)^2))/2) by
    rw [show (((m+2:ℕ):ℝ)^2-1)*(-b)^2 + (-a)^2 = a^2 + (((m+2:ℕ):ℝ)^2-1)*b^2 by ring]; ring]
  exact h

/-! ## Stage 4: the ranges are compact intervals -/

/-- A crude bound for a quadratic form in terms of the entrywise `1`-norm. -/
lemma quad_form_abs_le (C : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    |x ⬝ᵥ C *ᵥ x| ≤ ((n : ℝ) * ∑ i, ∑ j, |C i j|) * (x ⬝ᵥ x) := by
  classical
  set S : ℝ := ∑ i, ∑ j, |C i j| with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hle : ∀ i j, |C i j| ≤ S := by
    intro i j
    calc |C i j| ≤ ∑ j', |C i j'| :=
          Finset.single_le_sum (f := fun j' => |C i j'|)
            (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
      _ ≤ S := Finset.single_le_sum (f := fun i' => ∑ j', |C i' j'|)
            (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) (Finset.mem_univ i)
  have hterm : ∀ i j, |C i j * x i * x j| ≤ S * ((x i)^2 + (x j)^2) / 2 := by
    intro i j
    have h1 : |C i j * x i * x j| = |C i j| * |x i * x j| := by
      rw [mul_assoc, abs_mul]
    have h2 : |x i * x j| ≤ ((x i)^2 + (x j)^2)/2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j), abs_nonneg (x i),
        abs_nonneg (x j)]
    have h3 : (0:ℝ) ≤ ((x i)^2 + (x j)^2)/2 := by positivity
    calc |C i j * x i * x j| = |C i j| * |x i * x j| := h1
      _ ≤ S * (((x i)^2 + (x j)^2)/2) := by
          exact mul_le_mul (hle i j) h2 (abs_nonneg _) hSnn
      _ = S * ((x i)^2 + (x j)^2) / 2 := by ring
  have hsum : |x ⬝ᵥ C *ᵥ x| ≤ ∑ i, ∑ j, S * ((x i)^2 + (x j)^2) / 2 := by
    rw [quad_form]
    calc |∑ i, ∑ j, C i j * x i * x j| ≤ ∑ i, |∑ j, C i j * x i * x j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, S * ((x i)^2 + (x j)^2) / 2 :=
          Finset.sum_le_sum fun i _ =>
            le_trans (Finset.abs_sum_le_sum_abs _ _)
              (Finset.sum_le_sum fun j _ => hterm i j)
  have hpull : ∑ i, ∑ j, S * ((x i)^2 + (x j)^2) / 2
      = (S/2) * ∑ i, ∑ j : Fin n, ((x i)^2 + (x j)^2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  set T : ℝ := ∑ i, (x i)^2 with hT
  have hin : ∀ i : Fin n, ∑ j : Fin n, ((x i)^2 + (x j)^2) = (n:ℝ)*(x i)^2 + T := by
    intro i
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hT]
  have hdouble : ∑ i, ∑ j : Fin n, ((x i)^2 + (x j)^2) = 2*(n:ℝ)*T := by
    rw [Finset.sum_congr rfl (fun i _ => hin i), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← hT]
    ring
  have hcalc : ∑ i, ∑ j, S * ((x i)^2 + (x j)^2) / 2 = ((n : ℝ) * S) * (x ⬝ᵥ x) := by
    rw [hpull, hdouble, dotProduct_self, ← hT]
    ring
  rw [← hcalc]
  exact hsum

/-- A shifted monotonicity statement: an additive perturbation of the quadratic form moves the
ordered eigenvalues by at most the same amount. -/
lemma eigVal_le_add_of_quad {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (k : Fin n) (t : ℝ)
    (h : ∀ x : Fin n → ℝ, x ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ B *ᵥ x + t * (x ⬝ᵥ x)) :
    eigVal A k ≤ eigVal B k + t := by
  obtain ⟨V, hV, hVt⟩ := exists_subspace_le hB k
  refine eigVal_le_of_subspace hA k V hV _ fun x hx => ?_
  have := hVt x hx
  have := h x
  nlinarith

/-- **A Lipschitz estimate for the ordered eigenvalues** in the entrywise `1`-norm. -/
lemma abs_eigVal_sub_le {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (k : Fin n) :
    |eigVal A k - eigVal B k| ≤ (n : ℝ) * ∑ i, ∑ j, |A i j - B i j| := by
  set S : ℝ := (n : ℝ) * ∑ i, ∑ j, |A i j - B i j| with hS
  have hSnn : 0 ≤ S := by
    refine mul_nonneg (Nat.cast_nonneg n) ?_
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hquad : ∀ x : Fin n → ℝ, |x ⬝ᵥ A *ᵥ x - x ⬝ᵥ B *ᵥ x| ≤ S * (x ⬝ᵥ x) := by
    intro x
    have h1 : x ⬝ᵥ A *ᵥ x - x ⬝ᵥ B *ᵥ x = x ⬝ᵥ (A - B) *ᵥ x := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
    rw [h1, hS]
    exact quad_form_abs_le (A - B) x
  have h1 : eigVal A k ≤ eigVal B k + S := by
    refine eigVal_le_add_of_quad hA hB k S fun x => ?_
    have := abs_le.1 (hquad x)
    linarith [this.2]
  have h2 : eigVal B k ≤ eigVal A k + S := by
    refine eigVal_le_add_of_quad hB hA k S fun x => ?_
    have := abs_le.1 (hquad x)
    linarith [this.1]
  rw [abs_le]
  constructor <;> linarith

/-- A real linear combination of Hermitian matrices is Hermitian. -/
lemma herm_smul_add {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (s t : ℝ) : (s • A + t • B).IsHermitian := by
  ext i j
  have ha : A j i = A i j := by
    have := congrFun (congrFun hA i) j
    simpa [Matrix.conjTranspose_apply] using this
  have hb : B j i = B i j := by
    have := congrFun (congrFun hB i) j
    simpa [Matrix.conjTranspose_apply] using this
  simp only [Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.smul_apply, star_trivial,
    smul_eq_mul]
  rw [ha, hb]

/-- `SymIcc n a b` is convex: it is stable under taking segments. -/
lemma segment_mem_SymIcc {n : ℕ} {a b : ℝ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ SymIcc n a b) (hB : B ∈ SymIcc n a b) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (1 - θ) • A + θ • B ∈ SymIcc n a b := by
  refine ⟨herm_smul_add hA.1 hB.1 _ _, fun i j => ?_⟩
  · have hA' := hA.2 i j
    have hB' := hB.2 i j
    simp only [Set.mem_Icc] at hA' hB' ⊢
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    constructor
    · nlinarith [hA'.1, hB'.1]
    · nlinarith [hA'.2, hB'.2]

/-- The ordered eigenvalue is continuous along a segment of matrices. -/
lemma continuous_eigVal_segment {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (k : Fin n) :
    Continuous (fun θ : ℝ => eigVal ((1 - θ) • A + θ • B) k) := by
  classical
  set K : ℝ := (n : ℝ) * ∑ i, ∑ j, |A i j - B i j| with hK
  have hKnn : 0 ≤ K := by
    refine mul_nonneg (Nat.cast_nonneg n) ?_
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hherm : ∀ θ : ℝ, ((1 - θ) • A + θ • B).IsHermitian :=
    fun θ => herm_smul_add hA hB _ _
  have hlip : ∀ θ η : ℝ,
      |eigVal ((1 - θ) • A + θ • B) k - eigVal ((1 - η) • A + η • B) k| ≤ K * |θ - η| := by
    intro θ η
    have hbound := abs_eigVal_sub_le (hherm θ) (hherm η) k
    have hent : ∀ i j, |((1 - θ) • A + θ • B) i j - ((1 - η) • A + η • B) i j|
        = |θ - η| * |A i j - B i j| := by
      intro i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [show (1 - θ) * A i j + θ * B i j - ((1 - η) * A i j + η * B i j)
          = -((θ - η) * (A i j - B i j)) by ring, abs_neg, abs_mul]
    have hsum : (∑ i, ∑ j, |((1 - θ) • A + θ • B) i j - ((1 - η) • A + η • B) i j|)
        = |θ - η| * ∑ i, ∑ j, |A i j - B i j| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => hent i j
    rw [hsum] at hbound
    calc |eigVal ((1 - θ) • A + θ • B) k - eigVal ((1 - η) • A + η • B) k|
        ≤ (n : ℝ) * (|θ - η| * ∑ i, ∑ j, |A i j - B i j|) := hbound
      _ = K * |θ - η| := by rw [hK]; ring
  refine Metric.continuous_iff.2 fun θ ε hε => ?_
  refine ⟨ε / (K + 1), by positivity, fun η hη => ?_⟩
  have h1 := hlip η θ
  rw [Real.dist_eq] at hη ⊢
  have h2 : K * |η - θ| ≤ K * (ε / (K + 1)) :=
    mul_le_mul_of_nonneg_left hη.le hKnn
  have h3 : K * (ε / (K + 1)) < ε := by
    rw [div_eq_mul_inv, ← mul_assoc]
    rw [mul_comm K ε, mul_assoc]
    have : K * (K+1)⁻¹ < 1 := by
      rw [mul_inv_lt_iff₀ (by linarith)]
      linarith
    nlinarith
  linarith

/-- The image of a range: `eigRange` is order-connected. -/
lemma eigRange_ordConnected (n : ℕ) (a b : ℝ) (k : Fin n) :
    (eigRange n a b k).OrdConnected := by
  constructor
  rintro s ⟨A, hA, rfl⟩ u ⟨B, hB, rfl⟩ v hv
  simp only [Set.mem_Icc] at hv
  set f : ℝ → ℝ := fun θ => eigVal ((1 - θ) • A + θ • B) k with hf
  have hc : ContinuousOn f (Set.Icc 0 1) :=
    (continuous_eigVal_segment A B hA.1 hB.1 k).continuousOn
  have h0 : f 0 = eigVal A k := by simp [hf]
  have h1 : f 1 = eigVal B k := by simp [hf]
  have hmem : v ∈ Set.Icc (f 0) (f 1) := by rw [h0, h1]; exact Set.mem_Icc.2 hv
  obtain ⟨θ, hθ, hfθ⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hc hmem
  exact ⟨(1 - θ) • A + θ • B, segment_mem_SymIcc hA hB (Set.mem_Icc.1 hθ).1 (Set.mem_Icc.1 hθ).2,
    hfθ⟩

/-- An order-connected set with a least and a greatest element is the corresponding closed
interval. -/
lemma eq_Icc_of_isLeast_isGreatest {S : Set ℝ} {l u : ℝ} (hS : S.OrdConnected)
    (hl : IsLeast S l) (hu : IsGreatest S u) : S = Set.Icc l u := by
  refine Set.Subset.antisymm (fun s hs => Set.mem_Icc.2 ⟨hl.2 hs, hu.2 hs⟩) ?_
  intro s hs
  exact hS.out hl.1 hu.1 hs

/-- **The range of `λ₁`** is the interval `[L₁, U₁]`. -/
theorem eigRange_first_eq {m : ℕ} {a b : ℝ} (hab : a ≤ b) :
    eigRange (m+2) a b 0 = Set.Icc (L1 (m+2) a b) (U1 (m+2) a b) :=
  eq_Icc_of_isLeast_isGreatest (eigRange_ordConnected _ _ _ _)
    (isLeast_eigRange_first hab) (isGreatest_eigRange_first hab)

/-- **The range of `λₙ`** is the interval `[Lₙ, Uₙ]`. -/
theorem eigRange_last_eq {m : ℕ} {a b : ℝ} (hab : a ≤ b) :
    eigRange (m+2) a b (Fin.last (m+1)) = Set.Icc (Ln (m+2) a b) (Un (m+2) a b) :=
  eq_Icc_of_isLeast_isGreatest (eigRange_ordConnected _ _ _ _)
    (isLeast_eigRange_last hab) (isGreatest_eigRange_last hab)

/-- **The range of `λ₂` for a nonnegative interval** is `[a-b, phi a b n]`. -/
theorem eigRange_second_eq {m : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    eigRange (m+2) a b 1 = Set.Icc (a - b) (phi a b (m+2)) :=
  eq_Icc_of_isLeast_isGreatest (eigRange_ordConnected _ _ _ _)
    (isLeast_eigRange_second ha hab) (isGreatest_eigRange_second ha hab)

/-- **The range of `λ_{n-1}` for a nonpositive interval** is `[-phi (-b) (-a) n, b-a]`. -/
theorem eigRange_penultimate_eq {m : ℕ} {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) :
    eigRange (m+2) a b ⟨m, by omega⟩ = Set.Icc (- phi (-b) (-a) (m+2)) (b - a) :=
  eq_Icc_of_isLeast_isGreatest (eigRange_ordConnected _ _ _ _)
    (isLeast_eigRange_penultimate hab hb) (isGreatest_eigRange_penultimate hab hb)

/-! ### The exceptional case `n = 1` -/

lemma eigVal_one_eq {A : Matrix (Fin 1) (Fin 1) ℝ} (hA : A.IsHermitian) (k : Fin 1) :
    eigVal A k = A 0 0 := by
  have hquad : ∀ x : Fin 1 → ℝ, x ⬝ᵥ A *ᵥ x = A 0 0 * (x ⬝ᵥ x) := by
    intro x
    rw [quad_form, dotProduct_self]
    simp [sq]
    ring
  refine le_antisymm (eigVal_le_of_forall hA k _ fun x => le_of_eq (hquad x)) ?_
  refine le_eigVal_of_forall hA k _ fun x => le_of_eq (hquad x).symm

/-- **The exceptional case `n = 1`**: the range of the unique eigenvalue is `[a,b]`.
(The hypothesis `a ≤ b` turns out to be unnecessary: for `b < a` both sides are empty.) -/
theorem eigRange_one {a b : ℝ} : eigRange 1 a b 0 = Set.Icc a b := by
  ext t
  constructor
  · rintro ⟨A, hA, rfl⟩
    show eigVal A 0 ∈ Set.Icc a b
    rw [eigVal_one_eq hA.1]
    exact hA.2 0 0
  · intro ht
    refine ⟨Matrix.of fun _ _ => t, ⟨?_, fun i j => ht⟩, ?_⟩
    · ext i j; simp [Matrix.conjTranspose_apply]
    · show eigVal (Matrix.of fun _ _ => t) 0 = t
      rw [eigVal_one_eq (by ext i j; simp [Matrix.conjTranspose_apply])]
      rfl

/-! ## Stage 5: general bounds and the density-matrix characterization -/

/-! ### Trace identities in the spectral coordinates -/

lemma trace_eq_sum_eigVal {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    A.trace = ∑ i, eigVal A i := by
  obtain ⟨W, h1, h2, h3⟩ := spectral_diag hA
  conv_lhs => rw [h3]
  rw [Matrix.trace_mul_comm (W * diagonal (eigVal A)) Wᵀ, ← Matrix.mul_assoc, h1,
    Matrix.one_mul, Matrix.trace_diagonal]

lemma sum_sq_entries_eq_sum_sq_eigVal {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    ∑ i, ∑ j, (A i j)^2 = ∑ i, (eigVal A i)^2 := by
  obtain ⟨W, h1, h2, h3⟩ := spectral_diag hA
  have hAA : A * A = W * diagonal (fun i => (eigVal A i)^2) * Wᵀ := by
    conv_lhs => rw [h3]
    rw [show W * diagonal (eigVal A) * Wᵀ * (W * diagonal (eigVal A) * Wᵀ)
        = W * diagonal (eigVal A) * (Wᵀ * W) * (diagonal (eigVal A) * Wᵀ) by
          simp [Matrix.mul_assoc], h1, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_assoc W (diagonal (eigVal A)) (diagonal (eigVal A)),
      Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    simp [sq]
  have h4 : (A * A).trace = ∑ i, (eigVal A i)^2 := by
    rw [hAA, Matrix.trace_mul_comm (W * diagonal (fun i => (eigVal A i)^2)) Wᵀ,
      ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.trace_diagonal]
  have h5 : (A * A).trace = ∑ i, ∑ j, (A i j)^2 := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsym : A j i = A i j := by
      have := congrFun (congrFun hA i) j
      simpa [Matrix.conjTranspose_apply] using this
    rw [hsym, sq]
  rw [← h5, h4]

/-! ### The order-statistic (variance) lemma -/

/-- **Order-statistic lemma (8.1)**: if the mean of an antitone family is `m` and the `k`-th
entry is above the mean, then its deviation is controlled by the variance. -/
lemma order_stat_upper {n : ℕ} (mu : Fin n → ℝ) (hmu : Antitone mu) (k : Fin n) (m : ℝ)
    (hm : ∑ i, (mu i - m) = 0) (hd : m ≤ mu k) :
    ((((k:ℕ)+1 : ℝ)) * (n:ℝ)) * (mu k - m)^2
      ≤ ((n:ℝ) - (((k:ℕ)+1 : ℝ))) * ∑ i, (mu i - m)^2 := by
  classical
  set d : Fin n → ℝ := fun i => mu i - m with hdd
  set K : ℕ := (k:ℕ) + 1 with hK
  have hKn : K ≤ n := k.isLt
  set P : Finset (Fin n) := Finset.Iic k with hP
  have hPcard : P.card = K := by rw [hP, Fin.card_Iic]
  have hQcard : (Pᶜ).card = n - K := by
    rw [Finset.card_compl, hPcard]; simp
  have hδ : 0 ≤ d k := sub_nonneg.2 hd
  have hPle : ∀ i ∈ P, d k ≤ d i := by
    intro i hi
    exact sub_le_sub_right (hmu (Finset.mem_Iic.1 hi)) m
  have hsumP : (K:ℝ) * d k ≤ ∑ i ∈ P, d i := by
    calc (K:ℝ) * d k = ∑ _i ∈ P, d k := by rw [Finset.sum_const, hPcard, nsmul_eq_mul]
      _ ≤ ∑ i ∈ P, d i := Finset.sum_le_sum hPle
  have hsplit : ∑ i ∈ P, d i + ∑ i ∈ Pᶜ, d i = 0 := by
    rw [Finset.sum_add_sum_compl]; exact hm
  have hsqP : (K:ℝ) * (d k)^2 ≤ ∑ i ∈ P, (d i)^2 := by
    calc (K:ℝ) * (d k)^2 = ∑ _i ∈ P, (d k)^2 := by
          rw [Finset.sum_const, hPcard, nsmul_eq_mul]
      _ ≤ ∑ i ∈ P, (d i)^2 := by
          refine Finset.sum_le_sum fun i hi => ?_
          have := hPle i hi
          nlinarith
  have hQsum : ∑ i ∈ Pᶜ, d i ≤ -((K:ℝ) * d k) := by linarith
  have hCS : (∑ i ∈ Pᶜ, d i)^2 ≤ ((Pᶜ).card : ℝ) * ∑ i ∈ Pᶜ, (d i)^2 :=
    sq_sum_le_card_mul_sum_sq
  have hsqQ : ((K:ℝ) * d k)^2 ≤ ((n:ℝ) - (K:ℝ)) * ∑ i ∈ Pᶜ, (d i)^2 := by
    have hcast : (((Pᶜ).card : ℕ) : ℝ) = (n:ℝ) - (K:ℝ) := by
      rw [hQcard, Nat.cast_sub hKn]
    rw [hcast] at hCS
    have h1 : ((K:ℝ) * d k)^2 ≤ (∑ i ∈ Pᶜ, d i)^2 := by
      have hK0 : (0:ℝ) ≤ (K:ℝ) * d k := mul_nonneg (Nat.cast_nonneg K) hδ
      nlinarith [hQsum, hK0]
    linarith
  have hV : ∑ i, (d i)^2 = ∑ i ∈ P, (d i)^2 + ∑ i ∈ Pᶜ, (d i)^2 :=
    (Finset.sum_add_sum_compl _ _).symm
  have hnK : (0:ℝ) ≤ (n:ℝ) - (K:ℝ) := by
    have : (K:ℝ) ≤ (n:ℝ) := by exact_mod_cast hKn
    linarith
  have hKr : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
  have hcast2 : (((k:ℕ):ℝ) + 1) = (K:ℝ) := by rw [hK]; push_cast; ring
  rw [hcast2, hV]
  nlinarith [mul_le_mul_of_nonneg_left hsqP hnK, hsqQ, sq_nonneg (d k)]

/-! ### Fixing the diagonal at an endpoint -/

/-- The matrix obtained from `A` by setting all diagonal entries to `b`. -/
def diagFix (A : Matrix (Fin n) (Fin n) ℝ) (b : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i = j then b else A i j

lemma diagFix_diag (A : Matrix (Fin n) (Fin n) ℝ) (b : ℝ) (i : Fin n) : diagFix A b i i = b := by
  simp [diagFix]

lemma diagFix_offDiag (A : Matrix (Fin n) (Fin n) ℝ) (b : ℝ) {i j : Fin n} (h : i ≠ j) :
    diagFix A b i j = A i j := by
  simp [diagFix, h]

lemma diagFix_mem {a b : ℝ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ SymIcc n a b)
    (hab : a ≤ b) : diagFix A b ∈ SymIcc n a b := by
  refine ⟨?_, fun i j => ?_⟩
  · ext i j
    have hsym : A j i = A i j := by
      have := congrFun (congrFun hA.1 i) j
      simpa [Matrix.conjTranspose_apply] using this
    simp only [Matrix.conjTranspose_apply, diagFix, Matrix.of_apply, star_trivial]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h, hsym]
  · simp only [diagFix, Matrix.of_apply]
    split
    · exact ⟨hab, le_rfl⟩
    · exact hA.2 i j

lemma eigVal_le_diagFix {a b : ℝ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ SymIcc n a b)
    (hab : a ≤ b) (k : Fin n) : eigVal A k ≤ eigVal (diagFix A b) k := by
  refine eigVal_mono_quad hA.1 (diagFix_mem hA hab).1 k fun x => ?_
  rw [quad_form, quad_form]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases h : i = j
  · subst h
    have h1 : A i i ≤ b := (hA.2 i i).2
    rw [diagFix_diag A b i]
    nlinarith [sq_nonneg (x i)]
  · rw [diagFix_offDiag A b h]

/-! ### The variance bounds (2.14) and (2.15) -/

/-- `rho a b = max |a| |b|`. -/
noncomputable def rho (a b : ℝ) : ℝ := max |a| |b|

lemma rho_nonneg (a b : ℝ) : 0 ≤ rho a b := le_trans (abs_nonneg a) (le_max_left _ _)

lemma abs_le_rho {a b x : ℝ} (hx : x ∈ Set.Icc a b) : |x| ≤ rho a b := by
  rcases Set.mem_Icc.1 hx with ⟨h1, h2⟩
  have ha : |a| ≤ rho a b := by rw [rho]; exact le_max_left _ _
  have hb : |b| ≤ rho a b := by rw [rho]; exact le_max_right _ _
  have h3 : -|a| ≤ a := neg_abs_le a
  have h4 : b ≤ |b| := le_abs_self b
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **Formula (2.14)**: an explicit upper bound for every ordered eigenvalue. -/
theorem eigVal_le_variance_bound {n : ℕ} {a b : ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ SymIcc n a b) (hab : a ≤ b) (k : Fin n) :
    eigVal A k ≤ b + rho a b *
      Real.sqrt ((((n:ℝ) - (((k:ℕ):ℝ)+1)) * ((n:ℝ)-1))/(((k:ℕ):ℝ)+1)) := by
  classical
  set R := rho a b with hR
  have hR0 : 0 ≤ R := rho_nonneg a b
  set B := diagFix A b with hB
  have hBmem : B ∈ SymIcc n a b := diagFix_mem hA hab
  have hBd : ∀ i, B i i = b := by rw [hB]; exact fun i => diagFix_diag A b i
  have hmono : eigVal A k ≤ eigVal B k := eigVal_le_diagFix hA hab k
  set K : ℝ := ((k:ℕ):ℝ) + 1 with hKdef
  have hK1 : (1:ℝ) ≤ K := by rw [hKdef]; have := Nat.cast_nonneg (α := ℝ) (k:ℕ); linarith
  have hKn : K ≤ (n:ℝ) := by
    rw [hKdef]
    have : ((k:ℕ):ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast k.isLt
    linarith
  have hn1 : (1:ℝ) ≤ (n:ℝ) := le_trans hK1 hKn
  set X : ℝ := (((n:ℝ) - K) * ((n:ℝ)-1))/K with hX
  have hX0 : 0 ≤ X := by
    rw [hX]
    apply div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  rcases le_or_gt (eigVal B k) b with hcase | hcase
  · have : 0 ≤ R * Real.sqrt X := mul_nonneg hR0 (Real.sqrt_nonneg _)
    linarith
  -- the mean of the eigenvalues of `B` is `b`
  have htr : B.trace = (n:ℝ) * b := by
    rw [Matrix.trace]
    have : ∀ i : Fin n, B.diag i = b := fun i => hBd i
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hsumlam : ∑ i, eigVal B i = (n:ℝ)*b := by
    rw [← trace_eq_sum_eigVal hBmem.1, htr]
  have hmean : ∑ i, (eigVal B i - b) = 0 := by
    rw [Finset.sum_sub_distrib, hsumlam, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  -- the variance is at most `n(n-1)ρ²`
  have hentry : ∑ i, ∑ j, (B i j)^2 ≤ (n:ℝ)^2*R^2 - (n:ℝ)*R^2 + (n:ℝ)*b^2 := by
    have hstep : ∀ i : Fin n, ∑ j, (B i j)^2 ≤ (n:ℝ)*R^2 + b^2 - R^2 := by
      intro i
      have hpt : ∀ j : Fin n, (B i j)^2 ≤ R^2 + (if i = j then b^2 - R^2 else 0) := by
        intro j
        by_cases h : i = j
        · subst h
          rw [if_pos rfl, hBd i]
          linarith
        · rw [if_neg h, add_zero]
          have habs : |B i j| ≤ R := abs_le_rho (hBmem.2 i j)
          nlinarith [abs_nonneg (B i j), sq_abs (B i j)]
      calc ∑ j, (B i j)^2 ≤ ∑ j, (R^2 + (if i = j then b^2 - R^2 else 0)) :=
            Finset.sum_le_sum fun j _ => hpt j
        _ = (n:ℝ)*R^2 + b^2 - R^2 := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, Finset.sum_ite_eq Finset.univ i (fun _ => b^2 - R^2),
              if_pos (Finset.mem_univ i)]
            ring
    calc ∑ i, ∑ j, (B i j)^2 ≤ ∑ _i : Fin n, ((n:ℝ)*R^2 + b^2 - R^2) :=
          Finset.sum_le_sum fun i _ => hstep i
      _ = (n:ℝ)^2*R^2 - (n:ℝ)*R^2 + (n:ℝ)*b^2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hVexp : ∑ i, (eigVal B i - b)^2
      = (∑ i, (eigVal B i)^2) - 2*b*(∑ i, eigVal B i) + (n:ℝ)*b^2 := by
    have hpt : ∀ i : Fin n, (eigVal B i - b)^2
        = (eigVal B i)^2 - 2*b*(eigVal B i) + b^2 := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hV : ∑ i, (eigVal B i - b)^2 ≤ ((n:ℝ)^2 - (n:ℝ))*R^2 := by
    rw [hVexp, ← sum_sq_entries_eq_sum_sq_eigVal hBmem.1, hsumlam]
    nlinarith [hentry]
  -- the order-statistic bound
  have hos := order_stat_upper (eigVal B) (eigVal_antitone B) k b hmean hcase.le
  have hKpos : (0:ℝ) < K := by linarith
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hnK0 : (0:ℝ) ≤ (n:ℝ) - K := by linarith
  have hsq : (eigVal B k - b)^2 ≤ R^2 * X := by
    have h1 : K * (n:ℝ) * (eigVal B k - b)^2 ≤ ((n:ℝ) - K) * (((n:ℝ)^2 - (n:ℝ))*R^2) := by
      calc K * (n:ℝ) * (eigVal B k - b)^2
          ≤ ((n:ℝ) - K) * ∑ i, (eigVal B i - b)^2 := hos
        _ ≤ ((n:ℝ) - K) * (((n:ℝ)^2 - (n:ℝ))*R^2) := by
            exact mul_le_mul_of_nonneg_left hV hnK0
    have h2 : R^2 * X = (((n:ℝ) - K) * ((n:ℝ)-1) * R^2)/K := by
      rw [hX]; field_simp
    rw [h2, le_div_iff₀ hKpos]
    nlinarith [h1]
  have hle : eigVal B k - b ≤ R * Real.sqrt X := by
    have h1 : Real.sqrt ((eigVal B k - b)^2) ≤ Real.sqrt (R^2 * X) := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (by linarith), Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR0] at h1
    exact h1
  linarith

/-- **Formula (2.15)**: an explicit lower bound for every ordered eigenvalue. -/
theorem variance_bound_le_eigVal {n : ℕ} {a b : ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ SymIcc n a b) (hab : a ≤ b) (k : Fin n) :
    a - rho a b * Real.sqrt ((((k:ℕ):ℝ) * ((n:ℝ)-1))/((n:ℝ) - ((k:ℕ):ℝ))) ≤ eigVal A k := by
  have hAn : -A ∈ SymIcc n (-b) (-a) := neg_mem_SymIcc hA
  have hbound := eigVal_le_variance_bound hAn (by linarith) (Fin.rev k)
  have hneg : eigVal (-A) (Fin.rev k) = - eigVal A k := by
    rw [eigVal_neg hA.1, Fin.rev_rev]
  have hrev : ((Fin.rev k : Fin n) : ℕ) = n - 1 - (k:ℕ) := by
    simp [Fin.val_rev]; omega
  have hkn : (k:ℕ) < n := k.isLt
  have hrho : rho (-b) (-a) = rho a b := by
    rw [rho, rho, abs_neg, abs_neg, max_comm]
  have hcast : ((((Fin.rev k : Fin n)):ℕ):ℝ) = (n:ℝ) - 1 - ((k:ℕ):ℝ) := by
    rw [hrev]
    have h1 : (1:ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub, h1, (by omega : (k:ℕ) ≤ n - 1)]
    ring
  rw [hneg, hrho, hcast] at hbound
  have harg : ((n:ℝ) - (((n:ℝ) - 1 - ((k:ℕ):ℝ))+1)) * ((n:ℝ)-1)/(((n:ℝ) - 1 - ((k:ℕ):ℝ))+1)
      = (((k:ℕ):ℝ) * ((n:ℝ)-1))/((n:ℝ) - ((k:ℕ):ℝ)) := by
    congr 1
    · ring
    · ring
  rw [harg] at hbound
  linarith


/-! ### The trace pairing and the entrywise optimization identity -/

/-- The trace pairing `⟨A,X⟩ = tr(AX)`, written entrywise. -/
def traceForm (A X : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, A i j * X i j

/-- `1ᵀ X 1`, the sum of all entries. -/
def oneQuad (X : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, X i j

/-- The entrywise `1`-norm `|X|_{1,e}`. -/
def entryAbs (X : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, |X i j|

lemma entryAbs_nonneg (X : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ entryAbs X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma traceForm_eq_trace_mul {A X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) :
    traceForm A X = (A * X).trace := by
  rw [Matrix.trace]
  refine (Finset.sum_congr rfl fun i _ => ?_).symm
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsym : X j i = X i j := by
    have := congrFun (congrFun hX i) j
    simpa [Matrix.conjTranspose_apply] using this
  rw [hsym]

lemma oneQuad_eq_quad (X : Matrix (Fin n) (Fin n) ℝ) :
    oneQuad X = (fun _ => (1:ℝ)) ⬝ᵥ X *ᵥ (fun _ => (1:ℝ)) := by
  rw [quad_form]
  simp [oneQuad]

/-- The pointwise bound behind the entrywise optimization identity. -/
lemma entry_le {a b t x : ℝ} (ht : t ∈ Set.Icc a b) :
    t * x ≤ (a+b)/2 * x + (b-a)/2 * |x| := by
  rcases Set.mem_Icc.1 ht with ⟨h1, h2⟩
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]; nlinarith
  · rw [abs_of_neg hx]; nlinarith

lemma le_entry {a b t x : ℝ} (ht : t ∈ Set.Icc a b) :
    (a+b)/2 * x - (b-a)/2 * |x| ≤ t * x := by
  rcases Set.mem_Icc.1 ht with ⟨h1, h2⟩
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]; nlinarith
  · rw [abs_of_neg hx]; nlinarith

lemma traceForm_le {n : ℕ} {a b : ℝ} {A X : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ SymIcc n a b) :
    traceForm A X ≤ (a+b)/2 * oneQuad X + (b-a)/2 * entryAbs X := by
  have hstep : traceForm A X ≤ ∑ i, ∑ j, ((a+b)/2 * X i j + (b-a)/2 * |X i j|) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => entry_le (hA.2 i j)
  refine le_trans hstep (le_of_eq ?_)
  rw [oneQuad, entryAbs, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

lemma le_traceForm {n : ℕ} {a b : ℝ} {A X : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ SymIcc n a b) :
    (a+b)/2 * oneQuad X - (b-a)/2 * entryAbs X ≤ traceForm A X := by
  have hstep : ∑ i, ∑ j, ((a+b)/2 * X i j - (b-a)/2 * |X i j|) ≤ traceForm A X :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => le_entry (hA.2 i j)
  refine le_trans (le_of_eq ?_) hstep
  rw [oneQuad, entryAbs, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- The optimal sign matrix for `X`. -/
noncomputable def signOf (X : Matrix (Fin n) (Fin n) ℝ) (a b : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if 0 ≤ X i j then b else a

lemma signOf_mem {n : ℕ} {a b : ℝ} (hab : a ≤ b) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.IsHermitian) : signOf X a b ∈ SymIcc n a b := by
  have hsym : ∀ i j, X j i = X i j := by
    intro i j
    have := congrFun (congrFun hX i) j
    simpa [Matrix.conjTranspose_apply] using this
  refine ⟨?_, fun i j => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, signOf, Matrix.of_apply, star_trivial, hsym i j]
  · simp only [signOf, Matrix.of_apply]
    split
    · exact ⟨hab, le_rfl⟩
    · exact ⟨le_rfl, hab⟩

lemma traceForm_signOf {n : ℕ} {a b : ℝ} (X : Matrix (Fin n) (Fin n) ℝ) :
    traceForm (signOf X a b) X = (a+b)/2 * oneQuad X + (b-a)/2 * entryAbs X := by
  rw [traceForm, oneQuad, entryAbs, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [signOf, Matrix.of_apply]
  by_cases h : 0 ≤ X i j
  · rw [if_pos h, abs_of_nonneg h]; ring
  · rw [if_neg h, abs_of_neg (not_le.1 h)]; ring

/-- **The entrywise optimization identity**: the maximum of `tr(AX)` over `S_n([a,b])`. -/
theorem isGreatest_traceForm {n : ℕ} {a b : ℝ} (hab : a ≤ b) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.IsHermitian) :
    IsGreatest ((fun A => traceForm A X) '' SymIcc n a b)
      ((a+b)/2 * oneQuad X + (b-a)/2 * entryAbs X) := by
  refine ⟨⟨signOf X a b, signOf_mem hab hX, traceForm_signOf X⟩, ?_⟩
  rintro t ⟨A, hA, rfl⟩
  exact traceForm_le hA

/-- **The entrywise optimization identity**: the minimum of `tr(AX)` over `S_n([a,b])`. -/
theorem isLeast_traceForm {n : ℕ} {a b : ℝ} (hab : a ≤ b) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.IsHermitian) :
    IsLeast ((fun A => traceForm A X) '' SymIcc n a b)
      ((a+b)/2 * oneQuad X - (b-a)/2 * entryAbs X) := by
  refine ⟨⟨signOf (-X) a b, signOf_mem hab hX.neg, ?_⟩, ?_⟩
  · have h1 : traceForm (signOf (-X) a b) (-X)
        = (a+b)/2 * oneQuad (-X) + (b-a)/2 * entryAbs (-X) := traceForm_signOf (-X)
    have h2 : traceForm (signOf (-X) a b) (-X) = - traceForm (signOf (-X) a b) X := by
      rw [traceForm, traceForm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp [Matrix.neg_apply]
    have h3 : oneQuad (-X) = - oneQuad X := by
      rw [oneQuad, oneQuad, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp [Matrix.neg_apply]
    have h4 : entryAbs (-X) = entryAbs X := by
      rw [entryAbs, entryAbs]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      simp [Matrix.neg_apply]
    rw [h2, h3, h4] at h1
    linarith
  · rintro t ⟨A, hA, rfl⟩
    exact le_traceForm hA

/-! ### Spectral projections and the projection bounds (2.16), (2.17) -/

lemma trace_of_conj {W : Matrix (Fin n) (Fin n) ℝ} (h1 : Wᵀ * W = 1) (d : Fin n → ℝ) :
    (W * diagonal d * Wᵀ).trace = ∑ i, d i := by
  rw [Matrix.trace_mul_comm (W * diagonal d) Wᵀ, ← Matrix.mul_assoc, h1, Matrix.one_mul,
    Matrix.trace_diagonal]

lemma conj_mul_conj {W : Matrix (Fin n) (Fin n) ℝ} (h1 : Wᵀ * W = 1) (d e : Fin n → ℝ) :
    (W * diagonal d * Wᵀ) * (W * diagonal e * Wᵀ)
      = W * diagonal (fun i => d i * e i) * Wᵀ := by
  rw [show W * diagonal d * Wᵀ * (W * diagonal e * Wᵀ)
      = W * diagonal d * (Wᵀ * W) * (diagonal e * Wᵀ) by simp [Matrix.mul_assoc], h1,
    Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_assoc W (diagonal d) (diagonal e),
    Matrix.diagonal_mul_diagonal]

lemma conj_entry (W : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (i j : Fin n) :
    (W * diagonal d * Wᵀ) i j = ∑ l, W i l * d l * W j l := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply,
    Finset.sum_ite_eq', mul_comm]

lemma conj_isHermitian (W : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    (W * diagonal d * Wᵀ).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply, star_trivial, conj_entry, conj_entry]
  exact Finset.sum_congr rfl fun l _ => by ring

lemma sum_sq_entries_eq_trace_sq {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) :
    ∑ i, ∑ j, (M i j)^2 = (M * M).trace := by
  rw [Matrix.trace]
  refine (Finset.sum_congr rfl fun i _ => ?_).symm
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsym : M j i = M i j := by
    have := congrFun (congrFun hM i) j
    simpa [Matrix.conjTranspose_apply] using this
  rw [hsym, sq]

/-- The orthogonal projection onto the span of the columns of `W` indexed by `s`. -/
noncomputable def specProj (W : Matrix (Fin n) (Fin n) ℝ) (s : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  W * diagonal (fun l => if l ∈ s then (1:ℝ) else 0) * Wᵀ

lemma specProj_isHermitian (W : Matrix (Fin n) (Fin n) ℝ) (s : Finset (Fin n)) :
    (specProj W s).IsHermitian := conj_isHermitian _ _

lemma sum_ite_mem_mul {s : Finset (Fin n)} (y : Fin n → ℝ) :
    ∑ l, (if l ∈ s then (1:ℝ) else 0) * y l = ∑ l ∈ s, y l := by
  classical
  rw [Finset.sum_congr rfl (fun l _ => show (if l ∈ s then (1:ℝ) else 0) * y l
      = if l ∈ s then y l else 0 by split <;> ring)]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma sum_sq_specProj {W : Matrix (Fin n) (Fin n) ℝ} (h1 : Wᵀ * W = 1) (s : Finset (Fin n)) :
    ∑ i, ∑ j, ((specProj W s) i j)^2 = (s.card : ℝ) := by
  classical
  rw [sum_sq_entries_eq_trace_sq (specProj_isHermitian W s), specProj,
    conj_mul_conj h1, trace_of_conj h1]
  rw [Finset.sum_congr rfl (fun l _ => show
      (if l ∈ s then (1:ℝ) else 0) * (if l ∈ s then (1:ℝ) else 0)
        = if l ∈ s then (1:ℝ) else 0 by split <;> ring)]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma traceForm_specProj {A W : Matrix (Fin n) (Fin n) ℝ} (h1 : Wᵀ * W = 1)
    (h3 : A = W * diagonal (eigVal A) * Wᵀ) (s : Finset (Fin n)) :
    traceForm A (specProj W s) = ∑ l ∈ s, eigVal A l := by
  classical
  rw [traceForm_eq_trace_mul (specProj_isHermitian W s), specProj]
  conv_lhs => rw [h3]
  rw [conj_mul_conj h1, trace_of_conj h1,
    Finset.sum_congr rfl (fun l _ => show eigVal A l * (if l ∈ s then (1:ℝ) else 0)
      = if l ∈ s then eigVal A l else 0 by split <;> ring),
    Finset.sum_ite_mem, Finset.univ_inter]

lemma oneQuad_specProj_bounds {W : Matrix (Fin n) (Fin n) ℝ} (h2 : W * Wᵀ = 1)
    (s : Finset (Fin n)) :
    0 ≤ oneQuad (specProj W s) ∧ oneQuad (specProj W s) ≤ (n:ℝ) := by
  classical
  set one : Fin n → ℝ := fun _ => (1:ℝ) with hone
  have hq : oneQuad (specProj W s)
      = ∑ l, (if l ∈ s then (1:ℝ) else 0) * ((Wᵀ *ᵥ one) l)^2 := by
    rw [oneQuad_eq_quad, quad_of_diag _ (rfl : specProj W s = _) one]
  have hq2 : oneQuad (specProj W s) = ∑ l ∈ s, ((Wᵀ *ᵥ one) l)^2 := by
    rw [hq, sum_ite_mem_mul]
  have hall : ∑ l, ((Wᵀ *ᵥ one) l)^2 = (n:ℝ) := by
    rw [← norm_of_orth h2 one]
    simp [hone, dotProduct]
  constructor
  · rw [hq2]; exact Finset.sum_nonneg fun l _ => sq_nonneg _
  · rw [hq2, ← hall]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      fun l _ _ => sq_nonneg _

lemma entryAbs_le_of_sum_sq {M : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (h : ∑ i, ∑ j, (M i j)^2 = c) : entryAbs M ≤ (n:ℝ) * Real.sqrt c := by
  classical
  have hprod : entryAbs M = ∑ p : Fin n × Fin n, |M p.1 p.2| := by
    rw [entryAbs, Fintype.sum_prod_type]
  have hprod2 : ∑ p : Fin n × Fin n, |M p.1 p.2|^2 = c := by
    rw [Fintype.sum_prod_type, ← h]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => sq_abs _
  have hCS : (∑ p : Fin n × Fin n, |M p.1 p.2|)^2
      ≤ ((Finset.univ : Finset (Fin n × Fin n)).card : ℝ) * ∑ p : Fin n × Fin n, |M p.1 p.2|^2 :=
    sq_sum_le_card_mul_sum_sq
  rw [hprod2, Finset.card_univ] at hCS
  have hcard : ((Fintype.card (Fin n × Fin n) : ℕ) : ℝ) = (n:ℝ)^2 := by
    simp [Fintype.card_prod]; ring
  rw [hcard] at hCS
  rw [hprod]
  have h1 : Real.sqrt ((∑ p : Fin n × Fin n, |M p.1 p.2|)^2)
      ≤ Real.sqrt ((n:ℝ)^2 * c) := Real.sqrt_le_sqrt hCS
  rw [Real.sqrt_sq (Finset.sum_nonneg fun p _ => abs_nonneg _),
    Real.sqrt_mul (sq_nonneg (n:ℝ)), Real.sqrt_sq (Nat.cast_nonneg n)] at h1
  exact h1

/-- **Formula (2.16)**: the projection upper bound. -/
theorem eigVal_le_proj_bound {n : ℕ} {a b : ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ SymIcc n a b) (hab : a ≤ b) (k : Fin n) :
    eigVal A k ≤ ((n:ℝ)/(((k:ℕ):ℝ)+1)) *
      (max ((a+b)/2) 0 + ((b-a)/2) * Real.sqrt (((k:ℕ):ℝ)+1)) := by
  classical
  obtain ⟨W, h1, h2, h3⟩ := spectral_diag hA.1
  set s : Finset (Fin n) := Finset.Iic k with hs
  have hcard : s.card = (k:ℕ) + 1 := by rw [hs, Fin.card_Iic]
  set K : ℝ := ((k:ℕ):ℝ) + 1 with hK
  have hKpos : (0:ℝ) < K := by rw [hK]; positivity
  have hKcard : ((s.card : ℕ) : ℝ) = K := by rw [hcard, hK]; push_cast; ring
  set P := specProj W s with hP
  have hkey1 : K * eigVal A k ≤ ∑ l ∈ s, eigVal A l := by
    calc K * eigVal A k = ∑ _l ∈ s, eigVal A k := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul, hK]; push_cast; ring
      _ ≤ ∑ l ∈ s, eigVal A l :=
          Finset.sum_le_sum fun l hl => eigVal_antitone A (Finset.mem_Iic.1 (hs ▸ hl))
  have hkey2 : ∑ l ∈ s, eigVal A l = traceForm A P := (traceForm_specProj h1 h3 s).symm
  have hkey3 : traceForm A P ≤ (a+b)/2 * oneQuad P + (b-a)/2 * entryAbs P := traceForm_le hA
  obtain ⟨hq0, hqn⟩ := oneQuad_specProj_bounds h2 s
  have hkey4 : (a+b)/2 * oneQuad P ≤ max ((a+b)/2) 0 * (n:ℝ) := by
    rcases le_or_gt 0 ((a+b)/2) with hc | hc
    · have : max ((a+b)/2) 0 = (a+b)/2 := max_eq_left hc
      rw [this]
      exact mul_le_mul_of_nonneg_left hqn hc
    · have : max ((a+b)/2) 0 = 0 := max_eq_right hc.le
      rw [this, zero_mul]
      nlinarith
  have hsumsq : ∑ i, ∑ j, (P i j)^2 = K := by
    rw [hP, sum_sq_specProj h1 s, hKcard]
  have hkey5 : entryAbs P ≤ (n:ℝ) * Real.sqrt K := entryAbs_le_of_sum_sq hsumsq
  have hr0 : (0:ℝ) ≤ (b-a)/2 := by linarith
  have hfinal : K * eigVal A k ≤ (n:ℝ) * (max ((a+b)/2) 0 + (b-a)/2 * Real.sqrt K) := by
    have h5 : (b-a)/2 * entryAbs P ≤ (b-a)/2 * ((n:ℝ) * Real.sqrt K) :=
      mul_le_mul_of_nonneg_left hkey5 hr0
    calc K * eigVal A k ≤ ∑ l ∈ s, eigVal A l := hkey1
      _ = traceForm A P := hkey2
      _ ≤ (a+b)/2 * oneQuad P + (b-a)/2 * entryAbs P := hkey3
      _ ≤ max ((a+b)/2) 0 * (n:ℝ) + (b-a)/2 * ((n:ℝ) * Real.sqrt K) := by linarith
      _ = (n:ℝ) * (max ((a+b)/2) 0 + (b-a)/2 * Real.sqrt K) := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hKpos]
  linarith

/-- **Formula (2.17)**: the projection lower bound. -/
theorem proj_bound_le_eigVal {n : ℕ} {a b : ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ SymIcc n a b) (hab : a ≤ b) (k : Fin n) :
    ((n:ℝ)/((n:ℝ) - ((k:ℕ):ℝ))) *
        (min ((a+b)/2) 0 - ((b-a)/2) * Real.sqrt ((n:ℝ) - ((k:ℕ):ℝ)))
      ≤ eigVal A k := by
  have hAn : -A ∈ SymIcc n (-b) (-a) := neg_mem_SymIcc hA
  have hbound := eigVal_le_proj_bound hAn (by linarith) (Fin.rev k)
  have hneg : eigVal (-A) (Fin.rev k) = - eigVal A k := by
    rw [eigVal_neg hA.1, Fin.rev_rev]
  have hrev : ((Fin.rev k : Fin n) : ℕ) = n - 1 - (k:ℕ) := by
    simp [Fin.val_rev]; omega
  have hkn : (k:ℕ) < n := k.isLt
  have hcast : ((((Fin.rev k : Fin n)):ℕ):ℝ) + 1 = (n:ℝ) - ((k:ℕ):ℝ) := by
    rw [hrev]
    have h1 : (1:ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub, h1, (by omega : (k:ℕ) ≤ n - 1)]
    ring
  rw [hneg, hcast, show ((-b) + (-a))/2 = -((a+b)/2) by ring,
    show ((-a) - (-b))/2 = (b-a)/2 by ring] at hbound
  have hmin : -max (-((a+b)/2)) 0 = min ((a+b)/2) 0 := by
    rcases le_or_gt 0 ((a+b)/2) with hc | hc
    · rw [max_eq_right (by linarith), min_eq_right hc, neg_zero]
    · rw [max_eq_left (by linarith), min_eq_left hc.le, neg_neg]
  have hkey : -eigVal A k ≤ ((n:ℝ)/((n:ℝ) - ((k:ℕ):ℝ))) *
      (max (-((a+b)/2)) 0 + ((b-a)/2) * Real.sqrt ((n:ℝ) - ((k:ℕ):ℝ))) := hbound
  have hexp : ((n:ℝ)/((n:ℝ) - ((k:ℕ):ℝ))) *
      (min ((a+b)/2) 0 - ((b-a)/2) * Real.sqrt ((n:ℝ) - ((k:ℕ):ℝ)))
      = - (((n:ℝ)/((n:ℝ) - ((k:ℕ):ℝ))) *
          (max (-((a+b)/2)) 0 + ((b-a)/2) * Real.sqrt ((n:ℝ) - ((k:ℕ):ℝ)))) := by
    rw [← hmin]; ring
  rw [hexp]
  linarith

/-! ### Density matrices supported on a subspace -/

/-- `DensityOn V` is the set of density matrices supported on the subspace `V`: symmetric,
positive semidefinite, of trace one, with range contained in `V`. -/
def DensityOn (V : Submodule ℝ (Fin n → ℝ)) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | X.IsHermitian ∧ (∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ X *ᵥ x) ∧ X.trace = 1 ∧
    ∀ y : Fin n → ℝ, X *ᵥ y ∈ V}

/-- The objective function `c 1ᵀX1 + r |X|_{1,e}` of the minimax formula. -/
noncomputable def densityObj (a b : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (a+b)/2 * oneQuad X + (b-a)/2 * entryAbs X

lemma traceForm_vecMulVec (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    traceForm A (Matrix.vecMulVec x x) = x ⬝ᵥ A *ᵥ x := by
  rw [quad_form, traceForm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.vecMulVec_apply]
  ring

lemma vecMulVec_isHermitian (x : Fin n → ℝ) : (Matrix.vecMulVec x x).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]

lemma vecMulVec_mulVec (x y : Fin n → ℝ) :
    (Matrix.vecMulVec x x) *ᵥ y = (x ⬝ᵥ y) • x := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.mul_sum, mul_comm,
    mul_left_comm]

lemma vecMulVec_mem_DensityOn {V : Submodule ℝ (Fin n → ℝ)} {x : Fin n → ℝ}
    (hx : x ∈ V) (hx1 : x ⬝ᵥ x = 1) : Matrix.vecMulVec x x ∈ DensityOn V := by
  refine ⟨vecMulVec_isHermitian x, fun y => ?_, ?_, fun y => ?_⟩
  · have h : y ⬝ᵥ (Matrix.vecMulVec x x) *ᵥ y = (x ⬝ᵥ y)^2 := by
      rw [vecMulVec_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_comm y x, sq]
    rw [h]; positivity
  · rw [Matrix.trace]
    simpa [Matrix.diag_apply, Matrix.vecMulVec_apply, dotProduct] using hx1
  · rw [vecMulVec_mulVec]
    exact V.smul_mem _ hx

/-- A subspace of positive dimension contains a unit vector, hence a density matrix. -/
lemma exists_unit_mem {V : Submodule ℝ (Fin n → ℝ)} (hV : 0 < Module.finrank ℝ V) :
    ∃ x : Fin n → ℝ, x ∈ V ∧ x ⬝ᵥ x = 1 := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos hV
  obtain ⟨⟨y, hyV⟩, hy0⟩ := exists_ne (0 : V)
  have hy : y ≠ 0 := by simpa using hy0
  have hpos : 0 < y ⬝ᵥ y := by
    rw [dotProduct_self]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
    exact Finset.sum_pos' (fun j _ => sq_nonneg _)
      ⟨i, Finset.mem_univ i, pow_pos (abs_pos.2 hi) 2 |>.trans_le (le_of_eq (sq_abs _))⟩
  refine ⟨(1/Real.sqrt (y ⬝ᵥ y)) • y, V.smul_mem _ hyV, ?_⟩
  rw [dot_smul]
  rw [div_pow, one_pow, Real.sq_sqrt hpos.le]
  field_simp

lemma DensityOn_nonempty {V : Submodule ℝ (Fin n → ℝ)} (hV : 0 < Module.finrank ℝ V) :
    (DensityOn V).Nonempty := by
  obtain ⟨x, hxV, hx1⟩ := exists_unit_mem hV
  exact ⟨_, vecMulVec_mem_DensityOn hxV hx1⟩

lemma DensityOn_convex {V : Submodule ℝ (Fin n → ℝ)} {X Y : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ DensityOn V) (hY : Y ∈ DensityOn V) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (1-θ) • X + θ • Y ∈ DensityOn V := by
  obtain ⟨hX1, hX2, hX3, hX4⟩ := hX
  obtain ⟨hY1, hY2, hY3, hY4⟩ := hY
  refine ⟨herm_smul_add hX1 hY1 _ _, fun x => ?_, ?_, fun y => ?_⟩
  · rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.smul_mulVec,
      dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have := hX2 x
    have := hY2 x
    nlinarith
  · rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hX3, hY3, smul_eq_mul,
      smul_eq_mul]
    ring
  · rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
    exact V.add_mem (V.smul_mem _ (hX4 y)) (V.smul_mem _ (hY4 y))

/-! ### Exact dimension of coordinate kernels and the lower Courant--Fischer subspace -/

lemma finrank_coordKer_eq (s : Finset (Fin n)) :
    Module.finrank ℝ (coordKer s) = n - s.card := by
  classical
  set f := LinearMap.pi
    (fun j : s => LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (j : Fin n)) with hf
  have hsurj : Function.Surjective f := by
    intro w
    refine ⟨fun i => if h : i ∈ s then w ⟨i, h⟩ else 0, ?_⟩
    funext j
    simp [hf, LinearMap.pi_apply, LinearMap.proj_apply, j.2]
  have h := LinearMap.finrank_range_add_finrank_ker f
  have hr : Module.finrank ℝ ↥(LinearMap.range f) = s.card := by
    rw [LinearMap.range_eq_top.2 hsurj]
    simp
  rw [hr] at h
  simp only [Module.finrank_pi, Fintype.card_fin] at h
  have hcard : s.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ s)
  show Module.finrank ℝ ↥(LinearMap.ker f) = n - s.card
  omega

/-- There is a subspace of dimension exactly `k+1` on which the quadratic form of `A`
is at least `λ_{k+1}(A)`. -/
theorem exists_subspace_ge {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (k : Fin n) :
    ∃ V : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ V = (k : ℕ) + 1 ∧
      ∀ x ∈ V, eigVal A k * (x ⬝ᵥ x) ≤ x ⬝ᵥ A *ᵥ x := by
  classical
  obtain ⟨W, hWt, hWt', hnorm, hquad⟩ := spectral_coords hA
  set eW : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    LinearEquiv.ofLinear (Matrix.mulVecLin W) (Matrix.mulVecLin Wᵀ)
      (by rw [← Matrix.mulVecLin_mul, hWt', Matrix.mulVecLin_one])
      (by rw [← Matrix.mulVecLin_mul, hWt, Matrix.mulVecLin_one]) with heW
  refine ⟨(coordKer (Finset.Ioi k)).map (eW : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)), ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq eW, finrank_coordKer_eq, Fin.card_Ioi]
    have := k.isLt
    omega
  · rintro x ⟨c, hc, rfl⟩
    have hWc : Wᵀ *ᵥ ((eW : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) c) = c := by
      show Wᵀ *ᵥ (W *ᵥ c) = c
      rw [Matrix.mulVec_mulVec, hWt, Matrix.one_mulVec]
    set x := (eW : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) c
    rw [hquad x, hnorm x, hWc, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hik : k < i
    · rw [(mem_coordKer.1 hc) i (Finset.mem_Ioi.2 hik)]; simp
    · have : eigVal A k ≤ eigVal A i := eigVal_antitone A (not_lt.1 hik)
      nlinarith [sq_nonneg (c i)]

/-! ### Entrywise bounds for density matrices -/

/-- The standard basis vector, as a function `Fin n → ℝ`. -/
def stdVec (i : Fin n) : Fin n → ℝ := Pi.single i 1

lemma stdVec_apply (i j : Fin n) : stdVec i j = if j = i then (1:ℝ) else 0 := by
  simp [stdVec, Pi.single_apply]

lemma quad_single_add (X : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (u v : ℝ) :
    (u • stdVec i + v • stdVec j) ⬝ᵥ X *ᵥ (u • stdVec i + v • stdVec j)
      = u^2 * X i i + u*v*(X i j) + u*v*(X j i) + v^2 * X j j := by
  simp [stdVec, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
    smul_dotProduct, Matrix.mulVec_single, single_dotProduct]
  ring

lemma density_isHermitian {V : Submodule ℝ (Fin n → ℝ)} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ DensityOn V) (i j : Fin n) : X j i = X i j := by
  have := congrFun (congrFun hX.1 i) j
  simpa [Matrix.conjTranspose_apply] using this

lemma density_entry_bound {V : Submodule ℝ (Fin n → ℝ)} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ DensityOn V) (i j : Fin n) : |X i j| ≤ (X i i + X j j)/2 := by
  have hsym := density_isHermitian hX i j
  have h1 := hX.2.1 ((1:ℝ) • stdVec i + (1:ℝ) • stdVec j)
  have h2 := hX.2.1 ((1:ℝ) • stdVec i + (-1:ℝ) • stdVec j)
  rw [quad_single_add] at h1 h2
  rw [hsym] at h1 h2
  rw [abs_le]
  constructor <;> nlinarith

lemma density_diag_nonneg {V : Submodule ℝ (Fin n → ℝ)} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ DensityOn V) (i : Fin n) : 0 ≤ X i i := by
  have h := hX.2.1 (stdVec i)
  simpa [stdVec, Matrix.mulVec_single, single_dotProduct] using h

lemma density_diag_le_one {V : Submodule ℝ (Fin n → ℝ)} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ DensityOn V) (i : Fin n) : X i i ≤ 1 := by
  have htr : ∑ l, X l l = 1 := by
    have := hX.2.2.1
    simpa [Matrix.trace, Matrix.diag_apply] using this
  have : X i i ≤ ∑ l, X l l :=
    Finset.single_le_sum (f := fun l => X l l)
      (fun l _ => density_diag_nonneg hX l) (Finset.mem_univ i)
  linarith [htr ▸ this]

lemma density_entry_le_one {V : Submodule ℝ (Fin n → ℝ)} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ DensityOn V) (i j : Fin n) : |X i j| ≤ 1 := by
  have h := density_entry_bound hX i j
  have h1 := density_diag_le_one hX i
  have h2 := density_diag_le_one hX j
  linarith

/-! ### Convexification: the quadratic form bound transfers to density matrices -/

lemma le_traceForm_of_density {V : Submodule ℝ (Fin n → ℝ)} {A X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ DensityOn V) {lam : ℝ}
    (hV : ∀ y ∈ V, lam * (y ⬝ᵥ y) ≤ y ⬝ᵥ A *ᵥ y) :
    lam ≤ traceForm A X := by
  classical
  obtain ⟨hH, hpsd, htr, hran⟩ := hX
  obtain ⟨W, h1, h2, h3⟩ := spectral_diag hH
  set mu : Fin n → ℝ := eigVal X with hmu
  set u : Fin n → (Fin n → ℝ) := fun l i => W i l with hu
  -- coordinates of the columns
  have hcol : ∀ l, Wᵀ *ᵥ (u l) = stdVec l := by
    intro l
    funext m
    have : (Wᵀ *ᵥ (u l)) m = (Wᵀ * W) m l := by
      simp [Matrix.mulVec, Matrix.mul_apply, dotProduct, hu, Matrix.transpose_apply]
    rw [this, h1]
    by_cases hml : m = l
    · subst hml; simp [stdVec]
    · simp [stdVec_apply, hml]
  have hnorm1 : ∀ l, (u l) ⬝ᵥ (u l) = 1 := by
    intro l
    rw [norm_of_orth h2, hcol l]
    simp [stdVec_apply]
  have hmulVec : ∀ l, X *ᵥ (u l) = mu l • (u l) := by
    intro l
    conv_lhs => rw [h3]
    rw [show W * diagonal mu * Wᵀ = W * (diagonal mu * Wᵀ) by rw [Matrix.mul_assoc]]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol l]
    have hd : diagonal mu *ᵥ (stdVec l) = mu l • stdVec l := by
      funext m
      by_cases hml : m = l
      · subst hml; simp [Matrix.mulVec_diagonal, stdVec]
      · simp [Matrix.mulVec_diagonal, stdVec_apply, hml]
    rw [hd, Matrix.mulVec_smul]
    congr 1
    funext i
    simp [hu, Matrix.mulVec, dotProduct, stdVec_apply]
  have hmem : ∀ l, mu l ≠ 0 → u l ∈ V := by
    intro l hl
    have hmv : mu l • (u l) ∈ V := by rw [← hmulVec l]; exact hran (u l)
    have := V.smul_mem (mu l)⁻¹ hmv
    rwa [smul_smul, inv_mul_cancel₀ hl, one_smul] at this
  have hmunn : ∀ l, 0 ≤ mu l := fun l =>
    le_eigVal_of_forall hH l 0 (fun x => by simpa using hpsd x)
  have hsum : ∑ l, mu l = 1 := by rw [← trace_eq_sum_eigVal hH, htr]
  -- decompose the trace pairing
  have hTF : traceForm A X = ∑ l, mu l * ((u l) ⬝ᵥ A *ᵥ (u l)) := by
    have hent : ∀ i j, X i j = ∑ l, W i l * mu l * W j l := by
      intro i j
      conv_lhs => rw [h3]
      exact conj_entry W mu i j
    have e1 : traceForm A X
        = ∑ i, ∑ j, ∑ l, mu l * (A i j * W i l * W j l) := by
      rw [traceForm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hent i j, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have e2 : ∀ i : Fin n, ∑ j, ∑ l, mu l * (A i j * W i l * W j l)
        = ∑ l, ∑ j, mu l * (A i j * W i l * W j l) := fun i => Finset.sum_comm
    rw [e1, Finset.sum_congr rfl (fun i _ => e2 i), Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [quad_form, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hterm : ∀ l, mu l * lam ≤ mu l * ((u l) ⬝ᵥ A *ᵥ (u l)) := by
    intro l
    rcases eq_or_lt_of_le (hmunn l) with h | h
    · rw [← h]; simp
    · have hml : mu l ≠ 0 := ne_of_gt h
      have := hV (u l) (hmem l hml)
      rw [hnorm1 l, mul_one] at this
      exact mul_le_mul_of_nonneg_left this h.le
  calc lam = (∑ l, mu l) * lam := by rw [hsum, one_mul]
    _ = ∑ l, mu l * lam := by rw [Finset.sum_mul]
    _ ≤ ∑ l, mu l * ((u l) ⬝ᵥ A *ᵥ (u l)) := Finset.sum_le_sum fun l _ => hterm l
    _ = traceForm A X := hTF.symm


/-! ### Linearity of the trace pairing, and boundedness of the density objective -/

lemma traceForm_add (A X Y : Matrix (Fin n) (Fin n) ℝ) :
    traceForm A (X + Y) = traceForm A X + traceForm A Y := by
  simp only [traceForm, Matrix.add_apply, mul_add]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib

lemma traceForm_smul (c : ℝ) (A X : Matrix (Fin n) (Fin n) ℝ) :
    traceForm A (c • X) = c * traceForm A X := by
  simp only [traceForm, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma traceForm_smul_left (c : ℝ) (A X : Matrix (Fin n) (Fin n) ℝ) :
    traceForm (c • A) X = c * traceForm A X := by
  simp only [traceForm, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma traceForm_sum_left {ι : Type*} (s : Finset ι) (g : ι → Matrix (Fin n) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    traceForm (∑ l ∈ s, g l) X = ∑ l ∈ s, traceForm (g l) X := by
  classical
  induction s using Finset.induction with
  | empty => simp [traceForm]
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, ← ih]
      simp only [traceForm, Matrix.add_apply, add_mul]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib

lemma abs_oneQuad_le_of_density {V : Submodule ℝ (Fin n → ℝ)} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ DensityOn V) : |oneQuad X| ≤ (n:ℝ)^2 := by
  have h : |oneQuad X| ≤ ∑ i, ∑ j, |X i j| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ i, ∑ j : Fin n, |X i j| ≤ ∑ _i : Fin n, ∑ _j : Fin n, (1:ℝ) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => density_entry_le_one hX i j
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h2
  calc |oneQuad X| ≤ ∑ i, ∑ j : Fin n, |X i j| := h
    _ ≤ (n:ℝ) * (n:ℝ) := by simpa using h2
    _ = (n:ℝ)^2 := by ring

lemma entryAbs_le_of_density {V : Submodule ℝ (Fin n → ℝ)} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ DensityOn V) : entryAbs X ≤ (n:ℝ)^2 := by
  have h2 : ∑ i, ∑ j : Fin n, |X i j| ≤ ∑ _i : Fin n, ∑ _j : Fin n, (1:ℝ) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => density_entry_le_one hX i j
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h2
  calc entryAbs X ≤ (n:ℝ) * (n:ℝ) := by simpa [entryAbs] using h2
    _ = (n:ℝ)^2 := by ring

lemma bddBelow_densityObj (a b : ℝ) (V : Submodule ℝ (Fin n → ℝ)) :
    BddBelow (densityObj a b '' DensityOn V) := by
  refine ⟨-(|(a+b)/2| * (n:ℝ)^2 + |(b-a)/2| * (n:ℝ)^2), ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  have h1 : |(a+b)/2 * oneQuad X| ≤ |(a+b)/2| * (n:ℝ)^2 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_oneQuad_le_of_density hX) (abs_nonneg _)
  have h2 : |(b-a)/2 * entryAbs X| ≤ |(b-a)/2| * (n:ℝ)^2 := by
    rw [abs_mul, abs_of_nonneg (entryAbs_nonneg X)]
    exact mul_le_mul_of_nonneg_left (entryAbs_le_of_density hX) (abs_nonneg _)
  have e1 := abs_le.1 h1
  have e2 := abs_le.1 h2
  simp only [densityObj]
  linarith [e1.1, e2.1]

/-! ### (2.10), easy direction -/

/-- For every `A ∈ S_n([a,b])` there is a subspace `V` of dimension `k+1` on which the
density-matrix objective dominates `λ_{k+1}(A)`. -/
theorem exists_density_subspace {n : ℕ} {a b : ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ SymIcc n a b) (k : Fin n) :
    ∃ V : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ V = (k:ℕ) + 1 ∧
      ∀ X ∈ DensityOn V, eigVal A k ≤ densityObj a b X := by
  obtain ⟨V, hV, hq⟩ := exists_subspace_ge hA.1 k
  refine ⟨V, hV, fun X hX => ?_⟩
  have h1 : eigVal A k ≤ traceForm A X := le_traceForm_of_density hX hq
  have h2 : traceForm A X ≤ (a+b)/2 * oneQuad X + (b-a)/2 * entryAbs X := traceForm_le hA
  simpa [densityObj] using h1.trans h2

/-! ### Vertices of `S_n([a,b])` -/

/-- The `{a,b}`-valued symmetric matrix determined by a Boolean pattern.  These are the
extreme points used to linearize the entrywise optimization identity. -/
noncomputable def vertex (a b : ℝ) (s : Fin n → Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if (s i j || s j i) then b else a

lemma vertex_mem {n : ℕ} {a b : ℝ} (hab : a ≤ b) (s : Fin n → Fin n → Bool) :
    vertex a b s ∈ SymIcc n a b := by
  refine ⟨?_, fun i j => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, vertex, Matrix.of_apply]
    rw [Bool.or_comm]
  · simp only [vertex, Matrix.of_apply]
    split
    · exact ⟨hab, le_rfl⟩
    · exact ⟨le_rfl, hab⟩

lemma vertex_signOf {n : ℕ} {a b : ℝ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) :
    vertex a b (fun i j => decide (0 ≤ X i j)) = signOf X a b := by
  classical
  have hsym : ∀ i j, X j i = X i j := by
    intro i j
    have := congrFun (congrFun hX i) j
    simpa [Matrix.conjTranspose_apply] using this
  ext i j
  simp only [vertex, signOf, Matrix.of_apply, hsym i j, Bool.or_self, decide_eq_true_eq]

/-- The density objective is the maximum of the vertex pairings. -/
lemma densityObj_eq_vertex {n : ℕ} {a b : ℝ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.IsHermitian) :
    traceForm (vertex a b (fun i j => decide (0 ≤ X i j))) X = densityObj a b X := by
  rw [vertex_signOf hX, traceForm_signOf, densityObj]

/-! ### Convexity of `DensityOn V` and its vertex image -/

lemma convex_DensityOn (V : Submodule ℝ (Fin n → ℝ)) : Convex ℝ (DensityOn V) := by
  rintro X hX Y hY p q hp hq hpq
  have h : p • X + q • Y = (1 - q) • X + q • Y := by rw [show (1:ℝ) - q = p by linarith]
  rw [h]
  exact DensityOn_convex hX hY hq (by linarith)

/-- The vertex pairing map, as a linear map into a finite-dimensional coordinate space. -/
noncomputable def vertexMap (a b : ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ((Fin n → Fin n → Bool) → ℝ) where
  toFun X := fun s => traceForm (vertex a b s) X
  map_add' X Y := by funext s; exact traceForm_add _ X Y
  map_smul' c X := by funext s; exact traceForm_smul c _ X

lemma vertexMap_apply (a b : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → Fin n → Bool) :
    vertexMap a b X s = traceForm (vertex a b s) X := rfl


lemma eq_zero_of_dotProduct_self_eq_zero {y : Fin n → ℝ} (h : y ⬝ᵥ y = 0) : y = 0 := by
  funext i
  rw [dotProduct_self] at h
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (y j))).1 h i (Finset.mem_univ i)
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

/-! ### (2.10), hard direction: a finite-dimensional separation argument -/

/-- **Minimax, hard direction.**  If the density objective on `𝒟(V)` is bounded below by `t`
and `dim V ≥ k+1`, then some matrix of `S_n([a,b])` has `λ_{k+1} ≥ t`. -/
theorem exists_matrix_ge_density {n : ℕ} {a b : ℝ} (hab : a ≤ b) (k : Fin n)
    (V : Submodule ℝ (Fin n → ℝ)) (hV : (k : ℕ) + 1 ≤ Module.finrank ℝ V) (t : ℝ)
    (ht : ∀ X ∈ DensityOn V, t ≤ densityObj a b X) :
    ∃ A ∈ SymIcc n a b, t ≤ eigVal A k := by
  set K : Set ((Fin n → Fin n → Bool) → ℝ) := (vertexMap a b) '' (DensityOn V) with hKdef
  set U : Set ((Fin n → Fin n → Bool) → ℝ) := {z | ∀ s, z s < t} with hUdef
  have hVpos : 0 < Module.finrank ℝ V := lt_of_lt_of_le (Nat.succ_pos _) hV
  have hDne : (DensityOn V).Nonempty := DensityOn_nonempty hVpos
  have hKconv : Convex ℝ K := (convex_DensityOn V).linear_image _
  have hUconv : Convex ℝ U := by
    intro x hx y hy p q hp hq hpq s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le hp with hp0 | hp0
    · have hq1 : q = 1 := by linarith
      rw [← hp0, hq1]
      simpa using hy s
    · have h1 : p * x s < p * t := by
        exact mul_lt_mul_of_pos_left (hx s) hp0
      have h2 : q * y s ≤ q * t := mul_le_mul_of_nonneg_left (le_of_lt (hy s)) hq
      have h3 : p * t + q * t = t := by rw [← add_mul, hpq, one_mul]
      linarith
  have hUopen : IsOpen U := by
    have hEq : U = ⋂ s : (Fin n → Fin n → Bool),
        (fun z : (Fin n → Fin n → Bool) → ℝ => z s) ⁻¹' (Set.Iio t) := by
      ext z; simp [hUdef]
    rw [hEq]
    exact isOpen_iInter_of_finite fun s => (continuous_apply s).isOpen_preimage _ isOpen_Iio
  have hdisj : Disjoint U K := by
    rw [Set.disjoint_left]
    rintro z hz ⟨X, hX, rfl⟩
    have hmax := densityObj_eq_vertex (a := a) (b := b) hX.1
    have h1 : vertexMap a b X (fun i j => decide (0 ≤ X i j)) < t :=
      hz (fun i j => decide (0 ≤ X i j))
    rw [vertexMap_apply, hmax] at h1
    exact absurd (ht X hX) (not_le.2 h1)
  obtain ⟨f, u, hfU, hfK⟩ := geometric_hahn_banach_open hUconv hUopen hKconv hdisj
  -- coordinates of the separating functional
  set pw : (Fin n → Fin n → Bool) → ℝ :=
    fun s => f (Pi.single s (1:ℝ) : (Fin n → Fin n → Bool) → ℝ) with hpwdef
  have hf_apply : ∀ z : (Fin n → Fin n → Bool) → ℝ, f z = ∑ s, z s * pw s := by
    intro z
    conv_lhs => rw [← Finset.univ_sum_single z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hsingle : (Pi.single s (z s) : (Fin n → Fin n → Bool) → ℝ)
        = z s • (Pi.single s (1:ℝ) : (Fin n → Fin n → Bool) → ℝ) := by
      funext r
      by_cases hr : r = s
      · subst hr; simp
      · simp [hr]
    rw [hsingle, map_smul, smul_eq_mul, hpwdef]
  have hconstU : ∀ c : ℝ, c < t → (fun _ => c : (Fin n → Fin n → Bool) → ℝ) ∈ U :=
    fun c hc _ => hc
  have hpw_nonneg : ∀ s0, 0 ≤ pw s0 := by
    intro s0
    by_contra hneg
    push_neg at hneg
    set z0 : (Fin n → Fin n → Bool) → ℝ := fun _ => t - 1 with hz0def
    have hz0 : z0 ∈ U := hconstU _ (by linarith)
    have hf0 : f z0 < u := hfU z0 hz0
    set d : ℝ := (u - f z0 + 1) / (-pw s0) with hddef
    have hdpos : 0 < d := by
      apply div_pos (by linarith) (by linarith)
    set z1 : (Fin n → Fin n → Bool) → ℝ :=
      z0 - d • (Pi.single s0 (1:ℝ) : (Fin n → Fin n → Bool) → ℝ) with hz1def
    have hz1 : z1 ∈ U := by
      intro s
      simp only [hz1def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hz0def]
      by_cases hs : s = s0
      · subst hs; simp; linarith
      · simp [hs]
    have hfz1 : f z1 = f z0 - d * pw s0 := by
      simp only [hz1def, map_sub, map_smul, smul_eq_mul, hpwdef]
    have hne : pw s0 ≠ 0 := ne_of_lt hneg
    have hval : -(d * pw s0) = u - f z0 + 1 := by
      rw [hddef]; field_simp
    have hlt := hfU z1 hz1
    rw [hfz1] at hlt
    linarith
  set S : ℝ := ∑ s, pw s with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun s _ => hpw_nonneg s
  have hconstf : ∀ c : ℝ, f (fun _ => c) = c * S := by
    intro c
    rw [hf_apply]
    rw [hSdef, Finset.mul_sum]
  have hSpos : 0 < S := by
    rcases eq_or_lt_of_le hS0 with hS | hS
    · exfalso
      have hall : ∀ s, pw s = 0 := fun s =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => hpw_nonneg s)).1 hS.symm s (Finset.mem_univ s)
      have hfzero : ∀ z : (Fin n → Fin n → Bool) → ℝ, f z = 0 := by
        intro z; rw [hf_apply]; simp [hall]
      obtain ⟨X, hX⟩ := hDne
      have h1 : u ≤ f (vertexMap a b X) := hfK _ ⟨X, hX, rfl⟩
      have h2 := hfU _ (hconstU (t-1) (by linarith))
      rw [hfzero] at h1 h2
      linarith
    · exact hS
  have htS : t * S ≤ u := by
    by_contra hcon
    push_neg at hcon
    have hc : u / S < t := by rw [div_lt_iff₀ hSpos]; linarith
    have := hfU _ (hconstU _ hc)
    rw [hconstf, div_mul_cancel₀ _ (ne_of_gt hSpos)] at this
    exact lt_irrefl u this
  -- the optimal matrix
  set w : (Fin n → Fin n → Bool) → ℝ := fun s => pw s / S with hwdef
  have hw : ∀ s, 0 ≤ w s := fun s => div_nonneg (hpw_nonneg s) hS0
  have hwsum : ∑ s, w s = 1 := by
    rw [hwdef]
    simp only []
    rw [← Finset.sum_div, ← hSdef, div_self (ne_of_gt hSpos)]
  set Astar : Matrix (Fin n) (Fin n) ℝ := ∑ s, w s • vertex a b s with hAdef
  have hAentry : ∀ i j, Astar i j = ∑ s, w s * (vertex a b s) i j := by
    intro i j
    rw [hAdef]
    simp [Matrix.sum_apply, Matrix.smul_apply]
  have hAsym : ∀ i j, Astar j i = Astar i j := by
    intro i j
    rw [hAentry, hAentry]
    exact Finset.sum_congr rfl fun s _ => by
      simp only [vertex, Matrix.of_apply]
      rw [Bool.or_comm]
  have hAherm : Astar.IsHermitian := by
    ext i j
    simpa [Matrix.conjTranspose_apply] using hAsym i j
  have hAmem : Astar ∈ SymIcc n a b := by
    refine ⟨hAherm, fun i j => ⟨?_, ?_⟩⟩
    · rw [hAentry]
      calc a = ∑ s, w s * a := by rw [← Finset.sum_mul, hwsum, one_mul]
        _ ≤ ∑ s, w s * (vertex a b s) i j :=
            Finset.sum_le_sum fun s _ =>
              mul_le_mul_of_nonneg_left ((vertex_mem hab s).2 i j).1 (hw s)
    · rw [hAentry]
      calc ∑ s, w s * (vertex a b s) i j ≤ ∑ s, w s * b :=
            Finset.sum_le_sum fun s _ =>
              mul_le_mul_of_nonneg_left ((vertex_mem hab s).2 i j).2 (hw s)
        _ = b := by rw [← Finset.sum_mul, hwsum, one_mul]
  have htf : ∀ X ∈ DensityOn V, t ≤ traceForm Astar X := by
    intro X hX
    have h1 : traceForm Astar X = f (vertexMap a b X) / S := by
      rw [hAdef, traceForm_sum_left]
      rw [hf_apply]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [traceForm_smul_left, vertexMap_apply, hwdef]
      ring
    have h2 : u ≤ f (vertexMap a b X) := hfK _ ⟨X, hX, rfl⟩
    rw [h1, le_div_iff₀ hSpos]
    linarith
  have hquad : ∀ y ∈ V, t * (y ⬝ᵥ y) ≤ y ⬝ᵥ Astar *ᵥ y := by
    intro y hy
    rcases eq_or_lt_of_le (dotProduct_self_nonneg y) with h0 | hpos
    · have hy0 : y = 0 := eq_zero_of_dotProduct_self_eq_zero h0.symm
      subst hy0
      simp
    · set c : ℝ := 1 / Real.sqrt (y ⬝ᵥ y) with hcdef
      have hc2 : c ^ 2 = 1 / (y ⬝ᵥ y) := by
        rw [hcdef, div_pow, one_pow, Real.sq_sqrt hpos.le]
      have hxV : c • y ∈ V := V.smul_mem _ hy
      have hx1 : (c • y) ⬝ᵥ (c • y) = 1 := by
        rw [dot_smul, hc2]
        field_simp
      have hmain := htf (Matrix.vecMulVec (c • y) (c • y))
        (vecMulVec_mem_DensityOn hxV hx1)
      rw [traceForm_vecMulVec, quad_form_smul, hc2] at hmain
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos] at hmain
      linarith
  exact ⟨Astar, hAmem, le_eigVal_of_subspace hAherm k V hV t hquad⟩


/-! ### Boundedness of the eigenvalue range -/

lemma eigVal_le_of_SymIcc {n : ℕ} {a b : ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ SymIcc n a b) (k : Fin n) : eigVal A k ≤ (n:ℝ)^3 * max |a| |b| := by
  set M : ℝ := max |a| |b| with hMdef
  have hM0 : 0 ≤ M := le_trans (abs_nonneg a) (le_max_left _ _)
  have hent : ∀ i j, |A i j| ≤ M := by
    intro i j
    obtain ⟨h1, h2⟩ := hA.2 i j
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have ha : -|a| ≤ a := neg_abs_le a
      have hle : |a| ≤ M := le_max_left _ _
      linarith
    · have hb : b ≤ |b| := le_abs_self b
      have hle : |b| ≤ M := le_max_right _ _
      linarith
  have hsum : ∑ i, ∑ j : Fin n, |A i j| ≤ (n:ℝ)^2 * M := by
    have h : ∑ i : Fin n, ∑ j : Fin n, |A i j| ≤ ∑ _i : Fin n, ∑ _j : Fin n, M :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hent i j
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    calc ∑ i, ∑ j : Fin n, |A i j| ≤ (n:ℝ) * ((n:ℝ) * M) := by simpa using h
      _ = (n:ℝ)^2 * M := by ring
  refine eigVal_le_of_forall hA.1 k _ fun x => ?_
  have h := quad_form_abs_le A x
  have hx : 0 ≤ x ⬝ᵥ x := dotProduct_self_nonneg x
  have h2 : x ⬝ᵥ A *ᵥ x ≤ ((n:ℝ) * ∑ i, ∑ j, |A i j|) * (x ⬝ᵥ x) := le_trans (le_abs_self _) h
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have h3 : ((n:ℝ) * ∑ i, ∑ j, |A i j|) ≤ (n:ℝ)^3 * M := by nlinarith
  nlinarith

lemma le_eigVal_of_SymIcc {n : ℕ} {a b : ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ SymIcc n a b) (k : Fin n) : -((n:ℝ)^3 * max |b| |a|) ≤ eigVal A k := by
  have h := eigVal_le_of_SymIcc (neg_mem_SymIcc hA) (Fin.rev k)
  rw [eigVal_neg hA.1, Fin.rev_rev, abs_neg, abs_neg] at h
  linarith

lemma bddAbove_eigRange (n : ℕ) (a b : ℝ) (k : Fin n) : BddAbove (eigRange n a b k) := by
  refine ⟨(n:ℝ)^3 * max |a| |b|, ?_⟩
  rintro _ ⟨A, hA, rfl⟩
  exact eigVal_le_of_SymIcc hA k

lemma bddBelow_eigRange (n : ℕ) (a b : ℝ) (k : Fin n) : BddBelow (eigRange n a b k) := by
  refine ⟨-((n:ℝ)^3 * max |b| |a|), ?_⟩
  rintro _ ⟨A, hA, rfl⟩
  exact le_eigVal_of_SymIcc hA k

lemma eigRange_nonempty {n : ℕ} {a b : ℝ} (hab : a ≤ b) (k : Fin n) :
    (eigRange n a b k).Nonempty :=
  ⟨_, ⟨vertex a b (fun _ _ => true), vertex_mem hab _, rfl⟩⟩

lemma exists_submodule_finrank_succ (n : ℕ) (k : Fin n) :
    ∃ V : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ V = (k:ℕ) + 1 :=
  ⟨coordKer (Finset.Ioi k), by
    rw [finrank_coordKer_eq, Fin.card_Ioi]; have := k.isLt; omega⟩

lemma exists_submodule_finrank_compl (n : ℕ) (k : Fin n) :
    ∃ W : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ W = n - (k:ℕ) :=
  ⟨coordKer (Finset.Iio k), by rw [finrank_coordKer_eq, Fin.card_Iio]⟩

/-! ### (2.10): the exact density-matrix minimax formula for `U_k` -/

/-- The set of exact inner minimax values of the upper density objective over subspaces of
dimension `k+1`. -/
noncomputable def densMinimaxUpper (n : ℕ) (a b : ℝ) (k : Fin n) : Set ℝ :=
  {t | ∃ V : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ V = (k:ℕ) + 1 ∧
        IsGLB (densityObj a b '' DensityOn V) t}

lemma densMinimaxUpper_nonempty (n : ℕ) (a b : ℝ) (k : Fin n) :
    (densMinimaxUpper n a b k).Nonempty := by
  obtain ⟨V, hV⟩ := exists_submodule_finrank_succ n k
  have hpos : 0 < Module.finrank ℝ V := by rw [hV]; omega
  exact ⟨sInf (densityObj a b '' DensityOn V), V, hV,
    isGLB_csInf ((DensityOn_nonempty hpos).image _) (bddBelow_densityObj a b V)⟩

/-- **Formula (2.10)**: the supremum of the `(k+1)`-st largest eigenvalue over `S_n([a,b])`
equals the max-min of the density objective `c·1ᵀX1 + r·|X|_{1,e}` over subspaces of
dimension `k+1`.  This is an exact identity, not a relaxation. -/
theorem sSup_eigRange_eq_densMinimaxUpper {n : ℕ} {a b : ℝ} (hab : a ≤ b) (k : Fin n) :
    sSup (eigRange n a b k) = sSup (densMinimaxUpper n a b k) := by
  have hbddA : BddAbove (eigRange n a b k) := bddAbove_eigRange n a b k
  have hneA : (eigRange n a b k).Nonempty := eigRange_nonempty hab k
  have hneD : (densMinimaxUpper n a b k).Nonempty := densMinimaxUpper_nonempty n a b k
  have hbddD : BddAbove (densMinimaxUpper n a b k) := by
    refine ⟨sSup (eigRange n a b k), ?_⟩
    rintro t ⟨V, hV, hglb⟩
    obtain ⟨A, hA, hle⟩ := exists_matrix_ge_density hab k V (le_of_eq hV.symm) t
      (fun X hX => hglb.1 ⟨X, hX, rfl⟩)
    exact le_trans hle (le_csSup hbddA ⟨A, hA, rfl⟩)
  refine le_antisymm (csSup_le hneA ?_) (csSup_le hneD ?_)
  · rintro _ ⟨A, hA, rfl⟩
    obtain ⟨V, hV, hdom⟩ := exists_density_subspace hA k
    have hpos : 0 < Module.finrank ℝ V := by rw [hV]; omega
    have hglb : IsGLB (densityObj a b '' DensityOn V) (sInf (densityObj a b '' DensityOn V)) :=
      isGLB_csInf ((DensityOn_nonempty hpos).image _) (bddBelow_densityObj a b V)
    have hlb : eigVal A k ≤ sInf (densityObj a b '' DensityOn V) :=
      hglb.2 (by rintro _ ⟨X, hX, rfl⟩; exact hdom X hX)
    exact le_trans hlb (le_csSup hbddD ⟨V, hV, hglb⟩)
  · rintro t ⟨V, hV, hglb⟩
    obtain ⟨A, hA, hle⟩ := exists_matrix_ge_density hab k V (le_of_eq hV.symm) t
      (fun X hX => hglb.1 ⟨X, hX, rfl⟩)
    exact le_trans hle (le_csSup hbddA ⟨A, hA, rfl⟩)

/-! ### (2.11): the dual formula for `L_k` -/

/-- The lower density objective `c·1ᵀX1 - r·|X|_{1,e}`. -/
noncomputable def densityObjLower (a b : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (a+b)/2 * oneQuad X - (b-a)/2 * entryAbs X

lemma densityObjLower_eq (a b : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    densityObjLower a b X = - densityObj (-b) (-a) X := by
  simp only [densityObjLower, densityObj]; ring

lemma bddAbove_densityObjLower (a b : ℝ) (V : Submodule ℝ (Fin n → ℝ)) :
    BddAbove (densityObjLower a b '' DensityOn V) := by
  refine ⟨|(a+b)/2| * (n:ℝ)^2 + |(b-a)/2| * (n:ℝ)^2, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  have h1 : |(a+b)/2 * oneQuad X| ≤ |(a+b)/2| * (n:ℝ)^2 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_oneQuad_le_of_density hX) (abs_nonneg _)
  have h2 : |(b-a)/2 * entryAbs X| ≤ |(b-a)/2| * (n:ℝ)^2 := by
    rw [abs_mul, abs_of_nonneg (entryAbs_nonneg X)]
    exact mul_le_mul_of_nonneg_left (entryAbs_le_of_density hX) (abs_nonneg _)
  have e1 := abs_le.1 h1
  have e2 := abs_le.1 h2
  simp only [densityObjLower]
  linarith [e1.2, e2.1]

lemma rev_val_succ {n : ℕ} (k : Fin n) : ((Fin.rev k : Fin n) : ℕ) + 1 = n - (k:ℕ) := by
  have hk := k.isLt
  simp only [Fin.val_rev]
  omega

/-- (2.11), easy direction. -/
theorem exists_density_subspace_lower {n : ℕ} {a b : ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ SymIcc n a b) (k : Fin n) :
    ∃ W : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ W = n - (k:ℕ) ∧
      ∀ X ∈ DensityOn W, densityObjLower a b X ≤ eigVal A k := by
  obtain ⟨W, hW, hdom⟩ := exists_density_subspace (neg_mem_SymIcc hA) (Fin.rev k)
  refine ⟨W, by rw [hW, rev_val_succ], fun X hX => ?_⟩
  have h := hdom X hX
  rw [eigVal_neg hA.1, Fin.rev_rev] at h
  rw [densityObjLower_eq]
  linarith

/-- (2.11), hard direction. -/
theorem exists_matrix_le_density {n : ℕ} {a b : ℝ} (hab : a ≤ b) (k : Fin n)
    (W : Submodule ℝ (Fin n → ℝ)) (hW : n - (k:ℕ) ≤ Module.finrank ℝ W) (t : ℝ)
    (ht : ∀ X ∈ DensityOn W, densityObjLower a b X ≤ t) :
    ∃ A ∈ SymIcc n a b, eigVal A k ≤ t := by
  obtain ⟨A', hA', hge⟩ := exists_matrix_ge_density (a := -b) (b := -a) (by linarith)
    (Fin.rev k) W (by rw [rev_val_succ]; exact hW) (-t)
    (fun X hX => by have h := ht X hX; rw [densityObjLower_eq] at h; linarith)
  refine ⟨-A', by simpa using neg_mem_SymIcc hA', ?_⟩
  have h := eigVal_neg hA'.1 k
  linarith

/-- The set of exact inner values of the lower density objective over subspaces of
dimension `n-k`. -/
noncomputable def densMinimaxLower (n : ℕ) (a b : ℝ) (k : Fin n) : Set ℝ :=
  {t | ∃ W : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ W = n - (k:ℕ) ∧
        IsLUB (densityObjLower a b '' DensityOn W) t}

lemma densMinimaxLower_nonempty (n : ℕ) (a b : ℝ) (k : Fin n) :
    (densMinimaxLower n a b k).Nonempty := by
  obtain ⟨W, hW⟩ := exists_submodule_finrank_compl n k
  have hpos : 0 < Module.finrank ℝ W := by
    rw [hW]; have := k.isLt; omega
  exact ⟨sSup (densityObjLower a b '' DensityOn W), W, hW,
    isLUB_csSup ((DensityOn_nonempty hpos).image _) (bddAbove_densityObjLower a b W)⟩

/-- **Formula (2.11)**: the infimum of the `(k+1)`-st largest eigenvalue over `S_n([a,b])`
equals the min-max of the lower density objective `c·1ᵀX1 - r·|X|_{1,e}` over subspaces of
dimension `n-k`. -/
theorem sInf_eigRange_eq_densMinimaxLower {n : ℕ} {a b : ℝ} (hab : a ≤ b) (k : Fin n) :
    sInf (eigRange n a b k) = sInf (densMinimaxLower n a b k) := by
  have hbddA : BddBelow (eigRange n a b k) := bddBelow_eigRange n a b k
  have hneA : (eigRange n a b k).Nonempty := eigRange_nonempty hab k
  have hneL : (densMinimaxLower n a b k).Nonempty := densMinimaxLower_nonempty n a b k
  have hbddL : BddBelow (densMinimaxLower n a b k) := by
    refine ⟨sInf (eigRange n a b k), ?_⟩
    rintro t ⟨W, hW, hlub⟩
    obtain ⟨A, hA, hle⟩ := exists_matrix_le_density hab k W (le_of_eq hW.symm) t
      (fun X hX => hlub.1 ⟨X, hX, rfl⟩)
    exact le_trans (csInf_le hbddA ⟨A, hA, rfl⟩) hle
  refine le_antisymm (le_csInf hneL ?_) (le_csInf hneA ?_)
  · rintro t ⟨W, hW, hlub⟩
    obtain ⟨A, hA, hle⟩ := exists_matrix_le_density hab k W (le_of_eq hW.symm) t
      (fun X hX => hlub.1 ⟨X, hX, rfl⟩)
    exact le_trans (csInf_le hbddA ⟨A, hA, rfl⟩) hle
  · rintro _ ⟨A, hA, rfl⟩
    obtain ⟨W, hW, hdom⟩ := exists_density_subspace_lower hA k
    have hpos : 0 < Module.finrank ℝ W := by
      rw [hW]; have := k.isLt; omega
    have hlub : IsLUB (densityObjLower a b '' DensityOn W)
        (sSup (densityObjLower a b '' DensityOn W)) :=
      isLUB_csSup ((DensityOn_nonempty hpos).image _) (bddAbove_densityObjLower a b W)
    have hub : sSup (densityObjLower a b '' DensityOn W) ≤ eigVal A k :=
      hlub.2 (by rintro _ ⟨X, hX, rfl⟩; exact hdom X hX)
    exact le_trans (csInf_le hbddL ⟨W, hW, hlub⟩) hub


/-! ### (2.12)-(2.13): the centered interval -/

open scoped Pointwise

/-- The set whose supremum is the constant `η_{n,k}` of formula (2.12).

The numerical value of `η_{n,k}` for intermediate `k` is *not* determined here: evaluating it
explicitly is the open problem identified in the source.  Only `η_{n,1} = n` and
`η_{n,n} = 1` are proved below. -/
noncomputable def etaSet (n : ℕ) (k : Fin n) : Set ℝ :=
  {t | ∃ V : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ V = (k:ℕ) + 1 ∧
        IsGLB (entryAbs '' DensityOn V) t}

/-- The constant `η_{n,k} = max_{dim V = k} min_{X ∈ 𝒟(V)} |X|_{1,e}`. -/
noncomputable def etaConst (n : ℕ) (k : Fin n) : ℝ := sSup (etaSet n k)

lemma isGLB_mul_left {r : ℝ} (hr : 0 < r) {S : Set ℝ} {u : ℝ} :
    IsGLB ((fun x => r * x) '' S) (r * u) ↔ IsGLB S u := by
  constructor
  · rintro ⟨hlb, hgl⟩
    refine ⟨fun x hx => le_of_mul_le_mul_left (hlb ⟨x, hx, rfl⟩) hr, fun v hv => ?_⟩
    have hrv : r * v ∈ lowerBounds ((fun x => r * x) '' S) := by
      rintro _ ⟨x, hx, rfl⟩
      exact mul_le_mul_of_nonneg_left (hv hx) hr.le
    exact le_of_mul_le_mul_left (hgl hrv) hr
  · rintro ⟨hlb, hgl⟩
    refine ⟨?_, fun v hv => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact mul_le_mul_of_nonneg_left (hlb hx) hr.le
    · have hdiv : v / r ∈ lowerBounds S := by
        intro x hx
        have h := hv ⟨x, hx, rfl⟩
        rw [div_le_iff₀ hr]
        linarith
      have h := hgl hdiv
      rw [div_le_iff₀ hr] at h
      linarith

lemma densityObj_centered_image (r : ℝ) (V : Submodule ℝ (Fin n → ℝ)) :
    densityObj (-r) r '' DensityOn V = (fun x => r * x) '' (entryAbs '' DensityOn V) := by
  rw [Set.image_image]
  refine Set.image_congr fun X _ => ?_
  simp only [densityObj]
  ring

lemma densMinimaxUpper_centered {n : ℕ} {r : ℝ} (hr : 0 < r) (k : Fin n) :
    densMinimaxUpper n (-r) r k = r • etaSet n k := by
  ext t
  constructor
  · rintro ⟨V, hV, hglb⟩
    rw [densityObj_centered_image] at hglb
    have hrw : t = r * (t / r) := by field_simp
    rw [hrw] at hglb
    exact ⟨t / r, ⟨V, hV, (isGLB_mul_left hr).1 hglb⟩, by simp [smul_eq_mul]; field_simp⟩
  · rintro ⟨u, ⟨V, hV, hglb⟩, rfl⟩
    refine ⟨V, hV, ?_⟩
    rw [densityObj_centered_image]
    show IsGLB ((fun x => r * x) '' (entryAbs '' DensityOn V)) (r * u)
    exact (isGLB_mul_left hr).2 hglb

/-- **Formula (2.12)**: on the centered interval `[-r, r]` the maximum of the `(k+1)`-st
largest eigenvalue is `r · η_{n,k}`. -/
theorem sSup_eigRange_centered {n : ℕ} {r : ℝ} (hr : 0 < r) (k : Fin n) :
    sSup (eigRange n (-r) r k) = r * etaConst n k := by
  rw [sSup_eigRange_eq_densMinimaxUpper (by linarith) k, densMinimaxUpper_centered hr k,
    Real.sSup_smul_of_nonneg hr.le, etaConst, smul_eq_mul]

/-- **Formula (2.13)**: on a centered interval the minimum of `λ_{k+1}` is minus the maximum
of the reversed eigenvalue index. -/
theorem sInf_eigRange_centered {n : ℕ} (r : ℝ) (k : Fin n) :
    sInf (eigRange n (-r) r k) = - sSup (eigRange n (-r) r (Fin.rev k)) := by
  have h1 : eigRange n (-r) r (Fin.rev k) = -(eigRange n (-r) r k) := by
    have h := eigRange_neg' n (-r) r k
    rw [neg_neg, Set.image_neg_eq_neg] at h
    exact h.symm
  rw [← Real.sInf_neg, h1, neg_neg]

/-- `η_{n,1} = n`. -/
theorem etaConst_first (m : ℕ) : etaConst (m+2) (0 : Fin (m+2)) = ((m:ℝ)+2) := by
  have hg : IsGreatest (eigRange (m+2) (-1) 1 (0 : Fin (m+2))) (U1 (m+2) (-1) 1) :=
    isGreatest_eigRange_first (by norm_num)
  have hU : U1 (m+2) (-1) (1:ℝ) = ((m:ℝ)+2) := by
    rw [U1, if_pos (by norm_num)]
    push_cast
    ring
  have h := sSup_eigRange_centered (n := m+2) (r := 1) one_pos (0 : Fin (m+2))
  rw [hg.csSup_eq, hU, one_mul] at h
  exact h.symm

/-- `η_{n,n} = 1`. -/
theorem etaConst_last (m : ℕ) : etaConst (m+2) (Fin.last (m+1)) = 1 := by
  have hg : IsGreatest (eigRange (m+2) (-1) 1 (Fin.last (m+1))) (Un (m+2) (-1) 1) :=
    isGreatest_eigRange_last (by norm_num)
  have hU : Un (m+2) (-1) (1:ℝ) = 1 := by
    rw [Un, if_neg (by norm_num), if_pos (by norm_num)]
  have h := sSup_eigRange_centered (n := m+2) (r := 1) one_pos (Fin.last (m+1))
  rw [hg.csSup_eq, hU, one_mul] at h
  exact h.symm


end Q706
