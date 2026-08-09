import RMS.Q655Split

/-!
# Q655 — Stage 3B: the irreducible quadratic case

If `f` satisfies a monic quadratic with no root in `K` (so, over a field, an irreducible
quadratic — including inseparable ones in characteristic two), then the pair action at any
nonzero `(u, φ)` has the maximal rank `2n - 2`.

The proof is a coordinate form of the `K[X]/(q)`-linear algebra argument: the matrices
`Lrank1 f c a B` below are exactly the `K[X]/(q)`-rank-one endomorphisms.
-/

namespace Q655

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

/-! ## Prescribing two dot products -/

lemma eq_smul_of_dot_zero_imp {a b : Vec K n} (ha : a ≠ 0)
    (h : ∀ s : Vec K n, a ⬝ᵥ s = 0 → b ⬝ᵥ s = 0) : ∃ lam : K, b = lam • a := by
  obtain ⟨t, ht⟩ := exists_dotProduct_eq_one ha
  refine ⟨b ⬝ᵥ t, funext fun j => ?_⟩
  have key : ∀ s : Vec K n, b ⬝ᵥ s = (b ⬝ᵥ t) * (a ⬝ᵥ s) := by
    intro s
    have h0 : a ⬝ᵥ (s - (a ⬝ᵥ s) • t) = 0 := by
      simp [dotProduct_sub, dotProduct_smul, ht]
    have hb := h _ h0
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_eq_zero] at hb
    linear_combination hb
  have := key (Pi.single j 1)
  simpa [dotProduct, Pi.single_apply, Finset.sum_ite_eq', mul_comm] using this

lemma exists_dot_zero_one {a b : Vec K n} (ha : a ≠ 0)
    (hindep : ∀ lam : K, b ≠ lam • a) : ∃ s : Vec K n, a ⬝ᵥ s = 0 ∧ b ⬝ᵥ s = 1 := by
  by_cases h : ∀ s : Vec K n, a ⬝ᵥ s = 0 → b ⬝ᵥ s = 0
  · obtain ⟨lam, hlam⟩ := eq_smul_of_dot_zero_imp ha h
    exact absurd hlam (hindep lam)
  · push_neg at h
    obtain ⟨s, hs0, hs1⟩ := h
    exact ⟨(b ⬝ᵥ s)⁻¹ • s, by rw [dotProduct_smul, hs0, smul_zero],
      by rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hs1]⟩

/-! ## No eigenvalues -/

variable {f : Matrix (Fin n) (Fin n) K} {c d : K}

lemma no_eigenvector_of_no_root
    (hq : f * f + c • f + d • (1 : Matrix (Fin n) (Fin n) K) = 0)
    (hnoroot : ∀ x : K, x * x + c * x + d ≠ 0)
    {u : Vec K n} (hu : u ≠ 0) (lam : K) : f *ᵥ u ≠ lam • u := by
  intro h
  have h0 : (f * f + c • f + d • (1 : Matrix (Fin n) (Fin n) K)) *ᵥ u = 0 := by
    rw [hq, Matrix.zero_mulVec]
  rw [Matrix.add_mulVec, Matrix.add_mulVec, smul_mulVec, smul_mulVec,
    ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, h, Matrix.one_mulVec] at h0
  have : (lam * lam + c * lam + d) • u = 0 := by
    rw [← h0]; module
  rcases smul_eq_zero.1 this with h1 | h1
  · exact hnoroot lam h1
  · exact hu h1

lemma no_left_eigenvector_of_no_root
    (hq : f * f + c • f + d • (1 : Matrix (Fin n) (Fin n) K) = 0)
    (hnoroot : ∀ x : K, x * x + c * x + d ≠ 0)
    {phi : Vec K n} (hphi : phi ≠ 0) (lam : K) : phi ᵥ* f ≠ lam • phi := by
  intro h
  have h0 : phi ᵥ* (f * f + c • f + d • (1 : Matrix (Fin n) (Fin n) K)) = 0 := by
    rw [hq, Matrix.vecMul_zero]
  rw [Matrix.vecMul_add, Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_smul,
    ← Matrix.vecMul_vecMul, h, Matrix.smul_vecMul, h, Matrix.vecMul_one] at h0
  have : (lam * lam + c * lam + d) • phi = 0 := by
    rw [← h0]; module
  rcases smul_eq_zero.1 this with h1 | h1
  · exact hnoroot lam h1
  · exact hphi h1

/-! ## `K[X]/(q)`-rank-one matrices, in coordinates -/

/-- The coordinate form of an `L`-rank-one endomorphism, `L = K[X]/(X² + cX + d)`. -/
def Lrank1 (f : Matrix (Fin n) (Fin n) K) (c : K) (a B : Vec K n) :
    Matrix (Fin n) (Fin n) K :=
  outer a (B ᵥ* f + c • B) + outer (f *ᵥ a) B

lemma Lrank1_mulVec (f : Matrix (Fin n) (Fin n) K) (c : K) (a B x : Vec K n) :
    Lrank1 f c a B *ᵥ x = (B ⬝ᵥ (f *ᵥ x) + c * (B ⬝ᵥ x)) • a + (B ⬝ᵥ x) • (f *ᵥ a) := by
  rw [Lrank1, Matrix.add_mulVec, outer_mulVec, outer_mulVec]
  congr 1
  congr 1
  rw [add_dotProduct, smul_dotProduct, dotProduct_mulVec, smul_eq_mul]

lemma Lrank1_vecMul (f : Matrix (Fin n) (Fin n) K) (c : K) (a B phi : Vec K n) :
    phi ᵥ* Lrank1 f c a B =
      (phi ⬝ᵥ a) • (B ᵥ* f + c • B) + (phi ⬝ᵥ (f *ᵥ a)) • B := by
  rw [Lrank1, Matrix.vecMul_add, vecMul_outer, vecMul_outer]

lemma outer_add_left (a b C : Vec K n) : outer (a + b) C = outer a C + outer b C := by
  ext i j; simp [outer]; ring

lemma outer_add_right (a B C : Vec K n) : outer a (B + C) = outer a B + outer a C := by
  ext i j; simp [outer]; ring

lemma Lrank1_mem_commutant (hq : f * f + c • f + d • (1 : Matrix (Fin n) (Fin n) K) = 0)
    (a B : Vec K n) : Lrank1 f c a B ∈ commutant f := by
  have hf2 : f * f = -(c • f) - d • (1 : Matrix (Fin n) (Fin n) K) := by
    linear_combination (norm := module) hq
  have hBff : (B ᵥ* f + c • B) ᵥ* f = (-d) • B := by
    rw [Matrix.add_vecMul, Matrix.vecMul_vecMul, hf2, Matrix.smul_vecMul]
    simp only [Matrix.vecMul_sub, Matrix.vecMul_neg, Matrix.vecMul_smul, Matrix.vecMul_one]
    module
  have hffa : f *ᵥ (f *ᵥ a) = (-c) • (f *ᵥ a) + (-d) • a := by
    rw [Matrix.mulVec_mulVec, hf2]
    simp only [Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.mulVec_smul, smul_mulVec,
      Matrix.one_mulVec]
    module
  have hL : Lrank1 f c a B * f = (-d) • outer a B + outer (f *ᵥ a) (B ᵥ* f) := by
    rw [Lrank1, Matrix.add_mul, outer_mul, outer_mul, hBff, outer_smul_right]
  have hR : f * Lrank1 f c a B =
      outer (f *ᵥ a) (B ᵥ* f + c • B) + outer (f *ᵥ (f *ᵥ a)) B := by
    rw [Lrank1, Matrix.mul_add, mul_outer, mul_outer]
  rw [mem_commutant_iff, hL, hR, hffa, outer_add_left, outer_add_right, outer_smul_left,
    outer_smul_left, outer_smul_right]
  module


lemma Lrank1_add_left (f : Matrix (Fin n) (Fin n) K) (c : K) (a a' B : Vec K n) :
    Lrank1 f c (a + a') B = Lrank1 f c a B + Lrank1 f c a' B := by
  simp only [Lrank1, Matrix.mulVec_add, outer_add_left]
  abel

/-! ## The second invariant functional -/

/-- `ℓ₁(v, α) = φ(f v) - α(f u)`. -/
def ell1 (f : Matrix (Fin n) (Fin n) K) (u phi : Vec K n) :
    (Vec K n × Vec K n) →ₗ[K] K where
  toFun p := (phi ᵥ* f) ⬝ᵥ p.1 - p.2 ⬝ᵥ (f *ᵥ u)
  map_add' p q := by simp [dotProduct_add, add_dotProduct]; ring
  map_smul' r p := by simp [dotProduct_smul, smul_dotProduct]; ring

@[simp] lemma ell1_apply (f : Matrix (Fin n) (Fin n) K) (u phi : Vec K n)
    (p : Vec K n × Vec K n) : ell1 f u phi p = (phi ᵥ* f) ⬝ᵥ p.1 - p.2 ⬝ᵥ (f *ᵥ u) := rfl

lemma range_pairAction_le_kers (f : Matrix (Fin n) (Fin n) K) (u phi : Vec K n) :
    LinearMap.range (pairAction f u phi) ≤
      LinearMap.ker (compatFun u phi) ⊓ LinearMap.ker (ell1 f u phi) := by
  rintro p ⟨⟨X, hX⟩, rfl⟩
  have hXf : X * f = f * X := hX
  constructor
  · show phi ⬝ᵥ (X *ᵥ u) - (phi ᵥ* X) ⬝ᵥ u = 0
    rw [sub_eq_zero, dotProduct_mulVec]
  · show (phi ᵥ* f) ⬝ᵥ (X *ᵥ u) - (phi ᵥ* X) ⬝ᵥ (f *ᵥ u) = 0
    rw [sub_eq_zero, dotProduct_mulVec, dotProduct_mulVec, Matrix.vecMul_vecMul,
      Matrix.vecMul_vecMul, hXf]

/-! ## The main computation -/

theorem range_pairAction_irreducible
    (hq : f * f + c • f + d • (1 : Matrix (Fin n) (Fin n) K) = 0)
    (hnoroot : ∀ x : K, x * x + c * x + d ≠ 0)
    {u phi : Vec K n} (hu : u ≠ 0) (hphi : phi ≠ 0) :
    LinearMap.range (pairAction f u phi) =
      LinearMap.ker (compatFun u phi) ⊓ LinearMap.ker (ell1 f u phi) := by
  refine le_antisymm (range_pairAction_le_kers f u phi) ?_
  obtain ⟨s, hs0, hs1⟩ :=
    exists_dot_zero_one hphi (no_left_eigenvector_of_no_root hq hnoroot hphi)
  obtain ⟨E, hE0, hE1⟩ := exists_dot_zero_one hu (no_eigenvector_of_no_root hq hnoroot hu)
  -- `hE0 : u ⬝ᵥ E = 0`, `hE1 : (f *ᵥ u) ⬝ᵥ E = 1`
  have hEu : E ⬝ᵥ u = 0 := by rw [dotProduct_comm]; exact hE0
  have hEfu : E ⬝ᵥ (f *ᵥ u) = 1 := by rw [dotProduct_comm]; exact hE1
  have hphifs : phi ⬝ᵥ (f *ᵥ s) = 1 := by rw [dotProduct_mulVec]; exact hs1
  have hf2 : f * f = -(c • f) - d • (1 : Matrix (Fin n) (Fin n) K) := by
    linear_combination (norm := module) hq
  have hffs' : f *ᵥ (f *ᵥ s) = (-c) • (f *ᵥ s) + (-d) • s := by
    rw [Matrix.mulVec_mulVec, hf2]
    simp only [Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.mulVec_smul, smul_mulVec,
      Matrix.one_mulVec]
    module
  have hffs : phi ⬝ᵥ (f *ᵥ (f *ᵥ s)) = -c := by
    rw [hffs', dotProduct_add, dotProduct_smul, dotProduct_smul, hphifs, hs0]
    simp
  rintro ⟨v, alpha⟩ ⟨hc0, hc1⟩
  have hcompat : phi ⬝ᵥ v = alpha ⬝ᵥ u := by
    have h : phi ⬝ᵥ v - alpha ⬝ᵥ u = 0 := hc0
    linear_combination h
  have hcompat1 : (phi ᵥ* f) ⬝ᵥ v = alpha ⬝ᵥ (f *ᵥ u) := by
    have h : (phi ᵥ* f) ⬝ᵥ v - alpha ⬝ᵥ (f *ᵥ u) = 0 := hc1
    linear_combination h
  set A0 : K := alpha ⬝ᵥ (f *ᵥ u) + c * (alpha ⬝ᵥ u) with hA0
  set B0 : K := alpha ⬝ᵥ u with hB0
  set z : Vec K n := A0 • s + B0 • (f *ᵥ s) with hz
  have hpz : phi ⬝ᵥ z = B0 := by
    rw [hz, dotProduct_add, dotProduct_smul, dotProduct_smul, hs0, hphifs]
    simp
  have hpfz : phi ⬝ᵥ (f *ᵥ z) = A0 - c * B0 := by
    rw [hz, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_add,
      dotProduct_smul, dotProduct_smul, hphifs, hffs]
    simp only [smul_eq_mul]
    ring
  refine ⟨⟨Lrank1 f c (v - z) E + Lrank1 f c s alpha,
    Submodule.add_mem _ (Lrank1_mem_commutant hq _ _) (Lrank1_mem_commutant hq _ _)⟩, ?_⟩
  have hfirst : (Lrank1 f c (v - z) E + Lrank1 f c s alpha) *ᵥ u = v := by
    rw [Matrix.add_mulVec, Lrank1_mulVec, Lrank1_mulVec, hEu, hEfu]
    rw [show (alpha ⬝ᵥ (f *ᵥ u) + c * (alpha ⬝ᵥ u)) = A0 from rfl]
    simp only [mul_zero, add_zero, one_smul, zero_smul, add_zero, ← hB0, ← hz]
    abel
  have hsecond : phi ᵥ* (Lrank1 f c (v - z) E + Lrank1 f c s alpha) = alpha := by
    rw [Matrix.vecMul_add, Lrank1_vecMul, Lrank1_vecMul, hs0, hphifs]
    have h1 : phi ⬝ᵥ (v - z) = 0 := by
      rw [dotProduct_sub, hpz, hcompat]; ring
    have h2 : phi ⬝ᵥ (f *ᵥ (v - z)) = 0 := by
      rw [Matrix.mulVec_sub, dotProduct_sub, hpfz, dotProduct_mulVec, hcompat1, hA0]
      ring
    rw [h1, h2]
    simp
  exact Prod.ext hfirst hsecond

/-- **Stage 3B.**  For an irreducible monic quadratic, every nonzero pair is extremal. -/
theorem pairAction_rank_irreducible_quadratic
    (hq : f * f + c • f + d • (1 : Matrix (Fin n) (Fin n) K) = 0)
    (hnoroot : ∀ x : K, x * x + c * x + d ≠ 0)
    {u phi : Vec K n} (hu : u ≠ 0) (hphi : phi ≠ 0) :
    finrank K ↥(LinearMap.range (pairAction f u phi)) = 2 * n - 2 := by
  obtain ⟨s, hs0, hs1⟩ :=
    exists_dot_zero_one hphi (no_left_eigenvector_of_no_root hq hnoroot hphi)
  have hker := finrank_ker_compatFun (K := K) (u := u) hphi
  have hwit : ∃ p ∈ LinearMap.ker (compatFun u phi), ell1 f u phi p ≠ 0 := by
    refine ⟨(s, 0), ?_, ?_⟩
    · show phi ⬝ᵥ s - (0 : Vec K n) ⬝ᵥ u = 0
      rw [hs0, zero_dotProduct, sub_zero]
    · show (phi ᵥ* f) ⬝ᵥ s - (0 : Vec K n) ⬝ᵥ (f *ᵥ u) ≠ 0
      rw [hs1, zero_dotProduct, sub_zero]
      exact one_ne_zero
  have hcut := finrank_inf_ker_add_one (LinearMap.ker (compatFun u phi)) (ell1 f u phi) hwit
  rw [range_pairAction_irreducible hq hnoroot hu hphi]
  omega

end Q655
