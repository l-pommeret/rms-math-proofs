import RMS.Q655Irred

/-!
# Q655 — Stage 3C: the repeated-root (square-zero) case

Here `f = a • 1 + N` with `N ≠ 0` and `N * N = 0`; since `commutant f = commutant N` we work
directly with `N`.  We determine exactly when the pair action at `(u, φ)` has maximal rank
`2 * n - 2`.
-/

namespace Q655

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

/-! ## Rank helpers -/

lemma finrank_ker_mulVecLin_add_rank (A : Matrix (Fin n) (Fin n) K) :
    finrank K ↥(LinearMap.ker A.mulVecLin) + A.rank = n := by
  have := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  simp only [Matrix.rank, Module.finrank_pi, Fintype.card_fin] at *
  omega

/-- The left kernel `{α | α ᵥ* A = 0}`. -/
def leftKer (A : Matrix (Fin n) (Fin n) K) : Submodule K (Vec K n) :=
  LinearMap.ker (Aᵀ).mulVecLin

lemma mem_leftKer_iff {A : Matrix (Fin n) (Fin n) K} {alpha : Vec K n} :
    alpha ∈ leftKer A ↔ alpha ᵥ* A = 0 := by
  simp [leftKer, LinearMap.mem_ker, Matrix.mulVec_transpose]

lemma finrank_leftKer_add_rank (A : Matrix (Fin n) (Fin n) K) :
    finrank K ↥(leftKer A) + A.rank = n := by
  have := finrank_ker_mulVecLin_add_rank (Aᵀ)
  rw [Matrix.rank_transpose] at this
  exact this

/-- A matrix of rank at most one and nonzero is an outer product. -/
lemma isRankOneMat_of_rank_le_one {A : Matrix (Fin n) (Fin n) K} (hA : A ≠ 0)
    (h : A.rank ≤ 1) : IsRankOneMat A := by
  have h1 : A.rank = 1 := le_antisymm h (one_le_rank_of_ne_zero hA)
  have hfr : finrank K ↥(LinearMap.range A.mulVecLin) = 1 := h1
  obtain ⟨p, hp0, hpspan⟩ := finrank_eq_one_iff'.1 hfr
  set q : Vec K n := fun j =>
    (hpspan ⟨A *ᵥ (Pi.single j 1), ⟨Pi.single j 1, rfl⟩⟩).choose with hqdef
  have hcol : ∀ j : Fin n, A *ᵥ (Pi.single j 1) = q j • (p : Vec K n) := by
    intro j
    have := (hpspan ⟨A *ᵥ (Pi.single j 1), ⟨Pi.single j 1, rfl⟩⟩).choose_spec
    exact (congrArg Subtype.val this).symm
  have hentry : ∀ i j : Fin n, A i j = q j * (p : Vec K n) i := by
    intro i j
    have := congrFun (hcol j) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have hpne : (p : Vec K n) ≠ 0 := fun h => hp0 (Subtype.ext h)
  refine ⟨(p : Vec K n), q, hpne, ?_, ?_⟩
  · intro hq
    exact hA (by ext i j; rw [hentry i j, hq]; simp)
  · ext i j
    rw [hentry i j, outer_apply, mul_comm]

lemma rank_outer {p q : Vec K n} (hp : p ≠ 0) (hq : q ≠ 0) : (outer p q).rank = 1 := by
  have hrange : LinearMap.range (outer p q).mulVecLin = K ∙ p := by
    apply le_antisymm
    · rintro x ⟨w, rfl⟩
      exact Submodule.mem_span_singleton.2 ⟨q ⬝ᵥ w, by simp [Matrix.mulVecLin, outer_mulVec]⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      obtain ⟨w, hw⟩ := exists_dotProduct_eq_one hq
      exact ⟨w, by simp [Matrix.mulVecLin, outer_mulVec, hw]⟩
  rw [Matrix.rank, hrange, finrank_span_singleton hp]

lemma isRankOneMat_iff_rank_eq_one {A : Matrix (Fin n) (Fin n) K} :
    IsRankOneMat A ↔ A.rank = 1 := by
  constructor
  · rintro ⟨p, q, hp, hq, rfl⟩; exact rank_outer hp hq
  · intro h
    refine isRankOneMat_of_rank_le_one ?_ (le_of_eq h)
    intro h0
    rw [h0, Matrix.rank_zero] at h
    exact absurd h (by norm_num)

/-! ## Transpose duality for the pair action -/

lemma range_pairAction_transpose (f : Matrix (Fin n) (Fin n) K) (u phi : Vec K n) :
    LinearMap.range (pairAction fᵀ phi u) =
      Submodule.map (LinearEquiv.prodComm K (Vec K n) (Vec K n)).toLinearMap
        (LinearMap.range (pairAction f u phi)) := by
  apply le_antisymm
  · rintro _ ⟨⟨Y, hY⟩, rfl⟩
    have hYt : Yᵀ * f = f * Yᵀ := by
      have : Y * fᵀ = fᵀ * Y := hY
      have := congrArg Matrix.transpose this
      simpa [Matrix.transpose_mul] using this.symm
    refine ⟨(Y *ᵥ phi, u ᵥ* Y).swap, ⟨⟨Yᵀ, hYt⟩, ?_⟩, rfl⟩
    show (Yᵀ *ᵥ u, phi ᵥ* Yᵀ) = (u ᵥ* Y, Y *ᵥ phi)
    rw [Matrix.mulVec_transpose, Matrix.vecMul_transpose]
  · rintro _ ⟨_, ⟨⟨X, hX⟩, rfl⟩, rfl⟩
    have hXt : Xᵀ * fᵀ = fᵀ * Xᵀ := by
      have : X * f = f * X := hX
      have := congrArg Matrix.transpose this
      simpa [Matrix.transpose_mul] using this.symm
    refine ⟨⟨Xᵀ, hXt⟩, ?_⟩
    show (Xᵀ *ᵥ phi, u ᵥ* Xᵀ) = (phi ᵥ* X, X *ᵥ u)
    rw [Matrix.mulVec_transpose, Matrix.vecMul_transpose]

lemma finrank_range_pairAction_transpose (f : Matrix (Fin n) (Fin n) K) (u phi : Vec K n) :
    finrank K ↥(LinearMap.range (pairAction fᵀ phi u)) =
      finrank K ↥(LinearMap.range (pairAction f u phi)) := by
  rw [range_pairAction_transpose]
  exact LinearEquiv.finrank_map_eq _ _

/-! ## Generic upper bounds for the pair action -/

variable {f : Matrix (Fin n) (Fin n) K} {u phi : Vec K n}

lemma range_pairAction_le_prod (S T : Submodule K (Vec K n))
    (hS : ∀ X ∈ commutant f, X *ᵥ u ∈ S) (hT : ∀ X ∈ commutant f, phi ᵥ* X ∈ T) :
    LinearMap.range (pairAction f u phi) ≤ S.prod T := by
  rintro _ ⟨⟨X, hX⟩, rfl⟩
  exact ⟨hS X hX, hT X hX⟩

lemma finrank_range_pairAction_le_prod (S T : Submodule K (Vec K n))
    (hS : ∀ X ∈ commutant f, X *ᵥ u ∈ S) (hT : ∀ X ∈ commutant f, phi ᵥ* X ∈ T) :
    finrank K ↥(LinearMap.range (pairAction f u phi)) ≤ finrank K ↥S + finrank K ↥T := by
  have h := Submodule.finrank_mono (range_pairAction_le_prod S T hS hT)
  rwa [finrank_submodule_prod] at h

/-- Cutting by the compatibility functional saves one dimension. -/
lemma finrank_range_pairAction_lt_prod (S T : Submodule K (Vec K n))
    (hS : ∀ X ∈ commutant f, X *ᵥ u ∈ S) (hT : ∀ X ∈ commutant f, phi ᵥ* X ∈ T)
    (hc : ∃ p ∈ S.prod T, compatFun u phi p ≠ 0) :
    finrank K ↥(LinearMap.range (pairAction f u phi)) + 1 ≤ finrank K ↥S + finrank K ↥T := by
  have hle : LinearMap.range (pairAction f u phi) ≤ S.prod T ⊓ LinearMap.ker (compatFun u phi) := by
    refine le_inf (range_pairAction_le_prod S T hS hT) ?_
    rintro _ ⟨⟨X, hX⟩, rfl⟩
    have hXf : X * f = f * X := hX
    show phi ⬝ᵥ (X *ᵥ u) - (phi ᵥ* X) ⬝ᵥ u = 0
    rw [sub_eq_zero, dotProduct_mulVec]
  have h1 := Submodule.finrank_mono hle
  have h2 := finrank_inf_ker_add_one (S.prod T) (compatFun u phi) hc
  rw [finrank_submodule_prod] at h2
  omega

/-- With `u ≠ 0`, the first component alone already gives a bound with a saving of one. -/
lemma finrank_range_pairAction_le_left (hu : u ≠ 0) (S : Submodule K (Vec K n))
    (hS : ∀ X ∈ commutant f, X *ᵥ u ∈ S) :
    finrank K ↥(LinearMap.range (pairAction f u phi)) + 1 ≤ finrank K ↥S + n := by
  obtain ⟨alpha, halpha⟩ := exists_dotProduct_eq_one hu
  have h := finrank_range_pairAction_lt_prod (f := f) (u := u) (phi := phi) S ⊤ hS
    (fun X _ => Submodule.mem_top) ⟨(0, alpha), ⟨S.zero_mem, Submodule.mem_top⟩, ?_⟩
  · rw [finrank_top, Module.finrank_pi, Fintype.card_fin] at h
    exact h
  · show phi ⬝ᵥ (0 : Vec K n) - alpha ⬝ᵥ u ≠ 0
    rw [dotProduct_zero, dotProduct_comm, halpha]
    norm_num

lemma finrank_range_pairAction_le_right (hphi : phi ≠ 0) (T : Submodule K (Vec K n))
    (hT : ∀ X ∈ commutant f, phi ᵥ* X ∈ T) :
    finrank K ↥(LinearMap.range (pairAction f u phi)) + 1 ≤ n + finrank K ↥T := by
  obtain ⟨v, hv⟩ := exists_dotProduct_eq_one hphi
  have h := finrank_range_pairAction_lt_prod (f := f) (u := u) (phi := phi) ⊤ T
    (fun X _ => Submodule.mem_top) hT ⟨(v, 0), ⟨Submodule.mem_top, T.zero_mem⟩, ?_⟩
  · rw [finrank_top, Module.finrank_pi, Fintype.card_fin] at h
    exact h
  · show phi ⬝ᵥ v - (0 : Vec K n) ⬝ᵥ u ≠ 0
    rw [zero_dotProduct, sub_zero, hv]
    norm_num

/-! ## Invariant subspaces of a commutant -/

lemma mulVec_mem_ker_mulVecLin {N : Matrix (Fin n) (Fin n) K} (hNu : N *ᵥ u = 0) :
    ∀ X ∈ commutant N, X *ᵥ u ∈ LinearMap.ker N.mulVecLin := by
  intro X hX
  have hXN : X * N = N * X := hX
  show N *ᵥ (X *ᵥ u) = 0
  rw [Matrix.mulVec_mulVec, ← hXN, ← Matrix.mulVec_mulVec, hNu, Matrix.mulVec_zero]

lemma vecMul_mem_leftKer {N : Matrix (Fin n) (Fin n) K} (hphiN : phi ᵥ* N = 0) :
    ∀ X ∈ commutant N, phi ᵥ* X ∈ leftKer N := by
  intro X hX
  have hXN : X * N = N * X := hX
  rw [mem_leftKer_iff, Matrix.vecMul_vecMul, hXN, ← Matrix.vecMul_vecMul, hphiN,
    Matrix.zero_vecMul]

lemma mulVec_mem_range_mulVecLin {N : Matrix (Fin n) (Fin n) K} {x : Vec K n}
    (hx : N *ᵥ x = u) :
    ∀ X ∈ commutant N, X *ᵥ u ∈ LinearMap.range N.mulVecLin := by
  intro X hX
  have hXN : X * N = N * X := hX
  refine ⟨X *ᵥ x, ?_⟩
  show N *ᵥ (X *ᵥ x) = X *ᵥ u
  rw [Matrix.mulVec_mulVec, ← hXN, ← Matrix.mulVec_mulVec, hx]

/-- The row space of `N`, i.e. `{y ᵥ* N}`. -/
lemma vecMul_mem_rowSpace {N : Matrix (Fin n) (Fin n) K} {y : Vec K n}
    (hy : y ᵥ* N = phi) :
    ∀ X ∈ commutant N, phi ᵥ* X ∈ LinearMap.range (Nᵀ).mulVecLin := by
  intro X hX
  have hXN : X * N = N * X := hX
  refine ⟨y ᵥ* X, ?_⟩
  show Nᵀ *ᵥ (y ᵥ* X) = phi ᵥ* X
  rw [Matrix.mulVec_transpose, Matrix.vecMul_vecMul, hXN, ← Matrix.vecMul_vecMul, hy]

/-! ## Upper bounds in the degenerate configurations -/

lemma bad_of_rank_two_left {N : Matrix (Fin n) (Fin n) K} (hu : u ≠ 0) (hNu : N *ᵥ u = 0)
    (hk : 2 ≤ N.rank) :
    finrank K ↥(LinearMap.range (pairAction N u phi)) + 3 ≤ 2 * n := by
  have h : finrank K ↥(LinearMap.range (pairAction N u phi)) + 1 ≤
      finrank K ↥(LinearMap.ker N.mulVecLin) + n :=
    finrank_range_pairAction_le_left (f := N) (phi := phi) hu _ (mulVec_mem_ker_mulVecLin hNu)
  have h2 : finrank K ↥(LinearMap.ker N.mulVecLin) + N.rank = n :=
    finrank_ker_mulVecLin_add_rank N
  omega

lemma bad_of_rank_two_right {N : Matrix (Fin n) (Fin n) K} (hphi : phi ≠ 0)
    (hphiN : phi ᵥ* N = 0) (hk : 2 ≤ N.rank) :
    finrank K ↥(LinearMap.range (pairAction N u phi)) + 3 ≤ 2 * n := by
  have h : finrank K ↥(LinearMap.range (pairAction N u phi)) + 1 ≤ n + finrank K ↥(leftKer N) :=
    finrank_range_pairAction_le_right (f := N) (u := u) hphi _ (vecMul_mem_leftKer hphiN)
  have h2 : finrank K ↥(leftKer N) + N.rank = n := finrank_leftKer_add_rank N
  omega

lemma bad_of_mem_range {N : Matrix (Fin n) (Fin n) K} (hn : 3 ≤ n) (hu : u ≠ 0)
    (hk : N.rank = 1) (hx : ∃ x, N *ᵥ x = u) :
    finrank K ↥(LinearMap.range (pairAction N u phi)) + 3 ≤ 2 * n := by
  obtain ⟨x, hx⟩ := hx
  have h : finrank K ↥(LinearMap.range (pairAction N u phi)) + 1 ≤
      finrank K ↥(LinearMap.range N.mulVecLin) + n :=
    finrank_range_pairAction_le_left (f := N) (phi := phi) hu _ (mulVec_mem_range_mulVecLin hx)
  have h2 : finrank K ↥(LinearMap.range N.mulVecLin) = 1 := hk
  omega

lemma bad_of_mem_rowSpace {N : Matrix (Fin n) (Fin n) K} (hn : 3 ≤ n) (hphi : phi ≠ 0)
    (hk : N.rank = 1) (hy : ∃ y, y ᵥ* N = phi) :
    finrank K ↥(LinearMap.range (pairAction N u phi)) + 3 ≤ 2 * n := by
  obtain ⟨y, hy⟩ := hy
  have h : finrank K ↥(LinearMap.range (pairAction N u phi)) + 1 ≤
      n + finrank K ↥(LinearMap.range (Nᵀ).mulVecLin) :=
    finrank_range_pairAction_le_right (f := N) (u := u) hphi _ (vecMul_mem_rowSpace hy)
  have h2 : finrank K ↥(LinearMap.range (Nᵀ).mulVecLin) = 1 := by
    show (Nᵀ).rank = 1
    rw [Matrix.rank_transpose]; exact hk
  omega

/-- Both actions degenerate: `N u = 0` and `φ N = 0`. -/
lemma bad_of_both_zero {N : Matrix (Fin n) (Fin n) K} (hn : 3 ≤ n) (hN0 : N ≠ 0)
    (hu : u ≠ 0) (hphi : phi ≠ 0) (hNu : N *ᵥ u = 0) (hphiN : phi ᵥ* N = 0) :
    finrank K ↥(LinearMap.range (pairAction N u phi)) + 3 ≤ 2 * n := by
  rcases le_or_gt 2 N.rank with hk | hk
  · exact bad_of_rank_two_left hu hNu hk
  have hk1 : N.rank = 1 := le_antisymm (by omega) (one_le_rank_of_ne_zero hN0)
  obtain ⟨p, q, hp, hq, rfl⟩ := isRankOneMat_iff_rank_eq_one.2 hk1
  by_cases hlam : ∃ lam : K, phi = lam • q
  · obtain ⟨lam, rfl⟩ := hlam
    obtain ⟨t, ht⟩ := exists_dotProduct_eq_one hp
    refine bad_of_mem_rowSpace hn hphi hk1 ⟨lam • t, ?_⟩
    rw [vecMul_outer, smul_dotProduct, dotProduct_comm, ht, smul_eq_mul, mul_one]
  · push_neg at hlam
    obtain ⟨v, hqv, hpv⟩ := exists_dot_zero_one hq hlam
    have hv0 : outer p q *ᵥ v = 0 := by rw [outer_mulVec, hqv, zero_smul]
    have h : finrank K ↥(LinearMap.range (pairAction (outer p q) u phi)) + 1 ≤
        finrank K ↥(LinearMap.ker (outer p q).mulVecLin) + finrank K ↥(leftKer (outer p q)) :=
      finrank_range_pairAction_lt_prod (f := outer p q) (u := u) (phi := phi)
        (LinearMap.ker (outer p q).mulVecLin) (leftKer (outer p q))
        (mulVec_mem_ker_mulVecLin hNu) (vecMul_mem_leftKer hphiN)
        ⟨(v, 0), ⟨hv0, (leftKer (outer p q)).zero_mem⟩, by
          show phi ⬝ᵥ v - (0 : Vec K n) ⬝ᵥ u ≠ 0
          rw [zero_dotProduct, sub_zero, hpv]
          norm_num⟩
    have h1 : finrank K ↥(LinearMap.ker (outer p q).mulVecLin) + (outer p q).rank = n :=
      finrank_ker_mulVecLin_add_rank _
    have h2 : finrank K ↥(leftKer (outer p q)) + (outer p q).rank = n :=
      finrank_leftKer_add_rank _
    omega

/-! ## The extremal cases -/

/-- If the range of the pair action is all of the two obvious constraints, the rank is
maximal. -/
lemma finrank_range_eq_of_kers_le (hphi : phi ≠ 0)
    (hle : LinearMap.ker (compatFun u phi) ⊓ LinearMap.ker (ell1 f u phi) ≤
      LinearMap.range (pairAction f u phi))
    (hwit : ∃ p ∈ LinearMap.ker (compatFun u phi), ell1 f u phi p ≠ 0) :
    finrank K ↥(LinearMap.range (pairAction f u phi)) = 2 * n - 2 := by
  have heq := le_antisymm (range_pairAction_le_kers f u phi) hle
  have hker : finrank K ↥(LinearMap.ker (compatFun u phi)) + 1 = 2 * n :=
    finrank_ker_compatFun hphi
  have hcut : finrank K ↥(LinearMap.ker (compatFun u phi) ⊓ LinearMap.ker (ell1 f u phi)) + 1 =
      finrank K ↥(LinearMap.ker (compatFun u phi)) :=
    finrank_inf_ker_add_one _ _ hwit
  rw [heq]
  omega

section SquareZero

variable {N : Matrix (Fin n) (Fin n) K}

lemma squareZero_quad (hN2 : N * N = 0) :
    N * N + (0 : K) • N + (0 : K) • (1 : Matrix (Fin n) (Fin n) K) = 0 := by
  rw [hN2]; module

lemma mulVec_indep_of_squareZero (hN2 : N * N = 0) (hNu : N *ᵥ u ≠ 0) (lam : K) :
    N *ᵥ u ≠ lam • u := by
  intro h
  have h2 : N *ᵥ (N *ᵥ u) = 0 := by
    rw [Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]
  rw [h, Matrix.mulVec_smul, h] at h2
  rcases smul_eq_zero.1 h2 with h3 | h3
  · rw [h3, zero_smul] at h; exact hNu h
  · exact hNu (h.trans h3)

lemma vecMul_indep_of_squareZero (hN2 : N * N = 0) (hphiN : phi ᵥ* N ≠ 0) (lam : K) :
    phi ᵥ* N ≠ lam • phi := by
  intro h
  have h2 : (phi ᵥ* N) ᵥ* N = 0 := by
    rw [Matrix.vecMul_vecMul, hN2, Matrix.vecMul_zero]
  rw [h, Matrix.smul_vecMul, h] at h2
  rcases smul_eq_zero.1 h2 with h3 | h3
  · rw [h3, zero_smul] at h; exact hphiN h
  · exact hphiN (h.trans h3)

/-- **Case 1**: both actions are nondegenerate. -/
theorem pairAction_rank_squareZero_case1 (hN2 : N * N = 0)
    (hNu : N *ᵥ u ≠ 0) (hphiN : phi ᵥ* N ≠ 0) :
    finrank K ↥(LinearMap.range (pairAction N u phi)) = 2 * n - 2 := by
  have hu : u ≠ 0 := by
    intro h; rw [h, Matrix.mulVec_zero] at hNu; exact hNu rfl
  have hphi : phi ≠ 0 := by
    intro h; rw [h, Matrix.zero_vecMul] at hphiN; exact hphiN rfl
  obtain ⟨B0, hB0u, hB0Nu⟩ :=
    exists_dot_zero_one hu (mulVec_indep_of_squareZero hN2 hNu)
  obtain ⟨a0, ha0phi, ha0N⟩ :=
    exists_dot_zero_one hphi (vecMul_indep_of_squareZero hN2 hphiN)
  -- `hB0u : u ⬝ᵥ B0 = 0`, `hB0Nu : (N *ᵥ u) ⬝ᵥ B0 = 1`
  have hB0u' : B0 ⬝ᵥ u = 0 := by rw [dotProduct_comm]; exact hB0u
  have hB0Nu' : B0 ⬝ᵥ (N *ᵥ u) = 1 := by rw [dotProduct_comm]; exact hB0Nu
  have ha0N' : phi ⬝ᵥ (N *ᵥ a0) = 1 := by rw [dotProduct_mulVec]; exact ha0N
  refine finrank_range_eq_of_kers_le hphi ?_ ⟨(a0, 0), ?_, ?_⟩
  · rintro ⟨v, alpha⟩ ⟨hc0, hc1⟩
    have hcompat : phi ⬝ᵥ v = alpha ⬝ᵥ u := by
      have h : phi ⬝ᵥ v - alpha ⬝ᵥ u = 0 := hc0
      linear_combination h
    have hcompat1 : phi ⬝ᵥ (N *ᵥ v) = alpha ⬝ᵥ (N *ᵥ u) := by
      have h : (phi ᵥ* N) ⬝ᵥ v - alpha ⬝ᵥ (N *ᵥ u) = 0 := hc1
      rw [dotProduct_mulVec]
      linear_combination h
    set beta : Vec K n :=
      alpha - (phi ⬝ᵥ v) • (B0 ᵥ* N) - (phi ⬝ᵥ (N *ᵥ v)) • B0 with hbeta
    have e1 : (B0 ᵥ* N) ⬝ᵥ u = 1 := (dotProduct_mulVec B0 N u).symm.trans hB0Nu'
    have e0 : (B0 ᵥ* N) ⬝ᵥ (N *ᵥ u) = 0 := by
      rw [← dotProduct_mulVec, Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec, dotProduct_zero]
    have hbu : beta ⬝ᵥ u = 0 := by
      simp only [hbeta, sub_dotProduct, smul_dotProduct, smul_eq_mul, e1, hB0u']
      linear_combination -hcompat
    have hbNu : beta ⬝ᵥ (N *ᵥ u) = 0 := by
      simp only [hbeta, sub_dotProduct, smul_dotProduct, smul_eq_mul, e0, hB0Nu']
      linear_combination -hcompat1
    refine ⟨⟨Lrank1 N 0 v B0 + Lrank1 N 0 a0 beta,
      Submodule.add_mem _ (Lrank1_mem_commutant (squareZero_quad hN2) _ _)
        (Lrank1_mem_commutant (squareZero_quad hN2) _ _)⟩, ?_⟩
    have hfirst : (Lrank1 N 0 v B0 + Lrank1 N 0 a0 beta) *ᵥ u = v := by
      rw [Matrix.add_mulVec, Lrank1_mulVec, Lrank1_mulVec, hB0Nu', hB0u', hbu, hbNu]
      simp
    have hsecond : phi ᵥ* (Lrank1 N 0 v B0 + Lrank1 N 0 a0 beta) = alpha := by
      rw [Matrix.vecMul_add, Lrank1_vecMul, Lrank1_vecMul, ha0phi, ha0N', hbeta]
      module
    exact Prod.ext hfirst hsecond
  · show phi ⬝ᵥ a0 - (0 : Vec K n) ⬝ᵥ u = 0
    rw [ha0phi, zero_dotProduct, sub_zero]
  · show (phi ᵥ* N) ⬝ᵥ a0 - (0 : Vec K n) ⬝ᵥ (N *ᵥ u) ≠ 0
    rw [ha0N, zero_dotProduct, sub_zero]
    norm_num

lemma outer_mul_outer (p q p' q' : Vec K n) :
    outer p q * outer p' q' = (q ⬝ᵥ p') • outer p q' := by
  rw [outer_mul, vecMul_outer, outer_smul_right]

/-- **Case 2**: `N u = 0`, `φ N ≠ 0`, `N` of rank one and `u ∉ range N`. -/
theorem pairAction_rank_squareZero_case2 (hN2 : N * N = 0)
    (hrank1 : IsRankOneMat N) (hu : u ≠ 0)
    (hNu : N *ᵥ u = 0) (hphiN : phi ᵥ* N ≠ 0) (hnr : ¬ ∃ x, N *ᵥ x = u) :
    finrank K ↥(LinearMap.range (pairAction N u phi)) = 2 * n - 2 := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hrank1
  have hN0 : outer p q ≠ (0 : Matrix (Fin n) (Fin n) K) := by
    rw [ne_eq, outer_eq_zero_iff]; push_neg; exact ⟨hp, hq⟩
  -- basic consequences
  have hqp : q ⬝ᵥ p = 0 := by
    by_contra hc
    apply hN0
    have : (q ⬝ᵥ p) • outer p q = 0 := by rw [← outer_mul_outer, hN2]
    rcases smul_eq_zero.1 this with h | h
    · exact absurd h hc
    · exact h
  have hqu : q ⬝ᵥ u = 0 := by
    have := hNu
    rw [outer_mulVec] at this
    rcases smul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hp
  have hphip : phi ⬝ᵥ p ≠ 0 := by
    intro h
    apply hphiN
    rw [vecMul_outer, h, zero_smul]
  have hphi : phi ≠ 0 := by
    intro h; rw [h] at hphip; simp at hphip
  have hupindep : ∀ lam : K, u ≠ lam • p := by
    intro lam h
    obtain ⟨t, ht⟩ := exists_dotProduct_eq_one hq
    exact hnr ⟨lam • t, by rw [outer_mulVec, dotProduct_smul, ht, smul_eq_mul, mul_one, ← h]⟩
  have hphiqindep : ∀ lam : K, phi ≠ lam • q := by
    intro lam h
    apply hphip
    rw [h, smul_dotProduct, hqp, smul_eq_mul, mul_zero]
  obtain ⟨e, hep, heu⟩ := exists_dot_zero_one hp hupindep
  obtain ⟨w, hqw, hphiw⟩ := exists_dot_zero_one hq hphiqindep
  -- `hep : p ⬝ᵥ e = 0`, `heu : u ⬝ᵥ e = 1`, `hqw : q ⬝ᵥ w = 0`, `hphiw : phi ⬝ᵥ w = 1`
  have hep' : e ⬝ᵥ p = 0 := by rw [dotProduct_comm]; exact hep
  have heu' : e ⬝ᵥ u = 1 := by rw [dotProduct_comm]; exact heu
  refine finrank_range_eq_of_kers_le hphi ?_ ?_
  · rintro ⟨v, alpha⟩ ⟨hc0, hc1⟩
    have hcompat : phi ⬝ᵥ v = alpha ⬝ᵥ u := by
      have h : phi ⬝ᵥ v - alpha ⬝ᵥ u = 0 := hc0
      linear_combination h
    have hqv : q ⬝ᵥ v = 0 := by
      have h : (phi ᵥ* outer p q) ⬝ᵥ v - alpha ⬝ᵥ (outer p q *ᵥ u) = 0 := hc1
      rw [vecMul_outer, outer_mulVec, hqu, zero_smul, dotProduct_zero, sub_zero,
        smul_dotProduct, smul_eq_mul] at h
      rcases mul_eq_zero.1 h with h1 | h1
      · exact absurd h1 hphip
      · exact h1
    set c : K := (alpha ⬝ᵥ p) / (phi ⬝ᵥ p) with hc
    have hcp : c * (phi ⬝ᵥ p) = alpha ⬝ᵥ p := by
      rw [hc]; field_simp
    set v' : Vec K n := v - c • u with hv'
    set alpha' : Vec K n := alpha - c • phi with halpha'
    set gamma : Vec K n := alpha' - (phi ⬝ᵥ v') • e with hgamma
    have halphap : alpha' ⬝ᵥ p = 0 := by
      rw [halpha', sub_dotProduct, smul_dotProduct, smul_eq_mul, hcp, sub_self]
    have hgammap : gamma ⬝ᵥ p = 0 := by
      rw [hgamma, sub_dotProduct, halphap, smul_dotProduct, smul_eq_mul, hep', mul_zero,
        sub_zero]
    have hqv' : q ⬝ᵥ v' = 0 := by
      rw [hv', dotProduct_sub, hqv, dotProduct_smul, hqu, smul_eq_mul, mul_zero, sub_zero]
    have hphiv' : phi ⬝ᵥ v' = alpha' ⬝ᵥ u := by
      rw [hv', halpha', dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
        hcompat]
    have hgammau : gamma ⬝ᵥ u = 0 := by
      rw [hgamma, sub_dotProduct, smul_dotProduct, smul_eq_mul, heu', mul_one, hphiv',
        sub_self]
    set X : Matrix (Fin n) (Fin n) K :=
      c • (1 : Matrix (Fin n) (Fin n) K) + outer v' e + outer w gamma with hX
    have hXp : X *ᵥ p = c • p := by
      rw [hX, Matrix.add_mulVec, Matrix.add_mulVec, outer_mulVec, outer_mulVec, hep',
        hgammap, zero_smul, zero_smul, add_zero, add_zero, smul_mulVec, Matrix.one_mulVec]
    have hqX : q ᵥ* X = c • q := by
      rw [hX, Matrix.vecMul_add, Matrix.vecMul_add, vecMul_outer, vecMul_outer, hqv',
        hqw, zero_smul, zero_smul, add_zero, add_zero, Matrix.vecMul_smul, Matrix.vecMul_one]
    have hXmem : X ∈ commutant (outer p q) := by
      rw [mem_commutant_iff, mul_outer, outer_mul, hXp, hqX, outer_smul_left, outer_smul_right]
    refine ⟨⟨X, hXmem⟩, ?_⟩
    have hfirst : X *ᵥ u = v := by
      rw [hX, Matrix.add_mulVec, Matrix.add_mulVec, outer_mulVec, outer_mulVec, heu',
        hgammau, zero_smul, add_zero, one_smul, smul_mulVec, Matrix.one_mulVec, hv']
      abel
    have hsecond : phi ᵥ* X = alpha := by
      rw [hX, Matrix.vecMul_add, Matrix.vecMul_add, vecMul_outer, vecMul_outer, hphiw,
        one_smul, Matrix.vecMul_smul, Matrix.vecMul_one, hgamma, halpha']
      abel
    exact Prod.ext hfirst hsecond
  · obtain ⟨t, ht⟩ := exists_dotProduct_eq_one hq
    obtain ⟨alpha0, halpha0⟩ := exists_dotProduct_eq_one hu
    refine ⟨(t, (phi ⬝ᵥ t) • alpha0), ?_, ?_⟩
    · show phi ⬝ᵥ t - ((phi ⬝ᵥ t) • alpha0) ⬝ᵥ u = 0
      rw [smul_dotProduct, smul_eq_mul, dotProduct_comm alpha0 u, halpha0, mul_one, sub_self]
    · show (phi ᵥ* outer p q) ⬝ᵥ t - ((phi ⬝ᵥ t) • alpha0) ⬝ᵥ (outer p q *ᵥ u) ≠ 0
      rw [vecMul_outer, outer_mulVec, hqu, zero_smul, dotProduct_zero, sub_zero,
        smul_dotProduct, smul_eq_mul, ht, mul_one]
      exact hphip

lemma outer_transpose (p q : Vec K n) : (outer p q)ᵀ = outer q p := by
  ext i j; simp [outer, mul_comm]

/-- **Case 3**: the transpose-dual of case 2. -/
theorem pairAction_rank_squareZero_case3 (hN2 : N * N = 0)
    (hrank1 : IsRankOneMat N) (hphi : phi ≠ 0)
    (hNu : N *ᵥ u ≠ 0) (hphiN : phi ᵥ* N = 0)
    (hker : ∃ x, N *ᵥ x = 0 ∧ phi ⬝ᵥ x ≠ 0) :
    finrank K ↥(LinearMap.range (pairAction N u phi)) = 2 * n - 2 := by
  rw [← finrank_range_pairAction_transpose N u phi]
  have hN2' : Nᵀ * Nᵀ = 0 := by
    rw [← Matrix.transpose_mul, hN2, Matrix.transpose_zero]
  have hrank1' : IsRankOneMat (Nᵀ) := by
    obtain ⟨p, q, hp, hq, rfl⟩ := hrank1
    exact ⟨q, p, hq, hp, outer_transpose p q⟩
  have hNu' : Nᵀ *ᵥ phi = 0 := by rw [Matrix.mulVec_transpose]; exact hphiN
  have hphiN' : u ᵥ* Nᵀ ≠ 0 := by rw [Matrix.vecMul_transpose]; exact hNu
  have hnr' : ¬ ∃ x, Nᵀ *ᵥ x = phi := by
    rintro ⟨y, hy⟩
    rw [Matrix.mulVec_transpose] at hy
    obtain ⟨x, hx0, hx1⟩ := hker
    apply hx1
    rw [← hy, ← dotProduct_mulVec, hx0, dotProduct_zero]
  exact pairAction_rank_squareZero_case2 hN2' hrank1' hphi hNu' hphiN' hnr'

/-- **Stage 3C completion gate.**  The exact repeated-root criterion. -/
theorem pairAction_rank_squareZero_iff (hn : 3 ≤ n) (hN0 : N ≠ 0) (hN2 : N * N = 0)
    (hu : u ≠ 0) (hphi : phi ≠ 0) :
    finrank K ↥(LinearMap.range (pairAction N u phi)) = 2 * n - 2 ↔
      ((N *ᵥ u ≠ 0 ∧ phi ᵥ* N ≠ 0) ∨
       (N *ᵥ u = 0 ∧ phi ᵥ* N ≠ 0 ∧ IsRankOneMat N ∧ ¬ ∃ x, N *ᵥ x = u) ∨
       (N *ᵥ u ≠ 0 ∧ phi ᵥ* N = 0 ∧ IsRankOneMat N ∧
          ∃ x, N *ᵥ x = 0 ∧ phi ⬝ᵥ x ≠ 0)) := by
  constructor
  · intro hrank
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    have hbad : finrank K ↥(LinearMap.range (pairAction N u phi)) + 3 ≤ 2 * n := by
      by_cases hNu : N *ᵥ u = 0 <;> by_cases hphiN : phi ᵥ* N = 0
      · exact bad_of_both_zero hn hN0 hu hphi hNu hphiN
      · -- `N u = 0`, `φ N ≠ 0`
        rcases le_or_gt 2 N.rank with hk | hk
        · exact bad_of_rank_two_left hu hNu hk
        · have hk1 : N.rank = 1 := le_antisymm (by omega) (one_le_rank_of_ne_zero hN0)
          have hr1 : IsRankOneMat N := isRankOneMat_iff_rank_eq_one.2 hk1
          have hx := h2 hNu hphiN hr1
          exact bad_of_mem_range hn hu hk1 hx
      · -- `N u ≠ 0`, `φ N = 0`
        rcases le_or_gt 2 N.rank with hk | hk
        · exact bad_of_rank_two_right hphi hphiN hk
        · have hk1 : N.rank = 1 := le_antisymm (by omega) (one_le_rank_of_ne_zero hN0)
          have hr1 : IsRankOneMat N := isRankOneMat_iff_rank_eq_one.2 hk1
          have hx := h3 hNu hphiN hr1
          -- `φ` vanishes on `ker N`, hence lies in the row space
          obtain ⟨p, q, hp, hq, rfl⟩ := hr1
          have hdot : ∀ s : Vec K n, q ⬝ᵥ s = 0 → phi ⬝ᵥ s = 0 := by
            intro s hs
            exact hx s (by rw [outer_mulVec, hs, zero_smul])
          obtain ⟨lam, hlam⟩ := eq_smul_of_dot_zero_imp hq hdot
          obtain ⟨t, ht⟩ := exists_dotProduct_eq_one hp
          refine bad_of_mem_rowSpace hn hphi hk1 ⟨lam • t, ?_⟩
          rw [vecMul_outer, smul_dotProduct, dotProduct_comm, ht, smul_eq_mul, mul_one, hlam]
      · exact absurd (h1 hNu) hphiN
    omega
  · rintro (⟨hNu, hphiN⟩ | ⟨hNu, hphiN, hr1, hnr⟩ | ⟨hNu, hphiN, hr1, hker⟩)
    · exact pairAction_rank_squareZero_case1 hN2 hNu hphiN
    · exact pairAction_rank_squareZero_case2 hN2 hr1 hu hNu hphiN hnr
    · exact pairAction_rank_squareZero_case3 hN2 hr1 hphi hNu hphiN hker

end SquareZero

end Q655
