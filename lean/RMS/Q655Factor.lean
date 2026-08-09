import RMS.Q655Ext

/-!
# Q655 — Stage 5C: rank factorisations and the centralizer exact sequence

Let `U` be an `n × p` matrix with a left inverse and `V` a `p × n` matrix with a right inverse,
so that `a = U * V` has rank `card p` and `b = V * U` is the matrix of `a` restricted to its
image.  For a subspace `Y` of matrices commuting with `b` we consider

  `interSpace U V Y = {X | ∃ Z ∈ Y, X * U = U * Z ∧ V * X = Z * V}`,

and prove `dim (interSpace U V Y) = (n - card p) ^ 2 + dim Y`.

Two instances are used later:

* `Y = C(V * U)` gives `interSpace U V Y = C(U * V)`, i.e. the rank factorisation formula
  `dim C(a) = (n - rank a) ^ 2 + dim C(b)` (Stage 5C);
* a block-diagonal `Y` gives the common centralizer of two matrices in generic position
  (Stage 5D).

As a first application we prove the centralizer estimate of Stage 5B:
`dim C(a) ≤ n * e` when every eigenspace of `a` has dimension at most `e`.
-/

namespace Q655

open Matrix Module

variable {K : Type*} [Field K] {n d : ℕ} {p q : Type*} [Fintype p] [DecidableEq p]
  [Fintype q] [DecidableEq q]

/-! ## Matrix analogues of standard linear algebra facts -/

lemma toMatrix'_mulVecLin (L : (Fin d → K) →ₗ[K] (Fin n → K)) :
    (LinearMap.toMatrix' L).mulVecLin = L := by
  rw [show (LinearMap.toMatrix' L).mulVecLin = Matrix.toLin' (LinearMap.toMatrix' L) from rfl,
    Matrix.toLin'_toMatrix']

/-- Two matrices agreeing on all vectors are equal. -/
lemma matrix_ext_of_mulVec {m₁ m₂ : Type*} [Fintype m₂] [DecidableEq m₂]
    {M N : Matrix m₁ m₂ K} (h : ∀ x, M *ᵥ x = N *ᵥ x) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

/-- An injective matrix has a left inverse. -/
lemma exists_leftInv {p : Type*} [Fintype p] [DecidableEq p] {M : Matrix (Fin n) p K}
    (h : Function.Injective M.mulVecLin) :
    ∃ M' : Matrix p (Fin n) K, M' * M = 1 := by
  obtain ⟨g, hg⟩ := (M.mulVecLin).exists_leftInverse_of_injective (by rwa [LinearMap.ker_eq_bot])
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul]
  simpa [Matrix.toLin'_toMatrix'] using hg

/-- A surjective matrix has a right inverse. -/
lemma exists_rightInv {p : Type*} [Fintype p] [DecidableEq p] {M : Matrix p (Fin n) K}
    (h : Function.Surjective M.mulVecLin) :
    ∃ W : Matrix (Fin n) p K, M * W = 1 := by
  obtain ⟨g, hg⟩ := (M.mulVecLin).exists_rightInverse_of_surjective (by rwa [LinearMap.range_eq_top])
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul]
  simpa [Matrix.toLin'_toMatrix'] using hg

/-- A subspace of dimension `d` is the column space of an injective `n × d` matrix. -/
lemma exists_basis_matrix (S : Submodule K (Fin n → K)) (hd : finrank K ↥S = d) :
    ∃ M : Matrix (Fin n) (Fin d) K,
      Function.Injective M.mulVecLin ∧ LinearMap.range M.mulVecLin = S := by
  classical
  let b : Basis (Fin d) K ↥S := (Module.finBasis K ↥S).reindex (finCongr hd)
  let L : (Fin d → K) →ₗ[K] (Fin n → K) :=
    S.subtype ∘ₗ (b.equivFun.symm : (Fin d → K) →ₗ[K] ↥S)
  refine ⟨LinearMap.toMatrix' L, ?_, ?_⟩
  · rw [toMatrix'_mulVecLin]
    exact (Subtype.val_injective).comp (b.equivFun.symm.injective)
  · rw [toMatrix'_mulVecLin, LinearMap.range_comp]
    simp [LinearEquiv.range]

/-- If `M' * M = 1` then `M * M'` acts as the identity on the column space of `M`. -/
lemma mul_left_inv_mulVec {M : Matrix (Fin n) (Fin d) K} {M' : Matrix (Fin d) (Fin n) K}
    (hM : M' * M = 1) {v : Fin n → K} (hv : v ∈ LinearMap.range M.mulVecLin) :
    M *ᵥ (M' *ᵥ v) = v := by
  obtain ⟨y, rfl⟩ := hv
  rw [show M.mulVecLin y = M *ᵥ y from rfl,
    show M' *ᵥ (M *ᵥ y) = (M' * M) *ᵥ y from Matrix.mulVec_mulVec .., hM, Matrix.one_mulVec]

/-! ## The commutant for a general index type -/

/-- The commutant of a square matrix indexed by an arbitrary finite type. -/
def gcommutant (A : Matrix p p K) : Submodule K (Matrix p p K) where
  carrier := {X | X * A = A * X}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.add_mul, Matrix.mul_add, hx, hy]
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.smul_mul, Matrix.mul_smul, hx]

@[simp] lemma mem_gcommutant_iff {A X : Matrix p p K} : X ∈ gcommutant A ↔ X * A = A * X := Iff.rfl

lemma gcommutant_eq_commutant (f : Matrix (Fin n) (Fin n) K) : gcommutant f = commutant f := rfl

/-- The commutant dimension only depends on the matrix up to a relabelling of the index. -/
lemma finrank_gcommutant_reindex (e : p ≃ q) (A : Matrix p p K) :
    finrank K ↥(gcommutant (Matrix.reindex e e A)) = finrank K ↥(gcommutant A) := by
  classical
  set E := Matrix.reindexLinearEquiv K K e e with hE
  have hmul : ∀ M N : Matrix p p K, E (M * N) = E M * E N := by
    intro M N
    simpa [hE] using (Matrix.reindexLinearEquiv_mul K K e e e M N).symm
  have hmap : (gcommutant A).map (E : Matrix p p K →ₗ[K] Matrix q q K)
      = gcommutant (Matrix.reindex e e A) := by
    ext X
    constructor
    · rintro ⟨Z, hZ, rfl⟩
      show E Z * Matrix.reindex e e A = Matrix.reindex e e A * E Z
      have h : E Z * E A = E A * E Z := by rw [← hmul, ← hmul, hZ]
      simpa [hE] using h
    · intro hX
      refine ⟨E.symm X, ?_, by simp⟩
      show E.symm X * A = A * E.symm X
      have hX' : X * Matrix.reindex e e A = Matrix.reindex e e A * X := hX
      have hc := congrArg E.symm hX'
      have e1 : E.symm (X * Matrix.reindex e e A) = E.symm X * A := by
        have h2 := hmul (E.symm X) A
        simp only [LinearEquiv.apply_symm_apply] at h2
        rw [show Matrix.reindex e e A = E A from rfl, ← h2, LinearEquiv.symm_apply_apply]
      have e2 : E.symm (Matrix.reindex e e A * X) = A * E.symm X := by
        have h2 := hmul A (E.symm X)
        simp only [LinearEquiv.apply_symm_apply] at h2
        rw [show Matrix.reindex e e A = E A from rfl, ← h2, LinearEquiv.symm_apply_apply]
      rw [e1, e2] at hc
      exact hc
  rw [← hmap, LinearEquiv.finrank_map_eq]

/-! ## The intertwining space -/

/-- Matrices intertwining `U` and `V` through a multiplier taken from `Y`. -/
def interSpace (U : Matrix (Fin n) p K) (V : Matrix p (Fin n) K)
    (Y : Submodule K (Matrix p p K)) : Submodule K (Matrix (Fin n) (Fin n) K) where
  carrier := {X | ∃ Z ∈ Y, X * U = U * Z ∧ V * X = Z * V}
  add_mem' := by
    rintro x y ⟨Z, hZ, h1, h2⟩ ⟨Z', hZ', h1', h2'⟩
    exact ⟨Z + Z', Y.add_mem hZ hZ', by rw [Matrix.add_mul, Matrix.mul_add, h1, h1'],
      by rw [Matrix.mul_add, Matrix.add_mul, h2, h2']⟩
  zero_mem' := ⟨0, Y.zero_mem, by simp, by simp⟩
  smul_mem' := by
    rintro c x ⟨Z, hZ, h1, h2⟩
    exact ⟨c • Z, Y.smul_mem c hZ, by rw [Matrix.smul_mul, Matrix.mul_smul, h1],
      by rw [Matrix.mul_smul, Matrix.smul_mul, h2]⟩

lemma mem_interSpace_iff {U : Matrix (Fin n) p K} {V : Matrix p (Fin n) K}
    {Y : Submodule K (Matrix p p K)} {X : Matrix (Fin n) (Fin n) K} :
    X ∈ interSpace U V Y ↔ ∃ Z ∈ Y, X * U = U * Z ∧ V * X = Z * V := Iff.rfl

/-- Matrices killing the columns of `U` and landing in the kernel of `V`. -/
def zeroSpace (U : Matrix (Fin n) p K) (V : Matrix p (Fin n) K) :
    Submodule K (Matrix (Fin n) (Fin n) K) where
  carrier := {X | X * U = 0 ∧ V * X = 0}
  add_mem' := by
    rintro x y ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨by rw [Matrix.add_mul, h1, h1', add_zero], by rw [Matrix.mul_add, h2, h2', add_zero]⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := by
    rintro c x ⟨h1, h2⟩
    exact ⟨by rw [Matrix.smul_mul, h1, smul_zero], by rw [Matrix.mul_smul, h2, smul_zero]⟩

lemma mem_zeroSpace_iff {U : Matrix (Fin n) p K} {V : Matrix p (Fin n) K}
    {X : Matrix (Fin n) (Fin n) K} : X ∈ zeroSpace U V ↔ X * U = 0 ∧ V * X = 0 := Iff.rfl

/-- The dimension of the "corner" space. -/
lemma finrank_zeroSpace {U : Matrix (Fin n) p K} {V : Matrix p (Fin n) K}
    {U' : Matrix p (Fin n) K} {W : Matrix (Fin n) p K} (hU : U' * U = 1) (hW : V * W = 1) :
    finrank K ↥(zeroSpace U V) = (n - Fintype.card p) ^ 2 := by
  classical
  set m := Fintype.card p with hm
  -- `U` is injective and `V` is surjective
  have hUinj : Function.Injective U.mulVecLin := by
    intro x y hxy
    have : U' *ᵥ (U *ᵥ x) = U' *ᵥ (U *ᵥ y) := by
      simpa [Matrix.mulVecLin] using congrArg (fun v => U' *ᵥ v) hxy
    simpa [Matrix.mulVec_mulVec, hU] using this
  have hVsurj : Function.Surjective V.mulVecLin := by
    intro y
    exact ⟨W *ᵥ y, by simpa [Matrix.mulVecLin, Matrix.mulVec_mulVec, hW] using rfl⟩
  have hrankU : U.rank = m := by
    have : finrank K ↥(LinearMap.range U.mulVecLin) = finrank K (p → K) :=
      LinearMap.finrank_range_of_inj hUinj
    simpa [Matrix.rank, Module.finrank_pi, hm] using this
  have hrankV : V.rank = m := by
    have htop : LinearMap.range V.mulVecLin = ⊤ := LinearMap.range_eq_top.2 hVsurj
    have h5 : finrank K ↥(LinearMap.range V.mulVecLin) = finrank K (p → K) := by
      rw [htop]; exact finrank_top K (p → K)
    simpa [Matrix.rank, Module.finrank_pi, hm] using h5
  have hmn : m ≤ n := by
    have := Matrix.rank_le_card_width U
    have h2 := Matrix.rank_le_card_height U
    simp only [Fintype.card_fin] at h2
    omega
  -- the two kernels
  have hkerV : finrank K ↥(LinearMap.ker V.mulVecLin) = n - m := by
    have := LinearMap.finrank_range_add_finrank_ker V.mulVecLin
    rw [show finrank K (Fin n → K) = n by simp] at this
    have h4 : V.rank = finrank K ↥(LinearMap.range V.mulVecLin) := rfl
    omega
  have hkerU : finrank K ↥(LinearMap.ker Uᵀ.mulVecLin) = n - m := by
    have := LinearMap.finrank_range_add_finrank_ker Uᵀ.mulVecLin
    rw [show finrank K (Fin n → K) = n by simp] at this
    have h4 : Uᵀ.rank = finrank K ↥(LinearMap.range Uᵀ.mulVecLin) := rfl
    rw [Matrix.rank_transpose] at h4
    omega
  obtain ⟨Sm, hSinj, hSrange⟩ := exists_basis_matrix (LinearMap.ker V.mulVecLin) hkerV
  obtain ⟨Sm', hSm'⟩ := exists_leftInv hSinj
  obtain ⟨Tm, hTinj, hTrange⟩ := exists_basis_matrix (LinearMap.ker Uᵀ.mulVecLin) hkerU
  obtain ⟨Tm', hTm'⟩ := exists_leftInv hTinj
  set T : Matrix (Fin (n - m)) (Fin n) K := Tmᵀ with hT
  set T' : Matrix (Fin n) (Fin (n - m)) K := Tm'ᵀ with hT'
  have hTT' : T * T' = 1 := by
    rw [hT, hT', ← Matrix.transpose_mul, hTm', Matrix.transpose_one]
  have hVS : V * Sm = 0 := by
    refine matrix_ext_of_mulVec fun x => ?_
    have hx : Sm *ᵥ x ∈ LinearMap.ker V.mulVecLin := by
      rw [← hSrange]; exact ⟨x, rfl⟩
    have h5 : V *ᵥ (Sm *ᵥ x) = 0 := hx
    rw [Matrix.mulVec_mulVec] at h5
    rw [h5, Matrix.zero_mulVec]
  have hTU : T * U = 0 := by
    have hUT : Uᵀ * Tm = 0 := by
      refine matrix_ext_of_mulVec fun x => ?_
      have hx : Tm *ᵥ x ∈ LinearMap.ker Uᵀ.mulVecLin := by
        rw [← hTrange]; exact ⟨x, rfl⟩
      have h5 : Uᵀ *ᵥ (Tm *ᵥ x) = 0 := hx
      rw [Matrix.mulVec_mulVec] at h5
      rw [h5, Matrix.zero_mulVec]
    have h6 := congrArg Matrix.transpose hUT
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at h6
    exact h6
  -- the isomorphism `Z ↦ Sm * Z * T`
  set phi : Matrix (Fin (n - m)) (Fin (n - m)) K →ₗ[K] Matrix (Fin n) (Fin n) K :=
    { toFun := fun Z => Sm * Z * T
      map_add' := by intro Z Z'; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c Z; simp [Matrix.mul_smul, Matrix.smul_mul] } with hphi
  have hretract : ∀ Z0 : Matrix (Fin (n - m)) (Fin (n - m)) K, Sm' * (Sm * Z0 * T) * T' = Z0 := by
    intro Z0
    calc Sm' * (Sm * Z0 * T) * T' = ((Sm' * Sm) * Z0) * (T * T') := by
          simp [Matrix.mul_assoc]
      _ = Z0 := by rw [hSm', hTT', Matrix.one_mul, Matrix.mul_one]
  have hphi_inj : Function.Injective phi := by
    intro Z Z' h
    have h' : Sm * Z * T = Sm * Z' * T := h
    have h2 := congrArg (fun M => Sm' * M * T') h'
    simp only at h2
    rw [hretract, hretract] at h2
    exact h2
  have hrange : LinearMap.range phi = zeroSpace U V := by
    ext X
    constructor
    · rintro ⟨Z, rfl⟩
      refine ⟨?_, ?_⟩
      · show Sm * Z * T * U = 0
        rw [Matrix.mul_assoc, hTU, Matrix.mul_zero]
      · show V * (Sm * Z * T) = 0
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hVS, Matrix.zero_mul, Matrix.zero_mul]
    · rintro ⟨h1, h2⟩
      refine ⟨Sm' * X * T', ?_⟩
      show Sm * (Sm' * X * T') * T = X
      have hA : Sm * (Sm' * X) = X := by
        refine matrix_ext_of_mulVec fun x => ?_
        have hx : X *ᵥ x ∈ LinearMap.range Sm.mulVecLin := by
          rw [hSrange]
          show V *ᵥ (X *ᵥ x) = 0
          rw [Matrix.mulVec_mulVec, h2, Matrix.zero_mulVec]
        have h7 := mul_left_inv_mulVec hSm' hx
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        exact h7
      have hB : X * (T' * T) = X := by
        have hXT : Tm * (Tm' * Xᵀ) = Xᵀ := by
          refine matrix_ext_of_mulVec fun x => ?_
          have hx : Xᵀ *ᵥ x ∈ LinearMap.range Tm.mulVecLin := by
            rw [hTrange]
            show Uᵀ *ᵥ (Xᵀ *ᵥ x) = 0
            rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, h1, Matrix.transpose_zero,
              Matrix.zero_mulVec]
          have h7 := mul_left_inv_mulVec hTm' hx
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
          exact h7
        have h8 := congrArg Matrix.transpose hXT
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h8
        rw [hT, hT', ← Matrix.mul_assoc]
        exact h8
      calc Sm * (Sm' * X * T') * T = (Sm * (Sm' * X)) * (T' * T) := by
            simp [Matrix.mul_assoc]
        _ = X * (T' * T) := by rw [hA]
        _ = X := hB
  have : finrank K ↥(zeroSpace U V) = finrank K (Matrix (Fin (n - m)) (Fin (n - m)) K) := by
    rw [← hrange, LinearMap.finrank_range_of_inj hphi_inj]
  rw [this]
  simp [Module.finrank_matrix, sq]

/-- **The exact sequence of Stage 5C/5D.**  The intertwining space is an extension of `Y` by the
space of maps killing the image of `U` and landing in the kernel of `V`. -/
theorem finrank_interSpace {U : Matrix (Fin n) p K} {V : Matrix p (Fin n) K}
    {U' : Matrix p (Fin n) K} {W : Matrix (Fin n) p K}
    (hU : U' * U = 1) (hW : V * W = 1) (Y : Submodule K (Matrix p p K))
    (hY : ∀ Z ∈ Y, Z * (V * U) = (V * U) * Z) :
    finrank K ↥(interSpace U V Y) = (n - Fintype.card p) ^ 2 + finrank K ↥Y := by
  classical
  have hwit : ∀ (X : Matrix (Fin n) (Fin n) K) (Z : Matrix p p K), X * U = U * Z →
      U' * X * U = Z := by
    intro X Z h
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  set Theta : ↥(interSpace U V Y) →ₗ[K] Matrix p p K :=
    { toFun := fun X => U' * (X : Matrix (Fin n) (Fin n) K) * U
      map_add' := by intro X X'; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c X; simp [Matrix.mul_smul, Matrix.smul_mul] } with hTheta
  -- the range is exactly `Y`
  have hrange : LinearMap.range Theta = Y := by
    ext Z
    constructor
    · rintro ⟨X, rfl⟩
      obtain ⟨Z', hZ', h1, h2⟩ := X.2
      have : Theta X = Z' := hwit _ _ h1
      rw [this]
      exact hZ'
    · intro hZ
      refine ⟨⟨W * Z * V + (U * Z - W * Z * (V * U)) * U', ?_⟩, ?_⟩
      · refine ⟨Z, hZ, ?_, ?_⟩
        · have e : (W * Z * V + (U * Z - W * Z * (V * U)) * U') * U
              = W * Z * (V * U) + (U * Z - W * Z * (V * U)) * (U' * U) := by
            simp [Matrix.add_mul, Matrix.mul_assoc]
          rw [e, hU, Matrix.mul_one]
          abel
        · have e : V * (W * Z * V + (U * Z - W * Z * (V * U)) * U')
              = (V * W) * Z * V + ((V * U) * Z - (V * W) * Z * (V * U)) * U' := by
            simp [Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
          rw [e, hW, Matrix.one_mul, ← hY Z hZ, sub_self, Matrix.zero_mul, add_zero]
      · refine hwit _ _ ?_
        have e : (W * Z * V + (U * Z - W * Z * (V * U)) * U') * U
            = W * Z * (V * U) + (U * Z - W * Z * (V * U)) * (U' * U) := by
          simp [Matrix.add_mul, Matrix.mul_assoc]
        rw [e, hU, Matrix.mul_one]
        abel
  -- the kernel is the corner space
  have hle : zeroSpace U V ≤ interSpace U V Y := by
    rintro X ⟨h1, h2⟩
    exact ⟨0, Y.zero_mem, by rw [h1, Matrix.mul_zero], by rw [h2, Matrix.zero_mul]⟩
  have hkereq : LinearMap.ker Theta
      = Submodule.comap (interSpace U V Y).subtype (zeroSpace U V) := by
    ext X
    constructor
    · intro hX
      obtain ⟨Z, hZ, h1, h2⟩ := X.2
      have hZ0 : Z = 0 := by rw [← hwit _ Z h1]; exact hX
      refine ⟨?_, ?_⟩
      · show (X : Matrix (Fin n) (Fin n) K) * U = 0
        rw [h1, hZ0, Matrix.mul_zero]
      · show V * (X : Matrix (Fin n) (Fin n) K) = 0
        rw [h2, hZ0, Matrix.zero_mul]
    · intro hX
      have h1 : (X : Matrix (Fin n) (Fin n) K) * U = 0 := hX.1
      show U' * (X : Matrix (Fin n) (Fin n) K) * U = 0
      rw [Matrix.mul_assoc, h1, Matrix.mul_zero]
  have hkerrank : finrank K ↥(LinearMap.ker Theta) = (n - Fintype.card p) ^ 2 := by
    rw [hkereq]
    rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)]
    exact finrank_zeroSpace hU hW
  have hrn := LinearMap.finrank_range_add_finrank_ker Theta
  rw [hrange, hkerrank] at hrn
  omega

/-! ## Stage 5C proper -/

/-- For a rank factorisation, the commutant of `U * V` is an intertwining space. -/
theorem commutant_eq_interSpace {U : Matrix (Fin n) p K} {V : Matrix p (Fin n) K}
    {U' : Matrix p (Fin n) K} {W : Matrix (Fin n) p K} (hU : U' * U = 1) (hW : V * W = 1) :
    commutant (U * V) = interSpace U V (gcommutant (V * U)) := by
  ext X
  constructor
  · intro hX
    have hX' : X * (U * V) = (U * V) * X := hX
    -- `Z := V * X * W` is the multiplier
    have hb : X * U = U * (V * X * W) := by
      have := congrArg (fun M => M * W) hX'
      simp only [Matrix.mul_assoc] at this
      rw [show V * (X * W) = V * X * W by rw [Matrix.mul_assoc]] at this
      rw [show X * (U * (V * W)) = X * U by rw [hW, Matrix.mul_one]] at this
      exact this
    have hc : V * X = (V * X * W) * V := by
      have h2 := congrArg (fun M => U' * M) hX'
      simp only [← Matrix.mul_assoc] at h2
      rw [show U' * X * U * V = (U' * (X * U)) * V by simp [Matrix.mul_assoc]] at h2
      rw [hb] at h2
      simp only [← Matrix.mul_assoc, hU, Matrix.one_mul] at h2
      exact h2.symm
    refine ⟨V * X * W, ?_, hb, hc⟩
    show (V * X * W) * (V * U) = (V * U) * (V * X * W)
    have e1 : (V * X * W) * (V * U) = ((V * X * W) * V) * U := (Matrix.mul_assoc _ _ _).symm
    have e2 : (V * X) * U = V * (X * U) := Matrix.mul_assoc _ _ _
    have e3 : (V * U) * (V * X * W) = V * (U * (V * X * W)) := Matrix.mul_assoc _ _ _
    rw [e1, ← hc, e2, hb, e3]
  · rintro ⟨Z, -, h1, h2⟩
    show X * (U * V) = (U * V) * X
    rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, ← h2, ← Matrix.mul_assoc]

/-- **Stage 5C.**  `dim C(U V) = (n - r) ^ 2 + dim C(V U)` for a rank factorisation. -/
theorem finrank_commutant_factor {U : Matrix (Fin n) p K} {V : Matrix p (Fin n) K}
    {U' : Matrix p (Fin n) K} {W : Matrix (Fin n) p K} (hU : U' * U = 1) (hW : V * W = 1) :
    finrank K ↥(commutant (U * V)) =
      (n - Fintype.card p) ^ 2 + finrank K ↥(gcommutant (V * U)) := by
  rw [commutant_eq_interSpace hU hW]
  exact finrank_interSpace hU hW _ fun Z hZ => hZ

/-- Every matrix admits a rank factorisation through `Fin (rank a)`. -/
theorem exists_rank_factorization (a : Matrix (Fin n) (Fin n) K) :
    ∃ (U : Matrix (Fin n) (Fin a.rank) K) (V : Matrix (Fin a.rank) (Fin n) K)
      (U' : Matrix (Fin a.rank) (Fin n) K) (W : Matrix (Fin n) (Fin a.rank) K),
      a = U * V ∧ U' * U = 1 ∧ V * W = 1 := by
  classical
  obtain ⟨U, hUinj, hUrange⟩ :=
    exists_basis_matrix (LinearMap.range a.mulVecLin) (d := a.rank) rfl
  obtain ⟨U', hU'⟩ := exists_leftInv hUinj
  have hfac : a = U * (U' * a) := by
    refine (matrix_ext_of_mulVec fun x => ?_).symm
    rw [show (U * (U' * a)) *ᵥ x = U *ᵥ (U' *ᵥ (a *ᵥ x)) by
      simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]]
    exact mul_left_inv_mulVec hU' (by rw [hUrange]; exact ⟨x, rfl⟩)
  have hVsurj : Function.Surjective (U' * a).mulVecLin := by
    have h1 : a.rank ≤ (U' * a).rank := by
      conv_lhs => rw [hfac]
      exact Matrix.rank_mul_le_right U (U' * a)
    have h2 : finrank K ↑(LinearMap.range (U' * a).mulVecLin) = finrank K (Fin a.rank → K) := by
      have h3 : (U' * a).rank ≤ a.rank := by
        simpa using Matrix.rank_le_card_height (U' * a)
      have h4 : (U' * a).rank = finrank K ↑(LinearMap.range (U' * a).mulVecLin) := rfl
      simp only [Module.finrank_pi, Fintype.card_fin]
      omega
    rw [← LinearMap.range_eq_top]
    exact Submodule.eq_top_of_finrank_eq h2
  obtain ⟨W, hW⟩ := exists_rightInv hVsurj
  exact ⟨U, U' * a, U', W, hfac, hU', hW⟩

/-! ## Stage 5B: the centralizer estimate from the largest eigenspace -/

/-- A scalar shift does not change the commutant. -/
lemma commutant_sub_smul_one_eq (a : Matrix (Fin n) (Fin n) K) (lam : K) :
    commutant (a - lam • (1 : Matrix (Fin n) (Fin n) K)) = commutant a := by
  ext X
  simp only [mem_commutant_iff, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.one_mul, sub_left_inj]

/-- **Stage 5B.**  If every eigenspace of `a` has dimension at most `e`, then
`dim C(a) ≤ n * e`. -/
theorem finrank_commutant_le_mul [IsAlgClosed K] {e : ℕ} :
    ∀ (m : ℕ) (a : Matrix (Fin m) (Fin m) K),
      (∀ lam : K,
        finrank K ↥(LinearMap.ker (a - lam • (1 : Matrix (Fin m) (Fin m) K)).mulVecLin) ≤ e) →
      finrank K ↥(commutant a) ≤ m * e := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro a h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h0 : finrank K ↥(commutant a) ≤ finrank K (Matrix (Fin 0) (Fin 0) K) :=
        Submodule.finrank_le _
      have h1 : finrank K (Matrix (Fin 0) (Fin 0) K) = 0 := by simp [Module.finrank_matrix]
      simp only [Nat.zero_mul]
      omega
    · haveI : Inhabited (Fin m) := ⟨⟨0, hm⟩⟩
      haveI : Nontrivial (Fin m → K) := Pi.nontrivial
      obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue (Matrix.mulVecLin a)
      obtain ⟨v, hv, hv0⟩ := hlam.exists_hasEigenvector
      set b := a - lam • (1 : Matrix (Fin m) (Fin m) K) with hb
      have hav : a *ᵥ v = lam • v := by simpa [Module.End.mem_eigenspace_iff] using hv
      have hbv : b *ᵥ v = 0 := by
        simp [hb, Matrix.sub_mulVec, hav, Matrix.smul_mulVec, Matrix.one_mulVec]
      have hne : LinearMap.ker b.mulVecLin ≠ ⊥ := by
        intro hcon
        have hmem : v ∈ LinearMap.ker b.mulVecLin := hbv
        rw [hcon] at hmem
        exact hv0 (by simpa using hmem)
      have hkpos : finrank K ↥(LinearMap.ker b.mulVecLin) ≠ 0 := fun hz =>
        hne (Submodule.finrank_eq_zero.mp hz)
      have hrn := finrank_ker_mulVecLin_add_rank b
      have hble : finrank K ↥(LinearMap.ker b.mulVecLin) ≤ e := h lam
      have hrlt : b.rank < m := by omega
      obtain ⟨r, U, V, U', W, hr, hfac, hU, hW⟩ :
          ∃ (r : ℕ) (U : Matrix (Fin m) (Fin r) K) (V : Matrix (Fin r) (Fin m) K)
            (U' : Matrix (Fin r) (Fin m) K) (W : Matrix (Fin m) (Fin r) K),
            r = b.rank ∧ b = U * V ∧ U' * U = 1 ∧ V * W = 1 := by
        obtain ⟨U, V, U', W, hfac, hU, hW⟩ := exists_rank_factorization b
        exact ⟨b.rank, U, V, U', W, rfl, hfac, hU, hW⟩
      have hUinj : Function.Injective U.mulVecLin := by
        intro x y hxy
        have hxy' : U *ᵥ x = U *ᵥ y := hxy
        have := congrArg (fun w => U' *ᵥ w) hxy'
        simpa [Matrix.mulVec_mulVec, hU] using this
      have hVU : ∀ mu : K, finrank K ↥(LinearMap.ker
          ((V * U) - mu • (1 : Matrix (Fin r) (Fin r) K)).mulVecLin) ≤ e := by
        intro mu
        set S := LinearMap.ker ((V * U) - mu • (1 : Matrix (Fin r) (Fin r) K)).mulVecLin
          with hS
        set T := LinearMap.ker (b - mu • (1 : Matrix (Fin m) (Fin m) K)).mulVecLin with hT
        have hmap : S.map U.mulVecLin ≤ T := by
          rintro _ ⟨x, hx, rfl⟩
          have hx0 : ((V * U) - mu • (1 : Matrix (Fin r) (Fin r) K)) *ᵥ x = 0 := hx
          have hx' : (V * U) *ᵥ x = mu • x := by
            have := hx0
            rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
            exact this
          show (b - mu • (1 : Matrix (Fin m) (Fin m) K)) *ᵥ (U.mulVecLin x) = 0
          have hUx : U.mulVecLin x = U *ᵥ x := rfl
          rw [hUx, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero, hfac]
          rw [show (U * V) *ᵥ (U *ᵥ x) = U *ᵥ ((V * U) *ᵥ x) by
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc], hx',
            Matrix.mulVec_smul]
        have hTle : finrank K ↥T ≤ e := by
          have hbmu : b - mu • (1 : Matrix (Fin m) (Fin m) K)
              = a - (lam + mu) • (1 : Matrix (Fin m) (Fin m) K) := by
            rw [hb, add_smul]; abel
          rw [hT, hbmu]
          exact h (lam + mu)
        calc finrank K ↥S = finrank K ↥(S.map U.mulVecLin) :=
              (Submodule.equivMapOfInjective _ hUinj S).finrank_eq
          _ ≤ finrank K ↥T := Submodule.finrank_mono hmap
          _ ≤ e := hTle
      have hIH := IH r (by omega) (V * U) hVU
      have key := finrank_commutant_factor (n := m) (U := U) (V := V) hU hW
      rw [Fintype.card_fin] at key
      have hcomm : finrank K ↥(commutant a) = (m - r) ^ 2 + finrank K ↥(commutant (V * U)) := by
        rw [← commutant_sub_smul_one_eq a lam, ← hb, hfac, key, gcommutant_eq_commutant]
      have hkle : m - r ≤ e := by omega
      have hsq : (m - r) ^ 2 ≤ (m - r) * e := by
        rw [sq]; exact Nat.mul_le_mul_left _ hkle
      have hsum : (m - r) * e + r * e = m * e := by
        rw [← Nat.add_mul]; congr 1; omega
      omega

end Q655
