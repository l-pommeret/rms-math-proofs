import RMS.Q655Classification

/-!
# Q655 — Stage 3A: the split (idempotent) case

Here `f = a • 1 + (b - a) • P` with `P` an idempotent, `a ≠ b`.  We compute the exact rank of
the pair action of `f` at `(u, φ)`.
-/

namespace Q655

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

/-! ## Generalities -/

/-- The equivalence `↥(p.prod q) ≃ₗ ↥p × ↥q`. -/
noncomputable def submoduleProdEquiv {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (p : Submodule K M) (q : Submodule K N) :
    ↥(p.prod q) ≃ₗ[K] (↥p × ↥q) where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  left_inv := by intro x; rfl
  right_inv := by intro y; rfl

lemma finrank_submodule_prod {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [FiniteDimensional K M] [FiniteDimensional K N]
    (p : Submodule K M) (q : Submodule K N) :
    finrank K ↥(p.prod q) = finrank K ↥p + finrank K ↥q := by
  rw [(submoduleProdEquiv p q).finrank_eq, Module.finrank_prod]

/-- If a functional is nonzero somewhere on `S`, cutting `S` by its kernel drops the
dimension by exactly one. -/
lemma finrank_inf_ker_add_one {M : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (S : Submodule K M) (l : M →ₗ[K] K)
    (h : ∃ x ∈ S, l x ≠ 0) :
    finrank K ↥(S ⊓ LinearMap.ker l) + 1 = finrank K ↥S := by
  set T : ↥S →ₗ[K] K := l.domRestrict S with hT
  have hrange : LinearMap.range T = ⊤ := by
    obtain ⟨x, hxS, hx⟩ := h
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨(c / l x) • ⟨x, hxS⟩, ?_⟩
    simp only [hT, map_smul, LinearMap.domRestrict_apply, smul_eq_mul]
    field_simp
  have hker : LinearMap.ker T = Submodule.comap S.subtype (LinearMap.ker l) := by
    ext x; simp [hT, LinearMap.mem_ker]
  have := LinearMap.finrank_range_add_finrank_ker T
  rw [hrange, finrank_top, Module.finrank_self, hker,
    finrank_comap_subtype S (LinearMap.ker l)] at this
  omega

/-! ## Fixed spaces of an idempotent -/

/-- The fixed space of a matrix, realized as the range of its `mulVec` map. -/
def fixSpace (P : Matrix (Fin n) (Fin n) K) : Submodule K (Vec K n) :=
  LinearMap.range P.mulVecLin

lemma finrank_fixSpace (P : Matrix (Fin n) (Fin n) K) :
    finrank K ↥(fixSpace P) = P.rank := rfl

lemma mem_fixSpace_iff {P : Matrix (Fin n) (Fin n) K} (hP : P * P = P) {v : Vec K n} :
    v ∈ fixSpace P ↔ P *ᵥ v = v := by
  constructor
  · rintro ⟨w, rfl⟩
    show P *ᵥ (P *ᵥ w) = P *ᵥ w
    rw [Matrix.mulVec_mulVec, hP]
  · intro h; exact ⟨v, h⟩

lemma mulVec_mem_fixSpace (P : Matrix (Fin n) (Fin n) K) (v : Vec K n) :
    P *ᵥ v ∈ fixSpace P := ⟨v, rfl⟩

lemma transpose_idem {P : Matrix (Fin n) (Fin n) K} (hP : P * P = P) : Pᵀ * Pᵀ = Pᵀ := by
  rw [← Matrix.transpose_mul, hP]

lemma mem_fixSpace_transpose_iff {P : Matrix (Fin n) (Fin n) K} (hP : P * P = P)
    {alpha : Vec K n} : alpha ∈ fixSpace Pᵀ ↔ alpha ᵥ* P = alpha := by
  rw [mem_fixSpace_iff (transpose_idem hP), ← Matrix.mulVec_transpose]

lemma vecMul_mem_fixSpace_transpose (P : Matrix (Fin n) (Fin n) K) (alpha : Vec K n) :
    alpha ᵥ* P ∈ fixSpace Pᵀ := by
  rw [← Matrix.mulVec_transpose]; exact ⟨alpha, rfl⟩

lemma finrank_fixSpace_transpose (P : Matrix (Fin n) (Fin n) K) :
    finrank K ↥(fixSpace Pᵀ) = P.rank := by
  rw [finrank_fixSpace, Matrix.rank_transpose]

/-! ## The block map -/

/-- `Y ↦ (P (Y x), (ξ Y) P)`, whose range is the contribution of the `P`-block to the range
of the pair action. -/
def blockMap (P : Matrix (Fin n) (Fin n) K) (x xi : Vec K n) :
    Matrix (Fin n) (Fin n) K →ₗ[K] (Vec K n × Vec K n) where
  toFun Y := (P *ᵥ (Y *ᵥ x), (xi ᵥ* Y) ᵥ* P)
  map_add' Y Z := by
    simp [Matrix.add_mulVec, Matrix.vecMul_add, Matrix.mulVec_add, Matrix.add_vecMul]
  map_smul' c Y := by
    simp [smul_mulVec, vecMul_smul, Matrix.mulVec_smul, Prod.smul_mk, Matrix.smul_vecMul]

@[simp] lemma blockMap_apply (P : Matrix (Fin n) (Fin n) K) (x xi : Vec K n)
    (Y : Matrix (Fin n) (Fin n) K) :
    blockMap P x xi Y = (P *ᵥ (Y *ᵥ x), (xi ᵥ* Y) ᵥ* P) := rfl

lemma blockMap_range_le (P : Matrix (Fin n) (Fin n) K) (x xi : Vec K n) :
    LinearMap.range (blockMap P x xi) ≤ (fixSpace P).prod (fixSpace Pᵀ) := by
  rintro p ⟨Y, rfl⟩
  exact ⟨mulVec_mem_fixSpace P _, vecMul_mem_fixSpace_transpose P _⟩

/-- The exact range of the block map when both data are nonzero. -/
lemma blockMap_range_eq {P : Matrix (Fin n) (Fin n) K} (hP : P * P = P) {x xi : Vec K n}
    (hx : P *ᵥ x = x) (hxi : xi ᵥ* P = xi) (hx0 : x ≠ 0) (hxi0 : xi ≠ 0) :
    LinearMap.range (blockMap P x xi) =
      (fixSpace P).prod (fixSpace Pᵀ) ⊓ LinearMap.ker (compatFun x xi) := by
  apply le_antisymm
  · rintro p ⟨Y, rfl⟩
    refine ⟨blockMap_range_le P x xi ⟨Y, rfl⟩, ?_⟩
    show xi ⬝ᵥ (P *ᵥ (Y *ᵥ x)) - ((xi ᵥ* Y) ᵥ* P) ⬝ᵥ x = 0
    rw [sub_eq_zero]
    calc xi ⬝ᵥ (P *ᵥ (Y *ᵥ x)) = (xi ᵥ* P) ⬝ᵥ (Y *ᵥ x) := dotProduct_mulVec _ _ _
      _ = xi ⬝ᵥ (Y *ᵥ x) := by rw [hxi]
      _ = (xi ᵥ* Y) ⬝ᵥ x := dotProduct_mulVec _ _ _
      _ = (xi ᵥ* Y) ⬝ᵥ (P *ᵥ x) := by rw [hx]
      _ = ((xi ᵥ* Y) ᵥ* P) ⬝ᵥ x := dotProduct_mulVec _ _ _
  · rintro ⟨v, alpha⟩ ⟨⟨hv0, halpha0⟩, hcompat0⟩
    have hv : P *ᵥ v = v := (mem_fixSpace_iff hP).1 hv0
    have halpha : alpha ᵥ* P = alpha := (mem_fixSpace_transpose_iff hP).1 halpha0
    have hcompat : xi ⬝ᵥ v = alpha ⬝ᵥ x := by
      have : xi ⬝ᵥ v - alpha ⬝ᵥ x = 0 := hcompat0
      linear_combination this
    obtain ⟨s, hs⟩ := exists_dotProduct_eq_one hxi0
    obtain ⟨eta, heta0⟩ := exists_dotProduct_eq_one hx0
    have heta : eta ⬝ᵥ x = 1 := by rw [dotProduct_comm]; exact heta0
    refine ⟨outer v eta + outer s alpha - (alpha ⬝ᵥ x) • outer s eta, ?_⟩
    have h1 : (outer v eta + outer s alpha - (alpha ⬝ᵥ x) • outer s eta) *ᵥ x = v := by
      simp [Matrix.add_mulVec, Matrix.sub_mulVec, smul_mulVec, outer_mulVec, heta]
    have h2 : xi ᵥ* (outer v eta + outer s alpha - (alpha ⬝ᵥ x) • outer s eta) = alpha := by
      simp [Matrix.vecMul_add, Matrix.vecMul_sub, vecMul_smul, vecMul_outer, hs, hcompat]
    simp only [blockMap_apply, h1, h2, hv, halpha]

lemma blockMap_range_eq_of_xi_zero {P : Matrix (Fin n) (Fin n) K} (hP : P * P = P)
    {x : Vec K n} (hx : P *ᵥ x = x) (hx0 : x ≠ 0) :
    LinearMap.range (blockMap P x 0) = (fixSpace P).prod ⊥ := by
  apply le_antisymm
  · rintro p ⟨Y, rfl⟩
    exact ⟨mulVec_mem_fixSpace P _, by simp⟩
  · rintro ⟨v, alpha⟩ ⟨hv0, halpha0⟩
    have hv : P *ᵥ v = v := (mem_fixSpace_iff hP).1 hv0
    have halpha : alpha = 0 := halpha0
    subst halpha
    obtain ⟨eta, heta0⟩ := exists_dotProduct_eq_one hx0
    have heta : eta ⬝ᵥ x = 1 := by rw [dotProduct_comm]; exact heta0
    refine ⟨outer v eta, ?_⟩
    simp [outer_mulVec, heta, hv]

lemma blockMap_range_eq_of_x_zero (P : Matrix (Fin n) (Fin n) K)
    {xi : Vec K n} (hP : P * P = P) (hxi : xi ᵥ* P = xi) (hxi0 : xi ≠ 0) :
    LinearMap.range (blockMap P 0 xi) = (⊥ : Submodule K (Vec K n)).prod (fixSpace Pᵀ) := by
  apply le_antisymm
  · rintro p ⟨Y, rfl⟩
    exact ⟨by simp, vecMul_mem_fixSpace_transpose P _⟩
  · rintro ⟨v, alpha⟩ ⟨hv0, halpha0⟩
    have hv : v = 0 := hv0
    subst hv
    have halpha : alpha ᵥ* P = alpha := (mem_fixSpace_transpose_iff hP).1 halpha0
    obtain ⟨s, hs⟩ := exists_dotProduct_eq_one hxi0
    refine ⟨outer s alpha, ?_⟩
    simp [vecMul_outer, hs, halpha]

lemma blockMap_range_eq_bot (P : Matrix (Fin n) (Fin n) K) :
    LinearMap.range (blockMap P 0 (0 : Vec K n)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro p ⟨Y, rfl⟩
  simp [Prod.ext_iff]

/-! ## The exact dimension of the block range -/

/-- `BlockGood P u φ`: the `P`-block contributes the maximal possible amount. -/
def BlockGood (P : Matrix (Fin n) (Fin n) K) (u phi : Vec K n) : Prop :=
  (P.rank = 1 ∧ (P *ᵥ u ≠ 0 ∨ phi ᵥ* P ≠ 0)) ∨
    (2 ≤ P.rank ∧ P *ᵥ u ≠ 0 ∧ phi ᵥ* P ≠ 0)

lemma one_le_rank_of_ne_zero {P : Matrix (Fin n) (Fin n) K} (hP0 : P ≠ 0) : 1 ≤ P.rank := by
  rcases Nat.eq_zero_or_pos P.rank with h0 | hpos
  · exfalso
    have hbot : LinearMap.range P.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 h0
    refine hP0 (matrix_eq_zero_of_mulVec (fun w => ?_))
    have hw : P.mulVecLin w ∈ LinearMap.range P.mulVecLin := ⟨w, rfl⟩
    rw [hbot, Submodule.mem_bot] at hw
    exact hw
  · exact hpos

lemma finrank_blockRange_le_and_iff {P : Matrix (Fin n) (Fin n) K} (hP : P * P = P)
    (hP1 : 1 ≤ P.rank) (u phi : Vec K n) :
    finrank K ↥(LinearMap.range (blockMap P (P *ᵥ u) (phi ᵥ* P))) + 1 ≤ 2 * P.rank ∧
      (finrank K ↥(LinearMap.range (blockMap P (P *ᵥ u) (phi ᵥ* P))) + 1 = 2 * P.rank ↔
        BlockGood P u phi) := by
  set x := P *ᵥ u with hxdef
  set xi := phi ᵥ* P with hxidef
  have hx : P *ᵥ x = x := by
    simp only [hxdef, Matrix.mulVec_mulVec, hP]
  have hxi : xi ᵥ* P = xi := by
    simp only [hxidef, Matrix.vecMul_vecMul, hP]
  have hprod : finrank K ↥((fixSpace P).prod (fixSpace Pᵀ)) = 2 * P.rank := by
    rw [finrank_submodule_prod, finrank_fixSpace, finrank_fixSpace_transpose]
    ring
  by_cases hx0 : x = 0 <;> by_cases hxi0 : xi = 0
  · rw [hx0, hxi0, blockMap_range_eq_bot]
    simp only [finrank_bot]
    simp only [BlockGood, ← hxdef, ← hxidef, hx0, hxi0, ne_eq, not_true_eq_false, or_self,
      and_false, false_or, false_and, or_self, iff_false]
    omega
  · rw [hx0, blockMap_range_eq_of_x_zero P hP hxi hxi0, finrank_submodule_prod,
      finrank_bot, finrank_fixSpace_transpose]
    simp only [BlockGood, ← hxdef, ← hxidef, hx0, ne_eq, not_true_eq_false, hxi0, false_or,
      not_false_eq_true, or_true, and_true, false_and, and_false, or_false]
    omega
  · rw [hxi0, blockMap_range_eq_of_xi_zero hP hx hx0, finrank_submodule_prod,
      finrank_bot, finrank_fixSpace]
    simp only [BlockGood, ← hxdef, ← hxidef, hxi0, ne_eq, not_true_eq_false, hx0,
      not_false_eq_true, true_or, and_true, and_false, or_false]
    omega
  · rw [blockMap_range_eq hP hx hxi hx0 hxi0]
    have hne : ∃ p ∈ (fixSpace P).prod (fixSpace Pᵀ), compatFun x xi p ≠ 0 := by
      obtain ⟨v0, hv0⟩ : ∃ v0 : Vec K n, xi ⬝ᵥ v0 ≠ 0 := by
        by_contra hc
        push_neg at hc
        refine hxi0 (funext fun j => ?_)
        have := hc (Pi.single j 1)
        simpa [dotProduct, Pi.single_apply, Finset.sum_ite_eq'] using this
      refine ⟨(P *ᵥ v0, 0), ⟨mulVec_mem_fixSpace P v0, Submodule.zero_mem _⟩, ?_⟩
      simp only [compatFun_apply, zero_dotProduct, sub_zero]
      rwa [dotProduct_mulVec, hxi]
    have hcut := finrank_inf_ker_add_one ((fixSpace P).prod (fixSpace Pᵀ)) (compatFun x xi) hne
    have hgood : BlockGood P u phi := by
      rcases Nat.lt_or_ge P.rank 2 with h | h
      · exact Or.inl ⟨by omega, Or.inl hx0⟩
      · exact Or.inr ⟨h, hx0, hxi0⟩
    refine ⟨by omega, ?_⟩
    simp only [hgood, iff_true]
    omega

/-! ## Assembling the split case -/

lemma commutant_smul_of_ne_zero {c : K} (hc : c ≠ 0) (A : Matrix (Fin n) (Fin n) K) :
    commutant (c • A) = commutant A := by
  ext X
  simp only [mem_commutant_iff, Matrix.mul_smul, Matrix.smul_mul]
  constructor
  · intro h; exact smul_right_injective _ hc h
  · intro h; rw [h]

lemma range_pairAction_congr {f g : Matrix (Fin n) (Fin n) K} (h : commutant f = commutant g)
    (u phi : Vec K n) :
    LinearMap.range (pairAction f u phi) = LinearMap.range (pairAction g u phi) := by
  apply le_antisymm
  · rintro p ⟨⟨X, hX⟩, rfl⟩
    exact ⟨⟨X, h ▸ hX⟩, rfl⟩
  · rintro p ⟨⟨X, hX⟩, rfl⟩
    exact ⟨⟨X, h ▸ hX⟩, rfl⟩

lemma commutant_one_sub (P : Matrix (Fin n) (Fin n) K) :
    commutant (1 - P) = commutant P := by
  ext X
  simp only [mem_commutant_iff, Matrix.mul_sub, Matrix.sub_mul, mul_one, one_mul]
  constructor <;> intro h <;> [exact (sub_right_injective h).symm ▸ rfl; skip]
  · rw [h]

lemma idem_decomp {P X : Matrix (Fin n) (Fin n) K} (hP : P * P = P)
    (hX : X ∈ commutant P) : P * X * P + (1 - P) * X * (1 - P) = X := by
  have hXP : X * P = P * X := hX
  have key : P * X * P = P * X := by
    rw [Matrix.mul_assoc, hXP, ← Matrix.mul_assoc, hP]
  have h1 : (1 - P) * X * (1 - P) = X - P * X - X * P + P * X * P := by
    noncomm_ring
  rw [h1, key, hXP]
  abel

lemma blockMap_eq_pairAction (P : Matrix (Fin n) (Fin n) K) (u phi : Vec K n)
    (Y : Matrix (Fin n) (Fin n) K) :
    blockMap P (P *ᵥ u) (phi ᵥ* P) Y = ((P * Y * P) *ᵥ u, phi ᵥ* (P * Y * P)) := by
  simp only [blockMap_apply, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

lemma mul_self_mem_commutant (P Y : Matrix (Fin n) (Fin n) K) (hP : P * P = P) :
    P * Y * P ∈ commutant P := by
  simp only [mem_commutant_iff]
  rw [Matrix.mul_assoc, hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP]

lemma range_pairAction_split {P : Matrix (Fin n) (Fin n) K} (hP : P * P = P) (u phi : Vec K n) :
    LinearMap.range (pairAction P u phi) =
      LinearMap.range (blockMap P (P *ᵥ u) (phi ᵥ* P)) ⊔
        LinearMap.range (blockMap (1 - P) ((1 - P) *ᵥ u) (phi ᵥ* (1 - P))) := by
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    have : (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    rw [this, hP]; abel
  apply le_antisymm
  · rintro p ⟨⟨X, hX⟩, rfl⟩
    have hdec := idem_decomp hP hX
    have : pairAction P u phi ⟨X, hX⟩ =
        blockMap P (P *ᵥ u) (phi ᵥ* P) X +
          blockMap (1 - P) ((1 - P) *ᵥ u) (phi ᵥ* (1 - P)) X := by
      rw [blockMap_eq_pairAction, blockMap_eq_pairAction]
      simp only [pairAction_apply, Prod.mk_add_mk, ← Matrix.add_mulVec, ← Matrix.vecMul_add,
        hdec]
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨X, rfl⟩)
      (Submodule.mem_sup_right ⟨X, rfl⟩)
  · refine sup_le ?_ ?_
    · rintro p ⟨Y, rfl⟩
      refine ⟨⟨P * Y * P, mul_self_mem_commutant P Y hP⟩, ?_⟩
      rw [blockMap_eq_pairAction]
      rfl
    · rintro p ⟨Y, rfl⟩
      refine ⟨⟨(1 - P) * Y * (1 - P), ?_⟩, ?_⟩
      · rw [← commutant_one_sub]
        exact mul_self_mem_commutant (1 - P) Y hQ
      · rw [blockMap_eq_pairAction]
        rfl

lemma one_sub_idem {P : Matrix (Fin n) (Fin n) K} (hP : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  have h : (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
  rw [h, hP]; abel

lemma fixSpace_inf_one_sub {P : Matrix (Fin n) (Fin n) K} (hP : P * P = P) :
    fixSpace P ⊓ fixSpace (1 - P) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro v ⟨hv1, hv2⟩
  have h1 : P *ᵥ v = v := (mem_fixSpace_iff hP).1 hv1
  have h2 : (1 - P) *ᵥ v = v := (mem_fixSpace_iff (one_sub_idem hP)).1 hv2
  have h3 : P * (1 - P) = 0 := by
    have : P * (1 - P) = P - P * P := by noncomm_ring
    rw [this, hP]; abel
  have := congrArg (fun w => P *ᵥ w) h2
  simp only [Matrix.mulVec_mulVec, h3, Matrix.zero_mulVec, h1] at this
  exact this.symm

lemma fixSpace_sup_one_sub {P : Matrix (Fin n) (Fin n) K} (hP : P * P = P) :
    fixSpace P ⊔ fixSpace (1 - P) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v = P *ᵥ v + (1 - P) *ᵥ v := by
    rw [← Matrix.add_mulVec]
    simp
  rw [hv]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (mulVec_mem_fixSpace P v))
    (Submodule.mem_sup_right (mulVec_mem_fixSpace (1 - P) v))

lemma rank_add_rank_one_sub {P : Matrix (Fin n) (Fin n) K} (hP : P * P = P) :
    P.rank + (1 - P).rank = n := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (fixSpace P) (fixSpace (1 - P))
  rw [fixSpace_sup_one_sub hP, fixSpace_inf_one_sub hP, finrank_top, finrank_bot,
    finrank_fixSpace, finrank_fixSpace] at h
  simpa using h.symm

lemma prod_fix_inf_eq_bot {P : Matrix (Fin n) (Fin n) K} (hP : P * P = P) :
    ((fixSpace P).prod (fixSpace Pᵀ)) ⊓
      ((fixSpace (1 - P)).prod (fixSpace (1 - P)ᵀ)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro ⟨v, alpha⟩ ⟨⟨hv1, ha1⟩, ⟨hv2, ha2⟩⟩
  have hv : v = 0 := by
    have : v ∈ fixSpace P ⊓ fixSpace (1 - P) := ⟨hv1, hv2⟩
    rw [fixSpace_inf_one_sub hP] at this
    exact this
  have hT : (1 - P)ᵀ = 1 - Pᵀ := by simp [Matrix.transpose_sub]
  rw [hT] at ha2
  have ha : alpha = 0 := by
    have : alpha ∈ fixSpace Pᵀ ⊓ fixSpace (1 - Pᵀ) := ⟨ha1, ha2⟩
    rw [fixSpace_inf_one_sub (transpose_idem hP)] at this
    exact this
  simp [Prod.ext_iff, hv, ha]

/-- **Stage 3A.**  Exact rank of the pair action in the split case. -/
theorem pairAction_rank_split_iff {a b : K} (hab : a ≠ b)
    {P : Matrix (Fin n) (Fin n) K} (hP : P * P = P) (hP0 : P ≠ 0) (hP1 : P ≠ 1)
    {f : Matrix (Fin n) (Fin n) K} (hf : f = a • 1 + (b - a) • P) (u phi : Vec K n) :
    finrank K ↥(LinearMap.range (pairAction f u phi)) = 2 * n - 2 ↔
      (BlockGood P u phi ∧ BlockGood (1 - P) u phi) := by
  have hQ : (1 - P) * (1 - P) = 1 - P := one_sub_idem hP
  have hQ0 : (1 : Matrix (Fin n) (Fin n) K) - P ≠ 0 := by
    intro h
    exact hP1 (by linear_combination (norm := module) -h)
  have hrP : 1 ≤ P.rank := one_le_rank_of_ne_zero hP0
  have hrQ : 1 ≤ (1 - P).rank := one_le_rank_of_ne_zero hQ0
  have hsum : P.rank + (1 - P).rank = n := rank_add_rank_one_sub hP
  have hcom : commutant f = commutant P := by
    rw [hf, commutant_smul_one_add, commutant_smul_of_ne_zero (sub_ne_zero.2 (Ne.symm hab))]
  have hrange : LinearMap.range (pairAction f u phi) =
      LinearMap.range (blockMap P (P *ᵥ u) (phi ᵥ* P)) ⊔
        LinearMap.range (blockMap (1 - P) ((1 - P) *ᵥ u) (phi ᵥ* (1 - P))) := by
    rw [range_pairAction_congr hcom u phi, range_pairAction_split hP]
  have hdisj : LinearMap.range (blockMap P (P *ᵥ u) (phi ᵥ* P)) ⊓
      LinearMap.range (blockMap (1 - P) ((1 - P) *ᵥ u) (phi ᵥ* (1 - P))) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro p hp
    have h1 := blockMap_range_le P (P *ᵥ u) (phi ᵥ* P) hp.1
    have h2 := blockMap_range_le (1 - P) ((1 - P) *ᵥ u) (phi ᵥ* (1 - P)) hp.2
    have : p ∈ ((fixSpace P).prod (fixSpace Pᵀ)) ⊓
        ((fixSpace (1 - P)).prod (fixSpace (1 - P)ᵀ)) := ⟨h1, h2⟩
    rw [prod_fix_inf_eq_bot hP] at this
    exact this
  have hadd := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (blockMap P (P *ᵥ u) (phi ᵥ* P)))
    (LinearMap.range (blockMap (1 - P) ((1 - P) *ᵥ u) (phi ᵥ* (1 - P))))
  rw [hdisj, finrank_bot] at hadd
  obtain ⟨hleP, hiffP⟩ := finrank_blockRange_le_and_iff hP hrP u phi
  obtain ⟨hleQ, hiffQ⟩ := finrank_blockRange_le_and_iff hQ hrQ u phi
  rw [hrange]
  constructor
  · intro h
    exact ⟨hiffP.1 (by omega), hiffQ.1 (by omega)⟩
  · rintro ⟨g1, g2⟩
    have e1 := hiffP.2 g1
    have e2 := hiffQ.2 g2
    omega

end Q655
