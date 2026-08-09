import RMS.Q655

/-!
# Q655 — equality classification (continuation)

This file extends `RequestProject.Main` (which contains the already verified maximum theorem
`Q655.isGreatest_finrank_commutant_sup`) with the machinery needed for the *equality*
classification.
-/

namespace Q655

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

/-! ## Basic linear algebra helpers -/

section Helpers

variable {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- `finrank` of a preimage submodule. -/
lemma finrank_comap_eq [FiniteDimensional K M] (T : M →ₗ[K] N) (S : Submodule K N) :
    finrank K ↥(S.comap T) = finrank K ↥(LinearMap.ker T) +
      finrank K ↥(S ⊓ LinearMap.range T) := by
  classical
  set P : Submodule K M := S.comap T with hP
  set T' : ↥P →ₗ[K] N := T.domRestrict P with hT'
  have hrange : LinearMap.range T' = S ⊓ LinearMap.range T := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      exact ⟨x.2, ⟨x.1, rfl⟩⟩
    · rintro y ⟨hyS, x, rfl⟩
      exact ⟨⟨x, hyS⟩, rfl⟩
  have hkerle : LinearMap.ker T ≤ P := by
    intro x hx
    simp only [hP, Submodule.mem_comap, LinearMap.mem_ker.1 hx]
    exact S.zero_mem
  have hker : LinearMap.ker T' = Submodule.comap P.subtype (LinearMap.ker T) := by
    ext x; simp [hT', LinearMap.mem_ker]
  have h2 : finrank K ↥(LinearMap.ker T') = finrank K ↥(LinearMap.ker T) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe hkerle).finrank_eq
  have := LinearMap.finrank_range_add_finrank_ker T'
  rw [hrange, h2] at this
  omega

end Helpers

/-! ## Vectors, outer products, rank one -/

/-- Coordinate space. -/
abbrev Vec (K : Type*) (n : ℕ) := Fin n → K

/-- The outer product `u ⊗ φ`. -/
def outer (u phi : Vec K n) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => u i * phi j

@[simp] lemma outer_apply (u phi : Vec K n) (i j : Fin n) : outer u phi i j = u i * phi j := rfl

/-- `A` is a rank one matrix. -/
def IsRankOneMat (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ u phi : Vec K n, u ≠ 0 ∧ phi ≠ 0 ∧ A = outer u phi

/-- `A` is a scalar matrix plus a rank one matrix. -/
def IsScalarPlusRankOne (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ (a : K) (R : Matrix (Fin n) (Fin n) K), IsRankOneMat R ∧ A = a • 1 + R

lemma mul_outer (X : Matrix (Fin n) (Fin n) K) (u phi : Vec K n) :
    X * outer u phi = outer (X *ᵥ u) phi := by
  ext i j
  simp [outer, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

lemma outer_mul (X : Matrix (Fin n) (Fin n) K) (u phi : Vec K n) :
    outer u phi * X = outer u (phi ᵥ* X) := by
  ext i j
  simp [outer, Matrix.mul_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]

lemma outer_smul_left (c : K) (u phi : Vec K n) : outer (c • u) phi = c • outer u phi := by
  ext i j; simp [outer, mul_assoc]

lemma outer_smul_right (c : K) (u phi : Vec K n) : outer u (c • phi) = c • outer u phi := by
  ext i j; simp [outer]; ring

lemma outer_eq_zero_iff {u phi : Vec K n} : outer u phi = 0 ↔ u = 0 ∨ phi = 0 := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    obtain ⟨hu, hphi⟩ := hc
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra hcc; push_neg at hcc; exact hu (funext hcc)
    obtain ⟨j, hj⟩ : ∃ j, phi j ≠ 0 := by
      by_contra hcc; push_neg at hcc; exact hphi (funext hcc)
    have := congrFun (congrFun h i) j
    simp [outer] at this
    tauto
  · rintro (rfl | rfl) <;> ext i j <;> simp [outer]

/-- Rank-one tensor equality lemma. -/
lemma outer_eq_outer_iff {u phi v alpha : Vec K n} (hu : u ≠ 0) (hphi : phi ≠ 0) :
    outer u alpha = outer v phi ↔ ∃ c : K, v = c • u ∧ alpha = c • phi := by
  constructor
  · intro h
    obtain ⟨i0, hi0⟩ : ∃ i, u i ≠ 0 := by
      by_contra hcc; push_neg at hcc; exact hu (funext hcc)
    obtain ⟨j0, hj0⟩ : ∃ j, phi j ≠ 0 := by
      by_contra hcc; push_neg at hcc; exact hphi (funext hcc)
    -- entrywise:  u i * alpha j = v i * phi j
    have key : ∀ i j, u i * alpha j = v i * phi j := fun i j => congrFun (congrFun h i) j
    have hv : ∀ i, v i = (alpha j0 / phi j0) * u i := by
      intro i
      have := key i j0
      field_simp
      linear_combination -this
    refine ⟨alpha j0 / phi j0, ?_, ?_⟩
    · funext i; simpa [Pi.smul_apply, smul_eq_mul] using hv i
    · funext j
      have h1 := key i0 j
      rw [hv i0] at h1
      have : u i0 * alpha j = u i0 * ((alpha j0 / phi j0) * phi j) := by
        rw [h1]; ring
      have := mul_left_cancel₀ hi0 this
      simpa [Pi.smul_apply, smul_eq_mul] using this
  · rintro ⟨c, rfl, rfl⟩
    rw [outer_smul_right, outer_smul_left]

/-! ## The pair action -/

/-- `S(X) = (X *ᵥ u, φ ᵥ* X)`, defined on all matrices. -/
def pairActionFull (u phi : Vec K n) :
    Matrix (Fin n) (Fin n) K →ₗ[K] (Vec K n × Vec K n) where
  toFun X := (X *ᵥ u, phi ᵥ* X)
  map_add' X Y := by
    simp [Matrix.add_mulVec, Matrix.vecMul_add]
  map_smul' c X := by
    simp [smul_mulVec, vecMul_smul, Prod.smul_mk]

@[simp] lemma pairActionFull_apply (u phi : Vec K n) (X : Matrix (Fin n) (Fin n) K) :
    pairActionFull u phi X = (X *ᵥ u, phi ᵥ* X) := rfl

/-- The pair action restricted to the commutant of `f`. -/
def pairAction (f : Matrix (Fin n) (Fin n) K) (u phi : Vec K n) :
    ↥(commutant f) →ₗ[K] (Vec K n × Vec K n) :=
  (pairActionFull u phi).comp (commutant f).subtype

@[simp] lemma pairAction_apply (f : Matrix (Fin n) (Fin n) K) (u phi : Vec K n)
    (X : ↥(commutant f)) : pairAction f u phi X = ((X : Matrix (Fin n) (Fin n) K) *ᵥ u,
      phi ᵥ* (X : Matrix (Fin n) (Fin n) K)) := rfl

/-- The compatibility functional `(v, α) ↦ φ ⬝ v - α ⬝ u`. -/
def compatFun (u phi : Vec K n) : (Vec K n × Vec K n) →ₗ[K] K where
  toFun p := phi ⬝ᵥ p.1 - p.2 ⬝ᵥ u
  map_add' p q := by simp [dotProduct_add, add_dotProduct]; ring
  map_smul' c p := by simp [dotProduct_smul, smul_dotProduct]; ring

@[simp] lemma compatFun_apply (u phi : Vec K n) (p : Vec K n × Vec K n) :
    compatFun u phi p = phi ⬝ᵥ p.1 - p.2 ⬝ᵥ u := rfl

lemma outer_mulVec (u phi w : Vec K n) : outer u phi *ᵥ w = (phi ⬝ᵥ w) • u := by
  funext i
  simp [outer, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

lemma vecMul_outer (u phi w : Vec K n) : w ᵥ* outer u phi = (w ⬝ᵥ u) • phi := by
  funext j
  simp [outer, Matrix.vecMul, dotProduct, Finset.sum_mul, mul_assoc]

lemma exists_dotProduct_eq_one {phi : Vec K n} (hphi : phi ≠ 0) : ∃ s : Vec K n, phi ⬝ᵥ s = 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, phi j ≠ 0 := by
    by_contra hcc; push_neg at hcc; exact hphi (funext hcc)
  refine ⟨fun i => if i = j then (phi j)⁻¹ else 0, ?_⟩
  simp [dotProduct, Finset.sum_ite_eq', hj]

lemma compatFun_surjective {u phi : Vec K n} (hphi : phi ≠ 0) :
    Function.Surjective (compatFun u phi) := by
  obtain ⟨s, hs⟩ := exists_dotProduct_eq_one hphi
  intro c
  exact ⟨(c • s, 0), by simp [dotProduct_smul, hs]⟩

lemma range_pairActionFull {u phi : Vec K n} (hu : u ≠ 0) (hphi : phi ≠ 0) :
    LinearMap.range (pairActionFull u phi) = LinearMap.ker (compatFun u phi) := by
  apply le_antisymm
  · rintro p ⟨X, rfl⟩
    simp only [LinearMap.mem_ker, compatFun_apply, pairActionFull_apply, sub_eq_zero]
    exact dotProduct_mulVec phi X u
  · rintro ⟨v, alpha⟩ hp
    simp only [LinearMap.mem_ker, compatFun_apply, sub_eq_zero] at hp
    obtain ⟨s, hs⟩ := exists_dotProduct_eq_one hphi
    obtain ⟨xi, hxi0⟩ := exists_dotProduct_eq_one hu
    have hxi : xi ⬝ᵥ u = 1 := by rw [dotProduct_comm]; exact hxi0
    refine ⟨outer v xi + outer s alpha - (alpha ⬝ᵥ u) • outer s xi, ?_⟩
    have h1 : (outer v xi + outer s alpha - (alpha ⬝ᵥ u) • outer s xi) *ᵥ u = v := by
      simp [Matrix.add_mulVec, Matrix.sub_mulVec, smul_mulVec, outer_mulVec, hxi]
    have h2 : phi ᵥ* (outer v xi + outer s alpha - (alpha ⬝ᵥ u) • outer s xi) = alpha := by
      simp [Matrix.vecMul_add, Matrix.vecMul_sub, vecMul_smul, vecMul_outer, hs, hp]
    simp only [pairActionFull_apply, h1, h2]

lemma finrank_vec_prod : finrank K (Vec K n × Vec K n) = 2 * n := by
  simp [Module.finrank_prod]; ring

lemma finrank_matrix_sq : finrank K (Matrix (Fin n) (Fin n) K) = n ^ 2 := by
  simp [Module.finrank_matrix]; ring

lemma finrank_ker_compatFun {u phi : Vec K n} (hphi : phi ≠ 0) :
    finrank K ↥(LinearMap.ker (compatFun u phi)) + 1 = 2 * n := by
  have h := LinearMap.finrank_range_add_finrank_ker (compatFun u phi)
  rw [finrank_vec_prod] at h
  have hr : LinearMap.range (compatFun u phi) = ⊤ :=
    LinearMap.range_eq_top.2 (compatFun_surjective hphi)
  rw [hr, finrank_top, Module.finrank_self] at h
  omega

lemma finrank_ker_pairActionFull {u phi : Vec K n} (hu : u ≠ 0) (hphi : phi ≠ 0) :
    finrank K ↥(LinearMap.ker (pairActionFull u phi)) + 2 * n = n ^ 2 + 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (pairActionFull u phi)
  rw [finrank_matrix_sq, range_pairActionFull hu hphi] at h
  have h2 := finrank_ker_compatFun (K := K) (u := u) hphi
  omega

lemma commutant_outer_eq_comap (u phi : Vec K n) (hu : u ≠ 0) (hphi : phi ≠ 0) :
    commutant (outer u phi) =
      Submodule.comap (pairActionFull u phi) (K ∙ ((u, phi) : Vec K n × Vec K n)) := by
  ext X
  simp only [mem_commutant_iff, Submodule.mem_comap, pairActionFull_apply,
    Submodule.mem_span_singleton]
  rw [mul_outer, outer_mul]
  constructor
  · intro h
    obtain ⟨c, hc1, hc2⟩ := (outer_eq_outer_iff hu hphi).1 h.symm
    exact ⟨c, by simp [Prod.ext_iff, hc1, hc2]⟩
  · rintro ⟨c, hc⟩
    have hc1 : X *ᵥ u = c • u := by simpa using congrArg Prod.fst hc.symm
    have hc2 : phi ᵥ* X = c • phi := by simpa using congrArg Prod.snd hc.symm
    exact ((outer_eq_outer_iff hu hphi).2 ⟨c, hc1, hc2⟩).symm

/-- The centralizer of a nonzero rank-one matrix has dimension `n² - 2n + 2`. -/
theorem finrank_commutant_outer_add {u phi : Vec K n} (hu : u ≠ 0) (hphi : phi ≠ 0) :
    finrank K ↥(commutant (outer u phi)) + 2 * n = n ^ 2 + 2 := by
  have hmem : ((u, phi) : Vec K n × Vec K n) ∈ LinearMap.range (pairActionFull u phi) :=
    ⟨1, by simp⟩
  have hspan : (K ∙ ((u, phi) : Vec K n × Vec K n)) ⊓ LinearMap.range (pairActionFull u phi)
      = K ∙ ((u, phi) : Vec K n × Vec K n) :=
    inf_eq_left.2 (Submodule.span_le.2 (by simpa using hmem))
  have hne : ((u, phi) : Vec K n × Vec K n) ≠ 0 := by
    simp only [ne_eq, Prod.mk_eq_zero, not_and]
    intro h; exact absurd h hu
  have h1 := finrank_comap_eq (pairActionFull u phi) (K ∙ ((u, phi) : Vec K n × Vec K n))
  rw [hspan, finrank_span_singleton hne, ← commutant_outer_eq_comap u phi hu hphi] at h1
  have h2 := finrank_ker_pairActionFull (K := K) hu hphi
  omega

/-- A scalar shift does not change the commutant. -/
@[simp] lemma commutant_smul_one_add (a : K) (A : Matrix (Fin n) (Fin n) K) :
    commutant (a • (1 : Matrix (Fin n) (Fin n) K) + A) = commutant A := by
  ext X
  simp only [mem_commutant_iff, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_one, one_mul, add_right_inj]

lemma comap_subtype_inf {M : Type*} [AddCommGroup M] [Module K M]
    (P Q : Submodule K M) :
    Submodule.comap P.subtype Q = Submodule.comap P.subtype (Q ⊓ P) := by
  ext x; simp [x.2]

lemma finrank_comap_subtype {M : Type*} [AddCommGroup M] [Module K M]
    (P Q : Submodule K M) :
    finrank K ↥(Submodule.comap P.subtype Q) = finrank K ↥(P ⊓ Q) := by
  rw [comap_subtype_inf]
  have hle : Q ⊓ P ≤ P := inf_le_right
  rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq, inf_comm]

/-- The intersection of `C(f)` with the centralizer of a rank-one matrix. -/
lemma finrank_inf_commutant_outer {f : Matrix (Fin n) (Fin n) K} {u phi : Vec K n}
    (hu : u ≠ 0) (hphi : phi ≠ 0) :
    finrank K ↥(commutant f ⊓ commutant (outer u phi)) =
      finrank K ↥(LinearMap.ker (pairAction f u phi)) + 1 := by
  have hcomap : Submodule.comap (pairAction f u phi) (K ∙ ((u, phi) : Vec K n × Vec K n))
      = Submodule.comap (commutant f).subtype (commutant (outer u phi)) := by
    rw [commutant_outer_eq_comap u phi hu hphi]
    rfl
  have hone : ((u, phi) : Vec K n × Vec K n) ∈ LinearMap.range (pairAction f u phi) := by
    refine ⟨⟨1, by simp⟩, ?_⟩
    simp [pairAction]
  have hspan : (K ∙ ((u, phi) : Vec K n × Vec K n)) ⊓ LinearMap.range (pairAction f u phi)
      = K ∙ ((u, phi) : Vec K n × Vec K n) :=
    inf_eq_left.2 (Submodule.span_le.2 (by simpa using hone))
  have hne : ((u, phi) : Vec K n × Vec K n) ≠ 0 := by
    simp only [ne_eq, Prod.mk_eq_zero, not_and]
    intro h; exact absurd h hu
  have h1 := finrank_comap_eq (pairAction f u phi) (K ∙ ((u, phi) : Vec K n × Vec K n))
  rw [hspan, finrank_span_singleton hne, hcomap,
    finrank_comap_subtype (commutant f) (commutant (outer u phi))] at h1
  exact h1

/-- **Exact sum formula.** -/
theorem finrank_sup_outer_add {f : Matrix (Fin n) (Fin n) K} {u phi : Vec K n}
    (hu : u ≠ 0) (hphi : phi ≠ 0) :
    finrank K ↥(commutant f ⊔ commutant (outer u phi)) + 2 * n =
      n ^ 2 + finrank K ↥(LinearMap.range (pairAction f u phi)) + 1 := by
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (commutant f) (commutant (outer u phi))
  have hinf := finrank_inf_commutant_outer (f := f) hu hphi
  have hrn := LinearMap.finrank_range_add_finrank_ker (pairAction f u phi)
  have hR := finrank_commutant_outer_add (K := K) hu hphi
  omega

/-- **Stage 1 completion gate.** -/
theorem extremal_with_outer_iff_pairAction {f : Matrix (Fin n) (Fin n) K} {u phi : Vec K n}
    (hn : 2 ≤ n) (hu : u ≠ 0) (hphi : phi ≠ 0) :
    finrank K ↥(commutant f ⊔ commutant (outer u phi)) = n ^ 2 - 1 ↔
      finrank K ↥(LinearMap.range (pairAction f u phi)) = 2 * n - 2 := by
  have h := finrank_sup_outer_add (f := f) hu hphi
  have hle : finrank K ↥(LinearMap.range (pairAction f u phi)) ≤ 2 * n := by
    have := Submodule.finrank_le (LinearMap.range (pairAction f u phi))
    rwa [finrank_vec_prod] at this
  obtain ⟨N, hN⟩ : ∃ N, n ^ 2 = N := ⟨_, rfl⟩
  have h2 : 2 * n ≤ N := by
    rw [← hN]; nlinarith
  rw [hN] at h
  omega

/-! ## Non-scalar matrices have a non-eigenvector -/

lemma exists_not_eigenvector {f : Matrix (Fin n) (Fin n) K} (hf : ¬ IsScalarMat f) :
    ∃ v : Vec K n, ∀ c : K, f *ᵥ v ≠ c • v := by
  classical
  by_contra hcon
  push_neg at hcon
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    exact hf ⟨0, by ext i; exact absurd i.2 (by simp)⟩
  choose c hc using fun i : Fin n => hcon (Pi.single i 1)
  have hentry : ∀ i p : Fin n, f p i = if p = i then c i else 0 := by
    intro i p
    have := congrFun (hc i) p
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq'] using this
  have hpair : ∀ i j : Fin n, i ≠ j → c i = c j := by
    intro i j hij
    obtain ⟨d, hd⟩ := hcon (Pi.single i 1 + Pi.single j 1)
    rw [Matrix.mulVec_add, hc i, hc j] at hd
    have hi := congrFun hd i
    have hj := congrFun hd j
    simp [hij, Ne.symm hij] at hi hj
    rw [hi, hj]
  set i0 : Fin n := ⟨0, hn1⟩
  refine hf ⟨c i0, ?_⟩
  ext p q
  rw [hentry q p]
  by_cases h : p = q
  · subst h
    by_cases hq : p = i0
    · subst hq; simp
    · rw [hpair p i0 hq]; simp
  · simp [Matrix.one_apply, h]

/-! ## Stage 4 — the exceptional two-dimensional case -/

lemma one_f_linearIndependent {f : Matrix (Fin n) (Fin n) K} (hn : 1 ≤ n)
    (hf : ¬ IsScalarMat f) :
    LinearIndependent K ![(1 : Matrix (Fin n) (Fin n) K), f] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have ht : t = 0 := by
    by_contra ht
    refine hf ⟨-(s / t), ?_⟩
    have h1 : t • f = -(s • (1 : Matrix (Fin n) (Fin n) K)) :=
      (neg_eq_of_add_eq_zero_right hst).symm
    have h2 := congrArg (fun M => t⁻¹ • M) h1
    simp only [smul_smul, inv_mul_cancel₀ ht, one_smul, smul_neg] at h2
    rw [h2, ← neg_smul]
    congr 1
    field_simp
  subst ht
  refine ⟨?_, rfl⟩
  simp only [zero_smul, add_zero] at hst
  by_contra hs
  have := congrFun (congrFun hst ⟨0, hn⟩) ⟨0, hn⟩
  simp [Matrix.one_apply] at this
  exact hs this

lemma span_one_f_le_commutant (f : Matrix (Fin n) (Fin n) K) :
    Submodule.span K (Set.range ![(1 : Matrix (Fin n) (Fin n) K), f]) ≤ commutant f := by
  rw [Submodule.span_le]
  rintro x ⟨i, rfl⟩
  fin_cases i <;> simp [mem_commutant_iff]

lemma two_le_finrank_commutant {f : Matrix (Fin n) (Fin n) K} (hn : 1 ≤ n)
    (hf : ¬ IsScalarMat f) :
    2 ≤ finrank K ↥(commutant f) := by
  have hli := one_f_linearIndependent hn hf
  have := Submodule.finrank_mono (R := K) (span_one_f_le_commutant f)
  rwa [finrank_span_eq_card hli, Fintype.card_fin] at this

lemma matrix_eq_zero_of_mulVec {X : Matrix (Fin n) (Fin n) K} (h : ∀ w, X *ᵥ w = 0) : X = 0 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq'] using this

/-- Evaluation at a vector, as a linear map on the commutant. -/
def evalVec (f : Matrix (Fin n) (Fin n) K) (v : Vec K n) : ↥(commutant f) →ₗ[K] Vec K n where
  toFun X := (X : Matrix (Fin n) (Fin n) K) *ᵥ v
  map_add' := by intro X Y; simp [Matrix.add_mulVec]
  map_smul' := by intro c X; simp [smul_mulVec]

@[simp] lemma evalVec_apply (f : Matrix (Fin n) (Fin n) K) (v : Vec K n) (X : ↥(commutant f)) :
    evalVec f v X = (X : Matrix (Fin n) (Fin n) K) *ᵥ v := rfl

/-- A non-scalar `2 × 2` matrix has a two-dimensional commutant. -/
lemma finrank_commutant_fin_two {f : Matrix (Fin 2) (Fin 2) K} (hf : ¬ IsScalarMat f) :
    finrank K ↥(commutant f) = 2 := by
  obtain ⟨v, hv⟩ := exists_not_eigenvector hf
  have hv0 : v ≠ 0 := by rintro rfl; exact hv 0 (by simp)
  have hli : LinearIndependent K ![v, f *ᵥ v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      refine hv (-(s / t)) ?_
      have h1 : t • (f *ᵥ v) = -(s • v) := (neg_eq_of_add_eq_zero_right hst).symm
      have h2 := congrArg (fun w => t⁻¹ • w) h1
      simp only [smul_smul, inv_mul_cancel₀ ht, one_smul, smul_neg] at h2
      rw [h2, ← neg_smul]
      congr 1
      field_simp
    subst ht
    simp only [zero_smul, add_zero] at hst
    refine ⟨?_, rfl⟩
    by_contra hs
    exact hv0 (by simpa [hs] using congrArg (fun w => s⁻¹ • w) hst)
  have hcard : Fintype.card (Fin 2) = finrank K (Vec K 2) := by simp
  let b : Module.Basis (Fin 2) K (Vec K 2) := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ⇑b = ![v, f *ᵥ v] := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hinj : Function.Injective (evalVec f v) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨X, hX⟩ hker
    simp only [LinearMap.mem_ker] at hker
    have hker' : X *ᵥ v = 0 := hker
    have hXf : X * f = f * X := hX
    have h2 : X *ᵥ (f *ᵥ v) = 0 := by
      rw [Matrix.mulVec_mulVec, hXf, ← Matrix.mulVec_mulVec, hker', Matrix.mulVec_zero]
    have hall : ∀ w, X *ᵥ w = 0 := by
      intro w
      have hrep := b.linearCombination_repr w
      rw [← hrep, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp),
        Matrix.mulVec_sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [Matrix.mulVec_smul]
      fin_cases i <;> simp [hb, hker', h2]
    have := matrix_eq_zero_of_mulVec hall
    simpa [Submodule.mem_bot, Subtype.ext_iff] using this
  have hle : finrank K ↥(commutant f) ≤ 2 := by
    have := LinearMap.finrank_le_finrank_of_injective (f := evalVec f v) hinj
    simpa using this
  have hge := two_le_finrank_commutant (n := 2) (by norm_num) hf
  omega

lemma span_one_f_eq_commutant_fin_two {f : Matrix (Fin 2) (Fin 2) K}
    (hf : ¬ IsScalarMat f) :
    Submodule.span K (Set.range ![(1 : Matrix (Fin 2) (Fin 2) K), f]) = commutant f := by
  have hli := one_f_linearIndependent (n := 2) (by norm_num) hf
  refine Submodule.eq_of_le_of_finrank_le (span_one_f_le_commutant f) ?_
  rw [finrank_span_eq_card hli, Fintype.card_fin, finrank_commutant_fin_two hf]

/-- For non-scalar `2 × 2` matrices, commuting is the same as having equal commutants. -/
theorem commute_iff_commutant_eq_fin_two {f g : Matrix (Fin 2) (Fin 2) K}
    (hf : ¬ IsScalarMat f) (hg : ¬ IsScalarMat g) :
    f * g = g * f ↔ commutant f = commutant g := by
  constructor
  · intro hcomm
    have hgf : g ∈ commutant f := by simpa [mem_commutant_iff] using hcomm.symm
    rw [← span_one_f_eq_commutant_fin_two hf] at hgf
    -- `g = a • 1 + b • f`
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hgf
    have hg' : cf 0 • (1 : Matrix (Fin 2) (Fin 2) K) + cf 1 • f = g := by
      rw [← hcf]
      simp [Fin.sum_univ_two]
    have hb : cf 1 ≠ 0 := by
      intro h0
      refine hg ⟨cf 0, ?_⟩
      rw [← hg', h0]; simp
    have hfg : f ∈ commutant g := by
      have : f = (cf 1)⁻¹ • (g - cf 0 • (1 : Matrix (Fin 2) (Fin 2) K)) := by
        rw [← hg']
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hb, one_smul]
      rw [mem_commutant_iff, this]
      simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub]
    have hle : commutant f ≤ commutant g := by
      rw [← span_one_f_eq_commutant_fin_two hf, Submodule.span_le]
      rintro x ⟨i, rfl⟩
      fin_cases i
      · simp [mem_commutant_iff]
      · exact hfg
    exact Submodule.eq_of_le_of_finrank_le hle
      (by rw [finrank_commutant_fin_two hf, finrank_commutant_fin_two hg])
  · intro heq
    have : f ∈ commutant g := by rw [← heq]; simp [mem_commutant_iff]
    exact (mem_commutant_iff.1 this)

/-- **Stage 4 completion gate.**  In dimension two, equality in the bound is exactly
noncommutation. -/
theorem extremal_fin_two_iff_noncommute {f g : Matrix (Fin 2) (Fin 2) K}
    (hf : ¬ IsScalarMat f) (hg : ¬ IsScalarMat g) :
    finrank K ↥(commutant f ⊔ commutant g) = 3 ↔ f * g ≠ g * f := by
  have hff := finrank_commutant_fin_two hf
  have hgg := finrank_commutant_fin_two hg
  constructor
  · intro h3 hcomm
    rw [(commute_iff_commutant_eq_fin_two hf hg).1 hcomm, sup_idem, hgg] at h3
    omega
  · intro hnc
    have hne : commutant f ≠ commutant g := fun h =>
      hnc ((commute_iff_commutant_eq_fin_two hf hg).2 h)
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (commutant f) (commutant g)
    have hinf_le : finrank K ↥(commutant f ⊓ commutant g) ≤ 2 := by
      have := Submodule.finrank_mono (R := K)
        (inf_le_left : commutant f ⊓ commutant g ≤ commutant f)
      omega
    have hinf_ne : finrank K ↥(commutant f ⊓ commutant g) ≠ 2 := by
      intro h2
      have heq1 : commutant f ⊓ commutant g = commutant f :=
        Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
      have hle : commutant f ≤ commutant g := by
        intro x hx
        have hx' : x ∈ commutant f ⊓ commutant g := by rw [heq1]; exact hx
        exact hx'.2
      exact hne (Submodule.eq_of_le_of_finrank_le hle (by rw [hff, hgg]))
    have hone : (1 : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
      intro h
      have := congrFun (congrFun h 0) 0
      simp at this
    have hinf_ge : 1 ≤ finrank K ↥(commutant f ⊓ commutant g) := by
      have hle : (K ∙ (1 : Matrix (Fin 2) (Fin 2) K)) ≤ commutant f ⊓ commutant g := by
        rw [Submodule.span_le]
        rintro x hx
        simp only [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨by simp [mem_commutant_iff], by simp [mem_commutant_iff]⟩
      have := Submodule.finrank_mono (R := K) hle
      rwa [finrank_span_singleton hone] at this
    omega

end Q655
