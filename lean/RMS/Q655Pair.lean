import RMS.Q655Block

/-!
# Q655 — Stage 5D, part 3: the conjugated common commutant as a linear system

For an invertible `h`, the common commutant `C(F) ⊓ C(h G h⁻¹)` is isomorphic to

  `pairSpace F G h = {(X, Y) | X F = F X, Y G = G Y, X h = h Y}`,

which is the kernel of a coefficient matrix `pairMat F G h` whose entries depend *polynomially*
(indeed linearly) on the entries of `h`.  This is what makes the semicontinuity argument of the
generic-position step work without ever writing down entries of `h⁻¹`.
-/

namespace Q655

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

/-! ## The coefficient matrix -/

section CommRingDefs

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The coefficient matrix of `X ↦ f * X`. -/
def lmulMat (f : Matrix (Fin n) (Fin n) R) : Matrix (Fin n × Fin n) (Fin n × Fin n) R :=
  Matrix.of fun ij kl => if ij.2 = kl.2 then f ij.1 kl.1 else 0

/-- The coefficient matrix of `X ↦ X * f`. -/
def rmulMat (f : Matrix (Fin n) (Fin n) R) : Matrix (Fin n × Fin n) (Fin n × Fin n) R :=
  Matrix.of fun ij kl => if ij.1 = kl.1 then f kl.2 ij.2 else 0

/-- The coefficient matrix of `(X, Y) ↦ X * h - h * Y`. -/
def conjMat (h : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n × Fin n) ((Fin n × Fin n) ⊕ (Fin n × Fin n)) R :=
  Matrix.of fun ij kl =>
    Sum.elim (fun kl => rmulMat h ij kl) (fun kl => -(lmulMat h ij kl)) kl

/-- The coefficient matrix of the linear system
`X F = F X`, `Y G = G Y`, `X h = h Y` in the unknown pair `(X, Y)`. -/
def pairMat (F G h : Matrix (Fin n) (Fin n) R) :
    Matrix (((Fin n × Fin n) ⊕ (Fin n × Fin n)) ⊕ (Fin n × Fin n))
      ((Fin n × Fin n) ⊕ (Fin n × Fin n)) R :=
  Matrix.of fun ij kl =>
    Sum.elim
      (Sum.elim (fun ij : Fin n × Fin n => Sum.elim (fun kl => adMat F ij kl) (fun _ => 0) kl)
        (fun ij : Fin n × Fin n => Sum.elim (fun _ => 0) (fun kl => adMat G ij kl) kl))
      (fun ij : Fin n × Fin n => conjMat h ij kl) ij

lemma pairMat_map (φ : R →+* S) (F G h : Matrix (Fin n) (Fin n) R) :
    (pairMat F G h).map φ = pairMat (F.map φ) (G.map φ) (h.map φ) := by
  have hF : ∀ ij kl, φ (adMat F ij kl) = adMat (F.map φ) ij kl := fun ij kl =>
    congrFun (congrFun (adMat_map φ F) ij) kl
  have hG : ∀ ij kl, φ (adMat G ij kl) = adMat (G.map φ) ij kl := fun ij kl =>
    congrFun (congrFun (adMat_map φ G) ij) kl
  ext ij kl
  cases ij with
  | inl a =>
      cases a with
      | inl a =>
          cases kl <;> simp [pairMat, hF]
      | inr a =>
          cases kl <;> simp [pairMat, hG]
  | inr a =>
      cases kl <;> simp [pairMat, conjMat, lmulMat, rmulMat, apply_ite φ]

end CommRingDefs

lemma lmulMat_mulVec (f X : Matrix (Fin n) (Fin n) K) :
    lmulMat f *ᵥ vecMat K n X = vecMat K n (f * X) := by
  funext ij
  obtain ⟨i, j⟩ := ij
  simp only [Matrix.mulVec, dotProduct, lmulMat, Matrix.of_apply, vecMat_apply, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Finset.sum_ite_eq' Finset.univ j]

lemma rmulMat_mulVec (f X : Matrix (Fin n) (Fin n) K) :
    rmulMat f *ᵥ vecMat K n X = vecMat K n (X * f) := by
  funext ij
  obtain ⟨i, j⟩ := ij
  simp only [Matrix.mulVec, dotProduct, rmulMat, Matrix.of_apply, vecMat_apply, Matrix.mul_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [Finset.sum_ite_eq' Finset.univ i, mul_comm]

/-- The action of `pairMat` on a vectorised pair of matrices. -/
lemma pairMat_mulVec (F G h X Y : Matrix (Fin n) (Fin n) K) :
    pairMat F G h *ᵥ (vecPair K n n n n (X, Y)) =
      Sum.elim (Sum.elim (vecMat K n (F * X - X * F)) (vecMat K n (G * Y - Y * G)))
        (vecMat K n (X * h - h * Y)) := by
  funext ij
  cases ij with
  | inl a =>
      cases a with
      | inl a =>
          have hA := congrFun (adMat_mulVec F X) a
          simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, pairMat, Matrix.of_apply,
            Sum.elim_inl, vecPair_inl, vecPair_inr] at hA ⊢
          simpa using hA
      | inr a =>
          have hA := congrFun (adMat_mulVec G Y) a
          simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, pairMat, Matrix.of_apply,
            Sum.elim_inl, Sum.elim_inr, vecPair_inl, vecPair_inr] at hA ⊢
          simpa using hA
  | inr a =>
      have h1 := congrFun (rmulMat_mulVec h X) a
      have h2 := congrFun (lmulMat_mulVec h Y) a
      simp only [Matrix.mulVec, dotProduct, vecMat_apply] at h1 h2
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, pairMat, conjMat,
        Matrix.of_apply, Sum.elim_inr, Sum.elim_inl, vecPair_inl, vecPair_inr, vecMat_apply,
        Matrix.sub_apply, neg_mul, Finset.sum_neg_distrib]
      rw [h1, h2]
      abel

/-! ## The pair space -/

/-- The space of pairs `(X, Y)` with `X ∈ C(F)`, `Y ∈ C(G)` and `X h = h Y`. -/
def pairSpace (F G h : Matrix (Fin n) (Fin n) K) :
    Submodule K (Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K) where
  carrier := {XY | XY.1 * F = F * XY.1 ∧ XY.2 * G = G * XY.2 ∧ XY.1 * h = h * XY.2}
  add_mem' := by
    rintro x y ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Matrix.add_mul, Matrix.mul_add, h1, h1', h2, h2',
        h3, h3']
  zero_mem' := by simp
  smul_mem' := by
    rintro c x ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Prod.smul_fst, Prod.smul_snd, Matrix.smul_mul, Matrix.mul_smul, h1, h2, h3]

lemma mem_pairSpace_iff {F G h X Y : Matrix (Fin n) (Fin n) K} :
    (X, Y) ∈ pairSpace F G h ↔ X * F = F * X ∧ Y * G = G * Y ∧ X * h = h * Y := Iff.rfl

lemma finrank_pairSpace_add_rank (F G h : Matrix (Fin n) (Fin n) K) :
    finrank K ↥(pairSpace F G h) + (pairMat F G h).rank = 2 * n ^ 2 := by
  have := finrank_add_rank_of_ker' (K := K) (vecPair K n n n n) (pairMat F G h) (pairSpace F G h)
    (fun XY => by
      obtain ⟨X, Y⟩ := XY
      rw [pairMat_mulVec]
      constructor
      · rintro ⟨h1, h2, h3⟩
        have e1 : F * X - X * F = 0 := by rw [h1]; abel
        have e2 : G * Y - Y * G = 0 := by rw [h2]; abel
        have e3 : X * h - h * Y = 0 := by rw [h3]; abel
        rw [e1, e2, e3]
        funext x; rcases x with (x | x) | x <;> simp
      · intro hz
        have e1 : F * X - X * F = 0 := by
          refine (vecMat K n).map_eq_zero_iff.1 ?_
          funext ij
          simpa using congrFun hz (Sum.inl (Sum.inl ij))
        have e2 : G * Y - Y * G = 0 := by
          refine (vecMat K n).map_eq_zero_iff.1 ?_
          funext ij
          simpa using congrFun hz (Sum.inl (Sum.inr ij))
        have e3 : X * h - h * Y = 0 := by
          refine (vecMat K n).map_eq_zero_iff.1 ?_
          funext ij
          simpa using congrFun hz (Sum.inr ij)
        exact ⟨(sub_eq_zero.1 e1).symm, (sub_eq_zero.1 e2).symm, sub_eq_zero.1 e3⟩)
  rw [this]
  simp [Fintype.card_sum, Fintype.card_prod, sq, two_mul]

/-! ## Identification with the conjugated common commutant -/

lemma finrank_pairSpace_eq (F G h : Matrix (Fin n) (Fin n) K) (hh : IsUnit h.det) :
    finrank K ↥(pairSpace F G h) = finrank K ↥(commutant F ⊓ commutant (h * G * h⁻¹)) := by
  classical
  have hinv : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h hh
  have hinv' : h⁻¹ * h = 1 := Matrix.nonsing_inv_mul h hh
  set L : ↥(pairSpace F G h) →ₗ[K] Matrix (Fin n) (Fin n) K :=
    (LinearMap.fst K (Matrix (Fin n) (Fin n) K) (Matrix (Fin n) (Fin n) K)).domRestrict
      (pairSpace F G h) with hL
  have hker : LinearMap.ker L = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro ⟨⟨X, Y⟩, hXY⟩ hx
    have hX : X = 0 := hx
    obtain ⟨-, -, h3⟩ := hXY
    rw [hX] at h3
    have : h * Y = 0 := by rw [← h3]; simp
    have hY : Y = 0 := by
      have := congrArg (fun M => h⁻¹ * M) this
      simpa [← Matrix.mul_assoc, hinv'] using this
    simp [Subtype.ext_iff, Prod.ext_iff, hX, hY]
  have hrange : LinearMap.range L = commutant F ⊓ commutant (h * G * h⁻¹) := by
    ext X
    constructor
    · rintro ⟨⟨⟨X, Y⟩, h1, h2, h3⟩, rfl⟩
      refine ⟨h1, ?_⟩
      have hXh : X * h = h * Y := h3
      have hY : Y = h⁻¹ * X * h := by
        have e := congrArg (fun M => h⁻¹ * M) hXh
        simp only [← Matrix.mul_assoc, hinv', Matrix.one_mul] at e
        exact e.symm
      show X * (h * G * h⁻¹) = (h * G * h⁻¹) * X
      calc X * (h * G * h⁻¹) = (X * h) * G * h⁻¹ := by simp [Matrix.mul_assoc]
        _ = h * (Y * G) * h⁻¹ := by rw [hXh]; simp [Matrix.mul_assoc]
        _ = h * (G * Y) * h⁻¹ := by rw [h2]
        _ = h * G * (h⁻¹ * X * h) * h⁻¹ := by rw [hY]; simp [Matrix.mul_assoc]
        _ = (h * G * h⁻¹) * X * (h * h⁻¹) := by simp [Matrix.mul_assoc]
        _ = (h * G * h⁻¹) * X := by rw [hinv, Matrix.mul_one]
    · rintro ⟨h1, h2⟩
      have h2' : X * (h * G * h⁻¹) = (h * G * h⁻¹) * X := h2
      refine ⟨⟨(X, h⁻¹ * X * h), h1, ?_, ?_⟩, rfl⟩
      · show (h⁻¹ * X * h) * G = G * (h⁻¹ * X * h)
        have step : X * h * G = h * G * h⁻¹ * X * h := by
          have e := congrArg (fun M => M * h) h2'
          simpa [Matrix.mul_assoc, hinv, hinv'] using e
        calc (h⁻¹ * X * h) * G = h⁻¹ * (X * h * G) := by simp [Matrix.mul_assoc]
          _ = h⁻¹ * (h * G * h⁻¹ * X * h) := by rw [step]
          _ = (h⁻¹ * h) * (G * (h⁻¹ * X * h)) := by simp [Matrix.mul_assoc]
          _ = G * (h⁻¹ * X * h) := by rw [hinv', Matrix.one_mul]
      · show X * h = h * (h⁻¹ * X * h)
        rw [show h * (h⁻¹ * X * h) = (h * h⁻¹) * X * h by simp [Matrix.mul_assoc], hinv,
          Matrix.one_mul]
  have hinj : Function.Injective L := LinearMap.ker_eq_bot.1 hker
  rw [← hrange, LinearMap.finrank_range_of_inj hinj]

lemma finrank_pairSpace_one (F G : Matrix (Fin n) (Fin n) K) :
    finrank K ↥(pairSpace F G 1) = finrank K ↥(commutant F ⊓ commutant G) := by
  have hone : (1 : Matrix (Fin n) (Fin n) K)⁻¹ = 1 := Matrix.inv_eq_left_inv (by simp)
  have h := finrank_pairSpace_eq F G 1 (by simp)
  rw [hone, Matrix.one_mul, Matrix.mul_one] at h
  exact h

end Q655
