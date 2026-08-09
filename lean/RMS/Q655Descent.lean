import RMS.Q655Final

/-!
# Q655 — Stage 6: descent of a rank-one scalar shift to the base field

This file contains the elementary half of Stage 6.  It is completely general: `L` is an
arbitrary field extension of `K` (in the intended application `L = AlgebraicClosure K`).

* `isRankOneMat_iff_minors` — the entrywise `2 × 2`-minor characterisation of rank one.
  It replaces any use of the determinant/rank API and transfers immediately along field
  extensions.
* `isRankOneMat_of_map` — rank one descends along a field extension.
* `rank_one_scalar_descends` — if, for some scalar `lam` of an extension field `L`, the matrix
  `a ⊗ 1 - lam • 1` has rank one, then `lam` already lies in `K` and `a - lam₀ • 1` has rank one
  over `K`.  This is the descent step of Stage 6.
-/

namespace Q655

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

/-! ## The minor criterion for rank one -/

/-- A matrix is a nonzero outer product exactly when it is nonzero and all its `2 × 2` minors
vanish. -/
lemma isRankOneMat_iff_minors {A : Matrix (Fin n) (Fin n) K} :
    IsRankOneMat A ↔ A ≠ 0 ∧ ∀ i j k l, A i j * A k l = A i l * A k j := by
  constructor
  · rintro ⟨u, phi, hu, hphi, rfl⟩
    refine ⟨?_, fun i j k l => by simp only [outer_apply]; ring⟩
    intro h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hphi
    have : outer u phi i j = 0 := by rw [h]; rfl
    rw [outer_apply] at this
    exact hi ((mul_eq_zero.1 this).resolve_right hj)
  · rintro ⟨hA0, hmin⟩
    obtain ⟨p, q, hq⟩ : ∃ p q, A p q ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hA0 (by ext i j; exact hc i j)
    refine ⟨fun i => A i q, fun j => A p j / A p q, ?_, ?_, ?_⟩
    · intro h
      exact hq (by simpa using congrFun h p)
    · intro h
      have := congrFun h q
      simp only [div_self hq, Pi.zero_apply] at this
      exact one_ne_zero this
    · ext i j
      have h := hmin i j p q
      have hsplit : A i q * (A p j / A p q) = (A i q * A p j) / A p q := by ring
      rw [outer_apply, hsplit, eq_div_iff hq]
      exact h

/-! ## Descent along a field extension -/

lemma map_sub_smul_one (L : Type*) [Field L] [Algebra K L] (a : Matrix (Fin n) (Fin n) K)
    (c : K) :
    (a - c • (1 : Matrix (Fin n) (Fin n) K)).map (algebraMap K L)
      = a.map (algebraMap K L) - (algebraMap K L c) • (1 : Matrix (Fin n) (Fin n) L) := by
  ext i j
  by_cases h : i = j <;>
    simp [h, Algebra.algebraMap_eq_smul_one, sub_smul]

/-- Rank one descends along a field extension. -/
lemma isRankOneMat_of_map {L : Type*} [Field L] [Algebra K L] {A : Matrix (Fin n) (Fin n) K}
    (h : IsRankOneMat (A.map (algebraMap K L))) : IsRankOneMat A := by
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  rw [isRankOneMat_iff_minors] at h ⊢
  obtain ⟨h0, hmin⟩ := h
  refine ⟨fun hA => h0 (by rw [hA]; ext i j; simp), fun i j k l => ?_⟩
  have := hmin i j k l
  simp only [Matrix.map_apply, ← map_mul] at this
  exact hinj this

/-- **Descent of a rank-one scalar shift.**  If some scalar of an extension field `L` makes
`a` differ from a scalar matrix by a rank-one matrix, then that scalar already lies in `K`. -/
theorem rank_one_scalar_descends {L : Type*} [Field L] [Algebra K L] (hn : 3 ≤ n)
    {a : Matrix (Fin n) (Fin n) K} {lam : L}
    (h : IsRankOneMat (a.map (algebraMap K L) - lam • (1 : Matrix (Fin n) (Fin n) L))) :
    ∃ lam0 : K, algebraMap K L lam0 = lam ∧ IsRankOneMat (a - lam0 • 1) := by
  set B : Matrix (Fin n) (Fin n) L :=
    a.map (algebraMap K L) - lam • (1 : Matrix (Fin n) (Fin n) L) with hBdef
  have hBoff : ∀ i j : Fin n, i ≠ j → B i j = algebraMap K L (a i j) := by
    intro i j hij
    simp [hBdef, hij]
  have hBdiag : ∀ i : Fin n, B i i = algebraMap K L (a i i) - lam := by
    intro i
    simp [hBdef]
  obtain ⟨hB0, hmin⟩ := isRankOneMat_iff_minors.1 h
  have key : ∃ lam0 : K, algebraMap K L lam0 = lam := by
    by_cases hoff : ∃ i j : Fin n, i ≠ j ∧ a i j ≠ 0
    · obtain ⟨i, j, hij, hne⟩ := hoff
      obtain ⟨k, hk⟩ : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
        have hcard : ({i, j} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
          have h1 : ({i, j} : Finset (Fin n)).card ≤ 2 := by
            apply le_trans (Finset.card_insert_le _ _)
            simp
          simpa using lt_of_le_of_lt h1 (by simpa using hn)
        obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
        exact ⟨k, fun h => hk (by simp [h]), fun h => hk (by simp [h])⟩
      obtain ⟨hki, hkj⟩ := hk
      refine ⟨a k k - a i k * a k j / a i j, ?_⟩
      have hAij : algebraMap K L (a i j) ≠ 0 := by
        simpa using (map_ne_zero_iff _ (algebraMap K L).injective).2 hne
      have hm := hmin i j k k
      rw [hBoff i j hij, hBdiag k, hBoff i k (Ne.symm hki), hBoff k j hkj] at hm
      have : algebraMap K L (a i j) * lam =
          algebraMap K L (a i j) * algebraMap K L (a k k) -
            algebraMap K L (a i k) * algebraMap K L (a k j) := by
        linear_combination -hm
      rw [map_sub, map_div₀, map_mul]
      field_simp
      linear_combination -this
    · push_neg at hoff
      obtain ⟨p, q, hq⟩ : ∃ p q, B p q ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hB0 (by ext i j; exact hc i j)
      have hpq : p = q := by
        by_contra hne
        exact hq (by rw [hBoff p q hne, hoff p q hne, map_zero])
      subst hpq
      obtain ⟨k, hk⟩ : ∃ k : Fin n, k ≠ p := by
        have : ({p} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
          simpa using (by omega : 1 < n)
        obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card this
        exact ⟨k, by simpa using hk⟩
      refine ⟨a k k, ?_⟩
      have hm := hmin p p k k
      rw [hBoff p k (Ne.symm hk), hBoff k p hk, hoff p k (Ne.symm hk), hoff k p hk] at hm
      simp only [map_zero, mul_zero] at hm
      rw [hBdiag k] at hm
      have : algebraMap K L (a k k) - lam = 0 := by
        rcases mul_eq_zero.1 hm with h1 | h2
        · exact absurd h1 hq
        · exact h2
      exact sub_eq_zero.1 this
  obtain ⟨lam0, hlam0⟩ := key
  refine ⟨lam0, hlam0, isRankOneMat_of_map (L := L) ?_⟩
  rw [map_sub_smul_one, hlam0]
  exact h

end Q655
