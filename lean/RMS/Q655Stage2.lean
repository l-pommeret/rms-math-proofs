import RMS.Q655Nilp

/-!
# Q655 — Stage 2: an extremal pair action forces a quadratic relation

The pair action `T(X) = (X u, φ X)` on `C(f)` annihilates every functional of the form
`(v, α) ↦ (φ g) ⬝ v - α ⬝ (g u)` with `g` a polynomial in `f`.  Taking `g = 1, f, f²` gives
three such functionals; if they are independent the rank drops by three, which is incompatible
with the maximal value `2n - 2`.  Otherwise there is a nonzero `M = a₀ + a₁ f + a₂ f²` with
`M u = 0` and `φ M = 0`, and an elementary rank analysis of `M` shows that this too is
incompatible with maximality unless `M = 0`, i.e. unless `f` satisfies a monic quadratic.
-/

namespace Q655

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

/-! ## A nonzero annihilating covector for a proper subspace of `Kᵐ` -/

lemma exists_nonzero_dot_annihilator {m : ℕ} (S : Submodule K (Fin m → K)) (hS : S ≠ ⊤) :
    ∃ a : Fin m → K, a ≠ 0 ∧ ∀ x ∈ S, a ⬝ᵥ x = 0 := by
  obtain ⟨g, hg0, hgS⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.2 hS) inferInstance
  have hgS' : ∀ x ∈ S, g x = 0 := by
    intro x hx
    have hmem : g x ∈ Submodule.map g S := ⟨x, hx, rfl⟩
    rw [hgS, Submodule.mem_bot] at hmem
    exact hmem
  have key : ∀ y : Fin m → K, g y = (fun i => g (Pi.single i 1)) ⬝ᵥ y := by
    intro y
    have hy : y = ∑ i, y i • (Pi.single i 1 : Fin m → K) := by ext j; simp [Pi.single_apply]
    conv_lhs => rw [hy]
    rw [map_sum]
    simp [dotProduct, mul_comm]
  refine ⟨fun i => g (Pi.single i 1), ?_, ?_⟩
  · intro h
    refine hg0 (LinearMap.ext fun y => ?_)
    rw [key y, h]
    simp
  · intro x hx
    rw [← key x]
    exact hgS' x hx

/-! ## The pairing on `Vec × Vec` -/

/-- The standard nondegenerate pairing on `Vec K n × Vec K n`. -/
def pairing (Q x : Vec K n × Vec K n) : K := Q.1 ⬝ᵥ x.1 + Q.2 ⬝ᵥ x.2

lemma pairing_add_smul (a0 a1 a2 : K) (P0 P1 P2 x : Vec K n × Vec K n) :
    pairing (a0 • P0 + a1 • P1 + a2 • P2) x =
      a0 * pairing P0 x + a1 * pairing P1 x + a2 * pairing P2 x := by
  simp only [pairing, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, add_dotProduct,
    smul_dotProduct, smul_eq_mul]
  ring

lemma pairing_eq_zero_of_forall {Q : Vec K n × Vec K n} (h : ∀ x, pairing Q x = 0) : Q = 0 := by
  have h1 : Q.1 = 0 := by
    funext j
    have := h (Pi.single j 1, 0)
    simpa [pairing, dotProduct, Pi.single_apply] using this
  have h2 : Q.2 = 0 := by
    funext j
    have := h (0, Pi.single j 1)
    simpa [pairing, dotProduct, Pi.single_apply] using this
  exact Prod.ext h1 h2

/-- The three pairings, bundled into a map to `K³`. -/
def tripleFun (P0 P1 P2 : Vec K n × Vec K n) : (Vec K n × Vec K n) →ₗ[K] (Fin 3 → K) where
  toFun x := ![pairing P0 x, pairing P1 x, pairing P2 x]
  map_add' x y := by
    funext i
    fin_cases i <;>
      simp [pairing, dotProduct_add] <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;>
      simp [pairing, dotProduct_smul, mul_add]

/-- Three independent pairs cut down any subspace annihilated by all of them by three. -/
lemma finrank_le_of_three_indep (P0 P1 P2 : Vec K n × Vec K n)
    (hind : ∀ a0 a1 a2 : K, a0 • P0 + a1 • P1 + a2 • P2 = 0 → a0 = 0 ∧ a1 = 0 ∧ a2 = 0)
    (S : Submodule K (Vec K n × Vec K n))
    (hS : S ≤ LinearMap.ker (tripleFun P0 P1 P2)) :
    finrank K ↥S + 3 ≤ 2 * n := by
  have hsurj : LinearMap.range (tripleFun P0 P1 P2) = ⊤ := by
    by_contra hcon
    obtain ⟨a, ha0, haS⟩ := exists_nonzero_dot_annihilator _ hcon
    have hzero : ∀ x : Vec K n × Vec K n,
        pairing (a 0 • P0 + a 1 • P1 + a 2 • P2) x = 0 := by
      intro x
      have hx := haS (tripleFun P0 P1 P2 x) ⟨x, rfl⟩
      rw [pairing_add_smul]
      simpa [dotProduct, Fin.sum_univ_three, tripleFun] using hx
    obtain ⟨h0, h1, h2⟩ := hind _ _ _ (pairing_eq_zero_of_forall hzero)
    exact ha0 (funext fun i => by fin_cases i <;> assumption)
  have hrn := LinearMap.finrank_range_add_finrank_ker (tripleFun P0 P1 P2)
  rw [hsurj, finrank_top, Module.finrank_pi, Fintype.card_fin] at hrn
  rw [finrank_vec_prod] at hrn
  have := Submodule.finrank_mono hS
  omega

/-! ## The invariant functionals attached to a commuting matrix -/

variable {f : Matrix (Fin n) (Fin n) K} {u phi : Vec K n}

lemma pairing_vanishes_on_range {g : Matrix (Fin n) (Fin n) K}
    (hg : ∀ X ∈ commutant f, X * g = g * X) :
    ∀ x ∈ LinearMap.range (pairAction f u phi), pairing (phi ᵥ* g, -(g *ᵥ u)) x = 0 := by
  rintro _ ⟨⟨X, hX⟩, rfl⟩
  have hgX : X * g = g * X := hg X hX
  show (phi ᵥ* g) ⬝ᵥ (X *ᵥ u) + (-(g *ᵥ u)) ⬝ᵥ (phi ᵥ* X) = 0
  rw [← dotProduct_mulVec, neg_dotProduct, dotProduct_comm (g *ᵥ u) (phi ᵥ* X),
    ← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hgX]
  ring

/-- Powers of `f` commute with everything in `C(f)`. -/
lemma comm_of_quadratic_poly (a0 a1 a2 : K) :
    ∀ X ∈ commutant f,
      X * (a0 • (1 : Matrix (Fin n) (Fin n) K) + a1 • f + a2 • (f * f)) =
        (a0 • (1 : Matrix (Fin n) (Fin n) K) + a1 • f + a2 • (f * f)) * X := by
  intro X hX
  have h1 : X * f = f * X := hX
  have h2 : X * (f * f) = (f * f) * X := by
    rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, h1, ← Matrix.mul_assoc]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul,
    h1, h2]

lemma mulVec_mem_ker_of_comm {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ X ∈ commutant f, X * M = M * X) (hMu : M *ᵥ u = 0) :
    ∀ X ∈ commutant f, X *ᵥ u ∈ LinearMap.ker M.mulVecLin := by
  intro X hX
  show M *ᵥ (X *ᵥ u) = 0
  rw [Matrix.mulVec_mulVec, ← hM X hX, ← Matrix.mulVec_mulVec, hMu, Matrix.mulVec_zero]

lemma vecMul_mem_leftKer_of_comm {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ X ∈ commutant f, X * M = M * X) (hphiM : phi ᵥ* M = 0) :
    ∀ X ∈ commutant f, phi ᵥ* X ∈ leftKer M := by
  intro X hX
  rw [mem_leftKer_iff, Matrix.vecMul_vecMul, hM X hX, ← Matrix.vecMul_vecMul, hphiM,
    Matrix.zero_vecMul]

/-! ## Stage 2 -/

/-- **Stage 2 completion gate.**  A maximal pair action forces a monic quadratic relation. -/
theorem exists_quadratic_of_pairAction_extremal (hn : 3 ≤ n) (hf : ¬ IsScalarMat f)
    (hu : u ≠ 0) (hphi : phi ≠ 0)
    (hrank : finrank K ↥(LinearMap.range (pairAction f u phi)) = 2 * n - 2) :
    ∃ c d : K, f * f + c • f + d • (1 : Matrix (Fin n) (Fin n) K) = 0 := by
  by_cases hdep : ∃ a0 a1 a2 : K, ¬(a0 = 0 ∧ a1 = 0 ∧ a2 = 0) ∧
      (a0 • (1 : Matrix (Fin n) (Fin n) K) + a1 • f + a2 • (f * f)) *ᵥ u = 0 ∧
      phi ᵥ* (a0 • (1 : Matrix (Fin n) (Fin n) K) + a1 • f + a2 • (f * f)) = 0
  · obtain ⟨a0, a1, a2, hne, hMu, hphiM⟩ := hdep
    set M : Matrix (Fin n) (Fin n) K := a0 • 1 + a1 • f + a2 • (f * f) with hM
    have hcomm := comm_of_quadratic_poly (f := f) a0 a1 a2
    by_cases hM0 : M = 0
    · -- the relation is already a polynomial identity
      by_cases ha2 : a2 = 0
      · by_cases ha1 : a1 = 0
        · exfalso
          have ha0 : a0 ≠ 0 := by tauto
          have : a0 • (1 : Matrix (Fin n) (Fin n) K) = 0 := by
            rw [← hM0, hM, ha1, ha2]; module
          have := congrFun (congrFun this (⟨0, by omega⟩ : Fin n)) (⟨0, by omega⟩ : Fin n)
          simp at this
          exact ha0 this
        · exfalso
          apply hf
          refine ⟨-(a0 / a1), ?_⟩
          have h : a1 • f = (-a0) • (1 : Matrix (Fin n) (Fin n) K) := by
            rw [hM, ha2] at hM0
            linear_combination (norm := module) hM0
          have h2 := congrArg (fun A : Matrix (Fin n) (Fin n) K => a1⁻¹ • A) h
          simp only [smul_smul, inv_mul_cancel₀ ha1, one_smul] at h2
          rw [h2]
          congr 1
          field_simp
      · refine ⟨a1 / a2, a0 / a2, ?_⟩
        have h := hM0
        rw [hM] at h
        have h2 := congrArg (fun A : Matrix (Fin n) (Fin n) K => a2⁻¹ • A) h
        simp only [smul_add, smul_smul, inv_mul_cancel₀ ha2, one_smul, smul_zero] at h2
        rw [div_eq_inv_mul, div_eq_inv_mul, ← smul_smul, ← smul_smul]
        linear_combination (norm := module) h2
    · exfalso
      -- `M ≠ 0`: the rank of `M` bounds the pair action away from the maximum
      have hkerA := mulVec_mem_ker_of_comm hcomm hMu
      have hkerB := vecMul_mem_leftKer_of_comm hcomm hphiM
      rcases le_or_gt 2 M.rank with hk | hk
      · have hb : finrank K ↥(LinearMap.range (pairAction f u phi)) ≤
            finrank K ↥(LinearMap.ker M.mulVecLin) + finrank K ↥(leftKer M) :=
          finrank_range_pairAction_le_prod _ _ hkerA hkerB
        have h1 : finrank K ↥(LinearMap.ker M.mulVecLin) + M.rank = n :=
          finrank_ker_mulVecLin_add_rank M
        have h2 : finrank K ↥(leftKer M) + M.rank = n := finrank_leftKer_add_rank M
        omega
      · have hk1 : M.rank = 1 := le_antisymm (by omega) (one_le_rank_of_ne_zero hM0)
        obtain ⟨s, t, hs, ht, hMst⟩ := isRankOneMat_iff_rank_eq_one.2 hk1
        have h1 : finrank K ↥(LinearMap.ker M.mulVecLin) + M.rank = n :=
          finrank_ker_mulVecLin_add_rank M
        have h2 : finrank K ↥(leftKer M) + M.rank = n := finrank_leftKer_add_rank M
        have htu : t ⬝ᵥ u = 0 := by
          have := hMu
          rw [hMst, outer_mulVec] at this
          rcases smul_eq_zero.1 this with h | h
          · exact h
          · exact absurd h hs
        have hphis : phi ⬝ᵥ s = 0 := by
          have := hphiM
          rw [hMst, vecMul_outer] at this
          rcases smul_eq_zero.1 this with h | h
          · exact h
          · exact absurd h ht
        by_cases hcase1 : ∃ v : Vec K n, t ⬝ᵥ v = 0 ∧ phi ⬝ᵥ v ≠ 0
        · obtain ⟨v, hv0, hv1⟩ := hcase1
          have hvmem : v ∈ LinearMap.ker M.mulVecLin := by
            show M *ᵥ v = 0
            rw [hMst, outer_mulVec, hv0, zero_smul]
          have hb : finrank K ↥(LinearMap.range (pairAction f u phi)) + 1 ≤
              finrank K ↥(LinearMap.ker M.mulVecLin) + finrank K ↥(leftKer M) :=
            finrank_range_pairAction_lt_prod _ _ hkerA hkerB
              ⟨(v, 0), ⟨hvmem, (leftKer M).zero_mem⟩, by
                show phi ⬝ᵥ v - (0 : Vec K n) ⬝ᵥ u ≠ 0
                rw [zero_dotProduct, sub_zero]; exact hv1⟩
          omega
        · push_neg at hcase1
          by_cases hcase2 : ∃ alpha : Vec K n, alpha ⬝ᵥ s = 0 ∧ alpha ⬝ᵥ u ≠ 0
          · obtain ⟨alpha, ha0, ha1⟩ := hcase2
            have hamem : alpha ∈ leftKer M := by
              rw [mem_leftKer_iff, hMst, vecMul_outer, ha0, zero_smul]
            have hb : finrank K ↥(LinearMap.range (pairAction f u phi)) + 1 ≤
                finrank K ↥(LinearMap.ker M.mulVecLin) + finrank K ↥(leftKer M) :=
              finrank_range_pairAction_lt_prod _ _ hkerA hkerB
                ⟨(0, alpha), ⟨(LinearMap.ker M.mulVecLin).zero_mem, hamem⟩, by
                  show phi ⬝ᵥ (0 : Vec K n) - alpha ⬝ᵥ u ≠ 0
                  rw [dotProduct_zero, zero_sub, neg_ne_zero]; exact ha1⟩
            omega
          · push_neg at hcase2
            -- now `φ ∈ span t` and `u ∈ span s`, and the whole action lands in a plane
            obtain ⟨lam, hlam⟩ := eq_smul_of_dot_zero_imp ht hcase1
            have hcase2' : ∀ x : Vec K n, s ⬝ᵥ x = 0 → u ⬝ᵥ x = 0 := by
              intro x hx
              rw [dotProduct_comm]
              exact hcase2 x (by rw [dotProduct_comm]; exact hx)
            obtain ⟨mu, hmu⟩ := eq_smul_of_dot_zero_imp hs hcase2'
            have hstruct : ∀ X ∈ commutant f, ∃ c : K, X *ᵥ s = c • s ∧ t ᵥ* X = c • t := by
              intro X hX
              have hXM : X * M = M * X := hcomm X hX
              rw [hMst, mul_outer, outer_mul] at hXM
              exact (outer_eq_outer_iff hs ht).1 hXM.symm
            have hA : ∀ X ∈ commutant f, X *ᵥ u ∈ (K ∙ s) := by
              intro X hX
              obtain ⟨c, hc1, _⟩ := hstruct X hX
              rw [hmu, Matrix.mulVec_smul, hc1, smul_smul]
              exact Submodule.mem_span_singleton.2 ⟨mu * c, rfl⟩
            have hB : ∀ X ∈ commutant f, phi ᵥ* X ∈ (K ∙ t) := by
              intro X hX
              obtain ⟨c, _, hc2⟩ := hstruct X hX
              rw [hlam, Matrix.smul_vecMul, hc2, smul_smul]
              exact Submodule.mem_span_singleton.2 ⟨lam * c, rfl⟩
            have hb : finrank K ↥(LinearMap.range (pairAction f u phi)) ≤
                finrank K ↥(K ∙ s) + finrank K ↥(K ∙ t) :=
              finrank_range_pairAction_le_prod _ _ hA hB
            rw [finrank_span_singleton hs, finrank_span_singleton ht] at hb
            omega
  · -- the three functionals are independent
    exfalso
    have hind : ∀ a0 a1 a2 : K,
        a0 • ((phi, -u) : Vec K n × Vec K n) +
          a1 • ((phi ᵥ* f, -(f *ᵥ u)) : Vec K n × Vec K n) +
          a2 • ((phi ᵥ* (f * f), -((f * f) *ᵥ u)) : Vec K n × Vec K n) = 0 →
        a0 = 0 ∧ a1 = 0 ∧ a2 = 0 := by
      intro a0 a1 a2 hsum
      by_contra hne
      have h1 := congrArg Prod.fst hsum
      have h2 := congrArg Prod.snd hsum
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_zero,
        Prod.snd_zero] at h1 h2
      have hMu : (a0 • (1 : Matrix (Fin n) (Fin n) K) + a1 • f + a2 • (f * f)) *ᵥ u = 0 := by
        rw [Matrix.add_mulVec, Matrix.add_mulVec, smul_mulVec, smul_mulVec, smul_mulVec,
          Matrix.one_mulVec]
        simp only [smul_neg] at h2
        linear_combination (norm := module) -h2
      have hphiM : phi ᵥ* (a0 • (1 : Matrix (Fin n) (Fin n) K) + a1 • f + a2 • (f * f)) = 0 := by
        rw [Matrix.vecMul_add, Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_smul,
          Matrix.vecMul_smul, Matrix.vecMul_one]
        exact h1
      exact hdep ⟨a0, a1, a2, hne, hMu, hphiM⟩
    have hle : LinearMap.range (pairAction f u phi) ≤
        LinearMap.ker (tripleFun ((phi, -u) : Vec K n × Vec K n)
          (phi ᵥ* f, -(f *ᵥ u)) (phi ᵥ* (f * f), -((f * f) *ᵥ u))) := by
      intro x hx
      have e0 : ∀ y ∈ LinearMap.range (pairAction f u phi),
          pairing ((phi, -u) : Vec K n × Vec K n) y = 0 := by
        have := pairing_vanishes_on_range (f := f) (u := u) (phi := phi)
          (g := (1 : Matrix (Fin n) (Fin n) K)) (by intro X _; rw [mul_one, one_mul])
        simpa using this
      have e1 : ∀ y ∈ LinearMap.range (pairAction f u phi),
          pairing ((phi ᵥ* f, -(f *ᵥ u)) : Vec K n × Vec K n) y = 0 :=
        pairing_vanishes_on_range (f := f) (u := u) (phi := phi) (g := f)
          (fun X hX => hX)
      have e2 : ∀ y ∈ LinearMap.range (pairAction f u phi),
          pairing ((phi ᵥ* (f * f), -((f * f) *ᵥ u)) : Vec K n × Vec K n) y = 0 := by
        refine pairing_vanishes_on_range (f := f) (u := u) (phi := phi) (g := f * f) ?_
        intro X hX
        have h1 : X * f = f * X := hX
        rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, h1, ← Matrix.mul_assoc]
      show tripleFun _ _ _ x = 0
      funext i
      fin_cases i
      · exact e0 x hx
      · exact e1 x hx
      · exact e2 x hx
    have := finrank_le_of_three_indep _ _ _ hind _ hle
    omega

end Q655
