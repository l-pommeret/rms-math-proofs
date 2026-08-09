import RMS.Q730c
import RMS.Q730d
import RMS.Q730e

/-!
# Q730, part f : the constructive half of Weyl–Horn
-/

namespace Q730

open Matrix Finset BigOperators

variable {n m : ℕ}

/-- The statement of the constructive half of the Weyl–Horn theorem in dimension `n`:
given nonnegative `s` and prescribed diagonal `lam` satisfying weak log-majorization and
the product identity, there is an upper triangular matrix with singular values `s` and
diagonal `lam`. -/
def WHProp (n : ℕ) : Prop :=
  ∀ (s : Fin n → ℝ) (lam : Fin n → ℂ), (∀ i, 0 ≤ s i) →
    LogMajLE s (fun i => ‖lam i‖) → (∏ i, ‖lam i‖ = ∏ i, s i) →
    ∃ A : Matrix (Fin n) (Fin n) ℂ, HasSV A s ∧ A.BlockTriangular id ∧ ∀ i, A i i = lam i

/-! ### The weighted cyclic shift, used when all prescribed diagonal entries vanish -/

/-- The weighted cyclic shift matrix: `s j` in position `(j - 1, j)`. -/
noncomputable def shiftM (s : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (Equiv.addRight (1 : Fin (n + 1))).permMatrix ℂ * diagonal (fun i => (s i : ℂ))

lemma shiftM_hasSV (s : Fin (n + 1) → ℝ) : HasSV (shiftM s) s :=
  ⟨_, 1, permMatrix_unitary _, one_mem _, (mul_one _).symm⟩

lemma shiftM_apply (s : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    shiftM s i j = if i + 1 = j then (s j : ℂ) else 0 := by
  rw [shiftM, Matrix.mul_diagonal]
  have : (Equiv.addRight (1 : Fin (n + 1))).permMatrix ℂ i j = if i + 1 = j then 1 else 0 := by
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  rw [this]
  split <;> simp

lemma shiftM_apply_eq_zero (s : Fin (n + 1) → ℝ) (h0 : s 0 = 0) {i j : Fin (n + 1)}
    (hij : (j : ℕ) ≤ (i : ℕ)) : shiftM s i j = 0 := by
  rw [shiftM_apply]
  split
  · next h =>
    by_cases hlast : i = Fin.last n
    · have hj : j = 0 := by rw [← h, hlast, Fin.last_add_one]
      rw [hj, h0]
      simp
    · exfalso
      have hval : ((i + 1 : Fin (n + 1)) : ℕ) = (i : ℕ) + 1 := by
        rw [Fin.val_add_one, if_neg hlast]
      rw [h] at hval
      omega
  · rfl

/-! ### The base cases -/

lemma WH_zero : WHProp 0 := by
  intro s lam _ _ _
  refine ⟨0, ⟨1, 1, one_mem _, one_mem _, ?_⟩, ?_, ?_⟩
  · exact Subsingleton.elim _ _
  · intro i j _
    exact absurd i.2 (by omega)
  · intro i
    exact absurd i.2 (by omega)

lemma WH_one : WHProp 1 := by
  intro s lam hs0 _ hprod
  have hlam : ‖lam 0‖ = s 0 := by simpa using hprod
  refine ⟨Matrix.of fun _ _ => lam 0, ?_, ?_, ?_⟩
  · have hmul : (Matrix.of fun _ _ => lam 0 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ *
        (Matrix.of fun _ _ => lam 0) =
        (1 : Matrix (Fin 1) (Fin 1) ℂ) * diagonal (fun i => (((s i) ^ 2 : ℝ) : ℂ)) * 1ᴴ := by
      ext i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst hi; subst hj
      rw [Matrix.mul_apply]
      simp only [Fin.sum_univ_one, Matrix.conjTranspose_apply, Matrix.of_apply,
        Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.diagonal_apply_eq]
      rw [mul_comm, RCLike.star_def, Complex.mul_conj]
      rw [← hlam]
      norm_cast
      exact Complex.normSq_eq_norm_sq _
    have := hasSV_of_conjTranspose_mul_self (A := (Matrix.of fun _ _ => lam 0 :
      Matrix (Fin 1) (Fin 1) ℂ)) (U := 1) (e := fun i => (s i) ^ 2) (one_mem _)
      (fun i => sq_nonneg _) hmul
    have heq : (fun i => Real.sqrt ((s i) ^ 2)) = s := funext fun i => Real.sqrt_sq (hs0 i)
    rwa [heq] at this
  · intro i j hij
    rw [Subsingleton.elim i j] at hij
    exact absurd hij (lt_irrefl _)
  · intro i
    rw [Subsingleton.elim i 0]
    rfl

/-- The case where all prescribed diagonal entries are `0`; then one of the singular values
must vanish and a weighted cyclic shift does the job. -/
lemma WH_lam_zero (s : Fin (n + 1) → ℝ) (lam : Fin (n + 1) → ℂ)
    (hlam : ∀ i, lam i = 0) (hprod : ∏ i, s i = 0) :
    ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      HasSV A s ∧ A.BlockTriangular id ∧ ∀ i, A i i = lam i := by
  classical
  obtain ⟨k₀, -, hk₀⟩ := Finset.prod_eq_zero_iff.1 hprod
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 k₀ with hσ
  set s₂ : Fin (n + 1) → ℝ := s ∘ σ with hs₂
  have hs₂0 : s₂ 0 = 0 := by
    simp [hs₂, hσ, hk₀]
  refine ⟨shiftM s₂, ?_, ?_, ?_⟩
  · have h := (shiftM_hasSV s₂).perm σ⁻¹
    have : (s₂ ∘ (σ⁻¹ : Equiv.Perm (Fin (n + 1)))) = s := by
      funext i
      simp [hs₂]
    rwa [this] at h
  · intro i j hij
    exact shiftM_apply_eq_zero s₂ hs₂0 (le_of_lt hij)
  · intro i
    rw [hlam i]
    exact shiftM_apply_eq_zero s₂ hs₂0 (le_refl _)

/-! ### The inductive step -/

lemma le_s0_of_logMajLE {s : Fin (n + 1) → ℝ} {lam : Fin (n + 1) → ℂ}
    (hmaj : LogMajLE s fun i => ‖lam i‖) (hsmax : ∀ i, s i ≤ s 0) : ‖lam 0‖ ≤ s 0 := by
  obtain ⟨J, hJcard, hJle⟩ := hmaj {0}
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 (by simpa using hJcard)
  simp only [Finset.prod_singleton] at hJle
  exact le_trans (by simpa using hJle) (hsmax j)

lemma cons_zero_zero : (Fin.cons (0 : ℂ) 0 : Fin (m + 1) → ℂ) = 0 := by
  funext i
  refine Fin.cases ?_ ?_ i <;> simp

/-- The inductive step of the construction, in normalized position: `‖lam 0‖` is the largest
of the `‖lam i‖` and is positive, `s 0` is the largest of the `s i`, and `s 1` is the largest
of the `s i` with `i ≠ 0` which are at most `‖lam 0‖`. -/
lemma WH_step (m : ℕ) (ih : WHProp (m + 1)) (s : Fin (m + 2) → ℝ) (lam : Fin (m + 2) → ℂ)
    (hs0 : ∀ i, 0 ≤ s i) (hmaj : LogMajLE s fun i => ‖lam i‖)
    (hprod : ∏ i, ‖lam i‖ = ∏ i, s i)
    (hlam_max : ∀ i, ‖lam i‖ ≤ ‖lam 0‖) (ha : 0 < ‖lam 0‖)
    (hsmax : ∀ i, s i ≤ s 0) (hs1a : s 1 ≤ ‖lam 0‖)
    (hs1max : ∀ i, i ≠ 0 → s i ≤ ‖lam 0‖ → s i ≤ s 1) :
    ∃ A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ,
      HasSV A s ∧ A.BlockTriangular id ∧ ∀ i, A i i = lam i := by
  classical
  set a := ‖lam 0‖ with hadef
  set d : ℝ := s 0 * s 1 / a with hddef
  set mu : ℝ := Real.sqrt ((s 0 ^ 2 - a ^ 2) * (a ^ 2 - s 1 ^ 2)) / a with hmudef
  set s' : Fin (m + 1) → ℝ := Fin.cons d (fun i => s i.succ.succ) with hs'def
  have ha0 : a ≤ s 0 := le_s0_of_logMajLE hmaj hsmax
  have hd0 : 0 ≤ d := by
    rw [hddef]
    exact div_nonneg (mul_nonneg (hs0 0) (hs0 1)) ha.le
  have had : a * d = s 0 * s 1 := by rw [hddef]; field_simp
  have hs'0 : ∀ i, 0 ≤ s' i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa [hs'def] using hd0
    · intro j; simpa [hs'def] using hs0 j.succ.succ
  have hmaj' : LogMajLE s' (fun i => ‖lam i.succ‖) :=
    logMajLE_step s lam hs0 hmaj hlam_max ha hsmax hs1max
  have hprod' : ∏ i : Fin (m + 1), ‖lam i.succ‖ = ∏ i, s' i := by
    have h1 : ∏ i, ‖lam i‖ = a * ∏ i : Fin (m + 1), ‖lam i.succ‖ := by
      rw [Fin.prod_univ_succ]
    have h2 : ∏ i, s i = s 0 * (s 1 * ∏ i : Fin m, s i.succ.succ) := by
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.succ_zero_eq_one]
    have h3 : ∏ i, s' i = d * ∏ i : Fin m, s i.succ.succ := by
      rw [Fin.prod_univ_succ, hs'def]
      simp
    rw [h1, h2] at hprod
    rw [h3]
    have : a * ∏ i : Fin (m + 1), ‖lam i.succ‖ = a * (d * ∏ i : Fin m, s i.succ.succ) := by
      rw [hprod, ← mul_assoc, ← had, mul_assoc]
    exact mul_left_cancel₀ (ne_of_gt ha) this
  obtain ⟨C, hCsv, hCtri, hCdiag⟩ := ih s' (fun i => lam i.succ) hs'0 hmaj' hprod'
  obtain ⟨P, Q, hP, hQ, hCeq⟩ := hCsv
  -- the two-by-two corner
  have hmu2 : mu ^ 2 = ((s 0 ^ 2 - a ^ 2) * (a ^ 2 - s 1 ^ 2)) / a ^ 2 := by
    rw [hmudef, div_pow, Real.sq_sqrt]
    have h1 : 0 ≤ s 0 ^ 2 - a ^ 2 := by nlinarith [ha.le, hs0 0]
    have h2 : 0 ≤ a ^ 2 - s 1 ^ 2 := by nlinarith [hs0 1, hs1a]
    positivity
  have hH : HasSV !![lam 0, (mu : ℂ); 0, (d : ℂ)] ![s 0, s 1] := by
    refine hasSV_two (lam 0) mu d (s 0) (s 1) hd0 (hs0 0) (hs0 1) had ?_
    rw [hmu2, hddef]
    field_simp
    ring
  have hdiag : blk ((d : ℝ) : ℂ) 0 0 (diagonal fun i : Fin m => ((s i.succ.succ : ℝ) : ℂ))
      = diagonal (fun i => ((s' i : ℝ) : ℂ)) := by
    have hs'eq : (fun i => ((s' i : ℝ) : ℂ))
        = Fin.cons ((d : ℝ) : ℂ) (fun i : Fin m => ((s i.succ.succ : ℝ) : ℂ)) := by
      funext i
      refine Fin.cases ?_ ?_ i <;> simp [hs'def]
    rw [hs'eq, blk_diagonal]
  have hA₀sv : HasSV (blk (lam 0) (Fin.cons (mu : ℂ) 0) 0
      (diagonal fun i => ((s' i : ℝ) : ℂ))) s := by
    have hb : HasSV (blk (lam 0) (Fin.cons (mu : ℂ) 0) (Fin.cons (0 : ℂ) 0)
        (blk ((d : ℝ) : ℂ) 0 0 (diagonal fun i : Fin m => ((s i.succ.succ : ℝ) : ℂ)))) s :=
      hasSV_blk_two !![lam 0, (mu : ℂ); 0, (d : ℂ)] ![s 0, s 1] hH
        (fun i : Fin m => s i.succ.succ) s rfl rfl (fun i => rfl)
    rwa [cons_zero_zero, hdiag] at hb
  have hAeq : blk (lam 0) ((Fin.cons (mu : ℂ) 0) ᵥ* Q) 0 C
      = blk 1 0 0 P * (blk (lam 0) (Fin.cons (mu : ℂ) 0) 0
          (diagonal fun i => ((s' i : ℝ) : ℂ))) * blk 1 0 0 Q := by
    rw [blk_mul, blk_mul, hCeq]
    congr 1 <;> simp
  refine ⟨blk (lam 0) ((Fin.cons (mu : ℂ) 0) ᵥ* Q) 0 C, ?_, ?_, ?_⟩
  · rw [hAeq]
    exact hA₀sv.mul_unitary (blk_unitary hP) (blk_unitary hQ)
  · exact (blk_blockTriangular _ _ _).2 hCtri
  · intro i
    refine Fin.cases ?_ ?_ i
    · rw [blk_zero_zero]
    · intro j
      rw [blk_succ_succ]
      exact hCdiag j

/-- Reduction of the general case in dimension `m + 2` to the normalized one. -/
lemma WH_succ_succ (m : ℕ) (ih : WHProp (m + 1)) : WHProp (m + 2) := by
  classical
  intro s lam hs0 hmaj hprod
  by_cases hz : ∀ i, lam i = 0
  · refine WH_lam_zero s lam hz ?_
    rw [← hprod]
    exact Finset.prod_eq_zero (Finset.mem_univ 0) (by rw [hz 0]; simp)
  push_neg at hz
  obtain ⟨i₁, hi₁⟩ := hz
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_max_image (univ : Finset (Fin (m + 2))) (fun i => ‖lam i‖) univ_nonempty
  set p : Equiv.Perm (Fin (m + 2)) := Equiv.swap 0 i₀ with hp
  have hp0 : p 0 = i₀ := by simp [hp]
  set a : ℝ := ‖lam i₀‖ with hadef
  have ha : 0 < a := lt_of_lt_of_le (norm_pos_iff.2 hi₁) (hi₀ i₁ (Finset.mem_univ _))
  have hamax : ∀ i, ‖lam i‖ ≤ a := fun i => hi₀ i (Finset.mem_univ _)
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image (univ : Finset (Fin (m + 2))) s univ_nonempty
  set q₀ : Equiv.Perm (Fin (m + 2)) := Equiv.swap 0 j₀ with hq₀
  set s₁ : Fin (m + 2) → ℝ := s ∘ q₀ with hs₁def
  have hs₁0 : s₁ 0 = s j₀ := by simp [hs₁def, hq₀]
  have hs₁max : ∀ i, s₁ i ≤ s₁ 0 := by
    intro i
    rw [hs₁0]
    exact hj₀ _ (Finset.mem_univ _)
  have hs₁nonneg : ∀ i, 0 ≤ s₁ i := fun i => hs0 _
  have hs₁prod : ∏ i, s₁ i = ∏ i, s i := Equiv.prod_comp q₀ s
  -- the set of indices `≠ 0` whose value is at most `a` is nonempty
  have hSne : (univ.filter (fun i : Fin (m + 2) => i ≠ 0 ∧ s₁ i ≤ a)).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hempty
    have hgt : ∀ i : Fin (m + 1), a < s₁ i.succ := by
      intro i
      have := hempty (Finset.mem_univ i.succ)
      push_neg at this
      exact this (Fin.succ_ne_zero i)
    have h1 : a ^ (m + 1) ≤ ∏ i : Fin (m + 1), s₁ i.succ :=
      calc a ^ (m + 1) = ∏ _i : Fin (m + 1), a := by rw [Finset.prod_const]; simp
        _ ≤ ∏ i : Fin (m + 1), s₁ i.succ :=
            Finset.prod_le_prod (fun i _ => ha.le) (fun i _ => (hgt i).le)
    have h2 : a < s₁ 0 := lt_of_lt_of_le (hgt 0) (hs₁max _)
    have h3 : a ^ (m + 2) < ∏ i, s₁ i := by
      rw [Fin.prod_univ_succ]
      calc a ^ (m + 2) = a * a ^ (m + 1) := by ring
        _ < s₁ 0 * a ^ (m + 1) := by
            exact mul_lt_mul_of_pos_right h2 (by positivity)
        _ ≤ s₁ 0 * ∏ i : Fin (m + 1), s₁ i.succ :=
            mul_le_mul_of_nonneg_left h1 (le_trans ha.le h2.le)
    have h4 : ∏ i, ‖lam i‖ ≤ a ^ (m + 2) := by
      calc ∏ i, ‖lam i‖ ≤ ∏ _i : Fin (m + 2), a :=
            Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hamax i)
        _ = a ^ (m + 2) := by rw [Finset.prod_const]; simp
    rw [hprod, ← hs₁prod] at h4
    linarith
  obtain ⟨j₁, hj₁mem, hj₁⟩ :=
    Finset.exists_max_image (univ.filter (fun i : Fin (m + 2) => i ≠ 0 ∧ s₁ i ≤ a)) s₁ hSne
  rw [Finset.mem_filter] at hj₁mem
  obtain ⟨-, hj₁ne, hj₁a⟩ := hj₁mem
  set q : Equiv.Perm (Fin (m + 2)) := q₀ * Equiv.swap 1 j₁ with hqdef
  set t : Fin (m + 2) → ℝ := s ∘ q with htdef
  have htapp : ∀ i, t i = s₁ (Equiv.swap 1 j₁ i) := by
    intro i; rfl
  have ht0 : t 0 = s₁ 0 := by
    rw [htapp]
    rw [Equiv.swap_apply_of_ne_of_ne (by simp) (Ne.symm hj₁ne)]
  have ht1 : t 1 = s₁ j₁ := by
    rw [htapp, Equiv.swap_apply_left]
  -- the normalized data
  have hlam_max' : ∀ i, ‖(lam ∘ p) i‖ ≤ ‖(lam ∘ p) 0‖ := by
    intro i
    simp only [Function.comp_apply, hp0]
    exact hamax _
  have ha' : 0 < ‖(lam ∘ p) 0‖ := by
    simp only [Function.comp_apply, hp0]
    exact ha
  have htnonneg : ∀ i, 0 ≤ t i := fun i => hs0 _
  have htmax : ∀ i, t i ≤ t 0 := by
    intro i
    rw [ht0, htapp]
    exact hs₁max _
  have ht1a : t 1 ≤ ‖(lam ∘ p) 0‖ := by
    simp only [Function.comp_apply, hp0]
    rw [ht1]
    exact hj₁a
  have ht1max : ∀ i, i ≠ 0 → t i ≤ ‖(lam ∘ p) 0‖ → t i ≤ t 1 := by
    intro i hi hle
    simp only [Function.comp_apply, hp0] at hle
    rw [ht1]
    rw [htapp] at hle ⊢
    refine hj₁ _ ?_
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, hle⟩
    intro h0
    exact hi (by
      have := congrArg (Equiv.swap (1 : Fin (m + 2)) j₁) h0
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_of_ne_of_ne (by simp) (Ne.symm hj₁ne)] at this)
  have hmajt : LogMajLE t (fun i => ‖(lam ∘ p) i‖) := hmaj.perm q p
  have hprodt : ∏ i, ‖(lam ∘ p) i‖ = ∏ i, t i := by
    rw [htdef]
    rw [show (∏ i, ‖(lam ∘ p) i‖) = ∏ i, ‖lam i‖ from Equiv.prod_comp p (fun i => ‖lam i‖),
      show (∏ i, (s ∘ q) i) = ∏ i, s i from Equiv.prod_comp q s]
    exact hprod
  obtain ⟨A, hAsv, hAtri, hAdiag⟩ :=
    WH_step m ih t (lam ∘ p) htnonneg hmajt hprodt hlam_max' ha' htmax ht1a ht1max
  -- undo the permutations
  obtain ⟨W, hW, hWtri, hWdiag⟩ := exists_unitary_conj_perm_diag hAtri p⁻¹
  refine ⟨Wᴴ * A * W, ?_, hWtri, ?_⟩
  · have h := hAsv.perm q⁻¹
    have heq : (t ∘ (q⁻¹ : Equiv.Perm (Fin (m + 2)))) = s := by
      funext i
      simp [htdef]
    rw [heq] at h
    exact h.mul_unitary (unitary_conjTranspose hW) hW
  · intro i
    rw [hWdiag i, hAdiag]
    simp

theorem WH_core : ∀ n, WHProp n
  | 0 => WH_zero
  | 1 => WH_one
  | (m + 2) => WH_succ_succ m (WH_core (m + 1))

end Q730
