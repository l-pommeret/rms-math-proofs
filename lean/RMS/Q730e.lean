import RMS.Q730b

/-!
# Q730, part e : the majorization bookkeeping in the induction step of Weyl–Horn
-/

namespace Q730

open Matrix Finset BigOperators

variable {m : ℕ}

/-- The "predecessor" map, sending `0` and `1` to `0`. -/
def predF : Fin (m + 2) → Fin (m + 1) := fun i => Fin.cases 0 (fun j => j) i

@[simp] lemma predF_succ (j : Fin (m + 1)) : predF j.succ = j := rfl

lemma predF_inj {x y : Fin (m + 2)} (hx : x ≠ 0) (hy : y ≠ 0) (h : predF x = predF y) : x = y := by
  obtain ⟨x', rfl⟩ : ∃ x', x = x'.succ := ⟨x.pred hx, by simp⟩
  obtain ⟨y', rfl⟩ : ∃ y', y = y'.succ := ⟨y.pred hy, by simp⟩
  simp only [predF_succ] at h
  rw [h]

lemma predF_ne_zero {x : Fin (m + 2)} (hx0 : x ≠ 0) (hx1 : x ≠ 1) : predF x ≠ 0 := by
  obtain ⟨x', rfl⟩ : ∃ x', x = x'.succ := ⟨x.pred hx0, by simp⟩
  simp only [predF_succ]
  intro h
  exact hx1 (by rw [h]; rfl)

lemma s_le_scons (s : Fin (m + 2) → ℝ) (d : ℝ) (hbd : s 1 ≤ d) {i : Fin (m + 2)} (hi : i ≠ 0) :
    s i ≤ (Fin.cons d (fun k => s k.succ.succ) : Fin (m + 1) → ℝ) (predF i) := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i'.succ := ⟨i.pred hi, by simp⟩
  refine Fin.cases ?_ ?_ i'
  · simpa using hbd
  · intro i''; simp

lemma s_eq_scons (s : Fin (m + 2) → ℝ) (d : ℝ) {i : Fin (m + 2)} (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    (Fin.cons d (fun k => s k.succ.succ) : Fin (m + 1) → ℝ) (predF i) = s i := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i'.succ := ⟨i.pred hi0, by simp⟩
  revert hi1
  refine Fin.cases ?_ ?_ i'
  · intro hi1; exact absurd rfl hi1
  · intro i'' _; simp

lemma predF_injOn {S : Finset (Fin (m + 2))} (h0 : (0 : Fin (m + 2)) ∉ S) :
    Set.InjOn predF (S : Set (Fin (m + 2))) := by
  intro x hx y hy h
  exact predF_inj (fun hx0 => h0 (hx0 ▸ hx)) (fun hy0 => h0 (hy0 ▸ hy)) h

/-- Transferring a product over indices `≠ 0` to the shortened family. -/
lemma transfer1 (s : Fin (m + 2) → ℝ) (d : ℝ) (hs0 : ∀ i, 0 ≤ s i) (hbd : s 1 ≤ d)
    (S : Finset (Fin (m + 2))) (h0 : (0 : Fin (m + 2)) ∉ S) :
    (S.image predF).card = S.card ∧
      ∏ i ∈ S, s i ≤ ∏ j ∈ S.image predF,
        (Fin.cons d (fun k => s k.succ.succ) : Fin (m + 1) → ℝ) j := by
  have hinj := predF_injOn h0
  refine ⟨Finset.card_image_of_injOn hinj, ?_⟩
  rw [Finset.prod_image hinj]
  exact Finset.prod_le_prod (fun i _ => hs0 i)
    (fun i hi => s_le_scons s d hbd (fun h0' => h0 (h0' ▸ hi)))

/-- Transferring a product over indices `≠ 0, 1`, gaining the new first entry `d`. -/
lemma transfer2 (s : Fin (m + 2) → ℝ) (d : ℝ)
    (S : Finset (Fin (m + 2))) (h0 : (0 : Fin (m + 2)) ∉ S) (h1 : (1 : Fin (m + 2)) ∉ S) :
    (insert 0 (S.image predF)).card = S.card + 1 ∧
      ∏ j ∈ insert 0 (S.image predF),
        (Fin.cons d (fun k => s k.succ.succ) : Fin (m + 1) → ℝ) j = d * ∏ i ∈ S, s i := by
  have hinj := predF_injOn h0
  have hnot : (0 : Fin (m + 1)) ∉ S.image predF := by
    simp only [Finset.mem_image, not_exists]
    rintro x ⟨hx, hx0⟩
    exact predF_ne_zero (fun h => h0 (h ▸ hx)) (fun h => h1 (h ▸ hx)) hx0
  refine ⟨by rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj], ?_⟩
  rw [Finset.prod_insert hnot, Finset.prod_image hinj]
  congr 1
  refine Finset.prod_congr rfl (fun i hi => ?_)
  exact s_eq_scons s d (fun h => h0 (h ▸ hi)) (fun h => h1 (h ▸ hi))

/-- The inductive step for weak log-majorization.  Here `a = ‖lam 0‖` is the largest of the
`‖lam i‖`, `s 0` is the largest of the `s i` and `s 1` is the largest of the `s i`, `i ≠ 0`,
which are `≤ a`.  Deleting `lam 0` from the list `lam` and replacing `s 0, s 1` by the single
number `d = s 0 * s 1 / a` preserves weak log-majorization. -/
theorem logMajLE_step (s : Fin (m + 2) → ℝ) (lam : Fin (m + 2) → ℂ) (hs0 : ∀ i, 0 ≤ s i)
    (hmaj : LogMajLE s fun i => ‖lam i‖)
    (hlam_max : ∀ i, ‖lam i‖ ≤ ‖lam 0‖) (ha : 0 < ‖lam 0‖)
    (hsmax : ∀ i, s i ≤ s 0)
    (hs1max : ∀ i, i ≠ 0 → s i ≤ ‖lam 0‖ → s i ≤ s 1) :
    LogMajLE (Fin.cons (s 0 * s 1 / ‖lam 0‖) fun i => s i.succ.succ)
      (fun i => ‖lam i.succ‖) := by
  classical
  set a := ‖lam 0‖ with hadef
  set d := s 0 * s 1 / a with hddef
  set s' : Fin (m + 1) → ℝ := Fin.cons d (fun i => s i.succ.succ) with hs'def
  have hs00 : 0 ≤ s 0 := hs0 0
  have hs10 : 0 ≤ s 1 := hs0 1
  -- `s 0` dominates `a`
  have ha0 : a ≤ s 0 := by
    obtain ⟨J, hJcard, hJle⟩ := hmaj {0}
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 (by simpa using hJcard)
    simp only [Finset.prod_singleton] at hJle
    exact le_trans (by simpa using hJle) (hsmax j)
  have had : a * d = s 0 * s 1 := by
    rw [hddef]; field_simp
  have hd0 : 0 ≤ d := by
    rw [hddef]; positivity
  have hbd : s 1 ≤ d := by
    rw [hddef, le_div_iff₀ ha]
    nlinarith
  intro I'
  set I : Finset (Fin (m + 2)) := I'.image Fin.succ with hIdef
  have hI0 : (0 : Fin (m + 2)) ∉ I := by
    simp only [hIdef, Finset.mem_image, not_exists]
    rintro x ⟨-, hx⟩
    exact (Fin.succ_ne_zero x) hx
  have hIcard : I.card = I'.card :=
    Finset.card_image_of_injective _ (Fin.succ_injective _)
  have hIprod : ∏ i ∈ I, ‖lam i‖ = ∏ i ∈ I', ‖lam i.succ‖ := by
    rw [hIdef, Finset.prod_image (fun x _ y _ h => Fin.succ_injective _ h)]
  set P : ℝ := ∏ i ∈ I, ‖lam i‖ with hPdef
  have hP0 : 0 ≤ P := Finset.prod_nonneg (fun i _ => norm_nonneg _)
  have hPa : P ≤ a ^ I.card := by
    calc P ≤ ∏ _i ∈ I, a := Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hlam_max i)
      _ = a ^ I.card := by rw [Finset.prod_const]
  suffices h : ∃ S' : Finset (Fin (m + 1)), S'.card = I.card ∧ P ≤ ∏ j ∈ S', s' j by
    obtain ⟨S', h1, h2⟩ := h
    exact ⟨S', by rw [h1, hIcard], by rw [← hIprod]; exact h2⟩
  -- a set of indices `≠ 0` with large product does the job
  have final : ∀ S : Finset (Fin (m + 2)), (0 : Fin (m + 2)) ∉ S → S.card = I.card →
      P ≤ ∏ i ∈ S, s i → ∃ S' : Finset (Fin (m + 1)), S'.card = I.card ∧ P ≤ ∏ j ∈ S', s' j := by
    intro S h0 hcard hle
    obtain ⟨hc, hp⟩ := transfer1 s d hs0 hbd S h0
    exact ⟨S.image predF, by rw [hc, hcard], hle.trans hp⟩
  obtain ⟨J, hJcard, hJle⟩ := hmaj (insert 0 I)
  rw [Finset.card_insert_of_notMem hI0] at hJcard
  rw [Finset.prod_insert hI0] at hJle
  by_cases h0J : (0 : Fin (m + 2)) ∈ J
  · set T : Finset (Fin (m + 2)) := J.erase 0 with hTdef
    have hT0 : (0 : Fin (m + 2)) ∉ T := Finset.notMem_erase _ _
    have hTcard : T.card = I.card := by
      rw [hTdef, Finset.card_erase_of_mem h0J, hJcard]
      simp
    have hprodJ : ∏ j ∈ J, s j = s 0 * ∏ i ∈ T, s i := (Finset.mul_prod_erase J s h0J).symm
    rw [hprodJ] at hJle
    by_cases h1T : (1 : Fin (m + 2)) ∈ T
    · -- the second index is available: use it to build the new first entry
      have hinj := predF_injOn hT0
      have hprod : ∏ j ∈ T.image predF, s' j = d * ∏ i ∈ T.erase 1, s i := by
        rw [Finset.prod_image hinj, ← Finset.mul_prod_erase T (fun x => s' (predF x)) h1T]
        have h1 : s' (predF (1 : Fin (m + 2))) = d := by
          have h1' : (1 : Fin (m + 2)) = Fin.succ 0 := by ext; simp
          rw [h1', predF_succ, hs'def, Fin.cons_zero]
        rw [h1]
        congr 1
        refine Finset.prod_congr rfl (fun i hi => ?_)
        exact s_eq_scons s d (fun h => hT0 (h ▸ Finset.mem_of_mem_erase hi))
          (fun h => (Finset.notMem_erase 1 T) (h ▸ hi))
      have hTprod : ∏ i ∈ T, s i = s 1 * ∏ i ∈ T.erase 1, s i := (Finset.mul_prod_erase T s h1T).symm
      refine ⟨T.image predF, by rw [Finset.card_image_of_injOn hinj, hTcard], ?_⟩
      rw [hprod]
      have hrest : 0 ≤ ∏ i ∈ T.erase 1, s i := Finset.prod_nonneg (fun i _ => hs0 i)
      rw [hTprod] at hJle
      -- `a * P ≤ s 0 * (s 1 * ∏) = a * d * ∏`
      have : a * P ≤ a * (d * ∏ i ∈ T.erase 1, s i) := by
        calc a * P ≤ s 0 * (s 1 * ∏ i ∈ T.erase 1, s i) := hJle
          _ = (a * d) * ∏ i ∈ T.erase 1, s i := by rw [had]; ring
          _ = a * (d * ∏ i ∈ T.erase 1, s i) := by ring
      exact le_of_mul_le_mul_left this ha
    · by_cases hex : ∃ i ∈ T, s i ≤ a
      · obtain ⟨i, hiT, hia⟩ := hex
        have hi0 : i ≠ 0 := fun h => hT0 (h ▸ hiT)
        have hi1 : s i ≤ s 1 := hs1max i hi0 hia
        have hE0 : (0 : Fin (m + 2)) ∉ T.erase i := fun h => hT0 (Finset.mem_of_mem_erase h)
        have hE1 : (1 : Fin (m + 2)) ∉ T.erase i := fun h => h1T (Finset.mem_of_mem_erase h)
        obtain ⟨hc, hp⟩ := transfer2 s d (T.erase i) hE0 hE1
        refine ⟨insert 0 ((T.erase i).image predF), ?_, ?_⟩
        · rw [hc, Finset.card_erase_of_mem hiT, hTcard]
          have : 1 ≤ I.card := by
            rw [← hTcard]
            exact Finset.card_pos.2 ⟨i, hiT⟩
          omega
        · rw [hp]
          have hrest : 0 ≤ ∏ k ∈ T.erase i, s k := Finset.prod_nonneg (fun k _ => hs0 k)
          have hTprod : ∏ k ∈ T, s k = s i * ∏ k ∈ T.erase i, s k :=
            (Finset.mul_prod_erase T s hiT).symm
          rw [hTprod] at hJle
          have hstep : a * P ≤ a * (d * ∏ k ∈ T.erase i, s k) := by
            calc a * P ≤ s 0 * (s i * ∏ k ∈ T.erase i, s k) := hJle
              _ ≤ s 0 * (s 1 * ∏ k ∈ T.erase i, s k) := by
                  have : s i * ∏ k ∈ T.erase i, s k ≤ s 1 * ∏ k ∈ T.erase i, s k :=
                    mul_le_mul_of_nonneg_right hi1 hrest
                  exact mul_le_mul_of_nonneg_left this hs00
              _ = (a * d) * ∏ k ∈ T.erase i, s k := by rw [had]; ring
              _ = a * (d * ∏ k ∈ T.erase i, s k) := by ring
          exact le_of_mul_le_mul_left hstep ha
      · push_neg at hex
        refine final T hT0 hTcard ?_
        calc P ≤ a ^ I.card := hPa
          _ = ∏ _i ∈ T, a := by rw [Finset.prod_const, hTcard]
          _ ≤ ∏ i ∈ T, s i :=
              Finset.prod_le_prod (fun i _ => ha.le) (fun i hi => (hex i hi).le)
  · by_cases hex : ∃ i ∈ J, s i ≤ a
    · obtain ⟨i, hiJ, hia⟩ := hex
      have hE0 : (0 : Fin (m + 2)) ∉ J.erase i := fun h => h0J (Finset.mem_of_mem_erase h)
      refine final (J.erase i) hE0 ?_ ?_
      · rw [Finset.card_erase_of_mem hiJ, hJcard]
        simp
      · have hrest : 0 ≤ ∏ k ∈ J.erase i, s k := Finset.prod_nonneg (fun k _ => hs0 k)
        have hJprod : ∏ k ∈ J, s k = s i * ∏ k ∈ J.erase i, s k :=
          (Finset.mul_prod_erase J s hiJ).symm
        rw [hJprod] at hJle
        rcases eq_or_lt_of_le (hs0 i) with hsi | hsi
        · -- `s i = 0` forces `P = 0`
          have hP : P = 0 := by
            have : a * P ≤ 0 := hJle.trans (le_of_eq (by rw [← hsi]; ring))
            nlinarith
          rw [hP]; exact hrest
        · have h1 : s i * P ≤ s i * ∏ k ∈ J.erase i, s k := by
            calc s i * P ≤ a * P := mul_le_mul_of_nonneg_right hia hP0
              _ ≤ s i * ∏ k ∈ J.erase i, s k := hJle
          exact le_of_mul_le_mul_left h1 hsi
    · push_neg at hex
      obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (s := J) (n := I.card)
        (by rw [hJcard]; omega)
      have hS0 : (0 : Fin (m + 2)) ∉ S := fun h => h0J (hSsub h)
      refine final S hS0 hScard ?_
      calc P ≤ a ^ I.card := hPa
        _ = ∏ _i ∈ S, a := by rw [Finset.prod_const, hScard]
        _ ≤ ∏ i ∈ S, s i :=
            Finset.prod_le_prod (fun i _ => ha.le) (fun i hi => (hex i (hSsub hi)).le)

end Q730
