/-
# Q764 — Stage 3c.4: the exact ordered-line `k`-center algorithm

This module assembles the three phases

* the block-cost table (`RequestProject.Q764LineTable`, `O(n^2)` operations),
* the bottleneck dynamic program (`RequestProject.Q764LineDP`, `O(k*n)` operations),
* the reconstruction of the centres and the padding to exactly `k` centres
  (`O(k*n + n)` operations),

into one costed run `Q764.Line.lineKCenterRun`, and proves

* `Q764.Line.lineKCenter_correct`: the run outputs a set of exactly `k` of the `n` input
  points whose covering radius for the original point set `{x 0, …, x (n-1)} : Finset ℝ`
  is minimal among all `k`-element subsets;
* `Q764.Line.lineKCenter_work_le`: the same run performs at most `100 * (n^2 + k*n)`
  unit-cost operations.
-/
import RMS.Q764LineDP

open Finset

namespace Q764

namespace Line

variable {x : ℕ → ℝ}

/-! ## Finiteness of the prefix optima -/

lemma rho_antitone_blocks_le (hx : Monotone x) {p q : ℕ} (h : p ≤ q) (j : ℕ) :
    rho x q j ≤ rho x p j := by
  induction h with
  | refl => exact le_rfl
  | step h ih => exact le_trans (rho_antitone_blocks hx _ j) ih

lemma rho_ne_top (hx : Monotone x) {p : ℕ} (hp : 1 ≤ p) (j : ℕ) : rho x p j ≠ ⊤ := by
  have h2 : ∃ v : ℝ, rho x 1 j ≤ ((v : ℝ) : WithTop ℝ) := by
    cases j with
    | zero => exact ⟨0, by simp⟩
    | succ m =>
        refine ⟨bcost x 0 m, ?_⟩
        rw [rho_succ_succ]
        refine le_trans (Finset.inf'_le _ (mem_range.2 (Nat.succ_pos m))) ?_
        have : rho x 0 0 = 0 := rfl
        rw [this]
        refine max_le ?_ le_rfl
        exact_mod_cast bcost_nonneg hx 0 m
  obtain ⟨v, hv⟩ := h2
  have h1 : rho x p j ≤ ((v : ℝ) : WithTop ℝ) := le_trans (rho_antitone_blocks_le hx hp j) hv
  intro htop
  rw [htop] at h1
  exact absurd (top_le_iff.1 h1) (by simp)

/-- The recurrence, read off from a minimizer. -/
lemma rho_succ_eq_of_argmin {p m arg : ℕ} (harg : arg ≤ m)
    (hmin : ∀ i, i ≤ m →
      max (rho x p arg) (((bcost x arg m : ℝ) : WithTop ℝ))
        ≤ max (rho x p i) (((bcost x i m : ℝ) : WithTop ℝ))) :
    rho x p.succ (m + 1) = max (rho x p arg) (((bcost x arg m : ℝ) : WithTop ℝ)) := by
  rw [rho_succ_succ]
  exact inf'_eq_of_argmin harg hmin

/-! ## Phase 3: reconstruction of the centres -/

/-- The centres of the blocks are correctly recorded in the table. -/
def CenOK (x : ℕ → ℝ) (n : ℕ) (cen : ℕ → ℕ) : Prop :=
  ∀ i j, i ≤ j → j < n →
    i ≤ cen (i * n + j) ∧ cen (i * n + j) ≤ j ∧
      max (x (cen (i * n + j)) - x i) (x j - x (cen (i * n + j))) = bcost x i j

/-- The state of the reconstruction. -/
structure ReconState where
  mark : ℕ → Bool
  cent : Finset ℕ
  cnt : ℕ
  p : ℕ
  j : ℕ

/-- One step of the reconstruction: find the optimal last block, take its centre. -/
noncomputable def reconStep (dp : ℕ → WithTop ℝ) (cen : ℕ → ℕ) (tbl : ℕ → ℝ) (n : ℕ)
    (s : ReconState) : Counted ReconState :=
  (Counted.charge { comparisons := 1 }) >>= fun _ =>
  if s.j = 0 then ⟨⟨s.mark, s.cent, s.cnt, s.p - 1, 0⟩, 0⟩
  else
    (crossMin cmpLeTop (dpAB dp tbl n (s.p - 1) (s.j - 1)) 0 (s.j - 1)) >>= fun r =>
    (readIn cen (r.arg * n + (s.j - 1))) >>= fun l =>
    (writeMem s.mark l true) >>= fun mark' =>
    (Counted.charge { writes := 1 }) >>= fun _ =>
    ⟨⟨mark', insert l s.cent, s.cnt + 1, s.p - 1, r.arg⟩, 0⟩

lemma reconStep_zero (dp : ℕ → WithTop ℝ) (cen : ℕ → ℕ) (tbl : ℕ → ℝ) (n : ℕ)
    {s : ReconState} (h : s.j = 0) :
    (reconStep dp cen tbl n s).value = ⟨s.mark, s.cent, s.cnt, s.p - 1, 0⟩ := by
  simp [reconStep, h]

lemma reconStep_pos (dp : ℕ → WithTop ℝ) (cen : ℕ → ℕ) (tbl : ℕ → ℝ) (n : ℕ)
    {s : ReconState} (h : s.j ≠ 0) :
    (reconStep dp cen tbl n s).value =
      ⟨Function.update s.mark
          (cen ((crossMin cmpLeTop (dpAB dp tbl n (s.p - 1) (s.j - 1)) 0 (s.j - 1)).value.arg * n
            + (s.j - 1))) true,
        insert (cen ((crossMin cmpLeTop (dpAB dp tbl n (s.p - 1) (s.j - 1)) 0
            (s.j - 1)).value.arg * n + (s.j - 1))) s.cent,
        s.cnt + 1, s.p - 1,
        (crossMin cmpLeTop (dpAB dp tbl n (s.p - 1) (s.j - 1)) 0 (s.j - 1)).value.arg⟩ := by
  simp [reconStep, h]

lemma reconStep_p (dp : ℕ → WithTop ℝ) (cen : ℕ → ℕ) (tbl : ℕ → ℝ) (n : ℕ) (s : ReconState) :
    (reconStep dp cen tbl n s).value.p = s.p - 1 := by
  by_cases h : s.j = 0
  · rw [reconStep_zero dp cen tbl n h]
  · rw [reconStep_pos dp cen tbl n h]

lemma countedIter_reconStep_p (dp : ℕ → WithTop ℝ) (cen : ℕ → ℕ) (tbl : ℕ → ℝ) (n : ℕ) :
    ∀ (m : ℕ) (s : ReconState),
      (countedIter (reconStep dp cen tbl n) m s).value.p = s.p - m := by
  intro m
  induction m with
  | zero => intro s; simp
  | succ m ih =>
      intro s
      rw [countedIter_succ]
      simp only [Counted.bind_value]
      rw [ih, reconStep_p]
      omega

/-- The invariant of the reconstruction. -/
def ReconInv (x : ℕ → ℝ) (n k : ℕ) (rstar : ℝ) (s : ReconState) : Prop :=
  s.j ≤ n ∧ s.cent ⊆ range n ∧ s.cent.card = s.cnt ∧ s.cnt + s.p ≤ k ∧
    (∀ q ∈ s.cent, s.j ≤ q) ∧
    rho x s.p s.j ≤ ((rstar : ℝ) : WithTop ℝ) ∧
    (∀ t, s.j ≤ t → t < n → ∃ l ∈ s.cent, |x t - x l| ≤ rstar) ∧
    (∀ q, s.mark q = true ↔ q ∈ s.cent)

lemma reconInv_step (hx : StrictMono x) {n k : ℕ} {tbl : ℕ → ℝ} {cen : ℕ → ℕ}
    {dp : ℕ → WithTop ℝ} {rstar : ℝ} (hrstar : 0 ≤ rstar)
    (htbl : TblOK x n tbl) (hcen : CenOK x n cen)
    (hdp : ∀ p, p ≤ k → ∀ j, j ≤ n → dp (p * (n + 1) + j) = rho x p j)
    (s : ReconState) (hs : ReconInv x n k rstar s) :
    ReconInv x n k rstar (reconStep dp cen tbl n s).value := by
  obtain ⟨hjn, hsub, hcard, hcnt, hge, hrho, hcov, hmark⟩ := hs
  by_cases hj0 : s.j = 0
  · rw [reconStep_zero dp cen tbl n hj0]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (0 : ℕ) ≤ n
      omega
    · show s.cent ⊆ range n
      exact hsub
    · show s.cent.card = s.cnt
      exact hcard
    · show s.cnt + (s.p - 1) ≤ k
      omega
    · show ∀ q ∈ s.cent, 0 ≤ q
      intro q _; omega
    · show rho x (s.p - 1) 0 ≤ ((rstar : ℝ) : WithTop ℝ)
      cases hp : s.p - 1 with
      | zero =>
          simp only [rho_zero_zero]
          exact_mod_cast hrstar
      | succ m =>
          simp only [rho_succ_zero]
          exact_mod_cast hrstar
    · show ∀ t, 0 ≤ t → t < n → ∃ l ∈ s.cent, |x t - x l| ≤ rstar
      intro t _ htn
      exact hcov t (by omega) htn
    · show ∀ q, s.mark q = true ↔ q ∈ s.cent
      exact hmark
  · -- the main case
    have hp0 : s.p ≠ 0 := by
      intro hp
      rw [hp] at hrho
      cases hjj : s.j with
      | zero => exact hj0 hjj
      | succ m =>
          rw [hjj] at hrho
          simp only [rho_zero_succ] at hrho
          exact absurd (top_le_iff.1 hrho) (by simp)
    obtain ⟨p', hp'⟩ : ∃ p', s.p = p' + 1 := ⟨s.p - 1, by omega⟩
    set m := s.j - 1 with hm
    have hmn : m < n := by omega
    set A : ℕ → WithTop ℝ := fun i => rho x p' i with hA
    set B : ℕ → WithTop ℝ := fun i => ((bcost x i m : ℝ) : WithTop ℝ) with hB
    have hfAB : ∀ i, i ≤ m → (dpAB dp tbl n (s.p - 1) m i).value = (A i, B i) := by
      intro i hi
      rw [dpAB_value]
      have h1 : dp ((s.p - 1) * (n + 1) + i) = rho x p' i := by
        have hpp : s.p - 1 = p' := by omega
        rw [hpp]
        exact hdp p' (by omega) i (by omega)
      have h2 : tbl (i * n + m) = bcost x i m := htbl i m hi hmn
      rw [h1, h2]
    have hAmono : ∀ a b : ℕ, a ≤ b → b ≤ m → A a ≤ A b := fun a b hab _ =>
      rho_mono_le hx.monotone p' hab
    have hBanti : ∀ a b : ℕ, a ≤ b → b ≤ m → B b ≤ B a := by
      intro a b hab _
      simp only [hB]
      exact_mod_cast bcost_antitone hx.monotone m hab
    have hBm : B m ≤ A m := by
      simp only [hA, hB, bcost_self hx.monotone m]
      exact_mod_cast rho_nonneg (x := x) p' m
    obtain ⟨hargle, hargor, hvaleq, hvalmin⟩ :=
      crossMin_spec (cle := cmpLeTop) (fAB := dpAB dp tbl n (s.p - 1) m) (A := A) (B := B)
        cmpLeTop_value hfAB hAmono hBanti (Nat.zero_le m) (fun l hl => absurd hl (by omega)) hBm
    set r := (crossMin cmpLeTop (dpAB dp tbl n (s.p - 1) m) 0 m).value with hr
    have hrhoeq : rho x s.p s.j = max (A r.arg) (B r.arg) := by
      have hjm : s.j = m + 1 := by omega
      rw [hp', hjm]
      exact rho_succ_eq_of_argmin hargle (fun i hi => by
        have := hvalmin i hi
        rw [hvaleq] at this
        exact this)
    have hblock : ((bcost x r.arg m : ℝ) : WithTop ℝ) ≤ ((rstar : ℝ) : WithTop ℝ) := by
      have := le_trans (le_max_right (A r.arg) (B r.arg)) (hrhoeq ▸ hrho)
      exact this
    have hprefix : rho x p' r.arg ≤ ((rstar : ℝ) : WithTop ℝ) := by
      have := le_trans (le_max_left (A r.arg) (B r.arg)) (hrhoeq ▸ hrho)
      exact this
    have hblockR : bcost x r.arg m ≤ rstar := by exact_mod_cast hblock
    obtain ⟨hcl1, hcl2, hcl3⟩ := hcen r.arg m hargle hmn
    set l := cen (r.arg * n + m) with hl
    rw [reconStep_pos dp cen tbl n hj0]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show r.arg ≤ n
      omega
    · show insert l s.cent ⊆ range n
      exact Finset.insert_subset (mem_range.2 (by omega)) hsub
    · show (insert l s.cent).card = s.cnt + 1
      have hnotmem : l ∉ s.cent := by
        intro hmem
        have := hge l hmem
        omega
      rw [Finset.card_insert_of_notMem hnotmem, hcard]
    · show s.cnt + 1 + (s.p - 1) ≤ k
      omega
    · show ∀ q ∈ insert l s.cent, r.arg ≤ q
      intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq'
      · exact hcl1
      · have := hge q hq'
        omega
    · show rho x (s.p - 1) r.arg ≤ _
      have hpp : s.p - 1 = p' := by omega
      rw [hpp]
      exact hprefix
    · show ∀ t, r.arg ≤ t → t < n → ∃ l' ∈ insert l s.cent, |x t - x l'| ≤ rstar
      intro t ht htn
      rcases le_or_gt s.j t with hts | hts
      · obtain ⟨l', hl', hle⟩ := hcov t hts htn
        exact ⟨l', Finset.mem_insert_of_mem hl', hle⟩
      · refine ⟨l, Finset.mem_insert_self _ _, ?_⟩
        have htm : t ≤ m := by omega
        have := abs_sub_le_maxblock hx.monotone ht htm hcl1 hcl2
        rw [hcl3] at this
        linarith
    · show ∀ q, Function.update s.mark l true q = true ↔ q ∈ insert l s.cent
      intro q
      by_cases hq : q = l
      · subst hq
        simp [Function.update_self]
      · rw [Function.update_of_ne hq]
        rw [hmark q]
        simp [Finset.mem_insert, hq]

/-! ## Phase 4: padding to exactly `k` centres -/

/-- The state of the padding loop. -/
structure PadState where
  mark : ℕ → Bool
  cent : Finset ℕ
  cnt : ℕ
  cur : ℕ

/-- One step of the padding loop. -/
noncomputable def padStep (k : ℕ) (s : PadState) : Counted PadState :=
  (readIn s.mark s.cur) >>= fun b =>
  (cmpLeNat (s.cnt + 1) k) >>= fun c =>
  if b = false ∧ c = true then
    (writeMem s.mark s.cur true) >>= fun mark' =>
    (Counted.charge { writes := 1 }) >>= fun _ =>
    ⟨⟨mark', insert s.cur s.cent, s.cnt + 1, s.cur + 1⟩, 0⟩
  else ⟨⟨s.mark, s.cent, s.cnt, s.cur + 1⟩, 0⟩

lemma padStep_val_pos (k : ℕ) (s : PadState) (hb : s.mark s.cur = false)
    (hk : s.cnt + 1 ≤ k) :
    (padStep k s).value =
      ⟨Function.update s.mark s.cur true, insert s.cur s.cent, s.cnt + 1, s.cur + 1⟩ := by
  simp [padStep, hb, hk]

lemma padStep_val_neg (k : ℕ) (s : PadState) (hb : ¬ (s.mark s.cur = false ∧ s.cnt + 1 ≤ k)) :
    (padStep k s).value = ⟨s.mark, s.cent, s.cnt, s.cur + 1⟩ := by
  have : ¬ ((s.mark s.cur) = false ∧ (decide (s.cnt + 1 ≤ k)) = true) := by
    intro hcon
    exact hb ⟨hcon.1, by simpa using hcon.2⟩
  simp only [padStep, Counted.bind_value, readIn_value, cmpLeNat_value]
  rw [if_neg this]

lemma padStep_cur (k : ℕ) (s : PadState) : (padStep k s).value.cur = s.cur + 1 := by
  by_cases hb : s.mark s.cur = false ∧ s.cnt + 1 ≤ k
  · rw [padStep_val_pos k s hb.1 hb.2]
  · rw [padStep_val_neg k s hb]

lemma countedIter_padStep_cur (k : ℕ) :
    ∀ (m : ℕ) (s : PadState), (countedIter (padStep k) m s).value.cur = s.cur + m := by
  intro m
  induction m with
  | zero => intro s; simp
  | succ m ih =>
      intro s
      rw [countedIter_succ]
      simp only [Counted.bind_value]
      rw [ih, padStep_cur]
      omega

/-- The invariant of the padding loop. -/
def PadInv (n k : ℕ) (cent0 : Finset ℕ) (s : PadState) : Prop :=
  s.cur ≤ n →
    (s.cent ⊆ range n ∧ s.cent.card = s.cnt ∧ s.cnt ≤ k ∧ cent0 ⊆ s.cent ∧
      (∀ q, s.mark q = true ↔ q ∈ s.cent) ∧ (s.cnt = k ∨ range s.cur ⊆ s.cent))

lemma padInv_step (n k : ℕ) (cent0 : Finset ℕ) (s : PadState) (hs : PadInv n k cent0 s) :
    PadInv n k cent0 (padStep k s).value := by
  intro hcur'
  rw [padStep_cur] at hcur'
  obtain ⟨hsub, hcard, hcnt, hc0, hmark, hlast⟩ := hs (by omega)
  by_cases hb : s.mark s.cur = false ∧ s.cnt + 1 ≤ k
  · rw [padStep_val_pos k s hb.1 hb.2]
    have hnotmem : s.cur ∉ s.cent := by
      intro hmem
      have := (hmark s.cur).2 hmem
      rw [hb.1] at this
      exact absurd this (by simp)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show insert s.cur s.cent ⊆ range n
      exact Finset.insert_subset (mem_range.2 (by omega)) hsub
    · show (insert s.cur s.cent).card = s.cnt + 1
      rw [Finset.card_insert_of_notMem hnotmem, hcard]
    · show s.cnt + 1 ≤ k
      exact hb.2
    · show cent0 ⊆ insert s.cur s.cent
      exact hc0.trans (Finset.subset_insert _ _)
    · show ∀ q, Function.update s.mark s.cur true q = true ↔ q ∈ insert s.cur s.cent
      intro q
      by_cases hq : q = s.cur
      · subst hq; simp
      · rw [Function.update_of_ne hq, hmark q]
        simp [Finset.mem_insert, hq]
    · show s.cnt + 1 = k ∨ range (s.cur + 1) ⊆ insert s.cur s.cent
      right
      intro q hq
      rcases Nat.lt_or_ge q s.cur with hlt | hge2
      · rcases hlast with hk' | hr
        · exact absurd hb.2 (by omega)
        · exact Finset.mem_insert_of_mem (hr (mem_range.2 hlt))
      · have hqc : q = s.cur := by
          have := mem_range.1 hq
          omega
        subst hqc
        exact Finset.mem_insert_self _ _
  · rw [padStep_val_neg k s hb]
    refine ⟨hsub, hcard, hcnt, hc0, hmark, ?_⟩
    show s.cnt = k ∨ range (s.cur + 1) ⊆ s.cent
    rcases hlast with hk' | hr
    · exact Or.inl hk'
    · rcases Classical.em (s.cnt = k) with hk' | hk'
      · exact Or.inl hk'
      · right
        have hmarkcur : s.mark s.cur = true := by
          by_contra hcon
          simp only [Bool.not_eq_true] at hcon
          exact hb ⟨hcon, by omega⟩
        intro q hq
        rcases Nat.lt_or_ge q s.cur with hlt | hge2
        · exact hr (mem_range.2 hlt)
        · have hqc : q = s.cur := by
            have := mem_range.1 hq
            omega
          subst hqc
          exact (hmark s.cur).1 hmarkcur

/-! ## The algorithm -/

/-- **The exact ordered-line `k`-center algorithm**, as a costed run. -/
noncomputable def lineKCenterRun (x : ℕ → ℝ) (n k : ℕ) : Counted (Finset ℕ) :=
  (blockTableRun x n) >>= fun T =>
  (dpRun T.tbl n k) >>= fun D =>
  (countedIter (reconStep D.dp T.cen T.tbl n) k
    ⟨fun _ => false, ∅, 0, k, n⟩) >>= fun R =>
  (countedIter (padStep k) n ⟨R.mark, R.cent, R.cnt, 0⟩) >>= fun P =>
  ⟨P.cent, 0⟩

/-- The output of the algorithm: `k` indices covering all the points with radius
`rho x k n`. -/
theorem lineKCenterRun_spec (hx : StrictMono x) {n k : ℕ} (hkn : k ≤ n)
    {rstar : ℝ} (hrho : rho x k n = ((rstar : ℝ) : WithTop ℝ)) :
    let S := (lineKCenterRun x n k).value
    S ⊆ range n ∧ S.card = k ∧ ∀ t, t < n → ∃ l ∈ S, |x t - x l| ≤ rstar := by
  intro S
  have hrstar : 0 ≤ rstar := rho_eq_coe_nonneg hrho
  set T := (blockTableRun x n).value with hT
  set D := (dpRun T.tbl n k).value with hD
  have htbl : TblOK x n T.tbl := fun i j hij hj => (blockTable_correct hx n i j hij hj).1
  have hcen : CenOK x n T.cen := fun i j hij hj =>
    ⟨(blockTable_correct hx n i j hij hj).2.1, (blockTable_correct hx n i j hij hj).2.2.1,
      (blockTable_correct hx n i j hij hj).2.2.2⟩
  have hdp : ∀ p, p ≤ k → ∀ j, j ≤ n → D.dp (p * (n + 1) + j) = rho x p j :=
    dpRun_correct hx htbl k
  set R := (countedIter (reconStep D.dp T.cen T.tbl n) k
    (⟨fun _ => false, ∅, 0, k, n⟩ : ReconState)).value with hR
  have hinit : ReconInv x n k rstar (⟨fun _ => false, ∅, 0, k, n⟩ : ReconState) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show n ≤ n
      exact le_rfl
    · show (∅ : Finset ℕ) ⊆ range n
      simp
    · show (∅ : Finset ℕ).card = 0
      simp
    · show 0 + k ≤ k
      omega
    · show ∀ q ∈ (∅ : Finset ℕ), n ≤ q
      simp
    · show rho x k n ≤ ((rstar : ℝ) : WithTop ℝ)
      rw [hrho]
    · show ∀ t, n ≤ t → t < n → ∃ l ∈ (∅ : Finset ℕ), |x t - x l| ≤ rstar
      intro t ht htn; omega
    · show ∀ q, (fun _ : ℕ => false) q = true ↔ q ∈ (∅ : Finset ℕ)
      simp
  have hRinv : ReconInv x n k rstar R :=
    countedIter_inv (P := ReconInv x n k rstar)
      (reconInv_step hx hrstar htbl hcen hdp) k _ hinit
  have hRp : R.p = 0 := by
    rw [hR, countedIter_reconStep_p]
    simp
  obtain ⟨hjn, hsub, hcard, hcnt, hge, hrhoR, hcov, hmark⟩ := hRinv
  have hj0 : R.j = 0 := by
    by_contra hcon
    rw [hRp] at hrhoR
    obtain ⟨m, hm⟩ : ∃ m, R.j = m + 1 := ⟨R.j - 1, by omega⟩
    rw [hm] at hrhoR
    simp only [rho_zero_succ] at hrhoR
    exact absurd (top_le_iff.1 hrhoR) (by simp)
  -- padding
  set P := (countedIter (padStep k) n (⟨R.mark, R.cent, R.cnt, 0⟩ : PadState)).value with hP
  have hPinv : PadInv n k R.cent P :=
    countedIter_inv (P := PadInv n k R.cent) (padInv_step n k R.cent) n _
      (by
        intro _
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · show R.cent ⊆ range n
          exact hsub
        · show R.cent.card = R.cnt
          exact hcard
        · show R.cnt ≤ k
          omega
        · show R.cent ⊆ R.cent
          exact Finset.Subset.refl _
        · show ∀ q, R.mark q = true ↔ q ∈ R.cent
          exact hmark
        · show R.cnt = k ∨ range 0 ⊆ R.cent
          exact Or.inr (by simp))
  have hPcur : P.cur = n := by
    rw [hP, countedIter_padStep_cur]
    simp
  obtain ⟨hPsub, hPcard, hPcnt, hPc0, hPmark, hPlast⟩ := hPinv (by omega)
  have hSP : S = P.cent := rfl
  have hcntk : P.cnt = k := by
    rcases hPlast with h | h
    · exact h
    · rw [hPcur] at h
      have h1 : (range n).card ≤ P.cent.card := Finset.card_le_card h
      simp only [Finset.card_range] at h1
      omega
  refine ⟨by rw [hSP]; exact hPsub, by rw [hSP, hPcard, hcntk], ?_⟩
  intro t htn
  obtain ⟨l, hl, hle⟩ := hcov t (by omega) htn
  exact ⟨l, by rw [hSP]; exact hPc0 hl, hle⟩

/-- **Correctness of the exact ordered-line algorithm**: the run outputs `k` of the input
points, and no `k`-element subset of the input point set has a smaller covering radius. -/
theorem lineKCenter_correct (hx : StrictMono x) {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    let S := (lineKCenterRun x n k).value
    S ⊆ range n ∧ S.card = k ∧
      ∀ G ⊆ (range n).image x, G.card = k →
        covRad' ((range n).image x) (S.image x) ≤ covRad' ((range n).image x) G := by
  intro S
  obtain ⟨rstar, hrho⟩ : ∃ v : ℝ, rho x k n = ((v : ℝ) : WithTop ℝ) := by
    cases hval : rho x k n with
    | top => exact absurd hval (rho_ne_top hx.monotone hk n)
    | coe v => exact ⟨v, rfl⟩
  obtain ⟨hsub, hcard, hcov⟩ := lineKCenterRun_spec hx hkn hrho
  refine ⟨hsub, hcard, ?_⟩
  intro G hG hGcard
  set X := (range n).image x with hX
  have hXne : X.Nonempty := by
    refine ⟨x 0, Finset.mem_image.2 ⟨0, mem_range.2 (by omega), rfl⟩⟩
  have hSne : (S.image x).Nonempty := by
    have : S.Nonempty := Finset.card_pos.1 (by rw [hcard]; omega)
    exact this.image x
  have hGne : G.Nonempty := Finset.card_pos.1 (by rw [hGcard]; omega)
  -- the output covers with radius `rstar`
  have h1 : covRad' X (S.image x) ≤ rstar := by
    rw [covRad'_le_iff hXne hSne]
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨l, hl, hle⟩ := hcov t (mem_range.1 ht)
    exact ⟨x l, Finset.mem_image_of_mem _ hl, by rwa [Real.dist_eq]⟩
  -- no `k`-element subset does better
  have h2 : rstar ≤ covRad' X G := by
    have hnn : 0 ≤ covRad' X G := covRad'_nonneg X G
    have hdom : ∀ y ∈ X, ∃ g ∈ G, dist y g ≤ covRad' X G :=
      (covRad'_le_iff hXne hGne _).1 le_rfl
    have : rho x k n ≤ ((covRad' X G : ℝ) : WithTop ℝ) := by
      rw [rho_le_iff_exists_centers hx.monotone hx.injective hnn]
      exact ⟨G, hG, by omega, hdom⟩
    rw [hrho] at this
    exact_mod_cast this
  linarith

/-! ## The running time -/

lemma reconStep_work_le (dp : ℕ → WithTop ℝ) (cen : ℕ → ℕ) (tbl : ℕ → ℝ) (n : ℕ)
    (s : ReconState) (hj : s.j ≤ n) : (reconStep dp cen tbl n s).ops.work ≤ 4 * n + 20 := by
  by_cases hj0 : s.j = 0
  · have : (reconStep dp cen tbl n s).ops.work = 1 := by
      simp [reconStep, hj0, OpCount.work, OpCount.add_eq, OpCount.plus]
    omega
  · have hops : (reconStep dp cen tbl n s).ops.work
        = 1 + ((crossMin cmpLeTop (dpAB dp tbl n (s.p - 1) (s.j - 1)) 0 (s.j - 1)).ops.work
            + (1 + (1 + 1))) := by
      simp only [reconStep, Counted.bind_ops, Counted.charge_ops, OpCount.add_work,
        readIn_ops, writeMem_ops, OpCount.work_zero, if_neg hj0]
      norm_num [OpCount.work]
    have hcm := crossMin_work_le (cle := cmpLeTop)
      (fAB := dpAB dp tbl n (s.p - 1) (s.j - 1)) 1 3
      (fun a b => cmpLeTop_work a b) (dpAB_work dp tbl n (s.p - 1) (s.j - 1)) 0 (s.j - 1)
    have hcross : (crossMin cmpLeTop (dpAB dp tbl n (s.p - 1) (s.j - 1)) 0 (s.j - 1)).value.cross
        ≤ s.j - 1 := by
      have := crossMin_cross_le cmpLeTop (dpAB dp tbl n (s.p - 1) (s.j - 1)) 0 (s.j - 1)
      omega
    omega

lemma padStep_work_le (k : ℕ) (s : PadState) : (padStep k s).ops.work ≤ 4 := by
  simp only [padStep, Counted.bind_ops]
  split <;> simp [OpCount.work, OpCount.add_eq, OpCount.plus]

/-- **Running time of the exact ordered-line algorithm**: `O(n^2 + k*n)` unit-cost
operations. -/
theorem lineKCenter_work_le (x : ℕ → ℝ) {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (lineKCenterRun x n k).ops.work ≤ 100 * (n * n + k * n) := by
  set T := (blockTableRun x n).value with hT
  set D := (dpRun T.tbl n k).value with hD
  set R := (countedIter (reconStep D.dp T.cen T.tbl n) k
    (⟨fun _ => false, ∅, 0, k, n⟩ : ReconState)).value with hR
  have h1 : (blockTableRun x n).ops.work ≤ 33 * n * n := blockTable_work_le x n
  have h2 : (dpRun T.tbl n k).ops.work ≤ 24 * (k + 1) * (n + 1) := dpRun_work_le T.tbl n k
  have h3 : (countedIter (reconStep D.dp T.cen T.tbl n) k
      (⟨fun _ => false, ∅, 0, k, n⟩ : ReconState)).ops.work ≤ (4 * n + 20) * k := by
    refine countedIter_work_le_inv (P := fun s : ReconState => s.j ≤ n) (4 * n + 20)
      (fun s hs => ?_) (fun s hs => reconStep_work_le D.dp T.cen T.tbl n s hs) k _ le_rfl
    by_cases hj0 : s.j = 0
    · rw [reconStep_zero D.dp T.cen T.tbl n hj0]
      simp
    · rw [reconStep_pos D.dp T.cen T.tbl n hj0]
      show (crossMin cmpLeTop (dpAB D.dp T.tbl n (s.p - 1) (s.j - 1)) 0 (s.j - 1)).value.arg ≤ n
      have ha := crossMin_arg_le_cross cmpLeTop (dpAB D.dp T.tbl n (s.p - 1) (s.j - 1)) 0 (s.j - 1)
      have hc := crossMin_cross_le cmpLeTop (dpAB D.dp T.tbl n (s.p - 1) (s.j - 1)) 0 (s.j - 1)
      omega
  have h4 : (countedIter (padStep k) n (⟨R.mark, R.cent, R.cnt, 0⟩ : PadState)).ops.work
      ≤ 4 * n := countedIter_work_le (f := padStep k) 4 (padStep_work_le k) n _
  have hops : (lineKCenterRun x n k).ops.work
      = (blockTableRun x n).ops.work + ((dpRun T.tbl n k).ops.work
        + ((countedIter (reconStep D.dp T.cen T.tbl n) k
            (⟨fun _ => false, ∅, 0, k, n⟩ : ReconState)).ops.work
          + ((countedIter (padStep k) n (⟨R.mark, R.cent, R.cnt, 0⟩ : PadState)).ops.work
            + 0))) := by
    simp only [lineKCenterRun, Counted.bind_ops, OpCount.add_work, OpCount.work_zero, hT, hD, hR]
  have hfin : 33 * n * n + 24 * (k + 1) * (n + 1) + (4 * n + 20) * k + 4 * n
      ≤ 100 * (n * n + k * n) := by nlinarith
  omega

end Line

end Q764
