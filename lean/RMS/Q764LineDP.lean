/-
# Q764 — Stage 3c.3: the bottleneck dynamic-programming layers

The second phase of the exact ordered-line algorithm fills the table of the prefix optima
`Q764.Line.rho x p j` for `0 ≤ p ≤ k` and `0 ≤ j ≤ n`, reading the block costs from the
table of `RequestProject.Q764LineTable`.

Inside one layer the minimizing index of
`rho x (p+1) (j+1) = min_{i ≤ j} max (rho x p i) (c(i,j))`
is found by the crossing pointer of `Q764.Line.crossMin`, which never moves left as `j`
increases (this is the second monotone-pointer invariant, whose mathematical content is
`Q764.Line.rho_layer_crossing_monotone`).  Hence one layer costs `O(n)` operations and the
whole dynamic program costs `O(k*n)`.
-/
import RMS.Q764LineTable

open Finset

namespace Q764

namespace Line

variable {x : ℕ → ℝ}

/-! ## A minimum recognised by its minimizer -/

lemma inf'_eq_of_argmin {α : Type*} [LinearOrder α] {f : ℕ → α} {m arg : ℕ} (harg : arg ≤ m)
    (hmin : ∀ i, i ≤ m → f arg ≤ f i) :
    (range (m + 1)).inf' Finset.nonempty_range_add_one f = f arg := by
  refine le_antisymm (Finset.inf'_le f (mem_range.2 (by omega))) ?_
  exact Finset.le_inf' _ _ fun i hi => hmin i (by simpa [Nat.lt_succ_iff] using mem_range.1 hi)

/-! ## The costed layers -/

/-- One comparison in `WithTop ℝ` (the exact comparison oracle of the unit-cost model,
extended by the sentinel `⊤`). -/
noncomputable def cmpLeTop (a b : WithTop ℝ) : Counted Bool :=
  ⟨decide (a ≤ b), { comparisons := 1 }⟩

lemma cmpLeTop_value (a b : WithTop ℝ) : (cmpLeTop a b).value = decide (a ≤ b) := rfl

lemma cmpLeTop_work (a b : WithTop ℝ) : (cmpLeTop a b).ops.work ≤ 1 := by
  simp [cmpLeTop, OpCount.work]

/-- Costed evaluation of the two families of the dynamic-programming crossing:
`A i = rho x p i` (read from the previous layer) and `B i = c(i,j)` (read from the
block-cost table). -/
noncomputable def dpAB (dp : ℕ → WithTop ℝ) (tbl : ℕ → ℝ) (n p j : ℕ) (i : ℕ) :
    Counted (WithTop ℝ × WithTop ℝ) :=
  (readIn dp (p * (n + 1) + i)) >>= fun a =>
  (readIn tbl (i * n + j)) >>= fun b =>
  (arith ((b : WithTop ℝ))) >>= fun b' => ⟨(a, b'), 0⟩

@[simp] lemma dpAB_value (dp : ℕ → WithTop ℝ) (tbl : ℕ → ℝ) (n p j i : ℕ) :
    (dpAB dp tbl n p j i).value =
      (dp (p * (n + 1) + i), ((tbl (i * n + j) : ℝ) : WithTop ℝ)) := rfl

lemma dpAB_work (dp : ℕ → WithTop ℝ) (tbl : ℕ → ℝ) (n p j i : ℕ) :
    (dpAB dp tbl n p j i).ops.work ≤ 3 := by
  simp [dpAB, OpCount.work, OpCount.add_eq, OpCount.plus]

/-- The state of the scan of one dynamic-programming layer. -/
structure DpRow where
  dp : ℕ → WithTop ℝ
  ptr : ℕ
  col : ℕ

/-- One cell of the layer `p + 1`. -/
noncomputable def dpStep (tbl : ℕ → ℝ) (n p : ℕ) (s : DpRow) : Counted DpRow :=
  (crossMin cmpLeTop (dpAB s.dp tbl n p (s.col - 1)) s.ptr (s.col - 1)) >>= fun r =>
  (writeMem s.dp ((p + 1) * (n + 1) + s.col) r.val) >>= fun dp' =>
  ⟨⟨dp', r.cross, s.col + 1⟩, 0⟩

lemma dpStep_col (tbl : ℕ → ℝ) (n p : ℕ) (s : DpRow) :
    (dpStep tbl n p s).value.col = s.col + 1 := rfl

lemma dpStep_ptr (tbl : ℕ → ℝ) (n p : ℕ) (s : DpRow) :
    (dpStep tbl n p s).value.ptr =
      (crossMin cmpLeTop (dpAB s.dp tbl n p (s.col - 1)) s.ptr (s.col - 1)).value.cross := rfl

lemma dpStep_dp (tbl : ℕ → ℝ) (n p : ℕ) (s : DpRow) :
    (dpStep tbl n p s).value.dp =
      Function.update s.dp ((p + 1) * (n + 1) + s.col)
        (crossMin cmpLeTop (dpAB s.dp tbl n p (s.col - 1)) s.ptr (s.col - 1)).value.val := rfl

lemma countedIter_dpStep_col (tbl : ℕ → ℝ) (n p : ℕ) :
    ∀ (m : ℕ) (s : DpRow), (countedIter (dpStep tbl n p) m s).value.col = s.col + m := by
  intro m
  induction m with
  | zero => intro s; simp
  | succ m ih =>
      intro s
      rw [countedIter_succ]
      simp only [Counted.bind_value]
      rw [ih, dpStep_col]
      omega

/-- The block-cost table is correctly filled. -/
def TblOK (x : ℕ → ℝ) (n : ℕ) (tbl : ℕ → ℝ) : Prop :=
  ∀ i j, i ≤ j → j < n → tbl (i * n + j) = bcost x i j

/-- The invariant of the scan of the layer `p + 1`. -/
def DpRowInv (x : ℕ → ℝ) (n p : ℕ) (dp0 : ℕ → WithTop ℝ) (s : DpRow) : Prop :=
  s.col ≤ n + 1 →
    (1 ≤ s.col ∧ s.ptr + 1 ≤ s.col ∧
      (∀ l, l < s.ptr → ¬ ((bcost x l (s.col - 1) : ℝ) : WithTop ℝ) ≤ rho x p l) ∧
      (∀ q, q < (p + 1) * (n + 1) → s.dp q = dp0 q) ∧
      (∀ j, j < s.col → s.dp ((p + 1) * (n + 1) + j) = rho x (p + 1) j))

lemma dpRowInv_step (hx : StrictMono x) {n p : ℕ} {tbl : ℕ → ℝ} {dp0 : ℕ → WithTop ℝ}
    (htbl : TblOK x n tbl) (hdp0 : ∀ i, i ≤ n → dp0 (p * (n + 1) + i) = rho x p i)
    (s : DpRow) (hs : DpRowInv x n p dp0 s) :
    DpRowInv x n p dp0 (dpStep tbl n p s).value := by
  intro hcol'
  rw [dpStep_col] at hcol'
  obtain ⟨hcol1, hptr, hbefore, hkeep, hcells⟩ := hs (by omega)
  set j := s.col - 1 with hjdef
  have hjn : j < n := by omega
  set A : ℕ → WithTop ℝ := fun i => rho x p i with hA
  set B : ℕ → WithTop ℝ := fun i => ((bcost x i j : ℝ) : WithTop ℝ) with hB
  have hfAB : ∀ i, i ≤ j → (dpAB s.dp tbl n p j i).value = (A i, B i) := by
    intro i hi
    rw [dpAB_value]
    have h1 : s.dp (p * (n + 1) + i) = rho x p i := by
      rw [hkeep _ (by
        have : p * (n + 1) + i < p * (n + 1) + (n + 1) := by omega
        have h2 : p * (n + 1) + (n + 1) = (p + 1) * (n + 1) := by ring
        omega)]
      exact hdp0 i (by omega)
    have h2 : tbl (i * n + j) = bcost x i j := htbl i j hi hjn
    rw [h1, h2]
  have hAmono : ∀ a b : ℕ, a ≤ b → b ≤ j → A a ≤ A b := by
    intro a b hab _
    exact rho_mono_le hx.monotone p hab
  have hBanti : ∀ a b : ℕ, a ≤ b → b ≤ j → B b ≤ B a := by
    intro a b hab _
    simp only [hB]
    exact_mod_cast bcost_antitone hx.monotone j hab
  have hBm : B j ≤ A j := by
    simp only [hA, hB, bcost_self hx.monotone j]
    exact_mod_cast rho_nonneg (x := x) p j
  have hptrj : s.ptr ≤ j := by omega
  obtain ⟨hgec, hlec, hcrossc, hminc⟩ :=
    crossMin_cross (cle := cmpLeTop) (fAB := dpAB s.dp tbl n p j) (A := A) (B := B)
      cmpLeTop_value hfAB hptrj hBm
  obtain ⟨hargle, hargor, hvaleq, hvalmin⟩ :=
    crossMin_spec (cle := cmpLeTop) (fAB := dpAB s.dp tbl n p j) (A := A) (B := B)
      cmpLeTop_value hfAB hAmono hBanti hptrj (fun l hl => hbefore l hl) hBm
  set r := (crossMin cmpLeTop (dpAB s.dp tbl n p j) s.ptr j).value with hr
  -- the computed value is the prefix optimum
  have hvalrho : r.val = rho x (p + 1) s.col := by
    have hcol : s.col = j + 1 := by omega
    rw [hcol, rho_succ_succ]
    rw [inf'_eq_of_argmin (f := fun i => max (rho x p i) (((bcost x i j : ℝ) : WithTop ℝ)))
      hargle (fun i hi => by
        have := hvalmin i hi
        rw [hvaleq] at this
        exact this)]
    rw [hvaleq]
  refine ⟨by rw [dpStep_col]; omega, ?_, ?_, ?_, ?_⟩
  · rw [dpStep_col, dpStep_ptr, ← hjdef, ← hr]
    have hrc : r.cross ≤ j := hlec
    omega
  · rw [dpStep_col, dpStep_ptr, ← hjdef, ← hr]
    intro l hl
    have hnl : ¬ (B l ≤ A l) := by
      rcases lt_or_ge l s.ptr with h | h
      · exact hbefore l h
      · exact hminc l h hl
    intro hcon
    apply hnl
    simp only [hA, hB] at hcon ⊢
    refine le_trans ?_ hcon
    have : bcost x l j ≤ bcost x l (s.col + 1 - 1) := by
      have he : s.col + 1 - 1 = j + 1 := by omega
      rw [he]
      exact bcost_mono_right hx.monotone l j
    exact_mod_cast this
  · intro q hq
    rw [dpStep_dp]
    have hne : q ≠ (p + 1) * (n + 1) + s.col := by omega
    rw [Function.update_of_ne hne]
    exact hkeep q hq
  · intro j' hj'
    rw [dpStep_col] at hj'
    rw [dpStep_dp, ← hjdef, ← hr]
    rcases lt_or_ge j' s.col with hlt | hge
    · have hne : (p + 1) * (n + 1) + j' ≠ (p + 1) * (n + 1) + s.col := by omega
      rw [Function.update_of_ne hne]
      exact hcells j' hlt
    · have : j' = s.col := by omega
      subst this
      rw [Function.update_self]
      exact hvalrho

/-- Specification of one dynamic-programming layer. -/
theorem dpRow_spec (hx : StrictMono x) {n p : ℕ} {tbl : ℕ → ℝ} {dp0 : ℕ → WithTop ℝ}
    (htbl : TblOK x n tbl) (hdp0 : ∀ i, i ≤ n → dp0 (p * (n + 1) + i) = rho x p i)
    (hdp0' : dp0 ((p + 1) * (n + 1)) = 0) :
    let s := (countedIter (dpStep tbl n p) n ⟨dp0, 0, 1⟩).value
    (∀ q, q < (p + 1) * (n + 1) → s.dp q = dp0 q) ∧
      (∀ j, j ≤ n → s.dp ((p + 1) * (n + 1) + j) = rho x (p + 1) j) := by
  intro s
  have hinv : DpRowInv x n p dp0 s :=
    countedIter_inv (P := DpRowInv x n p dp0) (dpRowInv_step hx htbl hdp0) n _
      (by
        intro _
        refine ⟨le_rfl, le_rfl, by intro l hl; exact absurd hl (Nat.not_lt_zero l),
          fun q _ => rfl, ?_⟩
        intro j hj
        have hj0 : j = 0 := Nat.lt_one_iff.1 hj
        subst hj0
        simpa using hdp0')
  have hcol : s.col = 1 + n := countedIter_dpStep_col tbl n p n _
  obtain ⟨-, -, -, hkeep, hcells⟩ := hinv (by omega)
  exact ⟨hkeep, fun j hj => hcells j (by omega)⟩

/-! ## Cost of one layer -/

lemma dpStep_work (tbl : ℕ → ℝ) (n p : ℕ) (s : DpRow) :
    (dpStep tbl n p s).ops.work + 4 * s.ptr ≤ 17 + 4 * (dpStep tbl n p s).value.ptr := by
  have hcm := crossMin_work_le (cle := cmpLeTop) (fAB := dpAB s.dp tbl n p (s.col - 1)) 1 3
    (fun a b => cmpLeTop_work a b) (dpAB_work s.dp tbl n p (s.col - 1)) s.ptr (s.col - 1)
  have hge : s.ptr ≤ (crossMin cmpLeTop (dpAB s.dp tbl n p (s.col - 1)) s.ptr
      (s.col - 1)).value.cross := by
    have := findFromC_ge (crossStep cmpLeTop (dpAB s.dp tbl n p (s.col - 1)))
      (s.col - 1 - s.ptr) s.ptr
    have heq : (crossMin cmpLeTop (dpAB s.dp tbl n p (s.col - 1)) s.ptr (s.col - 1)).value.cross
        = (findFromC (crossStep cmpLeTop (dpAB s.dp tbl n p (s.col - 1))) s.ptr
            (s.col - 1 - s.ptr)).value := by
      simp only [crossMin, Counted.bind_value]
      split <;> rfl
    omega
  have hops : (dpStep tbl n p s).ops.work
      = (crossMin cmpLeTop (dpAB s.dp tbl n p (s.col - 1)) s.ptr (s.col - 1)).ops.work + 1 := by
    simp only [dpStep, Counted.bind_ops, OpCount.add_work, writeMem_ops, OpCount.work_zero]
    simp [OpCount.work]
  rw [dpStep_ptr]
  omega

lemma dpRow_work (tbl : ℕ → ℝ) (n p : ℕ) (dp0 : ℕ → WithTop ℝ) :
    (countedIter (dpStep tbl n p) n ⟨dp0, 0, 1⟩).ops.work ≤ 21 * n := by
  set s0 : DpRow := ⟨dp0, 0, 1⟩ with hs0
  have hPstep : ∀ s : DpRow, s.ptr + 1 ≤ s.col → (dpStep tbl n p s).value.ptr + 1 ≤
      (dpStep tbl n p s).value.col := by
    intro s hs
    rw [dpStep_col, dpStep_ptr]
    have heq : (crossMin cmpLeTop (dpAB s.dp tbl n p (s.col - 1)) s.ptr (s.col - 1)).value.cross
        = (findFromC (crossStep cmpLeTop (dpAB s.dp tbl n p (s.col - 1))) s.ptr
            (s.col - 1 - s.ptr)).value := by
      simp only [crossMin, Counted.bind_value]
      split <;> rfl
    have := findFromC_le (crossStep cmpLeTop (dpAB s.dp tbl n p (s.col - 1)))
      (s.col - 1 - s.ptr) s.ptr
    omega
  have hpot := countedIter_work_potential_inv (f := dpStep tbl n p)
    (P := fun s => s.ptr + 1 ≤ s.col) (φ := fun s => 4 * s.ptr) (C := 17)
    hPstep (fun s _ => dpStep_work tbl n p s) n s0 (by rw [hs0])
  have hcol : (countedIter (dpStep tbl n p) n s0).value.col = 1 + n :=
    countedIter_dpStep_col tbl n p n s0
  have hptr : (countedIter (dpStep tbl n p) n s0).value.ptr + 1
      ≤ (countedIter (dpStep tbl n p) n s0).value.col :=
    countedIter_inv (P := fun s : DpRow => s.ptr + 1 ≤ s.col) hPstep n s0 (by rw [hs0])
  have e1 : s0.ptr = 0 := by rw [hs0]
  simp only [] at hpot
  omega

/-! ## All layers -/

/-- The state of the dynamic program. -/
structure DpState where
  dp : ℕ → WithTop ℝ
  layer : ℕ

/-- One layer of the dynamic program: initialize the empty prefix, then scan. -/
noncomputable def dpOuterStep (tbl : ℕ → ℝ) (n : ℕ) (s : DpState) : Counted DpState :=
  (writeMem s.dp ((s.layer + 1) * (n + 1)) 0) >>= fun dp0 =>
  (countedIter (dpStep tbl n s.layer) n ⟨dp0, 0, 1⟩) >>= fun r =>
  ⟨⟨r.dp, s.layer + 1⟩, 0⟩

/-- **Phase 2 of the ordered-line algorithm**: the whole table of prefix optima. -/
noncomputable def dpRun (tbl : ℕ → ℝ) (n k : ℕ) : Counted DpState :=
  (Counted.charge { writes := (k + 1) * (n + 1) }) >>= fun _ =>
  countedIter (dpOuterStep tbl n) k ⟨fun q => if q = 0 then 0 else ⊤, 0⟩

lemma dpOuterStep_layer (tbl : ℕ → ℝ) (n : ℕ) (s : DpState) :
    (dpOuterStep tbl n s).value.layer = s.layer + 1 := rfl

lemma countedIter_dpOuterStep_layer (tbl : ℕ → ℝ) (n : ℕ) :
    ∀ (m : ℕ) (s : DpState),
      (countedIter (dpOuterStep tbl n) m s).value.layer = s.layer + m := by
  intro m
  induction m with
  | zero => intro s; simp
  | succ m ih =>
      intro s
      rw [countedIter_succ]
      simp only [Counted.bind_value]
      rw [ih, dpOuterStep_layer]
      omega

/-- The invariant of the dynamic program. -/
def DpInv (x : ℕ → ℝ) (n : ℕ) (s : DpState) : Prop :=
  ∀ p, p ≤ s.layer → ∀ j, j ≤ n → s.dp (p * (n + 1) + j) = rho x p j

lemma dpInv_step (hx : StrictMono x) {n : ℕ} {tbl : ℕ → ℝ} (htbl : TblOK x n tbl)
    (s : DpState) (hs : DpInv x n s) : DpInv x n (dpOuterStep tbl n s).value := by
  set p := s.layer with hp
  set dp0 := Function.update s.dp ((p + 1) * (n + 1)) (0 : WithTop ℝ) with hdp0def
  have hdp0 : ∀ i, i ≤ n → dp0 (p * (n + 1) + i) = rho x p i := by
    intro i hi
    have hne : p * (n + 1) + i ≠ (p + 1) * (n + 1) := by
      have : (p + 1) * (n + 1) = p * (n + 1) + (n + 1) := by ring
      omega
    rw [hdp0def, Function.update_of_ne hne]
    exact hs p le_rfl i hi
  have hdp0' : dp0 ((p + 1) * (n + 1)) = 0 := by
    rw [hdp0def, Function.update_self]
  obtain ⟨hkeep, hcells⟩ := dpRow_spec hx htbl hdp0 hdp0'
  intro p' hp' j hj
  have hdpval : (dpOuterStep tbl n s).value.dp
      = (countedIter (dpStep tbl n p) n ⟨dp0, 0, 1⟩).value.dp := rfl
  rw [dpOuterStep_layer] at hp'
  rcases Nat.lt_or_ge p' (p + 1) with hlt | hge
  · have hq : p' * (n + 1) + j < (p + 1) * (n + 1) := by
      have h0 : (p' + 1) * (n + 1) ≤ (p + 1) * (n + 1) := Nat.mul_le_mul_right (n + 1) (by omega)
      have h1 : (p' + 1) * (n + 1) = p' * (n + 1) + (n + 1) := by ring
      omega
    rw [hdpval, hkeep _ hq, hdp0def]
    have hne : p' * (n + 1) + j ≠ (p + 1) * (n + 1) := by omega
    rw [Function.update_of_ne hne]
    exact hs p' (by omega) j hj
  · have : p' = p + 1 := by omega
    subst this
    rw [hdpval]
    exact hcells j hj

/-- **Correctness of phase 2**: the dynamic program stores the prefix optima
`Q764.Line.rho`. -/
theorem dpRun_correct (hx : StrictMono x) {n : ℕ} {tbl : ℕ → ℝ} (htbl : TblOK x n tbl) (k : ℕ) :
    ∀ p, p ≤ k → ∀ j, j ≤ n → (dpRun tbl n k).value.dp (p * (n + 1) + j) = rho x p j := by
  have hval : (dpRun tbl n k).value
      = (countedIter (dpOuterStep tbl n) k
          (⟨fun q => if q = 0 then 0 else ⊤, 0⟩ : DpState)).value := rfl
  have hinv : DpInv x n (countedIter (dpOuterStep tbl n) k
      (⟨fun q => if q = 0 then 0 else ⊤, 0⟩ : DpState)).value := by
    refine countedIter_inv (P := DpInv x n) (dpInv_step hx htbl) k _ ?_
    intro p hp j hj
    have hp0 : p = 0 := Nat.le_zero.1 hp
    subst hp0
    simp only [Nat.zero_mul, Nat.zero_add]
    cases j with
    | zero => simp
    | succ m => simp [rho_zero_succ]
  have hlayer : (countedIter (dpOuterStep tbl n) k
      (⟨fun q => if q = 0 then 0 else ⊤, 0⟩ : DpState)).value.layer = k := by
    have := countedIter_dpOuterStep_layer tbl n k
      (⟨fun q => if q = 0 then 0 else ⊤, 0⟩ : DpState)
    simpa using this
  intro p hp j hj
  rw [hval]
  exact hinv p (by omega) j hj

/-- **Cost of phase 2**: the dynamic program costs `O(k*n)` unit-cost operations. -/
theorem dpRun_work_le (tbl : ℕ → ℝ) (n k : ℕ) :
    (dpRun tbl n k).ops.work ≤ 24 * (k + 1) * (n + 1) := by
  have houter : ∀ s : DpState, (dpOuterStep tbl n s).ops.work ≤ 22 * n + 1 := by
    intro s
    have heq : (dpOuterStep tbl n s).ops.work
        = 1 + (countedIter (dpStep tbl n s.layer) n
            ⟨Function.update s.dp ((s.layer + 1) * (n + 1)) 0, 0, 1⟩).ops.work := by
      simp only [dpOuterStep, Counted.bind_ops, OpCount.add_work, writeMem_ops,
        OpCount.work_zero]
      simp [OpCount.work]
    rw [heq]
    have := dpRow_work tbl n s.layer (Function.update s.dp ((s.layer + 1) * (n + 1)) 0)
    omega
  have hloop := countedIter_work_le (f := dpOuterStep tbl n) (22 * n + 1) houter k
    (⟨fun q => if q = 0 then 0 else ⊤, 0⟩ : DpState)
  have hops : (dpRun tbl n k).ops.work
      = (k + 1) * (n + 1) + (countedIter (dpOuterStep tbl n) k
          (⟨fun q => if q = 0 then 0 else ⊤, 0⟩ : DpState)).ops.work := by
    simp only [dpRun, Counted.bind_ops, Counted.charge_ops, OpCount.add_work]
    norm_num [OpCount.work]
  have hb : (22 * n + 1) * k + (k + 1) * (n + 1) ≤ 24 * (k + 1) * (n + 1) := by nlinarith
  omega

end Line

end Q764
