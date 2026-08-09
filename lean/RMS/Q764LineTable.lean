/-
# Q764 — Stage 3c.2: the block-cost table of the ordered-line algorithm

The first phase of the exact ordered-line algorithm fills, for every pair of indices
`i ≤ j < n`, the one-centre cost `c(i,j) = bcost x i j` of the block `[i,j]` **and** an
index of a point of the block realizing it.

The row for a fixed `i` is computed by a single left-to-right scan in which the crossing
pointer of `Q764.Line.crossMin` never moves left, so the whole table costs `O(n^2)`
operations, and this is proved for the very run whose output is proved correct
(`Q764.Line.blockTable_correct`, `Q764.Line.blockTable_work_le`).

The memory is modelled as a total function `ℕ → ℝ` (resp. `ℕ → ℕ`) accessed only through
the costed primitives `Q764.Line.readIn` and `Q764.Line.writeMem`; the initialization of
the `n × n` table is charged explicitly.
-/
import RMS.Q764LineCore

open Finset

namespace Q764

namespace Line

variable {x : ℕ → ℝ}

/-! ## Elementary facts about the one-centre cost of a block -/

lemma abs_sub_le_maxblock (hx : Monotone x) {i j t l : ℕ} (hit : i ≤ t) (htj : t ≤ j)
    (hil : i ≤ l) (hlj : l ≤ j) : |x t - x l| ≤ max (x l - x i) (x j - x l) := by
  have h1 : x i ≤ x t := hx hit
  have h2 : x t ≤ x j := hx htj
  have h3 : x i ≤ x l := hx hil
  have h4 : x l ≤ x j := hx hlj
  refine abs_le.2 ⟨?_, ?_⟩
  · have := le_max_left (x l - x i) (x j - x l); linarith
  · have := le_max_right (x l - x i) (x j - x l); linarith

lemma bcost_le_maxblock_of_mem (hx : Monotone x) {i j l : ℕ} (hij : i ≤ j) (hil : i ≤ l)
    (hlj : l ≤ j) : bcost x i j ≤ max (x l - x i) (x j - x l) := by
  rw [bcost_eq hij, blockCost]
  have := Finset.inf'_le (fun l => blockRadius x i j l hij) (mem_Icc.2 ⟨hil, hlj⟩)
  rwa [blockRadius_eq_max hx hij hil hlj] at this

lemma bcost_le_maxblock (hx : Monotone x) {i j l : ℕ} (hij : i ≤ j) (hlj : l ≤ j) :
    bcost x i j ≤ max (x l - x i) (x j - x l) := by
  rcases le_or_gt i l with hil | hli
  · exact bcost_le_maxblock_of_mem hx hij hil hlj
  · have h0 : bcost x i j ≤ max (x i - x i) (x j - x i) :=
      bcost_le_maxblock_of_mem hx hij le_rfl hij
    have h1 : x l ≤ x i := hx hli.le
    have h2 : x i ≤ x j := hx hij
    have h3 : max (x i - x i) (x j - x i) = x j - x i := by
      rw [max_eq_right (by linarith)]
    have h4 : x j - x i ≤ max (x l - x i) (x j - x l) :=
      le_trans (by linarith) (le_max_right (x l - x i) (x j - x l))
    linarith [h0, h4, h3.le, h3.ge]

lemma exists_maxblock_eq_bcost (hx : Monotone x) {i j : ℕ} (hij : i ≤ j) :
    ∃ l, i ≤ l ∧ l ≤ j ∧ max (x l - x i) (x j - x l) = bcost x i j := by
  rw [bcost_eq hij, blockCost]
  obtain ⟨l, hl, hval⟩ :=
    Finset.exists_mem_eq_inf' (nonempty_Icc.2 hij) (fun l => blockRadius x i j l hij)
  obtain ⟨hil, hlj⟩ := mem_Icc.1 hl
  exact ⟨l, hil, hlj, by rw [hval, blockRadius_eq_max hx hij hil hlj]⟩

/-! ## The costed row scan -/

/-- Costed evaluation of the two families of the block-cost crossing:
`A l = x l - x i` (nondecreasing) and `B l = x j - x l` (nonincreasing). -/
noncomputable def blockAB (x : ℕ → ℝ) (i j : ℕ) (l : ℕ) : Counted (ℝ × ℝ) :=
  (readIn x l) >>= fun a => (readIn x i) >>= fun b => (readIn x j) >>= fun c =>
  (arith (a - b)) >>= fun u => (arith (c - a)) >>= fun v => ⟨(u, v), 0⟩

@[simp] lemma blockAB_value (x : ℕ → ℝ) (i j l : ℕ) :
    (blockAB x i j l).value = (x l - x i, x j - x l) := rfl

lemma blockAB_work (x : ℕ → ℝ) (i j l : ℕ) : (blockAB x i j l).ops.work ≤ 5 := by
  simp [blockAB, OpCount.work, OpCount.add_eq, OpCount.plus]

/-- The state of the row scan: the two tables, the crossing pointer, and the column. -/
structure RowState where
  tbl : ℕ → ℝ
  cen : ℕ → ℕ
  ptr : ℕ
  col : ℕ

/-- One column of the row scan: advance the crossing pointer, then store the block cost
and a realizing centre. -/
noncomputable def tableStep (x : ℕ → ℝ) (n i : ℕ) (s : RowState) : Counted RowState :=
  (crossMin cmpLe (blockAB x i s.col) s.ptr s.col) >>= fun r =>
  (writeMem s.tbl (i * n + s.col) r.val) >>= fun tbl' =>
  (writeMem s.cen (i * n + s.col) r.arg) >>= fun cen' =>
  ⟨⟨tbl', cen', r.cross, s.col + 1⟩, 0⟩

lemma tableStep_col (x : ℕ → ℝ) (n i : ℕ) (s : RowState) :
    (tableStep x n i s).value.col = s.col + 1 := rfl

lemma tableStep_ptr (x : ℕ → ℝ) (n i : ℕ) (s : RowState) :
    (tableStep x n i s).value.ptr = (crossMin cmpLe (blockAB x i s.col) s.ptr s.col).value.cross :=
  rfl

lemma tableStep_tbl (x : ℕ → ℝ) (n i : ℕ) (s : RowState) :
    (tableStep x n i s).value.tbl =
      Function.update s.tbl (i * n + s.col)
        (crossMin cmpLe (blockAB x i s.col) s.ptr s.col).value.val := rfl

lemma tableStep_cen (x : ℕ → ℝ) (n i : ℕ) (s : RowState) :
    (tableStep x n i s).value.cen =
      Function.update s.cen (i * n + s.col)
        (crossMin cmpLe (blockAB x i s.col) s.ptr s.col).value.arg := rfl

lemma countedIter_tableStep_col (x : ℕ → ℝ) (n i : ℕ) :
    ∀ (m : ℕ) (s : RowState), (countedIter (tableStep x n i) m s).value.col = s.col + m := by
  intro m
  induction m with
  | zero => intro s; simp
  | succ m ih =>
      intro s
      rw [countedIter_succ]
      simp only [Counted.bind_value]
      rw [ih, tableStep_col]
      omega

/-- The cell `(i,j)` of the table is correctly filled. -/
def CellOK (x : ℕ → ℝ) (n : ℕ) (tbl : ℕ → ℝ) (cen : ℕ → ℕ) (i j : ℕ) : Prop :=
  tbl (i * n + j) = bcost x i j ∧ i ≤ cen (i * n + j) ∧ cen (i * n + j) ≤ j ∧
    max (x (cen (i * n + j)) - x i) (x j - x (cen (i * n + j))) = bcost x i j

/-- The invariant of the row scan. -/
def RowInv (x : ℕ → ℝ) (n i : ℕ) (tbl0 : ℕ → ℝ) (cen0 : ℕ → ℕ) (s : RowState) : Prop :=
  i ≤ s.col ∧ i ≤ s.ptr ∧ s.ptr ≤ s.col ∧
    (∀ l, l < s.ptr → ¬ (x s.col - x l ≤ x l - x i)) ∧
    (∀ q, q < i * n → s.tbl q = tbl0 q ∧ s.cen q = cen0 q) ∧
    (∀ j, i ≤ j → j < s.col → CellOK x n s.tbl s.cen i j)

lemma cmpLe_value' (a b : ℝ) : (cmpLe a b).value = decide (a ≤ b) := rfl

lemma rowInv_step (hx : StrictMono x) (n i : ℕ) (tbl0 : ℕ → ℝ) (cen0 : ℕ → ℕ) (s : RowState)
    (hs : RowInv x n i tbl0 cen0 s) : RowInv x n i tbl0 cen0 (tableStep x n i s).value := by
  obtain ⟨hcol, hptri, hptr, hbefore, hkeep, hcells⟩ := hs
  set j := s.col with hj
  set A : ℕ → ℝ := fun l => x l - x i with hA
  set B : ℕ → ℝ := fun l => x j - x l with hB
  have hmono : Monotone A := by
    intro a b hab; simp only [hA]; have := hx.monotone hab; linarith
  have hanti : Antitone B := by
    intro a b hab; simp only [hB]; have := hx.monotone hab; linarith
  have hfAB : ∀ l, l ≤ j → (blockAB x i j l).value = (A l, B l) := fun l _ => rfl
  have hBm : B j ≤ A j := by
    simp only [hA, hB]
    have := hx.monotone hcol
    linarith
  obtain ⟨hgec, hlec, hcrossc, hminc⟩ :=
    crossMin_cross (cle := cmpLe) (fAB := blockAB x i j) (A := A) (B := B)
      cmpLe_value' hfAB hptr hBm
  obtain ⟨hargle, hargor, hvaleq, hvalmin⟩ :=
    crossMin_spec (cle := cmpLe) (fAB := blockAB x i j) (A := A) (B := B)
      cmpLe_value' hfAB (fun a b hab _ => hmono hab) (fun a b hab _ => hanti hab) hptr
      (fun l hl => hbefore l hl) hBm
  set r := (crossMin cmpLe (blockAB x i j) s.ptr j).value with hr
  -- the computed value is the block cost
  have hvalbc : r.val = bcost x i j := by
    obtain ⟨l0, hl0i, hl0j, hl0⟩ := exists_maxblock_eq_bcost hx.monotone hcol
    have h1 : r.val ≤ bcost x i j := by
      have := hvalmin l0 hl0j
      rwa [hl0] at this
    have h2 : bcost x i j ≤ r.val := by
      rw [hvaleq]
      exact bcost_le_maxblock hx.monotone hcol hargle
    linarith
  -- the returned index lies in the block
  have hargi : i ≤ r.arg := by
    by_contra hlt
    push_neg at hlt
    have hxl : x r.arg < x i := hx hlt
    have h1 : bcost x i j ≤ x j - x i := by
      have := bcost_le_maxblock_of_mem hx.monotone hcol (le_refl i) hcol
      have he : max (x i - x i) (x j - x i) = x j - x i := by
        rw [max_eq_right (by have := hx.monotone hcol; linarith)]
      rwa [he] at this
    have h2 : x j - x i < B r.arg := by simp only [hB]; linarith
    have h3 : B r.arg ≤ max (A r.arg) (B r.arg) := le_max_right _ _
    rw [← hvaleq, hvalbc] at h3
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tableStep_col]; omega
  · rw [tableStep_ptr, ← hj, ← hr]; exact le_trans hptri hgec
  · rw [tableStep_col, tableStep_ptr, ← hj, ← hr]; omega
  · rw [tableStep_col, tableStep_ptr, ← hj, ← hr]
    intro l hl
    have hnl : ¬ (B l ≤ A l) := by
      rcases lt_or_ge l s.ptr with h | h
      · exact hbefore l h
      · exact hminc l h hl
    simp only [hA, hB] at hnl
    push_neg at hnl ⊢
    have hxx : x j ≤ x (j + 1) := hx.monotone (by omega)
    linarith
  · intro q hq
    rw [tableStep_tbl, tableStep_cen, ← hj]
    have hne : q ≠ i * n + j := by omega
    rw [Function.update_of_ne hne, Function.update_of_ne hne]
    exact hkeep q hq
  · intro j' hij' hj'
    rw [tableStep_col] at hj'
    rw [tableStep_tbl, tableStep_cen, ← hj, ← hr]
    rw [← hj] at hj'
    rcases lt_or_ge j' j with hlt | hge
    · have hne : i * n + j' ≠ i * n + j := by omega
      have hc := hcells j' hij' hlt
      simp only [CellOK, Function.update_of_ne hne]
      exact hc
    · have hj'j : j' = j := by omega
      subst hj'j
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Function.update_self]; exact hvalbc
      · rw [Function.update_self]; exact hargi
      · rw [Function.update_self]; exact hargle
      · rw [Function.update_self]
        have hve := hvaleq
        simp only [hA, hB] at hve
        rw [← hve]; exact hvalbc

/-- Specification of one row of the block-cost table. -/
theorem tableRow_spec (hx : StrictMono x) (n i : ℕ) (tbl0 : ℕ → ℝ) (cen0 : ℕ → ℕ) :
    let s := (countedIter (tableStep x n i) (n - i) ⟨tbl0, cen0, i, i⟩).value
    s.col = i + (n - i) ∧ s.ptr ≤ s.col ∧
      (∀ q, q < i * n → s.tbl q = tbl0 q ∧ s.cen q = cen0 q) ∧
      (∀ j, i ≤ j → j < i + (n - i) → CellOK x n s.tbl s.cen i j) := by
  intro s
  have hcol : s.col = i + (n - i) := countedIter_tableStep_col x n i (n - i) _
  have hinv : RowInv x n i tbl0 cen0 s :=
    countedIter_inv (P := RowInv x n i tbl0 cen0) (rowInv_step hx n i tbl0 cen0) (n - i) _
      ⟨le_rfl, le_rfl, le_rfl, by intro l hl; push_neg; have := hx hl; linarith,
        fun q _ => ⟨rfl, rfl⟩, by
          intro j h1 h2; exact absurd h2 (Nat.not_lt.2 h1)⟩
  obtain ⟨-, -, hptr, -, hkeep, hcells⟩ := hinv
  exact ⟨hcol, hptr, hkeep, fun j h1 h2 => hcells j h1 (by omega)⟩

/-- Cost of one column of the row scan (amortized through the pointer). -/
lemma tableStep_work (x : ℕ → ℝ) (n i : ℕ) (s : RowState) :
    (tableStep x n i s).ops.work + 6 * s.ptr ≤ 26 + 6 * (tableStep x n i s).value.ptr := by
  have hcm := crossMin_work_le (cle := cmpLe) (fAB := blockAB x i s.col) 1 5
    (fun a b => by simp [cmpLe, OpCount.work]) (blockAB_work x i s.col) s.ptr s.col
  have hge : s.ptr ≤ (crossMin cmpLe (blockAB x i s.col) s.ptr s.col).value.cross := by
    have := findFromC_ge (crossStep cmpLe (blockAB x i s.col)) (s.col - s.ptr) s.ptr
    have heq : (crossMin cmpLe (blockAB x i s.col) s.ptr s.col).value.cross
        = (findFromC (crossStep cmpLe (blockAB x i s.col)) s.ptr (s.col - s.ptr)).value := by
      simp only [crossMin, Counted.bind_value]
      split <;> rfl
    omega
  have hops : (tableStep x n i s).ops.work
      = (crossMin cmpLe (blockAB x i s.col) s.ptr s.col).ops.work + 1 + 1 := by
    simp only [tableStep, Counted.bind_ops, OpCount.add_work, writeMem_ops, OpCount.work_zero]
    simp [OpCount.work]
  rw [tableStep_ptr]
  omega

lemma tableRow_work (x : ℕ → ℝ) (n i : ℕ) (tbl0 : ℕ → ℝ) (cen0 : ℕ → ℕ) :
    (countedIter (tableStep x n i) (n - i) ⟨tbl0, cen0, i, i⟩).ops.work ≤ 32 * n := by
  set s0 : RowState := ⟨tbl0, cen0, i, i⟩ with hs0
  have hpot := countedIter_work_potential_inv (f := tableStep x n i)
    (P := fun s => s.ptr ≤ s.col) (φ := fun s => 6 * s.ptr) (C := 26)
    (by
      intro s hs
      rw [tableStep_col, tableStep_ptr]
      have heq : (crossMin cmpLe (blockAB x i s.col) s.ptr s.col).value.cross
          = (findFromC (crossStep cmpLe (blockAB x i s.col)) s.ptr (s.col - s.ptr)).value := by
        simp only [crossMin, Counted.bind_value]
        split <;> rfl
      have := findFromC_le (crossStep cmpLe (blockAB x i s.col)) (s.col - s.ptr) s.ptr
      omega)
    (fun s _ => tableStep_work x n i s) (n - i) s0 (le_rfl)
  have hcol : (countedIter (tableStep x n i) (n - i) s0).value.col = i + (n - i) :=
    countedIter_tableStep_col x n i (n - i) s0
  have hptr : (countedIter (tableStep x n i) (n - i) s0).value.ptr
      ≤ (countedIter (tableStep x n i) (n - i) s0).value.col := by
    have := countedIter_inv (P := fun s : RowState => s.ptr ≤ s.col)
      (f := tableStep x n i)
      (by
        intro s hs
        rw [tableStep_col, tableStep_ptr]
        have heq : (crossMin cmpLe (blockAB x i s.col) s.ptr s.col).value.cross
            = (findFromC (crossStep cmpLe (blockAB x i s.col)) s.ptr (s.col - s.ptr)).value := by
          simp only [crossMin, Counted.bind_value]
          split <;> rfl
        have := findFromC_le (crossStep cmpLe (blockAB x i s.col)) (s.col - s.ptr) s.ptr
        omega)
      (n - i) s0 le_rfl
    exact this
  have h1 : (countedIter (tableStep x n i) (n - i) s0).value.ptr ≤ i + (n - i) := by omega
  have h2 : 26 * (n - i) ≤ 26 * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h3 : i + (n - i) ≤ i + n := by omega
  have e1 : s0.ptr = i := by rw [hs0]
  simp only [] at hpot
  omega

/-! ## The whole table -/

/-- The state of the table computation. -/
structure TabState where
  tbl : ℕ → ℝ
  cen : ℕ → ℕ
  row : ℕ

/-- One row of the table computation. -/
noncomputable def tableOuterStep (x : ℕ → ℝ) (n : ℕ) (s : TabState) : Counted TabState :=
  (countedIter (tableStep x n s.row) (n - s.row) ⟨s.tbl, s.cen, s.row, s.row⟩) >>= fun r =>
  ⟨⟨r.tbl, r.cen, s.row + 1⟩, 0⟩

/-- **Phase 1 of the ordered-line algorithm**: the block-cost table together with a
realizing centre for every block. -/
noncomputable def blockTableRun (x : ℕ → ℝ) (n : ℕ) : Counted TabState :=
  (Counted.charge { writes := n * n }) >>= fun _ =>
  countedIter (tableOuterStep x n) n ⟨fun _ => 0, fun _ => 0, 0⟩

lemma tableOuterStep_row (x : ℕ → ℝ) (n : ℕ) (s : TabState) :
    (tableOuterStep x n s).value.row = s.row + 1 := rfl

lemma countedIter_tableOuterStep_row (x : ℕ → ℝ) (n : ℕ) :
    ∀ (m : ℕ) (s : TabState), (countedIter (tableOuterStep x n) m s).value.row = s.row + m := by
  intro m
  induction m with
  | zero => intro s; simp
  | succ m ih =>
      intro s
      rw [countedIter_succ]
      simp only [Counted.bind_value]
      rw [ih, tableOuterStep_row]
      omega

/-- The invariant of the table computation. -/
def TabInv (x : ℕ → ℝ) (n : ℕ) (s : TabState) : Prop :=
  ∀ i j, i < s.row → i ≤ j → j < n → CellOK x n s.tbl s.cen i j

lemma tabInv_step (hx : StrictMono x) (n : ℕ) (s : TabState) (hs : TabInv x n s) :
    TabInv x n (tableOuterStep x n s).value := by
  obtain ⟨hcol, hptr, hkeep, hcells⟩ := tableRow_spec hx n s.row s.tbl s.cen
  intro i j hi hij hj
  rw [tableOuterStep_row] at hi
  have htbl : (tableOuterStep x n s).value.tbl
      = (countedIter (tableStep x n s.row) (n - s.row) ⟨s.tbl, s.cen, s.row, s.row⟩).value.tbl :=
    rfl
  have hcen : (tableOuterStep x n s).value.cen
      = (countedIter (tableStep x n s.row) (n - s.row) ⟨s.tbl, s.cen, s.row, s.row⟩).value.cen :=
    rfl
  rcases Nat.lt_or_ge i s.row with hlt | hge
  · -- an earlier row: untouched
    have hq : i * n + j < s.row * n := by
      have h0 : (i + 1) * n ≤ s.row * n := Nat.mul_le_mul_right n hlt
      have h1 : (i + 1) * n = i * n + n := by ring
      omega
    obtain ⟨h1, h2⟩ := hkeep (i * n + j) hq
    have := hs i j hlt hij hj
    simp only [CellOK, htbl, hcen, h1, h2]
    exact this
  · have hirow : i = s.row := by omega
    have hji : j < s.row + (n - s.row) := by omega
    have hcj := hcells j (by omega) hji
    rw [hirow]
    simpa [CellOK, htbl, hcen] using hcj

/-- **Correctness of phase 1**: every cell `(i,j)` with `i ≤ j < n` holds the one-centre
cost of the block `[i,j]` and the index of a point of the block realizing it. -/
theorem blockTable_correct (hx : StrictMono x) (n : ℕ) (i j : ℕ) (hij : i ≤ j) (hj : j < n) :
    CellOK x n (blockTableRun x n).value.tbl (blockTableRun x n).value.cen i j := by
  have hval : (blockTableRun x n).value
      = (countedIter (tableOuterStep x n) n
          (⟨fun _ => 0, fun _ => 0, 0⟩ : TabState)).value := rfl
  have hinv : TabInv x n (countedIter (tableOuterStep x n) n
      (⟨fun _ => 0, fun _ => 0, 0⟩ : TabState)).value :=
    countedIter_inv (P := TabInv x n) (tabInv_step hx n) n _
      (by intro i j hi; exact absurd hi (Nat.not_lt_zero i))
  have hrow : (countedIter (tableOuterStep x n) n
      (⟨fun _ => 0, fun _ => 0, 0⟩ : TabState)).value.row = n := by
    have := countedIter_tableOuterStep_row x n n (⟨fun _ => 0, fun _ => 0, 0⟩ : TabState)
    simpa using this
  rw [hval]
  exact hinv i j (by omega) hij hj

/-- **Cost of phase 1**: the whole block-cost table is computed with `O(n^2)` unit-cost
operations. -/
theorem blockTable_work_le (x : ℕ → ℝ) (n : ℕ) :
    (blockTableRun x n).ops.work ≤ 33 * n * n := by
  have houter : ∀ s : TabState, (tableOuterStep x n s).ops.work ≤ 32 * n := by
    intro s
    have : (tableOuterStep x n s).ops.work
        = (countedIter (tableStep x n s.row) (n - s.row)
            (⟨s.tbl, s.cen, s.row, s.row⟩ : RowState)).ops.work := by
      simp [tableOuterStep]
    rw [this]
    exact tableRow_work x n s.row s.tbl s.cen
  have hloop := countedIter_work_le (f := tableOuterStep x n) (32 * n) houter n
    (⟨fun _ => 0, fun _ => 0, 0⟩ : TabState)
  have hops : (blockTableRun x n).ops.work
      = n * n + (countedIter (tableOuterStep x n) n
          (⟨fun _ => 0, fun _ => 0, 0⟩ : TabState)).ops.work := by
    simp only [blockTableRun, Counted.bind_ops, Counted.charge_ops, OpCount.add_work]
    norm_num [OpCount.work]
  have : 32 * n * n + n * n ≤ 33 * n * n := by ring_nf; omega
  omega

end Line

end Q764
