/-
# Q764 — Stage 3c.1: costed iteration, a monotone pointer search, and the generic
crossing minimum

This module contains the *reusable machinery* of the exact ordered-line algorithm:

* `Q764.Line.countedIter` — a costed `for` loop whose state carries its own counter, with
  an invariant lemma and an amortized (potential-function) cost lemma;
* `Q764.Line.findFromC` — a costed linear search starting at a given position, together
  with its exact specification and a cost bound proportional to the distance travelled;
* `Q764.Line.crossMin` — the costed routine computing
  `min_{i ≤ m} max (A i) (B i)` for a nondecreasing family `A` and a nonincreasing family
  `B`, by advancing the *crossing pointer* `c = least i with B i ≤ A i`.  Its cost is
  proportional to the distance travelled by the pointer, which is what makes both the
  block-cost table (`O(n^2)`) and the dynamic-programming layers (`O(k*n)`) fast.

Everything is generic in the ordered type `α` and in the costed evaluation of `A` and `B`,
so that the very same routine is instantiated twice later on.
-/
import RMS.Q764Line

namespace Q764

namespace Line

universe u v

/-! ## A costed iteration combinator -/

section Iter

variable {σ : Type u}

/-- Iterate a costed step `m` times. -/
def countedIter (f : σ → Counted σ) : ℕ → σ → Counted σ
  | 0, s => ⟨s, 0⟩
  | m + 1, s => (f s) >>= countedIter f m

@[simp] lemma countedIter_zero (f : σ → Counted σ) (s : σ) :
    countedIter f 0 s = ⟨s, 0⟩ := rfl

lemma countedIter_succ (f : σ → Counted σ) (m : ℕ) (s : σ) :
    countedIter f (m + 1) s = (f s) >>= countedIter f m := rfl

/-- Loop invariant. -/
lemma countedIter_inv {P : σ → Prop} {f : σ → Counted σ}
    (hf : ∀ s, P s → P (f s).value) :
    ∀ (m : ℕ) (s : σ), P s → P (countedIter f m s).value := by
  intro m
  induction m with
  | zero => intro s hs; exact hs
  | succ m ih =>
      intro s hs
      rw [countedIter_succ]
      simp only [Counted.bind_value]
      exact ih _ (hf s hs)

/-- Amortized cost of the loop, via a potential function. -/
lemma countedIter_work_potential {f : σ → Counted σ} (φ : σ → ℕ) (C : ℕ)
    (hf : ∀ s, (f s).ops.work + φ s ≤ C + φ (f s).value) :
    ∀ (m : ℕ) (s : σ),
      (countedIter f m s).ops.work + φ s ≤ C * m + φ (countedIter f m s).value := by
  intro m
  induction m with
  | zero => intro s; simp
  | succ m ih =>
      intro s
      rw [countedIter_succ]
      simp only [Counted.bind_ops, OpCount.add_work, Counted.bind_value]
      have h1 := hf s
      have h2 := ih (f s).value
      have : C * (m + 1) = C + C * m := by ring
      omega

/-- Amortized cost of the loop under a loop invariant. -/
lemma countedIter_work_potential_inv {f : σ → Counted σ} (P : σ → Prop) (φ : σ → ℕ) (C : ℕ)
    (hP : ∀ s, P s → P (f s).value)
    (hf : ∀ s, P s → (f s).ops.work + φ s ≤ C + φ (f s).value) :
    ∀ (m : ℕ) (s : σ), P s →
      (countedIter f m s).ops.work + φ s ≤ C * m + φ (countedIter f m s).value := by
  intro m
  induction m with
  | zero => intro s _; simp
  | succ m ih =>
      intro s hs
      rw [countedIter_succ]
      simp only [Counted.bind_ops, OpCount.add_work, Counted.bind_value]
      have h1 := hf s hs
      have h2 := ih (f s).value (hP s hs)
      have : C * (m + 1) = C + C * m := by ring
      omega

/-- Plain cost of the loop under a loop invariant. -/
lemma countedIter_work_le_inv {f : σ → Counted σ} (P : σ → Prop) (C : ℕ)
    (hP : ∀ s, P s → P (f s).value) (hf : ∀ s, P s → (f s).ops.work ≤ C) :
    ∀ (m : ℕ) (s : σ), P s → (countedIter f m s).ops.work ≤ C * m := by
  intro m s hs
  have := countedIter_work_potential_inv (f := f) P (fun _ => 0) C hP
    (by intro s hs; simpa using hf s hs) m s hs
  simpa using this

/-- Plain cost of the loop when each step has a uniform bound. -/
lemma countedIter_work_le {f : σ → Counted σ} (C : ℕ) (hf : ∀ s, (f s).ops.work ≤ C) :
    ∀ (m : ℕ) (s : σ), (countedIter f m s).ops.work ≤ C * m := by
  intro m s
  have := countedIter_work_potential (f := f) (fun _ => 0) C (by intro s; simpa using hf s) m s
  simpa using this

end Iter

/-! ## A costed read of the input -/

/-- One read of the input sequence. -/
def readIn {α : Type u} (x : ℕ → α) (i : ℕ) : Counted α := ⟨x i, { reads := 1 }⟩

@[simp] lemma readIn_value {α : Type u} (x : ℕ → α) (i : ℕ) : (readIn x i).value = x i := rfl
@[simp] lemma readIn_ops {α : Type u} (x : ℕ → α) (i : ℕ) :
    (readIn x i).ops = { reads := 1 } := rfl

/-- Costed write into a random-access store modelled as a total function. -/
def writeMem {α : Type u} (f : ℕ → α) (i : ℕ) (v : α) : Counted (ℕ → α) :=
  ⟨Function.update f i v, { writes := 1 }⟩

@[simp] lemma writeMem_value {α : Type u} (f : ℕ → α) (i : ℕ) (v : α) :
    (writeMem f i v).value = Function.update f i v := rfl
@[simp] lemma writeMem_ops {α : Type u} (f : ℕ → α) (i : ℕ) (v : α) :
    (writeMem f i v).ops = { writes := 1 } := rfl

/-! ## A costed linear search -/

/-- Search for the first position `≥ c` at which the costed predicate `P` holds, giving up
after `fuel` steps. -/
def findFromC (P : ℕ → Counted Bool) : ℕ → ℕ → Counted ℕ
  | c, 0 => ⟨c, 0⟩
  | c, fuel + 1 => (P c) >>= fun b => if b then ⟨c, 0⟩ else findFromC P (c + 1) fuel

lemma findFromC_zero (P : ℕ → Counted Bool) (c : ℕ) : findFromC P c 0 = ⟨c, 0⟩ := rfl

lemma findFromC_succ (P : ℕ → Counted Bool) (c fuel : ℕ) :
    findFromC P c (fuel + 1) =
      (P c) >>= fun b => if b then ⟨c, 0⟩ else findFromC P (c + 1) fuel := rfl

lemma findFromC_ge (P : ℕ → Counted Bool) :
    ∀ (fuel c : ℕ), c ≤ (findFromC P c fuel).value := by
  intro fuel
  induction fuel with
  | zero => intro c; simp [findFromC_zero]
  | succ f ih =>
      intro c
      rw [findFromC_succ]
      simp only [Counted.bind_value]
      by_cases hb : (P c).value = true
      · simp [hb]
      · simp only [Bool.not_eq_true] at hb
        simp only [hb, Bool.false_eq_true, if_false]
        exact le_trans (Nat.le_succ c) (ih (c + 1))

lemma findFromC_le (P : ℕ → Counted Bool) :
    ∀ (fuel c : ℕ), (findFromC P c fuel).value ≤ c + fuel := by
  intro fuel
  induction fuel with
  | zero => intro c; simp [findFromC_zero]
  | succ f ih =>
      intro c
      rw [findFromC_succ]
      simp only [Counted.bind_value]
      by_cases hb : (P c).value = true
      · simp [hb]
      · simp only [Bool.not_eq_true] at hb
        simp only [hb, Bool.false_eq_true, if_false]
        have := ih (c + 1)
        omega

/-- Nothing is missed before the returned position. -/
lemma findFromC_false_before (P : ℕ → Counted Bool) :
    ∀ (fuel c l : ℕ), c ≤ l → l < (findFromC P c fuel).value → (P l).value = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro c l hcl hlt
      simp [findFromC_zero] at hlt
      omega
  | succ f ih =>
      intro c l hcl hlt
      rw [findFromC_succ] at hlt
      simp only [Counted.bind_value] at hlt
      by_cases hb : (P c).value = true
      · simp [hb] at hlt; omega
      · simp only [Bool.not_eq_true] at hb
        simp only [hb, Bool.false_eq_true, if_false] at hlt
        rcases Nat.eq_or_lt_of_le hcl with rfl | hlt'
        · exact hb
        · exact ih (c + 1) l hlt' hlt

/-- If the predicate holds somewhere in the searched window, the returned position
satisfies it. -/
lemma findFromC_true (P : ℕ → Counted Bool) :
    ∀ (fuel c : ℕ), (∃ l, c ≤ l ∧ l ≤ c + fuel ∧ (P l).value = true) →
      (P (findFromC P c fuel).value).value = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro c h
      obtain ⟨l, hl1, hl2, hl3⟩ := h
      have : l = c := by omega
      subst this
      simpa [findFromC_zero] using hl3
  | succ f ih =>
      intro c h
      rw [findFromC_succ]
      simp only [Counted.bind_value]
      by_cases hb : (P c).value = true
      · simp [hb]
      · simp only [Bool.not_eq_true] at hb
        simp only [hb, Bool.false_eq_true, if_false]
        refine ih (c + 1) ?_
        obtain ⟨l, hl1, hl2, hl3⟩ := h
        have hlc : l ≠ c := by intro hc; rw [hc] at hl3; rw [hb] at hl3; exact absurd hl3 (by simp)
        exact ⟨l, by omega, by omega, hl3⟩

/-- The cost of the search is proportional to the distance travelled. -/
lemma findFromC_work_le (P : ℕ → Counted Bool) (w : ℕ) (hw : ∀ l, (P l).ops.work ≤ w) :
    ∀ (fuel c : ℕ),
      (findFromC P c fuel).ops.work ≤ w * ((findFromC P c fuel).value + 1 - c) := by
  intro fuel
  induction fuel with
  | zero => intro c; simp [findFromC_zero]
  | succ f ih =>
      intro c
      rw [findFromC_succ]
      simp only [Counted.bind_ops, OpCount.add_work, Counted.bind_value]
      by_cases hb : (P c).value = true
      · simp only [hb, if_true]
        have := hw c
        simpa using by
          have : (P c).ops.work + 0 ≤ w * (c + 1 - c) := by simpa using this
          simpa using this
      · simp only [Bool.not_eq_true] at hb
        simp only [hb, Bool.false_eq_true, if_false]
        have h1 := hw c
        have h2 := ih (c + 1)
        have h3 : c + 1 ≤ (findFromC P (c + 1) f).value := findFromC_ge P f (c + 1)
        set v := (findFromC P (c + 1) f).value with hv
        have : w * (v + 1 - (c + 1)) + w = w * (v + 1 - c) := by
          have hvc : v + 1 - c = (v + 1 - (c + 1)) + 1 := by omega
          rw [hvc]; ring
        omega

/-! ## The generic crossing minimum -/

section Cross

variable {α : Type} [LinearOrder α]

/-- The result of the crossing routine: the crossing pointer, the minimizing index, and
the minimal value. -/
structure CrossResult (α : Type) where
  cross : ℕ
  arg : ℕ
  val : α

/-- Costed maximum of two values. -/
def maxC (cle : α → α → Counted Bool) (a b : α) : Counted α :=
  (cle a b) >>= fun t => ⟨if t then b else a, 0⟩

/-- The costed test `B l ≤ A l`. -/
def crossStep (cle : α → α → Counted Bool) (fAB : ℕ → Counted (α × α)) (l : ℕ) :
    Counted Bool :=
  (fAB l) >>= fun p => cle p.2 p.1

/-- The costed crossing minimum: advance the pointer from `start` to the first crossing,
then return the better of the two candidates at the crossing and its predecessor. -/
def crossMin (cle : α → α → Counted Bool) (fAB : ℕ → Counted (α × α)) (start m : ℕ) :
    Counted (CrossResult α) :=
  (findFromC (crossStep cle fAB) start (m - start)) >>= fun c =>
  (fAB c) >>= fun p1 =>
  (maxC cle p1.1 p1.2) >>= fun v1 =>
  (fAB (c - 1)) >>= fun p2 =>
  (maxC cle p2.1 p2.2) >>= fun v2 =>
  (cle v1 v2) >>= fun t =>
  ⟨if t then ⟨c, c, v1⟩ else ⟨c, c - 1, v2⟩, 0⟩

variable {cle : α → α → Counted Bool} {fAB : ℕ → Counted (α × α)} {A B : ℕ → α}

lemma maxC_value (hcle : ∀ a b, (cle a b).value = decide (a ≤ b)) (a b : α) :
    (maxC cle a b).value = max a b := by
  simp only [maxC, Counted.bind_value, hcle]
  by_cases h : a ≤ b
  · simp [h]
  · simp [h, max_eq_left (le_of_not_ge h)]

omit [LinearOrder α] in
lemma maxC_work (wcle : ℕ) (hclew : ∀ a b, (cle a b).ops.work ≤ wcle) (a b : α) :
    (maxC cle a b).ops.work ≤ wcle := by
  simp only [maxC, Counted.bind_ops, OpCount.add_work]
  simpa using hclew a b

lemma crossStep_value (hcle : ∀ a b, (cle a b).value = decide (a ≤ b))
    {l : ℕ} (hfl : (fAB l).value = (A l, B l)) :
    (crossStep cle fAB l).value = decide (B l ≤ A l) := by
  simp [crossStep, hfl, hcle]

omit [LinearOrder α] in
lemma crossStep_work (wcle wf : ℕ) (hclew : ∀ a b, (cle a b).ops.work ≤ wcle)
    (hfw : ∀ i, (fAB i).ops.work ≤ wf) (l : ℕ) :
    (crossStep cle fAB l).ops.work ≤ wf + wcle := by
  simp only [crossStep, Counted.bind_ops, OpCount.add_work]
  exact Nat.add_le_add (hfw l) (hclew _ _)

/-- The crossing pointer returned by `crossMin` is the first crossing at or after
`start`, and it lies in `[start, m]`. -/
theorem crossMin_cross (hcle : ∀ a b, (cle a b).value = decide (a ≤ b))
    {start m : ℕ} (hfAB : ∀ i, i ≤ m → (fAB i).value = (A i, B i)) (hsm : start ≤ m)
    (hBm : B m ≤ A m) :
    let c := (crossMin cle fAB start m).value.cross
    start ≤ c ∧ c ≤ m ∧ B c ≤ A c ∧ ∀ l, start ≤ l → l < c → ¬ (B l ≤ A l) := by
  intro c
  have hcdef : c = (findFromC (crossStep cle fAB) start (m - start)).value := by
    simp only [c, crossMin, Counted.bind_value]
    split <;> rfl
  have hge : start ≤ c := by
    rw [hcdef]; exact findFromC_ge _ _ _
  have hle : c ≤ m := by
    rw [hcdef]
    have := findFromC_le (crossStep cle fAB) (m - start) start
    omega
  have hex : ∃ l, start ≤ l ∧ l ≤ start + (m - start) ∧
      (crossStep cle fAB l).value = true := by
    refine ⟨m, hsm, by omega, ?_⟩
    rw [crossStep_value hcle (hfAB m le_rfl)]
    simpa using hBm
  have htrue : (crossStep cle fAB c).value = true := by
    rw [hcdef]; exact findFromC_true _ _ _ hex
  rw [crossStep_value hcle (hfAB c hle)] at htrue
  refine ⟨hge, hle, by simpa using htrue, ?_⟩
  intro l hsl hlc
  have hfalse : (crossStep cle fAB l).value = false := by
    rw [hcdef] at hlc
    exact findFromC_false_before _ _ _ _ hsl hlc
  rw [crossStep_value hcle (hfAB l (by omega))] at hfalse
  simpa using hfalse

/-- Correctness of `crossMin`: the returned value is the minimum of `max (A i) (B i)` over
`i ≤ m`, attained at the returned index. -/
theorem crossMin_spec (hcle : ∀ a b, (cle a b).value = decide (a ≤ b))
    {start m : ℕ} (hfAB : ∀ i, i ≤ m → (fAB i).value = (A i, B i))
    (hA : ∀ a b, a ≤ b → b ≤ m → A a ≤ A b) (hB : ∀ a b, a ≤ b → b ≤ m → B b ≤ B a)
    (hsm : start ≤ m)
    (hbefore : ∀ l, l < start → ¬ (B l ≤ A l)) (hBm : B m ≤ A m) :
    let r := (crossMin cle fAB start m).value
    r.arg ≤ m ∧ (r.arg = r.cross ∨ r.arg = r.cross - 1) ∧
      r.val = max (A r.arg) (B r.arg) ∧ (∀ i, i ≤ m → r.val ≤ max (A i) (B i)) := by
  intro r
  obtain ⟨hge, hle, hcross, hmin⟩ := crossMin_cross hcle hfAB hsm hBm
  set c := (crossMin cle fAB start m).value.cross with hc
  have hminall : ∀ l, l < c → ¬ (B l ≤ A l) := by
    intro l hl
    rcases lt_or_ge l start with h | h
    · exact hbefore l h
    · exact hmin l h hl
  -- unfold the tail of the routine
  have hv1 : (maxC cle (fAB c).value.1 (fAB c).value.2).value = max (A c) (B c) := by
    rw [maxC_value hcle]; rw [hfAB c hle]
  have hv2 : (maxC cle (fAB (c - 1)).value.1 (fAB (c - 1)).value.2).value
      = max (A (c - 1)) (B (c - 1)) := by
    rw [maxC_value hcle]; rw [hfAB (c - 1) (le_trans (Nat.sub_le c 1) hle)]
  have hrdef : r = (if (cle (max (A c) (B c)) (max (A (c-1)) (B (c-1)))).value then
      (⟨c, c, max (A c) (B c)⟩ : CrossResult α) else ⟨c, c - 1, max (A (c-1)) (B (c-1))⟩) := by
    simp only [r, crossMin, Counted.bind_value]
    rw [show (findFromC (crossStep cle fAB) start (m - start)).value = c by
      simp only [hc, crossMin, Counted.bind_value]; split <;> rfl]
    rw [hv1, hv2]
  have hdec : (cle (max (A c) (B c)) (max (A (c-1)) (B (c-1)))).value
      = decide (max (A c) (B c) ≤ max (A (c-1)) (B (c-1))) := hcle _ _
  rw [hdec] at hrdef
  have hkey : ∀ i, i ≤ m → min (max (A c) (B c)) (max (A (c-1)) (B (c-1))) ≤ max (A i) (B i) := by
    intro i _
    rcases le_or_gt c i with h | h
    · refine le_trans (min_le_left _ _) ?_
      refine le_trans (max_le le_rfl hcross) (le_trans (hA c i h ‹i ≤ m›) (le_max_left _ _))
    · have hc1 : 0 < c := by omega
      refine le_trans (min_le_right _ _) ?_
      have hlt : A (c - 1) < B (c - 1) := lt_of_not_ge (hminall (c - 1) (by omega))
      rw [max_eq_right (le_of_lt hlt)]
      exact le_trans (hB i (c - 1) (by omega) (le_trans (Nat.sub_le c 1) hle)) (le_max_right _ _)
  by_cases hb : max (A c) (B c) ≤ max (A (c-1)) (B (c-1))
  · rw [hrdef, if_pos (by simpa using hb)]
    refine ⟨hle, Or.inl rfl, rfl, ?_⟩
    intro i hi
    have := hkey i hi
    rwa [min_eq_left hb] at this
  · rw [hrdef, if_neg (by simpa using hb)]
    refine ⟨le_trans (Nat.sub_le c 1) hle, Or.inr rfl, rfl, ?_⟩
    intro i hi
    have := hkey i hi
    rwa [min_eq_right (le_of_not_ge hb)] at this

omit [LinearOrder α] in
lemma crossMin_cross_eq (cle : α → α → Counted Bool) (fAB : ℕ → Counted (α × α))
    (start m : ℕ) :
    (crossMin cle fAB start m).value.cross
      = (findFromC (crossStep cle fAB) start (m - start)).value := by
  simp only [crossMin, Counted.bind_value]
  split <;> rfl

omit [LinearOrder α] in
lemma crossMin_arg_le_cross (cle : α → α → Counted Bool) (fAB : ℕ → Counted (α × α))
    (start m : ℕ) :
    (crossMin cle fAB start m).value.arg ≤ (crossMin cle fAB start m).value.cross := by
  simp only [crossMin, Counted.bind_value]
  split <;> simp

omit [LinearOrder α] in
lemma crossMin_cross_le (cle : α → α → Counted Bool) (fAB : ℕ → Counted (α × α))
    (start m : ℕ) :
    (crossMin cle fAB start m).value.cross ≤ start + (m - start) := by
  rw [crossMin_cross_eq]
  exact findFromC_le _ _ _

omit [LinearOrder α] in
/-- The cost of `crossMin` is proportional to the distance travelled by the pointer. -/
theorem crossMin_work_le (wcle wf : ℕ) (hclew : ∀ a b, (cle a b).ops.work ≤ wcle)
    (hfw : ∀ i, (fAB i).ops.work ≤ wf) (start m : ℕ) :
    (crossMin cle fAB start m).ops.work ≤
      (wf + wcle) * ((crossMin cle fAB start m).value.cross - start) + 4 * (wf + wcle) := by
  set c := (findFromC (crossStep cle fAB) start (m - start)).value with hcv
  have hcross : (crossMin cle fAB start m).value.cross = c := by
    simp only [crossMin, Counted.bind_value, hcv]
    split <;> rfl
  have hge : start ≤ c := findFromC_ge _ _ _
  have hfind : (findFromC (crossStep cle fAB) start (m - start)).ops.work
      ≤ (wf + wcle) * (c + 1 - start) :=
    findFromC_work_le _ (wf + wcle)
      (crossStep_work wcle wf hclew hfw) (m - start) start
  have hops : (crossMin cle fAB start m).ops.work
      = (findFromC (crossStep cle fAB) start (m - start)).ops.work
        + ((fAB c).ops.work + ((maxC cle (fAB c).value.1 (fAB c).value.2).ops.work
        + ((fAB (c - 1)).ops.work + ((maxC cle (fAB (c-1)).value.1 (fAB (c-1)).value.2).ops.work
        + ((cle (maxC cle (fAB c).value.1 (fAB c).value.2).value
              (maxC cle (fAB (c-1)).value.1 (fAB (c-1)).value.2).value).ops.work + 0))))) := by
    simp only [crossMin, Counted.bind_ops, OpCount.add_work, hcv, OpCount.work_zero]
  have h1 := hfw c
  have h2 := maxC_work (cle := cle) wcle hclew (fAB c).value.1 (fAB c).value.2
  have h3 := hfw (c - 1)
  have h4 := maxC_work (cle := cle) wcle hclew (fAB (c-1)).value.1 (fAB (c-1)).value.2
  have h5 := hclew (maxC cle (fAB c).value.1 (fAB c).value.2).value
      (maxC cle (fAB (c-1)).value.1 (fAB (c-1)).value.2).value
  rw [hcross]
  have hstep : (wf + wcle) * (c + 1 - start) = (wf + wcle) * (c - start) + (wf + wcle) := by
    have : c + 1 - start = (c - start) + 1 := by omega
    rw [this]; ring
  have hsmall : wf + wcle + wf + wcle + wcle ≤ 3 * (wf + wcle) := by omega
  omega

end Cross

end Line

end Q764
