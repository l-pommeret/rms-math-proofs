/-
# Q764 — a unit-cost operation-counting semantics

A small, auditable cost semantics for the algorithms of Q764.  Every primitive
(array read, array write, arithmetic operation, comparison, metric-distance query)
costs one unit, and the algorithms are written in the `Counted` writer monad, so that
the operation count of an actual execution is available as data.

Nothing here is allowed to hide unbounded work in a zero-cost `pure`: the loops below
are built from the costed primitives, and every cost theorem in the later files bounds
the count of *the same run* whose output is proved correct.
-/
import RMS.Q764

namespace Q764

universe u v w

/-! ## Operation counts -/

/-- A tally of the unit-cost operations performed by a run. -/
structure OpCount where
  reads : Nat := 0
  writes : Nat := 0
  arithmetic : Nat := 0
  comparisons : Nat := 0
  distanceQueries : Nat := 0
  deriving Repr, DecidableEq

namespace OpCount

/-- Componentwise sum of two operation counts. -/
def plus (a b : OpCount) : OpCount :=
  { reads := a.reads + b.reads
    writes := a.writes + b.writes
    arithmetic := a.arithmetic + b.arithmetic
    comparisons := a.comparisons + b.comparisons
    distanceQueries := a.distanceQueries + b.distanceQueries }

instance : Zero OpCount := ⟨{ }⟩

instance : Add OpCount := ⟨plus⟩

lemma add_eq (a b : OpCount) : a + b = plus a b := rfl

/-- Total number of unit-cost operations. -/
def work (c : OpCount) : Nat :=
  c.reads + c.writes + c.arithmetic + c.comparisons + c.distanceQueries

@[simp] lemma work_zero : (0 : OpCount).work = 0 := rfl

@[simp] lemma add_work (a b : OpCount) : (a + b).work = a.work + b.work := by
  cases a; cases b
  simp only [add_eq, plus, work]
  omega

@[simp] lemma zero_reads : (0 : OpCount).reads = 0 := rfl
@[simp] lemma zero_writes : (0 : OpCount).writes = 0 := rfl
@[simp] lemma zero_arithmetic : (0 : OpCount).arithmetic = 0 := rfl
@[simp] lemma zero_comparisons : (0 : OpCount).comparisons = 0 := rfl
@[simp] lemma zero_distanceQueries : (0 : OpCount).distanceQueries = 0 := rfl

@[simp] lemma zero_add' (a : OpCount) : (0 : OpCount) + a = a := by
  cases a
  simp [add_eq, plus]

@[simp] lemma add_zero' (a : OpCount) : a + (0 : OpCount) = a := by
  cases a
  simp [add_eq, plus]

lemma add_assoc' (a b c : OpCount) : a + b + c = a + (b + c) := by
  cases a; cases b; cases c
  simp only [add_eq, plus, Nat.add_assoc]

end OpCount

/-! ## The counting monad -/

/-- A value together with the operation count of the run that produced it. -/
structure Counted (α : Type u) where
  value : α
  ops : OpCount

namespace Counted

/-- A cost-free return. -/
def ret (a : α) : Counted α := ⟨a, 0⟩

def bind (c : Counted α) (f : α → Counted β) : Counted β :=
  ⟨(f c.value).value, c.ops + (f c.value).ops⟩

instance : Monad Counted where
  pure := ret
  bind := bind

@[simp] lemma pure_value (a : α) : (pure a : Counted α).value = a := rfl
@[simp] lemma pure_ops (a : α) : (pure a : Counted α).ops = 0 := rfl

@[simp] lemma bind_value (c : Counted α) (f : α → Counted β) :
    (c >>= f).value = (f c.value).value := rfl

@[simp] lemma bind_ops (c : Counted α) (f : α → Counted β) :
    (c >>= f).ops = c.ops + (f c.value).ops := rfl

@[simp] lemma map_value (f : α → β) (c : Counted α) : (f <$> c).value = f c.value := rfl
@[simp] lemma map_ops (f : α → β) (c : Counted α) : (f <$> c).ops = c.ops := by
  simp [Functor.map, bind, ret]

/-- Charge a bundle of operations. -/
def charge (o : OpCount) : Counted Unit := ⟨(), o⟩

@[simp] lemma charge_value (o : OpCount) : (charge o).value = () := rfl
@[simp] lemma charge_ops (o : OpCount) : (charge o).ops = o := rfl

/-- The work of a run. -/
def work (c : Counted α) : Nat := c.ops.work

@[simp] lemma work_def (c : Counted α) : c.work = c.ops.work := rfl

end Counted

/-! ## Costed primitives -/

/-- One array read (out-of-range reads return a default and still cost one unit). -/
def readArr {α : Type u} [Inhabited α] (a : Array α) (i : Nat) : Counted α :=
  ⟨a.getD i default, { reads := 1 }⟩

@[simp] lemma readArr_value {α : Type u} [Inhabited α] (a : Array α) (i : Nat) :
    (readArr a i).value = a.getD i default := rfl
@[simp] lemma readArr_ops {α : Type u} [Inhabited α] (a : Array α) (i : Nat) :
    (readArr a i).ops = { reads := 1 } := rfl

/-- One array write. -/
def writeArr {α : Type u} (a : Array α) (i : Nat) (v : α) : Counted (Array α) :=
  ⟨a.setIfInBounds i v, { writes := 1 }⟩

@[simp] lemma writeArr_value {α : Type u} (a : Array α) (i : Nat) (v : α) :
    (writeArr a i v).value = a.setIfInBounds i v := rfl
@[simp] lemma writeArr_ops {α : Type u} (a : Array α) (i : Nat) (v : α) :
    (writeArr a i v).ops = { writes := 1 } := rfl

/-- One push onto a (dynamic) array; counts as a write. -/
def pushArr {α : Type u} (a : Array α) (v : α) : Counted (Array α) :=
  ⟨a.push v, { writes := 1 }⟩

@[simp] lemma pushArr_value {α : Type u} (a : Array α) (v : α) :
    (pushArr a v).value = a.push v := rfl
@[simp] lemma pushArr_ops {α : Type u} (a : Array α) (v : α) :
    (pushArr a v).ops = { writes := 1 } := rfl

/-- One arithmetic operation. -/
def arith {α : Type u} (v : α) : Counted α := ⟨v, { arithmetic := 1 }⟩

@[simp] lemma arith_value {α : Type u} (v : α) : (arith v).value = v := rfl
@[simp] lemma arith_ops {α : Type u} (v : α) : (arith v).ops = { arithmetic := 1 } := rfl

/-- One comparison.  For real inputs this is the exact-comparison oracle of the
unit-cost real-RAM model. -/
noncomputable def cmpLe (a b : ℝ) : Counted Bool :=
  ⟨decide (a ≤ b), { comparisons := 1 }⟩

@[simp] lemma cmpLe_value (a b : ℝ) : (cmpLe a b).value = decide (a ≤ b) := rfl
@[simp] lemma cmpLe_ops (a b : ℝ) : (cmpLe a b).ops = { comparisons := 1 } := rfl

/-- One comparison of natural numbers. -/
def cmpLeNat (a b : Nat) : Counted Bool := ⟨decide (a ≤ b), { comparisons := 1 }⟩

@[simp] lemma cmpLeNat_value (a b : Nat) : (cmpLeNat a b).value = decide (a ≤ b) := rfl
@[simp] lemma cmpLeNat_ops (a b : Nat) : (cmpLeNat a b).ops = { comparisons := 1 } := rfl

/-- One metric-distance query. -/
def distQuery {α : Type u} (d : α → α → ℝ) (a b : α) : Counted ℝ :=
  ⟨d a b, { distanceQueries := 1 }⟩

@[simp] lemma distQuery_value {α : Type u} (d : α → α → ℝ) (a b : α) :
    (distQuery d a b).value = d a b := rfl
@[simp] lemma distQuery_ops {α : Type u} (d : α → α → ℝ) (a b : α) :
    (distQuery d a b).ops = { distanceQueries := 1 } := rfl

/-! ## Costed loops

All loops are `List.foldlM` in the `Counted` monad; the two lemmas below turn a
per-iteration cost bound into a bound for the whole loop. -/

lemma foldlM_ops_work_le {α : Type u} {β : Type v} (f : β → α → Counted β) (C : Nat)
    (hf : ∀ b a, (f b a).ops.work ≤ C) :
    ∀ (l : List α) (b : β), ((l.foldlM f b : Counted β)).ops.work ≤ C * l.length := by
  intro l
  induction l with
  | nil => intro b; simp [List.foldlM]
  | cons a t ih =>
      intro b
      have : (List.foldlM f b (a :: t) : Counted β) = (f b a) >>= fun b' => t.foldlM f b' := by
        simp [List.foldlM]
      rw [this]
      simp only [Counted.bind_ops, OpCount.add_work]
      have h1 := hf b a
      have h2 := ih (f b a).value
      simp only [List.length_cons]
      calc (f b a).ops.work + ((t.foldlM f (f b a).value : Counted β)).ops.work
          ≤ C + C * t.length := Nat.add_le_add h1 h2
        _ = C * (t.length + 1) := by ring
  
/-- Loop cost bound when the per-iteration bound is only known for the elements of the
list being traversed. -/
lemma foldlM_ops_work_le_mem {α : Type u} {β : Type v} (f : β → α → Counted β) (C : Nat) :
    ∀ (l : List α) (b : β), (∀ b a, a ∈ l → (f b a).ops.work ≤ C) →
      ((l.foldlM f b : Counted β)).ops.work ≤ C * l.length := by
  intro l
  induction l with
  | nil => intro b _; simp [List.foldlM]
  | cons a t ih =>
      intro b hf
      have hrw : (List.foldlM f b (a :: t) : Counted β)
          = (f b a) >>= fun b' => t.foldlM f b' := by
        simp [List.foldlM]
      rw [hrw]
      simp only [Counted.bind_ops, OpCount.add_work]
      have h1 := hf b a List.mem_cons_self
      have h2 := ih (f b a).value (fun b' a' ha' => hf b' a' (List.mem_cons_of_mem _ ha'))
      simp only [List.length_cons]
      calc (f b a).ops.work + ((t.foldlM f (f b a).value : Counted β)).ops.work
          ≤ C + C * t.length := Nat.add_le_add h1 h2
        _ = C * (t.length + 1) := by ring

/-- Loop cost bound under a loop invariant. -/
lemma foldlM_ops_work_le_inv {α : Type u} {β : Type v} (f : β → α → Counted β) (P : β → Prop)
    (C : Nat) (hP : ∀ b a, P b → P (f b a).value) (hf : ∀ b a, P b → (f b a).ops.work ≤ C) :
    ∀ (l : List α) (b : β), P b → ((l.foldlM f b : Counted β)).ops.work ≤ C * l.length := by
  intro l
  induction l with
  | nil => intro b _; simp [List.foldlM]
  | cons a t ih =>
      intro b hb
      have hrw : (List.foldlM f b (a :: t) : Counted β)
          = (f b a) >>= fun b' => t.foldlM f b' := by
        simp [List.foldlM]
      rw [hrw]
      simp only [Counted.bind_ops, OpCount.add_work]
      have h1 := hf b a hb
      have h2 := ih (f b a).value (hP b a hb)
      simp only [List.length_cons]
      calc (f b a).ops.work + ((t.foldlM f (f b a).value : Counted β)).ops.work
          ≤ C + C * t.length := Nat.add_le_add h1 h2
        _ = C * (t.length + 1) := by ring

/-- `Counted` version of a `for` loop over `List.range n`. -/
def countedFor {β : Type v} (n : Nat) (b : β) (f : β → Nat → Counted β) : Counted β :=
  (List.range n).foldlM f b

lemma countedFor_work_le {β : Type v} (n : Nat) (b : β) (f : β → Nat → Counted β) (C : Nat)
    (hf : ∀ b i, (f b i).ops.work ≤ C) : (countedFor n b f).ops.work ≤ C * n := by
  have := foldlM_ops_work_le f C hf (List.range n) b
  simpa [countedFor] using this

end Q764
