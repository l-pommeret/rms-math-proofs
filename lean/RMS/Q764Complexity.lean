/-
# Q764 — Stage 4: a uniform Boolean-circuit presentation of NP

Mathlib provides low-level Turing machines but no usable NP library, so the standard
*uniform circuit-verifier* presentation of NP is built here from scratch:

* `Q764.Circuit` — a topologically ordered list of gates (`inp`, `cst`, `neg`, `conj`,
  `disj`) plus an output index, with a total evaluation `Q764.Circuit.eval` and a
  serialized size `Q764.Circuit.codeSize`;
* `Q764.PolynomiallyBounded` — a polynomial bound on a cost or size function;
* `Q764.InNP` — a uniformly and polynomially constructible verifier circuit family;
* `Q764.InP` — a uniform polynomially costed decider;
* `Q764.PolyReduction` — a uniform polynomially costed many-one reduction;
* `Q764.CircuitSAT`, `Q764.NPHard`, `Q764.NPComplete`, `Q764.PEqualsNP`.

The definitions have the usual universal content: every `InNP` language reduces to
`CircuitSAT` (`Q764.inNP_polyReduces_circuitSAT`) and `CircuitSAT` itself is in NP
(`Q764.circuitSAT_inNP`), so `NPHard` is not a notion relative to one fixed problem;
`PEqualsNP` is equivalent to `CircuitSAT` having a polynomial decider
(`Q764.pEqualsNP_iff`).  Only polynomially many witness bits matter, by
`Q764.Circuit.sat_iff_exists_bits`.

All builders are computable finite data, and their cost is the one counted by
`RequestProject.Q764Cost`.
-/
import RMS.Q764Cost

namespace Q764

/-! ## Circuits -/

/-- A gate of a Boolean circuit.  Arguments are indices of *earlier* gates. -/
inductive Gate where
  | inp (i : Nat)
  | cst (b : Bool)
  | neg (a : Nat)
  | conj (a b : Nat)
  | disj (a b : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A circuit: a topologically ordered list of gates and an output index. -/
structure Circuit where
  gates : List Gate
  output : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Value of gate `i` on witness `w`.  Out-of-range indices and forward references
evaluate to `false`, so evaluation is total on arbitrary finite data. -/
def gateValue (gates : List Gate) (w : Nat → Bool) : Nat → Bool
  | i =>
    match gates[i]? with
    | none => false
    | some (.inp j) => w j
    | some (.cst b) => b
    | some (.neg a) => if a < i then !(gateValue gates w a) else false
    | some (.conj a b) =>
        (if a < i then gateValue gates w a else false) &&
          (if b < i then gateValue gates w b else false)
    | some (.disj a b) =>
        (if a < i then gateValue gates w a else false) ||
          (if b < i then gateValue gates w b else false)
  termination_by i => i

lemma gateValue_none {gates : List Gate} {w : Nat → Bool} {i : Nat}
    (h : gates[i]? = none) : gateValue gates w i = false := by
  rw [gateValue]; simp [h]

lemma gateValue_inp {gates : List Gate} {w : Nat → Bool} {i j : Nat}
    (h : gates[i]? = some (.inp j)) : gateValue gates w i = w j := by
  rw [gateValue]; simp [h]

lemma gateValue_cst {gates : List Gate} {w : Nat → Bool} {i : Nat} {b : Bool}
    (h : gates[i]? = some (.cst b)) : gateValue gates w i = b := by
  rw [gateValue]; simp [h]

lemma gateValue_neg {gates : List Gate} {w : Nat → Bool} {i a : Nat}
    (h : gates[i]? = some (.neg a)) (ha : a < i) :
    gateValue gates w i = !(gateValue gates w a) := by
  rw [gateValue]; simp [h, ha]

lemma gateValue_conj {gates : List Gate} {w : Nat → Bool} {i a b : Nat}
    (h : gates[i]? = some (.conj a b)) (ha : a < i) (hb : b < i) :
    gateValue gates w i = (gateValue gates w a && gateValue gates w b) := by
  rw [gateValue]; simp [h, ha, hb]

lemma gateValue_disj {gates : List Gate} {w : Nat → Bool} {i a b : Nat}
    (h : gates[i]? = some (.disj a b)) (ha : a < i) (hb : b < i) :
    gateValue gates w i = (gateValue gates w a || gateValue gates w b) := by
  rw [gateValue]; simp [h, ha, hb]

namespace Circuit

/-- Evaluation of a circuit on a witness. -/
def eval (C : Circuit) (w : Nat → Bool) : Bool := gateValue C.gates w C.output

/-- Number of gates. -/
def numGates (C : Circuit) : Nat := C.gates.length

/-- The list of witness positions read by the circuit. -/
def inputPositions (C : Circuit) : List Nat :=
  C.gates.filterMap fun g => match g with | .inp i => some i | _ => none

lemma inputPositions_length_le (C : Circuit) : C.inputPositions.length ≤ C.numGates :=
  le_trans (List.length_filterMap_le _ _) (le_of_eq rfl)

lemma mem_inputPositions {C : Circuit} {i j : Nat} (h : C.gates[i]? = some (.inp j)) :
    j ∈ C.inputPositions := by
  have hmem : Gate.inp j ∈ C.gates := List.mem_of_getElem? h
  simp only [inputPositions, List.mem_filterMap]
  exact ⟨Gate.inp j, hmem, rfl⟩

/-- Number of serialized symbols of a gate (opcode plus the bit lengths of its
arguments). -/
def gateCodeSize : Gate → Nat
  | .inp i => 2 + Nat.size i
  | .cst _ => 2
  | .neg a => 2 + Nat.size a
  | .conj a b => 2 + Nat.size a + Nat.size b
  | .disj a b => 2 + Nat.size a + Nat.size b

/-- Serialized size of the circuit code. -/
def codeSize (C : Circuit) : Nat := 1 + Nat.size C.output + (C.gates.map gateCodeSize).sum

lemma two_mul_numGates_le_codeSize (C : Circuit) : 2 * C.numGates ≤ C.codeSize := by
  have h : ∀ l : List Gate, 2 * l.length ≤ (l.map gateCodeSize).sum := by
    intro l
    induction l with
    | nil => simp
    | cons g t ih =>
        have hg : 2 ≤ gateCodeSize g := by cases g <;> (simp only [gateCodeSize]; omega)
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
  have := h C.gates
  simp only [codeSize, numGates]
  omega

lemma numGates_le_codeSize (C : Circuit) : C.numGates ≤ C.codeSize := by
  have := two_mul_numGates_le_codeSize C; omega

/-- Only the witness bits at the positions actually read matter. -/
lemma gateValue_congr (gates : List Gate) (w₁ w₂ : Nat → Bool)
    (hw : ∀ i j : Nat, gates[i]? = some (Gate.inp j) → w₁ j = w₂ j) :
    ∀ i, gateValue gates w₁ i = gateValue gates w₂ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have key : ∀ a, (if a < i then gateValue gates w₁ a else false)
        = (if a < i then gateValue gates w₂ a else false) := by
      intro a; by_cases ha : a < i <;> simp [ha, ih a]
    rcases hg : gates[i]? with _ | g
    · rw [gateValue_none hg, gateValue_none hg]
    · match g, hg with
      | Gate.inp j, hg => rw [gateValue_inp hg, gateValue_inp hg]; exact hw i j hg
      | Gate.cst b, hg => rw [gateValue_cst hg, gateValue_cst hg]
      | Gate.neg a, hg =>
          rw [gateValue, gateValue]
          simp only [hg]
          by_cases ha : a < i <;> simp [ha, ih a]
      | Gate.conj a b, hg =>
          rw [gateValue, gateValue]
          simp only [hg]
          rw [key a, key b]
      | Gate.disj a b, hg =>
          rw [gateValue, gateValue]
          simp only [hg]
          rw [key a, key b]

lemma eval_congr (C : Circuit) (w₁ w₂ : Nat → Bool)
    (hw : ∀ j ∈ C.inputPositions, w₁ j = w₂ j) : C.eval w₁ = C.eval w₂ :=
  gateValue_congr C.gates w₁ w₂ (fun i j h => hw j (mem_inputPositions h)) C.output

/-- Spreading a finite list of bits over the positions `ps`. -/
def spread (ps : List Nat) (b : List Bool) : Nat → Bool := fun j => b.getD (ps.idxOf j) false

/-- **Polynomially many witness bits suffice**: a circuit is satisfiable iff it is
satisfied by an assignment described by `C.inputPositions.length ≤ C.numGates` bits. -/
theorem sat_iff_exists_bits (C : Circuit) :
    (∃ w : Nat → Bool, C.eval w = true) ↔
      ∃ b : List Bool, b.length = C.inputPositions.length ∧
        C.eval (spread C.inputPositions b) = true := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨C.inputPositions.map w, by simp, ?_⟩
    rw [eval_congr C _ w ?_]
    · exact hw
    · intro j hj
      have hidx : C.inputPositions.idxOf j < C.inputPositions.length := List.idxOf_lt_length_of_mem hj
      have hget : C.inputPositions[C.inputPositions.idxOf j]! = j := by
        have := List.getElem_idxOf hidx
        simpa [getElem!_pos, hidx] using this
      simp only [spread]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map]
      have : C.inputPositions[C.inputPositions.idxOf j]? = some j := by
        rw [List.getElem?_eq_getElem hidx]
        congr 1
        simpa [getElem!_pos, hidx] using hget
      rw [this]
      rfl
  · rintro ⟨b, -, hb⟩; exact ⟨_, hb⟩

end Circuit

/-! ## Polynomial bounds -/

/-- `f` is polynomially bounded in the input size. -/
def PolynomiallyBounded {α : Type} (f : α → Nat) (size : α → Nat) : Prop :=
  ∃ C e : Nat, ∀ x, f x ≤ C * (size x + 1) ^ e

lemma PolynomiallyBounded.mono {α : Type} {f g : α → Nat} {size : α → Nat}
    (hf : PolynomiallyBounded f size) (hg : ∀ x, g x ≤ f x) : PolynomiallyBounded g size := by
  obtain ⟨C, e, h⟩ := hf
  exact ⟨C, e, fun x => le_trans (hg x) (h x)⟩

lemma PolynomiallyBounded.add {α : Type} {f g : α → Nat} {size : α → Nat}
    (hf : PolynomiallyBounded f size) (hg : PolynomiallyBounded g size) :
    PolynomiallyBounded (fun x => f x + g x) size := by
  obtain ⟨C₁, e₁, h₁⟩ := hf
  obtain ⟨C₂, e₂, h₂⟩ := hg
  refine ⟨C₁ + C₂, max e₁ e₂, fun x => ?_⟩
  have hs : 1 ≤ size x + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have p₁ : (size x + 1) ^ e₁ ≤ (size x + 1) ^ max e₁ e₂ :=
    Nat.pow_le_pow_right hs (le_max_left _ _)
  have p₂ : (size x + 1) ^ e₂ ≤ (size x + 1) ^ max e₁ e₂ :=
    Nat.pow_le_pow_right hs (le_max_right _ _)
  calc f x + g x ≤ C₁ * (size x + 1) ^ e₁ + C₂ * (size x + 1) ^ e₂ :=
        Nat.add_le_add (h₁ x) (h₂ x)
    _ ≤ C₁ * (size x + 1) ^ max e₁ e₂ + C₂ * (size x + 1) ^ max e₁ e₂ :=
        Nat.add_le_add (Nat.mul_le_mul_left _ p₁) (Nat.mul_le_mul_left _ p₂)
    _ = (C₁ + C₂) * (size x + 1) ^ max e₁ e₂ := by ring

lemma PolynomiallyBounded.const {α : Type} (c : Nat) (size : α → Nat) :
    PolynomiallyBounded (fun _ => c) size :=
  ⟨c, 0, fun x => by simp⟩

lemma PolynomiallyBounded.self {α : Type} (size : α → Nat) :
    PolynomiallyBounded size size :=
  ⟨1, 1, fun x => by simp⟩

lemma PolynomiallyBounded.mul {α : Type} {f g : α → Nat} {size : α → Nat}
    (hf : PolynomiallyBounded f size) (hg : PolynomiallyBounded g size) :
    PolynomiallyBounded (fun x => f x * g x) size := by
  obtain ⟨C₁, e₁, h₁⟩ := hf
  obtain ⟨C₂, e₂, h₂⟩ := hg
  refine ⟨C₁ * C₂, e₁ + e₂, fun x => ?_⟩
  calc f x * g x ≤ (C₁ * (size x + 1) ^ e₁) * (C₂ * (size x + 1) ^ e₂) :=
        Nat.mul_le_mul (h₁ x) (h₂ x)
    _ = C₁ * C₂ * (size x + 1) ^ (e₁ + e₂) := by rw [pow_add]; ring

/-- Composition of polynomial bounds. -/
lemma PolynomiallyBounded.comp {α β : Type} {sizeA : α → Nat} {sizeB : β → Nat}
    {g : β → Nat} {u : α → β} (hg : PolynomiallyBounded g sizeB)
    (hu : PolynomiallyBounded (fun x => sizeB (u x)) sizeA) :
    PolynomiallyBounded (fun x => g (u x)) sizeA := by
  obtain ⟨C₁, e₁, h₁⟩ := hg
  obtain ⟨C₂, e₂, h₂⟩ := hu
  refine ⟨C₁ * (C₂ + 1) ^ e₁, e₂ * e₁, fun x => ?_⟩
  have hs : 1 ≤ (sizeA x + 1) ^ e₂ := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hstep : sizeB (u x) + 1 ≤ (C₂ + 1) * (sizeA x + 1) ^ e₂ := by
    have : sizeB (u x) ≤ C₂ * (sizeA x + 1) ^ e₂ := h₂ x
    calc sizeB (u x) + 1 ≤ C₂ * (sizeA x + 1) ^ e₂ + 1 := by omega
      _ ≤ C₂ * (sizeA x + 1) ^ e₂ + (sizeA x + 1) ^ e₂ := by omega
      _ = (C₂ + 1) * (sizeA x + 1) ^ e₂ := by ring
  calc g (u x) ≤ C₁ * (sizeB (u x) + 1) ^ e₁ := h₁ (u x)
    _ ≤ C₁ * ((C₂ + 1) * (sizeA x + 1) ^ e₂) ^ e₁ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hstep _)
    _ = C₁ * (C₂ + 1) ^ e₁ * (sizeA x + 1) ^ (e₂ * e₁) := by
        rw [Nat.mul_pow, ← pow_mul]; ring

/-! ## NP, P, reductions -/

/-- Circuit satisfiability, the canonical NP-complete problem. -/
def CircuitSAT (C : Circuit) : Prop := ∃ w : Nat → Bool, C.eval w = true

/-- `L` is in NP: there is a uniformly and polynomially constructible family of verifier
circuits `V x`, of polynomial size (hence with polynomially many relevant witness bits,
by `Q764.Circuit.sat_iff_exists_bits`), such that `L x` holds iff `V x` is satisfiable. -/
def InNP {α : Type} (size : α → Nat) (L : α → Prop) : Prop :=
  ∃ V : α → Counted Circuit,
    PolynomiallyBounded (fun x => (V x).ops.work) size ∧
    PolynomiallyBounded (fun x => (V x).value.codeSize) size ∧
    (∀ x, L x ↔ CircuitSAT (V x).value)

/-- The number of witness bits of the verifier of an `InNP` language is polynomially
bounded. -/
theorem InNP.witness_bits_polynomial {α : Type} {size : α → Nat} {L : α → Prop}
    (h : InNP size L) :
    ∃ V : α → Counted Circuit,
      PolynomiallyBounded (fun x => (V x).value.inputPositions.length) size ∧
      (∀ x, L x ↔ ∃ b : List Bool, b.length = (V x).value.inputPositions.length ∧
        (V x).value.eval (Circuit.spread (V x).value.inputPositions b) = true) := by
  obtain ⟨V, -, hsize, hspec⟩ := h
  refine ⟨V, hsize.mono fun x => ?_, fun x => (hspec x).trans (Circuit.sat_iff_exists_bits _)⟩
  exact le_trans (Circuit.inputPositions_length_le _) (Circuit.numGates_le_codeSize _)

/-- `L` is in P: a uniform decider of polynomial cost. -/
def InP {α : Type} (size : α → Nat) (L : α → Prop) : Prop :=
  ∃ D : α → Counted Bool,
    PolynomiallyBounded (fun x => (D x).ops.work) size ∧
    (∀ x, (D x).value = true ↔ L x)

/-- A polynomially costed uniform many-one reduction from `L` to `M`. -/
def PolyReduction {α β : Type} (sizeA : α → Nat) (sizeB : β → Nat)
    (L : α → Prop) (M : β → Prop) : Prop :=
  ∃ f : α → Counted β,
    PolynomiallyBounded (fun x => (f x).ops.work) sizeA ∧
    PolynomiallyBounded (fun x => sizeB (f x).value) sizeA ∧
    (∀ x, L x ↔ M (f x).value)

/-- `L` is NP-hard: `CircuitSAT` reduces to it.  By `Q764.inNP_polyReduces_circuitSAT`
this implies that *every* language of NP reduces to `L`. -/
def NPHard {β : Type} (sizeB : β → Nat) (M : β → Prop) : Prop :=
  PolyReduction Circuit.codeSize sizeB CircuitSAT M

/-- NP-completeness. -/
def NPComplete {β : Type} (sizeB : β → Nat) (M : β → Prop) : Prop :=
  InNP sizeB M ∧ NPHard sizeB M

/-- `P = NP`, internally to the present uniform circuit model. -/
def PEqualsNP : Prop :=
  ∀ (α : Type) (size : α → Nat) (L : α → Prop), InNP size L → InP size L

/-! ## Closure properties -/

/-- Copying a circuit, at unit cost per gate. -/
def copyCircuit (C : Circuit) : Counted Circuit :=
  ⟨C, { reads := C.gates.length, writes := C.gates.length }⟩

@[simp] lemma copyCircuit_value (C : Circuit) : (copyCircuit C).value = C := rfl

lemma copyCircuit_work (C : Circuit) : (copyCircuit C).ops.work = 2 * C.gates.length := by
  simp [copyCircuit, OpCount.work]; omega

/-- **CircuitSAT is in NP**. -/
theorem circuitSAT_inNP : InNP Circuit.codeSize CircuitSAT := by
  refine ⟨copyCircuit, ?_, ?_, fun C => Iff.rfl⟩
  · refine ⟨1, 1, fun C => ?_⟩
    show (copyCircuit C).ops.work ≤ _
    rw [copyCircuit_work]
    have := Circuit.two_mul_numGates_le_codeSize C
    simp only [Circuit.numGates] at this
    calc 2 * C.gates.length ≤ C.codeSize := this
      _ ≤ 1 * (C.codeSize + 1) ^ 1 := by simp
  · exact ⟨1, 1, fun C => by simp⟩

/-- **Every language in NP reduces to CircuitSAT**: emit the verifier circuit. -/
theorem inNP_polyReduces_circuitSAT {α : Type} {size : α → Nat} {L : α → Prop}
    (h : InNP size L) : PolyReduction size Circuit.codeSize L CircuitSAT := by
  obtain ⟨V, hwork, hsize, hspec⟩ := h
  exact ⟨V, hwork, hsize, hspec⟩

/-- Composition of reductions. -/
theorem PolyReduction.trans {α β γ : Type} {sizeA : α → Nat} {sizeB : β → Nat}
    {sizeC : γ → Nat} {L : α → Prop} {M : β → Prop} {N : γ → Prop}
    (h₁ : PolyReduction sizeA sizeB L M) (h₂ : PolyReduction sizeB sizeC M N) :
    PolyReduction sizeA sizeC L N := by
  obtain ⟨f, hfw, hfs, hfc⟩ := h₁
  obtain ⟨g, hgw, hgs, hgc⟩ := h₂
  refine ⟨fun x => f x >>= g, ?_, ?_, fun x => (hfc x).trans (hgc _)⟩
  · have h1 : PolynomiallyBounded (fun x => (g (f x).value).ops.work) sizeA :=
      hgw.comp hfs
    have := hfw.add h1
    exact this.mono fun x => by simp
  · exact hgs.comp hfs

/-- A polynomial reduction transports membership in P backwards. -/
theorem InP.of_polyReduction {α β : Type} {sizeA : α → Nat} {sizeB : β → Nat}
    {L : α → Prop} {M : β → Prop} (hred : PolyReduction sizeA sizeB L M)
    (hM : InP sizeB M) : InP sizeA L := by
  obtain ⟨f, hfw, hfs, hfc⟩ := hred
  obtain ⟨D, hDw, hDc⟩ := hM
  refine ⟨fun x => f x >>= D, ?_, fun x => ?_⟩
  · have h1 : PolynomiallyBounded (fun x => (D (f x).value).ops.work) sizeA := hDw.comp hfs
    exact (hfw.add h1).mono fun x => by simp
  · simpa using (hDc (f x).value).trans (hfc x).symm

/-- **`P = NP` is equivalent to `CircuitSAT ∈ P`**, internally to this model. -/
theorem pEqualsNP_iff : PEqualsNP ↔ InP Circuit.codeSize CircuitSAT := by
  constructor
  · intro h
    exact h Circuit Circuit.codeSize CircuitSAT circuitSAT_inNP
  · intro h α size L hL
    exact InP.of_polyReduction (inNP_polyReduces_circuitSAT hL) h

end Q764
