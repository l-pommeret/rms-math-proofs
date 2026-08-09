/-
# Q764 — a small circuit-construction library

Circuits are built by *appending* gates to a topologically ordered list.  The three
combinators `Q764.orFold`, `Q764.andFold` and `Q764.confFold` are enough for the
verifier circuits of Stage 4; each comes with a full specification (prefix, length,
well-formedness and the Boolean value of the produced wire), so that no index
arithmetic is needed downstream.

`Q764.WFle` records that every gate argument is at most the gate's own index; it is
what turns a gate count into a bound on the serialized `Q764.Circuit.codeSize`.
-/
import RMS.Q764Complexity

namespace Q764

/-! ## Appending gates preserves the value of earlier wires -/

lemma gateValue_append (gs more : List Gate) (w : Nat → Bool) :
    ∀ i, i < gs.length → gateValue (gs ++ more) w i = gateValue gs w i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have key : ∀ a, (if a < i then gateValue (gs ++ more) w a else false)
        = (if a < i then gateValue gs w a else false) := by
      intro a
      by_cases ha : a < i
      · simp [ha, ih a ha (lt_trans ha hi)]
      · simp [ha]
    have hg : (gs ++ more)[i]? = gs[i]? := by rw [List.getElem?_append_left hi]
    rw [gateValue, gateValue, hg]
    rcases h : gs[i]? with _ | g
    · rfl
    · match g with
      | Gate.inp j => rfl
      | Gate.cst b => rfl
      | Gate.neg a =>
          simp only []
          by_cases ha : a < i
          · simp [ha, ih a ha (lt_trans ha hi)]
          · simp [ha]
      | Gate.conj a b => simp only []; rw [key a, key b]
      | Gate.disj a b => simp only []; rw [key a, key b]

lemma any_congr_of {ι : Type*} : ∀ (l : List ι) (f g : ι → Bool), (∀ x ∈ l, f x = g x) →
    l.any f = l.any g := by
  intro l
  induction l with
  | nil => intro _ _ _; rfl
  | cons a t ih =>
      intro f g h
      simp only [List.any_cons, h a List.mem_cons_self,
        ih f g (fun x hx => h x (List.mem_cons_of_mem _ hx))]

lemma all_congr_of {ι : Type*} : ∀ (l : List ι) (f g : ι → Bool), (∀ x ∈ l, f x = g x) →
    l.all f = l.all g := by
  intro l
  induction l with
  | nil => intro _ _ _; rfl
  | cons a t ih =>
      intro f g h
      simp only [List.all_cons, h a List.mem_cons_self,
        ih f g (fun x hx => h x (List.mem_cons_of_mem _ hx))]

lemma getElem?_snoc (gs : List Gate) (g : Gate) : (gs ++ [g])[gs.length]? = some g := by
  simp

lemma gateValue_snoc_disj (gs : List Gate) (a b : Nat) (ha : a < gs.length)
    (hb : b < gs.length) (v : Nat → Bool) :
    gateValue (gs ++ [Gate.disj a b]) v gs.length
      = (gateValue gs v a || gateValue gs v b) := by
  rw [gateValue_disj (getElem?_snoc gs _) ha hb, gateValue_append gs _ v a ha,
    gateValue_append gs _ v b hb]

lemma gateValue_snoc_conj (gs : List Gate) (a b : Nat) (ha : a < gs.length)
    (hb : b < gs.length) (v : Nat → Bool) :
    gateValue (gs ++ [Gate.conj a b]) v gs.length
      = (gateValue gs v a && gateValue gs v b) := by
  rw [gateValue_conj (getElem?_snoc gs _) ha hb, gateValue_append gs _ v a ha,
    gateValue_append gs _ v b hb]

lemma gateValue_snoc_neg (gs : List Gate) (a : Nat) (ha : a < gs.length) (v : Nat → Bool) :
    gateValue (gs ++ [Gate.neg a]) v gs.length = !(gateValue gs v a) := by
  rw [gateValue_neg (getElem?_snoc gs _) ha, gateValue_append gs _ v a ha]

/-! ## Well-formedness and the size bound -/

/-- The largest index occurring as an argument of a gate. -/
def argBound : Gate → Nat
  | .inp j => j
  | .cst _ => 0
  | .neg a => a
  | .conj a b => max a b
  | .disj a b => max a b

/-- Every gate argument is at most the gate's own position. -/
def WFle (gs : List Gate) : Prop := ∀ i g, gs[i]? = some g → argBound g ≤ i

lemma WFle_nil : WFle [] := by intro i g h; simp at h

lemma WFle_snoc {gs : List Gate} {g : Gate} (h : WFle gs) (hg : argBound g ≤ gs.length) :
    WFle (gs ++ [g]) := by
  intro i g' hi
  by_cases hlt : i < gs.length
  · exact h i g' (by rwa [List.getElem?_append_left hlt] at hi)
  · push_neg at hlt
    rw [List.getElem?_append_right hlt] at hi
    rcases hd : i - gs.length with _ | m
    · rw [hd] at hi
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      omega
    · rw [hd] at hi
      simp at hi

lemma WFle_mem {gs : List Gate} (h : WFle gs) {g : Gate} (hg : g ∈ gs) :
    argBound g ≤ gs.length := by
  obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hg
  exact le_trans (h i g (by rw [List.getElem?_eq_getElem hi, hgi])) (le_of_lt hi)

lemma gateCodeSize_le (g : Gate) : Circuit.gateCodeSize g ≤ 2 + 2 * argBound g := by
  have hs : ∀ m : Nat, Nat.size m ≤ m := fun m => Nat.size_le.2 (Nat.lt_two_pow_self)
  cases g with
  | inp j => have := hs j; simp only [Circuit.gateCodeSize, argBound]; omega
  | cst b => simp [Circuit.gateCodeSize, argBound]
  | neg a => have := hs a; simp only [Circuit.gateCodeSize, argBound]; omega
  | conj a b =>
      have h1 := hs a; have h2 := hs b
      have h3 : a ≤ max a b := le_max_left a b
      have h4 : b ≤ max a b := le_max_right a b
      simp only [Circuit.gateCodeSize, argBound]; omega
  | disj a b =>
      have h1 := hs a; have h2 := hs b
      have h3 : a ≤ max a b := le_max_left a b
      have h4 : b ≤ max a b := le_max_right a b
      simp only [Circuit.gateCodeSize, argBound]; omega

/-- A well-formed circuit has serialized size at most a fixed quadratic in its gate
count. -/
lemma codeSize_le_of_WFle (C : Circuit) (h : WFle C.gates) (ho : C.output ≤ C.gates.length) :
    C.codeSize ≤ 4 * (C.gates.length + 1) ^ 2 := by
  set L := C.gates.length with hL
  have hsum : (C.gates.map Circuit.gateCodeSize).sum ≤ L * (2 + 2 * L) := by
    have hb : ∀ x ∈ C.gates.map Circuit.gateCodeSize, x ≤ 2 + 2 * L := by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨g, hg, rfl⟩ := hx
      exact le_trans (gateCodeSize_le g) (by have := WFle_mem h hg; omega)
    have := List.sum_le_card_nsmul _ _ hb
    simpa [hL, smul_eq_mul] using this
  have hout : Nat.size C.output ≤ L :=
    le_trans (Nat.size_le.2 Nat.lt_two_pow_self) ho
  have : C.codeSize ≤ 1 + L + L * (2 + 2 * L) := by
    simp only [Circuit.codeSize]; omega
  nlinarith [this, sq_nonneg L]

/-! ## The base layer -/

/-- The initial gate list: one input gate per witness bit, then the constants `false`
and `true`. -/
def baseGates (m : Nat) : List Gate :=
  (List.range m).map Gate.inp ++ [Gate.cst false, Gate.cst true]

@[simp] lemma baseGates_length (m : Nat) : (baseGates m).length = m + 2 := by
  simp [baseGates]

lemma baseGates_getElem_lt {m t : Nat} (ht : t < m) :
    (baseGates m)[t]? = some (Gate.inp t) := by
  have hlen : t < ((List.range m).map Gate.inp).length := by simpa using ht
  rw [baseGates, List.getElem?_append_left hlen, List.getElem?_map,
    List.getElem?_range ht]
  rfl

lemma baseGates_inp {m t : Nat} (ht : t < m) (v : Nat → Bool) :
    gateValue (baseGates m) v t = v t :=
  gateValue_inp (baseGates_getElem_lt ht)

lemma baseGates_false (m : Nat) (v : Nat → Bool) : gateValue (baseGates m) v m = false := by
  refine gateValue_cst ?_
  have hlen : ((List.range m).map Gate.inp).length = m := by simp
  rw [baseGates, List.getElem?_append_right (by omega), hlen]
  simp

lemma baseGates_true (m : Nat) (v : Nat → Bool) :
    gateValue (baseGates m) v (m + 1) = true := by
  refine gateValue_cst ?_
  have hlen : ((List.range m).map Gate.inp).length = m := by simp
  rw [baseGates, List.getElem?_append_right (by omega), hlen]
  simp

lemma baseGates_WFle (m : Nat) : WFle (baseGates m) := by
  intro i g hi
  by_cases hlt : i < m
  · rw [baseGates_getElem_lt hlt] at hi
    simp only [Option.some.injEq] at hi
    subst hi
    simp [argBound]
  · push_neg at hlt
    have hlen : ((List.range m).map Gate.inp).length = m := by simp
    rw [baseGates, List.getElem?_append_right (by omega), hlen] at hi
    rcases hd : i - m with _ | j
    · rw [hd] at hi; simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi; simp [argBound]
    · rcases hd2 : j with _ | j2
      · rw [hd, hd2] at hi
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi; simp [argBound]
      · rw [hd, hd2] at hi; simp at hi

/-! ## The OR combinator -/

/-- Append an OR-chain over the wires `ws`, starting from the accumulator `acc`. -/
def orFold (gs : List Gate) (acc : Nat) : List Nat → (List Gate × Nat)
  | [] => (gs, acc)
  | w :: rest => orFold (gs ++ [Gate.disj acc w]) gs.length rest

lemma orFold_spec : ∀ (ws : List Nat) (gs : List Gate) (acc : Nat), acc < gs.length →
    (∀ w ∈ ws, w < gs.length) → WFle gs →
    (∃ more, (orFold gs acc ws).1 = gs ++ more) ∧
      (orFold gs acc ws).1.length = gs.length + ws.length ∧
      WFle (orFold gs acc ws).1 ∧
      (orFold gs acc ws).2 < (orFold gs acc ws).1.length ∧
      ∀ v, gateValue (orFold gs acc ws).1 v (orFold gs acc ws).2
        = (gateValue gs v acc || ws.any fun w => gateValue gs v w) := by
  intro ws
  induction ws with
  | nil =>
      intro gs acc hacc _ hwf
      refine ⟨⟨[], by simp [orFold]⟩, by simp [orFold], hwf, hacc, fun v => by
        simp [orFold]⟩
  | cons w rest ih =>
      intro gs acc hacc hws hwf
      have hw : w < gs.length := hws w List.mem_cons_self
      set gs1 := gs ++ [Gate.disj acc w] with hgs1
      have hlen1 : gs1.length = gs.length + 1 := by simp [hgs1]
      have hwf1 : WFle gs1 := WFle_snoc hwf (by simp [argBound]; omega)
      have hacc1 : gs.length < gs1.length := by omega
      have hws1 : ∀ x ∈ rest, x < gs1.length := fun x hx =>
        lt_of_lt_of_le (hws x (List.mem_cons_of_mem _ hx)) (by omega)
      obtain ⟨⟨more, hmore⟩, hlen, hwf', hlt, hval⟩ := ih gs1 gs.length hacc1 hws1 hwf1
      have hrec : orFold gs acc (w :: rest) = orFold gs1 gs.length rest := rfl
      rw [hrec]
      refine ⟨⟨Gate.disj acc w :: more, by rw [hmore, hgs1]; simp⟩, by
        rw [hlen, hlen1]; simp; omega, hwf', hlt, fun v => ?_⟩
      rw [hval v, hgs1, gateValue_snoc_disj gs acc w hacc hw v]
      rw [any_congr_of rest _ (fun w' => gateValue gs v w') (fun x hx =>
        gateValue_append gs _ v x (hws x (List.mem_cons_of_mem _ hx)))]
      simp [Bool.or_assoc]

/-! ## The conflict combinator -/

/-- Append, for each pair `(a, b)`, the gadget asserting `¬(a ∧ b)`, conjoined into the
accumulator. -/
def confFold (gs : List Gate) (acc : Nat) : List (Nat × Nat) → (List Gate × Nat)
  | [] => (gs, acc)
  | (a, b) :: rest =>
      confFold (((gs ++ [Gate.conj a b]) ++ [Gate.neg gs.length])
        ++ [Gate.conj acc (gs.length + 1)]) (gs.length + 2) rest

lemma confFold_spec : ∀ (l : List (Nat × Nat)) (gs : List Gate) (acc : Nat), acc < gs.length →
    (∀ p ∈ l, p.1 < gs.length ∧ p.2 < gs.length) → WFle gs →
    (∃ more, (confFold gs acc l).1 = gs ++ more) ∧
      (confFold gs acc l).1.length = gs.length + 3 * l.length ∧
      WFle (confFold gs acc l).1 ∧
      (confFold gs acc l).2 < (confFold gs acc l).1.length ∧
      ∀ v, gateValue (confFold gs acc l).1 v (confFold gs acc l).2
        = (gateValue gs v acc &&
            l.all fun p => !(gateValue gs v p.1 && gateValue gs v p.2)) := by
  intro l
  induction l with
  | nil =>
      intro gs acc hacc _ hwf
      exact ⟨⟨[], by simp [confFold]⟩, by simp [confFold], hwf, hacc, fun v => by
        simp [confFold]⟩
  | cons p rest ih =>
      obtain ⟨a, b⟩ := p
      intro gs acc hacc hl hwf
      obtain ⟨ha, hb⟩ := hl (a, b) List.mem_cons_self
      set g1 := gs ++ [Gate.conj a b] with hg1
      set g2 := g1 ++ [Gate.neg gs.length] with hg2
      set g3 := g2 ++ [Gate.conj acc (gs.length + 1)] with hg3
      have hl1 : g1.length = gs.length + 1 := by simp [hg1]
      have hl2 : g2.length = gs.length + 2 := by simp [hg2, hl1]
      have hl3 : g3.length = gs.length + 3 := by simp [hg3, hl2]
      have hwf1 : WFle g1 := WFle_snoc hwf (by simp [argBound]; omega)
      have hwf2 : WFle g2 := WFle_snoc hwf1 (by simp [argBound, hl1])
      have hwf3 : WFle g3 := WFle_snoc hwf2 (by simp [argBound, hl2]; omega)
      have hacc3 : gs.length + 2 < g3.length := by omega
      have hrest : ∀ q ∈ rest, q.1 < g3.length ∧ q.2 < g3.length := by
        intro q hq
        obtain ⟨h1, h2⟩ := hl q (List.mem_cons_of_mem _ hq)
        exact ⟨by omega, by omega⟩
      obtain ⟨⟨more, hmore⟩, hlen, hwf', hlt, hval⟩ :=
        ih g3 (gs.length + 2) hacc3 hrest hwf3
      have hrec : confFold gs acc ((a, b) :: rest) = confFold g3 (gs.length + 2) rest := rfl
      rw [hrec]
      -- values of the three new wires
      have e1 : ∀ v, gateValue g1 v gs.length = (gateValue gs v a && gateValue gs v b) :=
        fun v => gateValue_snoc_conj gs a b ha hb v
      have e2 : ∀ v, gateValue g2 v (gs.length + 1) = !(gateValue gs v a && gateValue gs v b) := by
        intro v
        have : gs.length + 1 = g1.length := by omega
        rw [this, hg2, gateValue_snoc_neg g1 gs.length (by omega) v, e1 v]
      have e3 : ∀ v, gateValue g3 v (gs.length + 2)
          = (gateValue gs v acc && !(gateValue gs v a && gateValue gs v b)) := by
        intro v
        have hx : gs.length + 2 = g2.length := by omega
        rw [hx, hg3, gateValue_snoc_conj g2 acc (gs.length + 1) (by omega) (by omega) v,
          e2 v, hg2, gateValue_append g1 _ v acc (by omega), hg1,
          gateValue_append gs _ v acc hacc]
      have hsub : ∀ v x, x < gs.length → gateValue g3 v x = gateValue gs v x := by
        intro v x hx
        rw [hg3, gateValue_append g2 _ v x (by omega), hg2,
          gateValue_append g1 _ v x (by omega), hg1, gateValue_append gs _ v x hx]
      refine ⟨⟨Gate.conj a b :: Gate.neg gs.length :: Gate.conj acc (gs.length + 1) :: more, by
        rw [hmore, hg3, hg2, hg1]; simp⟩, by rw [hlen, hl3]; simp; omega, hwf', hlt, fun v => ?_⟩
      rw [hval v, e3 v]
      rw [all_congr_of rest _ (fun q => !(gateValue gs v q.1 && gateValue gs v q.2))
        (fun q hq => by
          obtain ⟨h1, h2⟩ := hl q (List.mem_cons_of_mem _ hq)
          rw [hsub v q.1 h1, hsub v q.2 h2])]
      simp [Bool.and_assoc]

/-! ## The coverage combinator -/

/-- For each list of wires, append an OR over it and conjoin the result into the
accumulator.  `fW` must be a wire carrying the constant `false`. -/
def covFold (fW : Nat) (gs : List Gate) (acc : Nat) : List (List Nat) → (List Gate × Nat)
  | [] => (gs, acc)
  | ws :: rest =>
      covFold fW ((orFold gs fW ws).1 ++ [Gate.conj acc (orFold gs fW ws).2])
        (orFold gs fW ws).1.length rest

lemma covFold_spec (fW : Nat) : ∀ (l : List (List Nat)) (gs : List Gate) (acc : Nat),
    acc < gs.length → fW < gs.length → (∀ v, gateValue gs v fW = false) →
    (∀ ws ∈ l, ∀ w ∈ ws, w < gs.length) → WFle gs →
    (∃ more, (covFold fW gs acc l).1 = gs ++ more) ∧
      (covFold fW gs acc l).1.length
        = gs.length + (l.map fun ws => ws.length + 1).sum ∧
      WFle (covFold fW gs acc l).1 ∧
      (covFold fW gs acc l).2 < (covFold fW gs acc l).1.length ∧
      ∀ v, gateValue (covFold fW gs acc l).1 v (covFold fW gs acc l).2
        = (gateValue gs v acc && l.all fun ws => ws.any fun w => gateValue gs v w) := by
  intro l
  induction l with
  | nil =>
      intro gs acc hacc _ _ _ hwf
      exact ⟨⟨[], by simp [covFold]⟩, by simp [covFold], hwf, hacc, fun v => by
        simp [covFold]⟩
  | cons ws rest ih =>
      intro gs acc hacc hfW hfalse hl hwf
      have hws : ∀ w ∈ ws, w < gs.length := hl ws List.mem_cons_self
      obtain ⟨⟨m1, hm1⟩, hlenO, hwfO, hltO, hvalO⟩ := orFold_spec ws gs fW hfW hws hwf
      set p := orFold gs fW ws with hp
      set g2 := p.1 ++ [Gate.conj acc p.2] with hg2
      have hlen2 : g2.length = gs.length + ws.length + 1 := by simp [hg2, hlenO]
      have hwf2 : WFle g2 := WFle_snoc hwfO (by
        simp only [argBound]
        exact max_le (le_trans (le_of_lt hacc) (by omega)) (le_of_lt hltO))
      have hsub : ∀ v x, x < gs.length → gateValue g2 v x = gateValue gs v x := by
        intro v x hx
        rw [hg2, gateValue_append p.1 _ v x (by omega), hm1, gateValue_append gs _ v x hx]
      have hfW2 : fW < g2.length := by omega
      have hfalse2 : ∀ v, gateValue g2 v fW = false := fun v => by
        rw [hsub v fW hfW, hfalse v]
      have hrest : ∀ ws' ∈ rest, ∀ w ∈ ws', w < g2.length := by
        intro ws' hws' w hw
        exact lt_of_lt_of_le (hl ws' (List.mem_cons_of_mem _ hws') w hw) (by omega)
      have hacc2 : p.1.length < g2.length := by omega
      obtain ⟨⟨m2, hm2⟩, hlen, hwf', hlt, hval⟩ :=
        ih g2 p.1.length hacc2 hfW2 hfalse2 hrest hwf2
      have hrec : covFold fW gs acc (ws :: rest) = covFold fW g2 p.1.length rest := rfl
      rw [hrec]
      have e2 : ∀ v, gateValue g2 v p.1.length
          = (gateValue gs v acc && ws.any fun w => gateValue gs v w) := by
        intro v
        rw [hg2, gateValue_snoc_conj p.1 acc p.2 (by omega) hltO v, hvalO v, hfalse v,
          hm1, gateValue_append gs _ v acc hacc]
        simp
      refine ⟨⟨m1 ++ (Gate.conj acc p.2 :: m2), by
          rw [hm2, hg2, hm1]; simp⟩, ?_, hwf', hlt, fun v => ?_⟩
      · rw [hlen, hlen2]; simp; omega
      · rw [hval v, e2 v]
        rw [all_congr_of rest _ (fun ws' => ws'.any fun w => gateValue gs v w)
          (fun ws' hws' => any_congr_of ws' _ (fun w => gateValue gs v w)
            (fun w hw => hsub v w (hl ws' (List.mem_cons_of_mem _ hws') w hw)))]
        simp [Bool.and_assoc]

end Q764
