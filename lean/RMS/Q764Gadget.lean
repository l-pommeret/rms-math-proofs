/-
# Q764 — Stage 5b: from Vertex Cover to domination in a `1`–`2` metric

From a graph `G = (V,E)` we build the graph `H` on the vertex set `V ⊎ (V × V)` in which

* the `V`-vertices form a clique;
* the pair vertex `(a,b)` with `a < b` and `a—b ∈ E` is adjacent to exactly `a` and `b`;
* every other pair vertex is adjacent to all of `V`;
* distinct pair vertices are never adjacent.

The `1`–`2` distance table of `H` then has covering radius `≤ 1` for a set `S` exactly when
`S` dominates `H` (`Q764.oneTwoDist_le_one_iff_dominating`), and `H` has a dominating set of
size at most `k` exactly when `G` has a vertex cover of size at most `k`.

Degenerate instances (`k = 0`, `k ≥ n`, invalid codes) are normalized to fixed yes/no
instances so that the produced instance always satisfies the `1 ≤ k ≤ n` input convention.
-/
import RMS.Q764Codes
import RMS.Q764Complexity

namespace Q764

lemma natSize_le_self (m : Nat) : Nat.size m ≤ m := Nat.size_le.2 Nat.lt_two_pow_self

/-! ## Flat square tables -/

/-- A flat `N*N` Boolean table. -/
def flatTable (N : Nat) (f : Nat → Nat → Bool) : List Bool :=
  (List.range (N * N)).map (fun t => f (t / N) (t % N))

@[simp] lemma flatTable_length (N : Nat) (f : Nat → Nat → Bool) :
    (flatTable N f).length = N * N := by simp [flatTable]

lemma flatTable_getD {N : Nat} (f : Nat → Nat → Bool) {u v : Nat} (hu : u < N) (hv : v < N) :
    (flatTable N f).getD (u * N + v) false = f u v := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hv
  have hlt : u * N + v < N * N := by
    calc u * N + v < u * N + N := by omega
      _ = (u + 1) * N := by ring
      _ ≤ N * N := Nat.mul_le_mul_right N hu
  rw [List.getD_eq_getElem _ _ (by simpa [flatTable] using hlt)]
  simp only [flatTable, List.getElem_map, List.getElem_range]
  have hcomm : u * N + v = v + N * u := by ring
  rw [hcomm, Nat.add_mul_div_left v u hN, Nat.div_eq_of_lt hv, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]

/-! ## Fixed yes/no instances -/

/-- A fixed instance which is *not* a yes-instance of `Q764.OneTwoKCenterYes`: two
isolated vertices and one centre. -/
def noCode : GraphCode := ⟨2, flatTable 2 (fun _ _ => false), 1⟩

/-- A fixed yes-instance of `Q764.OneTwoKCenterYes`: a single vertex and one centre. -/
def yesCode : GraphCode := ⟨1, flatTable 1 (fun _ _ => false), 1⟩

lemma valid_of_edge_false {G : GraphCode} (hlen : G.adj.length = G.n * G.n)
    (h : ∀ i < G.n, ∀ j < G.n, G.edge i j = false) : G.valid = true := by
  simp only [GraphCode.valid, Bool.and_eq_true, allB_eq_true, beq_iff_eq, Bool.not_eq_true',
    hlen, true_and]
  intro i hi j hj
  rw [h i hi j hj, h j hj i hi, h i hi i hi]
  simp

lemma noCode_edge {i j : Nat} (hi : i < 2) (hj : j < 2) : noCode.edge i j = false := by
  show (flatTable 2 (fun _ _ => false)).getD (i * 2 + j) false = false
  exact flatTable_getD _ hi hj

lemma yesCode_edge {i j : Nat} (hi : i < 1) (hj : j < 1) : yesCode.edge i j = false := by
  show (flatTable 1 (fun _ _ => false)).getD (i * 1 + j) false = false
  exact flatTable_getD _ hi hj

lemma noCode_valid : noCode.valid = true :=
  valid_of_edge_false
    (by show (flatTable 2 (fun _ _ => false)).length = 2 * 2; simp)
    (fun i hi j hj => noCode_edge hi hj)

lemma yesCode_valid : yesCode.valid = true :=
  valid_of_edge_false
    (by show (flatTable 1 (fun _ _ => false)).length = 1 * 1; simp)
    (fun i hi j hj => yesCode_edge hi hj)

lemma yesCode_yes : OneTwoKCenterYes yesCode := by
  have hn : (0 : Nat) < yesCode.n := Nat.zero_lt_one
  refine ⟨yesCode_valid, ?_, ?_,
    {(⟨0, hn⟩ : Fin yesCode.n)}, ?_, ⟨⟨0, hn⟩, Finset.mem_singleton_self _⟩, ?_⟩
  · show 1 ≤ 1
    exact Nat.le_refl 1
  · show (1 : Nat) ≤ 1
    exact Nat.le_refl 1
  · rw [Finset.card_singleton]
    show 1 ≤ 1
    exact Nat.le_refl 1
  · intro i
    refine ⟨⟨0, hn⟩, Finset.mem_singleton_self _, Or.inl ?_⟩
    have h : (i : Nat) < 1 := i.isLt
    show (i : Nat) = 0
    omega

lemma noCode_not_yes : ¬ OneTwoKCenterYes noCode := by
  rintro ⟨-, -, -, S, hcard, -, hdom⟩
  have hn : noCode.n = 2 := rfl
  have key : ∀ i : Fin noCode.n, i ∈ S := by
    intro i
    obtain ⟨s, hs, hcase⟩ := hdom i
    rcases hcase with h | h
    · rwa [Fin.ext h]
    · rw [noCode_edge (by simpa [hn] using i.isLt) (by simpa [hn] using s.isLt)] at h
      exact absurd h (by simp)
  have : (Finset.univ : Finset (Fin noCode.n)) ⊆ S := fun i _ => key i
  have hle : (Finset.univ : Finset (Fin noCode.n)).card ≤ S.card := Finset.card_le_card this
  simp only [Finset.card_univ, Fintype.card_fin, hn] at hle
  have : noCode.k = 1 := rfl
  omega

/-! ## The domination gadget -/

namespace GraphCode

/-- Number of vertices of the gadget: the original vertices plus one vertex per ordered
pair of vertices. -/
def hSize (G : GraphCode) : Nat := G.n + G.n * G.n

/-- The pair slot `(a,b)` carries a genuine edge of `G`, listed once (`a < b`). -/
def isEdgePair (G : GraphCode) (a b : Nat) : Bool := decide (a < b) && G.edge a b

/-- Adjacency of the gadget. -/
def hEntry (G : GraphCode) (u v : Nat) : Bool :=
  if u < G.n then
    if v < G.n then decide (u ≠ v)
    else
      if isEdgePair G ((v - G.n) / G.n) ((v - G.n) % G.n) then
        decide (u = (v - G.n) / G.n ∨ u = (v - G.n) % G.n)
      else true
  else
    if v < G.n then
      if isEdgePair G ((u - G.n) / G.n) ((u - G.n) % G.n) then
        decide (v = (u - G.n) / G.n ∨ v = (u - G.n) % G.n)
      else true
    else false

/-- The gadget graph, with the same parameter `k`. -/
def toH (G : GraphCode) : GraphCode := ⟨G.hSize, flatTable G.hSize (hEntry G), G.k⟩

@[simp] lemma toH_n (G : GraphCode) : G.toH.n = G.hSize := rfl
@[simp] lemma toH_k (G : GraphCode) : G.toH.k = G.k := rfl

lemma toH_edge {G : GraphCode} {u v : Nat} (hu : u < G.hSize) (hv : v < G.hSize) :
    G.toH.edge u v = hEntry G u v :=
  flatTable_getD _ hu hv

lemma hEntry_symm (G : GraphCode) (u v : Nat) : hEntry G u v = hEntry G v u := by
  by_cases hu : u < G.n <;> by_cases hv : v < G.n
  · simp only [hEntry, if_pos hu, if_pos hv]
    simp [ne_comm]
  · simp only [hEntry, if_pos hu, if_neg hv]
  · simp only [hEntry, if_pos hv, if_neg hu]
  · simp only [hEntry, if_neg hu, if_neg hv]

lemma hEntry_irrefl (G : GraphCode) (u : Nat) : hEntry G u u = false := by
  unfold hEntry
  by_cases hu : u < G.n <;> simp [hu]

lemma toH_valid (G : GraphCode) : G.toH.valid = true := by
  simp only [GraphCode.valid, Bool.and_eq_true, allB_eq_true, beq_iff_eq, Bool.not_eq_true']
  refine ⟨by simp [toH], fun i hi j hj => ?_⟩
  simp only [toH_n] at hi hj
  rw [toH_edge hi hj, toH_edge hj hi, toH_edge hi hi, hEntry_irrefl, hEntry_symm]
  simp

end GraphCode

section Gadget

variable {G : GraphCode}

/-- The `V`-part of the gadget. -/
def emb (G : GraphCode) (i : Fin G.n) : Fin G.toH.n :=
  ⟨i, lt_of_lt_of_le i.isLt (by simp [GraphCode.hSize])⟩

@[simp] lemma emb_val (G : GraphCode) (i : Fin G.n) : ((emb G i : Fin G.toH.n) : Nat) = i := rfl

lemma emb_injective (G : GraphCode) : Function.Injective (emb G) := by
  intro a b h
  exact Fin.ext (by simpa [emb] using congrArg Fin.val h)

/-- Projection of a gadget vertex to an original vertex: a `V`-vertex is kept, a pair
vertex is replaced by (the first component of) its slot. -/
def proj (G : GraphCode) (hn : 0 < G.n) (u : Fin G.toH.n) : Fin G.n :=
  if h : (u : Nat) < G.n then ⟨u, h⟩
  else ⟨(((u : Nat) - G.n) / G.n) % G.n, Nat.mod_lt _ hn⟩

lemma proj_emb (hn : 0 < G.n) (i : Fin G.n) : proj G hn (emb G i) = i := by
  simp [proj, emb, i.isLt]

/-- **Forward direction**: a nonempty vertex cover of `G` dominates the gadget. -/
theorem toH_dominating_of_vertexCover {W : Finset (Fin G.n)} (hW : G.IsVertexCover W)
    (hne : W.Nonempty) : G.toH.IsDominating (W.image (emb G)) := by
  obtain ⟨w0, hw0⟩ := hne
  intro i
  have hiN : (i : Nat) < G.hSize := by simpa using i.isLt
  by_cases hi : (i : Nat) < G.n
  · refine ⟨emb G w0, Finset.mem_image_of_mem _ hw0, ?_⟩
    by_cases heq : (i : Nat) = (w0 : Nat)
    · exact Or.inl heq
    · right
      rw [GraphCode.toH_edge hiN (by simpa using (emb G w0).isLt)]
      simp only [GraphCode.hEntry, emb_val, if_pos hi, if_pos w0.isLt]
      simpa using heq
  · have hn : 0 < G.n := by
      rcases Nat.eq_zero_or_pos G.n with h0 | h0
      · exfalso; rw [GraphCode.hSize, h0] at hiN; simp at hiN
      · exact h0
    have htlt : (i : Nat) - G.n < G.n * G.n := by
      simp only [GraphCode.hSize] at hiN; omega
    have ha : ((i : Nat) - G.n) / G.n < G.n := Nat.div_lt_of_lt_mul htlt
    have hb : ((i : Nat) - G.n) % G.n < G.n := Nat.mod_lt _ hn
    by_cases hpair : GraphCode.isEdgePair G (((i : Nat) - G.n) / G.n) (((i : Nat) - G.n) % G.n) = true
    · have hpair' := hpair
      simp only [GraphCode.isEdgePair, Bool.and_eq_true, decide_eq_true_eq] at hpair'
      have hcover := hW ⟨((i : Nat) - G.n) / G.n, ha⟩ ⟨((i : Nat) - G.n) % G.n, hb⟩ hpair'.2
      rcases hcover with hmem | hmem
      · refine ⟨emb G ⟨((i : Nat) - G.n) / G.n, ha⟩, Finset.mem_image_of_mem _ hmem, Or.inr ?_⟩
        rw [GraphCode.toH_edge hiN (by simpa using (emb G ⟨((i : Nat) - G.n) / G.n, ha⟩).isLt)]
        simp only [GraphCode.hEntry, emb_val, if_neg hi, if_pos ha, if_pos hpair]
        simp
      · refine ⟨emb G ⟨((i : Nat) - G.n) % G.n, hb⟩, Finset.mem_image_of_mem _ hmem, Or.inr ?_⟩
        rw [GraphCode.toH_edge hiN (by simpa using (emb G ⟨((i : Nat) - G.n) % G.n, hb⟩).isLt)]
        simp only [GraphCode.hEntry, emb_val, if_neg hi, if_pos hb, if_pos hpair]
        simp
    · refine ⟨emb G w0, Finset.mem_image_of_mem _ hw0, Or.inr ?_⟩
      rw [GraphCode.toH_edge hiN (by simpa using (emb G w0).isLt)]
      simp only [GraphCode.hEntry, emb_val, if_neg hi, if_pos w0.isLt, if_neg hpair]

/-- **Backward direction**: projecting a dominating set of the gadget gives a vertex cover
of `G` of no larger size. -/
theorem vertexCover_of_toH_dominating (hval : G.valid = true) (hn : 0 < G.n)
    {T : Finset (Fin G.toH.n)} (hT : G.toH.IsDominating T) :
    G.IsVertexCover (T.image (proj G hn)) := by
  have main : ∀ a b : Fin G.n, (a : Nat) < (b : Nat) → G.edge a b = true →
      (a ∈ T.image (proj G hn) ∨ b ∈ T.image (proj G hn)) := by
    intro a b hab hedge
    have htlt : (a : Nat) * G.n + (b : Nat) < G.n * G.n := by
      have h1 : ((a : Nat) + 1) * G.n ≤ G.n * G.n := by
        have := Nat.mul_le_mul_right G.n (Nat.succ_le_of_lt a.isLt)
        simpa using this
      have h2 : (a : Nat) * G.n + G.n = ((a : Nat) + 1) * G.n := by ring
      have hb := b.isLt
      omega
    have hdiv : ((a : Nat) * G.n + (b : Nat)) / G.n = (a : Nat) := by
      have h : (a : Nat) * G.n + (b : Nat) = (b : Nat) + G.n * (a : Nat) := by ring
      rw [h, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt b.isLt, Nat.zero_add]
    have hmod : ((a : Nat) * G.n + (b : Nat)) % G.n = (b : Nat) := by
      have h : (a : Nat) * G.n + (b : Nat) = (b : Nat) + G.n * (a : Nat) := by ring
      rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
    have hpvlt : G.n + ((a : Nat) * G.n + (b : Nat)) < G.hSize := by
      simp only [GraphCode.hSize]; omega
    set p : Fin G.toH.n := ⟨G.n + ((a : Nat) * G.n + (b : Nat)), by simpa using hpvlt⟩ with hp
    have hpge : ¬ ((p : Nat) < G.n) := by simp [hp]
    have hpsub : (p : Nat) - G.n = (a : Nat) * G.n + (b : Nat) := by simp [hp]
    have hpair : GraphCode.isEdgePair G (a : Nat) (b : Nat) = true := by
      simp [GraphCode.isEdgePair, hab, hedge]
    obtain ⟨s, hs, hcase⟩ := hT p
    rcases hcase with heq | hedg
    · left
      have hsval : (s : Nat) = G.n + ((a : Nat) * G.n + (b : Nat)) := by rw [← heq, hp]
      have hsn : ¬ ((s : Nat) < G.n) := by omega
      have hprj : proj G hn s = a := by
        apply Fin.ext
        simp only [proj, dif_neg hsn]
        rw [hsval]
        simp only [Nat.add_sub_cancel_left]
        rw [hdiv, Nat.mod_eq_of_lt a.isLt]
      rw [← hprj]
      exact Finset.mem_image_of_mem _ hs
    · have hsn : (s : Nat) < G.n := by
        by_contra hsn
        rw [GraphCode.toH_edge (by simpa using p.isLt) (by simpa using s.isLt)] at hedg
        simp only [GraphCode.hEntry, if_neg hpge, if_neg hsn] at hedg
        exact absurd hedg (by simp)
      rw [GraphCode.toH_edge (by simpa using p.isLt) (by simpa using s.isLt)] at hedg
      simp only [GraphCode.hEntry, if_neg hpge, if_pos hsn, hpsub, hdiv, hmod,
        if_pos hpair, decide_eq_true_eq] at hedg
      have hprj : proj G hn s = ⟨(s : Nat), hsn⟩ := by simp only [proj, dif_pos hsn]
      rcases hedg with h | h
      · left
        have hEq : (⟨(s : Nat), hsn⟩ : Fin G.n) = a := Fin.ext h
        rw [← hEq, ← hprj]
        exact Finset.mem_image_of_mem _ hs
      · right
        have hEq : (⟨(s : Nat), hsn⟩ : Fin G.n) = b := Fin.ext h
        rw [← hEq, ← hprj]
        exact Finset.mem_image_of_mem _ hs
  intro i j hedge
  rcases lt_trichotomy (i : Nat) (j : Nat) with h | h | h
  · exact main i j h hedge
  · exfalso
    have hij : i = j := Fin.ext h
    rw [hij, GraphCode.valid_irrefl hval j.isLt] at hedge
    simp at hedge
  · exact (main j i h (by rw [GraphCode.valid_symm hval j.isLt i.isLt]; exact hedge)).symm

end Gadget

/-! ## The costed reduction -/

/-- Does the encoded graph have no edge at all? -/
def GraphCode.hasNoEdge (G : GraphCode) : Bool :=
  allB G.n (fun i => allB G.n (fun j => !(G.edge i j)))

lemma hasNoEdge_iff (G : GraphCode) :
    G.hasNoEdge = true ↔ ∀ i j : Fin G.n, G.edge i j = false := by
  simp only [GraphCode.hasNoEdge, allB_eq_true, Bool.not_eq_true']
  constructor
  · intro h i j; exact h i i.isLt j j.isLt
  · intro h i hi j hj; exact h ⟨i, hi⟩ ⟨j, hj⟩

/-- The branch of the reduction that actually builds the gadget. -/
def vcGadgetBranch (G : GraphCode) : Bool := G.valid && decide (G.k ≠ 0) && decide (G.k < G.n)

/-- The instance produced by the reduction: the gadget in the main case, and fixed yes/no
instances in the degenerate cases. -/
def vcTarget (G : GraphCode) : GraphCode :=
  if G.valid = true then
    if G.k = 0 then (if G.hasNoEdge = true then yesCode else noCode)
    else if G.n ≤ G.k then yesCode
    else G.toH
  else noCode

/-- The costed reduction: the validity check costs one pass over the table, and the gadget
costs one write per produced table cell. -/
def vcToOneTwo (G : GraphCode) : Counted GraphCode :=
  ⟨vcTarget G,
    if vcGadgetBranch G = true then
      { reads := G.adj.length + 1, comparisons := G.adj.length + 1,
        writes := G.hSize * G.hSize }
    else { reads := G.adj.length + 1, comparisons := G.adj.length + 1 }⟩

@[simp] lemma vcToOneTwo_value (G : GraphCode) : (vcToOneTwo G).value = vcTarget G := rfl

/-- **Stage 5b**: the reduction is correct. -/
theorem vertexCover_iff_oneTwo_radius_one (G : GraphCode) :
    VertexCoverYes G ↔ OneTwoKCenterYes (vcToOneTwo G).value := by
  rw [vcToOneTwo_value, vcTarget]
  by_cases hval : G.valid = true
  · rw [if_pos hval]
    by_cases hk0 : G.k = 0
    · rw [if_pos hk0]
      by_cases hne : G.hasNoEdge = true
      · rw [if_pos hne]
        have hyes : VertexCoverYes G := by
          refine ⟨hval, ∅, by simp [hk0], ?_⟩
          intro i j hij
          rw [(hasNoEdge_iff G).1 hne i j] at hij
          exact absurd hij (by simp)
        simp only [hyes, true_iff]
        exact yesCode_yes
      · rw [if_neg hne]
        have hno : ¬ VertexCoverYes G := by
          rintro ⟨-, S, hcard, hS⟩
          rw [hk0, Nat.le_zero] at hcard
          have hSe : S = ∅ := Finset.card_eq_zero.1 hcard
          apply hne
          rw [hasNoEdge_iff]
          intro i j
          by_contra hc
          rcases hS i j (by simpa using hc) with h | h <;> (rw [hSe] at h; simp at h)
        simp only [hno, false_iff]
        exact noCode_not_yes
    · rw [if_neg hk0]
      by_cases hnk : G.n ≤ G.k
      · rw [if_pos hnk]
        have hyes : VertexCoverYes G := by
          refine ⟨hval, Finset.univ, ?_, fun i j _ => Or.inl (Finset.mem_univ i)⟩
          simpa using hnk
        simp only [hyes, true_iff]
        exact yesCode_yes
      · rw [if_neg hnk]
        have hk1 : 1 ≤ G.k := Nat.one_le_iff_ne_zero.2 hk0
        have hkn : G.k < G.n := by omega
        have hn : 0 < G.n := by omega
        have hkH : G.k ≤ G.toH.n := by
          simp only [GraphCode.toH_n, GraphCode.hSize]; omega
        constructor
        · rintro ⟨-, W, hWcard, hW⟩
          have hW'card : (if W.Nonempty then W else {(⟨0, hn⟩ : Fin G.n)}).card ≤ G.k := by
            split_ifs
            · exact hWcard
            · simpa using hk1
          have hW'ne : (if W.Nonempty then W else {(⟨0, hn⟩ : Fin G.n)}).Nonempty := by
            split_ifs with h
            · exact h
            · exact ⟨_, Finset.mem_singleton_self _⟩
          have hW'vc : G.IsVertexCover (if W.Nonempty then W else {(⟨0, hn⟩ : Fin G.n)}) := by
            split_ifs with h
            · exact hW
            · intro i j hij
              have hWe : W = ∅ := Finset.not_nonempty_iff_eq_empty.1 h
              rcases hW i j hij with hh | hh <;> (rw [hWe] at hh; simp at hh)
          refine ⟨G.toH_valid, hk1, hkH,
            ((if W.Nonempty then W else {(⟨0, hn⟩ : Fin G.n)}).image (emb G)), ?_, ?_,
            toH_dominating_of_vertexCover hW'vc hW'ne⟩
          · exact le_trans Finset.card_image_le hW'card
          · exact hW'ne.image _
        · rintro ⟨-, -, -, T, hTcard, -, hTdom⟩
          exact ⟨hval, T.image (proj G hn), le_trans Finset.card_image_le hTcard,
            vertexCover_of_toH_dominating hval hn hTdom⟩
  · rw [if_neg hval]
    have hno : ¬ VertexCoverYes G := fun h => hval h.1
    simp only [hno, false_iff]
    exact noCode_not_yes

/-! ## Polynomial bounds for the reduction -/

lemma graphCodeSize_adj_le (G : GraphCode) : G.adj.length ≤ graphCodeSize G := by
  simp only [graphCodeSize, GraphCode.size]; omega

lemma graphCodeSize_sizek_le (G : GraphCode) : Nat.size G.k ≤ graphCodeSize G := by
  simp only [graphCodeSize, GraphCode.size]; omega

/-- In the gadget branch the number of gadget vertices is quadratic in the input size. -/
lemma hSize_le (G : GraphCode) (hval : G.valid = true) :
    G.hSize ≤ 2 * (graphCodeSize G + 1) ^ 2 := by
  set s := graphCodeSize G with hs
  have hlen : G.adj.length = G.n * G.n := GraphCode.valid_length hval
  have hnle : G.n ≤ s + 1 := by
    have h1 : G.n ≤ G.n * G.n + 1 := by nlinarith [Nat.zero_le G.n]
    have h2 : G.adj.length ≤ s := graphCodeSize_adj_le G
    omega
  have hsq : G.n * G.n ≤ (s + 1) ^ 2 := by
    have := Nat.mul_le_mul hnle hnle
    simpa [pow_two] using this
  simp only [GraphCode.hSize]
  have hlin : G.n ≤ (s + 1) ^ 2 := by
    have : (s + 1) ≤ (s + 1) ^ 2 := by nlinarith [Nat.zero_le s]
    omega
  omega

lemma vcToOneTwo_work_le (G : GraphCode) :
    (vcToOneTwo G).ops.work ≤ 6 * (graphCodeSize G + 1) ^ 4 := by
  set s := graphCodeSize G with hs
  have hA : 1 ≤ s + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have p1 : s + 1 ≤ (s + 1) ^ 4 := by
    calc s + 1 = (s + 1) ^ 1 := (pow_one _).symm
      _ ≤ (s + 1) ^ 4 := Nat.pow_le_pow_right hA (by norm_num)
  have hadj : G.adj.length ≤ s := graphCodeSize_adj_le G
  by_cases hbr : vcGadgetBranch G = true
  · have hval : G.valid = true := by
      simp only [vcGadgetBranch, Bool.and_eq_true] at hbr
      exact hbr.1.1
    have hH := hSize_le G hval
    have hHsq : G.hSize * G.hSize ≤ 4 * (s + 1) ^ 4 := by
      calc G.hSize * G.hSize ≤ (2 * (s + 1) ^ 2) * (2 * (s + 1) ^ 2) := Nat.mul_le_mul hH hH
        _ = 4 * (s + 1) ^ 4 := by ring
    have hw : (vcToOneTwo G).ops.work = (G.adj.length + 1) + (G.adj.length + 1)
        + G.hSize * G.hSize := by
      simp only [vcToOneTwo, if_pos hbr, OpCount.work]
      omega
    rw [hw]
    omega
  · have hw : (vcToOneTwo G).ops.work = (G.adj.length + 1) + (G.adj.length + 1) := by
      simp only [vcToOneTwo, if_neg hbr, OpCount.work]
      omega
    rw [hw]
    omega

lemma vcToOneTwo_size_le (G : GraphCode) :
    oneTwoCodeSize (vcToOneTwo G).value ≤ 10 * (graphCodeSize G + 1) ^ 4 := by
  set s := graphCodeSize G with hs
  have hA : 1 ≤ s + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have p1 : s + 1 ≤ (s + 1) ^ 4 := by
    calc s + 1 = (s + 1) ^ 1 := (pow_one _).symm
      _ ≤ (s + 1) ^ 4 := Nat.pow_le_pow_right hA (by norm_num)
  have p2 : (s + 1) ^ 2 ≤ (s + 1) ^ 4 := Nat.pow_le_pow_right hA (by norm_num)
  have hconst : ∀ C : GraphCode, C = yesCode ∨ C = noCode →
      oneTwoCodeSize C ≤ 10 * (s + 1) ^ 4 := by
    intro C hC
    have hle : oneTwoCodeSize C ≤ 9 := by
      rcases hC with rfl | rfl
      · simp only [oneTwoCodeSize, GraphCode.size, yesCode]
        simp
      · have h1 : Nat.size 2 ≤ 2 := Nat.size_le.2 (by norm_num)
        have h2 : Nat.size 1 ≤ 1 := Nat.size_le.2 (by norm_num)
        simp only [oneTwoCodeSize, GraphCode.size, noCode, flatTable_length]
        omega
    have : (9 : Nat) ≤ 10 * (s + 1) ^ 4 := by
      have : 1 ≤ (s + 1) ^ 4 := Nat.one_le_pow _ _ (Nat.succ_pos _)
      omega
    omega
  rw [vcToOneTwo_value, vcTarget]
  by_cases hval : G.valid = true
  · rw [if_pos hval]
    by_cases hk0 : G.k = 0
    · rw [if_pos hk0]
      split_ifs
      · exact hconst _ (Or.inl rfl)
      · exact hconst _ (Or.inr rfl)
    · rw [if_neg hk0]
      by_cases hnk : G.n ≤ G.k
      · rw [if_pos hnk]; exact hconst _ (Or.inl rfl)
      · rw [if_neg hnk]
        have hH := hSize_le G hval
        have hHsq : G.hSize * G.hSize ≤ 4 * (s + 1) ^ 4 := by
          calc G.hSize * G.hSize ≤ (2 * (s + 1) ^ 2) * (2 * (s + 1) ^ 2) := Nat.mul_le_mul hH hH
            _ = 4 * (s + 1) ^ 4 := by ring
        have hsz : oneTwoCodeSize G.toH
            = 2 + Nat.size G.hSize + Nat.size G.k + G.hSize * G.hSize := by
          simp only [oneTwoCodeSize, GraphCode.size, GraphCode.toH, flatTable_length]
        rw [hsz]
        have h1 : Nat.size G.hSize ≤ G.hSize := natSize_le_self _
        have h2 : Nat.size G.k ≤ s := graphCodeSize_sizek_le G
        have h3 : G.hSize ≤ 2 * (s + 1) ^ 2 := hH
        have h4 : 2 * (s + 1) ^ 2 ≤ 2 * (s + 1) ^ 4 := by omega
        omega
  · rw [if_neg hval]; exact hconst _ (Or.inr rfl)

/-- **Stage 5b**: Vertex Cover polynomially reduces to `k`-center for `1`–`2` metrics. -/
theorem vertexCover_polyReduces_oneTwoKCenter :
    PolyReduction graphCodeSize oneTwoCodeSize VertexCoverYes OneTwoKCenterYes :=
  ⟨vcToOneTwo, ⟨6, 4, vcToOneTwo_work_le⟩, ⟨10, 4, vcToOneTwo_size_le⟩,
    vertexCover_iff_oneTwo_radius_one⟩

/-! ## Stage 6: the exact gap of the produced instances -/

/-- Feasibility of radius `r` for the `1`–`2` table of `H`, with at most `H.k` centres. -/
def OneTwoFeasible (H : GraphCode) (r : ℕ) : Prop :=
  ∃ S : Finset (Fin H.n), S.Nonempty ∧ S.card ≤ H.k ∧
    ∀ i : Fin H.n, ∃ s ∈ S, oneTwoDist H i s ≤ r

open Classical in
/-- The optimal `1`–`2` covering radius with at most `H.k` centres.  All `1`–`2` distances
lie in `{0,1,2}`, so this is one of `0`, `1`, `2`. -/
noncomputable def oneTwoOpt (H : GraphCode) : ℕ :=
  if OneTwoFeasible H 0 then 0 else if OneTwoFeasible H 1 then 1 else 2

lemma oneTwoFeasible_mono {H : GraphCode} {r r' : ℕ} (h : r ≤ r')
    (hf : OneTwoFeasible H r) : OneTwoFeasible H r' := by
  obtain ⟨S, hne, hcard, hcov⟩ := hf
  exact ⟨S, hne, hcard, fun i => by
    obtain ⟨s, hs, hle⟩ := hcov i
    exact ⟨s, hs, le_trans hle h⟩⟩

lemma oneTwoFeasible_two {H : GraphCode} (hk : 1 ≤ H.k) (hn : 0 < H.n) :
    OneTwoFeasible H 2 :=
  ⟨{⟨0, hn⟩}, ⟨_, Finset.mem_singleton_self _⟩, by rw [Finset.card_singleton]; exact hk,
    fun i => ⟨⟨0, hn⟩, Finset.mem_singleton_self _, oneTwoDist_le_two H _ _⟩⟩

lemma oneTwoFeasible_one_iff (H : GraphCode) :
    OneTwoFeasible H 1 ↔ ∃ S : Finset (Fin H.n), S.Nonempty ∧ S.card ≤ H.k ∧ H.IsDominating S := by
  constructor
  · rintro ⟨S, hne, hcard, hcov⟩
    exact ⟨S, hne, hcard, (oneTwoDist_le_one_iff_dominating H S).1 hcov⟩
  · rintro ⟨S, hne, hcard, hdom⟩
    exact ⟨S, hne, hcard, (oneTwoDist_le_one_iff_dominating H S).2 hdom⟩

/-- The optimum is attained. -/
theorem oneTwoOpt_feasible {H : GraphCode} (hk : 1 ≤ H.k) (hn : 0 < H.n) :
    OneTwoFeasible H (oneTwoOpt H) := by
  classical
  rw [oneTwoOpt]
  split_ifs with h0 h1
  · exact h0
  · exact h1
  · exact oneTwoFeasible_two hk hn

theorem oneTwoOpt_le_two (H : GraphCode) : oneTwoOpt H ≤ 2 := by
  classical
  rw [oneTwoOpt]
  split_ifs <;> omega

theorem oneTwoOpt_le_one_iff (H : GraphCode) : oneTwoOpt H ≤ 1 ↔ OneTwoFeasible H 1 := by
  classical
  rw [oneTwoOpt]
  split_ifs with h0 h1
  · exact ⟨fun _ => oneTwoFeasible_mono (by omega) h0, fun _ => by omega⟩
  · exact ⟨fun _ => h1, fun _ => le_rfl⟩
  · exact ⟨fun h => absurd h (by omega), fun h => absurd h h1⟩

/-- The produced instance always satisfies the `1 ≤ k ≤ n` input convention. -/
lemma vcTarget_conv (G : GraphCode) :
    (vcTarget G).valid = true ∧ 1 ≤ (vcTarget G).k ∧ (vcTarget G).k ≤ (vcTarget G).n := by
  rw [vcTarget]
  by_cases hval : G.valid = true
  · rw [if_pos hval]
    by_cases hk0 : G.k = 0
    · rw [if_pos hk0]
      split_ifs
      · exact ⟨yesCode_valid, Nat.le_refl 1, Nat.le_refl 1⟩
      · exact ⟨noCode_valid, Nat.le_refl 1, by norm_num [noCode]⟩
    · rw [if_neg hk0]
      by_cases hnk : G.n ≤ G.k
      · rw [if_pos hnk]; exact ⟨yesCode_valid, Nat.le_refl 1, Nat.le_refl 1⟩
      · rw [if_neg hnk]
        refine ⟨G.toH_valid, Nat.one_le_iff_ne_zero.2 hk0, ?_⟩
        simp only [GraphCode.toH_n, GraphCode.toH_k, GraphCode.hSize]
        omega
  · rw [if_neg hval]
    exact ⟨noCode_valid, Nat.le_refl 1, by norm_num [noCode]⟩

lemma oneTwoKCenterYes_iff_feasible_one (H : GraphCode)
    (h : H.valid = true ∧ 1 ≤ H.k ∧ H.k ≤ H.n) :
    OneTwoKCenterYes H ↔ OneTwoFeasible H 1 := by
  rw [oneTwoFeasible_one_iff]
  constructor
  · rintro ⟨-, -, -, S, hcard, hne, hdom⟩; exact ⟨S, hne, hcard, hdom⟩
  · rintro ⟨S, hne, hcard, hdom⟩; exact ⟨h.1, h.2.1, h.2.2, S, hcard, hne, hdom⟩

/-- **Stage 6, yes case**: a yes-instance of Vertex Cover is mapped to an instance of
optimum `1`–`2` radius at most `1`. -/
theorem optimalRadius_le_one_of_vertexCover {G : GraphCode} (h : VertexCoverYes G) :
    oneTwoOpt (vcToOneTwo G).value ≤ 1 := by
  rw [vcToOneTwo_value, oneTwoOpt_le_one_iff,
    ← oneTwoKCenterYes_iff_feasible_one _ (vcTarget_conv G)]
  exact (vertexCover_iff_oneTwo_radius_one G).1 h

/-- **Stage 6, no case**: a no-instance of Vertex Cover is mapped to an instance of optimum
`1`–`2` radius exactly `2`. -/
theorem optimalRadius_eq_two_of_not_vertexCover {G : GraphCode} (h : ¬ VertexCoverYes G) :
    oneTwoOpt (vcToOneTwo G).value = 2 := by
  have hno : ¬ OneTwoFeasible (vcTarget G) 1 := by
    rw [← oneTwoKCenterYes_iff_feasible_one _ (vcTarget_conv G)]
    exact fun hc => h ((vertexCover_iff_oneTwo_radius_one G).2 hc)
  have h2 := oneTwoOpt_le_two (vcTarget G)
  have h1 : ¬ (oneTwoOpt (vcTarget G) ≤ 1) := by
    rw [oneTwoOpt_le_one_iff]; exact hno
  rw [vcToOneTwo_value]
  omega

/-- The exact gap: the reduction maps yes-instances to optimum at most `1` and
no-instances to optimum exactly `2`. -/
theorem vcToOneTwo_gap (G : GraphCode) :
    (VertexCoverYes G → oneTwoOpt (vcToOneTwo G).value ≤ 1) ∧
      (¬ VertexCoverYes G → oneTwoOpt (vcToOneTwo G).value = 2) :=
  ⟨optimalRadius_le_one_of_vertexCover, optimalRadius_eq_two_of_not_vertexCover⟩

end Q764
