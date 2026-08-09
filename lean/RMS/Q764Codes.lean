/-
# Q764 — stable finite encodings of the decision problems

Explicit flat encodings (no uncharged proofs, no abstract functions smuggled into the
input):

* `Q764.GraphCode` — `n`, a flat `n*n` Boolean adjacency table, and `k`;
* `Q764.MetricCode` — `n`, `k`, a threshold `r` and a flat `n*n` table of binary
  natural numbers.

Validity is a *polynomially checkable Boolean predicate* on the raw data
(`Q764.GraphCode.valid`, `Q764.MetricCode.valid`), and input sizes
(`Q764.graphCodeSize`, `Q764.metricCodeSize`) are computed from the serialized fields,
including the bit lengths of `k`, of the radius and of the distance entries.

The decision problems are `Q764.VertexCoverYes`, `Q764.OneTwoKCenterYes` (domination in
a graph, i.e. `k`-center at radius `1` for the `1`–`2` metric) and
`Q764.MetricKCenterYes`.

The `1`–`2` table of a graph is `Q764.oneTwoDist`; it is proved to be a metric
(`Q764.oneTwoDist_triangle`, reusing `Q764.oneTwo_triangle`), and for a valid metric code
the table predicate is identified with the covering radius of a genuine mathlib
pseudometric space (`Q764.MetricCode.covRad_le_iff_table`).
-/
import RMS.Q764Bridge

open Finset

namespace Q764

/-! ## Bounded Boolean quantifiers -/

/-- `allB n p` is `true` iff `p i` holds for all `i < n`. -/
def allB (n : Nat) (p : Nat → Bool) : Bool := (List.range n).all p

@[simp] lemma allB_eq_true {n : Nat} {p : Nat → Bool} :
    allB n p = true ↔ ∀ i < n, p i = true := by
  simp [allB, List.all_eq_true]

/-! ## Graphs -/

/-- A graph instance: `n` vertices, a flat `n*n` adjacency table, and a parameter `k`. -/
structure GraphCode where
  n : Nat
  adj : List Bool
  k : Nat
  deriving DecidableEq, Repr, Inhabited

namespace GraphCode

/-- Adjacency of the encoded graph. -/
def edge (G : GraphCode) (i j : Nat) : Bool := G.adj.getD (i * G.n + j) false

/-- Polynomially checkable validity: the table has the right length, is symmetric and has
zero diagonal (a simple graph). -/
def valid (G : GraphCode) : Bool :=
  (G.adj.length == G.n * G.n) &&
    allB G.n (fun i => allB G.n (fun j => (G.edge i j == G.edge j i) && !(G.edge i i)))

lemma valid_symm {G : GraphCode} (h : G.valid = true) {i j : Nat} (hi : i < G.n) (hj : j < G.n) :
    G.edge i j = G.edge j i := by
  simp only [valid, Bool.and_eq_true, allB_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  exact (h.2 i hi j hj).1

lemma valid_irrefl {G : GraphCode} (h : G.valid = true) {i : Nat} (hi : i < G.n) :
    G.edge i i = false := by
  simp only [valid, Bool.and_eq_true, allB_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  exact (h.2 i hi i hi).2

lemma valid_length {G : GraphCode} (h : G.valid = true) : G.adj.length = G.n * G.n := by
  simp only [valid, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- Serialized size of a graph code. -/
def size (G : GraphCode) : Nat := 2 + Nat.size G.n + Nat.size G.k + G.adj.length

/-- `S` is a vertex cover of `G`. -/
def IsVertexCover (G : GraphCode) (S : Finset (Fin G.n)) : Prop :=
  ∀ i j : Fin G.n, G.edge i j = true → i ∈ S ∨ j ∈ S

/-- `S` is a dominating set of `G` (every vertex is in `S` or adjacent to `S`). -/
def IsDominating (G : GraphCode) (S : Finset (Fin G.n)) : Prop :=
  ∀ i : Fin G.n, ∃ s ∈ S, (i : Nat) = (s : Nat) ∨ G.edge i s = true

end GraphCode

/-- Size function for graph codes. -/
def graphCodeSize (G : GraphCode) : Nat := G.size

/-- **Vertex Cover**: does the encoded graph have a vertex cover of size at most `k`? -/
def VertexCoverYes (G : GraphCode) : Prop :=
  G.valid = true ∧ ∃ S : Finset (Fin G.n), S.card ≤ G.k ∧ G.IsVertexCover S

/-- **`k`-center for the `1`–`2` metric of a graph at radius `1`**, i.e. domination.
The convention `1 ≤ k ≤ n` of the input format is part of the instance. -/
def OneTwoKCenterYes (G : GraphCode) : Prop :=
  G.valid = true ∧ 1 ≤ G.k ∧ G.k ≤ G.n ∧
    ∃ S : Finset (Fin G.n), S.card ≤ G.k ∧ S.Nonempty ∧ G.IsDominating S

/-- Size function for `1`–`2` instances (the same encoding as for graphs). -/
def oneTwoCodeSize (G : GraphCode) : Nat := G.size

/-! ## The `1`–`2` distance table of a graph -/

/-- The `1`–`2` table: `0` on the diagonal, `1` on edges, `2` otherwise. -/
def oneTwoDist (G : GraphCode) (i j : Nat) : Nat :=
  if i = j then 0 else if G.edge i j = true then 1 else 2

@[simp] lemma oneTwoDist_self (G : GraphCode) (i : Nat) : oneTwoDist G i i = 0 := by
  simp [oneTwoDist]

lemma oneTwoDist_pos {G : GraphCode} {i j : Nat} (h : i ≠ j) : 1 ≤ oneTwoDist G i j := by
  simp only [oneTwoDist, if_neg h]
  split <;> omega

lemma oneTwoDist_le_two (G : GraphCode) (i j : Nat) : oneTwoDist G i j ≤ 2 := by
  simp only [oneTwoDist]
  split <;> [omega; split] <;> omega

lemma oneTwoDist_symm {G : GraphCode} (h : G.valid = true) {i j : Nat}
    (hi : i < G.n) (hj : j < G.n) : oneTwoDist G i j = oneTwoDist G j i := by
  simp only [oneTwoDist]
  by_cases hij : i = j
  · simp [hij]
  · rw [if_neg hij, if_neg (Ne.symm hij), GraphCode.valid_symm h hi hj]

/-- **Lemma 9 applied to the `1`–`2` table**: it satisfies the triangle inequality. -/
theorem oneTwoDist_triangle (G : GraphCode) (a b c : Nat) :
    (oneTwoDist G a c : ℝ) ≤ (oneTwoDist G a b : ℝ) + (oneTwoDist G b c : ℝ) := by
  refine oneTwo_triangle (fun i j => (oneTwoDist G i j : ℝ)) (by simp) ?_ ?_ a b c
  · intro i j hij
    show (1 : ℝ) ≤ (oneTwoDist G i j : ℝ)
    exact_mod_cast oneTwoDist_pos hij
  · intro i j
    show (oneTwoDist G i j : ℝ) ≤ 2
    exact_mod_cast oneTwoDist_le_two G i j

/-- Radius `≤ 1` for the `1`–`2` table is exactly domination. -/
theorem oneTwoDist_le_one_iff_dominating (G : GraphCode) (S : Finset (Fin G.n)) :
    (∀ i : Fin G.n, ∃ s ∈ S, oneTwoDist G i s ≤ 1) ↔ G.IsDominating S := by
  constructor
  · intro h i
    obtain ⟨s, hs, hle⟩ := h i
    refine ⟨s, hs, ?_⟩
    by_cases hij : (i : Nat) = (s : Nat)
    · exact Or.inl hij
    · right
      simp only [oneTwoDist, if_neg hij] at hle
      by_cases he : G.edge i s = true
      · exact he
      · simp [he] at hle
  · intro h i
    obtain ⟨s, hs, hcase⟩ := h i
    refine ⟨s, hs, ?_⟩
    rcases hcase with hij | he
    · simp [oneTwoDist, hij]
    · simp only [oneTwoDist]
      split
      · omega
      · simp [he]

/-- **Stage 1.4**: failure of domination forces `1`–`2` radius exactly `2`. -/
theorem exists_dist_two_of_not_dominating {G : GraphCode} {S : Finset (Fin G.n)}
    (h : ¬ G.IsDominating S) : ∃ i : Fin G.n, ∀ s ∈ S, oneTwoDist G i s = 2 := by
  have hc : ¬ (∀ i : Fin G.n, ∃ s ∈ S, oneTwoDist G i s ≤ 1) := fun hh =>
    h ((oneTwoDist_le_one_iff_dominating G S).1 hh)
  push_neg at hc
  obtain ⟨i, hi⟩ := hc
  refine ⟨i, fun s hs => ?_⟩
  have h1 := hi s hs
  have h2 := oneTwoDist_le_two G i s
  omega

/-- **Stage 1.4**: all `1`–`2` distances are `0`, `1` or `2`. -/
theorem oneTwoDist_cases (G : GraphCode) (i j : Nat) :
    oneTwoDist G i j = 0 ∨ oneTwoDist G i j = 1 ∨ oneTwoDist G i j = 2 := by
  have := oneTwoDist_le_two G i j
  omega

/-! ## Metric codes -/

/-- A finite metric instance: `n` points, a parameter `k`, a threshold `r` and a flat
`n*n` table of nonnegative binary integers. -/
structure MetricCode where
  n : Nat
  k : Nat
  r : Nat
  d : List Nat
  deriving DecidableEq, Repr, Inhabited

namespace MetricCode

/-- The distance table. -/
def dist (I : MetricCode) (i j : Nat) : Nat := I.d.getD (i * I.n + j) 0

/-- Polynomially checkable validity: correct table length, `1 ≤ k ≤ n`, zero diagonal,
symmetry, positivity off the diagonal, and the triangle inequalities. -/
def valid (I : MetricCode) : Bool :=
  (I.d.length == I.n * I.n) && (1 ≤ I.k) && (I.k ≤ I.n) &&
    allB I.n (fun i => I.dist i i == 0) &&
    allB I.n (fun i => allB I.n (fun j => (I.dist i j == I.dist j i) &&
      (decide (i = j) || decide (1 ≤ I.dist i j)))) &&
    allB I.n (fun i => allB I.n (fun j => allB I.n (fun l =>
      decide (I.dist i l ≤ I.dist i j + I.dist j l))))

lemma valid_length {I : MetricCode} (h : I.valid = true) : I.d.length = I.n * I.n := by
  simp only [valid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h.1.1.1.1.1

lemma valid_k_pos {I : MetricCode} (h : I.valid = true) : 1 ≤ I.k := by
  simp only [valid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h.1.1.1.1.2

lemma valid_k_le {I : MetricCode} (h : I.valid = true) : I.k ≤ I.n := by
  simp only [valid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h.1.1.1.2

lemma valid_n_pos {I : MetricCode} (h : I.valid = true) : 0 < I.n :=
  lt_of_lt_of_le Nat.zero_lt_one (le_trans (valid_k_pos h) (valid_k_le h))

lemma valid_diag {I : MetricCode} (h : I.valid = true) {i : Nat} (hi : i < I.n) :
    I.dist i i = 0 := by
  simp only [valid, Bool.and_eq_true, allB_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h.1.1.2 i hi

lemma valid_symm {I : MetricCode} (h : I.valid = true) {i j : Nat} (hi : i < I.n)
    (hj : j < I.n) : I.dist i j = I.dist j i := by
  simp only [valid, Bool.and_eq_true, allB_eq_true] at h
  have := h.1.2 i hi j hj
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.1

lemma valid_triangle {I : MetricCode} (h : I.valid = true) {i j l : Nat} (hi : i < I.n)
    (hj : j < I.n) (hl : l < I.n) : I.dist i l ≤ I.dist i j + I.dist j l := by
  simp only [valid, Bool.and_eq_true, allB_eq_true, decide_eq_true_eq] at h
  exact h.2 i hi j hj l hl

/-- Serialized size of a metric code. -/
def size (I : MetricCode) : Nat :=
  3 + Nat.size I.n + Nat.size I.k + Nat.size I.r + (I.d.map fun v => 1 + Nat.size v).sum

/-- The table predicate: `F` covers all points within the threshold `r`. -/
def Covers (I : MetricCode) (F : Finset (Fin I.n)) (r : Nat) : Prop :=
  ∀ i : Fin I.n, ∃ c ∈ F, I.dist i c ≤ r

end MetricCode

/-- Size function for metric codes. -/
def metricCodeSize (I : MetricCode) : Nat := I.size

/-- **Metric `k`-center**, decision form: is there a nonempty set of at most `k` centers
covering all points within the threshold `r`? -/
def MetricKCenterYes (I : MetricCode) : Prop :=
  I.valid = true ∧ ∃ F : Finset (Fin I.n), F.Nonempty ∧ F.card ≤ I.k ∧ I.Covers F I.r

/-! ## A genuine metric space from a valid metric code -/

namespace MetricCode

variable (I : MetricCode)

/-- The pseudometric space structure carried by a valid metric code. -/
noncomputable def space (h : I.valid = true) : PseudoMetricSpace (Fin I.n) where
  dist i j := (I.dist i j : ℝ)
  dist_self i := by simp [valid_diag h i.isLt]
  dist_comm i j := by simp [valid_symm h i.isLt j.isLt]
  dist_triangle i j l := by
    have := valid_triangle h i.isLt j.isLt l.isLt
    push_cast
    exact_mod_cast this

/-- The table predicate is exactly the covering-radius condition of `Q764.covRad`
in the pseudometric space attached to the code. -/
theorem covRad_le_iff_table (h : I.valid = true) (F : Finset (Fin I.n))
    (hF : F.Nonempty) (r : Nat) :
    letI := I.space h
    covRad (Finset.univ : Finset (Fin I.n)) F
        ⟨⟨0, valid_n_pos h⟩, Finset.mem_univ _⟩ hF ≤ (r : ℝ) ↔
      I.Covers F r := by
  letI := I.space h
  rw [covRad_le_iff]
  constructor
  · intro hc i
    obtain ⟨f, hf, hle⟩ := hc i (Finset.mem_univ i)
    have h' : (I.dist i f : ℝ) ≤ (r : ℝ) := hle
    exact ⟨f, hf, by exact_mod_cast h'⟩
  · intro hc i _
    obtain ⟨f, hf, hle⟩ := hc i
    refine ⟨f, hf, ?_⟩
    show (I.dist (i : Nat) (f : Nat) : ℝ) ≤ (r : ℝ)
    exact_mod_cast hle

end MetricCode

end Q764
