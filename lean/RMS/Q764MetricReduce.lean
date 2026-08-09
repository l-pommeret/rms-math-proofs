/-
# Q764 — from `1`–`2` instances to general finite metric instances

The `1`–`2` table of a graph is a genuine metric (`Q764.oneTwoDist_triangle`, obtained from
the compiled `Q764.oneTwo_triangle`), so a `1`–`2` instance is literally a metric instance
at threshold `1`.  This file materializes that table as a `Q764.MetricCode` with polynomial
cost and proves

* `Q764.oneTwoKCenter_polyReduces_metricKCenter`;
* `Q764.vertexCover_polyReduces_metricKCenter`, by composition with
  `Q764.vertexCover_polyReduces_oneTwoKCenter`.
-/
import RMS.Q764Gadget

namespace Q764

/-! ## Flat square tables of naturals -/

/-- A flat `N*N` table of naturals. -/
def flatTabN (N : Nat) (f : Nat → Nat → Nat) : List Nat :=
  (List.range (N * N)).map (fun t => f (t / N) (t % N))

@[simp] lemma flatTabN_length (N : Nat) (f : Nat → Nat → Nat) :
    (flatTabN N f).length = N * N := by simp [flatTabN]

lemma flatTabN_getD {N : Nat} (f : Nat → Nat → Nat) {u v : Nat} (hu : u < N) (hv : v < N) :
    (flatTabN N f).getD (u * N + v) 0 = f u v := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hv
  have hlt : u * N + v < N * N := by
    calc u * N + v < u * N + N := by omega
      _ = (u + 1) * N := by ring
      _ ≤ N * N := Nat.mul_le_mul_right N hu
  rw [List.getD_eq_getElem _ _ (by simpa [flatTabN] using hlt)]
  simp only [flatTabN, List.getElem_map, List.getElem_range]
  have hcomm : u * N + v = v + N * u := by ring
  rw [hcomm, Nat.add_mul_div_left v u hN, Nat.div_eq_of_lt hv, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]

lemma flatTabN_mem_le {N : Nat} {f : Nat → Nat → Nat} {b : Nat}
    (hf : ∀ i j, f i j ≤ b) : ∀ v ∈ flatTabN N f, v ≤ b := by
  intro v hv
  simp only [flatTabN, List.mem_map] at hv
  obtain ⟨t, -, rfl⟩ := hv
  exact hf _ _

/-! ## A general validity criterion for metric codes -/

lemma MetricCode.valid_of {I : MetricCode} (hlen : I.d.length = I.n * I.n)
    (hk1 : 1 ≤ I.k) (hkn : I.k ≤ I.n)
    (hdiag : ∀ i < I.n, I.dist i i = 0)
    (hsymm : ∀ i < I.n, ∀ j < I.n, I.dist i j = I.dist j i)
    (hpos : ∀ i < I.n, ∀ j < I.n, i ≠ j → 1 ≤ I.dist i j)
    (htri : ∀ i < I.n, ∀ j < I.n, ∀ l < I.n, I.dist i l ≤ I.dist i j + I.dist j l) :
    I.valid = true := by
  simp only [MetricCode.valid, Bool.and_eq_true, allB_eq_true, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true, hlen, hk1, hkn, true_and, and_true]
  refine ⟨⟨hdiag, fun i hi j hj => ⟨hsymm i hi j hj, ?_⟩⟩, htri⟩
  by_cases hij : i = j
  · exact Or.inl hij
  · exact Or.inr (hpos i hi j hj hij)

/-! ## The metric code of a `1`–`2` instance -/

/-- The metric instance carrying the `1`–`2` table of `G`, at threshold `1`. -/
def toMetric (G : GraphCode) : MetricCode :=
  ⟨G.n, G.k, 1, flatTabN G.n (oneTwoDist G)⟩

@[simp] lemma toMetric_n (G : GraphCode) : (toMetric G).n = G.n := rfl
@[simp] lemma toMetric_k (G : GraphCode) : (toMetric G).k = G.k := rfl
@[simp] lemma toMetric_r (G : GraphCode) : (toMetric G).r = 1 := rfl

lemma toMetric_dist {G : GraphCode} {i j : Nat} (hi : i < G.n) (hj : j < G.n) :
    (toMetric G).dist i j = oneTwoDist G i j :=
  flatTabN_getD _ hi hj

lemma toMetric_valid {G : GraphCode} (hval : G.valid = true) (hk1 : 1 ≤ G.k)
    (hkn : G.k ≤ G.n) : (toMetric G).valid = true := by
  refine MetricCode.valid_of (by simp [toMetric]) hk1 hkn ?_ ?_ ?_ ?_
  · intro i hi; rw [toMetric_dist hi hi]; simp
  · intro i hi j hj; rw [toMetric_dist hi hj, toMetric_dist hj hi]
    exact oneTwoDist_symm hval hi hj
  · intro i hi j hj hij; rw [toMetric_dist hi hj]; exact oneTwoDist_pos hij
  · intro i hi j hj l hl
    rw [toMetric_dist hi hl, toMetric_dist hi hj, toMetric_dist hj hl]
    have := oneTwoDist_triangle G i j l
    exact_mod_cast this

lemma toMetric_covers_iff {G : GraphCode} (F : Finset (Fin G.n)) :
    (toMetric G).Covers F 1 ↔ G.IsDominating F := by
  rw [← oneTwoDist_le_one_iff_dominating]
  constructor
  · intro h i
    obtain ⟨c, hc, hle⟩ := h i
    rw [toMetric_dist i.isLt c.isLt] at hle
    exact ⟨c, hc, hle⟩
  · intro h i
    obtain ⟨c, hc, hle⟩ := h i
    exact ⟨c, hc, by rw [toMetric_dist i.isLt c.isLt]; exact hle⟩

/-- The target of the reduction: the `1`–`2` metric table of a well-formed instance, and
a fixed no-instance otherwise. -/
def oneTwoToMetricTarget (G : GraphCode) : MetricCode :=
  if G.valid = true ∧ 1 ≤ G.k ∧ G.k ≤ G.n then toMetric G else toMetric noCode

/-- The costed reduction. -/
def oneTwoToMetric (G : GraphCode) : Counted MetricCode :=
  ⟨oneTwoToMetricTarget G,
    { reads := G.adj.length + 1, comparisons := G.adj.length + 1,
      writes := G.adj.length + 4 }⟩

@[simp] lemma oneTwoToMetric_value (G : GraphCode) :
    (oneTwoToMetric G).value = oneTwoToMetricTarget G := rfl

lemma metricKCenterYes_toMetric_iff {G : GraphCode} (hval : G.valid = true) (hk1 : 1 ≤ G.k)
    (hkn : G.k ≤ G.n) : MetricKCenterYes (toMetric G) ↔ OneTwoKCenterYes G := by
  constructor
  · rintro ⟨-, F, hne, hcard, hcov⟩
    exact ⟨hval, hk1, hkn, F, hcard, hne, (toMetric_covers_iff F).1 hcov⟩
  · rintro ⟨-, -, -, S, hcard, hne, hdom⟩
    exact ⟨toMetric_valid hval hk1 hkn, S, hne, hcard, (toMetric_covers_iff S).2 hdom⟩

lemma not_metricKCenterYes_toMetric_noCode : ¬ MetricKCenterYes (toMetric noCode) := by
  intro h
  exact noCode_not_yes
    ((metricKCenterYes_toMetric_iff noCode_valid (Nat.le_refl 1) (by norm_num [noCode])).1 h)

/-- **Correctness** of the reduction from `1`–`2` instances to general metric instances. -/
theorem oneTwoKCenterYes_iff_metricKCenterYes (G : GraphCode) :
    OneTwoKCenterYes G ↔ MetricKCenterYes (oneTwoToMetric G).value := by
  rw [oneTwoToMetric_value, oneTwoToMetricTarget]
  by_cases hc : G.valid = true ∧ 1 ≤ G.k ∧ G.k ≤ G.n
  · rw [if_pos hc]
    exact (metricKCenterYes_toMetric_iff hc.1 hc.2.1 hc.2.2).symm
  · rw [if_neg hc]
    have hno : ¬ OneTwoKCenterYes G := fun h => hc ⟨h.1, h.2.1, h.2.2.1⟩
    simp only [hno, false_iff]
    exact not_metricKCenterYes_toMetric_noCode

/-! ## Polynomial bounds -/

lemma toMetric_size_le (G : GraphCode) :
    metricCodeSize (toMetric G) ≤ 4 + Nat.size G.n + Nat.size G.k + 3 * (G.n * G.n) := by
  have hbound : ∀ v ∈ (toMetric G).d.map (fun v => 1 + Nat.size v), v ≤ 3 := by
    intro v hv
    simp only [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have hw2 : w ≤ 2 := flatTabN_mem_le (fun i j => oneTwoDist_le_two G i j) w hw
    have : Nat.size w ≤ 2 := Nat.size_le.2 (by omega)
    omega
  have hsum := List.sum_le_card_nsmul _ 3 hbound
  have hlen : ((toMetric G).d.map (fun v => 1 + Nat.size v)).length = G.n * G.n := by
    simp [toMetric]
  rw [hlen] at hsum
  simp only [smul_eq_mul] at hsum
  have hsz : metricCodeSize (toMetric G)
      = 3 + Nat.size G.n + Nat.size G.k + Nat.size 1
        + ((toMetric G).d.map (fun v => 1 + Nat.size v)).sum := rfl
  have hone : Nat.size 1 = 1 := rfl
  rw [hsz, hone]
  omega

lemma oneTwoToMetric_work_le (G : GraphCode) :
    (oneTwoToMetric G).ops.work ≤ 6 * (graphCodeSize G + 1) ^ 1 := by
  have hadj : G.adj.length ≤ graphCodeSize G := graphCodeSize_adj_le G
  have hw : (oneTwoToMetric G).ops.work
      = (G.adj.length + 1) + (G.adj.length + 1) + (G.adj.length + 4) := by
    simp only [oneTwoToMetric, OpCount.work]
    omega
  rw [hw, pow_one]
  omega

lemma oneTwoToMetric_size_le (G : GraphCode) :
    metricCodeSize (oneTwoToMetric G).value ≤ 20 * (graphCodeSize G + 1) ^ 1 := by
  set s := graphCodeSize G with hs
  rw [oneTwoToMetric_value, oneTwoToMetricTarget, pow_one]
  by_cases hc : G.valid = true ∧ 1 ≤ G.k ∧ G.k ≤ G.n
  · rw [if_pos hc]
    have hlen : G.adj.length = G.n * G.n := GraphCode.valid_length hc.1
    have hadj : G.adj.length ≤ s := graphCodeSize_adj_le G
    have hk : Nat.size G.k ≤ s := graphCodeSize_sizek_le G
    have hn : Nat.size G.n ≤ G.n := natSize_le_self _
    have hnn : G.n ≤ G.n * G.n + 1 := by nlinarith [Nat.zero_le G.n]
    have := toMetric_size_le G
    omega
  · rw [if_neg hc]
    have h := toMetric_size_le noCode
    have h1 : Nat.size (2 : Nat) ≤ 2 := Nat.size_le.2 (by norm_num)
    have h2 : Nat.size (1 : Nat) ≤ 1 := Nat.size_le.2 (by norm_num)
    have hn2 : noCode.n = 2 := rfl
    have hk1 : noCode.k = 1 := rfl
    rw [hn2, hk1] at h
    omega

/-- `1`–`2` `k`-center polynomially reduces to general finite metric `k`-center. -/
theorem oneTwoKCenter_polyReduces_metricKCenter :
    PolyReduction oneTwoCodeSize metricCodeSize OneTwoKCenterYes MetricKCenterYes :=
  ⟨oneTwoToMetric, ⟨6, 1, oneTwoToMetric_work_le⟩, ⟨20, 1, oneTwoToMetric_size_le⟩,
    oneTwoKCenterYes_iff_metricKCenterYes⟩

/-- Vertex Cover polynomially reduces to general finite metric `k`-center. -/
theorem vertexCover_polyReduces_metricKCenter :
    PolyReduction graphCodeSize metricCodeSize VertexCoverYes MetricKCenterYes :=
  vertexCover_polyReduces_oneTwoKCenter.trans oneTwoKCenter_polyReduces_metricKCenter

/-- A polynomial decision procedure for general finite metric `k`-center would put Vertex
Cover in P. -/
theorem vertexCover_inP_of_metricKCenter_inP (h : InP metricCodeSize MetricKCenterYes) :
    InP graphCodeSize VertexCoverYes :=
  InP.of_polyReduction vertexCover_polyReduces_metricKCenter h

/-- A polynomial decision procedure for `k`-center restricted to `1`–`2` metrics would
already put Vertex Cover in P. -/
theorem vertexCover_inP_of_oneTwoKCenter_inP (h : InP oneTwoCodeSize OneTwoKCenterYes) :
    InP graphCodeSize VertexCoverYes :=
  InP.of_polyReduction vertexCover_polyReduces_oneTwoKCenter h

end Q764
