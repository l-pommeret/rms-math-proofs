import RMS.Q896

/-!
# A concrete admissible configuration for Q896

This file shows that the hypotheses of `Q896.q896` are satisfiable: it exhibits three rays and a
triangle satisfying *every* printed hypothesis (including the half-plane hypothesis, which the
upper bound does not use), with `n = p = 3`.  In particular the main theorem is not vacuous, and
the bound `p ≤ n` is attained here.
-/

namespace Q896

namespace Ex

open Set Topology

/-- The three prescribed ray directions. -/
def d0 : V := (1, 0)
def d1 : V := (0, 1)
def d2 : V := (-1, -1)

/-- The three prescribed rays. -/
def Rays : Fin 3 → Set V := fun j => ray (if j = 0 then d0 else if j = 1 then d1 else d2)

/-- The three zones (open sectors). -/
def S0 : Set V := {w : V | 0 < w.1 ∧ 0 < w.2}
def S1 : Set V := {w : V | w.1 < 0 ∧ w.1 < w.2}
def S2 : Set V := {w : V | w.2 < 0 ∧ w.2 < w.1}

lemma mem_ray_d0 {x : V} : x ∈ ray d0 ↔ x.2 = 0 ∧ 0 ≤ x.1 := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    simp only [d0, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero]
    exact ⟨trivial, ht⟩
  · rintro ⟨h2, h1⟩
    exact ⟨x.1, h1, by simp [d0, Prod.ext_iff, h2]⟩

lemma mem_ray_d1 {x : V} : x ∈ ray d1 ↔ x.1 = 0 ∧ 0 ≤ x.2 := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    simp only [d1, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero]
    exact ⟨trivial, ht⟩
  · rintro ⟨h1, h2⟩
    exact ⟨x.2, h2, by simp [d1, Prod.ext_iff, h1]⟩

lemma mem_ray_d2 {x : V} : x ∈ ray d2 ↔ x.1 = x.2 ∧ x.1 ≤ 0 := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    simp only [d2, Prod.smul_mk, smul_eq_mul, mul_neg, mul_one]
    exact ⟨trivial, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨-x.1, by linarith, by simp [d2, Prod.ext_iff, h1]⟩

lemma union_rays : (⋃ j, Rays j) = ray d0 ∪ ray d1 ∪ ray d2 := by
  ext x
  simp only [mem_iUnion, mem_union]
  constructor
  · rintro ⟨j, hj⟩
    simp only [Rays] at hj
    fin_cases j
    · exact Or.inl (Or.inl (by simpa using hj))
    · exact Or.inl (Or.inr (by simpa using hj))
    · exact Or.inr (by simpa using hj)
  · rintro ((h | h) | h)
    · exact ⟨0, by simpa [Rays] using h⟩
    · exact ⟨1, by simpa [Rays] using h⟩
    · exact ⟨2, by simpa [Rays] using h⟩

lemma compl_rays : (⋃ j, Rays j)ᶜ = S0 ∪ S1 ∪ S2 := by
  ext x
  rw [union_rays]
  simp only [mem_compl_iff, mem_union, mem_ray_d0, mem_ray_d1, mem_ray_d2, S0, S1, S2,
    mem_setOf_eq, not_or]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    rcases lt_trichotomy x.1 0 with hx1 | hx1 | hx1
    · rcases lt_trichotomy x.2 x.1 with hx2 | hx2 | hx2
      · right; exact ⟨by linarith, hx2⟩
      · exact absurd ⟨hx2.symm, le_of_lt hx1⟩ h2
      · left; right; exact ⟨hx1, hx2⟩
    · rcases lt_trichotomy x.2 0 with hx2 | hx2 | hx2
      · right; exact ⟨hx2, by linarith⟩
      · exact absurd ⟨hx1, le_of_eq hx2.symm⟩ h1
      · exact absurd ⟨hx1, le_of_lt hx2⟩ h1
    · rcases lt_trichotomy x.2 0 with hx2 | hx2 | hx2
      · right; exact ⟨hx2, by linarith⟩
      · exact absurd ⟨hx2, le_of_lt hx1⟩ h0
      · left; left; exact ⟨hx1, hx2⟩
  · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) <;>
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rintro ⟨ha, hb⟩ <;> linarith

lemma isOpen_S0 : IsOpen S0 :=
  (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd)

lemma isOpen_S1 : IsOpen S1 :=
  (isOpen_lt continuous_fst continuous_const).inter (isOpen_lt continuous_fst continuous_snd)

lemma isOpen_S2 : IsOpen S2 :=
  (isOpen_lt continuous_snd continuous_const).inter (isOpen_lt continuous_snd continuous_fst)

lemma convex_S0 : Convex ℝ S0 := by
  rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ a b ha hb hab
  have hab' : 0 < a ∨ 0 < b := by
    rcases eq_or_lt_of_le ha with h | h
    · right; linarith
    · left; exact h
  constructor <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] <;> rcases hab' with h | h <;> nlinarith

lemma convex_S1 : Convex ℝ S1 := by
  rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ a b ha hb hab
  have hab' : 0 < a ∨ 0 < b := by
    rcases eq_or_lt_of_le ha with h | h
    · right; linarith
    · left; exact h
  constructor <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] <;> rcases hab' with h | h <;> nlinarith

lemma convex_S2 : Convex ℝ S2 := by
  rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ a b ha hb hab
  have hab' : 0 < a ∨ 0 < b := by
    rcases eq_or_lt_of_le ha with h | h
    · right; linarith
    · left; exact h
  constructor <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] <;> rcases hab' with h | h <;> nlinarith

/-- A nonempty open convex piece of a partition of `U` into finitely many open pieces is a
connected component of `U`. -/
lemma component_eq_of_partition {U T T' : Set V} (hU : U = T ∪ T') (hT : IsOpen T)
    (hT' : IsOpen T') (hdisj : Disjoint T T') (hconv : Convex ℝ T) {x : V} (hx : x ∈ T) :
    connectedComponentIn U x = T := by
  refine Subset.antisymm ?_ ?_
  · refine IsPreconnected.subset_left_of_subset_union hT hT' hdisj ?_ ?_
      isPreconnected_connectedComponentIn
    · rw [← hU]; exact connectedComponentIn_subset U x
    · exact ⟨x, mem_connectedComponentIn (by rw [hU]; exact Or.inl hx), hx⟩
  · exact hconv.isPreconnected.subset_connectedComponentIn hx (by rw [hU]; exact subset_union_left)

lemma zone_eq {Z : Set V} (hZ : IsZone Rays Z) : Z = S0 ∨ Z = S1 ∨ Z = S2 := by
  obtain ⟨x, hx, rfl⟩ := hZ
  rw [compl_rays] at hx ⊢
  rcases hx with (hx | hx) | hx
  · left
    refine component_eq_of_partition (T := S0) (T' := S1 ∪ S2) ?_ isOpen_S0
      (isOpen_S1.union isOpen_S2) ?_ convex_S0 hx
    · rw [union_assoc]
    · rw [Set.disjoint_left]
      rintro w ⟨hw1, hw2⟩ (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith
  · right; left
    refine component_eq_of_partition (T := S1) (T' := S0 ∪ S2) ?_ isOpen_S1
      (isOpen_S0.union isOpen_S2) ?_ convex_S1 hx
    · ext w; simp only [mem_union]; tauto
    · rw [Set.disjoint_left]
      rintro w ⟨hw1, hw2⟩ (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith
  · right; right
    refine component_eq_of_partition (T := S2) (T' := S0 ∪ S1) ?_ isOpen_S2
      (isOpen_S0.union isOpen_S1) ?_ convex_S2 hx
    · ext w; simp only [mem_union]; tauto
    · rw [Set.disjoint_left]
      rintro w ⟨hw1, hw2⟩ (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith

/-! ### Closures of the zones -/

lemma closure_S0 : closure S0 ⊆ {w : V | 0 ≤ w.1 ∧ 0 ≤ w.2} := by
  refine closure_minimal (fun w hw => ⟨le_of_lt hw.1, le_of_lt hw.2⟩) ?_
  exact (isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_const continuous_snd)

lemma closure_S1 : closure S1 ⊆ {w : V | w.1 ≤ 0 ∧ w.1 ≤ w.2} := by
  refine closure_minimal (fun w hw => ⟨le_of_lt hw.1, le_of_lt hw.2⟩) ?_
  exact (isClosed_le continuous_fst continuous_const).inter
    (isClosed_le continuous_fst continuous_snd)

lemma closure_S2 : closure S2 ⊆ {w : V | w.2 ≤ 0 ∧ w.2 ≤ w.1} := by
  refine closure_minimal (fun w hw => ⟨le_of_lt hw.1, le_of_lt hw.2⟩) ?_
  exact (isClosed_le continuous_snd continuous_const).inter
    (isClosed_le continuous_snd continuous_fst)

/-! ### No zone contains an open half-plane -/

/-- A pointed closed convex cone (the intersection of two half-planes through the origin with
independent normals) contains no open half-plane. -/
lemma no_halfplane_subset_cone {u v a : V} (huv : det u v ≠ 0) (ha : a ≠ 0) {c : ℝ}
    (hsub : {x : V | c < a.1 * x.1 + a.2 * x.2} ⊆
      {x : V | 0 ≤ u.1 * x.1 + u.2 * x.2 ∧ 0 ≤ v.1 * x.1 + v.2 * x.2}) : False := by
  have hnorm : 0 < a.1 ^ 2 + a.2 ^ 2 := by
    rcases (by
      by_contra h
      push_neg at h
      exact ha (Prod.ext h.1 h.2) : a.1 ≠ 0 ∨ a.2 ≠ 0) with h | h
    · positivity
    · positivity
  set r : ℝ := (c + 1) / (a.1 ^ 2 + a.2 ^ 2) with hr
  set x0 : V := (r * a.1, r * a.2) with hx0
  have hline : ∀ t : ℝ, ((x0.1 - t * a.2, x0.2 + t * a.1) : V) ∈
      {x : V | c < a.1 * x.1 + a.2 * x.2} := by
    intro t
    simp only [mem_setOf_eq, hx0]
    have : a.1 * (r * a.1 - t * a.2) + a.2 * (r * a.2 + t * a.1) = r * (a.1 ^ 2 + a.2 ^ 2) := by
      ring
    rw [this, hr, div_mul_cancel₀ _ (ne_of_gt hnorm)]
    linarith
  have hu : ∀ t : ℝ, 0 ≤ (u.1 * x0.1 + u.2 * x0.2) + t * (a.1 * u.2 - a.2 * u.1) := by
    intro t
    have := (hsub (hline t)).1
    calc (0 : ℝ) ≤ u.1 * (x0.1 - t * a.2) + u.2 * (x0.2 + t * a.1) := this
    _ = (u.1 * x0.1 + u.2 * x0.2) + t * (a.1 * u.2 - a.2 * u.1) := by ring
  have hv : ∀ t : ℝ, 0 ≤ (v.1 * x0.1 + v.2 * x0.2) + t * (a.1 * v.2 - a.2 * v.1) := by
    intro t
    have := (hsub (hline t)).2
    calc (0 : ℝ) ≤ v.1 * (x0.1 - t * a.2) + v.2 * (x0.2 + t * a.1) := this
    _ = (v.1 * x0.1 + v.2 * x0.2) + t * (a.1 * v.2 - a.2 * v.1) := by ring
  have key : ∀ (A B : ℝ), (∀ t : ℝ, 0 ≤ A + t * B) → B = 0 := by
    intro A B hAB
    by_contra hB
    have := hAB (-(A + 1) / B)
    rw [div_mul_cancel₀ _ hB] at this
    linarith
  have hdu : det a u = 0 := by
    have := key _ _ hu
    simpa [det] using this
  have hdv : det a v = 0 := by
    have := key _ _ hv
    simpa [det] using this
  apply ha
  have e1 : det u v * a.1 = det a v * u.1 - det a u * v.1 := by simp only [det]; ring
  have e2 : det u v * a.2 = det a v * u.2 - det a u * v.2 := by simp only [det]; ring
  rw [hdu, hdv] at e1 e2
  simp only [zero_mul, sub_zero] at e1 e2
  exact Prod.ext ((mul_eq_zero.mp e1).resolve_left huv) ((mul_eq_zero.mp e2).resolve_left huv)

lemma no_halfplane : ∀ Z, IsZone Rays Z →
    ¬ ∃ (a : V) (c : ℝ), a ≠ 0 ∧ {x : V | c < a.1 * x.1 + a.2 * x.2} ⊆ Z := by
  rintro Z hZ ⟨a, c, ha, hsub⟩
  rcases zone_eq hZ with rfl | rfl | rfl
  · refine no_halfplane_subset_cone (u := (1, 0)) (v := (0, 1)) (c := c) (by norm_num [det]) ha ?_
    intro x hx
    obtain ⟨p1, p2⟩ := hsub hx
    exact ⟨by simp only; linarith, by simp only; linarith⟩
  · refine no_halfplane_subset_cone (u := (-1, 0)) (v := (-1, 1)) (c := c) (by norm_num [det]) ha ?_
    intro x hx
    obtain ⟨p1, p2⟩ := hsub hx
    exact ⟨by simp only; linarith, by simp only; linarith⟩
  · refine no_halfplane_subset_cone (u := (0, -1)) (v := (1, -1)) (c := c) (by norm_num [det]) ha ?_
    intro x hx
    obtain ⟨p1, p2⟩ := hsub hx
    exact ⟨by simp only; linarith, by simp only; linarith⟩

/-! ### The triangle -/

/-- The three vertices, as a function of the index modulo `3`. -/
def vtx (r : ℤ) : V := if r = 0 then (0, 0) else if r = 1 then (1, 1) else (-2, 2)

/-- The `3`-periodic vertex sequence. -/
def A (k : ℤ) : V := vtx (k % 3)

/-- The side-vector points. -/
def M (k : ℤ) : V := A (k + 1) - A k

lemma A_periodic (t : ℤ) : A (t + (3 : ℕ)) = A t := by
  have h : (t + (3 : ℕ)) % 3 = t % 3 := by push_cast; omega
  simp only [A, h]

lemma A_val (k : ℤ) :
    (k % 3 = 0 ∧ A k = (0, 0)) ∨ (k % 3 = 1 ∧ A k = (1, 1)) ∨ (k % 3 = 2 ∧ A k = (-2, 2)) := by
  have h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h with h | h | h
  · exact Or.inl ⟨h, by simp [A, h, vtx]⟩
  · exact Or.inr (Or.inl ⟨h, by simp [A, h, vtx]⟩)
  · refine Or.inr (Or.inr ⟨h, ?_⟩)
    simp only [A, h, vtx]
    norm_num

lemma A_of_mod {k : ℤ} (h : k % 3 = 0) : A k = (0, 0) := by simp [A, h, vtx]
lemma A_of_mod1 {k : ℤ} (h : k % 3 = 1) : A k = (1, 1) := by simp [A, h, vtx]
lemma A_of_mod2 {k : ℤ} (h : k % 3 = 2) : A k = (-2, 2) := by
  simp only [A, h, vtx]; norm_num

lemma A_congr {k l : ℤ} (h : k % 3 = l % 3) : A k = A l := by simp only [A, h]

lemma det_hyp (k l : ℤ) (h1 : ¬ ((3 : ℕ) : ℤ) ∣ (l - k)) (h2 : ¬ ((3 : ℕ) : ℤ) ∣ (l - (k + 1))) :
    0 < det (A (k + 1) - A k) (A l - A k) := by
  push_cast at h1 h2
  have hl : l % 3 = (k + 2) % 3 := by omega
  rw [A_congr hl]
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with h | h | h
  · rw [A_of_mod h, A_of_mod1 (by omega : (k + 1) % 3 = 1), A_of_mod2 (by omega : (k + 2) % 3 = 2)]
    norm_num [det]
  · rw [A_of_mod1 h, A_of_mod2 (by omega : (k + 1) % 3 = 2), A_of_mod (by omega : (k + 2) % 3 = 0)]
    norm_num [det]
  · rw [A_of_mod2 h, A_of_mod (by omega : (k + 1) % 3 = 0), A_of_mod1 (by omega : (k + 2) % 3 = 1)]
    norm_num [det]

lemma M_val (k : ℤ) :
    (k % 3 = 0 ∧ M k = (1, 1)) ∨ (k % 3 = 1 ∧ M k = (-3, 1)) ∨ (k % 3 = 2 ∧ M k = (2, -2)) := by
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with h | h | h
  · refine Or.inl ⟨h, ?_⟩
    simp only [M, A_of_mod h, A_of_mod1 (by omega : (k + 1) % 3 = 1)]
    norm_num [Prod.ext_iff]
  · refine Or.inr (Or.inl ⟨h, ?_⟩)
    simp only [M, A_of_mod1 h, A_of_mod2 (by omega : (k + 1) % 3 = 2)]
    norm_num [Prod.ext_iff]
  · refine Or.inr (Or.inr ⟨h, ?_⟩)
    simp only [M, A_of_mod2 h, A_of_mod (by omega : (k + 1) % 3 = 0)]
    norm_num [Prod.ext_iff]

lemma separation (k : ℤ) : ∀ Z, IsZone Rays Z → ¬ (M k ∈ closure Z ∧ M (k + 1) ∈ closure Z) := by
  rintro Z hZ ⟨hk, hk1⟩
  have hMk := M_val k
  have hMk1 := M_val (k + 1)
  rcases zone_eq hZ with rfl | rfl | rfl
  · have c1 := closure_S0 hk
    have c2 := closure_S0 hk1
    simp only [mem_setOf_eq] at c1 c2
    rcases hMk with ⟨h, hv⟩ | ⟨h, hv⟩ | ⟨h, hv⟩ <;>
      rcases hMk1 with ⟨h', hv'⟩ | ⟨h', hv'⟩ | ⟨h', hv'⟩ <;>
      rw [hv] at c1 <;> rw [hv'] at c2 <;> first | omega | (norm_num at c1; done) | (norm_num at c2; done)
  · have c1 := closure_S1 hk
    have c2 := closure_S1 hk1
    simp only [mem_setOf_eq] at c1 c2
    rcases hMk with ⟨h, hv⟩ | ⟨h, hv⟩ | ⟨h, hv⟩ <;>
      rcases hMk1 with ⟨h', hv'⟩ | ⟨h', hv'⟩ | ⟨h', hv'⟩ <;>
      rw [hv] at c1 <;> rw [hv'] at c2 <;> first | omega | (norm_num at c1; done) | (norm_num at c2; done)
  · have c1 := closure_S2 hk
    have c2 := closure_S2 hk1
    simp only [mem_setOf_eq] at c1 c2
    rcases hMk with ⟨h, hv⟩ | ⟨h, hv⟩ | ⟨h, hv⟩ <;>
      rcases hMk1 with ⟨h', hv'⟩ | ⟨h', hv'⟩ | ⟨h', hv'⟩ <;>
      rw [hv] at c1 <;> rw [hv'] at c2 <;> first | omega | (norm_num at c1; done) | (norm_num at c2; done)

lemma rays_injective : Function.Injective Rays := by
  intro i j hij
  rw [Set.ext_iff] at hij
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals
    exfalso
    first
    | (have h := hij ((1 : ℝ), (0 : ℝ)); simp [Rays, ray, d0, d1, d2, Prod.ext_iff] at h; done)
    | (have h := hij ((0 : ℝ), (1 : ℝ)); simp [Rays, ray, d0, d1, d2, Prod.ext_iff] at h; done)

/-- Every hypothesis of `Q896.q896` is satisfiable: three rays and a triangle, with `n = p = 3`,
so the bound `p ≤ n` is attained. -/
theorem admissible_configuration :
    (0 < 3) ∧ (0 < 3) ∧
    (∀ j, ∃ v : V, v ≠ 0 ∧ Rays j = ray v) ∧
    Function.Injective Rays ∧
    (∀ t : ℤ, A (t + ((3 : ℕ) : ℤ)) = A t) ∧
    (∀ k : ℤ, M k - (0 : V) = A (k + 1) - A k) ∧
    (∀ k l : ℤ, ¬ (((3 : ℕ) : ℤ) ∣ (l - k)) → ¬ (((3 : ℕ) : ℤ) ∣ (l - (k + 1))) →
      0 < det (A (k + 1) - A k) (A l - A k)) ∧
    (∀ Z, IsZone Rays Z →
      ¬ ∃ (a : V) (c : ℝ), a ≠ 0 ∧ {x : V | c < a.1 * x.1 + a.2 * x.2} ⊆ Z) ∧
    (∀ k : ℤ, ∀ Z, IsZone Rays Z → ¬ (M k ∈ closure Z ∧ M (k + 1) ∈ closure Z)) := by
  refine ⟨by norm_num, by norm_num, ?_, rays_injective, A_periodic, fun k => by simp [M],
    det_hyp, no_halfplane, separation⟩
  intro j
  fin_cases j
  · exact ⟨d0, by simp [d0, Prod.ext_iff], rfl⟩
  · exact ⟨d1, by simp [d1, Prod.ext_iff], rfl⟩
  · exact ⟨d2, by simp [d2, Prod.ext_iff], rfl⟩

/-- The main theorem applied to this configuration: the bound `p ≤ n` holds, and here it is an
equality, `p = n = 3`. -/
theorem q896_applied : (3 : ℕ) ≤ 3 := by
  obtain ⟨hn, hp, hR, hRinj, hper, hM, hdet, hhalf, hsep⟩ := admissible_configuration
  exact q896 hn hp Rays hR hRinj A hper M hM hdet hhalf hsep

end Ex

end Q896
