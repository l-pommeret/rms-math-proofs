import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Q896

From a point `O`, draw `n` distinct rays in an oriented affine plane.  Their complement has `n`
connected components `Z_1, …, Z_n`, called *zones*, and no zone contains an open half-plane.
A *direct convex polygonal line with `p` sides* is a `p`-periodic sequence `(A_t)_{t ∈ ℤ}` such
that
`det (A_(k+1) - A_k) (A_l - A_k) > 0` whenever `l ≢ k, k+1 [ZMOD p]`.
Define `M_k` by `OM_k = A_k A_(k+1)`.  Assume that no zone `Z_j` has both `M_k` and `M_(k+1)` in
its closure.  Then `p ≤ n`.

The oriented affine plane is identified with `V = ℝ × ℝ`, with `O` translated to `0`.
-/

namespace Q896

open Set Filter Topology

/-- The oriented affine plane, with the origin `O` translated to `0`. -/
abbrev V := ℝ × ℝ

/-- The determinant of two vectors of the oriented plane. -/
def det (u v : V) : ℝ := u.1 * v.2 - u.2 * v.1

/-- The (closed) ray issued from the origin `O = 0` with direction `v`. -/
def ray (v : V) : Set V := {x : V | ∃ t : ℝ, 0 ≤ t ∧ x = t • v}

/-- `Z` is a zone of the ray system `R`: a connected component of the complement of the union
of the rays. -/
def IsZone {n : ℕ} (R : Fin n → Set V) (Z : Set V) : Prop :=
  ∃ x ∈ (⋃ j, R j)ᶜ, Z = connectedComponentIn ((⋃ j, R j)ᶜ) x

/-! ### Elementary determinant algebra -/

@[simp] lemma det_self (u : V) : det u u = 0 := by simp only [det]; ring

lemma det_skew (u v : V) : det u v = - det v u := by simp only [det]; ring

@[simp] lemma det_zero_right (u : V) : det u 0 = 0 := by simp [det]

@[simp] lemma det_zero_left (u : V) : det 0 u = 0 := by simp [det]

lemma det_smul_right (u v : V) (t : ℝ) : det u (t • v) = t * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

lemma det_smul_left (u v : V) (t : ℝ) : det (t • u) v = t * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

lemma det_add_right (u v w : V) : det u (v + w) = det u v + det u w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

lemma det_add_left (u v w : V) : det (u + v) w = det u w + det v w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

lemma det_sub_right (u v w : V) : det u (v - w) = det u v - det u w := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

lemma det_sub_left (u v w : V) : det (u - v) w = det u w - det v w := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

lemma det_neg_right (u v : V) : det u (-v) = - det u v := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

lemma det_neg_left (u v : V) : det (-u) v = - det u v := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

lemma exists_det_pos {v : V} (hv : v ≠ 0) : ∃ w : V, 0 < det v w := by
  refine ⟨(-v.2, v.1), ?_⟩
  simp only [det]
  have : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (Prod.ext h.1 h.2)
  rcases this with h | h
  · nlinarith [mul_self_pos.mpr h, mul_self_nonneg v.2]
  · nlinarith [mul_self_pos.mpr h, mul_self_nonneg v.1]

lemma convex_det_pos (e : V) : Convex ℝ {w : V | 0 < det e w} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq, det_add_right, det_smul_right] at *
  rcases eq_or_lt_of_le ha with h | h
  · have hb1 : b = 1 := by linarith
    subst hb1; nlinarith
  · nlinarith

/-- The key planar-cone estimate: if `(b, a)` is a direct basis, `w` is a nonzero vector of the
closed convex cone spanned by `a` and `b`, and `v` is strictly to the right of both `a` and `b`,
then `v` is strictly to the right of `w`. -/
lemma det_pos_of_cone {a b v w : V} (hba : 0 < det b a) (hbw : 0 ≤ det b w)
    (hwa : 0 ≤ det w a) (hva : 0 < det v a) (hvb : 0 < det v b) (hw : w ≠ 0) :
    0 < det v w := by
  have key : det b a * det v w = det b w * det v a + det w a * det v b := by
    simp only [det]; ring
  have hpos : 0 < det b w * det v a + det w a * det v b := by
    rcases eq_or_lt_of_le hbw with h1 | h1
    · rcases eq_or_lt_of_le hwa with h2 | h2
      · exfalso
        apply hw
        have e1 : det b a * w.1 = 0 := by
          have h : det b a * w.1 = det b w * a.1 + det w a * b.1 := by simp only [det]; ring
          rw [h, ← h1, ← h2]; ring
        have e2 : det b a * w.2 = 0 := by
          have h : det b a * w.2 = det b w * a.2 + det w a * b.2 := by simp only [det]; ring
          rw [h, ← h1, ← h2]; ring
        exact Prod.ext ((mul_eq_zero.mp e1).resolve_left hba.ne')
          ((mul_eq_zero.mp e2).resolve_left hba.ne')
      · nlinarith [mul_nonneg hbw hva.le, mul_pos h2 hvb]
    · nlinarith [mul_nonneg hwa hvb.le, mul_pos h1 hva]
  nlinarith

/-! ### Producing zones out of convex subsets of the complement -/

lemma mem_closure_of_shift {S : Set V} {x w : V} (h : ∀ t : ℝ, 0 < t → x + t • w ∈ S) :
    x ∈ closure S := by
  refine mem_closure_of_tendsto (f := fun m : ℕ => x + (1 / ((m : ℝ) + 1)) • w) (b := atTop) ?_ ?_
  · have h0 : Tendsto (fun m : ℕ => (1 / ((m : ℝ) + 1))) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (h0.smul_const w).const_add x
  · filter_upwards with m
    exact h _ (by positivity)

/-- A nonempty convex subset of the complement of the rays is contained in a single zone, so any
two points adherent to it are adherent to a common zone. -/
lemma exists_zone_closure {n : ℕ} (R : Fin n → Set V) {S : Set V}
    (hconv : Convex ℝ S) (hne : S.Nonempty) (hsub : S ⊆ (⋃ j, R j)ᶜ)
    {x y : V} (hx : x ∈ closure S) (hy : y ∈ closure S) :
    ∃ Z, IsZone R Z ∧ x ∈ closure Z ∧ y ∈ closure Z := by
  obtain ⟨z, hz⟩ := hne
  have hZ : S ⊆ connectedComponentIn ((⋃ j, R j)ᶜ) z :=
    hconv.isPreconnected.subset_connectedComponentIn hz hsub
  exact ⟨_, ⟨z, hsub hz, rfl⟩, closure_mono hZ hx, closure_mono hZ hy⟩

/-- If an open half-plane avoids all rays, then its boundary line is adherent to a single zone. -/
lemma halfplane_zone {n : ℕ} (R : Fin n → Set V) {e x y : V} (he : e ≠ 0)
    (hsub : {w : V | 0 < det e w} ⊆ (⋃ j, R j)ᶜ)
    (hx : det e x = 0) (hy : det e y = 0) :
    ∃ Z, IsZone R Z ∧ x ∈ closure Z ∧ y ∈ closure Z := by
  obtain ⟨w₀, hw₀⟩ := exists_det_pos he
  refine exists_zone_closure R (convex_det_pos e) ⟨w₀, hw₀⟩ hsub ?_ ?_
  · refine mem_closure_of_shift (w := w₀) fun t ht => ?_
    simp only [mem_setOf_eq, det_add_right, det_smul_right, hx, zero_add]
    exact mul_pos ht hw₀
  · refine mem_closure_of_shift (w := w₀) fun t ht => ?_
    simp only [mem_setOf_eq, det_add_right, det_smul_right, hy, zero_add]
    exact mul_pos ht hw₀

/-! ### The direct convex polygonal line -/

/-- The `k`-th side vector `A_k A_(k+1)`. -/
def edge (A : ℤ → V) (k : ℤ) : V := A (k + 1) - A k

/-- The open turning arc-cone at the `k`-th vertex: the set of vectors strictly between the
side directions `e_k` and `e_(k+1)` in the positive sense. -/
def arcCone (A : ℤ → V) (k : ℤ) : Set V :=
  {w : V | 0 < det (edge A k) w ∧ 0 < det w (edge A (k + 1))}

lemma convex_arcCone (A : ℤ → V) (k : ℤ) : Convex ℝ (arcCone A k) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hab' : 0 < a ∨ 0 < b := by
    rcases eq_or_lt_of_le ha with h | h
    · right; linarith
    · left; exact h
  constructor <;>
    simp only [det_add_right, det_add_left, det_smul_right,
      det_smul_left] at * <;>
    rcases hab' with h | h <;> nlinarith

section Periodic

variable {p : ℕ} {A : ℤ → V}

lemma A_add_mul (hper : ∀ t : ℤ, A (t + (p : ℤ)) = A t) (k : ℤ) : ∀ m : ℤ, A (k + m * p) = A k := by
  intro m
  induction m using Int.induction_on with
  | zero => simp
  | succ i ih =>
      have h : k + ((i : ℤ) + 1) * p = (k + (i : ℤ) * p) + p := by ring
      rw [h, hper, ih]
  | pred i ih =>
      have h : k + (-(i : ℤ) - 1) * p + p = k + (-(i : ℤ)) * p := by ring
      have h2 := hper (k + (-(i : ℤ) - 1) * p)
      rw [h] at h2
      rw [← h2, ih]

lemma A_eq_of_dvd (hper : ∀ t : ℤ, A (t + (p : ℤ)) = A t) {k l : ℤ} (h : (p : ℤ) ∣ (l - k)) :
    A l = A k := by
  obtain ⟨m, hm⟩ := h
  have : l = k + m * p := by linarith [hm]
  rw [this, A_add_mul hper]

lemma edge_eq_of_dvd (hper : ∀ t : ℤ, A (t + (p : ℤ)) = A t) {k l : ℤ} (h : (p : ℤ) ∣ (l - k)) :
    edge A l = edge A k := by
  have h1 : A l = A k := A_eq_of_dvd hper h
  have h2 : A (l + 1) = A (k + 1) := A_eq_of_dvd hper (by simpa using h)
  simp [edge, h1, h2]

/-- Congruence of indices modulo `p` is exactly equality of the `ZMod p` classes. -/
lemma dvd_sub_iff_cast_eq {k l : ℤ} : ((p : ℤ) ∣ (l - k)) ↔ ((k : ZMod p) = (l : ZMod p)) := by
  rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]

/-- The printed `p`-periodic convention for the vertex sequence is equivalent to the data of a
cyclic `ZMod p` family of vertices. -/
lemma periodic_iff_zmod :
    (∀ t : ℤ, A (t + (p : ℤ)) = A t) ↔ ∃ A' : ZMod p → V, ∀ k : ℤ, A k = A' ((k : ℤ) : ZMod p) := by
  classical
  constructor
  · intro hper
    refine ⟨fun z => A (Classical.choose (ZMod.intCast_surjective z)), fun k => ?_⟩
    have hK : ((Classical.choose (ZMod.intCast_surjective ((k : ZMod p))) : ℤ) : ZMod p)
        = (k : ZMod p) := Classical.choose_spec (ZMod.intCast_surjective ((k : ZMod p)))
    exact (A_eq_of_dvd hper (dvd_sub_iff_cast_eq.mpr hK.symm)).symm
  · rintro ⟨A', hA'⟩ t
    rw [hA' (t + (p : ℤ)), hA' t]
    congr 1
    push_cast
    simp

/-- The wraparound edge: the last side joins `A_(p-1)` to `A_0`. -/
lemma edge_wraparound (hper : ∀ t : ℤ, A (t + (p : ℤ)) = A t) :
    edge A ((p : ℤ) - 1) = A 0 - A ((p : ℤ) - 1) := by
  have h : A ((p : ℤ) - 1 + 1) = A 0 := by
    have := hper 0
    simpa using this
  simp only [edge, h]

/-- The printed global convexity hypothesis, read with indices modulo `p`, is equivalent to the
same inequalities for the cyclic `ZMod p` family of vertices. -/
lemma det_hyp_iff_zmod (A' : ZMod p → V) (hA' : ∀ k : ℤ, A k = A' ((k : ℤ) : ZMod p)) :
    (∀ k l : ℤ, ¬ ((p : ℤ) ∣ (l - k)) → ¬ ((p : ℤ) ∣ (l - (k + 1))) →
        0 < det (A (k + 1) - A k) (A l - A k))
      ↔ (∀ k l : ZMod p, l ≠ k → l ≠ k + 1 →
        0 < det (A' (k + 1) - A' k) (A' l - A' k)) := by
  constructor
  · intro h k l hne1 hne2
    obtain ⟨K, hK⟩ := ZMod.intCast_surjective (n := p) k
    obtain ⟨L, hL⟩ := ZMod.intCast_surjective (n := p) l
    have hAK : A' k = A K := by rw [hA' K, hK]
    have hAK1 : A' (k + 1) = A (K + 1) := by
      rw [hA' (K + 1)]
      push_cast
      rw [hK]
    have hAL : A' l = A L := by rw [hA' L, hL]
    have h1 : ¬ ((p : ℤ) ∣ (L - K)) := by
      rw [dvd_sub_iff_cast_eq, hK, hL]
      exact fun hc => hne1 hc.symm
    have h2 : ¬ ((p : ℤ) ∣ (L - (K + 1))) := by
      rw [dvd_sub_iff_cast_eq]
      push_cast
      rw [hK, hL]
      exact fun hc => hne2 hc.symm
    rw [hAK, hAK1, hAL]
    exact h K L h1 h2
  · intro h k l h1 h2
    have hne1 : ((l : ZMod p)) ≠ ((k : ZMod p)) := fun hc => h1 (dvd_sub_iff_cast_eq.mpr hc.symm)
    have hne2 : ((l : ZMod p)) ≠ ((k : ZMod p)) + 1 := by
      intro hc
      apply h2
      rw [dvd_sub_iff_cast_eq]
      push_cast
      exact hc.symm
    have := h ((k : ZMod p)) ((l : ZMod p)) hne1 hne2
    rw [← hA' k, ← hA' l] at this
    rw [show (((k : ℤ) : ZMod p) + 1) = (((k + 1 : ℤ)) : ZMod p) by push_cast; ring,
      ← hA' (k + 1)] at this
    exact this

variable (hper : ∀ t : ℤ, A (t + (p : ℤ)) = A t) (hp3 : 3 ≤ p)
  (hdet : ∀ k l : ℤ, ¬ ((p : ℤ) ∣ (l - k)) → ¬ ((p : ℤ) ∣ (l - (k + 1))) →
    0 < det (A (k + 1) - A k) (A l - A k))

include hp3 in
lemma not_dvd_one : ¬ ((p : ℤ) ∣ (1 : ℤ)) := by
  intro h
  have := Int.le_of_dvd (by norm_num) h
  omega

include hp3 in
lemma not_dvd_two : ¬ ((p : ℤ) ∣ (2 : ℤ)) := by
  intro h
  have := Int.le_of_dvd (by norm_num) h
  omega

include hp3 hdet in
lemma edge_ne_zero (k : ℤ) : edge A k ≠ 0 := by
  intro h
  have h1 : ¬ ((p : ℤ) ∣ ((k + 2) - k)) := by simpa using not_dvd_two hp3
  have h2 : ¬ ((p : ℤ) ∣ ((k + 2) - (k + 1))) := by simpa using not_dvd_one hp3
  have hpos := hdet k (k + 2) h1 h2
  rw [show A (k + 1) - A k = edge A k from rfl, h] at hpos
  simp at hpos

include hper hp3 hdet in
lemma A_ne_of_not_dvd {j k : ℤ} (h : ¬ ((p : ℤ) ∣ (j - k))) : A j ≠ A k := by
  intro heq
  by_cases h1 : (p : ℤ) ∣ (j - (k + 1))
  · have hj : A j = A (k + 1) := A_eq_of_dvd hper h1
    have : edge A k = 0 := by simp [edge, ← hj, heq]
    exact edge_ne_zero hp3 hdet k this
  · have hpos := hdet k j h h1
    rw [heq] at hpos
    simp at hpos

include hp3 hdet in
/-- Successive side vectors turn strictly to the left. -/
lemma det_edge_edge_pos (k : ℤ) : 0 < det (edge A k) (edge A (k + 1)) := by
  have h1 : ¬ ((p : ℤ) ∣ ((k + 2) - k)) := by simpa using not_dvd_two hp3
  have h2 : ¬ ((p : ℤ) ∣ ((k + 2) - (k + 1))) := by simpa using not_dvd_one hp3
  have hpos := hdet k (k + 2) h1 h2
  have hsplit : A (k + 2) - A k = edge A k + edge A (k + 1) := by
    simp only [edge]
    have : k + 1 + 1 = k + 2 := by ring
    rw [this]
    abel
  rw [show A (k + 1) - A k = edge A k from rfl, hsplit, det_add_right, det_self,
    zero_add] at hpos
  exact hpos

include hper hp3 hdet in
/-- If `v` lies in the open turning arc-cone at the `k`-th vertex, then the vertex `A_(k+1)` is
the unique strict minimum of the linear form `X ↦ det v X` over the vertices. -/
lemma det_pos_of_mem_arcCone {k : ℤ} {v : V} (hv : v ∈ arcCone A k) {j : ℤ}
    (hj : ¬ ((p : ℤ) ∣ (j - (k + 1)))) : 0 < det v (A j - A (k + 1)) := by
  obtain ⟨hv1, hv2⟩ := hv
  set a : V := A k - A (k + 1) with ha
  set b : V := edge A (k + 1) with hb
  set w : V := A j - A (k + 1) with hw
  have haa : a = -(edge A k) := by simp [ha, edge]
  have hba : 0 < det b a := by
    rw [haa, det_neg_right, hb, det_skew (edge A (k+1)) (edge A k), neg_neg]
    exact det_edge_edge_pos hp3 hdet k
  have hbw : 0 ≤ det b w := by
    by_cases hc : (p : ℤ) ∣ (j - (k + 2))
    · have hj2 : A j = A (k + 2) := A_eq_of_dvd hper hc
      have : w = b := by
        simp only [hw, hj2, hb, edge]
        have : k + 1 + 1 = k + 2 := by ring
        rw [this]
      rw [this]
      simp
    · have h1 : ¬ ((p : ℤ) ∣ (j - (k + 1))) := hj
      have h2 : ¬ ((p : ℤ) ∣ (j - (k + 1 + 1))) := by
        intro hcon; exact hc (by rw [show j - (k+2) = j - (k+1+1) by ring]; exact hcon)
      have := hdet (k + 1) j h1 h2
      exact le_of_lt this
  have hwa : 0 ≤ det w a := by
    have hkey : det w a = det (edge A k) (A j - A (k + 1)) := by
      rw [haa, hw]
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg, edge]
      ring
    rw [hkey]
    have hsplit : A j - A (k + 1) = (A j - A k) - edge A k := by simp only [edge]; abel
    rw [hsplit, det_sub_right, det_self, sub_zero]
    by_cases hc : (p : ℤ) ∣ (j - k)
    · have hj2 : A j = A k := A_eq_of_dvd hper hc
      rw [hj2]; simp
    · exact le_of_lt (hdet k j hc hj)
  have hva : 0 < det v a := by
    rw [haa, det_neg_right, det_skew v (edge A k), neg_neg]
    exact hv1
  have hvb : 0 < det v b := hv2
  have hwne : w ≠ 0 := by
    have := A_ne_of_not_dvd hper hp3 hdet hj
    simpa [hw, sub_eq_zero] using this
  exact det_pos_of_cone hba hbw hwa hva hvb hwne

include hper hp3 hdet in
/-- The open turning arc-cones are pairwise disjoint modulo `p`. -/
lemma arcCone_unique {k l : ℤ} {v : V} (hk : v ∈ arcCone A k) (hl : v ∈ arcCone A l) :
    (p : ℤ) ∣ (l - k) := by
  by_contra hcon
  have h1 : ¬ ((p : ℤ) ∣ ((l + 1) - (k + 1))) := by
    intro h; exact hcon (by simpa using h)
  have h2 : ¬ ((p : ℤ) ∣ ((k + 1) - (l + 1))) := by
    intro h; exact hcon (by
      have := Dvd.dvd.neg_right h
      simpa [neg_sub] using (dvd_neg.mpr h))
  have p1 := det_pos_of_mem_arcCone hper hp3 hdet hk h1
  have p2 := det_pos_of_mem_arcCone hper hp3 hdet hl h2
  have : det v (A (l + 1) - A (k + 1)) + det v (A (k + 1) - A (l + 1)) = 0 := by
    simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
  linarith

end Periodic

/-! ### Arc-cones, rays and the final count -/

lemma arcCone_mem_of_turn {A : ℤ → V} {k : ℤ}
    (hturn : 0 < det (edge A k) (edge A (k + 1))) :
    (edge A k + edge A (k + 1)) ∈ arcCone A k := by
  constructor
  · rw [det_add_right, det_self, zero_add]; exact hturn
  · rw [det_add_left, det_self, add_zero]; exact hturn

lemma edge_mem_closure_arcCone {A : ℤ → V} {k : ℤ}
    (hturn : 0 < det (edge A k) (edge A (k + 1))) :
    edge A k ∈ closure (arcCone A k) := by
  refine mem_closure_of_shift (w := edge A k + edge A (k + 1)) fun t ht => ?_
  constructor
  · rw [det_add_right, det_self, zero_add, det_smul_right, det_add_right, det_self, zero_add]
    exact mul_pos ht hturn
  · rw [det_add_left, det_smul_left, det_add_left, det_self, add_zero]
    nlinarith

lemma edge_succ_mem_closure_arcCone {A : ℤ → V} {k : ℤ}
    (hturn : 0 < det (edge A k) (edge A (k + 1))) :
    edge A (k + 1) ∈ closure (arcCone A k) := by
  refine mem_closure_of_shift (w := edge A k + edge A (k + 1)) fun t ht => ?_
  constructor
  · rw [det_add_right, det_smul_right, det_add_right, det_self, zero_add]
    nlinarith
  · rw [det_add_left, det_self, zero_add, det_smul_left, det_add_left, det_self, add_zero]
    exact mul_pos ht hturn

/-- An open turning arc-cone containing no prescribed ray direction avoids the union of the
rays. -/
lemma arcCone_subset_compl {n : ℕ} {R : Fin n → Set V} {dir : Fin n → V}
    (hRay : ∀ j, R j = ray (dir j)) {A : ℤ → V} {k : ℤ}
    (havoid : ∀ j, dir j ∉ arcCone A k) : arcCone A k ⊆ (⋃ j, R j)ᶜ := by
  intro w hw
  simp only [mem_compl_iff, mem_iUnion, not_exists]
  intro j hj
  rw [hRay j] at hj
  obtain ⟨t, ht, rfl⟩ := hj
  obtain ⟨h1, h2⟩ := hw
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h] at h1
    simp at h1
  · refine havoid j ⟨?_, ?_⟩
    · rw [det_smul_right] at h1; nlinarith
    · rw [det_smul_left] at h2; nlinarith

/-- An open half-plane containing no prescribed ray direction on its positive side gives a zone
adherent to every point of its boundary line. -/
lemma zone_of_avoiding_halfplane {n : ℕ} {R : Fin n → Set V} {dir : Fin n → V}
    (hRay : ∀ j, R j = ray (dir j)) {e : V} (he : e ≠ 0)
    (havoid : ∀ j, det e (dir j) ≤ 0) {x y : V} (hx : det e x = 0) (hy : det e y = 0) :
    ∃ Z, IsZone R Z ∧ x ∈ closure Z ∧ y ∈ closure Z := by
  refine halfplane_zone R he ?_ hx hy
  intro w hw
  simp only [mem_compl_iff, mem_iUnion, not_exists]
  intro j hj
  rw [hRay j] at hj
  obtain ⟨t, ht, rfl⟩ := hj
  simp only [mem_setOf_eq, det_smul_right] at hw
  nlinarith [havoid j]

/-!
### The main theorem

`O` is the origin `0` of `V = ℝ × ℝ`.  The data are:

* `R j`, `j : Fin n`, the `n` pairwise distinct rays issued from `O` (`hR`, `hRinj`);
* `A : ℤ → V`, the `p`-periodic vertex sequence (`hper`) of a direct convex polygonal line
  with `p` sides (`hdet`);
* `M : ℤ → V`, the points defined by `OM_k = A_k A_(k+1)` (`hM`);
* `hhalf`: no zone contains an open half-plane;
* `hsep`: no zone has both `M_k` and `M_(k+1)` in its closure.

The conclusion is `p ≤ n`.
-/
theorem q896 {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (R : Fin n → Set V) (hR : ∀ j, ∃ v : V, v ≠ 0 ∧ R j = ray v)
    (hRinj : Function.Injective R)
    (A : ℤ → V) (hper : ∀ t : ℤ, A (t + (p : ℤ)) = A t)
    (M : ℤ → V) (hM : ∀ k : ℤ, M k - (0 : V) = A (k + 1) - A k)
    (hdet : ∀ k l : ℤ, ¬ ((p : ℤ) ∣ (l - k)) → ¬ ((p : ℤ) ∣ (l - (k + 1))) →
      0 < det (A (k + 1) - A k) (A l - A k))
    (hhalf : ∀ Z, IsZone R Z →
      ¬ ∃ (a : V) (c : ℝ), a ≠ 0 ∧ {x : V | c < a.1 * x.1 + a.2 * x.2} ⊆ Z)
    (hsep : ∀ k : ℤ, ∀ Z, IsZone R Z → ¬ (M k ∈ closure Z ∧ M (k + 1) ∈ closure Z)) :
    p ≤ n := by
  have hMe : ∀ k : ℤ, M k = edge A k := by
    intro k
    have h := hM k
    simpa [edge, sub_zero] using h
  choose dir hdirne hRay using hR
  rcases lt_or_ge p 3 with hlt | hp3
  · -- the degenerate periods `p = 1` and `p = 2`
    interval_cases p
    · exact hn
    · -- `p = 2` : the two side vectors are opposite, and a single ray cannot separate them
      by_contra hcon
      push_neg at hcon
      have hn1 : n = 1 := by omega
      subst hn1
      have hA2 : A 2 = A 0 := by
        have := hper 0
        norm_num at this
        exact this
      have hM0 : M 0 = A 1 - A 0 := by simpa [edge] using hMe 0
      have hM1 : M 1 = -(A 1 - A 0) := by
        have h := hMe 1
        rw [h]
        simp only [edge]
        norm_num [hA2]
      set e0 : V := A 1 - A 0 with he0
      set v : V := dir 0 with hv
      have hvne : v ≠ 0 := hdirne 0
      obtain ⟨Z, hZ, h1, h2⟩ : ∃ Z, IsZone R Z ∧ M 0 ∈ closure Z ∧ M 1 ∈ closure Z := by
        by_cases hz : e0 = 0
        · refine zone_of_avoiding_halfplane hRay hvne (fun j => ?_) ?_ ?_
          · have : dir j = v := by
              have : j = 0 := Subsingleton.elim _ _
              rw [this]
            rw [this]
            simp
          · rw [hM0, hz]; simp
          · rw [hM1, hz]; simp
        · by_cases hs : det e0 v ≤ 0
          · refine zone_of_avoiding_halfplane hRay hz (fun j => ?_) ?_ ?_
            · have : dir j = v := by
                have : j = 0 := Subsingleton.elim _ _
                rw [this]
              rw [this]; exact hs
            · rw [hM0]; simp
            · rw [hM1, det_neg_right]; simp
          · push_neg at hs
            have hz' : -e0 ≠ 0 := by simpa using hz
            refine zone_of_avoiding_halfplane hRay hz' (fun j => ?_) ?_ ?_
            · have : dir j = v := by
                have : j = 0 := Subsingleton.elim _ _
                rw [this]
              rw [this, det_neg_left]
              linarith
            · rw [hM0, det_neg_left]; simp
            · rw [hM1, det_neg_left, det_neg_right]; simp
      exact hsep 0 Z hZ ⟨h1, by simpa using h2⟩
  · -- the main case `p ≥ 3`
    have harc : ∀ k : ℤ, ∃ j : Fin n, dir j ∈ arcCone A k := by
      intro k
      by_contra hc
      push_neg at hc
      have hturn := det_edge_edge_pos hp3 hdet k
      obtain ⟨Z, hZ, h1, h2⟩ := exists_zone_closure R (convex_arcCone A k)
        ⟨_, arcCone_mem_of_turn hturn⟩ (arcCone_subset_compl hRay hc)
        (edge_mem_closure_arcCone hturn) (edge_succ_mem_closure_arcCone hturn)
      exact hsep k Z hZ ⟨by rw [hMe k]; exact h1, by rw [hMe (k + 1)]; exact h2⟩
    choose f hf using harc
    have hinj : Function.Injective (fun k : Fin p => f ((k : ℕ) : ℤ)) := by
      intro k l hkl
      simp only at hkl
      have h1 : dir (f ((k : ℕ) : ℤ)) ∈ arcCone A ((k : ℕ) : ℤ) := hf _
      have h2 : dir (f ((l : ℕ) : ℤ)) ∈ arcCone A ((l : ℕ) : ℤ) := hf _
      rw [hkl] at h1
      have hdvd := arcCone_unique hper hp3 hdet h1 h2
      have hk : ((k : ℕ) : ℤ) < (p : ℤ) := by exact_mod_cast k.isLt
      have hl : ((l : ℕ) : ℤ) < (p : ℤ) := by exact_mod_cast l.isLt
      have hk0 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) := by positivity
      have hl0 : (0 : ℤ) ≤ ((l : ℕ) : ℤ) := by positivity
      have hzero : ((l : ℕ) : ℤ) - ((k : ℕ) : ℤ) = 0 :=
        Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; omega)
      have : (k : ℕ) = (l : ℕ) := by omega
      exact Fin.ext this
    have hcard := Fintype.card_le_of_injective _ hinj
    simpa using hcard

/-!
### Conventions, and how the formal statement matches the printed one

* Lean version `4.28.0`; mathlib commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
* The oriented affine plane is `V = ℝ × ℝ` in the direct affine frame printed in the problem,
  with `O` translated to `0`; `det` is the determinant of that frame.
* `R : Fin n → Set V` are the `n` rays: each `R j` equals `ray v = {t • v | t ≥ 0}` for some
  nonzero direction `v` (hypothesis `hR`), and they are pairwise distinct (`hRinj`).
* The *zones* are, exactly as printed, the connected components of the complement of the union of
  the rays; this is the predicate `IsZone R`.  The separation hypothesis `hsep` is quantified over
  all zones, so no assumption on the *number* of zones is needed (that number is `n`, but the
  formal statement does not use it, which only makes the hypotheses weaker).
* The vertex sequence is the printed `p`-periodic sequence `A : ℤ → V` (`hper`), and `hdet` is the
  printed global convexity hypothesis with indices read modulo `p`.  `periodic_iff_zmod`,
  `det_hyp_iff_zmod` and `edge_wraparound` prove that this is equivalent to the cyclic `ZMod p`
  reading of the same data, including the wraparound edge.
* `M : ℤ → V` is given by the printed relation `OM_k = A_k A_(k+1)` (`hM`).
* `hhalf` (no zone contains an open half-plane) is retained because it is printed, but, as noticed
  in the solution, it is not needed for the upper bound; the formal proof does not use it.  The
  distinctness of the rays (`hRinj`) is likewise printed but not needed.
* Degenerate periods are all covered: `p = 1` gives `p ≤ n` from the printed positivity of the
  number of rays, and `p = 2` is settled by the half-plane argument (a single ray cannot have the
  two opposite side-vector points outside the closure of a common zone).
* There is no other mismatch: `q896` derives the printed conclusion `p ≤ n` from the printed
  hypotheses for every `n, p ≥ 1`.
* The hypotheses are not vacuous: `RequestProject/Example.lean` exhibits three rays and a triangle
  satisfying *all* of them (including the half-plane hypothesis) with `n = p = 3`.
-/

-- Kernel check: the aggregate theorem uses only the standard axioms.
#print axioms q896

end Q896
