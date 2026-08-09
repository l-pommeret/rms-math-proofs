/-
# Q804 (Luc Pommeret's problem list) — spherical codes

Let `S ⊆ ℝ³` be the unit sphere.  For a finite `X ⊆ S` with at least two points let
`δ(X)` be the smallest distance between two distinct points of `X`, and let
`d(n) = max {δ(X) : |X| = n}`.

Part (a) of the problem asks whether, whenever a regular (Platonic) polyhedron with `n`
vertices is inscribed in `S`, `d(n)` equals its edge length.  The answer is **no**:
it holds for the tetrahedron (`n = 4`), the octahedron (`n = 6`) and the icosahedron
(`n = 12`), but fails for the cube (`n = 8`) and the dodecahedron (`n = 20`).

This file formalizes:

* `Q804.d_four`   : `d 4 = √(8/3)`, the edge length of the inscribed regular tetrahedron;
* `Q804.d_six`    : `d 6 = √2`, the edge length of the inscribed regular octahedron;
* `Q804.cube_not_optimal`         : `√(4/3) < d 8`  (the cube's edge length is `√(4/3)`);
* `Q804.dodecahedron_not_optimal` : `√(2 - 2√5/3) < d 20`
  (the dodecahedron's edge length is `√(2 - 2√5/3)`);
* `Q804.icosahedron_le_d` : `√(2 - 2/√5) ≤ d 12` (the icosahedron's edge length is
  `√(2 - 2/√5)`; only this lower bound is formalized).

See the comments at the end of the file for the parts of the solution that are *not*
formalized here.
-/
import Mathlib

open RealInnerProductSpace

namespace Q804

/-- The ambient space: `ℝ³` with the Euclidean inner product. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- `Separations n` is the set of real numbers `r` that are realized as a lower bound for
the mutual distances of some `n`-point subset of the unit sphere of `ℝ³`. -/
def Separations (n : ℕ) : Set ℝ :=
  {r : ℝ | ∃ X : Finset E, (∀ x ∈ X, ‖x‖ = 1) ∧ X.card = n ∧
      ∀ x ∈ X, ∀ y ∈ X, x ≠ y → r ≤ dist x y}

/-- `d n` is the largest possible minimal distance between `n` distinct points on the unit
sphere of `ℝ³`, i.e. `d n = max_{|X| = n} min_{x ≠ y ∈ X} ‖x - y‖`. -/
noncomputable def d (n : ℕ) : ℝ := sSup (Separations n)

/-! ## Basic facts -/

lemma dist_sq_of_unit {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    dist x y ^ 2 = 2 - 2 * ⟪x, y⟫ := by
  rw [dist_eq_norm, @norm_sub_sq_real, hx, hy]; ring

lemma dist_le_two {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : dist x y ≤ 2 := by
  calc dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
  _ = 2 := by rw [hx, hy]; norm_num

lemma le_dist_of_inner_le {x y : E} {s : ℝ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (h : ⟪x, y⟫ ≤ s) : Real.sqrt (2 - 2 * s) ≤ dist x y := by
  have h1 : dist x y ^ 2 = 2 - 2 * ⟪x, y⟫ := dist_sq_of_unit hx hy
  have h2 : Real.sqrt (dist x y ^ 2) = dist x y := Real.sqrt_sq dist_nonneg
  rw [← h2, h1]
  exact Real.sqrt_le_sqrt (by linarith)

lemma dist_le_of_le_inner {x y : E} {s : ℝ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (h : s ≤ ⟪x, y⟫) : dist x y ≤ Real.sqrt (2 - 2 * s) := by
  have h1 : dist x y ^ 2 = 2 - 2 * ⟪x, y⟫ := dist_sq_of_unit hx hy
  have h2 : Real.sqrt (dist x y ^ 2) = dist x y := Real.sqrt_sq dist_nonneg
  rw [← h2, h1]
  exact Real.sqrt_le_sqrt (by linarith)

lemma bddAbove_separations {n : ℕ} (h2 : 2 ≤ n) : BddAbove (Separations n) := by
  refine ⟨2, ?_⟩
  rintro r ⟨X, hu, hc, hsep⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by omega : 1 < X.card)
  exact le_trans (hsep x hx y hy hxy) (dist_le_two (hu x hx) (hu y hy))

/-- Upper bound transfer: if every `n`-point configuration on the sphere has two distinct
points at distance at most `c`, then `d n ≤ c`. -/
lemma d_le {n : ℕ} {c : ℝ} (hne : (Separations n).Nonempty)
    (H : ∀ X : Finset E, (∀ x ∈ X, ‖x‖ = 1) → X.card = n →
      ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ dist x y ≤ c) : d n ≤ c := by
  refine csSup_le hne ?_
  rintro r ⟨X, hu, hc, hsep⟩
  obtain ⟨x, hx, y, hy, hxy, hd⟩ := H X hu hc
  exact le_trans (hsep x hx y hy hxy) hd

/-- Lower bound transfer: an explicit `n`-point configuration with all inner products at
most `s < 1` shows `√(2 - 2s) ≤ d n`. -/
lemma config_mem {n : ℕ} {s : ℝ} (hs : s < 1) (P : Fin n → E)
    (hu : ∀ i, ‖P i‖ = 1) (hinner : ∀ i j, i ≠ j → ⟪P i, P j⟫ ≤ s) :
    Real.sqrt (2 - 2 * s) ∈ Separations n := by
  classical
  have hinj : Function.Injective P := by
    intro i j hij
    by_contra hne
    have h := hinner i j hne
    rw [hij, real_inner_self_eq_norm_sq, hu j] at h
    norm_num at h
    linarith
  refine ⟨Finset.image P Finset.univ, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact hu i
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro x hx y hy hxy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    exact le_dist_of_inner_le (hu i) (hu j) (hinner i j (fun h => hxy (by rw [h])))

lemma le_d_of_config {n : ℕ} (h2 : 2 ≤ n) {s : ℝ} (hs : s < 1) (P : Fin n → E)
    (hu : ∀ i, ‖P i‖ = 1) (hinner : ∀ i j, i ≠ j → ⟪P i, P j⟫ ≤ s) :
    Real.sqrt (2 - 2 * s) ≤ d n :=
  le_csSup (bddAbove_separations h2) (config_mem hs P hu hinner)

/-! ## The averaging bound

In any set of `n ≥ 2` unit vectors, some two distinct vectors have inner product at least
`-1/(n-1)`; this comes from `0 ≤ ‖∑ x‖²`. -/

lemma exists_inner_ge (X : Finset E) (hu : ∀ x ∈ X, ‖x‖ = 1) (h2 : 2 ≤ X.card) :
    ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ -(1 / ((X.card : ℝ) - 1)) ≤ ⟪x, y⟫ := by
  by_contra hcon
  push_neg at hcon
  set n : ℕ := X.card with hn
  have hnR : (1:ℝ) ≤ (n:ℝ) - 1 := by
    have : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast h2
    linarith
  have key : ∀ x ∈ X, (∑ y ∈ X, ⟪x, y⟫) < 0 := by
    intro x hx
    have hcard : (X.erase x).card = n - 1 := by rw [Finset.card_erase_of_mem hx]
    have hne : (X.erase x).Nonempty := by
      rw [← Finset.card_pos, hcard]; omega
    have hsplit : ∑ y ∈ X, ⟪x, y⟫ = ⟪x, x⟫ + ∑ y ∈ X.erase x, ⟪x, y⟫ :=
      (Finset.add_sum_erase _ _ hx).symm
    have hxx : ⟪x, x⟫ = (1:ℝ) := by
      rw [real_inner_self_eq_norm_sq, hu x hx]; norm_num
    have hlt : ∑ y ∈ X.erase x, ⟪x, y⟫ < ∑ y ∈ X.erase x, (-(1 / ((n:ℝ) - 1))) := by
      refine Finset.sum_lt_sum_of_nonempty hne ?_
      intro y hy
      exact hcon x hx y (Finset.mem_of_mem_erase hy) (Ne.symm (Finset.ne_of_mem_erase hy))
    have hconst : ∑ y ∈ X.erase x, (-(1 / ((n:ℝ) - 1))) = ((n:ℝ) - 1) * (-(1 / ((n:ℝ) - 1))) := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
      congr 1
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
      ring
    have hval : ((n:ℝ) - 1) * (-(1 / ((n:ℝ) - 1))) = -1 := by
      field_simp
    rw [hsplit, hxx]
    rw [hconst, hval] at hlt
    linarith
  have hXne : X.Nonempty := by rw [← Finset.card_pos]; omega
  have hsum : (0:ℝ) ≤ ∑ x ∈ X, ∑ y ∈ X, ⟪x, y⟫ := by
    have h : ⟪∑ x ∈ X, x, ∑ y ∈ X, y⟫ = ∑ x ∈ X, ∑ y ∈ X, ⟪x, y⟫ := by
      rw [sum_inner]
      exact Finset.sum_congr rfl fun x _ => inner_sum _ _ _
    rw [← h]
    exact real_inner_self_nonneg
  have hlt : ∑ x ∈ X, ∑ y ∈ X, ⟪x, y⟫ < ∑ x ∈ X, (0:ℝ) :=
    Finset.sum_lt_sum_of_nonempty hXne key
  simp only [Finset.sum_const_zero] at hlt
  linarith

/-! ## The obtuse-set bound in `ℝ³`

At most four nonzero vectors of `ℝ³` can have pairwise negative inner products. -/

lemma exists_inner_nonneg (X : Finset E) (h5 : 5 ≤ X.card) :
    ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ 0 ≤ ⟪x, y⟫ := by
  by_contra hcon
  push_neg at hcon
  set p : {x // x ∈ X} → E := fun x => (x : E) with hp
  have hnai : ¬ AffineIndependent ℝ p := by
    intro h
    have hc := h.card_le_finrank_succ
    have h1 : Module.finrank ℝ ↥(vectorSpan ℝ (Set.range p)) ≤ 3 := by
      simpa [finrank_euclideanSpace_fin] using Submodule.finrank_le (vectorSpan ℝ (Set.range p))
    rw [Fintype.card_coe] at hc
    omega
  rw [affineIndependent_iff] at hnai
  push_neg at hnai
  obtain ⟨s, w, hw0, hwp, e0, he0s, he0⟩ := hnai
  classical
  set P := s.filter (fun e => 0 < w e) with hPdef
  set N := s.filter (fun e => ¬ 0 < w e) with hNdef
  obtain ⟨j0, hj0s, hj0⟩ : ∃ j ∈ s, w j < 0 := by
    by_contra h
    push_neg at h
    exact he0 ((Finset.sum_eq_zero_iff_of_nonneg h).1 hw0 e0 he0s)
  obtain ⟨i0, hi0s, hi0⟩ : ∃ i ∈ s, 0 < w i := by
    by_contra h
    push_neg at h
    exact he0 ((Finset.sum_eq_zero_iff_of_nonpos h).1 hw0 e0 he0s)
  have hi0P : i0 ∈ P := by simp [hPdef, hi0s, hi0]
  have hj0N : j0 ∈ N := by simp [hNdef, hj0s]; linarith
  have hneg : ∀ i ∈ P, ∀ j ∈ N, w j < 0 → w i * (-w j) * ⟪p i, p j⟫ < 0 := by
    intro i hi j hj hwj
    have hwi : 0 < w i := (Finset.mem_filter.1 hi).2
    have hij : i ≠ j := by intro hh; rw [hh] at hwi; linarith
    have hpij : p i ≠ p j := fun hh => hij (Subtype.ext hh)
    exact mul_neg_of_pos_of_neg (mul_pos hwi (by linarith)) (hcon (p i) i.2 (p j) j.2 hpij)
  have hterm : ∀ i ∈ P, ∀ j ∈ N, w i * (-w j) * ⟪p i, p j⟫ ≤ 0 := by
    intro i hi j hj
    have hwj : w j ≤ 0 := not_lt.1 (Finset.mem_filter.1 hj).2
    rcases eq_or_lt_of_le hwj with h | h
    · rw [h]; simp
    · exact le_of_lt (hneg i hi j hj h)
  set u : E := ∑ i ∈ P, w i • p i with hu
  have hsplit : (∑ i ∈ P, w i • p i) + (∑ j ∈ N, w j • p j) = 0 := by
    rw [hPdef, hNdef, Finset.sum_filter_add_sum_filter_not]
    exact hwp
  have hu2 : u = ∑ j ∈ N, (-w j) • p j := by
    have h1 : (∑ j ∈ N, (-w j) • p j) = -(∑ j ∈ N, w j • p j) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [neg_smul]
    rw [h1, hu]
    exact eq_neg_of_add_eq_zero_left hsplit
  have hexp : ⟪u, u⟫ = ∑ i ∈ P, ∑ j ∈ N, w i * (-w j) * ⟪p i, p j⟫ := by
    nth_rewrite 2 [hu2]
    rw [hu, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  have hlt : ∑ i ∈ P, ∑ j ∈ N, w i * (-w j) * ⟪p i, p j⟫ < 0 := by
    have hinner : ∀ i ∈ P, ∑ j ∈ N, w i * (-w j) * ⟪p i, p j⟫ < 0 := by
      intro i hi
      have h := Finset.sum_lt_sum (fun j hj => hterm i hi j hj)
        ⟨j0, hj0N, hneg i hi j0 hj0N hj0⟩
      simpa using h
    have h := Finset.sum_lt_sum_of_nonempty ⟨i0, hi0P⟩ hinner
    simpa using h
  have hnn := real_inner_self_nonneg (x := u)
  rw [hexp] at hnn
  linarith

/-! ## `n = 4`: the regular tetrahedron is optimal -/

/-- `√3/3`, the common coordinate of the vertices of the inscribed regular tetrahedron. -/
noncomputable def tc : ℝ := Real.sqrt 3 / 3

lemma tc_sq : tc ^ 2 = 1 / 3 := by
  rw [tc, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num

/-- The four vertices of a regular tetrahedron inscribed in the unit sphere. -/
noncomputable def tetra : Fin 4 → E
  | 0 => !₂[tc, tc, tc]
  | 1 => !₂[tc, -tc, -tc]
  | 2 => !₂[-tc, tc, -tc]
  | 3 => !₂[-tc, -tc, tc]

lemma tetra_unit : ∀ i, ‖tetra i‖ = 1 := by
  intro i
  fin_cases i <;>
    simp [tetra, EuclideanSpace.norm_eq, Fin.sum_univ_three, sq_abs] <;>
    rw [show tc ^ 2 + tc ^ 2 + tc ^ 2 = 1 by rw [tc_sq]; ring]

lemma tetra_inner : ∀ i j, i ≠ j → ⟪tetra i, tetra j⟫ ≤ -(1 / 3) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [tetra, PiLp.inner_apply, Fin.sum_univ_three] <;> nlinarith [tc_sq]

theorem d_four : d 4 = Real.sqrt (8 / 3) := by
  have hmem : Real.sqrt (8 / 3) ∈ Separations 4 := by
    have h := config_mem (s := -(1/3)) (by norm_num) tetra tetra_unit tetra_inner
    rwa [show (2 : ℝ) - 2 * (-(1/3)) = 8/3 by norm_num] at h
  refine le_antisymm ?_ (le_csSup (bddAbove_separations (by norm_num)) hmem)
  refine d_le ⟨_, hmem⟩ ?_
  intro X hu hc
  obtain ⟨x, hx, y, hy, hxy, hinner⟩ := exists_inner_ge X hu (by omega)
  refine ⟨x, hx, y, hy, hxy, ?_⟩
  rw [hc] at hinner
  norm_num at hinner
  have hd := dist_le_of_le_inner (hu x hx) (hu y hy) (show -(1/3 : ℝ) ≤ ⟪x, y⟫ by linarith)
  rwa [show (2 : ℝ) - 2 * (-(1/3)) = 8/3 by norm_num] at hd

/-! ## `n = 6`: the regular octahedron is optimal -/

/-- The six vertices `±e₁, ±e₂, ±e₃` of the regular octahedron. -/
noncomputable def octa : Fin 6 → E
  | 0 => !₂[1, 0, 0]
  | 1 => !₂[-1, 0, 0]
  | 2 => !₂[0, 1, 0]
  | 3 => !₂[0, -1, 0]
  | 4 => !₂[0, 0, 1]
  | 5 => !₂[0, 0, -1]

lemma octa_unit : ∀ i, ‖octa i‖ = 1 := by
  intro i
  fin_cases i <;> simp [octa, EuclideanSpace.norm_eq, Fin.sum_univ_three]

lemma octa_inner : ∀ i j, i ≠ j → ⟪octa i, octa j⟫ ≤ 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [octa, PiLp.inner_apply, Fin.sum_univ_three]

theorem d_six : d 6 = Real.sqrt 2 := by
  have hmem : Real.sqrt 2 ∈ Separations 6 := by
    have h := config_mem (s := 0) (by norm_num) octa octa_unit octa_inner
    rwa [show (2 : ℝ) - 2 * 0 = 2 by norm_num] at h
  refine le_antisymm ?_ (le_csSup (bddAbove_separations (by norm_num)) hmem)
  refine d_le ⟨_, hmem⟩ ?_
  intro X hu hc
  obtain ⟨x, hx, y, hy, hxy, hinner⟩ := exists_inner_nonneg X (by omega)
  refine ⟨x, hx, y, hy, hxy, ?_⟩
  have h := dist_le_of_le_inner (hu x hx) (hu y hy) hinner
  simpa using h

/-! ## `n = 8`: the cube is *not* optimal

The inscribed cube has edge length `√(4/3)` (`cube_dist_ge`, `cube_dist_eq`), but the
square antiprism with vertices at height `±√u`, `u = 1/(1+2√2) = (2√2-1)/7`, does
strictly better. -/

/-- The eight vertices of the cube inscribed in the unit sphere. -/
noncomputable def cube : Fin 8 → E
  | 0 => !₂[tc, tc, tc]
  | 1 => !₂[tc, tc, -tc]
  | 2 => !₂[tc, -tc, tc]
  | 3 => !₂[tc, -tc, -tc]
  | 4 => !₂[-tc, tc, tc]
  | 5 => !₂[-tc, tc, -tc]
  | 6 => !₂[-tc, -tc, tc]
  | 7 => !₂[-tc, -tc, -tc]

lemma cube_unit : ∀ i, ‖cube i‖ = 1 := by
  intro i
  fin_cases i <;>
    simp [cube, EuclideanSpace.norm_eq, Fin.sum_univ_three, sq_abs] <;>
    linarith [tc_sq]

lemma cube_inner : ∀ i j, i ≠ j → ⟪cube i, cube j⟫ ≤ 1 / 3 := by
  have htt : tc * tc = 1 / 3 := by nlinarith [tc_sq]
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [cube, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, neg_mul] <;>
    first
      | (exfalso; exact hij rfl)
      | linarith [htt]

/-- The minimal distance between two distinct vertices of the inscribed cube is at least
`√(4/3)`. -/
lemma cube_dist_ge : ∀ i j, i ≠ j → Real.sqrt (4 / 3) ≤ dist (cube i) (cube j) := by
  intro i j hij
  have h := le_dist_of_inner_le (cube_unit i) (cube_unit j) (cube_inner i j hij)
  rwa [show (2 : ℝ) - 2 * (1 / 3) = 4 / 3 by norm_num] at h

/-- ... and it is attained: the edge length of the inscribed cube is `√(4/3)`. -/
lemma cube_dist_eq : dist (cube 0) (cube 1) = Real.sqrt (4 / 3) := by
  have hinner : ⟪cube 0, cube 1⟫ = 1 / 3 := by
    have htt : tc * tc = 1 / 3 := by nlinarith [tc_sq]
    simp only [cube, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, neg_mul]
    linarith [htt]
  have hsq : dist (cube 0) (cube 1) ^ 2 = 4 / 3 := by
    rw [dist_sq_of_unit (cube_unit 0) (cube_unit 1), hinner]; norm_num
  rw [← hsq, Real.sqrt_sq dist_nonneg]

/-! ### The square antiprism -/

/-- The eight vertices of a square antiprism: two squares of circumradius `r` at heights
`±h`, rotated by 45° with respect to each other (`a = r/√2`). -/
noncomputable def antiprism (r h a : ℝ) : Fin 8 → E
  | 0 => !₂[r, 0, h]
  | 1 => !₂[0, r, h]
  | 2 => !₂[-r, 0, h]
  | 3 => !₂[0, -r, h]
  | 4 => !₂[a, a, -h]
  | 5 => !₂[-a, a, -h]
  | 6 => !₂[-a, -a, -h]
  | 7 => !₂[a, -a, -h]

lemma antiprism_unit {r h a : ℝ} (hA : r ^ 2 + h ^ 2 = 1) (hB : a ^ 2 + a ^ 2 + h ^ 2 = 1) :
    ∀ i, ‖antiprism r h a i‖ = 1 := by
  intro i
  fin_cases i <;>
    simp [antiprism, EuclideanSpace.norm_eq, Fin.sum_univ_three, sq_abs] <;>
    linarith

set_option maxHeartbeats 1000000 in
lemma antiprism_inner {r h a u q : ℝ} (hh : h * h = u) (hrr : r * r = 1 - u)
    (haa : a * a = (4 - q) / 7) (hra : r * a = 2 * u) (hu1 : u ≤ 1) (hu0 : 0 ≤ u)
    (hq : q < 1.42) : ∀ i j : Fin 8, i ≠ j → ⟪antiprism r h a i, antiprism r h a j⟫ ≤ u := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [antiprism, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, neg_mul, mul_neg, mul_zero,
    zero_mul, add_zero, zero_add, neg_neg] <;>
    first
      | (exfalso; exact hij rfl)
      | linarith [hh, hrr, haa, hra]

/-- `√2`. -/
noncomputable def q2 : ℝ := Real.sqrt 2

lemma q2_sq : q2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

lemma q2_lb : 1.41 < q2 := by
  rw [q2, show (1.41:ℝ) = Real.sqrt (1.41 ^ 2) by rw [Real.sqrt_sq]; norm_num]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma q2_ub : q2 < 1.42 := by
  rw [q2, show (1.42:ℝ) = Real.sqrt (1.42 ^ 2) by rw [Real.sqrt_sq]; norm_num]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- `u8 = 1/(1+2√2) = (2√2-1)/7` is the largest inner product occurring in the square
antiprism. -/
noncomputable def u8 : ℝ := (2 * q2 - 1) / 7

noncomputable def h8 : ℝ := Real.sqrt u8
noncomputable def a8 : ℝ := Real.sqrt ((4 - q2) / 7)
noncomputable def r8 : ℝ := a8 * q2

lemma u8_pos : 0 < u8 := by rw [u8]; nlinarith [q2_lb]
lemma u8_lt : u8 < 1 / 3 := by rw [u8]; nlinarith [q2_ub]
lemma h8_sq : h8 ^ 2 = u8 := Real.sq_sqrt u8_pos.le
lemma a8_sq : a8 ^ 2 = (4 - q2) / 7 := Real.sq_sqrt (by nlinarith [q2_ub])
lemma r8_sq : r8 ^ 2 = 1 - u8 := by rw [r8, mul_pow, a8_sq, q2_sq, u8]; ring

lemma r8_mul_a8 : r8 * a8 = 2 * u8 := by
  have h : r8 * a8 = q2 * a8 ^ 2 := by rw [r8]; ring
  rw [h, a8_sq, u8]; nlinarith [q2_sq]

/-- The square antiprism is an eight-point configuration on the sphere whose largest
inner product is `u8 < 1/3`; hence it beats the cube. -/
theorem cube_not_optimal : Real.sqrt (4 / 3) < d 8 := by
  have hunit : ∀ i, ‖antiprism r8 h8 a8 i‖ = 1 :=
    antiprism_unit (by rw [r8_sq, h8_sq]; ring) (by rw [h8_sq, a8_sq, u8]; ring)
  have hinner : ∀ i j : Fin 8, i ≠ j → ⟪antiprism r8 h8 a8 i, antiprism r8 h8 a8 j⟫ ≤ u8 :=
    antiprism_inner (by nlinarith [h8_sq]) (by nlinarith [r8_sq]) (by nlinarith [a8_sq])
      r8_mul_a8 (by linarith [u8_lt]) u8_pos.le q2_ub
  have hle : Real.sqrt (2 - 2 * u8) ≤ d 8 :=
    le_d_of_config (by norm_num) (by linarith [u8_lt]) _ hunit hinner
  have hlt : Real.sqrt (4 / 3) < Real.sqrt (2 - 2 * u8) :=
    Real.sqrt_lt_sqrt (by norm_num) (by linarith [u8_lt])
  linarith

/-! ## `n = 20`: the dodecahedron is *not* optimal

The inscribed regular dodecahedron has edge length `√(2 - 2√5/3)` (`dodeca_dist_ge`,
`dodeca_dist_eq`); the twenty-point configuration `beats20` (two poles, a regular hexagon
on the equator, and two rotated hexagons at heights `±1/√3`) has all inner products at
most `1/√2 < √5/3` and hence a strictly larger minimal distance. -/

/-- `√5`. -/
noncomputable def f5 : ℝ := Real.sqrt 5

lemma f5_mul : f5 * f5 = 5 := Real.mul_self_sqrt (by norm_num)

lemma f5_lb : 2.236 < f5 := by
  rw [f5, show (2.236:ℝ) = Real.sqrt (2.236 ^ 2) by rw [Real.sqrt_sq]; norm_num]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma f5_ub : f5 < 2.2361 := by
  rw [f5, show (2.2361:ℝ) = Real.sqrt (2.2361 ^ 2) by rw [Real.sqrt_sq]; norm_num]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma tc_mul : tc * tc = 1 / 3 := by
  rw [tc, div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num

/-- The golden ratio `φ = (1+√5)/2`. -/
noncomputable def gv : ℝ := (1 + f5) / 2
/-- `φ⁻¹ = (√5-1)/2`. -/
noncomputable def gi : ℝ := (f5 - 1) / 2

/-- The twenty vertices of the regular dodecahedron inscribed in the unit sphere. -/
noncomputable def dodeca : Fin 20 → E
  | 0 => !₂[tc, tc, tc]
  | 1 => !₂[tc, tc, -tc]
  | 2 => !₂[tc, -tc, tc]
  | 3 => !₂[tc, -tc, -tc]
  | 4 => !₂[-tc, tc, tc]
  | 5 => !₂[-tc, tc, -tc]
  | 6 => !₂[-tc, -tc, tc]
  | 7 => !₂[-tc, -tc, -tc]
  | 8 => !₂[0, tc * gi, tc * gv]
  | 9 => !₂[0, tc * gi, -tc * gv]
  | 10 => !₂[0, -tc * gi, tc * gv]
  | 11 => !₂[0, -tc * gi, -tc * gv]
  | 12 => !₂[tc * gi, tc * gv, 0]
  | 13 => !₂[tc * gi, -tc * gv, 0]
  | 14 => !₂[-tc * gi, tc * gv, 0]
  | 15 => !₂[-tc * gi, -tc * gv, 0]
  | 16 => !₂[tc * gv, 0, tc * gi]
  | 17 => !₂[tc * gv, 0, -tc * gi]
  | 18 => !₂[-tc * gv, 0, tc * gi]
  | 19 => !₂[-tc * gv, 0, -tc * gi]
  | _ => !₂[tc, tc, tc]

set_option maxHeartbeats 4000000 in
lemma dodeca_unit : ∀ i, ‖dodeca i‖ = 1 := by
  have h1 : tc * tc = 1 / 3 := tc_mul
  have h2 : f5 * f5 = 5 := f5_mul
  intro i
  fin_cases i <;>
    simp [dodeca, EuclideanSpace.norm_eq, Fin.sum_univ_three, sq_abs, gv, gi, mul_pow,
      div_pow] <;>
    nlinarith [h1, h2]

set_option maxHeartbeats 4000000 in
lemma dodeca_inner : ∀ i j : Fin 20, i ≠ j → ⟪dodeca i, dodeca j⟫ ≤ f5 / 3 := by
  have h1 : tc * tc = 1 / 3 := tc_mul
  have h2 : f5 * f5 = 5 := f5_mul
  have h3 : tc * tc * f5 = f5 / 3 := by rw [h1]; ring
  have h4 : tc * tc * (f5 * f5) = 5 / 3 := by rw [h1, h2]; norm_num
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [dodeca, gv, gi, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, neg_mul, mul_neg, mul_zero, zero_mul, add_zero,
      zero_add, neg_neg] <;>
    first
      | (exfalso; exact hij rfl)
      | linarith [h1, h2, h3, h4, f5_lb, f5_ub]

/-- Distinct vertices of the inscribed dodecahedron are at distance at least
`√(2 - 2√5/3)`. -/
lemma dodeca_dist_ge : ∀ i j, i ≠ j →
    Real.sqrt (2 - 2 * Real.sqrt 5 / 3) ≤ dist (dodeca i) (dodeca j) := by
  intro i j hij
  have h := le_dist_of_inner_le (dodeca_unit i) (dodeca_unit j) (dodeca_inner i j hij)
  rwa [show (2 : ℝ) - 2 * (f5 / 3) = 2 - 2 * Real.sqrt 5 / 3 by rw [f5]; ring] at h

/-- ... and this distance is attained: the edge length of the inscribed dodecahedron is
`√(2 - 2√5/3)`. -/
lemma dodeca_dist_eq :
    dist (dodeca 0) (dodeca 8) = Real.sqrt (2 - 2 * Real.sqrt 5 / 3) := by
  have hinner : ⟪dodeca 0, dodeca 8⟫ = f5 / 3 := by
    have h1 : tc * tc = 1 / 3 := tc_mul
    have h3 : tc * tc * f5 = f5 / 3 := by rw [h1]; ring
    simp only [dodeca, gv, gi, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, zero_mul, zero_add]
    linarith [h1, h3]
  have hsq : dist (dodeca 0) (dodeca 8) ^ 2 = 2 - 2 * Real.sqrt 5 / 3 := by
    rw [dist_sq_of_unit (dodeca_unit 0) (dodeca_unit 8), hinner, f5]; ring
  rw [← hsq, Real.sqrt_sq dist_nonneg]

/-! ### A better twenty-point configuration -/

/-- `√2`. -/
noncomputable def s2 : ℝ := Real.sqrt 2
/-- `√3`. -/
noncomputable def s3 : ℝ := Real.sqrt 3

lemma s2_mul : s2 * s2 = 2 := Real.mul_self_sqrt (by norm_num)
lemma s3_mul : s3 * s3 = 3 := Real.mul_self_sqrt (by norm_num)

lemma s2_lb : 1.414 < s2 := by
  rw [s2, show (1.414:ℝ) = Real.sqrt (1.414 ^ 2) by rw [Real.sqrt_sq]; norm_num]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma s2_ub : s2 < 1.4143 := by
  rw [s2, show (1.4143:ℝ) = Real.sqrt (1.4143 ^ 2) by rw [Real.sqrt_sq]; norm_num]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma s3_lb : 1.732 < s3 := by
  rw [s3, show (1.732:ℝ) = Real.sqrt (1.732 ^ 2) by rw [Real.sqrt_sq]; norm_num]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma s3_ub : s3 < 1.7321 := by
  rw [s3, show (1.7321:ℝ) = Real.sqrt (1.7321 ^ 2) by rw [Real.sqrt_sq]; norm_num]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- Twenty points on the unit sphere: the two poles, the six vertices of a regular hexagon
on the equator, and two hexagons at heights `±1/√3` rotated by 30°. -/
noncomputable def beats20 : Fin 20 → E
  | 0 => !₂[0, 0, 1]
  | 1 => !₂[0, 0, -1]
  | 2 => !₂[1, 0, 0]
  | 3 => !₂[1/2, s3/2, 0]
  | 4 => !₂[-1/2, s3/2, 0]
  | 5 => !₂[-1, 0, 0]
  | 6 => !₂[-1/2, -s3/2, 0]
  | 7 => !₂[1/2, -s3/2, 0]
  | 8 => !₂[s2/2, s2*s3/6, s3/3]
  | 9 => !₂[0, s2*s3/3, s3/3]
  | 10 => !₂[-s2/2, s2*s3/6, s3/3]
  | 11 => !₂[-s2/2, -s2*s3/6, s3/3]
  | 12 => !₂[0, -s2*s3/3, s3/3]
  | 13 => !₂[s2/2, -s2*s3/6, s3/3]
  | 14 => !₂[s2/2, s2*s3/6, -s3/3]
  | 15 => !₂[0, s2*s3/3, -s3/3]
  | 16 => !₂[-s2/2, s2*s3/6, -s3/3]
  | 17 => !₂[-s2/2, -s2*s3/6, -s3/3]
  | 18 => !₂[0, -s2*s3/3, -s3/3]
  | 19 => !₂[s2/2, -s2*s3/6, -s3/3]
  | _ => !₂[0, 0, 1]

set_option maxHeartbeats 4000000 in
lemma beats20_unit : ∀ i, ‖beats20 i‖ = 1 := by
  have h1 : s2 * s2 = 2 := s2_mul
  have h2 : s3 * s3 = 3 := s3_mul
  have h3 : s2 * s2 * (s3 * s3) = 6 := by rw [h1, h2]; norm_num
  intro i
  fin_cases i <;>
    simp [beats20, EuclideanSpace.norm_eq, Fin.sum_univ_three, sq_abs, div_pow, mul_pow] <;>
    nlinarith [h1, h2, h3]

set_option maxHeartbeats 4000000 in
lemma beats20_inner : ∀ i j : Fin 20, i ≠ j → ⟪beats20 i, beats20 j⟫ ≤ s2 / 2 := by
  have h1 : s2 * s2 = 2 := s2_mul
  have h2 : s3 * s3 = 3 := s3_mul
  have h3 : s2 * s2 * (s3 * s3) = 6 := by rw [h1, h2]; norm_num
  have h4 : s3 * s3 * s2 = 3 * s2 := by rw [h2]
  have h5 : s2 * s2 * s3 = 2 * s3 := by rw [h1]
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [beats20, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, neg_mul, mul_neg, mul_zero, zero_mul, add_zero, zero_add, neg_neg] <;>
    first
      | (exfalso; exact hij rfl)
      | linarith [h1, h2, h3, h4, h5, s2_lb, s2_ub, s3_lb, s3_ub]

/-! ## `n = 12`: the regular icosahedron

Only the lower bound `d 12 ≥ (icosahedral edge length)` is formalized here; the matching
upper bound rests on the Delsarte linear-programming method, which is not formalized. -/

/-- `1/√(1+φ²) = √((5-√5)/10)`, the normalizing factor for the icosahedron. -/
noncomputable def kk : ℝ := Real.sqrt ((5 - f5) / 10)

lemma kk_mul : kk * kk = (5 - f5) / 10 := Real.mul_self_sqrt (by nlinarith [f5_ub])

/-- The twelve vertices of the regular icosahedron inscribed in the unit sphere. -/
noncomputable def ico : Fin 12 → E
  | 0 => !₂[0, kk, kk * gv]
  | 1 => !₂[0, kk, -kk * gv]
  | 2 => !₂[0, -kk, kk * gv]
  | 3 => !₂[0, -kk, -kk * gv]
  | 4 => !₂[kk, kk * gv, 0]
  | 5 => !₂[kk, -kk * gv, 0]
  | 6 => !₂[-kk, kk * gv, 0]
  | 7 => !₂[-kk, -kk * gv, 0]
  | 8 => !₂[kk * gv, 0, kk]
  | 9 => !₂[kk * gv, 0, -kk]
  | 10 => !₂[-kk * gv, 0, kk]
  | 11 => !₂[-kk * gv, 0, -kk]

set_option maxHeartbeats 2000000 in
lemma ico_unit : ∀ i, ‖ico i‖ = 1 := by
  have h1 : kk * kk = (5 - f5) / 10 := kk_mul
  have h2 : f5 * f5 = 5 := f5_mul
  intro i
  fin_cases i <;>
    simp [ico, EuclideanSpace.norm_eq, Fin.sum_univ_three, sq_abs, gv, mul_pow, div_pow] <;>
    nlinarith [h1, h2]

set_option maxHeartbeats 2000000 in
lemma ico_inner : ∀ i j : Fin 12, i ≠ j → ⟪ico i, ico j⟫ ≤ f5 / 5 := by
  have h1 : kk * kk = (5 - f5) / 10 := kk_mul
  have h2 : f5 * f5 = 5 := f5_mul
  have h3 : kk * kk * f5 = (5 * f5 - 5) / 10 := by rw [h1]; nlinarith [h2]
  have h4 : kk * kk * (f5 * f5) = 5 * (5 - f5) / 10 := by rw [h1, h2]; ring
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [ico, gv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, neg_mul, mul_neg, mul_zero, zero_mul, add_zero,
      zero_add, neg_neg] <;>
    first
      | (exfalso; exact hij rfl)
      | linarith [h1, h2, h3, h4, f5_lb, f5_ub]

lemma f5_div : f5 / 5 = 1 / Real.sqrt 5 := by
  rw [f5, eq_div_iff (by positivity), div_mul_eq_mul_div, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- Distinct vertices of the inscribed icosahedron are at distance at least `√(2 - 2/√5)`. -/
lemma ico_dist_ge : ∀ i j, i ≠ j →
    Real.sqrt (2 - 2 / Real.sqrt 5) ≤ dist (ico i) (ico j) := by
  intro i j hij
  have h := le_dist_of_inner_le (ico_unit i) (ico_unit j) (ico_inner i j hij)
  rwa [show (2 : ℝ) - 2 * (f5 / 5) = 2 - 2 / Real.sqrt 5 by rw [f5_div]; ring] at h

/-- ... and this distance is attained: the edge length of the inscribed icosahedron is
`√(2 - 2/√5)`. -/
lemma ico_dist_eq : dist (ico 0) (ico 4) = Real.sqrt (2 - 2 / Real.sqrt 5) := by
  have hinner : ⟪ico 0, ico 4⟫ = f5 / 5 := by
    have h1 : kk * kk = (5 - f5) / 10 := kk_mul
    have h3 : kk * kk * f5 = (5 * f5 - 5) / 10 := by rw [h1]; nlinarith [f5_mul]
    simp only [ico, gv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, mul_zero, zero_mul, add_zero]
    linarith [h1, h3]
  have hsq : dist (ico 0) (ico 4) ^ 2 = 2 - 2 / Real.sqrt 5 := by
    rw [dist_sq_of_unit (ico_unit 0) (ico_unit 4), hinner, f5_div]; ring
  rw [← hsq, Real.sqrt_sq dist_nonneg]

/-- The icosahedral edge length is a lower bound for `d 12`. -/
theorem icosahedron_le_d : Real.sqrt (2 - 2 / Real.sqrt 5) ≤ d 12 := by
  have h := le_d_of_config (n := 12) (by norm_num) (s := f5 / 5)
    (by linarith [f5_ub]) _ ico_unit ico_inner
  rwa [show (2 : ℝ) - 2 * (f5 / 5) = 2 - 2 / Real.sqrt 5 by rw [f5_div]; ring] at h

theorem dodecahedron_not_optimal : Real.sqrt (2 - 2 * Real.sqrt 5 / 3) < d 20 := by
  have hle : Real.sqrt (2 - 2 * (s2 / 2)) ≤ d 20 :=
    le_d_of_config (by norm_num) (by linarith [s2_ub]) _ beats20_unit beats20_inner
  have hlt : Real.sqrt (2 - 2 * Real.sqrt 5 / 3) < Real.sqrt (2 - 2 * (s2 / 2)) := by
    refine Real.sqrt_lt_sqrt (by rw [← f5]; linarith [f5_ub]) ?_
    rw [← f5]
    linarith [f5_lb, s2_ub]
  linarith

/-!
## Scope of this formalization, and mismatches with the printed solution

What is proved here (all statements are about `d n = sSup (Separations n)`, the largest
minimal distance of an `n`-point subset of the unit sphere of `ℝ³`):

* `d_four : d 4 = √(8/3)` — the regular tetrahedron is optimal;
* `d_six : d 6 = √2` — the regular octahedron is optimal;
* `cube_not_optimal : √(4/3) < d 8`, together with `cube_dist_ge` and `cube_dist_eq`,
  which identify `√(4/3)` as the edge length of the inscribed cube;
* `dodecahedron_not_optimal : √(2 - 2√5/3) < d 20`, together with `dodeca_dist_ge` and
  `dodeca_dist_eq`, which identify `√(2 - 2√5/3)` as the edge length of the inscribed
  regular dodecahedron;
* `icosahedron_le_d : √(2 - 2/√5) ≤ d 12`, together with `ico_dist_ge` and `ico_dist_eq`,
  which identify `√(2 - 2/√5)` as the edge length of the inscribed regular icosahedron.

In particular the answer to part (a) of Q804 is *no*: for `n = 8` and `n = 20` the value of
`d n` is strictly larger than the edge length of the inscribed Platonic solid.

What is **not** formalized:

* the matching upper bound `d 12 = √(2 - 2/√5)` for the icosahedron, whose proof in the
  solution uses the Delsarte linear-programming bound (positive definiteness of Legendre
  polynomials on `S²` via the spherical-harmonic addition formula);
* part (b), `lim_{n→∞} √n·d n = √(8π/√3)`, whose proof needs the planar packing constant
  `2/√3` (Voronoi cells plus Euler's formula on the torus) and its bi-Lipschitz transfer
  to a compact surface.

Mismatches with the printed statement:

* the printed solution defines `d n` as a maximum over `n`-point subsets of the sphere;
  here `d n` is defined as the supremum of all real numbers realized as a lower bound for
  the mutual distances of some `n`-point subset. For `n ≥ 2` the two agree (the set of such
  lower bounds is bounded above by `2`, and the maximum is attained by compactness), and
  no compactness argument is needed for the results proved here.
* "regular polyhedron" is read, as in the solution, as "convex Platonic solid".

Environment: Lean 4.28.0, Mathlib commit 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
-/

end Q804
