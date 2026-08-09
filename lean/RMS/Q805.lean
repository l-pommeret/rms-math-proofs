/-
# Q805 : norms on `ℝ²` that are linearly isometric to their dual norm

This file formalizes the classification announced in the answer to Q805.

Setting: `V = Fin 2 → ℝ` with the standard inner product `x ⬝ᵥ y = x 0 * y 0 + x 1 * y 1`.
A *norm* on `V` is a function `N : V → ℝ` which is absolutely homogeneous, subadditive and
positive away from `0` (structure `IsNorm`).  Its dual norm is

  `dualNorm N x = sSup { (x ⬝ᵥ y) / N y | y ≠ 0 }`,

exactly the expression appearing in the statement of Q805 (no absolute value in the numerator).

Linear maps are represented by matrices acting through `Matrix.mulVec`.  `SelfDual N u` says
`dualNorm N = N ∘ u`.

Main result (`Q805_classification`): for a norm `N` on `ℝ²` there is an invertible `u` with
`N* = N ∘ u` if and only if there is an invertible `L` such that the norm `N ∘ L` satisfies
`M* = M ∘ F` (reflection type) or `M* = M ∘ R_{π/m}` for some even `m ≥ 2` (rotational type).

Together with `Q805_rotational_symmetry` (`M ∘ R_{2π/m} = M` in the rotational case) this is the
main theorem of the answer.

## Relation to the printed statement

* The printed statement is phrased with unit balls and Euclidean polars: `C = L B` with
  `C = F C°` or `C = R_{π/m} C°`.  Here everything is phrased equivalently at the level of the
  norms themselves, using the gauge/support-function dictionary `B = {N ≤ 1}`,
  `(C°)`'s gauge `= (gauge of C)*`, and `gauge (L B) = N ∘ L⁻¹`.  Since `L` ranges over all of
  `GL₂(ℝ)`, writing the change of coordinates as `M = N ∘ L` is the same statement as `C = L B`.
* The dual norm is defined exactly as printed, i.e. `sSup {(x ⬝ᵥ y) / N y : y ≠ 0}` with no
  absolute value in the numerator; as observed in the source, this agrees with the usual dual
  norm.
* Norms are described axiomatically by the structure `IsNorm` (absolute homogeneity,
  subadditivity, positivity off `0`) on `V = Fin 2 → ℝ`, and linear maps are `2 × 2` matrices
  acting by `Matrix.mulVec`; `GL₂(ℝ)` membership is `IsUnit u.det`.
* No other mismatch: the formal statement `Q805_classification` is the printed equivalence
  (1) ↔ (2), and `Q805_rotational_symmetry` is the printed automatic symmetry (2.1).

## Versions

Lean 4.28.0 (`leanprover/lean4:v4.28.0`) and mathlib4 tag `v4.28.0`
(commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`).
-/

import Mathlib

open Matrix Real

noncomputable section

namespace Q805

/-- The plane `ℝ²`. -/
abbrev V := Fin 2 → ℝ

/-- Real `2 × 2` matrices. -/
abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

/-- A norm on the plane, described axiomatically. -/
structure IsNorm (N : V → ℝ) : Prop where
  smul : ∀ (c : ℝ) (x : V), N (c • x) = |c| * N x
  add_le : ∀ x y : V, N (x + y) ≤ N x + N y
  pos : ∀ x : V, x ≠ 0 → 0 < N x

/-- The dual norm, defined exactly as in the statement of Q805. -/
def dualNorm (N : V → ℝ) (x : V) : ℝ := sSup {r : ℝ | ∃ y : V, y ≠ 0 ∧ r = (x ⬝ᵥ y) / N y}

/-- `N* = N ∘ u`. -/
def SelfDual (N : V → ℝ) (u : Mat) : Prop := ∀ x, dualNorm N x = N (u *ᵥ x)

/-- Counterclockwise rotation by `θ`. -/
def rot (θ : ℝ) : Mat := !![cos θ, -sin θ; sin θ, cos θ]

/-- Reflection in the first coordinate axis. -/
def refl2 : Mat := !![1, 0; 0, -1]

/-- The Euclidean norm. -/
def euc (x : V) : ℝ := Real.sqrt (x ⬝ᵥ x)

/-! ### Elementary properties of norms -/

variable {N : V → ℝ}

theorem IsNorm.map_zero (hN : IsNorm N) : N 0 = 0 := by
  have h := hN.smul 0 0
  simpa using h

theorem IsNorm.nonneg (hN : IsNorm N) (x : V) : 0 ≤ N x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [hN.map_zero]
  · exact (hN.pos x hx).le

theorem IsNorm.neg (hN : IsNorm N) (x : V) : N (-x) = N x := by
  have h := hN.smul (-1) x
  simpa using h

theorem IsNorm.eq_zero_iff (hN : IsNorm N) (x : V) : N x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact (hN.pos x hx).ne' h
  · rintro rfl; exact hN.map_zero

theorem IsNorm.sub_le (hN : IsNorm N) (x y : V) : |N x - N y| ≤ N (x - y) := by
  have h1 : N x ≤ N (x - y) + N y := by
    have := hN.add_le (x - y) y
    simpa using this
  have h2 : N y ≤ N (x - y) + N x := by
    have h := hN.add_le (y - x) x
    have hyx : N (y - x) = N (x - y) := by
      have hxy : (y : V) - x = -(x - y) := by ring
      rw [hxy, hN.neg]
    rw [hyx] at h
    simpa using h
  rw [abs_le]
  constructor <;> linarith

theorem IsNorm.exists_upper (hN : IsNorm N) : ∃ C : ℝ, 0 < C ∧ ∀ x : V, N x ≤ C * ‖x‖ := by
  refine ⟨N (Pi.single 0 1) + N (Pi.single 1 1) + 1, ?_, ?_⟩
  · have h0 := hN.nonneg (Pi.single 0 1)
    have h1 := hN.nonneg (Pi.single 1 1)
    linarith
  · intro x
    have hx : x = x 0 • (Pi.single 0 1 : V) + x 1 • (Pi.single 1 1 : V) := by
      funext i; fin_cases i <;> simp
    have hb0 : |x 0| ≤ ‖x‖ := by
      have := norm_le_pi_norm x 0
      rwa [Real.norm_eq_abs] at this
    have hb1 : |x 1| ≤ ‖x‖ := by
      have := norm_le_pi_norm x 1
      rwa [Real.norm_eq_abs] at this
    have hn0 := hN.nonneg (Pi.single 0 1 : V)
    have hn1 := hN.nonneg (Pi.single 1 1 : V)
    have hxn : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
    calc N x = N (x 0 • (Pi.single 0 1 : V) + x 1 • (Pi.single 1 1 : V)) := by rw [← hx]
      _ ≤ N (x 0 • (Pi.single 0 1 : V)) + N (x 1 • (Pi.single 1 1 : V)) := hN.add_le _ _
      _ = |x 0| * N (Pi.single 0 1 : V) + |x 1| * N (Pi.single 1 1 : V) := by
          rw [hN.smul, hN.smul]
      _ ≤ ‖x‖ * N (Pi.single 0 1 : V) + ‖x‖ * N (Pi.single 1 1 : V) := by
          gcongr
      _ ≤ (N (Pi.single 0 1 : V) + N (Pi.single 1 1 : V) + 1) * ‖x‖ := by nlinarith

theorem IsNorm.continuous (hN : IsNorm N) : Continuous N := by
  obtain ⟨C, hC, hbound⟩ := hN.exists_upper
  rw [Metric.continuous_iff]
  intro b ε hε
  refine ⟨ε / C, by positivity, fun a ha => ?_⟩
  have h1 : |N a - N b| ≤ N (a - b) := hN.sub_le a b
  have h2 : N (a - b) ≤ C * ‖a - b‖ := hbound _
  have h3 : ‖a - b‖ = dist a b := (dist_eq_norm a b).symm
  rw [Real.dist_eq]
  have h4 : C * dist a b < C * (ε / C) := by
    exact mul_lt_mul_of_pos_left ha hC
  have h5 : C * (ε / C) = ε := by field_simp
  rw [h3] at h2
  linarith

theorem IsNorm.exists_lower (hN : IsNorm N) : ∃ c : ℝ, 0 < c ∧ ∀ x : V, c * ‖x‖ ≤ N x := by
  have hcomp : IsCompact (Metric.sphere (0 : V) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : V) 1).Nonempty :=
    NormedSpace.sphere_nonempty.2 zero_le_one
  obtain ⟨x₀, hx₀mem, hx₀min⟩ := hcomp.exists_isMinOn hne hN.continuous.continuousOn
  have hx₀ne : x₀ ≠ 0 := by
    intro h
    rw [h] at hx₀mem
    simp at hx₀mem
  refine ⟨N x₀, hN.pos _ hx₀ne, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp [hN.map_zero]
  · have hnx : (0:ℝ) < ‖x‖ := norm_pos_iff.2 hx
    have hmem : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : V) 1 := by
      simp [norm_smul]
      field_simp
    have hle : N x₀ ≤ N (‖x‖⁻¹ • x) := hx₀min hmem
    rw [hN.smul] at hle
    rw [abs_of_pos (inv_pos.2 hnx)] at hle
    calc N x₀ * ‖x‖ ≤ (‖x‖⁻¹ * N x) * ‖x‖ := by
          exact mul_le_mul_of_nonneg_right hle hnx.le
      _ = N x := by field_simp

/-! ### The dual norm -/

theorem dotProduct_abs_le (x y : V) : |x ⬝ᵥ y| ≤ 2 * ‖x‖ * ‖y‖ := by
  have hb0 : |x 0| ≤ ‖x‖ := by
    have := norm_le_pi_norm x 0; rwa [Real.norm_eq_abs] at this
  have hb1 : |x 1| ≤ ‖x‖ := by
    have := norm_le_pi_norm x 1; rwa [Real.norm_eq_abs] at this
  have hc0 : |y 0| ≤ ‖y‖ := by
    have := norm_le_pi_norm y 0; rwa [Real.norm_eq_abs] at this
  have hc1 : |y 1| ≤ ‖y‖ := by
    have := norm_le_pi_norm y 1; rwa [Real.norm_eq_abs] at this
  have e : x ⬝ᵥ y = x 0 * y 0 + x 1 * y 1 := by
    simp [dotProduct, Fin.sum_univ_two]
  rw [e]
  have h1 : |x 0 * y 0 + x 1 * y 1| ≤ |x 0 * y 0| + |x 1 * y 1| := abs_add_le _ _
  rw [abs_mul, abs_mul] at h1
  have h2 : |x 0| * |y 0| ≤ ‖x‖ * ‖y‖ := by
    apply mul_le_mul hb0 hc0 (abs_nonneg _) (norm_nonneg _)
  have h3 : |x 1| * |y 1| ≤ ‖x‖ * ‖y‖ := by
    apply mul_le_mul hb1 hc1 (abs_nonneg _) (norm_nonneg _)
  linarith

theorem dualNorm_bddAbove (hN : IsNorm N) (x : V) :
    BddAbove {r : ℝ | ∃ y : V, y ≠ 0 ∧ r = (x ⬝ᵥ y) / N y} := by
  obtain ⟨c, hc, hlow⟩ := hN.exists_lower
  refine ⟨2 * ‖x‖ / c, ?_⟩
  rintro r ⟨y, hy, rfl⟩
  have hny : (0:ℝ) < ‖y‖ := norm_pos_iff.2 hy
  have hNy : 0 < N y := hN.pos y hy
  have hcy : c * ‖y‖ ≤ N y := hlow y
  have habs : x ⬝ᵥ y ≤ 2 * ‖x‖ * ‖y‖ := le_trans (le_abs_self _) (dotProduct_abs_le x y)
  rw [div_le_div_iff₀ hNy hc]
  nlinarith [norm_nonneg x]

theorem dualNorm_setNonempty (x : V) :
    {r : ℝ | ∃ y : V, y ≠ 0 ∧ r = (x ⬝ᵥ y) / N y}.Nonempty := by
  refine ⟨(x ⬝ᵥ (Pi.single 0 1 : V)) / N (Pi.single 0 1), ⟨Pi.single 0 1, ?_, rfl⟩⟩
  intro h
  have : (Pi.single 0 1 : V) 0 = 0 := by rw [h]; rfl
  simp at this

/-- The basic inequality `⟨x, y⟩ ≤ N*(x) N(y)`. -/
theorem dotProduct_le_dualNorm (hN : IsNorm N) (x y : V) : x ⬝ᵥ y ≤ dualNorm N x * N y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [hN.map_zero, dotProduct]
  · have hNy : 0 < N y := hN.pos y hy
    have hmem : (x ⬝ᵥ y) / N y ∈ {r : ℝ | ∃ y : V, y ≠ 0 ∧ r = (x ⬝ᵥ y) / N y} := ⟨y, hy, rfl⟩
    have hle : (x ⬝ᵥ y) / N y ≤ dualNorm N x := le_csSup (dualNorm_bddAbove hN x) hmem
    rw [div_le_iff₀ hNy] at hle
    exact hle

theorem dualNorm_le_of_forall (hN : IsNorm N) {x : V} {t : ℝ}
    (h : ∀ y : V, x ⬝ᵥ y ≤ t * N y) : dualNorm N x ≤ t := by
  refine csSup_le (dualNorm_setNonempty x) ?_
  rintro r ⟨y, hy, rfl⟩
  have hNy : 0 < N y := hN.pos y hy
  rw [div_le_iff₀ hNy]
  exact h y

theorem dualNorm_nonneg (hN : IsNorm N) (x : V) : 0 ≤ dualNorm N x := by
  set y : V := Pi.single 0 1 with hy
  have hy0 : y ≠ 0 := by
    intro h
    have : (Pi.single 0 1 : V) 0 = 0 := by rw [← hy, h]; rfl
    simp at this
  have hNy : 0 < N y := hN.pos y hy0
  have h1 : (x ⬝ᵥ y) / N y ≤ dualNorm N x :=
    le_csSup (dualNorm_bddAbove hN x) ⟨y, hy0, rfl⟩
  have hy0' : (-y : V) ≠ 0 := by simpa using hy0
  have h2 : (x ⬝ᵥ (-y)) / N (-y) ≤ dualNorm N x :=
    le_csSup (dualNorm_bddAbove hN x) ⟨-y, hy0', rfl⟩
  rw [hN.neg, dotProduct_neg] at h2
  rcases le_or_gt 0 (x ⬝ᵥ y) with hs | hs
  · exact le_trans (div_nonneg hs hNy.le) h1
  · refine le_trans ?_ h2
    exact div_nonneg (by linarith) hNy.le

theorem isNorm_dualNorm (hN : IsNorm N) : IsNorm (dualNorm N) := by
  constructor
  · intro c x
    rcases eq_or_ne c 0 with rfl | hc
    · simp only [zero_smul, abs_zero, zero_mul]
      have h0 : dualNorm N 0 ≤ 0 := by
        refine dualNorm_le_of_forall hN fun y => ?_
        simp [dotProduct]
      exact le_antisymm h0 (dualNorm_nonneg hN 0)
    · have key : ∀ (d : ℝ) (z : V), dualNorm N (d • z) ≤ |d| * dualNorm N z := by
        intro d z
        refine dualNorm_le_of_forall hN fun y => ?_
        have hdot : (d • z) ⬝ᵥ y = d * (z ⬝ᵥ y) := by
          rw [smul_dotProduct, smul_eq_mul]
        rw [hdot]
        rcases le_or_gt 0 d with hd | hd
        · have h1 := dotProduct_le_dualNorm hN z y
          rw [abs_of_nonneg hd]
          nlinarith [hN.nonneg y, dualNorm_nonneg hN z]
        · have h1 := dotProduct_le_dualNorm hN z (-y)
          rw [dotProduct_neg] at h1
          rw [hN.neg] at h1
          rw [abs_of_neg hd]
          nlinarith [hN.nonneg y, dualNorm_nonneg hN z]
      have h1 := key c x
      have h2 := key c⁻¹ (c • x)
      rw [inv_smul_smul₀ hc, abs_inv] at h2
      have hcpos : 0 < |c| := abs_pos.2 hc
      have h3 : |c| * dualNorm N x ≤ dualNorm N (c • x) := by
        have h4 := mul_le_mul_of_nonneg_left h2 (abs_nonneg c)
        rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul] at h4
      linarith
  · intro x y
    refine dualNorm_le_of_forall hN fun z => ?_
    have h1 := dotProduct_le_dualNorm hN x z
    have h2 := dotProduct_le_dualNorm hN y z
    have h3 : (x + y) ⬝ᵥ z = x ⬝ᵥ z + y ⬝ᵥ z := add_dotProduct x y z
    rw [h3]
    nlinarith
  · intro x hx
    have hNx : 0 < N x := hN.pos x hx
    have hxx : 0 < x ⬝ᵥ x := by
      simp only [dotProduct, Fin.sum_univ_two]
      rcases (Function.ne_iff.1 hx) with ⟨i, hi⟩
      fin_cases i
      · have h0 : x 0 ≠ 0 := by simpa using hi
        nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), (mul_self_pos.2 h0)]
      · have h1 : x 1 ≠ 0 := by simpa using hi
        nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), (mul_self_pos.2 h1)]
    have hle : (x ⬝ᵥ x) / N x ≤ dualNorm N x :=
      le_csSup (dualNorm_bddAbove hN x) ⟨x, hx, rfl⟩
    have hpos : 0 < (x ⬝ᵥ x) / N x := div_pos hxx hNx
    linarith

/-- Precomposition with an invertible matrix preserves the norm axioms. -/
theorem IsNorm.comp (hN : IsNorm N) {A : Mat} (hA : IsUnit A.det) :
    IsNorm (fun x => N (A *ᵥ x)) := by
  constructor
  · intro c x
    show N (A *ᵥ (c • x)) = |c| * N (A *ᵥ x)
    rw [Matrix.mulVec_smul, hN.smul]
  · intro x y
    show N (A *ᵥ (x + y)) ≤ N (A *ᵥ x) + N (A *ᵥ y)
    rw [Matrix.mulVec_add]
    exact hN.add_le _ _
  · intro x hx
    show 0 < N (A *ᵥ x)
    refine hN.pos _ ?_
    intro h
    apply hx
    have h2 := congrArg (fun z => A⁻¹ *ᵥ z) h
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA] using h2

/-- `(N ∘ A)* = N* ∘ A⁻ᵀ`. -/
theorem dualNorm_comp {A : Mat} (hA : IsUnit A.det) (x : V) :
    dualNorm (fun z => N (A *ᵥ z)) x = dualNorm N ((A⁻¹)ᵀ *ᵥ x) := by
  unfold dualNorm
  congr 1
  ext r
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨A *ᵥ y, ?_, ?_⟩
    · intro h
      apply hy
      have h2 := congrArg (fun z => A⁻¹ *ᵥ z) h
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA] using h2
    · have hdot : ((A⁻¹)ᵀ *ᵥ x) ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ y := by
        rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
          Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
      rw [hdot]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨A⁻¹ *ᵥ z, ?_, ?_⟩
    · intro h
      apply hz
      have h2 := congrArg (fun w => A *ᵥ w) h
      simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA] using h2
    · have hAz : A *ᵥ (A⁻¹ *ᵥ z) = z := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec]
      have hdot : x ⬝ᵥ (A⁻¹ *ᵥ z) = ((A⁻¹)ᵀ *ᵥ x) ⬝ᵥ z := by
        rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
      show (((A⁻¹)ᵀ *ᵥ x) ⬝ᵥ z) / N z = (x ⬝ᵥ (A⁻¹ *ᵥ z)) / N (A *ᵥ (A⁻¹ *ᵥ z))
      rw [hAz, hdot]

/-- The bipolar theorem, in the language of norms. -/
theorem dualNorm_dualNorm (hN : IsNorm N) (x : V) : dualNorm (dualNorm N) x = N x := by
  have hD := isNorm_dualNorm hN
  refine le_antisymm ?_ ?_
  · refine dualNorm_le_of_forall hD fun y => ?_
    have h := dotProduct_le_dualNorm hN y x
    rw [dotProduct_comm] at h
    linarith
  · rcases eq_or_ne x 0 with rfl | hx
    · rw [hN.map_zero]
      exact dualNorm_nonneg hD 0
    · have hNx : 0 < N x := hN.pos x hx
      have hdom : ∀ z : (LinearPMap.mkSpanSingleton (K := ℝ) x (N x) hx).domain,
          (LinearPMap.mkSpanSingleton (K := ℝ) x (N x) hx) z ≤ N (z : V) := by
        rintro ⟨z, hz⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
        have hval : (LinearPMap.mkSpanSingleton (K := ℝ) x (N x) hx) ⟨c • x, hz⟩ = c • N x :=
          LinearPMap.mkSpanSingleton'_apply x (N x) _ c hz
        rw [hval, hN.smul, smul_eq_mul]
        rcases le_or_gt 0 c with hc | hc
        · rw [abs_of_nonneg hc]
        · rw [abs_of_neg hc]
          nlinarith [hN.nonneg x]
      obtain ⟨g, hg_eq, hg_le⟩ :=
        exists_extension_of_le_sublinear (LinearPMap.mkSpanSingleton (K := ℝ) x (N x) hx) N
          (fun c hc z => by rw [hN.smul, abs_of_pos hc]) hN.add_le hdom
      set w : V := fun i => g (Pi.single i 1) with hw
      have hgw : ∀ z : V, g z = z ⬝ᵥ w := by
        intro z
        have hz : z = z 0 • (Pi.single 0 1 : V) + z 1 • (Pi.single 1 1 : V) := by
          funext i; fin_cases i <;> simp
        rw [hz]
        simp [map_add, map_smul, dotProduct, Fin.sum_univ_two, hw]
      have hgx : g x = N x := by
        have := hg_eq ⟨x, Submodule.mem_span_singleton_self x⟩
        rw [this]
        exact LinearPMap.mkSpanSingleton_apply ℝ hx (N x)
      have hwle : dualNorm N w ≤ 1 := by
        refine dualNorm_le_of_forall hN fun z => ?_
        have h1 := hg_le z
        rw [hgw z] at h1
        rw [dotProduct_comm]
        linarith
      have hxw : x ⬝ᵥ w = N x := by rw [← hgw x, hgx]
      have hwne : w ≠ 0 := by
        intro h
        rw [h] at hxw
        simp [dotProduct] at hxw
        linarith
      have hwpos : 0 < dualNorm N w := hD.pos w hwne
      have hle : (x ⬝ᵥ w) / dualNorm N w ≤ dualNorm (dualNorm N) x :=
        le_csSup (dualNorm_bddAbove hD x) ⟨w, hwne, rfl⟩
      rw [hxw] at hle
      have : N x ≤ N x / dualNorm N w := by
        rw [le_div_iff₀ hwpos]
        nlinarith
      linarith

/-! ### The Euclidean norm -/

theorem euc_nonneg (x : V) : 0 ≤ euc x := Real.sqrt_nonneg _

theorem euc_sq (x : V) : euc x * euc x = x ⬝ᵥ x := by
  refine Real.mul_self_sqrt ?_
  simp only [dotProduct, Fin.sum_univ_two]
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

theorem euc_eq_zero (x : V) : euc x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h2 := euc_sq x
    rw [h] at h2
    simp only [dotProduct, Fin.sum_univ_two] at h2
    have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  · rintro rfl
    simp [euc, dotProduct]

theorem cauchy_schwarz (x y : V) : (x ⬝ᵥ y) ≤ euc x * euc y := by
  have h1 := euc_sq x
  have h2 := euc_sq y
  have hx := euc_nonneg x
  have hy := euc_nonneg y
  have hd : (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
    simp only [dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0)]
  nlinarith [mul_nonneg hx hy]

theorem euc_rot (θ : ℝ) (x : V) : euc (rot θ *ᵥ x) = euc x := by
  unfold euc
  congr 1
  simp [rot, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- A norm equal to its own dual is the Euclidean norm. -/
theorem eq_euc_of_selfdual (hN : IsNorm N) (h : ∀ x, dualNorm N x = N x) : ∀ x, N x = euc x := by
  have h1 : ∀ x, euc x ≤ N x := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · rw [hN.map_zero, (euc_eq_zero 0).2 rfl]
    · have hpos := hN.pos x hx
      have hle : x ⬝ᵥ x ≤ dualNorm N x * N x := dotProduct_le_dualNorm hN x x
      rw [h x] at hle
      nlinarith [euc_sq x, euc_nonneg x]
  have h2 : ∀ x, N x ≤ euc x := by
    intro x
    rw [← h x]
    refine dualNorm_le_of_forall hN fun y => ?_
    calc x ⬝ᵥ y ≤ euc x * euc y := cauchy_schwarz x y
      _ ≤ euc x * N y := mul_le_mul_of_nonneg_left (h1 y) (euc_nonneg x)
  exact fun x => le_antisymm (h2 x) (h1 x)

/-! ### Rotations and reflections -/

theorem rot_mul (a b : ℝ) : rot a * rot b = rot (a + b) := by
  simp [rot, Real.cos_add, Real.sin_add]
  constructor <;> ring

theorem rot_zero : rot 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot]

theorem rot_pi : rot π = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot]

theorem rot_transpose (θ : ℝ) : rot θ * (rot θ)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp [Real.sin_sq_add_cos_sq]

theorem refl2_transpose : refl2 * refl2ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [refl2, Matrix.mul_apply, Fin.sum_univ_two]

theorem rot_det (θ : ℝ) : (rot θ).det = 1 := by
  simp [rot, Matrix.det_fin_two_of]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem refl2_mul_rot (θ : ℝ) : refl2 * rot θ = rot (-θ) * refl2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [refl2, rot, Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_cos_sin {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) : ∃ θ : ℝ, cos θ = a ∧ sin θ = b := by
  have ha1 : -1 ≤ a := by nlinarith
  have ha2 : a ≤ 1 := by nlinarith
  rcases le_or_gt 0 b with hb | hb
  · refine ⟨Real.arccos a, Real.cos_arccos ha1 ha2, ?_⟩
    rw [Real.sin_arccos, show 1 - a ^ 2 = b ^ 2 by linarith]
    exact Real.sqrt_sq hb
  · refine ⟨-Real.arccos a, by rw [Real.cos_neg]; exact Real.cos_arccos ha1 ha2, ?_⟩
    rw [Real.sin_neg, Real.sin_arccos, show 1 - a ^ 2 = b ^ 2 by linarith,
      show b ^ 2 = (-b) ^ 2 by ring, Real.sqrt_sq (by linarith)]
    ring

/-- Every orthogonal `2 × 2` matrix is a rotation or a rotation composed with `refl2`. -/
theorem orthogonal_classify {Q : Mat} (hQ : Q * Qᵀ = 1) :
    (∃ θ : ℝ, Q = rot θ) ∨ ∃ θ : ℝ, Q = rot θ * refl2 := by
  have h00 : (Q * Qᵀ) 0 0 = (1 : Mat) 0 0 := by rw [hQ]
  have h01 : (Q * Qᵀ) 0 1 = (1 : Mat) 0 1 := by rw [hQ]
  have h11 : (Q * Qᵀ) 1 1 = (1 : Mat) 1 1 := by rw [hQ]
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h11
  have hdet : (Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0) * (Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0) = 1 := by
    nlinarith
  rcases mul_self_eq_one_iff.mp hdet with he | he
  · left
    have hc : Q 1 0 = -Q 0 1 := by linear_combination (-(Q 1 0)) * h00 + Q 0 0 * h01 - Q 0 1 * he
    have hd : Q 1 1 = Q 0 0 := by linear_combination (-(Q 1 1)) * h00 + Q 0 1 * h01 + Q 0 0 * he
    obtain ⟨θ, hcos, hsin⟩ := exists_cos_sin (a := Q 0 0) (b := -Q 0 1) (by nlinarith)
    have hb : Q 0 1 = -sin θ := by rw [hsin]; ring
    refine ⟨θ, ?_⟩
    rw [Matrix.eta_fin_two Q, hc, hd, hb, ← hcos, rot]
    norm_num
  · right
    have hc : Q 1 0 = Q 0 1 := by linear_combination (-(Q 1 0)) * h00 + Q 0 0 * h01 - Q 0 1 * he
    have hd : Q 1 1 = -Q 0 0 := by linear_combination (-(Q 1 1)) * h00 + Q 0 1 * h01 + Q 0 0 * he
    obtain ⟨θ, hcos, hsin⟩ := exists_cos_sin (a := Q 0 0) (b := Q 0 1) (by nlinarith)
    refine ⟨θ, ?_⟩
    rw [Matrix.eta_fin_two Q, hc, hd, ← hcos, ← hsin]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rot, refl2, Matrix.mul_apply, Fin.sum_univ_two]

theorem isUnit_det_of_orthogonal {Q : Mat} (hQ : Q * Qᵀ = 1) : IsUnit Q.det := by
  have h : Q.det * Q.det = 1 := by
    have hd := congrArg Matrix.det hQ
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0] at h
  norm_num at h

theorem inv_of_orthogonal {Q : Mat} (hQ : Q * Qᵀ = 1) : Q⁻¹ = Qᵀ :=
  Matrix.inv_eq_right_inv hQ

/-! ### Power bounded matrices -/

/-- `S` is power bounded if the operators `Sⁿ` are uniformly bounded. -/
def PowerBounded (S : Mat) : Prop := ∃ K : ℝ, ∀ (n : ℕ) (x : V), ‖(S ^ n) *ᵥ x‖ ≤ K * ‖x‖

theorem exists_opNorm_bound (A : Mat) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : V, ‖A *ᵥ x‖ ≤ K * ‖x‖ := by
  refine ⟨|A 0 0| + |A 0 1| + |A 1 0| + |A 1 1|, by positivity, fun x => ?_⟩
  have hx0 : |x 0| ≤ ‖x‖ := by
    have := norm_le_pi_norm x 0; rwa [Real.norm_eq_abs] at this
  have hx1 : |x 1| ≤ ‖x‖ := by
    have := norm_le_pi_norm x 1; rwa [Real.norm_eq_abs] at this
  have hxn : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
  have hrow : ∀ i : Fin 2, ‖(A *ᵥ x) i‖
      ≤ (|A 0 0| + |A 0 1| + |A 1 0| + |A 1 1|) * ‖x‖ := by
    rw [Fin.forall_fin_two]
    constructor <;>
    · rw [Real.norm_eq_abs]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul]
      have h1 : |A 0 0| * |x 0| ≤ |A 0 0| * ‖x‖ :=
        mul_le_mul_of_nonneg_left hx0 (abs_nonneg _)
      have h2 : |A 0 1| * |x 1| ≤ |A 0 1| * ‖x‖ :=
        mul_le_mul_of_nonneg_left hx1 (abs_nonneg _)
      have h3 : |A 1 0| * |x 0| ≤ |A 1 0| * ‖x‖ :=
        mul_le_mul_of_nonneg_left hx0 (abs_nonneg _)
      have h4 : |A 1 1| * |x 1| ≤ |A 1 1| * ‖x‖ :=
        mul_le_mul_of_nonneg_left hx1 (abs_nonneg _)
      nlinarith [abs_nonneg (A 0 0), abs_nonneg (A 0 1), abs_nonneg (A 1 0), abs_nonneg (A 1 1)]
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  exact hrow

theorem conj_pow (S T : Mat) (hT : IsUnit T.det) (n : ℕ) :
    (T * S * T⁻¹) ^ n = T * S ^ n * T⁻¹ := by
  induction n with
  | zero => simp [Matrix.mul_nonsing_inv _ hT]
  | succ k ih =>
      have hcancel : ∀ Z : Mat, T⁻¹ * (T * Z) = Z := by
        intro Z; rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hT, Matrix.one_mul]
      rw [pow_succ, ih, pow_succ]
      simp [Matrix.mul_assoc, hcancel]

theorem PowerBounded.conj {S T : Mat} (hS : PowerBounded S) (hT : IsUnit T.det) :
    PowerBounded (T * S * T⁻¹) := by
  obtain ⟨K, hK⟩ := hS
  obtain ⟨K1, hK1nn, hK1⟩ := exists_opNorm_bound T
  obtain ⟨K2, hK2nn, hK2⟩ := exists_opNorm_bound T⁻¹
  refine ⟨K1 * (max K 0) * K2, fun n x => ?_⟩
  rw [conj_pow S T hT n]
  have hsplit : (T * S ^ n * T⁻¹) *ᵥ x = T *ᵥ (S ^ n *ᵥ (T⁻¹ *ᵥ x)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hsplit]
  have h1 : ‖T *ᵥ (S ^ n *ᵥ (T⁻¹ *ᵥ x))‖ ≤ K1 * ‖S ^ n *ᵥ (T⁻¹ *ᵥ x)‖ := hK1 _
  have h2 : ‖S ^ n *ᵥ (T⁻¹ *ᵥ x)‖ ≤ K * ‖T⁻¹ *ᵥ x‖ := hK n _
  have h2' : ‖S ^ n *ᵥ (T⁻¹ *ᵥ x)‖ ≤ max K 0 * ‖T⁻¹ *ᵥ x‖ := by
    refine le_trans h2 ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have h3 : ‖T⁻¹ *ᵥ x‖ ≤ K2 * ‖x‖ := hK2 x
  have hK0 : (0:ℝ) ≤ max K 0 := le_max_right _ _
  calc ‖T *ᵥ (S ^ n *ᵥ (T⁻¹ *ᵥ x))‖ ≤ K1 * ‖S ^ n *ᵥ (T⁻¹ *ᵥ x)‖ := h1
    _ ≤ K1 * (max K 0 * ‖T⁻¹ *ᵥ x‖) := by
        exact mul_le_mul_of_nonneg_left h2' hK1nn
    _ ≤ K1 * (max K 0 * (K2 * ‖x‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ hK1nn
        exact mul_le_mul_of_nonneg_left h3 hK0
    _ = K1 * max K 0 * K2 * ‖x‖ := by ring

theorem mulVec_smul_pow {S : Mat} {w : V} {l : ℝ} (hSw : S *ᵥ w = l • w) (n : ℕ) :
    (S ^ n) *ᵥ w = (l ^ n) • w := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hSw, Matrix.mulVec_smul, ih, smul_smul, pow_succ]
      rw [mul_comm]

theorem not_powerBounded_of_eigenvalue {S : Mat} {w : V} {l : ℝ} (hw : w ≠ 0)
    (hSw : S *ᵥ w = l • w) (hl : 1 < |l|) : ¬ PowerBounded S := by
  rintro ⟨K, hK⟩
  have hwn : (0:ℝ) < ‖w‖ := norm_pos_iff.2 hw
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt K hl
  have h1 := hK n w
  rw [mulVec_smul_pow hSw n, norm_smul, Real.norm_eq_abs, abs_pow] at h1
  nlinarith

theorem not_powerBounded_jordan {a : ℝ} (ha : a ≠ 0) : ¬ PowerBounded (!![-1, a; 0, -1] : Mat) := by
  have hpow : ∀ n : ℕ, (!![-1, a; 0, -1] : Mat) ^ n
      = !![(-1 : ℝ) ^ n, (-1 : ℝ) ^ (n + 1) * n * a; 0, (-1 : ℝ) ^ n] := by
    intro n
    induction n with
    | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
    | succ k ih =>
        rw [pow_succ, ih]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ] <;> ring
  rintro ⟨K, hK⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (K / |a|)
  have h1 := hK n (Pi.single 1 1)
  rw [hpow n] at h1
  have h2 : ‖(!![(-1 : ℝ) ^ n, (-1 : ℝ) ^ (n + 1) * n * a; 0, (-1 : ℝ) ^ n] : Mat)
      *ᵥ (Pi.single 1 1 : V)‖ ≥ |(-1 : ℝ) ^ (n + 1) * n * a| := by
    have := norm_le_pi_norm
      ((!![(-1 : ℝ) ^ n, (-1 : ℝ) ^ (n + 1) * n * a; 0, (-1 : ℝ) ^ n] : Mat) *ᵥ
        (Pi.single 1 1 : V)) 0
    rw [Real.norm_eq_abs] at this
    refine le_trans (le_of_eq ?_) this
    congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h3 : ‖(Pi.single 1 1 : V)‖ = 1 := by
    refine le_antisymm ?_ ?_
    · rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i; fin_cases i <;> simp
    · have := norm_le_pi_norm (Pi.single 1 (1:ℝ) : V) 1
      simpa using this
  rw [h3, mul_one] at h1
  have h4 : |(-1 : ℝ) ^ (n + 1) * n * a| = n * |a| := by
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  rw [h4] at h2
  have hapos : 0 < |a| := abs_pos.2 ha
  rw [div_lt_iff₀ hapos] at hn
  linarith

theorem not_powerBounded_jordan' {a : ℝ} (ha : a ≠ 0) :
    ¬ PowerBounded (!![-1, 0; a, -1] : Mat) := by
  have hpow : ∀ n : ℕ, (!![-1, 0; a, -1] : Mat) ^ n
      = !![(-1 : ℝ) ^ n, 0; (-1 : ℝ) ^ (n + 1) * n * a, (-1 : ℝ) ^ n] := by
    intro n
    induction n with
    | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
    | succ k ih =>
        rw [pow_succ, ih]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ] <;> ring
  rintro ⟨K, hK⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (K / |a|)
  have h1 := hK n (Pi.single 0 1)
  rw [hpow n] at h1
  have h2 : ‖(!![(-1 : ℝ) ^ n, 0; (-1 : ℝ) ^ (n + 1) * n * a, (-1 : ℝ) ^ n] : Mat)
      *ᵥ (Pi.single 0 1 : V)‖ ≥ |(-1 : ℝ) ^ (n + 1) * n * a| := by
    have := norm_le_pi_norm
      ((!![(-1 : ℝ) ^ n, 0; (-1 : ℝ) ^ (n + 1) * n * a, (-1 : ℝ) ^ n] : Mat) *ᵥ
        (Pi.single 0 1 : V)) 1
    rw [Real.norm_eq_abs] at this
    refine le_trans (le_of_eq ?_) this
    congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h3 : ‖(Pi.single 0 1 : V)‖ = 1 := by
    refine le_antisymm ?_ ?_
    · rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i; fin_cases i <;> simp
    · have := norm_le_pi_norm (Pi.single 0 (1:ℝ) : V) 0
      simpa using this
  rw [h3, mul_one] at h1
  have h4 : |(-1 : ℝ) ^ (n + 1) * n * a| = n * |a| := by
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  rw [h4] at h2
  have hapos : 0 < |a| := abs_pos.2 ha
  rw [div_lt_iff₀ hapos] at hn
  linarith

/-! ### The normal form of an admissible duality (Lemma 5.1) -/

/-- The "cosquare" `u u⁻ᵀ`. -/
def cosq (u : Mat) : Mat := u * (uᵀ)⁻¹

theorem cosq_congr {u T : Mat} (hT : IsUnit T.det) :
    cosq (T * u * Tᵀ) = T * cosq u * T⁻¹ := by
  have hTt : IsUnit (Tᵀ).det := by rwa [Matrix.det_transpose]
  unfold cosq
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have hcancel : Tᵀ * (Tᵀ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hTt
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Tᵀ), hcancel, Matrix.one_mul]

theorem conj_J (T : Mat) : T * (!![0, -1; 1, 0] : Mat) * Tᵀ = T.det • (!![0, -1; 1, 0] : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem sign_normalizer (p : ℝ) :
    ∃ f : ℝ, f ≠ 0 ∧ (p * (f * f) = 1 ∨ p * (f * f) = 0 ∨ p * (f * f) = -1) := by
  rcases lt_trichotomy p 0 with h | h | h
  · have hp : 0 < -p := by linarith
    have hs : 0 < Real.sqrt (-p) := Real.sqrt_pos.2 hp
    refine ⟨1 / Real.sqrt (-p), by positivity, Or.inr (Or.inr ?_)⟩
    have hsq : Real.sqrt (-p) * Real.sqrt (-p) = -p := Real.mul_self_sqrt hp.le
    field_simp
    linarith [hsq]
  · exact ⟨1, one_ne_zero, Or.inr (Or.inl (by rw [h]; ring))⟩
  · have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 h
    refine ⟨1 / Real.sqrt p, by positivity, Or.inl ?_⟩
    have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt h.le
    field_simp
    linarith [hsq]

theorem sylvester_diagonalize (H : Mat) (hsym : Hᵀ = H) :
    ∃ T : Mat, IsUnit T.det ∧ ∃ p r : ℝ, T * H * Tᵀ = !![p, 0; 0, r] := by
  have hb : H 1 0 = H 0 1 := by
    have h := congrFun (congrFun hsym 1) 0
    simpa [Matrix.transpose_apply] using h.symm
  have hH : H = !![H 0 0, H 0 1; H 0 1, H 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb]
  rcases eq_or_ne (H 0 0) 0 with ha | ha
  · rcases eq_or_ne (H 1 1) 0 with hd | hd
    · rcases eq_or_ne (H 0 1) 0 with hbz | hbz
      · refine ⟨1, by simp, 0, 0, ?_⟩
        rw [Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hb, ha, hd, hbz]
      · refine ⟨!![1, 1; 1, -1], ?_, 2 * H 0 1, -(2 * H 0 1), ?_⟩
        · rw [Matrix.det_fin_two_of]
          norm_num
        · rw [hH, ha, hd]
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    · refine ⟨!![1, -(H 0 1) / H 1 1; 0, 1], ?_, -(H 0 1 * H 0 1) / H 1 1, H 1 1, ?_⟩
      · rw [Matrix.det_fin_two_of]
        norm_num
      · rw [hH, ha]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  · refine ⟨!![1, 0; -(H 0 1) / H 0 0, 1], ?_, H 0 0,
      H 1 1 - H 0 1 * H 0 1 / H 0 0, ?_⟩
    · rw [Matrix.det_fin_two_of]
      norm_num
    · rw [hH]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem sylvester2 (H : Mat) (hsym : Hᵀ = H) :
    ∃ (T : Mat) (d₀ d₁ : ℝ), IsUnit T.det ∧ (d₀ = 1 ∨ d₀ = 0 ∨ d₀ = -1) ∧
      (d₁ = 1 ∨ d₁ = 0 ∨ d₁ = -1) ∧ T * H * Tᵀ = !![d₀, 0; 0, d₁] := by
  obtain ⟨T₁, hT₁, p, r, hdiag⟩ := sylvester_diagonalize H hsym
  obtain ⟨f, hf, hfp⟩ := sign_normalizer p
  obtain ⟨g, hg, hgr⟩ := sign_normalizer r
  refine ⟨!![f, 0; 0, g] * T₁, p * (f * f), r * (g * g), ?_, hfp, hgr, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_fin_two_of]
    refine IsUnit.mul ?_ hT₁
    simp only [mul_zero, sub_zero]
    exact (isUnit_iff_ne_zero).2 (by simp [hf, hg])
  · have hassoc : (!![f, 0; 0, g] * T₁) * H * (!![f, 0; 0, g] * T₁)ᵀ
        = !![f, 0; 0, g] * (T₁ * H * T₁ᵀ) * (!![f, 0; 0, g] : Mat)ᵀ := by
      rw [Matrix.transpose_mul]
      simp [Matrix.mul_assoc]
    rw [hassoc, hdiag]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem bad_one_zero {e s : ℝ} (he : e = 1 ∨ e = -1) (hs : s ≠ 0) :
    ¬ PowerBounded (cosq !![e, -s; s, 0]) := by
  have hcosq : cosq !![e, -s; s, (0:ℝ)] = !![-1, -2 * e / s; 0, -1] := by
    unfold cosq
    have htr : (!![e, -s; s, (0:ℝ)] : Mat)ᵀ = !![e, s; -s, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hinv : (!![e, s; -s, (0:ℝ)] : Mat)⁻¹ = (s ^ 2)⁻¹ • !![0, -s; s, e] := by
      apply Matrix.inv_eq_right_inv
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
    rw [htr, hinv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  rw [hcosq]
  have hne : -2 * e / s ≠ 0 := by
    have he0 : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
    exact div_ne_zero (by simpa using he0) hs
  exact not_powerBounded_jordan hne

theorem bad_zero_one {e s : ℝ} (he : e = 1 ∨ e = -1) (hs : s ≠ 0) :
    ¬ PowerBounded (cosq !![0, -s; s, e]) := by
  have hcosq : cosq !![(0:ℝ), -s; s, e] = !![-1, 0; 2 * e / s, -1] := by
    unfold cosq
    have htr : (!![(0:ℝ), -s; s, e] : Mat)ᵀ = !![0, s; -s, e] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hinv : (!![(0:ℝ), s; -s, e] : Mat)⁻¹ = (s ^ 2)⁻¹ • !![e, -s; s, 0] := by
      apply Matrix.inv_eq_right_inv
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
    rw [htr, hinv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  rw [hcosq]
  have hne : 2 * e / s ≠ 0 := by
    have he0 : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
    exact div_ne_zero (by simpa using he0) hs
  exact not_powerBounded_jordan' hne

/-- The cosquare of an indefinite normal form, in its diagonalised parametrisation. -/
theorem not_powerBounded_hyperbolic {t : ℝ} (ht : t ≠ 0) (ht1 : t * t ≠ 1) :
    ¬ PowerBounded (((1:ℝ) - t * t)⁻¹ • !![1 + t * t, 2 * t; 2 * t, 1 + t * t]) := by
  have h1 : (1:ℝ) - t ≠ 0 := by
    intro h; apply ht1; have : t = 1 := by linarith
    rw [this]; norm_num
  have h2 : (1:ℝ) + t ≠ 0 := by
    intro h; apply ht1; have : t = -1 := by linarith
    rw [this]; norm_num
  have h3 : (1:ℝ) - t * t ≠ 0 := fun h => mul_ne_zero h1 h2 (by nlinarith)
  have h4 : (1:ℝ) - t ^ 2 ≠ 0 := fun h => h3 (by nlinarith)
  set M : Mat := ((1:ℝ) - t * t)⁻¹ • !![1 + t * t, 2 * t; 2 * t, 1 + t * t] with hM
  set lam : ℝ := (1 + t) / (1 - t) with hlam
  have hev1 : M *ᵥ ![1, 1] = lam • (![1, 1] : V) := by
    rw [hM, hlam]
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp <;> ring
  have hev2 : M *ᵥ ![1, -1] = lam⁻¹ • (![1, -1] : V) := by
    rw [hM, hlam]
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp <;> ring
  have hw1 : (![1, 1] : V) ≠ 0 := by
    intro h; have := congrFun h 0; norm_num at this
  have hw2 : (![1, -1] : V) ≠ 0 := by
    intro h; have := congrFun h 0; norm_num at this
  have hlam0 : lam ≠ 0 := div_ne_zero h2 h1
  have habs : |lam| ≠ 1 := by
    intro h
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h with h5 | h5
    · rw [hlam, div_eq_iff h1] at h5; exact ht (by linarith)
    · rw [hlam, div_eq_iff h1] at h5; exact h2 (by linarith)
  rcases lt_trichotomy |lam| 1 with hc | hc | hc
  · have hpos : 0 < |lam| := abs_pos.2 hlam0
    have hgt : 1 < |lam⁻¹| := by
      rw [abs_inv, lt_inv_comm₀ (by norm_num) hpos]
      simpa using hc
    exact not_powerBounded_of_eigenvalue hw2 hev2 hgt
  · exact absurd hc habs
  · exact not_powerBounded_of_eigenvalue hw1 hev1 hc

theorem bad_indef {e s : ℝ} (he : e = 1 ∨ e = -1) (hs : s ≠ 0) (hs1 : s * s ≠ 1) :
    ¬ PowerBounded (cosq !![e, -s; s, -e]) := by
  have hd : s ^ 2 - 1 ≠ 0 := fun h => hs1 (by nlinarith)
  have hd2 : (1:ℝ) - s ^ 2 ≠ 0 := fun h => hs1 (by nlinarith)
  have hcosq : cosq !![e, -s; s, -e]
      = ((1:ℝ) - (e * s) * (e * s))⁻¹ •
        !![1 + (e * s) * (e * s), 2 * (e * s); 2 * (e * s), 1 + (e * s) * (e * s)] := by
    unfold cosq
    have htr : (!![e, -s; s, -e] : Mat)ᵀ = !![e, s; -s, -e] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hinv : (!![e, s; -s, -e] : Mat)⁻¹ = (s * s - 1)⁻¹ • !![-e, -s; s, e] := by
      apply Matrix.inv_eq_right_inv
      rcases he with rfl | rfl <;> ext i j <;>
        fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
    rw [htr, hinv]
    rcases he with rfl | rfl <;> ext i j <;>
      fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  rw [hcosq]
  have hes : e * s ≠ 0 := by
    have he0 : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
    exact mul_ne_zero he0 hs
  have hes1 : (e * s) * (e * s) ≠ 1 := by
    rcases he with rfl | rfl <;> simpa using hs1
  exact not_powerBounded_hyperbolic hes hes1

theorem normal_form_aux {d₀ d₁ s : ℝ} (h0 : d₀ = 1 ∨ d₀ = 0 ∨ d₀ = -1)
    (h1 : d₁ = 1 ∨ d₁ = 0 ∨ d₁ = -1) (hdet : d₀ * d₁ + s * s ≠ 0)
    (hpb : PowerBounded (cosq !![d₀, -s; s, d₁])) :
    ∃ l : ℝ, 0 < l ∧ (!![d₀, -s; s, d₁] : Mat) * (!![d₀, -s; s, d₁] : Mat)ᵀ = l • 1 := by
  have good : ∀ l : ℝ, 0 < l → d₀ * d₀ + s * s = l → d₁ * d₁ + s * s = l → d₀ * s - s * d₁ = 0 →
      ∃ l : ℝ, 0 < l ∧ (!![d₀, -s; s, d₁] : Mat) * (!![d₀, -s; s, d₁] : Mat)ᵀ = l • 1 := by
    intro l hl e0 e1 e2
    refine ⟨l, hl, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith
  rcases h0 with rfl | rfl | rfl <;> rcases h1 with rfl | rfl | rfl
  · exact good (1 + s * s) (by nlinarith [mul_self_nonneg s]) (by ring) (by ring) (by ring)
  · have hs : s ≠ 0 := by intro h; apply hdet; rw [h]; ring
    exact absurd hpb (bad_one_zero (Or.inl rfl) hs)
  · rcases eq_or_ne s 0 with rfl | hs
    · exact good 1 one_pos (by ring) (by ring) (by ring)
    · have hs1 : s * s ≠ 1 := by intro h; apply hdet; rw [h]; ring
      have hrw : (!![(1 : ℝ), -s; s, -1] : Mat) = !![(1 : ℝ), -s; s, -(1 : ℝ)] := rfl
      rw [hrw] at hpb
      exact absurd hpb (bad_indef (Or.inl rfl) hs hs1)
  · have hs : s ≠ 0 := by intro h; apply hdet; rw [h]; ring
    exact absurd hpb (bad_zero_one (Or.inl rfl) hs)
  · have hs : s ≠ 0 := by intro h; apply hdet; rw [h]; ring
    exact good (s * s) (mul_self_pos.2 hs) (by ring) (by ring) (by ring)
  · have hs : s ≠ 0 := by intro h; apply hdet; rw [h]; ring
    exact absurd hpb (bad_zero_one (Or.inr rfl) hs)
  · rcases eq_or_ne s 0 with rfl | hs
    · exact good 1 one_pos (by ring) (by ring) (by ring)
    · have hs1 : s * s ≠ 1 := by intro h; apply hdet; rw [h]; ring
      have hrw : (!![(-1 : ℝ), -s; s, 1] : Mat) = !![(-1 : ℝ), -s; s, -(-1 : ℝ)] := by norm_num
      rw [hrw] at hpb
      exact absurd hpb (bad_indef (Or.inr rfl) hs hs1)
  · have hs : s ≠ 0 := by intro h; apply hdet; rw [h]; ring
    exact absurd hpb (bad_one_zero (Or.inr rfl) hs)
  · exact good (1 + s * s) (by nlinarith [mul_self_nonneg s]) (by ring) (by ring) (by ring)

theorem good_case {u T v : Mat} (hT : IsUnit T.det) (hv : T * u * Tᵀ = v) {l : ℝ}
    (hl : 0 < l) (hvv : v * vᵀ = l • 1) :
    ∃ R : Mat, IsUnit R.det ∧ (R * u * Rᵀ) * (R * u * Rᵀ)ᵀ = 1 := by
  have ha0 : 0 < Real.sqrt l := Real.sqrt_pos.2 hl
  have haa : Real.sqrt l * Real.sqrt l = l := Real.mul_self_sqrt hl.le
  have hsa : 0 < Real.sqrt (Real.sqrt l) := Real.sqrt_pos.2 ha0
  have hsaa : Real.sqrt (Real.sqrt l) * Real.sqrt (Real.sqrt l) = Real.sqrt l :=
    Real.mul_self_sqrt ha0.le
  set k : ℝ := 1 / Real.sqrt (Real.sqrt l) with hk
  have hk0 : k ≠ 0 := by rw [hk]; positivity
  have hkk : k * k = 1 / Real.sqrt l := by
    rw [hk, div_mul_div_comm, one_mul, hsaa]
  refine ⟨k • T, ?_, ?_⟩
  · rw [Matrix.det_smul]
    simp only [Fintype.card_fin]
    exact (IsUnit.pow 2 (isUnit_iff_ne_zero.2 hk0)).mul hT
  · have hR : (k • T) * u * (k • T)ᵀ = (k * k) • v := by
      simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [hv]
    rw [hR]
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hvv, smul_smul]
    have hfin : (k * k) * (k * k) * l = 1 := by
      rw [hkk]
      field_simp
      linarith [haa]
    rw [hfin, one_smul]

/-- Lemma 5.1: an invertible matrix with power-bounded cosquare is congruent, up to a positive
scalar, to an orthogonal matrix. -/
theorem normal_form {u : Mat} (hu : IsUnit u.det) (hpb : PowerBounded (cosq u)) :
    ∃ R : Mat, IsUnit R.det ∧ (R * u * Rᵀ) * (R * u * Rᵀ)ᵀ = 1 := by
  set J : Mat := !![0, -1; 1, 0] with hJ
  set H : Mat := (2 : ℝ)⁻¹ • (u + uᵀ) with hH
  set t : ℝ := (u 1 0 - u 0 1) / 2 with ht
  have hsym : Hᵀ = H := by
    rw [hH, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have hsplit : u = H + t • J := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hH, hJ, ht, Matrix.add_apply] <;> ring
  obtain ⟨T, d₀, d₁, hT, h0, h1, hdiag⟩ := sylvester2 H hsym
  set s : ℝ := t * T.det with hs
  have hTuT : T * u * Tᵀ = !![d₀, -s; s, d₁] := by
    rw [hsplit, Matrix.mul_add, Matrix.add_mul, hdiag, Matrix.mul_smul, Matrix.smul_mul,
      conj_J T, smul_smul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hs]
  have hdetv : IsUnit ((!![d₀, -s; s, d₁] : Mat)).det := by
    rw [← hTuT, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact (hT.mul hu).mul hT
  have hdet : d₀ * d₁ + s * s ≠ 0 := by
    have hne := isUnit_iff_ne_zero.1 hdetv
    rw [Matrix.det_fin_two_of] at hne
    intro h; apply hne; linarith
  have hpbv : PowerBounded (cosq (!![d₀, -s; s, d₁] : Mat)) := by
    rw [← hTuT, cosq_congr hT]
    exact hpb.conj hT
  obtain ⟨l, hl, hvv⟩ := normal_form_aux h0 h1 hdet hpbv
  exact good_case hT hTuT hl hvv

/-! ### From self-duality to an orthogonal self-duality -/

theorem cosq_mem_aut (hN : IsNorm N) {u : Mat} (hu : IsUnit u.det) (hSD : SelfDual N u) (x : V) :
    N (cosq u *ᵥ x) = N x := by
  have hfun : dualNorm N = fun z => N (u *ᵥ z) := funext hSD
  have h1 : dualNorm (dualNorm N) x = N x := dualNorm_dualNorm hN x
  rw [hfun] at h1
  rw [dualNorm_comp hu x] at h1
  rw [hSD ((u⁻¹)ᵀ *ᵥ x)] at h1
  rw [Matrix.mulVec_mulVec] at h1
  rw [cosq, ← Matrix.transpose_nonsing_inv]
  exact h1

theorem powerBounded_cosq (hN : IsNorm N) {u : Mat} (hu : IsUnit u.det) (hSD : SelfDual N u) :
    PowerBounded (cosq u) := by
  obtain ⟨c, hc, hlow⟩ := hN.exists_lower
  obtain ⟨C, hC, hup⟩ := hN.exists_upper
  have hinv : ∀ (n : ℕ) (x : V), N ((cosq u ^ n) *ᵥ x) = N x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ, ← Matrix.mulVec_mulVec, ih, cosq_mem_aut hN hu hSD]
  refine ⟨C / c, fun n x => ?_⟩
  have h1 : c * ‖(cosq u ^ n) *ᵥ x‖ ≤ N ((cosq u ^ n) *ᵥ x) := hlow _
  rw [hinv n x] at h1
  have h2 : N x ≤ C * ‖x‖ := hup x
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  nlinarith [norm_nonneg ((cosq u ^ n) *ᵥ x)]

/-- Corollary 5.2, at the level of norms. -/
theorem exists_orthogonal_selfdual (hN : IsNorm N) {u : Mat} (hu : IsUnit u.det)
    (hSD : SelfDual N u) :
    ∃ L Q : Mat, IsUnit L.det ∧ Q * Qᵀ = 1 ∧ SelfDual (fun x => N (L *ᵥ x)) Q := by
  obtain ⟨R, hR, hQ⟩ := normal_form hu (powerBounded_cosq hN hu hSD)
  have hR0 : R.det ≠ 0 := hR.ne_zero
  have hLdet : IsUnit (R⁻¹).det := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', isUnit_iff_ne_zero]
    exact inv_ne_zero hR0
  refine ⟨R⁻¹, R * u * Rᵀ, hLdet, hQ, fun x => ?_⟩
  have h1 : dualNorm (fun z => N (R⁻¹ *ᵥ z)) x = dualNorm N (((R⁻¹)⁻¹)ᵀ *ᵥ x) :=
    dualNorm_comp hLdet x
  rw [Matrix.nonsing_inv_nonsing_inv _ hR] at h1
  rw [h1, hSD (Rᵀ *ᵥ x)]
  show N (u *ᵥ (Rᵀ *ᵥ x)) = N (R⁻¹ *ᵥ ((R * u * Rᵀ) *ᵥ x))
  congr 1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hR, Matrix.one_mul]

/-! ### Classification of orthogonal self-dualities (§6) -/

theorem selfDual_sq (hN : IsNorm N) {Q : Mat} (hQ : Q * Qᵀ = 1) (hSD : SelfDual N Q) (x : V) :
    N ((Q * Q) *ᵥ x) = N x := by
  have hu : IsUnit Q.det := isUnit_det_of_orthogonal hQ
  have hcos : cosq Q = Q * Q := by
    rw [cosq, ← inv_of_orthogonal hQ, Matrix.nonsing_inv_nonsing_inv _ hu]
  rw [← hcos]
  exact cosq_mem_aut hN hu hSD x

theorem selfDual_conj {Q P : Mat} (hP : P * Pᵀ = 1) (hSD : SelfDual N Q) :
    SelfDual (fun x => N (P *ᵥ x)) (P⁻¹ * Q * P) := by
  have hPu : IsUnit P.det := isUnit_det_of_orthogonal hP
  intro x
  rw [dualNorm_comp hPu x]
  have hPT : ((P⁻¹)ᵀ : Mat) = P := by rw [inv_of_orthogonal hP, Matrix.transpose_transpose]
  rw [hPT, hSD (P *ᵥ x)]
  show N (Q *ᵥ (P *ᵥ x)) = N (P *ᵥ ((P⁻¹ * Q * P) *ᵥ x))
  congr 1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]

/-- The group of rotation angles preserving `N`. -/
def rotStab (N : V → ℝ) : AddSubgroup ℝ where
  carrier := {θ : ℝ | ∀ x, N (rot θ *ᵥ x) = N x}
  zero_mem' := by intro x; rw [rot_zero]; simp
  add_mem' := by
    intro a b ha hb x
    rw [← rot_mul, ← Matrix.mulVec_mulVec, ha, hb]
  neg_mem' := by
    intro a ha x
    have := ha (rot (-a) *ᵥ x)
    rw [Matrix.mulVec_mulVec, rot_mul, add_neg_cancel, rot_zero, Matrix.one_mulVec] at this
    exact this.symm

theorem isClosed_rotStab (hN : IsNorm N) : IsClosed (rotStab N : Set ℝ) := by
  have h : (rotStab N : Set ℝ) = ⋂ x : V, {θ : ℝ | N (rot θ *ᵥ x) = N x} := by
    ext θ
    simp [rotStab, Set.mem_iInter]
  rw [h]
  refine isClosed_iInter fun x => ?_
  have hcont : Continuous fun θ : ℝ => N (rot θ *ᵥ x) := by
    refine hN.continuous.comp ?_
    refine continuous_pi fun i => ?_
    fin_cases i <;>
      simp [rot, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> fun_prop
  exact isClosed_eq hcont continuous_const

theorem pi_mem_rotStab (hN : IsNorm N) : π ∈ rotStab N := by
  intro x
  rw [rot_pi]
  have h : (-1 : Mat) *ᵥ x = -x := by
    rw [Matrix.neg_mulVec, Matrix.one_mulVec]
  rw [h, hN.neg]

theorem classify_orthogonal (hN : IsNorm N) {Q : Mat} (hQ : Q * Qᵀ = 1) (hSD : SelfDual N Q) :
    ∃ P : Mat, IsUnit P.det ∧
      (SelfDual (fun x => N (P *ᵥ x)) refl2 ∨
        ∃ m : ℕ, 2 ≤ m ∧ Even m ∧ SelfDual (fun x => N (P *ᵥ x)) (rot (π / m))) := by
  rcases orthogonal_classify hQ with ⟨α, hα⟩ | ⟨β, hβ⟩
  · subst hα
    have hid : (fun x => N ((1 : Mat) *ᵥ x)) = N := by
      funext x; rw [Matrix.one_mulVec]
    have hone : IsUnit ((1 : Mat) : Mat).det := by simp
    have h2α : (α + α) ∈ rotStab N := by
      intro x
      have h := selfDual_sq hN hQ hSD x
      rwa [rot_mul] at h
    have hπ : π ∈ rotStab N := pi_mem_rotStab hN
    -- the Euclidean alternative, used twice
    have heuc : (∀ x, dualNorm N x = N x) → ∃ P : Mat, IsUnit P.det ∧
        (SelfDual (fun x => N (P *ᵥ x)) refl2 ∨
          ∃ m : ℕ, 2 ≤ m ∧ Even m ∧ SelfDual (fun x => N (P *ᵥ x)) (rot (π / m))) := by
      intro hself
      have hNe := eq_euc_of_selfdual hN hself
      refine ⟨1, hone, Or.inr ⟨2, le_refl 2, even_two, ?_⟩⟩
      rw [hid]
      intro x
      rw [hself x, hNe x, hNe (rot (π / ((2 : ℕ) : ℝ)) *ᵥ x), euc_rot]
    rcases (rotStab N).dense_or_cyclic with hdense | ⟨a, ha⟩
    · have huniv : ∀ θ : ℝ, θ ∈ rotStab N := by
        intro θ
        have hcl := (isClosed_rotStab hN).closure_eq
        have h2 : θ ∈ closure (rotStab N : Set ℝ) := by rw [hdense.closure_eq]; trivial
        rwa [hcl] at h2
      exact heuc fun x => by rw [hSD x, huniv α x]
    · have haG : a ∈ rotStab N := by rw [ha]; exact AddSubgroup.subset_closure rfl
      obtain ⟨k, hk⟩ := AddSubgroup.mem_closure_singleton.1 (by rw [← ha]; exact hπ)
      have hkr : (k : ℝ) * a = π := by rw [← hk]; simp [zsmul_eq_mul]
      have hane : a ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hkr
        exact Real.pi_ne_zero hkr.symm
      have hk0 : k ≠ 0 := by
        intro h0
        rw [h0] at hkr
        simp at hkr
        exact Real.pi_ne_zero hkr.symm
      set n : ℕ := k.natAbs with hn
      have hn1 : 1 ≤ n := Int.natAbs_pos.2 hk0
      set m : ℕ := 2 * n with hm
      have hnR : (n : ℝ) = |(k : ℝ)| := by
        rw [hn]
        push_cast [Nat.cast_natAbs]
        rfl
      have hmR : (m : ℝ) = 2 * (n : ℝ) := by rw [hm]; push_cast; ring
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        have : 0 < n := hn1
        exact_mod_cast this
      have habs : |a| = 2 * π / (m : ℝ) := by
        have h1 : |(k : ℝ)| * |a| = π := by
          rw [← abs_mul, hkr, abs_of_pos Real.pi_pos]
        rw [hmR, ← hnR] at *
        field_simp at h1 ⊢
        linarith [h1]
      set c : ℝ := 2 * π / (m : ℝ) with hc
      have hcG : c ∈ rotStab N := by
        rw [← habs]
        rcases abs_choice a with h | h
        · rw [h]; exact haG
        · rw [h]; exact AddSubgroup.neg_mem _ haG
      obtain ⟨j, hj⟩ := AddSubgroup.mem_closure_singleton.1 (by rw [← ha]; exact h2α)
      have hjr : (j : ℝ) * a = α + α := by rw [← hj]; simp [zsmul_eq_mul]
      -- a = ε * c with ε = 1 or -1
      obtain ⟨e, he, hae⟩ : ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ a = (e : ℝ) * c := by
        rcases abs_choice a with h | h
        · exact ⟨1, Or.inl rfl, by rw [← habs, h]; ring⟩
        · refine ⟨-1, Or.inr rfl, ?_⟩
          rw [← habs, h]
          push_cast
          ring
      have hje : ((j * e : ℤ) : ℝ) * c = α + α := by
        rw [← hjr, hae]
        push_cast
        ring
      have hcpos : 0 < c := by
        rw [hc]
        have : (0:ℝ) < (m : ℝ) := by rw [hmR]; linarith
        positivity
      have hchalf : c / 2 = π / (m : ℝ) := by
        rw [hc]; ring
      rcases Int.even_or_odd (j * e) with ⟨i, hi⟩ | ⟨i, hi⟩
      · -- α is in the stabiliser
        have hαc : α = (i : ℝ) * c := by
          rw [hi] at hje
          push_cast at hje
          linarith
        have hαG : α ∈ rotStab N := by
          rw [hαc]
          have := AddSubgroup.zsmul_mem (rotStab N) hcG i
          rwa [zsmul_eq_mul] at this
        exact heuc fun x => by rw [hSD x, hαG x]
      · refine ⟨1, hone, Or.inr ⟨m, ?_, ⟨n, by rw [hm]; ring⟩, ?_⟩⟩
        · rw [hm]; omega
        · rw [hid]
          have hαsplit : α = (i : ℝ) * c + π / (m : ℝ) := by
            rw [hi] at hje
            push_cast at hje
            rw [← hchalf]
            linarith
          have hiG : ((i : ℝ) * c) ∈ rotStab N := by
            have := AddSubgroup.zsmul_mem (rotStab N) hcG i
            rwa [zsmul_eq_mul] at this
          intro x
          rw [hSD x, hαsplit, ← rot_mul, ← Matrix.mulVec_mulVec, hiG]
  · refine ⟨rot (β / 2), by rw [rot_det]; exact isUnit_one, Or.inl ?_⟩
    have hP : rot (β / 2) * (rot (β / 2))ᵀ = 1 := rot_transpose _
    have hinv : (rot (β / 2))⁻¹ = rot (-(β / 2)) := by
      refine Matrix.inv_eq_right_inv ?_
      rw [rot_mul, add_neg_cancel, rot_zero]
    have hkey : (rot (β / 2))⁻¹ * Q * rot (β / 2) = refl2 := by
      rw [hinv, hβ]
      have e1 : rot (-(β / 2)) * (rot β * refl2) * rot (β / 2)
          = (rot (-(β / 2)) * rot β) * (refl2 * rot (β / 2)) := by
        simp [Matrix.mul_assoc]
      rw [e1, rot_mul, refl2_mul_rot, ← Matrix.mul_assoc, rot_mul]
      have e2 : -(β / 2) + β + -(β / 2) = 0 := by ring
      rw [e2, rot_zero, Matrix.one_mul]
    have h := selfDual_conj hP hSD
    rwa [hkey] at h

/-- Transport of self-duality along a linear change of coordinates. -/
theorem selfDual_of_comp {L Q : Mat} (hN : IsNorm N) (hL : IsUnit L.det)
    (h : SelfDual (fun x => N (L *ᵥ x)) Q) : SelfDual N (L * Q * Lᵀ) := by
  have h0 : L.det ≠ 0 := hL.ne_zero
  have hLinv : IsUnit (L⁻¹).det := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', isUnit_iff_ne_zero]
    exact inv_ne_zero h0
  have hfun : N = fun z => (fun x => N (L *ᵥ x)) (L⁻¹ *ᵥ z) := by
    funext z
    show N z = N (L *ᵥ (L⁻¹ *ᵥ z))
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hL, Matrix.one_mulVec]
  intro x
  have hM : IsNorm (fun x => N (L *ᵥ x)) := hN.comp hL
  calc dualNorm N x = dualNorm (fun z => (fun x => N (L *ᵥ x)) (L⁻¹ *ᵥ z)) x := by rw [← hfun]
    _ = dualNorm (fun x => N (L *ᵥ x)) (((L⁻¹)⁻¹)ᵀ *ᵥ x) :=
        dualNorm_comp (N := fun x => N (L *ᵥ x)) hLinv x
    _ = dualNorm (fun x => N (L *ᵥ x)) (Lᵀ *ᵥ x) := by
        rw [Matrix.nonsing_inv_nonsing_inv _ hL]
    _ = N (L *ᵥ (Q *ᵥ (Lᵀ *ᵥ x))) := h _
    _ = N ((L * Q * Lᵀ) *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-! ### The main theorem -/

/-- **Q805.**  A norm `N` on the Euclidean plane satisfies `N* = N ∘ u` for some invertible
linear map `u` if and only if, after a linear change of coordinates `L`, the norm `M = N ∘ L`
satisfies either `M* = M ∘ F` (reflection type) or `M* = M ∘ R_{π/m}` for some even `m ≥ 2`
(rotational type). -/
theorem Q805_classification (N : V → ℝ) (hN : IsNorm N) :
    (∃ u : Mat, IsUnit u.det ∧ SelfDual N u) ↔
      ∃ L : Mat, IsUnit L.det ∧
        (SelfDual (fun x => N (L *ᵥ x)) refl2 ∨
          ∃ m : ℕ, 2 ≤ m ∧ Even m ∧ SelfDual (fun x => N (L *ᵥ x)) (rot (π / m))) := by
  constructor
  · rintro ⟨u, hu, hSD⟩
    obtain ⟨L, Q, hL, hQ, hSD'⟩ := exists_orthogonal_selfdual hN hu hSD
    obtain ⟨P, hP, hcase⟩ := classify_orthogonal (hN.comp hL) hQ hSD'
    have hfun : (fun x => (fun y => N (L *ᵥ y)) (P *ᵥ x)) = fun x => N ((L * P) *ᵥ x) := by
      funext x
      show N (L *ᵥ (P *ᵥ x)) = N ((L * P) *ᵥ x)
      rw [Matrix.mulVec_mulVec]
    refine ⟨L * P, ?_, ?_⟩
    · rw [Matrix.det_mul]; exact hL.mul hP
    · rw [hfun] at hcase; exact hcase
  · rintro ⟨L, hL, hcase⟩
    rcases hcase with h | ⟨m, hm2, hmeven, h⟩
    · refine ⟨L * refl2 * Lᵀ, ?_, selfDual_of_comp hN hL h⟩
      have hr : IsUnit (refl2).det := by
        rw [show refl2 = !![1, 0; 0, -1] from rfl, Matrix.det_fin_two_of]
        norm_num
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      exact (hL.mul hr).mul hL
    · refine ⟨L * rot (π / m) * Lᵀ, ?_, selfDual_of_comp hN hL h⟩
      have hr : IsUnit ((rot (π / m)).det) := by rw [rot_det]; exact isUnit_one
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      exact (hL.mul hr).mul hL

/-- In the rotational case the unit ball automatically has `m`-fold rotational symmetry. -/
theorem Q805_rotational_symmetry (M : V → ℝ) (hM : IsNorm M) {m : ℕ}
    (h : SelfDual M (rot (π / m))) (x : V) : M (rot (2 * π / m) *ᵥ x) = M x := by
  have hsq := selfDual_sq hM (rot_transpose (π / m)) h x
  rwa [rot_mul, show π / (m : ℝ) + π / m = 2 * π / m by ring] at hsq

end Q805
