/-
# Q788 — the endpoint `Dₙ = 2ⁿ`

The deterministic characterization of the extremal configurations,
`chordMax θ = 2ⁿ ↔ all the points e^{iθ_j} coincide` (for `n ≥ 1`), and the resulting
`ℙ(Dₙ = 2ⁿ) = 0` for every `n ≥ 2`.
-/
import RMS.Q788Probability

open Real Complex MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Q788

/-! ## A product of factors bounded by `2` equals `2ⁿ` only in the extreme case -/

theorem prod_eq_two_pow_iff {n : ℕ} (f : Fin n → ℝ) (h0 : ∀ i, 0 ≤ f i) (h2 : ∀ i, f i ≤ 2) :
    (∏ i, f i = 2 ^ n) ↔ ∀ i, f i = 2 := by
  constructor
  · intro heq j
    by_contra hne
    have hlt : f j < 2 := lt_of_le_of_ne (h2 j) hne
    have hsplit : ∏ i, f i = f j * ∏ i ∈ Finset.univ.erase j, f i :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
    have hb : ∏ i ∈ Finset.univ.erase j, f i ≤ 2 ^ (n - 1) := by
      calc ∏ i ∈ Finset.univ.erase j, f i ≤ ∏ _i ∈ Finset.univ.erase j, (2 : ℝ) :=
            Finset.prod_le_prod (fun i _ => h0 i) (fun i _ => h2 i)
        _ = 2 ^ (n - 1) := by rw [Finset.prod_const]; simp
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact absurd j.2 (by simp))
    have hp : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    have hpos : (0 : ℝ) < 2 ^ (n - 1) := by positivity
    have h1 : f j * ∏ i ∈ Finset.univ.erase j, f i ≤ f j * 2 ^ (n - 1) :=
      mul_le_mul_of_nonneg_left hb (h0 j)
    have h3 : f j * 2 ^ (n - 1) < 2 * 2 ^ (n - 1) := by nlinarith
    rw [hsplit] at heq
    linarith
  · intro h; simp [h]

/-! ## Antipodal characterization of the maximal chord -/

theorem cexp_eq_neg_one_iff (u : ℝ) :
    Complex.exp ((u : ℂ) * Complex.I) = -1 ↔ Real.cos u = -1 ∧ Real.sin u = 0 := by
  rw [Complex.exp_mul_I,
    show ((Complex.cos u) + Complex.sin u * Complex.I)
      = Complex.ofReal (Real.cos u) + Complex.ofReal (Real.sin u) * Complex.I by
      push_cast [← Complex.ofReal_cos, ← Complex.ofReal_sin]; ring]
  constructor
  · intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]; push_cast; ring

/-- Two points of the unit circle are at distance `2` exactly when they are antipodal. -/
theorem abs_sin_half_eq_one_iff (a b : ℝ) :
    |Real.sin ((a - b) / 2)| = 1 ↔
      Complex.exp ((a : ℂ) * Complex.I) = -Complex.exp ((b : ℂ) * Complex.I) := by
  set x := (a - b) / 2 with hx
  have h2x : 2 * x = a - b := by rw [hx]; ring
  have hcos2 : Real.cos (a - b) = 1 - 2 * Real.sin x ^ 2 := by
    have h := Real.cos_two_mul x
    rw [h2x] at h
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hsin2 : Real.sin (a - b) = 2 * Real.sin x * Real.cos x := by
    have h := Real.sin_two_mul x
    rw [h2x] at h
    linarith
  have hkey : Complex.exp ((a : ℂ) * Complex.I) = -Complex.exp ((b : ℂ) * Complex.I) ↔
      Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) = -1 := by
    constructor
    · intro h
      have hdiv : Complex.exp (((a - b : ℝ) : ℂ) * Complex.I)
          = Complex.exp ((a : ℂ) * Complex.I) / Complex.exp ((b : ℂ) * Complex.I) := by
        rw [← Complex.exp_sub]; push_cast; ring_nf
      rw [hdiv, h]
      field_simp
    · intro h
      have hb : Complex.exp ((a : ℂ) * Complex.I)
          = Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) * Complex.exp ((b : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]; push_cast; ring_nf
      rw [hb, h]; ring
  rw [hkey, cexp_eq_neg_one_iff]
  constructor
  · intro h
    have hs : Real.sin x ^ 2 = 1 := by
      have := sq_abs (Real.sin x); rw [h] at this; linarith [this]
    have hc : Real.cos x = 0 := by nlinarith [Real.sin_sq_add_cos_sq x]
    exact ⟨by rw [hcos2, hs]; ring, by rw [hsin2, hc]; ring⟩
  · rintro ⟨h1, -⟩
    rw [hcos2] at h1
    have hs : Real.sin x ^ 2 = 1 := by linarith
    have := sq_abs (Real.sin x)
    have habs : |Real.sin x| ^ 2 = 1 := by rw [this, hs]
    nlinarith [abs_nonneg (Real.sin x)]

/-- The chord product attains the value `2ⁿ` at `t` exactly when all the configuration points
are antipodal to `e^{it}`. -/
theorem chordProd_eq_two_pow_iff {n : ℕ} (θ : Fin n → ℝ) (t : ℝ) :
    chordProd θ t = 2 ^ n ↔
      ∀ j, Complex.exp ((θ j : ℂ) * Complex.I) = -Complex.exp ((t : ℂ) * Complex.I) := by
  have hfac : ∀ j, ‖Complex.exp ((t : ℂ) * Complex.I) - Complex.exp ((θ j : ℂ) * Complex.I)‖
      = 2 * |Real.sin ((t - θ j) / 2)| := fun j => norm_exp_sub_exp _ _
  rw [chordProd,
    prod_eq_two_pow_iff _ (fun j => norm_nonneg _)
      (fun j => by
        rw [hfac j]
        have := abs_sin_le_one ((t - θ j) / 2)
        linarith)]
  constructor
  · intro h j
    have hj := h j
    rw [hfac j] at hj
    have : |Real.sin ((t - θ j) / 2)| = 1 := by linarith
    have := (abs_sin_half_eq_one_iff t (θ j)).1 this
    -- `exp (i t) = - exp (i θ_j)` gives `exp (i θ_j) = - exp (i t)`
    rw [this]; ring
  · intro h j
    have hj : Complex.exp ((t : ℂ) * Complex.I) = -Complex.exp ((θ j : ℂ) * Complex.I) := by
      rw [h j]; ring
    have : |Real.sin ((t - θ j) / 2)| = 1 := (abs_sin_half_eq_one_iff t (θ j)).2 hj
    rw [hfac j, this]; ring

/-- **The endpoint characterization**: `Dₙ = 2ⁿ` exactly when all the `n` points of the
configuration coincide on the circle. -/
theorem chordMax_eq_two_pow_iff {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) :
    chordMax θ = 2 ^ n ↔
      ∀ j k, Complex.exp ((θ j : ℂ) * Complex.I) = Complex.exp ((θ k : ℂ) * Complex.I) := by
  constructor
  · intro h j k
    obtain ⟨t, ht⟩ := exists_chordProd_eq_chordMax θ
    rw [h] at ht
    have := (chordProd_eq_two_pow_iff θ t).1 ht
    rw [this j, this k]
  · intro h
    set j0 : Fin n := ⟨0, hn⟩
    have hge : (2 : ℝ) ^ n ≤ chordMax θ := by
      have := chordProd_le_chordMax θ (θ j0 + π)
      rwa [(chordProd_eq_two_pow_iff θ (θ j0 + π)).2 ?_] at this
      intro j
      have hpi : Complex.exp (((θ j0 + π : ℝ) : ℂ) * Complex.I)
          = -Complex.exp ((θ j0 : ℂ) * Complex.I) := by
        push_cast
        rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
        ring
      rw [hpi, h j j0]; ring
    exact le_antisymm (chordMax_le_two_pow θ) hge

/-! ## The endpoint is almost surely not attained -/

/-- A hyperplane `{θ | θ i - θ j = c}` (with `i ≠ j`) is Lebesgue-null. -/
theorem volume_diff_hyperplane_null {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : ℝ) :
    (volume : Measure (Fin n → ℝ)) {θ : Fin n → ℝ | θ i - θ j = c} = 0 := by
  classical
  set L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) - (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ) with hL
  have hLapp : ∀ θ, L θ = θ i - θ j := fun θ => rfl
  set p : Fin n → ℝ := fun k => if k = i then c else 0 with hp
  have hLp : L p = c := by rw [hLapp]; simp [hp, hij.symm]
  have hset : {θ : Fin n → ℝ | θ i - θ j = c}
      = (fun y => p + y) '' (LinearMap.ker L : Set (Fin n → ℝ)) := by
    ext θ
    constructor
    · intro hθ
      refine ⟨θ - p, ?_, by ring⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hLp]
      rw [hLapp θ]
      simp only [Set.mem_setOf_eq] at hθ
      rw [hθ]; ring
    · rintro ⟨y, hy, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker] at hy
      have h2 : L (p + y) = c := by rw [map_add, hy, hLp, add_zero]
      rw [hLapp] at h2
      exact h2
  have hne : LinearMap.ker L ≠ ⊤ := by
    intro h
    have hmem : (Pi.single i (1 : ℝ)) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    simp only [LinearMap.mem_ker] at hmem
    rw [hLapp] at hmem
    simp [hij.symm] at hmem
  rw [hset, Set.image_add_left, measure_preimage_add]
  exact Measure.addHaar_submodule volume _ hne

theorem cexp_eq_cexp_iff (a b : ℝ) :
    Complex.exp ((a : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I) ↔
      ∃ k : ℤ, a - b = 2 * π * k := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hI : (Complex.I) ≠ 0 := Complex.I_ne_zero
    have : ((a : ℂ) - (b : ℂ)) * Complex.I = ((2 * π * k : ℝ) : ℂ) * Complex.I := by
      push_cast
      linear_combination hk
    have h2 := mul_right_cancel₀ hI this
    exact_mod_cast h2
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have : (a : ℂ) = (b : ℂ) + ((2 * π * k : ℝ) : ℂ) := by
      have : ((a - b : ℝ) : ℂ) = ((2 * π * k : ℝ) : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) hk
      push_cast at this ⊢
      linear_combination this
    rw [this]
    push_cast
    ring

/-- Two coordinates almost surely give distinct points of the circle. -/
theorem angleLawN_coincidence_null {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    angleLawN n {θ : Fin n → ℝ |
      Complex.exp ((θ i : ℂ) * Complex.I) = Complex.exp ((θ j : ℂ) * Complex.I)} = 0 := by
  refine angleLawN_absolutelyContinuous n ?_
  have hsub : {θ : Fin n → ℝ |
      Complex.exp ((θ i : ℂ) * Complex.I) = Complex.exp ((θ j : ℂ) * Complex.I)}
      ⊆ ⋃ k : ℤ, {θ : Fin n → ℝ | θ i - θ j = 2 * π * k} := by
    intro θ hθ
    obtain ⟨k, hk⟩ := (cexp_eq_cexp_iff (θ i) (θ j)).1 hθ
    exact Set.mem_iUnion.2 ⟨k, hk⟩
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null fun k => ?_
  exact volume_diff_hyperplane_null i j hij _

/-- **`ℙ(Dₙ = 2ⁿ) = 0`** for every `n ≥ 2`. -/
theorem angleLawN_chordMax_eq_two_pow {n : ℕ} (hn : 2 ≤ n) :
    angleLawN n {θ : Fin n → ℝ | chordMax θ = 2 ^ n} = 0 := by
  have h0 : (0 : ℕ) < n := by omega
  have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    simp [Fin.ext_iff]
  refine measure_mono_null ?_ (angleLawN_coincidence_null (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ hij)
  intro θ hθ
  exact (chordMax_eq_two_pow_iff h0 θ).1 hθ _ _

/-- The real-valued form: the endpoint carries no mass, so `ℙ(Dₙ ≥ 2ⁿ) = 0`. -/
theorem probGE_two_pow {n : ℕ} (hn : 2 ≤ n) : probGE n (2 ^ n) = 0 := by
  have hsub : {θ : Fin n → ℝ | (2 : ℝ) ^ n ≤ chordMax θ} ⊆ {θ : Fin n → ℝ | chordMax θ = 2 ^ n} :=
    fun θ hθ => le_antisymm (chordMax_le_two_pow θ) hθ
  rw [probGE, measure_mono_null hsub (angleLawN_chordMax_eq_two_pow hn), ENNReal.toReal_zero]

end Q788
