import Mathlib

/-!
# Q885

Let `A n = [n, n + n⁻³)` for `n ≥ 1`, and let `f : ℝ → ℝ≥0∞` be the step function equal to `n`
on `A n` and `0` elsewhere.  For `a > 0` put

  `I a = ∫⁻ t, f t * f (t / a)`,   `J a = ∫⁻ t, t * f t * f (t / a)`.

We prove:

* `Q885.I_eq_top_of_rat` : `I a = ∞` for every positive rational `a`;
* `Q885.J_eq_top_of_rat` : hence `J a = ∞` for every positive rational `a`;
* `Q885.irrational_sqrt_two'` and `Q885.J_sqrt_two_ne_top` : `√2` is irrational and `J √2 < ∞`;
* `Q885.irrational_L`, `Q885.L_pos` and `Q885.J_L_eq_top` : the Liouville-type number
  `L = ∑' j, 10 ^ (-(j+1)!)` is a positive irrational number with `J L = ∞`.

All integrals are extended nonnegative Lebesgue integrals (`ℝ≥0∞`-valued), so that they are
defined unconditionally and can take the value `∞`.  `Q885.measurable_f` records that `f` is
measurable.

## Relation to the printed statement

* The printed problem defines `f` on `ℝ₊`; here `f` is defined on all of `ℝ` and vanishes
  outside `⋃ n ≥ 1, A n ⊆ [1, ∞)`, so `∫₀^∞` and `∫_ℝ` agree.  For `n = 0` the formula
  `A 0 = [0, 0 + 0⁻³)` degenerates to `∅` (in Lean `(0 : ℝ)⁻¹ = 0`), which is exactly the
  intended convention that only `n ≥ 1` contributes.
* `J a = ∫⁻ t, t * f t * f (t / a)` is written as
  `∫⁻ t, ENNReal.ofReal t * (f t * f (t / a))`; since the integrand vanishes for `t < 1`,
  this is the printed weight `t`.
* Finiteness of `J √2` is stated as `J (Real.sqrt 2) ≠ ⊤`, i.e. `J √2 < ∞`.
* Only the mandatory parts are formalized: divergence at every positive rational, the single
  explicit finite irrational example `√2`, and the explicit divergent irrational example `L`.
  The optional contextual averaged-integrability claim and the full family of quadratic surds
  are not formalized.

## Versions

Lean 4 toolchain `leanprover/lean4:v4.28.0`, mathlib revision `v4.28.0`
(commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`).
-/

open MeasureTheory Set
open scoped ENNReal Nat

namespace Q885

noncomputable section

/-! ## The sets `A n`, the step function `f`, and the integrals `I` and `J` -/

/-- `A n = [n, n + n⁻³)`.  For `n = 0` this is the empty set, so that only `n ≥ 1` matters. -/
def A (n : ℕ) : Set ℝ := Set.Ico (n : ℝ) ((n : ℝ) + ((n : ℝ) ^ 3)⁻¹)

/-- The step function of Q885 : `f t = n` for `t ∈ A n` (`n ≥ 1`) and `f t = 0` otherwise. -/
def f (t : ℝ) : ℝ≥0∞ := ∑' n : ℕ, (A n).indicator (fun _ => (n : ℝ≥0∞)) t

/-- The unweighted integral `I a = ∫₀^∞ f t * f (t / a) dt`. -/
def I (a : ℝ) : ℝ≥0∞ := ∫⁻ t, f t * f (t / a)

/-- The weighted integral `J a = ∫₀^∞ t * f t * f (t / a) dt`. -/
def J (a : ℝ) : ℝ≥0∞ := ∫⁻ t, ENNReal.ofReal t * (f t * f (t / a))

/-! ## Basic properties -/

lemma A_zero : A 0 = ∅ := by simp [A]

lemma A_subset (n : ℕ) : A n ⊆ Set.Ico (n : ℝ) ((n : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [A_zero]
  · apply Set.Ico_subset_Ico le_rfl
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : ((n : ℝ) ^ 3)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]; right; exact one_le_pow₀ h1
    linarith

lemma A_disjoint {m n : ℕ} (h : m ≠ n) : Disjoint (A m) (A n) := by
  wlog hlt : m < n generalizing m n
  · exact (this h.symm (by omega)).symm
  rw [Set.disjoint_left]
  intro t htm htn
  have h1 := A_subset m htm
  have h2 := htn.1
  have h3 : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlt
  simp only [Set.mem_Ico] at h1
  linarith [h1.2]

lemma f_eq_of_mem {t : ℝ} {n : ℕ} (h : t ∈ A n) : f t = (n : ℝ≥0∞) := by
  rw [f, tsum_eq_single n]
  · rw [Set.indicator_of_mem h]
  · intro j hj
    rw [Set.indicator_of_notMem]
    intro hjm
    exact (A_disjoint hj).le_bot ⟨hjm, h⟩

lemma f_of_notMem {t : ℝ} (h : ∀ n, t ∉ A n) : f t = 0 := by
  rw [f]; simp [Set.indicator_of_notMem (h _)]

lemma exists_of_f_ne_zero {t : ℝ} (h : f t ≠ 0) : ∃ n : ℕ, 0 < n ∧ t ∈ A n := by
  by_contra hc
  push_neg at hc
  refine h (f_of_notMem fun n hn => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [A_zero] at hn; exact hn
  · exact absurd hn (hc n hpos)

lemma one_le_of_f_ne_zero {t : ℝ} (h : f t ≠ 0) : 1 ≤ t := by
  obtain ⟨n, hn, ht⟩ := exists_of_f_ne_zero h
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact le_trans h1 ht.1

lemma f_le_ofReal (t : ℝ) : f t ≤ ENNReal.ofReal t := by
  by_cases h : f t = 0
  · simp [h]
  obtain ⟨n, hn, ht⟩ := exists_of_f_ne_zero h
  rw [f_eq_of_mem ht, show ((n : ℝ≥0∞)) = ENNReal.ofReal (n : ℝ) by simp]
  exact ENNReal.ofReal_le_ofReal ht.1

/-- `f` is measurable. -/
lemma measurable_f : Measurable f := by
  apply Measurable.ennreal_tsum
  intro n
  exact measurable_const.indicator measurableSet_Ico

/-- The unweighted integral is dominated by the weighted one, since `f` is supported in `[1, ∞)`. -/
lemma I_le_J (a : ℝ) : I a ≤ J a := by
  refine lintegral_mono fun t => ?_
  by_cases h : f t = 0
  · simp [h]
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal t := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (one_le_of_f_ne_zero h)
  exact le_mul_of_one_le_left' h1

/-! ## A general divergence criterion -/

/-- If there are infinitely many pairwise different indices `m k` and intervals
`[c k, d k) ⊆ A (m k)` on which `G` is at least `u k`, and if `∑ u k * (d k - c k) = ∞`,
then `∫⁻ G = ∞`. -/
theorem lintegral_eq_top_of_family (G : ℝ → ℝ≥0∞) (m : ℕ → ℕ) (c d : ℕ → ℝ) (u : ℕ → ℝ≥0∞)
    (hm : Function.Injective m) (hsub : ∀ k, Set.Ico (c k) (d k) ⊆ A (m k))
    (hG : ∀ k, ∀ t ∈ Set.Ico (c k) (d k), u k ≤ G t)
    (hdiv : ∑' k, u k * ENNReal.ofReal (d k - c k) = ⊤) :
    ∫⁻ t, G t = ⊤ := by
  set E : ℕ → Set ℝ := fun k => Set.Ico (c k) (d k) with hE
  have hmeas : ∀ k, MeasurableSet (E k) := fun _ => measurableSet_Ico
  have hdisj : Pairwise (Function.onFun Disjoint E) :=
    fun i j hij => (A_disjoint fun h => hij (hm h)).mono (hsub i) (hsub j)
  rw [← top_le_iff, ← hdiv]
  calc ∑' k, u k * ENNReal.ofReal (d k - c k)
      = ∑' k, ∫⁻ _t in E k, u k := by
        simp only [setLIntegral_const, hE, Real.volume_Ico]
    _ ≤ ∑' k, ∫⁻ t in E k, G t := by
        refine ENNReal.tsum_le_tsum fun k => lintegral_mono_ae ?_
        rw [ae_restrict_iff' (hmeas k)]
        exact Filter.Eventually.of_forall (hG k)
    _ = ∫⁻ t in ⋃ k, E k, G t := (lintegral_iUnion hmeas hdisj G).symm
    _ ≤ ∫⁻ t, G t := setLIntegral_le_lintegral _ _

/-- Divergence of the harmonic series, in `ℝ≥0∞` form. -/
lemma tsum_ofReal_harmonic_eq_top {C : ℝ} (hC : 0 < C) :
    ∑' k : ℕ, ENNReal.ofReal (C / (k + 1)) = ⊤ := by
  by_contra h
  have h2 : Summable fun k : ℕ => (ENNReal.ofReal (C / (k + 1))).toReal := ENNReal.summable_toReal h
  have h3 : Summable fun k : ℕ => C / ((k : ℝ) + 1) := by
    refine h2.congr fun k => ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
  have h4 : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) := by
    refine (h3.mul_left C⁻¹).congr fun k => ?_
    field_simp
  exact Real.not_summable_one_div_natCast
    (by exact_mod_cast (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).1 (by simpa using h4))

/-! ## Part (a) : positive rationals -/

/-- For every positive rational `p / q`, the unweighted integral diverges: the diagonal pairs
`(m, n) = (p k, q k)` contribute a positive multiple of the harmonic series. -/
theorem I_eq_top_of_ratio (p q : ℕ) (hp : 0 < p) (hq : 0 < q) : I ((p : ℝ) / q) = ⊤ := by
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  set a : ℝ := (p:ℝ)/q with ha_def
  have ha : 0 < a := div_pos hpR hqR
  have haq : a * q = p := by rw [ha_def]; field_simp
  set δ : ℝ := min (((p:ℝ)^3)⁻¹) (a * ((q:ℝ)^3)⁻¹) with hδdef
  have hδ1 : δ ≤ ((p:ℝ)^3)⁻¹ := min_le_left _ _
  have hδ2 : δ ≤ a * ((q:ℝ)^3)⁻¹ := min_le_right _ _
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hsub : ∀ k : ℕ, Set.Ico ((p:ℝ)*((k:ℝ)+1)) ((p:ℝ)*((k:ℝ)+1) + δ/((k:ℝ)+1)^3)
      ⊆ A (p*(k+1)) := by
    intro k
    have hk : (0:ℝ) < (k:ℝ)+1 := by positivity
    have hcast : ((p*(k+1) : ℕ) : ℝ) = (p:ℝ)*((k:ℝ)+1) := by push_cast; ring
    rw [A, hcast]
    refine Set.Ico_subset_Ico le_rfl ?_
    have key : δ / ((k:ℝ)+1)^3 ≤ (((p:ℝ)*((k:ℝ)+1))^3)⁻¹ := by
      calc δ / ((k:ℝ)+1)^3 ≤ ((p:ℝ)^3)⁻¹/((k:ℝ)+1)^3 := by gcongr
        _ = (((p:ℝ)*((k:ℝ)+1))^3)⁻¹ := by field_simp
    linarith
  have hsub2 : ∀ (k : ℕ), ∀ t ∈ Set.Ico ((p:ℝ)*((k:ℝ)+1)) ((p:ℝ)*((k:ℝ)+1) + δ/((k:ℝ)+1)^3),
      t / a ∈ A (q*(k+1)) := by
    intro k t ht
    have hk : (0:ℝ) < (k:ℝ)+1 := by positivity
    have hcast : ((q*(k+1) : ℕ) : ℝ) = (q:ℝ)*((k:ℝ)+1) := by push_cast; ring
    rw [A, hcast]
    obtain ⟨h1, h2⟩ := ht
    constructor
    · rw [le_div_iff₀ ha]
      calc (q:ℝ)*((k:ℝ)+1) * a = (p:ℝ)*((k:ℝ)+1) := by rw [← haq]; ring
        _ ≤ t := h1
    · rw [div_lt_iff₀ ha]
      have key : δ/((k:ℝ)+1)^3 ≤ a * (((q:ℝ)*((k:ℝ)+1))^3)⁻¹ := by
        calc δ/((k:ℝ)+1)^3 ≤ (a * ((q:ℝ)^3)⁻¹)/((k:ℝ)+1)^3 := by gcongr
          _ = a * (((q:ℝ)*((k:ℝ)+1))^3)⁻¹ := by field_simp
      have h3 : ((q:ℝ)*((k:ℝ)+1) + (((q:ℝ)*((k:ℝ)+1))^3)⁻¹) * a
          = (p:ℝ)*((k:ℝ)+1) + a * (((q:ℝ)*((k:ℝ)+1))^3)⁻¹ := by rw [← haq]; ring
      rw [h3]
      linarith
  rw [I]
  refine lintegral_eq_top_of_family _ (fun k => p*(k+1)) (fun k => (p:ℝ)*((k:ℝ)+1))
      (fun k => (p:ℝ)*((k:ℝ)+1) + δ/((k:ℝ)+1)^3)
      (fun k => ((p*(k+1) : ℕ) : ℝ≥0∞) * ((q*(k+1) : ℕ) : ℝ≥0∞)) ?_ hsub ?_ ?_
  · intro k1 k2 h
    simp only at h
    have := Nat.eq_of_mul_eq_mul_left hp h
    omega
  · intro k t ht
    rw [f_eq_of_mem (hsub k ht), f_eq_of_mem (hsub2 k t ht)]
  · have hterm : ∀ k : ℕ, ((p*(k+1) : ℕ) : ℝ≥0∞) * ((q*(k+1) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (((p:ℝ)*((k:ℝ)+1) + δ/((k:ℝ)+1)^3) - (p:ℝ)*((k:ℝ)+1))
        = ENNReal.ofReal (((p:ℝ)*(q:ℝ)*δ)/((k:ℝ)+1)) := by
      intro k
      have hk : (0:ℝ) < (k:ℝ)+1 := by positivity
      rw [← ENNReal.ofReal_natCast (p*(k+1)), ← ENNReal.ofReal_natCast (q*(k+1)),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      field_simp
      ring
    simp only [hterm]
    exact tsum_ofReal_harmonic_eq_top (by positivity)

/-- **Part (a)**: for every positive rational `a`, `∫ f(t) f(t/a) dt = ∞`. -/
theorem I_eq_top_of_rat (a : ℚ) (ha : 0 < a) : I (a : ℝ) = ⊤ := by
  have hnum : 0 < a.num := Rat.num_pos.mpr ha
  have h1 : (a : ℝ) = ((a.num.toNat : ℕ) : ℝ) / ((a.den : ℕ) : ℝ) := by
    rw [Rat.cast_def]
    congr 1
    rw [show ((a.num.toNat : ℕ) : ℝ) = ((a.num.toNat : ℤ) : ℝ) by norm_cast,
      Int.toNat_of_nonneg hnum.le]
  rw [h1]
  exact I_eq_top_of_ratio _ _ (by omega) a.pos

/-- **Part (a)**, weighted form: for every positive rational `a`, `J a = ∞`. -/
theorem J_eq_top_of_rat (a : ℚ) (ha : 0 < a) : J (a : ℝ) = ⊤ :=
  top_le_iff.1 (le_trans (le_of_eq (I_eq_top_of_rat a ha).symm) (I_le_J _))

/-! ## Part (b) : `J (√2) < ∞` -/

/-- `√2` is irrational. -/
theorem irrational_sqrt_two' : Irrational (Real.sqrt 2) := irrational_sqrt_two

lemma sqrt_two_sq' : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

lemma sqrt_two_lo : 1.414 < Real.sqrt 2 := by nlinarith [sqrt_two_sq', Real.sqrt_nonneg 2]

lemma sqrt_two_hi : Real.sqrt 2 < 1.415 := by nlinarith [sqrt_two_sq', Real.sqrt_nonneg 2]

lemma sq_ne_two_mul_sq (m n : ℕ) (hn : 0 < n) : (m:ℝ)^2 ≠ 2*(n:ℝ)^2 := by
  intro h
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have h2 : Real.sqrt 2 = (m:ℝ)/n := by
    rw [show (2:ℝ) = ((m:ℝ)/n)^2 by field_simp; linarith]
    exact Real.sqrt_sq (by positivity)
  exact irrational_sqrt_two ⟨((m : ℚ)/(n : ℚ)), by rw [h2]; push_cast; ring⟩

/-- The quadratic Diophantine separation: `m² - 2n²` is a nonzero integer. -/
lemma int_sep (m n : ℕ) (hn : 0 < n) :
    1 ≤ (m:ℝ)^2 - 2*(n:ℝ)^2 ∨ (m:ℝ)^2 - 2*(n:ℝ)^2 ≤ -1 := by
  have hz : ((m:ℤ)^2 - 2*(n:ℤ)^2) ≠ 0 := by
    intro h
    refine sq_ne_two_mul_sq m n hn ?_
    have h' : ((m:ℤ)^2 : ℝ) - 2*((n:ℤ)^2 : ℝ) = 0 := by
      exact_mod_cast congrArg (fun z : ℤ => (z:ℝ)) h
    push_cast at h'
    linarith
  have hcast : (m:ℝ)^2 - 2*(n:ℝ)^2 = (((m:ℤ)^2 - 2*(n:ℤ)^2 : ℤ) : ℝ) := by push_cast; ring
  rcases lt_or_gt_of_ne hz with h | h
  · right
    rw [hcast]
    have h' : ((m:ℤ)^2 - 2*(n:ℤ)^2) ≤ -1 := by omega
    exact_mod_cast h'
  · left
    rw [hcast]
    have h' : (1:ℤ) ≤ ((m:ℤ)^2 - 2*(n:ℤ)^2) := by omega
    exact_mod_cast h'

set_option maxHeartbeats 1000000 in
/-- The quantitative heart of part (b): an overlap `A m ∩ √2 • A n ≠ ∅` forces `n ≤ 7`. -/
lemma overlap_aux (a M N u v : ℝ) (ha2 : a^2 = 2) (halo : 1.414 < a) (hahi : a < 1.415)
    (hM : 1 ≤ M) (hN : 8 ≤ N) (hu : u * M^3 = 1) (hv : v * N^3 = 1)
    (h1 : a*N - M < u) (h2 : M - a*N < a*v)
    (hint : 1 ≤ M^2 - 2*N^2 ∨ M^2 - 2*N^2 ≤ -1) : False := by
  have hN0 : (0:ℝ) < N := by linarith
  have hM0 : (0:ℝ) < M := by linarith
  have hM3 : (1:ℝ) ≤ M^3 := one_le_pow₀ hM
  have hu0 : 0 < u := by nlinarith
  have hule : u ≤ 1 := by nlinarith
  have hN3pos : (0:ℝ) < N^3 := by positivity
  have hv0 : 0 < v := by nlinarith
  have hMN : N/2 ≤ M := by nlinarith
  have hN3 : N^3/8 ≤ M^3 := by nlinarith [sq_nonneg (M - N/2), sq_nonneg (M + N/2)]
  have huv : u ≤ 8*v := by nlinarith
  have hNv : N*v ≤ 1/64 := by nlinarith [sq_nonneg N]
  have hsum : M + a*N ≤ 3*N := by nlinarith
  have hsum0 : 0 < M + a*N := by nlinarith
  rcases hint with h | h
  · have hfac : (M - a*N) * (M + a*N) = M^2 - 2*N^2 := by linear_combination (-(N^2)) * ha2
    have hd : 0 < M - a*N := by nlinarith
    have hstep : (M - a*N) * (M + a*N) ≤ (a*v) * (3*N) :=
      mul_le_mul h2.le hsum hsum0.le (by nlinarith)
    nlinarith
  · have hfac : (a*N - M) * (M + a*N) = 2*N^2 - M^2 := by linear_combination (N^2) * ha2
    have hd : 0 < a*N - M := by nlinarith
    have hstep : (a*N - M) * (M + a*N) ≤ u * (3*N) :=
      mul_le_mul h1.le hsum hsum0.le (by nlinarith)
    nlinarith

/-- Only boundedly many overlaps occur for `a = √2`; all of them live in `[0, 12)`. -/
lemma sqrt_two_overlap (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (t : ℝ)
    (htm : t ∈ A m) (htn : t / Real.sqrt 2 ∈ A n) : t < 12 := by
  set a := Real.sqrt 2 with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have halo := sqrt_two_lo
  have hahi := sqrt_two_hi
  have hM : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hN : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  obtain ⟨hm1, hm2⟩ := htm
  obtain ⟨hn1, hn2⟩ := htn
  rw [le_div_iff₀ ha0] at hn1
  rw [div_lt_iff₀ ha0] at hn2
  have hvle : (((n:ℝ))^3)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact one_le_pow₀ hN
  have hule : (((m:ℝ))^3)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact one_le_pow₀ hM
  by_contra hc
  push_neg at hc
  have hn8 : (8:ℝ) ≤ (n:ℝ) := by
    by_contra hlt
    push_neg at hlt
    have hn7 : (n:ℝ) ≤ 7 := by
      have : n ≤ 7 := by
        by_contra hcc
        push_neg at hcc
        have : (8:ℝ) ≤ (n:ℝ) := by exact_mod_cast hcc
        linarith
      exact_mod_cast this
    nlinarith
  exact overlap_aux a (m:ℝ) (n:ℝ) (((m:ℝ)^3)⁻¹) (((n:ℝ)^3)⁻¹) sqrt_two_sq' halo hahi hM hn8
    (by field_simp) (by field_simp) (by linarith) (by linarith) (int_sep m n hn)

/-- **Part (b)**: the weighted integral at the irrational point `√2` is finite. -/
theorem J_sqrt_two_ne_top : J (Real.sqrt 2) ≠ ⊤ := by
  have h1le : (1:ℝ) ≤ Real.sqrt 2 := by
    nlinarith [sqrt_two_sq', Real.sqrt_nonneg 2]
  have hbound : ∀ t : ℝ, ENNReal.ofReal t * (f t * f (t / Real.sqrt 2))
      ≤ (Set.Ico (0:ℝ) 12).indicator (fun _ => ENNReal.ofReal (12^3)) t := by
    intro t
    by_cases h1 : f t = 0
    · simp [h1]
    by_cases h2 : f (t / Real.sqrt 2) = 0
    · simp [h2]
    obtain ⟨m, hm, htm⟩ := exists_of_f_ne_zero h1
    obtain ⟨n, hn, htn⟩ := exists_of_f_ne_zero h2
    have ht12 : t < 12 := sqrt_two_overlap m n hm hn t htm htn
    have ht0 : (0:ℝ) ≤ t := le_trans zero_le_one (one_le_of_f_ne_zero h1)
    rw [Set.indicator_of_mem (show t ∈ Set.Ico (0:ℝ) 12 from ⟨ht0, ht12⟩)]
    calc ENNReal.ofReal t * (f t * f (t / Real.sqrt 2))
        ≤ ENNReal.ofReal t * (ENNReal.ofReal t * ENNReal.ofReal (t / Real.sqrt 2)) := by
          gcongr <;> exact f_le_ofReal _
      _ = ENNReal.ofReal (t * (t * (t / Real.sqrt 2))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul ht0]
      _ ≤ ENNReal.ofReal (12^3) := by
          apply ENNReal.ofReal_le_ofReal
          have hdiv : t / Real.sqrt 2 ≤ t := by
            rw [div_le_iff₀ (by linarith)]
            nlinarith
          nlinarith [mul_nonneg ht0 ht0]
  have hle : J (Real.sqrt 2) ≤ ENNReal.ofReal (12^3) * ENNReal.ofReal 12 := by
    rw [J]
    calc ∫⁻ t, ENNReal.ofReal t * (f t * f (t / Real.sqrt 2))
        ≤ ∫⁻ t, (Set.Ico (0:ℝ) 12).indicator (fun _ => ENNReal.ofReal (12^3)) t :=
          lintegral_mono hbound
      _ = ENNReal.ofReal (12^3) * ENNReal.ofReal 12 := by
          rw [lintegral_indicator measurableSet_Ico, setLIntegral_const, Real.volume_Ico]
          norm_num
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hle

/-! ## Part (c) : an irrational number with `J = ∞` -/

/-- The Liouville-type number `L = ∑_{j ≥ 1} 10 ^ (-j!)`. -/
def L : ℝ := ∑' j : ℕ, (1 : ℝ) / (10 : ℝ) ^ (Nat.factorial (j + 1))

lemma L_summable : Summable (fun j : ℕ => (1:ℝ)/(10:ℝ)^((j+1)!)) := by
  apply summable_one_div_pow_of_le (by norm_num)
  intro i
  exact le_trans (Nat.le_succ i) (Nat.self_le_factorial (i+1))

/-- Splitting `L` into its first `k` terms and the Liouville remainder. -/
lemma L_split (k : ℕ) :
    L = (∑ j ∈ Finset.range k, (1:ℝ)/(10:ℝ)^((j+1)!)) + LiouvilleNumber.remainder 10 k := by
  rw [L, ← L_summable.sum_add_tsum_nat_add k]; rfl

/-- The numerator of the `k`-th truncation of `L`, i.e. `10 ^ k ! * ∑_{j ≤ k} 10 ^ (-j!)`. -/
def Pnum (k : ℕ) : ℕ := ∑ j ∈ Finset.range k, 10 ^ (Nat.factorial k - Nat.factorial (j+1))

lemma Pnum_div (k : ℕ) :
    (Pnum k : ℝ) / (10:ℝ)^(k !) = ∑ j ∈ Finset.range k, (1:ℝ)/(10:ℝ)^((j+1)!) := by
  rw [Pnum]; push_cast; rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : (j+1)! ≤ k ! := Nat.factorial_le (by simp at hj; omega)
  rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add, Nat.sub_add_cancel hj']

lemma NR_pos (j : ℕ) : (0:ℝ) < (10:ℝ)^(j !) := by positivity

lemma NR_ge_one (j : ℕ) : (1:ℝ) ≤ (10:ℝ)^(j !) := one_le_pow₀ (by norm_num)

lemma NR_big (j : ℕ) (hj : 4 ≤ j) : (10000:ℝ) ≤ (10:ℝ)^(j !) := by
  have h1 : 4 ≤ j ! := le_trans hj (Nat.self_le_factorial j)
  calc (10000:ℝ) = (10:ℝ)^4 := by norm_num
    _ ≤ (10:ℝ)^(j !) := pow_le_pow_right₀ (by norm_num) h1

lemma X_le_one (j : ℕ) : (((10:ℝ)^(j !))^3)⁻¹ ≤ 1 := by
  rw [inv_le_one_iff₀]; right; exact one_le_pow₀ (NR_ge_one j)

lemma L_sub_eq (j : ℕ) : L * (10:ℝ)^(j !) - Pnum j
    = (10:ℝ)^(j !) * LiouvilleNumber.remainder 10 j := by
  have h := L_split j
  have h2 := Pnum_div j
  have hN := NR_pos j
  field_simp at h2 ⊢
  nlinarith [h, h2]

/-- The truncations approximate `L` strictly from below. -/
lemma L_approx_pos (j : ℕ) : 0 < L * (10:ℝ)^(j !) - Pnum j := by
  rw [L_sub_eq]
  exact mul_pos (NR_pos j) (LiouvilleNumber.remainder_pos (by norm_num) j)

lemma L_approx_lt' (j : ℕ) :
    L * (10:ℝ)^(j !) - Pnum j < (10:ℝ)^(j !) / ((10:ℝ)^(j !))^j := by
  rw [L_sub_eq, ← mul_one_div]
  exact mul_lt_mul_of_pos_left (LiouvilleNumber.remainder_lt j (by norm_num)) (NR_pos j)

/-- The Liouville tail estimate at the quartic scale: `10^{j!} L - P_j < 10^{-3 j!}`. -/
lemma L_approx_lt (j : ℕ) (hj : 4 ≤ j) :
    L * (10:ℝ)^(j !) - Pnum j < (((10:ℝ)^(j !))^3)⁻¹ := by
  refine lt_of_lt_of_le (L_approx_lt' j) ?_
  have h2 : ((10:ℝ)^(j !))^4 ≤ ((10:ℝ)^(j !))^j := pow_le_pow_right₀ (NR_ge_one j) hj
  have h3 : (0:ℝ) < ((10:ℝ)^(j !))^j := by positivity
  have h4 : (0:ℝ) < ((10:ℝ)^(j !))^3 := by positivity
  rw [div_le_iff₀ h3, inv_mul_eq_div, le_div_iff₀ h4]
  calc (10:ℝ)^(j !) * ((10:ℝ)^(j !))^3 = ((10:ℝ)^(j !))^4 := by ring
    _ ≤ ((10:ℝ)^(j !))^j := h2

lemma Pnum_one : Pnum 1 = 1 := by decide

lemma L_lo : 1/10 < L := by
  have h := L_approx_pos 1
  rw [Pnum_one] at h
  norm_num [Nat.factorial] at h ⊢
  linarith

lemma L_hi : L < 1/5 := by
  have h := L_approx_lt' 1
  rw [Pnum_one] at h
  norm_num [Nat.factorial] at h ⊢
  linarith

/-- `L` is a positive real number. -/
theorem L_pos : 0 < L := lt_trans (by norm_num) L_lo

lemma liouvilleNumber_ten : liouvilleNumber 10 = 1/10 + L := by
  rw [liouvilleNumber,
    ← (LiouvilleNumber.summable (m := (10:ℝ)) (by norm_num)).sum_add_tsum_nat_add 1]
  norm_num [Nat.factorial, L]

/-- `L` is irrational. -/
theorem irrational_L : Irrational L := by
  have h : Irrational (liouvilleNumber 10) :=
    (liouville_liouvilleNumber (m := 10) (by norm_num)).irrational
  rw [liouvilleNumber_ten, add_comm, show (1/10 : ℝ) = ((1/10 : ℚ) : ℝ) by norm_num] at h
  exact h.of_add_ratCast (1/10 : ℚ)

lemma Pnum_bounds (j : ℕ) (hj : 4 ≤ j) :
    (10:ℝ)^(j !)/20 ≤ (Pnum j : ℝ) ∧ (Pnum j : ℝ) ≤ (10:ℝ)^(j !)/5 := by
  have hN := NR_big j hj
  have hX := X_le_one j
  have h0 := L_approx_pos j
  have h1 := L_approx_lt j hj
  have hlo := L_lo
  have hhi := L_hi
  constructor <;> nlinarith

lemma NR_succ (j : ℕ) (hj : 1 ≤ j) : 10 * (10:ℝ)^(j !) ≤ (10:ℝ)^((j+1)!) := by
  have h1 : (j+1)! = j * j ! + j ! := by rw [Nat.factorial_succ]; ring
  have h2 : 1 ≤ j * j ! := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h3 : j ! + 1 ≤ (j+1)! := by omega
  calc 10 * (10:ℝ)^(j !) = (10:ℝ)^(j ! + 1) := by rw [pow_succ]; ring
    _ ≤ (10:ℝ)^((j+1)!) := pow_le_pow_right₀ (by norm_num) h3

lemma Pnum_lt_succ (j : ℕ) (hj : 4 ≤ j) : Pnum j < Pnum (j+1) := by
  have h1 := (Pnum_bounds j hj).2
  have h2 := (Pnum_bounds (j+1) (by omega)).1
  have h3 := NR_succ j (by omega)
  have h4 := NR_pos j
  have h5 : (Pnum j : ℝ) < (Pnum (j+1) : ℝ) := by linarith
  exact_mod_cast h5

/-- The overlap interval sits inside `A (P j)`. -/
lemma L_overlap_left (j : ℕ) (hj : 4 ≤ j) :
    Set.Ico (L * (10:ℝ)^(j !)) (L * (10:ℝ)^(j !) + (((10:ℝ)^(j !))^3)⁻¹/10) ⊆ A (Pnum j) := by
  have hNpos := NR_pos j
  have hNbig := NR_big j hj
  have hM := Pnum_bounds j hj
  have hd0 := L_approx_pos j
  have hd1 := L_approx_lt j hj
  have hMpos : (0:ℝ) < (Pnum j : ℝ) := by linarith [hM.1]
  have hXN : (((10:ℝ)^(j !))^3)⁻¹ * ((10:ℝ)^(j !))^3 = 1 := inv_mul_cancel₀ (by positivity)
  have hYM : (((Pnum j : ℝ))^3)⁻¹ * ((Pnum j : ℝ))^3 = 1 := inv_mul_cancel₀ (by positivity)
  have hX0 : (0:ℝ) < (((10:ℝ)^(j !))^3)⁻¹ := by positivity
  have hM3 : ((Pnum j : ℝ))^3 ≤ ((10:ℝ)^(j !))^3/125 := by
    calc ((Pnum j : ℝ))^3 ≤ ((10:ℝ)^(j !)/5)^3 := pow_le_pow_left₀ hMpos.le hM.2 3
      _ = ((10:ℝ)^(j !))^3/125 := by ring
  have hM3pos : (0:ℝ) < ((Pnum j : ℝ))^3 := by positivity
  have hY : 125 * (((10:ℝ)^(j !))^3)⁻¹ ≤ (((Pnum j : ℝ))^3)⁻¹ := by
    nlinarith [hYM, hXN, hM3, hX0, hM3pos]
  rw [A]
  exact Set.Ico_subset_Ico (by linarith) (by linarith)

/-- Rescaling by `L` maps the overlap interval into `A (10 ^ j !)`. -/
lemma L_overlap_right (j : ℕ) :
    ∀ t ∈ Set.Ico (L * (10:ℝ)^(j !)) (L * (10:ℝ)^(j !) + (((10:ℝ)^(j !))^3)⁻¹/10),
      t / L ∈ A (10 ^ (j !)) := by
  intro t ht
  have hL0 : (0:ℝ) < L := L_pos
  have hLlo := L_lo
  have hNpos := NR_pos j
  have hX0 : (0:ℝ) < (((10:ℝ)^(j !))^3)⁻¹ := by positivity
  have hcast : ((10 ^ (j !) : ℕ) : ℝ) = (10:ℝ)^(j !) := by push_cast; ring
  obtain ⟨h1, h2⟩ := ht
  rw [A, hcast]
  constructor
  · rw [le_div_iff₀ hL0]; nlinarith
  · rw [div_lt_iff₀ hL0]; nlinarith

/-- The contribution of the `j`-th overlap to `J L` is bounded below by a fixed constant. -/
lemma L_weight_bound (j : ℕ) (hj : 4 ≤ j) :
    (1:ℝ)/2000 ≤ L * (10:ℝ)^(j !) * ((Pnum j : ℝ) * (10:ℝ)^(j !)) * ((((10:ℝ)^(j !))^3)⁻¹/10) := by
  have hNpos := NR_pos j
  have hNbig := NR_big j hj
  have hM := Pnum_bounds j hj
  have hLlo := L_lo
  have hX0 : (0:ℝ) < (((10:ℝ)^(j !))^3)⁻¹ := by positivity
  have hXN : (((10:ℝ)^(j !))^3)⁻¹ * ((10:ℝ)^(j !))^3 = 1 := inv_mul_cancel₀ (by positivity)
  have e1 : (10:ℝ)^(j !)/10 ≤ L * (10:ℝ)^(j !) := by nlinarith
  have e2 : ((10:ℝ)^(j !)/20) * (10:ℝ)^(j !) ≤ (Pnum j : ℝ) * (10:ℝ)^(j !) := by
    nlinarith [hM.1]
  have hstep : (10:ℝ)^(j !)/10 * (((10:ℝ)^(j !)/20) * (10:ℝ)^(j !)) * ((((10:ℝ)^(j !))^3)⁻¹/10)
      ≤ L * (10:ℝ)^(j !) * ((Pnum j : ℝ) * (10:ℝ)^(j !)) * ((((10:ℝ)^(j !))^3)⁻¹/10) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul e1 e2 (by positivity) (by positivity)) (by positivity)
  have heq : (10:ℝ)^(j !)/10 * (((10:ℝ)^(j !)/20) * (10:ℝ)^(j !)) * ((((10:ℝ)^(j !))^3)⁻¹/10)
      = 1/2000 := by
    linear_combination (2000:ℝ)⁻¹ * hXN
  linarith [heq ▸ hstep]

/-- **Part (c)**: the weighted integral diverges at the irrational point `L`. -/
theorem J_L_eq_top : J L = ⊤ := by
  have hL0 : (0:ℝ) < L := L_pos
  rw [J]
  refine lintegral_eq_top_of_family _ (fun k => Pnum (k+4))
    (fun k => L * (10:ℝ)^((k+4)!))
    (fun k => L * (10:ℝ)^((k+4)!) + (((10:ℝ)^((k+4)!))^3)⁻¹/10)
    (fun k => ENNReal.ofReal (L * (10:ℝ)^((k+4)!)) *
      ((Pnum (k+4) : ℝ≥0∞) * ((10 ^ ((k+4)!) : ℕ) : ℝ≥0∞))) ?_ ?_ ?_ ?_
  · have hmono : StrictMono (fun k : ℕ => Pnum (k+4)) :=
      strictMono_nat_of_lt_succ fun k => Pnum_lt_succ (k+4) (by omega)
    exact hmono.injective
  · exact fun k => L_overlap_left (k+4) (by omega)
  · intro k t ht
    rw [f_eq_of_mem (L_overlap_left (k+4) (by omega) ht),
      f_eq_of_mem (L_overlap_right (k+4) t ht)]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal ht.1) _
  · refine top_le_iff.1 ?_
    calc (⊤ : ℝ≥0∞) = ∑' _k : ℕ, ENNReal.ofReal ((1:ℝ)/2000) :=
          (ENNReal.tsum_const_eq_top_of_ne_zero (by simp)).symm
      _ ≤ _ := ENNReal.tsum_le_tsum fun k => ?_
    have hcast : ((10 ^ ((k+4)!) : ℕ) : ℝ) = (10:ℝ)^((k+4)!) := by push_cast; ring
    have hNpos := NR_pos (k+4)
    have hX0 : (0:ℝ) < ((((10:ℝ)^((k+4)!))^3))⁻¹ := by positivity
    have hterm : ENNReal.ofReal (L * (10:ℝ)^((k+4)!)) *
        ((Pnum (k+4) : ℝ≥0∞) * ((10 ^ ((k+4)!) : ℕ) : ℝ≥0∞)) *
        ENNReal.ofReal ((L * (10:ℝ)^((k+4)!) + (((10:ℝ)^((k+4)!))^3)⁻¹/10)
          - L * (10:ℝ)^((k+4)!))
        = ENNReal.ofReal (L * (10:ℝ)^((k+4)!) *
            ((Pnum (k+4) : ℝ) * (10:ℝ)^((k+4)!)) * ((((10:ℝ)^((k+4)!))^3)⁻¹/10)) := by
      rw [← ENNReal.ofReal_natCast (Pnum (k+4)), ← ENNReal.ofReal_natCast (10 ^ ((k+4)!)),
        hcast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    rw [hterm]
    exact ENNReal.ofReal_le_ofReal (L_weight_bound (k+4) (by omega))

end

end Q885
