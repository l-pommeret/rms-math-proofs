/-
# Q899 : a square function estimate for averaging projections onto intervals

For a nondegenerate closed interval `I = [a,b] ⊆ [0,1]` the averaging projection is
`P_I f = (average of f over I) * 1_I`.  We prove, at the exponent `p = 4`, the square function
inequality

  ‖(∑ j, |P_{I j} f j|²)^{1/2}‖_{L⁴(0,1)} ≤ C * ‖(∑ j, |f j|²)^{1/2}‖_{L⁴(0,1)}

with the explicit constant `C = 2√2`, uniformly in the number `N` of intervals, in the
intervals themselves and in the functions, and we deduce the existential statement asked
for in Q899 (`∃ p > 2, ∃ C ≥ 1, ...`).

The proof follows the classical route: a weak type estimate for the uncentered maximal
function of the family (via the Vitali covering lemma), the layer cake formula, and the
duality/Cauchy--Schwarz argument.  All the maximal function theory used here is developed
from scratch, since mathlib does not contain the Hardy--Littlewood maximal theorem.
-/
import Mathlib

open MeasureTheory Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace Q899

/-! ## Definitions -/

/-- Average of an `ℝ≥0∞`-valued function over a set, with respect to Lebesgue measure. -/
def avgOn (I : Set ℝ) (u : ℝ → ℝ≥0∞) : ℝ≥0∞ := (∫⁻ y in I, u y) / volume I

/-- The uncentered maximal function attached to a finite family of sets: at the point `x` it
is the largest of the averages of `u` over those members of the family which contain `x`. -/
def maxFun {N : ℕ} (I : Fin N → Set ℝ) (u : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ⨆ j, (I j).indicator (fun _ => avgOn (I j) u) x

/-- The averaging projection onto the interval `[a,b]`:
`P_{[a,b]} f = ((b-a)⁻¹ ∫_{[a,b]} f) 1_{[a,b]}`. -/
def avgProj (a b : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (Set.Icc a b).indicator (fun _ => (b - a)⁻¹ * ∫ y in Set.Icc a b, f y)

/-! ## Layer cake lemmas -/

theorem setOf_pos_lt_eq (c : ℝ≥0∞) (hc : c ≠ ∞) :
    {t : ℝ | 0 < t ∧ ENNReal.ofReal t < c} = Ioo 0 c.toReal := by
  ext t
  simp only [mem_setOf_eq, mem_Ioo]
  constructor
  · rintro ⟨ht, h⟩; exact ⟨ht, by rwa [ENNReal.ofReal_lt_iff_lt_toReal ht.le hc] at h⟩
  · rintro ⟨ht, h⟩; exact ⟨ht, by rwa [ENNReal.ofReal_lt_iff_lt_toReal ht.le hc]⟩

theorem setOf_pos_lt_top : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < ∞} = Ioi 0 := by
  ext t; simp [ENNReal.ofReal_lt_top]

theorem measurableSet_setOf_pos_lt (c : ℝ≥0∞) :
    MeasurableSet {t : ℝ | 0 < t ∧ ENNReal.ofReal t < c} :=
  measurableSet_Ioi.inter (measurableSet_lt ENNReal.measurable_ofReal measurable_const)

theorem volume_setOf_pos_lt (c : ℝ≥0∞) :
    volume {t : ℝ | 0 < t ∧ ENNReal.ofReal t < c} = c := by
  rcases eq_or_ne c ∞ with rfl | hc
  · rw [setOf_pos_lt_top]; simp
  · rw [setOf_pos_lt_eq c hc, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal hc]

theorem lintegral_ofReal_Ioo (r : ℝ) (hr : 0 ≤ r) :
    ∫⁻ t in Ioo 0 r, ENNReal.ofReal t = ENNReal.ofReal (r ^ 2 / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr,
      integral_id]
    ring
  · have h : IntegrableOn (fun t : ℝ => t) (Ioc 0 r) volume :=
      (intervalIntegral.intervalIntegrable_id (a := 0) (b := r)).1
    exact h.mono_set Ioo_subset_Ioc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht using ht.1.le

theorem lintegral_ofReal_setOf_pos_lt (c : ℝ≥0∞) :
    ∫⁻ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < c}, ENNReal.ofReal t = c ^ 2 / 2 := by
  rcases eq_or_ne c ∞ with rfl | hc
  · rw [setOf_pos_lt_top]
    have h1 : ∫⁻ _ in Ioi (1:ℝ), (1:ℝ≥0∞) ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal t := by
      calc ∫⁻ _ in Ioi (1:ℝ), (1:ℝ≥0∞) ≤ ∫⁻ t in Ioi (1:ℝ), ENNReal.ofReal t := by
            refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
            simpa using ENNReal.one_le_ofReal.2 (le_of_lt ht)
        _ ≤ _ := lintegral_mono' (Measure.restrict_mono (Ioi_subset_Ioi zero_le_one) le_rfl) le_rfl
    have h2 : ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal t = ∞ := by
      simpa using top_le_iff.mp (le_trans (by simp) h1)
    rw [h2]
    simp [ENNReal.top_div]
  · rw [setOf_pos_lt_eq c hc, lintegral_ofReal_Ioo _ ENNReal.toReal_nonneg,
      ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hc]
    norm_num

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Layer cake formula for the square of an `ℝ≥0∞`-valued function. -/
theorem lintegral_sq_eq_layercake [SFinite μ] {G : α → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x ^ 2 ∂μ =
      2 * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t * μ {x | ENNReal.ofReal t < G x} := by
  set F : ℝ → α → ℝ≥0∞ := fun t x => if ENNReal.ofReal t < G x then ENNReal.ofReal t else 0
    with hF
  have hmeasset : MeasurableSet {p : ℝ × α | ENNReal.ofReal p.1 < G p.2} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst) (hG.comp measurable_snd)
  have hFmeas : Measurable (Function.uncurry F) :=
    Measurable.ite hmeasset (ENNReal.measurable_ofReal.comp measurable_fst) measurable_const
  have step1 : ∀ t : ℝ, ENNReal.ofReal t * μ {x | ENNReal.ofReal t < G x} = ∫⁻ x, F t x ∂μ := by
    intro t
    rw [← lintegral_indicator_const (measurableSet_lt measurable_const hG)]
    congr 1 with x
    by_cases hx : ENNReal.ofReal t < G x <;> simp [hF, hx]
  simp_rw [step1]
  rw [lintegral_lintegral_swap hFmeas.aemeasurable]
  have inner : ∀ x : α, ∫⁻ t in Ioi (0:ℝ), F t x = G x ^ 2 / 2 := by
    intro x
    have h : ∫⁻ t in Ioi (0:ℝ), F t x
        = ∫⁻ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < G x}, ENNReal.ofReal t := by
      rw [← lintegral_indicator measurableSet_Ioi,
        ← lintegral_indicator (measurableSet_setOf_pos_lt (G x))]
      congr 1 with t
      by_cases ht : 0 < t <;> by_cases hgt : ENNReal.ofReal t < G x <;> simp [hF, ht, hgt]
    rw [h, lintegral_ofReal_setOf_pos_lt]
  simp_rw [inner]
  rw [← lintegral_const_mul _ ((hG.pow_const 2).div_const 2)]
  congr 1 with x
  rw [ENNReal.mul_div_cancel' (by norm_num) (by norm_num)]

/-- Tonelli: integrating the "tail integrals" of `h` over the level sets of `G` gives `∫ h G`. -/
theorem lintegral_layercake_mul [SFinite μ] {G h : α → ℝ≥0∞} (hG : Measurable G)
    (hh : Measurable h) :
    ∫⁻ t in Ioi (0 : ℝ), (∫⁻ x in {x | ENNReal.ofReal t < G x}, h x ∂μ) = ∫⁻ x, h x * G x ∂μ := by
  set F : ℝ → α → ℝ≥0∞ := fun t x => if ENNReal.ofReal t < G x then h x else 0 with hF
  have hmeasset : MeasurableSet {p : ℝ × α | ENNReal.ofReal p.1 < G p.2} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst) (hG.comp measurable_snd)
  have hFmeas : Measurable (Function.uncurry F) :=
    Measurable.ite hmeasset (hh.comp measurable_snd) measurable_const
  have step1 : ∀ t : ℝ, (∫⁻ x in {x | ENNReal.ofReal t < G x}, h x ∂μ) = ∫⁻ x, F t x ∂μ := by
    intro t
    rw [← lintegral_indicator (measurableSet_lt measurable_const hG)]
    congr 1 with x
    by_cases hx : ENNReal.ofReal t < G x <;> simp [hF, hx]
  simp_rw [step1]
  rw [lintegral_lintegral_swap hFmeas.aemeasurable]
  congr 1 with x
  have h1 : ∫⁻ t in Ioi (0:ℝ), F t x =
      ∫⁻ t, ({t : ℝ | 0 < t ∧ ENNReal.ofReal t < G x}).indicator (fun _ => h x) t := by
    rw [← lintegral_indicator measurableSet_Ioi]
    congr 1 with t
    by_cases ht : 0 < t <;> by_cases hgt : ENNReal.ofReal t < G x <;> simp [hF, ht, hgt]
  rw [h1, lintegral_indicator_const (measurableSet_setOf_pos_lt (G x)), volume_setOf_pos_lt]

/-! ## Elementary facts about `avgOn` and `maxFun` -/

theorem avgOn_le_maxFun {N : ℕ} (I : Fin N → Set ℝ) (u : ℝ → ℝ≥0∞) {j : Fin N} {x : ℝ}
    (hx : x ∈ I j) : avgOn (I j) u ≤ maxFun I u x := by
  refine le_trans (le_of_eq ?_) (le_iSup (fun j => (I j).indicator (fun _ => avgOn (I j) u) x) j)
  rw [Set.indicator_of_mem hx]

theorem measurable_maxFun {N : ℕ} {I : Fin N → Set ℝ} (hI : ∀ j, MeasurableSet (I j))
    (u : ℝ → ℝ≥0∞) : Measurable (maxFun I u) :=
  Measurable.iSup fun j => measurable_const.indicator (hI j)

theorem setOf_lt_maxFun {N : ℕ} (I : Fin N → Set ℝ) (u : ℝ → ℝ≥0∞) (t : ℝ≥0∞) :
    {x | t < maxFun I u x} = ⋃ j ∈ {j : Fin N | t < avgOn (I j) u}, I j := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, maxFun, lt_iSup_iff, exists_prop]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hx : x ∈ I j
    · rw [Set.indicator_of_mem hx] at hj; exact ⟨j, hj, hx⟩
    · rw [Set.indicator_of_notMem hx] at hj; exact absurd hj (by simp)
  · rintro ⟨j, hj, hx⟩
    exact ⟨j, by rwa [Set.indicator_of_mem hx]⟩

/-- Cauchy--Schwarz for `ℝ≥0∞`-valued functions. -/
theorem cauchy_schwarz {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ x, f x * g x ∂μ ≤ (∫⁻ x, f x ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫⁻ x, g x ^ 2 ∂μ) ^ (1/2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have e : ∀ x : ℝ≥0∞, x ^ (2:ℝ) = x ^ (2:ℕ) := fun x => by
    rw [← ENNReal.rpow_natCast x 2]; norm_num
  simp only [Pi.mul_apply, e] at h
  exact h

/-- A function dominated by a constant on a set of finite measure and vanishing off that set
is square integrable. -/
theorem lintegral_sq_le_of_bdd {g : ℝ → ℝ≥0∞} {M : ℝ≥0∞} {S : Set ℝ} (hS : MeasurableSet S)
    (hg : ∀ x, g x ≤ S.indicator (fun _ => M) x) : ∫⁻ x, g x ^ 2 ≤ M ^ 2 * volume S := by
  calc ∫⁻ x, g x ^ 2 ≤ ∫⁻ x, S.indicator (fun _ => M ^ 2) x := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ S
        · simpa [hx] using pow_le_pow_left' (by simpa [hx] using hg x) 2
        · simp only [hx, Set.indicator_of_notMem, not_false_iff]
          simpa [hx] using hg x
    _ = M ^ 2 * volume S := lintegral_indicator_const hS _

/-- If `A ≤ K * B^(1/2) * A^(1/2)` and `A ≠ ∞` then `A ≤ K² * B`. -/
theorem le_sq_of_le_sqrt_mul {A B K : ℝ≥0∞} (hA : A ≠ ∞)
    (h : A ≤ K * B ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ)) : A ≤ K ^ 2 * B := by
  rcases eq_or_ne A 0 with rfl | hA0
  · simp
  have hs : A ^ (1/2 : ℝ) ≠ 0 := by simp [ENNReal.rpow_eq_zero_iff, hA0, hA]
  have hs' : A ^ (1/2 : ℝ) ≠ ∞ := by simp [ENNReal.rpow_eq_top_iff, hA0, hA]
  have hAA : A = A ^ (1/2 : ℝ) * A ^ (1/2 : ℝ) := by
    rw [← ENNReal.rpow_add _ _ hA0 hA]; norm_num
  have key : A ^ (1/2 : ℝ) ≤ K * B ^ (1/2 : ℝ) := by
    have h2 := h
    nth_rewrite 1 [hAA] at h2
    exact (ENNReal.mul_le_mul_iff_left hs hs').mp h2
  calc A = (A ^ (1/2:ℝ)) ^ (2:ℕ) := by
        rw [← ENNReal.rpow_natCast (A ^ (1/2:ℝ)) 2, ← ENNReal.rpow_mul]; norm_num
    _ ≤ (K * B ^ (1/2:ℝ)) ^ (2:ℕ) := by gcongr
    _ = K ^ 2 * B := by
        rw [mul_pow, ← ENNReal.rpow_natCast (B ^ (1/2:ℝ)) 2, ← ENNReal.rpow_mul]; norm_num

/-! ## The weak type estimate, via the Vitali covering lemma -/

theorem weak_type {N : ℕ} {a b : Fin N → ℝ} (hab : ∀ j, a j < b j) (u : ℝ → ℝ≥0∞) (t : ℝ≥0∞) :
    t * volume {x | t < maxFun (fun j => Icc (a j) (b j)) u x} ≤
      4 * ∫⁻ x in {x | t < maxFun (fun j => Icc (a j) (b j)) u x}, u x := by
  classical
  set I : Fin N → Set ℝ := fun j => Icc (a j) (b j) with hI
  set S : Set (Fin N) := {j | t < avgOn (I j) u} with hS
  set E : Set ℝ := {x | t < maxFun I u x} with hE
  have hEeq : E = ⋃ j ∈ S, I j := setOf_lt_maxFun I u t
  have hball : ∀ j, closedBall ((a j + b j)/2) ((b j - a j)/2) = I j := by
    intro j; rw [Real.closedBall_eq_Icc]; congr 1 <;> ring
  have hrnn : ∀ j, 0 ≤ (b j - a j)/2 := fun j => by linarith [hab j]
  have hvolI : ∀ j, volume (I j) = ENNReal.ofReal (b j - a j) := by
    intro j; simp [hI, Real.volume_Icc]
  have hvolI0 : ∀ j, volume (I j) ≠ 0 := by
    intro j; rw [hvolI j]; simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, sub_pos]; exact hab j
  have hvolItop : ∀ j, volume (I j) ≠ ∞ := by intro j; rw [hvolI j]; exact ENNReal.ofReal_ne_top
  set R : ℝ := ∑ k, (b k - a k)/2 with hR
  have hRle : ∀ j ∈ S, (b j - a j)/2 ≤ R :=
    fun j _ => Finset.single_le_sum (f := fun k => (b k - a k)/2) (fun k _ => hrnn k)
      (Finset.mem_univ j)
  obtain ⟨v, hvS, hvdisj, hvcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall S
      (fun j => (a j + b j)/2) (fun j => (b j - a j)/2) R hRle 4 (by norm_num)
  set vf : Finset (Fin N) := (Set.toFinite v).toFinset with hvf
  have hvfmem : ∀ k, k ∈ vf ↔ k ∈ v := fun k => Set.Finite.mem_toFinset _
  have hcover : E ⊆ ⋃ k ∈ vf, closedBall ((a k + b k)/2) (4 * ((b k - a k)/2)) := by
    rw [hEeq]
    intro x hx
    simp only [mem_iUnion, exists_prop] at hx ⊢
    obtain ⟨j, hjS, hxj⟩ := hx
    obtain ⟨k, hkv, hsub⟩ := hvcov j hjS
    exact ⟨k, (hvfmem k).2 hkv, hsub (by rw [hball j]; exact hxj)⟩
  have hvol : volume E ≤ ∑ k ∈ vf, 4 * volume (I k) := by
    refine le_trans (measure_mono hcover) (le_trans (measure_biUnion_finset_le _ _) ?_)
    refine Finset.sum_le_sum fun k _ => ?_
    rw [Real.volume_closedBall, ← hball k, Real.volume_closedBall,
      show 2 * (4 * ((b k - a k)/2)) = 4 * (2 * ((b k - a k)/2)) by ring,
      ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hkey : ∀ k ∈ vf, t * volume (I k) ≤ ∫⁻ x in I k, u x := by
    intro k hk
    have hkS : k ∈ S := hvS ((hvfmem k).1 hk)
    have h1 : t < (∫⁻ y in I k, u y) / volume (I k) := hkS
    exact ((ENNReal.lt_div_iff_mul_lt (Or.inl (hvolI0 k)) (Or.inl (hvolItop k))).1 h1).le
  have hdisj : (↑vf : Set (Fin N)).PairwiseDisjoint I := by
    intro j hj k hk hjk
    have h := hvdisj ((hvfmem j).1 hj) ((hvfmem k).1 hk) hjk
    simpa [Function.onFun, hball] using h
  have hsum : ∑ k ∈ vf, ∫⁻ x in I k, u x = ∫⁻ x in ⋃ k ∈ vf, I k, u x :=
    (lintegral_biUnion_finset hdisj (fun k _ => measurableSet_Icc) u).symm
  have hsub : (⋃ k ∈ vf, I k) ⊆ E := by
    rw [hEeq]
    refine iUnion₂_subset fun k hk => ?_
    exact subset_iUnion₂ (s := fun j (_ : j ∈ S) => I j) k (hvS ((hvfmem k).1 hk))
  calc t * volume E ≤ t * ∑ k ∈ vf, 4 * volume (I k) := by gcongr
    _ = 4 * ∑ k ∈ vf, t * volume (I k) := by
        rw [Finset.mul_sum, Finset.mul_sum]; congr 1 with k; ring
    _ ≤ 4 * ∑ k ∈ vf, ∫⁻ x in I k, u x := by gcongr with k hk; exact hkey k hk
    _ = 4 * ∫⁻ x in ⋃ k ∈ vf, I k, u x := by rw [hsum]
    _ ≤ 4 * ∫⁻ x in E, u x := by gcongr

/-! ## The maximal inequality in `L²` -/

theorem lintegral_maxFun_sq_le_mul {N : ℕ} {a b : Fin N → ℝ} (hab : ∀ j, a j < b j)
    {u : ℝ → ℝ≥0∞} (hu : Measurable u) :
    ∫⁻ x, maxFun (fun j => Icc (a j) (b j)) u x ^ 2 ≤
      8 * ∫⁻ x, u x * maxFun (fun j => Icc (a j) (b j)) u x := by
  set W := maxFun (fun j => Icc (a j) (b j)) u with hW
  have hWm : Measurable W := measurable_maxFun (fun _ => measurableSet_Icc) u
  calc ∫⁻ x, W x ^ 2
      = 2 * ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal t * volume {x | ENNReal.ofReal t < W x} :=
        lintegral_sq_eq_layercake hWm
    _ ≤ 2 * ∫⁻ t in Ioi (0:ℝ), 4 * ∫⁻ x in {x | ENNReal.ofReal t < W x}, u x :=
        mul_le_mul_right (lintegral_mono fun t => weak_type hab u (ENNReal.ofReal t)) 2
    _ = 8 * ∫⁻ t in Ioi (0:ℝ), ∫⁻ x in {x | ENNReal.ofReal t < W x}, u x := by
        rw [lintegral_const_mul' _ _ (by norm_num), ← mul_assoc]; norm_num
    _ = 8 * ∫⁻ x, u x * W x := by rw [lintegral_layercake_mul hWm hu]

theorem lintegral_maxFun_sq_le {N : ℕ} {a b : Fin N → ℝ} (hab : ∀ j, a j < b j)
    {u : ℝ → ℝ≥0∞} (hu : Measurable u)
    (hfin : ∫⁻ x, maxFun (fun j => Icc (a j) (b j)) u x ^ 2 ≠ ∞) :
    ∫⁻ x, maxFun (fun j => Icc (a j) (b j)) u x ^ 2 ≤ 64 * ∫⁻ x, u x ^ 2 := by
  set W := maxFun (fun j => Icc (a j) (b j)) u with hW
  have hWm : Measurable W := measurable_maxFun (fun _ => measurableSet_Icc) u
  have key : ∫⁻ x, W x ^ 2 ≤ 8 * (∫⁻ x, u x ^ 2) ^ (1/2:ℝ) * (∫⁻ x, W x ^ 2) ^ (1/2:ℝ) := by
    calc ∫⁻ x, W x ^ 2 ≤ 8 * ∫⁻ x, u x * W x := lintegral_maxFun_sq_le_mul hab hu
      _ ≤ 8 * ((∫⁻ x, u x ^ 2) ^ (1/2 : ℝ) * (∫⁻ x, W x ^ 2) ^ (1/2 : ℝ)) := by
          gcongr
          exact cauchy_schwarz hu.aemeasurable hWm.aemeasurable
      _ = _ := by ring
  have h2 := le_sq_of_le_sqrt_mul hfin key
  norm_num at h2
  exact h2

/-! ## The core inequality -/

/-- The core estimate: for a finite family of nondegenerate intervals `I j` and nonnegative
functions `u j`, the function `V = ∑ j, (average of u j over I j) 1_{I j}` satisfies
`∫ V² ≤ 64 ∫ (∑ j, u j)²`. -/
theorem core {N : ℕ} {a b : Fin N → ℝ} (hab : ∀ j, a j < b j) {u : Fin N → ℝ → ℝ≥0∞}
    (hu : ∀ j, AEMeasurable (u j) (volume : Measure ℝ)) :
    ∫⁻ x, (∑ j, (Icc (a j) (b j)).indicator
        (fun _ => avgOn (Icc (a j) (b j)) (u j)) x) ^ 2 ≤
      64 * ∫⁻ x, (∑ j, u j x) ^ 2 := by
  classical
  set I : Fin N → Set ℝ := fun j => Icc (a j) (b j) with hI
  set c : Fin N → ℝ≥0∞ := fun j => avgOn (I j) (u j) with hc
  set V : ℝ → ℝ≥0∞ := fun x => ∑ j, (I j).indicator (fun _ => c j) x with hVdef
  set U : ℝ → ℝ≥0∞ := fun x => ∑ j, u j x with hUdef
  have hIm : ∀ j, MeasurableSet (I j) := fun _ => measurableSet_Icc
  have hvolI : ∀ j, volume (I j) = ENNReal.ofReal (b j - a j) := by
    intro j; simp [hI, Real.volume_Icc]
  have hvolI0 : ∀ j, volume (I j) ≠ 0 := by
    intro j; rw [hvolI j]; simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, sub_pos]; exact hab j
  have hvolItop : ∀ j, volume (I j) ≠ ∞ := by intro j; rw [hvolI j]; exact ENNReal.ofReal_ne_top
  have hVm : Measurable V :=
    Finset.measurable_sum _ fun j _ => measurable_const.indicator (hIm j)
  have hUm : AEMeasurable U volume := by
    have h := Finset.aemeasurable_sum (μ := (volume : Measure ℝ)) Finset.univ fun j _ => hu j
    have e : (∑ i, u i) = U := by funext x; simp [hUdef, Finset.sum_apply]
    rwa [e] at h
  rcases eq_or_ne (∫⁻ x, U x ^ 2) ∞ with hB | hB
  · rw [hB]; simp
  -- all the averages are finite
  have hcfin : ∀ j, c j ≠ ∞ := by
    intro j
    have h1 : ∫⁻ x in I j, u j x ≤ ∫⁻ x in I j, U x :=
      lintegral_mono fun x =>
        Finset.single_le_sum (f := fun k => u k x) (fun k _ => zero_le _) (Finset.mem_univ j)
    have h2 : ∫⁻ x in I j, U x ≤ (∫⁻ x in I j, U x ^ 2) ^ (1/2:ℝ) * (volume (I j)) ^ (1/2:ℝ) := by
      simpa using
        cauchy_schwarz (μ := volume.restrict (I j)) hUm.restrict (aemeasurable_const (b := (1:ℝ≥0∞)))
    have h3 : ∫⁻ x in I j, U x ^ 2 ≤ ∫⁻ x, U x ^ 2 := setLIntegral_le_lintegral _ _
    have h4 : ∫⁻ x in I j, u j x ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (h1.trans h2)
      exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ne_top_of_le_ne_top hB h3))
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hvolItop j))
    exact ENNReal.div_ne_top h4 (hvolI0 j)
  set M : ℝ≥0∞ := ∑ j, c j with hM
  have hMfin : M ≠ ∞ := ENNReal.sum_ne_top.mpr fun j _ => hcfin j
  set S : Set ℝ := ⋃ j, I j with hSdef
  have hSm : MeasurableSet S := MeasurableSet.iUnion hIm
  have hSfin : volume S ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr fun j _ => hvolItop j)
      (measure_iUnion_fintype_le volume I)
  have hVbdd : ∀ x, V x ≤ S.indicator (fun _ => M) x := by
    intro x
    by_cases hx : x ∈ S
    · simp only [hx, Set.indicator_of_mem, hVdef, hM]
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases hxj : x ∈ I j <;> simp [hxj]
    · have hall : ∀ j, x ∉ I j := fun j hxj => hx (Set.mem_iUnion.2 ⟨j, hxj⟩)
      simp [hVdef, hall, hx]
  have hAfin : ∫⁻ x, V x ^ 2 ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top hMfin) hSfin)
      (lintegral_sq_le_of_bdd hSm hVbdd)
  set W : ℝ → ℝ≥0∞ := maxFun I V with hWdef
  have hWm : Measurable W := measurable_maxFun hIm V
  have havgVM : ∀ j, avgOn (I j) V ≤ M := by
    intro j
    rw [avgOn, ENNReal.div_le_iff (hvolI0 j) (hvolItop j)]
    calc ∫⁻ y in I j, V y ≤ ∫⁻ _ in I j, M := lintegral_mono fun y => by
          refine le_trans (hVbdd y) ?_
          by_cases hy : y ∈ S <;> simp [hy]
      _ = M * volume (I j) := by rw [setLIntegral_const]
  have hWbdd : ∀ x, W x ≤ S.indicator (fun _ => M) x := by
    intro x
    by_cases hx : x ∈ S
    · simp only [hx, Set.indicator_of_mem]
      refine iSup_le fun j => ?_
      by_cases hxj : x ∈ I j
      · simpa [hxj] using havgVM j
      · simp [hxj]
    · have hall : ∀ j, x ∉ I j := fun j hxj => hx (Set.mem_iUnion.2 ⟨j, hxj⟩)
      simp [hWdef, maxFun, hall, hx]
  have hWfin : ∫⁻ x, W x ^ 2 ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top hMfin) hSfin)
      (lintegral_sq_le_of_bdd hSm hWbdd)
  -- the duality argument
  have step1 : ∫⁻ x, V x ^ 2 = ∑ j, ∫⁻ x, (I j).indicator (fun _ => c j) x * V x := by
    rw [← lintegral_finset_sum _ (fun j _ => (measurable_const.indicator (hIm j)).mul hVm)]
    refine lintegral_congr fun x => ?_
    rw [← Finset.sum_mul, sq]
  have step2 : ∀ j, ∫⁻ x, (I j).indicator (fun _ => c j) x * V x ≤ ∫⁻ x, u j x * W x := by
    intro j
    have e0 : ∀ x, (I j).indicator (fun _ => c j) x * V x
        = (I j).indicator (fun x => c j * V x) x := by
      intro x; by_cases hx : x ∈ I j <;> simp [hx]
    have e1 : ∫⁻ x, (I j).indicator (fun _ => c j) x * V x = c j * ∫⁻ x in I j, V x := by
      simp_rw [e0]
      rw [lintegral_indicator (hIm j), lintegral_const_mul _ hVm]
    have e2 : ∫⁻ x in I j, V x = avgOn (I j) V * volume (I j) := by
      rw [avgOn, ENNReal.div_mul_cancel (hvolI0 j) (hvolItop j)]
    have e3 : c j * volume (I j) = ∫⁻ x in I j, u j x := by
      show avgOn (I j) (u j) * volume (I j) = _
      rw [avgOn, ENNReal.div_mul_cancel (hvolI0 j) (hvolItop j)]
    have e4 : c j * ∫⁻ x in I j, V x = (∫⁻ x in I j, u j x) * avgOn (I j) V := by
      rw [e2, ← e3]; ring
    have e5 : (∫⁻ x in I j, u j x) * avgOn (I j) V = ∫⁻ x in I j, u j x * avgOn (I j) V :=
      (lintegral_mul_const' _ _ (ne_top_of_le_ne_top hMfin (havgVM j))).symm
    rw [e1, e4, e5]
    calc ∫⁻ x in I j, u j x * avgOn (I j) V ≤ ∫⁻ x in I j, u j x * W x := by
          refine setLIntegral_mono' (hIm j) fun x hx => ?_
          exact mul_le_mul_right (avgOn_le_maxFun I V hx) _
      _ ≤ ∫⁻ x, u j x * W x := setLIntegral_le_lintegral _ _
  have step3 : ∫⁻ x, V x ^ 2 ≤ ∫⁻ x, U x * W x := by
    calc ∫⁻ x, V x ^ 2 = ∑ j, ∫⁻ x, (I j).indicator (fun _ => c j) x * V x := step1
      _ ≤ ∑ j, ∫⁻ x, u j x * W x := Finset.sum_le_sum fun j _ => step2 j
      _ = ∫⁻ x, U x * W x := by
          rw [← lintegral_finset_sum' _ (fun j _ => (hu j).mul hWm.aemeasurable)]
          refine lintegral_congr fun x => ?_
          simp only [hUdef]
          rw [Finset.sum_mul]
  have hWsq : (∫⁻ x, W x ^ 2) ^ (1/2:ℝ) ≤ 8 * (∫⁻ x, V x ^ 2) ^ (1/2:ℝ) := by
    have h := lintegral_maxFun_sq_le hab hVm hWfin
    calc (∫⁻ x, W x ^ 2) ^ (1/2:ℝ) ≤ (64 * ∫⁻ x, V x ^ 2) ^ (1/2:ℝ) := by gcongr
      _ = 8 * (∫⁻ x, V x ^ 2) ^ (1/2:ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
          congr 1
          rw [show (64:ℝ≥0∞) = 8 ^ (2:ℕ) by norm_num, ← ENNReal.rpow_natCast (8:ℝ≥0∞) 2,
            ← ENNReal.rpow_mul]
          norm_num
  have final : ∫⁻ x, V x ^ 2 ≤ 8 * (∫⁻ x, U x ^ 2) ^ (1/2:ℝ) * (∫⁻ x, V x ^ 2) ^ (1/2:ℝ) := by
    calc ∫⁻ x, V x ^ 2 ≤ ∫⁻ x, U x * W x := step3
      _ ≤ (∫⁻ x, U x ^ 2) ^ (1/2:ℝ) * (∫⁻ x, W x ^ 2) ^ (1/2:ℝ) :=
          cauchy_schwarz hUm hWm.aemeasurable
      _ ≤ (∫⁻ x, U x ^ 2) ^ (1/2:ℝ) * (8 * (∫⁻ x, V x ^ 2) ^ (1/2:ℝ)) := by gcongr
      _ = 8 * (∫⁻ x, U x ^ 2) ^ (1/2:ℝ) * (∫⁻ x, V x ^ 2) ^ (1/2:ℝ) := by ring
  have := le_sq_of_le_sqrt_mul hAfin final
  norm_num at this
  exact this

/-! ## The `L⁴` square function inequality -/

/-- Lebesgue measure on the unit interval. -/
def volIcc : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

/-- On a subinterval of `[0,1]` integrating against `volIcc` is the same as integrating against
Lebesgue measure; in particular `avgProj` is the averaging projection of the problem, whether
read in `L⁴(0,1)` or on the line. -/
theorem setIntegral_volIcc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (f : ℝ → ℝ) :
    ∫ y in Icc a b, f y ∂volIcc = ∫ y in Icc a b, f y := by
  rw [volIcc, Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_self_of_subset_left (Icc_subset_Icc ha hb)]

/-- Cauchy--Schwarz on an interval: the square of the average of `f` over `[a,b]` is at most
the average of `f²`. -/
theorem proj_sq_le (a b : ℝ) (hab : a < b) (f : ℝ → ℝ)
    (hf : AEMeasurable f (volume.restrict (Icc a b))) :
    ENNReal.ofReal (((b - a)⁻¹ * ∫ y in Icc a b, f y) ^ 2)
      ≤ avgOn (Icc a b) (fun y => ENNReal.ofReal (f y ^ 2)) := by
  set J : Set ℝ := Icc a b with hJ
  set L : ℝ≥0∞ := volume J with hL
  have hLval : L = ENNReal.ofReal (b - a) := by simp [hL, hJ, Real.volume_Icc]
  have hL0 : L ≠ 0 := by
    rw [hLval]; simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, sub_pos]; exact hab
  have hLtop : L ≠ ∞ := by rw [hLval]; exact ENNReal.ofReal_ne_top
  set X : ℝ≥0∞ := ∫⁻ y in J, ENNReal.ofReal (f y ^ 2) with hX
  set A : ℝ≥0∞ := ENNReal.ofReal |∫ y in J, f y| with hA
  have hstep1 : A ≤ ∫⁻ y in J, ENNReal.ofReal |f y| := by
    have h := MeasureTheory.enorm_integral_le_lintegral_enorm (μ := volume.restrict J) (f := f)
    simpa [hA, Real.enorm_eq_ofReal_abs] using h
  have hstep2 : ∫⁻ y in J, ENNReal.ofReal |f y| ≤ X ^ (1/2:ℝ) * L ^ (1/2:ℝ) := by
    have h := cauchy_schwarz (μ := volume.restrict J) (f := fun y => ENNReal.ofReal |f y|)
      (g := fun _ => (1:ℝ≥0∞)) (ENNReal.measurable_ofReal.comp_aemeasurable hf.abs)
      aemeasurable_const
    have e : ∀ y : ℝ, ENNReal.ofReal |f y| ^ 2 = ENNReal.ofReal (f y ^ 2) := fun y => by
      rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    simp only [mul_one, e, one_pow] at h
    simpa [hX, hL] using h
  have hAsq : A ^ 2 ≤ X * L := by
    calc A ^ 2 ≤ (X ^ (1/2:ℝ) * L ^ (1/2:ℝ)) ^ 2 := by gcongr; exact hstep1.trans hstep2
      _ = X * L := by
          rw [mul_pow, ← ENNReal.rpow_natCast (X ^ (1/2:ℝ)) 2, ← ENNReal.rpow_mul,
            ← ENNReal.rpow_natCast (L ^ (1/2:ℝ)) 2, ← ENNReal.rpow_mul]
          norm_num
  have hm : ENNReal.ofReal (((b - a)⁻¹ * ∫ y in J, f y) ^ 2) = A ^ 2 / L ^ 2 := by
    have h1 : ((b - a)⁻¹ * ∫ y in J, f y) ^ 2 = (|∫ y in J, f y| / (b-a)) ^ 2 := by
      rw [div_pow, sq_abs, mul_pow, inv_pow, div_eq_inv_mul]
    rw [h1, ENNReal.ofReal_pow (div_nonneg (abs_nonneg _) (by linarith)),
      ENNReal.ofReal_div_of_pos (by linarith), ← hA, ← hLval,
      ENNReal.div_eq_inv_mul, mul_pow, ← ENNReal.inv_pow, ENNReal.div_eq_inv_mul]
  rw [hm, avgOn, ← hX, ← hL]
  calc A ^ 2 / L ^ 2 = A ^ 2 / (L * L) := by rw [show (L:ℝ≥0∞)^2 = L*L from sq L]
    _ ≤ (X * L) / (L * L) := ENNReal.div_le_div_right hAsq _
    _ = X / L := ENNReal.mul_div_mul_right _ _ hL0 hLtop

/-- Pointwise identity turning the `L⁴` integrand of a square function into an `ℝ≥0∞` square. -/
theorem enorm_sqrt_sum_sq (n : ℕ) (g : Fin n → ℝ → ℝ) (x : ℝ) :
    ‖Real.sqrt (∑ j, g j x ^ 2)‖ₑ ^ (4:ℝ) = (∑ j, ENNReal.ofReal (g j x ^ 2)) ^ 2 := by
  have hS : 0 ≤ ∑ j, g j x ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _),
    ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num),
    show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast,
    show Real.sqrt (∑ j, g j x ^ 2) ^ (4:ℕ) = (∑ j, g j x ^ 2)^2 by
      rw [show (4:ℕ) = 2*2 from rfl, pow_mul, Real.sq_sqrt hS],
    ENNReal.ofReal_pow hS, ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]

/-- The `L⁴` estimate in integrated form: `∫ G⁴ ≤ 64 ∫ F⁴`. -/
theorem lintegral_L4_le {N : ℕ} {a b : Fin N → ℝ} (ha : ∀ j, 0 ≤ a j) (hab : ∀ j, a j < b j)
    (hb : ∀ j, b j ≤ 1) {f : Fin N → ℝ → ℝ} (hf : ∀ j, MemLp (f j) 4 volIcc) :
    ∫⁻ x, ‖Real.sqrt (∑ j, avgProj (a j) (b j) (f j) x ^ 2)‖ₑ ^ (4:ℝ) ∂volIcc ≤
      64 * ∫⁻ x, ‖Real.sqrt (∑ j, f j x ^ 2)‖ₑ ^ (4:ℝ) ∂volIcc := by
  classical
  set I : Fin N → Set ℝ := fun j => Icc (a j) (b j) with hI
  have hIsub : ∀ j, I j ⊆ Icc (0:ℝ) 1 := fun j => Icc_subset_Icc (ha j) (hb j)
  set u : Fin N → ℝ → ℝ≥0∞ :=
    fun j => (Icc (0:ℝ) 1).indicator (fun y => ENNReal.ofReal (f j y ^ 2)) with hu
  have hfm : ∀ j, AEMeasurable (f j) (volume.restrict (Icc (0:ℝ) 1)) := fun j =>
    (hf j).aestronglyMeasurable.aemeasurable
  have hum : ∀ j, AEMeasurable (u j) (volume : Measure ℝ) := by
    intro j
    rw [hu]
    refine (aemeasurable_indicator_iff measurableSet_Icc).2 ?_
    exact ENNReal.measurable_ofReal.comp_aemeasurable ((hfm j).pow_const 2)
  have havg : ∀ j, avgOn (I j) (u j) = avgOn (I j) (fun y => ENNReal.ofReal (f j y ^ 2)) := by
    intro j
    unfold avgOn
    congr 1
    refine setLIntegral_congr_fun measurableSet_Icc fun y hy => ?_
    simp [hu, Set.indicator_of_mem (hIsub j hy)]
  have hproj : ∀ j x, ENNReal.ofReal (avgProj (a j) (b j) (f j) x ^ 2) ≤
      (I j).indicator (fun _ => avgOn (I j) (u j)) x := by
    intro j x
    by_cases hx : x ∈ I j
    · rw [Set.indicator_of_mem hx, havg j, avgProj, Set.indicator_of_mem hx]
      exact proj_sq_le (a j) (b j) (hab j) (f j)
        ((hfm j).mono_measure (Measure.restrict_mono (hIsub j) le_rfl))
    · rw [Set.indicator_of_notMem hx, avgProj, Set.indicator_of_notMem hx]
      simp
  calc ∫⁻ x, ‖Real.sqrt (∑ j, avgProj (a j) (b j) (f j) x ^ 2)‖ₑ ^ (4:ℝ) ∂volIcc
      = ∫⁻ x in Icc (0:ℝ) 1, (∑ j, ENNReal.ofReal (avgProj (a j) (b j) (f j) x ^ 2)) ^ 2 := by
        rw [volIcc]
        exact lintegral_congr fun x => enorm_sqrt_sum_sq N _ x
    _ ≤ ∫⁻ x in Icc (0:ℝ) 1, (∑ j, (I j).indicator (fun _ => avgOn (I j) (u j)) x) ^ 2 :=
        lintegral_mono fun x => pow_le_pow_left' (Finset.sum_le_sum fun j _ => hproj j x) 2
    _ ≤ ∫⁻ x, (∑ j, (I j).indicator (fun _ => avgOn (I j) (u j)) x) ^ 2 :=
        setLIntegral_le_lintegral _ _
    _ ≤ 64 * ∫⁻ x, (∑ j, u j x) ^ 2 := core hab hum
    _ = 64 * ∫⁻ x, ‖Real.sqrt (∑ j, f j x ^ 2)‖ₑ ^ (4:ℝ) ∂volIcc := by
        congr 1
        rw [volIcc, ← lintegral_indicator measurableSet_Icc]
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ Icc (0:ℝ) 1
        · rw [Set.indicator_of_mem hx, enorm_sqrt_sum_sq N f x]
          congr 1
          exact Finset.sum_congr rfl fun j _ => by simp [hu, Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx]
          have hz : ∀ j, u j x = 0 := fun j => by simp [hu, Set.indicator_of_notMem hx]
          simp [hz]

/-- **Q899 at `p = 4`.**  For every finite family of nondegenerate closed subintervals
`[a j, b j]` of `[0,1]` and every family of `L⁴(0,1)` functions `f j`, the square function
estimate holds with constant `2√2`. -/
theorem sq_function_L4 {N : ℕ} {a b : Fin N → ℝ} (ha : ∀ j, 0 ≤ a j) (hab : ∀ j, a j < b j)
    (hb : ∀ j, b j ≤ 1) {f : Fin N → ℝ → ℝ} (hf : ∀ j, MemLp (f j) 4 volIcc) :
    eLpNorm (fun x => Real.sqrt (∑ j, avgProj (a j) (b j) (f j) x ^ 2)) 4 volIcc ≤
      ENNReal.ofReal (2 * Real.sqrt 2) *
        eLpNorm (fun x => Real.sqrt (∑ j, f j x ^ 2)) 4 volIcc := by
  have key := lintegral_L4_le ha hab hb hf
  have hconst : (64:ℝ≥0∞) ^ (1/4:ℝ) = ENNReal.ofReal (2 * Real.sqrt 2) := by
    have h64 : (64:ℝ) = (2 * Real.sqrt 2) ^ (4:ℕ) := by
      have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith [h]
    have h2 : (64:ℝ≥0∞) = ENNReal.ofReal 64 := by simp
    rw [h2, ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num)]
    congr 1
    rw [h64, show (1/4:ℝ) = ((4:ℕ):ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    show (4:ℝ≥0∞).toReal = 4 by norm_num]
  calc (∫⁻ x, ‖Real.sqrt (∑ j, avgProj (a j) (b j) (f j) x ^ 2)‖ₑ ^ (4:ℝ) ∂volIcc) ^ (1/4:ℝ)
      ≤ (64 * ∫⁻ x, ‖Real.sqrt (∑ j, f j x ^ 2)‖ₑ ^ (4:ℝ) ∂volIcc) ^ (1/4:ℝ) := by gcongr
    _ = (64:ℝ≥0∞) ^ (1/4:ℝ) *
          (∫⁻ x, ‖Real.sqrt (∑ j, f j x ^ 2)‖ₑ ^ (4:ℝ) ∂volIcc) ^ (1/4:ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ = _ := by rw [hconst]

/-- **Q899.**  There exist an exponent `p > 2` and a constant `C ≥ 1` such that the square
function inequality for the averaging projections onto arbitrary nondegenerate closed
subintervals of `[0,1]` holds uniformly over all finite families of intervals and of
`L^p(0,1)` functions. -/
theorem exists_exponent_gt_two :
    ∃ p : ℝ, 2 < p ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (N : ℕ), 0 < N → ∀ a b : Fin N → ℝ, (∀ j, 0 ≤ a j) → (∀ j, a j < b j) →
        (∀ j, b j ≤ 1) → ∀ f : Fin N → ℝ → ℝ, (∀ j, MemLp (f j) (ENNReal.ofReal p) volIcc) →
        eLpNorm (fun x => Real.sqrt (∑ j, avgProj (a j) (b j) (f j) x ^ 2))
            (ENNReal.ofReal p) volIcc ≤
          ENNReal.ofReal C *
            eLpNorm (fun x => Real.sqrt (∑ j, f j x ^ 2)) (ENNReal.ofReal p) volIcc := by
  refine ⟨4, by norm_num, 2 * Real.sqrt 2, ?_, ?_⟩
  · nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  · intro N _ a b ha hab hb f hf
    have h4 : ENNReal.ofReal (4:ℝ) = (4:ℝ≥0∞) := by simp
    rw [h4] at hf ⊢
    exact sq_function_L4 ha hab hb hf

/-!
## Remarks

* **Constant.**  The audited informal solution obtains the constant `2 ^ (3/4)` at `p = 4`;
  the proof formalised here uses the Vitali covering lemma (with dilation factor `4`) instead
  of the sharp one-sided rising sun lemma, and therefore yields the larger explicit constant
  `C = 2 * √2 = 64 ^ (1/4)`.  Any explicit constant `C ≥ 1` answers Q899, which asks only for
  the existence of some `p > 2` and some `C(p) ≥ 1`.

* **Formulation.**  As noted in the informal solution, the intervals are required to be
  nondegenerate (`a j < b j`), since the definition of `P_I` divides by `|I|`, and the identity
  defining `P_I f` is an identity of functions (all `L⁴` statements are, as usual, invariant
  under modification on null sets).  `volIcc` is Lebesgue measure on `[0,1]`, and by
  `setIntegral_volIcc` the averages defining `avgProj` do not depend on whether they are read
  with respect to `volIcc` or to Lebesgue measure on the line.

* **Versions.**  Lean 4.28.0; mathlib4 at commit
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (tag `v4.28.0`).
-/

end Q899
