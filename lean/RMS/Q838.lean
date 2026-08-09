/-
# Q838 — the normalized mean quantization error `k^{1/n} m_k` need not converge

## What is formalized

Q838 asks for general asymptotic results on the mean `k`-point quantization error
`m_k(X) = inf_{#Σ ≤ k} E d_Σ(X)`, `d_Σ(x) = inf_{a ∈ Σ} ‖x - a‖`, and in particular whether
`k^{1/n} m_k(X)` must converge for every integrable random vector `X` and every norm.

This file formalizes the decisive **negative** answer, i.e. assertion (2.2) of the answer:
for every dimension `n ≥ 1` and every norm on `ℝ^n` there is an *integrable* random vector
`X` with

  `liminf_k  k^{1/n} m_k = 0`   and   `limsup_k  k^{1/n} m_k = +∞`.

See `Q838.exists_integrable_law_quantization_error_oscillates` (general `n`) and
`Q838.exists_integrable_law_quantization_error_oscillates_real` (the case `n = 1`).

The construction is the one of Section 8 of the answer: atoms at `4 ^ j • u` on a ray through
a unit vector `u`, with blockwise constant weights, the block lengths being chosen here so
that every estimate is an exact power of two.  The two key estimates are `mqe_le_tailA`
(the codebook `{0, 4u, ..., 4^{k-1}u}` gives `m_k ≤ A_k = ∑_{j ≥ k} a_j`) and `le_mqe`
(disjointness of the balls `B(4^j u, 4^j/4)` gives `m_k ≥ (K - k) a_K / 4` for every `K`).

## Scope, and relation to the printed source

* The source's incidental claim that `k^{1/n} m_k → 2^{-n}` for the uniform law on `[-1,1]^n`
  is *false* for `n ≥ 2` (the correct constant is `2 q_{n,‖·‖}`); it is not formalized here.
* The positive part of the answer (the Zador asymptotics (2.1), the universal lower bound,
  and the existence and positivity of the unit-cube constant `q_{n,‖·‖}`) is not formalized;
  only the negative answer (2.2) is.

## Formalization choices (differences from the printed statement)

* Codebooks are finite nonempty sets with `#Σ ≤ k` rather than `#Σ = k`; the answer notes
  that the two infima coincide.
* "`ℝ^n` with an arbitrary norm" is formalized as an arbitrary real normed space `E` with
  `Module.finrank ℝ E = n`; every norm on `ℝ^n` arises this way.
* The random vector is presented through its law `μ` on `E`, the random variable being the
  identity on the probability space `(E, μ)`; this is legitimate since `m_k` depends only on
  the law.  Integrability of `X` is `Integrable id μ`.
* `E d_Σ(X)` is defined as a lower integral with values in `[0, ∞]`, so that `m_k` is always
  defined; `mqe_eq_iInf_ofReal_integral` shows that for the law constructed here this agrees
  with the infimum of the (finite) Bochner integrals `E d_Σ(X)`.
* `liminf` and `limsup` are taken in `ℝ≥0∞`, which is where the value `+∞` is meaningful.

Lean version: 4.28.0.  Mathlib revision: 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
-/
import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Q838

section Quantization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The mean `k`-point quantization error of a law `μ`:
`m_k = inf { E d_Σ(X) : Σ finite nonempty, #Σ ≤ k }`, where `d_Σ(x) = inf_{a ∈ Σ} ‖x - a‖`.
It is defined through a lower integral, so it is always well defined in `[0, ∞]`;
`mqe_eq_iInf_ofReal_integral` below identifies it with the infimum of the expectations. -/
noncomputable def mqe (μ : Measure E) (k : ℕ) : ℝ≥0∞ :=
  ⨅ S : {S : Finset E // S.Nonempty ∧ S.card ≤ k},
    ∫⁻ x, ENNReal.ofReal (Metric.infDist x (S.1 : Set E)) ∂μ

omit [NormedSpace ℝ E] in
lemma measurable_dist_fun (S : Finset E) :
    Measurable fun x : E => ENNReal.ofReal (Metric.infDist x (S : Set E)) :=
  (ENNReal.measurable_ofReal.comp ((Metric.lipschitz_infDist_pt _).continuous.measurable))

end Quantization

/-! ## Elementary `ℝ≥0∞` helpers -/

lemma two_pow_ne_zero' (a : ℕ) : ((2 : ℝ≥0∞) ^ a) ≠ 0 := by simp

lemma two_pow_ne_top (a : ℕ) : ((2 : ℝ≥0∞) ^ a) ≠ ⊤ := ENNReal.pow_ne_top (by simp)

lemma two_pow_mul_inv_of_le {a b : ℕ} (h : b ≤ a) :
    ((2 : ℝ≥0∞) ^ a) * ((2 : ℝ≥0∞) ^ b)⁻¹ = (2 : ℝ≥0∞) ^ (a - b) := by
  have : (2 : ℝ≥0∞) ^ a = (2 : ℝ≥0∞) ^ (a - b) * (2 : ℝ≥0∞) ^ b := by
    rw [← pow_add]
    congr 1
    omega
  rw [this, mul_assoc, ENNReal.mul_inv_cancel (two_pow_ne_zero' b) (two_pow_ne_top b), mul_one]

lemma two_pow_mul_inv_of_ge {a b : ℕ} (h : a ≤ b) :
    ((2 : ℝ≥0∞) ^ a) * ((2 : ℝ≥0∞) ^ b)⁻¹ = (((2 : ℝ≥0∞) ^ (b - a))⁻¹) := by
  have hb : (2 : ℝ≥0∞) ^ b = (2 : ℝ≥0∞) ^ a * (2 : ℝ≥0∞) ^ (b - a) := by
    rw [← pow_add]; congr 1; omega
  rw [hb, ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
    ENNReal.mul_inv_cancel (two_pow_ne_zero' a) (two_pow_ne_top a), one_mul]

/-- Taking the `n`-th root of a power of two with exponent divisible by `n`. -/
lemma two_pow_rpow_inv {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    ((2 : ℝ≥0∞) ^ (n * m)) ^ ((1 : ℝ) / n) = (2 : ℝ≥0∞) ^ m := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [← ENNReal.rpow_natCast (2 : ℝ≥0∞) (n * m), ← ENNReal.rpow_natCast (2 : ℝ≥0∞) m,
    ← ENNReal.rpow_mul]
  congr 1
  push_cast
  field_simp

lemma tsum_shift (f : ℕ → ℝ≥0∞) (k : ℕ) (h : ∀ i, i < k → f i = 0) :
    ∑' i, f i = ∑' i, f (i + k) := by
  refine (Function.Injective.tsum_eq (g := fun c => c + k)
    (fun a b hab => by simpa using hab) ?_).symm
  intro x hx
  simp only [Function.mem_support] at hx
  have hk : k ≤ x := by
    by_contra hc
    exact hx (h x (by omega))
  exact ⟨x - k, by simp; omega⟩

lemma tsum_succ (f : ℕ → ℝ≥0∞) : ∑' j, f j = f 0 + ∑' b, f (b + 1) := by
  rw [ENNReal.tsum_eq_add_tsum_ite 0]
  congr 1
  rw [tsum_shift _ 1 (by intro i hi; simp [show i = 0 by omega])]
  exact tsum_congr fun b => by simp

lemma two_mul_le_two_pow (s : ℕ) : 2 * s ≤ 2 ^ s := by
  induction s with
  | zero => simp
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; norm_num
    · have h2 : 2 ≤ 2 ^ m := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
      calc 2 * (m + 1) = 2 * m + 2 := by ring
        _ ≤ 2 ^ m + 2 ^ m := by omega
        _ = 2 ^ (m + 1) := by ring

/-! ## The construction

`n` is the dimension, `u` a unit vector of the space.  The atoms are placed at `4 ^ j • u`
(`j ≥ 1`), the remaining mass sits at the origin. -/

/-- Block endpoints `N s = 2 ^ (n (2 ^ s + s))`. -/
def Nn (n s : ℕ) : ℕ := 2 ^ (n * (2 ^ s + s))

/-- Half-blocks `Nh s = 2 ^ (n (2 ^ s + s - 1))`, the points of the second subsequence. -/
def Nh (n s : ℕ) : ℕ := 2 ^ (n * (2 ^ s + s - 1))

/-- `C s = 2 ^ (-2 ^ s)`, the total mass of block `s`. -/
noncomputable def Cc (s : ℕ) : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ (2 ^ s))⁻¹

/-- Step heights `W s = C s / N s`. -/
noncomputable def Ww (n s : ℕ) : ℝ≥0∞ := Cc s * ((2 : ℝ≥0∞) ^ (n * (2 ^ s + s)))⁻¹

/-- The nonincreasing weight sequence `a_j = ∑_{s : j < N s} W s`. -/
noncomputable def aa (n j : ℕ) : ℝ≥0∞ := ∑' s : ℕ, if j < Nn n s then Ww n s else 0

/-- Tail sums `A_k = ∑_{j ≥ k} a_j`. -/
noncomputable def tailA (n k : ℕ) : ℝ≥0∞ := ∑' j : ℕ, if k ≤ j then aa n j else 0

/-- Total mass carried by the atoms, `∑_{j ≥ 1} a_j / 4 ^ j`. -/
noncomputable def Tot (n : ℕ) : ℝ≥0∞ := ∑' b : ℕ, aa n (b + 1) / 4 ^ (b + 1)

/-- Atom masses. -/
noncomputable def mass (n j : ℕ) : ℝ≥0∞ := if j = 0 then 1 - Tot n else aa n j / 4 ^ j

section Construction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Atom positions: `pt 0 = 0` and `pt j = 4 ^ j • u`. -/
noncomputable def pt (u : E) (j : ℕ) : E := if j = 0 then 0 else ((4 : ℝ) ^ j) • u

/-- The law of the counterexample random vector. -/
noncomputable def lawX (n : ℕ) (u : E) : Measure E :=
  Measure.sum fun j => mass n j • Measure.dirac (pt u j)

/-! ## Basic properties of the construction -/

lemma Nn_pos (n s : ℕ) : 0 < Nn n s := Nat.two_pow_pos _

lemma Nn_monotone (n : ℕ) : Monotone (Nn n) := by
  intro a b hab
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab
  exact Nat.mul_le_mul_left _ (by omega)

lemma Nn_strictMono {n : ℕ} (hn : 1 ≤ n) : StrictMono (Nn n) := by
  intro a b hab
  refine Nat.pow_lt_pow_right (by norm_num) ?_
  have h1 : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
  exact (Nat.mul_lt_mul_left (by omega)).2 (by omega)

lemma Nh_strictMono {n : ℕ} (hn : 1 ≤ n) : StrictMono (Nh n) := by
  intro a b hab
  refine Nat.pow_lt_pow_right (by norm_num) ?_
  have h1 : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
  have h2 : 1 ≤ (2 : ℕ) ^ a := Nat.one_le_two_pow
  exact (Nat.mul_lt_mul_left (by omega)).2 (by omega)

lemma Ww_mul_Nn (n s : ℕ) : Ww n s * (Nn n s : ℝ≥0∞) = Cc s := by
  have h : ((Nn n s : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (n * (2 ^ s + s)) := by simp [Nn]
  rw [Ww, h, mul_assoc, ENNReal.inv_mul_cancel (two_pow_ne_zero' _) (two_pow_ne_top _), mul_one]

lemma aa_antitone (n : ℕ) : Antitone (aa n) := by
  intro i j hij
  refine ENNReal.tsum_le_tsum ?_
  intro s
  by_cases h : j < Nn n s
  · simp [h, lt_of_le_of_lt hij h]
  · simp [h]

lemma Ww_le_aa {n j s : ℕ} (h : j < Nn n s) : Ww n s ≤ aa n j := by
  have := ENNReal.le_tsum (f := fun s => if j < Nn n s then Ww n s else 0) s
  simpa [h] using this

/-- The tail sums, computed blockwise. -/
lemma tailA_eq (n k : ℕ) : tailA n k = ∑' s : ℕ, Ww n s * ((Nn n s - k : ℕ) : ℝ≥0∞) := by
  have h1 : tailA n k = ∑' j : ℕ, ∑' s : ℕ, (if k ≤ j ∧ j < Nn n s then Ww n s else 0) := by
    unfold tailA aa
    refine tsum_congr fun j => ?_
    by_cases hj : k ≤ j
    · simp only [hj, if_true, true_and]
    · simp [hj]
  rw [h1, ENNReal.tsum_comm]
  refine tsum_congr fun s => ?_
  have hsupp : ∀ j ∉ Finset.Ico k (Nn n s), (if k ≤ j ∧ j < Nn n s then Ww n s else 0) = 0 := by
    intro j hj
    simp only [Finset.mem_Ico, not_and, not_lt] at hj
    by_cases h1 : k ≤ j
    · simp [h1, not_lt.2 (hj h1)]
    · simp [h1]
  rw [tsum_eq_sum hsupp]
  have : ∀ j ∈ Finset.Ico k (Nn n s), (if k ≤ j ∧ j < Nn n s then Ww n s else 0) = Ww n s := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    simp [hj.1, hj.2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  ring

lemma Cc_tail_le (s : ℕ) : ∑' t : ℕ, Cc (t + s) ≤ 2 * Cc s := by
  have hb : ∀ t : ℕ, Cc (t + s) ≤ Cc s * ((2 : ℝ≥0∞) ^ t)⁻¹ := by
    intro t
    have hexp : 2 ^ s + t ≤ 2 ^ (t + s) := by
      have h1 : (2 : ℕ) ^ (t + s) = 2 ^ s * 2 ^ t := by rw [pow_add]; ring
      have h2 : t + 1 ≤ 2 ^ t := Nat.succ_le_of_lt Nat.lt_two_pow_self
      have h3 : 1 ≤ (2 : ℕ) ^ s := Nat.one_le_two_pow
      calc 2 ^ s + t ≤ 2 ^ s * (t + 1) := by nlinarith
        _ ≤ 2 ^ s * 2 ^ t := Nat.mul_le_mul_left _ h2
        _ = 2 ^ (t + s) := h1.symm
    unfold Cc
    rw [← ENNReal.mul_inv (by simp) (by simp), ← pow_add]
    exact ENNReal.inv_le_inv.2 (pow_le_pow_right₀ (by norm_num) hexp)
  calc ∑' t : ℕ, Cc (t + s) ≤ ∑' t : ℕ, Cc s * ((2 : ℝ≥0∞) ^ t)⁻¹ := ENNReal.tsum_le_tsum hb
    _ = Cc s * ∑' t : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ t := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun t => by rw [ENNReal.inv_pow]
    _ = 2 * Cc s := by
        rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv, mul_comm]

lemma tailA_zero_le_one (n : ℕ) : tailA n 0 ≤ 1 := by
  rw [tailA_eq]
  have h1 : ∀ s, Ww n s * ((Nn n s - 0 : ℕ) : ℝ≥0∞) = Cc s := by
    intro s; simpa using Ww_mul_Nn n s
  rw [tsum_congr h1]
  have h2 := Cc_tail_le 0
  simp only [Nat.add_zero] at h2
  refine h2.trans ?_
  unfold Cc
  norm_num

lemma tailA_antitone (n : ℕ) : Antitone (tailA n) := by
  intro i j hij
  refine ENNReal.tsum_le_tsum fun m => ?_
  by_cases h : j ≤ m
  · simp [h, le_trans hij h]
  · simp [h]

lemma tailA_one_eq (n : ℕ) : tailA n 1 = ∑' b : ℕ, aa n (b + 1) := by
  unfold tailA
  rw [tsum_shift _ 1 (by intro i hi; simp [show i = 0 by omega])]
  exact tsum_congr fun b => by simp

lemma Tot_le_one (n : ℕ) : Tot n ≤ 1 := by
  refine le_trans ?_ (le_trans (tailA_antitone n (Nat.zero_le 1)) (tailA_zero_le_one n))
  rw [tailA_one_eq]
  refine ENNReal.tsum_le_tsum fun b => ?_
  refine ENNReal.div_le_of_le_mul ?_
  calc aa n (b + 1) = aa n (b + 1) * 1 := by ring
    _ ≤ aa n (b + 1) * 4 ^ (b + 1) := by
        gcongr
        exact one_le_pow₀ (by norm_num)

/-! ## The measure is a probability measure and `X` is integrable -/

lemma tsum_mass (n : ℕ) : ∑' j, mass n j = 1 := by
  rw [tsum_succ (mass n)]
  have h0 : mass n 0 = 1 - Tot n := by simp [mass]
  have h1 : ∑' b : ℕ, mass n (b + 1) = Tot n := by
    unfold Tot
    exact tsum_congr fun b => by simp [mass]
  rw [h0, h1, tsub_add_cancel_of_le (Tot_le_one n)]

instance (n : ℕ) (u : E) : IsProbabilityMeasure (lawX n u) := by
  constructor
  unfold lawX
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simpa using tsum_mass n

omit [BorelSpace E] in
lemma lintegral_lawX (n : ℕ) (u : E) {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(lawX n u) = ∑' j, mass n j * f (pt u j) := by
  unfold lawX
  rw [lintegral_sum_measure]
  refine tsum_congr fun j => ?_
  rw [lintegral_smul_measure, lintegral_dirac' _ hf]
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma norm_pt {u : E} (hu : ‖u‖ = 1) (b : ℕ) : ‖pt u (b + 1)‖ = (4 : ℝ) ^ (b + 1) := by
  rw [pt, if_neg (by omega), norm_smul, hu, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

lemma lintegral_norm_lawX (n : ℕ) {u : E} (hu : ‖u‖ = 1) :
    ∫⁻ x, ENNReal.ofReal ‖x‖ ∂(lawX n u) = tailA n 1 := by
  rw [lintegral_lawX n u (f := fun x : E => ENNReal.ofReal ‖x‖) (by fun_prop), tailA_one_eq,
    tsum_succ]
  have h0 : mass n 0 * ENNReal.ofReal ‖pt u 0‖ = 0 := by simp [pt]
  rw [h0, zero_add]
  refine tsum_congr fun b => ?_
  have hof : ENNReal.ofReal ((4 : ℝ) ^ (b + 1)) = (4 : ℝ≥0∞) ^ (b + 1) := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [norm_pt hu, hof, show mass n (b + 1) = aa n (b + 1) / 4 ^ (b + 1) by simp [mass],
    ENNReal.div_mul_cancel (by simp) (by simp)]

lemma tailA_one_lt_top (n : ℕ) : tailA n 1 < ⊤ :=
  lt_of_le_of_lt (le_trans (tailA_antitone n (Nat.zero_le 1)) (tailA_zero_le_one n)) (by simp)

lemma integrable_lawX [FiniteDimensional ℝ E] (n : ℕ) {u : E} (hu : ‖u‖ = 1) :
    Integrable (fun x : E => x) (lawX n u) := by
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have h : ∫⁻ x, ‖x‖ₑ ∂(lawX n u) = ∫⁻ x, ENNReal.ofReal ‖x‖ ∂(lawX n u) := by
    refine lintegral_congr fun x => ?_
    simp
  rw [h, lintegral_norm_lawX n hu]
  exact tailA_one_lt_top n

/-- For every finite codebook the map `x ↦ d_Σ(x)` is integrable, being dominated by
`d_Σ(0) + ‖x‖`. -/
lemma integrable_infDist [FiniteDimensional ℝ E] (n : ℕ) {u : E} (hu : ‖u‖ = 1) (S : Finset E) :
    Integrable (fun x : E => Metric.infDist x (S : Set E)) (lawX n u) := by
  have hmeas : AEStronglyMeasurable (fun x : E => Metric.infDist x (S : Set E)) (lawX n u) :=
    ((Metric.lipschitz_infDist_pt (S : Set E)).continuous.measurable).aestronglyMeasurable
  refine Integrable.mono' (g := fun x : E => Metric.infDist 0 (S : Set E) + ‖x‖)
    ((integrable_const _).add (integrable_lawX n hu).norm) hmeas ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg Metric.infDist_nonneg]
  have h := Metric.infDist_le_infDist_add_dist (x := x) (y := 0) (s := (S : Set E))
  simpa [dist_eq_norm] using h

/-- `mqe` is indeed the infimum of the expectations `E d_Σ(X)`: the lower-integral definition
agrees with the usual one, all the relevant Bochner integrals being defined. -/
lemma mqe_eq_iInf_ofReal_integral [FiniteDimensional ℝ E] (n k : ℕ) {u : E} (hu : ‖u‖ = 1) :
    mqe (lawX n u) k = ⨅ S : {S : Finset E // S.Nonempty ∧ S.card ≤ k},
      ENNReal.ofReal (∫ x, Metric.infDist x (S.1 : Set E) ∂(lawX n u)) := by
  refine iInf_congr fun S => ?_
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrable_infDist n hu S.1)
    (Filter.Eventually.of_forall fun x => Metric.infDist_nonneg)).symm

/-! ## Upper bound: `m_k ≤ A_k` -/

lemma mqe_le_tailA (n : ℕ) {u : E} (hu : ‖u‖ = 1) {k : ℕ} (hk : 1 ≤ k) :
    mqe (lawX n u) k ≤ tailA n k := by
  classical
  set S : Finset E := (Finset.range k).image (pt u) with hS
  have hzero : pt u 0 ∈ S := Finset.mem_image.2 ⟨0, Finset.mem_range.2 (by omega), rfl⟩
  have hne : S.Nonempty := ⟨pt u 0, hzero⟩
  have hcard : S.card ≤ k := le_trans Finset.card_image_le (by simp)
  refine le_trans (iInf_le _ (⟨S, hne, hcard⟩ :
    {S : Finset E // S.Nonempty ∧ S.card ≤ k})) ?_
  rw [lintegral_lawX n u (measurable_dist_fun S)]
  unfold tailA
  refine ENNReal.tsum_le_tsum fun j => ?_
  by_cases hj : k ≤ j
  · have hj1 : j ≠ 0 := by omega
    have hmass : mass n j = aa n j / 4 ^ j := by simp [mass, hj1]
    have hdist : Metric.infDist (pt u j) (S : Set E) ≤ (4 : ℝ) ^ j := by
      have h := Metric.infDist_le_dist_of_mem (x := pt u j) (Finset.mem_coe.2 hzero)
      have hp0 : pt u 0 = 0 := by simp [pt]
      obtain ⟨b, rfl⟩ : ∃ b, j = b + 1 := ⟨j - 1, by omega⟩
      simpa [hp0, dist_eq_norm, norm_pt hu b] using h
    have hof : ENNReal.ofReal (Metric.infDist (pt u j) (S : Set E)) ≤ (4 : ℝ≥0∞) ^ j := by
      refine le_trans (ENNReal.ofReal_le_ofReal hdist) ?_
      rw [ENNReal.ofReal_pow (by norm_num)]
      norm_num
    calc mass n j * ENNReal.ofReal (Metric.infDist (pt u j) (S : Set E))
        ≤ (aa n j / 4 ^ j) * (4 : ℝ≥0∞) ^ j := by rw [hmass]; gcongr
      _ = aa n j := ENNReal.div_mul_cancel (by simp) (by simp)
      _ = if k ≤ j then aa n j else 0 := by simp [hj]
  · have hjk : j < k := by omega
    have h : Metric.infDist (pt u j) (S : Set E) = 0 :=
      Metric.infDist_zero_of_mem (Finset.mem_coe.2
        (Finset.mem_image.2 ⟨j, Finset.mem_range.2 hjk, rfl⟩))
    simp [h, hj]

/-! ## Lower bound -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- The closed balls `B_j = B(4^j • u, 4^j / 4)` are pairwise disjoint. -/
lemma sep_aux {u : E} (hu : ‖u‖ = 1) {i j : ℕ} (hij : i < j) (z : E)
    (hi : dist (((4 : ℝ) ^ i) • u) z < 4 ^ i / 4)
    (hj : dist (((4 : ℝ) ^ j) • u) z < 4 ^ j / 4) : False := by
  have hd : dist (((4 : ℝ) ^ i) • u) (((4 : ℝ) ^ j) • u) = (4 : ℝ) ^ j - 4 ^ i := by
    rw [dist_eq_norm, ← sub_smul, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg]
    have : (4 : ℝ) ^ i ≤ 4 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have htri : dist (((4 : ℝ) ^ i) • u) (((4 : ℝ) ^ j) • u)
      ≤ dist (((4 : ℝ) ^ i) • u) z + dist z (((4 : ℝ) ^ j) • u) := dist_triangle _ _ _
  rw [dist_comm z] at htri
  have hpow : (4 : ℝ) ^ (i + 1) ≤ 4 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
  have h4 : (4 : ℝ) ^ (i + 1) = 4 * 4 ^ i := by ring
  have hipos : (0 : ℝ) < 4 ^ i := by positivity
  rw [hd] at htri
  nlinarith

lemma le_mqe (n : ℕ) {u : E} (hu : ‖u‖ = 1) (k K : ℕ) :
    ((K - k : ℕ) : ℝ≥0∞) * aa n K / 4 ≤ mqe (lawX n u) k := by
  classical
  refine le_iInf fun T => ?_
  obtain ⟨S, hne, hcard⟩ := T
  simp only
  rw [lintegral_lawX n u (measurable_dist_fun S)]
  set P : ℕ → Prop := fun j => ((4 : ℝ) ^ j / 4 ≤ Metric.infDist (pt u j) (S : Set E)) with hP
  set G : Finset ℕ := (Finset.Icc 1 K).filter P with hG
  set bad : Finset ℕ := (Finset.Icc 1 K).filter (fun j => ¬ P j) with hbad
  -- the bad indices inject into `S`
  have hbadcard : bad.card ≤ k := by
    refine le_trans ?_ hcard
    set F : ℕ → E := fun j =>
      if h : ∃ z, z ∈ S ∧ dist (pt u j) z < (4 : ℝ) ^ j / 4 then h.choose else 0 with hF
    have hex : ∀ j ∈ bad, ∃ z, z ∈ S ∧ dist (pt u j) z < (4 : ℝ) ^ j / 4 := by
      intro j hj
      rw [hbad, Finset.mem_filter] at hj
      have hlt : Metric.infDist (pt u j) (S : Set E) < (4 : ℝ) ^ j / 4 := by
        simpa [hP] using not_le.1 hj.2
      obtain ⟨z, hzS, hz⟩ := (Metric.infDist_lt_iff (by exact_mod_cast hne.to_set)).1 hlt
      exact ⟨z, hzS, hz⟩
    refine Finset.card_le_card_of_injOn F ?_ ?_
    · intro j hj
      have h := hex j hj
      simp only [hF, dif_pos h]
      exact h.choose_spec.1
    · intro i hi j hj hij
      by_contra hne'
      have hi1 : 1 ≤ i := by
        have h := hi; rw [hbad, Finset.coe_filter, Set.mem_setOf_eq] at h
        exact (Finset.mem_Icc.1 h.1).1
      have hj1 : 1 ≤ j := by
        have h := hj; rw [hbad, Finset.coe_filter, Set.mem_setOf_eq] at h
        exact (Finset.mem_Icc.1 h.1).1
      have hexi := hex i (by simpa using hi)
      have hexj := hex j (by simpa using hj)
      have hspi : dist (pt u i) (F i) < (4 : ℝ) ^ i / 4 := by
        simp only [hF, dif_pos hexi]; exact hexi.choose_spec.2
      have hspj : dist (pt u j) (F j) < (4 : ℝ) ^ j / 4 := by
        simp only [hF, dif_pos hexj]; exact hexj.choose_spec.2
      rw [show pt u i = ((4 : ℝ) ^ i) • u by simp [pt]; omega] at hspi
      rw [show pt u j = ((4 : ℝ) ^ j) • u by simp [pt]; omega] at hspj
      rw [hij] at hspi
      rcases lt_trichotomy i j with h | h | h
      · exact sep_aux hu h (F j) hspi hspj
      · exact hne' h
      · exact sep_aux hu h (F j) hspj hspi
  have hGcard : K - k ≤ G.card := by
    have hsum : G.card + bad.card = K := by
      rw [hG, hbad, Finset.card_filter_add_card_filter_not]
      simp
    omega
  -- each good index contributes at least `a_K / 4`
  have hterm : ∀ j ∈ G,
      aa n K / 4 ≤ mass n j * ENNReal.ofReal (Metric.infDist (pt u j) (S : Set E)) := by
    intro j hjG
    rw [hG, Finset.mem_filter, Finset.mem_Icc] at hjG
    obtain ⟨⟨hj1, hjK⟩, hjP⟩ := hjG
    have hj0 : j ≠ 0 := by omega
    have hmass : mass n j = aa n j / 4 ^ j := by simp [mass, hj0]
    have hof : ((4 : ℝ≥0∞) ^ j / 4) ≤ ENNReal.ofReal (Metric.infDist (pt u j) (S : Set E)) := by
      refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hjP)
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_pow (by norm_num)]
      norm_num
    have hcalc : (aa n j / 4 ^ j) * ((4 : ℝ≥0∞) ^ j / 4) = aa n j / 4 := by
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      rw [show ((4 : ℝ≥0∞) ^ j)⁻¹ * aa n j * (4⁻¹ * 4 ^ j)
            = (((4 : ℝ≥0∞) ^ j)⁻¹ * 4 ^ j) * (4⁻¹ * aa n j) by ring,
        ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
    calc aa n K / 4 ≤ aa n j / 4 := by gcongr; exact aa_antitone n hjK
      _ = (aa n j / 4 ^ j) * ((4 : ℝ≥0∞) ^ j / 4) := hcalc.symm
      _ ≤ mass n j * ENNReal.ofReal (Metric.infDist (pt u j) (S : Set E)) := by
          rw [hmass]; gcongr
  calc ((K - k : ℕ) : ℝ≥0∞) * aa n K / 4 = ((K - k : ℕ) : ℝ≥0∞) * (aa n K / 4) := mul_div_assoc _ _ _
    _ ≤ (G.card : ℝ≥0∞) * (aa n K / 4) := by gcongr
    _ = ∑ _j ∈ G, aa n K / 4 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ G, mass n j * ENNReal.ofReal (Metric.infDist (pt u j) (S : Set E)) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑' j, mass n j * ENNReal.ofReal (Metric.infDist (pt u j) (S : Set E)) :=
        ENNReal.sum_le_tsum G

/-! ## The two subsequences -/

/-- Tail estimate at the block endpoints. -/
lemma tailA_Nn_le (n s : ℕ) : tailA n (Nn n s) ≤ 2 * Cc (s + 1) := by
  rw [tailA_eq, tsum_shift _ (s + 1) ?_]
  · refine le_trans (ENNReal.tsum_le_tsum ?_) (Cc_tail_le (s + 1))
    intro i
    calc Ww n (i + (s + 1)) * ((Nn n (i + (s + 1)) - Nn n s : ℕ) : ℝ≥0∞)
        ≤ Ww n (i + (s + 1)) * ((Nn n (i + (s + 1)) : ℕ) : ℝ≥0∞) := by
          gcongr
          exact_mod_cast Nat.sub_le _ _
      _ = Cc (i + (s + 1)) := Ww_mul_Nn _ _
  · intro i hi
    have h : Nn n i ≤ Nn n s := Nn_monotone n (by omega)
    simp [Nat.sub_eq_zero_of_le h]

lemma Nn_mul_tailA_le (n s : ℕ) :
    (2 : ℝ≥0∞) ^ (2 ^ s + s) * tailA n (Nn n s) ≤ 2 * ((2 : ℝ≥0∞) ^ s)⁻¹ := by
  have hkey : 2 ^ s + s + s ≤ 2 ^ (s + 1) := by
    have h1 := two_mul_le_two_pow s
    have h2 : (2 : ℕ) ^ (s + 1) = 2 ^ s + 2 ^ s := by ring
    omega
  calc (2 : ℝ≥0∞) ^ (2 ^ s + s) * tailA n (Nn n s)
      ≤ (2 : ℝ≥0∞) ^ (2 ^ s + s) * (2 * Cc (s + 1)) := by
        gcongr
        exact tailA_Nn_le n s
    _ = 2 * ((2 : ℝ≥0∞) ^ (2 ^ s + s) * ((2 : ℝ≥0∞) ^ (2 ^ (s + 1)))⁻¹) := by
        rw [Cc]; ring
    _ = 2 * ((2 : ℝ≥0∞) ^ (2 ^ (s + 1) - (2 ^ s + s)))⁻¹ := by
        rw [two_pow_mul_inv_of_ge (by omega)]
    _ ≤ 2 * ((2 : ℝ≥0∞) ^ s)⁻¹ := by
        gcongr
        · exact one_le_two
        · omega

lemma tendsto_liminf_subseq (n : ℕ) (hn : 1 ≤ n) {u : E} (hu : ‖u‖ = 1) :
    Tendsto (fun s => ((Nn n s : ℕ) : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe (lawX n u) (Nn n s))
      atTop (𝓝 0) := by
  have hb : Tendsto (fun s : ℕ => 2 * ((2 : ℝ≥0∞) ^ s)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℕ => ((2 : ℝ≥0∞)⁻¹) ^ s) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by simp [ENNReal.inv_lt_one])
    have h2 : Tendsto (fun s : ℕ => (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ s) atTop
        (𝓝 ((2 : ℝ≥0∞) * 0)) := ENNReal.Tendsto.const_mul h1 (Or.inr (by norm_num))
    simpa [ENNReal.inv_pow] using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun s => zero_le _) (fun s => ?_)
  have hroot : ((Nn n s : ℕ) : ℝ≥0∞) ^ ((1 : ℝ) / n) = (2 : ℝ≥0∞) ^ (2 ^ s + s) := by
    have hc : ((Nn n s : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (n * (2 ^ s + s)) := by simp [Nn]
    rw [hc, two_pow_rpow_inv hn]
  rw [hroot]
  calc (2 : ℝ≥0∞) ^ (2 ^ s + s) * mqe (lawX n u) (Nn n s)
      ≤ (2 : ℝ≥0∞) ^ (2 ^ s + s) * tailA n (Nn n s) := by
        gcongr
        exact mqe_le_tailA n hu (by have := Nn_pos n s; omega)
    _ ≤ 2 * ((2 : ℝ≥0∞) ^ s)⁻¹ := Nn_mul_tailA_le n s

lemma le_Nh_mul_mqe (n : ℕ) (hn : 1 ≤ n) {u : E} (hu : ‖u‖ = 1) {s : ℕ} (hs : 5 ≤ s) :
    (2 : ℝ≥0∞) ^ (s - 5) ≤ (2 : ℝ≥0∞) ^ (2 ^ s + s - 1) * mqe (lawX n u) (Nh n s) := by
  have hqs : s ≤ 2 ^ s := Nat.le_of_lt Nat.lt_two_pow_self
  have hq1 : 1 ≤ (2 : ℕ) ^ s := Nat.one_le_two_pow
  set e := 2 ^ s + s with he
  have he7 : 7 ≤ e := by omega
  -- `M = n e` and `Mh = n (e-1) = M - n`
  obtain ⟨M, hM⟩ : ∃ M, n * e = M := ⟨_, rfl⟩
  have hMh : n * (e - 1) = M - n := by
    rw [Nat.mul_sub, hM, mul_one]
  have hMn : n ≤ M := by
    rw [← hM]
    calc n = n * 1 := by ring
      _ ≤ n * e := Nat.mul_le_mul_left _ (by omega)
  have hM7 : 7 ≤ M := by
    rw [← hM]
    calc 7 ≤ e := he7
      _ = 1 * e := by ring
      _ ≤ n * e := Nat.mul_le_mul_right _ hn
  have hNn : Nn n s = 2 ^ M := by rw [Nn, ← he, hM]
  have hNh : Nh n s = 2 ^ (M - n) := by rw [Nh, ← he, hMh]
  set K := Nn n s - 1 with hK
  have hKlt : K < Nn n s := by
    have := Nn_pos n s; omega
  have haaK : Ww n s ≤ aa n K := Ww_le_aa hKlt
  -- `K - Nh s ≥ 2 ^ (M - 2)`
  have hA : (2 : ℕ) ^ M = 4 * 2 ^ (M - 2) := by
    have h : (2 : ℕ) ^ M = 2 ^ (2 + (M - 2)) := by congr 1; omega
    rw [h, pow_add]; norm_num
  have hA' : (2 : ℕ) ^ (M - n) ≤ 2 * 2 ^ (M - 2) := by
    have h : (2 : ℕ) * 2 ^ (M - 2) = 2 ^ (1 + (M - 2)) := by rw [pow_add]; ring
    rw [h]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA1 : 1 ≤ (2 : ℕ) ^ (M - 2) := Nat.one_le_two_pow
  have hsub : (2 : ℕ) ^ (M - 2) ≤ K - Nh n s := by
    rw [hK, hNn, hNh]; omega
  -- the arithmetic identity
  have hWw : Ww n s = ((2 : ℝ≥0∞) ^ (2 ^ s + M))⁻¹ := by
    rw [Ww, Cc, ← he, hM, ← ENNReal.mul_inv (by simp) (by simp), ← pow_add]
  have hinv : ((2 : ℝ≥0∞) ^ (2 ^ s + M))⁻¹ * ((2 : ℝ≥0∞) ^ 2)⁻¹
      = ((2 : ℝ≥0∞) ^ (2 ^ s + M + 2))⁻¹ := by
    rw [← ENNReal.mul_inv (Or.inl (two_pow_ne_zero' _)) (Or.inl (two_pow_ne_top _)), ← pow_add]
  have key : (2 : ℝ≥0∞) ^ (e - 1) * ((2 : ℝ≥0∞) ^ (M - 2) * Ww n s / 4)
      = (2 : ℝ≥0∞) ^ (s - 5) := by
    have h4 : (4 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 2 := by norm_num
    rw [hWw, h4, div_eq_mul_inv,
      show (2 : ℝ≥0∞) ^ (e - 1) * ((2 : ℝ≥0∞) ^ (M - 2) * ((2 : ℝ≥0∞) ^ (2 ^ s + M))⁻¹
            * ((2 : ℝ≥0∞) ^ 2)⁻¹)
          = ((2 : ℝ≥0∞) ^ (e - 1) * (2 : ℝ≥0∞) ^ (M - 2))
            * (((2 : ℝ≥0∞) ^ (2 ^ s + M))⁻¹ * ((2 : ℝ≥0∞) ^ 2)⁻¹) by ring,
      hinv, ← pow_add, two_pow_mul_inv_of_le (by omega)]
    congr 1
    omega
  calc (2 : ℝ≥0∞) ^ (s - 5)
      = (2 : ℝ≥0∞) ^ (e - 1) * ((2 : ℝ≥0∞) ^ (M - 2) * Ww n s / 4) := key.symm
    _ ≤ (2 : ℝ≥0∞) ^ (e - 1) * (((K - Nh n s : ℕ) : ℝ≥0∞) * aa n K / 4) := by
        have h1 : ((2 : ℝ≥0∞) ^ (M - 2)) ≤ ((K - Nh n s : ℕ) : ℝ≥0∞) := by exact_mod_cast hsub
        exact mul_le_mul_of_nonneg_left (ENNReal.div_le_div_right (mul_le_mul' h1 haaK) 4)
          (zero_le _)
    _ ≤ (2 : ℝ≥0∞) ^ (e - 1) * mqe (lawX n u) (Nh n s) := by
        gcongr
        exact le_mqe n hu _ _

lemma tendsto_limsup_subseq (n : ℕ) (hn : 1 ≤ n) {u : E} (hu : ‖u‖ = 1) :
    Tendsto (fun s => ((Nh n s : ℕ) : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe (lawX n u) (Nh n s))
      atTop (𝓝 ⊤) := by
  refine ENNReal.tendsto_nhds_top fun m => ?_
  filter_upwards [eventually_ge_atTop (m + 5)] with s hs
  have hroot : ((Nh n s : ℕ) : ℝ≥0∞) ^ ((1 : ℝ) / n) = (2 : ℝ≥0∞) ^ (2 ^ s + s - 1) := by
    have hc : ((Nh n s : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (n * (2 ^ s + s - 1)) := by simp [Nh]
    rw [hc, two_pow_rpow_inv hn]
  rw [hroot]
  refine lt_of_lt_of_le ?_ (le_Nh_mul_mqe n hn hu (by omega))
  have hm : (m : ℝ≥0∞) < (2 : ℝ≥0∞) ^ m := by
    have h : (m : ℕ) < 2 ^ m := Nat.lt_two_pow_self
    calc (m : ℝ≥0∞) < ((2 ^ m : ℕ) : ℝ≥0∞) := by exact_mod_cast h
      _ = (2 : ℝ≥0∞) ^ m := by simp
  exact lt_of_lt_of_le hm (pow_le_pow_right₀ one_le_two (by omega))

/-! ## Main theorem -/

/-- **Q838, negative answer.**  For every dimension `n ≥ 1` and every norm on `ℝ^n`
(formalized as an arbitrary real normed space `E` of finite dimension `n`) there is an
integrable random vector — presented by its law `μ`, the random vector being the identity on
the probability space `(E, μ)` — whose mean `k`-point quantization errors `m_k` satisfy

`liminf_k k^{1/n} m_k = 0`  and  `limsup_k k^{1/n} m_k = +∞`.

In particular `k^{1/n} m_k` need not converge (even in `[0, ∞]`) for an integrable law. -/
theorem exists_integrable_law_quantization_error_oscillates
    {n : ℕ} (hn : 1 ≤ n) (hdim : Module.finrank ℝ E = n) :
    ∃ μ : Measure E, IsProbabilityMeasure μ ∧ Integrable (fun x : E => x) μ ∧
      liminf (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe μ k) atTop = 0 ∧
      limsup (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe μ k) atTop = ⊤ := by
  classical
  -- `E` is finite-dimensional and nonzero, so it carries a unit vector
  haveI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (R := ℝ) (by omega)
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  set u : E := ‖x‖⁻¹ • x with hudef
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
  refine ⟨lawX n u, inferInstance, integrable_lawX n hu, ?_, ?_⟩
  · have hmap : Filter.map (Nn n) atTop ≤ (atTop : Filter ℕ) := (Nn_strictMono hn).tendsto_atTop
    have hT : Tendsto (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe (lawX n u) k)
        (Filter.map (Nn n) atTop) (𝓝 0) := tendsto_map'_iff.2 (tendsto_liminf_subseq n hn hu)
    refine le_antisymm ?_ (zero_le _)
    calc liminf (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe (lawX n u) k) atTop
        ≤ liminf (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe (lawX n u) k)
            (Filter.map (Nn n) atTop) := liminf_le_liminf_of_le hmap
      _ = 0 := hT.liminf_eq
  · have hmap : Filter.map (Nh n) atTop ≤ (atTop : Filter ℕ) := (Nh_strictMono hn).tendsto_atTop
    have hT : Tendsto (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe (lawX n u) k)
        (Filter.map (Nh n) atTop) (𝓝 ⊤) := tendsto_map'_iff.2 (tendsto_limsup_subseq n hn hu)
    refine le_antisymm le_top ?_
    calc (⊤ : ℝ≥0∞)
        = limsup (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe (lawX n u) k)
            (Filter.map (Nh n) atTop) := hT.limsup_eq.symm
      _ ≤ limsup (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe (lawX n u) k) atTop :=
          limsup_le_limsup_of_le hmap

end Construction

/-- The dimension-one instance of the previous theorem: there is an integrable real random
variable whose mean `k`-point quantization errors satisfy `liminf k m_k = 0` and
`limsup k m_k = +∞`. -/
theorem exists_integrable_law_quantization_error_oscillates_real :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ Integrable (fun x : ℝ => x) μ ∧
      liminf (fun k : ℕ => (k : ℝ≥0∞) * mqe μ k) atTop = 0 ∧
      limsup (fun k : ℕ => (k : ℝ≥0∞) * mqe μ k) atTop = ⊤ := by
  obtain ⟨μ, hμ, hint, h0, htop⟩ :=
    exists_integrable_law_quantization_error_oscillates (E := ℝ) (n := 1) le_rfl
      (by simp)
  refine ⟨μ, hμ, hint, ?_, ?_⟩
  · simpa using h0
  · simpa using htop

end Q838
