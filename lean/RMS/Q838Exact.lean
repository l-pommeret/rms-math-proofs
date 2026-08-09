/-
# Q838 — the exact-cardinality form of the mean quantization error

The printed question defines

  `m_k = inf { E d_Σ(X) : Σ finite, #Σ = k }`,

with codebooks of *exactly* `k` points, whereas `Q838.mqe` (in `RequestProject.Q838`) takes the
infimum over nonempty codebooks with `#Σ ≤ k`.  This file introduces the exact-cardinality
functional `Q838.mqeExact`, proves the bridge `mqeExact μ k = mqe μ k` for `k ≥ 1` in every
infinite ambient space, and transfers the negative answer of
`Q838.exists_integrable_law_quantization_error_oscillates` to the printed definition.

Main results:

* `Q838.mqeExact_eq_mqe` — the two definitions agree for `1 ≤ k` (ambient space infinite);
* `Q838.mqeExact_eq_iInf_ofReal_integral` — `mqeExact` is the infimum of the ordinary
  expectations `E d_Σ(X)` for the constructed law;
* `Q838.exists_integrable_law_exact_quantization_error_oscillates` — for every `n ≥ 1` and every
  norm, an integrable law with `liminf k^{1/n} mqeExact = 0` and `limsup k^{1/n} mqeExact = ∞`;
* `Q838.exists_integrable_law_exact_quantization_error_oscillates_real` — the case `n = 1`;
* `Q838.exists_integrable_law_exact_quantization_error_not_convergent` — the normalized
  exact-cardinality sequence has no limit in `[0, ∞]`, while all of its terms are finite.

Lean version: 4.28.0.  Mathlib revision: 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
-/
import RMS.Q838

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Q838

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## The exact-cardinality error, and its identification with `mqe` -/

/-- The mean `k`-point quantization error of a law `μ` in the exact-cardinality form of the
printed question: `m_k = inf { E d_Σ(X) : Σ finite, #Σ = k }`, where
`d_Σ(x) = inf_{a ∈ Σ} ‖x - a‖`.  As for `Q838.mqe`, the expectation is a lower integral, so the
quantity is always well defined in `[0, ∞]`. -/
noncomputable def mqeExact (μ : Measure E) (k : ℕ) : ℝ≥0∞ :=
  ⨅ S : {S : Finset E // S.card = k},
    ∫⁻ x, ENNReal.ofReal (Metric.infDist x (S.1 : Set E)) ∂μ

omit [NormedSpace ℝ E] [BorelSpace E] in
/-- Enlarging a (nonempty) codebook can only decrease the lower integral of the distance
function. -/
lemma lintegral_infDist_mono (μ : Measure E) {S T : Finset E} (hST : S ⊆ T) (hS : S.Nonempty) :
    ∫⁻ x, ENNReal.ofReal (Metric.infDist x (T : Set E)) ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (Metric.infDist x (S : Set E)) ∂μ := by
  refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
  exact Metric.infDist_le_infDist_of_subset (by exact_mod_cast hST) (by exact_mod_cast hS)

omit [NormedSpace ℝ E] [BorelSpace E] in
/-- Every codebook of cardinality exactly `k ≥ 1` is nonempty, hence is an admissible codebook
for `mqe`; therefore `mqe μ k ≤ mqeExact μ k`. -/
lemma mqe_le_mqeExact (μ : Measure E) {k : ℕ} (hk : 1 ≤ k) :
    mqe μ k ≤ mqeExact μ k := by
  refine le_iInf fun S => ?_
  have hne : (S.1).Nonempty := Finset.card_pos.1 (by rw [S.2]; omega)
  exact iInf_le (fun S : {S : Finset E // S.Nonempty ∧ S.card ≤ k} =>
    ∫⁻ x, ENNReal.ofReal (Metric.infDist x (S.1 : Set E)) ∂μ) ⟨S.1, hne, le_of_eq S.2⟩

omit [NormedSpace ℝ E] [BorelSpace E] in
/-- In an infinite ambient space every nonempty codebook with at most `k` points extends to one
with exactly `k` points, without increasing the error; hence `mqeExact μ k ≤ mqe μ k`. -/
lemma mqeExact_le_mqe [Infinite E] (μ : Measure E) (k : ℕ) :
    mqeExact μ k ≤ mqe μ k := by
  refine le_iInf fun S => ?_
  obtain ⟨hne, hcard⟩ := S.2
  obtain ⟨T, hST, hT⟩ := Infinite.exists_superset_card_eq S.1 k hcard
  exact le_trans (iInf_le (fun T : {T : Finset E // T.card = k} =>
      ∫⁻ x, ENNReal.ofReal (Metric.infDist x (T.1 : Set E)) ∂μ) ⟨T, hT⟩)
    (lintegral_infDist_mono μ hST hne)

omit [NormedSpace ℝ E] [BorelSpace E] in
/-- **The exact-cardinality bridge.**  In an infinite ambient space the infimum over codebooks
of cardinality exactly `k` and the infimum over nonempty codebooks of cardinality at most `k`
agree, for every `k ≥ 1`. -/
theorem mqeExact_eq_mqe [Infinite E] (μ : Measure E) {k : ℕ} (hk : 1 ≤ k) :
    mqeExact μ k = mqe μ k :=
  le_antisymm (mqeExact_le_mqe μ k) (mqe_le_mqeExact μ hk)

/-! ## The constructed law -/

/-- The exact-cardinality error is the infimum of the ordinary expectations `E d_Σ(X)` over
codebooks `Σ` with `#Σ = k`: the lower-integral definition agrees with the usual one, all the
relevant Bochner integrals being defined. -/
lemma mqeExact_eq_iInf_ofReal_integral [FiniteDimensional ℝ E] (n k : ℕ) {u : E} (hu : ‖u‖ = 1) :
    mqeExact (lawX n u) k = ⨅ S : {S : Finset E // S.card = k},
      ENNReal.ofReal (∫ x, Metric.infDist x (S.1 : Set E) ∂(lawX n u)) := by
  refine iInf_congr fun S => ?_
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrable_infDist n hu S.1)
    (Filter.Eventually.of_forall fun x => Metric.infDist_nonneg)).symm

/-- For the constructed law the exact-cardinality error is finite for every `k ≥ 1`: the
counterexample really concerns finite mean quantization errors. -/
lemma mqeExact_lawX_lt_top [Infinite E] (n : ℕ) {u : E} (hu : ‖u‖ = 1) {k : ℕ} (hk : 1 ≤ k) :
    mqeExact (lawX n u) k < ⊤ := by
  rw [mqeExact_eq_mqe _ hk]
  exact lt_of_le_of_lt (le_trans (mqe_le_tailA n hu hk) (tailA_antitone n hk)) (tailA_one_lt_top n)

/-- The liminf of the normalized error of the constructed law vanishes (extracted from the proof
of `exists_integrable_law_quantization_error_oscillates`). -/
lemma liminf_mqe_lawX (n : ℕ) (hn : 1 ≤ n) {u : E} (hu : ‖u‖ = 1) :
    liminf (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe (lawX n u) k) atTop = 0 := by
  have hmap : Filter.map (Nn n) atTop ≤ (atTop : Filter ℕ) := (Nn_strictMono hn).tendsto_atTop
  have hT : Tendsto (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe (lawX n u) k)
      (Filter.map (Nn n) atTop) (𝓝 0) := tendsto_map'_iff.2 (tendsto_liminf_subseq n hn hu)
  refine le_antisymm ?_ (zero_le _)
  calc liminf (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe (lawX n u) k) atTop
      ≤ liminf (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe (lawX n u) k)
          (Filter.map (Nn n) atTop) := liminf_le_liminf_of_le hmap
    _ = 0 := hT.liminf_eq

/-- The limsup of the normalized error of the constructed law is `+∞` (extracted from the proof
of `exists_integrable_law_quantization_error_oscillates`). -/
lemma limsup_mqe_lawX (n : ℕ) (hn : 1 ≤ n) {u : E} (hu : ‖u‖ = 1) :
    limsup (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe (lawX n u) k) atTop = ⊤ := by
  have hmap : Filter.map (Nh n) atTop ≤ (atTop : Filter ℕ) := (Nh_strictMono hn).tendsto_atTop
  have hT : Tendsto (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe (lawX n u) k)
      (Filter.map (Nh n) atTop) (𝓝 ⊤) := tendsto_map'_iff.2 (tendsto_limsup_subseq n hn hu)
  refine le_antisymm le_top ?_
  calc (⊤ : ℝ≥0∞)
      = limsup (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe (lawX n u) k)
          (Filter.map (Nh n) atTop) := hT.limsup_eq.symm
    _ ≤ limsup (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe (lawX n u) k) atTop :=
        limsup_le_limsup_of_le hmap

omit [NormedSpace ℝ E] [BorelSpace E] in
/-- Eventual (in `k`) agreement of the two normalized error sequences. -/
lemma eventually_normalized_mqeExact_eq [Infinite E] (μ : Measure E) (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqeExact μ k
      = (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqe μ k := by
  filter_upwards [eventually_ge_atTop 1] with k hk
  rw [mqeExact_eq_mqe μ hk]

/-! ## The negative answer with the printed definition -/

/-- The full package for the constructed law: it is a probability law, the identity is integrable
under it, all exact-cardinality errors (for `k ≥ 1`) are finite, and the normalized exact
errors oscillate between `0` and `+∞`. -/
lemma lawX_exact_oscillates {n : ℕ} (hn : 1 ≤ n) (hdim : Module.finrank ℝ E = n) {u : E}
    (hu : ‖u‖ = 1) :
    IsProbabilityMeasure (lawX n u) ∧ Integrable (fun x : E => x) (lawX n u) ∧
      (∀ k : ℕ, 1 ≤ k → mqeExact (lawX n u) k < ⊤) ∧
      liminf (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqeExact (lawX n u) k) atTop = 0 ∧
      limsup (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqeExact (lawX n u) k) atTop = ⊤ := by
  haveI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (R := ℝ) (by omega)
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  haveI : Infinite E := PreconnectedSpace.infinite
  have hev := eventually_normalized_mqeExact_eq (lawX n u) n
  refine ⟨inferInstance, integrable_lawX n hu, fun k hk => mqeExact_lawX_lt_top n hu hk, ?_, ?_⟩
  · rw [liminf_congr hev]; exact liminf_mqe_lawX n hn hu
  · rw [limsup_congr hev]; exact limsup_mqe_lawX n hn hu

omit [MeasurableSpace E] [BorelSpace E] in
/-- A unit vector in a real normed space of positive finite dimension. -/
lemma exists_unit_vector {n : ℕ} (hn : 1 ≤ n) (hdim : Module.finrank ℝ E = n) :
    ∃ u : E, ‖u‖ = 1 := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  refine ⟨‖x‖⁻¹ • x, ?_⟩
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]

/-- **The negative answer to Q838, with the printed exact-cardinality definition.**
For every `n ≥ 1` and every norm on an `n`-dimensional real vector space there is an integrable
law `μ` for which the normalized exact-cardinality mean quantization errors satisfy

`liminf_k k^{1/n} m_k = 0`  and  `limsup_k k^{1/n} m_k = +∞`.

In particular `k^{1/n} m_k` need not converge, even in `[0, ∞]`. -/
theorem exists_integrable_law_exact_quantization_error_oscillates
    {n : ℕ} (hn : 1 ≤ n) (hdim : Module.finrank ℝ E = n) :
    ∃ μ : Measure E, IsProbabilityMeasure μ ∧ Integrable (fun x : E => x) μ ∧
      liminf (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqeExact μ k) atTop = 0 ∧
      limsup (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqeExact μ k) atTop = ⊤ := by
  obtain ⟨u, hu⟩ := exists_unit_vector hn hdim
  obtain ⟨hprob, hint, _, h0, htop⟩ := lawX_exact_oscillates hn hdim hu
  exact ⟨lawX n u, hprob, hint, h0, htop⟩

/-- The dimension-one instance: an integrable real random variable whose exact-cardinality mean
quantization errors satisfy `liminf k m_k = 0` and `limsup k m_k = +∞`. -/
theorem exists_integrable_law_exact_quantization_error_oscillates_real :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ Integrable (fun x : ℝ => x) μ ∧
      liminf (fun k : ℕ => (k : ℝ≥0∞) * mqeExact μ k) atTop = 0 ∧
      limsup (fun k : ℕ => (k : ℝ≥0∞) * mqeExact μ k) atTop = ⊤ := by
  obtain ⟨μ, hμ, hint, h0, htop⟩ :=
    exists_integrable_law_exact_quantization_error_oscillates (E := ℝ) (n := 1) le_rfl (by simp)
  refine ⟨μ, hμ, hint, ?_, ?_⟩
  · simpa using h0
  · simpa using htop

/-- **Direct answer to the printed question:** the normalized exact-cardinality mean quantization
error `k^{1/n} m_k` is *not* guaranteed to have a limit — not even in `[0, ∞]` — for an integrable
random vector; moreover the counterexample has finite mean quantization errors. -/
theorem exists_integrable_law_exact_quantization_error_not_convergent
    {n : ℕ} (hn : 1 ≤ n) (hdim : Module.finrank ℝ E = n) :
    ∃ μ : Measure E, IsProbabilityMeasure μ ∧ Integrable (fun x : E => x) μ ∧
      (∀ k : ℕ, 1 ≤ k → mqeExact μ k < ⊤) ∧
      ¬ ∃ L : ℝ≥0∞,
        Tendsto (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqeExact μ k) atTop (𝓝 L) := by
  obtain ⟨u, hu⟩ := exists_unit_vector hn hdim
  obtain ⟨hprob, hint, hfin, h0, htop⟩ := lawX_exact_oscillates hn hdim hu
  refine ⟨lawX n u, hprob, hint, hfin, ?_⟩
  rintro ⟨L, hL⟩
  have h1 : liminf (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqeExact (lawX n u) k) atTop = L :=
    hL.liminf_eq
  have h2 : limsup (fun k : ℕ => (k : ℝ≥0∞) ^ ((1 : ℝ) / n) * mqeExact (lawX n u) k) atTop = L :=
    hL.limsup_eq
  rw [h0] at h1
  rw [htop] at h2
  exact ENNReal.top_ne_zero (h2.trans h1.symm)

end Q838
