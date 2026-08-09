import Mathlib

/-!
# Q877 — singular partial sums of i.i.d. random matrices

This file formalizes the complete intended content of Q877 (a) and (b).

## Setting

`A 0, A 1, ...` are i.i.d. integrable random `d × d` real matrices on a probability space
`(Ω, μ)`, `S_N = A 0 + ... + A (N-1)` (the printed sum `∑_{k=0}^{p}` is reindexed as
`N = p + 1` summands, which is an exact reindexing), and property `(P)` is the existence of
`c ∈ (0,1)` with `μ {det S_N = 0} ≥ c` for every `N ≥ 1`.

## Printed / formal mismatches (documented as required)

* The printed statement asks for a vector `X` with `A n X = 0` almost surely but **omits
  `X ≠ 0`**; literally, `X = 0` makes both questions vacuous. We formalize the clearly intended
  statement: the vector is **deterministic and nonzero**.
* The printed sum is indexed by `k = 0, ..., p`; we use `N = p + 1` summands.
* Integrability of a random matrix is formalized entrywise (`Integrable (fun ω => A 0 ω i j)`),
  which is equivalent to integrability for any matrix norm (all norms on `M_d(ℝ)` are equivalent).
* Matrices are equipped with the product σ-algebra of their entries, which is the Borel σ-algebra
  of the product topology.
* Positive semidefiniteness is `Matrix.PosSemidef`, i.e. Hermitian (over `ℝ`: symmetric) together
  with nonnegativity of the quadratic form — the standard French "symétrique positive".

## Main results

* `Q877.tendsto_ae_partialSum_div` and `Q877.tendsto_inProbability_partialSum_div`:
  the (strong, hence weak) law of large numbers for i.i.d. integrable random matrices.
* `Q877.tendsto_measure_singularEvent_of_det_mean_ne_zero`: the mean obstruction —
  if `det E[A 0] ≠ 0` then `μ (det S_N = 0) → 0`.
* `Q877.q877a`: part (a) — for an a.s. positive semidefinite `A 0`, property `(P)` produces a
  deterministic nonzero `x` with `μ {ω | ∀ n, A n ω *ᵥ x = 0} = 1`.
* `Q877.CEA_*` and `Q877.CE_*`: the explicit `3 × 3` Rademacher obstruction — the sequence is
  i.i.d. (`CEA_isIID`), built from pairs of independent Rademacher variables (`CE_rademacher_fst`,
  `CE_rademacher_snd`, `CE_pair_indep`), symmetric (`CEA_isSymm`), bounded (`CEA_bounded`),
  centered (`CEA_centered`) and of rank `2 = 3 - 1` (`CEA_rank`), all its partial sums are
  singular (`CEA_det_partialSum`, `CEA_propP`), and yet it has no deterministic nonzero common
  kernel vector (`CEA_no_deterministic_kernel_vector`).  So symmetry, boundedness, centering and
  constant rank do not suffice: some extra structure is genuinely needed in part (b).
* `Q877.q877b`: part (b) — the same conclusion under the existence of a deterministic positive
  definite symmetrizer `H` with `H * A 0` positive semidefinite almost surely.
* `Q877.q877_synthesis`: a synthesis statement packaging (a) and (b).
-/

namespace Q877

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology ENNReal

/-- Matrices carry the product σ-algebra of their entries. -/
instance instMeasurableSpaceMatrix {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs (MeasurableSpace (m → n → α))

/-- The product σ-algebra on matrices is the Borel σ-algebra of the product topology. -/
instance instBorelSpaceMatrix {m n α : Type*} [Countable m] [Countable n] [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] :
    BorelSpace (Matrix m n α) :=
  inferInstanceAs (BorelSpace (m → n → α))

section Setting

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The partial sum `S_N = A 0 + ⋯ + A (N-1)` (the printed `∑_{k=0}^p` with `N = p+1`). -/
def partialSum (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (N : ℕ) (ω : Ω) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∑ k ∈ Finset.range N, A k ω

/-- The event that the `N`-th partial sum is singular. -/
def singularEvent (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (N : ℕ) : Set Ω :=
  {ω | (partialSum A N ω).det = 0}

/-- Property `(P)`: there is `c ∈ (0,1)` with `μ (det S_N = 0) ≥ c` for every `N = p + 1 ≥ 1`. -/
def PropP (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (μ : Measure Ω) : Prop :=
  ∃ c : ℝ≥0∞, 0 < c ∧ c < 1 ∧ ∀ p : ℕ, c ≤ μ (singularEvent A (p + 1))

/-- The probabilistic hypotheses of Q877: the `A n` are measurable, independent, identically
distributed, and integrable (entrywise). -/
structure IsIID (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (μ : Measure Ω) : Prop where
  meas : ∀ n, Measurable (A n)
  indep : iIndepFun A μ
  ident : ∀ n, IdentDistrib (A n) (A 0) μ μ
  integrable : ∀ i j, Integrable (fun ω => A 0 ω i j) μ

/-- The mean matrix `E[A 0]`, defined entrywise. -/
noncomputable def meanMatrix (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (μ : Measure Ω) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∫ ω, A 0 ω i j ∂μ

end Setting

section Auxiliary

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
  {A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ}

/-- Taking an entry of a matrix is measurable. -/
lemma measurable_entry (i j : Fin d) :
    Measurable (fun B : Matrix (Fin d) (Fin d) ℝ => B i j) :=
  (measurable_pi_apply j).comp (measurable_pi_apply i)

/-- Multiplying a matrix on the left by a fixed matrix is measurable. -/
lemma measurable_matrix_mul (H : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (fun B : Matrix (Fin d) (Fin d) ℝ => H * B) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (measurable_entry k j).const_mul _

/-- Applying a matrix to a fixed vector is measurable. -/
lemma measurable_mulVec (x : Fin d → ℝ) :
    Measurable (fun B : Matrix (Fin d) (Fin d) ℝ => B *ᵥ x) := by
  refine measurable_pi_lambda _ fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun k _ => (measurable_entry i k).mul_const _

/-- The set of matrices annihilating a fixed vector is measurable. -/
lemma measurableSet_mulVec_eq_zero (x : Fin d → ℝ) :
    MeasurableSet {B : Matrix (Fin d) (Fin d) ℝ | B *ᵥ x = 0} :=
  measurableSet_eq_fun (measurable_mulVec x) measurable_const

/-- Partial sums are measurable. -/
lemma measurable_partialSum (hA : ∀ n, Measurable (A n)) (N : ℕ) :
    Measurable (partialSum A N) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [partialSum, Matrix.sum_apply]
  exact Finset.measurable_sum _ fun k _ => (measurable_entry i j).comp (hA k)

/-- The singularity events are measurable. -/
lemma measurableSet_singularEvent (hA : ∀ n, Measurable (A n)) (N : ℕ) :
    MeasurableSet (singularEvent A N) :=
  measurableSet_eq_fun ((Continuous.matrix_det continuous_id).measurable.comp
    (measurable_partialSum hA N)) measurable_const

/-- If almost surely `A 0 ω` lies in a measurable set `T`, the same holds for every `A n`. -/
lemma ae_mem_of_identDistrib (h : IsIID A μ)
    {T : Set (Matrix (Fin d) (Fin d) ℝ)} (hT : MeasurableSet T)
    (h0 : ∀ᵐ ω ∂μ, A 0 ω ∈ T) (n : ℕ) : ∀ᵐ ω ∂μ, A n ω ∈ T := by
  have h1 : μ ((A n) ⁻¹' Tᶜ) = μ ((A 0) ⁻¹' Tᶜ) := (h.ident n).measure_mem_eq hT.compl
  have h2 : μ ((A 0) ⁻¹' Tᶜ) = 0 := by rw [ae_iff] at h0; exact h0
  rw [ae_iff]
  simpa using h1.trans h2

/-- Entrywise strong law of large numbers. -/
lemma tendsto_ae_entry (h : IsIID A μ) (i j : Fin d) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (partialSum A N ω) i j) atTop
      (𝓝 (meanMatrix A μ i j)) := by
  have hpair : Pairwise (Function.onFun (fun X Y => IndepFun X Y μ) (fun n ω => A n ω i j)) :=
    fun m n hmn => (h.indep.indepFun hmn).comp (measurable_entry i j) (measurable_entry i j)
  have hid : ∀ n, IdentDistrib (fun ω => A n ω i j) (fun ω => A 0 ω i j) μ μ :=
    fun n => (h.ident n).comp (measurable_entry i j)
  have hlln := ProbabilityTheory.strong_law_ae (fun n ω => A n ω i j) (h.integrable i j) hpair hid
  filter_upwards [hlln] with ω hω
  convert hω using 2 with N
  simp [partialSum, Matrix.sum_apply]

/-- If almost every `ω` eventually avoids `E N`, then `μ (E N) → 0`. -/
lemma tendsto_measure_of_ae_eventually_notMem [IsFiniteMeasure μ] {E : ℕ → Set Ω}
    (hE : ∀ N, MeasurableSet (E N)) (h : ∀ᵐ ω ∂μ, ∀ᶠ N in atTop, ω ∉ E N) :
    Tendsto (fun N => μ (E N)) atTop (𝓝 0) := by
  set F : ℕ → Set Ω := fun N => ⋃ k, ⋃ (_ : N ≤ k), E k with hF
  have hFmeas : ∀ N, MeasurableSet (F N) :=
    fun N => MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hE k
  have hanti : Antitone F := by
    intro m n hmn ω hω
    simp only [hF, Set.mem_iUnion] at hω ⊢
    obtain ⟨k, hk, hk'⟩ := hω
    exact ⟨k, le_trans hmn hk, hk'⟩
  have hsub : (⋂ N, F N) ⊆ {ω | ¬ ∀ᶠ N in atTop, ω ∉ E N} := by
    intro ω hω
    simp only [Set.mem_iInter, hF, Set.mem_iUnion] at hω
    simp only [Set.mem_setOf_eq, eventually_atTop, not_exists, not_forall]
    intro N
    obtain ⟨k, hk, hk'⟩ := hω N
    exact ⟨k, hk, by simpa using hk'⟩
  have hinter : μ (⋂ N, F N) = 0 := measure_mono_null hsub (by rwa [← ae_iff])
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (fun N => (hFmeas N).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun N => zero_le _) (fun N => measure_mono ?_)
  intro ω hω
  simp only [hF, Set.mem_iUnion]
  exact ⟨N, le_refl _, hω⟩

/-- Expansion of the quadratic form of a matrix. -/
lemma quadraticForm_expand (x : Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ) :
    x ⬝ᵥ B *ᵥ x = ∑ i, ∑ j, x i * B i j * x j := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- The quadratic form of the mean matrix is the mean of the quadratic form. -/
lemma dotProduct_meanMatrix_mulVec (h : IsIID A μ) (x : Fin d → ℝ) :
    x ⬝ᵥ (meanMatrix A μ) *ᵥ x = ∫ ω, x ⬝ᵥ (A 0 ω) *ᵥ x ∂μ := by
  simp only [quadraticForm_expand]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => ((h.integrable i j).const_mul (x i)).mul_const (x j)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (fun j _ => ((h.integrable i j).const_mul (x i)).mul_const (x j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, integral_const_mul]
  rfl

/-- The set of positive semidefinite matrices is closed, hence measurable. -/
lemma measurableSet_posSemidef :
    MeasurableSet {B : Matrix (Fin d) (Fin d) ℝ | B.PosSemidef} := by
  have hclosed : IsClosed {B : Matrix (Fin d) (Fin d) ℝ | B.PosSemidef} := by
    have hset : {B : Matrix (Fin d) (Fin d) ℝ | B.PosSemidef} =
        (⋂ (i : Fin d) (j : Fin d), {B : Matrix (Fin d) (Fin d) ℝ | B i j = B j i}) ∩
          ⋂ x : Fin d → ℝ, {B : Matrix (Fin d) (Fin d) ℝ | 0 ≤ x ⬝ᵥ B *ᵥ x} := by
      ext B
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq,
        posSemidef_iff_dotProduct_mulVec]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun i j => by
          simpa [Matrix.IsHermitian, ← Matrix.ext_iff, conjTranspose_apply] using
            (Matrix.IsHermitian.apply h1 j i), h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        ext i j
        simpa [conjTranspose_apply] using (h1 j i)
    rw [hset]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
      (isClosed_iInter fun x => ?_)
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · exact isClosed_le continuous_const (by fun_prop)
  exact hclosed.measurableSet

/-- The mean of an almost surely positive semidefinite integrable random matrix is positive
semidefinite. -/
lemma posSemidef_meanMatrix (h : IsIID A μ)
    (hpsd : ∀ᵐ ω ∂μ, (A 0 ω).PosSemidef) : (meanMatrix A μ).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    simp only [conjTranspose_apply, RCLike.star_def, conj_trivial, meanMatrix, Matrix.of_apply]
    refine integral_congr_ae ?_
    filter_upwards [hpsd] with ω hω
    have h2 := congrFun (congrFun hω.isHermitian i) j
    simpa [conjTranspose_apply] using h2
  · simp only [star_trivial]
    rw [dotProduct_meanMatrix_mulVec h]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hpsd] with ω hω
    simpa using (posSemidef_iff_dotProduct_mulVec.1 hω).2 x

end Auxiliary

section Obligation1

/-! ### 1. The mean obstruction, with the probabilistic hypotheses discharged -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
  {A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ}

/-- **Law of large numbers for i.i.d. integrable random matrices** (almost sure form):
`(1/N) S_N → E[A 0]` almost surely. -/
theorem tendsto_ae_partialSum_div (h : IsIID A μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • partialSum A N ω) atTop (𝓝 (meanMatrix A μ)) := by
  have hall : ∀ᵐ ω ∂μ, ∀ i j, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (partialSum A N ω) i j) atTop
      (𝓝 (meanMatrix A μ i j)) := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    exact tendsto_ae_entry h i j
  filter_upwards [hall] with ω hω
  exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => by simpa using hω i j

/-- **Weak law of large numbers** for i.i.d. integrable random matrices, entrywise form:
`(1/N) S_N → E[A 0]` in probability. -/
theorem tendsto_inProbability_partialSum_div [IsProbabilityMeasure μ] (h : IsIID A μ)
    (i j : Fin d) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ =>
      μ {ω | ε ≤ |(N : ℝ)⁻¹ * (partialSum A N ω) i j - meanMatrix A μ i j|}) atTop (𝓝 0) := by
  have hmeas : ∀ N : ℕ, AEStronglyMeasurable
      (fun ω => (N : ℝ)⁻¹ * (partialSum A N ω) i j) μ := fun N =>
    (((measurable_entry i j).comp (measurable_partialSum h.meas N)).const_mul
      _).aestronglyMeasurable
  have key := tendstoInMeasure_of_tendsto_ae hmeas (tendsto_ae_entry h i j)
    (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  refine key.congr fun N => ?_
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq]
  rw [edist_dist, Real.dist_eq, ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]

/-- **The mean obstruction.** If the mean `E[A 0]` is invertible, then the probability that the
`N`-th partial sum is singular tends to `0`. -/
theorem tendsto_measure_singularEvent_of_det_mean_ne_zero [IsProbabilityMeasure μ] (h : IsIID A μ)
    (hM : (meanMatrix A μ).det ≠ 0) :
    Tendsto (fun N => μ (singularEvent A N)) atTop (𝓝 0) := by
  refine tendsto_measure_of_ae_eventually_notMem (measurableSet_singularEvent h.meas) ?_
  filter_upwards [tendsto_ae_partialSum_div h] with ω hω
  have hdet : Tendsto (fun N : ℕ => ((N : ℝ)⁻¹ • partialSum A N ω).det) atTop
      (𝓝 (meanMatrix A μ).det) := ((Continuous.matrix_det continuous_id).tendsto _).comp hω
  filter_upwards [hdet.eventually_ne hM] with N hN
  simp only [singularEvent, Set.mem_setOf_eq]
  intro hcon
  exact hN (by rw [Matrix.det_smul, hcon, mul_zero])

/-- Property `(P)` forces the mean to be singular. -/
theorem det_meanMatrix_eq_zero_of_propP [IsProbabilityMeasure μ] (h : IsIID A μ)
    (hP : PropP A μ) : (meanMatrix A μ).det = 0 := by
  by_contra hM
  obtain ⟨c, hc0, hc1, hc⟩ := hP
  have h1 := (tendsto_measure_singularEvent_of_det_mean_ne_zero h hM).comp (tendsto_add_atTop_nat 1)
  have h2 : c ≤ 0 := ge_of_tendsto h1 (Eventually.of_forall hc)
  exact absurd (le_antisymm h2 (zero_le c)) hc0.ne'

end Obligation1

section Obligation2

/-! ### 2. Part (a): the full positive-semidefinite theorem -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {d : ℕ}
  {A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ}

/-- **Q877 (a).** For i.i.d. integrable random matrices which are almost surely symmetric
positive semidefinite, property `(P)` produces a *deterministic nonzero* vector `x` which is
almost surely annihilated by *every* `A n` simultaneously.

Since the `A n` are identically distributed, it suffices to assume positive semidefiniteness for
`A 0`; the conclusion for all `n` then follows from the equality of the laws. -/
theorem q877a (h : IsIID A μ) (hpsd : ∀ᵐ ω ∂μ, (A 0 ω).PosSemidef) (hP : PropP A μ) :
    ∃ x : Fin d → ℝ, x ≠ 0 ∧ μ {ω | ∀ n, (A n ω) *ᵥ x = 0} = 1 := by
  -- Property `(P)` and the mean obstruction make the mean singular.
  have hM : (meanMatrix A μ).det = 0 := det_meanMatrix_eq_zero_of_propP h hP
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hM
  refine ⟨x, hx0, ?_⟩
  -- The nonnegative quadratic form `x ⬝ᵥ A 0 ω *ᵥ x` has zero expectation.
  have hq : ∫ ω, x ⬝ᵥ (A 0 ω) *ᵥ x ∂μ = 0 := by
    rw [← dotProduct_meanMatrix_mulVec h, hx, dotProduct_zero]
  have hnonneg : 0 ≤ᵐ[μ] fun ω => x ⬝ᵥ (A 0 ω) *ᵥ x := by
    filter_upwards [hpsd] with ω hω
    simpa using (posSemidef_iff_dotProduct_mulVec.1 hω).2 x
  have hint : Integrable (fun ω => x ⬝ᵥ (A 0 ω) *ᵥ x) μ := by
    simp only [quadraticForm_expand]
    exact integrable_finset_sum _ fun i _ => integrable_finset_sum _
      fun j _ => ((h.integrable i j).const_mul (x i)).mul_const (x j)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).1 hq
  -- Positive semidefiniteness upgrades a vanishing quadratic form to `A 0 ω *ᵥ x = 0`.
  have h0 : ∀ᵐ ω ∂μ, A 0 ω ∈ {B : Matrix (Fin d) (Fin d) ℝ | B *ᵥ x = 0} := by
    filter_upwards [hpsd, hzero] with ω h1 h2
    exact (h1.dotProduct_mulVec_zero_iff x).1 (by simpa using h2)
  -- Identical laws give the statement for each `n`, countability the simultaneous event.
  have hall : ∀ᵐ ω ∂μ, ∀ n, (A n ω) *ᵥ x = 0 := by
    rw [ae_all_iff]
    exact fun n => ae_mem_of_identDistrib h (measurableSet_mulVec_eq_zero x) h0 n
  have hmeasS : MeasurableSet {ω | ∀ n, (A n ω) *ᵥ x = 0} := by
    have hrw : {ω | ∀ n, (A n ω) *ᵥ x = 0} =
        ⋂ n, (A n) ⁻¹' {B : Matrix (Fin d) (Fin d) ℝ | B *ᵥ x = 0} := by
      ext ω; simp
    rw [hrw]
    exact MeasurableSet.iInter fun n => (h.meas n) (measurableSet_mulVec_eq_zero x)
  refine (prob_compl_eq_zero_iff hmeasS).1 ?_
  rw [Set.compl_setOf, ← ae_iff]
  exact hall

end Obligation2

section Obligation3

/-! ### 3. The explicit `3 × 3` obstruction without positivity -/

/-- The sign of a boolean, giving a Rademacher variable under the uniform law. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The symmetric `3 × 3` matrix `M(x,y)`. -/
def M3 (x y : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0, x, y; x, 0, 0; y, 0, 0]

/-- Sample space of the counterexample: sequences of pairs of signs. -/
abbrev CEΩ : Type := ℕ → Bool × Bool

/-- Uniform law on a pair of independent Rademacher signs. -/
noncomputable def CEν : Measure (Bool × Bool) := (PMF.uniformOfFintype (Bool × Bool)).toMeasure

instance : IsProbabilityMeasure CEν := by
  unfold CEν; infer_instance

/-- The i.i.d. law of the counterexample. -/
noncomputable def CEμ : Measure CEΩ := Measure.infinitePi (fun _ : ℕ => CEν)

instance : IsProbabilityMeasure CEμ := by
  unfold CEμ; infer_instance

/-- The matrix attached to a pair of signs. -/
def CEmat (b : Bool × Bool) : Matrix (Fin 3) (Fin 3) ℝ := M3 (sgn b.1) (sgn b.2)

/-- The counterexample sequence `A n = M(ξ n, η n)` with `(ξ n, η n)` i.i.d. pairs of independent
Rademacher variables. -/
def CEA (n : ℕ) (ω : CEΩ) : Matrix (Fin 3) (Fin 3) ℝ := CEmat (ω n)

/-- `M(x,y)` is symmetric. -/
lemma M3_isSymm (x y : ℝ) : (M3 x y).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M3]

/-- `M(x,y)` is singular. -/
lemma M3_det (x y : ℝ) : (M3 x y).det = 0 := by
  simp [M3, Matrix.det_fin_three]

/-- `M` is additive in its arguments. -/
lemma M3_add (x y x' y' : ℝ) : M3 x y + M3 x' y' = M3 (x + x') (y + y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M3]

/-- `M(0,0)` is the zero matrix. -/
lemma M3_zero : M3 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M3]

/-- The action of `M(x,y)` on a vector. -/
lemma M3_mulVec (x y : ℝ) (v : Fin 3 → ℝ) :
    (M3 x y) *ᵥ v = ![x * v 1 + y * v 2, x * v 0, y * v 0] := by
  funext i
  fin_cases i <;> simp [M3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The kernel of `M(x,y)`, for `(x,y) ≠ (0,0)`, is the line spanned by `(0,-y,x)`. -/
lemma M3_ker (x y : ℝ) (h : x ≠ 0 ∨ y ≠ 0) :
    LinearMap.ker (M3 x y).mulVecLin = Submodule.span ℝ {(![0, -y, x] : Fin 3 → ℝ)} := by
  apply le_antisymm
  · intro v hv
    simp only [LinearMap.mem_ker, mulVecLin_apply, M3_mulVec] at hv
    have h0 : x * v 1 + y * v 2 = 0 := congrFun hv 0
    have h1 : x * v 0 = 0 := congrFun hv 1
    have h2 : y * v 0 = 0 := congrFun hv 2
    have hv0 : v 0 = 0 := by
      rcases h with hx | hy
      · exact (mul_eq_zero.1 h1).resolve_left hx
      · exact (mul_eq_zero.1 h2).resolve_left hy
    rw [Submodule.mem_span_singleton]
    rcases h with hx | hy
    · refine ⟨v 2 / x, ?_⟩
      funext i
      fin_cases i <;> simp [hv0] <;> field_simp <;> nlinarith [h0]
    · refine ⟨-(v 1) / y, ?_⟩
      funext i
      fin_cases i <;> simp [hv0] <;> field_simp <;> nlinarith [h0]
  · rw [Submodule.span_le]
    intro w hw
    simp only [Set.mem_singleton_iff] at hw
    subst hw
    simp only [SetLike.mem_coe, LinearMap.mem_ker, mulVecLin_apply, M3_mulVec]
    funext i
    fin_cases i <;> simp <;> ring

/-- `M(x,y)` has rank `2` as soon as `(x,y) ≠ (0,0)`. -/
lemma M3_rank (x y : ℝ) (h : x ≠ 0 ∨ y ≠ 0) : (M3 x y).rank = 2 := by
  have hv : (![0, -y, x] : Fin 3 → ℝ) ≠ 0 := by
    intro hc
    rcases h with hx | hy
    · have h2 := congrFun hc 2
      simp only [Matrix.cons_val, Pi.zero_apply] at h2
      exact hx h2
    · have h1 := congrFun hc 1
      simp only [Matrix.cons_val, Pi.zero_apply, neg_eq_zero] at h1
      exact hy h1
  have hker : Module.finrank ℝ (LinearMap.ker (M3 x y).mulVecLin) = 1 := by
    rw [M3_ker x y h]
    exact finrank_span_singleton hv
  have hrn := LinearMap.finrank_range_add_finrank_ker (M3 x y).mulVecLin
  rw [hker] at hrn
  simp only [Matrix.rank]
  have h3 : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by simp
  omega

/-- The signs are `±1`, in particular nonzero. -/
lemma sgn_ne_zero (b : Bool) : sgn b ≠ 0 := by
  cases b <;> norm_num [sgn]

/-- The signs have modulus one. -/
lemma abs_sgn (b : Bool) : |sgn b| = 1 := by
  cases b <;> norm_num [sgn]

/-- The counterexample matrices are symmetric. -/
theorem CEA_isSymm (n : ℕ) (ω : CEΩ) : (CEA n ω).IsSymm := M3_isSymm _ _

/-- The counterexample matrices are bounded (entries of modulus `≤ 1`). -/
theorem CEA_bounded (n : ℕ) (ω : CEΩ) (i j : Fin 3) : |CEA n ω i j| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> simp [CEA, CEmat, M3, abs_sgn]

/-- The counterexample matrices have rank `2 = 3 - 1` everywhere, in particular almost surely. -/
theorem CEA_rank (n : ℕ) (ω : CEΩ) : (CEA n ω).rank = 2 :=
  M3_rank _ _ (Or.inl (sgn_ne_zero _))

/-- The matrix-valued function of a pair of signs is measurable. -/
lemma measurable_CEmat : Measurable CEmat := Measurable.of_discrete

/-- The counterexample sequence is measurable. -/
lemma measurable_CEA (n : ℕ) : Measurable (CEA n) :=
  measurable_CEmat.comp (measurable_pi_apply n)

/-- The counterexample sequence is independent. -/
lemma CEA_indep : iIndepFun CEA CEμ :=
  iIndepFun_infinitePi (P := fun _ : ℕ => CEν) (X := fun _ : ℕ => CEmat)
    (fun _ => measurable_CEmat)

/-- The counterexample sequence is identically distributed. -/
lemma CEA_identDistrib (n : ℕ) : IdentDistrib (CEA n) (CEA 0) CEμ CEμ := by
  refine ⟨(measurable_CEA n).aemeasurable, (measurable_CEA 0).aemeasurable, ?_⟩
  have h1 : CEμ.map (Function.eval n) = CEν := (measurePreserving_eval_infinitePi _ n).map_eq
  have h0 : CEμ.map (Function.eval 0) = CEν := (measurePreserving_eval_infinitePi _ 0).map_eq
  have e1 : CEμ.map (CEA n) = (CEμ.map (Function.eval n)).map CEmat := by
    rw [Measure.map_map measurable_CEmat (measurable_pi_apply n)]
    rfl
  have e0 : CEμ.map (CEA 0) = (CEμ.map (Function.eval 0)).map CEmat := by
    rw [Measure.map_map measurable_CEmat (measurable_pi_apply 0)]
    rfl
  rw [e1, e0, h1, h0]

/-- The uniform (Rademacher) law on `Bool`. -/
noncomputable def uB : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure uB := by
  unfold uB; infer_instance

lemma uB_singleton (b : Bool) : uB {b} = 2⁻¹ := by
  simp [uB, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    PMF.uniformOfFintype_apply]

lemma CEν_singleton (b : Bool × Bool) : CEν {b} = 4⁻¹ := by
  simp [CEν, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    PMF.uniformOfFintype_apply]

/-- The law of a pair `(ξ n, η n)` is the product of two Rademacher laws: the two coordinates of
each pair are independent. -/
lemma CEν_eq_prod : CEν = uB.prod uB := by
  refine Measure.ext_of_singleton fun b => ?_
  obtain ⟨b1, b2⟩ := b
  rw [CEν_singleton, show ({(b1, b2)} : Set (Bool × Bool)) = {b1} ×ˢ {b2} by simp,
    Measure.prod_prod, uB_singleton, uB_singleton,
    show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num)]

/-- `ξ n` is a Rademacher variable: each of its two values has probability `1/2`. -/
theorem CE_rademacher_fst (n : ℕ) (b : Bool) : CEμ {ω : CEΩ | (ω n).1 = b} = 2⁻¹ := by
  have hmp := measurePreserving_eval_infinitePi (fun _ : ℕ => CEν) n
  have e : {ω : CEΩ | (ω n).1 = b} = (Function.eval n) ⁻¹' ({b} ×ˢ Set.univ) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Function.eval, Set.mem_prod,
      Set.mem_singleton_iff, Set.mem_univ, and_true]
  rw [e]
  show (Measure.infinitePi fun _ : ℕ => CEν) _ = _
  rw [hmp.measure_preimage ((MeasurableSet.of_discrete).prod MeasurableSet.univ).nullMeasurableSet,
    CEν_eq_prod, Measure.prod_prod, measure_univ, mul_one, uB_singleton]

/-- `η n` is a Rademacher variable: each of its two values has probability `1/2`. -/
theorem CE_rademacher_snd (n : ℕ) (b : Bool) : CEμ {ω : CEΩ | (ω n).2 = b} = 2⁻¹ := by
  have hmp := measurePreserving_eval_infinitePi (fun _ : ℕ => CEν) n
  have e : {ω : CEΩ | (ω n).2 = b} = (Function.eval n) ⁻¹' (Set.univ ×ˢ {b}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Function.eval, Set.mem_prod,
      Set.mem_singleton_iff, Set.mem_univ, true_and]
  rw [e]
  show (Measure.infinitePi fun _ : ℕ => CEν) _ = _
  rw [hmp.measure_preimage (MeasurableSet.univ.prod (MeasurableSet.of_discrete)).nullMeasurableSet,
    CEν_eq_prod, Measure.prod_prod, measure_univ, one_mul, uB_singleton]

/-- Within each pair, `ξ n` and `η n` are independent. -/
theorem CE_pair_indep (n : ℕ) :
    IndepFun (fun ω : CEΩ => (ω n).1) (fun ω : CEΩ => (ω n).2) CEμ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hmp := measurePreserving_eval_infinitePi (fun _ : ℕ => CEν) n
  have e1 : (fun ω : CEΩ => (ω n).1) ⁻¹' s ∩ (fun ω : CEΩ => (ω n).2) ⁻¹' t
      = (Function.eval n) ⁻¹' (s ×ˢ t) := rfl
  have e2 : (fun ω : CEΩ => (ω n).1) ⁻¹' s = (Function.eval n) ⁻¹' (s ×ˢ Set.univ) := by
    ext ω; simp [Function.eval]
  have e3 : (fun ω : CEΩ => (ω n).2) ⁻¹' t = (Function.eval n) ⁻¹' (Set.univ ×ˢ t) := by
    ext ω; simp [Function.eval]
  rw [e1, e2, e3]
  show (Measure.infinitePi fun _ : ℕ => CEν) _ = (Measure.infinitePi fun _ : ℕ => CEν) _ *
    (Measure.infinitePi fun _ : ℕ => CEν) _
  rw [hmp.measure_preimage (hs.prod ht).nullMeasurableSet,
    hmp.measure_preimage (hs.prod MeasurableSet.univ).nullMeasurableSet,
    hmp.measure_preimage (MeasurableSet.univ.prod ht).nullMeasurableSet,
    CEν_eq_prod, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, measure_univ,
    mul_one, one_mul]

/-- The counterexample sequence is i.i.d. and integrable (it is even bounded). -/
theorem CEA_isIID : IsIID CEA CEμ where
  meas := measurable_CEA
  indep := CEA_indep
  ident := CEA_identDistrib
  integrable i j := by
    refine Integrable.mono' (integrable_const 1)
      (((measurable_entry i j).comp (measurable_CEA 0)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    simpa [Real.norm_eq_abs] using CEA_bounded 0 ω i j

/-- The integral of a function of the first coordinate. -/
lemma integral_eval_zero (g : Bool × Bool → ℝ) :
    ∫ ω, g (ω 0) ∂CEμ = ∫ b, g b ∂CEν := by
  have h0 : CEμ.map (Function.eval 0) = CEν := (measurePreserving_eval_infinitePi _ 0).map_eq
  rw [← h0, integral_map (measurable_pi_apply 0).aemeasurable
    (Measurable.of_discrete (f := g)).aestronglyMeasurable]

/-- The counterexample sequence is centered. -/
theorem CEA_centered : meanMatrix CEA CEμ = 0 := by
  ext i j
  have hrw : ∫ ω, CEA 0 ω i j ∂CEμ = ∫ b, CEmat b i j ∂CEν :=
    integral_eval_zero (fun b => CEmat b i j)
  simp only [meanMatrix, Matrix.of_apply, Matrix.zero_apply]
  rw [hrw, CEν, PMF.integral_eq_sum]
  fin_cases i <;> fin_cases j <;>
    simp [Fintype.sum_prod_type, CEmat, M3, sgn] <;> norm_num

/-- The partial sums of the counterexample are again of the form `M(x,y)`. -/
lemma partialSum_CEA (N : ℕ) (ω : CEΩ) :
    partialSum CEA N ω =
      M3 (∑ k ∈ Finset.range N, sgn (ω k).1) (∑ k ∈ Finset.range N, sgn (ω k).2) := by
  induction N with
  | zero => simp [partialSum, M3_zero]
  | succ n ih =>
    simp only [partialSum, Finset.sum_range_succ] at ih ⊢
    rw [ih]
    exact M3_add _ _ _ _

/-- Every partial sum of the counterexample is singular, everywhere on `Ω`. -/
theorem CEA_det_partialSum (N : ℕ) (ω : CEΩ) : (partialSum CEA N ω).det = 0 := by
  rw [partialSum_CEA, M3_det]

/-- The counterexample satisfies property `(P)` (indeed with probability one). -/
theorem CEA_propP : PropP CEA CEμ := by
  refine ⟨1 / 2, by norm_num, by norm_num, fun p => ?_⟩
  have hset : singularEvent CEA (p + 1) = Set.univ := by
    ext ω
    simp [singularEvent, CEA_det_partialSum]
  rw [hset, measure_univ]
  norm_num

/-- The common kernel of the two support matrices `M(1,1)` and `M(1,-1)` is trivial. -/
theorem M3_common_kernel_trivial (x : Fin 3 → ℝ) (h1 : (M3 1 1) *ᵥ x = 0)
    (h2 : (M3 1 (-1)) *ᵥ x = 0) : x = 0 := by
  have e1 := congrFun h1 0
  have e2 := congrFun h1 1
  have e3 := congrFun h2 0
  simp [M3_mulVec] at e1 e2 e3
  funext i
  fin_cases i <;> simp <;> linarith

/-- **The `3 × 3` obstruction.** There is *no* deterministic nonzero vector annihilated almost
surely by `A 0`, although every partial sum is singular. -/
theorem CEA_no_deterministic_kernel_vector (x : Fin 3 → ℝ) (hx : x ≠ 0) :
    CEμ {ω | (CEA 0 ω) *ᵥ x = 0} ≠ 1 := by
  obtain ⟨b, hb⟩ : ∃ b : Bool × Bool, (CEmat b) *ᵥ x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine hx (M3_common_kernel_trivial x ?_ ?_)
    · simpa [CEmat, sgn] using hcon (true, true)
    · simpa [CEmat, sgn] using hcon (true, false)
  intro hcon
  set S : Set (Bool × Bool) := {c | (CEmat c) *ᵥ x = 0} with hS
  have hSmeas : MeasurableSet S := MeasurableSet.of_discrete
  have hpre : {ω : CEΩ | (CEA 0 ω) *ᵥ x = 0} = (Function.eval 0) ⁻¹' S := rfl
  have hmp := (measurePreserving_eval_infinitePi (fun _ : ℕ => CEν) 0).measure_preimage
    hSmeas.nullMeasurableSet
  rw [hpre] at hcon
  have hν : CEν S = 1 := by rw [← hmp]; exact hcon
  have hcompl : CEν Sᶜ = 0 := by
    rw [prob_compl_eq_zero_iff hSmeas]; exact hν
  have hbmem : ({b} : Set (Bool × Bool)) ⊆ Sᶜ := by
    intro c hc
    simp only [Set.mem_singleton_iff] at hc
    subst hc
    exact hb
  have hb0 : CEν {b} = 0 := measure_mono_null hbmem hcompl
  rw [CEν, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete] at hb0
  simp [PMF.uniformOfFintype_apply] at hb0

end Obligation3

section Obligation4

/-! ### 4. Part (b): a checked sufficient-hypothesis theorem -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {d : ℕ}
  {A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ}

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Left multiplication by a fixed matrix multiplies the determinant of every partial sum by
`det H`. -/
theorem det_partialSum_matrix_mul (H : Matrix (Fin d) (Fin d) ℝ) (N : ℕ) (ω : Ω) :
    (partialSum (fun n ω => H * A n ω) N ω).det = H.det * (partialSum A N ω).det := by
  have hHS : partialSum (fun n ω => H * A n ω) N ω = H * partialSum A N ω := by
    simp [partialSum, Finset.mul_sum]
  rw [hHS, Matrix.det_mul]

omit [IsProbabilityMeasure μ] in
/-- Left multiplication by a fixed matrix preserves the i.i.d. hypotheses. -/
theorem isIID_matrix_mul (h : IsIID A μ) (H : Matrix (Fin d) (Fin d) ℝ) :
    IsIID (fun n ω => H * A n ω) μ where
  meas n := (measurable_matrix_mul H).comp (h.meas n)
  indep := h.indep.comp (fun _ B => H * B) (fun _ => measurable_matrix_mul H)
  ident n := (h.ident n).comp (measurable_matrix_mul H)
  integrable i j := by
    simp only [Matrix.mul_apply]
    exact integrable_finset_sum _ fun k _ => (h.integrable k j).const_mul _

omit [IsProbabilityMeasure μ] in
/-- Left multiplication by an invertible matrix preserves property `(P)`. -/
theorem propP_matrix_mul (H : Matrix (Fin d) (Fin d) ℝ) (hH : H.det ≠ 0) (hP : PropP A μ) :
    PropP (fun n ω => H * A n ω) μ := by
  obtain ⟨c, hc0, hc1, hc⟩ := hP
  refine ⟨c, hc0, hc1, fun p => ?_⟩
  have hset : singularEvent (fun n ω => H * A n ω) (p + 1) = singularEvent A (p + 1) := by
    ext ω
    simp only [singularEvent, Set.mem_setOf_eq, det_partialSum_matrix_mul]
    constructor
    · intro hz
      rcases mul_eq_zero.1 hz with h1 | h1
      · exact absurd h1 hH
      · exact h1
    · intro hz
      rw [hz, mul_zero]
  rw [hset]
  exact hc p

/-- **Q877 (b).** If there is a deterministic positive definite matrix `H` such that `H * A 0` is
almost surely (symmetric) positive semidefinite, then property `(P)` again produces a deterministic
nonzero vector annihilated almost surely by every `A n`. -/
theorem q877b (h : IsIID A μ) (H : Matrix (Fin d) (Fin d) ℝ) (hH : H.PosDef)
    (hHA : ∀ᵐ ω ∂μ, (H * A 0 ω).PosSemidef) (hP : PropP A μ) :
    ∃ x : Fin d → ℝ, x ≠ 0 ∧ μ {ω | ∀ n, (A n ω) *ᵥ x = 0} = 1 := by
  have hdet : H.det ≠ 0 := ne_of_gt hH.det_pos
  obtain ⟨x, hx0, hx⟩ := q877a (isIID_matrix_mul h H) hHA (propP_matrix_mul H hdet hP)
  refine ⟨x, hx0, ?_⟩
  have hset : {ω | ∀ n, (H * A n ω) *ᵥ x = 0} = {ω | ∀ n, (A n ω) *ᵥ x = 0} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hω n
      have hn := hω n
      rw [← mulVec_mulVec] at hn
      exact Matrix.eq_zero_of_mulVec_eq_zero hdet hn
    · intro hω n
      rw [← mulVec_mulVec, hω n, Matrix.mulVec_zero]
  rwa [hset] at hx

end Obligation4

section Synthesis

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {d : ℕ}
  {A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ}

/-- **Synthesis of Q877.** Under the printed i.i.d. and integrability hypotheses and property
`(P)`, each of the two structural assumptions — (a) almost sure positive semidefiniteness, or
(b) the existence of a deterministic positive definite symmetrizer — yields a deterministic
nonzero vector `x` with `μ {ω | ∀ n, A n ω *ᵥ x = 0} = 1`. The `3 × 3` obstruction
`CEA_no_deterministic_kernel_vector` shows that some such structure is genuinely needed. -/
theorem q877_synthesis (h : IsIID A μ) (hP : PropP A μ)
    (hstruct : (∀ᵐ ω ∂μ, (A 0 ω).PosSemidef) ∨
      ∃ H : Matrix (Fin d) (Fin d) ℝ, H.PosDef ∧ ∀ᵐ ω ∂μ, (H * A 0 ω).PosSemidef) :
    ∃ x : Fin d → ℝ, x ≠ 0 ∧ μ {ω | ∀ n, (A n ω) *ᵥ x = 0} = 1 := by
  rcases hstruct with hpsd | ⟨H, hH, hHA⟩
  · exact q877a h hpsd hP
  · exact q877b h H hH hHA hP

end Synthesis

section AxiomAudit

/-! ### Environment and axiom audit

Formalized with **Lean `4.28.0`** and **Mathlib at commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`** (as pinned by this project's `lean-toolchain` and
`lake-manifest.json`).

The commands below print the axioms used by the main results.  Each of them depends only on the
three standard axioms `propext`, `Classical.choice`, `Quot.sound`.  No `sorry`, `admit`, `axiom`,
`unsafe`, `native_decide` or added unproved hypothesis occurs anywhere in this file. -/

#print axioms tendsto_ae_partialSum_div
#print axioms tendsto_inProbability_partialSum_div
#print axioms tendsto_measure_singularEvent_of_det_mean_ne_zero
#print axioms q877a
#print axioms CEA_isIID
#print axioms CEA_propP
#print axioms CEA_no_deterministic_kernel_vector
#print axioms q877b
#print axioms q877_synthesis

end AxiomAudit

end Q877
