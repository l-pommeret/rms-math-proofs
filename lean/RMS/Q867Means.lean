import RMS.Q867Fejer

/-!
# Dyadic mean-value functionals on `ℓ^∞(ℤ)`

We construct a uniformly bounded sequence of linear functionals `ξ n` on `ℓ^∞(ℤ)` with
the following three properties.

* `‖ξ n a‖ ≤ 2 ‖a‖`;
* `ξ n a → 0` as `n → ∞` for every almost periodic `a` (i.e. every `a` in the closed
  span `AP` of the characters `k ↦ exp (i θ k)`);
* `ξ n (Sseq x) = x n` for every `x ∈ c₀`.

They are obtained by averaging over translations by multiples of `2 ^ N` and letting
`N → ∞`; the (possibly non-convergent) limits are taken along a fixed ultrafilter
refining the filter `atTop`.
-/

noncomputable section

open Filter Topology Complex BoundedContinuousFunction

namespace Q867

/-! ### Limits along a fixed ultrafilter refining `atTop` -/

/-- A fixed ultrafilter on `ℕ` refining `atTop`. -/
def Uf : Ultrafilter ℕ := Ultrafilter.of atTop

lemma Uf_le_atTop : (Uf : Filter ℕ) ≤ atTop := Ultrafilter.of_le _

/-- The limit of a sequence of complex numbers along `Uf` (junk value if unbounded). -/
def ulim (f : ℕ → ℂ) : ℂ := lim (Filter.map f (Uf : Filter ℕ))

lemma tendsto_ulim {f : ℕ → ℂ} {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) :
    Tendsto f (Uf : Filter ℕ) (𝓝 (ulim f)) := by
  have hcpt : IsCompact (Metric.closedBall (0 : ℂ) C) := isCompact_closedBall _ _
  have hle : ((Ultrafilter.map f Uf) : Filter ℂ) ≤ 𝓟 (Metric.closedBall (0 : ℂ) C) := by
    rw [le_principal_iff]
    exact Filter.mem_map.2 (Filter.Eventually.of_forall (fun n => by
      simpa [Metric.mem_closedBall] using hf n))
  obtain ⟨a, -, ha⟩ := hcpt.ultrafilter_le_nhds (Ultrafilter.map f Uf) hle
  exact le_nhds_lim ⟨a, ha⟩

lemma ulim_eq_of_tendstoUf {f : ℕ → ℂ} {c : ℂ} (h : Tendsto f (Uf : Filter ℕ) (𝓝 c)) :
    ulim f = c :=
  tendsto_nhds_unique (le_nhds_lim ⟨c, h⟩) h

lemma ulim_add {f g : ℕ → ℂ} {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ulim (fun n => f n + g n) = ulim f + ulim g :=
  ulim_eq_of_tendstoUf ((tendsto_ulim hf).add (tendsto_ulim hg))

lemma ulim_smul (c : ℂ) {f : ℕ → ℂ} {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) :
    ulim (fun n => c * f n) = c * ulim f :=
  ulim_eq_of_tendstoUf ((tendsto_ulim hf).const_mul c)

lemma norm_ulim_le {f : ℕ → ℂ} {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) : ‖ulim f‖ ≤ C :=
  le_of_tendsto ((tendsto_ulim hf).norm) (Filter.Eventually.of_forall hf)

lemma ulim_eq_of_eventually {f : ℕ → ℂ} {c : ℂ} (h : ∀ᶠ n in atTop, f n = c) : ulim f = c := by
  refine ulim_eq_of_tendstoUf ?_
  have h' : ∀ᶠ n in (Uf : Filter ℕ), f n = c := Uf_le_atTop h
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [h'] with n hn using hn.symm

lemma ulim_eq_of_tendsto {f : ℕ → ℂ} {c : ℂ} (h : Tendsto f atTop (𝓝 c)) : ulim f = c :=
  ulim_eq_of_tendstoUf (h.mono_left Uf_le_atTop)

lemma ulim_const (c : ℂ) : ulim (fun _ => c) = c :=
  ulim_eq_of_eventually (Filter.Eventually.of_forall (fun _ => rfl))

lemma norm_ulim_sub_le {f : ℕ → ℂ} {c : ℂ} {C ε : ℝ} (hf : ∀ n, ‖f n‖ ≤ C)
    (h : ∀ᶠ n in atTop, ‖f n - c‖ ≤ ε) : ‖ulim f - c‖ ≤ ε := by
  have ht : Tendsto (fun n => f n - c) (Uf : Filter ℕ) (𝓝 (ulim f - c)) :=
    (tendsto_ulim hf).sub tendsto_const_nhds
  exact le_of_tendsto ht.norm (Uf_le_atTop h)

/-! ### The functionals `ξ n` -/

/-- The averaged difference `(1/M) ∑_{s<M} (a (2^n + 2^N s) - a (2^N s))`. -/
def avg (N M n : ℕ) (a : ℤ →ᵇ ℂ) : ℂ :=
  (M : ℂ)⁻¹ * ∑ s ∈ Finset.range M,
    (a ((2 : ℤ) ^ n + (2 : ℤ) ^ N * s) - a ((2 : ℤ) ^ N * s))

lemma avg_add (N M n : ℕ) (a b : ℤ →ᵇ ℂ) :
    avg N M n (a + b) = avg N M n a + avg N M n b := by
  simp only [avg, coe_add, Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
  exact congrArg _ (Finset.sum_congr rfl fun s _ => by ring)

lemma avg_smul (N M n : ℕ) (c : ℂ) (a : ℤ →ᵇ ℂ) :
    avg N M n (c • a) = c * avg N M n a := by
  simp only [avg, BoundedContinuousFunction.coe_smul, smul_eq_mul, Finset.mul_sum, ← mul_assoc]
  exact Finset.sum_congr rfl fun s _ => by ring

lemma norm_avg_le (N M n : ℕ) (a : ℤ →ᵇ ℂ) : ‖avg N M n a‖ ≤ 2 * ‖a‖ := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [avg]
  have h1 : ‖∑ s ∈ Finset.range M, (a ((2:ℤ) ^ n + (2:ℤ) ^ N * s) - a ((2:ℤ) ^ N * s))‖
      ≤ M * (2 * ‖a‖) := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ s ∈ Finset.range M, ‖a ((2:ℤ) ^ n + (2:ℤ) ^ N * s) - a ((2:ℤ) ^ N * s)‖
        ≤ ∑ _s ∈ Finset.range M, (2 * ‖a‖) := by
          refine Finset.sum_le_sum fun s _ => ?_
          refine le_trans (norm_sub_le _ _) ?_
          have := a.norm_coe_le_norm ((2:ℤ) ^ n + (2:ℤ) ^ N * s)
          have := a.norm_coe_le_norm ((2:ℤ) ^ N * s)
          linarith
      _ = M * (2 * ‖a‖) := by simp [Finset.sum_const]
  rw [avg, norm_mul, norm_inv, Complex.norm_natCast]
  rw [inv_mul_le_iff₀ (by positivity)]
  linarith [h1]

/-- The `n`-th dyadic mean-value functional. -/
def xi (n : ℕ) (a : ℤ →ᵇ ℂ) : ℂ := ulim (fun N => ulim (fun M => avg N M n a))

lemma norm_xi_le (n : ℕ) (a : ℤ →ᵇ ℂ) : ‖xi n a‖ ≤ 2 * ‖a‖ :=
  norm_ulim_le (fun N => norm_ulim_le (fun M => norm_avg_le N M n a))

lemma xi_add (n : ℕ) (a b : ℤ →ᵇ ℂ) : xi n (a + b) = xi n a + xi n b := by
  set C := 2 * ‖a‖ + 2 * ‖b‖ with hC
  have hba : ∀ N M, ‖avg N M n a‖ ≤ C := fun N M =>
    le_trans (norm_avg_le N M n a) (by simp [hC])
  have hbb : ∀ N M, ‖avg N M n b‖ ≤ C := fun N M =>
    le_trans (norm_avg_le N M n b) (by simp [hC])
  have hinner : ∀ N, ulim (fun M => avg N M n (a + b))
      = ulim (fun M => avg N M n a) + ulim (fun M => avg N M n b) := by
    intro N
    simp only [avg_add]
    exact ulim_add (C := C) (hba N) (hbb N)
  unfold xi
  simp only [hinner]
  exact ulim_add (C := C) (fun N => norm_ulim_le (hba N)) (fun N => norm_ulim_le (hbb N))

lemma xi_smul (n : ℕ) (c : ℂ) (a : ℤ →ᵇ ℂ) : xi n (c • a) = c * xi n a := by
  have hinner : ∀ N, ulim (fun M => avg N M n (c • a)) = c * ulim (fun M => avg N M n a) := by
    intro N
    simp only [avg_smul]
    exact ulim_smul c (C := 2 * ‖a‖) (fun M => norm_avg_le N M n a)
  unfold xi
  simp only [hinner]
  exact ulim_smul c (C := 2 * ‖a‖) (fun N => norm_ulim_le (fun M => norm_avg_le N M n a))

lemma xi_zero (n : ℕ) : xi n 0 = 0 := by simpa using xi_smul n 0 0

/-! ### Almost periodic sequences -/

/-- The character `k ↦ exp (i θ k)` as an element of `ℓ^∞(ℤ)`. -/
def charSeq (θ : ℝ) : ℤ →ᵇ ℂ :=
  ofNormedAddCommGroupDiscrete (fun k : ℤ => Complex.exp (θ * k * I)) 1
    (fun k => by
      rw [Complex.norm_exp]
      norm_num)

@[simp] lemma charSeq_apply (θ : ℝ) (k : ℤ) : charSeq θ k = Complex.exp (θ * k * I) := rfl

/-- The space `AP(ℤ)` of (uniformly) almost periodic sequences: the closed span of the
characters. -/
def AP : Submodule ℂ (ℤ →ᵇ ℂ) := (Submodule.span ℂ (Set.range charSeq)).topologicalClosure

lemma charSeq_mem_AP (θ : ℝ) : charSeq θ ∈ AP :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨θ, rfl⟩)

lemma AP_isClosed : IsClosed (AP : Set (ℤ →ᵇ ℂ)) := Submodule.isClosed_topologicalClosure _

lemma charSeq_add (θ : ℝ) (j k : ℤ) : charSeq θ (j + k) = charSeq θ j * charSeq θ k := by
  simp only [charSeq_apply, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma charSeq_mul_nat (θ : ℝ) (k : ℤ) (s : ℕ) : charSeq θ (k * s) = (charSeq θ k) ^ s := by
  simp only [charSeq_apply, ← Complex.exp_nat_mul]
  congr 1; push_cast; ring

lemma norm_charSeq (θ : ℝ) (k : ℤ) : ‖charSeq θ k‖ = 1 := by
  rw [charSeq_apply, Complex.norm_exp]
  norm_num

lemma avg_charSeq_eq (θ : ℝ) (N M n : ℕ) :
    avg N M n (charSeq θ) = (M : ℂ)⁻¹ *
      ((charSeq θ ((2:ℤ)^n) - 1) * ∑ s ∈ Finset.range M, (charSeq θ ((2:ℤ)^N)) ^ s) := by
  rw [avg]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by rw [charSeq_add, charSeq_mul_nat]; ring

/-- If the frequency is "dyadic at level `n`", the `n`-th functional kills the character. -/
lemma xi_charSeq_zero_of_one {θ : ℝ} {n : ℕ} (h : charSeq θ ((2:ℤ)^n) = 1) :
    xi n (charSeq θ) = 0 := by
  have h0 : ∀ N M, avg N M n (charSeq θ) = 0 := by
    intro N M
    rw [avg_charSeq_eq, h]
    ring
  unfold xi
  simp only [h0, ulim_const]

/-- If the frequency is not dyadic, every functional kills the character (the inner
averages genuinely converge to `0`). -/
lemma xi_charSeq_zero_of_ne {θ : ℝ} (n : ℕ) (h : ∀ N : ℕ, charSeq θ ((2:ℤ)^N) ≠ 1) :
    xi n (charSeq θ) = 0 := by
  have hinner : ∀ N : ℕ, ulim (fun M => avg N M n (charSeq θ)) = 0 := by
    intro N
    refine ulim_eq_of_tendsto ?_
    set w := charSeq θ ((2:ℤ)^N) with hw
    have hwne : w - 1 ≠ 0 := sub_ne_zero.2 (h N)
    set C : ℝ := 4 / ‖w - 1‖ with hC
    have hbound : ∀ M : ℕ, ‖avg N M n (charSeq θ)‖ ≤ C * (M:ℝ)⁻¹ := by
      intro M
      rw [avg_charSeq_eq, geom_sum_eq (h N)]
      rw [norm_mul, norm_inv, Complex.norm_natCast, norm_mul, norm_div]
      have h1 : ‖charSeq θ ((2:ℤ)^n) - 1‖ ≤ 2 := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_charSeq]; norm_num
      have h2 : ‖w ^ M - 1‖ ≤ 2 := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_pow, hw, norm_charSeq]; norm_num
      have hpos : 0 < ‖w - 1‖ := norm_pos_iff.2 hwne
      have hmain : ‖charSeq θ ((2:ℤ)^n) - 1‖ * (‖w ^ M - 1‖ / ‖w - 1‖) ≤ 4 / ‖w - 1‖ := by
        rw [div_eq_mul_inv, ← mul_assoc, div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        nlinarith [norm_nonneg (charSeq θ ((2:ℤ)^n) - 1), norm_nonneg (w ^ M - 1)]
      rw [mul_comm C]
      exact mul_le_mul_of_nonneg_left hmain (by positivity)
    refine squeeze_zero_norm hbound ?_
    simpa using tendsto_inv_atTop_nhds_zero_nat.const_mul C
  unfold xi
  simp only [hinner, ulim_const]

/-- On a character, `ξ n` vanishes for all large `n`. -/
lemma xi_charSeq_eventually_zero (θ : ℝ) : ∀ᶠ n in atTop, xi n (charSeq θ) = 0 := by
  by_cases hex : ∃ m : ℕ, charSeq θ ((2:ℤ)^m) = 1
  · obtain ⟨m, hm⟩ := hex
    filter_upwards [eventually_ge_atTop m] with n hn
    refine xi_charSeq_zero_of_one ?_
    have hsplit : ((2:ℤ)^m * ((2^(n-m) : ℕ) : ℤ)) = (2:ℤ)^n := by
      push_cast
      rw [← pow_add]
      congr 1
      omega
    rw [← hsplit, charSeq_mul_nat, hm, one_pow]
  · push_neg at hex
    exact Filter.Eventually.of_forall (fun n => xi_charSeq_zero_of_ne n hex)

lemma xi_eventually_zero_of_span {b : ℤ →ᵇ ℂ}
    (hb : b ∈ Submodule.span ℂ (Set.range charSeq)) : ∀ᶠ n in atTop, xi n b = 0 := by
  induction hb using Submodule.span_induction with
  | mem x hx => obtain ⟨θ, rfl⟩ := hx; exact xi_charSeq_eventually_zero θ
  | zero => exact Filter.Eventually.of_forall (fun n => xi_zero n)
  | add x y _ _ ihx ihy =>
      filter_upwards [ihx, ihy] with n h1 h2; rw [xi_add, h1, h2, add_zero]
  | smul c x _ ihx => filter_upwards [ihx] with n h1; rw [xi_smul, h1, mul_zero]

/-- The functionals `ξ n` tend to `0` pointwise on `AP`. -/
theorem xi_tendsto_zero {a : ℤ →ᵇ ℂ} (ha : a ∈ AP) :
    Tendsto (fun n => xi n a) atTop (𝓝 0) := by
  rw [NormedAddCommGroup.tendsto_nhds_zero]
  intro ε hε
  have hcl : a ∈ closure
      ((Submodule.span ℂ (Set.range charSeq) : Submodule ℂ (ℤ →ᵇ ℂ)) : Set (ℤ →ᵇ ℂ)) := ha
  obtain ⟨b, hb, hab⟩ := Metric.mem_closure_iff.1 hcl (ε / 4) (by linarith)
  have hnorm : ‖a - b‖ < ε / 4 := by rwa [← dist_eq_norm]
  filter_upwards [xi_eventually_zero_of_span hb] with n hn
  have hsplit : xi n a = xi n (a - b) + xi n b := by
    rw [← xi_add]; congr 1; abel
  rw [hsplit, hn, add_zero]
  calc ‖xi n (a - b)‖ ≤ 2 * ‖a - b‖ := norm_xi_le n (a - b)
    _ < ε := by linarith

/-- Sampling `F` produces almost periodic sequences. -/
theorem Rmap_mem_AP {f : E} (hf : f ∈ F) : Rmap f ∈ AP := by
  have hcl : IsClosed ((AP.comap (Rmap : E →ₗ[ℂ] (ℤ →ᵇ ℂ)) : Submodule ℂ E) : Set E) :=
    AP_isClosed.preimage Rmap.continuous
  have hsub : F ≤ AP.comap (Rmap : E →ₗ[ℂ] (ℤ →ᵇ ℂ)) := by
    refine Submodule.topologicalClosure_minimal _ ?_ hcl
    rw [Submodule.span_le]
    rintro g ⟨l, hl, hg⟩
    have heq : Rmap g = charSeq (l * hstep) := by
      ext k
      simp only [Rmap_apply, hg, expFn, charSeq_apply]
      congr 1
      push_cast
      ring
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    rw [show (Rmap : E →ₗ[ℂ] (ℤ →ᵇ ℂ)) g = Rmap g from rfl, heq]
    exact charSeq_mem_AP _
  exact hsub hf

/-! ### The dyadic valuation, revisited -/

lemma dyIdx_natCast (m : ℕ) : dyIdx (m : ℤ) = m.factorization 2 := by
  simp [dyIdx]

lemma dyIdx_add_mul {n N : ℕ} (h : n < N) (s : ℕ) :
    dyIdx ((2:ℤ)^n + (2:ℤ)^N * s) = n := by
  obtain ⟨d, rfl⟩ : ∃ d, N = n + 1 + d := ⟨N - n - 1, by omega⟩
  have he : ((2:ℤ)^n + (2:ℤ)^(n+1+d) * s) = ((2^n * (1 + 2^(1+d) * s) : ℕ) : ℤ) := by
    push_cast; ring
  rw [he, dyIdx_natCast, Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Nat.Prime.factorization_pow Nat.prime_two, Finsupp.add_apply, Finsupp.single_eq_same]
  have hodd : ¬ (2 ∣ (1 + 2^(1+d) * s)) := by
    have : 2 ∣ 2^(1+d) * s := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) s
    omega
  rw [Nat.factorization_eq_zero_of_not_dvd hodd]
  simp

lemma dyIdx_mul_ge (N : ℕ) {s : ℕ} (hs : s ≠ 0) : N ≤ dyIdx ((2:ℤ)^N * s) := by
  have he : ((2:ℤ)^N * s) = ((2^N * s : ℕ) : ℤ) := by push_cast; ring
  rw [he, dyIdx_natCast, Nat.factorization_mul (by positivity) hs]
  simp [Nat.Prime.factorization_pow Nat.prime_two]

/-- On the dyadic pullback of a null sequence, `ξ n` recovers the `n`-th entry. -/
theorem xi_Sseq {x : ℕ →ᵇ ℂ} (hx : x ∈ c0) (n : ℕ) : xi n (Sseq x) = x n := by
  have key : ∀ ε > 0, ‖xi n (Sseq x) - x n‖ ≤ 0 + ε := by
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hx ε hε
    have hxle : ∀ m ≥ N₀, ‖x m‖ ≤ ε := by
      intro m hm
      simpa [dist_eq_norm] using (hN₀ m hm).le
    rw [zero_add]
    refine norm_ulim_sub_le (C := 2 * ‖Sseq x‖)
      (fun N => norm_ulim_le (fun M => norm_avg_le _ _ _ _)) ?_
    filter_upwards [eventually_ge_atTop (max (n + 1) N₀)] with N hN
    have hnN : n < N := lt_of_lt_of_le (Nat.lt_succ_self n) (le_trans (le_max_left _ _) hN)
    have hN0N : N₀ ≤ N := le_trans (le_max_right _ _) hN
    refine norm_ulim_sub_le (C := 2 * ‖Sseq x‖) (fun M => norm_avg_le _ _ _ _) ?_
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hval : ∀ s : ℕ, Sseq x ((2:ℤ)^n + (2:ℤ)^N * s) = x n := by
      intro s
      have hne : ((2:ℤ)^n + (2:ℤ)^N * s) ≠ 0 := by positivity
      rw [Sseq_apply, if_neg hne, dyIdx_add_mul hnN]
    have hsmall : ∀ s : ℕ, ‖Sseq x ((2:ℤ)^N * s)‖ ≤ ε := by
      intro s
      rcases eq_or_ne s 0 with rfl | hs
      · simp; linarith
      · have hne : ((2:ℤ)^N * (s:ℤ)) ≠ 0 := by simp [hs]
        rw [Sseq_apply, if_neg hne]
        exact hxle _ (le_trans hN0N (dyIdx_mul_ge N hs))
    have hMne : (M:ℂ) ≠ 0 := by simp; omega
    have heq : avg N M n (Sseq x) - x n
        = -((M:ℂ)⁻¹ * ∑ s ∈ Finset.range M, Sseq x ((2:ℤ)^N * s)) := by
      rw [avg]
      simp only [hval]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_sub,
        ← mul_assoc, inv_mul_cancel₀ hMne, one_mul]
      ring
    rw [heq, norm_neg, norm_mul, norm_inv, Complex.norm_natCast]
    have hs : ‖∑ s ∈ Finset.range M, Sseq x ((2:ℤ)^N * s)‖ ≤ M * ε := by
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ s ∈ Finset.range M, ‖Sseq x ((2:ℤ)^N * s)‖ ≤ ∑ _s ∈ Finset.range M, ε :=
            Finset.sum_le_sum fun s _ => hsmall s
        _ = M * ε := by simp [Finset.sum_const]
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith
  have h0 : ‖xi n (Sseq x) - x n‖ ≤ 0 := le_of_forall_pos_le_add key
  have hz := le_antisymm h0 (norm_nonneg _)
  rwa [norm_eq_zero, sub_eq_zero] at hz

/-! ### The operator `T` -/

/-- The operator `T : E → ℓ^∞(ℕ)`, `T f = (ξ n (R f))ₙ`. -/
def Tmap : E →L[ℂ] (ℕ →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun f => ofNormedAddCommGroupDiscrete (fun n => xi n (Rmap f)) (2 * ‖Rmap f‖)
        (fun n => norm_xi_le n (Rmap f))
      map_add' := by
        intro f g
        ext n
        simpa using xi_add n (Rmap f) (Rmap g)
      map_smul' := by
        intro c f
        ext n
        simpa using xi_smul n c (Rmap f) }
    2 (by
      intro f
      refine (BoundedContinuousFunction.norm_le (by positivity)).2 (fun n => ?_)
      calc ‖xi n (Rmap f)‖ ≤ 2 * ‖Rmap f‖ := norm_xi_le n (Rmap f)
        _ ≤ 2 * ‖f‖ := by linarith [norm_Rmap_le f])

@[simp] lemma Tmap_apply (f : E) (n : ℕ) : Tmap f n = xi n (Rmap f) := rfl

end Q867
