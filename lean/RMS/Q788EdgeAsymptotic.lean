/-
# Q788 — Claim B: the fixed-`n` upper-edge asymptotic

For every fixed `n ≥ 2`, as `δ → 0+`,

  `ℙ(Dₙ ≥ 2ⁿ(1-δ)) = κₙ δ^{(n-1)/2} (1 + O_n(δ))`,
  `κₙ = √n / Γ((n+1)/2) · (2/π)^{(n-1)/2}`.

The proof combines the ellipsoidal sandwich of `RequestProject.Q788Localize`, the exact
volume of the ellipsoid of `RequestProject.Q788Ellipsoid` and the slice formula of
`RequestProject.Q788Slice`.
-/
import RMS.Q788Localize

set_option maxHeartbeats 1000000

open MeasureTheory Real Set Filter
open scoped ENNReal Topology

namespace Q788

/-- `κₙ = √n / Γ((n+1)/2) · (2/π)^{(n-1)/2}`, the constant of the upper-edge asymptotic. -/
noncomputable def kappa (n : ℕ) : ℝ :=
  Real.sqrt n / Real.Gamma (((n : ℝ) + 1) / 2) * (Real.sqrt (2 / π)) ^ (n - 1)

theorem gamma_pos (m : ℕ) : 0 < Real.Gamma ((m : ℝ) / 2 + 1) :=
  Real.Gamma_pos_of_pos (by positivity)

theorem kappa_pos {n : ℕ} (hn : 1 ≤ n) : 0 < kappa n := by
  have h1 : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have h2 : 0 < Real.Gamma (((n : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h3 : 0 < Real.sqrt (2 / π) := Real.sqrt_pos.2 (by positivity)
  rw [kappa]
  positivity

/-! ## The volume of the ellipsoid as a real number -/

/-- `edgeVol m r` is the normalized `m`-dimensional volume of `{relQuad ≤ r}`, i.e. the
probability predicted by the ellipsoid. -/
noncomputable def edgeVol (m : ℕ) (r : ℝ) : ℝ :=
  Real.sqrt ((m : ℝ) + 1) * (Real.sqrt r) ^ m
    * (Real.sqrt π ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) / (2 * π) ^ m

theorem volume_relQuad_toReal {m : ℕ} (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r) :
    (volume {x : Fin m → ℝ | relQuad m x ≤ r}).toReal
      = Real.sqrt ((m : ℝ) + 1) * (Real.sqrt r) ^ m
        * (Real.sqrt π ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) := by
  have hg := gamma_pos m
  rw [volume_relQuad_le hm r hr, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (by positivity), ← mul_assoc]

theorem volume_relQuad_ne_top {m : ℕ} (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r) :
    volume {x : Fin m → ℝ | relQuad m x ≤ r} ≠ ⊤ := by
  rw [volume_relQuad_le hm r hr]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)

theorem edgeVol_nonneg (m : ℕ) (r : ℝ) : 0 ≤ edgeVol m r := by
  have hg := gamma_pos m
  have hpi := Real.pi_pos
  rw [edgeVol]
  positivity

/-! ## The sandwich for the probability -/

/-- The probability is sandwiched between two ellipsoid volumes. -/
theorem probGE_sandwich {m : ℕ} (hm : 0 < m) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 100)
    (hδm : δ * ((m : ℝ) + 2) ≤ 1 / 4) :
    edgeVol m (8 * (δ - δ ^ 2)) ≤ probGE (m + 1) (2 ^ (m + 1) * (1 - δ)) ∧
      probGE (m + 1) (2 ^ (m + 1) * (1 - δ))
        ≤ edgeVol m (8 * δ + (8 + 7 * ((m : ℝ) + 1)) * δ ^ 2) := by
  have hpi := Real.pi_pos
  have hpi3 : 3 < π := Real.pi_gt_three
  set c' : Fin m → ℝ := fun _ => -π with hc'
  set S : Set (Fin m → ℝ) :=
    {y : Fin m → ℝ | 2 ^ (m + 1) * (1 - δ) ≤ chordMax (Fin.cons 0 y)} with hS
  have hprob := probGE_eq_slice_volume (n := m) (2 ^ (m + 1) * (1 - δ)) c'
  set rm : ℝ := 8 * (δ - δ ^ 2) with hrm
  set rp : ℝ := 8 * δ + (8 + 7 * ((m : ℝ) + 1)) * δ ^ 2 with hrp
  have hrm0 : 0 ≤ rm := by rw [hrm]; nlinarith
  have hrp0 : 0 ≤ rp := by rw [hrp]; positivity
  have hrmle : rm ≤ 8 * δ := by rw [hrm]; nlinarith
  have hbox : ∀ y : Fin m → ℝ, y ∈ angleBox c' ↔ ∀ j, -π ≤ y j ∧ y j < π := by
    intro y
    simp only [angleBox, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ico, hc']
    constructor
    · intro h j; exact ⟨(h j).1, by linarith [(h j).2]⟩
    · intro h j; exact ⟨(h j).1, by linarith [(h j).2]⟩
  have hinner : {x : Fin m → ℝ | relQuad m x ≤ rm} ⊆ S ∩ angleBox c' := by
    intro y hy
    have hy' : relQuad m y ≤ rm := hy
    have hsmall : ∀ j, |y j| ≤ 4 * Real.sqrt δ := by
      intro j
      have h1 : (y j) ^ 2 ≤ 2 * rm := le_trans (sq_le_two_mul_relQuad y j) (by linarith)
      have h2 : (y j) ^ 2 ≤ 16 * δ := by nlinarith
      have h3 : |y j| ≤ Real.sqrt (16 * δ) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt h2
      have h4 : Real.sqrt (16 * δ) = 4 * Real.sqrt δ := by
        rw [show (16 : ℝ) * δ = 4 ^ 2 * δ by ring, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num)]
      rwa [h4] at h3
    have hsq : Real.sqrt δ ≤ 1 / 10 := by
      have hd : δ ≤ (1 / 10 : ℝ) ^ 2 := by norm_num; linarith
      have := Real.sqrt_le_sqrt hd
      rwa [Real.sqrt_sq (by norm_num)] at this
    refine ⟨chordMax_cons_ge_of_relQuad_le y δ hδ0.le (by linarith) hy', ?_⟩
    rw [hbox]
    intro j
    have h5 := abs_le.1 (hsmall j)
    constructor <;> nlinarith
  have houter : S ∩ angleBox c' ⊆ {x : Fin m → ℝ | relQuad m x ≤ rp} := by
    rintro y ⟨hy1, hy2⟩
    have hy : ∀ j, |y j| ≤ π := by
      intro j
      rw [hbox] at hy2
      exact abs_le.2 ⟨(hy2 j).1, (hy2 j).2.le⟩
    exact relQuad_le_of_chordMax_cons_ge y hy δ hδ0.le hδ hδm hy1
  have hmono1 := measure_mono (μ := (volume : Measure (Fin m → ℝ))) hinner
  have hmono2 := measure_mono (μ := (volume : Measure (Fin m → ℝ))) houter
  have hfin : volume (S ∩ angleBox c') ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_relQuad_ne_top hm rp hrp0) hmono2
  have htoReal1 : (volume {x : Fin m → ℝ | relQuad m x ≤ rm}).toReal
      ≤ (volume (S ∩ angleBox c')).toReal := ENNReal.toReal_mono hfin hmono1
  have htoReal2 : (volume (S ∩ angleBox c')).toReal
      ≤ (volume {x : Fin m → ℝ | relQuad m x ≤ rp}).toReal :=
    ENNReal.toReal_mono (volume_relQuad_ne_top hm rp hrp0) hmono2
  rw [volume_relQuad_toReal hm rm hrm0] at htoReal1
  rw [volume_relQuad_toReal hm rp hrp0] at htoReal2
  have hdiv : (0 : ℝ) < (2 * π) ^ m := by positivity
  refine ⟨?_, ?_⟩
  · rw [hprob, edgeVol]
    exact div_le_div_of_nonneg_right htoReal1 hdiv.le
  · rw [hprob, edgeVol]
    exact div_le_div_of_nonneg_right htoReal2 hdiv.le

/-! ## Identification of the leading term -/

theorem sqrt_eight_mul_sqrt_pi : Real.sqrt 8 * Real.sqrt π / (2 * π) = Real.sqrt (2 / π) := by
  have hpi := Real.pi_pos
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  have hdiv : Real.sqrt (2 / π) = Real.sqrt 2 / Real.sqrt π :=
    Real.sqrt_div (by norm_num) π
  have hp : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt hpi.le
  have hpne : Real.sqrt π ≠ 0 := by positivity
  rw [h8, hdiv]
  field_simp
  nlinarith [hp]

theorem edgeVol_eight_mul (m : ℕ) (δ : ℝ) :
    edgeVol m (8 * δ) = kappa (m + 1) * (Real.sqrt δ) ^ m := by
  have hpi := Real.pi_pos
  have hg := gamma_pos m
  have hsplit : Real.sqrt (8 * δ) = Real.sqrt 8 * Real.sqrt δ :=
    Real.sqrt_mul (by norm_num) δ
  rw [edgeVol, kappa, hsplit, Nat.add_sub_cancel,
    show (((m + 1 : ℕ) : ℝ) + 1) / 2 = (m : ℝ) / 2 + 1 by push_cast; ring,
    show (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 by push_cast; ring,
    ← sqrt_eight_mul_sqrt_pi, div_pow, mul_pow, mul_pow]
  have h2p : ((2 : ℝ) * π) ^ m ≠ 0 := by positivity
  field_simp
  ring

/-- Rescaling the radius by a factor `1 + u` multiplies the ellipsoid volume by
`(√(1+u))^m`. -/
theorem edgeVol_scale (m : ℕ) (r u : ℝ) (hr : 0 ≤ r) :
    edgeVol m (r * (1 + u)) = edgeVol m r * (Real.sqrt (1 + u)) ^ m := by
  rw [edgeVol, edgeVol, Real.sqrt_mul hr, mul_pow]
  ring

/-! ## Elementary inequalities for the relative error -/

theorem pow_one_add_le (m : ℕ) (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 + u) ^ m ≤ 1 + (2 ^ m - 1) * u := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hk : (0 : ℝ) ≤ 2 ^ k - 1 := by
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      linarith
    have hpos : (0 : ℝ) ≤ 1 + u := by linarith
    calc (1 + u) ^ (k + 1) = (1 + u) ^ k * (1 + u) := by ring
      _ ≤ (1 + (2 ^ k - 1) * u) * (1 + u) := by
          exact mul_le_mul_of_nonneg_right ih hpos
      _ ≤ 1 + (2 ^ (k + 1) - 1) * u := by
          have hsq : u * u ≤ u := by nlinarith
          have : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
          nlinarith

theorem sqrt_pow_lower (m : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    1 - m * δ ≤ (Real.sqrt (1 - δ)) ^ m := by
  have h0 : (0 : ℝ) ≤ 1 - δ := by linarith
  have hle : (1 - δ) ≤ Real.sqrt (1 - δ) := by
    have h := Real.sqrt_le_sqrt (show (1 - δ) ^ 2 ≤ 1 - δ by nlinarith)
    rwa [Real.sqrt_sq h0] at h
  have hb : 1 + (m : ℝ) * (-δ) ≤ (1 + (-δ)) ^ m :=
    one_add_mul_le_pow (by linarith) m
  have hmono : (1 - δ) ^ m ≤ (Real.sqrt (1 - δ)) ^ m := pow_le_pow_left₀ h0 hle m
  have : 1 - (m : ℝ) * δ ≤ (1 - δ) ^ m := by
    have : (1 : ℝ) + (-δ) = 1 - δ := by ring
    rw [this] at hb
    linarith
  linarith

theorem sqrt_pow_upper (m : ℕ) (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    (Real.sqrt (1 + u)) ^ m ≤ 1 + (2 ^ m - 1) * u := by
  have h1 : Real.sqrt (1 + u) ≤ 1 + u := by
    nlinarith [Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 + u), Real.sqrt_nonneg (1 + u),
      Real.one_le_sqrt.2 (by linarith : (1:ℝ) ≤ 1 + u)]
  have h2 : (Real.sqrt (1 + u)) ^ m ≤ (1 + u) ^ m :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 m
  exact h2.trans (pow_one_add_le m u hu hu1)

/-! ## Claim B -/

/-- **Claim B, quantitative form.**  For every fixed `n ≥ 2` there are a constant `C` and a
threshold `δ₀ > 0` such that for `0 < δ ≤ δ₀`

  `|ℙ(Dₙ ≥ 2ⁿ(1-δ)) - κₙ (√δ)^{n-1}| ≤ C δ · κₙ (√δ)^{n-1}`,

i.e. the asymptotic `ℙ(Dₙ ≥ 2ⁿ(1-δ)) = κₙ δ^{(n-1)/2}(1 + O_n(δ))`. -/
theorem upperEdge_rel_error {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      |probGE n (2 ^ n * (1 - δ)) - kappa n * (Real.sqrt δ) ^ (n - 1)|
        ≤ C * δ * (kappa n * (Real.sqrt δ) ^ (n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 0 < m := by omega
  set w : ℝ := (8 + 7 * ((m : ℝ) + 1)) / 8 with hw
  have hw1 : 1 ≤ w := by
    rw [hw]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hwpos : 0 < w := by linarith
  have h2m : (0 : ℝ) ≤ 2 ^ m - 1 := by
    have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    linarith
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine ⟨(m : ℝ) + (2 ^ m - 1) * w + 1, by nlinarith, ?_⟩
  refine ⟨min (1 / 100) (min (1 / (4 * ((m : ℝ) + 2))) (1 / w)), ?_, ?_⟩
  · have : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    positivity
  intro δ hδ0 hδle
  have hδ100 : δ ≤ 1 / 100 := le_trans hδle (min_le_left _ _)
  have hδm4 : δ ≤ 1 / (4 * ((m : ℝ) + 2)) :=
    le_trans hδle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδw : δ ≤ 1 / w := le_trans hδle (le_trans (min_le_right _ _) (min_le_right _ _))
  have hm2 : (0 : ℝ) < 4 * ((m : ℝ) + 2) := by positivity
  have hδm : δ * ((m : ℝ) + 2) ≤ 1 / 4 := by
    rw [le_div_iff₀ hm2] at hδm4
    nlinarith
  have hwδ : w * δ ≤ 1 := by
    rw [le_div_iff₀ hwpos] at hδw
    nlinarith
  have hwδ0 : 0 ≤ w * δ := by positivity
  -- the leading term
  set L : ℝ := kappa (m + 1) * (Real.sqrt δ) ^ m with hL
  have hLnn : 0 ≤ L := by
    have := kappa_pos (n := m + 1) (by omega)
    rw [hL]; positivity
  have hLeq : edgeVol m (8 * δ) = L := edgeVol_eight_mul m δ
  obtain ⟨hlow, hhigh⟩ := probGE_sandwich hm δ hδ0 hδ100 hδm
  -- lower bound
  have hrm : 8 * (δ - δ ^ 2) = (8 * δ) * (1 + (-δ)) := by ring
  have hlow' : L * (1 - (m : ℝ) * δ) ≤ probGE (m + 1) (2 ^ (m + 1) * (1 - δ)) := by
    refine le_trans ?_ hlow
    rw [hrm, edgeVol_scale m (8 * δ) (-δ) (by positivity), hLeq]
    have := sqrt_pow_lower m δ hδ0.le (by linarith)
    have hs : (1 : ℝ) + -δ = 1 - δ := by ring
    rw [hs]
    exact mul_le_mul_of_nonneg_left this hLnn
  -- upper bound
  have hrp : 8 * δ + (8 + 7 * ((m : ℝ) + 1)) * δ ^ 2 = (8 * δ) * (1 + w * δ) := by
    rw [hw]; ring
  have hhigh' : probGE (m + 1) (2 ^ (m + 1) * (1 - δ)) ≤ L * (1 + (2 ^ m - 1) * (w * δ)) := by
    refine le_trans hhigh ?_
    rw [hrp, edgeVol_scale m (8 * δ) (w * δ) (by positivity), hLeq]
    exact mul_le_mul_of_nonneg_left (sqrt_pow_upper m (w * δ) hwδ0 hwδ) hLnn
  -- conclusion
  have hC : (0 : ℝ) ≤ (m : ℝ) + (2 ^ m - 1) * w + 1 := by nlinarith
  have hkey1 : L - ((m : ℝ) + (2 ^ m - 1) * w + 1) * δ * L
      ≤ probGE (m + 1) (2 ^ (m + 1) * (1 - δ)) := by
    refine le_trans ?_ hlow'
    nlinarith [mul_nonneg (mul_nonneg h2m hwpos.le) (mul_nonneg hδ0.le hLnn)]
  have hkey2 : probGE (m + 1) (2 ^ (m + 1) * (1 - δ))
      ≤ L + ((m : ℝ) + (2 ^ m - 1) * w + 1) * δ * L := by
    refine le_trans hhigh' ?_
    nlinarith [mul_nonneg (mul_nonneg hmnn hδ0.le) hLnn, mul_nonneg hδ0.le hLnn]
  rw [show ((m + 1 : ℕ) - 1) = m by omega, ← hL]
  rw [abs_le]
  constructor <;> linarith

/-- **Claim B, ratio form.**  For every fixed `n ≥ 2` the ratio of `ℙ(Dₙ ≥ 2ⁿ(1-δ))` to
`κₙ δ^{(n-1)/2}` tends to `1` as `δ → 0+`. -/
theorem upperEdge_ratio_tendsto {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun δ : ℝ => probGE n (2 ^ n * (1 - δ)) / (kappa n * (Real.sqrt δ) ^ (n - 1)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  obtain ⟨C, hC, δ₀, hδ₀, hbound⟩ := upperEdge_rel_error hn
  have hκ : 0 < kappa n := kappa_pos (by omega)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min (ε / (C + 1)) δ₀, lt_min (by positivity) hδ₀, fun δ hδmem hδdist => ?_⟩
  have hδ0 : 0 < δ := hδmem
  have hdd : |δ| < min (ε / (C + 1)) δ₀ := by
    rw [Real.dist_eq, sub_zero] at hδdist
    exact hδdist
  have habs : |δ| = δ := abs_of_pos hδ0
  rw [habs] at hdd
  have hδsmall : δ < ε / (C + 1) := lt_of_lt_of_le hdd (min_le_left _ _)
  have hδδ₀ : δ ≤ δ₀ := le_of_lt (lt_of_lt_of_le hdd (min_le_right _ _))
  have hden : 0 < kappa n * (Real.sqrt δ) ^ (n - 1) := by
    have : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ0
    positivity
  have hb := hbound δ hδ0 hδδ₀
  have hCδ : C * δ < ε := by
    rw [lt_div_iff₀ (by positivity)] at hδsmall
    nlinarith
  rw [Real.dist_eq, div_sub_one hden.ne', abs_div, abs_of_pos hden, div_lt_iff₀ hden]
  calc |probGE n (2 ^ n * (1 - δ)) - kappa n * (Real.sqrt δ) ^ (n - 1)|
      ≤ C * δ * (kappa n * (Real.sqrt δ) ^ (n - 1)) := hb
    _ < ε * (kappa n * (Real.sqrt δ) ^ (n - 1)) := by
        exact mul_lt_mul_of_pos_right hCδ hden

/-! ## The `rpow` formulation and the `α ↑ 2ⁿ` form -/

/-- `(√δ)^{n-1} = δ^{(n-1)/2}`. -/
theorem sqrt_pow_eq_rpow {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    (Real.sqrt δ) ^ (n - 1) = δ ^ (((n : ℝ) - 1) / 2) := by
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : (1 : ℕ) ≤ n := hn
    push_cast [Nat.cast_sub this]
    ring
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (δ ^ (1 / (2 : ℝ))) (n - 1),
    ← Real.rpow_mul hδ.le, hcast]
  ring_nf

/-- `κₙ = √n / Γ((n+1)/2) · (2/π)^{(n-1)/2}`, in `rpow` form. -/
theorem kappa_eq_rpow {n : ℕ} (hn : 1 ≤ n) :
    kappa n = Real.sqrt n / Real.Gamma (((n : ℝ) + 1) / 2) * (2 / π) ^ (((n : ℝ) - 1) / 2) := by
  have hpi := Real.pi_pos
  rw [kappa, sqrt_pow_eq_rpow hn (by positivity : (0 : ℝ) < 2 / π)]

/-- **Claim B in `rpow` form**: `ℙ(Dₙ ≥ 2ⁿ(1-δ)) = κₙ δ^{(n-1)/2}(1 + O_n(δ))`. -/
theorem upperEdge_rel_error_rpow {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      |probGE n (2 ^ n * (1 - δ)) - kappa n * δ ^ (((n : ℝ) - 1) / 2)|
        ≤ C * δ * (kappa n * δ ^ (((n : ℝ) - 1) / 2)) := by
  obtain ⟨C, hC, δ₀, hδ₀, hbound⟩ := upperEdge_rel_error hn
  refine ⟨C, hC, δ₀, hδ₀, fun δ hδ0 hδle => ?_⟩
  rw [← sqrt_pow_eq_rpow (by omega) hδ0]
  exact hbound δ hδ0 hδle

/-- **Claim B, the `α ↑ 2ⁿ` form.**  With `δ = (2ⁿ - α)/2ⁿ`, the ratio of `ℙ(Dₙ ≥ α)` to
`κₙ δ^{(n-1)/2}` tends to `1` as `α` increases to `2ⁿ`. -/
theorem upperEdge_ratio_tendsto_alpha {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun α : ℝ =>
        probGE n α / (kappa n * (Real.sqrt ((2 ^ n - α) / 2 ^ n)) ^ (n - 1)))
      (𝓝[<] ((2 : ℝ) ^ n)) (𝓝 1) := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hmap : Tendsto (fun α : ℝ => ((2 : ℝ) ^ n - α) / 2 ^ n) (𝓝[<] ((2 : ℝ) ^ n))
      (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun α : ℝ => ((2 : ℝ) ^ n - α) / 2 ^ n := by fun_prop
      have := hc.tendsto ((2 : ℝ) ^ n)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with α hα
      have : α < (2 : ℝ) ^ n := hα
      exact div_pos (by linarith) h2
  have hcomp := (upperEdge_ratio_tendsto hn).comp hmap
  refine hcomp.congr fun α => ?_
  simp only [Function.comp_apply]
  congr 2
  field_simp
  ring

end Q788
