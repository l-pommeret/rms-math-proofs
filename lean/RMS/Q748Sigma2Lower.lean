import RMS.Q748Sigma2Cone

/-!
# Q748 — the exact distance in `Σ₂`: the flat-torus lower bound

This module proves that the intrinsic distance inside the unit link `singularLink 2` (the Clifford
torus) between the normalisations of two nonzero singular `2 × 2` matrices is **at least**
`sigma2Theta A B`.  Combined with the geodesic constructed in `RequestProject.Q748Sigma2` this
gives the exact link distance, and combined with the cone bounds it gives the exact distance in
`Σ₂` for every pair of matrices (Theorem 9 of the answer).

The lower bound is proved by comparing a rectifiable path with fine polygonal approximations: on a
partition whose consecutive Clifford phases differ by at most `δ`, each chord is at least
`R θ cos (δ/2)` where `θ` is the *principal* (winding-number minimising) angle, the two phase
contributions are combined by the Minkowski inequality in the Euclidean plane, and the principal
angles add up along the partition by the triangle inequality.  Letting `δ → 0` gives the flat
factor `R = 1/√2`.
-/

open Set Metric Matrix
open scoped ENNReal NNReal Real

namespace Q748

noncomputable section Sigma2Lower

/-! ### Chords and principal angles on a circle -/

/-- The chord between two complex numbers of the same modulus `R` is `2R sin(θ/2)`, `θ` the
principal angle. -/
theorem norm_sub_eq_two_mul_sin_half {z w : ℂ} {R : ℝ} (hR : 0 < R) (hz : ‖z‖ = R) (hw : ‖w‖ = R) :
    ‖z - w‖ = 2 * R * Real.sin (complexPrincipalAngle z w / 2) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz; linarith
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw; linarith
  have hcos := cos_complexPrincipalAngle hz0 hw0
  rw [hz, hw] at hcos
  have hsq : ‖z - w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * (((starRingEnd ℂ) z) * w).re := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.mul_re]
    ring
  rw [hz, hw] at hsq
  have hre : (((starRingEnd ℂ) z) * w).re = R ^ 2 * Real.cos (complexPrincipalAngle z w) := by
    rw [hcos]; field_simp
  have hhalf : Real.cos (complexPrincipalAngle z w)
      = 1 - 2 * Real.sin (complexPrincipalAngle z w / 2) ^ 2 := by
    have h2 := Real.cos_two_mul' (complexPrincipalAngle z w / 2)
    rw [show 2 * (complexPrincipalAngle z w / 2) = complexPrincipalAngle z w by ring] at h2
    nlinarith [Real.sin_sq_add_cos_sq (complexPrincipalAngle z w / 2)]
  have hsq2 : ‖z - w‖ ^ 2 = (2 * R * Real.sin (complexPrincipalAngle z w / 2)) ^ 2 := by
    rw [hsq, hre, hhalf]; ring
  have hsin : 0 ≤ Real.sin (complexPrincipalAngle z w / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [complexPrincipalAngle_nonneg z w]
    · linarith [complexPrincipalAngle_le_pi z w, Real.pi_pos]
  nlinarith [norm_nonneg (z - w),
    mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hR.le) hsin]

/-- A chord bounds the principal angle from above. -/
theorem complexPrincipalAngle_le_of_norm_sub {z w : ℂ} {R : ℝ} (hR : 0 < R) (hz : ‖z‖ = R)
    (hw : ‖w‖ = R) : complexPrincipalAngle z w ≤ π * ‖z - w‖ / (2 * R) := by
  set θ := complexPrincipalAngle z w with hθ
  have hθ0 : 0 ≤ θ := complexPrincipalAngle_nonneg z w
  have hθpi : θ ≤ π := complexPrincipalAngle_le_pi z w
  have hpi := Real.pi_pos
  have hs : 2 / π * (θ / 2) ≤ Real.sin (θ / 2) :=
    Real.mul_le_sin (by linarith) (by linarith)
  have hchord := norm_sub_eq_two_mul_sin_half hR hz hw
  rw [← hθ] at hchord
  rw [le_div_iff₀ (by positivity)]
  have h2 : 2 * R * (2 / π * (θ / 2)) ≤ 2 * R * Real.sin (θ / 2) := by
    apply mul_le_mul_of_nonneg_left hs (by positivity)
  rw [← hchord] at h2
  have : 2 * R * (2 / π * (θ / 2)) = 2 * R * θ / π := by field_simp
  rw [this] at h2
  rw [div_le_iff₀ hpi] at h2
  nlinarith

/-- Lower bound of a chord by the principal angle, valid when the angle is at most `δ ≤ π`. -/
theorem chord_ge_of_angle_le {z w : ℂ} {R δ : ℝ} (hR : 0 < R) (hz : ‖z‖ = R) (hw : ‖w‖ = R)
    (hδ : δ ≤ π) (hle : complexPrincipalAngle z w ≤ δ) :
    R * complexPrincipalAngle z w * Real.cos (δ / 2) ≤ ‖z - w‖ := by
  set θ := complexPrincipalAngle z w with hθ
  have hθ0 : 0 ≤ θ := complexPrincipalAngle_nonneg z w
  have hθpi : θ ≤ π := complexPrincipalAngle_le_pi z w
  have h1 : θ / 2 * Real.cos (θ / 2) ≤ Real.sin (θ / 2) :=
    mul_cos_le_sin (by linarith) (by linarith [Real.pi_pos])
  have h2 : Real.cos (δ / 2) ≤ Real.cos (θ / 2) := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
    linarith
  rw [norm_sub_eq_two_mul_sin_half hR hz hw, ← hθ]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * R),
    mul_le_mul_of_nonneg_left h2 (mul_nonneg hR.le hθ0)]

theorem complexPrincipalAngle_self {z : ℂ} (hz : z ≠ 0) : complexPrincipalAngle z z = 0 := by
  have hn : (0:ℝ) < ‖z‖ := norm_pos_iff.2 hz
  have hre : (((starRingEnd ℂ) z) * z).re = ‖z‖ * ‖z‖ := by
    rw [Complex.mul_re]
    simp [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
    ring
  rw [complexPrincipalAngle, hre, div_self (by positivity), Real.arccos_one]

/-- The principal angle satisfies the triangle inequality. -/
theorem complexPrincipalAngle_triangle {z u w : ℂ} (hz : z ≠ 0) (hu : u ≠ 0) (hw : w ≠ 0) :
    complexPrincipalAngle z w ≤ complexPrincipalAngle z u + complexPrincipalAngle u w := by
  rw [← abs_arg_div_eq_complexPrincipalAngle hz hw, ← abs_arg_div_eq_complexPrincipalAngle hz hu,
    ← abs_arg_div_eq_complexPrincipalAngle hu hw]
  have hp : u / z ≠ 0 := div_ne_zero hu hz
  have hq : w / u ≠ 0 := div_ne_zero hw hu
  have hmul : (w / u) * (u / z) = w / z := by field_simp
  have hangle : ((Complex.arg (w / z) : ℝ) : Real.Angle)
      = (Complex.arg (w / u) : Real.Angle) + (Complex.arg (u / z) : Real.Angle) := by
    rw [← hmul, Complex.arg_mul_coe_angle hq hp]
  rcases le_or_gt π (|Complex.arg (u / z)| + |Complex.arg (w / u)|) with hbig | hsmall
  · have h := abs_le.2 ⟨by linarith [Complex.neg_pi_lt_arg (w / z)], Complex.arg_le_pi (w / z)⟩
    linarith
  · have hsum : Complex.arg (w / z) = Complex.arg (w / u) + Complex.arg (u / z) := by
      have hmem : Complex.arg (w / u) + Complex.arg (u / z) ∈ Ioc (-π) π := by
        constructor
        · rcases abs_cases (Complex.arg (u / z)) with h1 | h1 <;>
            rcases abs_cases (Complex.arg (w / u)) with h2 | h2 <;> linarith [h1.1, h2.1]
        · rcases abs_cases (Complex.arg (u / z)) with h1 | h1 <;>
            rcases abs_cases (Complex.arg (w / u)) with h2 | h2 <;> linarith [h1.1, h2.1]
      have h1 := Real.Angle.toReal_coe_eq_self_iff.2 hmem
      have h2 := Real.Angle.toReal_coe_eq_self_iff.2
        (⟨Complex.neg_pi_lt_arg (w / z), Complex.arg_le_pi (w / z)⟩ :
          Complex.arg (w / z) ∈ Ioc (-π) π)
      rw [← h2, hangle, ← Real.Angle.coe_add, h1]
    rw [hsum]
    calc |Complex.arg (w / u) + Complex.arg (u / z)|
        ≤ |Complex.arg (w / u)| + |Complex.arg (u / z)| := abs_add_le _ _
      _ = |Complex.arg (u / z)| + |Complex.arg (w / u)| := by ring

/-- Principal angles add up along a finite chain. -/
theorem complexPrincipalAngle_sum_le (f : ℕ → ℂ) (hf : ∀ i, f i ≠ 0) (n : ℕ) :
    complexPrincipalAngle (f 0) (f n)
      ≤ ∑ i ∈ Finset.range n, complexPrincipalAngle (f i) (f (i + 1)) := by
  induction n with
  | zero => simp [complexPrincipalAngle_self (hf 0)]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc complexPrincipalAngle (f 0) (f (n + 1))
          ≤ complexPrincipalAngle (f 0) (f n) + complexPrincipalAngle (f n) (f (n + 1)) :=
            complexPrincipalAngle_triangle (hf 0) (hf n) (hf (n + 1))
        _ ≤ _ := by linarith

/-- Minkowski's inequality for a finite sum of planar vectors. -/
theorem sqrt_sq_add_sq_sum_le (n : ℕ) (a b : ℕ → ℝ) :
    Real.sqrt ((∑ i ∈ Finset.range n, a i) ^ 2 + (∑ i ∈ Finset.range n, b i) ^ 2)
      ≤ ∑ i ∈ Finset.range n, Real.sqrt (a i ^ 2 + b i ^ 2) := by
  have hnorm : ∀ x y : ℝ, ‖(⟨x, y⟩ : ℂ)‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
    intro x y
    rw [Complex.norm_def, Complex.normSq_apply]
    ring_nf
  have hsum := norm_sum_le (Finset.range n) fun i => (⟨a i, b i⟩ : ℂ)
  have hre : (∑ i ∈ Finset.range n, (⟨a i, b i⟩ : ℂ)).re = ∑ i ∈ Finset.range n, a i := by
    simp [Complex.re_sum]
  have him : (∑ i ∈ Finset.range n, (⟨a i, b i⟩ : ℂ)).im = ∑ i ∈ Finset.range n, b i := by
    simp [Complex.im_sum]
  calc Real.sqrt ((∑ i ∈ Finset.range n, a i) ^ 2 + (∑ i ∈ Finset.range n, b i) ^ 2)
      = ‖∑ i ∈ Finset.range n, (⟨a i, b i⟩ : ℂ)‖ := by
        rw [Complex.norm_def, Complex.normSq_apply, hre, him]; ring_nf
    _ ≤ ∑ i ∈ Finset.range n, ‖(⟨a i, b i⟩ : ℂ)‖ := hsum
    _ = ∑ i ∈ Finset.range n, Real.sqrt (a i ^ 2 + b i ^ 2) :=
        Finset.sum_congr rfl fun i _ => hnorm (a i) (b i)

/-! ### Small auxiliary lemmas -/

/-- A coordinate of a vector of `ℂ²` is no larger than the vector. -/
theorem cliffordSpace_norm_coord_le (v : CliffordSpace) (i : Fin 2) : ‖v.ofLp i‖ ≤ ‖v‖ := by
  have h := norm_sq_cliffordSpace v
  have h0 := norm_nonneg (v.ofLp 0)
  have h1 := norm_nonneg (v.ofLp 1)
  have hv := norm_nonneg v
  fin_cases i
  · show ‖v.ofLp 0‖ ≤ ‖v‖
    nlinarith
  · show ‖v.ofLp 1‖ ≤ ‖v‖
    nlinarith

/-- Truncation at `1` is `1`-Lipschitz. -/
theorem abs_min_one_sub (a b : ℝ) : |min a 1 - min b 1| ≤ |a - b| := by
  have h1 := le_abs_self (a - b)
  have h2 := neg_abs_le (a - b)
  rw [abs_le]
  constructor <;> simp only [min_def] <;> split_ifs <;> linarith


/-! ### The partition estimate on the Clifford torus -/

set_option maxHeartbeats 2000000 in
/-- **The polygonal lower bound on the Clifford torus.**  For every continuous path inside the
unit link `singularLink 2` and every angular threshold `0 < δ ≤ π`, the length of the path is at
least `cos (δ/2)` times the flat-torus distance `√(θ₁² + θ₂²)/√2` between its endpoints, where
`θ₁, θ₂` are the principal angles of the two Clifford coordinates. -/
theorem torus_path_partition_estimate {γ : ℝ → MatSpace 2}
    (hcont : ContinuousOn γ (Icc 0 1))
    (hmem : ∀ t ∈ Icc (0:ℝ) 1, γ t ∈ singularLink 2)
    {δ : ℝ} (hδ0 : 0 < δ) (hδπ : δ ≤ π) :
    ENNReal.ofReal (Real.cos (δ / 2) *
        (Real.sqrt (complexPrincipalAngle ((cliffordPhiEquiv (γ 0)).ofLp 0)
              ((cliffordPhiEquiv (γ 1)).ofLp 0) ^ 2 +
            complexPrincipalAngle ((cliffordPhiEquiv (γ 0)).ofLp 1)
              ((cliffordPhiEquiv (γ 1)).ofLp 1) ^ 2) / Real.sqrt 2))
      ≤ eVariationOn γ (Icc 0 1) := by
  have hpi := Real.pi_pos
  set R : ℝ := 1 / Real.sqrt 2 with hRdef
  have hR : 0 < R := by rw [hRdef]; positivity
  set Z : ℝ → ℂ := fun t => (cliffordPhiEquiv (γ t)).ofLp 0 with hZdef
  set W : ℝ → ℂ := fun t => (cliffordPhiEquiv (γ t)).ofLp 1 with hWdef
  have htor : ∀ t ∈ Icc (0:ℝ) 1, ‖Z t‖ = R ∧ ‖W t‖ = R := by
    intro t ht
    have hmemt : cliffordPhiEquiv (γ t) ∈ cliffordTorus := by
      rw [← cliffordPhi_maps_singularLink]; exact ⟨γ t, hmem t ht, rfl⟩
    exact ⟨by rw [hRdef]; exact hmemt.1, by rw [hRdef]; exact hmemt.2⟩
  have hchordEq : ∀ x y : ℝ,
      dist (γ x) (γ y) = Real.sqrt (‖Z x - Z y‖ ^ 2 + ‖W x - W y‖ ^ 2) := by
    intro x y
    have h1 : dist (γ x) (γ y) = ‖cliffordPhiEquiv (γ x) - cliffordPhiEquiv (γ y)‖ := by
      rw [← map_sub, cliffordPhiEquiv.norm_map, dist_eq_norm]
    have h2 := norm_sq_cliffordSpace (cliffordPhiEquiv (γ x) - cliffordPhiEquiv (γ y))
    have hc0 : (cliffordPhiEquiv (γ x) - cliffordPhiEquiv (γ y)).ofLp 0 = Z x - Z y := rfl
    have hc1 : (cliffordPhiEquiv (γ x) - cliffordPhiEquiv (γ y)).ofLp 1 = W x - W y := rfl
    rw [hc0, hc1] at h2
    rw [h1, ← Real.sqrt_sq (norm_nonneg (cliffordPhiEquiv (γ x) - cliffordPhiEquiv (γ y))), h2]
  have hcoordZ : ∀ x y : ℝ, ‖Z x - Z y‖ ≤ dist (γ x) (γ y) := by
    intro x y
    have h1 : dist (γ x) (γ y) = ‖cliffordPhiEquiv (γ x) - cliffordPhiEquiv (γ y)‖ := by
      rw [← map_sub, cliffordPhiEquiv.norm_map, dist_eq_norm]
    have hc0 : (cliffordPhiEquiv (γ x) - cliffordPhiEquiv (γ y)).ofLp 0 = Z x - Z y := rfl
    rw [h1, ← hc0]
    exact cliffordSpace_norm_coord_le _ 0
  have hcoordW : ∀ x y : ℝ, ‖W x - W y‖ ≤ dist (γ x) (γ y) := by
    intro x y
    have h1 : dist (γ x) (γ y) = ‖cliffordPhiEquiv (γ x) - cliffordPhiEquiv (γ y)‖ := by
      rw [← map_sub, cliffordPhiEquiv.norm_map, dist_eq_norm]
    have hc1 : (cliffordPhiEquiv (γ x) - cliffordPhiEquiv (γ y)).ofLp 1 = W x - W y := rfl
    rw [h1, ← hc1]
    exact cliffordSpace_norm_coord_le _ 1
  -- a uniform modulus of continuity
  set κ : ℝ := 2 * R * δ / π with hκdef
  have hκ : 0 < κ := by rw [hκdef]; positivity
  obtain ⟨δ', hδ'0, hδ'⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hcont) κ hκ
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ'0
  set N : ℕ := m + 1 with hNdef
  have hNR : (0:ℝ) < (N : ℝ) := by rw [hNdef]; positivity
  set u : ℕ → ℝ := fun i => min ((i : ℝ) / (N : ℝ)) 1 with hudef
  have humono : Monotone u := by
    intro i j hij
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact min_le_min (by gcongr) le_rfl
  have humem : ∀ i, u i ∈ Icc (0:ℝ) 1 :=
    fun i => ⟨le_min (by positivity) (by norm_num), min_le_right _ _⟩
  have hu0 : u 0 = 0 := by rw [hudef]; norm_num
  have huN : u N = 1 := by
    rw [hudef]
    simp
  have hustep : ∀ i, |u (i + 1) - u i| ≤ 1 / (N : ℝ) := by
    intro i
    refine le_trans (abs_min_one_sub _ _) ?_
    have he : ((i + 1 : ℕ) : ℝ) / (N : ℝ) - (i : ℝ) / (N : ℝ) = 1 / (N : ℝ) := by
      push_cast; ring
    rw [he, abs_of_nonneg (by positivity)]
  have hstepdist : ∀ i, dist (u i) (u (i + 1)) < δ' := by
    intro i
    rw [Real.dist_eq, abs_sub_comm]
    refine lt_of_le_of_lt (hustep i) ?_
    have : (N : ℝ) = (m : ℝ) + 1 := by rw [hNdef]; push_cast; ring
    rw [this]; exact hm
  -- the principal angles along the partition
  set a : ℕ → ℝ := fun i => complexPrincipalAngle (Z (u i)) (Z (u (i + 1))) with hadef
  set b : ℕ → ℝ := fun i => complexPrincipalAngle (W (u i)) (W (u (i + 1))) with hbdef
  set c : ℝ := R * Real.cos (δ / 2) with hcdef
  have hcosnn : 0 ≤ Real.cos (δ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hcnn : 0 ≤ c := by rw [hcdef]; positivity
  have hstep : ∀ i, c * Real.sqrt (a i ^ 2 + b i ^ 2) ≤ dist (γ (u (i + 1))) (γ (u i)) := by
    intro i
    have hdlt : dist (γ (u i)) (γ (u (i + 1))) < κ :=
      hδ' _ (humem i) _ (humem (i + 1)) (hstepdist i)
    have hZn := (htor (u i) (humem i)).1
    have hZn' := (htor (u (i + 1)) (humem (i + 1))).1
    have hWn := (htor (u i) (humem i)).2
    have hWn' := (htor (u (i + 1)) (humem (i + 1))).2
    have hZκ : ‖Z (u i) - Z (u (i + 1))‖ ≤ 2 * R * δ / π := by
      rw [← hκdef]; exact le_of_lt (lt_of_le_of_lt (hcoordZ _ _) hdlt)
    have hWκ : ‖W (u i) - W (u (i + 1))‖ ≤ 2 * R * δ / π := by
      rw [← hκdef]; exact le_of_lt (lt_of_le_of_lt (hcoordW _ _) hdlt)
    have hbound : ∀ x : ℝ, x ≤ 2 * R * δ / π → π * x / (2 * R) ≤ δ := by
      intro x hx
      rw [div_le_iff₀ (by positivity)]
      have h1 : π * x ≤ π * (2 * R * δ / π) := by
        exact mul_le_mul_of_nonneg_left hx hpi.le
      have h2 : π * (2 * R * δ / π) = 2 * R * δ := by field_simp
      rw [h2] at h1
      linarith
    have haδ : a i ≤ δ := by
      rw [hadef]
      exact le_trans (complexPrincipalAngle_le_of_norm_sub hR hZn hZn') (hbound _ hZκ)
    have hbδ : b i ≤ δ := by
      rw [hbdef]
      exact le_trans (complexPrincipalAngle_le_of_norm_sub hR hWn hWn') (hbound _ hWκ)
    have hZchord : R * a i * Real.cos (δ / 2) ≤ ‖Z (u i) - Z (u (i + 1))‖ := by
      rw [hadef]; exact chord_ge_of_angle_le hR hZn hZn' hδπ (by rw [hadef] at haδ; exact haδ)
    have hWchord : R * b i * Real.cos (δ / 2) ≤ ‖W (u i) - W (u (i + 1))‖ := by
      rw [hbdef]; exact chord_ge_of_angle_le hR hWn hWn' hδπ (by rw [hbdef] at hbδ; exact hbδ)
    have hann : 0 ≤ a i := by rw [hadef]; exact complexPrincipalAngle_nonneg _ _
    have hbnn : 0 ≤ b i := by rw [hbdef]; exact complexPrincipalAngle_nonneg _ _
    have hca : c * a i = R * a i * Real.cos (δ / 2) := by rw [hcdef]; ring
    have hcb : c * b i = R * b i * Real.cos (δ / 2) := by rw [hcdef]; ring
    have h1 : (c * a i) ^ 2 ≤ ‖Z (u (i + 1)) - Z (u i)‖ ^ 2 := by
      rw [norm_sub_rev]
      exact pow_le_pow_left₀ (by positivity) (by rw [hca]; exact hZchord) 2
    have h2 : (c * b i) ^ 2 ≤ ‖W (u (i + 1)) - W (u i)‖ ^ 2 := by
      rw [norm_sub_rev]
      exact pow_le_pow_left₀ (by positivity) (by rw [hcb]; exact hWchord) 2
    have hkey : (c * Real.sqrt (a i ^ 2 + b i ^ 2)) ^ 2
        ≤ ‖Z (u (i + 1)) - Z (u i)‖ ^ 2 + ‖W (u (i + 1)) - W (u i)‖ ^ 2 := by
      have e : (c * Real.sqrt (a i ^ 2 + b i ^ 2)) ^ 2 = (c * a i) ^ 2 + (c * b i) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
      rw [e]; linarith
    rw [hchordEq (u (i + 1)) (u i)]
    calc c * Real.sqrt (a i ^ 2 + b i ^ 2)
        = Real.sqrt ((c * Real.sqrt (a i ^ 2 + b i ^ 2)) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hkey
  -- summing the estimate over the partition
  have hsum1 : c * Real.sqrt ((∑ i ∈ Finset.range N, a i) ^ 2 + (∑ i ∈ Finset.range N, b i) ^ 2)
      ≤ ∑ i ∈ Finset.range N, dist (γ (u (i + 1))) (γ (u i)) := by
    calc c * Real.sqrt ((∑ i ∈ Finset.range N, a i) ^ 2 + (∑ i ∈ Finset.range N, b i) ^ 2)
        ≤ c * ∑ i ∈ Finset.range N, Real.sqrt (a i ^ 2 + b i ^ 2) :=
          mul_le_mul_of_nonneg_left (sqrt_sq_add_sq_sum_le N a b) hcnn
      _ = ∑ i ∈ Finset.range N, c * Real.sqrt (a i ^ 2 + b i ^ 2) := by rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun i _ => hstep i
  have hZne : ∀ i, Z (u i) ≠ 0 := by
    intro i
    refine norm_pos_iff.1 ?_
    rw [(htor (u i) (humem i)).1]; exact hR
  have hWne : ∀ i, W (u i) ≠ 0 := by
    intro i
    refine norm_pos_iff.1 ?_
    rw [(htor (u i) (humem i)).2]; exact hR
  have hθ1 : complexPrincipalAngle (Z 0) (Z 1) ≤ ∑ i ∈ Finset.range N, a i := by
    have h := complexPrincipalAngle_sum_le (fun i => Z (u i)) hZne N
    rw [hu0, huN] at h
    simpa [hadef] using h
  have hθ2 : complexPrincipalAngle (W 0) (W 1) ≤ ∑ i ∈ Finset.range N, b i := by
    have h := complexPrincipalAngle_sum_le (fun i => W (u i)) hWne N
    rw [hu0, huN] at h
    simpa [hbdef] using h
  have hθ1nn : 0 ≤ complexPrincipalAngle (Z 0) (Z 1) := complexPrincipalAngle_nonneg _ _
  have hθ2nn : 0 ≤ complexPrincipalAngle (W 0) (W 1) := complexPrincipalAngle_nonneg _ _
  have hmono : Real.sqrt (complexPrincipalAngle (Z 0) (Z 1) ^ 2
        + complexPrincipalAngle (W 0) (W 1) ^ 2)
      ≤ Real.sqrt ((∑ i ∈ Finset.range N, a i) ^ 2 + (∑ i ∈ Finset.range N, b i) ^ 2) := by
    apply Real.sqrt_le_sqrt
    have h1 : complexPrincipalAngle (Z 0) (Z 1) ^ 2 ≤ (∑ i ∈ Finset.range N, a i) ^ 2 :=
      pow_le_pow_left₀ hθ1nn hθ1 2
    have h2 : complexPrincipalAngle (W 0) (W 1) ^ 2 ≤ (∑ i ∈ Finset.range N, b i) ^ 2 :=
      pow_le_pow_left₀ hθ2nn hθ2 2
    linarith
  -- transfer to the total variation
  have hvar := eVariationOn.sum_le γ N humono humem
  have hconv : ∑ i ∈ Finset.range N, edist (γ (u (i + 1))) (γ (u i))
      = ENNReal.ofReal (∑ i ∈ Finset.range N, dist (γ (u (i + 1))) (γ (u i))) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => dist_nonneg)]
    exact Finset.sum_congr rfl fun i _ => edist_dist _ _
  rw [hconv] at hvar
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hvar
  have hcval : Real.cos (δ / 2) * (Real.sqrt (complexPrincipalAngle (Z 0) (Z 1) ^ 2
        + complexPrincipalAngle (W 0) (W 1) ^ 2) / Real.sqrt 2)
      = c * Real.sqrt (complexPrincipalAngle (Z 0) (Z 1) ^ 2
        + complexPrincipalAngle (W 0) (W 1) ^ 2) := by
    rw [hcdef, hRdef]; ring
  rw [hcval]
  exact le_trans (mul_le_mul_of_nonneg_left hmono hcnn) hsum1


/-! ### The exact link distance and the exact distance in `Σ₂` -/

/-- A matrix is zero exactly when the corresponding point of `MatSpace n` is. -/
theorem ofMat_eq_zero_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ofMat M = 0 ↔ M = 0 := by
  constructor
  · intro h; rw [← toMat_ofMat M, h]; rfl
  · rintro rfl; rfl

/-- Letting the angular threshold tend to `0` in `torus_path_partition_estimate`: every path in
the unit link of `Σ₂` is at least as long as the flat-torus distance between its endpoints. -/
theorem torus_path_length_ge {γ : ℝ → MatSpace 2}
    (hcont : ContinuousOn γ (Icc 0 1))
    (hmem : ∀ t ∈ Icc (0:ℝ) 1, γ t ∈ singularLink 2) :
    ENNReal.ofReal
        (Real.sqrt (complexPrincipalAngle ((cliffordPhiEquiv (γ 0)).ofLp 0)
              ((cliffordPhiEquiv (γ 1)).ofLp 0) ^ 2 +
            complexPrincipalAngle ((cliffordPhiEquiv (γ 0)).ofLp 1)
              ((cliffordPhiEquiv (γ 1)).ofLp 1) ^ 2) / Real.sqrt 2)
      ≤ eVariationOn γ (Icc 0 1) := by
  have hpi := Real.pi_pos
  set θ1 := complexPrincipalAngle ((cliffordPhiEquiv (γ 0)).ofLp 0)
    ((cliffordPhiEquiv (γ 1)).ofLp 0) with hθ1def
  set θ2 := complexPrincipalAngle ((cliffordPhiEquiv (γ 0)).ofLp 1)
    ((cliffordPhiEquiv (γ 1)).ofLp 1) with hθ2def
  set S : ℝ := Real.sqrt (θ1 ^ 2 + θ2 ^ 2) / Real.sqrt 2 with hSdef
  have hSnn : 0 ≤ S := by rw [hSdef]; positivity
  have hSpi : S ≤ π := by
    have h1 : θ1 ≤ π := by rw [hθ1def]; exact complexPrincipalAngle_le_pi _ _
    have h2 : θ2 ≤ π := by rw [hθ2def]; exact complexPrincipalAngle_le_pi _ _
    have h1' : 0 ≤ θ1 := by rw [hθ1def]; exact complexPrincipalAngle_nonneg _ _
    have h2' : 0 ≤ θ2 := by rw [hθ2def]; exact complexPrincipalAngle_nonneg _ _
    have hsum : θ1 ^ 2 + θ2 ^ 2 ≤ 2 * π ^ 2 := by nlinarith
    have hsq : Real.sqrt (θ1 ^ 2 + θ2 ^ 2) ≤ Real.sqrt (2 * π ^ 2) := Real.sqrt_le_sqrt hsum
    have h2eq : Real.sqrt (2 * π ^ 2) = Real.sqrt 2 * π := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hpi.le]
    rw [hSdef, div_le_iff₀ (by positivity)]
    calc Real.sqrt (θ1 ^ 2 + θ2 ^ 2) ≤ Real.sqrt (2 * π ^ 2) := hsq
      _ = π * Real.sqrt 2 := by rw [h2eq]; ring
  by_cases hV : eVariationOn γ (Icc 0 1) = ⊤
  · rw [hV]; exact le_top
  rw [← ENNReal.ofReal_toReal hV]
  refine ENNReal.ofReal_le_ofReal ?_
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  set δ : ℝ := min π (Real.sqrt (8 * ε / π)) with hδdef
  have hδ0 : 0 < δ := lt_min hpi (Real.sqrt_pos.2 (by positivity))
  have hδπ : δ ≤ π := min_le_left _ _
  have hδsq : δ ^ 2 ≤ 8 * ε / π := by
    have h1 : δ ≤ Real.sqrt (8 * ε / π) := min_le_right _ _
    have h2 : Real.sqrt (8 * ε / π) ^ 2 = 8 * ε / π :=
      Real.sq_sqrt (by positivity)
    nlinarith [hδ0.le, Real.sqrt_nonneg (8 * ε / π)]
  have hkey := torus_path_partition_estimate hcont hmem hδ0 hδπ
  rw [← hθ1def, ← hθ2def, ← hSdef] at hkey
  have hkey' : Real.cos (δ / 2) * S ≤ (eVariationOn γ (Icc 0 1)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hV).1 hkey
  have hcos : 1 - δ ^ 2 / 8 ≤ Real.cos (δ / 2) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := δ / 2)
    nlinarith
  have hεbound : π * (δ ^ 2 / 8) ≤ ε := by
    rw [le_div_iff₀ hpi] at hδsq
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hcos hSnn]

/-- The link angle `sigma2Theta` computed from the *normalised* endpoints. -/
theorem sigma2Theta_eq_link_angles (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA0 : ofMat A ≠ 0) (hB0 : ofMat B ≠ 0) :
    sigma2Theta A B =
      Real.sqrt
        (complexPrincipalAngle ((cliffordPhiEquiv ((‖ofMat A‖)⁻¹ • ofMat A)).ofLp 0)
              ((cliffordPhiEquiv ((‖ofMat B‖)⁻¹ • ofMat B)).ofLp 0) ^ 2 +
          complexPrincipalAngle ((cliffordPhiEquiv ((‖ofMat A‖)⁻¹ • ofMat A)).ofLp 1)
              ((cliffordPhiEquiv ((‖ofMat B‖)⁻¹ • ofMat B)).ofLp 1) ^ 2) / Real.sqrt 2 := by
  have hnA : (0:ℝ) < ‖ofMat A‖ := norm_pos_iff.2 hA0
  have hnB : (0:ℝ) < ‖ofMat B‖ := norm_pos_iff.2 hB0
  have hcoordA : ∀ i, (cliffordPhiEquiv ((‖ofMat A‖)⁻¹ • ofMat A)).ofLp i
      = ((‖ofMat A‖)⁻¹ : ℝ) * (cliffordPhi A).ofLp i := by
    intro i
    have hp : cliffordPhiEquiv ((‖ofMat A‖)⁻¹ • ofMat A)
        = ((‖ofMat A‖)⁻¹ : ℝ) • cliffordPhi A := by
      rw [map_smul, cliffordPhiEquiv_apply]
    rw [hp]
    simp [Complex.real_smul]
  have hcoordB : ∀ i, (cliffordPhiEquiv ((‖ofMat B‖)⁻¹ • ofMat B)).ofLp i
      = ((‖ofMat B‖)⁻¹ : ℝ) * (cliffordPhi B).ofLp i := by
    intro i
    have hp : cliffordPhiEquiv ((‖ofMat B‖)⁻¹ • ofMat B)
        = ((‖ofMat B‖)⁻¹ : ℝ) • cliffordPhi B := by
      rw [map_smul, cliffordPhiEquiv_apply]
    rw [hp]
    simp [Complex.real_smul]
  rw [sigma2Theta, hcoordA 0, hcoordA 1, hcoordB 0, hcoordB 1,
    complexPrincipalAngle_smul_left (inv_pos.2 hnA),
    complexPrincipalAngle_smul_right (inv_pos.2 hnB),
    complexPrincipalAngle_smul_left (inv_pos.2 hnA),
    complexPrincipalAngle_smul_right (inv_pos.2 hnB)]

/-- **The flat-torus lower bound (Theorem 9 at the level of the link).** -/
theorem intrinsicEDist_singularLink_two_ge (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA0 : ofMat A ≠ 0) (hB0 : ofMat B ≠ 0) :
    ENNReal.ofReal (sigma2Theta A B) ≤
      intrinsicEDist (singularLink 2) ((‖ofMat A‖)⁻¹ • ofMat A) ((‖ofMat B‖)⁻¹ • ofMat B) := by
  refine le_iInf₂ fun γ hγ => ?_
  obtain ⟨hcont, hmaps, hγ0, hγ1⟩ := hγ
  have h := torus_path_length_ge hcont (fun t ht => hmaps ht)
  rw [hγ0, hγ1, ← sigma2Theta_eq_link_angles A B hA0 hB0] at h
  exact h

/-- **The exact link distance in `Σ₂`.**  Between the normalisations of two nonzero singular
`2 × 2` matrices, the intrinsic distance inside the unit link (the Clifford torus) is exactly the
flat-torus distance `sigma2Theta A B`. -/
theorem intrinsicEDist_singularLink_two (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.det = 0) (hB : B.det = 0) (hA0 : ofMat A ≠ 0) (hB0 : ofMat B ≠ 0) :
    intrinsicEDist (singularLink 2) ((‖ofMat A‖)⁻¹ • ofMat A) ((‖ofMat B‖)⁻¹ • ofMat B) =
      ENNReal.ofReal (sigma2Theta A B) :=
  le_antisymm (intrinsicEDist_singularLink_two_le A B hA hB hA0 hB0)
    (intrinsicEDist_singularLink_two_ge A B hA0 hB0)

/-- The capped angular distance of the unit link of `Σ₂` is exactly `sigma2Theta`. -/
theorem cappedAngularDistance_singularLink_two (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.det = 0) (hB : B.det = 0) (hA0 : ofMat A ≠ 0) (hB0 : ofMat B ≠ 0) :
    cappedAngularDistance (singularLink 2) ((‖ofMat A‖)⁻¹ • ofMat A)
        ((‖ofMat B‖)⁻¹ • ofMat B) = sigma2Theta A B := by
  have h := intrinsicEDist_singularLink_two A B hA hB hA0 hB0
  unfold cappedAngularDistance
  rw [h]
  rw [if_neg ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (sigma2Theta_nonneg A B)]
  exact min_eq_right (sigma2Theta_le_pi A B)

/-- **Theorem 9: the exact intrinsic distance between two nonzero singular `2 × 2` matrices.** -/
theorem intrinsicEDist_singularLocus_two_exact
    (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.det = 0) (hB : B.det = 0)
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) :
    intrinsicEDist (singularLocus 2) (ofMat A) (ofMat B) =
      ENNReal.ofReal
        (Real.sqrt
          (‖ofMat A‖ ^ 2 + ‖ofMat B‖ ^ 2 -
            2 * ‖ofMat A‖ * ‖ofMat B‖ * Real.cos (sigma2Theta A B))) := by
  have hA0' : ofMat A ≠ 0 := fun h => hA0 ((ofMat_eq_zero_iff A).1 h)
  have hB0' : ofMat B ≠ 0 := fun h => hB0 ((ofMat_eq_zero_iff B).1 h)
  refine le_antisymm (intrinsicEDist_singularLocus_two_le A B hA hB hA0' hB0') ?_
  have hlow := intrinsicEDist_singularLocus_cone_lower (n := 2) (by norm_num)
    ((ofMat_mem_singularLocus_iff A).2 hA) ((ofMat_mem_singularLocus_iff B).2 hB) hA0' hB0'
  rw [cappedAngularDistance_singularLink_two A B hA hB hA0' hB0'] at hlow
  exact hlow


/-! ### The `E₁₁`, `E₂₂` example, exactly -/

theorem complexPrincipalAngle_neg_self {z : ℂ} (hz : z ≠ 0) :
    complexPrincipalAngle z (-z) = π := by
  have hn : (0:ℝ) < ‖z‖ := norm_pos_iff.2 hz
  have hre : (((starRingEnd ℂ) z) * (-z)).re = -(‖z‖ * ‖z‖) := by
    have hnorm : ‖z‖ * ‖z‖ = z.re ^ 2 + z.im ^ 2 := by
      rw [← sq, Complex.sq_norm, Complex.normSq_apply]; ring
    rw [Complex.mul_re, hnorm]
    simp
    ring
  rw [complexPrincipalAngle, norm_neg, hre, neg_div, div_self (by positivity),
    Real.arccos_neg_one]

/-- The two Clifford phases of `E₁₁` and `E₂₂` differ by `0` and by `π`. -/
theorem sigma2Theta_E11_E22 : sigma2Theta E11 E22 = π / Real.sqrt 2 := by
  have hz : ((1:ℂ) / (Real.sqrt 2 : ℝ)) ≠ 0 := by simp
  have h0 : (cliffordPhi E11).ofLp 0 = ((1:ℂ) / (Real.sqrt 2 : ℝ)) := by simp [cliffordPhi, E11]
  have h1 : (cliffordPhi E11).ofLp 1 = ((1:ℂ) / (Real.sqrt 2 : ℝ)) := by simp [cliffordPhi, E11]
  have h2 : (cliffordPhi E22).ofLp 0 = ((1:ℂ) / (Real.sqrt 2 : ℝ)) := by simp [cliffordPhi, E22]
  have h3 : (cliffordPhi E22).ofLp 1 = -((1:ℂ) / (Real.sqrt 2 : ℝ)) := by
    simp [cliffordPhi, E22]; ring
  rw [sigma2Theta, h0, h1, h2, h3, complexPrincipalAngle_self hz,
    complexPrincipalAngle_neg_self hz]
  rw [show (0:ℝ) ^ 2 + π ^ 2 = π ^ 2 by ring, Real.sqrt_sq Real.pi_nonneg]

/-- **The exact value of the `E₁₁`, `E₂₂` example.**  This refines the previously proved bounds
`sqrt_three_le_dist_E11_E22` and `dist_E11_E22_gt`. -/
theorem intrinsicEDist_E11_E22_exact :
    intrinsicEDist (singularLocus 2) (ofMat E11) (ofMat E22) =
      ENNReal.ofReal (Real.sqrt (2 - 2 * Real.cos (Real.pi / Real.sqrt 2))) := by
  have hdA : E11.det = 0 := by simp [E11, Matrix.det_fin_two]
  have hdB : E22.det = 0 := by simp [E22, Matrix.det_fin_two]
  have hA0 : E11 ≠ 0 := by
    intro h
    have h1 := congrFun (congrFun h 0) 0
    simp [E11] at h1
  have hB0 : E22 ≠ 0 := by
    intro h
    have h1 := congrFun (congrFun h 1) 1
    simp [E22] at h1
  have hnA : ‖ofMat E11‖ = 1 := by rw [norm_ofMat]; simp [E11, Fin.sum_univ_two]
  have hnB : ‖ofMat E22‖ = 1 := by rw [norm_ofMat]; simp [E22, Fin.sum_univ_two]
  have h := intrinsicEDist_singularLocus_two_exact E11 E22 hdA hdB hA0 hB0
  rw [hnA, hnB, sigma2Theta_E11_E22] at h
  rw [h]
  norm_num

end Sigma2Lower

end Q748
