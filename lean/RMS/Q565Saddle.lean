/-
Saddle-point analysis for the Bell numbers (work file; to be merged into `Q565.lean`).
-/
import RMS.Q565

open Real Filter Asymptotics
open scoped BigOperators Nat Topology

set_option maxHeartbeats 1000000

namespace Q565

/-! ## Elementary expansions -/

/-- Third-order Taylor bound for the logarithm. -/
theorem log_taylor3 {u : ℝ} (hu : |u| ≤ 1/2) :
    |Real.log (1 + u) - (u - u^2/2)| ≤ 2 * |u|^3 := by
  have hx : |(-u)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at h
  simp only [Finset.sum_range_zero, zero_add] at h
  have h1 : (1 : ℝ) - (-u) = 1 + u := by ring
  rw [h1] at h
  have h2 : ((-u) ^ (0 + 1) / ((0:ℕ) + 1) + (-u) ^ (1 + 1) / ((1:ℕ) + 1))
      = -(u - u^2/2) := by push_cast; ring
  rw [h2] at h
  have h3 : |(-u)| ^ (2 + 1) / (1 - |(-u)|) ≤ 2 * |u|^3 := by
    rw [abs_neg, show (2+1) = 3 from rfl]
    rw [div_le_iff₀ (by linarith [abs_nonneg u])]
    nlinarith [mul_nonneg (pow_nonneg (abs_nonneg u) 3) (by linarith : (0:ℝ) ≤ 1 - 2*|u|)]
  have he : Real.log (1+u) - (u - u^2/2) = -(u - u^2/2) + Real.log (1+u) := by ring
  rw [he]
  exact le_trans h h3

/-! ## Quantitative Stirling -/

/-- The Stirling defect `θ k = log k! - (k log k - k + ½ log (2πk))`. -/
noncomputable def theta (k : ℕ) : ℝ :=
  Real.log (k !) - (k * Real.log k - k + Real.log (2 * π * k) / 2)

theorem log_two_pi_mul {k : ℕ} (hk : k ≠ 0) :
    Real.log (2 * π * k) = Real.log (2 * π) + Real.log k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  rw [Real.log_mul (by positivity) (ne_of_gt hk0)]

theorem theta_nonneg {k : ℕ} (hk : k ≠ 0) : 0 ≤ theta k := by
  have h := Stirling.le_log_factorial_stirling hk
  simp only [theta, log_two_pi_mul hk]
  linarith

/-- Telescoping form of Mathlib's bound on consecutive Stirling defects. -/
theorem log_stirlingSeq_sub_le {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    Real.log (Stirling.stirlingSeq (m+1)) - Real.log (Stirling.stirlingSeq (m+N+1))
      ≤ 1/(4*(m:ℝ)) - 1/(4*((m:ℝ)+N)) := by
  have hm0 : (1:ℝ) ≤ m := by exact_mod_cast hm
  induction N with
  | zero => simp
  | succ N ih =>
      have h1 := Stirling.log_stirlingSeq_sub_log_stirlingSeq_succ (m+N)
      have hcast : ((m + N + 1 : ℕ) : ℝ) = (m:ℝ) + N + 1 := by push_cast; ring
      rw [hcast] at h1
      have h2 : 1/(4*((m:ℝ)+N+1)^2) ≤ 1/(4*((m:ℝ)+N)) - 1/(4*((m:ℝ)+N+1)) := by
        have hA : (0:ℝ) < (m:ℝ) + N := by
          have := Nat.cast_nonneg (α := ℝ) N; linarith
        have hB : (0:ℝ) < (m:ℝ) + N + 1 := by linarith
        have hsplit : 1/(4*((m:ℝ)+N)) - 1/(4*((m:ℝ)+N+1))
            = 1/(4*((m:ℝ)+N)*((m:ℝ)+N+1)) := by
          field_simp
          ring
        rw [hsplit]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith [hA, hB]
      have heq1 : (m + (N+1) + 1 : ℕ) = (m + N) + 2 := by omega
      have heq2 : (m + N + 1 : ℕ) = (m + N) + 1 := by rfl
      rw [heq1]
      have hcast2 : ((m:ℝ) + (N+1)) = (m:ℝ) + N + 1 := by ring
      push_cast at ih ⊢
      rw [show (m:ℝ) + ((N:ℝ)+1) = (m:ℝ)+(N:ℝ)+1 from by ring]
      linarith [ih, h1, h2]

theorem theta_eq_log_stirlingSeq {k : ℕ} (hk : k ≠ 0) :
    theta k = Real.log (Stirling.stirlingSeq k) - Real.log (Real.sqrt π) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  rw [Stirling.log_stirlingSeq_formula, theta, log_two_pi_mul hk,
    Real.log_sqrt Real.pi_pos.le, Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos),
    Real.log_mul (by norm_num) (ne_of_gt hk0), Real.log_div (ne_of_gt hk0) (Real.exp_ne_zero 1),
    Real.log_exp]
  ring

theorem theta_le {k : ℕ} (hk : 2 ≤ k) : theta k ≤ 1 / k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k-1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hm0 : (1:ℝ) ≤ m := by exact_mod_cast hm
  rw [theta_eq_log_stirlingSeq (by omega)]
  have hidx : Tendsto (fun N : ℕ => m + N + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun N => (by omega : N ≤ m + N + 1)) tendsto_id
  have hlim : Tendsto (fun N : ℕ => Real.log (Stirling.stirlingSeq (m+N+1))) atTop
      (𝓝 (Real.log (Real.sqrt π))) := by
    have h1 : Tendsto (fun N : ℕ => Stirling.stirlingSeq (m+N+1)) atTop (𝓝 (Real.sqrt π)) :=
      Stirling.tendsto_stirlingSeq_sqrt_pi.comp hidx
    exact (Real.continuousAt_log (by positivity)).tendsto.comp h1
  have hbound : Real.log (Stirling.stirlingSeq (m+1)) - Real.log (Real.sqrt π) ≤ 1/(4*(m:ℝ)) := by
    refine le_of_tendsto (tendsto_const_nhds.sub hlim) ?_
    filter_upwards with N
    have h := log_stirlingSeq_sub_le hm N
    have : (0:ℝ) < 4*((m:ℝ)+N) := by
      have := Nat.cast_nonneg (α := ℝ) N; linarith
    have hpos : 0 < 1/(4*((m:ℝ)+N)) := by positivity
    linarith
  have hfin : 1/(4*(m:ℝ)) ≤ 1/((m:ℝ)+1) := by
    apply one_div_le_one_div_of_le (by linarith)
    linarith
  have hcast : ((m+1 : ℕ) : ℝ) = (m:ℝ) + 1 := by push_cast; ring
  rw [hcast]
  linarith

/-! ## Geometric tail bounds for log-concave sequences -/

/-- If `f` decays at least geometrically from `K` on, its tail is bounded by `f K/(1-ρ)`. -/
theorem geom_tail_upper {f : ℕ → ℝ} {ρ : ℝ} {K : ℕ} (hf : ∀ k, 0 ≤ f k)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hstep : ∀ k, K ≤ k → f (k+1) ≤ ρ * f k) :
    Summable (fun j : ℕ => f (K + j)) ∧ ∑' j : ℕ, f (K + j) ≤ f K / (1 - ρ) := by
  have hpow : ∀ j : ℕ, f (K + j) ≤ f K * ρ^j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have h1 : f (K + j + 1) ≤ ρ * f (K + j) := hstep (K + j) (by omega)
        have h2 : ρ * f (K + j) ≤ ρ * (f K * ρ^j) := by
          exact mul_le_mul_of_nonneg_left ih hρ0
        have h3 : K + (j+1) = K + j + 1 := by omega
        rw [h3]
        calc f (K + j + 1) ≤ ρ * (f K * ρ^j) := le_trans h1 h2
          _ = f K * ρ^(j+1) := by ring
  have hgeom : Summable (fun j : ℕ => f K * ρ^j) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  have hsum : Summable (fun j : ℕ => f (K + j)) :=
    Summable.of_nonneg_of_le (fun j => hf _) hpow hgeom
  refine ⟨hsum, ?_⟩
  calc ∑' j : ℕ, f (K + j) ≤ ∑' j : ℕ, f K * ρ^j := hsum.tsum_le_tsum hpow hgeom
    _ = f K * (1 - ρ)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    _ = f K / (1 - ρ) := by rw [div_eq_mul_inv]

/-- If `f` grows at least geometrically up to `K`, the sum below `K` is bounded. -/
theorem geom_tail_lower {f : ℕ → ℝ} {ρ : ℝ} (hf : ∀ k, 0 ≤ f k)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∀ K : ℕ, (∀ k, 1 ≤ k → k < K → f k ≤ ρ * f (k+1)) →
      ∑ k ∈ Finset.Ico 1 K, f k ≤ f K * ρ / (1 - ρ) := by
  have h1 : (0:ℝ) < 1 - ρ := by linarith
  have hne : (1:ℝ) - ρ ≠ 0 := ne_of_gt h1
  intro K
  induction K with
  | zero =>
      intro _
      have he : ∑ k ∈ Finset.Ico 1 0, f k = 0 := by simp
      rw [he]
      exact div_nonneg (mul_nonneg (hf 0) hρ0) h1.le
  | succ K ih =>
      intro hstep
      by_cases hK : K = 0
      · subst hK
        have he : ∑ k ∈ Finset.Ico 1 (0+1), f k = 0 := by simp
        rw [he]
        exact div_nonneg (mul_nonneg (hf 1) hρ0) h1.le
      have hIH := ih (fun k hk1 hk2 => hstep k hk1 (by omega))
      have hlast : f K ≤ ρ * f (K+1) := hstep K (by omega) (by omega)
      have hsplit : ∑ k ∈ Finset.Ico 1 (K+1), f k = ∑ k ∈ Finset.Ico 1 K, f k + f K :=
        Finset.sum_Ico_succ_top (by omega) _
      rw [hsplit]
      calc ∑ k ∈ Finset.Ico 1 K, f k + f K ≤ f K * ρ/(1-ρ) + f K := by linarith
        _ = f K / (1-ρ) := by field_simp; ring
        _ ≤ (ρ * f (K+1))/(1-ρ) := by gcongr
        _ = f (K+1) * ρ/(1-ρ) := by ring

/-! ## The exponent `psi` and its expansion at the saddle point -/

/-- `psi N x = N log x - x log x + x - ½ log (2πx)`; by Stirling, `k^N/k! = exp (psi N k - θ k)`. -/
noncomputable def psi (N x : ℝ) : ℝ :=
  N * Real.log x - x * Real.log x + x - Real.log (2 * π * x) / 2

theorem pow_div_factorial_le_exp {x : ℝ} (hx : 0 ≤ x) (m : ℕ) : x^m / m ! ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx (m+1)
  have h2 : x^m/m ! ≤ ∑ i ∈ Finset.range (m+1), x^i/i ! := by
    refine Finset.single_le_sum (f := fun i => x^i/(i ! : ℝ)) (fun i _ => by positivity) ?_
    simp
  linarith

theorem sq_le_exp {x : ℝ} (hx : 0 ≤ x) : x^2/2 ≤ Real.exp x := by
  have h := pow_div_factorial_le_exp hx 2
  norm_num [Nat.factorial] at h
  linarith

theorem cube_le_exp {x : ℝ} (hx : 0 ≤ x) : x^3/6 ≤ Real.exp x := by
  have h := pow_div_factorial_le_exp hx 3
  norm_num [Nat.factorial] at h
  linarith

theorem psi_diff {N w s : ℝ} (hw : 0 < w) (hws : 0 < w + s) :
    psi N (w+s) - psi N w
      = (N - w - s - 1/2) * Real.log (1 + s/w) - s * Real.log w + s := by
  have hu : 0 < 1 + s/w := by
    have : 1 + s/w = (w+s)/w := by field_simp
    rw [this]; positivity
  have h1 : Real.log (w+s) = Real.log w + Real.log (1+s/w) := by
    rw [← Real.log_mul (ne_of_gt hw) (ne_of_gt hu)]
    congr 1
    field_simp
  have h2 : Real.log (2*π*(w+s)) = Real.log (2*π) + Real.log (w+s) :=
    Real.log_mul (by positivity) (ne_of_gt hws)
  have h3 : Real.log (2*π*w) = Real.log (2*π) + Real.log w :=
    Real.log_mul (by positivity) (ne_of_gt hw)
  simp only [psi, h1, h2, h3]
  ring

/-- **The saddle-point expansion of `psi`.**  Near `x = w = e^r`, with `N = r w`, the exponent
is a Gaussian of variance `w/(r+1)`, up to an error which is uniformly tiny on the window
`|s| ≤ e^{3r/5}`. -/
theorem psi_taylor {N r w s : ℝ} (hr : 2048 ≤ r) (hw : w = Real.exp r) (hN : N = r * w)
    (hs : |s| ≤ Real.exp (3*r/5)) :
    |psi N (w+s) - psi N w + (r+1)*s^2/(2*w)| ≤ Real.exp (-r/10) := by
  have hr0 : (0:ℝ) < r := by linarith
  have hw0 : 0 < w := by rw [hw]; exact Real.exp_pos r
  have hwr : Real.log w = r := by rw [hw, Real.log_exp]
  have hsw : |s| ≤ Real.exp (3*r/5) := hs
  have hswlt : Real.exp (3*r/5) < w := by
    rw [hw]; exact Real.exp_lt_exp.2 (by linarith)
  have habs_s : |s| < w := lt_of_le_of_lt hsw hswlt
  have hws : 0 < w + s := by
    have := neg_abs_le s
    linarith
  -- the scaled variable
  set u : ℝ := s/w with hu_def
  have hu_abs : |u| ≤ Real.exp (-2*r/5) := by
    rw [hu_def, abs_div, abs_of_pos hw0]
    rw [div_le_iff₀ hw0, hw, ← Real.exp_add]
    refine hsw.trans (Real.exp_le_exp.2 (by linarith))
  have hu_half : |u| ≤ 1/2 := by
    refine hu_abs.trans ?_
    have : Real.exp (-2*r/5) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    refine this.trans ?_
    rw [Real.exp_neg]
    have h1 : (2:ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1:ℝ); linarith
    rw [inv_le_iff_one_le_mul₀ (Real.exp_pos 1)]
    linarith
  -- Taylor remainder for the logarithm
  set rho : ℝ := Real.log (1+u) - (u - u^2/2) with hrho_def
  have hrho : |rho| ≤ 2 * |u|^3 := log_taylor3 hu_half
  -- exact algebraic identity
  have hid : psi N (w+s) - psi N w + (r+1)*s^2/(2*w)
      = s^3/(2*w^2) - u/2 + u^2/4 + (N - w - s - 1/2) * rho := by
    rw [psi_diff hw0 hws, hwr, hrho_def, hu_def, hN]
    field_simp
    ring
  rw [hid]
  -- bound each term
  have hs3 : |s^3/(2*w^2)| ≤ Real.exp (-r/5)/2 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2*w^2)]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h1 : |s^3| ≤ (Real.exp (3*r/5))^3 := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg s) hsw 3
    have h2 : (Real.exp (3*r/5))^3 = Real.exp (9*r/5) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h3 : (2:ℝ)*w^2 = 2 * Real.exp (2*r) := by
      rw [hw, ← Real.exp_nat_mul]; norm_num
    rw [h2] at h1
    have h4 : Real.exp (9*r/5) * 2 ≤ Real.exp (-r/5) * (2*w^2) := by
      rw [h3]
      rw [show Real.exp (-r/5) * (2 * Real.exp (2*r)) = 2 * Real.exp (-r/5 + 2*r) by
        rw [Real.exp_add]; ring]
      have : Real.exp (9*r/5) ≤ Real.exp (-r/5 + 2*r) := Real.exp_le_exp.2 (by linarith)
      linarith
    linarith
  have hu2 : |u|^2 ≤ Real.exp (-4*r/5) := by
    have := pow_le_pow_left₀ (abs_nonneg u) hu_abs 2
    refine this.trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hu3 : |u|^3 ≤ Real.exp (-6*r/5) := by
    have := pow_le_pow_left₀ (abs_nonneg u) hu_abs 3
    refine this.trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hbig : |N - w - s - 1/2| ≤ 2 * r * w := by
    have h1 : |N - w - s - 1/2| ≤ |N| + |w| + |s| + 1/2 := by
      have t1 : N - w - s - 1/2 = N + (-w) + (-s) + (-(1/2:ℝ)) := by ring
      rw [t1]
      have b0 := abs_add_le (N + (-w) + (-s)) (-(1/2:ℝ))
      have b1 := abs_add_le (N + (-w)) (-s)
      have b2 := abs_add_le N (-w)
      simp only [abs_neg] at b0 b1 b2
      have h12 : |(1:ℝ)/2| = 1/2 := by norm_num
      linarith
    have hNa : |N| = r * w := by
      rw [hN, abs_of_pos (by positivity)]
    have hwa : |w| = w := abs_of_pos hw0
    have : |s| ≤ w := habs_s.le
    have hw1 : (1:ℝ) ≤ w := by
      rw [hw]
      have := Real.add_one_le_exp r; linarith
    have : r * w + w + w + 1/2 ≤ 2 * r * w := by nlinarith
    linarith [h1, hNa, hwa]
  -- combine
  have hterm4 : |(N - w - s - 1/2) * rho| ≤ 4 * r * Real.exp (-r/5) := by
    rw [abs_mul]
    have h1 : |N - w - s - 1/2| * |rho| ≤ (2*r*w) * (2 * |u|^3) :=
      mul_le_mul hbig hrho (abs_nonneg rho) (by positivity)
    refine h1.trans ?_
    have h2 : (2*r*w) * (2*|u|^3) ≤ (2*r*w) * (2*Real.exp (-6*r/5)) := by
      have : (0:ℝ) ≤ 2*r*w := by positivity
      nlinarith [hu3]
    refine h2.trans (le_of_eq ?_)
    have hee : Real.exp (-r/5) = Real.exp r * Real.exp (-6*r/5) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hw, hee]; ring
  have hsum : |s^3/(2*w^2) - u/2 + u^2/4 + (N - w - s - 1/2) * rho|
      ≤ Real.exp (-r/5)/2 + Real.exp (-2*r/5)/2 + Real.exp (-4*r/5)/4
        + 4 * r * Real.exp (-r/5) := by
    have e1 : s^3/(2*w^2) - u/2 + u^2/4 + (N - w - s - 1/2) * rho
        = ((s^3/(2*w^2) + (-(u/2))) + u^2/4) + (N - w - s - 1/2) * rho := by ring
    rw [e1]
    have b1 := abs_add_le ((s^3/(2*w^2) + (-(u/2))) + u^2/4) ((N - w - s - 1/2) * rho)
    have b2 := abs_add_le (s^3/(2*w^2) + (-(u/2))) (u^2/4)
    have b3 := abs_add_le (s^3/(2*w^2)) (-(u/2))
    have b4 : |(-(u/2))| = |u|/2 := by rw [abs_neg, abs_div]; norm_num
    have b5 : |u^2/4| = |u|^2/4 := by
      rw [abs_div, abs_pow]; norm_num
    linarith [hs3, hu_abs, hu2, hterm4]
  refine hsum.trans ?_
  -- final numeric comparison
  have hexp1 : Real.exp (-2*r/5) ≤ Real.exp (-r/5) := Real.exp_le_exp.2 (by linarith)
  have hexp2 : Real.exp (-4*r/5) ≤ Real.exp (-r/5) := Real.exp_le_exp.2 (by linarith)
  have hkey : (4*r + 2) * Real.exp (-r/5) ≤ Real.exp (-r/10) := by
    rw [show Real.exp (-r/5) = Real.exp (-r/10) * Real.exp (-r/10) by
      rw [← Real.exp_add]; congr 1; ring]
    have hexp : (4*r+2) ≤ Real.exp (r/10) := by
      have := sq_le_exp (by linarith : (0:ℝ) ≤ r/10)
      nlinarith
    have hpos : 0 < Real.exp (-r/10) := Real.exp_pos _
    have h2 : (4*r+2) * Real.exp (-r/10) ≤ Real.exp (r/10) * Real.exp (-r/10) :=
      mul_le_mul_of_nonneg_right hexp hpos.le
    have h3 : Real.exp (r/10) * Real.exp (-r/10) = 1 := by
      rw [← Real.exp_add, show r/10 + -r/10 = 0 by ring, Real.exp_zero]
    calc (4*r+2) * (Real.exp (-r/10) * Real.exp (-r/10))
        = ((4*r+2) * Real.exp (-r/10)) * Real.exp (-r/10) := by ring
      _ ≤ 1 * Real.exp (-r/10) := by
          apply mul_le_mul_of_nonneg_right _ hpos.le
          linarith [h2, h3]
      _ = Real.exp (-r/10) := by ring
  have hp : 0 < Real.exp (-r/5) := Real.exp_pos _
  linarith

/-! ## The Dobinski terms -/

/-- The Dobinski terms `a_k = kⁿ/k!`. -/
noncomputable def bterm (n k : ℕ) : ℝ := (k:ℝ)^n / k !

theorem bterm_nonneg (n k : ℕ) : 0 ≤ bterm n k := by
  simp only [bterm]
  positivity

theorem bterm_pos {n k : ℕ} (hk : k ≠ 0) : 0 < bterm n k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  simp only [bterm]
  positivity

/-- Stirling's formula in the form used here: `kⁿ/k! = exp (psi n k - θ k)`. -/
theorem bterm_eq {n k : ℕ} (hk : k ≠ 0) :
    bterm n k = Real.exp (psi n k - theta k) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hfac : (0:ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h : psi (n:ℝ) (k:ℝ) - theta k = n * Real.log k - Real.log (k !) := by
    simp only [psi, theta]; ring
  rw [bterm, h, Real.exp_sub, Real.exp_nat_mul, Real.exp_log hk0, Real.exp_log hfac]

theorem bterm_le_exp_psi {n k : ℕ} (hk : k ≠ 0) : bterm n k ≤ Real.exp (psi n k) := by
  rw [bterm_eq hk]
  exact Real.exp_le_exp.2 (by linarith [theta_nonneg hk])

/-- The ratio of consecutive Dobinski terms. -/
noncomputable def brat (n k : ℕ) : ℝ := ((k+1:ℝ)/k)^n / (k+1)

theorem brat_pos {n k : ℕ} (hk : 1 ≤ k) : 0 < brat n k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  simp only [brat]
  positivity

theorem bterm_succ (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    bterm n (k+1) = brat n k * bterm n k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hfac : (0:ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  simp only [bterm, brat]
  rw [Nat.factorial_succ]
  push_cast
  rw [div_pow]
  field_simp

theorem brat_antitone (n : ℕ) {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) : brat n k ≤ brat n j := by
  have hj0 : (0:ℝ) < j := by exact_mod_cast hj
  have hk0 : (0:ℝ) < k := by exact_mod_cast (lt_of_lt_of_le hj hjk : 0 < k)
  have hjk' : (j:ℝ) ≤ k := by exact_mod_cast hjk
  have h1 : ((k+1:ℝ)/k)^n ≤ ((j+1:ℝ)/j)^n := by
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_div_iff₀ hk0 hj0]
    nlinarith
  have h2 : (1:ℝ)/(k+1) ≤ 1/(j+1) := by
    apply one_div_le_one_div_of_le (by linarith)
    linarith
  have hb : brat n k = ((k+1:ℝ)/k)^n * (1/((k:ℝ)+1)) := by simp only [brat]; ring
  have hb' : brat n j = ((j+1:ℝ)/j)^n * (1/((j:ℝ)+1)) := by simp only [brat]; ring
  rw [hb, hb']
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-! ## Gaussian sums -/

open MeasureTheory


/-- The Gaussian `x ↦ exp (-c (x-w)²)`. -/
noncomputable def gauss (c w x : ℝ) : ℝ := Real.exp (-c*(x-w)^2)

theorem gauss_pos (c w x : ℝ) : 0 < gauss c w x := Real.exp_pos _

theorem gauss_le_one {c : ℝ} (hc : 0 ≤ c) (w x : ℝ) : gauss c w x ≤ 1 := by
  simp only [gauss]
  rw [Real.exp_le_one_iff]
  nlinarith [sq_nonneg (x-w)]

theorem gauss_integrable {c : ℝ} (hc : 0 < c) (w : ℝ) : Integrable (gauss c w) := by
  have h : Integrable (fun x : ℝ => Real.exp (-c * x^2)) := integrable_exp_neg_mul_sq hc
  refine (h.comp_sub_right w).congr ?_
  filter_upwards with x
  simp only [gauss]

theorem gauss_integral (c w : ℝ) :
    ∫ x, gauss c w x = Real.sqrt (π/c) := by
  have h1 : ∫ x, gauss c w x = ∫ x, Real.exp (-c*x^2) := by
    simpa only [gauss] using
      MeasureTheory.integral_sub_right_eq_self (μ := volume) (fun y : ℝ => Real.exp (-c*y^2)) w
  rw [h1, integral_gaussian]

theorem gauss_monotoneOn {c : ℝ} (hc : 0 ≤ c) (w : ℝ) : MonotoneOn (gauss c w) (Set.Iic w) := by
  intro x hx y hy hxy
  simp only [gauss, Set.mem_Iic] at *
  refine Real.exp_le_exp.2 ?_
  nlinarith [mul_nonneg hc (mul_nonneg (sub_nonneg.2 hxy) (by linarith : (0:ℝ) ≤ 2*w - x - y))]

theorem gauss_antitoneOn {c : ℝ} (hc : 0 ≤ c) (w : ℝ) : AntitoneOn (gauss c w) (Set.Ici w) := by
  intro x hx y hy hxy
  simp only [gauss, Set.mem_Ici] at *
  refine Real.exp_le_exp.2 ?_
  nlinarith [mul_nonneg hc (mul_nonneg (sub_nonneg.2 hxy) (by linarith : (0:ℝ) ≤ x + y - 2*w))]

/-- Any interval integral of the Gaussian is at most the full integral. -/
theorem gauss_interval_le {c : ℝ} (hc : 0 < c) (w a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, gauss c w x) ≤ Real.sqrt (π/c) := by
  rw [intervalIntegral.integral_of_le hab, ← gauss_integral c w]
  exact setIntegral_le_integral (gauss_integrable hc w)
    (Filter.Eventually.of_forall (fun x => (gauss_pos c w x).le))

/-- Gaussian tail bound: away from the centre the mass is exponentially small. -/
theorem gauss_tail_Ioi {c : ℝ} (hc : 0 < c) (w : ℝ) {a : ℝ} (ha : 0 < a) :
    (∫ x in Set.Ioi (w+a), gauss c w x) ≤ Real.exp (-c*a^2/2) * Real.sqrt (2*π/c) := by
  have hdom : ∀ x ∈ Set.Ioi (w+a), gauss c w x ≤ Real.exp (-c*a^2/2) * gauss (c/2) w x := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    simp only [gauss, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : a ≤ x - w := by linarith
    have h2 : a^2 ≤ (x-w)^2 := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 hc.le
    linarith
  have hint1 : IntegrableOn (gauss c w) (Set.Ioi (w+a)) := (gauss_integrable hc w).integrableOn
  have hint2 : IntegrableOn (fun x => Real.exp (-c*a^2/2) * gauss (c/2) w x) (Set.Ioi (w+a)) :=
    ((gauss_integrable (by linarith) w).const_mul _).integrableOn
  calc (∫ x in Set.Ioi (w+a), gauss c w x)
      ≤ ∫ x in Set.Ioi (w+a), Real.exp (-c*a^2/2) * gauss (c/2) w x :=
        setIntegral_mono_on hint1 hint2 measurableSet_Ioi hdom
    _ = Real.exp (-c*a^2/2) * ∫ x in Set.Ioi (w+a), gauss (c/2) w x := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ Real.exp (-c*a^2/2) * ∫ x, gauss (c/2) w x := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact setIntegral_le_integral (gauss_integrable (by linarith) w)
          (Filter.Eventually.of_forall (fun x => (gauss_pos _ w x).le))
    _ = Real.exp (-c*a^2/2) * Real.sqrt (2*π/c) := by
        rw [gauss_integral (c/2) w]
        congr 2
        field_simp

theorem gauss_tail_Iic {c : ℝ} (hc : 0 < c) (w : ℝ) {a : ℝ} (ha : 0 < a) :
    (∫ x in Set.Iic (w-a), gauss c w x) ≤ Real.exp (-c*a^2/2) * Real.sqrt (2*π/c) := by
  have hdom : ∀ x ∈ Set.Iic (w-a), gauss c w x ≤ Real.exp (-c*a^2/2) * gauss (c/2) w x := by
    intro x hx
    simp only [Set.mem_Iic] at hx
    simp only [gauss, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : a ≤ w - x := by linarith
    have h2 : a^2 ≤ (x-w)^2 := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 hc.le
    linarith
  have hint1 : IntegrableOn (gauss c w) (Set.Iic (w-a)) := (gauss_integrable hc w).integrableOn
  have hint2 : IntegrableOn (fun x => Real.exp (-c*a^2/2) * gauss (c/2) w x) (Set.Iic (w-a)) :=
    ((gauss_integrable (by linarith) w).const_mul _).integrableOn
  calc (∫ x in Set.Iic (w-a), gauss c w x)
      ≤ ∫ x in Set.Iic (w-a), Real.exp (-c*a^2/2) * gauss (c/2) w x :=
        setIntegral_mono_on hint1 hint2 measurableSet_Iic hdom
    _ = Real.exp (-c*a^2/2) * ∫ x in Set.Iic (w-a), gauss (c/2) w x := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ Real.exp (-c*a^2/2) * ∫ x, gauss (c/2) w x := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact setIntegral_le_integral (gauss_integrable (by linarith) w)
          (Filter.Eventually.of_forall (fun x => (gauss_pos _ w x).le))
    _ = Real.exp (-c*a^2/2) * Real.sqrt (2*π/c) := by
        rw [gauss_integral (c/2) w]
        congr 2
        field_simp

theorem gauss_intervalIntegrable {c : ℝ} (hc : 0 < c) (w a b : ℝ) :
    IntervalIntegrable (gauss c w) volume a b :=
  (gauss_integrable hc w).intervalIntegrable

/-- Lower bound for an interval integral of the Gaussian. -/
theorem gauss_interval_ge {c : ℝ} (hc : 0 < c) {w a b1 b2 : ℝ} (ha : 0 < a)
    (h1 : b1 ≤ w - a) (h2 : w + a ≤ b2) :
    Real.sqrt (π/c) - 2*(Real.exp (-c*a^2/2) * Real.sqrt (2*π/c))
      ≤ ∫ x in b1..b2, gauss c w x := by
  have hb12 : b1 ≤ b2 := by linarith
  have hint := gauss_integrable hc w
  -- split off the left tail
  have hsplit1 : (∫ x in Set.Iic b1, gauss c w x) + (∫ x in Set.Ioi b1, gauss c w x)
      = ∫ x, gauss c w x := by
    have := MeasureTheory.integral_add_compl (μ := volume) (f := gauss c w)
      (measurableSet_Iic (a := b1)) hint
    rwa [Set.compl_Iic] at this
  have hsplit2 : (∫ x in Set.Ioc b1 b2, gauss c w x) + (∫ x in Set.Ioi b2, gauss c w x)
      = ∫ x in Set.Ioi b1, gauss c w x := by
    rw [← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      hint.integrableOn hint.integrableOn, Set.Ioc_union_Ioi_eq_Ioi hb12]
  have hleft : (∫ x in Set.Iic b1, gauss c w x) ≤ Real.exp (-c*a^2/2) * Real.sqrt (2*π/c) := by
    refine le_trans ?_ (gauss_tail_Iic hc w ha)
    exact MeasureTheory.setIntegral_mono_set hint.integrableOn
      (Filter.Eventually.of_forall (fun x => (gauss_pos c w x).le))
      (HasSubset.Subset.eventuallyLE (Set.Iic_subset_Iic.2 h1))
  have hright : (∫ x in Set.Ioi b2, gauss c w x) ≤ Real.exp (-c*a^2/2) * Real.sqrt (2*π/c) := by
    refine le_trans ?_ (gauss_tail_Ioi hc w ha)
    exact MeasureTheory.setIntegral_mono_set hint.integrableOn
      (Filter.Eventually.of_forall (fun x => (gauss_pos c w x).le))
      (HasSubset.Subset.eventuallyLE (Set.Ioi_subset_Ioi h2))
  rw [intervalIntegral.integral_of_le hb12]
  rw [gauss_integral c w] at hsplit1
  linarith

/-- Upper bound for a Gaussian sum by the Gaussian integral. -/
theorem gauss_sum_upper {c : ℝ} (hc : 0 < c) {w : ℝ} {k₁ k₂ m : ℕ}
    (h1 : k₁ ≤ m) (h2 : m + 2 ≤ k₂) (hmw : (m:ℝ) ≤ w) (hwm : w ≤ (m:ℝ)+1) :
    ∑ k ∈ Finset.Ico k₁ k₂, gauss c w k ≤ Real.sqrt (π/c) + 2 := by
  have hmono : MonotoneOn (gauss c w) (Set.Icc (k₁:ℝ) (m:ℝ)) := by
    refine (gauss_monotoneOn hc.le w).mono ?_
    intro x hx
    exact le_trans hx.2 hmw
  have hanti : AntitoneOn (gauss c w) (Set.Icc ((m:ℝ)+1) (k₂:ℝ)) := by
    refine (gauss_antitoneOn hc.le w).mono ?_
    intro x hx
    exact le_trans hwm hx.1
  -- left part
  have hA : ∑ k ∈ Finset.Ico k₁ m, gauss c w k ≤ ∫ x in (k₁:ℝ)..(m:ℝ), gauss c w x :=
    MonotoneOn.sum_le_integral_Ico h1 hmono
  -- right part
  have hcast : ((m+1 : ℕ) : ℝ) = (m:ℝ) + 1 := by push_cast; ring
  have hB : ∑ k ∈ Finset.Ico (m+2) k₂, gauss c w k ≤ ∫ x in ((m:ℝ)+1)..(k₂:ℝ), gauss c w x := by
    have hkey := AntitoneOn.sum_le_integral_Ico (f := gauss c w) (a := m+1) (b := k₂)
      (by omega) (by rw [hcast]; exact hanti)
    rw [hcast] at hkey
    refine le_trans ?_ hkey
    have hshift : ∑ i ∈ Finset.Ico (m+1) k₂, gauss c w ((i+1 : ℕ) : ℝ)
        = ∑ j ∈ Finset.Ico (m+2) (k₂+1), gauss c w (j : ℝ) :=
      Finset.sum_Ico_add' (fun j : ℕ => gauss c w (j:ℝ)) (m+1) k₂ 1
    rw [hshift]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => (gauss_pos c w i).le)
    apply Finset.Ico_subset_Ico le_rfl (by omega)
  -- combine
  have hsplit1 : ∑ k ∈ Finset.Ico k₁ k₂, gauss c w k
      = ∑ k ∈ Finset.Ico k₁ m, gauss c w k + ∑ k ∈ Finset.Ico m k₂, gauss c w k :=
    (Finset.sum_Ico_consecutive _ h1 (by omega)).symm
  have hsplit2 : ∑ k ∈ Finset.Ico m k₂, gauss c w k
      = gauss c w m + ∑ k ∈ Finset.Ico (m+1) k₂, gauss c w k :=
    Finset.sum_eq_sum_Ico_succ_bot (by omega) _
  have hsplit3 : ∑ k ∈ Finset.Ico (m+1) k₂, gauss c w k
      = gauss c w ((m:ℝ)+1) + ∑ k ∈ Finset.Ico (m+2) k₂, gauss c w k := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega) (fun k : ℕ => gauss c w (k:ℝ)), hcast]
  have hint : (∫ x in (k₁:ℝ)..(m:ℝ), gauss c w x) + (∫ x in ((m:ℝ)+1)..(k₂:ℝ), gauss c w x)
      ≤ Real.sqrt (π/c) := by
    have hpos : 0 ≤ ∫ x in (m:ℝ)..((m:ℝ)+1), gauss c w x :=
      intervalIntegral.integral_nonneg (by linarith) (fun x _ => (gauss_pos c w x).le)
    have hadd1 : (∫ x in (k₁:ℝ)..(m:ℝ), gauss c w x) + (∫ x in (m:ℝ)..((m:ℝ)+1), gauss c w x)
        = ∫ x in (k₁:ℝ)..((m:ℝ)+1), gauss c w x :=
      intervalIntegral.integral_add_adjacent_intervals
        (gauss_intervalIntegrable hc w _ _) (gauss_intervalIntegrable hc w _ _)
    have hadd2 : (∫ x in (k₁:ℝ)..((m:ℝ)+1), gauss c w x) + (∫ x in ((m:ℝ)+1)..(k₂:ℝ), gauss c w x)
        = ∫ x in (k₁:ℝ)..(k₂:ℝ), gauss c w x :=
      intervalIntegral.integral_add_adjacent_intervals
        (gauss_intervalIntegrable hc w _ _) (gauss_intervalIntegrable hc w _ _)
    have hle : (∫ x in (k₁:ℝ)..(k₂:ℝ), gauss c w x) ≤ Real.sqrt (π/c) :=
      gauss_interval_le hc w _ _ (by exact_mod_cast (by omega : k₁ ≤ k₂))
    linarith
  have h1' := gauss_le_one hc.le w (m:ℝ)
  have h2' := gauss_le_one hc.le w ((m:ℝ)+1)
  rw [hsplit1, hsplit2, hsplit3]
  linarith

/-- Lower bound for a Gaussian sum by the Gaussian integral. -/
theorem gauss_sum_lower {c : ℝ} (hc : 0 < c) {w a : ℝ} {k₁ k₂ m : ℕ}
    (h1 : k₁ ≤ m) (h2 : m + 1 ≤ k₂) (hmw : (m:ℝ) ≤ w) (hwm : w ≤ (m:ℝ)+1)
    (ha : 0 < a) (hb1 : (k₁:ℝ) ≤ w - a) (hb2 : w + a ≤ (k₂:ℝ)) :
    Real.sqrt (π/c) - 2 - 2*(Real.exp (-c*a^2/2) * Real.sqrt (2*π/c))
      ≤ ∑ k ∈ Finset.Ico k₁ k₂, gauss c w k := by
  have hcast : ((m+1 : ℕ) : ℝ) = (m:ℝ) + 1 := by push_cast; ring
  have hmono : MonotoneOn (gauss c w) (Set.Icc (k₁:ℝ) (m:ℝ)) := by
    refine (gauss_monotoneOn hc.le w).mono ?_
    intro x hx
    exact le_trans hx.2 hmw
  have hanti : AntitoneOn (gauss c w) (Set.Icc ((m:ℝ)+1) (k₂:ℝ)) := by
    refine (gauss_antitoneOn hc.le w).mono ?_
    intro x hx
    exact le_trans hwm hx.1
  -- left half
  have hA : (∫ x in (k₁:ℝ)..(m:ℝ), gauss c w x) ≤ ∑ k ∈ Finset.Ico k₁ m, gauss c w k + 1 := by
    have hkey := MonotoneOn.integral_le_sum_Ico h1 hmono
    have hshift : ∑ i ∈ Finset.Ico k₁ m, gauss c w ((i+1 : ℕ) : ℝ)
        = ∑ j ∈ Finset.Ico (k₁+1) (m+1), gauss c w (j : ℝ) :=
      Finset.sum_Ico_add' (fun j : ℕ => gauss c w (j:ℝ)) k₁ m 1
    rw [hshift] at hkey
    have hsub : ∑ j ∈ Finset.Ico (k₁+1) (m+1), gauss c w (j : ℝ)
        ≤ ∑ j ∈ Finset.Ico k₁ (m+1), gauss c w (j : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => (gauss_pos c w i).le)
      exact Finset.Ico_subset_Ico (by omega) le_rfl
    have htop : ∑ j ∈ Finset.Ico k₁ (m+1), gauss c w (j : ℝ)
        = ∑ j ∈ Finset.Ico k₁ m, gauss c w (j : ℝ) + gauss c w (m : ℝ) :=
      Finset.sum_Ico_succ_top h1 _
    have hone := gauss_le_one hc.le w (m:ℝ)
    linarith
  -- right half
  have hB : (∫ x in ((m:ℝ)+1)..(k₂:ℝ), gauss c w x)
      ≤ ∑ k ∈ Finset.Ico (m+1) k₂, gauss c w k := by
    have hkey := AntitoneOn.integral_le_sum_Ico (f := gauss c w) (a := m+1) (b := k₂)
      h2 (by rw [hcast]; exact hanti)
    rwa [hcast] at hkey
  -- middle unit interval
  have hmid : (∫ x in (m:ℝ)..((m:ℝ)+1), gauss c w x) ≤ 1 := by
    have := intervalIntegral.integral_mono_on (f := gauss c w) (g := fun _ => (1:ℝ))
      (a := (m:ℝ)) (b := (m:ℝ)+1)
      (by linarith) (gauss_intervalIntegrable hc w _ _) intervalIntegrable_const
      (fun x _ => gauss_le_one hc.le w x)
    refine le_trans this (le_of_eq ?_)
    simp
  have hadd1 : (∫ x in (k₁:ℝ)..(m:ℝ), gauss c w x) + (∫ x in (m:ℝ)..((m:ℝ)+1), gauss c w x)
      = ∫ x in (k₁:ℝ)..((m:ℝ)+1), gauss c w x :=
    intervalIntegral.integral_add_adjacent_intervals
      (gauss_intervalIntegrable hc w _ _) (gauss_intervalIntegrable hc w _ _)
  have hadd2 : (∫ x in (k₁:ℝ)..((m:ℝ)+1), gauss c w x) + (∫ x in ((m:ℝ)+1)..(k₂:ℝ), gauss c w x)
      = ∫ x in (k₁:ℝ)..(k₂:ℝ), gauss c w x :=
    intervalIntegral.integral_add_adjacent_intervals
      (gauss_intervalIntegrable hc w _ _) (gauss_intervalIntegrable hc w _ _)
  have hbig := gauss_interval_ge hc (w := w) (a := a) (b1 := (k₁:ℝ)) (b2 := (k₂:ℝ)) ha
    (by linarith) (by linarith)
  have hsplit1 : ∑ k ∈ Finset.Ico k₁ k₂, gauss c w k
      = ∑ k ∈ Finset.Ico k₁ m, gauss c w k + ∑ k ∈ Finset.Ico m k₂, gauss c w k :=
    (Finset.sum_Ico_consecutive _ h1 (by omega)).symm
  have hsplit2 : ∑ k ∈ Finset.Ico m k₂, gauss c w k
      = gauss c w m + ∑ k ∈ Finset.Ico (m+1) k₂, gauss c w k :=
    Finset.sum_eq_sum_Ico_succ_bot (by omega) _
  have hgm : 0 < gauss c w (m:ℝ) := gauss_pos c w _
  rw [hsplit1, hsplit2]
  linarith

section Saddle

variable {n : ℕ} {r w : ℝ}

/-- Basic size facts implied by the standing hypotheses. -/
theorem setup_facts (hr : 2048 ≤ r) (hw : w = Real.exp r) :
    0 < w ∧ 2 * Real.exp (3*r/5) ≤ w ∧ (100:ℝ) ≤ Real.exp (3*r/5) := by
  have hr0 : (0:ℝ) < r := by linarith
  have hw0 : 0 < w := by rw [hw]; exact Real.exp_pos r
  refine ⟨hw0, ?_, ?_⟩
  · have h1 : (2:ℝ) ≤ Real.exp (2*r/5) := by
      have := sq_le_exp (by linarith : (0:ℝ) ≤ 2*r/5)
      nlinarith
    have h2 : Real.exp (3*r/5) * 2 ≤ Real.exp (3*r/5) * Real.exp (2*r/5) :=
      mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    rw [← Real.exp_add] at h2
    rw [hw, show 3*r/5 + 2*r/5 = r by ring] at *
    linarith
  · have := sq_le_exp (by linarith : (0:ℝ) ≤ 3*r/5)
    nlinarith

/-- **The central estimate.**  On the window `|k - w| ≤ e^{3r/5}` the Dobinski term agrees with
the Gaussian `exp (psi n w) · exp (-(r+1)(k-w)²/(2w))` up to a relative error `5 e^{-r/10}`. -/
theorem central_pointwise (hr : 2048 ≤ r) (hw : w = Real.exp r) (hn : (n:ℝ) = r * w)
    {k : ℕ} (hk1 : w - Real.exp (3*r/5) ≤ (k:ℝ)) (hk2 : (k:ℝ) ≤ w + Real.exp (3*r/5)) :
    |bterm n k - Real.exp (psi n w) * gauss ((r+1)/(2*w)) w k|
      ≤ 5 * Real.exp (-r/10) * (Real.exp (psi n w) * gauss ((r+1)/(2*w)) w k) := by
  obtain ⟨hw0, hMw, hM8⟩ := setup_facts hr hw
  have hr0 : (0:ℝ) < r := by linarith
  set M : ℝ := Real.exp (3*r/5) with hMdef
  set q : ℝ := Real.exp (-r/10) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hkw : w/2 ≤ (k:ℝ) := by linarith
  have hk0 : (0:ℝ) < k := by linarith [hw0]
  have hkne : k ≠ 0 := by
    intro h; rw [h] at hk0; simp at hk0
  have hk2' : 2 ≤ k := by
    have hw4 : (4:ℝ) ≤ w/2 := by linarith
    have : (2:ℝ) ≤ (k:ℝ) := by linarith
    exact_mod_cast this
  -- Taylor expansion of the exponent
  set s : ℝ := (k:ℝ) - w with hsdef
  have hs : |s| ≤ M := by
    rw [abs_le]
    constructor <;> [linarith; linarith]
  have hks : (k:ℝ) = w + s := by rw [hsdef]; ring
  have htay : |psi n (k:ℝ) - psi n w + (r+1)*s^2/(2*w)| ≤ q := by
    rw [hks]
    exact psi_taylor hr hw hn hs
  -- the Stirling defect is negligible
  have hth1 : 0 ≤ theta k := theta_nonneg hkne
  have hth2 : theta k ≤ q := by
    refine (theta_le hk2').trans ?_
    have h1 : (1:ℝ)/k ≤ 2/w := by
      rw [div_le_div_iff₀ hk0 hw0]
      linarith
    refine h1.trans ?_
    -- 2/w = 2 e^{-r} ≤ e^{-r/10}
    rw [hqdef, hw, div_le_iff₀ (Real.exp_pos r), ← Real.exp_add]
    have : (2:ℝ) ≤ Real.exp (-r/10 + r) := by
      have := sq_le_exp (by linarith : (0:ℝ) ≤ -r/10 + r)
      nlinarith
    linarith
  -- assemble
  set P : ℝ := Real.exp (psi n w) with hPdef
  set c : ℝ := (r+1)/(2*w) with hcdef
  have hPg : P * gauss c w (k:ℝ) = Real.exp (psi n w - (r+1)*s^2/(2*w)) := by
    rw [hPdef, gauss, ← Real.exp_add, hcdef, ← hsdef]
    congr 1
    field_simp
    ring
  set t : ℝ := (psi n (k:ℝ) - theta k) - (psi n w - (r+1)*s^2/(2*w)) with htdef
  have hta : |t| ≤ 2*q := by
    have e1 : t = (psi n (k:ℝ) - psi n w + (r+1)*s^2/(2*w)) + (-(theta k)) := by
      rw [htdef]; ring
    rw [e1]
    have := abs_add_le (psi n (k:ℝ) - psi n w + (r+1)*s^2/(2*w)) (-(theta k))
    rw [abs_neg] at this
    have h2 : |theta k| = theta k := abs_of_nonneg hth1
    linarith
  have hterm : bterm n k = P * gauss c w (k:ℝ) * Real.exp t := by
    rw [bterm_eq hkne, hPg, ← Real.exp_add, htdef]
    congr 1
    ring
  have hone : |t| ≤ 1 := by
    refine hta.trans ?_
    have : q ≤ 1/2 := by
      rw [hqdef]
      have h1 : Real.exp (-r/10) * Real.exp (r/10) = 1 := by
        rw [← Real.exp_add, show -r/10 + r/10 = 0 by ring, Real.exp_zero]
      have h2 : (2:ℝ) ≤ Real.exp (r/10) := by
        have := sq_le_exp (by linarith : (0:ℝ) ≤ r/10)
        nlinarith
      nlinarith [Real.exp_pos (-r/10), Real.exp_pos (r/10)]
    linarith
  have hexp := Real.abs_exp_sub_one_le hone
  have hPgpos : 0 < P * gauss c w (k:ℝ) := by
    rw [hPdef]
    exact mul_pos (Real.exp_pos _) (gauss_pos _ _ _)
  have : bterm n k - P * gauss c w (k:ℝ) = (P * gauss c w (k:ℝ)) * (Real.exp t - 1) := by
    rw [hterm]; ring
  rw [this, abs_mul, abs_of_pos hPgpos]
  have h4 : |Real.exp t - 1| ≤ 4*q := by
    calc |Real.exp t - 1| ≤ 2 * |t| := hexp
      _ ≤ 2 * (2*q) := by linarith
      _ = 4*q := by ring
  calc P * gauss c w (k:ℝ) * |Real.exp t - 1|
      ≤ P * gauss c w (k:ℝ) * (4*q) := by
        exact mul_le_mul_of_nonneg_left h4 hPgpos.le
    _ ≤ 5 * q * (P * gauss c w (k:ℝ)) := by nlinarith [hPgpos, hq0]

/-- The integer endpoints of the window. -/
theorem window_facts (hr : 2048 ≤ r) (hw : w = Real.exp r) :
    w - Real.exp (3*r/5) ≤ (⌈w - Real.exp (3*r/5)⌉₊ : ℝ)
  ∧ ((⌈w - Real.exp (3*r/5)⌉₊ : ℝ) ≤ w - Real.exp (3*r/5) + 1)
  ∧ ((⌊w + Real.exp (3*r/5)⌋₊ : ℝ) ≤ w + Real.exp (3*r/5))
  ∧ (w + Real.exp (3*r/5) - 1 ≤ (⌊w + Real.exp (3*r/5)⌋₊ : ℝ))
  ∧ ((⌊w⌋₊ : ℝ) ≤ w) ∧ (w ≤ (⌊w⌋₊:ℝ) + 1)
  ∧ (⌈w - Real.exp (3*r/5)⌉₊ ≤ ⌊w⌋₊) ∧ (⌊w⌋₊ + 2 ≤ ⌊w + Real.exp (3*r/5)⌋₊)
  ∧ (1 ≤ ⌈w - Real.exp (3*r/5)⌉₊) := by
  obtain ⟨hw0, hMw, hM8⟩ := setup_facts hr hw
  set M : ℝ := Real.exp (3*r/5) with hMdef
  have hM0 : (0:ℝ) < M := by linarith
  have hpos1 : (0:ℝ) ≤ w - M := by linarith
  have hpos2 : (0:ℝ) ≤ w + M := by linarith
  have hc1 : w - M ≤ (⌈w - M⌉₊ : ℝ) := Nat.le_ceil _
  have hc2 : ((⌈w - M⌉₊ : ℝ)) ≤ w - M + 1 := (Nat.ceil_lt_add_one hpos1).le
  have hf1 : ((⌊w + M⌋₊ : ℝ)) ≤ w + M := Nat.floor_le hpos2
  have hf2 : w + M - 1 ≤ ((⌊w + M⌋₊ : ℝ)) := by
    have := Nat.lt_floor_add_one (w + M)
    linarith
  have hm1 : ((⌊w⌋₊ : ℝ)) ≤ w := Nat.floor_le hw0.le
  have hm2 : w ≤ ((⌊w⌋₊:ℝ)) + 1 := (Nat.lt_floor_add_one w).le
  refine ⟨hc1, hc2, hf1, hf2, hm1, hm2, ?_, ?_, ?_⟩
  · have : ((⌈w - M⌉₊ : ℝ)) < ((⌊w⌋₊ : ℝ)) + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  · have h : ((⌊w⌋₊ : ℝ)) + 2 ≤ ((⌊w + M⌋₊ : ℝ)) := by linarith
    exact_mod_cast h
  · have h : (1:ℝ) ≤ ((⌈w - M⌉₊ : ℝ)) := by linarith
    exact_mod_cast h

/-- Beyond the window the Dobinski terms decay geometrically. -/
theorem brat_edge_upper (hr : 2048 ≤ r) (hw : w = Real.exp r) (hn : (n:ℝ) = r * w)
    {k : ℕ} (hk : w + Real.exp (3*r/5) - 1 ≤ (k:ℝ)) :
    brat n k ≤ Real.exp (-r*Real.exp (3*r/5)/(4*w)) := by
  obtain ⟨hw0, hMw, hM8⟩ := setup_facts hr hw
  have hr0 : (0:ℝ) < r := by linarith
  set M : ℝ := Real.exp (3*r/5) with hMdef
  have hk0 : (0:ℝ) < k := by linarith
  have hkpos : 0 < (k:ℝ) + 1 := by linarith
  -- upper bound for the power
  have h1 : ((k:ℝ)+1)/k = 1 + 1/k := by field_simp
  have hpow : (((k:ℝ)+1)/k)^n ≤ Real.exp ((n:ℝ)/k) := by
    have h2 : (1:ℝ) + 1/k ≤ Real.exp (1/k) := by
      have := Real.add_one_le_exp (1/(k:ℝ)); linarith
    calc (((k:ℝ)+1)/k)^n ≤ (Real.exp (1/k))^n := by
          rw [h1]; exact pow_le_pow_left₀ (by positivity) h2 n
      _ = Real.exp ((n:ℝ)*(1/k)) := by rw [← Real.exp_nat_mul]
      _ = Real.exp ((n:ℝ)/k) := by rw [mul_one_div]
  have hexp1 : Real.exp ((n:ℝ)/k) ≤ Real.exp (r*w/(w+M-1)) := by
    apply Real.exp_le_exp.2
    rw [hn, div_le_div_iff₀ hk0 (by linarith)]
    nlinarith [hk, hw0, hr0]
  have hden : w + M ≤ (k:ℝ) + 1 := by linarith
  -- final numeric estimate
  have hkey : Real.exp (r*w/(w+M-1)) / (w+M) ≤ Real.exp (-r*M/(4*w)) := by
    rw [div_le_iff₀ (by linarith)]
    have hsum : r*w/(w+M-1) ≤ -r*M/(4*w) + r := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < w+M-1)]
      have hfac : (-r*M/(4*w) + r) * (w+M-1) = r*(w+M-1) - r*M*(w+M-1)/(4*w) := by ring
      rw [hfac]
      have hmul : r*M*(w+M-1)/(4*w) ≤ r*(M-1) := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 4*w)]
        have hM0 : (0:ℝ) < M := by linarith
        have hsq : M*(2*M) ≤ M*w := mul_le_mul_of_nonneg_left hMw hM0.le
        have hcore : M*(w+M-1) ≤ 4*w*(M-1) := by nlinarith [hsq, hM8, hMw, hw0]
        nlinarith [hcore, hr0]
      nlinarith [hmul]
    calc Real.exp (r*w/(w+M-1)) ≤ Real.exp (-r*M/(4*w) + r) := Real.exp_le_exp.2 hsum
      _ = Real.exp (-r*M/(4*w)) * Real.exp r := by rw [Real.exp_add]
      _ ≤ Real.exp (-r*M/(4*w)) * (w+M) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          rw [← hw]; linarith [Real.exp_pos (3*r/5)]
  have hb : brat n k = (((k:ℝ)+1)/k)^n * (1/((k:ℝ)+1)) := by simp only [brat]; ring
  rw [hb]
  calc (((k:ℝ)+1)/k)^n * (1/((k:ℝ)+1))
      ≤ Real.exp (r*w/(w+M-1)) * (1/(w+M)) := by
        apply mul_le_mul (hpow.trans hexp1) _ (by positivity) (Real.exp_pos _).le
        exact one_div_le_one_div_of_le (by linarith) hden
    _ = Real.exp (r*w/(w+M-1)) / (w+M) := by ring
    _ ≤ Real.exp (-r*M/(4*w)) := hkey

/-- Below the window the Dobinski terms grow geometrically. -/
theorem brat_edge_lower (hr : 2048 ≤ r) (hw : w = Real.exp r) (hn : (n:ℝ) = r * w)
    {k : ℕ} (hk1 : w - Real.exp (3*r/5) - 1 ≤ (k:ℝ)) (hk2 : (k:ℝ) ≤ w - Real.exp (3*r/5)) :
    Real.exp (r*Real.exp (3*r/5)/(2*w)) ≤ brat n k := by
  obtain ⟨hw0, hMw, hM8⟩ := setup_facts hr hw
  have hr0 : (0:ℝ) < r := by linarith
  set M : ℝ := Real.exp (3*r/5) with hMdef
  have hk4 : w/4 ≤ (k:ℝ) := by linarith
  have hk0 : (0:ℝ) < k := by linarith
  -- lower bound for the logarithm
  have hinv : (1:ℝ)/k ≤ 1/4 := by
    rw [div_le_div_iff₀ hk0 (by norm_num)]
    linarith
  have hinv0 : (0:ℝ) < 1/(k:ℝ) := by positivity
  have hlog : (1:ℝ)/k - (1/(k:ℝ))^2 ≤ Real.log (1 + 1/k) := by
    have habs : |(1:ℝ)/(k:ℝ)| ≤ 1/2 := by
      rw [abs_of_pos hinv0]; linarith
    have h := log_taylor3 habs
    rw [abs_le] at h
    have habs2 : |(1:ℝ)/(k:ℝ)|^3 = (1/(k:ℝ))^3 := by
      rw [abs_of_pos hinv0]
    rw [habs2] at h
    have hcube : 2*(1/(k:ℝ))^3 ≤ (1/(k:ℝ))^2/2 := by
      have : (1/(k:ℝ))^3 = (1/(k:ℝ))^2 * (1/(k:ℝ)) := by ring
      rw [this]
      nlinarith [sq_nonneg (1/(k:ℝ)), hinv, hinv0]
    linarith [h.1]
  have h1 : ((k:ℝ)+1)/k = 1 + 1/k := by field_simp
  have hpow : Real.exp ((n:ℝ)*(1/(k:ℝ) - (1/(k:ℝ))^2)) ≤ (((k:ℝ)+1)/k)^n := by
    have he : (((k:ℝ)+1)/k)^n = Real.exp ((n:ℝ) * Real.log (1 + 1/(k:ℝ))) := by
      rw [Real.exp_nat_mul, Real.exp_log (by positivity), h1]
    rw [he]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n))
  have hden : (k:ℝ) + 1 ≤ w := by linarith
  have hb : brat n k = (((k:ℝ)+1)/k)^n * (1/((k:ℝ)+1)) := by simp only [brat]; ring
  -- exponent estimate
  have hexp : r*M/(2*w) ≤ (n:ℝ)*(1/(k:ℝ) - (1/(k:ℝ))^2) - r := by
    have hA : r + r*M/w ≤ (n:ℝ)*(1/(k:ℝ)) := by
      rw [hn, mul_one_div, le_div_iff₀ hk0]
      have hkey2 : (w+M)*(k:ℝ) ≤ w^2 := by nlinarith [hk2, hMw, hw0]
      have hrw : r + r*M/w = r*(w+M)/w := by field_simp
      rw [hrw, div_mul_eq_mul_div, div_le_iff₀ hw0]
      nlinarith [hkey2, hr0, hw0]
    have hB : (n:ℝ)*((1/(k:ℝ))^2) ≤ 16*r/w := by
      rw [hn]
      have hk2' : w^2 ≤ 16*(k:ℝ)^2 := by nlinarith [hk4, hw0]
      rw [← sub_nonneg]
      have hrw : 16*r/w - r*w*((1/(k:ℝ))^2) = r*(16*(k:ℝ)^2 - w^2)/(w*(k:ℝ)^2) := by
        field_simp
      rw [hrw]
      apply div_nonneg _ (by positivity)
      nlinarith [hk2', hr0]
    have hMbig : 16*r/w ≤ r*M/(2*w) := by
      rw [div_le_div_iff₀ hw0 (by linarith)]
      nlinarith [hM8, hr0, hw0]
    have : (n:ℝ)*(1/(k:ℝ) - (1/(k:ℝ))^2) = (n:ℝ)*(1/(k:ℝ)) - (n:ℝ)*((1/(k:ℝ))^2) := by ring
    rw [this]
    have hMw2 : r*M/w = 2*(r*M/(2*w)) := by field_simp
    linarith [hA, hB, hMbig, hMw2]
  rw [hb]
  calc Real.exp (r*M/(2*w))
      ≤ Real.exp ((n:ℝ)*(1/(k:ℝ) - (1/(k:ℝ))^2) - r) := Real.exp_le_exp.2 hexp
    _ = Real.exp ((n:ℝ)*(1/(k:ℝ) - (1/(k:ℝ))^2)) * (1/w) := by
        rw [Real.exp_sub, hw]; ring
    _ ≤ (((k:ℝ)+1)/k)^n * (1/((k:ℝ)+1)) := by
        apply mul_le_mul hpow (one_div_le_one_div_of_le (by linarith) hden)
          (by positivity) (by positivity)

theorem one_sub_exp_neg_lower {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x/2 ≤ 1 - Real.exp (-x) := by
  have h := exp_neg_le_quad x hx0
  nlinarith

theorem tail_numeric (hr : 2048 ≤ r) :
    16 * Real.exp (2*r/5) * Real.exp (-Real.exp (r/5)/5) ≤ Real.exp (-r/10) := by
  have hr0 : (0:ℝ) < r := by linarith
  have h16 : (16:ℝ) ≤ Real.exp (r/10) := by
    have := sq_le_exp (by linarith : (0:ℝ) ≤ r/10)
    nlinarith
  have hE : 3*r/5 ≤ Real.exp (r/5)/5 := by
    have := sq_le_exp (by linarith : (0:ℝ) ≤ r/5)
    nlinarith
  have h1 : Real.exp (2*r/5) * Real.exp (-Real.exp (r/5)/5) ≤ Real.exp (-r/5) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  calc 16 * Real.exp (2*r/5) * Real.exp (-Real.exp (r/5)/5)
      = 16 * (Real.exp (2*r/5) * Real.exp (-Real.exp (r/5)/5)) := by ring
    _ ≤ Real.exp (r/10) * Real.exp (-r/5) := by
        apply mul_le_mul h16 h1 (by positivity) (Real.exp_pos _).le
    _ = Real.exp (-r/10) := by rw [← Real.exp_add]; congr 1; ring

/-- The Dobinski terms at the ends of the window are negligible. -/
theorem bterm_edge_small (hr : 2048 ≤ r) (hw : w = Real.exp r) (hn : (n:ℝ) = r * w)
    {k : ℕ} (hk1 : w - Real.exp (3*r/5) ≤ (k:ℝ)) (hk2 : (k:ℝ) ≤ w + Real.exp (3*r/5))
    (hfar : Real.exp (3*r/5) - 1 ≤ |(k:ℝ) - w|) :
    bterm n k ≤ Real.exp (psi n w) * Real.exp (-Real.exp (r/5)/5) := by
  obtain ⟨hw0, hMw, hM8⟩ := setup_facts hr hw
  have hr0 : (0:ℝ) < r := by linarith
  set M : ℝ := Real.exp (3*r/5) with hMdef
  have hkne : k ≠ 0 := by
    intro h
    rw [h] at hk1
    simp at hk1
    linarith
  set s : ℝ := (k:ℝ) - w with hsdef
  have hs : |s| ≤ M := by
    rw [abs_le]; constructor <;> [linarith; linarith]
  have hks : (k:ℝ) = w + s := by rw [hsdef]; ring
  have htay : |psi n (k:ℝ) - psi n w + (r+1)*s^2/(2*w)| ≤ Real.exp (-r/10) := by
    rw [hks]; exact psi_taylor hr hw hn hs
  have habs : (M-1)^2 ≤ s^2 := by
    have h1 : (M-1) ≤ |s| := hfar
    nlinarith [abs_nonneg s, sq_abs s]
  have hMsq : M^2/2 ≤ (M-1)^2 := by nlinarith [hM8]
  have hkey : Real.exp (r/5)/4 ≤ (r+1)*s^2/(2*w) := by
    have hM2 : M^2 = Real.exp (6*r/5) := by
      rw [hMdef, sq, ← Real.exp_add]; congr 1; ring
    have hexp : M^2/(4*w) = Real.exp (r/5)/4 := by
      rw [hM2, hw, show (6*r/5 : ℝ) = r/5 + r by ring, Real.exp_add]
      field_simp
    rw [← hexp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hMsq, habs, hw0, hr0, sq_nonneg M]
  have hq2 : Real.exp (-r/10) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hpsi_le : psi n (k:ℝ) ≤ psi n w - Real.exp (r/5)/4 + 1 := by
    have := (abs_le.1 htay).2
    linarith
  have hbig : (20:ℝ) ≤ Real.exp (r/5) := by
    have := sq_le_exp (by linarith : (0:ℝ) ≤ r/5)
    nlinarith
  calc bterm n k ≤ Real.exp (psi n (k:ℝ)) := bterm_le_exp_psi hkne
    _ ≤ Real.exp (psi n w - Real.exp (r/5)/4 + 1) := Real.exp_le_exp.2 hpsi_le
    _ ≤ Real.exp (psi n w + -Real.exp (r/5)/5) := by
        apply Real.exp_le_exp.2; linarith
    _ = Real.exp (psi n w) * Real.exp (-Real.exp (r/5)/5) := by
        rw [← Real.exp_add]

end Saddle

end Q565
