/-
# Q565 : aggregation of the saddle-point estimates, and the unconditional first correction

This file sums the pointwise saddle estimates of `RequestProject.Saddle` over all Dobinski
terms, identifies the resulting saddle scale with `gQ n * e`, and deduces the unconditional
first-correction theorem for the Bell numbers.
-/
import RMS.Q565Saddle

open Real Filter Asymptotics
open scoped BigOperators Nat Topology

set_option maxHeartbeats 2000000

namespace Q565

section Aggregate

variable {n : ℕ} {r w : ℝ}

/-! ### Summing the central estimate -/

/-- Summed form of `central_pointwise` over the central window. -/
theorem central_sum_bound (hr : 2048 ≤ r) (hw : w = Real.exp r) (hn : (n:ℝ) = r * w) :
    |∑ k ∈ Finset.Ico ⌈w - Real.exp (3*r/5)⌉₊ ⌊w + Real.exp (3*r/5)⌋₊, bterm n k
        - Real.exp (psi n w)
            * ∑ k ∈ Finset.Ico ⌈w - Real.exp (3*r/5)⌉₊ ⌊w + Real.exp (3*r/5)⌋₊,
                gauss ((r+1)/(2*w)) w k|
      ≤ 5 * Real.exp (-r/10)
          * (Real.exp (psi n w)
              * ∑ k ∈ Finset.Ico ⌈w - Real.exp (3*r/5)⌉₊ ⌊w + Real.exp (3*r/5)⌋₊,
                  gauss ((r+1)/(2*w)) w k) := by
  obtain ⟨hw0, hMw, hM8⟩ := setup_facts hr hw
  set M : ℝ := Real.exp (3*r/5) with hMdef
  obtain ⟨hc1, hc2, hf1, hf2, hm1, hm2, hK1m, hmK2, hK1pos⟩ := window_facts hr hw
  set K₁ : ℕ := ⌈w - M⌉₊ with hK1def
  set K₂ : ℕ := ⌊w + M⌋₊ with hK2def
  set c : ℝ := (r+1)/(2*w) with hcdef
  set P : ℝ := Real.exp (psi n w) with hPdef
  have hP : 0 < P := Real.exp_pos _
  have hstep : ∀ k ∈ Finset.Ico K₁ K₂, |bterm n k - P * gauss c w k|
      ≤ 5 * Real.exp (-r/10) * (P * gauss c w k) := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have h1 : (K₁:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
    have h2 : (k:ℝ) ≤ (K₂:ℝ) := by exact_mod_cast hk.2.le
    exact central_pointwise hr hw hn (by linarith) (by linarith)
  calc |∑ k ∈ Finset.Ico K₁ K₂, bterm n k - P * ∑ k ∈ Finset.Ico K₁ K₂, gauss c w k|
      = |∑ k ∈ Finset.Ico K₁ K₂, (bterm n k - P * gauss c w k)| := by
        rw [Finset.mul_sum, Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ Finset.Ico K₁ K₂, |bterm n k - P * gauss c w k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ico K₁ K₂, 5 * Real.exp (-r/10) * (P * gauss c w k) :=
        Finset.sum_le_sum hstep
    _ = 5 * Real.exp (-r/10) * (P * ∑ k ∈ Finset.Ico K₁ K₂, gauss c w k) := by
        rw [Finset.mul_sum, Finset.mul_sum]

/-- Coarse comparison of the Gaussian window sum with the full Gaussian integral. -/
theorem gauss_window_sum_bound (hr : 2048 ≤ r) (hw : w = Real.exp r) :
    |∑ k ∈ Finset.Ico ⌈w - Real.exp (3*r/5)⌉₊ ⌊w + Real.exp (3*r/5)⌋₊,
        gauss ((r+1)/(2*w)) w k - Real.sqrt (π / ((r+1)/(2*w)))|
      ≤ 3 * Real.exp (-r/10) * Real.sqrt (π / ((r+1)/(2*w))) := by
  obtain ⟨hw0, hMw, hM8⟩ := setup_facts hr hw
  have hr0 : (0:ℝ) < r := by linarith
  set M : ℝ := Real.exp (3*r/5) with hMdef
  obtain ⟨hc1, hc2, hf1, hf2, hm1, hm2, hK1m, hmK2, hK1pos⟩ := window_facts hr hw
  set K₁ : ℕ := ⌈w - M⌉₊ with hK1def
  set K₂ : ℕ := ⌊w + M⌋₊ with hK2def
  set c : ℝ := (r+1)/(2*w) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  set A : ℝ := Real.sqrt (π/c) with hAdef
  set q : ℝ := Real.exp (-r/10) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  -- `r + 1 ≤ w` and hence a huge lower bound for `A`
  have hrw : r + 1 ≤ w := by rw [hw]; linarith [Real.add_one_le_exp r]
  have hr1 : r + 1 ≤ Real.exp (r/2) := by
    have h := sq_le_exp (by linarith : (0:ℝ) ≤ r/2)
    nlinarith
  have hAge : Real.exp (r/4) ≤ A := by
    have hquot : Real.exp (r/2) ≤ π/c := by
      have hpi : (3:ℝ) ≤ π := by linarith [Real.pi_gt_three]
      have hc' : π/c = 2*π*w/(r+1) := by
        rw [hcdef]; field_simp
      rw [hc', le_div_iff₀ (by linarith)]
      have hexp : Real.exp (r/2) * Real.exp (r/2) = w := by
        rw [← Real.exp_add, hw]; congr 1; ring
      nlinarith [Real.exp_pos (r/2), hr1, hexp]
    calc Real.exp (r/4) = Real.sqrt ((Real.exp (r/4))^2) :=
          (Real.sqrt_sq (Real.exp_pos _).le).symm
      _ = Real.sqrt (Real.exp (r/2)) := by
          congr 1
          rw [sq, ← Real.exp_add]; congr 1; ring
      _ ≤ A := Real.sqrt_le_sqrt hquot
  have hA0 : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hAge
  -- `2 ≤ q * A`
  have h2qA : (2:ℝ) ≤ q * A := by
    have h1 : q * Real.exp (r/4) = Real.exp (3*r/20) := by
      rw [hqdef, ← Real.exp_add]; congr 1; ring
    have h2 : (2:ℝ) ≤ Real.exp (3*r/20) := by
      have := Real.add_one_le_exp (3*r/20); linarith
    nlinarith [hq0, hAge]
  -- Gaussian tail factor
  have hMsq : M^2/2 ≤ (M-1)^2 := by nlinarith [hM8]
  have hbigexp : r/10 + 2 ≤ c*(M-1)^2/2 := by
    have hM2w : M^2/w = Real.exp (r/5) := by
      rw [hMdef, hw, sq, ← Real.exp_add, ← Real.exp_sub]
      congr 1; ring
    have hE : r^2/50 ≤ Real.exp (r/5) := by
      have := sq_le_exp (by linarith : (0:ℝ) ≤ r/5); nlinarith
    have hceq : c*(M-1)^2/2 = (r+1)*(M-1)^2/(4*w) := by
      rw [hcdef]; field_simp; ring
    have hMw2 : Real.exp (r/5) * w = M^2 := by
      rw [← hM2w]; field_simp
    have hcube : 4*M^2 ≤ 8*(r+1)*(M-1)^2 := by
      nlinarith [mul_le_mul_of_nonneg_left hMsq (show (0:ℝ) ≤ 8*(r+1) by linarith),
        mul_nonneg hr0.le (sq_nonneg M), sq_nonneg M]
    have hstep : Real.exp (r/5)/8 ≤ c*(M-1)^2/2 := by
      rw [hceq, div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [hMw2, hcube]
    have hfin : r/10 + 2 ≤ Real.exp (r/5)/8 := by nlinarith [hE]
    linarith
  have htail : Real.exp (-c*(M-1)^2/2) ≤ q/4 := by
    have h1 : Real.exp (-c*(M-1)^2/2) ≤ Real.exp (-r/10 - 2) := by
      apply Real.exp_le_exp.2; nlinarith [hbigexp]
    have h2 : Real.exp (-r/10 - 2) = q * Real.exp (-2) := by
      rw [hqdef, ← Real.exp_add]; ring_nf
    have h3 : Real.exp (-2:ℝ) ≤ 1/4 := by
      have he1 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
      have he2 : (4:ℝ) ≤ Real.exp 2 := by
        have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith
      rw [show (-2:ℝ) = -(2:ℝ) by ring, Real.exp_neg]
      rw [inv_le_iff_one_le_mul₀ (Real.exp_pos 2)]
      linarith
    nlinarith [hq0]
  have hsq2 : Real.sqrt (2*π/c) ≤ 2 * A := by
    have h1 : (2:ℝ)*π/c ≤ 4 * (π/c) := by
      have : (0:ℝ) < π/c := by positivity
      rw [show (2:ℝ)*π/c = 2*(π/c) by ring]; linarith
    calc Real.sqrt (2*π/c) ≤ Real.sqrt (4*(π/c)) := Real.sqrt_le_sqrt h1
      _ = 2 * A := by
          rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
            rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
  -- the two comparisons
  have hup : ∑ k ∈ Finset.Ico K₁ K₂, gauss c w k ≤ A + 2 :=
    gauss_sum_upper hcpos hK1m hmK2 hm1 hm2
  have hlow : A - 2 - 2*(Real.exp (-c*(M-1)^2/2) * Real.sqrt (2*π/c))
      ≤ ∑ k ∈ Finset.Ico K₁ K₂, gauss c w k :=
    gauss_sum_lower hcpos hK1m (by omega) hm1 hm2 (by linarith) (by linarith) (by linarith)
  have herr : 2*(Real.exp (-c*(M-1)^2/2) * Real.sqrt (2*π/c)) ≤ q * A := by
    have h0 : (0:ℝ) ≤ Real.exp (-c*(M-1)^2/2) := (Real.exp_pos _).le
    have h1 : Real.exp (-c*(M-1)^2/2) * Real.sqrt (2*π/c) ≤ (q/4) * (2*A) :=
      mul_le_mul htail hsq2 (Real.sqrt_nonneg _) (by positivity)
    linarith
  rw [abs_le]
  constructor <;> nlinarith [hq0, hA0, h2qA]

/-- The central window sum is `exp (psi n w) √(π/c)` up to a small relative error. -/
theorem central_total (hr : 2048 ≤ r) (hw : w = Real.exp r) (hn : (n:ℝ) = r * w) :
    |∑ k ∈ Finset.Ico ⌈w - Real.exp (3*r/5)⌉₊ ⌊w + Real.exp (3*r/5)⌋₊, bterm n k
        - Real.exp (psi n w) * Real.sqrt (π / ((r+1)/(2*w)))|
      ≤ 20 * Real.exp (-r/10)
          * (Real.exp (psi n w) * Real.sqrt (π / ((r+1)/(2*w)))) := by
  have h1 := central_sum_bound hr hw hn
  have h2 := gauss_window_sum_bound hr hw
  set S : ℝ := ∑ k ∈ Finset.Ico ⌈w - Real.exp (3*r/5)⌉₊ ⌊w + Real.exp (3*r/5)⌋₊,
    bterm n k with hSdef
  set G : ℝ := ∑ k ∈ Finset.Ico ⌈w - Real.exp (3*r/5)⌉₊ ⌊w + Real.exp (3*r/5)⌋₊,
    gauss ((r+1)/(2*w)) w k with hGdef
  set A : ℝ := Real.sqrt (π / ((r+1)/(2*w))) with hAdef
  set P : ℝ := Real.exp (psi n w) with hPdef
  set q : ℝ := Real.exp (-r/10) with hqdef
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hP : 0 < P := Real.exp_pos _
  have hq0 : 0 < q := Real.exp_pos _
  have hq3 : q ≤ 1/2 := by
    have he1 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    have h : q ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    have h' : Real.exp (-1:ℝ) ≤ 1/2 := by
      rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos 1)]; linarith
    linarith
  have hG : G ≤ 3*A := by
    have h := (abs_le.1 h2).2
    have := mul_le_mul_of_nonneg_right hq3 hA
    nlinarith
  have habs : |P*G - P*A| = P * |G - A| := by
    rw [← mul_sub, abs_mul, abs_of_pos hP]
  have hkey : |S - P*A| ≤ |S - P*G| + P*|G - A| := by
    rw [← habs]; exact abs_sub_le _ _ _
  have hstep1 : 5*q*(P*G) ≤ 15*q*(P*A) := by
    nlinarith [mul_le_mul_of_nonneg_left hG (show (0:ℝ) ≤ 5*q*P by positivity)]
  have hstep2 : P * |G - A| ≤ P * (3*q*A) := mul_le_mul_of_nonneg_left h2 hP.le
  nlinarith [mul_nonneg (mul_nonneg hq0.le hP.le) hA]

/-! ### Summing the two tails -/

theorem upper_tail_bound (hr : 2048 ≤ r) (hw : w = Real.exp r) (hn : (n:ℝ) = r * w) :
    Summable (fun j : ℕ => bterm n (⌊w + Real.exp (3*r/5)⌋₊ + j)) ∧
    ∑' j : ℕ, bterm n (⌊w + Real.exp (3*r/5)⌋₊ + j)
      ≤ Real.exp (-r/10) * Real.exp (psi n w) / 2 := by
  obtain ⟨hw0, hMw, hM8⟩ := setup_facts hr hw
  have hr0 : (0:ℝ) < r := by linarith
  set M : ℝ := Real.exp (3*r/5) with hMdef
  have hM0 : (0:ℝ) < M := by linarith
  obtain ⟨hc1, hc2, hf1, hf2, hm1, hm2, hK1m, hmK2, hK1pos⟩ := window_facts hr hw
  set K₂ : ℕ := ⌊w + M⌋₊ with hK2def
  have hK2ge : 1 ≤ K₂ := by omega
  set rho : ℝ := Real.exp (-r*M/(4*w)) with hrhodef
  have hx0 : (0:ℝ) < r*M/(4*w) := by positivity
  have hrho1 : rho < 1 := by
    rw [hrhodef, Real.exp_lt_one_iff]
    have : -r*M/(4*w) = -(r*M/(4*w)) := by ring
    rw [this]; linarith
  have hstep : ∀ k, K₂ ≤ k → bterm n (k+1) ≤ rho * bterm n k := by
    intro k hk
    have hk1 : 1 ≤ k := le_trans hK2ge hk
    have hkR : w + M - 1 ≤ (k:ℝ) := by
      have h : (K₂:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      linarith
    rw [bterm_succ n hk1]
    exact mul_le_mul_of_nonneg_right (brat_edge_upper hr hw hn hkR) (bterm_nonneg n k)
  obtain ⟨hsum, hle⟩ :=
    geom_tail_upper (fun k => bterm_nonneg n k) (Real.exp_pos _).le hrho1 hstep
  refine ⟨hsum, ?_⟩
  -- the edge term is tiny
  have hbK2 : bterm n K₂ ≤ Real.exp (psi n w) * Real.exp (-Real.exp (r/5)/5) := by
    refine bterm_edge_small hr hw hn (by linarith) (by linarith) ?_
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (K₂:ℝ) - w)]
    linarith
  -- the geometric denominator
  have hx1 : r*M/(4*w) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have hexp : Real.exp (2*r/5) * M = w := by
      rw [hMdef, hw, ← Real.exp_add]; congr 1; ring
    have h2 : r ≤ 4 * Real.exp (2*r/5) := by
      have := sq_le_exp (by linarith : (0:ℝ) ≤ 2*r/5); nlinarith
    nlinarith [hM0, Real.exp_pos (2*r/5)]
  have hden : r*M/(8*w) ≤ 1 - rho := by
    have h := one_sub_exp_neg_lower hx0.le hx1
    have heq : Real.exp (-(r*M/(4*w))) = rho := by rw [hrhodef]; congr 1; ring
    rw [heq] at h
    have : r*M/(4*w)/2 = r*M/(8*w) := by ring
    linarith [this ▸ h]
  have hden0 : (0:ℝ) < r*M/(8*w) := by positivity
  set P : ℝ := Real.exp (psi n w) with hPdef
  set E : ℝ := Real.exp (-Real.exp (r/5)/5) with hEdef
  have hP0 : 0 < P := Real.exp_pos _
  have hE0 : 0 < E := Real.exp_pos _
  have hwM : w / M = Real.exp (2*r/5) := by
    rw [hMdef, hw, ← Real.exp_sub]; congr 1; ring
  have hcoef : 8*w/(r*M) ≤ 8 * Real.exp (2*r/5) := by
    have h : 8*w/(r*M) = (8/r) * (w/M) := by field_simp
    rw [h, hwM]
    have h8 : 8/r ≤ 8 := by
      rw [div_le_iff₀ hr0]; nlinarith
    nlinarith [Real.exp_pos (2*r/5)]
  have hfinal : (8 * Real.exp (2*r/5) * E) * P ≤ Real.exp (-r/10) * P / 2 := by
    have h := tail_numeric (r := r) hr
    nlinarith [hP0, hE0, Real.exp_pos (2*r/5)]
  calc ∑' j : ℕ, bterm n (K₂ + j) ≤ bterm n K₂ / (1 - rho) := hle
    _ ≤ bterm n K₂ / (r*M/(8*w)) := by
        gcongr
        exact bterm_nonneg n K₂
    _ = bterm n K₂ * (8*w/(r*M)) := by
        rw [div_div_eq_mul_div, mul_div_assoc]
    _ ≤ (P*E) * (8 * Real.exp (2*r/5)) := by
        refine mul_le_mul hbK2 hcoef (by positivity) (by positivity)
    _ = (8 * Real.exp (2*r/5) * E) * P := by ring
    _ ≤ Real.exp (-r/10) * P / 2 := hfinal

theorem lower_tail_bound (hr : 2048 ≤ r) (hw : w = Real.exp r) (hn : (n:ℝ) = r * w) :
    ∑ k ∈ Finset.Ico 1 ⌈w - Real.exp (3*r/5)⌉₊, bterm n k
      ≤ Real.exp (-r/10) * Real.exp (psi n w) / 2 := by
  obtain ⟨hw0, hMw, hM8⟩ := setup_facts hr hw
  have hr0 : (0:ℝ) < r := by linarith
  set M : ℝ := Real.exp (3*r/5) with hMdef
  have hM0 : (0:ℝ) < M := by linarith
  obtain ⟨hc1, hc2, hf1, hf2, hm1, hm2, hK1m, hmK2, hK1pos⟩ := window_facts hr hw
  set K₁ : ℕ := ⌈w - M⌉₊ with hK1def
  have hK1big : (100:ℝ) ≤ (K₁:ℝ) := by linarith
  have hK1two : 2 ≤ K₁ := by
    have : (2:ℝ) ≤ (K₁:ℝ) := by linarith
    exact_mod_cast this
  set j₀ : ℕ := K₁ - 1 with hj0def
  have hj0cast : (j₀:ℝ) = (K₁:ℝ) - 1 := by
    rw [hj0def]
    have : (1:ℕ) ≤ K₁ := by omega
    push_cast [Nat.cast_sub this]
    ring
  set rho : ℝ := Real.exp (-(r*M/(2*w))) with hrhodef
  have hx0 : (0:ℝ) < r*M/(2*w) := by positivity
  have hrho0 : 0 < rho := Real.exp_pos _
  have hrho1 : rho < 1 := by
    rw [hrhodef, Real.exp_lt_one_iff]; linarith
  have hedge : Real.exp (r*M/(2*w)) ≤ brat n j₀ := by
    have h1 : w - M - 1 ≤ (j₀:ℝ) := by rw [hj0cast]; linarith
    have h2 : (j₀:ℝ) ≤ w - M := by rw [hj0cast]; linarith
    exact brat_edge_lower hr hw hn h1 h2
  have hstep : ∀ k, 1 ≤ k → k < K₁ → bterm n k ≤ rho * bterm n (k+1) := by
    intro k hk1 hk2
    have hkj : k ≤ j₀ := by omega
    have hb : Real.exp (r*M/(2*w)) ≤ brat n k :=
      le_trans hedge (brat_antitone n hk1 hkj)
    have hsucc : bterm n (k+1) = brat n k * bterm n k := bterm_succ n hk1
    have hnn : 0 ≤ bterm n k := bterm_nonneg n k
    have hmul : Real.exp (r*M/(2*w)) * bterm n k ≤ bterm n (k+1) := by
      rw [hsucc]
      exact mul_le_mul_of_nonneg_right hb hnn
    have hcancel : rho * Real.exp (r*M/(2*w)) = 1 := by
      rw [hrhodef, ← Real.exp_add]
      simp
    calc bterm n k = rho * (Real.exp (r*M/(2*w)) * bterm n k) := by
          rw [← mul_assoc, hcancel, one_mul]
      _ ≤ rho * bterm n (k+1) := mul_le_mul_of_nonneg_left hmul hrho0.le
  have hle := geom_tail_lower (fun k => bterm_nonneg n k) hrho0.le hrho1 K₁ hstep
  -- the edge term is tiny
  have hbK1 : bterm n K₁ ≤ Real.exp (psi n w) * Real.exp (-Real.exp (r/5)/5) := by
    refine bterm_edge_small hr hw hn (by linarith) (by linarith) ?_
    rw [abs_of_nonpos (by linarith : (K₁:ℝ) - w ≤ 0)]
    linarith
  -- the geometric denominator
  have hx1 : r*M/(2*w) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have hexp : Real.exp (2*r/5) * M = w := by
      rw [hMdef, hw, ← Real.exp_add]; congr 1; ring
    have h2 : r ≤ 2 * Real.exp (2*r/5) := by
      have := sq_le_exp (by linarith : (0:ℝ) ≤ 2*r/5); nlinarith
    nlinarith [hM0, Real.exp_pos (2*r/5)]
  have hden : r*M/(4*w) ≤ 1 - rho := by
    have h := one_sub_exp_neg_lower hx0.le hx1
    rw [← hrhodef] at h
    have heq : r*M/(2*w)/2 = r*M/(4*w) := by ring
    linarith [heq ▸ h]
  have hden0 : (0:ℝ) < r*M/(4*w) := by positivity
  set P : ℝ := Real.exp (psi n w) with hPdef
  set E : ℝ := Real.exp (-Real.exp (r/5)/5) with hEdef
  have hP0 : 0 < P := Real.exp_pos _
  have hE0 : 0 < E := Real.exp_pos _
  have hwM : w / M = Real.exp (2*r/5) := by
    rw [hMdef, hw, ← Real.exp_sub]; congr 1; ring
  have hcoef : 4*w/(r*M) ≤ 4 * Real.exp (2*r/5) := by
    have h : 4*w/(r*M) = (4/r) * (w/M) := by field_simp
    rw [h, hwM]
    have h4 : 4/r ≤ 4 := by
      rw [div_le_iff₀ hr0]; nlinarith
    nlinarith [Real.exp_pos (2*r/5)]
  have hfinal : (4 * Real.exp (2*r/5) * E) * P ≤ Real.exp (-r/10) * P / 2 := by
    have h := tail_numeric (r := r) hr
    rw [← hEdef] at h
    nlinarith [mul_le_mul_of_nonneg_right h hP0.le,
      mul_pos (Real.exp_pos (-r/10)) hP0]
  have hnnK1 : 0 ≤ bterm n K₁ := bterm_nonneg n K₁
  calc ∑ k ∈ Finset.Ico 1 K₁, bterm n k ≤ bterm n K₁ * rho / (1 - rho) := hle
    _ ≤ bterm n K₁ / (1 - rho) := by
        gcongr
        · linarith
        · nlinarith
    _ ≤ bterm n K₁ / (r*M/(4*w)) := by gcongr
    _ = bterm n K₁ * (4*w/(r*M)) := by rw [div_div_eq_mul_div, mul_div_assoc]
    _ ≤ (P*E) * (4 * Real.exp (2*r/5)) := by
        refine mul_le_mul hbK1 hcoef (by positivity) (by positivity)
    _ = (4 * Real.exp (2*r/5) * E) * P := by ring
    _ ≤ Real.exp (-r/10) * P / 2 := hfinal

/-! ### The full sum -/

theorem tsum_bterm_saddle_bound (hr : 2048 ≤ r) (hw : w = Real.exp r) (hn : (n:ℝ) = r * w) :
    |∑' k : ℕ, bterm n k - Real.exp (psi n w) * Real.sqrt (π / ((r+1)/(2*w)))|
      ≤ 100 * Real.exp (-r/10)
          * (Real.exp (psi n w) * Real.sqrt (π / ((r+1)/(2*w)))) := by
  obtain ⟨hw0, hMw, hM8⟩ := setup_facts hr hw
  have hr0 : (0:ℝ) < r := by linarith
  set M : ℝ := Real.exp (3*r/5) with hMdef
  obtain ⟨hc1, hc2, hf1, hf2, hm1, hm2, hK1m, hmK2, hK1pos⟩ := window_facts hr hw
  set K₁ : ℕ := ⌈w - M⌉₊ with hK1def
  set K₂ : ℕ := ⌊w + M⌋₊ with hK2def
  have hK12 : K₁ ≤ K₂ := by omega
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at hn
    norm_num at hn
    rcases hn with h' | h' <;> linarith
  have hb0 : bterm n 0 = 0 := by
    simp [bterm, hn0]
  have hsummable : Summable (bterm n) := by
    have h := summable_pow_div_fact n
    simpa [bterm] using h
  -- exact partition of the Dobinski sum
  have h1 : ∑ k ∈ Finset.range K₂, bterm n k
      = ∑ k ∈ Finset.Ico 1 K₁, bterm n k + ∑ k ∈ Finset.Ico K₁ K₂, bterm n k := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le K₁) hK12,
      Finset.sum_eq_sum_Ico_succ_bot (show 0 < K₁ by omega), hb0, zero_add]
  have h2 : ∑' j : ℕ, bterm n (j + K₂) = ∑' j : ℕ, bterm n (K₂ + j) :=
    tsum_congr (fun j => by rw [Nat.add_comm])
  have hsplit : ∑' k : ℕ, bterm n k
      = (∑ k ∈ Finset.Ico 1 K₁, bterm n k + ∑ k ∈ Finset.Ico K₁ K₂, bterm n k)
        + ∑' j : ℕ, bterm n (K₂ + j) := by
    rw [← hsummable.sum_add_tsum_nat_add K₂, h1, h2]
  -- the three pieces
  have hcen := central_total hr hw hn
  have hlow := lower_tail_bound hr hw hn
  obtain ⟨-, hupp⟩ := upper_tail_bound hr hw hn
  set A : ℝ := Real.sqrt (π / ((r+1)/(2*w))) with hAdef
  set P : ℝ := Real.exp (psi n w) with hPdef
  set q : ℝ := Real.exp (-r/10) with hqdef
  have hP0 : 0 < P := Real.exp_pos _
  have hq0 : 0 < q := Real.exp_pos _
  have hA1 : (1:ℝ) ≤ A := by
    have hrw : r + 1 ≤ w := by rw [hw]; linarith [Real.add_one_le_exp r]
    have hc2' : (r+1)/(2*w) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hpi : (3:ℝ) ≤ π := by linarith [Real.pi_gt_three]
    have hq1 : (1:ℝ) ≤ π / ((r+1)/(2*w)) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    calc (1:ℝ) = Real.sqrt 1 := by rw [Real.sqrt_one]
      _ ≤ A := Real.sqrt_le_sqrt hq1
  have hLnn : 0 ≤ ∑ k ∈ Finset.Ico 1 K₁, bterm n k :=
    Finset.sum_nonneg (fun k _ => bterm_nonneg n k)
  have hUnn : 0 ≤ ∑' j : ℕ, bterm n (K₂ + j) := tsum_nonneg (fun j => bterm_nonneg n _)
  rw [hsplit, abs_le]
  have hcen' := abs_le.1 hcen
  have hqA : q * P ≤ q * P * A := by nlinarith [mul_pos hq0 hP0]
  constructor <;> nlinarith [mul_pos hq0 hP0, hcen'.1, hcen'.2]

/-! ### The exact normalization identity -/

/-- `exp (-log z/2) * √z = 1` for `z > 0`. -/
theorem exp_neg_half_log_mul_sqrt {z : ℝ} (hz : 0 < z) :
    Real.exp (-Real.log z/2) * Real.sqrt z = 1 := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hz, ← Real.exp_add]
  rw [show -Real.log z/2 + Real.log z * (1/2) = 0 by ring, Real.exp_zero]

/-- The saddle scale `exp (psi N w) √(π/c)` in closed form. -/
theorem saddle_scale_eq {N r w : ℝ} (hr0 : 0 ≤ r) (hw0 : 0 < w)
    (hlogw : Real.log w = r) (hN : N = r * w) :
    Real.exp (psi N w) * Real.sqrt (π / ((r+1)/(2*w)))
      = (w ^ N * Real.exp (w - N - 1) / Real.sqrt (r+1)) * Real.exp 1 := by
  have hpiw : (0:ℝ) < 2*π*w := by positivity
  have hr1 : (0:ℝ) < r + 1 := by linarith
  have hsqrt : Real.sqrt (π / ((r+1)/(2*w))) = Real.sqrt (2*π*w) / Real.sqrt (r+1) := by
    have h : π / ((r+1)/(2*w)) = (2*π*w)/(r+1) := by field_simp
    rw [h, Real.sqrt_div hpiw.le]
  have hpsi : psi N w = (N*r - N + w) + (-Real.log (2*π*w)/2) := by
    simp only [psi, hlogw]
    have hwr : w * r = N := by rw [hN]; ring
    rw [hwr]; ring
  have hcancel := exp_neg_half_log_mul_sqrt hpiw
  calc Real.exp (psi N w) * Real.sqrt (π / ((r+1)/(2*w)))
      = (Real.exp (N*r - N + w)
          * (Real.exp (-Real.log (2*π*w)/2) * Real.sqrt (2*π*w))) / Real.sqrt (r+1) := by
        rw [hsqrt, hpsi, Real.exp_add]; ring
    _ = Real.exp (N*r - N + w) / Real.sqrt (r+1) := by rw [hcancel, mul_one]
    _ = (w ^ N * Real.exp (w - N - 1) / Real.sqrt (r+1)) * Real.exp 1 := by
        rw [Real.rpow_def_of_pos hw0, hlogw, div_mul_eq_mul_div, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

theorem saddle_scale_eq_gQ_exp_one (n : ℕ) (hn0 : 0 < (n:ℝ)) :
    Real.exp (psi n (W n)) * Real.sqrt (π / ((lamW n + 1)/(2 * W n)))
      = gQ n * Real.exp 1 := by
  have hw0 : 0 < W (n:ℝ) := W_pos _
  have hlogw : Real.log (W (n:ℝ)) = lamW (n:ℝ) := by rw [W, Real.log_exp]
  have hN : (n:ℝ) = lamW n * W n := by
    rw [W]; exact (lamW_spec hn0.le).symm
  rw [gQ]
  exact saddle_scale_eq (lamW_nonneg hn0.le) hw0 hlogw hN

end Aggregate

/-! ### The unconditional first correction -/

theorem eventually_lamW_ge : ∀ᶠ n : ℕ in atTop, (2048:ℝ) ≤ lamW n := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (2048 * Real.exp 2048)]
    with n hn
  by_contra hcon
  push_neg at hcon
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : lamW n * Real.exp (lamW n) < 2048 * Real.exp 2048 :=
    lambert_strictMono (Set.mem_Ici.2 (lamW_nonneg hn0)) (Set.mem_Ici.2 (by norm_num)) hcon
  rw [lamW_spec hn0] at h1
  linarith

theorem bell_over_gQ_bound :
    ∀ᶠ n : ℕ in atTop, |(Nat.bell n : ℝ) / gQ n - 1| ≤ 100 * Real.exp (-lamW n / 10) := by
  filter_upwards [eventually_lamW_ge, eventually_big] with n hlam hbig
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hbig
  have hw : W (n:ℝ) = Real.exp (lamW n) := rfl
  have hnrw : (n:ℝ) = lamW n * W n := by rw [W]; exact (lamW_spec hn0.le).symm
  have hsad := tsum_bterm_saddle_bound (n := n) (r := lamW n) (w := W n) hlam hw hnrw
  rw [saddle_scale_eq_gQ_exp_one n hn0] at hsad
  have hbt : ∑' k : ℕ, bterm n k = ∑' k : ℕ, (k:ℝ)^n / k ! := tsum_congr (fun k => rfl)
  rw [hbt, ← dobinski n] at hsad
  have hgQ : 0 < gQ (n:ℝ) := gQ_pos hn0
  have he1 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have hid : (Nat.bell n : ℝ) / gQ n - 1
      = ((Nat.bell n : ℝ) * Real.exp 1 - gQ n * Real.exp 1) / (gQ n * Real.exp 1) := by
    field_simp
  rw [hid, abs_div, abs_of_pos (mul_pos hgQ he1), div_le_iff₀ (mul_pos hgQ he1)]
  linarith [hsad]

theorem bell_over_gQ_isBigO :
    (fun n : ℕ => (Nat.bell n : ℝ) / gQ n - 1) =O[atTop]
      (fun n : ℕ => (Real.log (Real.log n))^2 / (Real.log n)^2) := by
  refine Asymptotics.IsBigO.of_bound 5000 ?_
  filter_upwards [bell_over_gQ_bound, eventually_lamW_ge, eventually_log_facts, eventually_big]
    with n hb hlam hfacts hbig
  obtain ⟨hL, hl4, hlL⟩ := hfacts
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hbig
  have hL0 : (0:ℝ) < Real.log n := by linarith
  have hr0 : (0:ℝ) < lamW n := by linarith
  have hlogr : Real.log (lamW n) ≤ lamW n := by
    linarith [Real.log_le_sub_one_of_pos hr0]
  have hLr : Real.log n ≤ 2 * lamW n := by
    have h := lamW_add_log hn0
    linarith
  -- `exp (-r/10) ≤ 200/r²`
  have h1 : (lamW n)^2/200 ≤ Real.exp (lamW n/10) := by
    have := sq_le_exp (show (0:ℝ) ≤ lamW n/10 by linarith)
    nlinarith
  have h2 : Real.exp (-lamW n/10) ≤ 200/(lamW n)^2 := by
    have hpos : (0:ℝ) < (lamW n)^2/200 := by positivity
    have h3 : 1/Real.exp (lamW n/10) ≤ 1/((lamW n)^2/200) :=
      one_div_le_one_div_of_le hpos h1
    have h4 : 1/((lamW n)^2/200) = 200/(lamW n)^2 := by
      rw [one_div_div]
    rw [show -lamW n/10 = -(lamW n/10) by ring, Real.exp_neg, ← one_div]
    rw [h4] at h3
    exact h3
  have h5 : (200:ℝ)/(lamW n)^2 ≤ 50 * ((Real.log (Real.log n))^2 / (Real.log n)^2) := by
    have hLsq : (0:ℝ) < (Real.log n)^2 := by positivity
    have hrsq : (0:ℝ) < (lamW n)^2 := by positivity
    rw [show (50:ℝ) * ((Real.log (Real.log n))^2 / (Real.log n)^2)
        = (50*(Real.log (Real.log n))^2) / (Real.log n)^2 by ring]
    rw [div_le_div_iff₀ hrsq hLsq]
    have hl16 : (16:ℝ) ≤ (Real.log (Real.log n))^2 := by nlinarith
    nlinarith [sq_nonneg (Real.log n), hLr, hL0, hr0]
  have hpos : (0:ℝ) ≤ (Real.log (Real.log n))^2 / (Real.log n)^2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos]
  calc |(Nat.bell n : ℝ) / gQ n - 1| ≤ 100 * Real.exp (-lamW n / 10) := hb
    _ ≤ 100 * (50 * ((Real.log (Real.log n))^2 / (Real.log n)^2)) := by
        have := h2.trans h5
        linarith
    _ = 5000 * ((Real.log (Real.log n))^2 / (Real.log n)^2) := by ring

/-- **Q565, unconditional first correction.** -/
theorem Q565_first_correction_complete :
    (fun n : ℕ => (Nat.bell n : ℝ) / fQ n
        - (1 + (Real.log (Real.log n) - 1) / (2 * Real.log n))) =O[atTop]
      (fun n : ℕ => (Real.log (Real.log n))^2 / (Real.log n)^2) :=
  Q565_first_correction.mp bell_over_gQ_isBigO

end Q565
