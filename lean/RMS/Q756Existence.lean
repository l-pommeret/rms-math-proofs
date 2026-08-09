/-
Q756 — existence of nonzero flat (hence nonpolynomial) solutions.

For every `beta` and every `lam` with `1 < |lam|` the space
`F(beta, lam) = {g ∈ C¹(ℝ,ℝ) : g' t = g (lam t) - beta * g t}` contains nonzero `C^∞` functions
which are flat at the origin, in particular functions which are not polynomials.

The solution is built from smooth bump seeds supported in the fundamental annulus
`1 < |t| < |lam|`: the outward extension `Wout` propagates a seed to infinity, the inward
correction `Vin` repairs the equation on `(-1,1) \ {0}`, and a three-parameter family of seeds
is used to kill both one-sided limits at the origin (§6–§7 of the solution).
-/
import RMS.Q756Glue

namespace Q756

open Set Filter Topology Polynomial

/-- A smooth bump of radius `r` centred at `c`, equal to `1` at the centre and vanishing outside
the ball of radius `r`. -/
theorem exists_bump (c : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ psi : ℝ → ℝ, (∀ m : ℕ, ContDiff ℝ m psi) ∧ (∀ x, r ≤ |x - c| → psi x = 0) ∧
      psi c = 1 ∧ (∀ x, |psi x| ≤ 1) := by
  set f : ContDiffBump c := ⟨r / 2, r, by linarith, by linarith⟩ with hf
  refine ⟨fun x => f x, fun m => f.contDiff, fun x hx => ?_, ?_, fun x => ?_⟩
  · refine f.zero_of_le_dist ?_
    rwa [Real.dist_eq]
  · refine f.one_of_mem_closedBall ?_
    simp only [hf, Metric.mem_closedBall, dist_self]
    positivity
  · rw [abs_of_nonneg f.nonneg]
    exact f.le_one

section Algebra

/-- Two proportional vectors of `ℝ²` admit a nontrivial linear relation. -/
theorem exists_kernel2 (x1 y1 x2 y2 : ℝ) (h : x1 * y2 - x2 * y1 = 0) :
    ∃ a1 a2 : ℝ, (a1 ≠ 0 ∨ a2 ≠ 0) ∧ a1 * x1 + a2 * x2 = 0 ∧ a1 * y1 + a2 * y2 = 0 := by
  by_cases hx : x1 ≠ 0
  · exact ⟨-x2, x1, Or.inr hx, by ring, by linarith⟩
  · by_cases hy : y1 ≠ 0
    · refine ⟨-y2, y1, Or.inr hy, by linarith, by ring⟩
    · push_neg at hx hy
      exact ⟨1, 0, Or.inl one_ne_zero, by simp [hx], by simp [hy]⟩

/-- Any three vectors of `ℝ²` admit a nontrivial linear relation. -/
theorem exists_kernel_vector (x1 y1 x2 y2 x3 y3 : ℝ) :
    ∃ a1 a2 a3 : ℝ, (a1 ≠ 0 ∨ a2 ≠ 0 ∨ a3 ≠ 0) ∧
      a1 * x1 + a2 * x2 + a3 * x3 = 0 ∧ a1 * y1 + a2 * y2 + a3 * y3 = 0 := by
  by_cases hw : x2 * y3 - x3 * y2 = 0 ∧ x3 * y1 - x1 * y3 = 0 ∧ x1 * y2 - x2 * y1 = 0
  · obtain ⟨a1, a2, hne, h1, h2⟩ := exists_kernel2 x1 y1 x2 y2 hw.2.2
    exact ⟨a1, a2, 0, by tauto, by linarith, by linarith⟩
  · refine ⟨x2 * y3 - x3 * y2, x3 * y1 - x1 * y3, x1 * y2 - x2 * y1, ?_, by ring, by ring⟩
    by_contra hc
    push_neg at hc
    exact hw ⟨hc.1, hc.2.1, hc.2.2⟩

end Algebra

section Main

variable {beta lam e : ℝ} {phi : ℝ → ℝ}

/-- On the closed annulus `1 - dlt ≤ |x| ≤ |lam|` the constructed solution coincides with the
seed: the inward correction is supported inside, and the outward extension starts with `phi`. -/
theorem Gsol_eq_seed (hlam : 1 < |lam|) (he : 0 < e) (hseed : IsSeed lam e phi) {L x : ℝ}
    (hx0 : x ≠ 0) (hx1 : 1 - dlt lam e ≤ |x|) (hx2 : |x| ≤ |lam|) :
    Gsol beta lam phi L x = phi x := by
  rw [Gsol_of_ne hx0, Wout_eq_phi he hlam hseed.vanish hx2,
    Vin_supp hlam he hseed.supp hx1, add_zero]

/-- A seed both of whose one-sided limits vanish produces a nonzero flat solution. -/
theorem sol_of_flat_seed (hlam : 1 < |lam|) (he : 0 < e) (hseed : IsSeed lam e phi)
    (hpos : Lpos beta lam phi = 0) (hneg : Lneg beta lam phi = 0) :
    IsSol beta lam (Gsol beta lam phi 0) ∧ (∀ n : ℕ, iteratedDeriv n (Gsol beta lam phi 0) 0 = 0)
      ∧ ∀ n : ℕ, ContDiff ℝ n (Gsol beta lam phi 0) := by
  have hsol : IsSol beta lam (Gsol beta lam phi 0) :=
    Gsol_isSol hlam he hseed hpos (by rw [hneg])
  exact ⟨hsol, flat_of_sol_zero hsol Gsol_at_zero, sol_contDiff hsol⟩

end Main

section Window

variable {beta lam : ℝ}

/-- **Construction of a flat solution localised in a prescribed window.**
Given `1 < u < v < |lam|`, there is a nonzero `C^∞` solution, flat at the origin, whose
restriction to the fundamental annulus is supported in `(u, v)`. -/
theorem exists_flat_sol_in_window (hlam : 1 < |lam|) {u v : ℝ} (hu : 1 < u) (huv : u < v)
    (hv : v < |lam|) :
    ∃ (g : ℝ → ℝ) (p : ℝ), IsSol beta lam g ∧ (∀ n : ℕ, iteratedDeriv n g 0 = 0) ∧
      (∀ n : ℕ, ContDiff ℝ n g) ∧ u < p ∧ p < v ∧ g p ≠ 0 ∧
      ∀ x : ℝ, 1 ≤ x → x ≤ |lam| → (x ≤ u ∨ v ≤ x) → g x = 0 := by
  obtain ⟨d, hd, hd0⟩ : ∃ d : ℝ, d = v - u ∧ 0 < d := ⟨v - u, rfl, by linarith⟩
  obtain ⟨r, hr, hr0⟩ : ∃ r : ℝ, r = d / 16 ∧ 0 < r := ⟨d / 16, rfl, by linarith⟩
  obtain ⟨e, he, he1, he2⟩ : ∃ e : ℝ, 0 < e ∧ 1 + e ≤ 1 + (u - 1) / 2 ∧
      |lam| - (|lam| - v) / 2 ≤ |lam| - e := by
    refine ⟨min ((u - 1) / 2) ((|lam| - v) / 2), lt_min (by linarith) (by linarith), ?_, ?_⟩
    · have : min ((u - 1) / 2) ((|lam| - v) / 2) ≤ (u - 1) / 2 := min_le_left _ _
      linarith
    · have : min ((u - 1) / 2) ((|lam| - v) / 2) ≤ (|lam| - v) / 2 := min_le_right _ _
      linarith
  -- the three bump centres
  obtain ⟨c1, hc1⟩ : ∃ c : ℝ, c = u + d / 4 := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c : ℝ, c = u + d / 2 := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c : ℝ, c = u + 3 * d / 4 := ⟨_, rfl⟩
  -- a general criterion for a bump centred in `[c1, c3]` to be a seed
  have hseedOf : ∀ c : ℝ, c1 ≤ c → c ≤ c3 → ∀ psi : ℝ → ℝ, (∀ m : ℕ, ContDiff ℝ m psi) →
      (∀ x, r ≤ |x - c| → psi x = 0) → (∀ x, |psi x| ≤ 1) → IsSeed lam e psi := by
    intro c hca hcb psi hsm hz hb
    refine ⟨hsm, fun t ht => ?_, ⟨1, hb⟩⟩
    refine hz t ?_
    have hle : t ≤ |t| := le_abs_self t
    rcases ht with ht | ht
    · rw [abs_of_nonpos (by linarith), neg_sub]
      linarith
    · rcases le_or_gt 0 t with h | h
      · rw [abs_of_nonneg h] at ht
        rw [abs_of_nonneg (by linarith)]
        linarith
      · rw [abs_of_nonpos (by linarith), neg_sub]
        linarith
  obtain ⟨p1, hp1s, hp1z, hp1o, hp1b⟩ := exists_bump c1 hr0
  obtain ⟨p2, hp2s, hp2z, hp2o, hp2b⟩ := exists_bump c2 hr0
  obtain ⟨p3, hp3s, hp3z, hp3o, hp3b⟩ := exists_bump c3 hr0
  have hs1 : IsSeed lam e p1 := hseedOf c1 le_rfl (by linarith) p1 hp1s hp1z hp1b
  have hs2 : IsSeed lam e p2 := hseedOf c2 (by linarith) (by linarith) p2 hp2s hp2z hp2b
  have hs3 : IsSeed lam e p3 := hseedOf c3 (by linarith) le_rfl p3 hp3s hp3z hp3b
  -- the bumps have pairwise disjoint supports
  have hz12 : p1 c2 = 0 :=
    hp1z _ (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c2 - c1)]; linarith)
  have hz13 : p1 c3 = 0 :=
    hp1z _ (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c3 - c1)]; linarith)
  have hz21 : p2 c1 = 0 :=
    hp2z _ (by rw [abs_of_nonpos (by linarith : c1 - c2 ≤ (0:ℝ)), neg_sub]; linarith)
  have hz23 : p2 c3 = 0 :=
    hp2z _ (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c3 - c2)]; linarith)
  have hz31 : p3 c1 = 0 :=
    hp3z _ (by rw [abs_of_nonpos (by linarith : c1 - c3 ≤ (0:ℝ)), neg_sub]; linarith)
  have hz32 : p3 c2 = 0 :=
    hp3z _ (by rw [abs_of_nonpos (by linarith : c2 - c3 ≤ (0:ℝ)), neg_sub]; linarith)
  -- kill both one-sided limits
  obtain ⟨a1, a2, a3, hane, hkn, hkp⟩ := exists_kernel_vector
    (Lneg beta lam p1) (Lpos beta lam p1) (Lneg beta lam p2) (Lpos beta lam p2)
    (Lneg beta lam p3) (Lpos beta lam p3)
  set phi : ℝ → ℝ := fun x => a1 * p1 x + (a2 * p2 x + a3 * p3 x) with hphi
  have hsa : IsSeed lam e (fun x => a1 * p1 x) := hs1.const_mul a1
  have hsb : IsSeed lam e (fun x => a2 * p2 x) := hs2.const_mul a2
  have hsc : IsSeed lam e (fun x => a3 * p3 x) := hs3.const_mul a3
  have hsbc : IsSeed lam e (fun x => a2 * p2 x + a3 * p3 x) := hsb.add hsc
  have hsphi : IsSeed lam e phi := hsa.add hsbc
  have hposphi : Lpos beta lam phi = 0 := by
    rw [hphi, Lpos_add hlam he hsa hsbc, Lpos_add hlam he hsb hsc,
      Lpos_const_mul hlam he hs1, Lpos_const_mul hlam he hs2, Lpos_const_mul hlam he hs3]
    linarith
  have hnegphi : Lneg beta lam phi = 0 := by
    rw [hphi, Lneg_add hlam he hsa hsbc, Lneg_add hlam he hsb hsc,
      Lneg_const_mul hlam he hs1, Lneg_const_mul hlam he hs2, Lneg_const_mul hlam he hs3]
    linarith
  obtain ⟨hsol, hflat, hsmooth⟩ := sol_of_flat_seed hlam he hsphi hposphi hnegphi
  have hdlt : 0 < dlt lam e := dlt_pos hlam he
  -- values of the solution on the fundamental annulus
  have hval : ∀ x : ℝ, 1 ≤ x → x ≤ |lam| → Gsol beta lam phi 0 x = phi x := by
    intro x hx1 hx2
    refine Gsol_eq_seed hlam he hsphi (by linarith) ?_ ?_ <;>
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x)] <;> linarith
  -- the solution vanishes on the annulus outside the window
  have houtside : ∀ x : ℝ, 1 ≤ x → x ≤ |lam| → (x ≤ u ∨ v ≤ x) → Gsol beta lam phi 0 x = 0 := by
    intro x hx1 hx2 hx3
    have hzz : ∀ c : ℝ, c1 ≤ c → c ≤ c3 → r ≤ |x - c| := by
      intro c hca hcb
      rcases hx3 with h | h
      · rw [abs_of_nonpos (by linarith), neg_sub]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    rw [hval x hx1 hx2]
    simp only [hphi]
    rw [hp1z x (hzz c1 le_rfl (by linarith)), hp2z x (hzz c2 (by linarith) (by linarith)),
      hp3z x (hzz c3 (by linarith) le_rfl)]
    ring
  -- the solution is nonzero at one of the three centres
  have hcu : ∀ c : ℝ, c1 ≤ c → c ≤ c3 → 1 ≤ c ∧ c ≤ |lam| ∧ u < c ∧ c < v := by
    intro c hca hcb
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  rcases hane with ha | ha | ha
  · obtain ⟨h1, h2, h3, h4⟩ := hcu c1 le_rfl (by linarith)
    refine ⟨Gsol beta lam phi 0, c1, hsol, hflat, hsmooth, h3, h4, ?_, houtside⟩
    rw [hval c1 h1 h2]
    simp only [hphi]
    rw [hp1o, hz21, hz31]
    simpa using ha
  · obtain ⟨h1, h2, h3, h4⟩ := hcu c2 (by linarith) (by linarith)
    refine ⟨Gsol beta lam phi 0, c2, hsol, hflat, hsmooth, h3, h4, ?_, houtside⟩
    rw [hval c2 h1 h2]
    simp only [hphi]
    rw [hp2o, hz12, hz32]
    simpa using ha
  · obtain ⟨h1, h2, h3, h4⟩ := hcu c3 (by linarith) le_rfl
    refine ⟨Gsol beta lam phi 0, c3, hsol, hflat, hsmooth, h3, h4, ?_, houtside⟩
    rw [hval c3 h1 h2]
    simp only [hphi]
    rw [hp3o, hz13, hz23]
    simpa using ha

end Window

/-- **Main existence theorem (§5–§7 of the solution).** For every `beta` and every `lam` with
`1 < |lam|` there is a nonzero `C^∞` solution of `g' t = g (lam t) - beta * g t` which is flat at
the origin; in particular it is not a polynomial function. -/
theorem exists_flat_nonpolynomial_sol (beta lam : ℝ) (hlam : 1 < |lam|) :
    ∃ g : ℝ → ℝ, IsSol beta lam g ∧ (∀ n : ℕ, iteratedDeriv n g 0 = 0) ∧
      (∀ n : ℕ, ContDiff ℝ n g) ∧ g ≠ 0 ∧ ∀ P : ℝ[X], g ≠ fun t => P.eval t := by
  obtain ⟨g, p, hsol, hflat, hsmooth, _, _, hgp, _⟩ :=
    exists_flat_sol_in_window (beta := beta) hlam (u := 1 + (|lam| - 1) / 3)
      (v := 1 + 2 * (|lam| - 1) / 3) (by linarith) (by linarith) (by linarith)
  have hg0 : g 0 = 0 := by simpa using hflat 0
  refine ⟨g, hsol, hflat, hsmooth, fun h => hgp (by rw [h]; rfl), fun P hP => ?_⟩
  have hPsol : IsSol beta lam (fun t => P.eval t) := by rw [← hP]; exact hsol
  have hP0 : P.coeff 0 = 0 := by
    have : P.eval 0 = 0 := by rw [← congrFun hP 0]; exact hg0
    rw [Polynomial.coeff_zero_eq_eval_zero]; exact this
  have : P = 0 := poly_eq_zero_of_coeff_zero P hPsol hP0
  rw [hP, this] at hgp
  simp at hgp

end Q756
