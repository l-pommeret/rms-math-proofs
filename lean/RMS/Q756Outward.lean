/-
# Q756 — the outward extension

Construction of nonzero `C^∞` solutions of `g'(t) = g (lam t) - beta g t` that are flat at
the origin, for every `beta` and every `|lam| > 1`.  Such solutions are not polynomials.

The construction follows the "shell" argument: a smooth seed supported strictly inside the
fundamental annulus `1 < |t| < |lam|` is propagated outward by an explicit differentiation
formula, and inward by a Volterra integral equation.
-/

import RMS.Q756

namespace Q756

open Set Filter Finset

section Outward

variable (beta lam : ℝ) (phi : ℝ → ℝ)

/-- The pieces of the outward extension: `Hseq n` is the restriction of the outward
extension to the `n`-th annulus, pulled back to the fundamental annulus. -/
noncomputable def Hseq : ℕ → (ℝ → ℝ)
  | 0 => phi
  | (n + 1) => fun t => (lam ^ n)⁻¹ * deriv (Hseq n) t + beta * Hseq n t

/-- The open set on which the seed (and all its outward propagates) vanish. -/
def Uset (lam e : ℝ) : Set ℝ := {t : ℝ | |t| < 1 + e ∨ |lam| - e < |t|}

theorem isOpen_Uset (lam e : ℝ) : IsOpen (Uset lam e) := by
  have h1 : IsOpen {t : ℝ | |t| < 1 + e} := isOpen_lt (by fun_prop) continuous_const
  have h2 : IsOpen {t : ℝ | |lam| - e < |t|} := isOpen_lt continuous_const (by fun_prop)
  exact h1.union h2

variable {beta lam phi}

theorem Hseq_contDiff (hsmooth : ∀ m : ℕ, ContDiff ℝ m phi) (n : ℕ) :
    ∀ m : ℕ, ContDiff ℝ m (Hseq beta lam phi n) := by
  induction n with
  | zero => exact hsmooth
  | succ n ih =>
      intro m
      have hd : ContDiff ℝ m (deriv (Hseq beta lam phi n)) := by
        have := ih (m + 1)
        rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; ring,
          contDiff_succ_iff_deriv] at this
        exact this.2.2
      exact (contDiff_const.mul hd).add (contDiff_const.mul (ih m))

theorem Hseq_vanish {e : ℝ} (hsupp : ∀ t ∈ Uset lam e, phi t = 0) (n : ℕ) :
    ∀ t ∈ Uset lam e, Hseq beta lam phi n t = 0 := by
  induction n with
  | zero => exact hsupp
  | succ n ih =>
      intro t ht
      have hev : Hseq beta lam phi n =ᶠ[nhds t] fun _ => 0 :=
        Filter.eventuallyEq_of_mem ((isOpen_Uset lam e).mem_nhds ht) ih
      have : deriv (Hseq beta lam phi n) t = 0 := by
        rw [hev.deriv_eq]; simp
      simp [Hseq, this, ih t ht]

theorem deriv_Hseq_vanish {e : ℝ} (hsupp : ∀ t ∈ Uset lam e, phi t = 0) (n : ℕ) :
    ∀ t ∈ Uset lam e, deriv (Hseq beta lam phi n) t = 0 := by
  intro t ht
  have hev : Hseq beta lam phi n =ᶠ[nhds t] fun _ => 0 :=
    Filter.eventuallyEq_of_mem ((isOpen_Uset lam e).mem_nhds ht)
      (Hseq_vanish hsupp n)
  rw [hev.deriv_eq]; simp

/-- The outward extension of the seed. -/
noncomputable def Wout (beta lam : ℝ) (phi : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∑' n : ℕ, Hseq beta lam phi n (x / lam ^ n)

variable {e : ℝ}

theorem Wout_eq_sum (he : 0 < e) (hlam : 1 < |lam|)
    (hsupp : ∀ t ∈ Uset lam e, phi t = 0) {x : ℝ} {N : ℕ} (hx : |x| ≤ |lam| ^ N) :
    Wout beta lam phi x = ∑ n ∈ range N, Hseq beta lam phi n (x / lam ^ n) := by
  refine tsum_eq_sum ?_
  intro n hn
  refine Hseq_vanish hsupp n _ (Or.inl ?_)
  have hN : N ≤ n := by simpa using Finset.mem_range.not.1 hn
  have h1 : (1 : ℝ) < |lam| := hlam
  have hpow : |lam| ^ N ≤ |lam| ^ n := pow_le_pow_right₀ h1.le hN
  have hposn : (0 : ℝ) < |lam| ^ n := by positivity
  rw [abs_div, abs_pow]
  have : |x| / |lam| ^ n ≤ 1 := by
    rw [div_le_one hposn]
    exact hx.trans hpow
  linarith

theorem Wout_zero_of_abs_le_one (he : 0 < e) (hlam : 1 < |lam|)
    (hsupp : ∀ t ∈ Uset lam e, phi t = 0) {x : ℝ} (hx : |x| ≤ 1) :
    Wout beta lam phi x = 0 := by
  rw [Wout_eq_sum he hlam hsupp (N := 0) (by simpa using hx)]
  simp

theorem Wout_eq_phi (he : 0 < e) (hlam : 1 < |lam|)
    (hsupp : ∀ t ∈ Uset lam e, phi t = 0) {x : ℝ} (hx : |x| ≤ |lam|) :
    Wout beta lam phi x = phi x := by
  rw [Wout_eq_sum he hlam hsupp (N := 1) (by simpa using hx)]
  simp [Hseq]

/-- The outward extension satisfies the equation up to the inhomogeneity `phi (lam t)`,
which is supported in the shell `|lam|⁻¹ < |t| < 1`. -/
theorem Wout_hasDerivAt (he : 0 < e) (hlam : 1 < |lam|)
    (hsmooth : ∀ m : ℕ, ContDiff ℝ m phi) (hsupp : ∀ t ∈ Uset lam e, phi t = 0) (t : ℝ) :
    HasDerivAt (Wout beta lam phi)
      (Wout beta lam phi (lam * t) - beta * Wout beta lam phi t - phi (lam * t)) t := by
  have hlam0 : lam ≠ 0 := by
    intro h; rw [h] at hlam; simp at hlam; linarith
  have habs1 : (1 : ℝ) < |lam| := hlam
  obtain ⟨M, hM⟩ : ∃ M : ℕ, |t| < |lam| ^ M := pow_unbounded_of_one_lt _ habs1
  have hpowpos : ∀ k : ℕ, (0 : ℝ) < |lam| ^ k := fun k => by positivity
  -- bounds
  have hmono : ∀ {a b : ℕ}, a ≤ b → |lam| ^ a ≤ |lam| ^ b := fun hab =>
    pow_le_pow_right₀ habs1.le hab
  have ht2 : |t| ≤ |lam| ^ (M + 2) := le_of_lt (hM.trans_le (hmono (by omega)))
  have hlt2 : |lam * t| ≤ |lam| ^ (M + 2) := by
    rw [abs_mul]
    calc |lam| * |t| ≤ |lam| * |lam| ^ M := by nlinarith [hpowpos M]
      _ = |lam| ^ (M + 1) := by ring
      _ ≤ |lam| ^ (M + 2) := hmono (by omega)
  -- the last term of the sums vanishes
  have hlast : t / lam ^ (M + 1) ∈ Uset lam e := by
    refine Or.inl ?_
    rw [abs_div, abs_pow]
    have h1 : |t| / |lam| ^ (M + 1) < 1 := by
      rw [div_lt_one (hpowpos _)]
      exact hM.trans_le (hmono (by omega))
    linarith
  -- localize
  have hopen : IsOpen {y : ℝ | |y| < |lam| ^ (M + 2)} := isOpen_lt (by fun_prop) continuous_const
  have hmem : t ∈ {y : ℝ | |y| < |lam| ^ (M + 2)} := lt_of_lt_of_le hM (hmono (by omega))
  have hlocal : Wout beta lam phi =ᶠ[nhds t]
      fun y => ∑ n ∈ range (M + 2), Hseq beta lam phi n (y / lam ^ n) :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem)
      (fun y hy => Wout_eq_sum he hlam hsupp (le_of_lt hy))
  have hderiv : HasDerivAt (fun y => ∑ n ∈ range (M + 2), Hseq beta lam phi n (y / lam ^ n))
      (∑ n ∈ range (M + 2), (lam ^ n)⁻¹ * deriv (Hseq beta lam phi n) (t / lam ^ n)) t := by
    have hterm : ∀ n : ℕ, HasDerivAt (fun y : ℝ => Hseq beta lam phi n (y / lam ^ n))
        ((lam ^ n)⁻¹ * deriv (Hseq beta lam phi n) (t / lam ^ n)) t := by
      intro n
      have hdiff : HasDerivAt (Hseq beta lam phi n)
          (deriv (Hseq beta lam phi n) (t / lam ^ n)) (t / lam ^ n) :=
        (((Hseq_contDiff hsmooth n 1).differentiable (by norm_num)) (t / lam ^ n)).hasDerivAt
      have := hdiff.comp t ((hasDerivAt_id t).div_const (lam ^ n))
      simpa [mul_comm, one_div] using this
    have hsum := HasDerivAt.sum (u := range (M + 2))
      (A := fun n (y : ℝ) => Hseq beta lam phi n (y / lam ^ n))
      (A' := fun n => (lam ^ n)⁻¹ * deriv (Hseq beta lam phi n) (t / lam ^ n))
      (fun n _ => hterm n)
    exact hsum.congr_of_eventuallyEq (by filter_upwards with y; simp)
  rw [hlocal.hasDerivAt_iff]
  convert hderiv using 1
  -- the algebraic identity
  have hW1 : Wout beta lam phi (lam * t)
      = ∑ n ∈ range (M + 2), Hseq beta lam phi n (lam * t / lam ^ n) :=
    Wout_eq_sum he hlam hsupp hlt2
  have hW2 : Wout beta lam phi t = ∑ n ∈ range (M + 2), Hseq beta lam phi n (t / lam ^ n) :=
    Wout_eq_sum he hlam hsupp ht2
  have hshift : ∀ n : ℕ, lam * t / lam ^ (n + 1) = t / lam ^ n := by
    intro n
    field_simp
    ring
  have hsum1 : ∑ n ∈ range (M + 2), Hseq beta lam phi n (lam * t / lam ^ n)
      = (∑ n ∈ range (M + 1),
          ((lam ^ n)⁻¹ * deriv (Hseq beta lam phi n) (t / lam ^ n)
            + beta * Hseq beta lam phi n (t / lam ^ n))) + phi (lam * t) := by
    rw [Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [hshift n]
      rfl
    · simp [Hseq]
  have hsum2 : ∑ n ∈ range (M + 2), Hseq beta lam phi n (t / lam ^ n)
      = ∑ n ∈ range (M + 1), Hseq beta lam phi n (t / lam ^ n) := by
    rw [Finset.sum_range_succ, Hseq_vanish hsupp _ _ hlast, add_zero]
  have hsum3 : ∑ n ∈ range (M + 2), (lam ^ n)⁻¹ * deriv (Hseq beta lam phi n) (t / lam ^ n)
      = ∑ n ∈ range (M + 1), (lam ^ n)⁻¹ * deriv (Hseq beta lam phi n) (t / lam ^ n) := by
    rw [Finset.sum_range_succ, deriv_Hseq_vanish hsupp _ _ hlast, mul_zero, add_zero]
  rw [hW1, hW2, hsum1, hsum2, hsum3, Finset.sum_add_distrib, Finset.mul_sum]
  ring

end Outward

end Q756
