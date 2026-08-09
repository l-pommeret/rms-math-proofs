import RMS.Q867SpaceE

/-!
# Entire functions of small exponential type restrict to elements of `E`

If `g : ℂ → ℂ` is entire and satisfies `‖g z‖ ≤ K * exp (|Im z| / 4)`, then Cauchy's
estimates on the circle of radius `4 n` show that all derivatives of the restriction of
`g` to `ℝ` are bounded by `K`; in particular this restriction lies in `E` and has norm
at most `K`.
-/

noncomputable section

open Filter Topology Complex

namespace Q867

lemma norm_sin_le (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have h1 : ‖Complex.exp (-w * I) - Complex.exp (w * I)‖ ≤ Real.exp w.im + Real.exp (-w.im) := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_exp, Complex.norm_exp]
    simp
  have h2 : Real.exp w.im ≤ Real.exp |w.im| := Real.exp_le_exp.2 (le_abs_self _)
  have h3 : Real.exp (-w.im) ≤ Real.exp |w.im| := Real.exp_le_exp.2 (neg_le_abs _)
  rw [Complex.norm_ofNat]
  linarith

/-- The real iterated derivatives of the restriction to `ℝ` of an entire function are the
restrictions of its complex iterated derivatives. -/
lemma iteratedDeriv_ofReal (g : ℂ → ℂ) (hg : Differentiable ℂ g) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t : ℝ => g t) x = iteratedDeriv n g x := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
      have hdg : Differentiable ℂ (deriv g) := by
        have h := (hg.contDiff (n := (⊤ : ℕ∞))).differentiable_iteratedDeriv 1
          (compareOfLessAndEq_eq_lt.mp rfl)
        simpa [iteratedDeriv_one] using h
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      have he : deriv (fun t : ℝ => g t) = fun t : ℝ => deriv g t := by
        funext t
        exact ((hg (t : ℂ)).hasDerivAt.comp_ofReal).deriv
      rw [he]
      exact ih (deriv g) hdg

lemma contDiff_ofReal (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => g t) :=
  (hg.contDiff.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff

/-- **Cauchy's estimate**, in the form needed here: an entire function bounded by
`K * exp (|Im z| / 4)` has all its derivatives on the real line bounded by `K`. -/
theorem norm_iteratedDeriv_ofReal_le {g : ℂ → ℂ} (hg : Differentiable ℂ g) {K : ℝ}
    (hK : ∀ z : ℂ, ‖g z‖ ≤ K * Real.exp (|z.im| / 4)) (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n (fun t : ℝ => g t) x‖ ≤ K := by
  have hK0 : 0 ≤ K := by
    have := (norm_nonneg (g 0)).trans (hK 0)
    simpa using this
  rw [iteratedDeriv_ofReal g hg n x]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using (hK (x : ℂ))
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hcauchy : ‖iteratedDeriv n g x‖ ≤ (n.factorial : ℝ) * (K * Real.exp n) / (4 * n) ^ n := by
      refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (R := 4 * n)
        (by positivity) hg.diffContOnCl ?_
      intro z hz
      rw [mem_sphere_iff_norm] at hz
      have him : |z.im| ≤ 4 * n := by
        have h := abs_im_le_norm (z - (x : ℂ))
        simpa [hz] using h
      refine (hK z).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hK0
    refine hcauchy.trans ?_
    have hden : (0 : ℝ) < (4 * n) ^ n := by positivity
    rw [div_le_iff₀ hden]
    have h1 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have h2 : Real.exp (n : ℝ) ≤ 4 ^ n := by
      have he : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
        rw [← Real.exp_nat_mul]; ring_nf
      rw [he]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) n
    calc (n.factorial : ℝ) * (K * Real.exp n) ≤ (n : ℝ) ^ n * (K * 4 ^ n) := by
          exact mul_le_mul h1 (by nlinarith [Real.exp_pos ((n : ℝ))]) (by positivity)
            (by positivity)
      _ = K * (4 * n) ^ n := by rw [mul_pow]; ring

/-- The restriction to `ℝ` of an entire function of exponential type at most `1/4`
which is bounded on horizontal lines is an element of `E`. -/
theorem isE_ofReal {g : ℂ → ℂ} (hg : Differentiable ℂ g) {K : ℝ}
    (hK : ∀ z : ℂ, ‖g z‖ ≤ K * Real.exp (|z.im| / 4)) :
    IsE (fun t : ℝ => g t) :=
  ⟨contDiff_ofReal g hg, K, fun n x => norm_iteratedDeriv_ofReal_le hg hK n x⟩

theorem norm_mk_ofReal_le {g : ℂ → ℂ} (hg : Differentiable ℂ g) {K : ℝ}
    (hK : ∀ z : ℂ, ‖g z‖ ≤ K * Real.exp (|z.im| / 4)) :
    ‖E.mk _ (isE_ofReal hg hK)‖ ≤ K := by
  have hK0 : 0 ≤ K := by
    have := (norm_nonneg (g 0)).trans (hK 0)
    simpa using this
  exact (E.norm_le_iff hK0).2 (fun n x => norm_iteratedDeriv_ofReal_le hg hK n x)

end Q867
