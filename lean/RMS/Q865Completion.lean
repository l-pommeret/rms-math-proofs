import RMS.Q865

/-!
# Q865 — completion: the minimum modulus is attained

The file `RequestProject.Q865` proves the three parts of Q865, but it defines the quantity
`r m` of the printed statement as the *infimum* `Q865.rmin m` of the moduli of the complex
roots of `P m`.  The printed problem speaks of the **smallest** modulus of a complex root.

This file closes that gap: for every `m ≥ 2` the set of moduli of complex roots of `P m` is a
finite nonempty set of reals, hence its infimum is attained and is a genuine minimum
(`Q865.rmin_spec`).  Consequently `Q865.odd_limit` really is a statement about the canonical
sequence of attained minima.
-/

namespace Q865

open Finset Polynomial

/-- For `m ≥ 2` the polynomial `P m` is not the zero polynomial (its value at `1` is `1 - m`). -/
theorem Pc_ne_zero (m : ℕ) (hm : 2 ≤ m) : Pc m ≠ 0 := by
  intro h
  have h1 : (Pc m).eval 1 = 1 - (m : ℂ) := by simp [Pc]
  rw [h] at h1
  simp only [Polynomial.eval_zero] at h1
  have h2 : (m : ℂ) = 1 := by linear_combination h1
  have h3 : (m : ℕ) = 1 := by exact_mod_cast h2
  omega

/-- For `m ≥ 2` the polynomial `P m` has a complex root (indeed a positive real one). -/
theorem exists_isRoot (m : ℕ) (hm : 2 ≤ m) : ∃ z : ℂ, (Pc m).IsRoot z := by
  obtain ⟨x, ⟨hx, hxroot⟩, -⟩ := exists_unique_pos_root m hm
  refine ⟨(x : ℂ), ?_⟩
  have : ((x : ℂ)) ^ m = ∑ k ∈ range m, ((x : ℂ)) ^ k := by
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) hxroot
  simp [Polynomial.IsRoot, Pc, this]

/-- The set of moduli of complex roots of `P m` is nonempty for every `m ≥ 2`. -/
theorem rootNorms_nonempty (m : ℕ) (hm : 2 ≤ m) :
    ((fun z : ℂ => ‖z‖) '' {z : ℂ | (Pc m).IsRoot z}).Nonempty := by
  obtain ⟨z, hz⟩ := exists_isRoot m hm
  exact ⟨‖z‖, z, hz, rfl⟩

/-- The set of moduli of complex roots of `P m` is finite for every `m ≥ 2`. -/
theorem rootNorms_finite (m : ℕ) (hm : 2 ≤ m) :
    ((fun z : ℂ => ‖z‖) '' {z : ℂ | (Pc m).IsRoot z}).Finite :=
  (Polynomial.finite_setOf_isRoot (Pc_ne_zero m hm)).image _

/-- `rmin m` is a lower bound for the modulus of every complex root of `P m`. -/
theorem rmin_le_of_isRoot (m : ℕ) {z : ℂ} (hz : (Pc m).IsRoot z) : rmin m ≤ ‖z‖ :=
  csInf_le (rootSet_bddBelow m) ⟨z, hz, rfl⟩

/-- For `m ≥ 2` the infimum `rmin m` is attained: some complex root of `P m` has modulus
`rmin m`. -/
theorem rmin_attained (m : ℕ) (hm : 2 ≤ m) :
    ∃ z : ℂ, (Pc m).IsRoot z ∧ ‖z‖ = rmin m := by
  have hmem := (rootNorms_nonempty m hm).csInf_mem (rootNorms_finite m hm)
  obtain ⟨z, hz, hzn⟩ := hmem
  exact ⟨z, hz, hzn⟩

/-- **The bridge for Q865(c)**: for every `m ≥ 2`, `rmin m` is the *smallest* modulus of a
complex root of `P m`, i.e. it is attained and is a lower bound for all root moduli. -/
theorem rmin_spec (m : ℕ) (hm : 2 ≤ m) :
    ∃ z : ℂ,
      (Pc m).IsRoot z ∧
      ‖z‖ = rmin m ∧
      ∀ w : ℂ, (Pc m).IsRoot w → rmin m ≤ ‖w‖ := by
  obtain ⟨z, hz, hzn⟩ := rmin_attained m hm
  exact ⟨z, hz, hzn, fun w hw => rmin_le_of_isRoot m hw⟩

/-- `rmin m` is characterised as the least element of the set of moduli of roots, i.e. it is
`IsLeast` for that set. -/
theorem rmin_isLeast (m : ℕ) (hm : 2 ≤ m) :
    IsLeast ((fun z : ℂ => ‖z‖) '' {z : ℂ | (Pc m).IsRoot z}) (rmin m) := by
  obtain ⟨z, hz, hzn, hmin⟩ := rmin_spec m hm
  refine ⟨⟨z, hz, hzn⟩, ?_⟩
  rintro x ⟨w, hw, rfl⟩
  exact hmin w hw

/-!
## Synthesis: the three parts of Q865

* **(a)** `Q865.Acoef_formula` : for every `k` and every `n ≥ 1`,
  `A k (n) = (1/(k+1)!) ∏_{j<k} ((k+1) n + j) = C((k+1)(n+1) - 2, k)/(k+1)`.
* **(b)** `Q865.summable_A` (absolute convergence) together with `Q865.pos_root_eq_series`
  (and its binomial form `Q865.pos_root_eq_series'`) : for every `n ≥ 2` the series converges
  and its sum gives exactly the unique positive root `ρ n`
  (uniqueness/existence: `Q865.exists_unique_pos_root`).
* **(c)** `Q865.rmin_spec` (the infimum `rmin m` is the attained minimum modulus of a complex
  root of `P m`, for every `m ≥ 2`) together with `Q865.odd_limit`
  (`(2n+1)(1 - r (2n+1)) → log 3`).
-/

/-- **Q865, synthesis.**  The three printed claims, packaged together:

(a) the closed formula for the coefficient polynomials `A k`;
(b) convergence of the series and the exact identity for the positive root of `P n`, `n ≥ 2`;
(c) `(2n+1)(1 - r (2n+1)) → log 3`, where `r m = rmin m` is the *attained minimum* modulus of a
complex root of `P m`. -/
theorem Q865_answer :
    (∀ k n : ℕ, 1 ≤ n →
        (Acoef k).eval (n : ℚ) = (((k + 1) * (n + 1) - 2).choose k : ℚ) / (k + 1)) ∧
    (∀ n : ℕ, 2 ≤ n → Summable (fun k : ℕ => Aval k n * uu n ^ (k + 1))) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ x : ℝ, 0 < x → x ^ n = ∑ k ∈ range n, x ^ k →
        x = 2 * (1 - ∑' k : ℕ, Aval k n * uu n ^ (k + 1))) ∧
    (∀ m : ℕ, 2 ≤ m → ∃ z : ℂ, (Pc m).IsRoot z ∧ ‖z‖ = rmin m ∧
        ∀ w : ℂ, (Pc m).IsRoot w → rmin m ≤ ‖w‖) ∧
    Filter.Tendsto (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ) * (1 - rmin (2 * n + 1))) Filter.atTop
      (nhds (Real.log 3)) :=
  ⟨fun k n hn => Acoef_formula k n hn,
   fun n hn => summable_A n hn,
   fun n hn _ hx hroot => pos_root_eq_series n hn hx hroot,
   fun m hm => rmin_spec m hm,
   odd_limit⟩

end Q865
