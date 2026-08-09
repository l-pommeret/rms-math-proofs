/-
# Q756 — summary of the formalization

Canonical source: <https://lucpommeret.com/assets/Qsansreponse260405.pdf>, problem Q756.

For `beta lam : ℝ` with `|lam| > 1` put

  `F(beta, lam) = { g ∈ C¹(ℝ, ℝ) : g' t = g (lam * t) - beta * g t  for every t }`.

Membership in `F(beta, lam)` is formalized by `Q756.IsSol beta lam g`, i.e.
`∀ t, HasDerivAt g (g (lam * t) - beta * g t) t`.  This is equivalent to the definition above:
differentiability with the prescribed derivative is exactly the displayed equation, and the
`C¹` requirement is automatic, since `Q756.sol_contDiff` shows every such `g` is `C^∞`.

## What is formalized

* Automatic regularity (§3): `Q756.sol_contDiff`, `Q756.hasDerivAt_iteratedDeriv`,
  `Q756.iteratedDeriv_zero`, `Q756.flat_of_sol_zero`.
* The complete classification of polynomial solutions (§4): `Q756_polynomial_classification`
  below, assembled from `Q756.resonance_of_poly_sol`, `Q756.Ppoly_isSol`,
  `Q756.Ppoly_natDegree`, `Q756.poly_sol_eq_smul_Ppoly`, `Q756.poly_sol_eq_zero_of_nonresonant`.
* The shell construction (§5–§7): for every `beta` and every `lam` with `1 < |lam|` there is a
  nonzero `C^∞` solution which is flat at the origin, hence nonpolynomial
  (`Q756_exists_flat_nonpolynomial_solution`), and the space of solutions is infinite
  dimensional (`Q756_solution_space_infinite_dimensional`,
  `Q756.exists_linearIndependent_flat_sols`).

## Mismatches with the printed text

* The material is split over several files of one Lean library rather than a single file
  (`RequestProject/Q756.lean`, `Q756Outward.lean`, `Q756Inner.lean`, `Q756Linear.lean`,
  `Q756Limits.lean`, `Q756Glue.lean`, `Q756Existence.lean`, `Q756Dimension.lean`, and this
  summary file); the whole library is self contained on top of Mathlib.
* The inward construction is organized slightly differently from §5.2/§6: instead of a
  shell-by-shell recursion it uses the Picard iterates of the Volterra operator `Q756.Vop`,
  whose sum is pointwise finite.  This yields exactly the same object and the same estimates.
* §7 kills the two one-sided limits with three seeds (a linear map `ℝ³ → ℝ²` has a nontrivial
  kernel); the formalization follows this argument, and obtains infinite dimensionality by
  placing seeds in disjoint windows of the fundamental annulus.
* The auxiliary Proposition of §8 (a solution that is real analytic near `0` is polynomial) is
  *not* formalized; it is not part of the main claim.

## Versions

Lean 4 toolchain `leanprover/lean4:v4.28.0`; Mathlib pinned at commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365` (tag `v4.28.0`).
-/
import RMS.Q756Dimension

namespace Q756

open Polynomial

/-- **Classification of the polynomial solutions (§4).**  Let `|lam| > 1`.

1. A nonzero polynomial solution can only occur at a resonant parameter `beta = lam ^ p`.
2. At a resonant parameter `beta = lam ^ p` the polynomial `Ppoly lam p` is a solution of
   degree exactly `p`, and every polynomial solution is a scalar multiple of it.
3. At a nonresonant parameter the zero polynomial is the only polynomial solution. -/
theorem Q756_polynomial_classification (lam : ℝ) (hlam : 1 < |lam|) :
    (∀ (beta : ℝ) (P : ℝ[X]), IsSol beta lam (fun t => P.eval t) → P ≠ 0 →
        beta = lam ^ P.natDegree) ∧
      (∀ p : ℕ, IsSol (lam ^ p) lam (fun t => (Ppoly lam p).eval t) ∧
        (Ppoly lam p).natDegree = p ∧ Ppoly lam p ≠ 0 ∧
        ∀ P : ℝ[X], IsSol (lam ^ p) lam (fun t => P.eval t) →
          P = C (P.coeff 0) * Ppoly lam p) ∧
      (∀ beta : ℝ, (∀ p : ℕ, beta ≠ lam ^ p) →
        ∀ P : ℝ[X], IsSol beta lam (fun t => P.eval t) → P = 0) :=
  ⟨fun _ P h hP => resonance_of_poly_sol P h hP,
   fun p => ⟨Ppoly_isSol lam p, Ppoly_natDegree lam hlam p, Ppoly_ne_zero lam hlam p,
     fun P h => poly_sol_eq_smul_Ppoly p P h⟩,
   fun _ hb P h => poly_sol_eq_zero_of_nonresonant P h hb⟩

/-- **Main theorem (§2).**  For every `beta` and every `lam` with `|lam| > 1` the space
`F(beta, lam)` contains a nonzero `C^∞` function which is flat at the origin; in particular
`F(beta, lam)` contains nonpolynomial functions. -/
theorem Q756_exists_flat_nonpolynomial_solution (beta lam : ℝ) (hlam : 1 < |lam|) :
    ∃ g : ℝ → ℝ, IsSol beta lam g ∧ (∀ n : ℕ, iteratedDeriv n g 0 = 0) ∧
      (∀ n : ℕ, ContDiff ℝ n g) ∧ g ≠ 0 ∧ ∀ P : ℝ[X], g ≠ fun t => P.eval t :=
  exists_flat_nonpolynomial_sol beta lam hlam

/-- **Main theorem, dimension statement (§2 and §7).**  For `|lam| > 1` the solution space
`F(beta, lam)` is infinite dimensional. -/
theorem Q756_solution_space_infinite_dimensional (beta lam : ℝ) (hlam : 1 < |lam|) :
    ¬ FiniteDimensional ℝ (solSpace beta lam) :=
  solSpace_not_finiteDimensional beta lam hlam

end Q756
