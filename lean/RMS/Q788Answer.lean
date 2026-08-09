/-
# Q788 — aggregate module: the canonical answers

This module gathers the two canonical claims of Q788, restated directly in terms of the
authoritative statistic `Q788.chordMax` and the product law `Q788.angleLawN` of `n` independent
uniform angles.

* **Claim A (fixed level).**  `P(Dₙ ≥ α) = 1` for `α ≤ 2`; for every fixed `α > 2` and every real
  `A > 0` there is a constant `C = C(α, A)` with `P(Dₙ < α) ≤ C n^{-A}`, whence `P(Dₙ ≥ α) → 1`.
* **Claim B (fixed `n`, upper edge).**  For every fixed `n ≥ 2`,
  `P(Dₙ ≥ 2ⁿ(1-δ)) = κₙ δ^{(n-1)/2} (1 + O_n(δ))` with
  `κₙ = √n / Γ((n+1)/2) · (2/π)^{(n-1)/2}`, together with the ratio limit and its `α ↑ 2ⁿ` form.
-/
import RMS.Q788
import RMS.Q788Probability
import RMS.Q788Endpoint
import RMS.Q788LowerBound
import RMS.Q788UpperEdge
import RMS.Q788Volume
import RMS.Q788Ellipsoid
import RMS.Q788Slice
import RMS.Q788Localize
import RMS.Q788EdgeAsymptotic
import RMS.Q788Vec
import RMS.Q788PowerSum
import RMS.Q788CharFun
import RMS.Q788SmallBall
import RMS.Q788FixedLevel

open MeasureTheory Real Filter
open scoped ENNReal Topology

namespace Q788

/-! ## Claim A — the fixed level -/

/-- **Claim A, sure regime.**  For `α ≤ 2` the maximal chord product is at least `α` almost
surely: `P(Dₙ ≥ α) = 1`. -/
theorem answer_sure_regime {n : ℕ} (hn : 0 < n) (α : ℝ) (hα : α ≤ 2) :
    (angleLawN n {θ : Fin n → ℝ | α ≤ chordMax θ}).toReal = 1 :=
  probGE_of_le_two hn α hα

/-- **Claim A, superpolynomial decay.**  For every level `α > 2` and every real exponent `A`
there is a constant `C = C(α, A) > 0` such that `P(Dₙ < α) ≤ C n^{-A}` for all `n ≥ 1`. -/
theorem answer_superpolynomial_decay (α : ℝ) (hα : 2 < α) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (angleLawN n {θ : Fin n → ℝ | chordMax θ < α}).toReal ≤ C * (n : ℝ) ^ (-A) :=
  probLT_le_superpoly α hα A

/-- **Claim A, limit form.**  For every fixed level `α`, `P(Dₙ ≥ α) → 1` as `n → ∞`. -/
theorem answer_fixed_level_limit (α : ℝ) :
    Tendsto (fun n : ℕ => (angleLawN n {θ : Fin n → ℝ | α ≤ chordMax θ}).toReal) atTop (𝓝 1) :=
  probGE_tendsto_one α

/-! ## Claim B — the fixed-`n` upper edge -/

/-- **Claim B, quantitative relative error.**  For every fixed `n ≥ 2` there are `C > 0` and
`δ₀ > 0` such that for `0 < δ ≤ δ₀`,
`|P(Dₙ ≥ 2ⁿ(1-δ)) - κₙ δ^{(n-1)/2}| ≤ C δ · κₙ δ^{(n-1)/2}`. -/
theorem answer_upper_edge {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      |(angleLawN n {θ : Fin n → ℝ | 2 ^ n * (1 - δ) ≤ chordMax θ}).toReal
          - kappa n * δ ^ (((n : ℝ) - 1) / 2)|
        ≤ C * δ * (kappa n * δ ^ (((n : ℝ) - 1) / 2)) :=
  upperEdge_rel_error_rpow hn

/-- **Claim B, ratio limit.**  For every fixed `n ≥ 2`,
`P(Dₙ ≥ 2ⁿ(1-δ)) / (κₙ δ^{(n-1)/2}) → 1` as `δ → 0⁺`. -/
theorem answer_upper_edge_ratio {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun δ : ℝ =>
        (angleLawN n {θ : Fin n → ℝ | 2 ^ n * (1 - δ) ≤ chordMax θ}).toReal
          / (kappa n * (Real.sqrt δ) ^ (n - 1)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) :=
  upperEdge_ratio_tendsto hn

/-- **Claim B, the `α ↑ 2ⁿ` form.**  With `δ = (2ⁿ - α)/2ⁿ`,
`P(Dₙ ≥ α) / (κₙ δ^{(n-1)/2}) → 1` as `α ↑ 2ⁿ`. -/
theorem answer_upper_edge_alpha {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun α : ℝ =>
        (angleLawN n {θ : Fin n → ℝ | α ≤ chordMax θ}).toReal
          / (kappa n * (Real.sqrt ((2 ^ n - α) / 2 ^ n)) ^ (n - 1)))
      (𝓝[<] ((2 : ℝ) ^ n)) (𝓝 1) :=
  upperEdge_ratio_tendsto_alpha hn

end Q788
