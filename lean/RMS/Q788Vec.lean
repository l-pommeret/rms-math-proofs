/-
# Q788 — the trigonometric vector statistic

Common definitions for the fixed-level estimate (Claim A).  For a truncation level `K` we
package the first `K` power sums

  `S_r(θ) = ∑_j e^{i r θ_j}`,  `r = 1, …, K`

as a real vector of dimension `2K`: the coordinate `(r, false)` is `∑_j cos((r+1)θ_j)` and the
coordinate `(r, true)` is `∑_j sin((r+1)θ_j)`.  This is a sum of independent identically
distributed bounded vectors, and the whole fixed-level argument is a small-ball estimate for it.
-/
import RMS.Q788Slice

open MeasureTheory Real Set
open scoped ENNReal Topology

namespace Q788

/-- The index set of the `2K` real trigonometric coordinates. -/
abbrev trigIdx (K : ℕ) : Type := Fin K × Bool

/-- `trigVec K t` is the vector `(cos t, sin t, cos 2t, sin 2t, …, cos Kt, sin Kt)`. -/
noncomputable def trigVec (K : ℕ) (t : ℝ) : trigIdx K → ℝ := fun i =>
  if i.2 then Real.sin ((((i.1 : ℕ) : ℝ) + 1) * t) else Real.cos ((((i.1 : ℕ) : ℝ) + 1) * t)

/-- The squared Euclidean norm on the `2K` coordinates. -/
noncomputable def sqNorm {K : ℕ} (x : trigIdx K → ℝ) : ℝ := ∑ i, (x i) ^ 2

/-- The real trigonometric polynomial `t ↦ ⟨ξ, trigVec K t⟩`; it has degree at most `K` and no
constant term. -/
noncomputable def trigPoly {K : ℕ} (ξ : trigIdx K → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ξ i * trigVec K t i

/-- The vector of the first `K` power sums of a configuration, in real coordinates. -/
noncomputable def powerVec (K : ℕ) {n : ℕ} (θ : Fin n → ℝ) : trigIdx K → ℝ :=
  fun i => ∑ j, trigVec K (θ j) i

/-- The characteristic function of `trigVec` under the uniform angle law. -/
noncomputable def charTrig (K : ℕ) (ξ : trigIdx K → ℝ) : ℂ :=
  ∫ t, Complex.exp ((trigPoly ξ t : ℂ) * Complex.I) ∂angleLaw

/-- The explicit constant in the characteristic-function gap. -/
noncomputable def charBoundConst (K : ℕ) : ℝ := 1 / (10 ^ 6 * (K : ℝ) ^ 2)

theorem charBoundConst_pos {K : ℕ} (hK : 1 ≤ K) : 0 < charBoundConst K := by
  have : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  rw [charBoundConst]
  positivity

theorem charBoundConst_le_one {K : ℕ} (hK : 1 ≤ K) : charBoundConst K ≤ 1 := by
  have h : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  rw [charBoundConst, div_le_one (by nlinarith)]
  nlinarith

theorem sqNorm_nonneg {K : ℕ} (x : trigIdx K → ℝ) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem abs_trigVec_le_one {K : ℕ} (t : ℝ) (i : trigIdx K) : |trigVec K t i| ≤ 1 := by
  rw [trigVec]
  by_cases h : i.2 <;> simp [h, Real.abs_sin_le_one, Real.abs_cos_le_one]

theorem card_trigIdx (K : ℕ) : Fintype.card (trigIdx K) = 2 * K := by
  simp [trigIdx, mul_comm]

/-- The measurability of the statistic. -/
theorem measurable_powerVec (K : ℕ) {n : ℕ} :
    Measurable fun θ : Fin n → ℝ => powerVec K θ := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Finset.measurable_sum _ fun j _ => ?_
  obtain ⟨r, b⟩ := i
  simp only [trigVec]
  cases b <;> simp <;> fun_prop

theorem measurableSet_sqNorm_le (K : ℕ) {n : ℕ} (b : ℝ) :
    MeasurableSet {θ : Fin n → ℝ | sqNorm (powerVec K θ) ≤ b} := by
  refine measurableSet_le ?_ measurable_const
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_pi_apply i).comp (measurable_powerVec K)).pow_const 2

end Q788
