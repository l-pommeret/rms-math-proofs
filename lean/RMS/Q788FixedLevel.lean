/-
# Q788 — Claim A: the fixed-level estimate

For every fixed `α > 2` and every real `A > 0` the probability that the maximal chord product of
`n` independent uniform points of the circle stays below `α` is `O(n^{-A})`; consequently
`P(D_n ≥ α) → 1`.  Together with the sure regime `α ≤ 2` this resolves the first regime of Q788.
-/
import RMS.Q788PowerSum
import RMS.Q788SmallBall

open MeasureTheory Real Set Filter
open scoped ENNReal Topology

namespace Q788

/-- **Claim A, quantitative form.**  For every level `α > 2` and every exponent `A > 0` there is
a constant `C` with `P(D_n < α) ≤ C n^{-A}` for all `n ≥ 1`.  (The statement is proved for
every real `A`, in particular for every `A > 0` as requested.) -/
theorem probLT_le_superpoly (α : ℝ) (hα : 2 < α) (A : ℝ) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → probLT n α ≤ C * (n : ℝ) ^ (-A) := by
  obtain ⟨K, hK1, hKA⟩ : ∃ K : ℕ, 1 ≤ K ∧ A ≤ (K : ℝ) := by
    refine ⟨max 1 ⌈A⌉₊, le_max_left _ _, ?_⟩
    calc A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
      _ ≤ ((max 1 ⌈A⌉₊ : ℕ) : ℝ) := by exact_mod_cast Nat.le_max_right 1 ⌈A⌉₊
  have h1α : (1 : ℝ) ≤ α := by linarith
  have h0α : (0 : ℝ) < α := by linarith
  obtain ⟨C, hC, hbound⟩ := exists_smallBall K (powerBound K α)
  refine ⟨C, hC, fun n hn => ?_⟩
  have hsub : {θ : Fin n → ℝ | chordMax θ < α} ⊆
      {θ : Fin n → ℝ | sqNorm (powerVec K θ) ≤ powerBound K α} := fun θ hθ =>
    sqNorm_powerVec_le_of_chordMax_le θ h1α (le_of_lt hθ)
  have hstep : probLT n α ≤ C / (n : ℝ) ^ K := by
    refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)) (hbound n hn)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ A ≤ (n : ℝ) ^ K := by
    rw [show ((n : ℝ) ^ K) = (n : ℝ) ^ (K : ℝ) by rw [Real.rpow_natCast]]
    exact Real.rpow_le_rpow_of_exponent_le hn1 hKA
  have hposA : (0 : ℝ) < (n : ℝ) ^ A := Real.rpow_pos_of_pos (by linarith) A
  calc probLT n α ≤ C / (n : ℝ) ^ K := hstep
    _ ≤ C / (n : ℝ) ^ A := by
        exact div_le_div_of_nonneg_left hC.le hposA hpow
    _ = C * (n : ℝ) ^ (-A) := by
        rw [Real.rpow_neg (by linarith), div_eq_mul_inv]

/-- **Claim A, limit form.**  For every fixed level `α`, `P(D_n ≥ α) → 1` as `n → ∞`. -/
theorem probGE_tendsto_one (α : ℝ) :
    Tendsto (fun n : ℕ => probGE n α) atTop (nhds 1) := by
  rcases le_or_gt α 2 with h | h
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (probGE_of_le_two hn α h).symm
  · obtain ⟨C, hC, hbound⟩ := probLT_le_superpoly α h 1
    have hzero : Tendsto (fun n : ℕ => probLT n α) atTop (nhds 0) := by
      have hg : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-(1 : ℝ))) atTop (nhds 0) := by
        have h0 : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-(1 : ℝ))) atTop (nhds (C * 0)) :=
          Tendsto.const_mul C
            ((tendsto_rpow_neg_atTop one_pos).comp tendsto_natCast_atTop_atTop)
        simpa using h0
      refine squeeze_zero' (Eventually.of_forall fun n => probLT_nonneg n α) ?_ hg
      filter_upwards [eventually_ge_atTop 1] with n hn using hbound n hn
    have := Tendsto.const_sub (1 : ℝ) hzero
    simpa [probGE_eq_one_sub_probLT] using this

end Q788
