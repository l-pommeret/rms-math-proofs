/-
Q756 — gluing the outward extension and the inward correction into a genuine solution.

If the two one-sided limits of the inward correction at the origin agree (with common value `L`),
then the function

  `Gsol beta lam phi L t = if t = 0 then L else Wout beta lam phi t + Vin beta lam phi t`

is a solution of `g' t = g (lam t) - beta * g t` on all of `ℝ`.
-/
import RMS.Q756Limits

namespace Q756

open Set Filter Topology

variable {beta lam e L : ℝ} {phi : ℝ → ℝ}

/-- The candidate solution attached to a seed `phi` and a value `L` at the origin. -/
noncomputable def Gsol (beta lam : ℝ) (phi : ℝ → ℝ) (L : ℝ) : ℝ → ℝ :=
  fun t => if t = 0 then L else Wout beta lam phi t + Vin beta lam phi t

theorem Gsol_of_ne {t : ℝ} (ht : t ≠ 0) :
    Gsol beta lam phi L t = Wout beta lam phi t + Vin beta lam phi t := if_neg ht

theorem Gsol_at_zero : Gsol beta lam phi L 0 = L := if_pos rfl

theorem eventually_abs_le_one : ∀ᶠ x in nhds (0:ℝ), |x| ≤ 1 := by
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) one_pos] with x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  exact hx.le

theorem Gsol_tendsto_pos (hlam : 1 < |lam|) (he : 0 < e) (hseed : IsSeed lam e phi)
    (hpos : Lpos beta lam phi = L) :
    Tendsto (Gsol beta lam phi L) (𝓝[>] (0:ℝ)) (𝓝 L) := by
  have hev : Gsol beta lam phi L =ᶠ[𝓝[>] (0:ℝ)] Vin beta lam phi := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds eventually_abs_le_one] with x hx hx1
    rw [Gsol_of_ne (ne_of_gt hx), Wout_zero_of_abs_le_one he hlam hseed.vanish hx1, zero_add]
  have := Vin_tendsto_pos (beta := beta) hlam he hseed
  rw [hpos] at this
  exact this.congr' hev.symm

theorem Gsol_tendsto_neg (hlam : 1 < |lam|) (he : 0 < e) (hseed : IsSeed lam e phi)
    (hneg : Lneg beta lam phi = L) :
    Tendsto (Gsol beta lam phi L) (𝓝[<] (0:ℝ)) (𝓝 L) := by
  have hev : Gsol beta lam phi L =ᶠ[𝓝[<] (0:ℝ)] Vin beta lam phi := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds eventually_abs_le_one] with x hx hx1
    rw [Gsol_of_ne (ne_of_lt hx), Wout_zero_of_abs_le_one he hlam hseed.vanish hx1, zero_add]
  have := Vin_tendsto_neg (beta := beta) hlam he hseed
  rw [hneg] at this
  exact this.congr' hev.symm

theorem Gsol_continuousAt_zero (hlam : 1 < |lam|) (he : 0 < e) (hseed : IsSeed lam e phi)
    (hpos : Lpos beta lam phi = L) (hneg : Lneg beta lam phi = L) :
    ContinuousAt (Gsol beta lam phi L) 0 := by
  rw [← continuousWithinAt_compl_self]
  have h : Tendsto (Gsol beta lam phi L) (𝓝[≠] (0:ℝ)) (𝓝 L) := by
    rw [← nhdsLT_sup_nhdsGT, tendsto_sup]
    exact ⟨Gsol_tendsto_neg hlam he hseed hneg, Gsol_tendsto_pos hlam he hseed hpos⟩
  simpa [ContinuousWithinAt, Gsol_at_zero] using h

/-- **Existence, main step.** A seed whose two one-sided limits agree produces a solution. -/
theorem Gsol_isSol (hlam : 1 < |lam|) (he : 0 < e) (hseed : IsSeed lam e phi)
    (hpos : Lpos beta lam phi = L) (hneg : Lneg beta lam phi = L) :
    IsSol beta lam (Gsol beta lam phi L) := by
  have hc := Gsol_continuousAt_zero hlam he hseed hpos hneg
  have hderiv : ∀ y ≠ (0:ℝ), HasDerivAt (Gsol beta lam phi L)
      (Gsol beta lam phi L (lam * y) - beta * Gsol beta lam phi L y) y := by
    intro y hy
    have hW := Wout_hasDerivAt (beta := beta) he hlam hseed.smooth hseed.vanish y
    have hV := Vin_hasDerivAt (beta := beta) hlam he hseed.cont hseed.supp hy
    have hev : Gsol beta lam phi L =ᶠ[nhds y]
        fun t => Wout beta lam phi t + Vin beta lam phi t := by
      filter_upwards [isOpen_ne.mem_nhds hy] with x hx using Gsol_of_ne hx
    rw [hev.hasDerivAt_iff, Gsol_of_ne (mul_ne_zero (lam_ne_zero hlam) hy), Gsol_of_ne hy]
    convert hW.add hV using 1
    ring
  have hg : ContinuousAt (fun y : ℝ => Gsol beta lam phi L (lam * y)
      - beta * Gsol beta lam phi L y) 0 := by
    have hmul : ContinuousAt (fun y : ℝ => lam * y) 0 :=
      (continuous_const.mul continuous_id).continuousAt
    have h1 : ContinuousAt (fun y : ℝ => Gsol beta lam phi L (lam * y)) 0 :=
      ContinuousAt.comp (g := Gsol beta lam phi L) (x := (0:ℝ)) (by simpa using hc) hmul
    exact h1.sub (continuousAt_const.mul hc)
  exact fun t => hasDerivAt_of_hasDerivAt_of_ne' hderiv hc hg t

end Q756
