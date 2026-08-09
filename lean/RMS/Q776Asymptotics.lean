import RMS.Q776Gate3
import RMS.Q776Local
import RMS.Q776Gap

/-!
# Q776 — the leading additive asymptotics on the negative axis

This module exposes the *canonical* asymptotic statements of Q776 in the exact form
requested:

* `Q776.f_two_leading_stationary_phase` — the boundary case `m = 2`,
  `‖f 2 (-R²) - (πR)^{-1/2} cos (2R - π/4)‖ ≤ C (πR)^{-1/2}/R`,
  obtained from the kernel-checked stationary phase analysis of the defining integral
  (`Q776.f_two_stationary_phase`, itself built on `Q776.f_two_neg`);
* `Q776.leading_additive` — the leading additive estimate for every fixed `m ≥ 2`,
  obtained for `m ≥ 3` from the torus representation, the classification of the dominant
  saddles, the off-saddle exponential gap and the local multidimensional Laplace estimate.

Both are *additive* estimates, valid through the zeros of the cosine.
-/

open scoped Real Nat
open Complex MeasureTheory

namespace Q776

/-- **Gate 2.**  The leading stationary phase estimate for `m = 2`:
`|f 2 (-R²) - (πR)^{-1/2} cos (2R - π/4)| ≤ C (πR)^{-1/2} / R` for all large `R`. -/
theorem f_two_leading_stationary_phase :
    ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ R : ℝ, R0 ≤ R →
        ‖f 2 (-((R:ℂ)^2))
          - ((1 / Real.sqrt (π*R) * Real.cos (2*R - π/4) : ℝ) : ℂ)‖
          ≤ C * (1 / Real.sqrt (π*R)) / R := by
  obtain ⟨C, R0, hC0, hR0, h⟩ := leading_additive_two
  refine ⟨C, R0, hC0, hR0, fun R hR => ?_⟩
  have hRpos : (0:ℝ) < R := by linarith
  have hA : amplitude 2 R = 1 / Real.sqrt (π*R) := amplitude_two hRpos
  have := h R hR
  rwa [hA, phase_two] at this

/-! ## The case `m ≥ 3` -/

/-- The volume of the cube `[-π,π]^d`. -/
theorem volume_cube (d : ℕ) : (volume (cube d)).toReal = (2*π)^d := by
  have hpi := Real.pi_pos
  rw [cube, volume_pi_pi]
  simp only [Real.volume_Icc, sub_neg_eq_add, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith), ENNReal.toReal_ofReal (by positivity)]
  ring_nf

theorem leading_additive_ge_three {d : ℕ} (hd : 2 ≤ d) :
    ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ R : ℝ, R0 ≤ R →
        ‖f (d+1) (-((R:ℂ)^(d+1)))
            - ((amplitude (d+1) R * Real.cos (phase (d+1) R) : ℝ) : ℂ)‖
          ≤ C * amplitude (d+1) R / R := by
  have hpi := Real.pi_pos
  have ha : 0 < alpha (d+1) := alpha_pos (by omega)
  have ha3 : alpha (d+1) ≤ π/3 := alpha_le_pi_div_three (by omega)
  have hkap : 0 < Real.cos (alpha (d+1)) := cos_alpha_pos (by omega)
  obtain ⟨δ0, hδ0, hlocall⟩ := local_estimate hd
  set δ : ℝ := min δ0 (alpha (d+1) / 2) with hδdef
  have hδpos : 0 < δ := lt_min hδ0 (by positivity)
  have hδa : δ ≤ alpha (d+1)/2 := min_le_right _ _
  obtain ⟨C1, R1, hC1, hR1, hlocb⟩ := hlocall δ hδpos (min_le_left _ _)
  obtain ⟨η, hη, hgap⟩ := offSaddle_gap (d := d) (by omega) hδpos
  obtain ⟨R2, hR2, hpow⟩ := exists_pow_le_exp (d+1) hη
  set c0 : ℝ := 2 * (2*π) ^ (-(d:ℝ)/2) / Real.sqrt (d+1) with hc0def
  have hc0 : 0 < c0 := by
    apply div_pos (by positivity) (Real.sqrt_pos.2 (by positivity))
  have htwopi : (0:ℝ) < (2*π)^d := by positivity
  -- geometry
  have hbox : box d δ ⊆ cube d := by
    intro θ hθ j _
    have := hθ j (Set.mem_univ j)
    simp only [Set.mem_Icc] at this ⊢
    constructor <;> linarith [this.1, this.2]
  have hboxN : boxNeg d δ ⊆ cube d := by
    intro θ hθ j _
    have := hθ j (Set.mem_univ j)
    simp only [Set.mem_Icc] at this ⊢
    constructor <;> linarith [this.1, this.2]
  have hdisj : Disjoint (box d δ) (boxNeg d δ) := by
    rw [Set.disjoint_left]
    intro θ h1 h2
    have j0 : Fin d := ⟨0, by omega⟩
    have e1 := h1 j0 (Set.mem_univ j0)
    have e2 := h2 j0 (Set.mem_univ j0)
    simp only [Set.mem_Icc] at e1 e2
    linarith [e1.1, e1.2, e2.1, e2.2]
  refine ⟨(((2*π)^d)⁻¹ * (2*C1) + 1)/c0, max R1 R2, by positivity, le_trans hR1 (le_max_left _ _),
    fun R hR => ?_⟩
  have hRR1 : R1 ≤ R := le_trans (le_max_left _ _) hR
  have hRR2 : R2 ≤ R := le_trans (le_max_right _ _) hR
  have hR1' : (1:ℝ) ≤ R := le_trans hR1 hRR1
  have hRpos : (0:ℝ) < R := by linarith
  set F : (Fin d → ℝ) → ℂ := fun θ => Complex.exp (rr (d+1) R * torusPhase θ) with hFdef
  set J : ℂ := ∫ θ in box d δ, F θ with hJdef
  set M : ℂ := mainTerm d R with hMdef
  set S : Set (Fin d → ℝ) := cube d \ (box d δ ∪ boxNeg d δ) with hSdef
  set E : ℂ := ∫ θ in S, F θ with hEdef
  have hFc : Continuous F := continuous_integrand _
  have hIcube : IntegrableOn F (cube d) :=
    hFc.continuousOn.integrableOn_compact (isCompact_cube d)
  have hIbox : IntegrableOn F (box d δ) :=
    hFc.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)
  have hIboxN : IntegrableOn F (boxNeg d δ) :=
    hFc.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)
  have hIrest : IntegrableOn F S := hIcube.mono_set Set.diff_subset
  -- the splitting
  have hsub : box d δ ∪ boxNeg d δ ⊆ cube d := Set.union_subset hbox hboxN
  have hsplit : (∫ θ in cube d, F θ) = J + (∫ θ in boxNeg d δ, F θ) + E := by
    calc (∫ θ in cube d, F θ)
        = ∫ θ in ((box d δ ∪ boxNeg d δ) ∪ S), F θ := by
          rw [hSdef, Set.union_diff_cancel hsub]
      _ = (∫ θ in (box d δ ∪ boxNeg d δ), F θ) + E := by
          refine setIntegral_union ?_ ?_ (hIbox.union hIboxN) hIrest
          · exact Set.disjoint_sdiff_right
          · exact ((measurableSet_cube d).diff
              ((measurableSet_box d δ).union (measurableSet_boxNeg d δ)))
      _ = J + (∫ θ in boxNeg d δ, F θ) + E := by
          rw [setIntegral_union hdisj (measurableSet_boxNeg d δ) hIbox hIboxN]
  have htorus : (∫ θ in cube d, F θ) = ((2*(π:ℂ))^d) * f (d+1) (-((R:ℂ)^(d+1))) := by
    rw [hFdef, torus_rep d (rr (d+1) R), rr_pow (by omega)]
  have hconj : (∫ θ in boxNeg d δ, F θ) = (starRingEnd ℂ) J := integral_boxNeg_eq_conj δ R
  -- the off-saddle bound
  have hrest : ‖E‖ ≤ (2*π)^d * Real.exp (R * (((d:ℝ)+1) * Real.cos (alpha (d+1)) - η)) := by
    have hbd : ∀ θ ∈ S, ‖F θ‖ ≤ Real.exp (R * (((d:ℝ)+1) * Real.cos (alpha (d+1)) - η)) := by
      intro θ hθ
      have hθc : θ ∈ cube d := hθ.1
      have hnb : θ ∉ box d δ := fun h => hθ.2 (Or.inl h)
      have hnbN : θ ∉ boxNeg d δ := fun h => hθ.2 (Or.inr h)
      have h1 : ∃ j, δ ≤ |θ j| := by
        by_contra hcon
        push_neg at hcon
        exact hnb fun j _ => by
          have := hcon j
          rw [abs_lt] at this
          exact ⟨this.1.le, this.2.le⟩
      have h2 : ∃ j, δ ≤ |θ j + 2 * alpha (d+1)| := by
        by_contra hcon
        push_neg at hcon
        refine hnbN fun j _ => ?_
        have := hcon j
        rw [abs_lt] at this
        constructor <;> [linarith [this.1]; linarith [this.2]]
      have hg := hgap θ hθc h1 h2
      rw [hFdef, norm_integrand]
      apply Real.exp_le_exp.2
      have hgg : gfun (d+1) θ ≤ ((d:ℝ)+1) * Real.cos (alpha (d+1)) - η := by
        push_cast at hg ⊢
        linarith
      exact mul_le_mul_of_nonneg_left hgg hRpos.le
    have hvol : volume S < ⊤ := by
      refine lt_of_le_of_lt (measure_mono (Set.diff_subset)) ?_
      rw [cube, volume_pi_pi]
      simp only [Real.volume_Icc]
      exact ENNReal.prod_lt_top (fun i _ => ENNReal.ofReal_lt_top)
    have hb := norm_setIntegral_le_of_norm_le_const hvol hbd
    refine le_trans hb ?_
    have hvle : (volume S).toReal ≤ (2*π)^d := by
      rw [← volume_cube d]
      exact ENNReal.toReal_mono (by
        rw [cube, volume_pi_pi]; simp only [Real.volume_Icc]
        exact (ENNReal.prod_lt_top (fun i _ => ENNReal.ofReal_lt_top)).ne)
        (measure_mono Set.diff_subset)
    have h9 := mul_le_mul_of_nonneg_left hvle
      (Real.exp_pos (R * (((d:ℝ)+1) * Real.cos (alpha (d+1)) - η))).le
    rw [measureReal_def]
    nlinarith [h9]
  -- the model term
  have hmodel : ((2*(π:ℂ))^d) * ((amplitude (d+1) R * Real.cos (phase (d+1) R) : ℝ) : ℂ)
      = M + (starRingEnd ℂ) M := by
    rw [Complex.add_conj, two_re_mainTerm (d := d) (by omega) hRpos]
    push_cast
    ring
  have hkey : ((2*(π:ℂ))^d) * (f (d+1) (-((R:ℂ)^(d+1)))
        - ((amplitude (d+1) R * Real.cos (phase (d+1) R) : ℝ) : ℂ))
      = (J - M) + (starRingEnd ℂ) (J - M) + E := by
    rw [mul_sub, ← htorus, hsplit, hconj, hmodel, map_sub]
    ring
  -- putting the bounds together
  set W : ℝ := Real.exp (((d:ℝ)+1) * R * Real.cos (alpha (d+1))) * R ^ (-(d:ℝ)/2 - 1) with hWdef
  have hWpos : 0 < W := by
    apply mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hRpos _)
  have hJM : ‖J - M‖ ≤ C1 * W := by
    have := hlocb R hRR1
    rw [hWdef]
    calc ‖J - M‖ ≤ C1 * Real.exp (((d:ℝ)+1) * R * Real.cos (alpha (d+1))) * R ^ (-((d:ℝ)/2) - 1) :=
          this
      _ = C1 * (Real.exp (((d:ℝ)+1) * R * Real.cos (alpha (d+1))) * R ^ (-(d:ℝ)/2 - 1)) := by
          rw [show (-((d:ℝ)/2) - 1) = (-(d:ℝ)/2 - 1) by ring]; ring
  have hEW : ‖E‖ ≤ (2*π)^d * W := by
    refine le_trans hrest ?_
    have hexp : Real.exp (R * (((d:ℝ)+1) * Real.cos (alpha (d+1)) - η))
        = Real.exp (((d:ℝ)+1) * R * Real.cos (alpha (d+1))) * Real.exp (-(η * R)) := by
      rw [← Real.exp_add]; ring_nf
    have hsmall : Real.exp (-(η*R)) ≤ R ^ (-(d:ℝ)/2 - 1) := by
      have h1 : R ^ ((d:ℝ)/2 + 1) ≤ R ^ ((d+1 : ℕ) : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hR1'
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) d]
      have h2 : R ^ ((d+1:ℕ) : ℝ) = R ^ (d+1) := by
        rw [Real.rpow_natCast]
      have h3 : R ^ (d+1) ≤ Real.exp (η * R) := hpow R hRR2
      rw [h2] at h1
      have h4 : R ^ ((d:ℝ)/2 + 1) ≤ Real.exp (η * R) := le_trans h1 h3
      have h5 : (0:ℝ) < R ^ ((d:ℝ)/2 + 1) := Real.rpow_pos_of_pos hRpos _
      rw [Real.exp_neg, show (-(d:ℝ)/2 - 1) = -((d:ℝ)/2 + 1) by ring, Real.rpow_neg hRpos.le]
      exact inv_anti₀ h5 h4
    rw [hexp, hWdef]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsmall (Real.exp_pos _).le) (by positivity)
  have hnormX : ‖f (d+1) (-((R:ℂ)^(d+1)))
      - ((amplitude (d+1) R * Real.cos (phase (d+1) R) : ℝ) : ℂ)‖
      ≤ ((2*π)^d)⁻¹ * (2 * ‖J - M‖ + ‖E‖) := by
    have h1 := congrArg norm hkey
    rw [norm_mul] at h1
    have h2 : ‖((2*(π:ℂ))^d)‖ = (2*π)^d := by
      rw [norm_pow]
      congr 1
      simp [Complex.norm_real, abs_of_nonneg hpi.le]
    rw [h2] at h1
    have h3 : ‖(J - M) + (starRingEnd ℂ) (J - M) + E‖ ≤ 2 * ‖J - M‖ + ‖E‖ := by
      refine le_trans (norm_add_le _ _) ?_
      have := norm_add_le (J - M) ((starRingEnd ℂ) (J - M))
      rw [RCLike.norm_conj] at this
      linarith
    rw [← h1] at h3
    have h4 := mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 htwopi.le)
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt htwopi), one_mul] at h4
    exact h4
  -- the amplitude in terms of W
  have hamp : amplitude (d+1) R / R = c0 * W := by
    rw [amplitude_succ d R, hc0def, hWdef]
    rw [show (-(d:ℝ)/2 - 1) = (-(d:ℝ)/2) - 1 by ring, Real.rpow_sub hRpos, Real.rpow_one]
    field_simp
  rw [show ((((2*π)^d)⁻¹ * (2*C1) + 1)/c0) * amplitude (d+1) R / R
      = ((((2*π)^d)⁻¹ * (2*C1) + 1)/c0) * (amplitude (d+1) R / R) by ring, hamp]
  have hfin : ((((2*π)^d)⁻¹ * (2*C1) + 1)/c0) * (c0 * W)
      = ((2*π)^d)⁻¹ * (2 * (C1 * W) + (2*π)^d * W) := by
    field_simp
  rw [hfin]
  refine le_trans hnormX (mul_le_mul_of_nonneg_left ?_ (by positivity))
  linarith

/-- **Gate 1.**  The canonical leading additive asymptotics of `f m` on the negative axis,
for every fixed `m ≥ 2`:
`‖f m (-R^m) - A m R cos (Ψ m R)‖ ≤ C A m R / R` for all `R ≥ R0`. -/
theorem leading_additive :
    ∀ m : ℕ, 2 ≤ m →
      ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
        ∀ R : ℝ, R0 ≤ R →
          ‖f m (-((R:ℂ)^m)) - ((amplitude m R * Real.cos (phase m R) : ℝ) : ℂ)‖
            ≤ C * amplitude m R / R := by
  intro m hm
  rcases eq_or_lt_of_le hm with h2 | h3
  · rw [← h2]; exact leading_additive_two
  · obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, by omega⟩
    exact leading_additive_ge_three (by omega)

end Q776
