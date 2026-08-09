/-
# Q788 — the rotation slice formula for the probabilities

The events `{Dₙ ≥ α}` are invariant under adding `2π` to any single angle and under a common
rotation of all the angles.  Combining the fundamental-domain results of
`RequestProject.Q788Volume` with Fubini in the first coordinate, we obtain

  `ℙ(Dₙ ≥ α) = vol_{n-1} ({y : Dₙ(0, y) ≥ α} ∩ [-π, π)^{n-1}) / (2π)^{n-1}`,

which reduces every probability computation to an `(n-1)`-dimensional volume in relative
coordinates.
-/
import RMS.Q788Ellipsoid

set_option maxHeartbeats 1000000

open MeasureTheory Real Set
open scoped ENNReal

namespace Q788

/-! ## Invariance of the chord maximum under the angle lattice -/

theorem chordProd_add_two_pi_int {n : ℕ} (θ : Fin n → ℝ) (k : Fin n → ℤ) (t : ℝ) :
    chordProd (fun j => θ j + 2 * π * k j) t = chordProd θ t := by
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 2
  have : ((θ j + 2 * π * (k j : ℝ) : ℝ) : ℂ) * Complex.I
      = ((θ j : ℝ) : ℂ) * Complex.I + (k j : ℂ) * (2 * π * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem chordMax_add_two_pi_int {n : ℕ} (θ : Fin n → ℝ) (k : Fin n → ℤ) :
    chordMax (fun j => θ j + 2 * π * k j) = chordMax θ := by
  rw [chordMax_eq_iSup, chordMax_eq_iSup]
  exact iSup_congr fun t => chordProd_add_two_pi_int θ k t

/-- The event `{Dₙ ≥ α}` is invariant under the lattice `(2πℤ)^n`. -/
theorem chordMax_ge_lattice_invariant {n : ℕ} (α : ℝ) (g : angleLattice n) :
    (fun x => g +ᵥ x) ⁻¹' {θ : Fin n → ℝ | α ≤ chordMax θ} = {θ : Fin n → ℝ | α ≤ chordMax θ} := by
  choose k hk using fun i => angleLattice_apply_mem g i
  ext x
  have hshift : ((g : Fin n → ℝ) + x) = fun j => x j + 2 * π * (k j : ℝ) := by
    funext j
    rw [Pi.add_apply, hk j]
    ring
  have : ((g +ᵥ x : Fin n → ℝ)) = (g : Fin n → ℝ) + x := rfl
  simp only [Set.mem_preimage, Set.mem_setOf_eq, this, hshift, chordMax_add_two_pi_int]

/-- The event `{Dₙ ≥ α}` is invariant under a common rotation. -/
theorem chordMax_ge_rotation_invariant {n : ℕ} (α : ℝ) (a : ℝ) (x : Fin n → ℝ) :
    ((fun i => x i + a) ∈ {θ : Fin n → ℝ | α ≤ chordMax θ}) ↔ x ∈ {θ : Fin n → ℝ | α ≤ chordMax θ} := by
  simp only [Set.mem_setOf_eq, chordMax_add_const]

/-! ## Fubini in the first coordinate -/

/-- **The slice formula.**  For a measurable, lattice- and rotation-invariant event, the
volume inside one period box is `2π` times the volume of the slice at first angle `0`. -/
theorem volume_inter_angleBox_eq_slice {n : ℕ} {A : Set (Fin (n + 1) → ℝ)} (hA : MeasurableSet A)
    (hlat : ∀ g : angleLattice (n + 1), (fun x => g +ᵥ x) ⁻¹' A = A)
    (hdiag : ∀ (a : ℝ) (x : Fin (n + 1) → ℝ), ((fun i => x i + a) ∈ A ↔ x ∈ A))
    (c0 : ℝ) (c' : Fin n → ℝ) :
    volume (A ∩ angleBox (Fin.cons c0 c'))
      = ENNReal.ofReal (2 * π)
        * volume ({y : Fin n → ℝ | Fin.cons 0 y ∈ A} ∩ angleBox c') := by
  have hpi := Real.pi_pos
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with he
  have hmp : MeasurePreserving e (volume : Measure (Fin (n + 1) → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    have := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ)) 0
    simpa [he, Measure.volume_eq_prod, volume_pi] using this
  set T : Set (ℝ × (Fin n → ℝ)) :=
    {p : ℝ × (Fin n → ℝ) | Fin.cons p.1 p.2 ∈ A ∩ angleBox (Fin.cons c0 c')} with hT
  have hTmeas : MeasurableSet T := by
    have hmc : Measurable fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ) := by
      refine measurable_pi_lambda _ fun i => ?_
      refine Fin.cases ?_ ?_ i
      · simpa using measurable_fst
      · intro j; simpa using (measurable_pi_apply j).comp measurable_snd
    exact hmc (hA.inter (measurableSet_angleBox _))
  have hpre : e ⁻¹' T = A ∩ angleBox (Fin.cons c0 c') := by
    ext x
    have : (Fin.cons (x 0) (fun j => x j.succ) : Fin (n + 1) → ℝ) = x := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro j; simp
    simp only [Set.mem_preimage, hT, Set.mem_setOf_eq, he]
    rw [show (e x : ℝ × (Fin n → ℝ)) = (x 0, fun j => x j.succ) from rfl]
    rw [this]
  have hstep : volume (A ∩ angleBox (Fin.cons c0 c'))
      = ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) T := by
    rw [← hpre, hmp.measure_preimage hTmeas.nullMeasurableSet]
  rw [hstep, Measure.prod_apply hTmeas]
  set V : ℝ≥0∞ := volume ({y : Fin n → ℝ | Fin.cons 0 y ∈ A} ∩ angleBox c') with hV
  have hslice : ∀ a : ℝ, volume (Prod.mk a ⁻¹' T)
      = Set.indicator (Set.Ico c0 (c0 + 2 * π)) (fun _ => V) a := by
    intro a
    have hset : Prod.mk a ⁻¹' T
        = if a ∈ Set.Ico c0 (c0 + 2 * π)
          then {y : Fin n → ℝ | Fin.cons a y ∈ A} ∩ angleBox c' else ∅ := by
      by_cases ha : a ∈ Set.Ico c0 (c0 + 2 * π)
      · rw [if_pos ha]
        ext y
        simp only [hT, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_inter_iff, angleBox,
          Set.mem_pi, Set.mem_univ, forall_const]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun i => ?_⟩
          have := h2 i.succ
          simpa using this
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun i => ?_⟩
          refine Fin.cases ?_ ?_ i
          · simpa using ha
          · intro j; simpa using h2 j
      · rw [if_neg ha]
        ext y
        simp only [hT, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_inter_iff, angleBox,
          Set.mem_pi, Set.mem_univ, forall_const, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, h2⟩
        exact ha (by simpa using h2 0)
    by_cases ha : a ∈ Set.Ico c0 (c0 + 2 * π)
    · rw [hset, if_pos ha, Set.indicator_of_mem ha, hV,
        volume_consSlice_eq hA hlat hdiag a c']
    · rw [hset, if_neg ha, Set.indicator_of_notMem ha, measure_empty]
  rw [lintegral_congr hslice, lintegral_indicator measurableSet_Ico, setLIntegral_const,
    Real.volume_Ico]
  simp [mul_comm]

/-! ## The probability as a relative-coordinate volume -/

theorem angleLawN_apply {n : ℕ} {E : Set (Fin n → ℝ)} (hE : MeasurableSet E) :
    angleLawN n E = ((ENNReal.ofReal (2 * π))⁻¹) ^ n * volume (E ∩ angleBox fun _ => 0) := by
  rw [angleLawN_eq, Measure.smul_apply, Measure.restrict_apply hE, smul_eq_mul]
  congr 2
  simp [angleBox]

/-- **The probability of a high chord maximum as a relative volume.** -/
theorem probGE_eq_slice_volume {n : ℕ} (α : ℝ) (c' : Fin n → ℝ) :
    probGE (n + 1) α
      = (volume ({y : Fin n → ℝ | α ≤ chordMax (Fin.cons 0 y)} ∩ angleBox c')).toReal
        / (2 * π) ^ n := by
  have hpi := Real.pi_pos
  set A : Set (Fin (n + 1) → ℝ) := {θ : Fin (n + 1) → ℝ | α ≤ chordMax θ} with hAdef
  have hA : MeasurableSet A := measurableSet_chordMax_ge α
  have hlat := chordMax_ge_lattice_invariant (n := n + 1) α
  have hvol := volume_inter_angleBox_eq_slice hA hlat
    (fun a x => chordMax_ge_rotation_invariant α a x) 0 (fun _ : Fin n => (0 : ℝ))
  have hindep : volume ({y : Fin n → ℝ | Fin.cons 0 y ∈ A} ∩ angleBox (fun _ : Fin n => (0 : ℝ)))
      = volume ({y : Fin n → ℝ | Fin.cons 0 y ∈ A} ∩ angleBox c') :=
    volume_inter_angleBox_eq (measurableSet_consSlice hA 0)
      (consSlice_lattice_invariant hlat) _ _
  rw [hindep] at hvol
  have hslice : {y : Fin n → ℝ | Fin.cons 0 y ∈ A}
      = {y : Fin n → ℝ | α ≤ chordMax (Fin.cons 0 y)} := rfl
  rw [hslice] at hvol
  set V : ℝ≥0∞ := volume ({y : Fin n → ℝ | α ≤ chordMax (Fin.cons 0 y)} ∩ angleBox c') with hV
  have hbase : angleLawN (n + 1) A
      = ((ENNReal.ofReal (2 * π))⁻¹) ^ (n + 1) * (ENNReal.ofReal (2 * π) * V) := by
    rw [angleLawN_apply hA]
    congr 1
    rw [show ((fun _ : Fin (n + 1) => (0 : ℝ))) = Fin.cons 0 (fun _ : Fin n => (0 : ℝ)) by
      funext i; refine Fin.cases ?_ ?_ i <;> simp]
    exact hvol
  have hne : ENNReal.ofReal (2 * π) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hnet : ENNReal.ofReal (2 * π) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsimp : ((ENNReal.ofReal (2 * π))⁻¹) ^ (n + 1) * (ENNReal.ofReal (2 * π) * V)
      = ((ENNReal.ofReal (2 * π))⁻¹) ^ n * V := by
    rw [pow_succ, mul_assoc,
      ← mul_assoc ((ENNReal.ofReal (2 * π))⁻¹) (ENNReal.ofReal (2 * π)) V,
      ENNReal.inv_mul_cancel hne hnet, one_mul]
  rw [probGE, ← hAdef, hbase, hsimp, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity)]
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  rw [inv_pow]

end Q788
