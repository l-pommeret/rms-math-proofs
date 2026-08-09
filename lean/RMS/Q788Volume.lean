/-
# Q788 — Stage 6a: periodic boxes and the rotation reduction

The events `{Dₙ ≥ α}` are invariant both under adding `2π` to any single angle and under a
common rotation of all the angles.  This module turns those two symmetries into a volume
identity: the measure of such an event inside one period box equals `2π` times the
`(n-1)`-dimensional volume of its slice at first angle `0`, computed inside one period box.
-/
import RMS.Q788UpperEdge

open Real MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Q788

/-! ## The lattice `(2πℤ)^m` and its fundamental boxes -/

/-- The lattice `(2πℤ)^m ⊆ ℝ^m` of translations leaving every angular event invariant. -/
noncomputable def angleLattice (m : ℕ) : AddSubgroup (Fin m → ℝ) :=
  AddSubgroup.pi Set.univ fun _ : Fin m => AddSubgroup.zmultiples (2 * π)

/-- One period box `∏ᵢ [cᵢ, cᵢ + 2π)`. -/
def angleBox {m : ℕ} (c : Fin m → ℝ) : Set (Fin m → ℝ) :=
  Set.univ.pi fun i => Set.Ico (c i) (c i + 2 * π)

theorem measurableSet_angleBox {m : ℕ} (c : Fin m → ℝ) : MeasurableSet (angleBox c) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem angleLattice_apply_mem {m : ℕ} (g : angleLattice m) (i : Fin m) :
    ∃ k : ℤ, (g : Fin m → ℝ) i = k * (2 * π) := by
  obtain ⟨k, hk⟩ := g.2 i (Set.mem_univ i)
  exact ⟨k, by rw [← hk]; push_cast [zsmul_eq_mul]; ring⟩

instance angleLattice_countable (m : ℕ) : Countable (angleLattice m) := by
  have hpi := Real.pi_pos
  refine Function.Injective.countable
    (f := fun g : angleLattice m => fun i => ⌊(g : Fin m → ℝ) i / (2 * π)⌋) ?_
  intro g g' hgg
  refine Subtype.ext (funext fun i => ?_)
  obtain ⟨k, hk⟩ := angleLattice_apply_mem g i
  obtain ⟨k', hk'⟩ := angleLattice_apply_mem g' i
  have h1 : ⌊(g : Fin m → ℝ) i / (2 * π)⌋ = k := by
    rw [hk, mul_div_assoc, div_self (by positivity : (2 * π) ≠ 0), mul_one, Int.floor_intCast]
  have h2 : ⌊(g' : Fin m → ℝ) i / (2 * π)⌋ = k' := by
    rw [hk', mul_div_assoc, div_self (by positivity : (2 * π) ≠ 0), mul_one, Int.floor_intCast]
  have hkk : k = k' := by
    have hc : ⌊(g : Fin m → ℝ) i / (2 * π)⌋ = ⌊(g' : Fin m → ℝ) i / (2 * π)⌋ := congrFun hgg i
    rw [h1, h2] at hc
    exact hc
  show (g : Fin m → ℝ) i = (g' : Fin m → ℝ) i
  rw [hk, hk', hkk]

/-- Every period box is a fundamental domain for the lattice `(2πℤ)^m`. -/
theorem isAddFundamentalDomain_angleBox {m : ℕ} (c : Fin m → ℝ) :
    IsAddFundamentalDomain (angleLattice m) (angleBox c) (volume : Measure (Fin m → ℝ)) := by
  have hpi := Real.pi_pos
  constructor
  · exact (measurableSet_angleBox c).nullMeasurableSet
  · filter_upwards with x
    set f : Fin m → ℝ := fun i => -(2 * π * ⌊(x i - c i) / (2 * π)⌋) with hf
    have hmem : f ∈ angleLattice m := by
      intro i _
      exact AddSubgroup.neg_mem _ ⟨⌊(x i - c i) / (2 * π)⌋, by push_cast; ring⟩
    refine ⟨⟨f, hmem⟩, ?_⟩
    intro i _
    have hfr : (x i - c i) - 2 * π * ⌊(x i - c i) / (2 * π)⌋
        = 2 * π * Int.fract ((x i - c i) / (2 * π)) := by
      rw [Int.fract]; field_simp
    have h0 := Int.fract_nonneg ((x i - c i) / (2 * π))
    have h1 := Int.fract_lt_one ((x i - c i) / (2 * π))
    have hvadd : ((⟨f, hmem⟩ : angleLattice m) +ᵥ x) i
        = -(2 * π * ⌊(x i - c i) / (2 * π)⌋) + x i := by
      simp [hf]
    rw [Set.mem_Ico, hvadd]
    constructor <;> nlinarith [hfr]
  · intro g g' hne
    refine Disjoint.aedisjoint ?_
    obtain ⟨i, hi⟩ : ∃ i, (g : Fin m → ℝ) i ≠ (g' : Fin m → ℝ) i := by
      by_contra hc
      push_neg at hc
      exact hne (Subtype.ext (funext hc))
    obtain ⟨k, hk⟩ := angleLattice_apply_mem g i
    obtain ⟨k', hk'⟩ := angleLattice_apply_mem g' i
    have hkk : (k : ℤ) ≠ k' := by
      intro h; apply hi; rw [hk, hk', h]
    have hgap : 2 * π ≤ |(g : Fin m → ℝ) i - (g' : Fin m → ℝ) i| := by
      rw [hk, hk', ← sub_mul, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * π)]
      have h1 : (1:ℝ) ≤ |((k : ℝ) - (k' : ℝ))| := by
        have hcast : ((k : ℝ) - (k' : ℝ)) = ((k - k' : ℤ) : ℝ) := by push_cast; ring
        rw [hcast, ← Int.cast_abs]
        exact_mod_cast Int.one_le_abs (sub_ne_zero.2 hkk)
      nlinarith
    rw [Set.disjoint_left]
    rintro y hy hy'
    simp only [Set.mem_vadd_set] at hy hy'
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, hb, hb2⟩ := hy'
    have ha' := ha i (Set.mem_univ i)
    have hb' := hb i (Set.mem_univ i)
    simp only [Set.mem_Ico] at ha' hb'
    have hcoord : (g : Fin m → ℝ) i + a i = (g' : Fin m → ℝ) i + b i := by
      have := congrFun hb2 i
      simpa using this.symm
    rcases abs_cases ((g : Fin m → ℝ) i - (g' : Fin m → ℝ) i) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      nlinarith [ha'.1, ha'.2, hb'.1, hb'.2]

/-- A set invariant under the lattice has the same volume in every period box. -/
theorem volume_inter_angleBox_eq {m : ℕ} {A : Set (Fin m → ℝ)} (hA : MeasurableSet A)
    (hinv : ∀ g : angleLattice m, (fun x => g +ᵥ x) ⁻¹' A = A) (c c' : Fin m → ℝ) :
    volume (A ∩ angleBox c) = volume (A ∩ angleBox c') :=
  (isAddFundamentalDomain_angleBox c).measure_set_eq (isAddFundamentalDomain_angleBox c') hA hinv


/-! ## Slices and the rotation reduction -/

theorem measurable_cons_const {n : ℕ} (a : ℝ) :
    Measurable (fun y : Fin n → ℝ => (Fin.cons a y : Fin (n + 1) → ℝ)) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j
    simpa using measurable_pi_apply j

theorem measurableSet_consSlice {n : ℕ} {A : Set (Fin (n + 1) → ℝ)} (hA : MeasurableSet A)
    (a : ℝ) : MeasurableSet {y : Fin n → ℝ | Fin.cons a y ∈ A} :=
  (measurable_cons_const a) hA

theorem cons_zero_mem_angleLattice {n : ℕ} (g : angleLattice n) :
    (Fin.cons 0 (g : Fin n → ℝ) : Fin (n + 1) → ℝ) ∈ angleLattice (n + 1) := by
  intro i _
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j
    simpa using g.2 j (Set.mem_univ j)

/-- The slice at first angle `0` of a lattice-invariant set is lattice invariant. -/
theorem consSlice_lattice_invariant {n : ℕ} {A : Set (Fin (n + 1) → ℝ)}
    (hlat : ∀ g : angleLattice (n + 1), (fun x => g +ᵥ x) ⁻¹' A = A) (g : angleLattice n) :
    (fun y => g +ᵥ y) ⁻¹' {y : Fin n → ℝ | Fin.cons 0 y ∈ A}
      = {y : Fin n → ℝ | Fin.cons 0 y ∈ A} := by
  ext y
  have hcons : (Fin.cons 0 ((g : Fin n → ℝ) + y) : Fin (n + 1) → ℝ)
      = (⟨Fin.cons 0 (g : Fin n → ℝ), cons_zero_mem_angleLattice g⟩ :
          angleLattice (n + 1)) +ᵥ (Fin.cons 0 y : Fin (n + 1) → ℝ) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j; simp
  have hg : ((g +ᵥ y : Fin n → ℝ)) = (g : Fin n → ℝ) + y := rfl
  simp only [Set.mem_preimage, Set.mem_setOf_eq, hg, hcons]
  exact Set.ext_iff.1 (hlat ⟨Fin.cons 0 (g : Fin n → ℝ), cons_zero_mem_angleLattice g⟩)
    (Fin.cons 0 y)

/-- Every slice of a rotation- and lattice-invariant set has the same volume in a period box. -/
theorem volume_consSlice_eq {n : ℕ} {A : Set (Fin (n + 1) → ℝ)} (hA : MeasurableSet A)
    (hlat : ∀ g : angleLattice (n + 1), (fun x => g +ᵥ x) ⁻¹' A = A)
    (hdiag : ∀ (a : ℝ) (x : Fin (n + 1) → ℝ), ((fun i => x i + a) ∈ A ↔ x ∈ A))
    (a : ℝ) (c' : Fin n → ℝ) :
    volume ({y : Fin n → ℝ | Fin.cons a y ∈ A} ∩ angleBox c')
      = volume ({y : Fin n → ℝ | Fin.cons 0 y ∈ A} ∩ angleBox c') := by
  have hpi := Real.pi_pos
  have hkey : {y : Fin n → ℝ | Fin.cons a y ∈ A} ∩ angleBox c'
      = (fun y : Fin n → ℝ => (fun _ : Fin n => -a) + y) ⁻¹'
          ({y : Fin n → ℝ | Fin.cons 0 y ∈ A} ∩ angleBox (fun i => c' i - a)) := by
    ext y
    have hshift : (Fin.cons a y : Fin (n + 1) → ℝ)
        = fun i => (Fin.cons 0 ((fun _ : Fin n => -a) + y) : Fin (n + 1) → ℝ) i + a := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro j; simp
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, angleBox, Set.mem_pi,
      Set.mem_univ, forall_const, Set.mem_Ico, Pi.add_apply]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, fun i => ⟨by linarith [(h2 i).1], by linarith [(h2 i).2]⟩⟩
      rw [hshift] at h1
      exact (hdiag a _).1 h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, fun i => ⟨by linarith [(h2 i).1], by linarith [(h2 i).2]⟩⟩
      rw [hshift]
      exact (hdiag a _).2 h1
  rw [hkey, measure_preimage_add]
  exact volume_inter_angleBox_eq (measurableSet_consSlice hA 0)
    (consSlice_lattice_invariant hlat) _ _

end Q788
