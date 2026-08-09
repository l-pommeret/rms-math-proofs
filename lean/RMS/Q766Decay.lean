import RMS.Q766Compact

/-!
# Q766, Stage 4 : decay of the optimal distortion

For any nondecreasing `q` with finite first moment on `(0,1)` (i.e. interval integrable), the
optimal distortion tends to `0`:

`Q766.quantError_tendsto_zero : Tendsto (fun n => quantError q (n+1)) atTop (𝓝 0)`.

The proof truncates the parameter interval near its two endpoints, where the integral of `|q|`
is small, and places an equally spaced grid of centres in the range of the truncated function.
No boundedness or compact support assumption is used.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral Set Filter Topology

namespace Q766

section Grid

/-- `n` equally spaced centres covering `[-R, R]` with mesh `R/n`. -/
noncomputable def gridCentres (R : ℝ) (n : ℕ) : Fin n → ℝ :=
  fun j => -R + (2 * (j : ℕ) + 1) * R / n

lemma exists_grid_close {R : ℝ} (hR : 0 < R) {n : ℕ} (hn : 0 < n) {y : ℝ} (hy : |y| ≤ R) :
    ∃ j : Fin n, |y - gridCentres R n j| ≤ R / n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hyR : -R ≤ y := neg_le_of_abs_le hy
  have hyR' : y ≤ R := le_of_abs_le hy
  set t : ℝ := (y + R) * n / (2 * R) with ht
  have ht0 : 0 ≤ t := by
    apply div_nonneg (by nlinarith) (by linarith)
  have htn : t ≤ n := by
    rw [ht, div_le_iff₀ (by linarith)]
    nlinarith
  set m := ⌊t⌋₊ with hm
  have hmle : (m : ℝ) ≤ t := Nat.floor_le ht0
  have hmlt : t < m + 1 := Nat.lt_floor_add_one t
  set j : ℕ := min m (n - 1) with hj
  have hjlt : j < n := by omega
  have hjt : (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 := by
    by_cases hcase : m ≤ n - 1
    · have : j = m := by omega
      rw [this]
      exact ⟨hmle, hmlt.le⟩
    · have hjn : j = n - 1 := by omega
      have hmn : n ≤ m := by omega
      have h1 : ((n : ℝ) - 1) ≤ t := by
        have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmn
        linarith
      rw [hjn]
      constructor
      · have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          have : (1:ℕ) ≤ n := hn
          push_cast [Nat.cast_sub this]
          ring
        rw [this]; exact h1
      · have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          have : (1:ℕ) ≤ n := hn
          push_cast [Nat.cast_sub this]
          ring
        rw [this]; linarith
  refine ⟨⟨j, hjlt⟩, ?_⟩
  have hyt : y = -R + 2 * t * R / n := by
    rw [ht]; field_simp; ring
  have hval : y - gridCentres R n ⟨j, hjlt⟩ = R / n * (2 * t - (2 * (j : ℝ) + 1)) := by
    simp only [gridCentres]
    rw [hyt]
    field_simp
    ring
  rw [hval, abs_mul, abs_of_pos (by positivity : (0:ℝ) < R / n)]
  have hbound : |2 * t - (2 * (j : ℝ) + 1)| ≤ 1 := by
    rw [abs_le]
    constructor <;> [linarith [hjt.2]; linarith [hjt.1]]
  nlinarith [abs_nonneg (2 * t - (2 * (j : ℝ) + 1)), div_pos hR hn']

lemma nearest_grid_le_of_abs_le {R : ℝ} (hR : 0 < R) {n : ℕ} (hn : 0 < n) {y : ℝ}
    (hy : |y| ≤ R) : nearest (gridCentres R n) y ≤ R / n := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨j, hj⟩ := exists_grid_close hR hn hy
  exact le_trans (nearest_le j) hj

lemma nearest_grid_le {R : ℝ} (hR : 0 < R) {n : ℕ} (hn : 0 < n) (y : ℝ) :
    nearest (gridCentres R n) y ≤ |y| + R / n := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  by_cases hy : |y| ≤ R
  · exact le_trans (nearest_grid_le_of_abs_le hR hn hy) (by linarith [abs_nonneg y])
  · push_neg at hy
    rcases lt_or_gt_of_ne (show y ≠ 0 by rintro rfl; simp at hy; linarith) with hneg | hpos
    · -- `y < -R`
      have hylt : y < -R := by
        rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩
        · linarith
        · linarith [hy, h]
      have h0 : (0:ℕ) < n := hn
      refine le_trans (nearest_le (⟨0, h0⟩ : Fin n)) ?_
      have hg : gridCentres R n ⟨0, h0⟩ = -R + R / n := by
        simp [gridCentres]
      rw [hg]
      have hya : |y| = -y := abs_of_neg (by linarith)
      rw [abs_of_nonpos (by
        have : (0:ℝ) < R / n := by positivity
        linarith)]
      rw [hya]
      have : (0:ℝ) < R / n := by positivity
      linarith
    · -- `y > R`
      have hygt : R < y := by
        rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩
        · linarith [hy, h]
        · linarith
      have hlast : (n - 1 : ℕ) < n := by omega
      refine le_trans (nearest_le (⟨n - 1, hlast⟩ : Fin n)) ?_
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        have h1 : (1:ℕ) ≤ n := hn
        push_cast [Nat.cast_sub h1]
        ring
      have hg : gridCentres R n ⟨n - 1, hlast⟩ = R - R / n := by
        simp only [gridCentres]
        rw [show (((⟨n - 1, hlast⟩ : Fin n) : ℕ) : ℝ) = (n : ℝ) - 1 from hcast]
        field_simp
        ring
      rw [hg, abs_of_nonneg (by
        have : (0:ℝ) < R / n := by positivity
        linarith)]
      have hya : |y| = y := abs_of_pos (by linarith)
      rw [hya]
      have : (0:ℝ) < R / n := by positivity
      linarith

end Grid

section Decay

variable {q : ℝ → ℝ}

/-- **Decay of the optimal distortion (§8.3).**  Only the finite first moment of `q` is used. -/
theorem quantError_tendsto_zero (hmono : MonotoneOn q (Set.Ioo (0:ℝ) 1))
    (hint : IntervalIntegrable q volume 0 1) :
    Tendsto (fun n : ℕ => quantError q (n + 1)) atTop (𝓝 0) := by
  have habs : IntervalIntegrable (fun u => |q u|) volume 0 1 := hint.abs
  have hG : ContinuousOn (H (fun u => |q u|)) (Set.Icc 0 1) := continuousOn_H habs
  have hG0 : H (fun u => |q u|) 0 = 0 := by simp [H]
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose the truncation parameter `δ`
  obtain ⟨δ₁, hδ₁, hb1⟩ := Metric.continuousWithinAt_iff.1
    (hG.continuousWithinAt (by norm_num : (0:ℝ) ∈ Set.Icc (0:ℝ) 1)) (ε / 4) (by linarith)
  obtain ⟨δ₂, hδ₂, hb2⟩ := Metric.continuousWithinAt_iff.1
    (hG.continuousWithinAt (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)) (ε / 4) (by linarith)
  set δ : ℝ := min (min (δ₁ / 2) (δ₂ / 2)) (1 / 4) with hδdef
  have hδpos : 0 < δ := by
    simp only [hδdef, lt_min_iff]
    exact ⟨⟨by linarith, by linarith⟩, by norm_num⟩
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  have hδ1' : δ ≤ δ₁ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ2' : δ ≤ δ₂ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδmem : δ ∈ Set.Icc (0:ℝ) 1 := ⟨hδpos.le, by linarith⟩
  have hδmem' : (1 - δ) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have htail1 : H (fun u => |q u|) δ < ε / 4 := by
    have := hb1 hδmem (by rw [Real.dist_eq, sub_zero, abs_of_pos hδpos]; linarith)
    rw [Real.dist_eq, hG0, sub_zero] at this
    exact lt_of_abs_lt this
  have htail2 : H (fun u => |q u|) 1 - H (fun u => |q u|) (1 - δ) < ε / 4 := by
    have := hb2 hδmem' (by
      rw [Real.dist_eq, show (1:ℝ) - δ - 1 = -δ by ring, abs_neg, abs_of_pos hδpos]
      linarith)
    rw [Real.dist_eq] at this
    have := abs_lt.1 this
    linarith [this.1]
  -- the truncation level
  have hδIoo : δ ∈ Set.Ioo (0:ℝ) 1 := ⟨hδpos, by linarith⟩
  have hδIoo' : (1 - δ) ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  set R : ℝ := max (max |q δ| |q (1 - δ)|) 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hRq1 : |q δ| ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hRq2 : |q (1 - δ)| ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  -- the bound
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * R / ε)
  refine ⟨N + 1, fun n hn => ?_⟩
  set m : ℕ := n + 1 with hmdef
  have hm0 : 0 < m := Nat.succ_pos n
  have hm' : (0:ℝ) < m := by exact_mod_cast hm0
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm0
  have hRn : R / m < ε / 2 := by
    have hNn : (N : ℝ) < m := by
      have : (N : ℕ) < m := by omega
      exact_mod_cast this
    have h1 : 2 * R / ε < m := lt_trans hN hNn
    rw [div_lt_iff₀ hm']
    rw [div_lt_iff₀ hε] at h1
    linarith
  set x : Fin m → ℝ := gridCentres R m with hx
  have hsplit := Phi_split (q := q) (a := δ) (b := 1 - δ) hint x hδpos.le (by linarith)
    (by linarith)
  have hIabs : ∀ {a b : ℝ}, 0 ≤ a → b ≤ 1 → a ≤ b →
      (∫ u in a..b, nearest x (q u)) ≤ (∫ u in a..b, |q u|) + R / m * (b - a) := by
    intro a b ha hb hab
    have h1 : (∫ u in a..b, nearest x (q u)) ≤ ∫ u in a..b, (|q u| + R / m) :=
      intervalIntegral.integral_mono_on hab (intInt_nearest hint ha hb hab)
        ((intInt_sub habs ha hb hab).add _root_.intervalIntegrable_const)
        (fun u _ => nearest_grid_le hRpos hm0 (q u))
    have h2 : (∫ u in a..b, (|q u| + R / m))
        = (∫ u in a..b, |q u|) + R / m * (b - a) := by
      rw [intervalIntegral.integral_add (intInt_sub habs ha hb hab)
        _root_.intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
      ring
    linarith [h1, h2.le, h2.ge]
  have hA : (∫ u in (0:ℝ)..δ, nearest x (q u)) ≤ (∫ u in (0:ℝ)..δ, |q u|) + R / m * δ := by
    have := hIabs (a := 0) (b := δ) le_rfl (by linarith) hδpos.le
    simpa using this
  have hC : (∫ u in (1 - δ)..1, nearest x (q u))
      ≤ (∫ u in (1 - δ)..1, |q u|) + R / m * δ := by
    have := hIabs (a := 1 - δ) (b := 1) (by linarith) le_rfl (by linarith)
    simpa [show (1:ℝ) - (1 - δ) = δ by ring] using this
  have hB : (∫ u in δ..(1 - δ), nearest x (q u)) ≤ R / m * (1 - 2 * δ) := by
    have hle : ∀ u ∈ Set.Icc δ (1 - δ), nearest x (q u) ≤ R / m := by
      intro u hu
      have huIoo : u ∈ Set.Ioo (0:ℝ) 1 := ⟨lt_of_lt_of_le hδpos hu.1,
        lt_of_le_of_lt hu.2 (by linarith)⟩
      have h1 : q δ ≤ q u := hmono hδIoo huIoo hu.1
      have h2 : q u ≤ q (1 - δ) := hmono huIoo hδIoo' hu.2
      have h3 : |q u| ≤ R := by
        rw [abs_le]
        constructor
        · have := neg_abs_le (q δ); linarith
        · have := le_abs_self (q (1 - δ)); linarith
      exact nearest_grid_le_of_abs_le hRpos hm0 h3
    have h := intervalIntegral.integral_mono_on (by linarith : δ ≤ 1 - δ)
      (intInt_nearest hint hδpos.le (by linarith) (by linarith))
      (_root_.intervalIntegrable_const (c := R / m)) hle
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    calc (∫ u in δ..(1 - δ), nearest x (q u)) ≤ (1 - δ - δ) * (R / m) := h
      _ = R / m * (1 - 2 * δ) := by ring
  have hHA : (∫ u in (0:ℝ)..δ, |q u|) = H (fun u => |q u|) δ := rfl
  have hHC : (∫ u in (1 - δ)..1, |q u|)
      = H (fun u => |q u|) 1 - H (fun u => |q u|) (1 - δ) :=
    H_sub habs (by linarith) le_rfl (by linarith)
  have hPhi : Phi q x < ε := by
    rw [hHA] at hA
    rw [hHC] at hC
    rw [hsplit]
    have hid : R / m * δ + R / m * (1 - 2 * δ) + R / m * δ = R / m := by ring
    linarith [hA, hB, hC, htail1, htail2, hRn, hid]
  have h0 : 0 ≤ quantError q m := quantError_nonneg hm0 hmono hint
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  exact lt_of_le_of_lt (quantError_le hm0 hmono hint x) hPhi

/-- **Stage-4 corollary.**  For a continuous nonconstant nondecreasing quantile, the optimal
distortions form a strictly decreasing sequence of positive numbers tending to `0`. -/
theorem quantError_pos_strictAnti_tendsto_zero (hmono : MonotoneOn q (Set.Ioo (0:ℝ) 1))
    (hcont : ContinuousOn q (Set.Ioo (0:ℝ) 1)) (hint : IntervalIntegrable q volume 0 1)
    (hqne : ∃ u ∈ Set.Ioo (0:ℝ) 1, ∃ v ∈ Set.Ioo (0:ℝ) 1, q u ≠ q v) :
    (∀ n : ℕ, 0 < n → 0 < quantError q n ∧ quantError q (n + 1) < quantError q n) ∧
      Tendsto (fun n : ℕ => quantError q (n + 1)) atTop (𝓝 0) :=
  ⟨fun n hn => ⟨quantError_pos hn hmono hcont hint hqne,
      quantError_succ_lt hn hmono hcont hint hqne⟩,
    quantError_tendsto_zero hmono hint⟩

end Decay

end Q766
