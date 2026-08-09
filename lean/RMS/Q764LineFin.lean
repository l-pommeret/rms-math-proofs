/-
# Q764 — Stage 3c.5: the ordered-line algorithm for an indexed family `x : Fin n → ℝ`

The exact algorithm of `RequestProject.Q764LineAlg` is stated for a strictly increasing
`x : ℕ → ℝ`.  This module repackages it for the more usual input format
`x : Fin n → ℝ` with `StrictMono x`, with centres a `Finset (Fin n)` and the objective

`lineCovRad x C = covRad' (image x univ) (image x C)`,

i.e. the covering radius of the actual point set `{x 0, …, x (n-1)} : Finset ℝ`.
-/
import RMS.Q764LineAlg

open Finset

namespace Q764

namespace Line

/-- Extension of a finite increasing family to a strictly increasing sequence on `ℕ`
(the values beyond the input are irrelevant to the algorithm; they only make the
hypotheses of the `ℕ`-indexed development available). -/
noncomputable def extendLine {n : ℕ} (x : Fin n → ℝ) : ℕ → ℝ := fun i =>
  if h : i < n then x ⟨i, h⟩
  else (if hn : 0 < n then x ⟨n - 1, by omega⟩ else 0) + ((i - n : ℕ) + 1 : ℕ)

lemma extendLine_of_lt {n : ℕ} (x : Fin n → ℝ) {i : ℕ} (h : i < n) :
    extendLine x i = x ⟨i, h⟩ := by
  simp [extendLine, h]

lemma extendLine_strictMono {n : ℕ} (x : Fin n → ℝ) (hx : StrictMono x) :
    StrictMono (extendLine x) := by
  intro i j hij
  by_cases hjn : j < n
  · have hin : i < n := by omega
    rw [extendLine_of_lt x hin, extendLine_of_lt x hjn]
    exact hx (by simpa [Fin.lt_def] using hij)
  · have hn : 0 < n ∨ n = 0 := by omega
    have hjval : extendLine x j
        = (if hn : 0 < n then x ⟨n - 1, by omega⟩ else 0) + ((j - n : ℕ) + 1 : ℕ) := by
      simp [extendLine, hjn]
    by_cases hin : i < n
    · have hnpos : 0 < n := by omega
      rw [extendLine_of_lt x hin, hjval]
      simp only [hnpos, dif_pos]
      have h1 : x ⟨i, hin⟩ ≤ x ⟨n - 1, by omega⟩ := by
        rcases eq_or_lt_of_le (show i ≤ n - 1 by omega) with h | h
        · have : (⟨i, hin⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
            apply Fin.ext; simpa using h
          rw [this]
        · exact le_of_lt (hx (by simpa [Fin.lt_def] using h))
      have h2 : (0 : ℝ) < ((j - n : ℕ) + 1 : ℕ) := by positivity
      linarith
    · rw [hjval]
      have hival : extendLine x i
          = (if hn : 0 < n then x ⟨n - 1, by omega⟩ else 0) + ((i - n : ℕ) + 1 : ℕ) := by
        simp [extendLine, hin]
      rw [hival]
      have hlt : ((i - n : ℕ) + 1 : ℕ) < ((j - n : ℕ) + 1 : ℕ) := by omega
      have hcast : ((((i - n : ℕ) + 1 : ℕ) : ℝ)) < ((((j - n : ℕ) + 1 : ℕ) : ℝ)) := by
        exact_mod_cast hlt
      linarith

/-- The covering radius of a set of indices, as a covering radius of the actual point set
of the real line. -/
noncomputable def lineCovRad {n : ℕ} (x : Fin n → ℝ) (C : Finset (Fin n)) : ℝ :=
  covRad' (univ.image x) (C.image x)

/-- The set of centres returned by the algorithm, as a set of indices. -/
noncomputable def lineKCenter {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : Finset (Fin n) :=
  univ.filter fun i => (i : ℕ) ∈ (lineKCenterRun (extendLine x) n k).value

lemma image_val_lineKCenter {n : ℕ} (x : Fin n → ℝ) (k : ℕ)
    (hsub : (lineKCenterRun (extendLine x) n k).value ⊆ range n) :
    (lineKCenter x k).image Fin.val = (lineKCenterRun (extendLine x) n k).value := by
  ext m
  simp only [lineKCenter, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro hm
    exact ⟨⟨m, mem_range.1 (hsub hm)⟩, hm, rfl⟩

lemma card_lineKCenter {n : ℕ} (x : Fin n → ℝ) (k : ℕ)
    (hsub : (lineKCenterRun (extendLine x) n k).value ⊆ range n) :
    (lineKCenter x k).card = (lineKCenterRun (extendLine x) n k).value.card := by
  rw [← image_val_lineKCenter x k hsub]
  exact (Finset.card_image_of_injective _ Fin.val_injective).symm

lemma image_extendLine_range {n : ℕ} (x : Fin n → ℝ) :
    (range n).image (extendLine x) = univ.image x := by
  ext y
  simp only [Finset.mem_image, mem_range, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, (extendLine_of_lt x hm).symm ▸ rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(i : ℕ), i.isLt, extendLine_of_lt x i.isLt⟩

lemma image_of_subset_range {n : ℕ} (x : Fin n → ℝ) (F : Finset (Fin n)) :
    F.image x = (F.image Fin.val).image (extendLine x) := by
  rw [Finset.image_image]
  refine Finset.image_congr ?_
  intro i _
  exact (extendLine_of_lt x i.isLt).symm

/-- **The exact ordered-line `k`-center algorithm, indexed form.**  For `n` points
`x 0 < x 1 < ⋯ < x (n-1)` of the real line and `1 ≤ k ≤ n`, the algorithm returns `k`
indices whose covering radius for the point set `{x 0, …, x (n-1)}` is minimal among all
`k`-element sets of indices. -/
theorem lineKCenter_fin_correct {n k : ℕ} (x : Fin n → ℝ) (hx : StrictMono x)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    (lineKCenter x k).card = k ∧
      ∀ F : Finset (Fin n), F.card = k →
        lineCovRad x (lineKCenter x k) ≤ lineCovRad x F := by
  have hxe : StrictMono (extendLine x) := extendLine_strictMono x hx
  obtain ⟨hsub, hcard, hopt⟩ := lineKCenter_correct hxe hk hkn
  have hxinj : Function.Injective x := hx.injective
  refine ⟨by rw [card_lineKCenter x k hsub, hcard], ?_⟩
  intro F hF
  have h1 : lineCovRad x (lineKCenter x k)
      = covRad' ((range n).image (extendLine x))
          (((lineKCenterRun (extendLine x) n k).value).image (extendLine x)) := by
    rw [lineCovRad, image_extendLine_range, image_of_subset_range x (lineKCenter x k),
      image_val_lineKCenter x k hsub]
  have h2 : lineCovRad x F
      = covRad' ((range n).image (extendLine x)) ((F.image Fin.val).image (extendLine x)) := by
    rw [lineCovRad, image_extendLine_range, image_of_subset_range x F]
  rw [h1, h2]
  refine hopt _ ?_ ?_
  · intro y hy
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hm
    exact Finset.mem_image.2 ⟨(i : ℕ), mem_range.2 i.isLt, rfl⟩
  · rw [Finset.card_image_of_injOn, Finset.card_image_of_injective _ Fin.val_injective, hF]
    intro a ha b hb hab
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hb
    rw [extendLine_of_lt x i.isLt, extendLine_of_lt x j.isLt] at hab
    have := hxinj hab
    simpa using congrArg Fin.val this

/-- **Running time, indexed form**: `O(n^2 + k*n)` unit-cost operations. -/
theorem lineKCenter_fin_work_le {n k : ℕ} (x : Fin n → ℝ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (lineKCenterRun (extendLine x) n k).ops.work ≤ 100 * (n * n + k * n) :=
  lineKCenter_work_le (extendLine x) hk hkn

end Line

end Q764
