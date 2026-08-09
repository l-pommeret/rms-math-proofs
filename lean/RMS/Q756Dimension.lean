/-
Q756 — the space of flat solutions is infinite dimensional.

Placing the seeds of the construction in `N` pairwise disjoint windows of the fundamental annulus
produces `N` solutions which are linearly independent (each one is nonzero at the centre of its
own window and vanishes at the centres of the others).
-/
import RMS.Q756Existence

namespace Q756

open Set Filter Topology Polynomial

/-- **Infinite dimensionality (§7).** For every `N` there are `N` linearly independent
`C^∞` solutions, all of them flat at the origin. -/
theorem exists_linearIndependent_flat_sols (beta lam : ℝ) (hlam : 1 < |lam|) (N : ℕ) :
    ∃ g : Fin N → (ℝ → ℝ), (∀ i, IsSol beta lam (g i)) ∧
      (∀ i, ∀ n : ℕ, iteratedDeriv n (g i) 0 = 0) ∧
      (∀ i, ∀ n : ℕ, ContDiff ℝ n (g i)) ∧ LinearIndependent ℝ g := by
  obtain ⟨del, hdel, hdel0⟩ : ∃ del : ℝ, del = (|lam| - 1) / (N + 1) ∧ 0 < del := by
    refine ⟨(|lam| - 1) / (N + 1), rfl, div_pos (by linarith) (by positivity)⟩
  have hlamN : 1 + (N + 1 : ℝ) * del = |lam| := by
    rw [hdel]
    field_simp
    ring
  set u : ℕ → ℝ := fun k => 1 + k * del + del / 3 with hu
  set v : ℕ → ℝ := fun k => 1 + k * del + 2 * del / 3 with hv
  have hwin : ∀ k : Fin N, 1 < u k ∧ u k < v k ∧ v k < |lam| := by
    intro k
    have hk : ((k : ℕ) : ℝ) ≤ (N : ℝ) - 1 := by
      have : ((k : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt k.isLt
      linarith
    have hkpos : (0:ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
    refine ⟨by simp only [hu]; nlinarith, by simp only [hu, hv]; linarith, ?_⟩
    simp only [hv]
    nlinarith
  have H : ∀ k : Fin N, ∃ (g : ℝ → ℝ) (p : ℝ), IsSol beta lam g ∧
      (∀ n : ℕ, iteratedDeriv n g 0 = 0) ∧ (∀ n : ℕ, ContDiff ℝ n g) ∧ u k < p ∧ p < v k ∧
      g p ≠ 0 ∧ ∀ x : ℝ, 1 ≤ x → x ≤ |lam| → (x ≤ u k ∨ v k ≤ x) → g x = 0 := by
    intro k
    obtain ⟨h1, h2, h3⟩ := hwin k
    exact exists_flat_sol_in_window hlam h1 h2 h3
  choose g p hsol hflat hsmooth hup hpv hgp hout using H
  refine ⟨g, hsol, hflat, hsmooth, ?_⟩
  -- the windows are pairwise disjoint, hence `g i` vanishes at `p j` for `i ≠ j`
  have hzero : ∀ i j : Fin N, i ≠ j → g i (p j) = 0 := by
    intro i j hij
    obtain ⟨hj1, hj2, hj3⟩ := hwin j
    refine hout i (p j) (by linarith [hup j]) (by linarith [hpv j]) ?_
    rcases lt_or_gt_of_ne (fun h : (i : ℕ) = (j : ℕ) => hij (Fin.ext h)) with h | h
    · -- `i < j`: the window of `i` lies to the left
      right
      have : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
      have hvi : v i ≤ u j := by
        simp only [hu, hv]
        nlinarith
      linarith [hup j]
    · -- `j < i`: the window of `i` lies to the right
      left
      have : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
      have hvj : v j ≤ u i := by
        simp only [hu, hv]
        nlinarith
      linarith [hpv j]
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hev : ∑ i : Fin N, c i * g i (p j) = 0 := by
    have := congrFun hc (p j)
    simpa using this
  have hsingle : ∑ i : Fin N, c i * g i (p j) = c j * g j (p j) := by
    refine Finset.sum_eq_single j (fun i _ hij => ?_) (fun h => absurd (Finset.mem_univ j) h)
    rw [hzero i j hij, mul_zero]
  rw [hsingle] at hev
  rcases mul_eq_zero.1 hev with h | h
  · exact h
  · exact absurd h (hgp j)


/-- The solution space `F(beta, lam)` as a submodule of `ℝ → ℝ`. -/
def solSpace (beta lam : ℝ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {g | IsSol beta lam g}
  add_mem' := by
    intro a b ha hb t
    have h := (ha t).add (hb t)
    have heq : a (lam * t) - beta * a t + (b (lam * t) - beta * b t)
        = (a + b) (lam * t) - beta * (a + b) t := by
      simp only [Pi.add_apply]; ring
    rw [heq] at h
    exact h
  zero_mem' := by
    intro t
    simpa using hasDerivAt_const t (0:ℝ)
  smul_mem' := by
    intro c a ha t
    have h := (ha t).const_mul c
    have heq : c * (a (lam * t) - beta * a t) = (c • a) (lam * t) - beta * (c • a) t := by
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [heq] at h
    exact h

theorem mem_solSpace {beta lam : ℝ} {g : ℝ → ℝ} : g ∈ solSpace beta lam ↔ IsSol beta lam g :=
  Iff.rfl

/-- **The solution space is infinite dimensional** whenever `1 < |lam|`. -/
theorem solSpace_not_finiteDimensional (beta lam : ℝ) (hlam : 1 < |lam|) :
    ¬ FiniteDimensional ℝ (solSpace beta lam) := by
  intro hfin
  obtain ⟨g, hsol, _, _, hli⟩ :=
    exists_linearIndependent_flat_sols beta lam hlam (Module.finrank ℝ (solSpace beta lam) + 1)
  have hlif : LinearIndependent ℝ (fun i => (⟨g i, hsol i⟩ : solSpace beta lam)) :=
    LinearIndependent.of_comp (solSpace beta lam).subtype hli
  have hcard := hlif.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  omega

end Q756
