/-
Q756 — linearity of the inward correction `Vin` in the seed `phi`.

This file collects the (elementary but needed) fact that the Volterra operator `Vop`, its
Picard iterates `Dseq` and hence the inward correction `Vin` depend linearly on the data.
-/
import RMS.Q756Inner

namespace Q756

open Set Filter MeasureTheory intervalIntegral

section VopLinear

variable {beta lam : ℝ} {psi1 psi2 u1 u2 : ℝ → ℝ}

theorem uIcc_outer_ne_zero {t : ℝ} (ht : t ≠ 0) : ∀ s ∈ Set.uIcc (outer t) t, s ≠ 0 := by
  intro s hs h
  have h1 := (mem_uIcc_outer t s hs).1
  rw [h, abs_zero] at h1
  exact ht (abs_eq_zero.1 (le_antisymm h1 (abs_nonneg t)))

theorem Vop_add (hlam : 1 < |lam|)
    (hu1 : ∀ x ≠ (0:ℝ), ContinuousAt u1 x) (hu2 : ∀ x ≠ (0:ℝ), ContinuousAt u2 x)
    (hp1 : ∀ x ≠ (0:ℝ), ContinuousAt psi1 x) (hp2 : ∀ x ≠ (0:ℝ), ContinuousAt psi2 x)
    (t : ℝ) :
    Vop beta lam (fun x => psi1 x + psi2 x) (fun x => u1 x + u2 x) t
      = Vop beta lam psi1 u1 t + Vop beta lam psi2 u2 t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [Vop_at_zero]
  · have hne := uIcc_outer_ne_zero ht
    have h1 := Vop_integrable (beta := beta) hlam hu1 hp1 t hne
    have h2 := Vop_integrable (beta := beta) hlam hu2 hp2 t hne
    rw [Vop, Vop, Vop, ← intervalIntegral.integral_add h1 h2]
    exact intervalIntegral.integral_congr (fun s _ => by ring)

theorem Vop_smul (beta lam : ℝ) (c : ℝ) (psi u : ℝ → ℝ) (t : ℝ) :
    Vop beta lam (fun x => c * psi x) (fun x => c * u x) t = c * Vop beta lam psi u t := by
  rw [Vop, Vop, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr (fun s _ => by ring)

end VopLinear

section DseqLinear

variable {beta lam e : ℝ} {phi1 phi2 : ℝ → ℝ}

theorem Dseq_add (hlam : 1 < |lam|) (he : 0 < e)
    (hc1 : Continuous phi1) (hs1 : ∀ x, |lam| - e < |x| → phi1 x = 0)
    (hc2 : Continuous phi2) (hs2 : ∀ x, |lam| - e < |x| → phi2 x = 0) (n : ℕ) (t : ℝ) :
    Dseq beta lam (fun x => phi1 x + phi2 x) n t
      = Dseq beta lam phi1 n t + Dseq beta lam phi2 n t := by
  induction n generalizing t with
  | zero =>
      have := Vop_add (beta := beta) (u1 := 0) (u2 := 0) (psi1 := phi1) (psi2 := phi2) hlam
        (fun y _ => continuousAt_const) (fun y _ => continuousAt_const)
        (fun y _ => hc1.continuousAt) (fun y _ => hc2.continuousAt) t
      simpa [Dseq] using this
  | succ n ih =>
      have hfun : Dseq beta lam (fun x => phi1 x + phi2 x) n
          = fun x => Dseq beta lam phi1 n x + Dseq beta lam phi2 n x := funext ih
      have := Vop_add (beta := beta) (u1 := Dseq beta lam phi1 n) (u2 := Dseq beta lam phi2 n)
        (psi1 := 0) (psi2 := 0) hlam
        (Dseq_continuousAt hlam he hc1 hs1 n) (Dseq_continuousAt hlam he hc2 hs2 n)
        (fun y _ => continuousAt_const) (fun y _ => continuousAt_const) t
      simp only [Dseq, hfun]
      simpa using this

theorem Dseq_smul (beta lam : ℝ) (phi : ℝ → ℝ) (c : ℝ) (n : ℕ) (t : ℝ) :
    Dseq beta lam (fun x => c * phi x) n t = c * Dseq beta lam phi n t := by
  induction n generalizing t with
  | zero =>
      have := Vop_smul beta lam c phi 0 t
      simpa [Dseq] using this
  | succ n ih =>
      have hfun : Dseq beta lam (fun x => c * phi x) n
          = fun x => c * Dseq beta lam phi n x := funext ih
      have := Vop_smul beta lam c 0 (Dseq beta lam phi n) t
      simp only [Dseq, hfun]
      simpa using this

end DseqLinear

section VinLinear

variable {beta lam e : ℝ} {phi1 phi2 : ℝ → ℝ}

theorem Vin_add (hlam : 1 < |lam|) (he : 0 < e)
    (hc1 : Continuous phi1) (hs1 : ∀ x, |lam| - e < |x| → phi1 x = 0)
    (hc2 : Continuous phi2) (hs2 : ∀ x, |lam| - e < |x| → phi2 x = 0) (t : ℝ) :
    Vin beta lam (fun x => phi1 x + phi2 x) t
      = Vin beta lam phi1 t + Vin beta lam phi2 t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [Vin_at_zero]
  · obtain ⟨N, hN⟩ := exists_rad_le (e := e) hlam (abs_pos.2 ht)
    have hs12 : ∀ x, |lam| - e < |x| → phi1 x + phi2 x = 0 := by
      intro x hx; simp [hs1 x hx, hs2 x hx]
    rw [Vin_eq_sum (beta := beta) hlam he hs12 hN, Vin_eq_sum (beta := beta) hlam he hs1 hN,
      Vin_eq_sum (beta := beta) hlam he hs2 hN, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun n _ => Dseq_add hlam he hc1 hs1 hc2 hs2 n t)

theorem Vin_smul (beta lam : ℝ) (phi : ℝ → ℝ) (c : ℝ) (t : ℝ) :
    Vin beta lam (fun x => c * phi x) t = c * Vin beta lam phi t := by
  rw [Vin, Vin, ← tsum_mul_left]
  exact tsum_congr (fun n => Dseq_smul beta lam phi c n t)

end VinLinear

end Q756
