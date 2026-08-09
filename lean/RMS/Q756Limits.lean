/-
Q756 — one-sided limits of the inward correction at the origin.

The inward correction `Vin` is bounded and has a bounded derivative away from `0`, hence it is
Lipschitz on each of the two half lines and therefore has one-sided limits `Lpos`, `Lneg` at the
origin.  Both are linear functionals of the seed.
-/
import RMS.Q756Linear

namespace Q756

open Set Filter Topology

/-- A *seed*: a smooth bump supported in the open annulus `1 + e < |t| < |lam| - e`,
with bounded values. -/
structure IsSeed (lam e : ℝ) (phi : ℝ → ℝ) : Prop where
  smooth : ∀ m : ℕ, ContDiff ℝ m phi
  vanish : ∀ t ∈ Uset lam e, phi t = 0
  bound : ∃ K : ℝ, ∀ x, |phi x| ≤ K

namespace IsSeed

variable {lam e : ℝ} {phi phi1 phi2 : ℝ → ℝ}

theorem cont (h : IsSeed lam e phi) : Continuous phi := (h.smooth 0).continuous

theorem supp (h : IsSeed lam e phi) : ∀ x, |lam| - e < |x| → phi x = 0 :=
  fun x hx => h.vanish x (Or.inr hx)

theorem add (h1 : IsSeed lam e phi1) (h2 : IsSeed lam e phi2) :
    IsSeed lam e (fun x => phi1 x + phi2 x) where
  smooth m := (h1.smooth m).add (h2.smooth m)
  vanish t ht := by simp [h1.vanish t ht, h2.vanish t ht]
  bound := by
    obtain ⟨K1, hK1⟩ := h1.bound
    obtain ⟨K2, hK2⟩ := h2.bound
    exact ⟨K1 + K2, fun x => (abs_add_le _ _).trans (add_le_add (hK1 x) (hK2 x))⟩

theorem const_mul (c : ℝ) (h : IsSeed lam e phi) : IsSeed lam e (fun x => c * phi x) where
  smooth m := contDiff_const.mul (h.smooth m)
  vanish t ht := by simp [h.vanish t ht]
  bound := by
    obtain ⟨K, hK⟩ := h.bound
    exact ⟨|c| * K, fun x => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK x) (abs_nonneg c)⟩

end IsSeed

section Lipschitz

variable {beta lam e : ℝ} {phi : ℝ → ℝ}

/-- Away from the origin `Vin` has a uniformly bounded derivative, so it is Lipschitz on any
convex set avoiding the origin. -/
theorem Vin_lipschitzOn (hlam : 1 < |lam|) (he : 0 < e) (hseed : IsSeed lam e phi)
    {s : Set ℝ} (hs : Convex ℝ s) (h0 : ∀ x ∈ s, x ≠ 0) :
    ∃ C : NNReal, LipschitzOnWith C (Vin beta lam phi) s := by
  obtain ⟨K, hK⟩ := hseed.bound
  set B : ℝ := ∑' n : ℕ, bnd beta lam e K n with hBdef
  have hB : ∀ x, |Vin beta lam phi x| ≤ B := Vin_bound hlam he hseed.cont hseed.supp hK
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0)
  set C : ℝ := B + |beta| * B + K with hCdef
  have hC0 : 0 ≤ C := by have := abs_nonneg beta; positivity
  refine ⟨C.toNNReal, ?_⟩
  refine hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun x => Vin beta lam phi (lam * x) + phi (lam * x) - beta * Vin beta lam phi x)
    (fun x hx => (Vin_hasDerivAt hlam he hseed.cont hseed.supp (h0 x hx)).hasDerivWithinAt)
    (fun x hx => ?_)
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hC0, Real.norm_eq_abs, abs_le]
  have h4 : |beta * Vin beta lam phi x| ≤ |beta| * B := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _)
  obtain ⟨a1, a2⟩ := abs_le.1 (hB (lam * x))
  obtain ⟨b1, b2⟩ := abs_le.1 (hK (lam * x))
  obtain ⟨c1, c2⟩ := abs_le.1 h4
  constructor <;> linarith

/-- A function Lipschitz on a set has a limit at `0` along the filter of that set. -/
theorem exists_tendsto_of_lipschitzOn {f : ℝ → ℝ} {s : Set ℝ} {C : NNReal}
    (hf : LipschitzOnWith C f s) : ∃ L : ℝ, Tendsto f (𝓝[s] 0) (𝓝 L) := by
  obtain ⟨F, hF, hEq⟩ := hf.extend_real
  refine ⟨F 0, ?_⟩
  have h1 : Tendsto F (𝓝[s] 0) (𝓝 (F 0)) :=
    hF.continuous.continuousAt.mono_left nhdsWithin_le_nhds
  exact h1.congr' (eventually_mem_nhdsWithin.mono fun x hx => (hEq hx).symm)

end Lipschitz

section Limits

variable {beta lam e : ℝ} {phi phi1 phi2 : ℝ → ℝ}

/-- The right-hand limit of the inward correction at the origin. -/
noncomputable def Lpos (beta lam : ℝ) (phi : ℝ → ℝ) : ℝ :=
  limUnder (𝓝[>] (0:ℝ)) (Vin beta lam phi)

/-- The left-hand limit of the inward correction at the origin. -/
noncomputable def Lneg (beta lam : ℝ) (phi : ℝ → ℝ) : ℝ :=
  limUnder (𝓝[<] (0:ℝ)) (Vin beta lam phi)

theorem Vin_tendsto_pos (hlam : 1 < |lam|) (he : 0 < e) (hseed : IsSeed lam e phi) :
    Tendsto (Vin beta lam phi) (𝓝[>] (0:ℝ)) (𝓝 (Lpos beta lam phi)) := by
  obtain ⟨C, hC⟩ := Vin_lipschitzOn (beta := beta) hlam he hseed (convex_Ioi (0:ℝ))
    (fun x hx => ne_of_gt hx)
  obtain ⟨L, hL⟩ := exists_tendsto_of_lipschitzOn hC
  rw [Lpos, hL.limUnder_eq]
  exact hL

theorem Vin_tendsto_neg (hlam : 1 < |lam|) (he : 0 < e) (hseed : IsSeed lam e phi) :
    Tendsto (Vin beta lam phi) (𝓝[<] (0:ℝ)) (𝓝 (Lneg beta lam phi)) := by
  obtain ⟨C, hC⟩ := Vin_lipschitzOn (beta := beta) hlam he hseed (convex_Iio (0:ℝ))
    (fun x hx => ne_of_lt hx)
  obtain ⟨L, hL⟩ := exists_tendsto_of_lipschitzOn hC
  rw [Lneg, hL.limUnder_eq]
  exact hL

theorem Lpos_add (hlam : 1 < |lam|) (he : 0 < e) (h1 : IsSeed lam e phi1)
    (h2 : IsSeed lam e phi2) :
    Lpos beta lam (fun x => phi1 x + phi2 x) = Lpos beta lam phi1 + Lpos beta lam phi2 := by
  refine tendsto_nhds_unique (Vin_tendsto_pos hlam he (h1.add h2)) ?_
  have := ((Vin_tendsto_pos (beta := beta) hlam he h1).add (Vin_tendsto_pos (beta := beta) hlam he h2))
  refine this.congr (fun x => ?_)
  exact (Vin_add hlam he h1.cont h1.supp h2.cont h2.supp x).symm

theorem Lneg_add (hlam : 1 < |lam|) (he : 0 < e) (h1 : IsSeed lam e phi1)
    (h2 : IsSeed lam e phi2) :
    Lneg beta lam (fun x => phi1 x + phi2 x) = Lneg beta lam phi1 + Lneg beta lam phi2 := by
  refine tendsto_nhds_unique (Vin_tendsto_neg hlam he (h1.add h2)) ?_
  have := ((Vin_tendsto_neg (beta := beta) hlam he h1).add (Vin_tendsto_neg (beta := beta) hlam he h2))
  refine this.congr (fun x => ?_)
  exact (Vin_add hlam he h1.cont h1.supp h2.cont h2.supp x).symm

theorem Lpos_const_mul (hlam : 1 < |lam|) (he : 0 < e) (h : IsSeed lam e phi) (c : ℝ) :
    Lpos beta lam (fun x => c * phi x) = c * Lpos beta lam phi := by
  refine tendsto_nhds_unique (Vin_tendsto_pos hlam he (h.const_mul c)) ?_
  have := (Vin_tendsto_pos (beta := beta) hlam he h).const_mul c
  exact this.congr (fun x => (Vin_smul beta lam phi c x).symm)

theorem Lneg_const_mul (hlam : 1 < |lam|) (he : 0 < e) (h : IsSeed lam e phi) (c : ℝ) :
    Lneg beta lam (fun x => c * phi x) = c * Lneg beta lam phi := by
  refine tendsto_nhds_unique (Vin_tendsto_neg hlam he (h.const_mul c)) ?_
  have := (Vin_tendsto_neg (beta := beta) hlam he h).const_mul c
  exact this.congr (fun x => (Vin_smul beta lam phi c x).symm)

end Limits

end Q756
