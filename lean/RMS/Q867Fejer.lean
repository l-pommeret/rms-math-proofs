import RMS.Q867Kernel
import RMS.Q867Linfty

/-!
# The interpolation operator built from Fejér kernels

With `q n = 2^(n+1)` we set `Phi n z = fejer (q n) (z / (8π) - 2^n)`, an entire function
whose restriction to `ℝ` is a finite combination of exponentials `e^{i λ x}` with
`|λ| < 1/4`, hence lies in `F`.  Summing, `Smap x = ∑' n, x n • Phi n` defines a bounded
operator `ℓ^∞(ℕ) → E` which maps `c₀` into `F`, and whose samples at the points `8π k`
recover the "dyadic" sequence `Sseq x`.

The summability of `∑ n, ‖Phi n z‖` uses that the "peaks" of the various `Phi n` sit at
*distinct* integers: the peak set of `Phi n` is `2^n + 2^(n+1) ℤ`, and these sets are
pairwise disjoint.  Comparing with a rearrangement of `∑ 1/j²` over `ℤ` gives a bound
independent of `z.re`.
-/

noncomputable section

open Filter Topology Complex BoundedContinuousFunction

namespace Q867

/-! ### Real and imaginary parts of the shifted variable -/

lemma two_pow_im (n : ℕ) : ((2 : ℂ) ^ n).im = 0 := by
  have h2 : (2 : ℂ) ^ n = ((2 ^ n : ℝ) : ℂ) := by push_cast; ring
  rw [h2]; exact Complex.ofReal_im _

lemma two_pow_re (n : ℕ) : ((2 : ℂ) ^ n).re = 2 ^ n := by
  have h2 : (2 : ℂ) ^ n = ((2 ^ n : ℝ) : ℂ) := by push_cast; ring
  rw [h2]; exact Complex.ofReal_re _

lemma shift_im (z : ℂ) (n : ℕ) : (z / (hstep : ℂ) - 2 ^ n).im = z.im / hstep := by
  have h : z / (hstep : ℂ) = ((hstep⁻¹ : ℝ) : ℂ) * z := by push_cast; field_simp
  rw [h]
  simp [two_pow_im]
  ring

lemma shift_re (z : ℂ) (n : ℕ) : (z / (hstep : ℂ) - 2 ^ n).re = z.re / hstep - 2 ^ n := by
  have h : z / (hstep : ℂ) = ((hstep⁻¹ : ℝ) : ℂ) * z := by push_cast; field_simp
  rw [h]
  simp [two_pow_re]
  ring

/-! ### The functions `Phi n` -/

/-- The dyadic period `2^(n+1)`. -/
def qq (n : ℕ) : ℕ := 2 ^ (n + 1)

lemma qq_pos (n : ℕ) : 0 < qq n := pow_pos (by norm_num) _

/-- The `n`-th building block: a Fejér kernel of period `2^(n+1)` in the sampling
variable, centred at the lattice points `k` with `2`-adic valuation `n`. -/
def Phi (n : ℕ) (z : ℂ) : ℂ := fejer (qq n) (z / hstep - 2 ^ n)

lemma exp_arg_Phi (z : ℂ) (n : ℕ) :
    2 * Real.pi * |(z / (hstep : ℂ) - 2 ^ n).im| = |z.im| / 4 := by
  rw [shift_im, abs_div, abs_of_pos hstep_pos, hstep]
  have := Real.pi_pos
  field_simp
  ring

lemma norm_Phi_le (n : ℕ) (z : ℂ) : ‖Phi n z‖ ≤ Real.exp (|z.im| / 4) := by
  have h := norm_fejer_le (qq_pos n) (z / hstep - 2 ^ n)
  rwa [exp_arg_Phi] at h

lemma norm_Phi_le_of_dist (n : ℕ) (z : ℂ) (d : ℝ) (hd : 0 < d)
    (hdist : ∀ k : ℤ, d ≤ |z.re / hstep - 2 ^ n - (qq n : ℝ) * k|) :
    ‖Phi n z‖ ≤ Real.exp (|z.im| / 4) / (4 * d ^ 2) := by
  have h := norm_fejer_le_of_dist (qq_pos n) (z / hstep - 2 ^ n) d hd (by
    intro k
    rw [shift_re]
    exact hdist k)
  rwa [exp_arg_Phi] at h

lemma differentiable_Phi (n : ℕ) : Differentiable ℂ (Phi n) :=
  (differentiable_fejer _).comp (by fun_prop)

/-- Sampling values of `Phi n` at the lattice `hstep • ℤ`. -/
lemma Phi_sample (n : ℕ) (k : ℤ) :
    Phi n (hstep * k) = if ((2 : ℤ) ^ (n + 1)) ∣ (k - 2 ^ n) then 1 else 0 := by
  have hne : (hstep : ℂ) ≠ 0 := by
    simpa using ne_of_gt hstep_pos
  have harg : (hstep : ℂ) * (k : ℂ) / (hstep : ℂ) - 2 ^ n = (((k - 2 ^ n : ℤ)) : ℂ) := by
    field_simp
    push_cast
    ring
  rw [Phi, harg, fejer_intCast (qq_pos n)]
  norm_num [qq]

/-- Each `Phi n` restricted to `ℝ` lies in `E`. -/
lemma isE_Phi (n : ℕ) : IsE (fun x : ℝ => Phi n x) :=
  isE_ofReal (K := 1) (differentiable_Phi n) (fun z => by simpa using norm_Phi_le n z)

/-- `Phi n` as an element of `E`. -/
def PhiE (n : ℕ) : E := E.mk _ (isE_Phi n)

lemma norm_PhiE_le (n : ℕ) : ‖PhiE n‖ ≤ 1 :=
  norm_mk_ofReal_le (K := 1) (differentiable_Phi n) (fun z => by simpa using norm_Phi_le n z)

lemma PhiE_mem_F (n : ℕ) : PhiE n ∈ F := by
  classical
  set q := qq n with hq
  have hqpos : 0 < q := qq_pos n
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hqc : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hqpos.ne'
  have hpi := Real.pi_pos
  have hh : (0 : ℝ) < hstep := hstep_pos
  set l : ℕ × ℕ → ℝ := fun p =>
    if p.1 < q ∧ p.2 < q then 2 * Real.pi * ((p.1 : ℝ) - p.2) / (hstep * q) else 0 with hl
  have hlb : ∀ p : ℕ × ℕ, |l p| ≤ 1 := by
    intro p
    rw [hl]
    dsimp only
    split
    · rename_i hp
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < hstep * q)]
      rw [div_le_one (by positivity)]
      have h1 : |(p.1 : ℝ) - p.2| ≤ q := by
        rw [abs_le]
        constructor
        · have : (p.2 : ℝ) ≤ q := by exact_mod_cast hp.2.le
          have : (0 : ℝ) ≤ p.1 := Nat.cast_nonneg _
          linarith
        · have : (p.1 : ℝ) ≤ q := by exact_mod_cast hp.1.le
          have : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg _
          linarith
      have h2 : |2 * Real.pi * ((p.1 : ℝ) - p.2)| = 2 * Real.pi * |(p.1 : ℝ) - p.2| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      rw [h2, hstep]
      nlinarith
    · simp
  set c : ℕ × ℕ → ℂ := fun p =>
    ((q : ℂ) ^ 2)⁻¹ * Complex.exp (-(2 * Real.pi * I * ((p.1 : ℂ) - p.2) * (2 ^ n) / q)) with hc
  refine mem_F_of_finite_sum (Finset.range q ×ˢ Finset.range q) c l hlb (PhiE n) ?_
  funext x
  show Phi n (x : ℂ) = _
  rw [Phi, ← hq, fejer_eq_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
  rw [hc, hl]
  dsimp only
  rw [if_pos ⟨hp.1, hp.2⟩, expFn, mul_assoc ((q : ℂ) ^ 2)⁻¹, ← Complex.exp_add]
  congr 1
  have hhc : (hstep : ℂ) ≠ 0 := by simpa using ne_of_gt hstep_pos
  push_cast
  field_simp
  ring_nf

/-! ### A majorant for the sum over `n` -/

/-- An injection `ℤ → ℕ` with `phiInj j ≤ 2 |j| + 1`. -/
def phiInj (j : ℤ) : ℕ := 2 * j.natAbs + (if 0 ≤ j then 0 else 1)

lemma phiInj_injective : Function.Injective phiInj := by
  intro a b h
  unfold phiInj at h
  split_ifs at h <;> omega

lemma phiInj_le (j : ℤ) : (phiInj j : ℝ) ≤ 2 * |(j : ℝ)| + 1 := by
  have hj : ((j.natAbs : ℕ) : ℝ) = |(j : ℝ)| := by
    rw [Nat.cast_natAbs]; simp
  unfold phiInj
  split_ifs
  · push_cast
    rw [hj]
    linarith [abs_nonneg ((j : ℝ))]
  · push_cast
    rw [hj]

/-- The majorant sequence. -/
def Hmaj (v : ℕ) : ℝ := if v ≤ 2 then 1 else 4 / ((v : ℝ) - 1) ^ 2

lemma Hmaj_nonneg (v : ℕ) : 0 ≤ Hmaj v := by
  unfold Hmaj; split
  · norm_num
  · positivity

lemma summable_inv_sq_shift : Summable (fun k : ℕ => 1 / ((k : ℝ) + 2) ^ 2) := by
  have h2 := (summable_nat_add_iff 2).2 hasSum_zeta_two.summable
  refine h2.congr (fun k => ?_)
  push_cast
  ring_nf

lemma tsum_inv_sq_shift : ∑' k : ℕ, 1 / ((k : ℝ) + 2) ^ 2 = Real.pi ^ 2 / 6 - 1 := by
  have key := hasSum_zeta_two.summable.sum_add_tsum_nat_add 2
  rw [hasSum_zeta_two.tsum_eq] at key
  have hs : ∑ i ∈ Finset.range 2, 1 / ((i : ℝ)) ^ 2 = 1 := by norm_num
  have hc : ∑' k : ℕ, 1 / (((k + 2 : ℕ)) : ℝ) ^ 2 = ∑' k : ℕ, 1 / ((k : ℝ) + 2) ^ 2 :=
    tsum_congr (fun k => by push_cast; ring_nf)
  rw [hs, hc] at key
  linarith

lemma summable_Hmaj : Summable Hmaj := by
  rw [← summable_nat_add_iff 3]
  refine Summable.congr (summable_inv_sq_shift.mul_left 4) (fun k => ?_)
  unfold Hmaj
  rw [if_neg (by omega)]
  push_cast
  ring_nf

lemma tsum_Hmaj_le : ∑' v, Hmaj v ≤ 6 := by
  have key := summable_Hmaj.sum_add_tsum_nat_add 3
  have hs : ∑ i ∈ Finset.range 3, Hmaj i = 3 := by
    simp [Hmaj, Finset.sum_range_succ]
    norm_num
  have hc : ∑' k : ℕ, Hmaj (k + 3) = 4 * ∑' k : ℕ, 1 / ((k : ℝ) + 2) ^ 2 := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    unfold Hmaj
    rw [if_neg (by omega)]
    push_cast
    ring_nf
  rw [hs, hc, tsum_inv_sq_shift] at key
  rw [← key]
  nlinarith [Real.pi_lt_d2, Real.pi_gt_three]

/-! ### Summability of `∑ ‖Phi n z‖` -/

lemma abs_sub_round_le (x : ℝ) (k : ℤ) : |x - round x| ≤ |x - k| := by
  by_cases hk : k = round x
  · rw [hk]
  · have h1 : (1 : ℝ) ≤ |((k : ℝ)) - round x| := by
      have : (1 : ℤ) ≤ |k - round x| := Int.one_le_abs (sub_ne_zero.2 hk)
      have h2 : ((|k - round x| : ℤ) : ℝ) = |((k : ℝ)) - ((round x : ℤ) : ℝ)| := by
        push_cast [Int.cast_abs]
        ring_nf
      calc (1 : ℝ) ≤ ((|k - round x| : ℤ) : ℝ) := by exact_mod_cast this
        _ = |((k : ℝ)) - round x| := h2
    have h3 : |x - round x| ≤ 1 / 2 := abs_sub_round x
    have h4 : |((k : ℝ)) - round x| ≤ |x - k| + |x - round x| := by
      calc |((k : ℝ)) - round x| = |(x - round x) - (x - k)| := by ring_nf
        _ ≤ |x - round x| + |x - k| := abs_sub _ _
        _ = |x - k| + |x - round x| := by ring
    linarith

theorem summable_norm_Phi (z : ℂ) :
    Summable (fun n => ‖Phi n z‖) ∧
      ∑' n, ‖Phi n z‖ ≤ 6 * Real.exp (|z.im| / 4) := by
  set M := Real.exp (|z.im| / 4) with hM
  have hMpos : 0 < M := Real.exp_pos _
  set t := z.re / hstep with ht
  set xx : ℕ → ℝ := fun n => (t - 2 ^ n) / 2 ^ (n + 1) with hxx
  set pk : ℕ → ℤ := fun n => 2 ^ n + 2 ^ (n + 1) * round (xx n) with hpk
  -- the peaks are distinct
  have hpk_inj : Function.Injective pk := by
    have haux : ∀ a b : ℕ, a < b → pk a ≠ pk b := by
      intro a b hab hEq
      obtain ⟨e, rfl⟩ : ∃ e, b = a + 1 + e := ⟨b - a - 1, by omega⟩
      rw [hpk] at hEq
      dsimp only at hEq
      have h2 : (2 : ℤ) ^ a * (1 + 2 * round (xx a))
          = (2 : ℤ) ^ a * (2 * (2 ^ e * (1 + 2 * round (xx (a + 1 + e))))) := by
        have e1 : (2 : ℤ) ^ (a + 1) = 2 ^ a * 2 := by ring
        have e2 : (2 : ℤ) ^ (a + 1 + e) = 2 ^ a * (2 * 2 ^ e) := by ring
        have e3 : (2 : ℤ) ^ (a + 1 + e + 1) = 2 ^ a * (2 * (2 * 2 ^ e)) := by ring
        rw [e1, e2, e3] at hEq
        linarith [hEq]
      have h3 : (0 : ℤ) < 2 ^ a := by positivity
      have h4 : (1 + 2 * round (xx a)) = 2 * (2 ^ e * (1 + 2 * round (xx (a + 1 + e)))) :=
        mul_left_cancel₀ (by omega) h2
      omega
    intro a b hEq
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hEq (haux a b h)
    · exact h
    · exact absurd hEq.symm (haux b a h)
  set m0 : ℤ := round t with hm0
  set jj : ℕ → ℤ := fun n => pk n - m0 with hjj
  have hjj_inj : Function.Injective jj := by
    intro a b h
    refine hpk_inj ?_
    rw [hjj] at h
    dsimp only at h
    omega
  set nu : ℕ → ℕ := fun n => phiInj (jj n) with hnu
  have hnu_inj : Function.Injective nu := phiInj_injective.comp hjj_inj
  -- the key pointwise bound
  have hbound : ∀ n, ‖Phi n z‖ ≤ M * Hmaj (nu n) := by
    intro n
    by_cases hv : nu n ≤ 2
    · rw [Hmaj, if_pos hv, mul_one]
      exact norm_Phi_le n z
    · push_neg at hv
      rw [Hmaj, if_neg (by omega)]
      set J : ℝ := |((jj n : ℤ) : ℝ)| with hJ
      have hnule : (nu n : ℝ) ≤ 2 * J + 1 := by rw [hnu, hJ]; exact phiInj_le _
      have hJ1 : (1 : ℝ) ≤ J := by
        have : (3 : ℝ) ≤ (nu n : ℝ) := by exact_mod_cast hv
        linarith
      -- distance from `t` to the `n`-th peak
      set d : ℝ := |t - ((pk n : ℤ) : ℝ)| with hd
      have hdge : J - 1 / 2 ≤ d := by
        have h1 : |t - ((m0 : ℤ) : ℝ)| ≤ 1 / 2 := by
          rw [hm0]; exact abs_sub_round t
        have h2 : J ≤ d + |t - ((m0 : ℤ) : ℝ)| := by
          rw [hJ, hjj, hd]
          push_cast
          calc |((pk n : ℤ) : ℝ) - ((m0 : ℤ) : ℝ)|
              = |(t - ((m0 : ℤ) : ℝ)) - (t - ((pk n : ℤ) : ℝ))| := by ring_nf
            _ ≤ |t - ((m0 : ℤ) : ℝ)| + |t - ((pk n : ℤ) : ℝ)| := abs_sub _ _
            _ = |t - ((pk n : ℤ) : ℝ)| + |t - ((m0 : ℤ) : ℝ)| := by ring
        linarith
      have hdpos : 0 < d := by linarith
      have hdist : ∀ k : ℤ, d ≤ |z.re / hstep - 2 ^ n - (qq n : ℝ) * k| := by
        intro k
        have hrw : z.re / hstep - 2 ^ n - (qq n : ℝ) * k
            = (2 : ℝ) ^ (n + 1) * (xx n - k) := by
          rw [hxx, ← ht, qq]
          push_cast
          field_simp
        have hrw2 : t - ((pk n : ℤ) : ℝ) = (2 : ℝ) ^ (n + 1) * (xx n - round (xx n)) := by
          rw [hpk, hxx]
          push_cast
          field_simp
          ring
        rw [hd, hrw, hrw2, abs_mul, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (n + 1))]
        exact mul_le_mul_of_nonneg_left (abs_sub_round_le (xx n) k) (by positivity)
      have hmain := norm_Phi_le_of_dist n z d hdpos hdist
      refine le_trans hmain ?_
      rw [← hM]
      rw [div_le_iff₀ (by positivity)]
      have hstep1 : (nu n : ℝ) - 1 ≤ 2 * J := by linarith
      have hd2 : J / 2 ≤ d := by linarith
      have hnn : (0 : ℝ) < ((nu n : ℝ) - 1) := by
        have : (3 : ℝ) ≤ (nu n : ℝ) := by exact_mod_cast hv
        linarith
      have hne : ((nu n : ℝ) - 1) ≠ 0 := ne_of_gt hnn
      have hsq : ((nu n : ℝ) - 1) ^ 2 ≤ 16 * d ^ 2 := by nlinarith
      have key : M * (4 / ((nu n : ℝ) - 1) ^ 2) * (((nu n : ℝ) - 1) ^ 2)
          ≤ M * (4 / ((nu n : ℝ) - 1) ^ 2) * (16 * d ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg hMpos.le (by positivity))
      have keyeq : M * (4 / ((nu n : ℝ) - 1) ^ 2) * (((nu n : ℝ) - 1) ^ 2) = 4 * M := by
        field_simp
      have keyeq2 : M * (4 / ((nu n : ℝ) - 1) ^ 2) * (16 * d ^ 2)
          = 4 * (M * (4 / ((nu n : ℝ) - 1) ^ 2) * (4 * d ^ 2)) := by ring
      linarith
  -- summability and the bound
  have hgsum : Summable (fun v => M * Hmaj v) := summable_Hmaj.mul_left M
  have hcomp : Summable (fun n => M * Hmaj (nu n)) := hgsum.comp_injective hnu_inj
  have hf : Summable (fun n => ‖Phi n z‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hcomp
  refine ⟨hf, ?_⟩
  calc ∑' n, ‖Phi n z‖ ≤ ∑' v, M * Hmaj v :=
        Summable.tsum_le_tsum_of_inj nu hnu_inj
          (fun v _ => mul_nonneg hMpos.le (Hmaj_nonneg v)) hbound hf hgsum
    _ = M * ∑' v, Hmaj v := tsum_mul_left
    _ ≤ M * 6 := by
        exact mul_le_mul_of_nonneg_left tsum_Hmaj_le hMpos.le
    _ = 6 * M := by ring

/-! ### The summed operator -/

/-- The interpolating entire function attached to a bounded sequence. -/
def Gfun (x : ℕ →ᵇ ℂ) (z : ℂ) : ℂ := ∑' n, x n * Phi n z

lemma summable_Gfun (x : ℕ →ᵇ ℂ) (z : ℂ) : Summable (fun n => x n * Phi n z) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_
    ((summable_norm_Phi z).1.mul_left ‖x‖)
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (x.norm_coe_le_norm n) (norm_nonneg _)

lemma norm_Gfun_le (x : ℕ →ᵇ ℂ) (z : ℂ) :
    ‖Gfun x z‖ ≤ (6 * ‖x‖) * Real.exp (|z.im| / 4) := by
  rw [Gfun]
  have h1 : ‖∑' n, x n * Phi n z‖ ≤ ∑' n, ‖x n * Phi n z‖ :=
    norm_tsum_le_tsum_norm ((summable_Gfun x z).norm)
  have h2 : ∑' n, ‖x n * Phi n z‖ ≤ ∑' n, ‖x‖ * ‖Phi n z‖ := by
    refine Summable.tsum_le_tsum (fun n => ?_) ((summable_Gfun x z).norm)
      ((summable_norm_Phi z).1.mul_left ‖x‖)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (x.norm_coe_le_norm n) (norm_nonneg _)
  have h3 : ∑' n, ‖x‖ * ‖Phi n z‖ = ‖x‖ * ∑' n, ‖Phi n z‖ := tsum_mul_left
  have h4 : ‖x‖ * ∑' n, ‖Phi n z‖ ≤ ‖x‖ * (6 * Real.exp (|z.im| / 4)) :=
    mul_le_mul_of_nonneg_left (summable_norm_Phi z).2 (norm_nonneg x)
  calc ‖∑' n, x n * Phi n z‖ ≤ ‖x‖ * (6 * Real.exp (|z.im| / 4)) := by
        rw [← h3] at h4; linarith
    _ = (6 * ‖x‖) * Real.exp (|z.im| / 4) := by ring

/-- On any bounded region `{|Re w| ≤ R, |Im w| ≤ R}` the kernels `Phi n` obey a uniform
geometric bound: for `2 ^ n` large compared with `R / hstep` the point `w` stays at
distance at least `2 ^ n / 2` from every peak `2 ^ n + 2 ^ (n+1) k`, so `norm_Phi_le_of_dist`
gives an `O(4 ^ (-n))` estimate; the finitely many remaining indices are absorbed in the
constant. -/
lemma Phi_geom_bound (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (w : ℂ), |w.re| ≤ R → |w.im| ≤ R →
      ‖Phi n w‖ ≤ C * (1 / 4 : ℝ) ^ n := by
  have hh : (0 : ℝ) < hstep := hstep_pos
  set T : ℝ := R / hstep with hT
  have hT0 : 0 ≤ T := by positivity
  obtain ⟨n0, hn0⟩ := pow_unbounded_of_one_lt (2 * T) (by norm_num : (1 : ℝ) < 2)
  refine ⟨Real.exp (R / 4) * 4 ^ n0, by positivity, ?_⟩
  intro n w hwre hwim
  have hexp : Real.exp (|w.im| / 4) ≤ Real.exp (R / 4) :=
    Real.exp_le_exp.2 (by linarith [abs_nonneg w.im])
  have hEpos : (0 : ℝ) < Real.exp (R / 4) := Real.exp_pos _
  have h1n : (1 : ℝ) ≤ 4 ^ n0 := one_le_pow₀ (by norm_num)
  have hrw : Real.exp (R / 4) * 4 ^ n0 * (1 / 4 : ℝ) ^ n
      = (Real.exp (R / 4) * 4 ^ n0) / 4 ^ n := by
    rw [div_pow, one_pow, mul_one_div]
  by_cases hn : n0 ≤ n
  · have h2n : 2 * T < (2 : ℝ) ^ n :=
      lt_of_lt_of_le hn0 (pow_le_pow_right₀ (by norm_num) hn)
    have hd : (0 : ℝ) < 2 ^ n / 2 := by positivity
    have hdist : ∀ k : ℤ, (2 : ℝ) ^ n / 2 ≤ |w.re / hstep - 2 ^ n - (qq n : ℝ) * k| := by
      intro k
      have habs : (1 : ℝ) ≤ |1 + 2 * (k : ℝ)| := by
        rcases lt_or_ge k 0 with hk | hk
        · have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
          rw [abs_of_nonpos (by linarith)]; linarith
        · have : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
          rw [abs_of_nonneg (by linarith)]; linarith
      have hkey : |(2 : ℝ) ^ n + (qq n : ℝ) * k| = 2 ^ n * |1 + 2 * (k : ℝ)| := by
        have hrw2 : (2 : ℝ) ^ n + (qq n : ℝ) * k = 2 ^ n * (1 + 2 * k) := by
          simp only [qq]; push_cast; ring
        rw [hrw2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)]
      have ht : |w.re / hstep| ≤ T := by
        rw [abs_div, abs_of_pos hh, hT]
        gcongr
      have h1 : (2 : ℝ) ^ n ≤ |(2 : ℝ) ^ n + (qq n : ℝ) * k| := by
        rw [hkey]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
      have h2 := abs_sub_abs_le_abs_sub ((2 : ℝ) ^ n + (qq n : ℝ) * k) (w.re / hstep)
      have e : ((2 : ℝ) ^ n + (qq n : ℝ) * k) - (w.re / hstep)
          = -(w.re / hstep - 2 ^ n - (qq n : ℝ) * k) := by ring
      rw [e, abs_neg] at h2
      linarith
    have hmain := norm_Phi_le_of_dist n w ((2 : ℝ) ^ n / 2) hd hdist
    have hp : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have heq : 4 * ((2 : ℝ) ^ n / 2) ^ 2 = 4 ^ n := by rw [hp]; ring
    rw [heq] at hmain
    refine hmain.trans ?_
    rw [hrw]
    gcongr
    exact hexp.trans (le_mul_of_one_le_right hEpos.le h1n)
  · push_neg at hn
    have h44 : (4 : ℝ) ^ n ≤ 4 ^ n0 := pow_le_pow_right₀ (by norm_num) hn.le
    have hquot : (1 : ℝ) ≤ 4 ^ n0 * (1 / 4 : ℝ) ^ n := by
      rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 4 ^ n)]
      simpa using h44
    calc ‖Phi n w‖ ≤ Real.exp (|w.im| / 4) := norm_Phi_le n w
      _ ≤ Real.exp (R / 4) := hexp
      _ ≤ Real.exp (R / 4) * (4 ^ n0 * (1 / 4 : ℝ) ^ n) := le_mul_of_one_le_right hEpos.le hquot
      _ = Real.exp (R / 4) * 4 ^ n0 * (1 / 4 : ℝ) ^ n := by ring

/-- `Gfun x` is entire: on every ball the series `∑ x n * Phi n` is dominated by a summable
geometric series, so the holomorphic partial sums converge locally uniformly. -/
lemma differentiable_Gfun (x : ℕ →ᵇ ℂ) : Differentiable ℂ (Gfun x) := by
  intro z0
  set R : ℝ := |z0.re| + |z0.im| + 1 with hRdef
  have hR0 : 0 ≤ R := by positivity
  obtain ⟨C, hC0, hCle⟩ := Phi_geom_bound R hR0
  set U := Metric.ball z0 1 with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hsum : Summable (fun n : ℕ => (‖x‖ * C) * (1 / 4 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hle : ∀ (n : ℕ) (w : ℂ), w ∈ U → ‖x n * Phi n w‖ ≤ (‖x‖ * C) * (1 / 4 : ℝ) ^ n := by
    intro n w hw
    rw [hUdef, Metric.mem_ball, Complex.dist_eq] at hw
    have hre0 : |(w - z0).re| ≤ ‖w - z0‖ := Complex.abs_re_le_norm _
    have him0 : |(w - z0).im| ≤ ‖w - z0‖ := Complex.abs_im_le_norm _
    have hn1 : ‖w - z0‖ < 1 := hw
    have hre : |w.re| ≤ R := by
      have h := abs_sub_abs_le_abs_sub w.re z0.re
      simp only [Complex.sub_re] at hre0
      have := abs_nonneg z0.im
      linarith
    have him : |w.im| ≤ R := by
      have h := abs_sub_abs_le_abs_sub w.im z0.im
      simp only [Complex.sub_im] at him0
      have := abs_nonneg z0.re
      linarith
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (x.norm_coe_le_norm n) (hCle n w hre him) (norm_nonneg _) (norm_nonneg x)
  have hdiff := differentiableOn_tsum_of_summable_norm hsum
    (fun n => ((differentiable_Phi n).const_mul (x n)).differentiableOn) hUopen hle
  exact hdiff.differentiableAt (hUopen.mem_nhds (Metric.mem_ball_self one_pos))

lemma isE_Gfun (x : ℕ →ᵇ ℂ) : IsE (fun t : ℝ => Gfun x t) :=
  isE_ofReal (differentiable_Gfun x) (norm_Gfun_le x)

/-- The interpolation operator `ℓ^∞(ℕ) → E`. -/
def Smap : (ℕ →ᵇ ℂ) →L[ℂ] E := by
  refine LinearMap.mkContinuous
    { toFun := fun x => E.mk _ (isE_Gfun x)
      map_add' := ?_
      map_smul' := ?_ } 6 ?_
  · intro x y
    refine E.ext ?_
    funext s
    show Gfun (x + y) s = Gfun x s + Gfun y s
    rw [Gfun, Gfun, Gfun, ← Summable.tsum_add (summable_Gfun x s) (summable_Gfun y s)]
    exact tsum_congr (fun n => by simp [add_mul])
  · intro c x
    refine E.ext ?_
    funext s
    show Gfun (c • x) s = c * Gfun x s
    rw [Gfun, Gfun, ← tsum_mul_left]
    exact tsum_congr (fun n => by simp [mul_assoc])
  · intro x
    exact norm_mk_ofReal_le (differentiable_Gfun x) (norm_Gfun_le x)

@[simp] lemma Smap_fn (x : ℕ →ᵇ ℂ) : (Smap x).fn = fun t : ℝ => Gfun x t := rfl

/-! ### The dyadic sequence space -/

/-- The `2`-adic valuation of a nonzero integer (junk value `0` at `0`). -/
def dyIdx (k : ℤ) : ℕ := (k.natAbs).factorization 2

lemma dyadic_iff {n : ℕ} {k : ℤ} (hk : k ≠ 0) :
    ((2 : ℤ) ^ (n + 1)) ∣ (k - 2 ^ n) ↔ dyIdx k = n := by
  have hk' : k.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hk
  have hdvd : ∀ m : ℕ, ((2 : ℤ) ^ m ∣ k) ↔ (2 ^ m ∣ k.natAbs) := by
    intro m
    rw [← Int.natAbs_dvd_natAbs]
    simp
  have h2 : ∀ m : ℕ, (0 : ℤ) < 2 ^ m := fun m => by positivity
  have key : ((2 : ℤ) ^ (n + 1)) ∣ (k - 2 ^ n) ↔ ((2 : ℤ) ^ n ∣ k ∧ ¬ ((2 : ℤ) ^ (n + 1) ∣ k)) := by
    constructor
    · rintro ⟨m, hm⟩
      have hkm : k = 2 ^ n * (1 + 2 * m) := by rw [pow_succ] at hm; linarith [hm]
      refine ⟨⟨1 + 2 * m, hkm⟩, ?_⟩
      rintro ⟨c, hc⟩
      rw [hkm, pow_succ] at hc
      have hcan : (1 + 2 * m) = 2 * c :=
        mul_left_cancel₀ (h2 n).ne' (by linarith [hc])
      omega
    · rintro ⟨⟨u, hu⟩, hnd⟩
      have hodd : ¬ (2 ∣ u) := by
        rintro ⟨v, rfl⟩
        exact hnd ⟨v, by rw [hu, pow_succ]; ring⟩
      obtain ⟨w, hw⟩ : (2 : ℤ) ∣ (u - 1) := by omega
      refine ⟨w, ?_⟩
      rw [hu, pow_succ, show u = 2 * w + 1 by omega]
      ring
  rw [key, hdvd, hdvd, dyIdx,
    Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hk',
    Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hk']
  omega

lemma dyIdx_two_pow (n : ℕ) : dyIdx (2 ^ n) = n := by
  have h : ((2 : ℤ) ^ n) ≠ 0 := by positivity
  exact (dyadic_iff h).1 (by simp)

lemma coe_ofDiscrete (f : ℤ → ℂ) (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C) :
    ⇑(ofNormedAddCommGroupDiscrete f C h) = f := rfl

/-- The underlying function of the "dyadic pullback". -/
def sseqFun (x : ℕ →ᵇ ℂ) : ℤ → ℂ := fun k => if k = 0 then 0 else x (dyIdx k)

lemma norm_sseqFun_le (x : ℕ →ᵇ ℂ) (k : ℤ) : ‖sseqFun x k‖ ≤ ‖x‖ := by
  unfold sseqFun
  split
  · simpa using norm_nonneg x
  · exact x.norm_coe_le_norm _

/-- The "dyadic pullback" of a bounded sequence: `Sseq x k = x (v₂ k)` for `k ≠ 0`. -/
def Sseq : (ℕ →ᵇ ℂ) →L[ℂ] (ℤ →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun x => ofNormedAddCommGroupDiscrete (sseqFun x) ‖x‖ (norm_sseqFun_le x)
      map_add' := by
        intro x y; ext k
        simp only [coe_ofDiscrete, coe_add, Pi.add_apply, sseqFun]
        split <;> simp
      map_smul' := by
        intro c x; ext k
        simp only [coe_ofDiscrete, BoundedContinuousFunction.coe_smul, sseqFun, RingHom.id_apply]
        split <;> simp }
    1 (by
      intro x
      refine (BoundedContinuousFunction.norm_le (by simpa using norm_nonneg x)).2 (fun k => ?_)
      simpa [coe_ofDiscrete] using norm_sseqFun_le x k)

@[simp] lemma Sseq_apply (x : ℕ →ᵇ ℂ) (k : ℤ) :
    Sseq x k = if k = 0 then 0 else x (dyIdx k) := rfl

/-- Sampling the interpolant recovers the dyadic sequence. -/
theorem Rmap_Smap (x : ℕ →ᵇ ℂ) : Rmap (Smap x) = Sseq x := by
  have hpow : ∀ n : ℕ, (2 : ℤ) ^ n < 2 ^ (n + 1) := by
    intro n
    have : (0 : ℤ) < 2 ^ n := by positivity
    rw [pow_succ]; linarith
  ext k
  rw [Rmap_apply, Sseq_apply]
  show Gfun x (((hstep * (k : ℝ) : ℝ)) : ℂ) = _
  have hcast : (((hstep * (k : ℝ) : ℝ)) : ℂ) = (hstep : ℂ) * (k : ℂ) := by push_cast; ring
  rw [hcast, Gfun]
  by_cases hk : k = 0
  · subst hk
    have hz : ∀ n : ℕ, x n * Phi n ((hstep : ℂ) * ((0 : ℤ) : ℂ)) = 0 := by
      intro n
      rw [Phi_sample n 0, if_neg, mul_zero]
      intro h
      rw [zero_sub, dvd_neg] at h
      have h1 := Int.le_of_dvd (by positivity) h
      linarith [hpow n]
    simp only [hz, tsum_zero, if_pos]
  · rw [tsum_eq_single (dyIdx k), Phi_sample, if_pos ((dyadic_iff hk).2 rfl), mul_one,
      if_neg hk]
    intro n hn
    rw [Phi_sample, if_neg, mul_zero]
    intro h
    exact hn ((dyadic_iff hk).1 h).symm

/-- The interpolation operator maps `c₀` into `F`. -/
theorem Smap_mem_F {x : ℕ →ᵇ ℂ} (hx : x ∈ c0) : Smap x ∈ F := by
  classical
  set y : ℕ → (ℕ →ᵇ ℂ) := fun N => ofNormedAddCommGroupDiscrete
      (fun n => if n < N then x n else 0) ‖x‖ (fun n => by
        dsimp only
        split
        · exact x.norm_coe_le_norm _
        · simp) with hy
  have hyval : ∀ N n, y N n = if n < N then x n else 0 := fun N n => rfl
  have hyF : ∀ N, Smap (y N) ∈ F := by
    intro N
    have hEq : Smap (y N) = ∑ n ∈ Finset.range N, (x n) • PhiE n := by
      refine E.ext ?_
      funext t
      show Gfun (y N) (t : ℂ) = _
      rw [E.fn_sum, Gfun]
      have hzero : ∀ n ∉ Finset.range N, y N n * Phi n (t : ℂ) = 0 := by
        intro n hn
        rw [Finset.mem_range] at hn
        rw [hyval, if_neg hn, zero_mul]
      rw [tsum_eq_sum hzero]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_range] at hn
      rw [hyval, if_pos hn]
      rfl
    rw [hEq]
    exact Submodule.sum_mem _ (fun n _ => Submodule.smul_mem _ _ (PhiE_mem_F n))
  have h1 : Filter.Tendsto y atTop (𝓝 x) := by
    rw [Metric.tendsto_atTop]
    intro e he
    obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.1 (mem_c0.1 hx)) (e / 2) (by linarith)
    refine ⟨N0, fun N hN => ?_⟩
    rw [dist_eq_norm]
    refine lt_of_le_of_lt
      ((BoundedContinuousFunction.norm_le (C := e / 2) (by linarith)).2 ?_) (by linarith)
    intro n
    have hval : (y N - x) n = (if n < N then x n else 0) - x n := rfl
    rw [hval]
    by_cases hn : n < N
    · rw [if_pos hn, sub_self, norm_zero]; linarith
    · rw [if_neg hn, zero_sub, norm_neg]
      have := hN0 n (by omega)
      rw [dist_zero_right] at this
      exact this.le
  have hlim : Filter.Tendsto (fun N => Smap (y N)) atTop (𝓝 (Smap x)) :=
    (Smap.continuous.tendsto x).comp h1
  exact F_isClosed.mem_of_tendsto hlim (.of_forall hyF)

end Q867
