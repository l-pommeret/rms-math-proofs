/-
# Q788 — the deterministic step of the fixed-level estimate

If the maximal chord product of a configuration is at most `α`, then each of its power sums
`∑_j e^{i r θ_j}` is bounded by `α ^ r`, *uniformly in the number `n` of points*.

The proof is elementary.  Writing `w_j = e^{iθ_j}`, the identity
`z ^ r - w ^ r = ∏_{ζ ^ r = 1} (z - ζ w)` together with the rotation invariance of `chordMax`
shows that the `r`-th power configuration `(r θ_j)` has chord products bounded by `α ^ r`.  The
power sum `∑_j w_j ^ r` is (minus) the subleading coefficient of `∏_j (X - w_j ^ r)`, and a
coefficient of a polynomial is bounded by the maximum of its modulus on the unit circle — here
obtained by *discrete* Fourier extraction over the `N`-th roots of unity.
-/
import RMS.Q788Vec

open MeasureTheory Real Set
open scoped ENNReal Topology

namespace Q788

/-! ## Discrete Fourier extraction of polynomial coefficients -/

/-- **Discrete Cauchy estimate.**  A coefficient of a complex polynomial is bounded by the
maximum modulus of the polynomial on the unit circle. -/
theorem norm_coeff_le_of_circle_bound (p : Polynomial ℂ) (M : ℝ) (m : ℕ)
    (h : ∀ t : ℝ, ‖p.eval (Complex.exp ((t : ℂ) * Complex.I))‖ ≤ M) :
    ‖p.coeff m‖ ≤ M := by
  classical
  set N := max (p.natDegree + 1) (m + 1) with hNdef
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.succ_pos _) (le_max_right _ _)
  have hmN : m < N := lt_of_lt_of_le (Nat.lt_succ_self m) (le_max_right _ _)
  have hdN : p.natDegree < N := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  set ζ := Complex.exp (2 * Real.pi * Complex.I / N) with hζdef
  have hprim : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hNpos.ne'
  have hζN : ζ ^ N = 1 := hprim.pow_eq_one
  have hnormζ : ‖ζ‖ = 1 := by
    rw [hζdef, Complex.norm_exp]; norm_num
  set e := N - m with hedef
  have hkey : ∑ k ∈ Finset.range N, p.eval (ζ ^ k) * ζ ^ (k * e) = (N : ℂ) * p.coeff m := by
    have hstep : ∀ k, p.eval (ζ ^ k) = ∑ m' ∈ Finset.range N, p.coeff m' * (ζ ^ k) ^ m' :=
      fun k => Polynomial.eval_eq_sum_range' hdN _
    simp_rw [hstep, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hinner : ∀ m' ∈ Finset.range N,
        (∑ k ∈ Finset.range N, p.coeff m' * (ζ ^ k) ^ m' * ζ ^ (k * e))
          = p.coeff m' * ∑ k ∈ Finset.range N, (ζ ^ (m' + e)) ^ k := by
      intro m' _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← pow_mul, mul_assoc, ← pow_add, ← pow_mul]
      congr 2
      ring
    have hgeom : ∀ m' ∈ Finset.range N,
        (∑ k ∈ Finset.range N, (ζ ^ (m' + e)) ^ k) = if m' = m then (N : ℂ) else 0 := by
      intro m' hm'
      simp only [Finset.mem_range] at hm'
      by_cases hcase : m' = m
      · subst hcase
        have hh : m' + e = N := by omega
        rw [hh, hζN]
        simp
      · have hne : ζ ^ (m' + e) ≠ 1 := by
          intro hone
          rw [hprim.pow_eq_one_iff_dvd] at hone
          obtain ⟨c, hc⟩ := hone
          have hc2 : c ≤ 1 := by
            by_contra hcon
            push_neg at hcon
            have : N * 2 ≤ N * c := Nat.mul_le_mul le_rfl hcon
            omega
          interval_cases c <;> omega
        rw [geom_sum_eq hne, ← pow_mul, mul_comm (m' + e) N, pow_mul, hζN, one_pow]
        simp [hcase]
    have hcomb : ∀ m' ∈ Finset.range N,
        (∑ k ∈ Finset.range N, p.coeff m' * (ζ ^ k) ^ m' * ζ ^ (k * e))
          = if m' = m then (N : ℂ) * p.coeff m else 0 := by
      intro m' hm'
      rw [hinner m' hm', hgeom m' hm']
      by_cases hc : m' = m
      · subst hc; simp [mul_comm]
      · simp [hc]
    rw [Finset.sum_congr rfl hcomb]
    simp [Finset.mem_range.mpr hmN]
  have hbound : ‖(N : ℂ) * p.coeff m‖ ≤ N * M := by
    rw [← hkey]
    calc ‖∑ k ∈ Finset.range N, p.eval (ζ ^ k) * ζ ^ (k * e)‖
        ≤ ∑ k ∈ Finset.range N, ‖p.eval (ζ ^ k) * ζ ^ (k * e)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range N, M := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, norm_pow, hnormζ, one_pow, mul_one]
          have hzk : ζ ^ k = Complex.exp (((2 * Real.pi * k / N : ℝ) : ℂ) * Complex.I) := by
            rw [hζdef, ← Complex.exp_nat_mul]
            congr 1
            have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
            push_cast
            field_simp
          rw [hzk]
          exact h _
      _ = N * M := by simp [mul_comm]
  rw [norm_mul] at hbound
  simp only [Complex.norm_natCast] at hbound
  have hN : (0 : ℝ) < N := by exact_mod_cast hNpos
  exact le_of_mul_le_mul_left (by linarith [hbound]) hN

/-- If all chord products of the points `v j` on the unit circle are at most `M`, then the sum
of the points is at most `M` in modulus. -/
theorem norm_sum_le_of_chordProd_le {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ) (M : ℝ)
    (h : ∀ t : ℝ, ∏ j, ‖Complex.exp ((t : ℂ) * Complex.I) - v j‖ ≤ M) :
    ‖∑ j, v j‖ ≤ M := by
  classical
  set p : Polynomial ℂ := ∏ j, (Polynomial.X - Polynomial.C (v j)) with hp
  have hdeg : p.natDegree = n := by
    rw [hp, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (v i)]
    simp
  have heval : ∀ z : ℂ, p.eval z = ∏ j, (z - v j) := by
    intro z; rw [hp, Polynomial.eval_prod]; simp
  have hnext : p.nextCoeff = -∑ j, v j := by
    rw [hp]; exact Polynomial.prod_X_sub_C_nextCoeff v
  have hc : p.coeff (p.natDegree - 1) = -∑ j, v j := by
    rw [← Polynomial.nextCoeff_of_natDegree_pos (by omega), hnext]
  have hkey := norm_coeff_le_of_circle_bound p M (p.natDegree - 1) (by
    intro t
    rw [heval, norm_prod]
    exact h t)
  rwa [hc, norm_neg] at hkey

/-! ## The power configuration -/

/-- The chord products of the `r`-th power configuration are bounded by the `r`-th power of the
maximal chord product of the original configuration. -/
theorem chordProd_pow_le {n : ℕ} (θ : Fin n → ℝ) (r : ℕ) (hr : 0 < r) (t : ℝ) :
    ∏ j, ‖Complex.exp ((t : ℂ) * Complex.I) - Complex.exp ((((r : ℝ) * θ j : ℝ) : ℂ) * Complex.I)‖
      ≤ chordMax θ ^ r := by
  classical
  set s : ℝ := t / r with hs
  set z : ℂ := Complex.exp ((s : ℂ) * Complex.I) with hz
  have hzr : z ^ r = Complex.exp ((t : ℂ) * Complex.I) := by
    have hrC : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    rw [hs]
    push_cast
    field_simp
  have hw : ∀ j, Complex.exp ((((r : ℝ) * θ j : ℝ) : ℂ) * Complex.I)
      = (Complex.exp ((θ j : ℂ) * Complex.I)) ^ r := by
    intro j; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  set ζ0 : ℂ := Complex.exp (2 * Real.pi * Complex.I / r) with hζ0
  have hprim : IsPrimitiveRoot ζ0 r := Complex.isPrimitiveRoot_exp r hr.ne'
  have hfac : ∀ j, Complex.exp ((t : ℂ) * Complex.I)
        - Complex.exp ((((r : ℝ) * θ j : ℝ) : ℂ) * Complex.I)
      = ∏ ζ ∈ Polynomial.nthRootsFinset r 1,
          (z - ζ * Complex.exp ((θ j : ℂ) * Complex.I)) := by
    intro j
    rw [← hzr, hw j]
    exact IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul _ _ hr hprim
  have hstep : ∀ ζ ∈ Polynomial.nthRootsFinset r 1,
      (∏ j, ‖z - ζ * Complex.exp ((θ j : ℂ) * Complex.I)‖) ≤ chordMax θ := by
    intro ζ hζ
    have hζr : ζ ^ r = 1 := (Polynomial.mem_nthRootsFinset hr 1).mp hζ
    have hnorm : ‖ζ‖ = 1 := by
      have hx : (0 : ℝ) ≤ ‖ζ‖ := norm_nonneg _
      have h1 : ‖ζ‖ ^ r = 1 := by rw [← norm_pow, hζr, norm_one]
      rcases (pow_eq_one_iff_cases (R := ℝ) (n := r) (a := ‖ζ‖)).mp h1 with h2 | h2 | h2 <;>
        simp_all
      linarith
    obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, ζ = Complex.exp ((φ : ℂ) * Complex.I) := by
      refine ⟨ζ.arg, ?_⟩
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I ζ]
      rw [hnorm]; ring_nf; simp
    have hcomb : ∀ j, ζ * Complex.exp ((θ j : ℂ) * Complex.I)
        = Complex.exp (((θ j + φ : ℝ) : ℂ) * Complex.I) := by
      intro j; rw [hφ, ← Complex.exp_add]; push_cast; ring_nf
    calc (∏ j, ‖z - ζ * Complex.exp ((θ j : ℂ) * Complex.I)‖)
        = chordProd (fun j => θ j + φ) s := by
          unfold chordProd
          exact Finset.prod_congr rfl fun j _ => by rw [hcomb j]
      _ ≤ chordMax (fun j => θ j + φ) := chordProd_le_chordMax _ _
      _ = chordMax θ := chordMax_add_const θ φ
  calc ∏ j, ‖Complex.exp ((t : ℂ) * Complex.I)
          - Complex.exp ((((r : ℝ) * θ j : ℝ) : ℂ) * Complex.I)‖
      = ∏ j, ∏ ζ ∈ Polynomial.nthRootsFinset r 1,
          ‖z - ζ * Complex.exp ((θ j : ℂ) * Complex.I)‖ := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [hfac j, norm_prod]
    _ = ∏ ζ ∈ Polynomial.nthRootsFinset r 1, ∏ j,
          ‖z - ζ * Complex.exp ((θ j : ℂ) * Complex.I)‖ := Finset.prod_comm
    _ ≤ ∏ _ζ ∈ Polynomial.nthRootsFinset r 1, chordMax θ :=
        Finset.prod_le_prod (fun _ _ => Finset.prod_nonneg fun _ _ => norm_nonneg _) hstep
    _ = chordMax θ ^ r := by rw [Finset.prod_const, hprim.card_nthRootsFinset]

/-- **The power sum bound.**  Each power sum of a configuration with maximal chord product at
most `α` is bounded by `α ^ r`, uniformly in the number of points. -/
theorem norm_powerSum_le {n : ℕ} (θ : Fin n → ℝ) (r : ℕ) (hr : 0 < r) {α : ℝ}
    (h1 : 0 ≤ α) (hα : chordMax θ ≤ α) :
    ‖∑ j, Complex.exp ((((r : ℝ) * θ j : ℝ) : ℂ) * Complex.I)‖ ≤ α ^ r := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using pow_nonneg h1 r
  have hcm : (0 : ℝ) ≤ chordMax θ := le_trans (by norm_num) (two_le_chordMax hn θ)
  calc ‖∑ j, Complex.exp ((((r : ℝ) * θ j : ℝ) : ℂ) * Complex.I)‖
      ≤ chordMax θ ^ r :=
        norm_sum_le_of_chordProd_le hn _ _ (chordProd_pow_le θ r hr)
    _ ≤ α ^ r := pow_le_pow_left₀ hcm hα r

/-! ## The bound for the trigonometric vector -/

/-- The explicit radius of the small ball forced by the event `{chordMax ≤ α}`. -/
noncomputable def powerBound (K : ℕ) (α : ℝ) : ℝ := (K : ℝ) * α ^ (2 * K)

theorem powerBound_pos {K : ℕ} (hK : 1 ≤ K) {α : ℝ} (hα : 0 < α) : 0 < powerBound K α := by
  have : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  unfold powerBound; positivity

/-- **The deterministic inclusion.**  On the event `{chordMax θ ≤ α}` the first `K` power sums
all lie in a ball whose radius does not depend on `n`. -/
theorem sqNorm_powerVec_le_of_chordMax_le {K n : ℕ} (θ : Fin n → ℝ) {α : ℝ}
    (h1 : 1 ≤ α) (hα : chordMax θ ≤ α) :
    sqNorm (powerVec K θ) ≤ powerBound K α := by
  have h0 : (0 : ℝ) ≤ α := by linarith
  have hcoord : ∀ r : Fin K,
      (powerVec K θ (r, true)) ^ 2 + (powerVec K θ (r, false)) ^ 2 ≤ α ^ (2 * K) := by
    intro r
    set m : ℕ := (r : ℕ) + 1 with hm
    set S : ℂ := ∑ j, Complex.exp ((((m : ℝ) * θ j : ℝ) : ℂ) * Complex.I) with hS
    have hre : S.re = powerVec K θ (r, false) := by
      rw [hS, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [trigVec]
      rw [Complex.exp_ofReal_mul_I_re, hm]
      push_cast
      simp
    have him : S.im = powerVec K θ (r, true) := by
      rw [hS, Complex.im_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [trigVec]
      rw [Complex.exp_ofReal_mul_I_im, hm]
      push_cast
      simp
    have hnorm : ‖S‖ ≤ α ^ m := norm_powerSum_le θ m (by omega) h0 hα
    have hsq : S.re ^ 2 + S.im ^ 2 = ‖S‖ ^ 2 := by
      rw [Complex.norm_def, Complex.normSq_apply,
        Real.sq_sqrt (by nlinarith [sq_nonneg S.re, sq_nonneg S.im] :
          (0 : ℝ) ≤ S.re * S.re + S.im * S.im)]
      ring
    have hmK : 2 * m ≤ 2 * K := by omega
    calc (powerVec K θ (r, true)) ^ 2 + (powerVec K θ (r, false)) ^ 2
        = S.re ^ 2 + S.im ^ 2 := by rw [hre, him]; ring
      _ = ‖S‖ ^ 2 := hsq
      _ ≤ (α ^ m) ^ 2 := by
          have := norm_nonneg S
          nlinarith [hnorm, norm_nonneg S, pow_nonneg h0 m]
      _ = α ^ (2 * m) := by rw [← pow_mul, mul_comm]
      _ ≤ α ^ (2 * K) := pow_le_pow_right₀ h1 hmK
  have hsplit : sqNorm (powerVec K θ)
      = ∑ r : Fin K, ((powerVec K θ (r, true)) ^ 2 + (powerVec K θ (r, false)) ^ 2) := by
    rw [sqNorm, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun r _ => by rw [Fintype.sum_bool]
  rw [hsplit, powerBound]
  calc ∑ _r : Fin K, ((powerVec K θ (_r, true)) ^ 2 + (powerVec K θ (_r, false)) ^ 2)
      ≤ ∑ _r : Fin K, α ^ (2 * K) := Finset.sum_le_sum fun r _ => hcoord r
    _ = (K : ℝ) * α ^ (2 * K) := by simp [mul_comm]

end Q788
