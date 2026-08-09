/-
# Q788 — maximal product of chord distances from a point of the unit circle
  to `n` independent uniform random points of the unit circle.

Formalization target (as recommended by the audit of the candidate solution):

* the exact deterministic evaluation for `n = 2`,
    `D₂ = 2 + 2|cos((θ₁-θ₂)/2)| = 4 cos²(Δ/4)`,
* the exact law for `n = 2`,
    `ℙ(D₂ ≥ α) = (4/π) arccos(√α/2)`   for `2 ≤ α ≤ 4`,
* its upper-edge equivalent `ℙ(D₂ ≥ α) ~ (2/π)√(4-α)` as `α ↑ 4`,
  together with `ℙ(D₂ = 4) = 0`,
* the deterministic ingredients of the fixed-`n` upper-edge analysis:
  the quadratic-form identity `min_c Σ (x_j - c)² = Σ (x_j - x̄)²` and the
  determinant `det (I_{n-1} - J_{n-1}/n) = 1/n`.

Beyond that target, the two-sided deterministic bound stated in the problem is proved for
all `n`:  `2 ≤ Dₙ ≤ 2ⁿ` (`two_le_chordMax`, `chordMax_le_two_pow`).  Since this holds for
*every* configuration, it is stronger than the almost sure statement of the problem.

Not formalized here (deliberately, following the audit): the fixed-`α`, `n → ∞`
superpolynomial estimate obtained from the Fourier/local-limit argument, the constructive
lower bound for the exceptional probability, the general fixed-`n` upper-edge asymptotic,
and the externally quoted Brownian-bridge limit theorem.

Points where the formal statements differ from the printed ones:

* `Dₙ` is defined as a supremum over the angle `t` of `∏_j |e^{it} - e^{iθ_j}|` rather than
  as a maximum over the circle; the two agree because the supremum is attained, and for
  `n = 2` the value is computed exactly, so nothing is lost.
* The probability space is the concrete uniform measure on `[0, 2π) × [0, 2π)` for the two
  angles (`unifAngles`), rather than an abstract product of Haar measures on the circle;
  these are isomorphic as probability spaces.
* The upper-edge equivalent is stated as the convergence to `1` of the ratio of the exact
  probability to `(2/π)√(4-α)`, which is the meaning of `∼`.

Lean version: 4.28.0 (`leanprover/lean4:v4.28.0`);
Mathlib: commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
-/
import Mathlib

open Real Complex MeasureTheory Set
open scoped ENNReal

namespace Q788

/-! ## The maximal chord product -/

/-- `chordMax θ` is `max_{|z| = 1} ∏_j |z - e^{i θ_j}|`, the maximum over the unit circle of
the product of the distances to the points `e^{i θ_j}` (written as a supremum over the
angle `t` of the point `z = e^{i t}`). -/
noncomputable def chordMax {n : ℕ} (θ : Fin n → ℝ) : ℝ :=
  ⨆ t : ℝ, ∏ j, ‖Complex.exp ((t : ℂ) * Complex.I) - Complex.exp ((θ j : ℂ) * Complex.I)‖

/-- The chord length between two points of the unit circle. -/
theorem norm_exp_sub_exp (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖
      = 2 * |Real.sin ((a - b) / 2)| := by
  have h1 : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)
      = Complex.ofReal (Real.cos a - Real.cos b)
        + Complex.ofReal (Real.sin a - Real.sin b) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  rw [h1, Complex.norm_add_mul_I]
  have hcos : Real.cos (a - b) = 1 - 2 * Real.sin ((a - b) / 2) ^ 2 := by
    have h := Real.cos_two_mul ((a - b) / 2)
    rw [show 2 * ((a - b) / 2) = a - b by ring] at h
    nlinarith [Real.sin_sq_add_cos_sq ((a - b) / 2)]
  have h2 : (Real.cos a - Real.cos b) ^ 2 + (Real.sin a - Real.sin b) ^ 2
      = (2 * |Real.sin ((a - b) / 2)|) ^ 2 := by
    have hc : Real.cos (a - b) = Real.cos a * Real.cos b + Real.sin a * Real.sin b :=
      Real.cos_sub a b
    nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b,
      sq_abs (Real.sin ((a - b) / 2))]
  rw [h2]
  exact Real.sqrt_sq (by positivity)

/-- Each factor is at most `2`, so the whole product is at most `2 ^ n`. -/
theorem chordProd_le_two_pow {n : ℕ} (θ : Fin n → ℝ) (t : ℝ) :
    ∏ j, ‖Complex.exp ((t : ℂ) * Complex.I) - Complex.exp ((θ j : ℂ) * Complex.I)‖ ≤ 2 ^ n := by
  calc ∏ j, ‖Complex.exp ((t : ℂ) * Complex.I) - Complex.exp ((θ j : ℂ) * Complex.I)‖
      ≤ ∏ _j : Fin n, (2 : ℝ) := by
        refine Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => ?_
        calc ‖Complex.exp ((t : ℂ) * Complex.I) - Complex.exp ((θ j : ℂ) * Complex.I)‖
            ≤ ‖Complex.exp ((t : ℂ) * Complex.I)‖ + ‖Complex.exp ((θ j : ℂ) * Complex.I)‖ :=
              norm_sub_le _ _
          _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]; norm_num
    _ = 2 ^ n := by simp

theorem bddAbove_chordProd {n : ℕ} (θ : Fin n → ℝ) :
    BddAbove (Set.range fun t : ℝ =>
      ∏ j, ‖Complex.exp ((t : ℂ) * Complex.I) - Complex.exp ((θ j : ℂ) * Complex.I)‖) :=
  ⟨2 ^ n, by rintro y ⟨t, rfl⟩; exact chordProd_le_two_pow θ t⟩

/-- `Dₙ ≤ 2 ⁿ`. -/
theorem chordMax_le_two_pow {n : ℕ} (θ : Fin n → ℝ) : chordMax θ ≤ 2 ^ n :=
  ciSup_le fun t => chordProd_le_two_pow θ t

/-- Averaging a polynomial of degree `n` over the `n`-th roots of unity keeps only the
constant and the leading term:  `∑_{k<n} p(ζᵏ z) = n (p₀ + pₙ zⁿ)`. -/
theorem sum_eval_roots {n : ℕ} (hn : 0 < n) (p : Polynomial ℂ) (hdeg : p.natDegree = n) (z : ℂ) :
    ∑ k ∈ Finset.range n,
        p.eval (Complex.exp (2 * Real.pi * Complex.I / n) ^ k * z)
      = n * (p.coeff 0 + p.coeff n * z ^ n) := by
  classical
  set ζ := Complex.exp (2 * Real.pi * Complex.I / n) with hζ
  have hprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hζn : ζ ^ n = 1 := hprim.pow_eq_one
  have hstep : ∀ k, p.eval (ζ ^ k * z)
      = ∑ m ∈ Finset.range (n + 1), p.coeff m * (ζ ^ k * z) ^ m :=
    fun k => Polynomial.eval_eq_sum_range' (by omega) _
  simp_rw [hstep]
  rw [Finset.sum_comm]
  have hinner : ∀ m ∈ Finset.range (n + 1),
      (∑ k ∈ Finset.range n, p.coeff m * (ζ ^ k * z) ^ m)
        = p.coeff m * z ^ m * ∑ k ∈ Finset.range n, (ζ ^ m) ^ k := by
    intro m _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k m]
    ring
  rw [Finset.sum_congr rfl hinner]
  have hgeom : ∀ m ∈ Finset.range (n + 1), (∑ k ∈ Finset.range n, (ζ ^ m) ^ k)
      = if m = 0 ∨ m = n then (n : ℂ) else 0 := by
    intro m hm
    simp only [Finset.mem_range] at hm
    by_cases h : m = 0
    · simp [h]
    · by_cases h2 : m = n
      · simp [h2, hζn]
      · have hne : ζ ^ m ≠ 1 := hprim.pow_ne_one_of_pos_of_lt h (by omega)
        rw [geom_sum_eq hne, ← pow_mul, mul_comm m n, pow_mul, hζn, one_pow]
        simp [h, h2]
  rw [Finset.sum_congr rfl fun m hm => by rw [hgeom m hm]]
  have hsub : ({0, n} : Finset ℕ) ⊆ Finset.range (n + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp
  rw [← Finset.sum_subset hsub (by
    intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    push_neg at hx
    simp [hx.1, hx.2])]
  rw [Finset.sum_pair (by omega)]
  simp
  ring

/-- `2 ≤ Dₙ` for every configuration of `n ≥ 1` points on the unit circle: the maximum of the
product of the chord distances is always at least `2`. -/
theorem two_le_chordMax {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) : 2 ≤ chordMax θ := by
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  set Z : Fin n → ℂ := fun j => Complex.exp ((θ j : ℂ) * Complex.I) with hZ
  set p : Polynomial ℂ := ∏ j, (Polynomial.X - Polynomial.C (Z j)) with hp
  have hmonic : p.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _
  have hdeg : p.natDegree = n := by
    rw [hp, Polynomial.natDegree_prod _ _ fun j _ => Polynomial.X_sub_C_ne_zero _]; simp
  have hcn : p.coeff n = 1 := by rw [← hdeg]; exact hmonic.coeff_natDegree
  have hc0 : ‖p.coeff 0‖ = 1 := by
    rw [hp, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
    simp [hZ, norm_prod]
  set w := p.coeff 0 with hw
  set φ : ℝ := Complex.arg w with hφ
  have hwe : w = Complex.exp ((φ : ℂ) * Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
    rw [hc0]; simp [hφ]
  set z₀ : ℂ := Complex.exp (((φ / n : ℝ) : ℂ) * Complex.I) with hz₀
  have hz₀n : z₀ ^ n = w := by
    rw [hz₀, ← Complex.exp_nat_mul, hwe]
    congr 1
    push_cast
    field_simp
  have hsum := sum_eval_roots hn p hdeg z₀
  rw [hz₀n, hcn, one_mul] at hsum
  have hnorm : ‖∑ k ∈ Finset.range n,
      p.eval (Complex.exp (2 * Real.pi * Complex.I / n) ^ k * z₀)‖ = 2 * n := by
    rw [hsum, show w + w = 2 * w by ring, norm_mul, norm_mul, hc0]
    simp
    ring
  have hex : ∃ k ∈ Finset.range n,
      2 ≤ ‖p.eval (Complex.exp (2 * Real.pi * Complex.I / n) ^ k * z₀)‖ := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∑ k ∈ Finset.range n,
          ‖p.eval (Complex.exp (2 * Real.pi * Complex.I / n) ^ k * z₀)‖
        < ∑ _k ∈ Finset.range n, (2 : ℝ) :=
      Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hn.ne') fun k hk => hcon k hk
    have hle := norm_sum_le (Finset.range n)
      (fun k => p.eval (Complex.exp (2 * Real.pi * Complex.I / n) ^ k * z₀))
    rw [hnorm] at hle
    simp at hlt
    linarith
  obtain ⟨k, hk, hk2⟩ := hex
  set t : ℝ := 2 * Real.pi * k / n + φ / n with ht
  have hpt : Complex.exp (2 * Real.pi * Complex.I / n) ^ k * z₀
      = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [hz₀, ← Complex.exp_nat_mul, ← Complex.exp_add, ht]
    congr 1
    push_cast
    field_simp
  rw [hpt] at hk2
  have heval : ‖p.eval (Complex.exp ((t : ℂ) * Complex.I))‖
      = ∏ j, ‖Complex.exp ((t : ℂ) * Complex.I) - Complex.exp ((θ j : ℂ) * Complex.I)‖ := by
    rw [hp, Polynomial.eval_prod, norm_prod]
    simp [hZ]
  rw [heval] at hk2
  exact le_ciSup_of_le (bddAbove_chordProd θ) t hk2

/-! ## The case `n = 2` -/

/-- The product of the two chord distances, in closed form. -/
theorem prod_two (a b t : ℝ) :
    ∏ j : Fin 2, ‖Complex.exp ((t : ℂ) * Complex.I) - Complex.exp (((![a, b] j : ℝ) : ℂ) * Complex.I)‖
      = 2 * |Real.cos ((a - b) / 2) - Real.cos (t - (a + b) / 2)| := by
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_exp_sub_exp]
  have key : 2 * Real.sin ((t - a) / 2) * (2 * Real.sin ((t - b) / 2))
      = 2 * (Real.cos ((a - b) / 2) - Real.cos (t - (a + b) / 2)) := by
    have h1 := Real.cos_sub ((t - a) / 2) ((t - b) / 2)
    have h2 := Real.cos_add ((t - a) / 2) ((t - b) / 2)
    rw [show (t - a) / 2 - (t - b) / 2 = (b - a) / 2 by ring] at h1
    rw [show (t - a) / 2 + (t - b) / 2 = t - (a + b) / 2 by ring] at h2
    have h3 : Real.cos ((b - a) / 2) = Real.cos ((a - b) / 2) := by
      rw [show (b - a) / 2 = -((a - b) / 2) by ring, Real.cos_neg]
    nlinarith [h1, h2, h3]
  have habs : |2 * Real.sin ((t - a) / 2) * (2 * Real.sin ((t - b) / 2))|
      = 2 * |Real.sin ((t - a) / 2)| * (2 * |Real.sin ((t - b) / 2)|) := by
    simp [abs_mul]
  rw [← habs, key, abs_mul]
  simp

/-- The bound `2 + 2|cos((a-b)/2)|` for the product, valid for every `t`. -/
theorem prod_two_le (a b t : ℝ) :
    ∏ j : Fin 2, ‖Complex.exp ((t : ℂ) * Complex.I) - Complex.exp (((![a, b] j : ℝ) : ℂ) * Complex.I)‖
      ≤ 2 + 2 * |Real.cos ((a - b) / 2)| := by
  rw [prod_two]
  have h := abs_le.mp (abs_cos_le_one (t - (a + b) / 2))
  cases abs_cases (Real.cos ((a - b) / 2) - Real.cos (t - (a + b) / 2)) with
  | inl h1 => cases abs_cases (Real.cos ((a - b) / 2)) with
    | inl h2 => linarith [h1.1, h2.1]
    | inr h2 => linarith [h1.1, h2.1]
  | inr h1 => cases abs_cases (Real.cos ((a - b) / 2)) with
    | inl h2 => linarith [h1.1, h2.1]
    | inr h2 => linarith [h1.1, h2.1]

/-- The exact value of `D₂`. -/
theorem chordMax_two (a b : ℝ) : chordMax ![a, b] = 2 + 2 * |Real.cos ((a - b) / 2)| := by
  have hb : BddAbove (Set.range fun t : ℝ => ∏ j : Fin 2,
      ‖Complex.exp ((t : ℂ) * Complex.I) - Complex.exp (((![a, b] j : ℝ) : ℂ) * Complex.I)‖) :=
    ⟨2 + 2 * |Real.cos ((a - b) / 2)|, by rintro y ⟨t, rfl⟩; exact prod_two_le a b t⟩
  refine le_antisymm (ciSup_le fun t => prod_two_le a b t) ?_
  rcases le_or_gt 0 (Real.cos ((a - b) / 2)) with hc | hc
  · refine le_ciSup_of_le hb ((a + b) / 2 + π) ?_
    rw [prod_two, show (a + b) / 2 + π - (a + b) / 2 = π by ring, Real.cos_pi, abs_of_nonneg hc,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.cos ((a - b) / 2) - (-1))]
    ring_nf
    linarith
  · refine le_ciSup_of_le hb ((a + b) / 2) ?_
    rw [prod_two, show (a + b) / 2 - (a + b) / 2 = 0 by ring, Real.cos_zero, abs_of_neg hc,
      abs_of_nonpos (by linarith : Real.cos ((a - b) / 2) - 1 ≤ 0)]
    ring_nf
    linarith

/-- With the two points at angular separation `Δ ∈ [0, π]`, `D₂ = 4 cos²(Δ/4)`. -/
theorem chordMax_two_sep (Δ : ℝ) (h₀ : 0 ≤ Δ) (h₁ : Δ ≤ π) :
    chordMax ![Δ / 2, -(Δ / 2)] = 4 * Real.cos (Δ / 4) ^ 2 := by
  rw [chordMax_two, show Δ / 2 - -(Δ / 2) = Δ by ring]
  have hcos : 0 ≤ Real.cos (Δ / 2) := by
    refine Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  rw [abs_of_nonneg hcos]
  have h := Real.cos_two_mul (Δ / 4)
  rw [show 2 * (Δ / 4) = Δ / 2 by ring] at h
  rw [h]; ring

theorem two_le_chordMax_two (a b : ℝ) : 2 ≤ chordMax ![a, b] := two_le_chordMax (by norm_num) _

theorem chordMax_two_le_four (a b : ℝ) : chordMax ![a, b] ≤ 4 := by
  rw [chordMax_two]
  have : |Real.cos ((a - b) / 2)| ≤ 1 := abs_cos_le_one _
  linarith

/-! ## The law of `D₂` -/

/-- The uniform probability measure on `[0, 2π) × [0, 2π)`: the law of the pair of angles of
two independent Haar-uniform random points of the unit circle. -/
noncomputable def unifAngles : Measure (ℝ × ℝ) :=
  (ENNReal.ofReal (4 * π ^ 2))⁻¹ •
    volume.restrict (Set.Ico 0 (2 * π) ×ˢ Set.Ico 0 (2 * π))

instance : IsProbabilityMeasure unifAngles := by
  constructor
  have hpi := Real.pi_pos
  rw [unifAngles, Measure.smul_apply, Measure.restrict_apply_univ, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ico, sub_zero, smul_eq_mul,
    ← ENNReal.ofReal_mul (by positivity)]
  rw [show (2 * π) * (2 * π) = 4 * π ^ 2 by ring]
  exact ENNReal.inv_mul_cancel (by simp [ENNReal.ofReal_eq_zero]) ENNReal.ofReal_ne_top

/-! ### The level sets of `|cos(u/2)|` -/

/-- The `2π`-periodic function whose level sets describe the event `D₂ ≥ α`. -/
noncomputable def cosHalf (u : ℝ) : ℝ := |Real.cos (u / 2)|

theorem cosHalf_periodic : Function.Periodic cosHalf (2 * π) := by
  intro u
  simp [cosHalf, show (u + 2 * π) / 2 = u / 2 + π by ring, Real.cos_add_pi]

theorem measurableSet_levelSet (β : ℝ) : MeasurableSet {u : ℝ | β ≤ cosHalf u} := by
  apply measurableSet_le measurable_const
  unfold cosHalf
  fun_prop

/-- The level set of `|cos(u/2)|` inside one period `(0, 2π]` is a union of two intervals. -/
theorem levelSet_inter_Ioc (β : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 1) :
    {u : ℝ | β ≤ cosHalf u} ∩ Ioc 0 (2 * π)
      = Ioc 0 (2 * Real.arccos β) ∪ Icc (2 * π - 2 * Real.arccos β) (2 * π) := by
  set c := Real.arccos β with hc
  have hc0 : 0 ≤ c := Real.arccos_nonneg β
  have hcpi : c ≤ π / 2 := Real.arccos_le_pi_div_two.mpr h0
  have hcosc : Real.cos c = β := Real.cos_arccos (by linarith) h1
  have hpi := Real.pi_pos
  ext u
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ioc, Set.mem_union, Set.mem_Icc,
    cosHalf]
  constructor
  · rintro ⟨hβ, hu0, hu2⟩
    rcases abs_cases (Real.cos (u / 2)) with ⟨he, _⟩ | ⟨he, _⟩
    · left
      refine ⟨hu0, ?_⟩
      have h : Real.arccos (Real.cos (u / 2)) ≤ Real.arccos β :=
        Real.arccos_le_arccos (by linarith)
      rw [Real.arccos_cos (by linarith) (by linarith)] at h
      linarith
    · right
      refine ⟨?_, hu2⟩
      have hle : Real.cos (u / 2) ≤ -β := by rw [he] at hβ; linarith
      have h : Real.arccos (-β) ≤ Real.arccos (Real.cos (u / 2)) := Real.arccos_le_arccos hle
      rw [Real.arccos_cos (by linarith) (by linarith), Real.arccos_neg] at h
      linarith
  · rintro (⟨hu0, hu2⟩ | ⟨hu1, hu2⟩)
    · refine ⟨?_, hu0, by linarith⟩
      have h : β ≤ Real.cos (u / 2) := by
        rw [← hcosc]
        exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
      exact h.trans (le_abs_self _)
    · refine ⟨?_, by linarith, hu2⟩
      have h : Real.cos (u / 2) ≤ -β := by
        rw [← hcosc, ← Real.cos_pi_sub]
        exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
      exact (by linarith : β ≤ -Real.cos (u / 2)).trans (neg_le_abs _)

theorem volume_levelSet_Ioc_zero (β : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 1) :
    volume ({u : ℝ | β ≤ cosHalf u} ∩ Ioc 0 (2 * π))
      = ENNReal.ofReal (4 * Real.arccos β) := by
  set c := Real.arccos β with hc
  have hc0 : 0 ≤ c := Real.arccos_nonneg β
  have hcpi : c ≤ π / 2 := Real.arccos_le_pi_div_two.mpr h0
  have hpi := Real.pi_pos
  rw [levelSet_inter_Ioc β h0 h1]
  have hdisj : (volume : Measure ℝ) (Ioc 0 (2 * c) ∩ Icc (2 * π - 2 * c) (2 * π)) = 0 := by
    refine measure_mono_null (t := Icc (2 * π - 2 * c) (2 * c))
      (fun u hu => ⟨hu.2.1, hu.1.2⟩) ?_
    rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]
    linarith
  rw [measure_union₀ (MeasurableSet.nullMeasurableSet measurableSet_Icc) hdisj,
    Real.volume_Ioc, Real.volume_Icc, ← ENNReal.ofReal_add (by linarith) (by linarith)]
  ring_nf

/-- By periodicity, the level set has the same measure in every period. -/
theorem volume_levelSet_Ioc (β x : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 1) :
    volume ({u : ℝ | β ≤ cosHalf u} ∩ Ioc (x - 2 * π) x)
      = ENNReal.ofReal (4 * Real.arccos β) := by
  have hpi := Real.pi_pos
  have hA : ∀ g : AddSubgroup.zmultiples (2 * π),
      (fun y => g +ᵥ y) ⁻¹' {u : ℝ | β ≤ cosHalf u} = {u : ℝ | β ≤ cosHalf u} := by
    intro g
    ext u
    simp [cosHalf_periodic.map_vadd_zmultiples g u]
  have hf1 := isAddFundamentalDomain_Ioc (T := 2 * π) (by linarith) (x - 2 * π) volume
  have hf2 := isAddFundamentalDomain_Ioc (T := 2 * π) (by linarith) 0 volume
  have h := hf1.measure_set_eq hf2 (measurableSet_levelSet β) hA
  rw [show x - 2 * π + 2 * π = x by ring, zero_add] at h
  rw [h, volume_levelSet_Ioc_zero β h0 h1]

/-- The one-dimensional slice of the event, at a fixed value of the first angle. -/
theorem volume_slice (β x : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 1) :
    volume {y : ℝ | y ∈ Ico 0 (2 * π) ∧ β ≤ |Real.cos ((x - y) / 2)|}
      = ENNReal.ofReal (4 * Real.arccos β) := by
  have hpre : {y : ℝ | y ∈ Ico 0 (2 * π) ∧ β ≤ |Real.cos ((x - y) / 2)|}
      = (fun y => x - y) ⁻¹' ({u : ℝ | β ≤ cosHalf u} ∩ Ioc (x - 2 * π) x) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ico,
      cosHalf]
    constructor
    · rintro ⟨⟨hy0, hy2⟩, hy⟩
      exact ⟨hy, by linarith, by linarith⟩
    · rintro ⟨hy, hy1, hy2⟩
      exact ⟨⟨by linarith, by linarith⟩, hy⟩
  rw [hpre, (Measure.measurePreserving_sub_left (volume : Measure ℝ) x).measure_preimage
    (((measurableSet_levelSet β).inter measurableSet_Ioc).nullMeasurableSet),
    volume_levelSet_Ioc β x h0 h1]

/-- The two-dimensional event, computed by Fubini. -/
theorem volume_box_event (β : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 1) :
    volume ({p : ℝ × ℝ | β ≤ |Real.cos ((p.1 - p.2) / 2)|}
        ∩ (Ico 0 (2 * π) ×ˢ Ico 0 (2 * π)))
      = ENNReal.ofReal (2 * π) * ENNReal.ofReal (4 * Real.arccos β) := by
  have hmeas : MeasurableSet ({p : ℝ × ℝ | β ≤ |Real.cos ((p.1 - p.2) / 2)|}
      ∩ (Ico 0 (2 * π) ×ˢ Ico 0 (2 * π))) := by
    refine MeasurableSet.inter ?_ (measurableSet_Ico.prod measurableSet_Ico)
    apply measurableSet_le measurable_const; fun_prop
  rw [Measure.volume_eq_prod, Measure.prod_apply hmeas]
  have hfun : ∀ x : ℝ, volume (Prod.mk x ⁻¹' ({p : ℝ × ℝ | β ≤ |Real.cos ((p.1 - p.2) / 2)|}
        ∩ (Ico 0 (2 * π) ×ˢ Ico 0 (2 * π))))
      = Set.indicator (Ico 0 (2 * π))
          (fun _ => ENNReal.ofReal (4 * Real.arccos β)) x := by
    intro x
    by_cases hx : x ∈ Ico 0 (2 * π)
    · rw [Set.indicator_of_mem hx, ← volume_slice β x h0 h1]
      congr 1
      ext y
      simp [hx, and_comm]
    · rw [Set.indicator_of_notMem hx]
      convert measure_empty (μ := (volume : Measure ℝ))
      ext y
      simp [hx]
  simp_rw [hfun]
  rw [lintegral_indicator measurableSet_Ico, setLIntegral_const, Real.volume_Ico]
  ring_nf

/-- `arccos ((α-2)/2) = 2 arccos (√α / 2)` for `0 ≤ α ≤ 4`. -/
theorem arccos_half_sqrt (α : ℝ) (h0 : 0 ≤ α) (h4 : α ≤ 4) :
    Real.arccos ((α - 2) / 2) = 2 * Real.arccos (Real.sqrt α / 2) := by
  have hs : Real.sqrt α / 2 ≤ 1 := by
    have h : Real.sqrt α ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt h4
    linarith
  have hs0 : 0 ≤ Real.sqrt α / 2 := by positivity
  have hsq : (Real.sqrt α / 2) ^ 2 = α / 4 := by
    rw [div_pow, Real.sq_sqrt h0]; norm_num
  have hc : Real.cos (2 * Real.arccos (Real.sqrt α / 2)) = (α - 2) / 2 := by
    rw [Real.cos_two_mul, Real.cos_arccos (by linarith) hs, hsq]
    ring
  have hle : Real.arccos (Real.sqrt α / 2) ≤ π / 2 := Real.arccos_le_pi_div_two.mpr hs0
  have hnn := Real.arccos_nonneg (Real.sqrt α / 2)
  rw [← hc, Real.arccos_cos (by linarith) (by linarith)]

/-- **The law of `D₂`.**  For `2 ≤ α ≤ 4`,
`ℙ(D₂ ≥ α) = (4/π) arccos(√α / 2)`. -/
theorem prob_chordMax_two_ge (α : ℝ) (h2 : 2 ≤ α) (h4 : α ≤ 4) :
    unifAngles {p : ℝ × ℝ | α ≤ chordMax ![p.1, p.2]}
      = ENNReal.ofReal (4 / π * Real.arccos (Real.sqrt α / 2)) := by
  have hpi := Real.pi_pos
  set β := (α - 2) / 2 with hβ
  have h0 : 0 ≤ β := by rw [hβ]; linarith
  have h1 : β ≤ 1 := by rw [hβ]; linarith
  have hset : {p : ℝ × ℝ | α ≤ chordMax ![p.1, p.2]}
      = {p : ℝ × ℝ | β ≤ |Real.cos ((p.1 - p.2) / 2)|} := by
    ext p
    simp only [Set.mem_setOf_eq, chordMax_two, hβ]
    constructor <;> intro h <;> linarith
  have hmeasE : MeasurableSet {p : ℝ × ℝ | β ≤ |Real.cos ((p.1 - p.2) / 2)|} := by
    apply measurableSet_le measurable_const; fun_prop
  rw [hset, unifAngles, Measure.smul_apply, Measure.restrict_apply hmeasE, smul_eq_mul,
    volume_box_event β h0 h1, arccos_half_sqrt α (by linarith) h4]
  have harc := Real.arccos_nonneg (Real.sqrt α / 2)
  rw [← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

/-- The trivial regime of part (a): for `α ≤ 2` the event `D₂ ≥ α` is sure. -/
theorem prob_chordMax_two_ge_of_le_two (α : ℝ) (hα : α ≤ 2) :
    unifAngles {p : ℝ × ℝ | α ≤ chordMax ![p.1, p.2]} = 1 := by
  have huniv : {p : ℝ × ℝ | α ≤ chordMax ![p.1, p.2]} = Set.univ := by
    ext p
    simpa using hα.trans (two_le_chordMax_two p.1 p.2)
  rw [huniv]
  exact measure_univ

/-- The maximal value `2 ^ 2 = 4` is attained with probability zero. -/
theorem prob_chordMax_two_eq_four :
    unifAngles {p : ℝ × ℝ | chordMax ![p.1, p.2] = 4} = 0 := by
  refine measure_mono_null (t := {p : ℝ × ℝ | (4 : ℝ) ≤ chordMax ![p.1, p.2]})
    (fun p hp => le_of_eq hp.symm) ?_
  rw [prob_chordMax_two_ge 4 (by norm_num) le_rfl,
    show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  norm_num

/-- **The upper-edge equivalent** for `n = 2`:  `ℙ(D₂ ≥ α) ∼ (2/π)√(4-α)` as `α ↑ 4`. -/
theorem prob_chordMax_two_ge_asymptotic :
    Filter.Tendsto
      (fun α : ℝ => (4 / π * Real.arccos (Real.sqrt α / 2)) / (2 / π * Real.sqrt (4 - α)))
      (nhdsWithin 4 (Set.Iio 4)) (nhds 1) := by
  have hpi := Real.pi_pos
  have hd : HasDerivAt Real.arcsin 1 0 := by
    have h := Real.hasDerivAt_arcsin (x := 0) (by norm_num) (by norm_num)
    simpa using h
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  have hu : Filter.Tendsto (fun α : ℝ => Real.sqrt (4 - α) / 2) (nhdsWithin 4 (Set.Iio 4))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : Continuous (fun α : ℝ => Real.sqrt (4 - α) / 2) := by fun_prop
      have h2 : Filter.Tendsto (fun α : ℝ => Real.sqrt (4 - α) / 2)
          (nhdsWithin 4 (Set.Iio 4)) (nhds (Real.sqrt (4 - 4) / 2)) :=
        (hcont.tendsto 4).mono_left nhdsWithin_le_nhds
      simpa using h2
    · filter_upwards [self_mem_nhdsWithin] with α hα
      simp only [Set.mem_Iio] at hα
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, div_eq_zero_iff]
      push_neg
      exact ⟨ne_of_gt (Real.sqrt_pos.mpr (by linarith)), by norm_num⟩
  refine (hslope.comp hu).congr' ?_
  have hpos : ∀ᶠ α : ℝ in nhdsWithin 4 (Set.Iio 4), (0 : ℝ) < α :=
    (eventually_gt_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hpos] with α hα hα0
  simp only [Set.mem_Iio] at hα
  have h4 : (0 : ℝ) < 4 - α := by linarith
  have hupos : 0 < Real.sqrt (4 - α) / 2 := by
    have := Real.sqrt_pos.mpr h4; linarith
  have hs0 : 0 ≤ Real.sqrt α / 2 := by positivity
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsq : Real.sqrt (1 - (Real.sqrt α / 2) ^ 2) = Real.sqrt (4 - α) / 2 := by
    rw [div_pow, Real.sq_sqrt hα0.le, show 1 - α / 2 ^ 2 = (4 - α) / 4 by ring,
      Real.sqrt_div h4.le, hsqrt4]
  rw [Real.arccos_eq_arcsin hs0, hsq]
  simp only [Function.comp_apply, slope_def_field, Real.arcsin_zero, sub_zero]
  rw [show Real.sqrt (4 - α) = 2 * (Real.sqrt (4 - α) / 2) by ring]
  field_simp
  ring

/-! ## Deterministic ingredients of the general upper-edge analysis -/

/-- `min_c Σ_j (x_j - c)² = Σ_j (x_j - x̄)²`: the sum of squared deviations is minimal at
the mean. -/
theorem sum_sq_sub_mean_le {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (c : ℝ) :
    ∑ j, (x j - (∑ i, x i) / n) ^ 2 ≤ ∑ j, (x j - c) ^ 2 := by
  set m := (∑ i, x i) / n with hm
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsum : ∑ j, (x j - m) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hm]
    field_simp
    ring
  have key : ∑ j, (x j - c) ^ 2
      = ∑ j, ((x j - m) ^ 2 + 2 * (m - c) * (x j - m) + (m - c) ^ 2) :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [key, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
  simp
  positivity

/-- `det (I_m - J_m / (m+1)) = 1 / (m+1)`, i.e. with `m = n - 1`, `det A = 1/n`. -/
theorem det_one_sub_smul_ones (m : ℕ) :
    Matrix.det ((1 : Matrix (Fin m) (Fin m) ℝ)
        - ((m : ℝ) + 1)⁻¹ • (Matrix.of fun _ _ => (1 : ℝ))) = ((m : ℝ) + 1)⁻¹ := by
  have h : ((1 : Matrix (Fin m) (Fin m) ℝ) - ((m : ℝ) + 1)⁻¹ • (Matrix.of fun _ _ => (1 : ℝ)))
      = 1 + Matrix.replicateCol (Fin 1) (fun _ : Fin m => -((m : ℝ) + 1)⁻¹)
            * Matrix.replicateRow (Fin 1) (fun _ : Fin m => (1 : ℝ)) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply, sub_eq_add_neg]
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  simp [dotProduct]
  field_simp
  ring

end Q788
