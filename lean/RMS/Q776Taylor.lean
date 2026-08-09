import RMS.Q776Gauss

/-!
# Q776 — Taylor expansion of the torus phase at the dominant saddle

At the dominant saddle `θ = 0` the torus phase satisfies

`S θ = (d+1) - Q θ / 2 - i (cubForm θ)/6 + E θ`,  `‖E θ‖ ≤ (1+d²)/12 (sqNorm θ)²`,

together with the elementary algebraic bounds on `quadForm`, `cubForm` and `sqNorm`
and the parity (oddness) of the cubic term that are needed for the local Laplace
estimate.
-/

open scoped Real Nat
open Complex MeasureTheory

namespace Q776

/-! ## An elementary exponential bound -/

/-- `‖exp X - 1 - X‖ ≤ ‖X‖²/2 · e^{‖X‖}`, valid for every complex `X`. -/
theorem norm_exp_sub_one_sub_self_le (X : ℂ) :
    ‖Complex.exp X - 1 - X‖ ≤ ‖X‖^2/2 * Real.exp ‖X‖ := by
  have hs : Summable (fun n : ℕ => X^n / (n ! : ℂ)) := NormedSpace.expSeries_div_summable X
  have hs1 : Summable (fun n : ℕ => X^(n+1) / ((n+1)! : ℂ)) := by
    simpa using (summable_nat_add_iff 1).2 hs
  have hexp : Complex.exp X = ∑' n : ℕ, X^n / (n ! : ℂ) := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  have key : Complex.exp X - 1 - X = ∑' n : ℕ, X^(n+2)/((n+2)! : ℂ) := by
    rw [hexp, hs.tsum_eq_zero_add, hs1.tsum_eq_zero_add]
    norm_num
  have hr : Summable (fun n : ℕ => ‖X‖^n / (n ! : ℝ)) := Real.summable_pow_div_factorial _
  have hrb : Summable (fun n : ℕ => ‖X‖^2/2 * (‖X‖^n / (n ! : ℝ))) := hr.mul_left _
  have hterm : ∀ n : ℕ, ‖X^(n+2)/((n+2)! : ℂ)‖ ≤ ‖X‖^2/2 * (‖X‖^n / (n ! : ℝ)) := by
    intro n
    rw [norm_div, norm_pow, Complex.norm_natCast, div_le_iff₀ (by positivity)]
    have h1 : (((n+2)! : ℕ) : ℝ) = ((n:ℝ)+2)*((n:ℝ)+1)*(n ! : ℝ) := by
      rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
    have h2 : ‖X‖^(n+2) = ‖X‖^2 * ‖X‖^n := by ring
    rw [h1, h2]
    have hfac : (0:ℝ) < (n ! : ℝ) := by positivity
    have he : ‖X‖ ^ 2 / 2 * (‖X‖ ^ n / (n ! :ℝ)) * (((n:ℝ) + 2) * ((n:ℝ) + 1) * (n ! : ℝ))
        = (‖X‖^2 * ‖X‖^n) * ((((n:ℝ)+2)*((n:ℝ)+1))/2) := by field_simp
    rw [he]
    have hpos : (0:ℝ) ≤ ‖X‖^2 * ‖X‖^n := by positivity
    have hge : (1:ℝ) ≤ ((n:ℝ)+2)*((n:ℝ)+1)/2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith [hpos, hge]
  have hnormsum : Summable (fun n : ℕ => ‖X^(n+2)/((n+2)! : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hrb
  rw [key]
  calc ‖∑' n : ℕ, X^(n+2)/((n+2)! : ℂ)‖ ≤ ∑' n : ℕ, ‖X^(n+2)/((n+2)! : ℂ)‖ :=
        norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ, ‖X‖^2/2 * (‖X‖^n / (n ! : ℝ)) := hnormsum.tsum_le_tsum hterm hrb
    _ = ‖X‖^2/2 * Real.exp ‖X‖ := by
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-! ## Growth comparisons -/

theorem exists_pow_le_exp (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ R0 : ℝ, 1 ≤ R0 ∧ ∀ R : ℝ, R0 ≤ R → R ^ k ≤ Real.exp (η * R) := by
  have htend : Filter.Tendsto (fun x : ℝ => x ^ k * Real.exp (-x)) Filter.atTop (nhds 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, x ^ k * Real.exp (-x) ≤ η ^ k := by
    have := htend.eventually_le_const (show (0:ℝ) < η ^ k by positivity)
    exact this
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.1 h1
  refine ⟨max 1 (max A (A/η)), le_max_left _ _, fun R hR => ?_⟩
  have hR1 : (1:ℝ) ≤ R := le_trans (le_max_left _ _) hR
  have hRA : A ≤ η * R := by
    have h2 : A / η ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
    calc A = η * (A/η) := by field_simp
      _ ≤ η * R := by nlinarith
  have := hA (η * R) hRA
  have hexp : (0:ℝ) < Real.exp (η * R) := Real.exp_pos _
  rw [Real.exp_neg] at this
  have hmulpow : (η * R) ^ k = η ^ k * R ^ k := mul_pow _ _ _
  rw [hmulpow] at this
  have hηk : (0:ℝ) < η ^ k := by positivity
  have h3 : η ^ k * R ^ k ≤ η ^ k * Real.exp (η * R) := by
    have h4 : η ^ k * R ^ k * (Real.exp (η * R))⁻¹ ≤ η ^ k := this
    have h5 := mul_le_mul_of_nonneg_right h4 hexp.le
    rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hexp), mul_one] at h5
    exact h5
  exact le_of_mul_le_mul_left h3 hηk

/-- An exponentially small quantity is eventually dominated by any negative power. -/
theorem exists_exp_neg_le_rpow {η s : ℝ} (hη : 0 < η) :
    ∃ R0 : ℝ, 1 ≤ R0 ∧ ∀ R : ℝ, R0 ≤ R → Real.exp (-(η * R)) ≤ R ^ (-s) := by
  obtain ⟨k, hk⟩ := exists_nat_ge s
  obtain ⟨R0, hR0, hpow⟩ := exists_pow_le_exp k hη
  refine ⟨R0, hR0, fun R hR => ?_⟩
  have hR1 : (1:ℝ) ≤ R := le_trans hR0 hR
  have hRpos : (0:ℝ) < R := by linarith
  have h1 : R ^ s ≤ R ^ (k:ℝ) := Real.rpow_le_rpow_of_exponent_le hR1 hk
  have h2 : R ^ (k:ℝ) = R ^ k := Real.rpow_natCast R k
  have h3 : R ^ s ≤ Real.exp (η * R) := by rw [h2] at h1; exact le_trans h1 (hpow R hR)
  have h4 : (0:ℝ) < R ^ s := Real.rpow_pos_of_pos hRpos _
  rw [Real.exp_neg, Real.rpow_neg hRpos.le]
  exact inv_anti₀ h4 h3

/-! ## Elementary bounds on the quadratic and cubic forms -/

theorem sq_le_sqNorm {d : ℕ} (θ : Fin d → ℝ) (j : Fin d) : (θ j)^2 ≤ sqNorm θ :=
  Finset.single_le_sum (f := fun k => (θ k)^2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)

theorem sum_pow_four_le {d : ℕ} (θ : Fin d → ℝ) : ∑ j, (θ j)^4 ≤ (sqNorm θ)^2 := by
  have h : ∀ j ∈ (Finset.univ : Finset (Fin d)), (θ j)^4 ≤ (θ j)^2 * sqNorm θ := by
    intro j _
    have h1 := sq_le_sqNorm θ j
    nlinarith [sq_nonneg (θ j)]
  calc ∑ j, (θ j)^4 ≤ ∑ j, (θ j)^2 * sqNorm θ := Finset.sum_le_sum h
    _ = (sqNorm θ)^2 := by rw [← Finset.sum_mul]; simp only [sqNorm]; ring

theorem sum_pow_six_le {d : ℕ} (θ : Fin d → ℝ) : ∑ j, (θ j)^6 ≤ (sqNorm θ)^3 := by
  have h : ∀ j ∈ (Finset.univ : Finset (Fin d)), (θ j)^6 ≤ (θ j)^2 * (sqNorm θ)^2 := by
    intro j _
    have h1 := sq_le_sqNorm θ j
    have h2 : (0:ℝ) ≤ (θ j)^2 := sq_nonneg _
    have h4 : (θ j)^2 * (θ j)^2 ≤ sqNorm θ * sqNorm θ :=
      mul_le_mul h1 h1 h2 (sqNorm_nonneg θ)
    nlinarith [h4, h2]
  calc ∑ j, (θ j)^6 ≤ ∑ j, (θ j)^2 * (sqNorm θ)^2 := Finset.sum_le_sum h
    _ = (sqNorm θ)^3 := by rw [← Finset.sum_mul]; simp only [sqNorm]; ring

theorem coordSum_sq_le {d : ℕ} (θ : Fin d → ℝ) : (coordSum θ)^2 ≤ (d:ℝ) * sqNorm θ := by
  have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := θ)
  simpa [coordSum, sqNorm] using this

theorem abs_coordSum_le {d : ℕ} {θ : Fin d → ℝ} {δ : ℝ} (hθ : ∀ j, |θ j| ≤ δ) :
    |coordSum θ| ≤ (d:ℝ) * δ := by
  calc |coordSum θ| ≤ ∑ j, |θ j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, δ := Finset.sum_le_sum fun j _ => hθ j
    _ = (d:ℝ) * δ := by simp [mul_comm]

theorem sqNorm_le_of_box {d : ℕ} {θ : Fin d → ℝ} {δ : ℝ} (hθ : ∀ j, |θ j| ≤ δ) :
    sqNorm θ ≤ (d:ℝ) * δ^2 := by
  calc sqNorm θ = ∑ j, (θ j)^2 := rfl
    _ ≤ ∑ _j : Fin d, δ^2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have := hθ j
        nlinarith [abs_nonneg (θ j), sq_abs (θ j)]
    _ = (d:ℝ) * δ^2 := by simp [mul_comm]

theorem abs_cubForm_le {d : ℕ} {θ : Fin d → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hθ : ∀ j, |θ j| ≤ δ) :
    |cubForm θ| ≤ (1 + (d:ℝ)^2) * δ * sqNorm θ := by
  have hA : |∑ j, (θ j)^3| ≤ δ * sqNorm θ := by
    calc |∑ j, (θ j)^3| ≤ ∑ j, |(θ j)^3| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, δ * (θ j)^2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h1 := hθ j
          have h2 : |(θ j)^3| = |θ j| * (θ j)^2 := by
            rw [abs_pow]
            nlinarith [sq_abs (θ j), abs_nonneg (θ j)]
          rw [h2]
          nlinarith [sq_nonneg (θ j)]
      _ = δ * sqNorm θ := by rw [← Finset.mul_sum]; rfl
  have hB : |(coordSum θ)^3| ≤ (d:ℝ)^2 * δ * sqNorm θ := by
    have h1 : |coordSum θ| ≤ (d:ℝ) * δ := abs_coordSum_le hθ
    have h2 : (coordSum θ)^2 ≤ (d:ℝ) * sqNorm θ := coordSum_sq_le θ
    have h3 : |(coordSum θ)^3| = |coordSum θ| * (coordSum θ)^2 := by
      rw [abs_pow]
      nlinarith [sq_abs (coordSum θ), abs_nonneg (coordSum θ)]
    rw [h3]
    have h4 : (0:ℝ) ≤ (coordSum θ)^2 := sq_nonneg _
    have h5 : (0:ℝ) ≤ (d:ℝ) * δ := by positivity
    nlinarith [abs_nonneg (coordSum θ), sqNorm_nonneg θ, Nat.cast_nonneg (α := ℝ) d]
  have : |cubForm θ| ≤ |∑ j, (θ j)^3| + |(coordSum θ)^3| := by
    rw [cubForm]
    exact abs_sub _ _
  nlinarith [this, hA, hB]

theorem cubForm_sq_le {d : ℕ} (θ : Fin d → ℝ) :
    (cubForm θ)^2 ≤ 2 * ((d:ℝ) + (d:ℝ)^3) * (sqNorm θ)^3 := by
  have hA : (∑ j, (θ j)^3)^2 ≤ (d:ℝ) * (sqNorm θ)^3 := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun j => (θ j)^3)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    have h2 : ∑ j, ((θ j)^3)^2 = ∑ j, (θ j)^6 := by
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [h2] at h1
    have h3 := sum_pow_six_le θ
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hB : ((coordSum θ)^3)^2 ≤ (d:ℝ)^3 * (sqNorm θ)^3 := by
    have h1 : (coordSum θ)^2 ≤ (d:ℝ) * sqNorm θ := coordSum_sq_le θ
    have h2 : (0:ℝ) ≤ (coordSum θ)^2 := sq_nonneg _
    have h3 : ((coordSum θ)^3)^2 = ((coordSum θ)^2)^3 := by ring
    have h4 : (0:ℝ) ≤ (d:ℝ) * sqNorm θ := by
      have := sqNorm_nonneg θ; positivity
    rw [h3]
    calc ((coordSum θ)^2)^3 ≤ ((d:ℝ) * sqNorm θ)^3 := by
          exact pow_le_pow_left₀ h2 h1 3
      _ = (d:ℝ)^3 * (sqNorm θ)^3 := by ring
  have hexp : (cubForm θ)^2 = (∑ j, (θ j)^3)^2 - 2*(∑ j, (θ j)^3)*(coordSum θ)^3
      + ((coordSum θ)^3)^2 := by
    rw [cubForm]; ring
  nlinarith [hA, hB, sq_nonneg ((∑ j, (θ j)^3) + (coordSum θ)^3),
    sq_nonneg ((∑ j, (θ j)^3) - (coordSum θ)^3)]

/-! ## The Taylor expansion of the torus phase -/

/-- The fourth-order Taylor bound for `e^{iv}`. -/
theorem exp_I_taylor {v : ℝ} (hv : |v| ≤ 1) :
    ‖Complex.exp ((v:ℂ) * I) - (1 + (v:ℂ)*I - (v:ℂ)^2/2 - I*(v:ℂ)^3/6)‖ ≤ v^4/12 := by
  have hx : ‖(v:ℂ)*I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hv
  have h := Complex.exp_bound hx (n := 4) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 4, ((v:ℂ)*I)^m / (m ! : ℂ)
      = 1 + (v:ℂ)*I - (v:ℂ)^2/2 - I*(v:ℂ)^3/6 := by
    simp [Finset.sum_range_succ, Complex.I_sq, Complex.I_pow_four, pow_succ, Nat.factorial]
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [hsum] at h
  refine le_trans h ?_
  have hnx : ‖(v:ℂ)*I‖ = |v| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h4 : |v|^4 = v^4 := by
    rw [← abs_pow]
    exact abs_of_nonneg (by positivity)
  rw [hnx, h4]
  have hv4 : (0:ℝ) ≤ v^4 := by positivity
  have hconst : ((Nat.succ 4 : ℕ) : ℝ) * ((((4:ℕ)!) : ℝ) * ((4:ℕ) : ℝ))⁻¹ ≤ 1/12 := by
    norm_num [Nat.factorial]
  nlinarith [hv4, hconst]

/-- The Taylor expansion of the torus phase at the dominant saddle `θ = 0`. -/
theorem taylor_bound {d : ℕ} {θ : Fin d → ℝ} (hθ : ∀ j, |θ j| ≤ 1) (hs : |coordSum θ| ≤ 1) :
    ‖torusPhase θ - ((d:ℂ)+1) + ((quadForm θ : ℝ):ℂ)/2 + I * ((cubForm θ : ℝ):ℂ)/6‖
      ≤ (1 + (d:ℝ)^2)/12 * (sqNorm θ)^2 := by
  set G : ℝ → ℂ := fun v => Complex.exp ((v:ℂ) * I) - (1 + (v:ℂ)*I - (v:ℂ)^2/2 - I*(v:ℂ)^3/6)
    with hGdef
  have hsum : ∀ s : Finset (Fin d), ∑ j ∈ s, G (θ j)
      = (∑ j ∈ s, Complex.exp ((θ j : ℂ)*I)) - (s.card : ℂ) - I*(∑ j ∈ s, (θ j : ℂ))
        + (∑ j ∈ s, (θ j : ℂ)^2)/2 + I*(∑ j ∈ s, (θ j : ℂ)^3)/6 := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
          Finset.sum_insert ha, Finset.sum_insert ha, ih, Finset.card_insert_of_notMem ha]
        simp only [hGdef]
        push_cast
        ring
  have hkey : torusPhase θ - ((d:ℂ)+1) + ((quadForm θ : ℝ):ℂ)/2 + I * ((cubForm θ : ℝ):ℂ)/6
      = (∑ j, G (θ j)) + G (-(coordSum θ)) := by
    rw [hsum Finset.univ]
    simp only [Finset.card_univ, Fintype.card_fin, hGdef, torusPhase, quadForm, cubForm, coordSum]
    push_cast
    ring_nf
    simp only [show ∀ x : ℝ, Complex.exp ((x:ℂ) * I) = Complex.exp (I * (x:ℂ)) from
      fun x => by rw [mul_comm]]
    ring
  rw [hkey]
  have hbound : ‖(∑ j, G (θ j)) + G (-(coordSum θ))‖ ≤ (∑ j, ‖G (θ j)‖) + ‖G (-(coordSum θ))‖ :=
    le_trans (norm_add_le _ _) (by gcongr; exact norm_sum_le _ _)
  refine le_trans hbound ?_
  have h1 : ∀ j, ‖G (θ j)‖ ≤ (θ j)^4/12 := fun j => exp_I_taylor (hθ j)
  have h2 : ‖G (-(coordSum θ))‖ ≤ (coordSum θ)^4/12 := by
    have := exp_I_taylor (v := -(coordSum θ)) (by rwa [abs_neg])
    calc ‖G (-(coordSum θ))‖ ≤ (-(coordSum θ))^4/12 := this
      _ = (coordSum θ)^4/12 := by ring
  have h3 : ∑ j, ‖G (θ j)‖ ≤ (sqNorm θ)^2/12 := by
    calc ∑ j, ‖G (θ j)‖ ≤ ∑ j, (θ j)^4/12 := Finset.sum_le_sum fun j _ => h1 j
      _ = (∑ j, (θ j)^4)/12 := by rw [Finset.sum_div]
      _ ≤ (sqNorm θ)^2/12 := by linarith [sum_pow_four_le θ]
  have h4 : (coordSum θ)^4 ≤ (d:ℝ)^2 * (sqNorm θ)^2 := by
    have h5 : (coordSum θ)^2 ≤ (d:ℝ) * sqNorm θ := coordSum_sq_le θ
    have h6 : (0:ℝ) ≤ (coordSum θ)^2 := sq_nonneg _
    nlinarith [sqNorm_nonneg θ, Nat.cast_nonneg (α := ℝ) d]
  linarith [h2, h3, h4]

/-! ## Parity -/

theorem sqNorm_neg {d : ℕ} (θ : Fin d → ℝ) : sqNorm (-θ) = sqNorm θ := by
  simp [sqNorm]

theorem coordSum_neg {d : ℕ} (θ : Fin d → ℝ) : coordSum (-θ) = -coordSum θ := by
  simp [coordSum, Finset.sum_neg_distrib]

theorem quadForm_neg {d : ℕ} (θ : Fin d → ℝ) : quadForm (-θ) = quadForm θ := by
  simp [quadForm, coordSum_neg]

theorem cubForm_neg {d : ℕ} (θ : Fin d → ℝ) : cubForm (-θ) = -cubForm θ := by
  simp only [cubForm, coordSum_neg]
  rw [show ∑ j, ((-θ) j)^3 = ∑ j, -((θ j)^3) from Finset.sum_congr rfl fun j _ => by
    simp; ring]
  rw [Finset.sum_neg_distrib]
  ring

theorem box_neg_preimage (d : ℕ) (δ : ℝ) :
    (fun y : Fin d → ℝ => -y) ⁻¹' (box d δ) = box d δ := by
  ext u
  simp only [box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Icc, Pi.neg_apply,
    forall_true_left]
  constructor
  · intro h j
    have := h j
    constructor <;> linarith [this.1, this.2]
  · intro h j
    have := h j
    constructor <;> linarith [this.1, this.2]

/-- The cubic term integrates to zero over the (symmetric) box, by parity. -/
theorem integral_box_cubForm_zero {d : ℕ} (δ : ℝ) (b : ℂ) :
    (∫ θ in box d δ, Complex.exp (-b * ((quadForm θ : ℝ):ℂ)) * ((cubForm θ : ℝ):ℂ)) = 0 := by
  set F : (Fin d → ℝ) → ℂ :=
    fun θ => Complex.exp (-b * ((quadForm θ : ℝ):ℂ)) * ((cubForm θ : ℝ):ℂ) with hF
  have hodd : ∀ θ : Fin d → ℝ, F (-θ) = -F θ := by
    intro θ
    simp only [hF, quadForm_neg, cubForm_neg]
    push_cast
    ring
  have hrefl : (∫ θ in box d δ, F θ) = ∫ θ in box d δ, F (-θ) := by
    have := (Measure.measurePreserving_neg (volume : Measure (Fin d → ℝ))).setIntegral_preimage_emb
      (measurableEmbedding_neg) F (box d δ)
    rw [box_neg_preimage d δ] at this
    exact this.symm
  have h2 : (∫ θ in box d δ, F (-θ)) = -∫ θ in box d δ, F θ := by
    rw [show (fun θ : Fin d → ℝ => F (-θ)) = fun θ => -F θ from funext hodd, integral_neg]
  rw [h2] at hrefl
  have h5 : (2:ℂ) * (∫ θ in box d δ, F θ) = 0 := by linear_combination hrefl
  rcases mul_eq_zero.mp h5 with h | h
  · norm_num at h
  · exact h
