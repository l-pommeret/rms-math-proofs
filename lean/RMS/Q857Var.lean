import RMS.Q857Aux

/-!
# Q857 — the variational (structural) theorem for a nearest determinant-`τ` matrix

This module proves Lemma 3.1 of the source note by an elementary variational argument that
avoids nuclear-norm duality and nonsmooth Lagrange multipliers.

Let `M` minimize `‖A - X‖` among matrices with `det X = det M ≠ 0`, and put `E = A - M`,
`r = ‖E‖ > 0`.

* `Q857.exists_better_diag` is the descent step: in the frame in which `E` is diagonal, if the
  smallest singular value of `E` is smaller than the largest one, then moving along `E` and
  correcting the determinant by a rank-one matrix supported on the smallest singular direction
  strictly decreases the distance.
* `Q857.svals_eq_norm_of_min` concludes that all singular values of `E` are equal to `r`, hence
  `Q857.exists_unitary_of_min`: `E = r • Q` with `Q` unitary.
* `Q857.trace_ne_zero_of_min` is the second variational step: if `K + Kᴴ` is (uniformly)
  positive definite, then `tr (M⁻¹ Q K) ≠ 0`.
* `Q857.exists_hermitian_of_trace_cond` turns that condition into the algebraic statement
  `M⁻¹ Q = ζ • S` with `S` Hermitian, and `Q857.exists_structure_of_min` records the
  resulting form `Qᴴ M = α • P`, `P` Hermitian.
-/

namespace Q857

open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {n : ℕ}

lemma app_smul {𝕜 : Type*} [RCLike 𝕜] (c : 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (x : EuclideanSpace 𝕜 (Fin n)) : app (c • A) x = c • app A x := by
  simp [app, map_smul]

/-- Coordinatewise estimate for the descent direction: the matrix
`(1-t) • diag s - D`, where `D` has range the last coordinate axis, is small. -/
lemma norm_sq_descent (hn : 0 < n) (s : Fin n → ℝ) (hs : ∀ i, 0 ≤ s i) (hanti : Antitone s)
    (t : ℝ) (ht1 : t ≤ 1) (z : EuclideanSpace ℂ (Fin n)) (D : Matrix (Fin n) (Fin n) ℂ)
    (hD : ∀ w, app D w = (inner ℂ z w : ℂ) • (EuclideanSpace.single (⟨n-1, by omega⟩ : Fin n) (1:ℂ)))
    (w : EuclideanSpace ℂ (Fin n)) :
    ‖app ((((1-t : ℝ)):ℂ) • diagonal (fun i => ((s i:ℝ):ℂ)) - D) w‖^2
      ≤ (1-t)^2 * (s ⟨0,hn⟩)^2 * (‖w‖^2 - ‖(WithLp.ofLp w) ⟨n-1, by omega⟩‖^2)
        + ((1-t) * s ⟨n-1, by omega⟩ * ‖(WithLp.ofLp w) ⟨n-1, by omega⟩‖ + ‖z‖*‖w‖)^2 := by
  classical
  set j : Fin n := ⟨n-1, by omega⟩ with hj
  set c : ℂ := inner ℂ z w with hc
  set a : ℝ := 1 - t with ha
  have ha0 : 0 ≤ a := by simp only [ha]; linarith
  set x : Fin n → ℂ := WithLp.ofLp w with hx
  set F : Matrix (Fin n) (Fin n) ℂ :=
    (((a : ℝ)):ℂ) • diagonal (fun i => ((s i:ℝ):ℂ)) - D with hF
  have hcoord : ∀ i, (WithLp.ofLp (app F w)) i
      = ((a:ℝ):ℂ) * ((s i:ℝ):ℂ) * x i - (if i = j then c else 0) := by
    intro i
    rw [hF, app_sub, app_smul, hD w]
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    have h1 : (WithLp.ofLp (app (diagonal (fun i => ((s i:ℝ):ℂ))) w)) i
        = ((s i:ℝ):ℂ) * x i := by simp [app, Matrix.mulVec_diagonal, hx]
    rw [h1]
    simp [EuclideanSpace.single_apply, mul_assoc, hc]
  have hnormsum : ‖app F w‖^2 = ∑ i, ‖(WithLp.ofLp (app F w)) i‖^2 :=
    EuclideanSpace.norm_sq_eq _
  have hwsum : ‖w‖^2 = ∑ i, ‖x i‖^2 := EuclideanSpace.norm_sq_eq _
  have hsplit : ∑ i, ‖(WithLp.ofLp (app F w)) i‖^2
      = (∑ i ∈ Finset.univ.erase j, ‖(WithLp.ofLp (app F w)) i‖^2)
        + ‖(WithLp.ofLp (app F w)) j‖^2 :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm
  have hwsplit : ∑ i ∈ Finset.univ.erase j, ‖x i‖^2 = ‖w‖^2 - ‖x j‖^2 := by
    rw [hwsum, ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]; ring
  have hr : ∀ i, s i ≤ s ⟨0, hn⟩ := by
    intro i; exact hanti (by simp [Fin.le_def])
  have hoff : ∀ i ∈ Finset.univ.erase j, ‖(WithLp.ofLp (app F w)) i‖^2
      ≤ a^2 * (s ⟨0,hn⟩)^2 * ‖x i‖^2 := by
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    rw [hcoord i, if_neg hij, sub_zero, norm_mul, norm_mul, mul_pow, mul_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hsq : (s i)^2 ≤ (s ⟨0,hn⟩)^2 := by nlinarith [hs i, hr i]
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq (sq_nonneg a)) (sq_nonneg ‖x i‖)
    linarith
  have hlast : ‖(WithLp.ofLp (app F w)) j‖ ≤ a * s j * ‖x j‖ + ‖z‖ * ‖w‖ := by
    rw [hcoord j, if_pos rfl]
    refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
    · rw [norm_mul, norm_mul]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0, abs_of_nonneg (hs j)]
      exact le_rfl
    · rw [hc]; exact norm_inner_le_norm _ _
  have hstep := add_le_add (Finset.sum_le_sum hoff)
    (pow_le_pow_left₀ (norm_nonneg ((WithLp.ofLp (app F w)) j)) hlast 2)
  rw [← Finset.mul_sum, hwsplit] at hstep
  rw [hnormsum, hsplit]
  exact hstep

/-- The scalar inequality behind the descent step. -/
lemma descent_scalar_bound (r g κ t W b : ℝ) (hr : 0 < r) (hg0 : 0 ≤ g) (hgr : g < r) :
    (1-t)^2*r^2*(W^2-b^2) + ((1-t)*g*b + κ*W)^2
      ≤ ((1-t)^2*r^2 + (1 + 2*r^2/(r^2-g^2))*κ^2) * W^2 := by
  set d : ℝ := r^2 - g^2 with hd
  have hd0 : 0 < d := by rw [hd]; nlinarith
  have hC : (1 + 2*r^2/d) * d = d + 2*r^2 := by field_simp
  nlinarith [sq_nonneg ((1-t)*b*d - g*κ*W), sq_nonneg κ, sq_nonneg W, sq_nonneg (κ*W),
    mul_pos hd0 hd0, sq_nonneg (1-t), hC, hd0]

/-- The final scalar inequality: the perturbed norm is strictly smaller. -/
lemma descent_final_bound (r C K κ t : ℝ) (hC0 : 0 < C)
    (hκ0 : 0 ≤ κ) (ht0 : 0 < t) (ht1 : t ≤ 1) (hz : κ ≤ K*t)
    (ht3 : t ≤ r^2/(C*(K^2+1))) : (1-t)^2*r^2 + C*κ^2 < r^2 := by
  have h2 : C*(K^2+1)*t ≤ r^2 := by
    rw [le_div_iff₀ (by positivity)] at ht3
    nlinarith
  have e0 : κ^2 ≤ (K*t)^2 := by
    have := mul_self_le_mul_self hκ0 hz
    nlinarith
  have e1 : C * κ^2 ≤ C * (K*t)^2 := mul_le_mul_of_nonneg_left e0 hC0.le
  have e3 : C*K^2*t ≤ r^2 - C*t := by nlinarith
  have e4 : C*K^2*t^2 ≤ (r^2 - C*t)*t := by nlinarith
  have e5 : 0 ≤ t * r^2 * (1-t) := by
    apply mul_nonneg (mul_nonneg ht0.le (sq_nonneg r)); linarith
  have e6 : 0 < C * t^2 := by positivity
  nlinarith

/-- **Descent step.**  In the frame where the perturbation is the nonnegative sorted diagonal
matrix `S = diag s`, if `s` is not constant then `M` is not a nearest matrix with determinant
`det M`. -/
theorem exists_better_diag (hn : 0 < n) (s : Fin n → ℝ) (hs : ∀ i, 0 ≤ s i) (hanti : Antitone s)
    (hlt : s ⟨n - 1, by omega⟩ < s ⟨0, hn⟩) (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, X.det = M.det ∧
      ‖(M + diagonal (fun i => ((s i : ℝ) : ℂ))) - X‖ < s ⟨0, hn⟩ := by
  classical
  set j : Fin n := ⟨n - 1, by omega⟩ with hjdef
  set r : ℝ := s ⟨0, hn⟩ with hrdef
  set g : ℝ := s j with hgdef
  have hg0 : 0 ≤ g := hs j
  have hr0 : 0 < r := lt_of_le_of_lt hg0 hlt
  set S : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => ((s i : ℝ) : ℂ)) with hSdef
  obtain ⟨K₁, hK₁0, hK₁⟩ := det_add_smul_bound M S hM
  have hd0 : 0 < r^2 - g^2 := by nlinarith
  set C : ℝ := 1 + 2*r^2/(r^2 - g^2) with hCdef
  have hC0 : 0 < C := by rw [hCdef]; positivity
  set Kn : ℝ := ‖M‖ + ‖S‖ with hKndef
  have hKn0 : 0 ≤ Kn := by positivity
  have hdM : 0 < ‖M.det‖ := norm_pos_iff.mpr hM
  set K : ℝ := (2*K₁/‖M.det‖) * Kn with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  set t : ℝ := min (min 1 (‖M.det‖/(2*(K₁+1)))) (r^2/(C*(K^2+1))) with htdef
  have ht0 : 0 < t := by
    rw [htdef]; refine lt_min (lt_min one_pos ?_) ?_ <;> positivity
  have ht1 : t ≤ 1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have ht2 : t ≤ ‖M.det‖/(2*(K₁+1)) := le_trans (min_le_left _ _) (min_le_right _ _)
  have ht3 : t ≤ r^2/(C*(K^2+1)) := min_le_right _ _
  set Mt : Matrix (Fin n) (Fin n) ℂ := M + (t : ℂ) • S with hMtdef
  have hdiff : ‖Mt.det - M.det‖ ≤ K₁ * t := hK₁ t (le_of_lt ht0) ht1
  have hhalf : K₁ * t ≤ ‖M.det‖/2 := by
    refine le_trans (mul_le_mul_of_nonneg_left ht2 hK₁0) ?_
    have h : K₁ * (‖M.det‖/(2*(K₁+1))) = (K₁*‖M.det‖)/(2*(K₁+1)) := by ring
    rw [h, div_le_iff₀ (by positivity : (0:ℝ) < 2*(K₁+1))]
    nlinarith
  have hMtlow : ‖M.det‖/2 ≤ ‖Mt.det‖ := by
    have h1 : ‖M.det‖ - ‖Mt.det‖ ≤ ‖M.det - Mt.det‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev] at h1
    linarith
  have hMtpos : 0 < ‖Mt.det‖ := lt_of_lt_of_le (by positivity) hMtlow
  have hMtne : Mt.det ≠ 0 := norm_pos_iff.mp hMtpos
  set β : ℂ := M.det/Mt.det - 1 with hβdef
  have hβeq : β * Mt.det = M.det - Mt.det := by rw [hβdef]; field_simp
  have hβbound : ‖β‖ ≤ (2*K₁/‖M.det‖) * t := by
    have h1 : ‖β‖ * ‖Mt.det‖ = ‖Mt.det - M.det‖ := by rw [← norm_mul, hβeq, norm_sub_rev]
    have h2 : ‖β‖ * (‖M.det‖/2) ≤ ‖β‖ * ‖Mt.det‖ :=
      mul_le_mul_of_nonneg_left hMtlow (norm_nonneg β)
    rw [h1] at h2
    have h3 : ‖β‖ * (‖M.det‖/2) ≤ K₁ * t := le_trans h2 hdiff
    rw [div_mul_eq_mul_div, le_div_iff₀ hdM]
    linarith
  set v : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j (1:ℂ) with hvdef
  have hv : ‖v‖ = 1 := by rw [hvdef]; simp
  obtain ⟨z, D, hdetfix, hzbound, hDact⟩ := exists_det_fix Mt hMtne v hv β
  refine ⟨Mt + D, ?_, ?_⟩
  · rw [hdetfix, hβdef]; field_simp; ring
  have hMtnorm : ‖Mt‖ ≤ Kn := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul]
    have hts : ‖(t:ℂ)‖ = t := by simp [abs_of_nonneg ht0.le]
    rw [hts, hKndef]
    nlinarith [norm_nonneg S]
  have hz : ‖z‖ ≤ K * t := by
    refine le_trans hzbound ?_
    calc ‖β‖ * ‖Mt‖ ≤ ((2*K₁/‖M.det‖) * t) * Kn :=
          mul_le_mul hβbound hMtnorm (norm_nonneg _) (by positivity)
      _ = K * t := by rw [hKdef]; ring
  have hFeq : (M + S) - (Mt + D) = (((1-t : ℝ)):ℂ) • S - D := by
    rw [hMtdef]; push_cast; module
  rw [hFeq, hSdef]
  set κ : ℝ := ‖z‖ with hκ
  set c : ℝ := Real.sqrt ((1-t)^2*r^2 + C*κ^2) with hc
  have hcarg : 0 ≤ (1-t)^2*r^2 + C*κ^2 := by positivity
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcsq : c^2 = (1-t)^2*r^2 + C*κ^2 := Real.sq_sqrt hcarg
  have hbound : ‖(((1-t : ℝ)):ℂ) • diagonal (fun i => ((s i:ℝ):ℂ)) - D‖ ≤ c := by
    refine opNorm_le_of_forall hc0 (fun w => ?_)
    refine le_of_sq_le_sq' ?_ (by positivity)
    have h1 := norm_sq_descent hn s hs hanti t ht1 z D hDact w
    have h2 := descent_scalar_bound r g κ t ‖w‖ ‖(WithLp.ofLp w) j‖ hr0 hg0 hlt
    calc ‖app ((((1-t : ℝ)):ℂ) • diagonal (fun i => ((s i:ℝ):ℂ)) - D) w‖^2
        ≤ (1-t)^2 * r^2 * (‖w‖^2 - ‖(WithLp.ofLp w) j‖^2)
          + ((1-t) * g * ‖(WithLp.ofLp w) j‖ + κ*‖w‖)^2 := h1
      _ ≤ ((1-t)^2*r^2 + C*κ^2) * ‖w‖^2 := h2
      _ = (c * ‖w‖)^2 := by rw [mul_pow, hcsq]
  refine lt_of_le_of_lt hbound ?_
  have hsq : c^2 < r^2 := by
    rw [hcsq]
    exact descent_final_bound r C K κ t hC0 (norm_nonneg z) ht0 ht1 hz ht3
  exact lt_of_pow_lt_pow_left₀ 2 hr0.le hsq

/-- **All singular values of the optimal perturbation are equal.** -/
theorem svals_eq_norm_of_min (hn : 0 < n) (A M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0)
    (hmin : ∀ X : Matrix (Fin n) (Fin n) ℂ, X.det = M.det → ‖A - M‖ ≤ ‖A - X‖) (i : Fin n) :
    svals (A - M) i = ‖A - M‖ := by
  classical
  set E : Matrix (Fin n) (Fin n) ℂ := A - M with hE
  set s : Fin n → ℝ := svals E with hsdef
  have hs : ∀ i, 0 ≤ s i := svals_nonneg E
  have hanti : Antitone s := svals_antitone E
  have htop : s ⟨0, hn⟩ = ‖E‖ := svals_zero_eq_norm hn E
  have hkey : ¬ (s ⟨n-1, by omega⟩ < s ⟨0, hn⟩) := by
    intro hlt
    obtain ⟨U, V, hU, hV, hEsvd0⟩ := exists_svd_svals E
    have hEsvd : E = U * diagonal (fun i => ((s i : ℝ) : ℂ)) * Vᴴ := hEsvd0
    have hV' : Vᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
      have := Unitary.star_mem hV; rwa [Matrix.star_eq_conjTranspose] at this
    have hUU : Uᴴ * U = 1 := by have := hU.1; rwa [Matrix.star_eq_conjTranspose] at this
    have hVV : Vᴴ * V = 1 := by have := hV.1; rwa [Matrix.star_eq_conjTranspose] at this
    have hUU' : U * Uᴴ = 1 := by have := hU.2; rwa [Matrix.star_eq_conjTranspose] at this
    have hVV' : V * Vᴴ = 1 := by have := hV.2; rwa [Matrix.star_eq_conjTranspose] at this
    set M' : Matrix (Fin n) (Fin n) ℂ := Uᴴ * M * V with hM'
    have hM'det : M'.det ≠ 0 := by
      rw [hM', Matrix.det_mul, Matrix.det_mul]
      have h1 : Uᴴ.det ≠ 0 := by
        intro h
        have hz : (Uᴴ * U).det = 0 := by rw [Matrix.det_mul, h, zero_mul]
        rw [hUU, Matrix.det_one] at hz; exact one_ne_zero hz
      have h2 : V.det ≠ 0 := by
        intro h
        have hz : (Vᴴ * V).det = 0 := by rw [Matrix.det_mul, h, mul_zero]
        rw [hVV, Matrix.det_one] at hz; exact one_ne_zero hz
      exact mul_ne_zero (mul_ne_zero h1 hM) h2
    have hAeq : Uᴴ * A * V = M' + diagonal (fun i => ((s i : ℝ) : ℂ)) := by
      have hA : A = M + U * diagonal (fun i => ((s i : ℝ) : ℂ)) * Vᴴ := by
        rw [← hEsvd, hE]; abel
      rw [hA, hM']
      have hexp : Uᴴ * (M + U * diagonal (fun i => ((s i : ℝ) : ℂ)) * Vᴴ) * V
          = Uᴴ * M * V + (Uᴴ * U) * diagonal (fun i => ((s i : ℝ) : ℂ)) * (Vᴴ * V) := by
        noncomm_ring
      rw [hexp, hUU, hVV, one_mul, mul_one]
    obtain ⟨X, hXdet, hXnorm⟩ := exists_better_diag hn s hs hanti hlt M' hM'det
    rw [← hAeq] at hXnorm
    set Y : Matrix (Fin n) (Fin n) ℂ := U * X * Vᴴ with hY
    have hYdet : Y.det = M.det := by
      rw [hY, Matrix.det_mul, Matrix.det_mul, hXdet, hM', Matrix.det_mul, Matrix.det_mul]
      have e1 : U.det * (Uᴴ.det * M.det * V.det) * Vᴴ.det
          = U.det * Uᴴ.det * M.det * (V.det * Vᴴ.det) := by ring
      rw [e1, ← Matrix.det_mul, hUU', Matrix.det_one, one_mul, ← Matrix.det_mul, hVV',
        Matrix.det_one, mul_one]
    have hAY : A - Y = U * ((Uᴴ * A * V) - X) * Vᴴ := by
      rw [hY]
      have hexp2 : U * ((Uᴴ * A * V) - X) * Vᴴ = (U * Uᴴ) * A * (V * Vᴴ) - U * X * Vᴴ := by
        noncomm_ring
      rw [hexp2, hUU', hVV', one_mul, mul_one]
    have hlt2 : ‖A - Y‖ < ‖A - M‖ := by
      rw [hAY, norm_mul_unitary hn hV', norm_unitary_mul hn hU, ← hE, ← htop]
      exact hXnorm
    exact absurd (hmin Y hYdet) (not_le.mpr hlt2)
  push_neg at hkey
  have hlow : s ⟨n-1, by omega⟩ ≤ s i := hanti (by simp only [Fin.le_def]; omega)
  have hhigh : s i ≤ s ⟨0, hn⟩ := hanti (by simp [Fin.le_def])
  rw [← htop]
  linarith

/-- The optimal perturbation is `r` times a unitary matrix. -/
theorem exists_unitary_of_min (hn : 0 < n) (A M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0)
    (hmin : ∀ X : Matrix (Fin n) (Fin n) ℂ, X.det = M.det → ‖A - M‖ ≤ ‖A - X‖) :
    ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      A - M = ((‖A - M‖ : ℝ) : ℂ) • Q := by
  obtain ⟨Q, hQ, hQeq⟩ :=
    exists_unitary_of_svals_const (A - M) (svals_eq_norm_of_min hn A M hM hmin)
  exact ⟨Q, hQ, hQeq⟩

/-- A rank-one matrix `w ↦ ⟪z, w⟫ • v` with `‖v‖ = 1` has operator norm at most `‖z‖`. -/
lemma opNorm_rankOne_le {z v : EuclideanSpace ℂ (Fin n)}
    (hv : ‖v‖ = 1) {D : Matrix (Fin n) (Fin n) ℂ}
    (hD : ∀ w, app D w = (inner ℂ z w : ℂ) • v) : ‖D‖ ≤ ‖z‖ := by
  refine opNorm_le_of_forall (norm_nonneg z) (fun w => ?_)
  rw [hD w, norm_smul, hv, mul_one]
  exact norm_inner_le_norm _ _

/-- Pointwise estimate for the shifted operator `r • 1 - t • K`. -/
lemma norm_sq_shift_bound (r t δ : ℝ) (K : Matrix (Fin n) (Fin n) ℂ)
    (hr : 0 < r) (ht0 : 0 < t)
    (hK : ∀ y : EuclideanSpace ℂ (Fin n), δ * ‖y‖ ^ 2 ≤ (inner ℂ y (app K y) : ℂ).re)
    (y : EuclideanSpace ℂ (Fin n)) :
    ‖app (((r:ℝ):ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (t:ℂ) • K) y‖^2
      ≤ (r^2 - 2*r*t*δ + t^2*‖K‖^2) * ‖y‖^2 := by
  rw [app_sub, app_smul, app_smul, app_one, norm_sub_sq (𝕜 := ℂ)]
  have h1 : ‖((r:ℝ):ℂ) • y‖^2 = r^2 * ‖y‖^2 := by
    rw [norm_smul]; simp [mul_pow, abs_of_nonneg hr.le]
  have h2 : ‖((t:ℝ):ℂ) • app K y‖^2 ≤ t^2 * (‖K‖^2 * ‖y‖^2) := by
    rw [norm_smul]
    have hb := norm_app_le K y
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0.le]
    have := mul_self_le_mul_self (norm_nonneg (app K y)) hb
    nlinarith [sq_nonneg t]
  have h3 : RCLike.re (inner ℂ (((r:ℝ):ℂ) • y) (((t:ℝ):ℂ) • app K y))
      = r * t * (inner ℂ y (app K y) : ℂ).re := by
    rw [inner_smul_left, inner_smul_right]
    show ((starRingEnd ℂ) ((r:ℝ):ℂ) * (((t:ℝ):ℂ) * inner ℂ y (app K y))).re = _
    simp; ring
  rw [h1, h3]
  have h5 : r*t*(δ*‖y‖^2) ≤ r*t*(inner ℂ y (app K y) : ℂ).re :=
    mul_le_mul_of_nonneg_left (hK y) (mul_pos hr ht0).le
  nlinarith [h2, h5]

/-- The determinant correction is of second order, hence negligible against the first-order
gain. -/
lemma descent_tangent_final (C η t : ℝ) (hC : 0 ≤ C) (hη : 0 < η) (ht : 0 < t)
    (ht5 : t ≤ η/(C+1)) : C*t^2 < t*η := by
  have h1 : C*t ≤ C*(η/(C+1)) := mul_le_mul_of_nonneg_left ht5 hC
  have h2 : C*(η/(C+1)) < η := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Second variational step.**  If the Hermitian part of `K` is uniformly positive definite,
then the direction `Q K` is not tangent to the determinant level set at the minimizer `M`. -/
theorem trace_ne_zero_of_min (hn : 0 < n) (A M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0)
    (hmin : ∀ X : Matrix (Fin n) (Fin n) ℂ, X.det = M.det → ‖A - M‖ ≤ ‖A - X‖)
    {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hr : 0 < ‖A - M‖) (hE : A - M = ((‖A - M‖ : ℝ) : ℂ) • Q)
    (K : Matrix (Fin n) (Fin n) ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hK : ∀ y : EuclideanSpace ℂ (Fin n),
      δ * ‖y‖ ^ 2 ≤ (inner ℂ y (app K y) : ℂ).re) :
    (M⁻¹ * Q * K).trace ≠ 0 := by
  classical
  intro htr0
  set r : ℝ := ‖A - M‖ with hrdef
  set G : Matrix (Fin n) (Fin n) ℂ := Q * K with hG
  have htr : (M⁻¹ * G).trace = 0 := by rw [hG, ← mul_assoc]; exact htr0
  obtain ⟨K₂, hK₂0, hK₂⟩ := det_add_smul_bound_tangent M G hM htr
  set η : ℝ := δ/2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hdM : 0 < ‖M.det‖ := norm_pos_iff.mpr hM
  set Kn : ℝ := ‖M‖ + ‖G‖ with hKn
  have hKn0 : 0 ≤ Kn := by rw [hKn]; positivity
  set C₂ : ℝ := (2*K₂/‖M.det‖) * Kn with hC₂
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  obtain ⟨t, ht0, ht1, ht2, ht3, ht4, ht5⟩ :
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t ≤ ‖M.det‖/(2*(K₂+1)) ∧ t ≤ r*δ/(‖K‖^2+1) ∧
        t ≤ r/(η+1) ∧ t ≤ η/(C₂+1) := by
    refine ⟨min (min 1 (‖M.det‖/(2*(K₂+1))))
      (min (r*δ/(‖K‖^2+1)) (min (r/(η+1)) (η/(C₂+1)))), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact lt_min (lt_min one_pos (div_pos hdM (by positivity)))
        (lt_min (div_pos (mul_pos hr hδ) (by positivity))
          (lt_min (div_pos hr (by positivity)) (div_pos hη0 (by positivity))))
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact le_trans (min_le_left _ _) (min_le_right _ _)
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  set Mt : Matrix (Fin n) (Fin n) ℂ := M + (t : ℂ) • G with hMt
  have hdiff : ‖Mt.det - M.det‖ ≤ K₂ * t^2 := hK₂ t ht0.le ht1
  have hhalf : K₂ * t^2 ≤ ‖M.det‖/2 := by
    have hsq : t^2 ≤ t := by nlinarith
    have h1 : K₂ * t^2 ≤ K₂ * t := mul_le_mul_of_nonneg_left hsq hK₂0
    refine le_trans h1 (le_trans (mul_le_mul_of_nonneg_left ht2 hK₂0) ?_)
    have h : K₂ * (‖M.det‖/(2*(K₂+1))) = (K₂*‖M.det‖)/(2*(K₂+1)) := by ring
    rw [h, div_le_iff₀ (by positivity : (0:ℝ) < 2*(K₂+1))]
    nlinarith
  have hMtlow : ‖M.det‖/2 ≤ ‖Mt.det‖ := by
    have h1 : ‖M.det‖ - ‖Mt.det‖ ≤ ‖M.det - Mt.det‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev] at h1
    linarith
  have hMtpos : 0 < ‖Mt.det‖ := lt_of_lt_of_le (by positivity) hMtlow
  have hMtne : Mt.det ≠ 0 := norm_pos_iff.mp hMtpos
  set β : ℂ := M.det/Mt.det - 1 with hβdef
  have hβeq : β * Mt.det = M.det - Mt.det := by rw [hβdef]; field_simp
  have hβbound : ‖β‖ ≤ (2*K₂/‖M.det‖) * t^2 := by
    have h1 : ‖β‖ * ‖Mt.det‖ = ‖Mt.det - M.det‖ := by rw [← norm_mul, hβeq, norm_sub_rev]
    have h2 : ‖β‖ * (‖M.det‖/2) ≤ ‖β‖ * ‖Mt.det‖ :=
      mul_le_mul_of_nonneg_left hMtlow (norm_nonneg β)
    rw [h1] at h2
    have h3 : ‖β‖ * (‖M.det‖/2) ≤ K₂ * t^2 := le_trans h2 hdiff
    rw [div_mul_eq_mul_div, le_div_iff₀ hdM]
    linarith
  set v : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ (1:ℂ) with hvdef
  have hv : ‖v‖ = 1 := by rw [hvdef]; simp
  obtain ⟨z, D, hdetfix, hzbound, hDact⟩ := exists_det_fix Mt hMtne v hv β
  have hXdet : (Mt + D).det = M.det := by rw [hdetfix, hβdef]; field_simp; ring
  have hMtnorm : ‖Mt‖ ≤ Kn := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul]
    have hts : ‖(t:ℂ)‖ = t := by simp [abs_of_nonneg ht0.le]
    rw [hts, hKn]
    nlinarith [norm_nonneg G]
  have hDnorm : ‖D‖ ≤ C₂ * t^2 := by
    refine le_trans (opNorm_rankOne_le hv hDact) (le_trans hzbound ?_)
    calc ‖β‖ * ‖Mt‖ ≤ ((2*K₂/‖M.det‖) * t^2) * Kn :=
          mul_le_mul hβbound hMtnorm (norm_nonneg _) (by positivity)
      _ = C₂ * t^2 := by rw [hC₂]; ring
  have hsplit : A - Mt = Q * (((r:ℝ):ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (t:ℂ) • K) := by
    have h1 : A - Mt = (A - M) - (t:ℂ) • G := by rw [hMt]; abel
    rw [h1, hE, hG, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, mul_one]
  have hrt : 0 ≤ r - t*η := by
    have hle : t*η ≤ r := by
      rw [le_div_iff₀ (by positivity)] at ht4
      nlinarith
    linarith
  have hSle : r^2 - 2*r*t*δ + t^2*‖K‖^2 ≤ (r - t*η)^2 := by
    have h1 : t*‖K‖^2 ≤ r*δ := by
      rw [le_div_iff₀ (by positivity)] at ht3
      nlinarith [sq_nonneg ‖K‖]
    have h2 : t^2*‖K‖^2 ≤ t*(r*δ) := by nlinarith
    have h3 : (r - t*η)^2 = r^2 - 2*r*t*η + t^2*η^2 := by ring
    rw [h3, hη]
    nlinarith [sq_nonneg (t*η), sq_nonneg t]
  have hMtbound : ‖A - Mt‖ ≤ r - t*η := by
    rw [hsplit, norm_unitary_mul hn hQ]
    refine opNorm_le_of_forall hrt (fun y => ?_)
    refine le_of_sq_le_sq' ?_ (by positivity)
    calc ‖app (((r:ℝ):ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (t:ℂ) • K) y‖^2
        ≤ (r^2 - 2*r*t*δ + t^2*‖K‖^2) * ‖y‖^2 := norm_sq_shift_bound r t δ K hr ht0 hK y
      _ ≤ ((r - t*η))^2 * ‖y‖^2 := by nlinarith [sq_nonneg ‖y‖]
      _ = ((r - t*η) * ‖y‖)^2 := by ring
  have hAX : A - (Mt + D) = (A - Mt) - D := by abel
  have hnormAX : ‖A - (Mt + D)‖ ≤ ‖A - Mt‖ + ‖D‖ := by rw [hAX]; exact norm_sub_le _ _
  have hlast := descent_tangent_final C₂ η t hC₂0 hη0 ht0 ht5
  have hmin' := hmin (Mt + D) hXdet
  linarith

/-- Conjugating the trace amounts to transposing the matrix. -/
lemma trace_conj (Z : Matrix (Fin n) (Fin n) ℂ) :
    (starRingEnd ℂ) Z.trace = (Zᴴ).trace := by
  rw [Matrix.trace_conjTranspose]; rfl

/-- The trace of a product of two Hermitian matrices is real. -/
lemma trace_mul_isReal (X Y : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian)
    (hY : Y.IsHermitian) : (starRingEnd ℂ) ((X * Y).trace) = (X * Y).trace := by
  rw [trace_conj, Matrix.conjTranspose_mul, hX, hY, Matrix.trace_mul_comm]

/-- The trace of a Hermitian matrix is real. -/
lemma trace_isReal (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    (starRingEnd ℂ) H.trace = H.trace := by
  rw [trace_conj, hH]

/-- A real multiple of a Hermitian matrix is Hermitian. -/
lemma isHermitian_smul_real {x : ℂ} (hx : (starRingEnd ℂ) x = x)
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : (x • H).IsHermitian := by
  unfold Matrix.IsHermitian at *
  rw [Matrix.conjTranspose_smul, hH]
  simp [hx]

/-- For a Hermitian matrix, `tr (H * H)` is the squared Frobenius norm. -/
lemma trace_self_mul (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    (H * H).trace = ((∑ i, ∑ j, ‖H i j‖^2 : ℝ) : ℂ) := by
  rw [Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hji : H j i = (starRingEnd ℂ) (H i j) := by
    conv_lhs => rw [← hH]
    simp [Matrix.conjTranspose_apply]
  rw [hji, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

/-- A Hermitian matrix with `tr (H * H) = 0` vanishes. -/
lemma eq_zero_of_trace_self_mul (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (h : (H * H).trace = 0) : H = 0 := by
  rw [trace_self_mul H hH] at h
  have h0 : (∑ i, ∑ j, ‖H i j‖^2 : ℝ) = 0 := by exact_mod_cast h
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp h0 i (mem_univ i)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp h1 j (mem_univ j)
  simpa using (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2

lemma app_add' (A B : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    app (A + B) x = app A x + app B x := by simp [app, map_add]

/-- The quadratic form of a Hermitian matrix is real. -/
lemma inner_hermitian_im (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian)
    (y : EuclideanSpace ℂ (Fin n)) : (inner ℂ y (app T y) : ℂ).im = 0 := by
  have hs := Matrix.isHermitian_iff_isSymmetric.mp hT
  have hy : app T y = Matrix.toEuclideanLin T y := rfl
  have hc := (inner_conj_symm (𝕜 := ℂ) (Matrix.toEuclideanLin T y) y).trans (hs y y)
  rw [hy]
  exact Complex.conj_eq_iff_im.mp hc

/-- For Hermitian `T`, the matrix `1 + i T` has uniformly positive definite Hermitian part. -/
lemma posdef_shift (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian)
    (y : EuclideanSpace ℂ (Fin n)) :
    (1:ℝ) * ‖y‖^2 ≤
      (inner ℂ y (app ((1 : Matrix (Fin n) (Fin n) ℂ) + Complex.I • T) y) : ℂ).re := by
  have h2 := inner_hermitian_im T hT y
  rw [app_add', app_smul, app_one, inner_add_right, inner_smul_right]
  have h1 : (inner ℂ y y : ℂ) = ((‖y‖^2:ℝ):ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [h1]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, h2, one_mul, zero_mul,
    mul_zero, sub_zero, add_zero, Complex.ofReal_re]
  simp

set_option maxHeartbeats 1000000 in
/-- **Algebraic consequence of the multiplier condition.**  If `tr (B (1 + i T)) ≠ 0` for every
Hermitian `T`, then `B` is a complex multiple of a Hermitian matrix.

Indeed, writing `B = H₁ + i H₂` with `H₁, H₂` Hermitian, the hypothesis says that the pair of
real linear functionals `T ↦ tr (H₁ T)`, `T ↦ tr (H₂ T)` never takes the value
`(-tr H₂, tr H₁)`; since the Hilbert–Schmidt inner product is definite on Hermitian matrices,
this forces `H₁` and `H₂` to be proportional over `ℝ`. -/
theorem exists_hermitian_of_trace_cond (B : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ T : Matrix (Fin n) (Fin n) ℂ, T.IsHermitian →
       (B * ((1 : Matrix (Fin n) (Fin n) ℂ) + Complex.I • T)).trace ≠ 0) :
    ∃ (ζ : ℂ) (S : Matrix (Fin n) (Fin n) ℂ), ζ ≠ 0 ∧ S.IsHermitian ∧ B = ζ • S := by
  classical
  set H₁ : Matrix (Fin n) (Fin n) ℂ := (2:ℂ)⁻¹ • (B + Bᴴ) with hH₁def
  set H₂ : Matrix (Fin n) (Fin n) ℂ := (Complex.I/2) • (Bᴴ - B) with hH₂def
  have hH₁ : H₁.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hH₁def, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm]
    norm_num
  have hH₂ : H₂.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hH₂def, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose,
      show (star (Complex.I/2) : ℂ) = -(Complex.I/2) by simp [Complex.conj_I, neg_div]]
    module
  have hBdec : B = H₁ + Complex.I • H₂ := by
    rw [hH₁def, hH₂def]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.conjTranspose_apply, smul_eq_mul, Complex.star_def]
    linear_combination ((B i j - (starRingEnd ℂ) (B j i))/2) * Complex.I_sq
  clear_value H₁ H₂
  set m₁ : ℂ := H₁.trace with hm₁
  set m₂ : ℂ := H₂.trace with hm₂
  set a : ℂ := (H₁ * H₁).trace with ha
  set b : ℂ := (H₁ * H₂).trace with hb
  have key : ∀ T : Matrix (Fin n) (Fin n) ℂ, T.IsHermitian →
      (H₁ * T).trace = -m₂ → (H₂ * T).trace = m₁ → False := by
    intro T hT e1 e2
    refine h T hT ?_
    rw [hBdec]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, e1, e2, ← hm₁, ← hm₂]
    linear_combination m₁ * Complex.I_sq
  by_cases ha0 : a = 0
  · have hH₁0 : H₁ = 0 := eq_zero_of_trace_self_mul H₁ hH₁ (by rw [← ha]; exact ha0)
    exact ⟨Complex.I, H₂, Complex.I_ne_zero, hH₂, by rw [hBdec, hH₁0, zero_add]⟩
  · have hare : (starRingEnd ℂ) a = a := trace_mul_isReal H₁ H₁ hH₁ hH₁
    have hbre : (starRingEnd ℂ) b = b := trace_mul_isReal H₁ H₂ hH₁ hH₂
    have hwre : (starRingEnd ℂ) (b/a) = b/a := by rw [map_div₀, hare, hbre]
    set Z : Matrix (Fin n) (Fin n) ℂ := H₂ - (b/a) • H₁ with hZdef
    have hZ : Z.IsHermitian := hH₂.sub (isHermitian_smul_real hwre hH₁)
    have h1Z : (H₁ * Z).trace = 0 := by
      rw [hZdef, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
        smul_eq_mul, ← ha, ← hb]
      field_simp
      ring
    set e : ℂ := (Z * Z).trace with he
    have h2Z : (H₂ * Z).trace = e := by
      have hzz : (Z * Z).trace = (H₂ * Z).trace - (b/a) * (H₁ * Z).trace := by
        conv_lhs => rw [hZdef]
        rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
          ← hZdef]
      rw [he, hzz, h1Z]
      ring
    by_cases he0 : e = 0
    · have hZ0 : Z = 0 := eq_zero_of_trace_self_mul Z hZ (by rw [← he]; exact he0)
      have hH₂eq : H₂ = (b/a) • H₁ := by
        have hz := hZdef ▸ hZ0
        rw [sub_eq_zero] at hz
        exact hz
      refine ⟨1 + Complex.I * (b/a), H₁, ?_, hH₁, ?_⟩
      · have hwim : (b/a).im = 0 := Complex.conj_eq_iff_im.mp hwre
        intro hc
        have hre : (1 + Complex.I * (b/a)).re = 0 := by rw [hc]; simp
        simp [Complex.add_re, Complex.mul_re, hwim] at hre
      · rw [hBdec, hH₂eq, smul_smul]
        module
    · set x : ℂ := -m₂/a with hx
      set y : ℂ := (m₁ - x*b)/e with hy
      have hm₁re : (starRingEnd ℂ) m₁ = m₁ := trace_isReal H₁ hH₁
      have hm₂re : (starRingEnd ℂ) m₂ = m₂ := trace_isReal H₂ hH₂
      have here : (starRingEnd ℂ) e = e := trace_mul_isReal Z Z hZ hZ
      have hxre : (starRingEnd ℂ) x = x := by rw [hx, map_div₀, map_neg, hm₂re, hare]
      have hyre : (starRingEnd ℂ) y = y := by
        rw [hy, map_div₀, map_sub, hm₁re, map_mul, hxre, hbre, here]
      set T : Matrix (Fin n) (Fin n) ℂ := x • H₁ + y • Z with hT
      have hTH : T.IsHermitian :=
        (isHermitian_smul_real hxre hH₁).add (isHermitian_smul_real hyre hZ)
      have e1 : (H₁ * T).trace = -m₂ := by
        rw [hT, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add,
          Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, ← ha, h1Z, hx]
        field_simp
        ring
      have e2 : (H₂ * T).trace = m₁ := by
        rw [hT, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add,
          Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, h2Z,
          Matrix.trace_mul_comm H₂ H₁, ← hb, hy]
        field_simp
        ring
      exact (key T hTH e1 e2).elim

/-- **Structural theorem for a nearest matrix** (Lemma 3.1).  If `M` is nearest to `A` among
matrices of determinant `det M ≠ 0` and `r = ‖A - M‖ > 0`, then `A - M = r • Q` with `Q`
unitary and `Qᴴ M = α • P` with `α ≠ 0` and `P` Hermitian. -/
theorem exists_structure_of_min (hn : 0 < n) (A M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0)
    (hmin : ∀ X : Matrix (Fin n) (Fin n) ℂ, X.det = M.det → ‖A - M‖ ≤ ‖A - X‖)
    (hr : 0 < ‖A - M‖) :
    ∃ (Q : Matrix (Fin n) (Fin n) ℂ) (α : ℂ) (P : Matrix (Fin n) (Fin n) ℂ),
      Q ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ A - M = ((‖A - M‖ : ℝ) : ℂ) • Q ∧
      α ≠ 0 ∧ P.IsHermitian ∧ Qᴴ * M = α • P := by
  classical
  obtain ⟨Q, hQ, hE⟩ := exists_unitary_of_min hn A M hM hmin
  have hQQ : Q * Qᴴ = 1 := by
    have h := hQ.2
    simpa [Matrix.star_eq_conjTranspose] using h
  set B : Matrix (Fin n) (Fin n) ℂ := M⁻¹ * Q with hB
  set X : Matrix (Fin n) (Fin n) ℂ := Qᴴ * M with hX
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have hBX : B * X = 1 := by
    rw [hB, hX, Matrix.mul_assoc, ← Matrix.mul_assoc Q Qᴴ M, hQQ, Matrix.one_mul,
      Matrix.nonsing_inv_mul M hMu]
  have hcond : ∀ T : Matrix (Fin n) (Fin n) ℂ, T.IsHermitian →
      (B * ((1 : Matrix (Fin n) (Fin n) ℂ) + Complex.I • T)).trace ≠ 0 := by
    intro T hT
    have h := trace_ne_zero_of_min hn A M hM hmin hQ hr hE
      ((1 : Matrix (Fin n) (Fin n) ℂ) + Complex.I • T) (δ := 1) one_pos (posdef_shift T hT)
    simpa [hB] using h
  obtain ⟨ζ, S, hζ, hS, hBeq⟩ := exists_hermitian_of_trace_cond B hcond
  have hSX : S * (ζ • X) = 1 := by
    have h1 : ζ • (S * X) = 1 := by rw [← Matrix.smul_mul, ← hBeq]; exact hBX
    rw [Matrix.mul_smul]; exact h1
  have hSinv : S⁻¹ = ζ • X := Matrix.inv_eq_right_inv hSX
  have hSherm : (S⁻¹).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_nonsing_inv, hS]
  refine ⟨Q, ζ⁻¹, S⁻¹, hQ, hE, inv_ne_zero hζ, hSherm, ?_⟩
  rw [← hX, hSinv, smul_smul, inv_mul_cancel₀ hζ, one_smul]

end Q857
