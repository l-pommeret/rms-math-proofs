import RMS.Q857Var

/-!
# Q857 — the arbitrary-phase complex lower bound and the aggregate complex theorem

Using the structural theorem `Q857.exists_structure_of_min` for a nearest determinant-one
matrix, this module proves the missing half of Q857 over `ℂ`:

* `Q857.cmin_le_of_det_one` : for every `A` and every `M` with `det M = 1`,
  `cmin (svals A) (etaOf A) ≤ ‖A - M‖`;
* `Q857.complex_isLeast` : the distance from an arbitrary complex matrix to the
  determinant-one matrices is exactly the arbitrary-phase scalar minimax value
  `cmin (svals A) (etaOf A)`.

The argument for a *nearest* matrix `M` runs as follows.  Put `E = A - M` and `r = ‖E‖`.
If `r = 0` then `det A = 1` and the scalars `z = σ(A)` are admissible at cost `0`.  If `r > 0`,
the structural theorem gives `E = r • Q` with `Q` unitary and `Qᴴ M = α • P` with `P` Hermitian.
Hence `C := Qᴴ A = r • 1 + α • P` is normal, so it is unitarily diagonalizable; after sorting the
eigenvalues `μ i` by decreasing modulus, `‖μ i‖ = svals C i = svals A i`.  Writing
`μ i = ‖μ i‖ * u i` with unit phases `u i` whose product is a prescribed unimodular number, the
scalars `z i = conj (u i) * (μ i - r)` satisfy `|σ i - z i| = r` and `∏ z i = η_A`, so
`cmin (σ(A), η_A) ≤ r` by the scalar minimax theorem `Q857.cmin_isLeast`.
-/

namespace Q857

open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {n : ℕ}

/-- A matrix of the form `r • 1 + α • P` with `P` Hermitian is normal, hence unitarily
diagonalizable. -/
lemma exists_eigen_of_shift_hermitian (C : Matrix (Fin n) (Fin n) ℂ) (α : ℂ)
    (r : ℝ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : P.IsHermitian)
    (hC : C = ((r : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + α • P) :
    ∃ (W : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℂ),
      W ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ C = W * diagonal lam * Wᴴ := by
  classical
  obtain ⟨U, d, hUmem, hPeq⟩ : ∃ (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ),
      U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ P = U * diagonal d * Uᴴ := by
    refine ⟨(hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ),
      fun i => ((hP.eigenvalues i : ℝ) : ℂ), hP.eigenvectorUnitary.2, ?_⟩
    have h := hP.spectral_theorem
    simpa [Unitary.conjStarAlgAut, Matrix.star_eq_conjTranspose, Function.comp] using h
  have hUU : U * Uᴴ = 1 := by
    have h := hUmem.2
    simpa [Matrix.star_eq_conjTranspose] using h
  refine ⟨U, fun i => ((r : ℝ) : ℂ) + α * d i, hUmem, ?_⟩
  have hdiag : (diagonal fun i => ((r : ℝ) : ℂ) + α * d i)
      = ((r:ℝ):ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + α • diagonal d := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hdiag, hC, hPeq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, hUU, Matrix.mul_assoc]

/-- Permuting the columns of a unitary matrix gives a unitary matrix. -/
lemma submatrix_unitary {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (e : Equiv.Perm (Fin n)) : W.submatrix id e ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hWW : Wᴴ * W = 1 := by
    have h := hW.1
    simpa [Matrix.star_eq_conjTranspose] using h
  have h1 : star (W.submatrix id ⇑e) = Wᴴ.submatrix (⇑e) id := by
    rw [Matrix.star_eq_conjTranspose]
    ext i j
    simp
  rw [h1]
  have h2 : Wᴴ.submatrix (⇑e) id * W.submatrix id ⇑e
      = (Wᴴ.submatrix (⇑e) ⇑(Equiv.refl (Fin n))) * (W.submatrix ⇑(Equiv.refl (Fin n)) ⇑e) := rfl
  rw [h2, Matrix.submatrix_mul_equiv, hWW]
  simp

/-- The eigenvalues of a unitarily diagonalizable matrix can be sorted so that their moduli are
exactly the singular values. -/
lemma exists_sorted_eigen (C W : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin n) ℂ) (hC : C = W * diagonal lam * Wᴴ) :
    ∃ (W' : Matrix (Fin n) (Fin n) ℂ) (mu : Fin n → ℂ),
      W' ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ C = W' * diagonal mu * W'ᴴ ∧
      (∀ i, ‖mu i‖ = svals C i) := by
  classical
  set e : Equiv.Perm (Fin n) := Tuple.sort (fun i => -‖lam i‖) with he
  have hanti : Antitone (fun i => ‖lam (e i)‖) := by
    have hm := Tuple.monotone_sort (fun i => -‖lam i‖)
    intro i j hij
    have h := hm hij
    simp only [Function.comp_apply, ← he] at h
    simpa using neg_le_neg_iff.mp h
  set W' : Matrix (Fin n) (Fin n) ℂ := W.submatrix id e with hW'def
  have hW' : W' ∈ Matrix.unitaryGroup (Fin n) ℂ := submatrix_unitary hW e
  set mu : Fin n → ℂ := fun i => lam (e i) with hmu
  have hW'H : W'ᴴ = Wᴴ.submatrix (⇑e) id := by
    ext i j; simp [hW'def]
  have hCeq : C = W' * diagonal mu * W'ᴴ := by
    rw [hC, hW'def, hW'H]
    have hd : diagonal mu = (diagonal lam).submatrix ⇑e ⇑e := by
      rw [Matrix.submatrix_diagonal_equiv]; rfl
    rw [hd]
    have h1 : W.submatrix id ⇑e * (diagonal lam).submatrix (⇑e) (⇑e)
        = (W * diagonal lam).submatrix id ⇑e := by
      rw [show W.submatrix id ⇑e = W.submatrix (⇑(Equiv.refl (Fin n))) ⇑e from rfl,
        Matrix.submatrix_mul_equiv]
      rfl
    rw [h1, show Wᴴ.submatrix (⇑e) id = Wᴴ.submatrix (⇑e) (⇑(Equiv.refl (Fin n))) from rfl,
      Matrix.submatrix_mul_equiv]
    rfl
  refine ⟨W', mu, hW', hCeq, ?_⟩
  set u : Fin n → ℂ := fun i => if mu i = 0 then 1 else mu i / ((‖mu i‖ : ℝ) : ℂ) with hu
  have hunorm : ∀ i, ‖u i‖ = 1 := by
    intro i
    rw [hu]
    by_cases h : mu i = 0
    · simp [h]
    · simp only [h, if_false]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact div_self (by simpa using h)
  have hmusplit : ∀ i, mu i = ((‖mu i‖ : ℝ) : ℂ) * u i := by
    intro i
    rw [hu]
    by_cases h : mu i = 0
    · simp [h]
    · simp only [h, if_false]
      field_simp
  have hdiagsplit : diagonal mu
      = diagonal (fun i => ((‖mu i‖ : ℝ) : ℂ)) * diagonal u := by
    rw [Matrix.diagonal_mul_diagonal]
    exact congrArg diagonal (funext hmusplit)
  set V : Matrix (Fin n) (Fin n) ℂ := W' * diagonal (fun i => star (u i)) with hV
  have hVmem : V ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    mul_mem hW' (diagonal_mem_unitaryGroup (by intro i; simpa using hunorm i))
  have hVH : Vᴴ = diagonal u * W'ᴴ := by
    rw [hV, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose]
    congr 1
    exact congrArg diagonal (funext (fun i => by simp))
  have hsvd : C = W' * diagonal (fun i => ((‖mu i‖ : ℝ) : ℂ)) * Vᴴ := by
    rw [hVH, hCeq, hdiagsplit]
    noncomm_ring
  have hsvals := svals_eq_of_svd hW' hVmem (fun i => norm_nonneg (mu i))
    (fun i j hij => hanti hij) hsvd
  intro i
  rw [hsvals]

/-- Unit phases with a prescribed product.  If the product of the `μ i` has the phase `τ`
whenever no `μ i` vanishes, then one can choose unit numbers `u i` of product `τ` with
`μ i = ‖μ i‖ * u i`. -/
lemma exists_unit_phases (μ : Fin n → ℂ) (τ : ℂ) (hτ : ‖τ‖ = 1)
    (h : (∀ i, μ i ≠ 0) → (∏ i, μ i) = τ * ∏ i, ((‖μ i‖ : ℝ) : ℂ)) :
    ∃ u : Fin n → ℂ, (∀ i, ‖u i‖ = 1) ∧ (∀ i, μ i = ((‖μ i‖ : ℝ) : ℂ) * u i) ∧
      ∏ i, u i = τ := by
  classical
  set u₀ : Fin n → ℂ := fun i => if μ i = 0 then 1 else μ i / ((‖μ i‖ : ℝ) : ℂ) with hu₀
  have hu₀norm : ∀ i, ‖u₀ i‖ = 1 := by
    intro i
    rw [hu₀]
    by_cases hi : μ i = 0
    · simp [hi]
    · simp only [hi, if_false]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact div_self (by simpa using hi)
  have hu₀split : ∀ i, μ i = ((‖μ i‖ : ℝ) : ℂ) * u₀ i := by
    intro i
    rw [hu₀]
    by_cases hi : μ i = 0
    · simp [hi]
    · simp only [hi, if_false]
      field_simp
  by_cases hall : ∀ i, μ i ≠ 0
  · refine ⟨u₀, hu₀norm, hu₀split, ?_⟩
    have hprod : ∏ i, μ i = (∏ i, ((‖μ i‖ : ℝ) : ℂ)) * ∏ i, u₀ i := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => hu₀split i)
    have hne : (∏ i, ((‖μ i‖ : ℝ) : ℂ)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr (fun i _ => ?_)
      simpa using hall i
    have hkey : (∏ i, ((‖μ i‖ : ℝ) : ℂ)) * ∏ i, u₀ i = (∏ i, ((‖μ i‖ : ℝ) : ℂ)) * τ := by
      rw [← hprod, h hall]; ring
    exact mul_left_cancel₀ hne hkey
  · push_neg at hall
    obtain ⟨i₀, hi₀⟩ := hall
    set p : ℂ := ∏ i ∈ univ.erase i₀, u₀ i with hp
    have hpnorm : ‖p‖ = 1 := by
      rw [hp, norm_prod]
      exact Finset.prod_eq_one (fun i _ => hu₀norm i)
    have hpne : p ≠ 0 := by
      intro hc; rw [hc, norm_zero] at hpnorm; exact zero_ne_one hpnorm
    set u : Fin n → ℂ := fun i => if i = i₀ then τ / p else u₀ i with hu
    have hui₀ : u i₀ = τ / p := by rw [hu]; simp
    refine ⟨u, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = i₀
      · rw [hi, hui₀, norm_div, hτ, hpnorm, div_one]
      · have hval : u i = u₀ i := by rw [hu]; simp [hi]
        rw [hval]; exact hu₀norm i
    · intro i
      by_cases hi : i = i₀
      · rw [hi, hui₀]; simp [hi₀]
      · have hval : u i = u₀ i := by rw [hu]; simp [hi]
        rw [hval]; exact hu₀split i
    · rw [← Finset.mul_prod_erase univ u (mem_univ i₀)]
      have hrest : ∏ i ∈ univ.erase i₀, u i = p := by
        rw [hp]
        refine Finset.prod_congr rfl (fun i hi => ?_)
        have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
        simp [hu, hne]
      rw [hrest, hui₀]
      field_simp

/-- The determinant of a matrix written as `W * diagonal d * Wᴴ` with `W` unitary. -/
lemma det_conj_diagonal {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (d : Fin n → ℂ) : (W * diagonal d * Wᴴ).det = ∏ i, d i := by
  have hWW : W * Wᴴ = 1 := by
    have h := hW.2
    simpa [Matrix.star_eq_conjTranspose] using h
  have hdet : (W.det) * (Wᴴ.det) = 1 := by
    rw [← Matrix.det_mul, hWW, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  calc W.det * (∏ i, d i) * Wᴴ.det = (W.det * Wᴴ.det) * ∏ i, d i := by ring
    _ = ∏ i, d i := by rw [hdet, one_mul]

/-- **The arbitrary-phase lower bound for a nearest matrix.** -/
theorem cmin_le_of_min (hn : 0 < n) (A M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det = 1)
    (hmin : ∀ X : Matrix (Fin n) (Fin n) ℂ, X.det = 1 → ‖A - M‖ ≤ ‖A - X‖) :
    cmin (svals A) (etaOf A) ≤ ‖A - M‖ := by
  classical
  rcases eq_or_lt_of_le (norm_nonneg (A - M)) with hr0 | hr
  · -- `A = M`, hence `det A = 1` and the scalars `z = σ(A)` are admissible at cost `0`
    have hAM : A = M := sub_eq_zero.mp (norm_eq_zero.mp hr0.symm)
    have hdetA : A.det = 1 := by rw [hAM, hM]
    have heta : etaOf A = 1 := by
      rw [etaOf, if_neg (by rw [hdetA]; exact one_ne_zero), hdetA]
      simp
    have hprod : ∏ i, ((svals A i : ℝ) : ℂ) = etaOf A := by
      have h1 : (∏ i, svals A i) = ‖A.det‖ := prod_svals A
      rw [hdetA, norm_one] at h1
      rw [heta, ← Complex.ofReal_one, ← h1]
      push_cast
      rfl
    have hle : cmin (svals A) (etaOf A) ≤ 0 :=
      (cmin_isLeast (σ := svals A) hn (etaOf A)).2
        ⟨fun i => ((svals A i : ℝ) : ℂ), hprod, fun i => by simp⟩
    rw [← hr0]
    exact hle
  · set r : ℝ := ‖A - M‖ with hrdef
    have hMne : M.det ≠ 0 := by rw [hM]; exact one_ne_zero
    have hmin' : ∀ X : Matrix (Fin n) (Fin n) ℂ, X.det = M.det → ‖A - M‖ ≤ ‖A - X‖ := by
      intro X hX; exact hmin X (by rw [hX, hM])
    obtain ⟨Q, α, P, hQ, hE, hα, hP, hQM⟩ :=
      exists_structure_of_min hn A M hMne hmin' hr
    have hQH : Qᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
      have h := Unitary.star_mem hQ
      rwa [Matrix.star_eq_conjTranspose] at h
    have hQQ : Qᴴ * Q = 1 := by
      have h := hQ.1
      simpa [Matrix.star_eq_conjTranspose] using h
    set C : Matrix (Fin n) (Fin n) ℂ := Qᴴ * A with hCdef
    have hCM : C - ((r : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) = Qᴴ * M := by
      have hA : A = M + ((r : ℝ) : ℂ) • Q := by rw [← hE]; abel
      rw [hCdef, hA, Matrix.mul_add, Matrix.mul_smul, hQQ]
      abel
    have hC : C = ((r : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + α • P := by
      have h := hCM
      rw [hQM] at h
      linear_combination (norm := abel) h
    obtain ⟨W, lam, hW, hCW⟩ := exists_eigen_of_shift_hermitian C α r P hP hC
    obtain ⟨W', mu, hW', hCW', hmunorm⟩ := exists_sorted_eigen C W lam hW hCW
    have hsv : ∀ i, svals C i = svals A i := by
      intro i; rw [hCdef, svals_unitary_mul hQH A]
    set D : ℂ := (Qᴴ).det with hD
    have hDnorm : ‖D‖ = 1 := norm_det_unitary hQH
    have hdetshift : ∏ i, (mu i - ((r : ℝ) : ℂ)) = D := by
      have h1 : C - ((r : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
          = W' * diagonal (fun i => mu i - ((r : ℝ) : ℂ)) * W'ᴴ := by
        have hWW : W' * W'ᴴ = 1 := by
          have h := hW'.2
          simpa [Matrix.star_eq_conjTranspose] using h
        have hd : diagonal (fun i => mu i - ((r : ℝ) : ℂ))
            = diagonal mu - ((r : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
          ext i j
          by_cases hij : i = j <;> simp [hij]
        rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, hWW, ← hCW']
      have h2 := det_conj_diagonal hW' (fun i => mu i - ((r : ℝ) : ℂ))
      rw [← h1, hCM, Matrix.det_mul, hM, mul_one] at h2
      exact h2.symm
    have hdetC : ∏ i, mu i = D * A.det := by
      have h2 := det_conj_diagonal hW' mu
      rw [← hCW', hCdef, Matrix.det_mul] at h2
      exact h2.symm
    set τ : ℂ := (starRingEnd ℂ) (etaOf A) * D with hτdef
    have hτ : ‖τ‖ = 1 := by
      rw [hτdef, norm_mul, RCLike.norm_conj, norm_etaOf, hDnorm, one_mul]
    have hcond : (∀ i, mu i ≠ 0) → (∏ i, mu i) = τ * ∏ i, ((‖mu i‖ : ℝ) : ℂ) := by
      intro hall
      have hprodmu : (∏ i, ((‖mu i‖ : ℝ) : ℂ)) = ((‖A.det‖ : ℝ) : ℂ) := by
        have h1 : (∏ i, ‖mu i‖) = ∏ i, svals C i :=
          Finset.prod_congr rfl (fun i _ => hmunorm i)
        have h2 : (∏ i, svals C i) = ‖C.det‖ := prod_svals C
        have h3 : ‖C.det‖ = ‖A.det‖ := by
          rw [hCdef, Matrix.det_mul, norm_mul, ← hD, hDnorm, one_mul]
        have h4 : (∏ i, ‖mu i‖) = ‖A.det‖ := by rw [h1, h2, h3]
        rw [← h4]
        push_cast
        rfl
      have hdetA : A.det ≠ 0 := by
        intro h0
        have hz : ∏ i, mu i = 0 := by rw [hdetC, h0, mul_zero]
        exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hall i)) hz
      have hetaconj : (starRingEnd ℂ) (etaOf A) * ((‖A.det‖ : ℝ) : ℂ) = A.det := by
        rw [etaOf, if_neg hdetA, map_div₀]
        simp only [RingHomCompTriple.comp_apply, RingHom.id_apply, starRingEnd_self_apply,
          Complex.star_def]
        have hreal : (starRingEnd ℂ) (((‖A.det‖ : ℝ) : ℂ)) =
            (((‖A.det‖ : ℝ) : ℂ)) := by
          apply Complex.ext <;> simp [Complex.star_def]
        rw [hreal]
        field_simp
      rw [hdetC, hprodmu, hτdef]
      calc D * A.det = ((starRingEnd ℂ) (etaOf A) * ((‖A.det‖:ℝ):ℂ)) * D := by
            rw [hetaconj]; ring
        _ = (starRingEnd ℂ) (etaOf A) * D * ((‖A.det‖:ℝ):ℂ) := by ring
    obtain ⟨u, hunorm, husplit, huprod⟩ := exists_unit_phases mu τ hτ hcond
    set z : Fin n → ℂ := fun i => (starRingEnd ℂ) (u i) * (mu i - ((r : ℝ) : ℂ)) with hz
    have hconju : ∀ i, (starRingEnd ℂ) (u i) * u i = 1 := by
      intro i
      rw [Complex.conj_mul', hunorm i]
      norm_num
    have hzdist : ∀ i, ‖((svals A i : ℝ) : ℂ) - z i‖ = r := by
      intro i
      have h1 : ((svals A i : ℝ) : ℂ) = ((‖mu i‖ : ℝ) : ℂ) := by
        rw [← hsv i, hmunorm i]
      have h2 : z i = ((‖mu i‖ : ℝ) : ℂ) - ((r : ℝ) : ℂ) * (starRingEnd ℂ) (u i) := by
        rw [hz]
        simp only
        rw [mul_sub]
        congr 1
        · conv_lhs => rw [husplit i]
          rw [← mul_assoc, mul_comm ((starRingEnd ℂ) (u i)) (((‖mu i‖:ℝ):ℂ)), mul_assoc,
            hconju i, mul_one]
        · ring
      rw [h1, h2]
      have h3 : ((‖mu i‖ : ℝ) : ℂ)
            - (((‖mu i‖ : ℝ) : ℂ) - ((r : ℝ) : ℂ) * (starRingEnd ℂ) (u i))
          = ((r : ℝ) : ℂ) * (starRingEnd ℂ) (u i) := by ring
      rw [h3, norm_mul, Complex.norm_real, RCLike.norm_conj, hunorm i, mul_one,
        Real.norm_eq_abs, abs_of_nonneg hr.le]
    have hzprod : ∏ i, z i = etaOf A := by
      have h1 : ∏ i, z i = (∏ i, (starRingEnd ℂ) (u i)) * ∏ i, (mu i - ((r : ℝ) : ℂ)) := by
        rw [← Finset.prod_mul_distrib]
      have h2 : (∏ i, (starRingEnd ℂ) (u i)) = (starRingEnd ℂ) τ := by
        rw [← huprod, map_prod]
      rw [h1, h2, hdetshift, hτdef, map_mul]
      have h3 : (starRingEnd ℂ) ((starRingEnd ℂ) (etaOf A)) = etaOf A := by simp
      have h4 : (starRingEnd ℂ) D * D = 1 := by
        rw [Complex.conj_mul', hDnorm]
        norm_num
      rw [h3]
      calc etaOf A * (starRingEnd ℂ) D * D = etaOf A * ((starRingEnd ℂ) D * D) := by ring
        _ = etaOf A := by rw [h4, mul_one]
    exact (cmin_isLeast (σ := svals A) hn (etaOf A)).2
      ⟨z, hzprod, fun i => le_of_eq (hzdist i)⟩

/-- **The arbitrary-phase complex lower bound.**  No determinant-one matrix beats the scalar
optimum: `cmin (σ(A), η_A) ≤ ‖A - M‖` for every `M` with `det M = 1`. -/
theorem cmin_le_of_det_one (hn : 0 < n) (A M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det = 1) :
    cmin (svals A) (etaOf A) ≤ ‖A - M‖ := by
  obtain ⟨M₀, hM₀, hleast⟩ := exists_nearest A
  have hmin : ∀ X : Matrix (Fin n) (Fin n) ℂ, X.det = 1 → ‖A - M₀‖ ≤ ‖A - X‖ :=
    fun X hX => hleast.2 ⟨X, hX, le_refl _⟩
  exact le_trans (cmin_le_of_min hn A M₀ hM₀ hmin) (hleast.2 ⟨M, hM, le_refl _⟩)

/-- **The aggregate complex theorem (2.4).**  For every `n ≥ 1` and every complex `n × n`
matrix `A`, the distance from `A` to the determinant-one matrices, for the operator norm
subordinate to the standard Hermitian norm, is attained and equals the arbitrary-phase scalar
minimax value `min { max_i |σ_i(A) - z_i| : ∏ z_i = η_A }`. -/
theorem complex_isLeast (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ) :
    IsLeast {r : ℝ | ∃ M : Matrix (Fin n) (Fin n) ℂ, M.det = 1 ∧ ‖A - M‖ ≤ r}
      (cmin (svals A) (etaOf A)) := by
  refine ⟨complex_upper hn A, ?_⟩
  rintro r ⟨M, hM, hMr⟩
  exact le_trans (cmin_le_of_det_one hn A M hM) hMr

#print axioms exists_hermitian_of_trace_cond
#print axioms exists_structure_of_min
#print axioms cmin_le_of_det_one
#print axioms complex_isLeast

end Q857
