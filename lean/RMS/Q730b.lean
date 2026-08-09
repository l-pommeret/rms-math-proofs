import RMS.Q730

/-!
# Q730, part b : the necessity bound

`‖det (A.submatrix ι κ)‖ ≤ σ₁ ⋯ σ_k` for any `k × k` submatrix of `A`, where `σ` are the
singular values of `A` in decreasing order.
-/

namespace Q730

open Matrix Finset BigOperators
open scoped ComplexOrder

variable {n m k : ℕ}

lemma HasSV.unitary_mul {A : Matrix (Fin n) (Fin n) ℂ} {s : Fin n → ℝ} (h : HasSV A s)
    {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) : HasSV (W * A) s := by
  obtain ⟨U, V, hU, hV, hA⟩ := h
  exact ⟨W * U, V, mul_mem hW hU, hV, by rw [hA]; simp only [Matrix.mul_assoc]⟩

lemma strictMono_le_apply {g : Fin k → Fin n} (hg : StrictMono g) (i : Fin k) :
    (i : ℕ) ≤ (g i : ℕ) := by
  have key : ∀ m : ℕ, ∀ i : Fin k, (i : ℕ) = m → m ≤ (g i : ℕ) := by
    intro m
    induction m with
    | zero => intro i _; exact Nat.zero_le _
    | succ p ih =>
        intro i hi
        have hp : (p : ℕ) < k := by omega
        have h1 : (⟨p, hp⟩ : Fin k) < i := by
          simp only [Fin.lt_def]; omega
        have h2 := hg h1
        have h3 := ih ⟨p, hp⟩ rfl
        simp only [Fin.lt_def] at h2
        omega
  exact key i i rfl

/-- For a unitary `U` and an injective `ι`, the sum of the squared moduli of the maximal
minors of the `k` rows `ι` of `U` is `1`. -/
theorem sum_norm_det_sq_rows {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ unitaryGroup (Fin n) ℂ)
    {ι : Fin k → Fin n} (hι : Function.Injective ι) :
    ∑ g ∈ univ.filter (fun g : Fin k → Fin n => StrictMono g), ‖(U.submatrix ι g).det‖ ^ 2 = 1 := by
  classical
  set P : Matrix (Fin k) (Fin n) ℂ := U.submatrix ι id with hP
  have hPP : P * Pᴴ = 1 := by
    rw [hP, Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]
    have h : U * Uᴴ = 1 := by simpa [Matrix.star_eq_conjTranspose] using hU.2
    rw [h, Matrix.submatrix_one _ hι]
  have hcb := cauchy_binet P Pᴴ
  rw [hPP, Matrix.det_one] at hcb
  have key : ∀ g : Fin k → Fin n, (P.submatrix id g).det * (Pᴴ.submatrix g id).det
      = ((‖(U.submatrix ι g).det‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    have h1 : P.submatrix id g = U.submatrix ι g := by rw [hP]; rfl
    have h2 : Pᴴ.submatrix g id = (U.submatrix ι g)ᴴ := by
      rw [hP, Matrix.conjTranspose_submatrix]; rfl
    rw [h1, h2, Matrix.det_conjTranspose, RCLike.star_def, Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq _
  rw [Finset.sum_congr rfl (fun g _ => key g)] at hcb
  exact_mod_cast hcb.symm

/-- The column version of `sum_norm_det_sq_rows`. -/
theorem sum_norm_det_sq_cols {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ unitaryGroup (Fin n) ℂ)
    {κ : Fin k → Fin n} (hκ : Function.Injective κ) :
    ∑ g ∈ univ.filter (fun g : Fin k → Fin n => StrictMono g), ‖(V.submatrix g κ).det‖ ^ 2 = 1 := by
  rw [← sum_norm_det_sq_rows (unitary_conjTranspose hV) hκ]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  have h : Vᴴ.submatrix κ g = (V.submatrix g κ)ᴴ := Matrix.conjTranspose_submatrix _ _ _
  rw [h, Matrix.det_conjTranspose]
  simp

/-- The key bound: every `k × k` minor of a matrix with singular values `s` (in decreasing
order) has determinant of modulus at most `s₀ ⋯ s_{k-1}`. -/
theorem norm_det_submatrix_le (hk : k ≤ n) {A : Matrix (Fin n) (Fin n) ℂ} {s : Fin n → ℝ}
    (hA : HasSV A s) (hs0 : ∀ i, 0 ≤ s i) (hanti : Antitone s)
    {ι κ : Fin k → Fin n} (hι : Function.Injective ι) (hκ : Function.Injective κ) :
    ‖(A.submatrix ι κ).det‖ ≤ ∏ p : Fin k, s (Fin.castLE hk p) := by
  classical
  obtain ⟨U, V, hU, hV, hAeq⟩ := hA
  set F := univ.filter (fun g : Fin k → Fin n => StrictMono g) with hF
  set Sk := ∏ p : Fin k, s (Fin.castLE hk p) with hSk
  have hSk0 : 0 ≤ Sk := Finset.prod_nonneg (fun p _ => hs0 _)
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (s i : ℂ)) with hD
  have hsub : A.submatrix ι κ = ((U * D).submatrix ι id) * (V.submatrix id κ) := by
    rw [hAeq, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]
  have hcb := cauchy_binet ((U * D).submatrix ι id) (V.submatrix id κ)
  rw [← hsub] at hcb
  have key : ∀ g : Fin k → Fin n,
      (((U * D).submatrix ι id).submatrix id g).det * ((V.submatrix id κ).submatrix g id).det
        = (∏ j, ((s (g j) : ℂ))) * ((U.submatrix ι g).det * (V.submatrix g κ).det) := by
    intro g
    have h1 : ((U * D).submatrix ι id).submatrix id g
        = (U.submatrix ι g) * diagonal (fun j => (s (g j) : ℂ)) := by
      ext i j
      simp [Matrix.mul_apply, hD, Matrix.diagonal_apply]
    have h2 : ((V.submatrix id κ).submatrix g id) = V.submatrix g κ := rfl
    rw [h1, h2, Matrix.det_mul, Matrix.det_diagonal]
    ring
  rw [Finset.sum_congr rfl (fun g _ => key g)] at hcb
  have hsum : ∑ g ∈ F, ((‖(U.submatrix ι g).det‖ ^ 2 + ‖(V.submatrix g κ).det‖ ^ 2) / 2) = 1 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, sum_norm_det_sq_rows hU hι,
      sum_norm_det_sq_cols hV hκ]
    norm_num
  calc ‖(A.submatrix ι κ).det‖
      = ‖∑ g ∈ F, (∏ j, ((s (g j) : ℂ))) * ((U.submatrix ι g).det * (V.submatrix g κ).det)‖ := by
        rw [hcb]
    _ ≤ ∑ g ∈ F, ‖(∏ j, ((s (g j) : ℂ))) * ((U.submatrix ι g).det * (V.submatrix g κ).det)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ g ∈ F, Sk * ((‖(U.submatrix ι g).det‖ ^ 2 + ‖(V.submatrix g κ).det‖ ^ 2) / 2) := by
        refine Finset.sum_le_sum (fun g hg => ?_)
        have hgm : StrictMono g := by simpa [hF] using hg
        have hp : ‖(∏ j, ((s (g j) : ℂ)))‖ ≤ Sk := by
          rw [norm_prod]
          refine Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => ?_)
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hs0 _)]
          exact hanti (by simpa [Fin.le_def] using strictMono_le_apply hgm j)
        rw [norm_mul, norm_mul]
        have h2 : ‖(U.submatrix ι g).det‖ * ‖(V.submatrix g κ).det‖
            ≤ (‖(U.submatrix ι g).det‖ ^ 2 + ‖(V.submatrix g κ).det‖ ^ 2) / 2 := by
          nlinarith [sq_nonneg (‖(U.submatrix ι g).det‖ - ‖(V.submatrix g κ).det‖)]
        have h3 : ‖(∏ j, ((s (g j) : ℂ)))‖ * (‖(U.submatrix ι g).det‖ * ‖(V.submatrix g κ).det‖)
            ≤ Sk * (‖(U.submatrix ι g).det‖ * ‖(V.submatrix g κ).det‖) :=
          mul_le_mul_of_nonneg_right hp (by positivity)
        exact h3.trans (mul_le_mul_of_nonneg_left h2 hSk0)
    _ = Sk := by rw [← Finset.mul_sum, hsum, mul_one]

/-! ### Top products -/

/-- The product of the first `k` entries of `f`. -/
def topProd (f : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), f i

lemma filter_lt_eq_image_castLE (hk : k ≤ n) :
    univ.filter (fun i : Fin n => (i : ℕ) < k) = univ.image (Fin.castLE hk) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  exact ⟨fun h => ⟨⟨(i : ℕ), h⟩, rfl⟩, by rintro ⟨a, rfl⟩; simp⟩

lemma card_filter_lt (hk : k ≤ n) :
    (univ.filter (fun i : Fin n => (i : ℕ) < k)).card = k := by
  rw [filter_lt_eq_image_castLE hk, Finset.card_image_of_injective _ (Fin.castLE_injective hk)]
  simp

lemma topProd_eq_prod_castLE (hk : k ≤ n) (f : Fin n → ℝ) :
    topProd f k = ∏ p : Fin k, f (Fin.castLE hk p) := by
  rw [topProd, filter_lt_eq_image_castLE hk,
    Finset.prod_image (fun a _ b _ h => Fin.castLE_injective hk h)]

lemma topProd_nonneg {f : Fin n → ℝ} (h0 : ∀ i, 0 ≤ f i) (k : ℕ) : 0 ≤ topProd f k :=
  Finset.prod_nonneg fun i _ => h0 i

/-- For a nonnegative antitone family, the product over any set of `k` indices is at most the
product of the first `k` entries. -/
lemma prod_le_topProd {f : Fin n → ℝ} (h0 : ∀ i, 0 ≤ f i) (hanti : Antitone f)
    (I : Finset (Fin n)) : ∏ i ∈ I, f i ≤ topProd f I.card := by
  have hk : I.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ I)
  have e1 := Finset.prod_image (s := (univ : Finset (Fin I.card))) (f := f)
    (g := fun p => I.orderEmbOfFin rfl p) (fun a _ b _ h => (I.orderEmbOfFin rfl).injective h)
  rw [Finset.image_orderEmbOfFin_univ] at e1
  rw [topProd_eq_prod_castLE hk, e1]
  refine Finset.prod_le_prod (fun i _ => h0 _) (fun p _ => hanti ?_)
  have h2 : (p : ℕ) ≤ (I.orderEmbOfFin rfl p : ℕ) :=
    strictMono_le_apply (I.orderEmbOfFin rfl).strictMono p
  simpa [Fin.le_def] using h2

/-! ### Weak log-majorization -/

/-- `LogMajLE s a` : every product of entries of `a` over a finite index set `I` is dominated
by the product of the entries of `s` over some index set of the same cardinality.  For
nonnegative antitone `s` and `a` this is the usual weak log-majorization `a ≺_{log} s`. -/
def LogMajLE (s a : Fin n → ℝ) : Prop :=
  ∀ I : Finset (Fin n), ∃ J : Finset (Fin n), J.card = I.card ∧ ∏ i ∈ I, a i ≤ ∏ j ∈ J, s j

lemma LogMajLE.perm {s a : Fin n → ℝ} (h : LogMajLE s a) (t p : Equiv.Perm (Fin n)) :
    LogMajLE (s ∘ t) (a ∘ p) := by
  intro I
  obtain ⟨J, hJ, hle⟩ := h (I.image p)
  refine ⟨J.image t.symm, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ t.symm.injective, hJ,
      Finset.card_image_of_injective _ p.injective]
  · rw [Finset.prod_image (fun x _ y _ hxy => t.symm.injective hxy)]
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    rw [Finset.prod_image (fun x _ y _ hxy => p.injective hxy)] at hle
    exact hle

/-- For nonnegative antitone data, weak log-majorization follows from the usual condition on
the products of the largest entries. -/
lemma logMajLE_of_topProd {s a : Fin n → ℝ} (h0 : ∀ i, 0 ≤ a i) (hanti : Antitone a)
    (h : ∀ k, topProd a k ≤ topProd s k) : LogMajLE s a := by
  intro I
  have hk : I.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ I)
  exact ⟨univ.filter (fun i : Fin n => (i : ℕ) < I.card), card_filter_lt hk,
    (prod_le_topProd h0 hanti I).trans (h I.card)⟩

/-- Necessity: if `A` is upper triangular with singular values `s` (decreasing), then the
product of the moduli of any `k` diagonal entries is at most `s₀ ⋯ s_{k-1}`. -/
theorem prod_norm_diag_le {A : Matrix (Fin n) (Fin n) ℂ} {s : Fin n → ℝ}
    (hA : HasSV A s) (hs0 : ∀ i, 0 ≤ s i) (hanti : Antitone s)
    (htri : A.BlockTriangular id) (I : Finset (Fin n)) :
    ∏ i ∈ I, ‖A i i‖ ≤ topProd s I.card := by
  classical
  have hk : I.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ I)
  set ι := I.orderEmbOfFin (rfl : I.card = I.card) with hιdef
  have hmono : StrictMono ι := (I.orderEmbOfFin rfl).strictMono
  have hinj : Function.Injective ι := (I.orderEmbOfFin rfl).injective
  have htri' : (A.submatrix ι ι).BlockTriangular id := fun p q hpq => htri (hmono hpq)
  have hdet : (A.submatrix ι ι).det = ∏ p, A (ι p) (ι p) :=
    Matrix.det_of_upperTriangular htri'
  have h1 : ∏ i ∈ I, ‖A i i‖ = ‖(A.submatrix ι ι).det‖ := by
    rw [hdet, norm_prod]
    have e1 := Finset.prod_image (s := (univ : Finset (Fin I.card)))
      (f := fun i => ‖A i i‖) (g := fun p => ι p) (fun a _ b _ h => hinj h)
    rw [Finset.image_orderEmbOfFin_univ] at e1
    exact e1
  rw [h1, topProd_eq_prod_castLE hk]
  exact norm_det_submatrix_le hk hA hs0 hanti hinj hinj

end Q730
