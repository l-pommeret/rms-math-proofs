import RMS.Q730f

/-!
# Q730, part g : the classification
-/

namespace Q730

open Matrix Finset BigOperators

variable {n : ℕ}

/-- Two matrices with the same singular values are unitarily equivalent. -/
lemma hasSV_eq {A M : Matrix (Fin n) (Fin n) ℂ} {s : Fin n → ℝ} (hA : HasSV A s)
    (hM : HasSV M s) :
    ∃ U V : Matrix (Fin n) (Fin n) ℂ, U ∈ unitaryGroup (Fin n) ℂ ∧ V ∈ unitaryGroup (Fin n) ℂ ∧
      A = U * M * V := by
  obtain ⟨U₁, V₁, hU₁, hV₁, hA'⟩ := hA
  obtain ⟨U₂, V₂, hU₂, hV₂, hM'⟩ := hM
  refine ⟨U₁ * U₂ᴴ, V₂ᴴ * V₁, ?_, ?_, ?_⟩
  · exact Submonoid.mul_mem _ hU₁ (unitary_conjTranspose hU₂)
  · exact Submonoid.mul_mem _ (unitary_conjTranspose hV₂) hV₁
  · have h1 : U₂ᴴ * U₂ = 1 := by
      have := hU₂
      rw [Matrix.mem_unitaryGroup_iff'] at this
      rwa [Matrix.star_eq_conjTranspose] at this
    have h2 : V₂ * V₂ᴴ = 1 := by
      have := hV₂
      rw [Matrix.mem_unitaryGroup_iff] at this
      rwa [Matrix.star_eq_conjTranspose] at this
    calc A = U₁ * diagonal (fun i => ((s i : ℝ) : ℂ)) * V₁ := hA'
      _ = U₁ * (U₂ᴴ * U₂) * diagonal (fun i => ((s i : ℝ) : ℂ)) * (V₂ * V₂ᴴ) * V₁ := by
          rw [h1, h2]; simp
      _ = U₁ * U₂ᴴ * (U₂ * diagonal (fun i => ((s i : ℝ) : ℂ)) * V₂) * (V₂ᴴ * V₁) := by
          simp only [Matrix.mul_assoc]
      _ = U₁ * U₂ᴴ * M * (V₂ᴴ * V₁) := by rw [← hM']
      _ = U₁ * U₂ᴴ * M * (V₂ᴴ * V₁) := rfl

/-- The index map used to select the `r` first rows/columns together with one extra one. -/
def extIdx {r : ℕ} (hr1 : r + 1 ≤ n) (i : Fin n) : Fin (r + 1) → Fin n :=
  fun p => if (p : ℕ) < r then Fin.castLE hr1 p else i

lemma extIdx_of_lt {r : ℕ} (hr1 : r + 1 ≤ n) (i : Fin n) {p : Fin (r + 1)} (hp : (p : ℕ) < r) :
    extIdx hr1 i p = Fin.castLE hr1 p := by
  rw [extIdx, if_pos hp]

lemma extIdx_last {r : ℕ} (hr1 : r + 1 ≤ n) (i : Fin n) :
    extIdx hr1 i (Fin.last r) = i := by
  rw [extIdx, if_neg (by simp)]

lemma extIdx_val {r : ℕ} (hr1 : r + 1 ≤ n) (i : Fin n) (p : Fin (r + 1)) :
    (extIdx hr1 i p : ℕ) = if (p : ℕ) < r then (p : ℕ) else (i : ℕ) := by
  rw [extIdx]
  split <;> simp

lemma extIdx_injective {r : ℕ} (hr1 : r + 1 ≤ n) {i : Fin n} (hi : r ≤ (i : ℕ)) :
    Function.Injective (extIdx hr1 i) := by
  intro p q hpq
  have h := congrArg (fun x : Fin n => (x : ℕ)) hpq
  simp only [extIdx_val] at h
  have hp := p.2
  have hq := q.2
  refine Fin.ext ?_
  split at h <;> split at h <;> omega

/-- If an upper triangular matrix with singular values `s` has nonzero first `r` diagonal
entries and `s` vanishes from index `r` on, then all rows from index `r` on vanish. -/
theorem rows_zero {A : Matrix (Fin n) (Fin n) ℂ} {s : Fin n → ℝ} (hA : HasSV A s)
    (hs0 : ∀ i, 0 ≤ s i) (hanti : Antitone s) (htri : A.BlockTriangular id)
    {r : ℕ} (hr : r < n) (hpos : ∀ p : Fin n, (p : ℕ) < r → A p p ≠ 0)
    (hzero : ∀ p : Fin n, r ≤ (p : ℕ) → s p = 0) :
    ∀ i j : Fin n, r ≤ (i : ℕ) → A i j = 0 := by
  intro i j hi
  by_cases hj : (j : ℕ) < r
  · exact htri (show id j < id i from Fin.lt_def.2 (lt_of_lt_of_le hj hi))
  push_neg at hj
  have hr1 : r + 1 ≤ n := hr
  set ι := extIdx hr1 i with hιdef
  set κ := extIdx hr1 j with hκdef
  have hιinj : Function.Injective ι := extIdx_injective hr1 hi
  have hκinj : Function.Injective κ := extIdx_injective hr1 hj
  -- the submatrix is upper triangular
  have hsub_tri : (A.submatrix ι κ).BlockTriangular id := by
    intro p q hqp
    have hq : (q : ℕ) < (p : ℕ) := hqp
    apply htri
    show ((κ q : Fin n) : ℕ) < ((ι p : Fin n) : ℕ)
    rw [extIdx_val, extIdx_val]
    have hqr : (q : ℕ) < r := by
      have := p.2
      omega
    rw [if_pos hqr]
    split
    · omega
    · omega
  have hdet : (A.submatrix ι κ).det = (∏ p : Fin r, A (Fin.castLE hr.le p) (Fin.castLE hr.le p))
      * A i j := by
    rw [Matrix.det_of_upperTriangular hsub_tri, Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl (fun p _ => ?_)
      have hp : ((p.castSucc : Fin (r + 1)) : ℕ) < r := p.2
      simp only [Matrix.submatrix_apply, hιdef, hκdef]
      rw [extIdx_of_lt hr1 i hp, extIdx_of_lt hr1 j hp]
      congr 1
    · simp only [Matrix.submatrix_apply, hιdef, hκdef]
      rw [extIdx_last, extIdx_last]
  have hbound : ‖(A.submatrix ι κ).det‖ ≤ ∏ p : Fin (r + 1), s (Fin.castLE hr1 p) :=
    norm_det_submatrix_le hr1 hA hs0 hanti hιinj hκinj
  have hzeroprod : (∏ p : Fin (r + 1), s (Fin.castLE hr1 p)) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ (Fin.last r)) ?_
    refine hzero _ ?_
    simp
  rw [hzeroprod] at hbound
  have hdet0 : (A.submatrix ι κ).det = 0 := by
    have := norm_nonneg ((A.submatrix ι κ).det)
    have h : ‖(A.submatrix ι κ).det‖ = 0 := le_antisymm hbound this
    exact norm_eq_zero.1 h
  rw [hdet] at hdet0
  rcases mul_eq_zero.1 hdet0 with h | h
  · exact absurd h (Finset.prod_ne_zero_iff.2 (fun p _ => hpos _ (by simp)))
  · exact h

lemma topProd_eq_prod {f : Fin n → ℝ} {k : ℕ} (hk : n ≤ k) : topProd f k = ∏ i, f i := by
  rw [topProd]
  congr 1
  refine Finset.filter_true_of_mem (fun i _ => ?_)
  exact lt_of_lt_of_le i.2 hk

lemma topProd_eq_zero_of_mem {f : Fin n → ℝ} {k : ℕ} {i : Fin n} (hi : (i : ℕ) < k)
    (hfi : f i = 0) : topProd f k = 0 := by
  rw [topProd]
  exact Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩) hfi

/-- A nonnegative antitone rearrangement of a family which is positive exactly below `r`
vanishes from index `r` on. -/
lemma antitone_rearrangement_eq_zero {t tau : Fin n → ℝ} {r : ℕ}
    (ht0 : ∀ i : Fin n, (i : ℕ) < r → 0 < t i) (ht1 : ∀ i : Fin n, r ≤ (i : ℕ) → t i = 0)
    (e : Equiv.Perm (Fin n)) (htau : tau = t ∘ e) (hanti : Antitone tau) :
    ∀ i : Fin n, r ≤ (i : ℕ) → tau i = 0 := by
  classical
  intro i hi
  by_contra hne
  have hrn : r ≤ n := le_trans hi (le_of_lt i.2)
  have htnonneg : ∀ j, 0 ≤ t j := by
    intro j
    by_cases h : (j : ℕ) < r
    · exact (ht0 j h).le
    · rw [ht1 j (by omega)]
  have hpos : 0 < tau i := lt_of_le_of_ne (by rw [htau]; exact htnonneg _) (Ne.symm hne)
  set S : Finset (Fin n) := univ.filter (fun j => tau j ≠ 0) with hS
  have hsub : univ.filter (fun j : Fin n => (j : ℕ) < (i : ℕ) + 1) ⊆ S := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hji : j ≤ i := Fin.le_def.2 (Nat.lt_succ_iff.1 hj.2)
    exact ne_of_gt (lt_of_lt_of_le hpos (hanti hji))
  have hcard1 : (i : ℕ) + 1 ≤ S.card := by
    calc (i : ℕ) + 1 = (univ.filter (fun j : Fin n => (j : ℕ) < (i : ℕ) + 1)).card :=
          (card_filter_lt (by omega)).symm
      _ ≤ S.card := Finset.card_le_card hsub
  have himg : S.image e = univ.filter (fun j : Fin n => t j ≠ 0) := by
    ext k
    simp only [Finset.mem_image, hS, Finset.mem_filter, Finset.mem_univ, true_and, htau,
      Function.comp_apply]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hk
      exact ⟨e.symm k, by simpa using hk, by simp⟩
  have hfilter : (univ.filter (fun j : Fin n => t j ≠ 0))
      = univ.filter (fun j : Fin n => (j : ℕ) < r) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_contra hjr
      push_neg at hjr
      exact h (ht1 j hjr)
    · intro h
      exact ne_of_gt (ht0 j h)
  have hScard : S.card = r := by
    rw [← Finset.card_image_of_injective S e.injective, himg, hfilter]
    exact card_filter_lt hrn
  omega


/-! ### Two bridges between `LogMajLE` and top products -/

lemma norm_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ‖((x : ℝ) : ℂ)‖ = x := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]

/-- Weak log-majorization implies the prefix product inequalities. -/
lemma topProd_le_topProd_of_logMajLE {s a : Fin n → ℝ} (hs0 : ∀ i, 0 ≤ s i)
    (hsanti : Antitone s) (hmaj : LogMajLE s a) {k : ℕ} (hk : k ≤ n) :
    topProd a k ≤ topProd s k := by
  classical
  obtain ⟨J, hJ, hle⟩ := hmaj (univ.filter (fun i : Fin n => (i : ℕ) < k))
  rw [card_filter_lt hk] at hJ
  calc topProd a k = ∏ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), a i := rfl
    _ ≤ ∏ j ∈ J, s j := hle
    _ ≤ topProd s J.card := prod_le_topProd hs0 hsanti J
    _ = topProd s k := by rw [hJ]

/-- The diagonal of an upper triangular matrix is weakly log-majorized by its singular
values. -/
lemma logMajLE_norm_diag_of_upperTriangular {A : Matrix (Fin n) (Fin n) ℂ} {s : Fin n → ℝ}
    (hA : HasSV A s) (hs0 : ∀ i, 0 ≤ s i) (hsanti : Antitone s)
    (htri : A.BlockTriangular id) :
    LogMajLE s (fun i => ‖A i i‖) := by
  classical
  intro I
  have hk : I.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ I)
  exact ⟨univ.filter (fun i : Fin n => (i : ℕ) < I.card), card_filter_lt hk,
    prod_norm_diag_le hA hs0 hsanti htri I⟩

lemma topProd_zero (f : Fin n → ℝ) : topProd f 0 = 1 := by
  rw [topProd]
  simp

/-! ### The requested block form -/

/-- The conclusion of Q730 in coordinates: there are unitary `U`, `V` such that `U * M * V`
is upper triangular with diagonal exactly `t` (in that order) and all rows of index at least
`r` vanish.  Equivalently `U * M * V = ((T, B), (0, 0))` with `T` upper triangular of order
`r` and diagonal `t₀, …, t_{r-1}`. -/
def Q730BlockForm (M : Matrix (Fin n) (Fin n) ℂ) (t : Fin n → ℝ) (r : ℕ) : Prop :=
  ∃ U V : Matrix (Fin n) (Fin n) ℂ,
    U ∈ unitaryGroup (Fin n) ℂ ∧
    V ∈ unitaryGroup (Fin n) ℂ ∧
    (U * M * V).BlockTriangular id ∧
    (∀ i, (U * M * V) i i = (t i : ℂ)) ∧
    ∀ i j : Fin n, r ≤ (i : ℕ) → (U * M * V) i j = 0

/-! ### The classification -/

/-- **Q730.**  Let `M` be an `n × n` complex matrix with singular value list `s`, nonnegative
and decreasing, positive exactly below `r` and zero from `r` on (so `M` has rank `r`), and let
`t` be positive below `r` and zero from `r` on, with decreasing rearrangement `tau = t ∘ e`.
Then unitary `U, V` with `U * M * V` upper triangular, with diagonal exactly `t`, and with
vanishing rows from index `r` on, exist if and only if `tau` is weakly log-majorized by `s`
(`∏_{i<k} tau i ≤ ∏_{i<k} s i` for `1 ≤ k ≤ r`), together with `∏ i, t i = ‖det M‖` in the
full-rank case `r = n`.

The hypothesis `hspos` (that `s` is positive below `r`) is part of the requested statement,
encoding that `M` has rank exactly `r`; the proof does not in fact need it. -/
theorem Q730_classification
    {M : Matrix (Fin n) (Fin n) ℂ} {s t tau : Fin n → ℝ} {r : ℕ}
    (hr : r ≤ n)
    (hM : HasSV M s)
    (hs0 : ∀ i, 0 ≤ s i)
    (hsanti : Antitone s)
    (hspos : ∀ i : Fin n, (i : ℕ) < r → 0 < s i)
    (hszero : ∀ i : Fin n, r ≤ (i : ℕ) → s i = 0)
    (htpos : ∀ i : Fin n, (i : ℕ) < r → 0 < t i)
    (htzero : ∀ i : Fin n, r ≤ (i : ℕ) → t i = 0)
    (e : Equiv.Perm (Fin n))
    (htau : tau = t ∘ e)
    (htauanti : Antitone tau) :
    Q730BlockForm M t r ↔
      ((∀ k : ℕ, 1 ≤ k → k ≤ r → topProd tau k ≤ topProd s k) ∧
       (r = n → ∏ i, t i = ‖M.det‖)) := by
  classical
  have ht0 : ∀ i, 0 ≤ t i := by
    intro i
    by_cases h : (i : ℕ) < r
    · exact (htpos i h).le
    · rw [htzero i (by omega)]
  have htau0 : ∀ i, 0 ≤ tau i := by
    intro i; rw [htau]; exact ht0 _
  have htauzero : ∀ i : Fin n, r ≤ (i : ℕ) → tau i = 0 :=
    antitone_rearrangement_eq_zero htpos htzero e htau htauanti
  have hnormt : (fun i => ‖((t i : ℝ) : ℂ)‖) = t := by
    funext i; exact norm_ofReal_of_nonneg (ht0 i)
  have hnorms : (fun i => ‖s i‖) = s := by
    funext i; exact abs_of_nonneg (hs0 i)
  constructor
  · -- necessity
    rintro ⟨U, V, hU, hV, htri, hdiag, _hlow⟩
    set A : Matrix (Fin n) (Fin n) ℂ := U * M * V with hA
    have hAsv : HasSV A s := hM.mul_unitary hU hV
    have hmaj : LogMajLE s (fun i => ‖A i i‖) :=
      logMajLE_norm_diag_of_upperTriangular hAsv hs0 hsanti htri
    have hmaj' : LogMajLE s t := by
      have hfun : (fun i => ‖A i i‖) = t := by
        funext i; rw [hdiag i]; exact norm_ofReal_of_nonneg (ht0 i)
      rwa [hfun] at hmaj
    have hmajtau : LogMajLE s tau := by
      have := hmaj'.perm 1 e
      simpa [htau] using this
    -- the determinant identity
    have hdetA : ‖A.det‖ = ∏ i, t i := by
      rw [Matrix.det_of_upperTriangular htri, norm_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [hdiag i]; exact norm_ofReal_of_nonneg (ht0 i)
    have hdetM : ∏ i, t i = ‖M.det‖ := by
      rw [← hdetA, hAsv.norm_det, hM.norm_det]
    refine ⟨fun k _ hkr => topProd_le_topProd_of_logMajLE hs0 hsanti hmajtau (hkr.trans hr),
      fun _ => hdetM⟩
  · -- sufficiency
    rintro ⟨hineq, hdet⟩
    have hall : ∀ k, topProd tau k ≤ topProd s k := by
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · rw [topProd_zero, topProd_zero]
      by_cases hkr : k ≤ r
      · exact hineq k hk1 hkr
      push_neg at hkr
      rcases lt_or_eq_of_le hr with hrn | hrn
      · have hz : topProd tau k = 0 :=
          topProd_eq_zero_of_mem (i := ⟨r, hrn⟩) (by simpa using hkr)
            (htauzero ⟨r, hrn⟩ (le_refl _))
        rw [hz]
        exact topProd_nonneg hs0 k
      · have hnk : n ≤ k := by omega
        have h1 : topProd tau k = ∏ i, tau i := topProd_eq_prod hnk
        have h2 : topProd s k = ∏ i, s i := topProd_eq_prod hnk
        have h3 : ∏ i, tau i = ∏ i, t i := by
          rw [htau]; exact Equiv.prod_comp e t
        have h4 : ∏ i, t i = ∏ i, s i := by
          rw [hdet hrn, hM.norm_det, hnorms]
        rw [h1, h2, h3, h4]
    have hmajtau : LogMajLE s tau := logMajLE_of_topProd htau0 htauanti hall
    have hmajt : LogMajLE s t := by
      have := hmajtau.perm 1 e.symm
      have hcomp : tau ∘ (e.symm : Fin n → Fin n) = t := by
        funext i; simp [htau]
      simpa [hcomp] using this
    have hmaj2 : LogMajLE s (fun i => ‖((t i : ℝ) : ℂ)‖) := by rwa [hnormt]
    have hprod : ∏ i, ‖((t i : ℝ) : ℂ)‖ = ∏ i, s i := by
      rw [hnormt]
      rcases lt_or_eq_of_le hr with hrn | hrn
      · rw [Finset.prod_eq_zero (Finset.mem_univ (⟨r, hrn⟩ : Fin n))
            (htzero ⟨r, hrn⟩ (le_refl _)),
          Finset.prod_eq_zero (Finset.mem_univ (⟨r, hrn⟩ : Fin n))
            (hszero ⟨r, hrn⟩ (le_refl _))]
      · rw [hdet hrn, hM.norm_det, hnorms]
    obtain ⟨A, hAsv, hAtri, hAdiag⟩ := WH_core n s (fun i => ((t i : ℝ) : ℂ)) hs0 hmaj2 hprod
    obtain ⟨U, V, hU, hV, hAeq⟩ := hasSV_eq hAsv hM
    refine ⟨U, V, hU, hV, ?_, ?_, ?_⟩
    · rw [← hAeq]; exact hAtri
    · intro i; rw [← hAeq]; exact hAdiag i
    · intro i j hi
      rw [← hAeq]
      rcases lt_or_eq_of_le hr with hrn | hrn
      · refine rows_zero hAsv hs0 hsanti hAtri hrn ?_ hszero i j hi
        intro p hp
        rw [hAdiag p]
        exact_mod_cast ne_of_gt (htpos p hp)
      · exact absurd i.2 (by omega)

end Q730
