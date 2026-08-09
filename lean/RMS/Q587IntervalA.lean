/-
# Q587 — the arbitrary-interval layer, part 2 (Gate 2): descent and part (a)

Relative versions, on an arbitrary nondegenerate interval `I` (endpoints included), of the
descent lemma (Lemma 2.1) and of part (a): convergence of the top coefficient alone implies
convergence of **all** monomial coefficients `c_q` of the Lagrange interpolation polynomial.
-/

import RMS.Q587Interval

open Polynomial Finset

namespace Q587

variable {I : Set ℝ}

/-- Relative version of `ddiff_compare`: two divided differences of the same order over nodes of
`I` in a small relative neighborhood are close, provided the divided differences of the next
order over nodes of `I` are bounded there. -/
lemma ddiff_compareOn (f : ℝ → ℝ) (x ρ M : ℝ) (hρ : 0 < ρ) (hM : 0 ≤ M) (r : ℕ)
    (hbd : ∀ s : Finset ℝ, s.card = r + 1 → ↑s ⊆ I → (∀ t ∈ s, |t - x| < ρ) → |ddiff f s| ≤ M) :
    ∀ (k : ℕ) (A B : Finset ℝ), (A \ B).card ≤ k → A.card = r → B.card = r →
      (↑A ⊆ I) → (↑B ⊆ I) → (∀ t ∈ A, |t - x| < ρ) → (∀ t ∈ B, |t - x| < ρ) →
      |ddiff f A - ddiff f B| ≤ k * (2 * ρ * M) := by
  intro k
  induction k with
  | zero =>
    intro A B hk hA hB _ _ _ _
    have h0 : A \ B = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hk)
    have hAB : A = B :=
      Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.1 h0) (by omega)
    simp [hAB]
  | succ k ih =>
    intro A B hk hA hB hAI hBI hAx hBx
    by_cases hAB : A = B
    · simp only [hAB, sub_self, abs_zero]
      positivity
    · have hne : (A \ B).Nonempty := by
        rw [Finset.sdiff_nonempty]
        intro hsub
        exact hAB (Finset.eq_of_subset_of_card_le hsub (by omega))
      obtain ⟨a, ha'⟩ := hne
      have hne2 : (B \ A).Nonempty := by
        rw [Finset.sdiff_nonempty]
        intro hsub
        exact hAB ((Finset.eq_of_subset_of_card_le hsub (by omega)).symm)
      obtain ⟨c, hc⟩ := hne2
      have ha := ha'
      rw [Finset.mem_sdiff] at ha hc
      have hr1 : 1 ≤ r := by rw [← hA]; exact Finset.card_pos.2 ⟨a, ha.1⟩
      set A' : Finset ℝ := insert c (A.erase a) with hA'
      have hcA : c ∉ A.erase a := fun h => hc.2 (Finset.mem_of_mem_erase h)
      have haA : a ∉ A.erase a := Finset.notMem_erase a A
      have hac : a ≠ c := fun h => hc.2 (h ▸ ha.1)
      have hcardA' : A'.card = r := by
        rw [hA', Finset.card_insert_of_notMem hcA, Finset.card_erase_of_mem ha.1, hA]
        omega
      have hAins : A = insert a (A.erase a) := (Finset.insert_erase ha.1).symm
      have hA'I : (↑A' : Set ℝ) ⊆ I := by
        intro z hz
        have hz' : z ∈ A' := hz
        rcases Finset.mem_insert.1 hz' with rfl | hz2
        · exact hBI hc.1
        · exact hAI (Finset.mem_of_mem_erase hz2)
      have hstep : |ddiff f A - ddiff f A'| ≤ 2 * ρ * M := by
        have hrep := ddiff_replace f (A.erase a) a c haA hcA hac
        rw [← hAins] at hrep
        rw [hrep, abs_mul]
        have h1 : |a - c| ≤ 2 * ρ := by
          have h3 := hAx a ha.1
          have h4 := hBx c hc.1
          rw [abs_sub_lt_iff] at h3 h4
          rw [abs_le]; constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]
        have h2 : |ddiff f (insert a (insert c (A.erase a)))| ≤ M := by
          refine hbd _ ?_ ?_ ?_
          · rw [Finset.card_insert_of_notMem (by simp [hac, haA]), hcardA']
          · intro z hz
            have hz' : z ∈ insert a (insert c (A.erase a)) := hz
            rcases Finset.mem_insert.1 hz' with rfl | hz2
            · exact hAI ha.1
            · exact hA'I hz2
          · intro t ht
            rcases Finset.mem_insert.1 ht with rfl | ht
            · exact hAx t ha.1
            · rcases Finset.mem_insert.1 ht with rfl | ht
              · exact hBx t hc.1
              · exact hAx t (Finset.mem_of_mem_erase ht)
        calc |a - c| * |ddiff f (insert a (insert c (A.erase a)))|
            ≤ (2 * ρ) * M := mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
          _ = 2 * ρ * M := by ring
      have hsub' : A' \ B ⊆ (A \ B).erase a := by
        intro z hz
        rw [Finset.mem_sdiff] at hz
        rcases Finset.mem_insert.1 hz.1 with rfl | hz2
        · exact absurd hc.1 hz.2
        · exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hz2).1,
            Finset.mem_sdiff.2 ⟨Finset.mem_of_mem_erase hz2, hz.2⟩⟩
      have hcard' : (A' \ B).card ≤ k := by
        have h5 := Finset.card_le_card hsub'
        rw [Finset.card_erase_of_mem ha'] at h5
        omega
      have hA'x : ∀ t ∈ A', |t - x| < ρ := by
        intro t ht
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact hBx t hc.1
        · exact hAx t (Finset.mem_of_mem_erase ht)
      have hIH := ih A' B hcard' hcardA' hB hA'I hBI hA'x hBx
      have htri : |ddiff f A - ddiff f B|
          ≤ |ddiff f A - ddiff f A'| + |ddiff f A' - ddiff f B| := by
        calc |ddiff f A - ddiff f B| = |(ddiff f A - ddiff f A') + (ddiff f A' - ddiff f B)| := by
              ring_nf
          _ ≤ _ := abs_add_le _ _
      push_cast
      push_cast at hIH
      nlinarith [hIH, hstep, htri]

/-- Relative Lemma 2.1: boundedness of the divided differences of order `m+1` over nodes of `I`
near `x` implies convergence of the relative divided differences of order `m`. -/
lemma exists_ddLimOn_of_bdd (hI : I.OrdConnected) (hne : I.Nontrivial) (f : ℝ → ℝ)
    (x M ρ0 : ℝ) (hx : x ∈ I) (hρ0 : 0 < ρ0) (hM : 0 ≤ M) (m : ℕ)
    (hbd : ∀ s : Finset ℝ, s.card = m + 2 → ↑s ⊆ I → (∀ t ∈ s, |t - x| < ρ0) → |ddiff f s| ≤ M) :
    ∃ L, DDLimOn I f m x L := by
  set ρ : ℕ → ℝ := fun j => min ρ0 (1 / (j + 1)) with hρdef
  have hρpos : ∀ j, 0 < ρ j := fun j => lt_min hρ0 (by positivity)
  have hρmono : ∀ i j : ℕ, i ≤ j → ρ j ≤ ρ i := by
    intro i j hij
    apply min_le_min le_rfl
    gcongr
  have hρ0' : Filter.Tendsto ρ Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun n => le_of_lt (hρpos n)) (fun n => min_le_right _ _)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hcomp : ∀ (j : ℕ) (A B : Finset ℝ), A.card = m + 1 → B.card = m + 1 →
      (↑A ⊆ I) → (↑B ⊆ I) →
      (∀ t ∈ A, |t - x| < ρ j) → (∀ t ∈ B, |t - x| < ρ j) →
      |ddiff f A - ddiff f B| ≤ ((m : ℝ) + 1) * (2 * ρ j * M) := by
    intro j A B hA hB hAI hBI hAx hBx
    have hcc := ddiff_compareOn f x (ρ j) M (hρpos j) hM (m + 1) ?_ (m + 1) A B ?_ hA hB
      hAI hBI hAx hBx
    · push_cast at hcc; linarith
    · intro s hs hsI hsx
      exact hbd s (by omega) hsI (fun t ht => lt_of_lt_of_le (hsx t ht) (min_le_left _ _))
    · calc (A \ B).card ≤ A.card := Finset.card_le_card (Finset.sdiff_subset)
        _ = m + 1 := hA
  choose S hScard hSI hSx _ using fun j =>
    exists_nodesOn' hI hne hx (hρpos j) (m + 1) ∅
  set a : ℕ → ℝ := fun j => ddiff f (S j) with hadef
  have hcauchy : CauchySeq a := by
    refine cauchySeq_of_le_tendsto_0 (fun N => ((m : ℝ) + 1) * (2 * ρ N * M)) ?_ ?_
    · intro n1 n2 N h1 h2
      rw [Real.dist_eq]
      exact hcomp N (S n1) (S n2) (hScard n1) (hScard n2) (hSI n1) (hSI n2)
        (fun t ht => lt_of_lt_of_le (hSx n1 t ht) (hρmono N n1 h1))
        (fun t ht => lt_of_lt_of_le (hSx n2 t ht) (hρmono N n2 h2))
    · have hh := hρ0'.const_mul (((m : ℝ) + 1) * (2 * M))
      simp only [mul_zero] at hh
      convert hh using 2 with N
      ring
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨L, ?_⟩
  intro ε hε
  obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ, ρ N ≤ ε / (4 * ((m : ℝ) + 1) * (M + 1)) ∧ |a N - L| < ε / 2 := by
    have hpos : (0:ℝ) < ε / (4 * ((m : ℝ) + 1) * (M + 1)) := by positivity
    have hev1 : ∀ᶠ N : ℕ in Filter.atTop, ρ N ≤ ε / (4 * ((m : ℝ) + 1) * (M + 1)) :=
      hρ0'.eventually (eventually_le_nhds hpos)
    have hev2 : ∀ᶠ N : ℕ in Filter.atTop, |a N - L| < ε / 2 := by
      rw [Metric.tendsto_atTop] at hL
      obtain ⟨N0, hN0⟩ := hL (ε/2) (by linarith)
      filter_upwards [Filter.eventually_ge_atTop N0] with n hn
      have := hN0 n hn
      rwa [Real.dist_eq] at this
    exact (hev1.and hev2).exists
  refine ⟨ρ N, hρpos N, fun s hs hsI hsx => ?_⟩
  have h1 : |ddiff f s - a N| ≤ ((m : ℝ) + 1) * (2 * ρ N * M) :=
    hcomp N s (S N) hs (hScard N) hsI (hSI N) hsx (hSx N)
  have h2 : ((m : ℝ) + 1) * (2 * ρ N * M) < ε / 2 := by
    have hmm : (0:ℝ) < (m:ℝ) + 1 := by positivity
    have hMM : (0:ℝ) < M + 1 := by linarith
    have hstep : ((m : ℝ) + 1) * (2 * ρ N * M)
        ≤ ((m:ℝ) + 1) * (2 * (ε / (4 * ((m:ℝ) + 1) * (M + 1))) * M) := by
      apply mul_le_mul_of_nonneg_left _ hmm.le
      apply mul_le_mul_of_nonneg_right _ hM
      linarith [hN1]
    have h3 : ((m:ℝ) + 1) * (2 * (ε / (4 * ((m:ℝ) + 1) * (M + 1))) * M) = ε * M / (2*(M+1)) := by
      field_simp; ring
    have h4 : ε * M / (2*(M+1)) < ε / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  calc |ddiff f s - L| ≤ |ddiff f s - a N| + |a N - L| := by
        calc |ddiff f s - L| = |(ddiff f s - a N) + (a N - L)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
    _ < ε := by linarith

/-- One step of relative descent. -/
lemma ddLimOn_descent (hI : I.OrdConnected) (hne : I.Nontrivial) (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I)
    (m : ℕ) (h : ∃ L, DDLimOn I f (m + 1) x L) : ∃ L, DDLimOn I f m x L := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨δ, hδ, hδ'⟩ := hL 1 one_pos
  refine exists_ddLimOn_of_bdd hI hne f x (|L| + 1) δ hx hδ (by positivity) m
    (fun s hs hsI hsx => ?_)
  have := hδ' s (by omega) hsI hsx
  calc |ddiff f s| = |(ddiff f s - L) + L| := by ring_nf
    _ ≤ |ddiff f s - L| + |L| := abs_add_le _ _
    _ ≤ |L| + 1 := by linarith

/-- Relative `DIT(n)` implies convergence of all the lower-order relative divided differences. -/
lemma exists_ddLimOn_of_le (hI : I.OrdConnected) (hne : I.Nontrivial) (f : ℝ → ℝ) (x : ℝ)
    (hx : x ∈ I) (n : ℕ) (h : HasDITOn I f n x) : ∀ k ≤ n, ∃ L, DDLimOn I f k x L := by
  induction n with
  | zero => intro k hk; rw [Nat.le_zero.1 hk]; exact h
  | succ n ih =>
    intro k hk
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · exact ih (ddLimOn_descent hI hne f x hx n h) k (by omega)
    · have : k = n + 1 := by omega
      rw [this]; exact h

/-- Relative version of `lagrEval_conv`: convergence of the values of the interpolating
polynomials at nodes of `I`. -/
lemma lagrEval_convOn (f : ℝ → ℝ) (x : ℝ) (lam : ℕ → ℝ) :
    ∀ (m : ℕ), (∀ k ≤ m, DDLimOn I f k x (lam k)) → ∀ (y ε : ℝ), 0 < ε →
    ∃ δ > 0, ∀ s : Finset ℝ, s.card = m + 1 → (↑s ⊆ I) → (∀ t ∈ s, |t - x| < δ) →
      |lagrEval f s y - ∑ k ∈ Finset.range (m+1), lam k * (y - x)^k| < ε := by
  intro m
  induction m with
  | zero =>
    intro h y ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h 0 le_rfl ε hε
    refine ⟨δ, hδ, fun s hs hsI hsx => ?_⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hs
    have h1 : lagrEval f {a} y = f a := by simp [lagrEval]
    have h2 : ddiff f {a} = f a := by simp [ddiff]
    have h3 := hδ' {a} hs hsI hsx
    rw [h2] at h3
    simpa [h1] using h3
  | succ m ih =>
    intro h y ε hε
    set B : ℝ := max 1 (|y - x| + 1) with hBdef
    have hB1 : 1 ≤ B := le_max_left _ _
    have hBpos : (0:ℝ) < B ^ (m+1) := by positivity
    obtain ⟨δ1, hδ1, hδ1'⟩ := h (m+1) le_rfl (ε / (4 * B ^ (m+1))) (by positivity)
    obtain ⟨δ2, hδ2, hδ2'⟩ := ih (fun k hk => h k (by omega)) y (ε/4) (by positivity)
    set C : ℝ := ((m:ℝ)+1) * B ^ (m+1) * (|lam (m+1)| + 1) with hCdef
    have hCpos : 0 < C := by positivity
    refine ⟨min (min δ1 δ2) (min 1 (ε / (4 * C))), by positivity, fun s hs hsI hsx => ?_⟩
    have hsx1 : ∀ t ∈ s, |t - x| < δ1 := fun t ht =>
      lt_of_lt_of_le (hsx t ht) (le_trans (min_le_left _ _) (min_le_left _ _))
    have hsx2 : ∀ t ∈ s, |t - x| < δ2 := fun t ht =>
      lt_of_lt_of_le (hsx t ht) (le_trans (min_le_left _ _) (min_le_right _ _))
    have hsxδ : ∀ t ∈ s, |t - x| ≤ min 1 (ε / (4*C)) := fun t ht =>
      le_of_lt (lt_of_lt_of_le (hsx t ht) (min_le_right _ _))
    obtain ⟨a, ha⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
    set t : Finset ℝ := s.erase a with htdef
    have hat : a ∉ t := Finset.notMem_erase a s
    have hst : s = insert a t := (Finset.insert_erase ha).symm
    have htcard : t.card = m + 1 := by rw [htdef, Finset.card_erase_of_mem ha, hs]; rfl
    have htI : (↑t : Set ℝ) ⊆ I := fun z hz => hsI (Finset.mem_of_mem_erase hz)
    have hkey : lagrEval f s y = lagrEval f t y + ddiff f s * ∏ u ∈ t, (y - u) := by
      have h4 := lagrEval_insert_sub f a t hat y
      rw [← hst] at h4
      linarith
    have hbB : |y - x| + min 1 (ε / (4*C)) ≤ B := by
      have h1 : min 1 (ε/(4*C)) ≤ 1 := min_le_left _ _
      calc |y - x| + min 1 (ε/(4*C)) ≤ |y-x| + 1 := by linarith
        _ ≤ B := le_max_right _ _
    have e1 : |lagrEval f t y - ∑ k ∈ Finset.range (m+1), lam k * (y - x)^k| < ε/4 :=
      hδ2' t htcard htI (fun z hz => hsx2 z (Finset.mem_of_mem_erase hz))
    have hdd : |ddiff f s - lam (m+1)| < ε / (4 * B ^ (m+1)) := hδ1' s hs hsI hsx1
    have hprodbd : |∏ u ∈ t, (y - u)| ≤ B ^ (m+1) := by
      have h5 := prod_abs_le x y (min 1 (ε/(4*C))) B hbB t
        (fun z hz => hsxδ z (Finset.mem_of_mem_erase hz))
      rwa [htcard] at h5
    have hproderr : |∏ u ∈ t, (y - u) - (y-x)^(m+1)|
        ≤ ((m:ℝ)+1) * (min 1 (ε/(4*C))) * B ^ (m+1) := by
      have h6 := prod_sub_pow_le x y (min 1 (ε/(4*C))) B (by positivity) hB1 hbB t
        (fun z hz => hsxδ z (Finset.mem_of_mem_erase hz))
      rw [htcard] at h6; push_cast at h6 ⊢; linarith
    have e2 : |ddiff f s * ∏ u ∈ t, (y - u) - lam (m+1) * (y-x)^(m+1)| < ε/2 := by
      have hsplit : ddiff f s * ∏ u ∈ t, (y - u) - lam (m+1) * (y-x)^(m+1)
          = (ddiff f s - lam (m+1)) * (∏ u ∈ t, (y - u))
            + lam (m+1) * ((∏ u ∈ t, (y - u)) - (y-x)^(m+1)) := by ring
      rw [hsplit]
      have t1 : |(ddiff f s - lam (m+1)) * (∏ u ∈ t, (y - u))| < ε/4 := by
        rw [abs_mul]
        calc |ddiff f s - lam (m+1)| * |∏ u ∈ t, (y - u)|
            ≤ |ddiff f s - lam (m+1)| * B ^ (m+1) :=
              mul_le_mul_of_nonneg_left hprodbd (abs_nonneg _)
          _ < (ε / (4 * B ^ (m+1))) * B ^ (m+1) := mul_lt_mul_of_pos_right hdd hBpos
          _ = ε/4 := by field_simp
      have t2 : |lam (m+1) * ((∏ u ∈ t, (y - u)) - (y-x)^(m+1))| ≤ ε/4 := by
        rw [abs_mul]
        calc |lam (m+1)| * |(∏ u ∈ t, (y - u)) - (y-x)^(m+1)|
            ≤ (|lam (m+1)| + 1) * (((m:ℝ)+1) * (min 1 (ε/(4*C))) * B ^ (m+1)) :=
              mul_le_mul (by linarith) hproderr (abs_nonneg _) (by positivity)
          _ ≤ ε/4 := by
              have hmin : min 1 (ε/(4*C)) ≤ ε/(4*C) := min_le_right _ _
              have hstep : (|lam (m+1)| + 1) * (((m:ℝ)+1) * (min 1 (ε/(4*C))) * B ^ (m+1))
                  ≤ (|lam (m+1)| + 1) * (((m:ℝ)+1) * (ε/(4*C)) * B ^ (m+1)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact mul_le_mul_of_nonneg_left hmin (by positivity)
              have hval : (|lam (m+1)| + 1) * (((m:ℝ)+1) * (ε/(4*C)) * B ^ (m+1)) = ε/4 := by
                rw [hCdef]; field_simp
              linarith
      calc |(ddiff f s - lam (m+1)) * (∏ u ∈ t, (y - u))
              + lam (m+1) * ((∏ u ∈ t, (y - u)) - (y-x)^(m+1))|
          ≤ _ := abs_add_le _ _
        _ < ε/2 := by linarith
    rw [Finset.sum_range_succ, hkey]
    calc |lagrEval f t y + ddiff f s * ∏ u ∈ t, (y - u)
            - (∑ k ∈ Finset.range (m+1), lam k * (y - x)^k + lam (m+1) * (y-x)^(m+1))|
        = |(lagrEval f t y - ∑ k ∈ Finset.range (m+1), lam k * (y - x)^k)
            + (ddiff f s * ∏ u ∈ t, (y - u) - lam (m+1) * (y-x)^(m+1))| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ < ε := by linarith

/-- **Part (a) on an interval**, the substantive half: if the relative divided differences of all
orders `k ≤ n` converge at `x`, then the interpolation polynomials at nodes of `I` converge
coefficientwise to `Q = ∑_{k≤n} λ_k (X-x)^k`. -/
theorem interpPoly_coeff_convOn (f : ℝ → ℝ) (x : ℝ) (n : ℕ) (lam : ℕ → ℝ)
    (h : ∀ k ≤ n, DDLimOn I f k x (lam k)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ s : Finset ℝ, s.card = n + 1 → (↑s ⊆ I) → (∀ t ∈ s, |t - x| < δ) →
      ∀ q, |(interpPoly f s).coeff q
        - (∑ k ∈ Finset.range (n+1), C (lam k) * (X - C x)^k).coeff q| < ε := by
  set Q : ℝ[X] := ∑ k ∈ Finset.range (n+1), C (lam k) * (X - C x)^k with hQ
  have hQdeg : Q.degree < ((n+1 : ℕ) : WithBot ℕ) := by
    have h1 : Q.degree ≤ (n : WithBot ℕ) := by
      refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun k hk => ?_)
      have hstep : (C (lam k) * (X - C x)^k).degree ≤ ((X - C x)^k : ℝ[X]).degree := by
        rw [← smul_eq_C_mul]; exact degree_smul_le _ _
      refine le_trans hstep ?_
      rw [degree_pow, degree_X_sub_C]
      simp only [nsmul_eq_mul, mul_one]
      exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    exact lt_of_le_of_lt h1 (by exact_mod_cast Nat.lt_succ_self n)
  have hQeval : ∀ y : ℝ, Q.eval y = ∑ k ∈ Finset.range (n+1), lam k * (y - x)^k := by
    intro y; rw [hQ]; simp [eval_finset_sum]
  set w : ℝ → ℕ → ℝ := fun i q => (Lagrange.basis (gridE n) id i).coeff q with hw
  set W : ℝ := ∑ i ∈ gridE n, ∑ q' ∈ Finset.range (n+1), |w i q'| with hW
  have hWnonneg : 0 ≤ W := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun q _ => abs_nonneg _
  have hWq : ∀ q : ℕ, ∑ i ∈ gridE n, |w i q| ≤ W := by
    intro q
    rcases Nat.lt_or_ge n q with hq | hq
    · have hzero : ∀ i ∈ gridE n, |w i q| = 0 := by
        intro i hi
        have hdeg : (Lagrange.basis (gridE n) id i).natDegree = n := by
          rw [Lagrange.natDegree_basis (gridE_inj n) hi, gridE_card]
          omega
        have hz : (Lagrange.basis (gridE n) id i).coeff q = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        rw [hw]; simp [hz]
      rw [Finset.sum_congr rfl hzero]
      simpa using hWnonneg
    · refine Finset.sum_le_sum fun i hi => ?_
      exact Finset.single_le_sum (f := fun q' => |w i q'|) (fun q' _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
  set ε' : ℝ := ε / (2 * (W + 1)) with hε'
  have hε'pos : 0 < ε' := by positivity
  choose δfun hδfun hδfun' using fun (y : ℝ) => lagrEval_convOn f x lam n h y ε' hε'pos
  have hEne : (gridE n).Nonempty := by
    rw [← Finset.card_pos, gridE_card]; omega
  set δ : ℝ := (gridE n).inf' hEne δfun with hδ
  have hδpos : 0 < δ := (Finset.lt_inf'_iff hEne).2 (fun i _ => hδfun i)
  refine ⟨δ, hδpos, fun s hs hsI hsx q => ?_⟩
  have hPdeg : (interpPoly f s).degree < ((n+1 : ℕ) : WithBot ℕ) := by
    have hd := Lagrange.degree_interpolate_lt (v := (id : ℝ → ℝ)) (s := s) f
      (fun _ _ _ _ hab => hab)
    rw [hs] at hd
    exact hd
  have hPc := coeff_eq_sum_eval n (interpPoly f s) hPdeg q
  have hQc := coeff_eq_sum_eval n Q hQdeg q
  have hdiff : (interpPoly f s).coeff q - Q.coeff q
      = ∑ i ∈ gridE n, ((interpPoly f s).eval i - Q.eval i) * w i q := by
    rw [hPc, hQc, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hdiff]
  have hbound : ∀ i ∈ gridE n, |((interpPoly f s).eval i - Q.eval i) * w i q| ≤ ε' * |w i q| := by
    intro i hi
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [eval_interpPoly, hQeval]
    exact (hδfun' i s hs hsI (fun t ht => lt_of_lt_of_le (hsx t ht) (Finset.inf'_le _ hi))).le
  calc |∑ i ∈ gridE n, ((interpPoly f s).eval i - Q.eval i) * w i q|
      ≤ ∑ i ∈ gridE n, |((interpPoly f s).eval i - Q.eval i) * w i q| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ gridE n, ε' * |w i q| := Finset.sum_le_sum hbound
    _ = ε' * ∑ i ∈ gridE n, |w i q| := by rw [Finset.mul_sum]
    _ ≤ ε' * W := mul_le_mul_of_nonneg_left (hWq q) hε'pos.le
    _ < ε := by
        rw [hε', div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-- **Part (a) on an arbitrary nondegenerate interval** (endpoints included): the literal
definition of `DIT(n)` relative to `I` (convergence of all the monomial coefficients `c_q`) is
equivalent to the convergence of the top coefficient `c_n` alone, i.e. to the convergence of the
relative divided differences of order `n`. -/
theorem part_a_On (hI : I.OrdConnected) (hne : I.Nontrivial) (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I)
    (n : ℕ) : HasDITcoeffOn I f n x ↔ HasDITOn I f n x := by
  constructor
  · rintro hc
    obtain ⟨L, hL⟩ := hc n le_rfl
    refine ⟨L, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hδ'⟩ := hL ε hε
    exact ⟨δ, hδ, fun s hs hsI hsx => by
      have := hδ' s hs hsI hsx
      rwa [coeff_top_interpPoly f s n hs] at this⟩
  · intro hD q hq
    set lam : ℕ → ℝ := fun k => ddLimValOn I f k x with hlam
    have hlam' : ∀ k ≤ n, DDLimOn I f k x (lam k) := fun k hk =>
      ddLimOn_spec (exists_ddLimOn_of_le hI hne f x hx n hD k hk)
    refine ⟨(∑ k ∈ Finset.range (n+1), C (lam k) * (X - C x)^k).coeff q, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hδ'⟩ := interpPoly_coeff_convOn f x n lam hlam' ε hε
    exact ⟨δ, hδ, fun s hs hsI hsx => hδ' s hs hsI hsx q⟩

/-- **Part (a) on an interval**, the "moreover" statement: the limiting polynomial. -/
theorem part_a_limit_polynomialOn (hI : I.OrdConnected) (hne : I.Nontrivial) (f : ℝ → ℝ) (x : ℝ)
    (hx : x ∈ I) (n : ℕ) (hD : HasDITOn I f n x) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ s : Finset ℝ, s.card = n + 1 → (↑s ⊆ I) → (∀ t ∈ s, |t - x| < δ) →
      ∀ q, |(interpPoly f s).coeff q
        - (∑ k ∈ Finset.range (n+1), C (ddLimValOn I f k x) * (X - C x)^k).coeff q| < ε :=
  interpPoly_coeff_convOn f x n (fun k => ddLimValOn I f k x)
    (fun k hk => ddLimOn_spec (exists_ddLimOn_of_le hI hne f x hx n hD k hk)) ε hε

end Q587
