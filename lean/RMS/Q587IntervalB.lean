/-
# Q587 — the arbitrary-interval layer, part 3 (Gate 3): the relative Peano expansion

Part (b) on an arbitrary interval `I`: relative `DIT(n)` at `x ∈ I` implies the Peano expansion
`f (x+h) = ∑_{k ≤ n} λ_k h^k + o(|h|^n)`, where the increment `h` ranges only over the admissible
increments `H(I,x) = {h | x + h ∈ I}`.  At a finite endpoint of `I` this is the one-sided
expansion of the printed problem; no value of `f` outside `I` is used and no two-sided
neighborhood of `0` is involved.
-/

import RMS.Q587IntervalA

open Polynomial Finset

namespace Q587

variable {I : Set ℝ}

/-- `H(I,x) = {h | x + h ∈ I}`, the set of admissible increments at `x`. -/
def incrSet (I : Set ℝ) (x : ℝ) : Set ℝ := {h : ℝ | x + h ∈ I}

lemma mem_incrSet_iff {x h : ℝ} : h ∈ incrSet I x ↔ x + h ∈ I := Iff.rfl

/-- **Part (b) on an arbitrary interval**, ε–δ form.  If `f` has relative `DIT(m+1)` at `x ∈ I`
with relative limits `lam k`, then for every admissible increment `h` (i.e. `x + h ∈ I`) small
enough, `|f (x+h) - ∑_{k ≤ m+1} lam k h^k| ≤ ε |h|^{m+1}`. -/
theorem part_b_expansionOn (hI : I.OrdConnected) (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I) (m : ℕ)
    (lam : ℕ → ℝ) (h : ∀ k ≤ m + 1, DDLimOn I f k x (lam k)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ hh : ℝ, x + hh ∈ I → 0 < |hh| → |hh| < δ →
      |f (x + hh) - ∑ k ∈ Finset.range (m+2), lam k * hh ^ k| ≤ ε * |hh| ^ (m+1) := by
  set n := m + 1 with hn
  set K : ℝ := (|lam n| + 1) * ((m:ℝ) + 1) * 2 ^ n with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨δn, hδn, hδn'⟩ := h n le_rfl (ε / (4 * 2 ^ n)) (by positivity)
  refine ⟨δn, hδn, ?_⟩
  intro hh hhI hh0 hhδ
  set y := x + hh with hy
  have hyx : y - x = hh := by rw [hy]; ring
  have hyne : y ≠ x := by
    intro hc
    have : hh = 0 := by rw [← hyx, hc]; ring
    rw [this] at hh0; simp at hh0
  obtain ⟨δc, hδc, hδc'⟩ := lagrEval_convOn f x lam m (fun k hk => h k (by omega)) y
    (ε * |hh| ^ n / 4) (by positivity)
  set δ' : ℝ := min (min δc δn) (min |hh| (ε * |hh| / (4 * K))) with hδ'
  have hδ'pos : 0 < δ' := lt_min (lt_min hδc hδn) (lt_min hh0 (by positivity))
  obtain ⟨s, hscard, hsI, hsx, hsdisj⟩ :=
    exists_nodesOn hI hx hhI hyne hδ'pos n {y}
  have hys : y ∉ s := fun hmem =>
    (Finset.disjoint_left.1 hsdisj hmem) (Finset.mem_singleton_self y)
  have hsxc : ∀ t ∈ s, |t - x| < δc := fun t ht =>
    lt_of_lt_of_le (hsx t ht) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hsxn : ∀ t ∈ s, |t - x| < δn := fun t ht =>
    lt_of_lt_of_le (hsx t ht) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hsxh : ∀ t ∈ s, |t - x| ≤ δ' := fun t ht => (hsx t ht).le
  have hδ'h : δ' ≤ |hh| := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ'K : δ' ≤ ε * |hh| / (4 * K) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hnew := newton_remainder f s y hys
  have e1 : |lagrEval f s y - ∑ k ∈ Finset.range n, lam k * hh ^ k| < ε * |hh| ^ n / 4 := by
    have := hδc' s hscard hsI hsxc
    rwa [hyx] at this
  have e2 : |ddiff f (insert y s) - lam n| < ε / (4 * 2 ^ n) := by
    refine hδn' _ ?_ ?_ ?_
    · rw [Finset.card_insert_of_notMem hys, hscard]
    · intro z hz
      have hz' : z ∈ insert y s := hz
      rcases Finset.mem_insert.1 hz' with rfl | hz2
      · exact hhI
      · exact hsI hz2
    · intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht
      · rw [hyx]; exact hhδ
      · exact hsxn t ht
  have hB2 : |y - x| + δ' ≤ 2 * |hh| := by rw [hyx]; linarith
  have hBpos : (0:ℝ) < 2 * |hh| := by linarith
  have e3 : |∏ u ∈ s, (y - u)| ≤ (2 * |hh|) ^ n := by
    have := prod_abs_le x y δ' (2 * |hh|) hB2 s hsxh
    rwa [hscard] at this
  have e4 : (2 * |hh|) * |∏ u ∈ s, (y - u) - hh ^ n| ≤ (n:ℝ) * δ' * (2 * |hh|) ^ n := by
    have := prod_sub_pow_mul_le x y δ' (2 * |hh|) hδ'pos.le hBpos hB2 s hsxh
    rwa [hscard, hyx] at this
  have hsplit : f y - ∑ k ∈ Finset.range (n+1), lam k * hh ^ k
      = (lagrEval f s y - ∑ k ∈ Finset.range n, lam k * hh ^ k)
        + (ddiff f (insert y s) * ∏ u ∈ s, (y - u) - lam n * hh ^ n) := by
    rw [Finset.sum_range_succ]
    linarith [hnew]
  have t2 : |ddiff f (insert y s) * ∏ u ∈ s, (y - u) - lam n * hh ^ n| ≤ ε * |hh| ^ n / 2 := by
    have hs2 : ddiff f (insert y s) * ∏ u ∈ s, (y - u) - lam n * hh ^ n
        = (ddiff f (insert y s) - lam n) * (∏ u ∈ s, (y - u))
          + lam n * ((∏ u ∈ s, (y - u)) - hh ^ n) := by ring
    rw [hs2]
    have p1 : |(ddiff f (insert y s) - lam n) * (∏ u ∈ s, (y - u))| ≤ ε * |hh| ^ n / 4 := by
      rw [abs_mul]
      calc |ddiff f (insert y s) - lam n| * |∏ u ∈ s, (y - u)|
          ≤ (ε / (4 * 2 ^ n)) * (2 * |hh|) ^ n :=
            mul_le_mul e2.le e3 (abs_nonneg _) (by positivity)
        _ = ε * |hh| ^ n / 4 := by rw [mul_pow]; field_simp
    have p2 : |lam n * ((∏ u ∈ s, (y - u)) - hh ^ n)| ≤ ε * |hh| ^ n / 4 := by
      rw [abs_mul]
      have hmul : (2 * |hh|) * (|lam n| * |(∏ u ∈ s, (y - u)) - hh ^ n|)
          ≤ (2 * |hh|) * (ε * |hh| ^ n / 4) := by
        have step1 : (2 * |hh|) * (|lam n| * |(∏ u ∈ s, (y - u)) - hh ^ n|)
            = |lam n| * ((2 * |hh|) * |(∏ u ∈ s, (y - u)) - hh ^ n|) := by ring
        have step2 : |lam n| * ((2 * |hh|) * |(∏ u ∈ s, (y - u)) - hh ^ n|)
            ≤ (|lam n| + 1) * ((n:ℝ) * δ' * (2 * |hh|) ^ n) :=
          mul_le_mul (by linarith) e4 (by positivity) (by positivity)
        have step3 : (|lam n| + 1) * ((n:ℝ) * δ' * (2 * |hh|) ^ n)
            ≤ (|lam n| + 1) * ((n:ℝ) * (ε * |hh| / (4 * K)) * (2 * |hh|) ^ n) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hδ'K (by positivity)
        have step4 : (|lam n| + 1) * ((n:ℝ) * (ε * |hh| / (4 * K)) * (2 * |hh|) ^ n)
            = ε * |hh| * |hh| ^ n / 4 := by
          rw [hK, mul_pow, hn]
          push_cast
          field_simp
        have hfin : ε * |hh| * |hh| ^ n / 4 ≤ (2 * |hh|) * (ε * |hh| ^ n / 4) := by
          have : (2 * |hh|) * (ε * |hh| ^ n / 4) = ε * |hh| * |hh| ^ n / 2 := by ring
          rw [this]
          have hpp : 0 ≤ ε * |hh| * |hh| ^ n := by positivity
          linarith
        linarith
      have := le_of_mul_le_mul_left hmul hBpos
      linarith
    calc |(ddiff f (insert y s) - lam n) * (∏ u ∈ s, (y - u))
            + lam n * ((∏ u ∈ s, (y - u)) - hh ^ n)| ≤ _ := abs_add_le _ _
      _ ≤ ε * |hh| ^ n / 2 := by linarith
  have hnonneg : 0 ≤ ε * |hh| ^ n := by positivity
  rw [hsplit]
  calc |(lagrEval f s y - ∑ k ∈ Finset.range n, lam k * hh ^ k)
        + (ddiff f (insert y s) * ∏ u ∈ s, (y - u) - lam n * hh ^ n)| ≤ _ := abs_add_le _ _
    _ ≤ ε * |hh| ^ n := by linarith

/-- **Part (b) on an arbitrary interval**, little-o form, at the relative punctured
neighborhood `𝓝[H(I,x) \ {0}] 0` of admissible increments. -/
theorem part_b_isLittleOOn (hI : I.OrdConnected) (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I) (m : ℕ)
    (lam : ℕ → ℝ) (h : ∀ k ≤ m + 1, DDLimOn I f k x (lam k)) :
    (fun hh => f (x + hh) - ∑ k ∈ Finset.range (m+2), lam k * hh ^ k)
      =o[nhdsWithin 0 (incrSet I x \ {0})] (fun hh => hh ^ (m+1)) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hδ'⟩ := part_b_expansionOn hI f x hx m lam h c hc
  have hball : Metric.ball (0:ℝ) δ ∈ nhds (0:ℝ) := Metric.ball_mem_nhds _ hδ
  filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with hh h1 h2
  have hhI : x + hh ∈ I := h2.1
  have hh0 : 0 < |hh| := abs_pos.2 (by simpa using h2.2)
  have hhd : |hh| < δ := by
    simpa [Real.dist_eq] using Metric.mem_ball.1 h1
  have := hδ' hh hhI hh0 hhd
  simpa [Real.norm_eq_abs, abs_pow] using this

/-- The order-zero case of part (b) under the continuity convention: relative `DIT(0)` at `x`
says exactly that `f (x + h) → f x` as `h → 0` inside `H(I,x)`, i.e. the order-zero expansion
`f(x+h) = λ₀ + o(1)` with `λ₀ = f x`. -/
theorem part_b_zeroOn (f : ℝ → ℝ) (x : ℝ) (hD : HasDITOn I f 0 x) (ε : ℝ)
    (hε : 0 < ε) : ∃ δ > 0, ∀ hh : ℝ, x + hh ∈ I → |hh| < δ →
      |f (x + hh) - ddLimValOn I f 0 x| ≤ ε := by
  have hL : DDLimOn I f 0 x (ddLimValOn I f 0 x) := ddLimOn_spec hD
  obtain ⟨δ, hδ, hδ'⟩ := hL ε hε
  refine ⟨δ, hδ, fun hh hhI hhδ => ?_⟩
  have := hδ' {x + hh} (by simp) (by simpa using hhI) (by
    intro u hu
    simp only [Finset.mem_singleton] at hu; subst hu
    simpa using hhδ)
  rw [ddiff_singleton'] at this
  exact this.le

end Q587
