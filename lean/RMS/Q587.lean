/-
# Q587 — Interpolated Taylor expansions (DIT)

Formalization of the solution of problem Q587: a function `f` admits an *interpolated Taylor
expansion of order `n`* at `x` (`DIT(n)`) when all monomial coefficients of the Lagrange
interpolation polynomial of `f` at `n+1` distinct nodes have finite limits as all the nodes
tend to `x`.

Contents:
* `part_a`, `part_a_limit_polynomial` — it suffices to assume convergence of the top
  coefficient `c_n` (equivalently, of the divided differences of order `n`), and then the
  interpolation polynomials converge coefficientwise to `∑_{k≤n} λ_k (X - x)^k`;
* `part_b_expansion`, `part_b_isLittleO` — `DIT(n)` implies the Peano expansion
  `f (x + h) = ∑_{k≤n} λ_k h^k + o(|h|^n)`;
* `hasDIT_deriv_iff`, `ddLimVal_deriv` — the differentiation theorem (Lemma 5.1);
* `part_c_hasDIT`, `part_c_ddLimVal`, `part_c_ditTop` — part (c): for `f` of class `C^p`,
  `f` has `DIT(p+k)` at `x` iff `f^{(p)}` has `DIT(k)` at `x`, with
  `k ! λ_k(f^{(p)};x) = (p+k)! λ_{p+k}(f;x)`, i.e. `(f^{(p)})^{[k]} = f^{[p+k]}`;
* `contDiff_of_hasDIT`, `ditTop_eq_iteratedDeriv`, `part_d` — part (d): `DIT(p)` everywhere
  forces `f ∈ C^p` with `f^{[p]} = f^{(p)}`, whence `f` has `DIT(p+k)` at `x` iff `f^{[p]}`
  has `DIT(k)` at `x`;
* `order_zero_counterexample` — the §8 counterexample showing that part (d) fails at `p = 0`
  under the punctured-limit convention.

## Versions

Lean 4.28.0; Mathlib at commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
(toolchain `leanprover/lean4:v4.28.0`).

## Mismatches between the printed statement and the formal one

* The interval `I` of the printed problem is taken to be the whole real line, so functions are
  `f : ℝ → ℝ` and all nodes range over `ℝ`.  This avoids the one-sided/relative limits at
  endpoints discussed in §1 of the source, which require no separate argument there either.
* Node tuples `x_0 < ... < x_n` are modelled as a `Finset ℝ` of cardinality `n+1`: distinctness
  is then automatic and the symmetry of the divided differences is free.  Since divided
  differences and interpolation polynomials are symmetric in the nodes, this is equivalent to
  the ordered formulation.
* Limits are expressed as explicit ε–δ statements (`DDLim`, `CoeffLim`) rather than filter
  limits; `part_b_isLittleO` also gives the filter form of part (b).
* In Lemma 5.1 and its ingredients, differentiability of `f` on all of `ℝ` is assumed in the
  form `∀ y, HasDerivAt f (f' y) y`; as remarked in §5 of the source, continuity of `f'` is not
  needed.  Part (c) is stated with the hypothesis `ContDiff ℝ p f`, as in the source.
* With the finset model, order `0` corresponds to a single node `t` which may equal `x`, so
  `HasDIT f 0 x` is the *continuity* convention of §8 (`f t → f x`).  The punctured-limit
  convention is formalized separately as `PunctLim`, and the §8 counterexample shows that part
  (d) fails at `p = 0` for it.
* Parts (c) and (d) are stated for `n = p + k` with arbitrary `k` (the printed statement is the
  case `k ≥ 1`, i.e. `p < n`) and, in part (d), for arbitrary `p` (the printed statement assumes
  `p ≥ 1`); these extra cases are proved, not assumed.
-/

import Mathlib

open Polynomial Finset

namespace Q587

/-! ## Divided differences and Lagrange interpolation -/

/-- The divided difference of `f` over the finite set of (automatically distinct) nodes `s`.
If `s.card = r + 1` this is the divided difference of order `r`. -/
noncomputable def ddiff (f : ℝ → ℝ) (s : Finset ℝ) : ℝ :=
  ∑ t ∈ s, f t / ∏ u ∈ s.erase t, (t - u)

/-- The value at `y` of the Lagrange interpolation polynomial of `f` at the nodes `s`. -/
noncomputable def lagrEval (f : ℝ → ℝ) (s : Finset ℝ) (y : ℝ) : ℝ :=
  ∑ v ∈ s, f v * ∏ u ∈ s.erase v, ((y - u) / (v - u))

/-- The Lagrange interpolation polynomial of `f` at the nodes `s`. -/
noncomputable def interpPoly (f : ℝ → ℝ) (s : Finset ℝ) : ℝ[X] :=
  Lagrange.interpolate s id f

/-- `DDLim f r x L` says that the divided differences of order `r` of `f` (i.e. over `r+1`
distinct nodes) tend to `L` as all the nodes tend to `x`. -/
def DDLim (f : ℝ → ℝ) (r : ℕ) (x L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ s : Finset ℝ, s.card = r + 1 → (∀ t ∈ s, |t - x| < δ) →
    |ddiff f s - L| < ε

/-- `f` admits an interpolated Taylor expansion of order `n` at `x`, `DIT(n)`.
By Theorem `part_a` below this is equivalent to the convergence of all the monomial
coefficients of the interpolation polynomials. -/
def HasDIT (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : Prop := ∃ L, DDLim f n x L

/-- The limit `λ_r (f;x)` of the divided differences of order `r`, when it exists
(and the junk value `0` otherwise). -/
noncomputable def ddLimVal (f : ℝ → ℝ) (r : ℕ) (x : ℝ) : ℝ := by
  classical
  exact if h : ∃ L, DDLim f r x L then h.choose else 0

/-! ### Elementary nonvanishing facts -/

lemma prod_erase_ne_zero (t : Finset ℝ) (v : ℝ) : ∏ u ∈ t.erase v, (v - u) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 (fun u hu => ?_)
  have := (Finset.mem_erase.1 hu).1
  intro h; exact this (by linarith [sub_eq_zero.1 h])

lemma prod_sub_ne_zero {t : Finset ℝ} {a : ℝ} (ha : a ∉ t) : ∏ u ∈ t, (a - u) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 (fun u hu h => ha ?_)
  rw [sub_eq_zero.1 h]; exact hu

lemma sub_ne_zero_of_mem_of_not_mem {t : Finset ℝ} {z a : ℝ} (hz : z ∈ t) (ha : a ∉ t) :
    z - a ≠ 0 := fun h => ha (by rw [← sub_eq_zero.1 h]; exact hz)

/-! ### The basic identities -/

/-- Expansion of a divided difference along a new node. -/
lemma ddiff_insert (f : ℝ → ℝ) (a : ℝ) (t : Finset ℝ) (ha : a ∉ t) :
    ddiff f (insert a t) =
      f a / ∏ u ∈ t, (a - u)
      + ∑ v ∈ t, f v / ((v - a) * ∏ u ∈ t.erase v, (v - u)) := by
  unfold ddiff
  rw [Finset.sum_insert ha, Finset.erase_insert ha]
  congr 1
  refine Finset.sum_congr rfl (fun v hv => ?_)
  have hva : v ≠ a := fun h => ha (h ▸ hv)
  rw [Finset.erase_insert_of_ne (Ne.symm hva),
    Finset.prod_insert (fun h => ha (Finset.mem_erase.1 h).2)]

/-- Adding one interpolation node changes the interpolating function by the Newton term. -/
lemma lagrEval_insert_sub (f : ℝ → ℝ) (a : ℝ) (t : Finset ℝ) (ha : a ∉ t) (y : ℝ) :
    lagrEval f (insert a t) y - lagrEval f t y = ddiff f (insert a t) * ∏ u ∈ t, (y - u) := by
  have hprodA : ∏ u ∈ t, (a - u) ≠ 0 := prod_sub_ne_zero ha
  rw [ddiff_insert f a t ha, lagrEval, lagrEval, Finset.sum_insert ha, Finset.erase_insert ha,
    add_mul, Finset.sum_mul]
  rw [add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.prod_div_distrib]
    field_simp
  · refine Finset.sum_congr rfl (fun v hv => ?_)
    have hva : v ≠ a := fun h => ha (h ▸ hv)
    have hva' : v - a ≠ 0 := sub_eq_zero.not.2 hva
    have hpe : ∏ u ∈ t.erase v, (v - u) ≠ 0 := prod_erase_ne_zero t v
    have hprody : ∏ u ∈ t, (y - u) = (y - v) * ∏ u ∈ t.erase v, (y - u) :=
      (Finset.mul_prod_erase t (fun u => y - u) hv).symm
    rw [Finset.erase_insert_of_ne (Ne.symm hva),
      Finset.prod_insert (fun h => ha (Finset.mem_erase.1 h).2), Finset.prod_div_distrib, hprody]
    field_simp
    ring

/-- The interpolating function takes the value `f y` at the node `y`. -/
lemma lagrEval_self (f : ℝ → ℝ) (t : Finset ℝ) (y : ℝ) (hy : y ∉ t) :
    lagrEval f (insert y t) y = f y := by
  rw [lagrEval, Finset.sum_insert hy, Finset.erase_insert hy]
  have h1 : ∏ u ∈ t, ((y - u) / (y - u)) = 1 := by
    refine Finset.prod_eq_one (fun u hu => ?_)
    exact div_self (sub_ne_zero.2 (fun h => hy (h ▸ hu)))
  have h2 : ∀ v ∈ t, f v * ∏ u ∈ (insert y t).erase v, ((y - u) / (v - u)) = 0 := by
    intro v hv
    have hyv : y ≠ v := fun h => hy (h ▸ hv)
    have hmem : y ∈ (insert y t).erase v := Finset.mem_erase.2 ⟨hyv, Finset.mem_insert_self _ _⟩
    have : ∏ u ∈ (insert y t).erase v, ((y - u) / (v - u)) = 0 :=
      Finset.prod_eq_zero hmem (by simp)
    rw [this, mul_zero]
  rw [Finset.sum_eq_zero h2, h1, mul_one, add_zero]

/-- Newton's remainder formula: the interpolation error at a point `y` outside the nodes. -/
lemma newton_remainder (f : ℝ → ℝ) (t : Finset ℝ) (y : ℝ) (hy : y ∉ t) :
    f y - lagrEval f t y = ddiff f (insert y t) * ∏ u ∈ t, (y - u) := by
  rw [← lagrEval_self f t y hy]
  exact lagrEval_insert_sub f y t hy y

/-- The replacement identity `[A,u]f - [A,v]f = (u-v) [A,u,v]f`. -/
lemma ddiff_replace (f : ℝ → ℝ) (t : Finset ℝ) (u v : ℝ) (hu : u ∉ t) (hv : v ∉ t) (huv : u ≠ v) :
    ddiff f (insert u t) - ddiff f (insert v t) = (u - v) * ddiff f (insert u (insert v t)) := by
  have hu2 : u ∉ insert v t := by simp [huv, hu]
  rw [ddiff_insert f u t hu, ddiff_insert f v t hv, ddiff_insert f u (insert v t) hu2,
    Finset.prod_insert hv, Finset.sum_insert hv, Finset.erase_insert hv]
  have hsum : ∑ z ∈ t, f z / ((z - u) * ∏ w ∈ (insert v t).erase z, (z - w))
      = ∑ z ∈ t, f z / ((z - u) * ((z - v) * ∏ w ∈ t.erase z, (z - w))) := by
    refine Finset.sum_congr rfl fun z hz => ?_
    have hzv : v ≠ z := fun h => hv (h ▸ hz)
    rw [Finset.erase_insert_of_ne hzv, Finset.prod_insert (fun h => hv (Finset.mem_erase.1 h).2)]
  rw [hsum]
  have hs : (∑ z ∈ t, f z / ((z - u) * ∏ w ∈ t.erase z, (z - w)))
      - (∑ z ∈ t, f z / ((z - v) * ∏ w ∈ t.erase z, (z - w)))
      = ∑ z ∈ t, (u - v) * (f z / ((z - u) * ((z - v) * ∏ w ∈ t.erase z, (z - w)))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun z hz => ?_
    have h1 : z - u ≠ 0 := sub_ne_zero_of_mem_of_not_mem hz hu
    have h2 : z - v ≠ 0 := sub_ne_zero_of_mem_of_not_mem hz hv
    have h3 : ∏ w ∈ t.erase z, (z - w) ≠ 0 := prod_erase_ne_zero t z
    field_simp
    ring
  have hPu : ∏ w ∈ t, (u - w) ≠ 0 := prod_sub_ne_zero hu
  have hPv : ∏ w ∈ t, (v - w) ≠ 0 := prod_sub_ne_zero hv
  have huv' : u - v ≠ 0 := sub_ne_zero.2 huv
  have hvu' : v - u ≠ 0 := sub_ne_zero.2 (Ne.symm huv)
  have hc : f u / ∏ w ∈ t, (u - w) - f v / ∏ w ∈ t, (v - w)
      = (u - v) * (f u / ((u - v) * ∏ w ∈ t, (u - w)))
        + (u - v) * (f v / ((v - u) * ∏ w ∈ t, (v - w))) := by
    field_simp
    ring
  rw [mul_add, mul_add, Finset.mul_sum]
  linarith [hs, hc]

/-! ## The interpolation polynomial -/

lemma eval_interpPoly (f : ℝ → ℝ) (s : Finset ℝ) (y : ℝ) :
    (interpPoly f s).eval y = lagrEval f s y := by
  simp only [interpPoly, Lagrange.interpolate_apply, Lagrange.basis, Lagrange.basisDivisor,
    eval_finset_sum, eval_mul, eval_C, eval_prod, eval_sub, eval_X, lagrEval, id]
  refine Finset.sum_congr rfl fun v hv => ?_
  refine congrArg (f v * ·) (Finset.prod_congr rfl fun u hu => ?_)
  field_simp

/-- The leading coefficient of the interpolation polynomial is the divided difference:
`c_n (x_0, …, x_n) = [x_0, …, x_n] f`. -/
lemma coeff_top_interpPoly (f : ℝ → ℝ) (s : Finset ℝ) (n : ℕ) (hs : s.card = n + 1) :
    (interpPoly f s).coeff n = ddiff f s := by
  simp only [interpPoly, Lagrange.interpolate_apply, finset_sum_coeff, ddiff]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hcard : (s.erase v).card = n := by rw [Finset.card_erase_of_mem hv, hs]; rfl
  have hb : Lagrange.basis s (id : ℝ → ℝ) v
      = C (∏ u ∈ s.erase v, (v - u)⁻¹) * ∏ u ∈ s.erase v, (X - C u) := by
    simp only [Lagrange.basis, Lagrange.basisDivisor, id, Finset.prod_mul_distrib, map_prod]
  rw [hb, ← mul_assoc, ← C_mul, coeff_C_mul]
  have hmon : (∏ u ∈ s.erase v, (X - C u) : ℝ[X]).Monic :=
    monic_prod_of_monic _ _ (fun j _ => monic_X_sub_C j)
  have hdeg : (∏ u ∈ s.erase v, (X - C u) : ℝ[X]).natDegree = n := by
    rw [natDegree_finset_prod_X_sub_C_eq_card (s.erase v) (fun a => a), hcard]
  have hone : (∏ u ∈ s.erase v, (X - C u) : ℝ[X]).coeff n = 1 := by
    rw [← hdeg]; exact hmon.coeff_natDegree
  rw [hone, mul_one, Finset.prod_inv_distrib, ← div_eq_mul_inv]

/-! ## Existence of node configurations -/

lemma exists_nodes (x δ : ℝ) (hδ : 0 < δ) (m : ℕ) (A : Finset ℝ) :
    ∃ s : Finset ℝ, s.card = m ∧ (∀ t ∈ s, |t - x| < δ) ∧ Disjoint s A := by
  have hinf : (Set.Ioo (x - δ) (x + δ) \ (A : Set ℝ)).Infinite :=
    (Set.Ioo_infinite (by linarith)).diff A.finite_toSet
  obtain ⟨s, hsub, hcard⟩ := hinf.exists_subset_card_eq m
  refine ⟨s, hcard, fun t ht => ?_, ?_⟩
  · have h1 := (hsub ht).1
    simp only [Set.mem_Ioo] at h1
    rw [abs_sub_lt_iff]
    constructor <;> linarith [h1.1, h1.2]
  · rw [Finset.disjoint_left]
    intro a ha haA
    exact (hsub ha).2 haA

/-! ## Descent: boundedness at order `r` forces convergence at order `r-1` -/

/-- Two divided differences of the same order over nodes in a small interval are close,
provided the divided differences of the next order are bounded there. -/
lemma ddiff_compare (f : ℝ → ℝ) (x ρ M : ℝ) (hρ : 0 < ρ) (hM : 0 ≤ M) (r : ℕ)
    (hbd : ∀ s : Finset ℝ, s.card = r + 1 → (∀ t ∈ s, |t - x| < ρ) → |ddiff f s| ≤ M) :
    ∀ (k : ℕ) (A B : Finset ℝ), (A \ B).card ≤ k → A.card = r → B.card = r →
      (∀ t ∈ A, |t - x| < ρ) → (∀ t ∈ B, |t - x| < ρ) →
      |ddiff f A - ddiff f B| ≤ k * (2 * ρ * M) := by
  intro k
  induction k with
  | zero =>
    intro A B hk hA hB _ _
    have h0 : A \ B = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hk)
    have hAB : A = B :=
      Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.1 h0) (by omega)
    simp [hAB]
  | succ k ih =>
    intro A B hk hA hB hAx hBx
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
          refine hbd _ ?_ ?_
          · rw [Finset.card_insert_of_notMem (by simp [hac, haA]), hcardA']
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
      have hIH := ih A' B hcard' hcardA' hB hA'x hBx
      have htri : |ddiff f A - ddiff f B|
          ≤ |ddiff f A - ddiff f A'| + |ddiff f A' - ddiff f B| := by
        calc |ddiff f A - ddiff f B| = |(ddiff f A - ddiff f A') + (ddiff f A' - ddiff f B)| := by
              ring_nf
          _ ≤ _ := abs_add_le _ _
      push_cast
      push_cast at hIH
      nlinarith [hIH, hstep, htri]

/-- Lemma 2.1: boundedness of the divided differences of order `m+1` near `x` implies
convergence of the divided differences of order `m`. -/
lemma exists_ddLim_of_bdd (f : ℝ → ℝ) (x M ρ0 : ℝ) (hρ0 : 0 < ρ0) (hM : 0 ≤ M) (m : ℕ)
    (hbd : ∀ s : Finset ℝ, s.card = m + 2 → (∀ t ∈ s, |t - x| < ρ0) → |ddiff f s| ≤ M) :
    ∃ L, DDLim f m x L := by
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
      (∀ t ∈ A, |t - x| < ρ j) → (∀ t ∈ B, |t - x| < ρ j) →
      |ddiff f A - ddiff f B| ≤ ((m : ℝ) + 1) * (2 * ρ j * M) := by
    intro j A B hA hB hAx hBx
    have hcc := ddiff_compare f x (ρ j) M (hρpos j) hM (m + 1) ?_ (m + 1) A B ?_ hA hB hAx hBx
    · push_cast at hcc; linarith
    · intro s hs hsx
      exact hbd s (by omega) (fun t ht => lt_of_lt_of_le (hsx t ht) (min_le_left _ _))
    · calc (A \ B).card ≤ A.card := Finset.card_le_card (Finset.sdiff_subset)
        _ = m + 1 := hA
  choose S hScard hSx _ using fun j => exists_nodes x (ρ j) (hρpos j) (m + 1) ∅
  set a : ℕ → ℝ := fun j => ddiff f (S j) with hadef
  have hcauchy : CauchySeq a := by
    refine cauchySeq_of_le_tendsto_0 (fun N => ((m : ℝ) + 1) * (2 * ρ N * M)) ?_ ?_
    · intro n1 n2 N h1 h2
      rw [Real.dist_eq]
      exact hcomp N (S n1) (S n2) (hScard n1) (hScard n2)
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
  refine ⟨ρ N, hρpos N, fun s hs hsx => ?_⟩
  have h1 : |ddiff f s - a N| ≤ ((m : ℝ) + 1) * (2 * ρ N * M) :=
    hcomp N s (S N) hs (hScard N) hsx (hSx N)
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

/-- One step of descent: convergence at order `m+1` implies convergence at order `m`. -/
lemma ddLim_descent (f : ℝ → ℝ) (x : ℝ) (m : ℕ) (h : ∃ L, DDLim f (m + 1) x L) :
    ∃ L, DDLim f m x L := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨δ, hδ, hδ'⟩ := hL 1 one_pos
  refine exists_ddLim_of_bdd f x (|L| + 1) δ hδ (by positivity) m (fun s hs hsx => ?_)
  have := hδ' s (by omega) hsx
  calc |ddiff f s| = |(ddiff f s - L) + L| := by ring_nf
    _ ≤ |ddiff f s - L| + |L| := abs_add_le _ _
    _ ≤ |L| + 1 := by linarith

/-- If `f` has `DIT(n)` at `x` then all the lower order divided differences converge as well. -/
lemma exists_ddLim_of_le (f : ℝ → ℝ) (x : ℝ) (n : ℕ) (h : HasDIT f n x) :
    ∀ k ≤ n, ∃ L, DDLim f k x L := by
  induction n with
  | zero => intro k hk; rw [Nat.le_zero.1 hk]; exact h
  | succ n ih =>
    intro k hk
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · exact ih (ddLim_descent f x n h) k (by omega)
    · have : k = n + 1 := by omega
      rw [this]; exact h

/-! ## Convergence of the interpolating functions -/

lemma prod_sub_pow_le (x y δ B : ℝ) (hδ : 0 ≤ δ) (hB1 : 1 ≤ B) (hB2 : |y - x| + δ ≤ B) :
    ∀ t : Finset ℝ, (∀ u ∈ t, |u - x| ≤ δ) →
      |∏ u ∈ t, (y - u) - (y - x) ^ t.card| ≤ t.card * δ * B ^ t.card := by
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    intro hmem
    have hih := ih (fun u hu => hmem u (Finset.mem_insert_of_mem hu))
    have hax : |a - x| ≤ δ := hmem a (Finset.mem_insert_self a t)
    have hyx : |y - x| ≤ B := by linarith [abs_nonneg (y-x)]
    have hya : |y - a| ≤ B := by
      have : |y - a| ≤ |y - x| + |a - x| := by
        calc |y - a| = |(y - x) - (a - x)| := by ring_nf
          _ ≤ |y - x| + |a - x| := abs_sub _ _
      linarith
    have hpow : |(y - x) ^ t.card| ≤ B ^ t.card := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hyx _
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have key : (y - a) * ∏ u ∈ t, (y - u) - (y - x) ^ (t.card + 1)
        = (y - a) * (∏ u ∈ t, (y - u) - (y - x) ^ t.card)
          + ((y - a) - (y - x)) * (y - x) ^ t.card := by
      ring
    rw [key]
    have h1 : |(y - a) * (∏ u ∈ t, (y - u) - (y - x) ^ t.card)|
        ≤ B * (t.card * δ * B ^ t.card) := by
      rw [abs_mul]
      exact mul_le_mul hya hih (abs_nonneg _) (by linarith)
    have h2 : |((y - a) - (y - x)) * (y - x) ^ t.card| ≤ δ * B ^ t.card := by
      rw [abs_mul]
      refine mul_le_mul ?_ hpow (abs_nonneg _) (by positivity)
      have h3 : (y - a) - (y - x) = -(a - x) := by ring
      rw [h3, abs_neg]; exact hax
    have hBpow : (0:ℝ) < B ^ t.card := by positivity
    calc |(y - a) * (∏ u ∈ t, (y - u) - (y - x) ^ t.card) + ((y-a) - (y-x)) * (y - x)^t.card|
        ≤ B * (t.card * δ * B ^ t.card) + δ * B ^ t.card :=
          le_trans (abs_add_le _ _) (by linarith)
      _ ≤ (t.card + 1 : ℝ) * δ * B ^ (t.card + 1) := by
          rw [pow_succ]
          nlinarith [mul_nonneg (mul_nonneg hδ hBpow.le) (sub_nonneg.2 hB1)]
      _ = ((t.card + 1 : ℕ) : ℝ) * δ * B ^ (t.card + 1) := by push_cast; ring

lemma prod_abs_le (x y δ B : ℝ) (hB2 : |y - x| + δ ≤ B) (t : Finset ℝ)
    (ht : ∀ u ∈ t, |u - x| ≤ δ) : |∏ u ∈ t, (y - u)| ≤ B ^ t.card := by
  rw [Finset.abs_prod]
  calc ∏ u ∈ t, |y - u| ≤ ∏ _u ∈ t, B := by
        refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i hi => ?_)
        have : |y - i| ≤ |y - x| + |i - x| := by
          calc |y - i| = |(y - x) - (i - x)| := by ring_nf
            _ ≤ _ := abs_sub _ _
        linarith [ht i hi]
    _ = B ^ t.card := by rw [Finset.prod_const]

/-- Coefficientwise convergence, in the form of convergence of the values: if all the divided
differences of order `≤ m` converge at `x`, then the interpolating polynomials at `m+1` nodes
near `x` converge, at every point `y`, to `∑_{k≤m} λ_k (y-x)^k`. -/
lemma lagrEval_conv (f : ℝ → ℝ) (x : ℝ) (lam : ℕ → ℝ) :
    ∀ (m : ℕ), (∀ k ≤ m, DDLim f k x (lam k)) → ∀ (y ε : ℝ), 0 < ε →
    ∃ δ > 0, ∀ s : Finset ℝ, s.card = m + 1 → (∀ t ∈ s, |t - x| < δ) →
      |lagrEval f s y - ∑ k ∈ Finset.range (m+1), lam k * (y - x)^k| < ε := by
  intro m
  induction m with
  | zero =>
    intro h y ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h 0 le_rfl ε hε
    refine ⟨δ, hδ, fun s hs hsx => ?_⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hs
    have h1 : lagrEval f {a} y = f a := by simp [lagrEval]
    have h2 : ddiff f {a} = f a := by simp [ddiff]
    have h3 := hδ' {a} hs hsx
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
    refine ⟨min (min δ1 δ2) (min 1 (ε / (4 * C))), by positivity, fun s hs hsx => ?_⟩
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
    have hkey : lagrEval f s y = lagrEval f t y + ddiff f s * ∏ u ∈ t, (y - u) := by
      have h4 := lagrEval_insert_sub f a t hat y
      rw [← hst] at h4
      linarith
    have hbB : |y - x| + min 1 (ε / (4*C)) ≤ B := by
      have h1 : min 1 (ε/(4*C)) ≤ 1 := min_le_left _ _
      calc |y - x| + min 1 (ε/(4*C)) ≤ |y-x| + 1 := by linarith
        _ ≤ B := le_max_right _ _
    have e1 : |lagrEval f t y - ∑ k ∈ Finset.range (m+1), lam k * (y - x)^k| < ε/4 :=
      hδ2' t htcard (fun z hz => hsx2 z (Finset.mem_of_mem_erase hz))
    have hdd : |ddiff f s - lam (m+1)| < ε / (4 * B ^ (m+1)) := hδ1' s hs hsx1
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

lemma prod_sub_pow_mul_le (x y δ B : ℝ) (hδ : 0 ≤ δ) (hB0 : 0 < B) (hB2 : |y - x| + δ ≤ B) :
    ∀ t : Finset ℝ, (∀ u ∈ t, |u - x| ≤ δ) →
      B * |∏ u ∈ t, (y - u) - (y - x) ^ t.card| ≤ t.card * δ * B ^ t.card := by
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    intro hmem
    have hih := ih (fun u hu => hmem u (Finset.mem_insert_of_mem hu))
    have hax : |a - x| ≤ δ := hmem a (Finset.mem_insert_self a t)
    have hyx : |y - x| ≤ B := by linarith [abs_nonneg (y-x)]
    have hya : |y - a| ≤ B := by
      have : |y - a| ≤ |y - x| + |a - x| := by
        calc |y - a| = |(y - x) - (a - x)| := by ring_nf
          _ ≤ |y - x| + |a - x| := abs_sub _ _
      linarith
    have hpow : |(y - x) ^ t.card| ≤ B ^ t.card := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hyx _
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have key : (y - a) * ∏ u ∈ t, (y - u) - (y - x) ^ (t.card + 1)
        = (y - a) * (∏ u ∈ t, (y - u) - (y - x) ^ t.card)
          + ((y - a) - (y - x)) * (y - x) ^ t.card := by ring
    rw [key]
    have hstep : B * |(y - a) * (∏ u ∈ t, (y - u) - (y - x) ^ t.card)
          + ((y - a) - (y - x)) * (y - x) ^ t.card|
        ≤ B * (|y - a| * |∏ u ∈ t, (y - u) - (y - x) ^ t.card| + δ * B ^ t.card) := by
      apply mul_le_mul_of_nonneg_left _ hB0.le
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul]
      have h3 : |(y - a) - (y - x)| ≤ δ := by
        have h4 : (y - a) - (y - x) = -(a - x) := by ring
        rw [h4, abs_neg]; exact hax
      have := mul_le_mul h3 hpow (abs_nonneg _) hδ
      linarith
    refine le_trans hstep ?_
    have h5 : B * (|y - a| * |∏ u ∈ t, (y - u) - (y - x) ^ t.card|)
        = |y - a| * (B * |∏ u ∈ t, (y - u) - (y - x) ^ t.card|) := by ring
    have h6 : |y - a| * (B * |∏ u ∈ t, (y - u) - (y - x) ^ t.card|)
        ≤ B * ((t.card : ℝ) * δ * B ^ t.card) :=
      mul_le_mul hya hih (by positivity) hB0.le
    have h7 : B * (δ * B ^ t.card) = δ * B ^ (t.card + 1) := by rw [pow_succ]; ring
    push_cast
    nlinarith [h5, h6, h7]

/-! ## Part (a): coefficientwise convergence of the interpolation polynomials -/

/-- A fixed grid of `n+1` distinct points, used to recover the coefficients of a polynomial of
degree `≤ n` from its values. -/
noncomputable def gridE (n : ℕ) : Finset ℝ := (Finset.range (n+1)).image (fun i : ℕ => (i:ℝ))

lemma gridE_card (n : ℕ) : (gridE n).card = n + 1 := by
  rw [gridE, Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]

lemma gridE_inj (n : ℕ) : Set.InjOn (id : ℝ → ℝ) (gridE n) := fun _ _ _ _ h => h

/-- The coefficients of a polynomial of degree `≤ n` are fixed linear combinations of its values
on the grid. -/
lemma coeff_eq_sum_eval (n : ℕ) (P : ℝ[X]) (hP : P.degree < ((n + 1 : ℕ) : WithBot ℕ)) (q : ℕ) :
    P.coeff q = ∑ i ∈ gridE n, P.eval i * (Lagrange.basis (gridE n) id i).coeff q := by
  have hcard : ((gridE n).card : WithBot ℕ) = ((n+1 : ℕ) : WithBot ℕ) := by rw [gridE_card]
  have h1 : P = Lagrange.interpolate (gridE n) id (fun i => P.eval (id i)) :=
    Lagrange.eq_interpolate (gridE_inj n) (by rw [hcard]; exact hP)
  conv_lhs => rw [h1]
  rw [Lagrange.interpolate_apply, finset_sum_coeff]
  exact Finset.sum_congr rfl fun i _ => by rw [coeff_C_mul]; rfl

/-- **Part (a)**, the substantive half: if the divided differences of all orders `k ≤ n` converge
at `x` (which, by `exists_ddLim_of_le`, follows from the convergence of the top one alone), then
the interpolation polynomials converge coefficientwise to `Q = ∑_{k≤n} λ_k (X-x)^k`. -/
theorem interpPoly_coeff_conv (f : ℝ → ℝ) (x : ℝ) (n : ℕ) (lam : ℕ → ℝ)
    (h : ∀ k ≤ n, DDLim f k x (lam k)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ s : Finset ℝ, s.card = n + 1 → (∀ t ∈ s, |t - x| < δ) →
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
  choose δfun hδfun hδfun' using fun (y : ℝ) => lagrEval_conv f x lam n h y ε' hε'pos
  have hEne : (gridE n).Nonempty := by
    rw [← Finset.card_pos, gridE_card]; omega
  set δ : ℝ := (gridE n).inf' hEne δfun with hδ
  have hδpos : 0 < δ := (Finset.lt_inf'_iff hEne).2 (fun i _ => hδfun i)
  refine ⟨δ, hδpos, fun s hs hsx q => ?_⟩
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
    exact (hδfun' i s hs (fun t ht => lt_of_lt_of_le (hsx t ht) (Finset.inf'_le _ hi))).le
  calc |∑ i ∈ gridE n, ((interpPoly f s).eval i - Q.eval i) * w i q|
      ≤ ∑ i ∈ gridE n, |((interpPoly f s).eval i - Q.eval i) * w i q| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ gridE n, ε' * |w i q| := Finset.sum_le_sum hbound
    _ = ε' * ∑ i ∈ gridE n, |w i q| := by rw [Finset.mul_sum]
    _ ≤ ε' * W := mul_le_mul_of_nonneg_left (hWq q) hε'pos.le
    _ < ε := by
        rw [hε', div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-- The limit value is unique. -/
lemma DDLim.unique {f : ℝ → ℝ} {r : ℕ} {x L1 L2 : ℝ} (h1 : DDLim f r x L1)
    (h2 : DDLim f r x L2) : L1 = L2 := by
  by_contra hne
  set ε := |L1 - L2| / 2 with hε
  have hεpos : 0 < ε := by
    have : L1 - L2 ≠ 0 := sub_ne_zero.2 hne
    positivity
  obtain ⟨δ1, hδ1, hδ1'⟩ := h1 ε hεpos
  obtain ⟨δ2, hδ2, hδ2'⟩ := h2 ε hεpos
  obtain ⟨s, hs, hsx, -⟩ := exists_nodes x (min δ1 δ2) (lt_min hδ1 hδ2) (r+1) ∅
  have e1 := hδ1' s hs (fun t ht => lt_of_lt_of_le (hsx t ht) (min_le_left _ _))
  have e2 := hδ2' s hs (fun t ht => lt_of_lt_of_le (hsx t ht) (min_le_right _ _))
  have htri : |L1 - L2| ≤ |ddiff f s - L1| + |ddiff f s - L2| := by
    calc |L1 - L2| = |(ddiff f s - L2) - (ddiff f s - L1)| := by ring_nf
      _ ≤ |ddiff f s - L2| + |ddiff f s - L1| := abs_sub _ _
      _ = |ddiff f s - L1| + |ddiff f s - L2| := by ring
  rw [hε] at e1 e2
  linarith

lemma ddLim_spec {f : ℝ → ℝ} {r : ℕ} {x : ℝ} (h : ∃ L, DDLim f r x L) :
    DDLim f r x (ddLimVal f r x) := by
  simp only [ddLimVal, dif_pos h]
  exact h.choose_spec

lemma ddLimVal_eq {f : ℝ → ℝ} {r : ℕ} {x L : ℝ} (h : DDLim f r x L) : ddLimVal f r x = L :=
  (ddLim_spec ⟨L, h⟩).unique h

/-- The monomial coefficient `c_q` of the interpolation polynomials converges to `L`
as all `n+1` nodes tend to `x`. -/
def CoeffLim (f : ℝ → ℝ) (n q : ℕ) (x L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ s : Finset ℝ, s.card = n + 1 → (∀ t ∈ s, |t - x| < δ) →
    |(interpPoly f s).coeff q - L| < ε

/-- The definition of `DIT(n)` as in the statement of the problem: every coefficient `c_q`,
`q ≤ n`, of the interpolation polynomial has a finite limit as all the nodes tend to `x`. -/
def HasDITcoeff (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : Prop := ∀ q ≤ n, ∃ L, CoeffLim f n q x L

/-- **Part (a).** It suffices to assume the convergence of the highest coefficient `c_n`:
the literal definition `DIT(n)` (convergence of all the `c_q`) is equivalent to the convergence
of `c_n` alone, equivalently to the convergence of the divided differences of order `n`. -/
theorem part_a (f : ℝ → ℝ) (x : ℝ) (n : ℕ) : HasDITcoeff f n x ↔ HasDIT f n x := by
  constructor
  · rintro hc
    obtain ⟨L, hL⟩ := hc n le_rfl
    refine ⟨L, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hδ'⟩ := hL ε hε
    exact ⟨δ, hδ, fun s hs hsx => by
      have := hδ' s hs hsx
      rwa [coeff_top_interpPoly f s n hs] at this⟩
  · intro hD q hq
    set lam : ℕ → ℝ := fun k => ddLimVal f k x with hlam
    have hlam' : ∀ k ≤ n, DDLim f k x (lam k) := fun k hk =>
      ddLim_spec (exists_ddLim_of_le f x n hD k hk)
    refine ⟨(∑ k ∈ Finset.range (n+1), C (lam k) * (X - C x)^k).coeff q, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hδ'⟩ := interpPoly_coeff_conv f x n lam hlam' ε hε
    exact ⟨δ, hδ, fun s hs hsx => hδ' s hs hsx q⟩

/-- **Part (a)**, the "moreover" statement: under `DIT(n)` the interpolation polynomials converge
coefficientwise to `Q_{n,x} = ∑_{k≤n} λ_k (X-x)^k`, where `λ_k = ddLimVal f k x`. -/
theorem part_a_limit_polynomial (f : ℝ → ℝ) (x : ℝ) (n : ℕ) (hD : HasDIT f n x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ s : Finset ℝ, s.card = n + 1 → (∀ t ∈ s, |t - x| < δ) →
      ∀ q, |(interpPoly f s).coeff q
        - (∑ k ∈ Finset.range (n+1), C (ddLimVal f k x) * (X - C x)^k).coeff q| < ε :=
  interpPoly_coeff_conv f x n (fun k => ddLimVal f k x)
    (fun k hk => ddLim_spec (exists_ddLim_of_le f x n hD k hk)) ε hε

/-! ## Part (b): the Peano–Taylor expansion -/

/-- **Part (b).** If `f` has `DIT(n)` at `x` with `n = m+1 ≥ 1`, and `lam k` are the limits of the
divided differences of order `k ≤ n`, then
`f (x+h) = ∑_{k≤n} lam k h^k + o(|h|^n)`. -/
theorem part_b_expansion (f : ℝ → ℝ) (x : ℝ) (m : ℕ) (lam : ℕ → ℝ)
    (h : ∀ k ≤ m + 1, DDLim f k x (lam k)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ hh : ℝ, 0 < |hh| → |hh| < δ →
      |f (x + hh) - ∑ k ∈ Finset.range (m+2), lam k * hh ^ k| ≤ ε * |hh| ^ (m+1) := by
  set n := m + 1 with hn
  set K : ℝ := (|lam n| + 1) * ((m:ℝ) + 1) * 2 ^ n with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨δn, hδn, hδn'⟩ := h n le_rfl (ε / (4 * 2 ^ n)) (by positivity)
  refine ⟨δn, hδn, ?_⟩
  intro hh hh0 hhδ
  set y := x + hh with hy
  have hyx : y - x = hh := by rw [hy]; ring
  obtain ⟨δc, hδc, hδc'⟩ := lagrEval_conv f x lam m (fun k hk => h k (by omega)) y
    (ε * |hh| ^ n / 4) (by positivity)
  set δ' : ℝ := min (min δc δn) (min |hh| (ε * |hh| / (4 * K))) with hδ'
  have hδ'pos : 0 < δ' := lt_min (lt_min hδc hδn) (lt_min hh0 (by positivity))
  obtain ⟨s, hscard, hsx, hsdisj⟩ := exists_nodes x δ' hδ'pos n {y}
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
    have := hδc' s hscard hsxc
    rwa [hyx] at this
  have e2 : |ddiff f (insert y s) - lam n| < ε / (4 * 2 ^ n) := by
    refine hδn' _ ?_ ?_
    · rw [Finset.card_insert_of_notMem hys, hscard]
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

/-- **Part (b)**, stated with the little-o notation. -/
theorem part_b_isLittleO (f : ℝ → ℝ) (x : ℝ) (m : ℕ) (lam : ℕ → ℝ)
    (h : ∀ k ≤ m + 1, DDLim f k x (lam k)) :
    (fun hh => f (x + hh) - ∑ k ∈ Finset.range (m+2), lam k * hh ^ k)
      =o[nhdsWithin 0 {(0:ℝ)}ᶜ] (fun hh => hh ^ (m+1)) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hδ'⟩ := part_b_expansion f x m lam h c hc
  have hball : Metric.ball (0:ℝ) δ ∈ nhds (0:ℝ) := Metric.ball_mem_nhds _ hδ
  filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with hh h1 h2
  have hh0 : 0 < |hh| := abs_pos.2 h2
  have hhd : |hh| < δ := by
    simpa [Real.dist_eq] using Metric.mem_ball.1 h1
  have := hδ' hh hh0 hhd
  simpa [Real.norm_eq_abs, abs_pow] using this

/-! ## Differentiating a DIT (Lemma 5.1) -/

lemma ddiff_image_add (f : ℝ → ℝ) (K : Finset ℝ) (h : ℝ) :
    ddiff f (K.image (· + h)) = ∑ v ∈ K, f (v + h) / ∏ u ∈ K.erase v, (v - u) := by
  have hinj : Function.Injective (fun z : ℝ => z + h) := fun a b hab => by simpa using hab
  rw [ddiff, Finset.sum_image (fun a _ b _ hab => hinj hab)]
  refine Finset.sum_congr rfl fun v hv => ?_
  congr 1
  rw [← Finset.image_erase hinj, Finset.prod_image (fun a _ b _ hab => hinj hab)]
  exact Finset.prod_congr rfl fun u _ => by ring_nf

/-- For a fixed finite set of nodes, a small enough shift moves no node onto another. -/
lemma eventually_sep (K : Finset ℝ) :
    ∀ᶠ hh in nhdsWithin (0:ℝ) {0}ᶜ, ∀ a ∈ K, ∀ b ∈ K, a + hh ≠ b := by
  classical
  set B : Finset ℝ := ((K ×ˢ K).image (fun p : ℝ × ℝ => p.2 - p.1)).erase 0 with hB
  have h0 : (0:ℝ) ∉ B := Finset.notMem_erase _ _
  have hclosed : IsClosed (B : Set ℝ) := B.finite_toSet.isClosed
  have hmem : (B : Set ℝ)ᶜ ∈ nhds (0:ℝ) := hclosed.isOpen_compl.mem_nhds (by simpa using h0)
  filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with hh h1 h2
  intro a ha b hb hab
  apply h1
  have hval : hh = b - a := by linarith [hab]
  simp only [hB, Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Finset.mem_image]
  refine ⟨⟨(a, b), by simp [ha, hb], by simpa using hval.symm⟩, by simpa using h2⟩

/-- Telescoping estimate: shifting all the nodes by `h` changes the divided difference of order
`r-1` by approximately `r * h * L`. -/
theorem ddiff_shift_telescope (f : ℝ → ℝ) (x L δ ε h : ℝ) (r : ℕ)
    (hbd : ∀ w : Finset ℝ, w.card = r + 1 → (∀ u ∈ w, |u - x| < δ) → |ddiff f w - L| < ε)
    (hh : h ≠ 0) (hhδ : |h| < δ/2) :
    ∀ t s : Finset ℝ, Disjoint t s → ((t ∪ s).card = r) →
      (∀ u ∈ t ∪ s, |u - x| < δ/2) →
      (∀ a ∈ t ∪ s, ∀ b ∈ t ∪ s, a + h ≠ b) →
      |ddiff f (t.image (· + h) ∪ s) - ddiff f (t ∪ s) - t.card * h * L| ≤ t.card * ε * |h| := by
  have hinj : Function.Injective (fun z : ℝ => z + h) := fun a b hab => by simpa using hab
  intro t
  induction t using Finset.induction_on with
  | empty => intro s _ _ _ _; simp
  | insert a t' ha ih =>
    intro s hdisj hcard hnear hsep
    have hunion : insert a t' ∪ s = t' ∪ insert a s := by
      ext z; simp [Finset.mem_insert, Finset.mem_union]
    have hdisj' : Disjoint t' (insert a s) := by
      rw [Finset.disjoint_insert_right]
      exact ⟨ha, (Finset.disjoint_insert_left.1 hdisj).2⟩
    have has : a ∉ s := (Finset.disjoint_insert_left.1 hdisj).1
    set A : Finset ℝ := t'.image (· + h) ∪ s with hA
    have himg : (insert a t').image (· + h) ∪ s = insert (a + h) A := by
      rw [Finset.image_insert]
      ext z; simp [hA, Finset.mem_union, Finset.mem_insert]
    have hins : insert a A = t'.image (· + h) ∪ insert a s := by
      ext z; simp [hA, Finset.mem_union, Finset.mem_insert]
    have haK : a ∈ insert a t' ∪ s := by simp
    have haA : a ∉ A := by
      intro hmem
      rcases Finset.mem_union.1 hmem with hmem | hmem
      · obtain ⟨b, hb, hb'⟩ := Finset.mem_image.1 hmem
        exact hsep b (by simp [hb]) a haK hb'
      · exact has hmem
    have hahA : a + h ∉ A := by
      intro hmem
      rcases Finset.mem_union.1 hmem with hmem | hmem
      · obtain ⟨b, hb, hb'⟩ := Finset.mem_image.1 hmem
        exact ha ((hinj hb') ▸ hb)
      · exact hsep a haK (a + h) (by simp [hmem]) rfl
    have hane : a + h ≠ a := by intro hc; exact hh (by linarith [hc])
    have hdisjimg : Disjoint (t'.image (· + h)) s := by
      rw [Finset.disjoint_left]
      intro z hz hzs
      obtain ⟨b, hb, hb'⟩ := Finset.mem_image.1 hz
      exact hsep b (by simp [hb]) z (by simp [hzs]) hb'
    have hcards : (insert a t' ∪ s).card = t'.card + 1 + s.card := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_insert_of_notMem ha]
    have hcardA : A.card + 2 = r + 1 := by
      rw [hA, Finset.card_union_of_disjoint hdisjimg, Finset.card_image_of_injective _ hinj]
      omega
    have hcardbig : (insert (a + h) (insert a A)).card = r + 1 := by
      rw [Finset.card_insert_of_notMem (by simp [hane, hahA]), Finset.card_insert_of_notMem haA]
      omega
    have hnearA : ∀ u ∈ A, |u - x| < δ := by
      intro u hu
      rcases Finset.mem_union.1 hu with hu | hu
      · obtain ⟨b, hb, hb'⟩ := Finset.mem_image.1 hu
        have h1 : |b - x| < δ/2 := hnear b (by simp [hb])
        have h2 : u - x = (b - x) + h := by rw [← hb']; ring
        rw [h2]
        calc |(b - x) + h| ≤ |b - x| + |h| := abs_add_le _ _
          _ < δ := by linarith
      · exact lt_trans (hnear u (by simp [hu])) (by linarith [abs_nonneg h, hhδ])
    have hbig : |ddiff f (insert (a + h) (insert a A)) - L| < ε := by
      refine hbd _ hcardbig ?_
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · have h1 : |a - x| < δ/2 := hnear a haK
        have h2 : a + h - x = (a - x) + h := by ring
        rw [h2]
        calc |(a - x) + h| ≤ |a - x| + |h| := abs_add_le _ _
          _ < δ := by linarith
      · rcases Finset.mem_insert.1 hu with rfl | hu
        · exact lt_trans (hnear u haK) (by linarith [abs_nonneg h, hhδ])
        · exact hnearA u hu
    have hrep : ddiff f (insert (a + h) A) - ddiff f (insert a A)
        = h * ddiff f (insert (a + h) (insert a A)) := by
      rw [ddiff_replace f A (a + h) a hahA haA hane]
      ring_nf
    have hIH := ih (insert a s) hdisj' (by rw [← hunion]; exact hcard)
      (by rw [← hunion]; exact hnear) (by rw [← hunion]; exact hsep)
    rw [← hins, ← hunion] at hIH
    rw [himg, Finset.card_insert_of_notMem ha]
    have hstep : |h * ddiff f (insert (a + h) (insert a A)) - h * L| ≤ |h| * ε := by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left hbig.le (abs_nonneg _)
    have hdecomp : ddiff f (insert (a+h) A) - ddiff f (insert a t' ∪ s)
          - ((t'.card : ℝ) + 1) * h * L
        = (ddiff f (insert a A) - ddiff f (insert a t' ∪ s) - (t'.card : ℝ) * h * L)
          + (h * ddiff f (insert (a + h) (insert a A)) - h * L) := by
      rw [← hrep]; ring
    push_cast
    rw [hdecomp]
    calc |(ddiff f (insert a A) - ddiff f (insert a t' ∪ s) - (t'.card : ℝ) * h * L)
          + (h * ddiff f (insert (a + h) (insert a A)) - h * L)| ≤ _ := abs_add_le _ _
      _ ≤ (t'.card : ℝ) * ε * |h| + |h| * ε := by
          have h9 := hIH
          push_cast at h9
          linarith
      _ = ((t'.card : ℝ) + 1) * ε * |h| := by ring

/-- Lemma 5.1, first half: if `f` is differentiable and has `DIT(m+1)` at `x` with limit `L`,
then `f'` has `DIT(m)` at `x` with limit `(m+1) L`. -/
theorem ddLim_deriv_forward (f f' : ℝ → ℝ) (hderiv : ∀ y, HasDerivAt f (f' y) y)
    (x L : ℝ) (m : ℕ) (hL : DDLim f (m+1) x L) : DDLim f' m x (((m:ℝ)+1) * L) := by
  intro ε hε
  set ε' : ℝ := ε / (2*((m:ℝ)+1)) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := hL ε' hε'pos
  refine ⟨δ/2, by linarith, fun K hK hKx => ?_⟩
  set G : ℝ → ℝ := fun hh => ∑ v ∈ K, f (v + hh) / ∏ u ∈ K.erase v, (v - u) with hG
  have hG0 : G 0 = ddiff f K := by simp [hG, ddiff]
  have hGd : HasDerivAt G (ddiff f' K) 0 := by
    rw [hG, show (fun hh : ℝ => ∑ v ∈ K, f (v + hh) / ∏ u ∈ K.erase v, (v - u))
        = ∑ v ∈ K, (fun hh : ℝ => f (v + hh) / ∏ u ∈ K.erase v, (v - u)) from by
      funext hh; simp]
    rw [ddiff]
    apply HasDerivAt.sum
    intro v hv
    have h1 : HasDerivAt (fun hh : ℝ => v + hh) 1 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_add v
    have h2 : HasDerivAt (fun hh : ℝ => f (v + hh)) (f' v) 0 := by
      simpa using (hderiv (v + 0)).comp 0 h1
    exact h2.div_const _
  have hslope := hasDerivAt_iff_tendsto_slope.1 hGd
  have hball : Metric.ball (0:ℝ) (δ/2) ∈ nhds (0:ℝ) := Metric.ball_mem_nhds _ (by linarith)
  have hev : ∀ᶠ hh in nhdsWithin (0:ℝ) {0}ᶜ,
      |slope G 0 hh - (((m:ℝ)+1) * L)| ≤ ((m:ℝ)+1) * ε' := by
    filter_upwards [eventually_sep K, nhdsWithin_le_nhds hball, self_mem_nhdsWithin]
      with hh hsep h1 h2
    have hhne : hh ≠ 0 := h2
    have hhabs : |hh| < δ/2 := by simpa [Real.dist_eq] using Metric.mem_ball.1 h1
    have htel := ddiff_shift_telescope f x L δ ε' hh (m+1) hδ' hhne hhabs K ∅
      (by simp) (by simpa using hK) (by simpa using hKx) (by simpa using hsep)
    simp only [Finset.union_empty] at htel
    rw [hK] at htel
    have hGhh : G hh = ddiff f (K.image (· + hh)) := (ddiff_image_add f K hh).symm
    rw [← hGhh, ← hG0] at htel
    have hslope_eq : slope G 0 hh = (G hh - G 0) / hh := by rw [slope_def_field, sub_zero]
    rw [hslope_eq]
    have habs : |(G hh - G 0)/hh - (((m:ℝ)+1) * L)|
        = |G hh - G 0 - (((m:ℝ)+1) * L) * hh| / |hh| := by
      rw [← abs_div]; congr 1; field_simp
    rw [habs, div_le_iff₀ (abs_pos.2 hhne)]
    push_cast at htel
    have heq : G hh - G 0 - (((m:ℝ)+1) * L) * hh = G hh - G 0 - ((m:ℝ)+1) * hh * L := by ring
    rw [heq]
    linarith [htel]
  have hlim : Filter.Tendsto (fun hh => |slope G 0 hh - (((m:ℝ)+1) * L)|) (nhdsWithin (0:ℝ) {0}ᶜ)
      (nhds |ddiff f' K - ((m:ℝ)+1) * L|) := (hslope.sub_const _).abs
  have hfin := le_of_tendsto hlim hev
  have hlt : ((m:ℝ)+1) * ε' < ε := by
    rw [hε', mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- Rolle's theorem applied to `f - P`: between consecutive interpolation nodes there is a zero
of the derivative of the interpolation error. -/
lemma exists_rolle_nodes (H H' : ℝ → ℝ) (hH : ∀ y, HasDerivAt H (H' y) y) (s : Finset ℝ) (m : ℕ)
    (hs : s.card = m + 2) (hz : ∀ v ∈ s, H v = 0) :
    ∃ S' : Finset ℝ, S'.card = m + 1 ∧ (∀ w ∈ S', H' w = 0) ∧
      (∀ w ∈ S', ∃ a ∈ s, ∃ b ∈ s, a < w ∧ w < b) := by
  classical
  set z := s.orderIsoOfFin hs with hzdef
  set zz : Fin (m+2) → ℝ := fun i => (z i : ℝ) with hzz
  have hzzmem : ∀ i, zz i ∈ s := fun i => (z i).2
  have hzzmono : StrictMono zz := by
    intro i j hij
    exact_mod_cast (z.strictMono hij)
  have hcont : Continuous H := continuous_iff_continuousAt.2 (fun y => (hH y).continuousAt)
  have hrolle : ∀ i : Fin (m+1), ∃ c ∈ Set.Ioo (zz i.castSucc) (zz i.succ), H' c = 0 := by
    intro i
    refine exists_hasDerivAt_eq_zero (hzzmono Fin.castSucc_lt_succ) (hcont.continuousOn) ?_
      (fun y _ => hH y)
    rw [hz _ (hzzmem _), hz _ (hzzmem _)]
  choose ξ hξ hξ0 using hrolle
  have hξmono : StrictMono ξ := by
    intro i j hij
    have h1 : ξ i < zz i.succ := (hξ i).2
    have h2 : zz j.castSucc < ξ j := (hξ j).1
    have h3 : zz i.succ ≤ zz j.castSucc := by
      apply hzzmono.monotone
      rw [Fin.le_def]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    linarith
  refine ⟨Finset.image ξ Finset.univ, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hξmono.injective, Finset.card_univ, Fintype.card_fin]
  · intro w hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw
    exact hξ0 i
  · intro w hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw
    exact ⟨zz i.castSucc, hzzmem _, zz i.succ, hzzmem _, (hξ i).1, (hξ i).2⟩

/-- Lemma 5.1, second half: if `f` is differentiable and `f'` has `DIT(m)` at `x` with limit `M`,
then `f` has `DIT(m+1)` at `x` with limit `M/(m+1)`. -/
theorem ddLim_deriv_backward (f f' : ℝ → ℝ) (hderiv : ∀ y, HasDerivAt f (f' y) y)
    (x M : ℝ) (m : ℕ) (hM : DDLim f' m x M) : DDLim f (m+1) x (M / ((m:ℝ)+1)) := by
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hM (((m:ℝ)+1) * ε) (by positivity)
  refine ⟨δ, hδ, fun s hs hsx => ?_⟩
  set P := interpPoly f s with hP
  set H : ℝ → ℝ := fun y => f y - P.eval y with hH
  set H' : ℝ → ℝ := fun y => f' y - (derivative P).eval y with hH'
  have hHd : ∀ y, HasDerivAt H (H' y) y := fun y => (hderiv y).sub (P.hasDerivAt y)
  have hHz : ∀ v ∈ s, H v = 0 := by
    intro v hv
    have hev : P.eval v = f v := by
      have := Lagrange.eval_interpolate_at_node (v := (id : ℝ → ℝ)) (s := s) (i := v) f
        (fun _ _ _ _ h => h) hv
      simpa [hP, interpPoly] using this
    simp [hH, hev]
  obtain ⟨S', hS'card, hS'zero, hS'loc⟩ := exists_rolle_nodes H H' hHd s m (by omega) hHz
  have hS'x : ∀ w ∈ S', |w - x| < δ := by
    intro w hw
    obtain ⟨a, ha, b, hb, hab1, hab2⟩ := hS'loc w hw
    have h1 := hsx a ha
    have h2 := hsx b hb
    rw [abs_sub_lt_iff] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hPdeg : P.degree < ((m + 2 : ℕ) : WithBot ℕ) := by
    have hd := Lagrange.degree_interpolate_lt (v := (id : ℝ → ℝ)) (s := s) f (fun _ _ _ _ h => h)
    rw [hs] at hd
    exact_mod_cast hd
  have hPnd : P.natDegree ≤ m + 1 := by
    rw [Polynomial.natDegree_le_iff_degree_le]
    exact Order.le_of_lt_succ (by exact_mod_cast hPdeg)
  have hdPdeg : (derivative P).degree < (S'.card : WithBot ℕ) := by
    rw [hS'card]
    have h1 : (derivative P).natDegree ≤ m :=
      le_trans (Polynomial.natDegree_derivative_le P) (by omega)
    calc (derivative P).degree ≤ ((derivative P).natDegree : WithBot ℕ) := degree_le_natDegree
      _ ≤ (m : WithBot ℕ) := by exact_mod_cast h1
      _ < ((m+1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self m
  have heq : derivative P = interpPoly f' S' := by
    refine Lagrange.eq_interpolate_of_eval_eq f' (fun _ _ _ _ h => h) hdPdeg ?_
    intro w hw
    have hzero := hS'zero w hw
    rw [hH'] at hzero
    simp only [id]
    linarith [hzero]
  have hcoeff : ddiff f' S' = ((m:ℝ)+1) * ddiff f s := by
    rw [← coeff_top_interpPoly f' S' m hS'card, ← heq, Polynomial.coeff_derivative,
      coeff_top_interpPoly f s (m+1) hs]
    ring
  have hfin := hδ' S' hS'card hS'x
  rw [hcoeff] at hfin
  have hsplit : ddiff f s - M / ((m:ℝ)+1) = (((m:ℝ)+1) * ddiff f s - M) / ((m:ℝ)+1) := by
    field_simp
  rw [hsplit, abs_div, abs_of_pos (show (0:ℝ) < (m:ℝ)+1 by positivity),
    div_lt_iff₀ (by positivity)]
  linarith [hfin]

/-- **Lemma 5.1.** For a differentiable `f`, `DIT(r)` for `f` at `x` is equivalent to `DIT(r-1)`
for `f'` at `x` (here `r = m+1`). -/
theorem hasDIT_deriv_iff (f f' : ℝ → ℝ) (hderiv : ∀ y, HasDerivAt f (f' y) y) (x : ℝ) (m : ℕ) :
    HasDIT f (m+1) x ↔ HasDIT f' m x := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨((m:ℝ)+1) * L, ddLim_deriv_forward f f' hderiv x L m hL⟩
  · rintro ⟨M, hM⟩
    exact ⟨M / ((m:ℝ)+1), ddLim_deriv_backward f f' hderiv x M m hM⟩

/-- The relation `λ_{r-1}(f';x) = r λ_r(f;x)` between the top limits. -/
theorem ddLimVal_deriv (f f' : ℝ → ℝ) (hderiv : ∀ y, HasDerivAt f (f' y) y) (x : ℝ) (m : ℕ)
    (hD : HasDIT f (m+1) x) :
    ddLimVal f' m x = ((m:ℝ)+1) * ddLimVal f (m+1) x := by
  obtain ⟨L, hL⟩ := hD
  rw [ddLimVal_eq hL, ddLimVal_eq (ddLim_deriv_forward f f' hderiv x L m hL)]

/-- `f^{[r]}(x)`, the top interpolated derivative: `r !` times the limit of the divided
differences of order `r`. -/
noncomputable def ditTop (f : ℝ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  (Nat.factorial r : ℝ) * ddLimVal f r x

/-! ## Part (c) -/

/-- **Part (c).** If `f` is `C^p`, then `f` has `DIT(p+k)` at `x` if and only if `f^{(p)}` has
`DIT(k)` at `x`.  (The printed statement is the case `k ≥ 1`, i.e. `p < n`.) -/
theorem part_c_hasDIT (p : ℕ) : ∀ (f : ℝ → ℝ), ContDiff ℝ (p : ℕ) f → ∀ (x : ℝ) (k : ℕ),
    (HasDIT f (p + k) x ↔ HasDIT (iteratedDeriv p f) k x) := by
  induction p with
  | zero => intro f _ x k; simp [iteratedDeriv_zero]
  | succ p ih =>
    intro f hf x k
    have hdiff : Differentiable ℝ f := hf.differentiable (by norm_cast)
    have hd : ∀ y, HasDerivAt f (deriv f y) y := fun y => (hdiff y).hasDerivAt
    have h1 : HasDIT f (p + 1 + k) x ↔ HasDIT (deriv f) (p + k) x := by
      have h := hasDIT_deriv_iff f (deriv f) hd x (p + k)
      have e : p + 1 + k = (p + k) + 1 := by omega
      rw [e]; exact h
    rw [h1, ih (deriv f) (ContDiff.deriv' hf) x k, ← iteratedDeriv_succ']

/-- **Part (c)**, the quantitative form (6.1): `k ! λ_k(f^{(p)};x) = (p+k)! λ_{p+k}(f;x)`. -/
theorem part_c_ddLimVal (p : ℕ) : ∀ (f : ℝ → ℝ), ContDiff ℝ (p : ℕ) f → ∀ (x : ℝ) (k : ℕ),
    HasDIT f (p + k) x →
    (Nat.factorial k : ℝ) * ddLimVal (iteratedDeriv p f) k x
      = (Nat.factorial (p + k) : ℝ) * ddLimVal f (p + k) x := by
  induction p with
  | zero => intro f _ x k _; simp [iteratedDeriv_zero]
  | succ p ih =>
    intro f hf x k hD
    have hdiff : Differentiable ℝ f := hf.differentiable (by norm_cast)
    have hd : ∀ y, HasDerivAt f (deriv f y) y := fun y => (hdiff y).hasDerivAt
    have e : p + 1 + k = (p + k) + 1 := by omega
    rw [e] at hD
    have hD' : HasDIT (deriv f) (p + k) x := (hasDIT_deriv_iff f (deriv f) hd x (p + k)).1 hD
    have h2 := ddLimVal_deriv f (deriv f) hd x (p + k) hD
    have h3 := ih (deriv f) (ContDiff.deriv' hf) x k hD'
    rw [iteratedDeriv_succ', e, h3, h2, Nat.factorial_succ]
    push_cast
    ring

/-- **Part (c)**, identity (6.2): `(f^{(p)})^{[k]}(x) = f^{[p+k]}(x)`. -/
theorem part_c_ditTop (p k : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ (p : ℕ) f) (x : ℝ)
    (hD : HasDIT f (p + k) x) :
    ditTop (iteratedDeriv p f) k x = ditTop f (p + k) x :=
  part_c_ddLimVal p f hf x k hD

/-! ## Part (d) -/

lemma ddiff_singleton (f : ℝ → ℝ) (a : ℝ) : ddiff f {a} = f a := by simp [ddiff]

lemma ddiff_pair (f : ℝ → ℝ) (u v : ℝ) (h : u ≠ v) :
    ddiff f {u, v} = (f v - f u) / (v - u) := by
  have h1 : ({u, v} : Finset ℝ).erase u = {v} := by
    ext w; simp [Finset.mem_erase]; aesop
  have h2 : ({u, v} : Finset ℝ).erase v = {u} := by
    ext w; simp [Finset.mem_erase]; aesop
  have hne : v - u ≠ 0 := sub_ne_zero.2 h.symm
  have hne2 : u - v ≠ 0 := sub_ne_zero.2 h
  rw [ddiff, Finset.sum_pair h, h1, h2, Finset.prod_singleton, Finset.prod_singleton]
  field_simp; ring

lemma ddLim_zero_eq (f : ℝ → ℝ) (x L : ℝ) (h : DDLim f 0 x L) : f x = L := by
  by_contra hne
  have hpos : 0 < |f x - L| := by simpa [sub_eq_zero] using hne
  obtain ⟨δ, hδ, hδ'⟩ := h _ hpos
  have := hδ' {x} (by simp) (by simp [hδ])
  rw [ddiff_singleton] at this
  linarith

lemma ddLimVal_zero (f : ℝ → ℝ) (x : ℝ) (h : HasDIT f 0 x) : ddLimVal f 0 x = f x :=
  (ddLim_zero_eq f x _ (ddLim_spec h)).symm

lemma continuous_of_hasDIT_zero (f : ℝ → ℝ) (h : ∀ y, HasDIT f 0 y) : Continuous f := by
  rw [Metric.continuous_iff]
  intro x ε hε
  have hx : DDLim f 0 x (f x) := by
    obtain ⟨L, hL⟩ := h x
    rwa [ddLim_zero_eq f x L hL]
  obtain ⟨δ, hδ, hδ'⟩ := hx ε hε
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have := hδ' {y} (by simp) (by
    intro u hu
    simp only [Finset.mem_singleton] at hu; subst hu
    rwa [Real.dist_eq] at hy)
  rw [ddiff_singleton] at this
  rwa [Real.dist_eq]

/-- Lemma 7.1, first half: `DIT(1)` at `x` implies differentiability at `x`, with derivative
the limit of the first-order divided differences. -/
lemma hasDerivAt_of_ddLim_one (f : ℝ → ℝ) (x L : ℝ) (h : DDLim f 1 x L) : HasDerivAt f L x := by
  rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := h ε hε
  refine ⟨δ, hδ, fun t ht hdist => ?_⟩
  have hxt : x ≠ t := fun hc => ht (by simp [hc])
  have hcard : ({x, t} : Finset ℝ).card = 1 + 1 := Finset.card_pair hxt
  have hnodes : ∀ u ∈ ({x, t} : Finset ℝ), |u - x| < δ := by
    intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · simpa using hδ
    · simp only [Finset.mem_singleton] at hu
      subst hu
      simpa [Real.dist_eq] using hdist
  have := hδ' {x, t} hcard hnodes
  rw [ddiff_pair f x t hxt] at this
  rw [Real.dist_eq, slope_def_field]
  simpa using this

/-- Lemma 7.1, second half: if `f` has `DIT(1)` at every point, the limits `λ_1(f;·)` depend
continuously on the point. -/
lemma continuous_ddLimVal_one (f : ℝ → ℝ) (h : ∀ y, HasDIT f 1 y) :
    Continuous (fun y => ddLimVal f 1 y) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  have hL : DDLim f 1 x (ddLimVal f 1 x) := ddLim_spec (h x)
  obtain ⟨δ, hδ, hδ'⟩ := hL (ε/2) (by linarith)
  refine ⟨δ/2, by linarith, fun y hy => ?_⟩
  have hyx : |y - x| < δ/2 := by rwa [Real.dist_eq] at hy
  have hM : DDLim f 1 y (ddLimVal f 1 y) := ddLim_spec (h y)
  obtain ⟨δ2, hδ2, hδ2'⟩ := hM (ε/2) (by linarith)
  set η := min δ2 (δ/2) / 2 with hηdef
  have hη : 0 < η := by positivity
  have hη1 : η < δ2 := by
    have : min δ2 (δ/2) ≤ δ2 := min_le_left _ _
    simp only [hηdef]; linarith
  have hη2 : η < δ/2 := by
    have : min δ2 (δ/2) ≤ δ/2 := min_le_right _ _
    simp only [hηdef]; linarith
  set v := y + η with hv
  have hyv : y ≠ v := by simp [hv]; linarith
  have hcard : ({y, v} : Finset ℝ).card = 1 + 1 := Finset.card_pair hyv
  have h1 : |ddiff f {y, v} - ddLimVal f 1 y| < ε/2 := by
    refine hδ2' {y, v} hcard ?_
    intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · simpa using hδ2
    · simp only [Finset.mem_singleton] at hu; subst hu
      have hvy : v - y = η := by simp [hv]
      rw [hvy, abs_of_pos hη]; exact hη1
  have h2 : |ddiff f {y, v} - ddLimVal f 1 x| < ε/2 := by
    refine hδ' {y, v} hcard ?_
    intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · linarith [hyx]
    · simp only [Finset.mem_singleton] at hu; subst hu
      have hvx : v - x = (y - x) + η := by simp [hv]; ring
      rw [hvx]
      calc |(y - x) + η| ≤ |y - x| + |η| := abs_add_le _ _
        _ < δ/2 + δ/2 := by rw [abs_of_pos hη]; linarith
        _ = δ := by ring
  rw [Real.dist_eq]
  have e : ddLimVal f 1 y - ddLimVal f 1 x
      = (ddiff f {y, v} - ddLimVal f 1 x) - (ddiff f {y, v} - ddLimVal f 1 y) := by ring
  rw [e]
  calc |(ddiff f {y, v} - ddLimVal f 1 x) - (ddiff f {y, v} - ddLimVal f 1 y)|
      ≤ |ddiff f {y, v} - ddLimVal f 1 x| + |ddiff f {y, v} - ddLimVal f 1 y| := abs_sub _ _
    _ < ε := by linarith

/-- **Lemma 7.1.** If `f` has `DIT(1)` at every point then `f` is differentiable with derivative
`λ_1(f;·)`; combined with `continuous_ddLimVal_one` this says that `f` is `C¹`. -/
theorem dit_one_deriv_eq (f : ℝ → ℝ) (h : ∀ y, HasDIT f 1 y) :
    (∀ y, HasDerivAt f (ddLimVal f 1 y) y) ∧ deriv f = fun y => ddLimVal f 1 y := by
  have hd : ∀ y, HasDerivAt f (ddLimVal f 1 y) y := fun y =>
    hasDerivAt_of_ddLim_one f y _ (ddLim_spec (h y))
  exact ⟨hd, funext fun y => (hd y).deriv⟩

/-- **Proposition 7.2**, regularity part: if `f` has `DIT(p)` at every point, then `f` is `C^p`. -/
theorem contDiff_of_hasDIT (p : ℕ) : ∀ f : ℝ → ℝ, (∀ y, HasDIT f p y) → ContDiff ℝ (p : ℕ) f := by
  induction p with
  | zero =>
    intro f h
    exact contDiff_zero.2 (continuous_of_hasDIT_zero f h)
  | succ p ih =>
    intro f h
    have hone : ∀ y, HasDIT f 1 y := fun y => exists_ddLim_of_le f y (p+1) (h y) 1 (by omega)
    obtain ⟨hd, hderiv⟩ := dit_one_deriv_eq f hone
    have hd' : ∀ y, HasDerivAt f (deriv f y) y := by
      intro y; rw [hderiv]; exact hd y
    have hDeriv : ∀ y, HasDIT (deriv f) p y := fun y =>
      (hasDIT_deriv_iff f (deriv f) hd' y p).1 (h y)
    have hcast : ((p+1 : ℕ) : WithTop ℕ∞) = (p : WithTop ℕ∞) + 1 := by push_cast; ring
    rw [hcast, contDiff_succ_iff_deriv]
    exact ⟨fun y => (hd' y).differentiableAt, by simp, ih (deriv f) hDeriv⟩

/-- **Proposition 7.2**, identity (7.1): if `f` has `DIT(p)` at every point then
`f^{[p]} = f^{(p)}`. -/
theorem ditTop_eq_iteratedDeriv (p : ℕ) (f : ℝ → ℝ) (h : ∀ y, HasDIT f p y) (x : ℝ) :
    ditTop f p x = iteratedDeriv p f x := by
  have hf : ContDiff ℝ (p : ℕ) f := contDiff_of_hasDIT p f h
  have hx : HasDIT f (p + 0) x := by simpa using h x
  have h0 : HasDIT (iteratedDeriv p f) 0 x := (part_c_hasDIT p f hf x 0).1 hx
  have key := part_c_ddLimVal p f hf x 0 hx
  rw [ddLimVal_zero _ _ h0] at key
  simpa [ditTop] using key.symm

/-- **Part (d).** If `f` has `DIT(p)` at every point, then for every `k`, `f` has `DIT(p+k)` at `x`
if and only if `f^{[p]}` has `DIT(k)` at `x`.  The printed statement is the case `1 ≤ p` and
`k ≥ 1` (i.e. `p < n`), which is contained in this one; note that with the continuity convention
for order `0` used here (see `DDLim`), the hypothesis `1 ≤ p` is not needed. -/
theorem part_d (p k : ℕ) (f : ℝ → ℝ) (h : ∀ y, HasDIT f p y) (x : ℝ) :
    HasDIT f (p + k) x ↔ HasDIT (fun y => ditTop f p y) k x := by
  have hf : ContDiff ℝ (p : ℕ) f := contDiff_of_hasDIT p f h
  have he : (fun y => ditTop f p y) = iteratedDeriv p f :=
    funext (ditTop_eq_iteratedDeriv p f h)
  rw [he]
  exact part_c_hasDIT p f hf x k

/-! ## §8: the order-zero counterexample

Under the *punctured limit* convention for order zero, part (d) fails for `p = 0`. -/

/-- The punctured-limit convention at order zero: `f t → L` as `t → x`, `t ≠ x`. -/
def PunctLim (f : ℝ → ℝ) (x L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t, t ≠ x → |t - x| < δ → |f t - L| < ε

/-- The counterexample of §8: the indicator function of `{0}`. -/
noncomputable def cex : ℝ → ℝ := fun t => if t = 0 then 1 else 0

lemma cex_punctLim (x : ℝ) : PunctLim cex x 0 := by
  intro ε hε
  refine ⟨if x = 0 then 1 else |x|, ?_, ?_⟩
  · by_cases hx : x = 0
    · simp [hx]
    · simp only [hx, if_false]
      exact abs_pos.2 hx
  · intro t ht hlt
    by_cases hx : x = 0
    · subst hx
      simp only [ne_eq] at ht
      simp [cex, ht, hε]
    · simp only [hx, if_false] at hlt
      have ht0 : t ≠ 0 := by
        intro hc; subst hc
        rw [zero_sub, abs_neg] at hlt; exact lt_irrefl _ hlt
      simp [cex, ht0, hε]

lemma hasDIT_zero_fun (n : ℕ) (x : ℝ) : HasDIT (fun _ : ℝ => (0:ℝ)) n x := by
  refine ⟨0, fun ε hε => ⟨1, one_pos, fun s _ _ => ?_⟩⟩
  simp [ddiff, hε]

lemma cex_not_hasDIT_one : ¬ HasDIT cex 1 0 := by
  rintro ⟨L, hL⟩
  obtain ⟨δ, hδ, hδ'⟩ := hL 1 one_pos
  set t := min (δ/2) (1/(|L|+1)) with htdef
  have hLpos : (0:ℝ) < |L| + 1 := by positivity
  have ht0 : 0 < t := lt_min (by linarith) (by positivity)
  have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htb : t ≤ 1/(|L|+1) := min_le_right _ _
  have hne : (0:ℝ) ≠ t := ne_of_lt ht0
  have hcard : (({0, t} : Finset ℝ)).card = 1 + 1 := Finset.card_pair hne
  have hnodes : ∀ u ∈ ({0, t} : Finset ℝ), |u - 0| < δ := by
    intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · simpa using hδ
    · simp only [Finset.mem_singleton] at hu; subst hu
      rw [sub_zero, abs_of_pos ht0]; exact htδ
  have hdd := hδ' {0, t} hcard hnodes
  rw [ddiff_pair cex 0 t hne] at hdd
  have hcex : cex t = 0 := by simp [cex, ne_of_gt ht0]
  have hcex0 : cex 0 = 1 := by simp [cex]
  rw [hcex, hcex0, sub_zero, zero_sub, neg_div] at hdd
  have h1t : |L| + 1 ≤ 1/t := by
    rw [le_div_iff₀ ht0]
    calc (|L|+1) * t ≤ (|L|+1) * (1/(|L|+1)) := mul_le_mul_of_nonneg_left htb (le_of_lt hLpos)
      _ = 1 := by field_simp
  have hab := abs_sub_abs_le_abs_sub (-(1/t)) L
  rw [abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1/t)] at hab
  linarith

/-- **The order-zero counterexample of §8.**  For the indicator function `cex` of `{0}`, the
punctured limit of `cex` exists at every point and is `0`, so under the punctured-limit
convention `cex^{[0]}` is the zero function, which has `DIT(1)` at `0`; but `cex` itself does
not have `DIT(1)` at `0`.  Hence part (d) fails for `p = 0` under that convention. -/
theorem order_zero_counterexample :
    (∀ x : ℝ, PunctLim cex x 0) ∧ HasDIT (fun _ : ℝ => (0:ℝ)) 1 0 ∧ ¬ HasDIT cex 1 0 :=
  ⟨cex_punctLim, hasDIT_zero_fun 1 0, cex_not_hasDIT_one⟩

end Q587
