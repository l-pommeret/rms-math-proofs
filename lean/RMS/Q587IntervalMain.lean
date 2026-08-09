/-
# Q587 — the arbitrary-interval layer, part 6 (Gate 6): the full canonical interface

The source-facing statements of Q587: an arbitrary real interval `I` (any order-connected,
nondegenerate subset of `ℝ`), a function `f : ↥I → ℝ` defined **only on `I`**, an arbitrary point
`x ∈ I` (finite endpoints included), and all the relative limits and derivatives of the printed
problem.

The interval notions are those of `RequestProject.Q587Interval`, transported to functions
`f : ↥I → ℝ` through the extension by `0`, `IExt`; `..._of_extension` lemmas show that every
displayed object is independent of the chosen extension, so nothing depends on the values of the
extension outside `I`.

Corollaries at the end (`..._univ`) show that for `I = Set.univ` these notions specialize to the
whole-line theory of the preserved baseline `RequestProject.Q587`.
-/

import RMS.Q587IntervalD

open Polynomial Finset

namespace Q587

/-! ## Functions defined only on `I` -/

open Classical in
/-- The extension by `0` of a function defined only on `I`.  It is an auxiliary device: all the
notions below are independent of the extension, see `ddiffOn_of_extension`,
`DDLimOnFun_of_extension`, etc. -/
noncomputable def IExt (I : Set ℝ) (f : ↥I → ℝ) : ℝ → ℝ :=
  fun y => if h : y ∈ I then f ⟨y, h⟩ else 0

@[simp] lemma IExt_apply {I : Set ℝ} (f : ↥I → ℝ) {y : ℝ} (hy : y ∈ I) :
    IExt I f y = f ⟨y, hy⟩ := by
  classical
  simp only [IExt, dif_pos hy]

@[simp] lemma IExt_coe {I : Set ℝ} (f : ↥I → ℝ) (y : ↥I) : IExt I f (y : ℝ) = f y :=
  IExt_apply f y.2

lemma eqOn_IExt {I : Set ℝ} (f : ↥I → ℝ) (F : ℝ → ℝ) (hF : ∀ y : ↥I, F (y : ℝ) = f y) :
    Set.EqOn F (IExt I f) I := fun y hy => by
  rw [IExt_apply f hy]
  exact hF ⟨y, hy⟩

/-- The divided difference of `f : ↥I → ℝ` over a finite set of nodes of `I`. -/
noncomputable def ddiffOn (I : Set ℝ) (f : ↥I → ℝ) (s : Finset ℝ) : ℝ := ddiff (IExt I f) s

/-- The Lagrange interpolation polynomial of `f : ↥I → ℝ` at nodes of `I`. -/
noncomputable def interpPolyOn (I : Set ℝ) (f : ↥I → ℝ) (s : Finset ℝ) : ℝ[X] :=
  interpPoly (IExt I f) s

/-- Relative divided-difference limit for a function defined only on `I`. -/
def DDLimOnFun (I : Set ℝ) (f : ↥I → ℝ) (r : ℕ) (x L : ℝ) : Prop :=
  DDLimOn I (IExt I f) r x L

/-- Relative `DIT(n)` for a function defined only on `I`. -/
def HasDITOnFun (I : Set ℝ) (f : ↥I → ℝ) (n : ℕ) (x : ℝ) : Prop :=
  HasDITOn I (IExt I f) n x

/-- Relative convergence of the monomial coefficient `c_q` for a function defined only on `I`. -/
def CoeffLimOnFun (I : Set ℝ) (f : ↥I → ℝ) (n q : ℕ) (x L : ℝ) : Prop :=
  CoeffLimOn I (IExt I f) n q x L

/-- The literal (all-coefficients) definition of relative `DIT(n)` for `f : ↥I → ℝ`. -/
def HasDITcoeffOnFun (I : Set ℝ) (f : ↥I → ℝ) (n : ℕ) (x : ℝ) : Prop :=
  HasDITcoeffOn I (IExt I f) n x

/-- The relative limit `λ_r(f;x)` for a function defined only on `I`. -/
noncomputable def ddLimValOnFun (I : Set ℝ) (f : ↥I → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  ddLimValOn I (IExt I f) r x

/-- `f^{[r]}(x)` for a function defined only on `I`. -/
noncomputable def ditTopOnFun (I : Set ℝ) (f : ↥I → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  ditTopOn I (IExt I f) r x

/-- The relative `p`-th derivative of a function defined only on `I`, again as a function on
`I`. -/
noncomputable def intervalIteratedDerivFun (I : Set ℝ) (p : ℕ) (f : ↥I → ℝ) : ↥I → ℝ :=
  fun y => intervalIteratedDeriv I p (IExt I f) (y : ℝ)

/-- Relative `C^p` regularity for a function defined only on `I`. -/
def ContDiffOnFun (I : Set ℝ) (p : ℕ) (f : ↥I → ℝ) : Prop := ContDiffOn ℝ (p : ℕ) (IExt I f) I

/-! ## Independence of the auxiliary extension -/

variable {I : Set ℝ}

lemma ddiffOn_of_extension (f : ↥I → ℝ) (F : ℝ → ℝ) (hF : ∀ y : ↥I, F (y : ℝ) = f y)
    {s : Finset ℝ} (hs : ↑s ⊆ I) : ddiffOn I f s = ddiff F s :=
  (ddiff_congr (eqOn_IExt f F hF) hs).symm

lemma interpPolyOn_of_extension (f : ↥I → ℝ) (F : ℝ → ℝ) (hF : ∀ y : ↥I, F (y : ℝ) = f y)
    {s : Finset ℝ} (hs : ↑s ⊆ I) : interpPolyOn I f s = interpPoly F s :=
  (interpPoly_congr (eqOn_IExt f F hF) hs).symm

lemma DDLimOnFun_of_extension (f : ↥I → ℝ) (F : ℝ → ℝ) (hF : ∀ y : ↥I, F (y : ℝ) = f y)
    (r : ℕ) (x L : ℝ) : DDLimOnFun I f r x L ↔ DDLimOn I F r x L :=
  (DDLimOn_congr (eqOn_IExt f F hF) r x L).symm

lemma HasDITOnFun_of_extension (f : ↥I → ℝ) (F : ℝ → ℝ) (hF : ∀ y : ↥I, F (y : ℝ) = f y)
    (n : ℕ) (x : ℝ) : HasDITOnFun I f n x ↔ HasDITOn I F n x :=
  (HasDITOn_congr (eqOn_IExt f F hF) n x).symm

lemma CoeffLimOnFun_of_extension (f : ↥I → ℝ) (F : ℝ → ℝ) (hF : ∀ y : ↥I, F (y : ℝ) = f y)
    (n q : ℕ) (x L : ℝ) : CoeffLimOnFun I f n q x L ↔ CoeffLimOn I F n q x L :=
  (CoeffLimOn_congr (eqOn_IExt f F hF) n q x L).symm

lemma HasDITcoeffOnFun_of_extension (f : ↥I → ℝ) (F : ℝ → ℝ) (hF : ∀ y : ↥I, F (y : ℝ) = f y)
    (n : ℕ) (x : ℝ) : HasDITcoeffOnFun I f n x ↔ HasDITcoeffOn I F n x :=
  (HasDITcoeffOn_congr (eqOn_IExt f F hF) n x).symm

lemma ddLimValOnFun_of_extension (f : ↥I → ℝ) (F : ℝ → ℝ) (hF : ∀ y : ↥I, F (y : ℝ) = f y)
    (r : ℕ) (x : ℝ) : ddLimValOnFun I f r x = ddLimValOn I F r x :=
  (ddLimValOn_congr (eqOn_IExt f F hF) r x).symm

lemma ditTopOnFun_of_extension (f : ↥I → ℝ) (F : ℝ → ℝ) (hF : ∀ y : ↥I, F (y : ℝ) = f y)
    (r : ℕ) (x : ℝ) : ditTopOnFun I f r x = ditTopOn I F r x :=
  (ditTopOn_congr (eqOn_IExt f F hF) r x).symm

lemma ContDiffOnFun_of_extension (f : ↥I → ℝ) (F : ℝ → ℝ) (hF : ∀ y : ↥I, F (y : ℝ) = f y)
    (p : ℕ) : ContDiffOnFun I p f ↔ ContDiffOn ℝ (p : ℕ) F I := by
  have h := eqOn_IExt f F hF
  constructor
  · exact fun hc => hc.congr fun y hy => h hy
  · exact fun hc => hc.congr fun y hy => (h hy).symm

lemma intervalIteratedDerivFun_of_extension (f : ↥I → ℝ) (F : ℝ → ℝ)
    (hF : ∀ y : ↥I, F (y : ℝ) = f y) (p : ℕ) (y : ↥I) :
    intervalIteratedDerivFun I p f y = intervalIteratedDeriv I p F (y : ℝ) :=
  (intervalIteratedDeriv_congr (eqOn_IExt f F hF) p y.2).symm

/-! ## Uniqueness of the relative limits and the order-zero classification -/

/-- **Uniqueness of the relative limits** on a nondegenerate interval, at every point including
the endpoints. -/
theorem ddLimOnFun_unique (hI : I.OrdConnected) (hne : I.Nontrivial) (f : ↥I → ℝ) (r : ℕ)
    (x : ↥I) {L1 L2 : ℝ} (h1 : DDLimOnFun I f r (x : ℝ) L1) (h2 : DDLimOnFun I f r (x : ℝ) L2) :
    L1 = L2 := DDLimOn.unique hI hne x.2 h1 h2

/-- **The order-zero classification** (continuity convention): relative `DIT(0)` at `x ∈ I` is
exactly relative continuity at `x`. -/
theorem hasDITOnFun_zero_iff (f : ↥I → ℝ) (x : ↥I) :
    HasDITOnFun I f 0 (x : ℝ) ↔ ContinuousWithinAt (IExt I f) I (x : ℝ) :=
  hasDITOn_zero_iff x.2

/-! ## Part (a) -/

/-- **Part (a) — canonical interval form.**  For an arbitrary nondegenerate interval `I`, a
function `f` defined only on `I`, and an arbitrary point `x ∈ I` (endpoints included): the literal
definition of `DIT(n)` (convergence of every monomial coefficient `c_q` of the Lagrange
interpolation polynomial, as the `n+1` distinct nodes tend to `x` inside `I`) is equivalent to
the convergence of the top coefficient `c_n` alone. -/
theorem part_a_interval (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nontrivial) (f : ↥I → ℝ)
    (n : ℕ) (x : ↥I) : HasDITcoeffOnFun I f n (x : ℝ) ↔ HasDITOnFun I f n (x : ℝ) :=
  part_a_On hI hne (IExt I f) (x : ℝ) x.2 n

/-- **Part (a) — the limiting polynomial**, interval form. -/
theorem part_a_limit_polynomial_interval (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nontrivial)
    (f : ↥I → ℝ) (n : ℕ) (x : ↥I) (hD : HasDITOnFun I f n (x : ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ s : Finset ℝ, s.card = n + 1 → (↑s ⊆ I) → (∀ t ∈ s, |t - (x : ℝ)| < δ) →
      ∀ q, |(interpPolyOn I f s).coeff q
        - (∑ k ∈ Finset.range (n+1),
            C (ddLimValOnFun I f k (x : ℝ)) * (X - C (x : ℝ))^k).coeff q| < ε :=
  part_a_limit_polynomialOn hI hne (IExt I f) (x : ℝ) x.2 n hD ε hε

/-! ## Part (b) -/

/-- **Part (b) — canonical interval form.**  Relative `DIT(n)` (`n = m+1 ≥ 1`) at `x ∈ I` implies
the Peano expansion `f(x+h) = ∑_{k≤n} λ_k h^k + o(|h|^n)`, where `h` ranges over the admissible
increments `H(I,x) = {h | x + h ∈ I}` only.  At a finite endpoint this is the one-sided
expansion; no value of `f` outside `I` occurs. -/
theorem part_b_interval (I : Set ℝ) (hI : I.OrdConnected) (f : ↥I → ℝ) (x : ↥I) (m : ℕ)
    (lam : ℕ → ℝ) (h : ∀ k ≤ m + 1, DDLimOnFun I f k (x : ℝ) (lam k)) :
    (∀ ε > 0, ∃ δ > 0, ∀ (hh : ℝ) (hmem : (x : ℝ) + hh ∈ I), 0 < |hh| → |hh| < δ →
        |f ⟨(x : ℝ) + hh, hmem⟩ - ∑ k ∈ Finset.range (m+2), lam k * hh ^ k|
          ≤ ε * |hh| ^ (m+1))
      ∧ (fun hh => IExt I f ((x : ℝ) + hh) - ∑ k ∈ Finset.range (m+2), lam k * hh ^ k)
          =o[nhdsWithin 0 (incrSet I (x : ℝ) \ {0})] (fun hh => hh ^ (m+1)) := by
  constructor
  · intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := part_b_expansionOn hI (IExt I f) (x : ℝ) x.2 m lam h ε hε
    refine ⟨δ, hδ, fun hh hmem hh0 hhδ => ?_⟩
    have := hδ' hh hmem hh0 hhδ
    rwa [IExt_apply f hmem] at this
  · exact part_b_isLittleOOn hI (IExt I f) (x : ℝ) x.2 m lam h

/-! ## Part (c) -/

/-- **Part (c) — canonical interval form.**  For `p < n` and `f` of class `C^p` on `I` in the
relative sense (`ContDiffOn ℝ p f I`, no two-sided extension assumed), `f` has relative `DIT(n)`
at `x ∈ I` if and only if the relative `p`-th derivative `f^{(p)}` has relative `DIT(n-p)` at
`x`. -/
theorem part_c_interval (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nontrivial) (f : ↥I → ℝ)
    (p n : ℕ) (hpn : p < n) (hf : ContDiffOnFun I p f) (x : ↥I) :
    HasDITOnFun I f n (x : ℝ) ↔
      HasDITOnFun I (intervalIteratedDerivFun I p f) (n - p) (x : ℝ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = p + k := ⟨n - p, by omega⟩
  have heq : Set.EqOn (IExt I (intervalIteratedDerivFun I p f))
      (intervalIteratedDeriv I p (IExt I f)) I := by
    intro y hy
    rw [IExt_apply _ hy]
    rfl
  rw [Nat.add_sub_cancel_left, HasDITOnFun, HasDITOnFun, HasDITOn_congr heq k (x : ℝ)]
  exact part_c_hasDITOn hI hne p (IExt I f) hf (x : ℝ) x.2 k

/-- **Part (c)**, the factorial/DIT-value identities, interval form: `(n-p)! λ_{n-p}(f^{(p)};x)
= n! λ_n(f;x)`, equivalently `(f^{(p)})^{[n-p]}(x) = f^{[n]}(x)`. -/
theorem part_c_values_interval (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nontrivial)
    (f : ↥I → ℝ) (p n : ℕ) (hpn : p < n) (hf : ContDiffOnFun I p f) (x : ↥I)
    (hD : HasDITOnFun I f n (x : ℝ)) :
    (Nat.factorial (n - p) : ℝ) * ddLimValOnFun I (intervalIteratedDerivFun I p f) (n - p) (x : ℝ)
        = (Nat.factorial n : ℝ) * ddLimValOnFun I f n (x : ℝ) ∧
      ditTopOnFun I (intervalIteratedDerivFun I p f) (n - p) (x : ℝ)
        = ditTopOnFun I f n (x : ℝ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = p + k := ⟨n - p, by omega⟩
  have heq : Set.EqOn (IExt I (intervalIteratedDerivFun I p f))
      (intervalIteratedDeriv I p (IExt I f)) I := by
    intro y hy
    rw [IExt_apply _ hy]
    rfl
  rw [Nat.add_sub_cancel_left]
  have hval : ddLimValOn I (IExt I (intervalIteratedDerivFun I p f)) k (x : ℝ)
      = ddLimValOn I (intervalIteratedDeriv I p (IExt I f)) k (x : ℝ) :=
    ddLimValOn_congr heq k (x : ℝ)
  have key := part_c_ddLimValOn hI hne p (IExt I f) hf (x : ℝ) x.2 k hD
  refine ⟨by rw [ddLimValOnFun, hval, key]; rfl, ?_⟩
  rw [ditTopOnFun, ditTopOnFun, ditTopOn, ditTopOn, hval, key]

/-! ## Part (d) -/

/-- **Part (d) — canonical interval form**, regularity and identification: if `f` has relative
`DIT(p)` (`p ≥ 1`) at **every point of `I`**, then `f` is exactly of class `C^p` on `I` in the
relative sense, and `f^{[p]}` coincides with the relative `p`-th derivative at every point of
`I`, finite endpoints included.  (The printed hypothesis `1 ≤ p` is kept, although the proof does
not need it.) -/
theorem part_d_regularity_interval (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nontrivial)
    (f : ↥I → ℝ) (p : ℕ) (hp : 1 ≤ p) (h : ∀ y : ↥I, HasDITOnFun I f p (y : ℝ)) :
    ContDiffOnFun I p f ∧ ∀ y : ↥I, ditTopOnFun I f p (y : ℝ)
      = intervalIteratedDerivFun I p f y := by
  have h' : ∀ y ∈ I, HasDITOn I (IExt I f) p y := fun y hy => h ⟨y, hy⟩
  refine ⟨contDiffOn_of_hasDITOn hI hne p (IExt I f) h', fun y => ?_⟩
  exact ditTopOn_eq_intervalIteratedDeriv hI hne p (IExt I f) h' (y : ℝ) y.2

/-- **Part (d) — canonical interval form.**  If `f` has relative `DIT(p)` at every point of the
nondegenerate interval `I` (`p ≥ 1`), then for every `n > p` and every `x ∈ I` (endpoints
included), `f` has relative `DIT(n)` at `x` if and only if `f^{[p]}` has relative `DIT(n-p)` at
`x`.  The hypothesis ranges only over points of `I`, and `f^{[p]}` is the relative top DIT value,
not a pre-supplied derivative.  (The printed hypothesis `1 ≤ p` is kept, although the proof does
not need it: the case `p = 0` also holds, under the continuity convention.) -/
theorem part_d_interval (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nontrivial) (f : ↥I → ℝ)
    (p n : ℕ) (hp : 1 ≤ p) (hpn : p < n) (h : ∀ y : ↥I, HasDITOnFun I f p (y : ℝ)) (x : ↥I) :
    HasDITOnFun I f n (x : ℝ) ↔
      HasDITOnFun I (fun y : ↥I => ditTopOnFun I f p (y : ℝ)) (n - p) (x : ℝ) := by
  have h' : ∀ y ∈ I, HasDITOn I (IExt I f) p y := fun y hy => h ⟨y, hy⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = p + k := ⟨n - p, by omega⟩
  have heq : Set.EqOn (IExt I (fun y : ↥I => ditTopOnFun I f p (y : ℝ)))
      (fun y => ditTopOn I (IExt I f) p y) I := by
    intro y hy
    rw [IExt_apply _ hy]
    rfl
  rw [Nat.add_sub_cancel_left, HasDITOnFun, HasDITOnFun, HasDITOn_congr heq k (x : ℝ)]
  exact part_d_On hI hne p k (IExt I f) h' (x : ℝ) x.2

/-! ## Agreement with the preserved whole-line baseline (`I = Set.univ`) -/

lemma IExt_univ (f : ↥(Set.univ : Set ℝ) → ℝ) :
    IExt Set.univ f = fun y => f ⟨y, Set.mem_univ y⟩ := by
  funext y
  exact IExt_apply f (Set.mem_univ y)

theorem hasDITOnFun_univ (f : ↥(Set.univ : Set ℝ) → ℝ) (n : ℕ) (x : ℝ) :
    HasDITOnFun Set.univ f n x ↔ HasDIT (fun y => f ⟨y, Set.mem_univ y⟩) n x := by
  rw [HasDITOnFun, IExt_univ, HasDITOn_univ]

theorem hasDITcoeffOnFun_univ (f : ↥(Set.univ : Set ℝ) → ℝ) (n : ℕ) (x : ℝ) :
    HasDITcoeffOnFun Set.univ f n x ↔ HasDITcoeff (fun y => f ⟨y, Set.mem_univ y⟩) n x := by
  rw [HasDITcoeffOnFun, IExt_univ, HasDITcoeffOn_univ]

theorem ddLimValOnFun_univ (f : ↥(Set.univ : Set ℝ) → ℝ) (r : ℕ) (x : ℝ) :
    ddLimValOnFun Set.univ f r x = ddLimVal (fun y => f ⟨y, Set.mem_univ y⟩) r x := by
  rw [ddLimValOnFun, IExt_univ, ddLimValOn_univ]

theorem ditTopOnFun_univ (f : ↥(Set.univ : Set ℝ) → ℝ) (r : ℕ) (x : ℝ) :
    ditTopOnFun Set.univ f r x = ditTop (fun y => f ⟨y, Set.mem_univ y⟩) r x := by
  rw [ditTopOnFun, IExt_univ, ditTopOn_univ]

theorem intervalIteratedDerivFun_univ (f : ↥(Set.univ : Set ℝ) → ℝ) (p : ℕ) (y : ℝ) :
    intervalIteratedDerivFun Set.univ p f ⟨y, Set.mem_univ y⟩
      = iteratedDeriv p (fun z => f ⟨z, Set.mem_univ z⟩) y := by
  rw [intervalIteratedDerivFun, IExt_univ, intervalIteratedDeriv_univ]

/-- `Set.univ` corollary of part (a): the interval statement specializes to the baseline
`Q587.part_a`. -/
theorem part_a_interval_univ (f : ↥(Set.univ : Set ℝ) → ℝ) (n : ℕ) (x : ℝ) :
    (HasDITcoeffOnFun Set.univ f n x ↔ HasDITOnFun Set.univ f n x) ↔
      (HasDITcoeff (fun y => f ⟨y, Set.mem_univ y⟩) n x
        ↔ HasDIT (fun y => f ⟨y, Set.mem_univ y⟩) n x) := by
  rw [hasDITOnFun_univ, hasDITcoeffOnFun_univ]

/-- `Set.univ` corollary of part (d): the interval statement specializes to the baseline
`Q587.part_d`. -/
theorem part_d_interval_univ (f : ↥(Set.univ : Set ℝ) → ℝ) (p k : ℕ)
    (h : ∀ y : ℝ, HasDIT (fun z => f ⟨z, Set.mem_univ z⟩) p y) (x : ℝ) :
    HasDITOnFun Set.univ f (p + k) x ↔
      HasDIT (fun y => ditTop (fun z => f ⟨z, Set.mem_univ z⟩) p y) k x := by
  rw [hasDITOnFun_univ]
  exact part_d p k (fun y => f ⟨y, Set.mem_univ y⟩) h x

/-! ## Sanity checks: the canonical statements apply at a finite endpoint -/

section EndpointCheck

/-- `[0,1]` is an order-connected, nondegenerate interval. -/
lemma ordConnected_unitInterval : (Set.Icc (0:ℝ) 1).OrdConnected := Set.ordConnected_Icc

lemma nontrivial_unitInterval : (Set.Icc (0:ℝ) 1).Nontrivial :=
  ⟨0, by norm_num, 1, by norm_num, by norm_num⟩

/-- Part (a) at the **left endpoint** `0` of `[0,1]`. -/
example (f : ↥(Set.Icc (0:ℝ) 1) → ℝ) (n : ℕ) :
    HasDITcoeffOnFun (Set.Icc (0:ℝ) 1) f n 0 ↔ HasDITOnFun (Set.Icc (0:ℝ) 1) f n 0 :=
  part_a_interval _ ordConnected_unitInterval nontrivial_unitInterval f n ⟨0, by norm_num⟩

/-- Part (d) at the **right endpoint** `1` of `[0,1]`. -/
example (f : ↥(Set.Icc (0:ℝ) 1) → ℝ) (p n : ℕ) (hp : 1 ≤ p) (hpn : p < n)
    (h : ∀ y : ↥(Set.Icc (0:ℝ) 1), HasDITOnFun (Set.Icc (0:ℝ) 1) f p (y : ℝ)) :
    HasDITOnFun (Set.Icc (0:ℝ) 1) f n 1 ↔
      HasDITOnFun (Set.Icc (0:ℝ) 1)
        (fun y : ↥(Set.Icc (0:ℝ) 1) => ditTopOnFun (Set.Icc (0:ℝ) 1) f p (y : ℝ)) (n - p) 1 :=
  part_d_interval _ ordConnected_unitInterval nontrivial_unitInterval f p n hp hpn h
    ⟨1, by norm_num⟩

end EndpointCheck

end Q587
