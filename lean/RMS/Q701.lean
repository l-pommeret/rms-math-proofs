import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Q701 : extreme points of the set of anchored `α`-Hölder functions of ratio ≤ 1

Let `0 < α < 1`, `I = [0,1]` and

  `C α = { f : I → ℝ | f 0 = 0 ∧ ∀ x y, |f x - f y| ≤ |x - y| ^ α }`.

This is a convex set.  For `f ∈ C α` define the *slack*

  `σ f x y = |x - y| ^ α - |f x - f y| ≥ 0`,

and the *path pseudometric*

  `ρ f a b = inf { Σ_{i<n} σ f (x i) (x (i+1)) : x 0 = a, x n = b }`.

The main theorem `Q701.mem_extremePoints_iff` states

  `f` is an extreme point of `C α`  ↔  `∀ x, ρ f 0 x = 0`,

i.e. every point of `[0,1]` can be joined to `0` by finite chains along which the total
deficit in the Hölder inequalities is arbitrarily small (`Q701.mem_extremePoints_iff_chains`).

The characterisation is purely metric/algebraic: it needs neither `0 < α` nor `α < 1`, so the
exponent is an unconstrained real parameter in the statements below (the case `0 < α < 1`
of Q701 is a particular instance).  As an illustration, `Q701.rpow_mem_extremePoints`
shows that `x ↦ x ^ α` is an extreme point when `0 < α ≤ 1`, while
`Q701.zero_notMem_extremePoints` shows the zero function is not extreme.

## Mismatches with the printed statement

* The printed problem considers `C([0,1])` with the uniform topology; here `C α` is taken
  inside the vector space of *all* functions `[0,1] → ℝ`.  Membership in `C α` forces
  continuity, and extremality is a purely algebraic (convexity) notion, so the two readings
  of "extreme point" agree.
* "α-Hölder of ratio 1" is read as "Hölder constant at most 1" (otherwise the set is not
  convex), as explained in the source answer.
* Only the main characterisation (conditions (1), (2), (4) of the answer, i.e. the chain
  criterion) is formalised, together with convexity and two illustrative examples; the
  optional material (McShane extensions, exposed points, strong extremality, `α = 1`) is not.
* The characterisation is proved for an arbitrary real exponent `α`; the Q701 range
  `0 < α < 1` is a special case, so no hypothesis on `α` appears in the main theorem.

## Versions

Lean 4.28.0, mathlib at commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (tag `v4.28.0`).
-/

namespace Q701

noncomputable section

/-- The unit interval, as a type. -/
abbrev I : Type := Set.Icc (0 : ℝ) 1

/-- The base point `0` of `I`. -/
def Izero : I := ⟨0, by norm_num⟩

@[simp] lemma coe_Izero : ((Izero : I) : ℝ) = 0 := rfl

/-- `HolderBall α` is the set of functions `f : [0,1] → ℝ` with `f 0 = 0` which are
`α`-Hölder with constant at most `1`. -/
def HolderBall (α : ℝ) : Set (I → ℝ) :=
  {f | f Izero = 0 ∧ ∀ x y : I, |f x - f y| ≤ |(x : ℝ) - (y : ℝ)| ^ α}

/-- The slack of `f` at the pair `(x,y)`: the deficit in the Hölder inequality. -/
def slack (α : ℝ) (f : I → ℝ) (x y : I) : ℝ := |(x : ℝ) - (y : ℝ)| ^ α - |f x - f y|

/-- The total slack of the chain `x 0, x 1, …, x n`. -/
def chainSlack (α : ℝ) (f : I → ℝ) (x : ℕ → I) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, slack α f (x i) (x (i + 1))

/-- The set of total slacks of chains joining `a` to `b`. -/
def chainSlacks (α : ℝ) (f : I → ℝ) (a b : I) : Set ℝ :=
  {s | ∃ (n : ℕ) (x : ℕ → I), x 0 = a ∧ x n = b ∧ chainSlack α f x n = s}

/-- The path pseudometric attached to `f`: the infimum of the total slacks of chains. -/
def rho (α : ℝ) (f : I → ℝ) (a b : I) : ℝ := sInf (chainSlacks α f a b)

section Basic

variable {α : ℝ} {f : I → ℝ}

lemma slack_comm (x y : I) : slack α f x y = slack α f y x := by
  simp only [slack, abs_sub_comm]

lemma slack_nonneg (hf : f ∈ HolderBall α) (x y : I) : 0 ≤ slack α f x y :=
  sub_nonneg.2 (hf.2 x y)

lemma chainSlack_nonneg (hf : f ∈ HolderBall α) (x : ℕ → I) (n : ℕ) :
    0 ≤ chainSlack α f x n :=
  Finset.sum_nonneg fun _ _ => slack_nonneg hf _ _

lemma chainSlacks_nonempty (a b : I) : (chainSlacks α f a b).Nonempty := by
  refine ⟨chainSlack α f (fun i => if i = 0 then a else b) 1, 1,
    (fun i => if i = 0 then a else b), by simp, by simp, rfl⟩

lemma chainSlacks_bddBelow (hf : f ∈ HolderBall α) (a b : I) :
    BddBelow (chainSlacks α f a b) := by
  refine ⟨0, ?_⟩
  rintro s ⟨n, x, -, -, rfl⟩
  exact chainSlack_nonneg hf x n

lemma rho_nonneg (hf : f ∈ HolderBall α) (a b : I) : 0 ≤ rho α f a b := by
  refine le_csInf (chainSlacks_nonempty a b) ?_
  rintro s ⟨n, x, -, -, rfl⟩
  exact chainSlack_nonneg hf x n

lemma rho_le_slack (hf : f ∈ HolderBall α) (a b : I) : rho α f a b ≤ slack α f a b := by
  refine csInf_le (chainSlacks_bddBelow hf a b) ⟨1, (fun i => if i = 0 then a else b), by simp,
    by simp, ?_⟩
  simp [chainSlack]

lemma rho_self (hf : f ∈ HolderBall α) (a : I) : rho α f a a = 0 := by
  refine le_antisymm ?_ (rho_nonneg hf a a)
  refine csInf_le (chainSlacks_bddBelow hf a a) ⟨0, (fun _ => a), rfl, rfl, ?_⟩
  simp [chainSlack]

/-- Appending one edge to a chain: `ρ f a c ≤ ρ f a b + σ f b c`. -/
lemma rho_le_rho_add_slack (hf : f ∈ HolderBall α) (a b c : I) :
    rho α f a c ≤ rho α f a b + slack α f b c := by
  refine le_of_forall_pos_lt_add ?_
  intro ε hε
  obtain ⟨s, hs, hs'⟩ := Real.lt_sInf_add_pos (chainSlacks_nonempty (f := f) (α := α) a b) hε
  obtain ⟨n, x, hx0, hxn, rfl⟩ := hs
  set y : ℕ → I := fun i => if i ≤ n then x i else c with hy
  have hy0 : y 0 = a := by simp [hy, hx0]
  have hyn : y n = b := by simp [hy, hxn]
  have hysucc : y (n + 1) = c := by simp [hy]
  have hchain : chainSlack α f y (n + 1) = chainSlack α f x n + slack α f b c := by
    rw [chainSlack, Finset.sum_range_succ, hyn, hysucc]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp only [Finset.mem_range] at hi
    have h1 : y i = x i := by simp [hy, Nat.le_of_lt hi]
    have h2 : y (i + 1) = x (i + 1) := by simp [hy, hi]
    rw [h1, h2]
  have hle : rho α f a c ≤ chainSlack α f x n + slack α f b c :=
    csInf_le (chainSlacks_bddBelow hf a c) ⟨n + 1, y, hy0, hysucc, hchain⟩
  have hrho : rho α f a b = sInf (chainSlacks α f a b) := rfl
  rw [hrho]
  linarith

/-- If `u` has increments bounded by the slack of `f`, then they are bounded by `ρ f`. -/
lemma abs_sub_le_rho {u : I → ℝ}
    (hu : ∀ x y : I, |u x - u y| ≤ slack α f x y) (a b : I) :
    |u a - u b| ≤ rho α f a b := by
  refine le_csInf (chainSlacks_nonempty a b) ?_
  rintro s ⟨n, x, hx0, hxn, rfl⟩
  subst hx0
  subst hxn
  induction n with
  | zero => simp [chainSlack]
  | succ n ih =>
      rw [chainSlack, Finset.sum_range_succ]
      have h1 : |u (x 0) - u (x n)| ≤ chainSlack α f x n := ih
      have h2 : |u (x n) - u (x (n + 1))| ≤ slack α f (x n) (x (n + 1)) := hu _ _
      calc |u (x 0) - u (x (n + 1))|
          ≤ |u (x 0) - u (x n)| + |u (x n) - u (x (n + 1))| := by
            simpa using abs_sub_le (u (x 0)) (u (x n)) (u (x (n + 1)))
        _ ≤ chainSlack α f x n + slack α f (x n) (x (n + 1)) := by linarith
end Basic

section Perturbation

variable {α : ℝ} {f : I → ℝ}

/-- The real scalar identity `max (|A+B|) (|A-B|) = |A| + |B|`, in the form needed here. -/
lemma abs_add_abs_le_of_abs_add_abs_sub_le {A B d : ℝ} (h1 : |A + B| ≤ d) (h2 : |A - B| ≤ d) :
    |A| + |B| ≤ d := by
  obtain ⟨p, q⟩ := abs_le.mp h1
  obtain ⟨r, s⟩ := abs_le.mp h2
  rcases abs_cases A with ⟨hA, -⟩ | ⟨hA, -⟩ <;> rcases abs_cases B with ⟨hB, -⟩ | ⟨hB, -⟩ <;>
    rw [hA, hB] <;> linarith

/-- Lemma 4.1, easy direction: an anchored perturbation whose increments are dominated by the
slack keeps `f ± u` inside the ball. -/
lemma add_mem_HolderBall (hf : f ∈ HolderBall α) {u : I → ℝ} (hu0 : u Izero = 0)
    (hu : ∀ x y : I, |u x - u y| ≤ slack α f x y) : (f + u) ∈ HolderBall α := by
  refine ⟨by simp [hf.1, hu0], fun x y => ?_⟩
  have h1 := hu x y
  have h2 := hf.2 x y
  have : |(f + u) x - (f + u) y| ≤ |f x - f y| + |u x - u y| := by
    simpa [Pi.add_apply, add_sub_add_comm] using abs_add_le (f x - f y) (u x - u y)
  simp only [slack] at h1
  linarith

lemma sub_mem_HolderBall (hf : f ∈ HolderBall α) {u : I → ℝ} (hu0 : u Izero = 0)
    (hu : ∀ x y : I, |u x - u y| ≤ slack α f x y) : (f - u) ∈ HolderBall α := by
  refine ⟨by simp [hf.1, hu0], fun x y => ?_⟩
  have h1 := hu x y
  have h2 := hf.2 x y
  have : |(f - u) x - (f - u) y| ≤ |f x - f y| + |u x - u y| := by
    have : (f - u) x - (f - u) y = (f x - f y) - (u x - u y) := by
      simp [Pi.sub_apply]; ring
    rw [this]
    exact abs_sub (f x - f y) (u x - u y)
  simp only [slack] at h1
  linarith

end Perturbation

section Main

variable {α : ℝ} {f : I → ℝ}

/-- **Main theorem (Q701).**  A function `f` in the anchored Hölder ball is an extreme point
of that (convex) set if and only if the path pseudometric `ρ f` vanishes between `0` and every
point. -/
theorem mem_extremePoints_iff (hf : f ∈ HolderBall α) :
    f ∈ (HolderBall α).extremePoints ℝ ↔ ∀ x : I, rho α f Izero x = 0 := by
  constructor
  · rintro ⟨-, hext⟩ x
    by_contra hx
    -- the canonical perturbation `u = ρ f 0 ·`
    set u : I → ℝ := fun z => rho α f Izero z with hu
    have hu0 : u Izero = 0 := rho_self hf _
    have hubd : ∀ x y : I, |u x - u y| ≤ slack α f x y := by
      intro p q
      have h1 : rho α f Izero p ≤ rho α f Izero q + slack α f q p :=
        rho_le_rho_add_slack hf _ _ _
      have h2 : rho α f Izero q ≤ rho α f Izero p + slack α f p q :=
        rho_le_rho_add_slack hf _ _ _
      rw [slack_comm q p] at h1
      rw [abs_le]
      constructor <;> simp only [hu] <;> linarith
    have hplus : (f + u) ∈ HolderBall α := add_mem_HolderBall hf hu0 hubd
    have hminus : (f - u) ∈ HolderBall α := sub_mem_HolderBall hf hu0 hubd
    have hseg : f ∈ openSegment ℝ (f + u) (f - u) := by
      refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      funext z
      simp [Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      ring
    have := hext hplus hminus hseg
    have hux : u x = 0 := by
      have := congrFun this x
      simpa using this
    exact hx hux
  · intro h0
    refine ⟨hf, ?_⟩
    rintro g hg h hh ⟨a, b, ha, hb, hab, hfeq⟩
    -- write `g = f + b•(g-h)`, `h = f - a•(g-h)`; the scaled difference `c•(g-h)` with
    -- `c = min a b` is an admissible perturbation.
    set c : ℝ := min a b with hc
    have hc0 : 0 < c := lt_min ha hb
    have hca : c ≤ a := min_le_left _ _
    have hcb : c ≤ b := min_le_right _ _
    set u : I → ℝ := fun z => c * (g z - h z) with hu
    have hfz : ∀ z : I, f z = a * g z + b * h z := by
      intro z
      have := congrFun hfeq z
      simpa [Pi.add_apply, smul_eq_mul] using this.symm
    have hu0 : u Izero = 0 := by
      simp [hu, hg.1, hh.1]
    have hplus : ∀ x y : I, |(f x + u x) - (f y + u y)| ≤ |(x : ℝ) - (y : ℝ)| ^ α := by
      intro x y
      have hG := abs_le.mp (hg.2 x y)
      have hH := abs_le.mp (hh.2 x y)
      have hkey : (f x + u x) - (f y + u y)
          = (a + c) * (g x - g y) + (b - c) * (h x - h y) := by
        rw [hfz x, hfz y]; simp only [hu]; ring
      rw [hkey, abs_le]
      have hac : 0 ≤ a + c := by linarith
      have hbc : 0 ≤ b - c := by linarith
      constructor <;> nlinarith [hG.1, hG.2, hH.1, hH.2]
    have hminus : ∀ x y : I, |(f x - u x) - (f y - u y)| ≤ |(x : ℝ) - (y : ℝ)| ^ α := by
      intro x y
      have hG := abs_le.mp (hg.2 x y)
      have hH := abs_le.mp (hh.2 x y)
      have hkey : (f x - u x) - (f y - u y)
          = (a - c) * (g x - g y) + (b + c) * (h x - h y) := by
        rw [hfz x, hfz y]; simp only [hu]; ring
      rw [hkey, abs_le]
      have hac : 0 ≤ a - c := by linarith
      have hbc : 0 ≤ b + c := by linarith
      constructor <;> nlinarith [hG.1, hG.2, hH.1, hH.2]
    -- Lemma 4.1, hard direction
    have hubd : ∀ x y : I, |u x - u y| ≤ slack α f x y := by
      intro x y
      have h1 : |(f x - f y) + (u x - u y)| ≤ |(x : ℝ) - (y : ℝ)| ^ α := by
        have : (f x - f y) + (u x - u y) = (f x + u x) - (f y + u y) := by ring
        rw [this]; exact hplus x y
      have h2 : |(f x - f y) - (u x - u y)| ≤ |(x : ℝ) - (y : ℝ)| ^ α := by
        have : (f x - f y) - (u x - u y) = (f x - u x) - (f y - u y) := by ring
        rw [this]; exact hminus x y
      have := abs_add_abs_le_of_abs_add_abs_sub_le h1 h2
      simp only [slack]
      linarith
    have huzero : ∀ x : I, u x = 0 := by
      intro x
      have h1 : |u Izero - u x| ≤ rho α f Izero x := abs_sub_le_rho hubd _ _
      rw [h0 x, hu0] at h1
      have : |u x| ≤ 0 := by simpa using h1
      exact abs_nonpos_iff.mp this
    have hgh : g = h := by
      funext z
      have := huzero z
      simp only [hu, mul_eq_zero] at this
      rcases this with h' | h'
      · exact absurd h' (ne_of_gt hc0)
      · linarith
    funext z
    have := hfz z
    rw [hgh] at this ⊢
    have hfh : f z = h z := by
      rw [this]; linear_combination (h z) * hab
    rw [hfh]

/-- Reformulation of the main theorem as the chain condition (3.3) of the answer:
`f` is extreme iff every point can be joined to `0` by finite chains whose accumulated
Hölder deficit is arbitrarily small. -/
theorem mem_extremePoints_iff_chains (hf : f ∈ HolderBall α) :
    f ∈ (HolderBall α).extremePoints ℝ ↔
      ∀ (x : I) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (z : ℕ → I), z 0 = Izero ∧ z n = x ∧
        ∑ i ∈ Finset.range n,
          (|(z (i + 1) : ℝ) - (z i : ℝ)| ^ α - |f (z (i + 1)) - f (z i)|) < ε := by
  rw [mem_extremePoints_iff hf]
  constructor
  · intro h x ε hε
    obtain ⟨s, hs, hs'⟩ := Real.lt_sInf_add_pos (chainSlacks_nonempty (f := f) (α := α) Izero x) hε
    obtain ⟨n, z, hz0, hzn, rfl⟩ := hs
    refine ⟨n, z, hz0, hzn, ?_⟩
    have : rho α f Izero x = 0 := h x
    rw [rho] at this
    rw [this, zero_add] at hs'
    calc ∑ i ∈ Finset.range n, (|(z (i + 1) : ℝ) - (z i : ℝ)| ^ α - |f (z (i + 1)) - f (z i)|)
        = chainSlack α f z n := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simp only [slack, abs_sub_comm]
      _ < ε := hs'
  · intro h x
    refine le_antisymm ?_ (rho_nonneg hf _ _)
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨n, z, hz0, hzn, hlt⟩ := h x ε hε
    have hmem : chainSlack α f z n ∈ chainSlacks α f Izero x := ⟨n, z, hz0, hzn, rfl⟩
    have h1 : rho α f Izero x ≤ chainSlack α f z n :=
      csInf_le (chainSlacks_bddBelow hf _ _) hmem
    have h2 : chainSlack α f z n
        = ∑ i ∈ Finset.range n,
            (|(z (i + 1) : ℝ) - (z i : ℝ)| ^ α - |f (z (i + 1)) - f (z i)|) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      simp only [slack, abs_sub_comm]
    rw [h2] at h1
    linarith

end Main

section Convexity

variable {α : ℝ}

/-- The anchored Hölder ball is convex. -/
theorem convex_HolderBall (α : ℝ) : Convex ℝ (HolderBall α) := by
  rintro g ⟨hg0, hg⟩ h ⟨hh0, hh⟩ a b ha hb hab
  refine ⟨by simp [Pi.add_apply, smul_eq_mul, hg0, hh0], fun x y => ?_⟩
  have hG := abs_le.mp (hg x y)
  have hH := abs_le.mp (hh x y)
  have hkey : (a • g + b • h) x - (a • g + b • h) y
      = a * (g x - g y) + b * (h x - h y) := by
    simp [Pi.add_apply, smul_eq_mul]; ring
  rw [hkey, abs_le]
  constructor <;> nlinarith [hG.1, hG.2, hH.1, hH.2]

end Convexity

section Example

/-- Subadditivity of `t ↦ t ^ α` for `0 < α ≤ 1`. -/
lemma rpow_add_le_rpow_add_rpow {α r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hα : 0 < α)
    (hα1 : α ≤ 1) : (r + s) ^ α ≤ r ^ α + s ^ α := by
  have hp : (1 : ℝ) ≤ 1 / α := by
    rw [le_div_iff₀ hα]; linarith
  have := Real.rpow_add_rpow_le_add (p := 1 / α) (a := r ^ α) (b := s ^ α)
    (Real.rpow_nonneg hr α) (Real.rpow_nonneg hs α) hp
  have h1 : (r ^ α) ^ (1 / α) = r := by
    rw [← Real.rpow_mul hr]
    field_simp
    exact Real.rpow_one r
  have h2 : (s ^ α) ^ (1 / α) = s := by
    rw [← Real.rpow_mul hs]
    field_simp
    exact Real.rpow_one s
  rw [h1, h2] at this
  have h3 : (1 : ℝ) / (1 / α) = α := by field_simp
  rw [h3] at this
  exact this

/-- For `0 ≤ y ≤ x` and `0 < α ≤ 1` one has `x ^ α - y ^ α ≤ (x - y) ^ α`. -/
lemma rpow_sub_rpow_le {α x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (hα : 0 < α) (hα1 : α ≤ 1) :
    x ^ α - y ^ α ≤ (x - y) ^ α := by
  have h := rpow_add_le_rpow_add_rpow (r := x - y) (s := y) (by linarith) hy hα hα1
  have : x - y + y = x := by ring
  rw [this] at h
  linarith

/-- `x ↦ x ^ α` belongs to the anchored Hölder ball, for `0 < α ≤ 1`. -/
theorem rpow_mem_HolderBall {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (fun x : I => ((x : ℝ)) ^ α) ∈ HolderBall α := by
  refine ⟨by simp [Real.zero_rpow (ne_of_gt hα)], fun x y => ?_⟩
  have hx : (0 : ℝ) ≤ (x : ℝ) := x.2.1
  have hy : (0 : ℝ) ≤ (y : ℝ) := y.2.1
  rcases le_total (y : ℝ) (x : ℝ) with hle | hle
  · have h1 : (x : ℝ) ^ α - (y : ℝ) ^ α ≤ ((x : ℝ) - (y : ℝ)) ^ α :=
      rpow_sub_rpow_le hy hle hα hα1
    have h2 : (0 : ℝ) ≤ (x : ℝ) ^ α - (y : ℝ) ^ α := by
      have := Real.rpow_le_rpow hy hle (le_of_lt hα)
      linarith
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (x:ℝ) ^ α - (y:ℝ) ^ α),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ (x:ℝ) - (y:ℝ))]
    exact h1
  · have h1 : (y : ℝ) ^ α - (x : ℝ) ^ α ≤ ((y : ℝ) - (x : ℝ)) ^ α :=
      rpow_sub_rpow_le hx hle hα hα1
    have h2 : (0 : ℝ) ≤ (y : ℝ) ^ α - (x : ℝ) ^ α := by
      have := Real.rpow_le_rpow hx hle (le_of_lt hα)
      linarith
    rw [abs_of_nonpos (by linarith : (x:ℝ) ^ α - (y:ℝ) ^ α ≤ 0), abs_sub_comm,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ (y:ℝ) - (x:ℝ))]
    linarith

/-- The function `x ↦ x ^ α` is an extreme point of the anchored Hölder ball
(`0 < α ≤ 1`): every pair `(0, x)` is a tight pair, so `ρ f 0 x = 0`. -/
theorem rpow_mem_extremePoints {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (fun x : I => ((x : ℝ)) ^ α) ∈ (HolderBall α).extremePoints ℝ := by
  have hf := rpow_mem_HolderBall hα hα1
  rw [mem_extremePoints_iff hf]
  intro x
  have hx : (0 : ℝ) ≤ (x : ℝ) := x.2.1
  have hslack : slack α (fun x : I => ((x : ℝ)) ^ α) Izero x = 0 := by
    simp only [slack, coe_Izero, zero_sub, abs_neg, Real.zero_rpow (ne_of_gt hα), zero_sub,
      abs_neg]
    rw [abs_of_nonneg hx, abs_of_nonneg (Real.rpow_nonneg hx α)]
    ring
  have h1 : rho α (fun x : I => ((x : ℝ)) ^ α) Izero x ≤ 0 := by
    have := rho_le_slack hf Izero x
    rw [hslack] at this
    exact this
  exact le_antisymm h1 (rho_nonneg hf _ _)

/-- The zero function is in the ball. -/
theorem zero_mem_HolderBall {α : ℝ} : (fun _ : I => (0 : ℝ)) ∈ HolderBall α := by
  refine ⟨rfl, fun x y => ?_⟩
  simpa using Real.rpow_nonneg (abs_nonneg ((x : ℝ) - (y : ℝ))) α

/-- For the zero function the total slack of a chain dominates the `α`-snowflake distance
between its endpoints. -/
lemma rpow_dist_le_chainSlack_zero {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (x : ℕ → I) (n : ℕ) :
    |((x n : ℝ)) - (x 0 : ℝ)| ^ α ≤ chainSlack α (fun _ : I => (0 : ℝ)) x n := by
  induction n with
  | zero => simp [chainSlack, Real.zero_rpow (ne_of_gt hα)]
  | succ n ih =>
      rw [chainSlack, Finset.sum_range_succ]
      have hedge : slack α (fun _ : I => (0 : ℝ)) (x n) (x (n + 1))
          = |((x n : ℝ)) - (x (n + 1) : ℝ)| ^ α := by simp [slack]
      have htri : |((x (n + 1) : ℝ)) - (x 0 : ℝ)|
          ≤ |((x n : ℝ)) - (x 0 : ℝ)| + |((x n : ℝ)) - (x (n + 1) : ℝ)| := by
        calc |((x (n + 1) : ℝ)) - (x 0 : ℝ)|
            ≤ |((x (n + 1) : ℝ)) - (x n : ℝ)| + |((x n : ℝ)) - (x 0 : ℝ)| :=
              abs_sub_le _ _ _
          _ = |((x n : ℝ)) - (x 0 : ℝ)| + |((x n : ℝ)) - (x (n + 1) : ℝ)| := by
              rw [abs_sub_comm ((x (n + 1) : ℝ)) ((x n : ℝ))]; ring
      have hmono : |((x (n + 1) : ℝ)) - (x 0 : ℝ)| ^ α
          ≤ (|((x n : ℝ)) - (x 0 : ℝ)| + |((x n : ℝ)) - (x (n + 1) : ℝ)|) ^ α :=
        Real.rpow_le_rpow (abs_nonneg _) htri (le_of_lt hα)
      have hsub := rpow_add_le_rpow_add_rpow (α := α) (r := |((x n : ℝ)) - (x 0 : ℝ)|)
        (s := |((x n : ℝ)) - (x (n + 1) : ℝ)|) (abs_nonneg _) (abs_nonneg _) hα hα1
      rw [hedge]
      have : chainSlack α (fun _ : I => (0 : ℝ)) x n
          = ∑ i ∈ Finset.range n, slack α (fun _ : I => (0 : ℝ)) (x i) (x (i + 1)) := rfl
      rw [this] at ih
      linarith

/-- The point `1` of `I`. -/
def Ione : I := ⟨1, by norm_num⟩

/-- The zero function is *not* an extreme point of the anchored Hölder ball
(for `0 < α ≤ 1`): the criterion is therefore not vacuous. -/
theorem zero_notMem_extremePoints {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (fun _ : I => (0 : ℝ)) ∉ (HolderBall α).extremePoints ℝ := by
  intro hext
  have h := (mem_extremePoints_iff (zero_mem_HolderBall (α := α))).mp hext Ione
  have hone : (1 : ℝ) ≤ rho α (fun _ : I => (0 : ℝ)) Izero Ione := by
    refine le_csInf (chainSlacks_nonempty _ _) ?_
    rintro s ⟨n, x, hx0, hxn, rfl⟩
    have := rpow_dist_le_chainSlack_zero hα hα1 x n
    rw [hx0, hxn] at this
    simpa [Ione, Izero, Real.one_rpow] using this
  rw [h] at hone
  linarith

end Example

end

end Q701
