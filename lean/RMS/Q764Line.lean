/-
# Q764 — Stage 3a: the numeric prefix optimum of the line dynamic program

`Q764.rho x p j` is the total numeric value (in `WithTop ℝ`) of the bottleneck dynamic
program: the least radius with which the first `j` points can be covered by `p` blocks.
`Q764.rho_le_iff` is the sublevel-set dictionary

```
0 ≤ r → j ≤ n → (rho x p j ≤ r ↔ CoverPrefix x n j p r),
```

which identifies the numeric recurrence with the already compiled feasibility recurrence
`Q764.coverPrefix_succ_iff`, hence — through `Q764.coverPrefix_iff_exists_centers` — with
the original `k`-center problem on the real line.
-/
import RMS.Q764Bridge

open Finset

namespace Q764

namespace Line

variable {x : ℕ → ℝ}

/-- The one-centre cost of the block `[i,j]`, as a total function (junk value `0` when
`j < i`). -/
noncomputable def bcost (x : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if h : i ≤ j then blockCost x i j h else 0

lemma bcost_eq {i j : ℕ} (h : i ≤ j) : bcost x i j = blockCost x i j h := dif_pos h

lemma bcost_of_not_le {i j : ℕ} (h : ¬ i ≤ j) : bcost x i j = 0 := dif_neg h

lemma bcost_nonneg (hx : Monotone x) (i j : ℕ) : 0 ≤ bcost x i j := by
  rw [bcost]
  split_ifs with h
  · rw [blockCost_eq hx h]
    have h1 : 0 ≤ (x j - x i) / 2 := by
      have := hx h; linarith
    have h2 : (0 : ℝ) ≤ (Icc i j).inf' (nonempty_Icc.2 h) fun l => |x l - (x i + x j) / 2| :=
      Finset.le_inf' _ _ fun l _ => abs_nonneg _
    linarith
  · exact le_rfl

/-- **Stage 3a**: the numeric prefix optimum.  `rho x p j` is the least radius with which
the first `j` points can be covered by `p` blocks (`⊤` when this is impossible). -/
noncomputable def rho (x : ℕ → ℝ) : ℕ → ℕ → WithTop ℝ
  | 0, 0 => 0
  | 0, _ + 1 => ⊤
  | _ + 1, 0 => 0
  | p + 1, j + 1 =>
      (Finset.range (j + 1)).inf' (Finset.nonempty_range_add_one)
        fun i => max (rho x p i) ((bcost x i j : ℝ) : WithTop ℝ)

@[simp] lemma rho_zero_zero : rho x 0 0 = 0 := rfl
@[simp] lemma rho_zero_succ (j : ℕ) : rho x 0 (j + 1) = ⊤ := rfl
@[simp] lemma rho_succ_zero (p : ℕ) : rho x (p + 1) 0 = 0 := rfl

lemma rho_succ_succ (p j : ℕ) :
    rho x (p + 1) (j + 1) =
      (Finset.range (j + 1)).inf' (Finset.nonempty_range_add_one)
        fun i => max (rho x p i) ((bcost x i j : ℝ) : WithTop ℝ) := rfl

/-- `CoverPrefix` with no points to cover is always satisfiable. -/
lemma coverPrefix_zero (n p : ℕ) (r : ℝ) : CoverPrefix x n 0 p r :=
  ⟨∅, Finset.empty_subset _, by simp, by omega⟩

/-- With `0` centres nothing can be covered. -/
lemma not_coverPrefix_zero_centers {n j : ℕ} (hj : 0 < j) (r : ℝ) :
    ¬ CoverPrefix x n j 0 r := by
  rintro ⟨F, -, hcard, hcov⟩
  have hFe : F = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
  obtain ⟨l, hl, -⟩ := hcov 0 hj
  rw [hFe] at hl
  exact absurd hl (by simp)

/-- **Stage 3a — the sublevel-set dictionary**: the numeric dynamic program computes
exactly the feasibility predicate `Q764.CoverPrefix`. -/
theorem rho_le_iff (hx : Monotone x) {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    ∀ (p j : ℕ), j ≤ n → (rho x p j ≤ ((r : ℝ) : WithTop ℝ) ↔ CoverPrefix x n j p r) := by
  intro p
  induction p with
  | zero =>
      intro j hj
      cases j with
      | zero =>
          simp only [rho_zero_zero]
          constructor
          · intro _; exact coverPrefix_zero n 0 r
          · intro _
            exact_mod_cast (by exact_mod_cast hr : ((0 : ℝ) : WithTop ℝ) ≤ ((r : ℝ) : WithTop ℝ))
      | succ m =>
          simp only [rho_zero_succ]
          constructor
          · intro h
            exact absurd h (by simp)
          · intro h
            exact absurd h (not_coverPrefix_zero_centers (Nat.succ_pos m) r)
  | succ p ih =>
      intro j hj
      cases j with
      | zero =>
          simp only [rho_succ_zero]
          constructor
          · intro _; exact coverPrefix_zero n (p + 1) r
          · intro _
            exact_mod_cast (by exact_mod_cast hr : ((0 : ℝ) : WithTop ℝ) ≤ ((r : ℝ) : WithTop ℝ))
      | succ m =>
          have hmn : m < n := by omega
          rw [rho_succ_succ, Finset.inf'_le_iff, coverPrefix_succ_iff hx hmn r]
          constructor
          · rintro ⟨i, hi, hle⟩
            rw [max_le_iff] at hle
            have him : i ≤ m := by simpa [Nat.lt_succ_iff] using hi
            refine ⟨i, him, ?_, ?_⟩
            · rw [← bcost_eq him]
              exact_mod_cast hle.2
            · exact (ih i (by omega)).1 hle.1
          · rintro ⟨i, him, hblock, hprefix⟩
            refine ⟨i, Finset.mem_range.2 (by omega), max_le ?_ ?_⟩
            · exact (ih i (by omega)).2 hprefix
            · rw [bcost_eq him]
              exact_mod_cast hblock

/-- The optimum for the whole point set: `rho x k n ≤ r` is exactly the `k`-center
feasibility of radius `r` for `X = {x 0, …, x (n-1)}`. -/
theorem rho_le_iff_exists_centers (hx : Monotone x) (hinj : Function.Injective x)
    {n k : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    rho x k n ≤ ((r : ℝ) : WithTop ℝ) ↔
      ∃ F ⊆ (range n).image x, F.card ≤ k ∧
        ∀ y ∈ (range n).image x, ∃ f ∈ F, dist y f ≤ r := by
  rw [rho_le_iff hx hr k n le_rfl, coverPrefix_iff_exists_centers hinj r]

/-! ## Monotonicity of the layers -/

lemma rho_nonneg : ∀ (p j : ℕ), (0 : WithTop ℝ) ≤ rho x p j := by
  intro p
  induction p with
  | zero => intro j; cases j <;> simp
  | succ p ih =>
      intro j
      cases j with
      | zero => simp
      | succ m =>
          rw [rho_succ_succ]
          refine Finset.le_inf' _ _ fun i _ => le_trans (ih i) (le_max_left _ _)

lemma rho_eq_coe_nonneg {p j : ℕ} {v : ℝ}
    (hv : rho x p j = ((v : ℝ) : WithTop ℝ)) : 0 ≤ v := by
  have := rho_nonneg (x := x) p j
  rw [hv] at this
  exact_mod_cast this

/-- **Stage 3b.2**: for a fixed number of blocks the prefix optimum is nondecreasing in
the number of points covered. -/
theorem rho_mono_right (hx : Monotone x) (p j : ℕ) : rho x p j ≤ rho x p (j + 1) := by
  by_cases htop : rho x p (j + 1) = ⊤
  · rw [htop]; exact le_top
  obtain ⟨v, hv⟩ : ∃ v : ℝ, rho x p (j + 1) = ((v : ℝ) : WithTop ℝ) := by
    cases hval : rho x p (j + 1) with
    | top => exact absurd hval htop
    | coe v => exact ⟨v, rfl⟩
  have hvnn : (0 : ℝ) ≤ v := rho_eq_coe_nonneg hv
  have hcov : CoverPrefix x (j + 1) (j + 1) p v :=
    (rho_le_iff hx hvnn p (j + 1) le_rfl).1 (by rw [hv])
  have hcov' : CoverPrefix x (j + 1) j p v := by
    obtain ⟨F, hF, hcard, hc⟩ := hcov
    exact ⟨F, hF, hcard, fun t ht => hc t (by omega)⟩
  rw [hv]
  exact (rho_le_iff hx hvnn p j (by omega)).2 hcov'

/-- More blocks never increase the prefix optimum. -/
theorem rho_antitone_blocks (hx : Monotone x) (p j : ℕ) : rho x (p + 1) j ≤ rho x p j := by
  by_cases htop : rho x p j = ⊤
  · rw [htop]; exact le_top
  obtain ⟨v, hv⟩ : ∃ v : ℝ, rho x p j = ((v : ℝ) : WithTop ℝ) := by
    cases hval : rho x p j with
    | top => exact absurd hval htop
    | coe v => exact ⟨v, rfl⟩
  have hvnn : (0 : ℝ) ≤ v := rho_eq_coe_nonneg hv
  have hcov : CoverPrefix x j j p v := (rho_le_iff hx hvnn p j le_rfl).1 (by rw [hv])
  have hcov' : CoverPrefix x j j (p + 1) v := by
    obtain ⟨F, hF, hcard, hc⟩ := hcov
    exact ⟨F, hF, by omega, hc⟩
  rw [hv]
  exact (rho_le_iff hx hvnn (p + 1) j le_rfl).2 hcov'

/-! ## Stage 3b: the crossing lemma -/

lemma bcost_self (hx : Monotone x) (i : ℕ) : bcost x i i = 0 := by
  rw [bcost_eq (le_refl i), blockCost_eq hx (le_refl i)]
  have h : ((Icc i i).inf' (nonempty_Icc.2 (le_refl i)) fun l => |x l - (x i + x i) / 2|) = 0 := by
    refine le_antisymm ?_ (Finset.le_inf' _ _ fun l _ => abs_nonneg _)
    simp
  rw [h]
  ring

/-- Removing points on the left never increases the block cost. -/
lemma bcost_antitone_left (hx : Monotone x) (i j : ℕ) : bcost x (i + 1) j ≤ bcost x i j := by
  by_cases h : i + 1 ≤ j
  · rw [bcost_eq h, bcost_eq (by omega : i ≤ j)]
    exact blockCost_mono_left hx h
  · rw [bcost_of_not_le h]
    rcases le_or_gt i j with hij | hij
    · have hij' : i = j := by omega
      subst hij'
      rw [bcost_self hx]
    · rw [bcost_of_not_le (by omega : ¬ i ≤ j)]

lemma bcost_antitone (hx : Monotone x) (j : ℕ) {a b : ℕ} (h : a ≤ b) :
    bcost x b j ≤ bcost x a j := by
  induction h with
  | refl => exact le_rfl
  | step h ih => exact le_trans (bcost_antitone_left hx _ _) ih

/-- Adding points on the right never decreases the block cost. -/
lemma bcost_mono_right (hx : Monotone x) (i j : ℕ) : bcost x i j ≤ bcost x i (j + 1) := by
  by_cases h : i ≤ j
  · rw [bcost_eq h, bcost_eq (by omega : i ≤ j + 1)]
    exact blockCost_mono_right hx h
  · rw [bcost_of_not_le h]
    exact bcost_nonneg hx _ _

lemma rho_mono_le (hx : Monotone x) (p : ℕ) {a b : ℕ} (h : a ≤ b) : rho x p a ≤ rho x p b := by
  induction h with
  | refl => exact le_rfl
  | step h ih => exact le_trans ih (rho_mono_right hx p _)

section Crossing

variable {α : Type*} [LinearOrder α] {A B : ℕ → α} {j c : ℕ}

/-- **Crossing lemma, right half**: past the first crossing the objective `max (A i) (B i)`
is at least its value at the crossing. -/
theorem crossing_right (hA : ∀ a b : ℕ, a ≤ b → A a ≤ A b) (hc : B c ≤ A c)
    {i : ℕ} (hci : c ≤ i) : max (A c) (B c) ≤ max (A i) (B i) :=
  le_trans (max_le le_rfl hc) (le_trans (hA c i hci) (le_max_left _ _))

/-- **Crossing lemma, left half**: before the first crossing the objective is at least its
value at the predecessor of the crossing. -/
theorem crossing_left (hB : ∀ a b : ℕ, a ≤ b → B b ≤ B a)
    (hcmin : ∀ i < c, ¬ (B i ≤ A i)) {i : ℕ} (hic : i < c) (hc1 : 0 < c) :
    max (A (c - 1)) (B (c - 1)) ≤ max (A i) (B i) := by
  have hlt : A (c - 1) < B (c - 1) := lt_of_not_ge (hcmin (c - 1) (by omega))
  have heq : max (A (c - 1)) (B (c - 1)) = B (c - 1) := max_eq_right (le_of_lt hlt)
  rw [heq]
  exact le_trans (hB i (c - 1) (by omega)) (le_max_right _ _)

/-- **Crossing lemma, no crossing**: if the crossing never happens the objective is
minimized at the right end. -/
theorem crossing_none (hB : ∀ a b : ℕ, a ≤ b → B b ≤ B a)
    (hnone : ∀ i ≤ j, ¬ (B i ≤ A i)) {i : ℕ} (hij : i ≤ j) :
    max (A j) (B j) ≤ max (A i) (B i) := by
  have hlt : A j < B j := lt_of_not_ge (hnone j le_rfl)
  rw [max_eq_right (le_of_lt hlt)]
  exact le_trans (hB i j hij) (le_max_right _ _)

/-- **The crossing pointer never moves left** when the right-hand family increases. -/
theorem crossing_monotone {B' : ℕ → α} (hBB' : ∀ i, B i ≤ B' i) {c c' : ℕ}
    (hcmin : ∀ i < c, ¬ (B i ≤ A i)) (hc' : B' c' ≤ A c') : c ≤ c' := by
  by_contra hlt
  push_neg at hlt
  exact hcmin c' hlt (le_trans (hBB' c') hc')

end Crossing

/-- **Stage 3b.2 instantiated**: in the layer `p` of the dynamic program the family
`i ↦ rho x p i` is nondecreasing and the family `i ↦ bcost x i j` is nonincreasing, so the
crossing lemmas above apply, and the crossing pointer of layer `p` cannot move left as `j`
increases. -/
theorem rho_layer_crossing_monotone (hx : Monotone x) (p j : ℕ) {c c' : ℕ}
    (hcmin : ∀ i < c, ¬ ((bcost x i j : WithTop ℝ) ≤ rho x p i))
    (hc' : ((bcost x c' (j + 1) : ℝ) : WithTop ℝ) ≤ rho x p c') : c ≤ c' :=
  crossing_monotone (B := fun i => ((bcost x i j : ℝ) : WithTop ℝ))
    (B' := fun i => ((bcost x i (j + 1) : ℝ) : WithTop ℝ))
    (fun i => by
      show ((bcost x i j : ℝ) : WithTop ℝ) ≤ ((bcost x i (j + 1) : ℝ) : WithTop ℝ)
      exact_mod_cast bcost_mono_right hx i j) hcmin hc'

end Line

end Q764
