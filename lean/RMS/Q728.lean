import Mathlib

/-!
# Q728 — the stick-splitting game

A position is a finite multiset of sticks of positive integer lengths.  A legal move
replaces one stick of length `m` by two sticks of **distinct** positive integer lengths
`a < b` with `a + b = m`.  Players `A` and `B` alternate, `A` moving first, until every
stick has length `1` or `2`.  If the terminal position has `x` sticks of length `1` and
`y` sticks of length `2`, then the last mover wins if `x > y`, loses if `x < y`, and the
game is a draw if `x = y`.

Main result (`Q728.main`): for `n ≥ 3`, the game starting from the single stick of
length `n` is a win for `A` if `n ≡ 2 [MOD 3]`, a win for `B` if `n ≡ 1 [MOD 3]`, and a
draw if `n ≡ 0 [MOD 3]`.

## Notes on the formalization

* **Hypothesis `3 ≤ n`.**  The printed problem does not state it, but for `n = 1, 2` no
  move is ever possible, so there is no "last mover" and the payoff rule is undefined.
  This is the only hypothesis added to the printed statement.
* **Outcomes.**  Instead of a numerical minimax value we use the two predicates
  `Good true P` ("the player to move at `P` can force a win") and `Good false P`
  ("the player to move at `P` can force at least a draw"), defined by well-founded
  recursion on the number of remaining moves.  Then, from the initial position `{n}`
  where `A` is to move:
  `AWins n := Good true {n}`, `BWins n := ¬ Good false {n}` (`A` cannot even avoid
  losing, i.e. `B` forces a win), and
  `Drawn n := Good false {n} ∧ ¬ Good true {n}` (`A` can avoid losing but cannot win,
  which is exactly the statement that both players have non-losing strategies).
* **Positions** are finite multisets of natural numbers; a move erases one stick `m`
  and inserts two sticks `a < b` with `0 < a` and `a + b = m`.  Positivity of all
  sticks is propagated as an invariant from the initial position `{n}`.
* The proof follows the solution: the weight `d m = 2 β m + η m` (`Q728.d`), the control
  interval encoded through `Dm P = ∑ d`, the overlap lemma (`Q728.move_Dm`), the
  steering lemma (`Q728.steer`) and the interval-control theorem (`Q728.control`).
  The parity bookkeeping of Section 8 of the solution is carried inside `control` by
  the invariant `(P.card + turn b) % 2 = par`.

## Versions

Lean 4 toolchain `leanprover/lean4:v4.28.0`; Mathlib at tag `v4.28.0`
(commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`).
-/

namespace Q728

open Multiset

/-! ## Positions and moves -/

/-- A legal move: replace a stick `m` of `P` by two distinct positive sticks `a < b`
with `a + b = m`. -/
def Move (P Q : Multiset ℕ) : Prop :=
  ∃ m ∈ P, ∃ a b : ℕ, 0 < a ∧ a < b ∧ a + b = m ∧ Q = a ::ₘ b ::ₘ P.erase m

/-- Weight of a stick: `d m = 2 * β m + η m` in the notation of the solution. -/
def d (m : ℕ) : ℕ := if m = 2 then 2 else 2 * (m / 3) + (if m % 3 = 2 then 1 else 0)

/-- The (doubled) centre of the control interval of a position. -/
def Dm (P : Multiset ℕ) : ℕ := (P.map d).sum

/-- Termination measure: each move decreases it by exactly one. -/
def msr (P : Multiset ℕ) : ℕ := (P.map (fun m => m - 1)).sum

lemma sumf_erase (f : ℕ → ℕ) {m : ℕ} {P : Multiset ℕ} (hm : m ∈ P) :
    (P.map f).sum = f m + ((P.erase m).map f).sum := by
  conv_lhs => rw [← Multiset.cons_erase hm]
  simp

lemma move_sum {P Q : Multiset ℕ} (h : Move P Q) : Q.sum = P.sum := by
  obtain ⟨m, hm, a, b, ha, hab, hs, rfl⟩ := h
  have h1 : P.sum = m + (P.erase m).sum := by
    conv_lhs => rw [← Multiset.cons_erase hm]
    simp
  simp [h1]
  omega

lemma move_card {P Q : Multiset ℕ} (h : Move P Q) : Q.card = P.card + 1 := by
  obtain ⟨m, hm, a, b, ha, hab, hs, rfl⟩ := h
  have h1 : P.card = (P.erase m).card + 1 := by
    conv_lhs => rw [← Multiset.cons_erase hm]
    simp
  simp [h1]

lemma move_msr {P Q : Multiset ℕ} (h : Move P Q) : msr Q + 1 = msr P := by
  obtain ⟨m, hm, a, b, ha, hab, hs, rfl⟩ := h
  have h1 : msr P = (m - 1) + ((P.erase m).map (fun m => m - 1)).sum :=
    sumf_erase _ hm
  simp only [msr, Multiset.map_cons, Multiset.sum_cons] at *
  omega

lemma move_pos {P Q : Multiset ℕ} (h : Move P Q) (hp : ∀ x ∈ P, 0 < x) : ∀ x ∈ Q, 0 < x := by
  obtain ⟨m, hm, a, b, ha, hab, hs, rfl⟩ := h
  intro x hx
  rcases Multiset.mem_cons.1 hx with rfl | hx
  · omega
  rcases Multiset.mem_cons.1 hx with rfl | hx
  · omega
  exact hp x (Multiset.mem_of_mem_erase hx)

/-- The effect of a move on `Dm`. -/
lemma move_Dm_eq {P Q : Multiset ℕ} {m a b : ℕ} (hm : m ∈ P)
    (hQ : Q = a ::ₘ b ::ₘ P.erase m) : Dm Q + d m = Dm P + (d a + d b) := by
  have h1 : Dm P = d m + ((P.erase m).map d).sum := sumf_erase _ hm
  subst hQ
  simp only [Dm, Multiset.map_cons, Multiset.sum_cons] at *
  omega

lemma move_Dm {P Q : Multiset ℕ} (h : Move P Q) : Dm P ≤ Dm Q + 1 ∧ Dm Q ≤ Dm P + 1 := by
  obtain ⟨m, hm, a, b, ha, hab, hs, hQ⟩ := h
  have key := move_Dm_eq hm hQ
  have harith : d a + d b + 1 ≥ d (a + b) ∧ d a + d b ≤ d (a + b) + 1 := by
    unfold d; split_ifs <;> omega
  rw [hs] at harith
  omega

/-! ## Terminal positions -/

lemma no_move_iff {P : Multiset ℕ} : (∀ Q, ¬ Move P Q) ↔ ∀ m ∈ P, m ≤ 2 := by
  constructor
  · intro h m hm
    by_contra hlt
    push_neg at hlt
    exact h (1 ::ₘ (m - 1) ::ₘ P.erase m) ⟨m, hm, 1, m - 1, by omega, by omega, by omega, rfl⟩
  · rintro h Q ⟨m, hm, a, b, ha, hab, hs, -⟩
    have := h m hm
    omega

lemma terminal_counts (Q : Multiset ℕ) (h2 : ∀ m ∈ Q, m ≤ 2) (hp : ∀ m ∈ Q, 0 < m) :
    Q.card = Q.count 1 + Q.count 2 ∧ Q.sum = Q.count 1 + 2 * Q.count 2 ∧
      Dm Q = 2 * Q.count 2 := by
  induction Q using Multiset.induction with
  | empty => simp [Dm]
  | cons a s ih =>
    have ha2 : a ≤ 2 := h2 a (Multiset.mem_cons_self _ _)
    have hap : 0 < a := hp a (Multiset.mem_cons_self _ _)
    have hs2 : ∀ m ∈ s, m ≤ 2 := fun m hm => h2 m (Multiset.mem_cons_of_mem hm)
    have hsp : ∀ m ∈ s, 0 < m := fun m hm => hp m (Multiset.mem_cons_of_mem hm)
    obtain ⟨i1, i2, i3⟩ := ih hs2 hsp
    interval_cases a <;>
      simp only [Dm, Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
        Multiset.count_cons, d] at * <;> norm_num at * <;> omega

/-! ## The steering lemma -/

lemma Dm_even {P : Multiset ℕ} (h : ∀ x ∈ P, 5 ≤ x → x % 3 ≠ 2) : Dm P % 2 = 0 := by
  unfold Dm
  induction P using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have hda : d a % 2 = 0 := by
      have := h a (Multiset.mem_cons_self _ _)
      unfold d; split_ifs <;> omega
    have := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    simp only [Multiset.map_cons, Multiset.sum_cons]
    omega

lemma steer {P : Multiset ℕ} (hne : ∃ m ∈ P, 3 ≤ m) (t : ℕ)
    (h1 : 2 * t ≤ Dm P + 1) (h2 : Dm P ≤ 2 * t + 3) :
    ∃ Q, Move P Q ∧ 2 * t ≤ Dm Q ∧ Dm Q ≤ 2 * t + 2 := by
  by_cases hhot : ∃ m ∈ P, 5 ≤ m ∧ m % 3 = 2
  · obtain ⟨m, hm, hm5, hm3⟩ := hhot
    by_cases hbig : 2 * t + 2 ≤ Dm P
    · -- split off a `1`, decreasing `Dm` by one
      refine ⟨1 ::ₘ (m - 1) ::ₘ P.erase m, ⟨m, hm, 1, m - 1, by omega, by omega, by omega, rfl⟩,
        ?_, ?_⟩ <;>
      · have key := move_Dm_eq (a := 1) (b := m - 1) hm rfl
        have : d 1 + d (m - 1) + 1 = d m := by unfold d; split_ifs <;> omega
        omega
    · -- split off a `2`, increasing `Dm` by one
      refine ⟨2 ::ₘ (m - 2) ::ₘ P.erase m, ⟨m, hm, 2, m - 2, by omega, by omega, by omega, rfl⟩,
        ?_, ?_⟩ <;>
      · have key := move_Dm_eq (a := 2) (b := m - 2) hm rfl
        have : d 2 + d (m - 2) = d m + 1 := by unfold d; split_ifs <;> omega
        omega
  · -- no hot stick: `Dm P` is even and there is a move that does not change it
    push_neg at hhot
    have heven : Dm P % 2 = 0 := Dm_even hhot
    obtain ⟨m, hm, hm3⟩ := hne
    have hnot2 : m % 3 ≠ 2 := by
      intro h
      exact absurd h (hhot m hm (by omega))
    by_cases hm0 : m % 3 = 0
    · by_cases hm3' : m = 3
      · refine ⟨1 ::ₘ 2 ::ₘ P.erase m, ⟨m, hm, 1, 2, by omega, by omega, by omega, rfl⟩, ?_, ?_⟩ <;>
        · have key := move_Dm_eq (a := 1) (b := 2) hm rfl
          have : d 1 + d 2 = d m := by unfold d; split_ifs <;> omega
          omega
      · refine ⟨2 ::ₘ (m - 2) ::ₘ P.erase m,
          ⟨m, hm, 2, m - 2, by omega, by omega, by omega, rfl⟩, ?_, ?_⟩ <;>
        · have key := move_Dm_eq (a := 2) (b := m - 2) hm rfl
          have : d 2 + d (m - 2) = d m := by unfold d; split_ifs <;> omega
          omega
    · refine ⟨1 ::ₘ (m - 1) ::ₘ P.erase m,
        ⟨m, hm, 1, m - 1, by omega, by omega, by omega, rfl⟩, ?_, ?_⟩ <;>
      · have key := move_Dm_eq (a := 1) (b := m - 1) hm rfl
        have : d 1 + d (m - 1) = d m := by unfold d; split_ifs <;> omega
        omega

/-! ## The game value -/

/-- `Good true P`: the player to move at `P` can force a win.
`Good false P`: the player to move at `P` can avoid losing (win or draw).

At a terminal position the player to move is the opponent of the last mover, so that
player wins iff `y > x` and does not lose iff `y ≥ x`, where `x` (resp. `y`) is the
number of sticks of length `1` (resp. `2`). -/
def Good (b : Bool) (P : Multiset ℕ) : Prop :=
  ((∀ Q, ¬ Move P Q) → (if b then P.count 1 < P.count 2 else P.count 1 ≤ P.count 2)) ∧
  (b = true → (∃ Q, Move P Q) → ∃ Q, ∃ _hm : Move P Q, ¬ Good false Q) ∧
  (b = false → (∃ Q, Move P Q) → ∃ Q, ∃ _hm : Move P Q, ¬ Good true Q)
termination_by msr P
decreasing_by
  all_goals (have := move_msr _hm; omega)

lemma Good_true_iff (P : Multiset ℕ) : Good true P ↔
    ((∀ Q, ¬ Move P Q) → P.count 1 < P.count 2) ∧
    ((∃ Q, Move P Q) → ∃ Q, Move P Q ∧ ¬ Good false Q) := by
  rw [Good]; simp

lemma Good_false_iff (P : Multiset ℕ) : Good false P ↔
    ((∀ Q, ¬ Move P Q) → P.count 1 ≤ P.count 2) ∧
    ((∃ Q, Move P Q) → ∃ Q, Move P Q ∧ ¬ Good true Q) := by
  rw [Good]; simp

/-! ## Forcing a terminal condition -/

/-- `Force T b P`: the *controller* can force the play starting at `P` to end at a
terminal position `Q` with `T c Q`, where the boolean `c` records whether the controller
is the player to move at `Q`.  The boolean `b` says whether the controller is to move
at `P`. -/
def Force (T : Bool → Multiset ℕ → Prop) (b : Bool) (P : Multiset ℕ) : Prop :=
  ((∀ Q, ¬ Move P Q) → T b P) ∧
  (b = true → (∃ Q, Move P Q) → ∃ Q, ∃ _hm : Move P Q, Force T false Q) ∧
  (b = false → ∀ Q, ∀ _hm : Move P Q, Force T true Q)
termination_by msr P
decreasing_by
  all_goals (have := move_msr _hm; omega)

/-- Terminal payoff predicate: "the controller wins". -/
def Twin : Bool → Multiset ℕ → Prop
  | true, Q => Q.count 1 < Q.count 2
  | false, Q => Q.count 2 < Q.count 1

/-- Terminal payoff predicate: "the controller does not lose". -/
def Tnl : Bool → Multiset ℕ → Prop
  | true, Q => Q.count 1 ≤ Q.count 2
  | false, Q => Q.count 2 ≤ Q.count 1

/-- `1` if the controller is the player to move, `0` otherwise.  Since each move
increases the number of sticks by one and passes the turn, the quantity
`(P.card + turn b) % 2` is invariant along a play. -/
def turn : Bool → ℕ
  | true => 1
  | false => 0

/-- If the controller can force a win, then: if he is to move he can win, and if he is
not to move then the player to move loses. -/
lemma force_win : ∀ (k : ℕ) (b : Bool) (P : Multiset ℕ), msr P = k → Force Twin b P →
    (b = true → Good true P) ∧ (b = false → ¬ Good false P) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro b P hk hF
    rw [Force] at hF
    obtain ⟨hterm, htrue, hfalse⟩ := hF
    constructor
    · rintro rfl
      rw [Good_true_iff]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simpa only [Twin] using hterm h
      · obtain ⟨Q, hm, hFQ⟩ := htrue rfl h
        have hlt : msr Q < k := by have := move_msr hm; omega
        exact ⟨Q, hm, (ih _ hlt false Q rfl hFQ).2 rfl⟩
    · rintro rfl hG
      rw [Good_false_iff] at hG
      obtain ⟨hg1, hg2⟩ := hG
      by_cases hex : ∃ Q, Move P Q
      · obtain ⟨Q, hm, hnG⟩ := hg2 hex
        have hlt : msr Q < k := by have := move_msr hm; omega
        exact hnG ((ih _ hlt true Q rfl (hfalse rfl Q hm)).1 rfl)
      · push_neg at hex
        have h1 := hterm hex
        have h2 := hg1 hex
        simp only [Twin] at h1
        omega

/-- If the controller can force a non-loss, then: if he is to move he can avoid losing,
and if he is not to move then the player to move cannot win. -/
lemma force_nonloss : ∀ (k : ℕ) (b : Bool) (P : Multiset ℕ), msr P = k → Force Tnl b P →
    (b = true → Good false P) ∧ (b = false → ¬ Good true P) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro b P hk hF
    rw [Force] at hF
    obtain ⟨hterm, htrue, hfalse⟩ := hF
    constructor
    · rintro rfl
      rw [Good_false_iff]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simpa only [Tnl] using hterm h
      · obtain ⟨Q, hm, hFQ⟩ := htrue rfl h
        have hlt : msr Q < k := by have := move_msr hm; omega
        exact ⟨Q, hm, (ih _ hlt false Q rfl hFQ).2 rfl⟩
    · rintro rfl hG
      rw [Good_true_iff] at hG
      obtain ⟨hg1, hg2⟩ := hG
      by_cases hex : ∃ Q, Move P Q
      · obtain ⟨Q, hm, hnG⟩ := hg2 hex
        have hlt : msr Q < k := by have := move_msr hm; omega
        exact hnG ((ih _ hlt true Q rfl (hfalse rfl Q hm)).1 rfl)
      · push_neg at hex
        have h1 := hterm hex
        have h2 := hg1 hex
        simp only [Tnl] at h1
        omega

/-! ## The interval-control theorem -/

/-- **Interval control.**  If the control interval of `P` meets `{t, t+1}` (and is
contained in it when the controller is not to move), then the controller can force the
terminal position to have its number `y` of sticks of length `2` in `{t, t+1}`.  The
target predicate `T` is arbitrary, subject to being implied by that information at
terminal positions (hypothesis `hT`); `N` is the conserved total length and `par` the
conserved parity linking the number of sticks with whose turn it is. -/
theorem control (N t par : ℕ) (T : Bool → Multiset ℕ → Prop)
    (hT : ∀ (b : Bool) (Q : Multiset ℕ), (∀ m ∈ Q, m ≤ 2) → (∀ m ∈ Q, 0 < m) → Q.sum = N →
      (Q.card + turn b) % 2 = par → 2 * t ≤ Dm Q + 1 → Dm Q ≤ 2 * t + 3 →
      T b Q) :
    ∀ (k : ℕ) (b : Bool) (P : Multiset ℕ), msr P = k → (∀ m ∈ P, 0 < m) → P.sum = N →
      (P.card + turn b) % 2 = par →
      2 * t ≤ Dm P + 1 → Dm P ≤ 2 * t + 3 →
      (b = false → 2 * t ≤ Dm P ∧ Dm P ≤ 2 * t + 2) →
      Force T b P := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro b P hk hpos hsum hpar h1 h2 hstrong
    rw [Force]
    refine ⟨fun h => hT b P (no_move_iff.1 h) hpos hsum hpar h1 h2, ?_, ?_⟩
    · rintro rfl hex
      have hbig : ∃ m ∈ P, 3 ≤ m := by
        by_contra hc
        push_neg at hc
        obtain ⟨Q, hQ⟩ := hex
        exact no_move_iff.2 (fun m hm => by have := hc m hm; omega) Q hQ
      obtain ⟨Q, hmv, hd1, hd2⟩ := steer hbig t h1 h2
      refine ⟨Q, hmv, ?_⟩
      have hlt : msr Q < k := by have := move_msr hmv; omega
      refine ih _ hlt false Q rfl (move_pos hmv hpos) (by rw [move_sum hmv, hsum]) ?_
        (by omega) (by omega) (fun _ => ⟨hd1, hd2⟩)
      rw [move_card hmv]
      simp only [turn] at *
      omega
    · rintro rfl Q hmv
      obtain ⟨hs1, hs2⟩ := hstrong rfl
      have hD := move_Dm hmv
      have hlt : msr Q < k := by have := move_msr hmv; omega
      refine ih _ hlt true Q rfl (move_pos hmv hpos) (by rw [move_sum hmv, hsum]) ?_
        (by omega) (by omega) (by simp)
      rw [move_card hmv]
      simp only [turn] at *
      omega

/-! ## The main theorem -/

/-- The first player `A` can force a win. -/
def AWins (n : ℕ) : Prop := Good true {n}

/-- The second player `B` can force a win, i.e. `A` cannot even avoid losing. -/
def BWins (n : ℕ) : Prop := ¬ Good false {n}

/-- The game is a draw: `A` can avoid losing, but cannot force a win. -/
def Drawn (n : ℕ) : Prop := Good false {n} ∧ ¬ Good true {n}

lemma Dm_singleton (n : ℕ) : Dm {n} = d n := by simp [Dm]

lemma pos_singleton {n : ℕ} (hn : 0 < n) : ∀ m ∈ ({n} : Multiset ℕ), 0 < m := by
  intro m hm; simp at hm; omega

lemma sum_singleton' (n : ℕ) : ({n} : Multiset ℕ).sum = n := by simp


theorem q728_A_wins {n : ℕ} (hn : 3 ≤ n) (h3 : n % 3 = 2) : AWins n := by
  have hd : d n = 2 * (n / 3) + 1 := by unfold d; split_ifs <;> omega
  refine (force_win (msr {n}) true {n} rfl ?_).1 rfl
  refine control n (n / 3) 0 Twin ?_ (msr {n}) true {n} rfl (pos_singleton (by omega))
    (sum_singleton' n) (by simp [turn]) (by rw [Dm_singleton]; omega)
    (by rw [Dm_singleton]; omega) (by simp)
  intro b Q hle hpos hsum hpar hd1 hd2
  obtain ⟨hc, hs, hD⟩ := terminal_counts Q hle hpos
  cases b <;> simp only [Twin, turn] at * <;> omega

theorem q728_B_wins {n : ℕ} (hn : 3 ≤ n) (h3 : n % 3 = 1) : BWins n := by
  have hd : d n = 2 * (n / 3) := by unfold d; split_ifs <;> omega
  refine (force_win (msr {n}) false {n} rfl ?_).2 rfl
  refine control n (n / 3) 1 Twin ?_ (msr {n}) false {n} rfl (pos_singleton (by omega))
    (sum_singleton' n) (by simp [turn]) (by rw [Dm_singleton]; omega)
    (by rw [Dm_singleton]; omega) (fun _ => by rw [Dm_singleton]; omega)
  intro b Q hle hpos hsum hpar hd1 hd2
  obtain ⟨hc, hs, hD⟩ := terminal_counts Q hle hpos
  cases b <;> simp only [Twin, turn] at * <;> omega

theorem q728_draw {n : ℕ} (hn : 3 ≤ n) (h3 : n % 3 = 0) : Drawn n := by
  have hd : d n = 2 * (n / 3) := by unfold d; split_ifs <;> omega
  constructor
  · -- `A` can avoid losing: `A` is the controller, with target `{q, q+1}`
    refine (force_nonloss (msr {n}) true {n} rfl ?_).1 rfl
    refine control n (n / 3) 0 Tnl ?_ (msr {n}) true {n} rfl (pos_singleton (by omega))
      (sum_singleton' n) (by simp [turn]) (by rw [Dm_singleton]; omega)
      (by rw [Dm_singleton]; omega) (by simp)
    intro b Q hle hpos hsum hpar hd1 hd2
    obtain ⟨hc, hs, hD⟩ := terminal_counts Q hle hpos
    cases b <;> simp only [Tnl, turn] at * <;> omega
  · -- `A` cannot win: `B` is the controller, with target `{q-1, q}`
    refine (force_nonloss (msr {n}) false {n} rfl ?_).2 rfl
    refine control n (n / 3 - 1) 1 Tnl ?_ (msr {n}) false {n} rfl (pos_singleton (by omega))
      (sum_singleton' n) (by simp [turn]) (by rw [Dm_singleton]; omega)
      (by rw [Dm_singleton]; omega) (fun _ => by rw [Dm_singleton]; omega)
    intro b Q hle hpos hsum hpar hd1 hd2
    obtain ⟨hc, hs, hD⟩ := terminal_counts Q hle hpos
    have hq : 1 ≤ n / 3 := by omega
    cases b <;> simp only [Tnl, turn] at * <;> omega

/-- **Q728.**  For every `n ≥ 3`, the stick game starting from a single stick of length
`n` is a win for the first player `A` when `n ≡ 2 [MOD 3]`, a win for the second player
`B` when `n ≡ 1 [MOD 3]`, and a draw when `n ≡ 0 [MOD 3]`. -/
theorem main {n : ℕ} (hn : 3 ≤ n) :
    (n % 3 = 2 → AWins n) ∧ (n % 3 = 1 → BWins n) ∧ (n % 3 = 0 → Drawn n) :=
  ⟨fun h => q728_A_wins hn h, fun h => q728_B_wins hn h, fun h => q728_draw hn h⟩

/-! ## Sanity checks

The first four cases, and a check that the notions are not vacuous: `Good true {5}`
holds while `Good false {4}` fails. -/

example : Drawn 3 := q728_draw (by norm_num) (by norm_num)
example : BWins 4 := q728_B_wins (by norm_num) (by norm_num)
example : AWins 5 := q728_A_wins (by norm_num) (by norm_num)
example : Drawn 6 := q728_draw (by norm_num) (by norm_num)

example : Move {3} {1, 2} := ⟨3, by simp, 1, 2, by norm_num, by norm_num, by norm_num, by decide⟩

end Q728
