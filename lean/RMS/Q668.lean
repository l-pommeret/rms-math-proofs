import Mathlib

/-!
# Q668 : the Ducci map on nonnegative real `n`-tuples

Formalization of the structural classification theorem for the Ducci map
`P(X)_i = |x_i - x_{i+1}|` acting on nonnegative real `n`-tuples, together with the
complete `n = 5` binary-cycle result.

Environment: Lean 4.28.0, Mathlib rev `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
(as pinned by `lean-toolchain` and `lake-manifest.json`).

## Modelling choices (differences between the printed statements and the formal ones)

* `ℝ₊ = [0, ∞)` is modelled not as a subtype but by carrying an explicit
  nonnegativity hypothesis `hx : ∀ i, 0 ≤ x i` on vectors `x : ZMod n → ℝ`.
* Indices are cyclic: the index type is `ZMod n`, so `x (i + 1)` is automatically
  read modulo `n`.  A `[NeZero n]` instance is assumed wherever finiteness of the
  index type (or the sup norm on `ZMod n → ℝ`) is needed.
* Vectors carry the sup norm (the `Pi` norm), which is the norm used in all
  quantitative statements below.
* `S n` is *defined* by the `h` parity conditions (2.1); the description (3.6) of
  `S n` as the image `range (dbin^[h])` is proved as the theorem
  `S_eq_range_dbin_hpart`, rather than being taken as the definition.
* `hpart n = 2 ^ (v₂ n)` and `mpart n = n / hpart n` are the `h` and `m` of the text.

## Main results

* `periodic_iff`               — Theorem 2.1 (3).
* `dbin_bijOn_S`               — Theorem 2.1 (4).
* `main_asymptotic`            — Theorem 2.1 (1) and (2) (limit `c`, periodic binary
                                 sequence `E`, and shadowing of the orbit by `c • E`).
* `tendsto_zero_iff_pow_two`   — Theorem 2.1 (5).
* `S_eq_range_dbin_hpart`      — (3.6).
* `S_five_eq`, `mem_S_five_iff` — (4.1).
* `dbin_iterate_fifteen`, `dbin_iterate_ne_of_lt_fifteen`, `S_five_orbit`
                               — Proposition 4.1 (the 15-cycle for `n = 5`).
* `asymptotic_five`            — Corollary 4.2.
* `exists_nonconstant_tendsto_zero_five` — the Section 5 example (optional extra):
  an explicit nonconstant nonnegative `5`-tuple on an eigenray `P V = p V` whose orbit
  tends to `0` but is never `0`.

## Not formalized

* The Section 6 example (an orbit that is not eventually periodic and approaches the
  15-cycle) is not formalized.
* The general basin-of-attraction problem for the cycles is left open; nothing here
  should be read as solving it.
-/

namespace Q668

open Finset Filter Topology

/-! ## Definitions -/

/-- The Ducci map on real `n`-tuples indexed by `ZMod n`. -/
def ducci {n : ℕ} (x : ZMod n → ℝ) : ZMod n → ℝ := fun i => |x i - x (i + 1)|

/-- The Ducci map on binary `n`-tuples. -/
def dbin {n : ℕ} (e : ZMod n → ZMod 2) : ZMod n → ZMod 2 := fun i => e i + e (i + 1)

/-- The real value of a bit. -/
def bval (a : ZMod 2) : ℝ := if a = 0 then 0 else 1

/-- A binary vector, viewed as a real vector. -/
def emb {n : ℕ} (e : ZMod n → ZMod 2) : ZMod n → ℝ := fun i => bval (e i)

/-- `h = 2 ^ (v₂ n)`, the largest power of two dividing `n`. -/
def hpart (n : ℕ) : ℕ := 2 ^ (n.factorization 2)

/-- The odd part `m` of `n`. -/
def mpart (n : ℕ) : ℕ := n / hpart n

/-- `S n` is the set of binary vectors satisfying the `h` parity conditions (2.1). -/
def S (n : ℕ) : Set (ZMod n → ZMod 2) :=
  {e | ∀ r : ZMod n, ∑ k ∈ Finset.range (mpart n), e (r + ((k * hpart n : ℕ) : ZMod n)) = 0}

/-! ## Elementary arithmetic facts about `hpart` and `mpart` -/

lemma hpart_pos (n : ℕ) : 0 < hpart n := Nat.ordProj_pos n 2

lemma hpart_mul_mpart (n : ℕ) : hpart n * mpart n = n :=
  Nat.ordProj_mul_ordCompl_eq_self n 2

lemma mpart_pos {n : ℕ} (hn : n ≠ 0) : 0 < mpart n := Nat.ordCompl_pos 2 hn

lemma mpart_odd {n : ℕ} (hn : n ≠ 0) : ¬ (2 ∣ mpart n) := Nat.not_dvd_ordCompl Nat.prime_two hn

lemma hpart_le {n : ℕ} (hn : n ≠ 0) : hpart n ≤ n := Nat.ordProj_le 2 hn

/-! ## The binary Ducci map -/

lemma two_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

lemma dbin_iterate_two_pow {n : ℕ} (v : ℕ) (e : ZMod n → ZMod 2) (i : ZMod n) :
    dbin^[2 ^ v] e i = e i + e (i + ((2 ^ v : ℕ) : ZMod n)) := by
  have key : ∀ a b c : ZMod 2, a + b + (b + c) = a + c := by decide
  induction v generalizing e i with
  | zero => simp [dbin]
  | succ v ih =>
      have h2 : 2 ^ (v + 1) = 2 ^ v + 2 ^ v := by ring
      rw [h2, Function.iterate_add_apply, ih, ih, ih,
        show ((2 ^ v + 2 ^ v : ℕ) : ZMod n) = ((2 ^ v : ℕ) : ZMod n) + ((2 ^ v : ℕ) : ZMod n) from by
          push_cast; ring,
        show (i + (((2 ^ v : ℕ) : ZMod n) + ((2 ^ v : ℕ) : ZMod n)))
            = i + ((2 ^ v : ℕ) : ZMod n) + ((2 ^ v : ℕ) : ZMod n) from by ring]
      exact key _ _ _

lemma dbin_iterate_hpart {n : ℕ} (e : ZMod n → ZMod 2) (i : ZMod n) :
    dbin^[hpart n] e i = e i + e (i + ((hpart n : ℕ) : ZMod n)) :=
  dbin_iterate_two_pow _ e i

lemma sum_range_telescope_two (g : ℕ → ZMod 2) (m : ℕ) :
    ∑ k ∈ Finset.range m, (g k + g (k + 1)) = g 0 + g m := by
  induction m with
  | zero => simp [two_add_self]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      generalize g 0 = a
      generalize g m = b
      generalize g (m + 1) = c
      revert a b c; decide

/-- Easy direction of (3.6) : the image of `L^h` satisfies the parity conditions. -/
lemma range_dbin_hpart_subset_S {n : ℕ} : Set.range (dbin^[hpart n]) ⊆ S n := by
  rintro e ⟨d, rfl⟩ r
  set g : ℕ → ZMod 2 := fun k => d (r + ((k * hpart n : ℕ) : ZMod n)) with hg
  have hstep : ∀ k, dbin^[hpart n] d (r + ((k * hpart n : ℕ) : ZMod n)) = g k + g (k + 1) := by
    intro k
    rw [dbin_iterate_hpart]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun k _ => hstep k), sum_range_telescope_two]
  have h0 : g 0 = d r := by simp [hg]
  have hm : g (mpart n) = d r := by
    have h : ((mpart n * hpart n : ℕ) : ZMod n) = 0 := by
      rw [Nat.mul_comm, hpart_mul_mpart]; exact ZMod.natCast_self n
    simp only [hg]
    rw [h, add_zero]
  rw [h0, hm, two_add_self]

lemma add_eq_zero_iff_eq_two : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide

/-- The explicit telescoping preimage used for the hard direction of (3.6). -/
noncomputable def dsec {n : ℕ} (e : ZMod n → ZMod 2) : ZMod n → ZMod 2 := fun i =>
  ∑ j ∈ Finset.range (i.val / hpart n), e (((i.val % hpart n + j * hpart n : ℕ)) : ZMod n)

lemma dbin_iterate_hpart_dsec {n : ℕ} [NeZero n] {e : ZMod n → ZMod 2} (he : e ∈ S n) :
    dbin^[hpart n] (dsec e) = e := by
  funext i
  rw [dbin_iterate_hpart]
  have hhpos : 0 < hpart n := hpart_pos n
  have hn : hpart n * mpart n = n := hpart_mul_mpart n
  set h := hpart n with hh
  set m := mpart n with hm
  set r := i.val % h with hr
  set k := i.val / h with hk
  have hrh : r < h := Nat.mod_lt _ hhpos
  have hik : r + k * h = i.val := by rw [hr, hk]; exact Nat.mod_add_div' _ _
  have hilt : i.val < n := ZMod.val_lt i
  have hcomm : h * k = k * h := Nat.mul_comm _ _
  have hkm : k < m := by
    by_contra hcon
    push_neg at hcon
    have : h * m ≤ h * k := Nat.mul_le_mul_left h hcon
    omega
  have hcastnat : ((i.val : ℕ) : ZMod n) = i := by simp [ZMod.natCast_val, ZMod.cast_id]
  have hcast : ((r + k * h : ℕ) : ZMod n) = i := by rw [hik]; exact hcastnat
  have hdsec_i : dsec e i = ∑ j ∈ Finset.range k, e (((r + j * h : ℕ)) : ZMod n) := rfl
  by_cases hcase : k + 1 < m
  · -- interior step of the telescoping
    have hhn : h < n := by nlinarith [hn, hhpos, hkm]
    have hsum : i.val + h < n := by nlinarith [hn, hik, hrh, hcase]
    have hval : (i + ((h : ℕ) : ZMod n)).val = i.val + h := by
      rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hhn, Nat.mod_eq_of_lt hsum]
    have hdsec_ih : dsec e (i + ((h : ℕ) : ZMod n))
        = ∑ j ∈ Finset.range (k + 1), e (((r + j * h : ℕ)) : ZMod n) := by
      show ∑ j ∈ Finset.range ((i + ((h : ℕ) : ZMod n)).val / h),
          e ((((i + ((h : ℕ) : ZMod n)).val % h + j * h : ℕ)) : ZMod n) = _
      rw [hval, Nat.add_mod_right, Nat.add_div_right _ hhpos]
    rw [hdsec_i, hdsec_ih, Finset.sum_range_succ, hcast, ← add_assoc, two_add_self, zero_add]
  · -- wrap-around step, where the parity condition is used
    have hkm' : k + 1 = m := by omega
    have hsum : i.val + h = n + r := by
      have h1 : (k + 1) * h = m * h := by rw [hkm']
      have hmh : m * h = n := by rw [Nat.mul_comm]; exact hn
      nlinarith [hik]
    have hival : i + ((h : ℕ) : ZMod n) = ((r : ℕ) : ZMod n) := by
      have e2 : i + ((h : ℕ) : ZMod n) = ((i.val + h : ℕ) : ZMod n) := by
        push_cast
        rw [hcastnat]
      rw [e2, hsum]
      push_cast
      simp
    have hval : (i + ((h : ℕ) : ZMod n)).val = r := by
      rw [hival, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hdsec_ih : dsec e (i + ((h : ℕ) : ZMod n)) = 0 := by
      show ∑ j ∈ Finset.range ((i + ((h : ℕ) : ZMod n)).val / h),
          e ((((i + ((h : ℕ) : ZMod n)).val % h + j * h : ℕ)) : ZMod n) = 0
      rw [hval, Nat.div_eq_of_lt hrh]
      simp
    rw [hdsec_i, hdsec_ih, add_zero]
    have hpar := he ((r : ℕ) : ZMod n)
    have hterms : ∀ j : ℕ,
        (((r : ℕ) : ZMod n) + ((j * h : ℕ) : ZMod n)) = ((r + j * h : ℕ) : ZMod n) := by
      intro j; push_cast; ring
    rw [Finset.sum_congr rfl (fun j _ => by rw [hterms j]), ← hm, ← hkm', Finset.sum_range_succ,
      hcast] at hpar
    exact (add_eq_zero_iff_eq_two _ _).mp hpar

/-- Hard direction of (3.6). -/
lemma S_subset_range_dbin_hpart {n : ℕ} [NeZero n] :
    S n ⊆ Set.range (dbin^[hpart n]) :=
  fun _ he => ⟨dsec _, dbin_iterate_hpart_dsec he⟩

/-- (3.6) : `S n` is exactly the image of `L^h`. -/
theorem S_eq_range_dbin_hpart {n : ℕ} [NeZero n] :
    S n = Set.range (dbin^[hpart n]) :=
  Set.Subset.antisymm S_subset_range_dbin_hpart range_dbin_hpart_subset_S

lemma zero_mem_S (n : ℕ) : (0 : ZMod n → ZMod 2) ∈ S n := by
  intro r; simp

lemma add_mem_S {n : ℕ} {e f : ZMod n → ZMod 2} (he : e ∈ S n) (hf : f ∈ S n) :
    e + f ∈ S n := by
  intro r
  have : ∀ k : ℕ, (e + f) (r + ((k * hpart n : ℕ) : ZMod n))
      = e (r + ((k * hpart n : ℕ) : ZMod n)) + f (r + ((k * hpart n : ℕ) : ZMod n)) := fun _ => rfl
  rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_add_distrib, he r, hf r, add_zero]

lemma dbin_mem_S {n : ℕ} {e : ZMod n → ZMod 2} (he : e ∈ S n) : dbin e ∈ S n := by
  intro r
  have hs : ∀ k : ℕ, dbin e (r + ((k * hpart n : ℕ) : ZMod n))
      = e (r + ((k * hpart n : ℕ) : ZMod n)) + e ((r + 1) + ((k * hpart n : ℕ) : ZMod n)) := by
    intro k
    show e _ + e _ = _
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun k _ => hs k), Finset.sum_add_distrib, he r, he (r + 1), add_zero]

/-- The all-ones vector is not in `S n`, since `m` is odd. -/
lemma one_not_mem_S {n : ℕ} (hn : n ≠ 0) : (fun _ => (1 : ZMod 2)) ∉ S n := by
  intro h
  have h0 := h 0
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  exact mpart_odd hn h0

lemma dbin_eq_iff_const {n : ℕ} [NeZero n] {e : ZMod n → ZMod 2} (he : dbin e = 0) :
    e = 0 ∨ e = (fun _ => 1) := by
  have hstep : ∀ i : ZMod n, e (i + 1) = e i := by
    intro i
    have : e i + e (i + 1) = 0 := congrFun he i
    revert this
    generalize e i = a
    generalize e (i + 1) = b
    revert a b; decide
  have hcast : ∀ k : ℕ, e ((k : ZMod n)) = e 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, hstep, ih]
  have hall : ∀ i : ZMod n, e i = e 0 := by
    intro i
    have := hcast i.val
    rwa [ZMod.natCast_val, ZMod.cast_id] at this
  have hbit : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hbit (e 0) with h0 | h0
  · left; funext i; rw [hall i, h0]; rfl
  · right; funext i; rw [hall i, h0]

/-- `L` is injective on `S n`. -/
lemma dbin_injOn_S {n : ℕ} [NeZero n] : Set.InjOn dbin (S n) := by
  intro e he f hf hef
  have hsum : dbin (e + f) = 0 := by
    funext i
    have h1 : dbin (e + f) i = dbin e i + dbin f i := by
      show (e + f) i + (e + f) (i + 1) = _
      show e i + f i + (e (i + 1) + f (i + 1)) = e i + e (i + 1) + (f i + f (i + 1))
      ring
    rw [h1, hef]
    exact two_add_self _
  rcases dbin_eq_iff_const hsum with h | h
  · funext i
    have : e i + f i = 0 := congrFun h i
    revert this
    generalize e i = a
    generalize f i = b
    revert a b; decide
  · exact absurd (h ▸ add_mem_S he hf) (one_not_mem_S (NeZero.ne n))

/-- Part 4 of Theorem 2.1 : `L` permutes the finite set `S n`. -/
theorem dbin_bijOn_S {n : ℕ} [NeZero n] : Set.BijOn dbin (S n) (S n) :=
  (Set.Finite.injOn_iff_bijOn_of_mapsTo (Set.toFinite _) (fun _ he => dbin_mem_S he)).mp
    dbin_injOn_S

/-- Every element of `S n` is periodic for `L`. -/
lemma dbin_iterate_mem_S {n : ℕ} {e : ZMod n → ZMod 2} (he : e ∈ S n) (k : ℕ) :
    dbin^[k] e ∈ S n := by
  induction k with
  | zero => simpa using he
  | succ k ih => rw [Function.iterate_succ_apply']; exact dbin_mem_S ih

lemma dbin_iterate_injOn_S {n : ℕ} [NeZero n] (k : ℕ) : Set.InjOn (dbin^[k]) (S n) := by
  induction k with
  | zero => intro e _ f _ h; simpa using h
  | succ k ih =>
      intro e he f hf h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
      exact dbin_injOn_S he hf (ih (dbin_mem_S he) (dbin_mem_S hf) h)

lemma exists_period_of_mem_S {n : ℕ} [NeZero n] {e : ZMod n → ZMod 2} (he : e ∈ S n) :
    ∃ r > 0, dbin^[r] e = e := by
  obtain ⟨a, b, hne, hab⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => dbin^[k] e)
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨b - a, by omega, ?_⟩
    apply dbin_iterate_injOn_S a (dbin_iterate_mem_S he _) he
    rw [← Function.iterate_add_apply]
    rw [show a + (b - a) = b by omega]
    exact hab.symm
  · refine ⟨a - b, by omega, ?_⟩
    apply dbin_iterate_injOn_S b (dbin_iterate_mem_S he _) he
    rw [← Function.iterate_add_apply]
    rw [show b + (a - b) = a by omega]
    exact hab

lemma mem_S_of_periodic {n : ℕ} [NeZero n] {e : ZMod n → ZMod 2} {r : ℕ} (hr : 0 < r)
    (h : dbin^[r] e = e) : e ∈ S n := by
  have hh : 0 < hpart n := hpart_pos n
  have hfix : dbin^[r * hpart n] e = e := by
    rw [Function.iterate_mul]
    have : ∀ k : ℕ, (dbin^[r])^[k] e = e := by
      intro k; induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', ih, h]
    exact this _
  refine range_dbin_hpart_subset_S ⟨dbin^[r * hpart n - hpart n] e, ?_⟩
  rw [← Function.iterate_add_apply]
  rw [show hpart n + (r * hpart n - hpart n) = r * hpart n by
    have : hpart n ≤ r * hpart n := Nat.le_mul_of_pos_left _ hr
    omega]
  exact hfix

/-- If `n` is not a power of two there is a nonzero element of `S n`. -/
lemma exists_ne_zero_mem_S {n : ℕ} [NeZero n] (hpow : ¬ ∃ v, n = 2 ^ v) :
    ∃ e ∈ S n, e ≠ 0 := by
  have hn : n ≠ 0 := NeZero.ne n
  have hlt : hpart n < n := lt_of_le_of_ne (hpart_le hn) (by
    intro hEq
    exact hpow ⟨n.factorization 2, hEq.symm⟩)
  set d : ZMod n → ZMod 2 := fun i => if i = 0 then 1 else 0 with hd
  have hne : ((hpart n : ℕ) : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact absurd (Nat.le_of_dvd (hpart_pos n) hdvd) (by omega)
  have hval : dbin^[hpart n] d 0 = 1 := by
    rw [dbin_iterate_hpart]
    simp [hd, hne]
  refine ⟨dbin^[hpart n] d, range_dbin_hpart_subset_S ⟨d, rfl⟩, ?_⟩
  intro hzero
  rw [hzero] at hval
  simp at hval

/-- Part 5, binary half : `S n = {0}` exactly when `n` is a power of two. -/
theorem S_eq_zero_iff {n : ℕ} [NeZero n] :
    S n = {0} ↔ ∃ v, n = 2 ^ v := by
  constructor
  · intro hS
    by_contra hpow
    obtain ⟨e, heS, hne⟩ := exists_ne_zero_mem_S hpow
    rw [hS] at heS
    exact hne heS
  · rintro ⟨v, rfl⟩
    have hh : hpart (2 ^ v) = 2 ^ v := by
      simp [hpart, Nat.Prime.factorization_pow Nat.prime_two]
    have hm : mpart (2 ^ v) = 1 := by
      rw [mpart, hh, Nat.div_self (Nat.two_pow_pos v)]
    ext e
    simp only [Set.mem_singleton_iff]
    constructor
    · intro he
      funext r
      have := he r
      rw [hm] at this
      simpa using this
    · rintro rfl
      exact zero_mem_S _

/-! ## Real sequences : the strict decrease lemma (Lemma 3.1, Corollary 3.2) -/

/-- The absolute difference operator on sequences indexed by `ℕ`. -/
def sdiff (u : ℕ → ℝ) : ℕ → ℝ := fun i => |u i - u (i + 1)|

lemma sdiff_mem_Icc {M : ℝ} {u : ℕ → ℝ} (hu : ∀ j, u j ∈ Set.Icc (0 : ℝ) M) (j : ℕ) :
    sdiff u j ∈ Set.Icc (0 : ℝ) M := by
  obtain ⟨h1, h2⟩ := hu j
  obtain ⟨h3, h4⟩ := hu (j + 1)
  refine ⟨abs_nonneg _, ?_⟩
  show |u j - u (j + 1)| ≤ M
  rw [abs_le]
  constructor <;> linarith

lemma sdiff_iterate_mem_Icc {M : ℝ} : ∀ (k : ℕ) {u : ℕ → ℝ},
    (∀ j, u j ∈ Set.Icc (0 : ℝ) M) → ∀ j, sdiff^[k] u j ∈ Set.Icc (0 : ℝ) M := by
  intro k
  induction k with
  | zero => intro u hu j; simpa using hu j
  | succ k ih => intro u hu j; rw [Function.iterate_succ_apply]; exact ih (sdiff_mem_Icc hu) j

private lemma abs_cases4 {M a b t : ℝ} (ha : a = 0 ∨ a = M) (hb : b = t ∨ b = M - t)
    (ht : 0 ≤ t) (htM : t ≤ M) : |a - b| = t ∨ |a - b| = M - t := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · left; rw [zero_sub, abs_neg, abs_of_nonneg ht]
  · right; rw [zero_sub, abs_neg, abs_of_nonneg (by linarith)]
  · right; rw [abs_of_nonneg (by linarith)]
  · left; rw [show a - (a - t) = t by ring, abs_of_nonneg ht]

/-- Endpoint fact (3.2), right-hand version. -/
lemma sdiff_binary_right {M : ℝ} {u : ℕ → ℝ} (hu : ∀ j, u j ∈ Set.Icc (0 : ℝ) M) :
    ∀ (k i : ℕ), (∀ j, i ≤ j → j < i + k → u j = 0 ∨ u j = M) →
      sdiff^[k] u i = u (i + k) ∨ sdiff^[k] u i = M - u (i + k) := by
  intro k
  induction k with
  | zero => intro i _; left; simp
  | succ k ih =>
      intro i hb
      have hA : sdiff^[k] u i = 0 ∨ sdiff^[k] u i = M := by
        rcases ih i (fun j h1 h2 => hb j h1 (by omega)) with h | h <;>
          rcases hb (i + k) (by omega) (by omega) with h' | h'
        · left; rw [h, h']
        · right; rw [h, h']
        · right; rw [h, h']; ring
        · left; rw [h, h']; ring
      have hB := ih (i + 1) (fun j h1 h2 => hb j (by omega) (by omega))
      rw [Function.iterate_succ_apply']
      have hi : i + (k + 1) = i + 1 + k := by omega
      rw [hi]
      obtain ⟨ht, htM⟩ := hu (i + 1 + k)
      exact abs_cases4 hA hB ht htM

/-- Endpoint fact (3.2), left-hand version. -/
lemma sdiff_binary_left {M : ℝ} {u : ℕ → ℝ} (hu : ∀ j, u j ∈ Set.Icc (0 : ℝ) M) :
    ∀ (k i : ℕ), (∀ j, i < j → j ≤ i + k → u j = 0 ∨ u j = M) →
      sdiff^[k] u i = u i ∨ sdiff^[k] u i = M - u i := by
  intro k
  induction k with
  | zero => intro i _; left; simp
  | succ k ih =>
      intro i hb
      have hA := ih i (fun j h1 h2 => hb j h1 (by omega))
      have hB : sdiff^[k] u (i + 1) = 0 ∨ sdiff^[k] u (i + 1) = M := by
        rcases ih (i + 1) (fun j h1 h2 => hb j (by omega) (by omega)) with h | h <;>
          rcases hb (i + 1) (by omega) (by omega) with h' | h'
        · left; rw [h, h']
        · right; rw [h, h']
        · right; rw [h, h']; ring
        · left; rw [h, h']; ring
      rw [Function.iterate_succ_apply']
      show |sdiff^[k] u i - sdiff^[k] u (i + 1)| = u i ∨ |sdiff^[k] u i - sdiff^[k] u (i + 1)| = M - u i
      rw [abs_sub_comm]
      obtain ⟨ht, htM⟩ := hu i
      exact abs_cases4 hB hA ht htM

/-- Lemma 3.1 : an iterated absolute difference can only attain the maximum `M`
if all the entries involved are extremal. -/
lemma sdiff_eq_max_imp {M : ℝ} {u : ℕ → ℝ} (hu : ∀ j, u j ∈ Set.Icc (0 : ℝ) M) :
    ∀ (k i : ℕ), sdiff^[k] u i = M → ∀ j, i ≤ j → j ≤ i + k → u j = 0 ∨ u j = M := by
  intro k
  induction k with
  | zero =>
      intro i h j h1 h2
      have : j = i := by omega
      subst this
      right; simpa using h
  | succ k ih =>
      intro i h
      rw [Function.iterate_succ_apply'] at h
      have hAmem := sdiff_iterate_mem_Icc k hu i
      have hBmem := sdiff_iterate_mem_Icc k hu (i + 1)
      have hcase : (sdiff^[k] u i = M ∧ sdiff^[k] u (i + 1) = 0) ∨
          (sdiff^[k] u i = 0 ∧ sdiff^[k] u (i + 1) = M) := by
        have h' : |sdiff^[k] u i - sdiff^[k] u (i + 1)| = M := h
        obtain ⟨a1, a2⟩ := hAmem
        obtain ⟨b1, b2⟩ := hBmem
        rcases abs_cases (sdiff^[k] u i - sdiff^[k] u (i + 1)) with ⟨he, _⟩ | ⟨he, _⟩
        · left; rw [he] at h'; constructor <;> linarith
        · right; rw [he] at h'; constructor <;> linarith
      rcases hcase with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · have hIH := ih i hA
        intro j h1 h2
        rcases Nat.lt_or_ge j (i + k + 1) with hj | hj
        · exact hIH j h1 (by omega)
        · have hj' : j = i + 1 + k := by omega
          subst hj'
          have := sdiff_binary_right hu k (i + 1) (fun j h1 h2 => hIH j (by omega) (by omega))
          rcases this with h' | h'
          · left; rw [← h', hB]
          · right
            have hx : M - u (i + 1 + k) = 0 := by rw [← h', hB]
            linarith
      · have hIH := ih (i + 1) hB
        intro j h1 h2
        rcases Nat.eq_or_lt_of_le h1 with hj | hj
        · subst hj
          have hbl := sdiff_binary_left hu k i (fun j' h1' h2' => hIH j' (by omega) (by omega))
          rcases hbl with h' | h'
          · left; rw [← h', hA]
          · right
            have hx : M - u i = 0 := by rw [← h', hA]
            linarith
        · exact hIH j (by omega) (by omega)

/-! ## Basic properties of the real Ducci map -/

lemma ducci_nonneg {n : ℕ} (x : ZMod n → ℝ) (i : ZMod n) : 0 ≤ ducci x i := abs_nonneg _

lemma ducci_mem_Icc {n : ℕ} {M : ℝ} {x : ZMod n → ℝ} (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) M)
    (i : ZMod n) : ducci x i ∈ Set.Icc (0 : ℝ) M := by
  obtain ⟨h1, h2⟩ := hx i
  obtain ⟨h3, h4⟩ := hx (i + 1)
  refine ⟨abs_nonneg _, ?_⟩
  show |x i - x (i + 1)| ≤ M
  rw [abs_le]
  constructor <;> linarith

lemma ducci_iterate_mem_Icc {n : ℕ} {M : ℝ} {x : ZMod n → ℝ} (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) M) :
    ∀ (k : ℕ) (i : ZMod n), ducci^[k] x i ∈ Set.Icc (0 : ℝ) M := by
  intro k
  induction k generalizing x with
  | zero => simpa using hx
  | succ k ih => intro i; rw [Function.iterate_succ_apply]; exact ih (ducci_mem_Icc hx) i

lemma ducci_iterate_nonneg {n : ℕ} {x : ZMod n → ℝ} (hx : ∀ i, 0 ≤ x i) (k : ℕ) (i : ZMod n) :
    0 ≤ ducci^[k] x i := by
  induction k generalizing x with
  | zero => simpa using hx i
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (fun j => ducci_nonneg x j)

lemma norm_ducci_le {n : ℕ} [NeZero n] {x : ZMod n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    ‖ducci x‖ ≤ ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro i
  have h1 : x i ≤ ‖x‖ := le_trans (le_abs_self _) (by simpa using norm_le_pi_norm x i)
  have h2 : x (i + 1) ≤ ‖x‖ := le_trans (le_abs_self _) (by simpa using norm_le_pi_norm x (i + 1))
  have h3 := hx i
  have h4 := hx (i + 1)
  rw [Real.norm_eq_abs, abs_of_nonneg (ducci_nonneg x i)]
  show |x i - x (i + 1)| ≤ ‖x‖
  rw [abs_le]
  constructor <;> linarith

/-- The orbit of a nonnegative vector has nonincreasing sup norm (Section 3.1). -/
lemma antitone_norm_iterate {n : ℕ} [NeZero n] {x : ZMod n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    Antitone (fun q => ‖ducci^[q] x‖) := by
  apply antitone_nat_of_succ_le
  intro q
  rw [Function.iterate_succ_apply']
  exact norm_ducci_le (fun i => ducci_iterate_nonneg hx q i)

/-- Periodizing a vector : the `ℕ`-indexed and `ZMod n`-indexed difference operators agree. -/
lemma sdiff_iterate_eq {n : ℕ} : ∀ (k : ℕ) (x : ZMod n → ℝ) (i : ℕ),
    sdiff^[k] (fun j : ℕ => x (j : ZMod n)) i = ducci^[k] x (i : ZMod n) := by
  intro k
  induction k with
  | zero => intro x i; simp
  | succ k ih =>
      intro x i
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      have : sdiff (fun j : ℕ => x (j : ZMod n)) = fun j : ℕ => ducci x (j : ZMod n) := by
        funext j
        show |x (j : ZMod n) - x ((j + 1 : ℕ) : ZMod n)| = |x (j : ZMod n) - x ((j : ZMod n) + 1)|
        push_cast
        ring_nf
      rw [this, ih]

/-- Corollary 3.2 : if some coordinate is strictly between `0` and `M`, then after `n-1`
iterations the sup norm has dropped below `M`. -/
theorem norm_iterate_pred_lt {n : ℕ} [NeZero n] {M : ℝ} {x : ZMod n → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) M) {i₀ : ZMod n} (h1 : x i₀ ≠ 0) (h2 : x i₀ ≠ M) :
    ‖ducci^[n - 1] x‖ < M := by
  have hM : 0 < M := lt_of_lt_of_le (lt_of_le_of_ne (hx i₀).1 (Ne.symm h1)) (hx i₀).2
  rw [pi_norm_lt_iff hM]
  intro i
  have hmem := ducci_iterate_mem_Icc hx (n - 1) i
  rw [Real.norm_eq_abs, abs_of_nonneg hmem.1]
  rcases lt_or_eq_of_le hmem.2 with h | heq
  · exact h
  exfalso
  set u : ℕ → ℝ := fun j : ℕ => x ((j : ZMod n)) with hu_def
  have hu : ∀ j, u j ∈ Set.Icc (0 : ℝ) M := fun j => hx _
  have hmax : sdiff^[n - 1] u i.val = M := by
    rw [hu_def, sdiff_iterate_eq]
    rw [ZMod.natCast_val, ZMod.cast_id]
    exact heq
  have hall := sdiff_eq_max_imp hu (n - 1) i.val hmax
  obtain ⟨j, hj1, hj2, hj3⟩ : ∃ j, i.val ≤ j ∧ j ≤ i.val + (n - 1) ∧ (j : ZMod n) = i₀ := by
    refine ⟨i.val + (i₀ - i).val, by omega, ?_, ?_⟩
    · have : (i₀ - i).val < n := ZMod.val_lt _
      omega
    · push_cast
      rw [ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_val, ZMod.cast_id]
      ring
  have := hall j hj1 hj2
  rw [hu_def] at this
  simp only [hj3] at this
  rcases this with h | h
  · exact h1 h
  · exact h2 h

/-! ## Binary vectors inside the reals -/

lemma bit_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

lemma bval_cases (a : ZMod 2) : bval a = 0 ∨ bval a = 1 := by
  rcases bit_cases a with rfl | rfl
  · left; rfl
  · right; rfl

lemma bval_nonneg (a : ZMod 2) : 0 ≤ bval a := by
  rcases bval_cases a with h | h <;> simp [h]

lemma bval_le_one (a : ZMod 2) : bval a ≤ 1 := by
  rcases bval_cases a with h | h <;> simp [h]

lemma bval_zero : bval 0 = 0 := rfl

lemma bval_one : bval 1 = 1 := by norm_num [bval]

lemma abs_bval_sub (a b : ZMod 2) : |bval a - bval b| = bval (a + b) := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl
  · rw [show (0 : ZMod 2) + 0 = 0 from rfl, bval_zero]; norm_num
  · rw [show (0 : ZMod 2) + 1 = 1 from rfl, bval_zero, bval_one]; norm_num
  · rw [show (1 : ZMod 2) + 0 = 1 from rfl, bval_zero, bval_one]; norm_num
  · rw [show (1 : ZMod 2) + 1 = 0 from by decide, bval_zero, bval_one]; norm_num

lemma bval_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : bval a = 1 := by
  simp [bval, ha]

lemma bval_injective : Function.Injective bval := by
  intro a b hab
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl
  · rfl
  · rw [bval_zero, bval_one] at hab; norm_num at hab
  · rw [bval_zero, bval_one] at hab; norm_num at hab
  · rfl

lemma emb_injective {n : ℕ} : Function.Injective (emb (n := n)) := by
  intro e f hef
  funext i
  exact bval_injective (congrFun hef i)

lemma emb_nonneg {n : ℕ} (e : ZMod n → ZMod 2) (i : ZMod n) : 0 ≤ emb e i := bval_nonneg _

lemma smul_emb_nonneg {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (e : ZMod n → ZMod 2) (i : ZMod n) :
    0 ≤ (c • emb e) i := mul_nonneg hc (bval_nonneg _)

/-- Positive homogeneity : the Ducci map on scaled binary vectors is the binary Ducci map. -/
lemma ducci_smul_emb {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (e : ZMod n → ZMod 2) :
    ducci (c • emb e) = c • emb (dbin e) := by
  funext i
  show |c * bval (e i) - c * bval (e (i + 1))| = c * bval (e i + e (i + 1))
  rw [← mul_sub, abs_mul, abs_of_nonneg hc, abs_bval_sub]

lemma ducci_iterate_smul_emb {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (e : ZMod n → ZMod 2) (k : ℕ) :
    ducci^[k] (c • emb e) = c • emb (dbin^[k] e) := by
  induction k generalizing e with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ducci_smul_emb hc, ih]

lemma norm_smul_emb_le {n : ℕ} [NeZero n] {c : ℝ} (hc : 0 ≤ c) (e : ZMod n → ZMod 2) :
    ‖c • emb e‖ ≤ c := by
  rw [pi_norm_le_iff_of_nonneg hc]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (smul_emb_nonneg hc e i)]
  show c * bval (e i) ≤ c
  nlinarith [bval_le_one (e i), bval_nonneg (e i)]

lemma norm_smul_emb_of_ne_zero {n : ℕ} [NeZero n] {c : ℝ} (hc : 0 ≤ c) {e : ZMod n → ZMod 2}
    (he : e ≠ 0) : ‖c • emb e‖ = c := by
  refine le_antisymm (norm_smul_emb_le hc e) ?_
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact he (funext hcon)
  have h1 : e i = 1 := (bit_cases (e i)).resolve_left hi
  have : ‖(c • emb e) i‖ ≤ ‖c • emb e‖ := norm_le_pi_norm _ i
  rw [Real.norm_eq_abs, abs_of_nonneg (smul_emb_nonneg hc e i)] at this
  have hval : (c • emb e) i = c := by
    show c * bval (e i) = c
    rw [h1]
    norm_num [bval]
  rwa [hval] at this

/-- Distinct scaled binary vectors are `c`-separated in sup norm. -/
lemma norm_smul_emb_sub {n : ℕ} [NeZero n] {c : ℝ} (hc : 0 ≤ c) {e f : ZMod n → ZMod 2}
    (hef : e ≠ f) : c ≤ ‖c • emb e - c • emb f‖ := by
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ f i := by
    by_contra hcon
    push_neg at hcon
    exact hef (funext hcon)
  have h := norm_le_pi_norm (c • emb e - c • emb f) i
  have hval : |(c • emb e - c • emb f) i| = c := by
    show |c * bval (e i) - c * bval (f i)| = c
    rw [← mul_sub, abs_mul, abs_of_nonneg hc, abs_bval_sub]
    have hne : e i + f i ≠ 0 := by
      revert hi
      generalize e i = a
      generalize f i = b
      revert a b
      decide
    rw [bval_eq_one_of_ne_zero hne, mul_one]
  rw [Real.norm_eq_abs, hval] at h
  exact h

/-! ## Classification of the periodic points (Theorem 2.1 (3)) -/

/-- The real periodic points of the Ducci map in `ℝ₊^n` are exactly the vectors `c • ε`
with `c ≥ 0` and `ε ∈ S n`. -/
theorem periodic_iff {n : ℕ} [NeZero n] {x : ZMod n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    (∃ r > 0, ducci^[r] x = x) ↔ ∃ c ≥ (0 : ℝ), ∃ e ∈ S n, x = c • emb e := by
  constructor
  · rintro ⟨r, hr, hper⟩
    set M := ‖x‖ with hM
    have hMnn : 0 ≤ M := norm_nonneg _
    have hiter : ∀ k : ℕ, ducci^[k * r] x = x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [show (k + 1) * r = k * r + r by ring, Function.iterate_add_apply, hper, ih]
    have hconst : ∀ q : ℕ, ‖ducci^[q] x‖ = M := by
      intro q
      refine le_antisymm ?_ ?_
      · simpa using antitone_norm_iterate hx (Nat.zero_le q)
      · have hq : q ≤ q * r := Nat.le_mul_of_pos_right _ hr
        have := antitone_norm_iterate hx hq
        simp only [hiter q] at this
        exact this
    have hmemIcc : ∀ i, x i ∈ Set.Icc (0 : ℝ) M := by
      intro i
      refine ⟨hx i, ?_⟩
      have := norm_le_pi_norm x i
      rw [Real.norm_eq_abs, abs_of_nonneg (hx i)] at this
      exact this
    have hbinary : ∀ i, x i = 0 ∨ x i = M := by
      intro i
      by_contra hcon
      push_neg at hcon
      have := norm_iterate_pred_lt hmemIcc hcon.1 hcon.2
      rw [hconst (n - 1)] at this
      exact lt_irrefl _ this
    set e : ZMod n → ZMod 2 := fun i => if x i = 0 then 0 else 1 with he_def
    have hxe : x = M • emb e := by
      funext i
      show x i = M * bval (e i)
      rcases hbinary i with h | h
      · rw [h]
        simp [he_def, bval, h]
      · by_cases hzero : x i = 0
        · rw [hzero]
          simp [he_def, bval, hzero]
        · rw [h]
          simp [he_def, bval, hzero]
    rcases eq_or_lt_of_le hMnn with hM0 | hMpos
    · exact ⟨0, le_refl _, 0, zero_mem_S n, by
        rw [hxe, ← hM0]
        funext i
        simp⟩
    · refine ⟨M, hMnn, e, ?_, hxe⟩
      refine mem_S_of_periodic hr ?_
      have h1 : ducci^[r] (M • emb e) = M • emb (dbin^[r] e) := ducci_iterate_smul_emb hMnn e r
      rw [← hxe, hper] at h1
      have h2 : M • emb (dbin^[r] e) = M • emb e := by rw [← h1]; exact hxe
      have hMne : M ≠ 0 := ne_of_gt hMpos
      apply emb_injective
      funext i
      have h3 : M * emb (dbin^[r] e) i = M * emb e i := congrFun h2 i
      exact mul_left_cancel₀ hMne h3
  · rintro ⟨c, hc, e, he, rfl⟩
    obtain ⟨r, hr, hper⟩ := exists_period_of_mem_S he
    exact ⟨r, hr, by rw [ducci_iterate_smul_emb hc e r, hper]⟩

/-! ## Limit points of an orbit (Sections 3.3, 3.5) -/

lemma exists_smul_emb_of_binary {n : ℕ} {M : ℝ} {y : ZMod n → ℝ}
    (hy : ∀ i, y i = 0 ∨ y i = M) : ∃ e : ZMod n → ZMod 2, y = M • emb e := by
  refine ⟨fun i => if y i = 0 then 0 else 1, ?_⟩
  funext i
  show y i = M * bval (if y i = 0 then 0 else 1)
  by_cases h : y i = 0
  · rw [h]; simp [bval_zero]
  · rw [if_neg h, bval_one, mul_one]
    exact (hy i).resolve_left h

lemma continuous_ducci {n : ℕ} : Continuous (ducci : (ZMod n → ℝ) → ZMod n → ℝ) := by
  apply continuous_pi
  intro i
  exact ((continuous_apply i).sub (continuous_apply (i + 1))).abs

lemma continuous_ducci_iterate {n : ℕ} (k : ℕ) :
    Continuous ((ducci : (ZMod n → ℝ) → ZMod n → ℝ)^[k]) := by
  induction k with
  | zero => simpa using continuous_id
  | succ k ih => rw [Function.iterate_succ]; exact ih.comp continuous_ducci

/-- The limiting sup norm `c(X)` exists (Theorem 2.1 (1)). -/
theorem exists_tendsto_norm_iterate {n : ℕ} [NeZero n] {x : ZMod n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    ∃ c : ℝ, 0 ≤ c ∧ Filter.Tendsto (fun q => ‖ducci^[q] x‖) Filter.atTop (nhds c) ∧
      ∀ q, c ≤ ‖ducci^[q] x‖ := by
  have hanti := antitone_norm_iterate hx
  have hbdd : BddBelow (Set.range fun q => ‖ducci^[q] x‖) := ⟨0, by
    rintro y ⟨q, rfl⟩; exact norm_nonneg _⟩
  refine ⟨⨅ q, ‖ducci^[q] x‖, le_ciInf fun q => norm_nonneg _, tendsto_atTop_ciInf hanti hbdd,
    fun q => ciInf_le hbdd q⟩

/-- `Y` is a limit point of the orbit of `x`. -/
def IsOrbitLimit {n : ℕ} (x Y : ZMod n → ℝ) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (fun j => ducci^[φ j] x) Filter.atTop (nhds Y)

lemma exists_orbitLimit {n : ℕ} [NeZero n] {x : ZMod n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    ∃ Y, IsOrbitLimit x Y := by
  have hb : ∀ q : ℕ, ducci^[q] x ∈ Metric.closedBall (0 : ZMod n → ℝ) ‖x‖ := by
    intro q
    simp only [Metric.mem_closedBall, dist_zero_right]
    simpa using antitone_norm_iterate hx (Nat.zero_le q)
  obtain ⟨Y, -, φ, hφ, hconv⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hb
  exact ⟨Y, φ, hφ, hconv⟩

lemma IsOrbitLimit.norm_eq {n : ℕ} [NeZero n] {x Y : ZMod n → ℝ} {c : ℝ}
    (hc : Filter.Tendsto (fun q => ‖ducci^[q] x‖) Filter.atTop (nhds c)) (hY : IsOrbitLimit x Y) :
    ‖Y‖ = c := by
  obtain ⟨φ, hφ, hconv⟩ := hY
  have h1 : Filter.Tendsto (fun j => ‖ducci^[φ j] x‖) Filter.atTop (nhds ‖Y‖) :=
    (continuous_norm.tendsto Y).comp hconv
  have h2 : Filter.Tendsto (fun j => ‖ducci^[φ j] x‖) Filter.atTop (nhds c) :=
    hc.comp hφ.tendsto_atTop
  exact tendsto_nhds_unique h1 h2

lemma IsOrbitLimit.nonneg {n : ℕ} {x Y : ZMod n → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hY : IsOrbitLimit x Y) (i : ZMod n) : 0 ≤ Y i := by
  obtain ⟨φ, hφ, hconv⟩ := hY
  have := (tendsto_pi_nhds.mp hconv) i
  exact ge_of_tendsto' this (fun j => ducci_iterate_nonneg hx _ i)

/-- Every limit point of an orbit is binary up to the scale `c` (Section 3.3). -/
lemma IsOrbitLimit.binary {n : ℕ} [NeZero n] {x Y : ZMod n → ℝ} {c : ℝ} (hx : ∀ i, 0 ≤ x i)
    (hc : Filter.Tendsto (fun q => ‖ducci^[q] x‖) Filter.atTop (nhds c))
    (hlow : ∀ q, c ≤ ‖ducci^[q] x‖) (hY : IsOrbitLimit x Y) (i : ZMod n) :
    Y i = 0 ∨ Y i = c := by
  by_contra hcon
  push_neg at hcon
  have hnorm : ‖Y‖ = c := hY.norm_eq hc
  have hmem : ∀ j, Y j ∈ Set.Icc (0 : ℝ) c := by
    intro j
    refine ⟨hY.nonneg hx j, ?_⟩
    have := norm_le_pi_norm Y j
    rw [Real.norm_eq_abs, abs_of_nonneg (hY.nonneg hx j), hnorm] at this
    exact this
  have hdrop : ‖ducci^[n - 1] Y‖ < c := norm_iterate_pred_lt hmem hcon.1 hcon.2
  obtain ⟨φ, hφ, hconv⟩ := hY
  have h1 : Filter.Tendsto (fun j => ‖ducci^[n - 1] (ducci^[φ j] x)‖) Filter.atTop
      (nhds ‖ducci^[n - 1] Y‖) :=
    (continuous_norm.tendsto _).comp (((continuous_ducci_iterate (n - 1)).tendsto Y).comp hconv)
  have h2 : ∀ j, c ≤ ‖ducci^[n - 1] (ducci^[φ j] x)‖ := by
    intro j
    rw [← Function.iterate_add_apply]
    exact hlow _
  have := ge_of_tendsto' h1 (fun j => h2 j)
  exact absurd hdrop (not_lt.mpr this)

/-- The set of limit points is invariant under taking preimages along the orbit (3.7). -/
lemma IsOrbitLimit.exists_preimage {n : ℕ} [NeZero n] {x Y : ZMod n → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hY : IsOrbitLimit x Y) (k : ℕ) : ∃ Z, IsOrbitLimit x Z ∧ ducci^[k] Z = Y := by
  obtain ⟨φ, hφ, hconv⟩ := hY
  set ψ : ℕ → ℕ := fun j => φ (j + k) - k with hψ_def
  have hge : ∀ j, k ≤ φ (j + k) := fun j => le_trans (by omega) (hφ.le_apply)
  have hψ : StrictMono ψ := by
    intro a b hab
    have h1 : φ (a + k) < φ (b + k) := hφ (by omega)
    have := hge a
    have := hge b
    simp only [hψ_def]
    omega
  have hb : ∀ j : ℕ, ducci^[ψ j] x ∈ Metric.closedBall (0 : ZMod n → ℝ) ‖x‖ := by
    intro j
    simp only [Metric.mem_closedBall, dist_zero_right]
    simpa using antitone_norm_iterate hx (Nat.zero_le (ψ j))
  obtain ⟨Z, -, θ, hθ, hZ⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hb
  refine ⟨Z, ⟨fun j => ψ (θ j), hψ.comp hθ, hZ⟩, ?_⟩
  have h1 : Filter.Tendsto (fun j => ducci^[k] (ducci^[ψ (θ j)] x)) Filter.atTop
      (nhds (ducci^[k] Z)) :=
    ((continuous_ducci_iterate k).tendsto Z).comp hZ
  have h2 : ∀ j, ducci^[k] (ducci^[ψ (θ j)] x) = ducci^[φ (θ j + k)] x := by
    intro j
    rw [← Function.iterate_add_apply]
    congr 1
    have := hge (θ j)
    simp only [hψ_def]
    omega
  have h3 : Filter.Tendsto (fun j => ducci^[φ (θ j + k)] x) Filter.atTop (nhds Y) := by
    have hmono : StrictMono (fun j => θ j + k) := fun a b hab => by
      show θ a + k < θ b + k
      have := hθ hab; omega
    exact hconv.comp hmono.tendsto_atTop
  have h1' : Filter.Tendsto (fun j => ducci^[φ (θ j + k)] x) Filter.atTop (nhds (ducci^[k] Z)) := by
    simpa only [h2] using h1
  exact tendsto_nhds_unique h1' h3

/-- Every limit point of an orbit with positive limiting scale is `c` times an element of
`S n` (3.8). -/
lemma IsOrbitLimit.mem_scaled_S {n : ℕ} [NeZero n] {x Y : ZMod n → ℝ} {c : ℝ}
    (hx : ∀ i, 0 ≤ x i) (hcpos : 0 < c)
    (hc : Filter.Tendsto (fun q => ‖ducci^[q] x‖) Filter.atTop (nhds c))
    (hlow : ∀ q, c ≤ ‖ducci^[q] x‖) (hY : IsOrbitLimit x Y) :
    ∃ e ∈ S n, Y = c • emb e := by
  obtain ⟨e, he⟩ := exists_smul_emb_of_binary (hY.binary hx hc hlow)
  obtain ⟨Z, hZ, hZY⟩ := hY.exists_preimage hx (hpart n)
  obtain ⟨d, hd⟩ := exists_smul_emb_of_binary (hZ.binary hx hc hlow)
  refine ⟨e, ?_, he⟩
  have h1 : ducci^[hpart n] (c • emb d) = c • emb (dbin^[hpart n] d) :=
    ducci_iterate_smul_emb (le_of_lt hcpos) d _
  rw [← hd, hZY, he] at h1
  have h2 : e = dbin^[hpart n] d := by
    apply emb_injective
    funext i
    have h3 : c * emb e i = c * emb (dbin^[hpart n] d) i := congrFun h1 i
    exact mul_left_cancel₀ (ne_of_gt hcpos) h3
  rw [h2]
  exact range_dbin_hpart_subset_S ⟨d, rfl⟩

/-! ## Shadowing : the orbit follows one periodic binary cycle (Theorem 2.1 (2)) -/

/-- The Ducci map is `2`-Lipschitz (3.10). -/
lemma norm_ducci_sub_le {n : ℕ} [NeZero n] (u v : ZMod n → ℝ) :
    ‖ducci u - ducci v‖ ≤ 2 * ‖u - v‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  have h1 : |u i - v i| ≤ ‖u - v‖ := by
    have := norm_le_pi_norm (u - v) i
    rwa [Real.norm_eq_abs] at this
  have h2 : |u (i + 1) - v (i + 1)| ≤ ‖u - v‖ := by
    have := norm_le_pi_norm (u - v) (i + 1)
    rwa [Real.norm_eq_abs] at this
  have hcoord : (ducci u - ducci v) i = |u i - u (i + 1)| - |v i - v (i + 1)| := rfl
  rw [Real.norm_eq_abs, hcoord]
  have key := abs_abs_sub_abs_le_abs_sub (u i - u (i + 1)) (v i - v (i + 1))
  have h3 : |(u i - u (i + 1)) - (v i - v (i + 1))| ≤ |u i - v i| + |u (i + 1) - v (i + 1)| := by
    rw [show (u i - u (i + 1)) - (v i - v (i + 1)) = (u i - v i) - (u (i + 1) - v (i + 1)) by ring]
    exact abs_sub _ _
  linarith

private lemma norm_sub_triangle {E : Type*} [SeminormedAddCommGroup E] (a b c : E) :
    ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  simpa using norm_add_le (a - b) (b - c)

/-- The orbit approaches the finite set `c • S n` (3.9). -/
lemma exists_approx {n : ℕ} [NeZero n] {x : ZMod n → ℝ} {c : ℝ} (hx : ∀ i, 0 ≤ x i)
    (hcpos : 0 < c) (hc : Filter.Tendsto (fun q => ‖ducci^[q] x‖) Filter.atTop (nhds c))
    (hlow : ∀ q, c ≤ ‖ducci^[q] x‖) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q, ∀ q ≥ Q, ∃ e ∈ S n, ‖ducci^[q] x - c • emb e‖ < δ := by
  by_contra hcon
  push_neg at hcon
  have hfreq : ∃ᶠ q in Filter.atTop, ∀ e ∈ S n, δ ≤ ‖ducci^[q] x - c • emb e‖ := by
    rw [Filter.frequently_atTop]
    intro Q
    obtain ⟨q, hq, hq'⟩ := hcon Q
    exact ⟨q, hq, hq'⟩
  obtain ⟨φ, hφ, hprop⟩ := extraction_of_frequently_atTop hfreq
  have hb : ∀ j : ℕ, ducci^[φ j] x ∈ Metric.closedBall (0 : ZMod n → ℝ) ‖x‖ := by
    intro j
    simp only [Metric.mem_closedBall, dist_zero_right]
    simpa using antitone_norm_iterate hx (Nat.zero_le (φ j))
  obtain ⟨Y, -, θ, hθ, hY⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hb
  have hYlim : IsOrbitLimit x Y := ⟨fun j => φ (θ j), hφ.comp hθ, hY⟩
  obtain ⟨e, heS, rfl⟩ := hYlim.mem_scaled_S hx hcpos hc hlow
  have hconst : Filter.Tendsto (fun _ : ℕ => c • emb e) Filter.atTop (nhds (c • emb e)) :=
    tendsto_const_nhds
  have hsub := hY.sub hconst
  rw [sub_self] at hsub
  have hconv : Filter.Tendsto (fun j => ‖ducci^[φ (θ j)] x - c • emb e‖) Filter.atTop (nhds 0) := by
    simpa using hsub.norm
  have hge : ∀ j, δ ≤ ‖ducci^[φ (θ j)] x - c • emb e‖ := fun j => hprop (θ j) e heS
  have := ge_of_tendsto' hconv hge
  linarith

/-- Theorem 2.1 (1) and (2) : the sup norms converge to a limit `c`, and the orbit is
asymptotic, phase by phase, to the periodic cycle `q ↦ c • E q` of the binary Ducci map. -/
theorem main_asymptotic {n : ℕ} [NeZero n] {x : ZMod n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    ∃ (c : ℝ) (E : ℕ → (ZMod n → ZMod 2)), 0 ≤ c ∧
      Filter.Tendsto (fun q => ‖ducci^[q] x‖) Filter.atTop (nhds c) ∧
      (∀ q, E q ∈ S n) ∧ (∀ q, E (q + 1) = dbin (E q)) ∧ (∃ r > 0, ∀ q, E (q + r) = E q) ∧
      Filter.Tendsto (fun q => ‖ducci^[q] x - c • emb (E q)‖) Filter.atTop (nhds 0) := by
  obtain ⟨c, hc0, hc, hlow⟩ := exists_tendsto_norm_iterate hx
  rcases eq_or_lt_of_le hc0 with hc0' | hcpos
  · -- the orbit converges to zero
    refine ⟨c, fun _ => 0, hc0, hc, fun _ => zero_mem_S n, fun _ => by funext i; rfl,
      ⟨1, one_pos, fun _ => rfl⟩, ?_⟩
    have : ∀ q : ℕ, ‖ducci^[q] x - c • emb (0 : ZMod n → ZMod 2)‖ = ‖ducci^[q] x‖ := by
      intro q
      congr 1
      rw [← hc0']
      funext i
      show ducci^[q] x i - 0 * bval 0 = ducci^[q] x i
      ring
    simp only [this]
    rw [hc0']
    exact hc
  · -- the orbit shadows a nonzero cycle
    obtain ⟨Q, hQ⟩ := exists_approx hx hcpos hc hlow (δ := c / 10) (by linarith)
    obtain ⟨eQ, heQS, heQ⟩ := hQ Q (le_refl Q)
    -- the nearby binary vectors follow the binary orbit of `eQ`
    have hstep : ∀ k : ℕ, ‖ducci^[Q + k] x - c • emb (dbin^[k] eQ)‖ < c / 10 := by
      intro k
      induction k with
      | zero => simpa using heQ
      | succ k ih =>
          obtain ⟨g, hgS, hg⟩ := hQ (Q + (k + 1)) (by omega)
          have hlip : ‖ducci^[Q + (k + 1)] x - c • emb (dbin^[k + 1] eQ)‖ ≤ 2 * (c / 10) := by
            have h1 : ducci^[Q + (k + 1)] x = ducci (ducci^[Q + k] x) := by
              rw [show Q + (k + 1) = (Q + k) + 1 by ring, Function.iterate_succ_apply']
            have h2 : c • emb (dbin^[k + 1] eQ) = ducci (c • emb (dbin^[k] eQ)) := by
              rw [Function.iterate_succ_apply', ducci_smul_emb (le_of_lt hcpos)]
            rw [h1, h2]
            exact le_trans (norm_ducci_sub_le _ _) (by linarith [ih.le])
          have hsep : ‖c • emb g - c • emb (dbin^[k + 1] eQ)‖ < c := by
            have := norm_sub_triangle (c • emb g) (ducci^[Q + (k + 1)] x)
              (c • emb (dbin^[k + 1] eQ))
            have hg' : ‖c • emb g - ducci^[Q + (k + 1)] x‖ < c / 10 := by
              rw [norm_sub_rev]; exact hg
            linarith
          have hgeq : g = dbin^[k + 1] eQ := by
            by_contra hne
            exact absurd hsep (not_lt.mpr (norm_smul_emb_sub (le_of_lt hcpos) hne))
          rw [← hgeq]
          exact hg
    obtain ⟨r, hr, hrper⟩ := exists_period_of_mem_S heQS
    set E : ℕ → (ZMod n → ZMod 2) := fun q => dbin^[q + Q * (r - 1)] eQ with hE_def
    have hEper : ∀ a : ℕ, dbin^[a + r] eQ = dbin^[a] eQ := by
      intro a
      rw [Function.iterate_add_apply, hrper]
    have hiter_mul : ∀ a m : ℕ, dbin^[a + m * r] eQ = dbin^[a] eQ := by
      intro a m
      induction m with
      | zero => simp
      | succ m ih => rw [show a + (m + 1) * r = (a + m * r) + r by ring, hEper, ih]
    have hQr : Q * (r - 1) + Q = Q * r := by
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      simp [Nat.mul_succ]
    have hEQ : ∀ k : ℕ, E (Q + k) = dbin^[k] eQ := by
      intro k
      show dbin^[Q + k + Q * (r - 1)] eQ = dbin^[k] eQ
      rw [show Q + k + Q * (r - 1) = k + Q * r by omega]
      exact hiter_mul k Q
    refine ⟨c, E, hc0, hc, fun q => dbin_iterate_mem_S heQS _, fun q => ?_, ⟨r, hr, fun q => ?_⟩, ?_⟩
    · show dbin^[q + 1 + Q * (r - 1)] eQ = dbin (dbin^[q + Q * (r - 1)] eQ)
      rw [show q + 1 + Q * (r - 1) = (q + Q * (r - 1)) + 1 by ring, Function.iterate_succ_apply']
    · show dbin^[q + r + Q * (r - 1)] eQ = dbin^[q + Q * (r - 1)] eQ
      rw [show q + r + Q * (r - 1) = (q + Q * (r - 1)) + r by ring, hEper]
    · rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨Q', hQ'⟩ := exists_approx hx hcpos hc hlow (δ := min ε (c / 10))
        (lt_min hε (by linarith))
      refine ⟨max Q Q', fun q hq => ?_⟩
      have hq1 : Q ≤ q := le_trans (le_max_left _ _) hq
      have hq2 : Q' ≤ q := le_trans (le_max_right _ _) hq
      obtain ⟨g, hgS, hg⟩ := hQ' q hq2
      have hEq : E q = dbin^[q - Q] eQ := by
        have : q = Q + (q - Q) := by omega
        rw [this, hEQ]
        congr 1
        omega
      have hclose : ‖ducci^[q] x - c • emb (E q)‖ < c / 10 := by
        rw [hEq]
        have := hstep (q - Q)
        rwa [show Q + (q - Q) = q by omega] at this
      have hgmin : ‖ducci^[q] x - c • emb g‖ < c / 10 := lt_of_lt_of_le hg (min_le_right _ _)
      have hsep : ‖c • emb g - c • emb (E q)‖ < c := by
        have := norm_sub_triangle (c • emb g) (ducci^[q] x) (c • emb (E q))
        have hg' : ‖c • emb g - ducci^[q] x‖ < c / 10 := by
          rw [norm_sub_rev]; exact hgmin
        linarith
      have hgeq : g = E q := by
        by_contra hne
        exact absurd hsep (not_lt.mpr (norm_smul_emb_sub (le_of_lt hcpos) hne))
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), ← hgeq]
      exact lt_of_lt_of_le hg (min_le_left _ _)

/-! ## Theorem 2.1 (5) : all orbits converge to zero iff `n` is a power of two -/

theorem tendsto_zero_iff_pow_two {n : ℕ} [NeZero n] :
    (∀ x : ZMod n → ℝ, (∀ i, 0 ≤ x i) →
        Filter.Tendsto (fun q => ducci^[q] x) Filter.atTop (nhds 0)) ↔ ∃ v, n = 2 ^ v := by
  constructor
  · intro hall
    by_contra hpow
    obtain ⟨e, heS, hne⟩ := exists_ne_zero_mem_S hpow
    obtain ⟨r, hr, hper⟩ := exists_period_of_mem_S heS
    have hxnn : ∀ i, 0 ≤ ((1 : ℝ) • emb e) i := fun i => smul_emb_nonneg zero_le_one e i
    have hnormlim : Filter.Tendsto (fun q => ‖ducci^[q] ((1 : ℝ) • emb e)‖) Filter.atTop (nhds 0) := by
      simpa using (hall _ hxnn).norm
    have hfix : ∀ k : ℕ, ducci^[k * r] ((1 : ℝ) • emb e) = (1 : ℝ) • emb e := by
      intro k
      rw [ducci_iterate_smul_emb zero_le_one]
      congr 1
      induction k with
      | zero => simp
      | succ k ih =>
          rw [show (k + 1) * r = k * r + r by ring, Function.iterate_add_apply, hper, ih]
    have hone : ‖(1 : ℝ) • emb e‖ = 1 := norm_smul_emb_of_ne_zero zero_le_one hne
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hnormlim (1 / 2) (by norm_num)
    have hNr : N ≤ N * r := Nat.le_mul_of_pos_right _ hr
    have := hN (N * r) hNr
    rw [hfix N, hone, Real.dist_eq, sub_zero] at this
    norm_num at this
  · intro hpow x hx
    obtain ⟨c, E, hc0, hc, hES, hEstep, hEper, hconv⟩ := main_asymptotic hx
    have hzero : ∀ q, E q = 0 := by
      intro q
      have h := hES q
      rw [S_eq_zero_iff.mpr hpow] at h
      exact h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq : ∀ q, ‖ducci^[q] x‖ = ‖ducci^[q] x - c • emb (E q)‖ := by
      intro q
      rw [hzero q]
      congr 1
      funext i
      show ducci^[q] x i = ducci^[q] x i - c * bval 0
      rw [bval_zero]
      ring
    simpa only [← heq] using hconv

/-! ## The case `n = 5` (Section 4) -/

lemma hpart_five : hpart 5 = 1 := by
  simp [hpart, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ (2 ∣ 5))]

lemma mpart_five : mpart 5 = 5 := by rw [mpart, hpart_five, Nat.div_one]

/-- (4.1) : for `n = 5`, `S 5` is the set of binary vectors of even Hamming weight. -/
theorem mem_S_five_iff : ∀ e : ZMod 5 → ZMod 2, e ∈ S 5 ↔ ∑ i, e i = 0 := by
  simp only [S, Set.mem_setOf_eq, hpart_five, mpart_five]
  decide

theorem S_five_eq : S 5 = {e : ZMod 5 → ZMod 2 | ∑ i, e i = 0} := Set.ext mem_S_five_iff

/-- The starting point `e₀ = (1,1,0,0,0)` of the `15`-cycle. -/
def e5 : ZMod 5 → ZMod 2 := ![1, 1, 0, 0, 0]

lemma e5_mem_S : e5 ∈ S 5 := (mem_S_five_iff e5).mpr (by decide)

/-- Proposition 4.1, part one : the binary Ducci map has period exactly `15` at `e₀`. -/
theorem dbin_iterate_fifteen : dbin^[15] e5 = e5 := by decide

/-- Proposition 4.1, part two : the period is exactly `15`. -/
theorem dbin_iterate_ne_of_lt_fifteen : ∀ k < 15, 0 < k → dbin^[k] e5 ≠ e5 := by decide

/-- Proposition 4.1, part three : the fifteen nonzero elements of `S 5` form a single cycle. -/
theorem S_five_orbit (e : ZMod 5 → ZMod 2) (he : e ∈ S 5) (hne : e ≠ 0) :
    ∃ k < 15, dbin^[k] e5 = e := by
  rw [mem_S_five_iff] at he
  revert e
  decide

lemma dbin_zero {n : ℕ} : dbin (0 : ZMod n → ZMod 2) = 0 := by
  funext i
  show (0 : ZMod 2) + 0 = 0
  simp

lemma dbin_iterate_zero {n : ℕ} (k : ℕ) : dbin^[k] (0 : ZMod n → ZMod 2) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, dbin_zero]

lemma dbin_iterate_e5_mod (a : ℕ) : dbin^[a] e5 = dbin^[a % 15] e5 := by
  have hmul : ∀ m : ℕ, dbin^[15 * m] e5 = e5 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [show 15 * (m + 1) = 15 + 15 * m by ring, Function.iterate_add_apply, ih,
          dbin_iterate_fifteen]
  conv_lhs => rw [show a = a % 15 + 15 * (a / 15) by omega]
  rw [Function.iterate_add_apply, hmul]

/-- Corollary 4.2 : for `n = 5` every nonnegative orbit either converges to `0`, or is
asymptotic to a positive multiple of the `15`-cycle, with a definite phase. -/
theorem asymptotic_five {x : ZMod 5 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    Filter.Tendsto (fun q => ducci^[q] x) Filter.atTop (nhds 0) ∨
      ∃ c > (0 : ℝ), ∃ r < 15, Filter.Tendsto
        (fun q => ‖ducci^[q] x - c • emb (dbin^[(q + r) % 15] e5)‖) Filter.atTop (nhds 0) := by
  obtain ⟨c, E, hc0, hc, hES, hEstep, -, hconv⟩ := main_asymptotic hx
  have hEiter : ∀ q, E q = dbin^[q] (E 0) := by
    intro q
    induction q with
    | zero => rfl
    | succ q ih =>
        rw [hEstep q, ih]
        exact (Function.iterate_succ_apply' dbin q (E 0)).symm
  rcases eq_or_lt_of_le hc0 with hc0' | hcpos
  · left
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq : ∀ q, ‖ducci^[q] x‖ = ‖ducci^[q] x - c • emb (E q)‖ := by
      intro q
      congr 1
      funext i
      show ducci^[q] x i = ducci^[q] x i - c * bval (E q i)
      rw [← hc0']
      ring
    simpa only [← heq] using hconv
  · right
    have hE0 : E 0 ≠ 0 := by
      intro h0
      have hzero : ∀ q, E q = 0 := by
        intro q; rw [hEiter q, h0, dbin_iterate_zero]
      have heq : ∀ q, ‖ducci^[q] x‖ = ‖ducci^[q] x - c • emb (E q)‖ := by
        intro q
        rw [hzero q]
        congr 1
        funext i
        show ducci^[q] x i = ducci^[q] x i - c * bval 0
        rw [bval_zero]
        ring
      have h1 : Filter.Tendsto (fun q => ‖ducci^[q] x‖) Filter.atTop (nhds 0) := by
        simpa only [← heq] using hconv
      have := tendsto_nhds_unique hc h1
      exact absurd this (ne_of_gt hcpos)
    obtain ⟨r, hr, hre⟩ := S_five_orbit (E 0) (hES 0) hE0
    refine ⟨c, hcpos, r, hr, ?_⟩
    have hEq : ∀ q, E q = dbin^[(q + r) % 15] e5 := by
      intro q
      rw [hEiter q, ← hre, ← Function.iterate_add_apply, dbin_iterate_e5_mod]
    simpa only [hEq] using hconv

/-! ## Section 5 : an explicit nonconstant orbit tending to `0` but never reaching it

This is an optional extra: an eigenray of the Ducci map for `n = 5`.  We exhibit
`p ∈ (0,1)` with `(1+p)^3 (1-p^2) = 1` and a nonnegative, nonconstant vector `V`
with `P V = p • V`.  Its orbit is `p^q • V`, which converges to `0` but is never `0`. -/

lemma ducci_smul {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (x : ZMod n → ℝ) :
    ducci (c • x) = c • ducci x := by
  funext i
  show |c * x i - c * x (i + 1)| = c * |x i - x (i + 1)|
  rw [← mul_sub, abs_mul, abs_of_nonneg hc]

lemma ducci_iterate_smul {n : ℕ} {c : ℝ} (hc : 0 ≤ c) {x : ZMod n → ℝ}
    (hx : ducci x = c • x) (q : ℕ) : ducci^[q] x = c ^ q • x := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Function.iterate_succ_apply', ih, ducci_smul (pow_nonneg hc q), hx, smul_smul,
        pow_succ, mul_comm]

/-- There is a root of `t^4 + 3t^3 + 2t^2 - 2t - 3` in `(0,1)`; equivalently a
`p ∈ (0,1)` with `(1+p)^3 (1-p^2) = 1`. -/
lemma exists_eigen_ratio : ∃ p : ℝ, 0 < p ∧ p < 1 ∧ (1 + p) ^ 3 * (1 - p ^ 2) = 1 := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ 4 + 3 * t ^ 3 + 2 * t ^ 2 - 2 * t - 3)
      (Set.Icc 0 1) := by fun_prop
  have h := intermediate_value_Ioo (by norm_num : (0:ℝ) ≤ 1) hcont
  norm_num at h
  obtain ⟨p, hp, hq⟩ := h (by norm_num : (0:ℝ) ∈ Set.Ioo (-3:ℝ) 1)
  exact ⟨p, hp.1, hp.2, by linear_combination (-p) * hq⟩

/-- The eigenvector of the Ducci map on `ZMod 5` associated with the ratio `p`. -/
noncomputable def Vray (p : ℝ) : ZMod 5 → ℝ :=
  ![1, 1 - p, 1 - p ^ 2, (1 + p) * (1 - p ^ 2), (1 + p) ^ 2 * (1 - p ^ 2)]

lemma Vray_nonneg {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : ZMod 5) : 0 ≤ Vray p i := by
  have hsq : 0 < 1 - p ^ 2 := by nlinarith
  have hcase : ∀ i : ZMod 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide
  have h0 : Vray p 0 = 1 := rfl
  have h1 : Vray p 1 = 1 - p := rfl
  have h2 : Vray p 2 = 1 - p ^ 2 := rfl
  have h3 : Vray p 3 = (1 + p) * (1 - p ^ 2) := rfl
  have h4 : Vray p 4 = (1 + p) ^ 2 * (1 - p ^ 2) := rfl
  rcases hcase i with h | h | h | h | h <;> subst h <;>
    simp only [h0, h1, h2, h3, h4] <;> nlinarith

lemma Vray_ne {p : ℝ} (hp0 : 0 < p) : Vray p 0 ≠ Vray p 1 := by
  have h0 : Vray p 0 = 1 := rfl
  have h1 : Vray p 1 = 1 - p := rfl
  rw [h0, h1]; intro h; linarith

lemma ducci_Vray {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hkey : (1 + p) ^ 3 * (1 - p ^ 2) = 1) :
    ducci (Vray p) = p • Vray p := by
  have hsq : 0 < 1 - p ^ 2 := by nlinarith
  have hcase : ∀ i : ZMod 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide
  funext i
  have h0 : Vray p 0 = 1 := rfl
  have h1 : Vray p 1 = 1 - p := rfl
  have h2 : Vray p 2 = 1 - p ^ 2 := rfl
  have h3 : Vray p 3 = (1 + p) * (1 - p ^ 2) := rfl
  have h4 : Vray p 4 = (1 + p) ^ 2 * (1 - p ^ 2) := rfl
  have e0 : (0 : ZMod 5) + 1 = 1 := by decide
  have e1 : (1 : ZMod 5) + 1 = 2 := by decide
  have e2 : (2 : ZMod 5) + 1 = 3 := by decide
  have e3 : (3 : ZMod 5) + 1 = 4 := by decide
  have e4 : (4 : ZMod 5) + 1 = 0 := by decide
  rcases hcase i with h | h | h | h | h <;> subst h <;>
    simp only [ducci, Pi.smul_apply, smul_eq_mul, e0, e1, e2, e3, e4, h0, h1, h2, h3, h4]
  · rw [abs_of_nonneg (by nlinarith)]; ring
  · rw [abs_of_nonpos (by nlinarith)]; ring
  · rw [abs_of_nonpos (by nlinarith)]; ring
  · rw [abs_of_nonpos (by nlinarith)]; ring
  · rw [abs_of_nonpos (by nlinarith [mul_pos hp0 (mul_pos (by positivity : (0:ℝ) < (1 + p) ^ 2) hsq)])]
    linear_combination -hkey

/-- Section 5: there is a nonnegative, nonconstant vector in `ℝ^5` whose Ducci orbit
converges to `0` but never equals `0`. -/
theorem exists_nonconstant_tendsto_zero_five :
    ∃ x : ZMod 5 → ℝ, (∀ i, 0 ≤ x i) ∧ (∃ i j, x i ≠ x j) ∧
      (∀ q, ducci^[q] x ≠ 0) ∧
      Filter.Tendsto (fun q => ducci^[q] x) Filter.atTop (nhds 0) := by
  obtain ⟨p, hp0, hp1, hkey⟩ := exists_eigen_ratio
  refine ⟨Vray p, Vray_nonneg hp0 hp1, ⟨0, 1, Vray_ne hp0⟩, ?_, ?_⟩
  · intro q hq
    have hiter : ducci^[q] (Vray p) = p ^ q • Vray p :=
      ducci_iterate_smul hp0.le (ducci_Vray hp0 hp1 hkey) q
    rw [hiter] at hq
    have h0 : (p ^ q • Vray p) 0 = p ^ q := by
      show p ^ q * Vray p 0 = p ^ q
      rw [show Vray p 0 = 1 from rfl, mul_one]
    rw [hq] at h0
    exact absurd h0.symm (pow_ne_zero q (ne_of_gt hp0))
  · have hiter : ∀ q, ducci^[q] (Vray p) = p ^ q • Vray p := fun q =>
      ducci_iterate_smul hp0.le (ducci_Vray hp0 hp1 hkey) q
    have hpow : Filter.Tendsto (fun q : ℕ => p ^ q) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hp0.le hp1
    simpa only [← hiter, zero_smul] using hpow.smul_const (Vray p)


end Q668
