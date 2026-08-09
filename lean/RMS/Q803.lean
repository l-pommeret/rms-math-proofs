/-
# Q803 — Achievement sets of positive summable series

Q803 asks for a characterization of the sequences `a₁ ≥ a₂ ≥ ⋯ > 0` with `∑ aₙ < ∞` whose
set of subsums (the *achievement set*)

  `Σ(a) = { ∑ εₙ aₙ : εₙ ∈ {0,1} }`

has empty interior.

The answer formalized here is the exact finite-stage criterion.  With

  `rₙ = ∑_{k > n} aₖ`,  `Fₙ = { ∑_{k ≤ n} εₖ aₖ : εₖ ∈ {0,1} }`,

and `Δₙ` the largest span of a maximal block of `Fₙ` whose successive gaps are at most `rₙ`,
the main results are:

* `Q803.achievement_eq_iInter`   : `Σ(a) = ⋂ n, (Fₙ + [0, rₙ])`;
* `Q803.isGreatest_len_approx`   : the longest interval inside `Fₙ + [0, rₙ]` has length
  exactly `ℓₙ = rₙ + Δₙ`;
* `Q803.ell_antitone`, `Q803.tendsto_ell` : `ℓₙ` is nonincreasing and converges;
* `Q803.isGreatest_limLen`       : `lim ℓₙ = max { b - a : [a,b] ⊆ Σ(a) }` (the maximum is
  attained);
* `Q803.interior_achievement_eq_empty_iff` : `interior Σ(a) = ∅ ↔ Δₙ → 0`;
* `Q803.interior_achievement_eq_empty_iff_forall_eps` : `interior Σ(a) = ∅ ↔ ∀ ε > 0, ∃ n,
  rₙ + Δₙ < ε`.

## Differences between the printed statement and the formal statements

* Indexing.  The printed statement indexes the sequence from `1`; here sequences are indexed
  from `0`, so `tail a n = ∑_{k ≥ n} a k` is the sum of the terms *after* the first `n` terms
  `a 0, …, a (n-1)`, and `finSums a n` is the set of subsums of those first `n` terms.  This is
  a pure re-indexing of the printed `rₙ` and `Fₙ`.
* Monotonicity.  The printed statement assumes the sequence to be nonincreasing.  As the answer
  and its audit both observe, monotonicity is never needed for this characterization, so the
  theorems below are stated for an arbitrary summable sequence of positive (or, where that
  suffices, nonnegative) terms; they apply in particular to nonincreasing sequences.
* Definition of `Δₙ`.  Instead of listing `Fₙ` in increasing order and cutting it into maximal
  blocks with consecutive gaps `≤ rₙ`, we define `Δₙ` as the supremum of `y - x` over pairs
  `x, y ∈ Fₙ` joined by a chain of elements of `Fₙ` with consecutive steps of size at most `rₙ`
  (`Q803.chainRel`), together with `0`.  Two elements of `Fₙ` lie in a common maximal block
  exactly when they are so chained, so this is the same number.
* "Empty interior" is `interior Σ(a) = ∅` for the usual topology of `ℝ`, and the maximal
  length of an interval contained in `Σ(a)` is expressed as
  `IsGreatest {L | ∃ x, Set.Icc x (x + L) ⊆ Σ(a)}`, which also records that the maximum is
  attained.

Lean version: 4.28.0, mathlib: v4.28.0 (commit 8f9d9cff6bd728b17a24e163c9402775d9e6a365).
-/
import Mathlib

open Set Filter Topology

namespace Q803

noncomputable section

variable (a : ℕ → ℝ)

/-- The tail `r n = ∑_{k ≥ n} a k`. (With `0`-based indexing, `tail a n` is the sum of the
terms *after* the first `n` terms `a 0, …, a (n-1)`.) -/
def tail (n : ℕ) : ℝ := ∑' k : ℕ, a (n + k)

/-- The finite set `F n` of all subsums of the first `n` terms `a 0, …, a (n-1)`. -/
def finSums (n : ℕ) : Finset ℝ :=
  (Finset.range n).powerset.image (fun s => ∑ i ∈ s, a i)

/-- The achievement set `Σ(a)` of all subsums `∑ ε n * a n`, `ε n ∈ {0,1}`. -/
def achievement : Set ℝ := {x | ∃ ε : ℕ → Bool, HasSum (fun n => if ε n then a n else 0) x}

/-- The `n`-th approximant `I n = F n + [0, r n]`. -/
def approx (n : ℕ) : Set ℝ := ⋃ f ∈ finSums a n, Icc f (f + tail a n)

variable {a}

/-- `x` and `y` are joined by a chain inside the finite set `F` with steps of size at most `r`. -/
def chainRel (F : Finset ℝ) (r : ℝ) (x y : ℝ) : Prop :=
  Relation.ReflTransGen (fun u v => u ∈ F ∧ v ∈ F ∧ |u - v| ≤ r) x y

/-- `Δ`: the largest span `y - x` of a maximal `r`-chain-connected block of the finite set `F`. -/
def blockSpan (F : Finset ℝ) (r : ℝ) : ℝ :=
  sSup (insert (0 : ℝ) {d : ℝ | ∃ x ∈ F, ∃ y ∈ F, chainRel F r x y ∧ d = y - x})

variable (a)

/-- `ℓ n = r n + Δ n`, the largest length of an interval contained in the `n`-th approximant. -/
def ell (n : ℕ) : ℝ := tail a n + blockSpan (finSums a n) (tail a n)

/-- The limit of the nonincreasing sequence `ℓ n`. -/
def limLen : ℝ := ⨅ n, ell a n

variable {a}

/-! ### Basic facts about tails and finite subsums -/

theorem tail_nonneg (ha : ∀ n, 0 ≤ a n) (n : ℕ) : 0 ≤ tail a n :=
  tsum_nonneg fun _ => ha _

theorem summable_shift (hsum : Summable a) (n : ℕ) : Summable fun k : ℕ => a (n + k) := by
  simpa [add_comm] using (summable_nat_add_iff (f := a) n).2 hsum

theorem tail_succ (hsum : Summable a) (n : ℕ) : tail a n = a n + tail a (n + 1) := by
  rw [tail, (summable_shift hsum n).tsum_eq_zero_add]
  simp only [add_zero, tail]
  congr 1
  exact tsum_congr fun k => by ring_nf

theorem tendsto_tail (a : ℕ → ℝ) : Tendsto (tail a) atTop (𝓝 0) := by
  simpa [tail, add_comm] using tendsto_sum_nat_add a

theorem zero_mem_finSums (n : ℕ) : (0 : ℝ) ∈ finSums a n :=
  Finset.mem_image.2 ⟨∅, by simp, by simp⟩

theorem finSums_subset_succ (n : ℕ) : finSums a n ⊆ finSums a (n + 1) := by
  intro x hx
  rcases Finset.mem_image.1 hx with ⟨s, hs, rfl⟩
  simp only [Finset.mem_powerset] at hs
  exact Finset.mem_image.2 ⟨s, Finset.mem_powerset.2
    (hs.trans (Finset.range_mono (Nat.le_succ n))), rfl⟩

theorem finSums_succ (n : ℕ) :
    finSums a (n + 1) = finSums a n ∪ (finSums a n).image (fun x => x + a n) := by
  unfold finSums
  rw [Finset.range_add_one, Finset.powerset_insert, Finset.image_union, Finset.image_image]
  congr 1
  rw [Finset.image_image]
  refine Finset.image_congr ?_
  intro s hs
  simp only [Finset.mem_coe, Finset.mem_powerset] at hs
  have hn : n ∉ s := fun h => by simpa using hs h
  simp [Function.comp, Finset.sum_insert hn, add_comm]

theorem finSums_nonneg (ha : ∀ n, 0 ≤ a n) {n : ℕ} {f : ℝ} (hf : f ∈ finSums a n) : 0 ≤ f := by
  rcases Finset.mem_image.1 hf with ⟨s, _, rfl⟩
  exact Finset.sum_nonneg fun i _ => ha i

theorem tail_eq' (n : ℕ) : tail a n = ∑' k : ℕ, a (k + n) :=
  tsum_congr fun k => by rw [add_comm]

theorem summable_select (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) (ε : ℕ → Bool) :
    Summable (fun n => if ε n then a n else 0) :=
  Summable.of_nonneg_of_le (fun n => by by_cases h : ε n <;> simp [h, ha n])
    (fun n => by by_cases h : ε n <;> simp [h, ha n]) hsum

/-! ### The approximants -/

theorem mem_approx_iff {n : ℕ} {x : ℝ} :
    x ∈ approx a n ↔ ∃ f ∈ finSums a n, f ≤ x ∧ x ≤ f + tail a n := by
  simp only [approx, mem_iUnion, mem_Icc, exists_prop]

theorem approx_antitone (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) (n : ℕ) :
    approx a (n + 1) ⊆ approx a n := by
  intro x hx
  rw [mem_approx_iff] at hx ⊢
  obtain ⟨f, hf, hfx, hxf⟩ := hx
  have hts := tail_succ hsum n
  have han := ha n
  rw [finSums_succ] at hf
  rcases Finset.mem_union.1 hf with hf | hf
  · exact ⟨f, hf, hfx, by linarith⟩
  · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hf
    exact ⟨g, hg, by linarith, by linarith⟩

theorem achievement_subset_approx (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) (n : ℕ) :
    achievement a ⊆ approx a n := by
  rintro x ⟨ε, hx⟩
  have hgs : Summable (fun k => if ε k then a k else 0) := summable_select ha hsum ε
  have hxeq : x = ∑' k, (if ε k then a k else 0) := hx.tsum_eq.symm
  have hsplit := hgs.sum_add_tsum_nat_add n
  rw [mem_approx_iff]
  refine ⟨∑ i ∈ Finset.range n, (if ε i then a i else 0), ?_, ?_, ?_⟩
  · refine Finset.mem_image.2 ⟨(Finset.range n).filter (fun i => ε i = true), ?_, ?_⟩
    · exact Finset.mem_powerset.2 (Finset.filter_subset _ _)
    · rw [Finset.sum_filter]
  · have h0 : 0 ≤ ∑' i : ℕ, (if ε (i + n) then a (i + n) else 0) :=
      tsum_nonneg fun i => by by_cases h : ε (i + n) <;> simp [h, ha]
    rw [hxeq, ← hsplit]; linarith
  · have h1 : (∑' i : ℕ, (if ε (i + n) then a (i + n) else 0)) ≤ tail a n := by
      rw [tail_eq']
      exact Summable.tsum_le_tsum (f := fun i : ℕ => (if ε (i + n) then a (i + n) else 0))
        (g := fun i : ℕ => a (i + n)) (fun i => by by_cases h : ε (i + n) <;> simp [h, ha])
        ((summable_nat_add_iff n).2 hgs) ((summable_nat_add_iff n).2 hsum)
    rw [hxeq, ← hsplit]; linarith

theorem finSums_subset_achievement {n : ℕ} {f : ℝ} (hf : f ∈ finSums a n) : f ∈ achievement a := by
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hf
  refine ⟨fun i => decide (i ∈ s), ?_⟩
  have := hasSum_sum_of_ne_finset_zero (f := fun i => if decide (i ∈ s) = true then a i else 0)
    (s := s) (L := SummationFilter.unconditional ℕ) (fun b hb => by simp [hb])
  simpa using this

theorem isCompact_achievement (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) :
    IsCompact (achievement a) := by
  have hcont : Continuous (fun ε : ℕ → Bool => ∑' n, if ε n then a n else 0) := by
    refine continuous_tsum (u := fun n => |a n|) (fun n => ?_) hsum.abs (fun n x => ?_)
    · exact (continuous_of_discreteTopology
        (f := fun b : Bool => if b then a n else 0)).comp (continuous_apply n)
    · by_cases h : x n <;> simp [h, abs_nonneg]
  have hrange : achievement a = Set.range (fun ε : ℕ → Bool => ∑' n, if ε n then a n else 0) := by
    ext x
    constructor
    · rintro ⟨ε, hx⟩; exact ⟨ε, hx.tsum_eq⟩
    · rintro ⟨ε, rfl⟩; exact ⟨ε, (summable_select ha hsum ε).hasSum⟩
  rw [hrange]
  exact isCompact_range hcont

/-- The fundamental identity `Σ(a) = ⋂ n, (F n + [0, r n])`. -/
theorem achievement_eq_iInter (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) :
    achievement a = ⋂ n, approx a n := by
  refine Set.Subset.antisymm (subset_iInter fun n => achievement_subset_approx ha hsum n) ?_
  intro x hx
  have hxn : ∀ n, ∃ f ∈ finSums a n, f ≤ x ∧ x ≤ f + tail a n := fun n =>
    mem_approx_iff.1 (mem_iInter.1 hx n)
  choose f hf hfx hxf using hxn
  have hzero : Tendsto (fun n => f n - x) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (tendsto_tail a)
    rw [Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith [hfx n])]
    linarith [hxf n]
  have hlim : Tendsto f atTop (𝓝 x) := by
    have := hzero.add (tendsto_const_nhds (x := x) (f := atTop (α := ℕ)))
    simpa using this
  exact ((isCompact_achievement ha hsum).isClosed).mem_of_tendsto hlim
    (Eventually.of_forall fun n => finSums_subset_achievement (hf n))

/-! ### Basic API for `blockSpan` -/

/-- The set of spans of `r`-chain-connected pairs of `F`, together with `0`. -/
def spanSet (F : Finset ℝ) (r : ℝ) : Set ℝ :=
  insert (0 : ℝ) {d : ℝ | ∃ x ∈ F, ∃ y ∈ F, chainRel F r x y ∧ d = y - x}

theorem blockSpan_eq_sSup (F : Finset ℝ) (r : ℝ) : blockSpan F r = sSup (spanSet F r) := rfl

theorem spanSet_finite (F : Finset ℝ) (r : ℝ) : (spanSet F r).Finite := by
  refine Set.Finite.insert _ (Set.Finite.subset
    (Set.Finite.image (fun p : ℝ × ℝ => p.2 - p.1) ((F.finite_toSet).prod (F.finite_toSet))) ?_)
  rintro d ⟨x, hx, y, hy, -, rfl⟩
  exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩

theorem spanSet_bddAbove (F : Finset ℝ) (r : ℝ) : BddAbove (spanSet F r) :=
  (spanSet_finite F r).bddAbove

theorem blockSpan_nonneg (F : Finset ℝ) (r : ℝ) : 0 ≤ blockSpan F r :=
  le_csSup (spanSet_bddAbove F r) (Set.mem_insert _ _)

theorem le_blockSpan {F : Finset ℝ} {r x y : ℝ} (hx : x ∈ F) (hy : y ∈ F)
    (h : chainRel F r x y) : y - x ≤ blockSpan F r :=
  le_csSup (spanSet_bddAbove F r) (Set.mem_insert_of_mem _ ⟨x, hx, y, hy, h, rfl⟩)

theorem blockSpan_mem_spanSet (F : Finset ℝ) (r : ℝ) : blockSpan F r ∈ spanSet F r :=
  Set.Nonempty.csSup_mem ⟨0, Set.mem_insert _ _⟩ (spanSet_finite F r)

/-! ### The components of a finite union of intervals of equal length -/

/-- `thicken F r = F + [0, r]`, a finite union of closed intervals of length `r`. -/
def thicken (F : Finset ℝ) (r : ℝ) : Set ℝ := ⋃ f ∈ F, Icc f (f + r)

theorem approx_eq_thicken (n : ℕ) : approx a n = thicken (finSums a n) (tail a n) := rfl

theorem mem_thicken {F : Finset ℝ} {r t : ℝ} :
    t ∈ thicken F r ↔ ∃ f ∈ F, f ≤ t ∧ t ≤ f + r := by
  simp only [thicken, mem_iUnion, mem_Icc, exists_prop]

theorem isClosed_thicken (F : Finset ℝ) (r : ℝ) : IsClosed (thicken F r) :=
  F.finite_toSet.isClosed_biUnion fun _ _ => isClosed_Icc

theorem chainRel_symm {F : Finset ℝ} {r x y : ℝ} (h : chainRel F r x y) : chainRel F r y x := by
  refine Relation.ReflTransGen.symmetric ?_ h
  rintro u v ⟨hu, hv, huv⟩
  exact ⟨hv, hu, by rwa [abs_sub_comm]⟩

/-- A chain of steps of size at most `r` inside `F` spans an interval contained in `thicken F r`. -/
theorem chain_Icc_subset {F : Finset ℝ} {r x y : ℝ} (hx : x ∈ F) (h : chainRel F r x y) :
    Icc (min x y) (max x y + r) ⊆ thicken F r := by
  induction h with
  | refl =>
    intro t ht
    rw [min_self, max_self] at ht
    exact mem_thicken.2 ⟨x, hx, ht.1, ht.2⟩
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hc, hbc'⟩ := hbc
    have hcb : c ≤ b + r := by cases abs_le.1 hbc'; linarith
    have hbc2 : b ≤ c + r := by cases abs_le.1 hbc'; linarith
    intro t ht
    by_cases hin : t ∈ Icc (min x b) (max x b + r)
    · exact ih hin
    · obtain ⟨h1, h2⟩ := ht
      have hmm : min x c = x ∨ min x c = c := min_choice x c
      have hMM : max x c = x ∨ max x c = c := max_choice x c
      have hmb : min x b ≤ x := min_le_left _ _
      have hmb' : min x b ≤ b := min_le_right _ _
      have hMb : x ≤ max x b := le_max_left _ _
      have hMb' : b ≤ max x b := le_max_right _ _
      simp only [mem_Icc, not_and_or, not_le] at hin
      refine mem_thicken.2 ⟨c, hc, ?_, ?_⟩
      · rcases hin with hlt | hgt
        · rcases hmm with h | h <;> rw [h] at h1 <;> linarith
        · linarith
      · rcases hin with hlt | hgt
        · linarith
        · rcases hMM with h | h <;> rw [h] at h2 <;> linarith

/-- Any interval contained in `thicken F r` has length at most `r + blockSpan F r`. -/
theorem le_of_Icc_subset_thicken {F : Finset ℝ} {r x L : ℝ} (hL : 0 ≤ L)
    (hsub : Icc x (x + L) ⊆ thicken F r) : L ≤ r + blockSpan F r := by
  classical
  have hx : x ∈ thicken F r := hsub ⟨le_rfl, by linarith⟩
  obtain ⟨f0, hf0, hf0x, hxf0⟩ := mem_thicken.1 hx
  set R : Finset ℝ := F.filter (fun g => chainRel F r f0 g) with hRdef
  have hf0R : f0 ∈ R := Finset.mem_filter.2 ⟨hf0, Relation.ReflTransGen.refl⟩
  have hRne : R.Nonempty := ⟨f0, hf0R⟩
  have hRsub : R ⊆ F := Finset.filter_subset _ _
  set A : Set ℝ := thicken R r with hA
  set B : Set ℝ := thicken (F \ R) r with hB
  have hcover : thicken F r ⊆ A ∪ B := by
    intro t ht
    obtain ⟨g, hg, hg1, hg2⟩ := mem_thicken.1 ht
    by_cases hgR : g ∈ R
    · exact Or.inl (mem_thicken.2 ⟨g, hgR, hg1, hg2⟩)
    · exact Or.inr (mem_thicken.2 ⟨g, Finset.mem_sdiff.2 ⟨hg, hgR⟩, hg1, hg2⟩)
  have hdisj : ∀ t, t ∈ A → t ∈ B → False := by
    intro t htA htB
    obtain ⟨g, hg, hg1, hg2⟩ := mem_thicken.1 htA
    obtain ⟨h, hh, hh1, hh2⟩ := mem_thicken.1 htB
    obtain ⟨hhF, hhR⟩ := Finset.mem_sdiff.1 hh
    have hgF : g ∈ F := hRsub hg
    have hgch : chainRel F r f0 g := (Finset.mem_filter.1 hg).2
    have habs : |g - h| ≤ r := abs_le.2 ⟨by linarith, by linarith⟩
    exact hhR (Finset.mem_filter.2 ⟨hhF, hgch.tail ⟨hgF, hhF, habs⟩⟩)
  have hsubA : Icc x (x + L) ⊆ A := by
    by_contra hcon
    obtain ⟨t, htI, htA⟩ := Set.not_subset.1 hcon
    have hBne : (Icc x (x + L) ∩ B).Nonempty := by
      refine ⟨t, htI, ?_⟩
      rcases hcover (hsub htI) with h | h
      · exact absurd h htA
      · exact h
    have hAne : (Icc x (x + L) ∩ A).Nonempty :=
      ⟨x, ⟨le_rfl, by linarith⟩, mem_thicken.2 ⟨f0, hf0R, hf0x, hxf0⟩⟩
    obtain ⟨s, -, hsA, hsB⟩ := isPreconnected_closed_iff.mp
      (isPreconnected_Icc (a := x) (b := x + L)) A B
      (isClosed_thicken _ _) (isClosed_thicken _ _) (hsub.trans hcover) hAne hBne
    exact hdisj s hsA hsB
  have hMmem : R.max' hRne ∈ R := R.max'_mem hRne
  have hmmem : R.min' hRne ∈ R := R.min'_mem hRne
  have hchainM : chainRel F r f0 (R.max' hRne) := (Finset.mem_filter.1 hMmem).2
  have hchainm : chainRel F r f0 (R.min' hRne) := (Finset.mem_filter.1 hmmem).2
  have hspan : R.max' hRne - R.min' hRne ≤ blockSpan F r :=
    le_blockSpan (hRsub hmmem) (hRsub hMmem) ((chainRel_symm hchainm).trans hchainM)
  have hend : x + L ≤ R.max' hRne + r := by
    obtain ⟨g, hg, hg1, hg2⟩ := mem_thicken.1 (hsubA ⟨by linarith, le_rfl⟩)
    have : g ≤ R.max' hRne := R.le_max' g hg
    linarith
  have hstart : R.min' hRne ≤ x := le_trans (R.min'_le f0 hf0R) hf0x
  linarith

theorem isGreatest_thicken (F : Finset ℝ) (r : ℝ) (hr : 0 ≤ r) (hF : F.Nonempty) :
    IsGreatest {L : ℝ | ∃ x, Icc x (x + L) ⊆ thicken F r} (r + blockSpan F r) := by
  constructor
  · rcases blockSpan_mem_spanSet F r with h0 | ⟨x, hx, y, hy, hchain, hd⟩
    · obtain ⟨f, hf⟩ := hF
      refine ⟨f, ?_⟩
      rw [h0, add_zero]
      intro t ht
      exact mem_thicken.2 ⟨f, hf, ht.1, ht.2⟩
    · have hxy : x ≤ y := by
        have := blockSpan_nonneg F r
        rw [hd] at this; linarith
      refine ⟨x, ?_⟩
      have h1 : Icc (min x y) (max x y + r) ⊆ thicken F r := chain_Icc_subset hx hchain
      rw [min_eq_left hxy, max_eq_right hxy] at h1
      have heq : x + (r + blockSpan F r) = y + r := by rw [hd]; ring
      rw [heq]
      exact h1
  · rintro L ⟨x, hxsub⟩
    rcases le_or_gt 0 L with hL | hL
    · exact le_of_Icc_subset_thicken hL hxsub
    · have := blockSpan_nonneg F r
      linarith

/-! ### The components of an approximant -/

theorem isGreatest_len_approx (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    IsGreatest {L : ℝ | ∃ x, Icc x (x + L) ⊆ approx a n} (ell a n) := by
  simpa [approx_eq_thicken, ell] using
    isGreatest_thicken (finSums a n) (tail a n) (tail_nonneg ha n)  ⟨0, zero_mem_finSums n⟩

/-! ### Passing to the limit -/

theorem ell_antitone (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) : Antitone (ell a) := by
  refine antitone_nat_of_succ_le fun n => ?_
  obtain ⟨x, hx⟩ := (isGreatest_len_approx ha (n + 1)).1
  exact (isGreatest_len_approx ha n).2 ⟨x, hx.trans (approx_antitone ha hsum n)⟩

theorem ell_nonneg (ha : ∀ n, 0 ≤ a n) (n : ℕ) : 0 ≤ ell a n :=
  add_nonneg (tail_nonneg ha n) (blockSpan_nonneg _ _)

theorem bddBelow_range_ell (ha : ∀ n, 0 ≤ a n) : BddBelow (Set.range (ell a)) :=
  ⟨0, by rintro y ⟨n, rfl⟩; exact ell_nonneg ha n⟩

theorem tendsto_ell (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) :
    Tendsto (ell a) atTop (𝓝 (limLen a)) :=
  tendsto_atTop_ciInf (ell_antitone ha hsum) (bddBelow_range_ell ha)

theorem limLen_nonneg (ha : ∀ n, 0 ≤ a n) : 0 ≤ limLen a :=
  le_ciInf fun n => ell_nonneg ha n

theorem limLen_le (ha : ∀ n, 0 ≤ a n) (n : ℕ) : limLen a ≤ ell a n :=
  ciInf_le (bddBelow_range_ell ha) n

theorem approx_subset_Icc (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) (n : ℕ) :
    approx a n ⊆ Icc 0 (tail a 0) := by
  intro y hy
  rw [mem_approx_iff] at hy
  obtain ⟨f, hf, hfy, hyf⟩ := hy
  have h0 : 0 ≤ f := finSums_nonneg ha hf
  have hb : f + tail a n ≤ tail a 0 := by
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hf
    have hsplit := hsum.sum_add_tsum_nat_add n
    have h1 : ∑ i ∈ s, a i ≤ ∑ i ∈ Finset.range n, a i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.mem_powerset.1 hs) fun i _ _ => ha i
    have h2 : tail a n = ∑' i : ℕ, a (i + n) := tail_eq' n
    have h3 : tail a 0 = ∑' i : ℕ, a i := by simp [tail]
    rw [h2, h3, ← hsplit]
    linarith
  exact ⟨le_trans h0 hfy, by linarith [tail_nonneg ha n]⟩

theorem isClosed_approx (n : ℕ) : IsClosed (approx a n) :=
  (finSums a n).finite_toSet.isClosed_biUnion fun _ _ => isClosed_Icc

theorem approx_antitone' (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) : Antitone (approx a) :=
  antitone_nat_of_succ_le (approx_antitone ha hsum)

/-- **Main theorem.** The limit of `ℓ n = r n + Δ n` is the maximal length of an interval
contained in the achievement set, and this maximum is attained. -/
theorem isGreatest_limLen (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) :
    IsGreatest {L : ℝ | ∃ x, Icc x (x + L) ⊆ achievement a} (limLen a) := by
  constructor
  · choose u hu using fun n => (isGreatest_len_approx ha n).1
    have humem : ∀ n, u n ∈ Icc (0 : ℝ) (tail a 0) := fun n =>
      approx_subset_Icc ha hsum n (hu n ⟨le_rfl, by linarith [ell_nonneg ha n]⟩)
    obtain ⟨x, -, phi, hphi, hlim⟩ :=
      (isCompact_Icc (a := (0 : ℝ)) (b := tail a 0)).tendsto_subseq humem
    refine ⟨x, ?_⟩
    rw [achievement_eq_iInter ha hsum]
    intro t ht
    refine mem_iInter.2 fun m => ?_
    refine (isClosed_approx m).mem_of_tendsto (b := atTop)
      (f := fun j => u (phi j) + (t - x)) ?_ ?_
    · have := hlim.add (tendsto_const_nhds (x := t - x) (f := atTop (α := ℕ)))
      simpa using this
    · filter_upwards [eventually_ge_atTop m] with j hj
      refine approx_antitone' ha hsum (le_trans hj hphi.le_apply) (hu (phi j) ⟨?_, ?_⟩)
      · linarith [ht.1]
      · have h1 : limLen a ≤ ell a (phi j) := limLen_le ha _
        have h2 := ht.2
        linarith
  · rintro L ⟨x, hx⟩
    refine le_ciInf fun n => ?_
    exact (isGreatest_len_approx ha n).2
      ⟨x, hx.trans (achievement_subset_approx ha hsum n)⟩

theorem tendsto_blockSpan (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) :
    Tendsto (fun n => blockSpan (finSums a n) (tail a n)) atTop (𝓝 (limLen a)) := by
  have hfun : (fun n => blockSpan (finSums a n) (tail a n)) = fun n => ell a n - tail a n := by
    funext n; simp [ell]
  rw [hfun]
  simpa using (tendsto_ell ha hsum).sub (tendsto_tail a)

theorem limLen_eq_zero_iff_interior (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) :
    interior (achievement a) = ∅ ↔ limLen a = 0 := by
  constructor
  · intro hint
    by_contra h
    have hpos : 0 < limLen a := lt_of_le_of_ne (limLen_nonneg ha) (Ne.symm h)
    obtain ⟨x, hx⟩ := (isGreatest_limLen ha hsum).1
    have hsub : Ioo x (x + limLen a) ⊆ interior (achievement a) :=
      interior_maximal (Ioo_subset_Icc_self.trans hx) isOpen_Ioo
    rw [hint, Set.subset_empty_iff] at hsub
    have : (Ioo x (x + limLen a)).Nonempty := ⟨x + limLen a / 2, by constructor <;> linarith⟩
    rw [hsub] at this
    exact this.ne_empty rfl
  · intro h0
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
    have hIcc : Icc (x - ε / 2) (x - ε / 2 + ε / 2) ⊆ achievement a := by
      intro y hy
      refine interior_subset (hball ?_)
      simp only [Metric.mem_ball, Real.dist_eq, abs_lt]
      obtain ⟨hy1, hy2⟩ := hy
      constructor <;> linarith
    have hle := (isGreatest_limLen ha hsum).2 ⟨x - ε / 2, hIcc⟩
    rw [h0] at hle
    linarith

/-- **Main theorem.** The achievement set has empty interior if and only if `Δ n → 0`. -/
theorem interior_achievement_eq_empty_iff (ha : ∀ n, 0 < a n) (hsum : Summable a) :
    interior (achievement a) = ∅ ↔
      Tendsto (fun n => blockSpan (finSums a n) (tail a n)) atTop (𝓝 0) := by
  have ha' : ∀ n, 0 ≤ a n := fun n => (ha n).le
  have hlim := tendsto_blockSpan ha' hsum
  rw [limLen_eq_zero_iff_interior ha' hsum]
  constructor
  · intro h0; rwa [h0] at hlim
  · intro h; exact tendsto_nhds_unique hlim h

/-- **Main theorem, `ε`-form.** The achievement set has empty interior if and only if
for every `ε > 0` there is a stage `n` with `r n + Δ n < ε`. -/
theorem interior_achievement_eq_empty_iff_forall_eps (ha : ∀ n, 0 < a n) (hsum : Summable a) :
    interior (achievement a) = ∅ ↔ ∀ ε > 0, ∃ n, ell a n < ε := by
  have ha' : ∀ n, 0 ≤ a n := fun n => (ha n).le
  rw [limLen_eq_zero_iff_interior ha' hsum]
  constructor
  · intro h0 ε hε
    have hlim := tendsto_ell ha' hsum
    rw [h0] at hlim
    obtain ⟨n, hn⟩ := ((hlim.eventually (eventually_lt_nhds hε)).exists)
    exact ⟨n, hn⟩
  · intro h
    by_contra hne
    have hpos : 0 < limLen a := lt_of_le_of_ne (limLen_nonneg ha') (Ne.symm hne)
    obtain ⟨n, hn⟩ := h (limLen a) hpos
    exact absurd (limLen_le ha' n) (not_le.2 hn)

end

end Q803
