import Mathlib

/-!
# `ℓ^∞` spaces, the subspace `c₀`, and the Phillips–Sobczyk theorem

We model `ℓ^∞(X)` for a discrete index type `X` as the space `X →ᵇ ℂ` of bounded
continuous functions (equivalently, bounded functions, since `X` is discrete),
with the supremum norm.

The main result of this file is `Q867.no_projection_onto_c0`: there is no bounded
linear projection of `ℓ^∞(ℕ)` onto `c₀`.

The proof is the classical one.  One uses an almost disjoint family `(A_w)` of infinite
subsets of `ℕ`, indexed by the uncountable set `ℕ → Bool`: `A_w` is the set of codes of
the finite initial segments of `w`.  If `U` were a bounded projection onto `c₀`, then
for each `w` the "deficiency vector" `1_{A_w} - U 1_{A_w}` would have modulus at least
`1/2` at some index `k = k(w)`; by uncountability some index `k` is used by infinitely
many `w`.  Summing suitably rotated indicators over `n` such `w`'s, and splitting off the
(finitely supported, hence `c₀`, hence `U`-fixed) part living on the pairwise
intersections, one gets a vector of norm `≤ 1` whose deficiency vector has modulus at
least `n/2` at `k`.  For `n` large this contradicts `‖1 - U‖ ≤ 1 + ‖U‖`.
-/

noncomputable section

open Filter Topology BoundedContinuousFunction

namespace Q867

/-- `c₀`, the space of sequences tending to `0`, as a submodule of `ℓ^∞(ℕ)`. -/
def c0 : Submodule ℂ (ℕ →ᵇ ℂ) where
  carrier := {a | Tendsto (fun n => a n) atTop (𝓝 0)}
  add_mem' := by
    intro a b ha hb
    simpa using ha.add hb
  zero_mem' := by simpa using tendsto_const_nhds
  smul_mem' := by
    intro c a ha
    simpa using ha.const_smul c

@[simp] lemma mem_c0 {a : ℕ →ᵇ ℂ} : a ∈ c0 ↔ Tendsto (fun n => a n) atTop (𝓝 0) := Iff.rfl

/-! ### Uncountability of `ℕ → Bool` -/

open Classical in
theorem not_countable_boolSeq : ¬ Countable (ℕ → Bool) := by
  intro h
  obtain ⟨g, hg⟩ := exists_surjective_nat (ℕ → Bool)
  refine Function.cantor_surjective (fun n => {m | g n m = true}) ?_
  intro S
  obtain ⟨n, hn⟩ := hg (fun m => decide (m ∈ S))
  refine ⟨n, ?_⟩
  simp only
  ext m
  simp [hn]

/-! ### A unimodular rotation factor -/

/-- A unimodular complex number rotating `z` onto the nonnegative reals. -/
def uu (z : ℂ) : ℂ := if z = 0 then 1 else (starRingEnd ℂ) z / (‖z‖ : ℂ)

lemma norm_uu (z : ℂ) : ‖uu z‖ = 1 := by
  unfold uu
  split
  · simp
  · rename_i h
    rw [norm_div, RCLike.norm_conj]
    simp [norm_ne_zero_iff.2 h]

lemma uu_mul (z : ℂ) : uu z * z = (‖z‖ : ℂ) := by
  unfold uu
  split
  · rename_i h; simp [h]
  · rename_i h
    rw [div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast
    have : (‖z‖ : ℂ) ≠ 0 := by simpa using h
    field_simp

/-! ### An almost disjoint family of infinite subsets of `ℕ` -/

/-- The code of the length-`k` initial segment of `w`. -/
def codeSeg (w : ℕ → Bool) (k : ℕ) : ℕ :=
  Encodable.encode (List.ofFn (fun i : Fin k => w i))

lemma codeSeg_eq_iff {w w' : ℕ → Bool} {k k' : ℕ} (h : codeSeg w k = codeSeg w' k') :
    k = k' ∧ ∀ i, i < k → w i = w' i := by
  have h1 : List.ofFn (fun i : Fin k => w i) = List.ofFn (fun i : Fin k' => w' i) :=
    Encodable.encode_injective h
  have hk : k = k' := by simpa using congrArg List.length h1
  subst hk
  rw [List.ofFn_inj] at h1
  exact ⟨rfl, fun i hi => congrFun h1 ⟨i, hi⟩⟩

lemma codeSeg_injective (w : ℕ → Bool) : Function.Injective (codeSeg w) :=
  fun _ _ h => (codeSeg_eq_iff h).1

/-- The branch set attached to `w`: the codes of all its finite initial segments. -/
def Aset (w : ℕ → Bool) : Set ℕ := Set.range (codeSeg w)

lemma Aset_infinite (w : ℕ → Bool) : (Aset w).Infinite :=
  Set.infinite_range_of_injective (codeSeg_injective w)

lemma Aset_inter_finite {w w' : ℕ → Bool} (hne : w ≠ w') : (Aset w ∩ Aset w').Finite := by
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ w' j := by
    by_contra hcon
    push_neg at hcon
    exact hne (funext hcon)
  refine Set.Finite.subset (Set.Finite.image (codeSeg w) (Set.finite_Iic j)) ?_
  rintro m ⟨⟨kk, rfl⟩, ⟨kk', hk'⟩⟩
  obtain ⟨rfl, hval⟩ := codeSeg_eq_iff hk'.symm
  refine ⟨kk, ?_, rfl⟩
  simp only [Set.mem_Iic]
  by_contra hcon
  push_neg at hcon
  exact hj (hval j hcon)

open Classical in
/-- The indicator function of the branch set `A_w`, as an element of `ℓ^∞(ℕ)`. -/
def chiA (w : ℕ → Bool) : ℕ →ᵇ ℂ :=
  ofNormedAddCommGroupDiscrete (fun m => if m ∈ Aset w then 1 else 0) 1
    (fun m => by dsimp only; split <;> simp)

open Classical in
@[simp] lemma chiA_apply (w : ℕ → Bool) (m : ℕ) :
    chiA w m = if m ∈ Aset w then 1 else 0 := rfl

lemma norm_chiA_le (w : ℕ → Bool) : ‖chiA w‖ ≤ 1 := by
  classical
  refine (BoundedContinuousFunction.norm_le zero_le_one).2 (fun m => ?_)
  rw [chiA_apply]
  split <;> simp

/-! ### The Phillips–Sobczyk theorem -/

/-- **Phillips–Sobczyk**: `c₀` is not complemented in `ℓ^∞`; that is, there is no
bounded linear projection of `ℓ^∞(ℕ)` onto `c₀`. -/
theorem no_projection_onto_c0 (U : (ℕ →ᵇ ℂ) →L[ℂ] (ℕ →ᵇ ℂ))
    (hrange : ∀ a, U a ∈ c0) (hid : ∀ a ∈ c0, U a = a) : False := by
  classical
  set C := ‖U‖ with hCdef
  have hC0 : (0:ℝ) ≤ C := norm_nonneg _
  -- the deficiency operator has norm at most `1 + C` on the unit ball
  have hdef : ∀ v : ℕ →ᵇ ℂ, ‖v‖ ≤ 1 → ‖v - U v‖ ≤ 1 + C := by
    intro v hv
    calc ‖v - U v‖ ≤ ‖v‖ + ‖U v‖ := norm_sub_le _ _
      _ ≤ 1 + C * 1 := by
          have := U.le_opNorm v
          have : ‖U v‖ ≤ C * 1 := le_trans this (by nlinarith)
          linarith
      _ = 1 + C := by ring
  -- deficiency vectors of the indicators
  set bv : (ℕ → Bool) → (ℕ →ᵇ ℂ) := fun w => chiA w - U (chiA w) with hbvdef
  -- each deficiency vector is large somewhere
  have hkey : ∀ w, ∃ kk, (1:ℝ)/2 ≤ ‖bv w kk‖ := by
    intro w
    have hc : Tendsto (fun m => ‖(U (chiA w)) m‖) atTop (𝓝 0) := by
      simpa using (hrange (chiA w)).norm
    have hev : ∀ᶠ m in atTop, ‖(U (chiA w)) m‖ < 1/2 := by
      have := hc.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1/2))
      exact this
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    obtain ⟨kk, hkkA, hkkN⟩ := (Aset_infinite w).exists_notMem_finset (Finset.range N)
    have hkkge : N ≤ kk := by
      by_contra hcon
      exact hkkN (Finset.mem_range.2 (by omega))
    refine ⟨kk, ?_⟩
    have h1 : (bv w) kk = 1 - (U (chiA w)) kk := by
      rw [hbvdef]
      simp only [coe_sub, Pi.sub_apply, chiA_apply, if_pos hkkA]
    rw [h1]
    have h2 := hN kk hkkge
    have := norm_sub_norm_le (1 : ℂ) ((U (chiA w)) kk)
    simp only [norm_one] at this
    linarith
  choose gk hgk using hkey
  -- some index is used by infinitely many branches
  obtain ⟨kidx, hkinf⟩ : ∃ kk : ℕ, {w : ℕ → Bool | gk w = kk}.Infinite := by
    by_contra hcon
    have hfin : ∀ kk : ℕ, {w : ℕ → Bool | gk w = kk}.Finite := by
      intro kk
      by_contra h2
      exact hcon ⟨kk, h2⟩
    have hcount : (Set.univ : Set (ℕ → Bool)).Countable := by
      have hun : (Set.univ : Set (ℕ → Bool)) ⊆ ⋃ kk, {w | gk w = kk} :=
        fun w _ => Set.mem_iUnion.2 ⟨gk w, rfl⟩
      exact Set.Countable.mono hun (Set.countable_iUnion (fun kk => (hfin kk).countable))
    exact not_countable_boolSeq (Set.countable_univ_iff.mp hcount)
  -- choose many branches with that index
  set n : ℕ := ⌈2 * (1 + C)⌉₊ + 1 with hndef
  obtain ⟨S, hSsub, hScard⟩ := hkinf.exists_subset_card_eq n
  have hgS : ∀ w ∈ S, gk w = kidx := fun w hw => hSsub hw
  have hbig : ∀ w ∈ S, (1:ℝ)/2 ≤ ‖bv w kidx‖ := by
    intro w hw
    have := hgk w
    rwa [hgS w hw] at this
  -- the rotated sum of indicators
  set cf : (ℕ → Bool) → ℂ := fun w => uu (bv w kidx) with hcfdef
  set x : ℕ →ᵇ ℂ := ∑ w ∈ S, cf w • chiA w with hxdef
  have hxapp : ∀ m, x m = ∑ w ∈ S, cf w * (if m ∈ Aset w then 1 else 0) := by
    intro m
    rw [hxdef, sum_apply]
    exact Finset.sum_congr rfl (fun w _ => by simp)
  -- the finite "overlap" set
  set Dset : Set ℕ := {m | ∃ w ∈ S, ∃ w' ∈ S, w ≠ w' ∧ m ∈ Aset w ∧ m ∈ Aset w'} with hDdef
  have hDfin : Dset.Finite := by
    set T : ((ℕ → Bool) × (ℕ → Bool)) → Set ℕ :=
      fun p => if p.1 = p.2 then (∅ : Set ℕ) else Aset p.1 ∩ Aset p.2 with hT
    have hbigfin :
        (⋃ p ∈ ((S ×ˢ S : Finset ((ℕ → Bool) × (ℕ → Bool))) : Set _), T p).Finite := by
      refine Set.Finite.biUnion (Finset.finite_toSet _) ?_
      intro p _
      by_cases hp : p.1 = p.2
      · simp [hT, hp]
      · simpa [hT, hp] using Aset_inter_finite hp
    refine Set.Finite.subset hbigfin ?_
    rintro m ⟨w, hw, w', hw', hne, hm1, hm2⟩
    refine Set.mem_biUnion (x := (w, w')) (by simpa using ⟨hw, hw'⟩) ?_
    simpa [hT, hne] using ⟨hm1, hm2⟩
  set D : Finset ℕ := hDfin.toFinset with hDfindef
  have hmemD : ∀ m, m ∈ D ↔ m ∈ Dset := fun m => by
    rw [hDfindef, Set.Finite.mem_toFinset]
  -- off `D`, the sum has at most one nonzero term
  have hxle : ∀ m, m ∉ D → ‖x m‖ ≤ 1 := by
    intro m hm
    rw [hxapp m]
    have hone : (S.filter (fun w => m ∈ Aset w)).card ≤ 1 := by
      refine Finset.card_le_one.2 (fun w hw w' hw' => ?_)
      simp only [Finset.mem_filter] at hw hw'
      by_contra hne
      exact hm ((hmemD m).2 ⟨w, hw.1, w', hw'.1, hne, hw.2, hw'.2⟩)
    have hsum : ∑ w ∈ S, cf w * (if m ∈ Aset w then 1 else 0)
        = ∑ w ∈ S.filter (fun w => m ∈ Aset w), cf w := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl (fun w _ => by split <;> simp)
    rw [hsum]
    calc ‖∑ w ∈ S.filter (fun w => m ∈ Aset w), cf w‖
        ≤ ∑ w ∈ S.filter (fun w => m ∈ Aset w), ‖cf w‖ := norm_sum_le _ _
      _ = (S.filter (fun w => m ∈ Aset w)).card := by
          simp [hcfdef, norm_uu]
      _ ≤ 1 := by exact_mod_cast hone
  -- split `x` into a small part and a finitely supported part
  have hybound : ∀ m, ‖(if m ∈ D then 0 else x m : ℂ)‖ ≤ 1 := by
    intro m
    by_cases h : m ∈ D
    · simp [h]
    · rw [if_neg h]; exact hxle m h
  have hzbound : ∀ m, ‖(if m ∈ D then x m else 0 : ℂ)‖ ≤ ‖x‖ := by
    intro m
    by_cases h : m ∈ D
    · rw [if_pos h]; exact x.norm_coe_le_norm m
    · rw [if_neg h]; simpa using norm_nonneg x
  set y : ℕ →ᵇ ℂ :=
    ofNormedAddCommGroupDiscrete (fun m => if m ∈ D then 0 else x m) 1 hybound with hydef
  set z : ℕ →ᵇ ℂ :=
    ofNormedAddCommGroupDiscrete (fun m => if m ∈ D then x m else 0) ‖x‖ hzbound with hzdef
  have hyapp : ∀ m, y m = if m ∈ D then 0 else x m := fun _ => rfl
  have hzapp : ∀ m, z m = if m ∈ D then x m else 0 := fun _ => rfl
  have hxyz : x = y + z := by
    ext m
    rw [coe_add, Pi.add_apply, hyapp, hzapp]
    split <;> simp
  have hynorm : ‖y‖ ≤ 1 := by
    refine (BoundedContinuousFunction.norm_le zero_le_one).2 (fun m => ?_)
    rw [hyapp]
    split
    · simp
    · exact hxle m ‹_›
  have hzc0 : z ∈ c0 := by
    rw [mem_c0]
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0:ℂ)))
    filter_upwards [eventually_ge_atTop (D.sup id + 1)] with m hm
    rw [hzapp, if_neg]
    intro hmD
    have := Finset.le_sup (f := id) hmD
    simp only [id] at this
    omega
  -- the deficiency vector of `x` equals that of `y`
  have hbdef : x - U x = y - U y := by
    rw [hxyz, map_add, hid z hzc0]
    abel
  have hbnorm : ‖x - U x‖ ≤ 1 + C := by rw [hbdef]; exact hdef y hynorm
  -- but it is large at `kidx`
  have hbval : (x - U x) kidx = ((∑ w ∈ S, ‖bv w kidx‖ : ℝ) : ℂ) := by
    have hsum : x - U x = ∑ w ∈ S, cf w • bv w := by
      rw [hxdef, map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [map_smul, hbvdef, smul_sub]
    rw [hsum, sum_apply]
    push_cast
    exact Finset.sum_congr rfl (fun w _ => by
      simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul, hcfdef]
      exact uu_mul _)
  have hlower : (n : ℝ) / 2 ≤ ‖(x - U x) kidx‖ := by
    rw [hbval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · calc (n : ℝ) / 2 = ∑ _w ∈ S, (1:ℝ)/2 := by
            rw [Finset.sum_const, hScard, nsmul_eq_mul]; ring
        _ ≤ ∑ w ∈ S, ‖bv w kidx‖ := Finset.sum_le_sum hbig
    · exact Finset.sum_nonneg (fun w _ => norm_nonneg _)
  have hupper : ‖(x - U x) kidx‖ ≤ 1 + C := le_trans ((x - U x).norm_coe_le_norm kidx) hbnorm
  have hnbig : 2 * (1 + C) < (n : ℝ) := by
    rw [hndef]
    push_cast
    have := Nat.le_ceil (2 * (1 + C))
    linarith
  linarith

end Q867
