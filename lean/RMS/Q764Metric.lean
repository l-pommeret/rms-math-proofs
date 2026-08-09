/-
# Q764 — Stage 2: the metric-space algorithms, with their operation counts

* `Q764.farthestFirstRun` — the scan-based farthest-first traversal, with
  `Q764.farthestFirstRun_spec` (it satisfies the `Q764.FarthestFirst` predicate),
  `Q764.farthestFirstRun_work_le` (`O(n*k)` unit-cost operations) and
  `Q764.farthestFirstAlgorithm_two_approx` (factor-`2` guarantee, obtained from the
  already compiled `Q764.FarthestFirst.covRad_le_two_mul`);
* `Q764.exhaustiveMetricRun` — the exact enumeration algorithm, with
  `Q764.exhaustiveMetric_correct` and `Q764.exhaustiveMetric_work_le`
  (`O((n choose k) * n * k)`).
-/
import RMS.Q764Bridge

open Finset

namespace Q764

variable {α : Type} [PseudoMetricSpace α] [DecidableEq α] [Inhabited α]

/-! ## Distances to the first `t+1` centers -/

lemma nd_zero (c : ℕ → α) (x : α) : nd c 0 x = dist x (c 0) := by
  simp [nd]

lemma nd_succ (c : ℕ → α) (t : ℕ) (x : α) :
    nd c (t + 1) x = min (nd c t x) (dist x (c (t + 1))) := by
  refine le_antisymm (le_min (nd_antitone c (Nat.le_succ t) x) (nd_le_dist c le_rfl x)) ?_
  refine Finset.le_inf' _ _ fun s hs => ?_
  have hs' : s ≤ t + 1 := by simpa [Nat.lt_succ_iff] using hs
  rcases eq_or_lt_of_le hs' with rfl | hlt
  · exact le_trans (min_le_right _ _) le_rfl
  · exact le_trans (min_le_left _ _) (nd_le_dist c (by omega) x)

lemma nd_congr {c c' : ℕ → α} {t : ℕ} (h : ∀ i ≤ t, c i = c' i) (x : α) :
    nd c t x = nd c' t x := by
  refine Finset.inf'_congr _ rfl fun i hi => ?_
  rw [h i (by simpa [Nat.lt_succ_iff] using hi)]

/-! ## The costed scans -/

/-- Scan for a point maximizing the stored distance to the centers chosen so far:
one read and one comparison per point. -/
noncomputable def argmaxScan (init : α × ℝ) (l : List (α × ℝ)) : Counted (α × ℝ) :=
  l.foldlM (fun best p => do
    let _ ← Counted.charge { reads := 1 }
    let b ← cmpLe best.2 p.2
    pure (if b then p else best)) init

lemma argmaxScan_mem (init : α × ℝ) (l : List (α × ℝ)) :
    (argmaxScan init l).value ∈ init :: l := by
  induction l generalizing init with
  | nil => simp [argmaxScan, List.foldlM]
  | cons a t ih =>
      have hstep : (argmaxScan init (a :: t)).value =
          (argmaxScan (if init.2 ≤ a.2 then a else init) t).value := by
        simp [argmaxScan, List.foldlM, Counted.bind, Counted.charge, cmpLe, Counted.ret]
      rw [hstep]
      have := ih (if init.2 ≤ a.2 then a else init)
      rcases List.mem_cons.1 this with h | h
      · rw [h]
        split_ifs with hc
        · exact List.mem_cons_of_mem _ (List.mem_cons_self)
        · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

lemma argmaxScan_ge (init : α × ℝ) (l : List (α × ℝ)) :
    ∀ p ∈ init :: l, p.2 ≤ (argmaxScan init l).value.2 := by
  induction l generalizing init with
  | nil => simp [argmaxScan, List.foldlM]
  | cons a t ih =>
      have hstep : (argmaxScan init (a :: t)).value =
          (argmaxScan (if init.2 ≤ a.2 then a else init) t).value := by
        simp [argmaxScan, List.foldlM, Counted.bind, Counted.charge, cmpLe, Counted.ret]
      intro p hp
      rw [hstep]
      have hkey : init.2 ≤ (if init.2 ≤ a.2 then a else init).2 ∧
          a.2 ≤ (if init.2 ≤ a.2 then a else init).2 := by
        split_ifs with hc
        · exact ⟨hc, le_rfl⟩
        · exact ⟨le_rfl, le_of_not_ge hc⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · exact le_trans hkey.1 (ih _ _ List.mem_cons_self)
      rcases List.mem_cons.1 hp with rfl | hp
      · exact le_trans hkey.2 (ih _ _ List.mem_cons_self)
      · exact ih _ p (List.mem_cons_of_mem _ hp)

lemma argmaxScan_work (init : α × ℝ) (l : List (α × ℝ)) :
    (argmaxScan init l).ops.work ≤ 2 * l.length := by
  refine foldlM_ops_work_le _ 2 (fun best p => ?_) l init
  simp [Counted.bind, Counted.charge, cmpLe, Counted.ret, OpCount.work, OpCount.add_eq,
    OpCount.plus]

/-- Recompute the nearest-center distances after adding the center `c`: one distance
query, one comparison and one write per point. -/
noncomputable def updateScan (c : α) (l : List (α × ℝ)) : Counted (List (α × ℝ)) :=
  l.foldlM (fun acc p => do
    let dv ← distQuery (fun a b => dist a b) p.1 c
    let b ← cmpLe dv p.2
    let _ ← Counted.charge { writes := 1 }
    pure (acc ++ [(p.1, if b then dv else p.2)])) []

lemma updateScan_aux (c : α) (l : List (α × ℝ)) (acc : List (α × ℝ)) :
    (l.foldlM (fun acc p => do
      let dv ← distQuery (fun a b => dist a b) p.1 c
      let b ← cmpLe dv p.2
      let _ ← Counted.charge { writes := 1 }
      pure (acc ++ [(p.1, if b then dv else p.2)])) acc : Counted (List (α × ℝ))).value
      = acc ++ l.map (fun p => (p.1, min p.2 (dist p.1 c))) := by
  induction l generalizing acc with
  | nil => simp [List.foldlM]
  | cons a t ih =>
      have : ((a :: t).foldlM (fun acc p => do
          let dv ← distQuery (fun a b => dist a b) p.1 c
          let b ← cmpLe dv p.2
          let _ ← Counted.charge { writes := 1 }
          pure (acc ++ [(p.1, if b then dv else p.2)])) acc : Counted (List (α × ℝ))).value
          = (t.foldlM (fun acc p => do
          let dv ← distQuery (fun a b => dist a b) p.1 c
          let b ← cmpLe dv p.2
          let _ ← Counted.charge { writes := 1 }
          pure (acc ++ [(p.1, if b then dv else p.2)]))
            (acc ++ [(a.1, if dist a.1 c ≤ a.2 then dist a.1 c else a.2)]) :
              Counted (List (α × ℝ))).value := by
        simp [List.foldlM, Counted.bind, Counted.charge, cmpLe, distQuery, Counted.ret]
      rw [this, ih]
      rcases le_total (dist a.1 c) a.2 with h | h
      · simp [h, min_eq_right h, List.append_assoc]
      · rcases eq_or_lt_of_le h with h' | h'
        · simp [h', min_eq_left h, List.append_assoc]
        · simp [not_le.2 h', min_eq_left h, List.append_assoc]

lemma updateScan_value (c : α) (l : List (α × ℝ)) :
    (updateScan c l).value = l.map (fun p => (p.1, min p.2 (dist p.1 c))) := by
  have := updateScan_aux c l []
  simpa [updateScan] using this

lemma updateScan_work (c : α) (l : List (α × ℝ)) :
    (updateScan c l).ops.work ≤ 3 * l.length := by
  refine foldlM_ops_work_le _ 3 (fun acc p => ?_) l []
  simp [Counted.bind, Counted.charge, cmpLe, distQuery, Counted.ret, OpCount.work,
    OpCount.add_eq, OpCount.plus]

/-- The distances to the first center: one distance query and one write per point. -/
noncomputable def initScan (c : α) (pts : List α) : Counted (List (α × ℝ)) :=
  pts.foldlM (fun acc x => do
    let dv ← distQuery (fun a b => dist a b) x c
    let _ ← Counted.charge { writes := 1 }
    pure (acc ++ [(x, dv)])) []

lemma initScan_aux (c : α) (pts : List α) (acc : List (α × ℝ)) :
    (pts.foldlM (fun acc x => do
      let dv ← distQuery (fun a b => dist a b) x c
      let _ ← Counted.charge { writes := 1 }
      pure (acc ++ [(x, dv)])) acc : Counted (List (α × ℝ))).value
      = acc ++ pts.map (fun x => (x, dist x c)) := by
  induction pts generalizing acc with
  | nil => simp [List.foldlM]
  | cons a t ih =>
      have : ((a :: t).foldlM (fun acc x => do
          let dv ← distQuery (fun a b => dist a b) x c
          let _ ← Counted.charge { writes := 1 }
          pure (acc ++ [(x, dv)])) acc : Counted (List (α × ℝ))).value
          = (t.foldlM (fun acc x => do
          let dv ← distQuery (fun a b => dist a b) x c
          let _ ← Counted.charge { writes := 1 }
          pure (acc ++ [(x, dv)])) (acc ++ [(a, dist a c)]) : Counted (List (α × ℝ))).value := by
        simp [List.foldlM, Counted.bind, Counted.charge, distQuery, Counted.ret]
      rw [this, ih]
      simp [List.append_assoc]

lemma initScan_value (c : α) (pts : List α) :
    (initScan c pts).value = pts.map (fun x => (x, dist x c)) := by
  have := initScan_aux c pts []
  simpa [initScan] using this

lemma initScan_work (c : α) (pts : List α) : (initScan c pts).ops.work ≤ 2 * pts.length := by
  refine foldlM_ops_work_le _ 2 (fun acc x => ?_) pts []
  simp [Counted.bind, Counted.charge, distQuery, Counted.ret, OpCount.work, OpCount.add_eq,
    OpCount.plus]

/-! ## The farthest-first traversal -/

lemma headI_append_ne {l : List α} (hl : l ≠ []) (m : List α) : (l ++ m).headI = l.headI := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => simp

lemma cons_headI_tail {l : List α} (hl : l ≠ []) : l.headI :: l.tail = l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => simp

lemma headI_mem_ne {l : List α} (hl : l ≠ []) : l.headI ∈ l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => simp

lemma getD_mem_of_lt {l : List α} {i : ℕ} (hi : i < l.length) (d : α) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simpa using List.getElem_mem hi

/-- The center function attached to the list of chosen centers. -/
noncomputable def cOf (l : List α) : ℕ → α := fun i => l.getD i l.headI

lemma cOf_append_lt {l : List α} (hl : l ≠ []) (b : α) {i : ℕ} (hi : i < l.length) :
    cOf (l ++ [b]) i = cOf l i := by
  simp only [cOf, headI_append_ne hl]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma cOf_append_len {l : List α} (hl : l ≠ []) (b : α) :
    cOf (l ++ [b]) l.length = b := by
  simp only [cOf, headI_append_ne hl]
  rw [List.getD_eq_getElem?_getD]
  simp

/-- One step: choose a farthest point and refresh the nearest-center distances. -/
noncomputable def ffStep (s : List α × List (α × ℝ)) : Counted (List α × List (α × ℝ)) := do
  let best ← argmaxScan s.2.headI s.2.tail
  let v ← updateScan best.1 s.2
  pure (s.1 ++ [best.1], v)

/-- `m` steps of the traversal. -/
noncomputable def ffIter : ℕ → (List α × List (α × ℝ)) → Counted (List α × List (α × ℝ))
  | 0, s => pure s
  | (m + 1), s => do
      let s' ← ffStep s
      ffIter m s'

/-- The complete costed farthest-first run: the first center is the first point, and each
later center is obtained by a full scan for a point farthest from the chosen centers. -/
noncomputable def farthestFirstRun (pts : List α) (k : ℕ) : Counted (List α) := do
  let _ ← Counted.charge { reads := 1 }
  let v0 ← initScan pts.headI pts
  let s ← ffIter (k - 1) ([pts.headI], v0)
  pure s.1

/-- The loop invariant of the traversal. -/
structure FFInv (pts : List α) (s : List α × List (α × ℝ)) : Prop where
  ne : s.1 ≠ []
  mem : ∀ c ∈ s.1, c ∈ pts
  vals : s.2 = pts.map fun x => (x, nd (cOf s.1) (s.1.length - 1) x)
  greedy : ∀ t, t + 1 < s.1.length → ∀ x ∈ pts,
    nd (cOf s.1) t x ≤ nd (cOf s.1) t (cOf s.1 (t + 1))

lemma ffStep_fst (s : List α × List (α × ℝ)) :
    (ffStep s).value.1 = s.1 ++ [(argmaxScan s.2.headI s.2.tail).value.1] := by
  simp [ffStep, Counted.bind]

lemma ffStep_inv {pts : List α} (hpts : pts ≠ []) {s : List α × List (α × ℝ)}
    (h : FFInv pts s) : FFInv pts (ffStep s).value := by
  set c := cOf s.1 with hc
  set t := s.1.length - 1 with ht
  have hlen : s.1.length = t + 1 := by
    have := List.length_pos_iff.2 h.ne; omega
  have hs2 : s.2 = pts.map fun x => (x, nd c t x) := h.vals
  have hs2ne : s.2 ≠ [] := by
    rw [hs2]; simpa using hpts
  have hcons : s.2.headI :: s.2.tail = s.2 := cons_headI_tail hs2ne
  set best := (argmaxScan s.2.headI s.2.tail).value with hbest
  have hbmem : best ∈ s.2 := by
    have := argmaxScan_mem s.2.headI s.2.tail
    rwa [hcons] at this
  have hbge : ∀ p ∈ s.2, p.2 ≤ best.2 := by
    intro p hp
    have := argmaxScan_ge s.2.headI s.2.tail
    rw [hcons] at this
    exact this p hp
  -- the chosen point and its stored value
  obtain ⟨y, hy, hyeq⟩ : ∃ y ∈ pts, best = (y, nd c t y) := by
    rw [hs2] at hbmem
    obtain ⟨y, hy, hyeq⟩ := List.mem_map.1 hbmem
    exact ⟨y, hy, hyeq.symm⟩
  have hbfst : best.1 = y := by rw [hyeq]
  have hbsnd : best.2 = nd c t y := by rw [hyeq]
  have hnew1 : (ffStep s).value.1 = s.1 ++ [best.1] := ffStep_fst s
  have hnewlen : (ffStep s).value.1.length = t + 2 := by
    rw [hnew1]; simp [hlen]
  have hc' : ∀ i < s.1.length, cOf (ffStep s).value.1 i = c i := by
    intro i hi
    rw [hnew1]
    exact cOf_append_lt h.ne _ hi
  have hc'top : cOf (ffStep s).value.1 (t + 1) = best.1 := by
    rw [hnew1]
    have := cOf_append_len h.ne best.1
    rwa [hlen] at this
  have hndagree : ∀ (u : ℕ), u ≤ t → ∀ x : α, nd (cOf (ffStep s).value.1) u x = nd c u x := by
    intro u hu x
    exact nd_congr (fun i hi => hc' i (by omega)) x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hnew1]; simp
  · intro z hz
    rw [hnew1] at hz
    rcases List.mem_append.1 hz with hz | hz
    · exact h.mem z hz
    · have : z = best.1 := by simpa using hz
      rw [this, hbfst]; exact hy
  · have hv : (ffStep s).value.2 = (updateScan best.1 s.2).value := by
      simp only [ffStep, Counted.bind_value, Counted.pure_value, hbest]
    rw [hv, updateScan_value, hs2, hnewlen]
    simp only [List.map_map, Function.comp_def]
    refine List.map_congr_left fun x hx => ?_
    have : t + 2 - 1 = t + 1 := by omega
    rw [this]
    have := nd_succ (cOf (ffStep s).value.1) t x
    rw [hc'top] at this
    rw [this, hndagree t le_rfl x]
  · intro u hu x hx
    rw [hnewlen] at hu
    rcases Nat.lt_or_ge u t with hut | hut
    · have h1 := h.greedy u (by omega) x hx
      rw [hndagree u (by omega) x, hndagree u (by omega) _]
      have : cOf (ffStep s).value.1 (u + 1) = c (u + 1) := hc' (u + 1) (by omega)
      rw [this]
      exact h1
    · have hut' : u = t := by omega
      rw [hut', hndagree t le_rfl x, hc'top, hndagree t le_rfl best.1, hbfst]
      have hmem2 := hbge (x, nd c t x) (by rw [hs2]; exact List.mem_map_of_mem hx)
      rw [hbsnd] at hmem2
      exact hmem2

lemma ffIter_inv {pts : List α} (hpts : pts ≠ []) :
    ∀ (m : ℕ) (s : List α × List (α × ℝ)), FFInv pts s →
      FFInv pts (ffIter m s).value ∧ (ffIter m s).value.1.length = s.1.length + m := by
  intro m
  induction m with
  | zero => intro s hs; exact ⟨hs, by simp [ffIter]⟩
  | succ m ih =>
      intro s hs
      have hstep := ffStep_inv hpts hs
      have hval : (ffIter (m + 1) s).value = (ffIter m (ffStep s).value).value := by
        simp [ffIter, Counted.bind]
      have hlen : (ffStep s).value.1.length = s.1.length + 1 := by
        rw [ffStep_fst]; simp
      obtain ⟨h1, h2⟩ := ih (ffStep s).value hstep
      refine ⟨by rw [hval]; exact h1, ?_⟩
      rw [hval, h2, hlen]
      omega

lemma farthestFirstRun_inv {pts : List α} (hpts : pts ≠ []) {k : ℕ} (hk : 1 ≤ k) :
    FFInv pts (ffIter (k - 1) ([pts.headI], (initScan pts.headI pts).value)).value ∧
      (ffIter (k - 1) ([pts.headI], (initScan pts.headI pts).value)).value.1.length = k := by
  have hinit : FFInv pts ([pts.headI], (initScan pts.headI pts).value) := by
    refine ⟨by simp, ?_, ?_, ?_⟩
    · intro c hc
      have : c = pts.headI := by simpa using hc
      rw [this]
      exact headI_mem_ne hpts
    · rw [initScan_value]
      refine List.map_congr_left fun x hx => ?_
      simp only [List.length_singleton]
      rw [nd_zero]
      rfl
    · intro t ht
      simp at ht
  obtain ⟨h1, h2⟩ := ffIter_inv hpts (k - 1) _ hinit
  refine ⟨h1, ?_⟩
  rw [h2]
  simp only [List.length_singleton]
  omega

/-- **The costed farthest-first run satisfies the `FarthestFirst` specification.** -/
theorem farthestFirstRun_spec {pts : List α} (hpts : pts ≠ []) {k : ℕ} (hk : 1 ≤ k) :
    FarthestFirst pts.toFinset k (cOf (farthestFirstRun pts k).value) ∧
      (farthestFirstRun pts k).value.length = k ∧
      ∀ c ∈ (farthestFirstRun pts k).value, c ∈ pts := by
  obtain ⟨hinv, hlen⟩ := farthestFirstRun_inv hpts hk
  have hval : (farthestFirstRun pts k).value =
      (ffIter (k - 1) ([pts.headI], (initScan pts.headI pts).value)).value.1 := by
    simp [farthestFirstRun, Counted.bind]
  refine ⟨⟨?_, ?_⟩, by rw [hval]; exact hlen, ?_⟩
  · intro i hi
    rw [List.mem_toFinset]
    rw [hval]
    refine hinv.mem _ ?_
    have : i < (ffIter (k - 1) ([pts.headI], (initScan pts.headI pts).value)).value.1.length := by
      rw [hlen]; exact hi
    exact getD_mem_of_lt this _
  · intro t htk x hx
    rw [hval]
    refine hinv.greedy t (by rw [hlen]; exact htk) x (List.mem_toFinset.1 hx)
  · intro c hc
    rw [hval] at hc
    exact hinv.mem c hc

/-! ### The `O(n*k)` cost of the traversal -/

lemma ffStep_snd_length (s : List α × List (α × ℝ)) :
    (ffStep s).value.2.length = s.2.length := by
  have : (ffStep s).value.2 = (updateScan (argmaxScan s.2.headI s.2.tail).value.1 s.2).value := by
    simp only [ffStep, Counted.bind_value, Counted.pure_value]
  rw [this, updateScan_value]
  simp

lemma ffStep_work (s : List α × List (α × ℝ)) : (ffStep s).ops.work ≤ 5 * s.2.length := by
  have hops : (ffStep s).ops = (argmaxScan s.2.headI s.2.tail).ops +
      ((updateScan (argmaxScan s.2.headI s.2.tail).value.1 s.2).ops + 0) := by
    simp only [ffStep, Counted.bind_ops, Counted.pure_ops]
  rw [hops]
  simp only [OpCount.add_work, OpCount.work_zero, Nat.add_zero]
  have h1 := argmaxScan_work s.2.headI s.2.tail
  have h2 := updateScan_work (argmaxScan s.2.headI s.2.tail).value.1 s.2
  have h3 : s.2.tail.length ≤ s.2.length := by simp [List.length_tail]
  omega

lemma ffIter_work (n : ℕ) : ∀ (m : ℕ) (s : List α × List (α × ℝ)), s.2.length = n →
    (ffIter m s).ops.work ≤ 5 * n * m := by
  intro m
  induction m with
  | zero => intro s _; simp [ffIter]
  | succ m ih =>
      intro s hs
      have hops : (ffIter (m + 1) s).ops = (ffStep s).ops + (ffIter m (ffStep s).value).ops := by
        simp only [ffIter, Counted.bind_ops]
      rw [hops]
      simp only [OpCount.add_work]
      have h1 := ffStep_work s
      have h2 := ih (ffStep s).value (by rw [ffStep_snd_length, hs])
      rw [hs] at h1
      have : 5 * n + 5 * n * m = 5 * n * (m + 1) := by ring
      omega

/-- **The farthest-first run performs `O(n*k)` unit-cost operations.** -/
theorem farthestFirstRun_work_le {pts : List α} (hpts : pts ≠ []) {k : ℕ} (hk : 1 ≤ k) :
    (farthestFirstRun pts k).ops.work ≤ 5 * pts.length * k := by
  have hops : (farthestFirstRun pts k).ops =
      ({ reads := 1 } : OpCount) + ((initScan pts.headI pts).ops +
        ((ffIter (k - 1) ([pts.headI], (initScan pts.headI pts).value)).ops + 0)) := by
    simp only [farthestFirstRun, Counted.bind_ops, Counted.pure_ops, Counted.charge_ops]
  rw [hops]
  simp only [OpCount.add_work, OpCount.work_zero, Nat.add_zero]
  have h1 := initScan_work pts.headI pts
  have h2 := ffIter_work (α := α) pts.length (k - 1) ([pts.headI], (initScan pts.headI pts).value)
    (by rw [initScan_value]; simp)
  have hn : 1 ≤ pts.length := List.length_pos_iff.2 hpts
  have hw : ({ reads := 1 } : OpCount).work = 1 := by simp [OpCount.work]
  rw [hw]
  have : 5 * pts.length * (k - 1) + 5 * pts.length = 5 * pts.length * k := by
    have : k - 1 + 1 = k := by omega
    calc 5 * pts.length * (k - 1) + 5 * pts.length = 5 * pts.length * (k - 1 + 1) := by ring
      _ = 5 * pts.length * k := by rw [this]
  omega

/-! ### Padding the centers to exactly `k` points -/

/-- Membership test by a scan. -/
def memScan (x : α) (l : List α) : Counted Bool :=
  l.foldlM (fun found y => do
    let _ ← Counted.charge { reads := 1, comparisons := 1 }
    pure (found || decide (y = x))) false

lemma memScan_aux (x : α) (l : List α) (b : Bool) :
    (l.foldlM (fun found y => do
      let _ ← Counted.charge { reads := 1, comparisons := 1 }
      pure (found || decide (y = x))) b : Counted Bool).value = (b || decide (x ∈ l)) := by
  induction l generalizing b with
  | nil => simp [List.foldlM]
  | cons a t ih =>
      have hrw : ((a :: t).foldlM (fun found y => do
          let _ ← Counted.charge { reads := 1, comparisons := 1 }
          pure (found || decide (y = x))) b : Counted Bool).value
          = (t.foldlM (fun found y => do
          let _ ← Counted.charge { reads := 1, comparisons := 1 }
          pure (found || decide (y = x))) (b || decide (a = x)) : Counted Bool).value := by
        simp [List.foldlM, Counted.bind, Counted.charge]
      rw [hrw, ih]
      by_cases h : a = x
      · subst h; simp
      · have hx : ¬ (x = a) := fun hh => h hh.symm
        simp [List.mem_cons, h, hx, Bool.or_assoc]

lemma memScan_value (x : α) (l : List α) : (memScan x l).value = decide (x ∈ l) := by
  have := memScan_aux x l false
  simpa [memScan] using this

lemma memScan_work (x : α) (l : List α) : (memScan x l).ops.work ≤ 2 * l.length := by
  refine foldlM_ops_work_le _ 2 (fun b y => ?_) l false
  simp [Counted.bind, Counted.charge, OpCount.work, OpCount.add_eq, OpCount.plus]

/-- The pure padding function: keep the first `k` distinct points met. -/
def padList (k : ℕ) : List α → List α → List α
  | [], acc => acc
  | (x :: t), acc => padList k t (if acc.length < k ∧ x ∉ acc then acc ++ [x] else acc)

lemma padList_append (k : ℕ) (l₁ l₂ : List α) (acc : List α) :
    padList k (l₁ ++ l₂) acc = padList k l₂ (padList k l₁ acc) := by
  induction l₁ generalizing acc with
  | nil => simp [padList]
  | cons a t ih => simp [padList, ih]

lemma padList_props (k : ℕ) : ∀ (l acc : List α), acc.Nodup → acc.length ≤ k →
    (padList k l acc).Nodup ∧ (padList k l acc).length ≤ k ∧
      acc <+: (padList k l acc) ∧ (∀ y ∈ padList k l acc, y ∈ acc ∨ y ∈ l) ∧
      ((padList k l acc).length = k ∨ ∀ y ∈ l, y ∈ padList k l acc) := by
  intro l
  induction l with
  | nil =>
      intro acc h1 h2
      exact ⟨h1, h2, List.prefix_rfl, fun y hy => Or.inl hy, Or.inr (by simp)⟩
  | cons x t ih =>
      intro acc h1 h2
      set acc' := if acc.length < k ∧ x ∉ acc then acc ++ [x] else acc with hacc'
      have hpre : acc <+: acc' := by
        rw [hacc']
        split_ifs with h
        · exact List.prefix_append _ _
        · exact List.prefix_rfl
      have hnd' : acc'.Nodup := by
        rw [hacc']
        split_ifs with h
        · rw [List.nodup_append']
          exact ⟨h1, by simp, by simpa using h.2⟩
        · exact h1
      have hlen' : acc'.length ≤ k := by
        rw [hacc']
        split_ifs with h
        · simp only [List.length_append, List.length_singleton]
          omega
        · exact h2
      obtain ⟨p1, p2, p3, p4, p5⟩ := ih acc' hnd' hlen'
      have hstep : padList k (x :: t) acc = padList k t acc' := rfl
      rw [hstep]
      refine ⟨p1, p2, hpre.trans p3, ?_, ?_⟩
      · intro y hy
        rcases p4 y hy with hy' | hy'
        · rw [hacc'] at hy'
          split_ifs at hy' with h
          · rcases List.mem_append.1 hy' with hy'' | hy''
            · exact Or.inl hy''
            · right; simp at hy''; simp [hy'']
          · exact Or.inl hy'
        · exact Or.inr (List.mem_cons_of_mem _ hy')
      · rcases p5 with hfull | hall
        · exact Or.inl hfull
        · by_cases hfull : (padList k t acc').length = k
          · exact Or.inl hfull
          · right
            intro y hy
            rcases List.mem_cons.1 hy with rfl | hy
            · -- `y = x` was inserted, unless `acc` was already full
              have hxacc' : y ∈ acc' := by
                rw [hacc']
                by_cases h : acc.length < k ∧ y ∉ acc
                · simp [h]
                · simp only [h, if_false]
                  by_cases hy' : y ∈ acc
                  · exact hy'
                  · exfalso
                    have hfullacc : acc.length = k := by
                      rcases not_and_or.1 h with h' | h'
                      · omega
                      · exact absurd hy' h'
                    have : acc'.length = k := by rw [hacc']; simp [h, hfullacc]
                    have hle := p3.length_le
                    omega
              exact p3.subset hxacc'
            · exact hall y hy

/-- The costed padding: scan the centers and then the points, keeping the first `k`
distinct ones. -/
def padRun (k : ℕ) (cs pts : List α) : Counted (List α) :=
  (cs ++ pts).foldlM (fun acc x => do
    let b ← memScan x acc
    let _ ← Counted.charge { comparisons := 1 }
    pure (if acc.length < k ∧ b = false then acc ++ [x] else acc)) []

lemma padRun_aux (k : ℕ) (l : List α) (acc : List α) :
    (l.foldlM (fun acc x => do
      let b ← memScan x acc
      let _ ← Counted.charge { comparisons := 1 }
      pure (if acc.length < k ∧ b = false then acc ++ [x] else acc)) acc :
        Counted (List α)).value = padList k l acc := by
  induction l generalizing acc with
  | nil => simp [List.foldlM, padList]
  | cons a t ih =>
      have hrw : ((a :: t).foldlM (fun acc x => do
          let b ← memScan x acc
          let _ ← Counted.charge { comparisons := 1 }
          pure (if acc.length < k ∧ b = false then acc ++ [x] else acc)) acc :
            Counted (List α)).value
          = (t.foldlM (fun acc x => do
          let b ← memScan x acc
          let _ ← Counted.charge { comparisons := 1 }
          pure (if acc.length < k ∧ b = false then acc ++ [x] else acc))
            (if acc.length < k ∧ (memScan a acc).value = false then acc ++ [a] else acc) :
              Counted (List α)).value := by
        simp [List.foldlM, Counted.bind, Counted.charge]
      have hacc : (if acc.length < k ∧ (memScan a acc).value = false then acc ++ [a] else acc)
          = (if acc.length < k ∧ a ∉ acc then acc ++ [a] else acc) := by
        rw [memScan_value]
        by_cases h : a ∈ acc <;> simp [h]
      rw [hrw, hacc, ih]
      rfl

lemma padRun_value (k : ℕ) (cs pts : List α) :
    (padRun k cs pts).value = padList k (cs ++ pts) [] := padRun_aux k (cs ++ pts) []

lemma padRun_work (k : ℕ) (cs pts : List α) :
    (padRun k cs pts).ops.work ≤ (2 * k + 1) * (cs.length + pts.length) := by
  have := foldlM_ops_work_le_inv
    (f := fun (acc : List α) (x : α) => do
      let b ← memScan x acc
      let _ ← Counted.charge { comparisons := 1 }
      pure (if acc.length < k ∧ b = false then acc ++ [x] else acc))
    (P := fun acc => acc.length ≤ k) (C := 2 * k + 1) ?_ ?_ (cs ++ pts) [] (by simp)
  · simpa [padRun] using this
  · intro acc x hacc
    simp only [Counted.bind_value, Counted.pure_value]
    split_ifs with h
    · simp only [List.length_append, List.length_singleton]; omega
    · exact hacc
  · intro acc x hacc
    simp only [Counted.bind_ops, Counted.pure_ops, Counted.charge_ops, OpCount.add_work,
      OpCount.work_zero, Nat.add_zero]
    have h1 := memScan_work x acc
    have h2 : ({ comparisons := 1 } : OpCount).work = 1 := by simp [OpCount.work]
    omega

/-! ### The complete farthest-first algorithm -/

/-- The farthest-first algorithm: run the traversal, then pad the chosen centers with
unused points so that exactly `k` centers are returned. -/
noncomputable def farthestFirstAlgorithm (pts : List α) (k : ℕ) : Counted (List α) := do
  let cs ← farthestFirstRun pts k
  padRun k cs pts

lemma image_cOf_eq_toFinset {cs : List α} {k : ℕ} (hlen : cs.length = k) :
    (range k).image (cOf cs) = cs.toFinset := by
  ext y
  simp only [Finset.mem_image, Finset.mem_range, List.mem_toFinset]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact getD_mem_of_lt (by omega) _
  · intro hy
    obtain ⟨i, hi, hval⟩ := List.getElem_of_mem hy
    refine ⟨i, by omega, ?_⟩
    simp only [cOf]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simpa using hval

/-- **The whole farthest-first algorithm still runs in `O(n*k)` unit-cost operations.** -/
theorem farthestFirstAlgorithm_work_le {pts : List α} (hne : pts ≠ []) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ pts.length) :
    (farthestFirstAlgorithm pts k).ops.work ≤ 11 * pts.length * k := by
  have hops : (farthestFirstAlgorithm pts k).ops =
      (farthestFirstRun pts k).ops + (padRun k (farthestFirstRun pts k).value pts).ops := by
    simp only [farthestFirstAlgorithm, Counted.bind_ops]
  rw [hops]
  simp only [OpCount.add_work]
  have h1 := farthestFirstRun_work_le hne hk
  have h2 := padRun_work k (farthestFirstRun pts k).value pts
  obtain ⟨-, hcslen, -⟩ := farthestFirstRun_spec hne hk
  rw [hcslen] at h2
  have hn : 1 ≤ pts.length := List.length_pos_iff.2 hne
  have hb : (2 * k + 1) * (k + pts.length) ≤ 6 * pts.length * k := by
    have h3 : k + pts.length ≤ 2 * pts.length := by omega
    calc (2 * k + 1) * (k + pts.length) ≤ (2 * k + 1) * (2 * pts.length) :=
          Nat.mul_le_mul_left _ h3
      _ = 4 * pts.length * k + 2 * pts.length := by ring
      _ ≤ 4 * pts.length * k + 2 * pts.length * k := by
          have : 2 * pts.length ≤ 2 * pts.length * k := by
            calc 2 * pts.length = 2 * pts.length * 1 := by ring
              _ ≤ 2 * pts.length * k := Nat.mul_le_mul_left _ hk
          omega
      _ = 6 * pts.length * k := by ring
  calc (farthestFirstRun pts k).ops.work + (padRun k (farthestFirstRun pts k).value pts).ops.work
      ≤ 5 * pts.length * k + (2 * k + 1) * (k + pts.length) := Nat.add_le_add h1 h2
    _ ≤ 5 * pts.length * k + 6 * pts.length * k := Nat.add_le_add_left hb _
    _ = 11 * pts.length * k := by ring

/-- **The farthest-first algorithm returns exactly `k` centers, all input points, whose
covering radius is at most twice the optimum.** -/
theorem farthestFirstAlgorithm_two_approx {pts : List α} (hnd : pts.Nodup) (hne : pts ≠ [])
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ pts.length) :
    ((farthestFirstAlgorithm pts k).value.toFinset.card = k) ∧
      (farthestFirstAlgorithm pts k).value.toFinset ⊆ pts.toFinset ∧
      covRad' pts.toFinset (farthestFirstAlgorithm pts k).value.toFinset ≤
        2 * optimalRadius pts.toFinset k := by
  set cs := (farthestFirstRun pts k).value with hcs
  obtain ⟨hff, hcslen, hcsmem⟩ := farthestFirstRun_spec hne hk
  set res := (farthestFirstAlgorithm pts k).value with hres
  have hresval : res = padList k (cs ++ pts) [] := by
    rw [hres, farthestFirstAlgorithm]
    simp only [Counted.bind_value]
    exact padRun_value k cs pts
  obtain ⟨hnd', hlen', -, hmem', hfull⟩ := padList_props k (cs ++ pts) [] (by simp) (by simp)
  rw [← hresval] at hnd' hlen' hmem' hfull
  -- every returned centre is an input point
  have hsub : res.toFinset ⊆ pts.toFinset := by
    intro y hy
    rw [List.mem_toFinset] at hy ⊢
    rcases hmem' y hy with h | h
    · exact absurd h (by simp)
    · rcases List.mem_append.1 h with h | h
      · exact hcsmem y h
      · exact h
  have hcard : res.toFinset.card = res.length := by
    rw [List.toFinset_card_of_nodup hnd']
  have hptscard : pts.toFinset.card = pts.length := List.toFinset_card_of_nodup hnd
  -- exactly `k` centres
  have hreslen : res.length = k := by
    rcases hfull with h | h
    · exact h
    · have hpts_sub : pts.toFinset ⊆ res.toFinset := by
        intro y hy
        rw [List.mem_toFinset] at hy ⊢
        exact h y (List.mem_append_right _ hy)
      have := Finset.card_le_card hpts_sub
      rw [hcard, hptscard] at this
      omega
  -- the traversal centres are among the returned ones
  have hcs_sub : cs.toFinset ⊆ res.toFinset := by
    have hsplit : padList k (cs ++ pts) [] = padList k pts (padList k cs []) :=
      padList_append k cs pts []
    obtain ⟨n1, n2, n3, n4, n5⟩ := padList_props k cs ([] : List α) (by simp) (by simp)
    obtain ⟨-, -, m3, -, -⟩ := padList_props k pts (padList k cs []) n1 n2
    have hAsub : (padList k cs []).toFinset ⊆ res.toFinset := by
      intro y hy
      rw [List.mem_toFinset] at hy ⊢
      rw [hresval, hsplit]
      exact m3.subset hy
    refine subset_trans ?_ hAsub
    intro y hy
    rw [List.mem_toFinset] at hy ⊢
    rcases n5 with hfullA | hallA
    · -- `A` is already full, hence equal to the set of centres
      have hAsubcs : (padList k cs []).toFinset ⊆ cs.toFinset := by
        intro z hz
        rw [List.mem_toFinset] at hz ⊢
        rcases n4 z hz with h | h
        · exact absurd h (by simp)
        · exact h
      have hcardA : (padList k cs []).toFinset.card = k := by
        rw [List.toFinset_card_of_nodup n1, hfullA]
      have hcslen' : cs.length = k := hcslen
      have hcardcs : cs.toFinset.card ≤ k := by
        have := List.toFinset_card_le cs
        omega
      have : (padList k cs []).toFinset = cs.toFinset :=
        Finset.eq_of_subset_of_card_le hAsubcs (by omega)
      rw [← List.mem_toFinset, this, List.mem_toFinset]
      exact hy
    · exact hallA y hy
  refine ⟨by rw [hcard, hreslen], hsub, ?_⟩
  -- the factor-2 guarantee, from the compiled `FarthestFirst.covRad_le_two_mul`
  have hX : pts.toFinset.Nonempty := (List.toFinset_nonempty_iff pts).2 hne
  obtain ⟨F, hFsub, hFcard, hFval, -⟩ :=
    optimalRadius_attained (X := pts.toFinset) (k := k) (by rw [hptscard]; exact hkn)
  have hFne : F.Nonempty := Finset.card_pos.1 (by omega)
  have hcslen' : cs.length = k := hcslen
  have hGeq : (range k).image (cOf cs) = cs.toFinset := image_cOf_eq_toFinset hcslen'
  have hGne : ((range k).image (cOf cs)).Nonempty := by
    rw [hGeq]
    refine (List.toFinset_nonempty_iff cs).2 ?_
    intro hcsnil
    rw [hcsnil] at hcslen'
    simp only [List.length_nil] at hcslen'
    omega
  have hff' : FarthestFirst pts.toFinset k (cOf cs) := hff
  have hkey := FarthestFirst.covRad_le_two_mul (X := pts.toFinset) (k := k) (c := cOf cs)
    (by omega) hff' hX hGne hFne (le_of_eq hFcard)
  have hGne' : cs.toFinset.Nonempty := by rw [← hGeq]; exact hGne
  calc covRad' pts.toFinset res.toFinset
      ≤ covRad' pts.toFinset cs.toFinset := covRad'_mono hGne' hcs_sub
    _ = covRad pts.toFinset ((range k).image (cOf cs)) hX hGne := by
        rw [covRad'_eq_covRad hX hGne']
        congr 1
        exact hGeq.symm
    _ ≤ 2 * covRad pts.toFinset F hX hFne := hkey
    _ = 2 * optimalRadius pts.toFinset k := by
        rw [← covRad'_eq_covRad hX hFne, hFval]

/-! ## The exhaustive algorithm on an arbitrary finite metric space -/

/-- Scan of the centers for the one nearest to `x`. -/
noncomputable def minDistScan (x : α) (F : List α) : Counted ℝ := do
  let d0 ← distQuery (fun a b => dist a b) x F.headI
  F.tail.foldlM (fun acc c => do
    let dv ← distQuery (fun a b => dist a b) x c
    let b ← cmpLe dv acc
    pure (if b then dv else acc)) d0

lemma minDistScan_aux (x : α) (l : List α) (a : ℝ) :
    ((l.foldlM (fun acc c => do
      let dv ← distQuery (fun a b => dist a b) x c
      let b ← cmpLe dv acc
      pure (if b then dv else acc)) a : Counted ℝ).value ∈ a :: l.map (fun c => dist x c)) ∧
    (∀ v ∈ a :: l.map (fun c => dist x c),
      (l.foldlM (fun acc c => do
      let dv ← distQuery (fun a b => dist a b) x c
      let b ← cmpLe dv acc
      pure (if b then dv else acc)) a : Counted ℝ).value ≤ v) := by
  induction l generalizing a with
  | nil => simp [List.foldlM]
  | cons b t ih =>
      have hrw : ((b :: t).foldlM (fun acc c => do
          let dv ← distQuery (fun a b => dist a b) x c
          let bb ← cmpLe dv acc
          pure (if bb then dv else acc)) a : Counted ℝ).value
          = (t.foldlM (fun acc c => do
          let dv ← distQuery (fun a b => dist a b) x c
          let bb ← cmpLe dv acc
          pure (if bb then dv else acc)) (if dist x b ≤ a then dist x b else a) :
            Counted ℝ).value := by
        simp [List.foldlM, Counted.bind, Counted.charge, cmpLe, distQuery]
      obtain ⟨h1, h2⟩ := ih (if dist x b ≤ a then dist x b else a)
      rw [hrw]
      constructor
      · rcases List.mem_cons.1 h1 with h | h
        · rw [h]
          split_ifs
          · exact List.mem_cons_of_mem _ (by simp)
          · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
      · intro v hv
        have hkey : (if dist x b ≤ a then dist x b else a) ≤ a ∧
            (if dist x b ≤ a then dist x b else a) ≤ dist x b := by
          split_ifs with hc
          · exact ⟨hc, le_rfl⟩
          · exact ⟨le_rfl, le_of_not_ge hc⟩
        rcases List.mem_cons.1 hv with rfl | hv
        · exact le_trans (h2 _ List.mem_cons_self) hkey.1
        rcases List.mem_cons.1 hv with rfl | hv
        · exact le_trans (h2 _ List.mem_cons_self) hkey.2
        · exact h2 v (List.mem_cons_of_mem _ hv)

lemma minDistScan_spec (x : α) {F : List α} (hF : F ≠ []) :
    (minDistScan x F).value = distTo F.toFinset ((List.toFinset_nonempty_iff F).2 hF) x := by
  obtain ⟨h1, h2⟩ := minDistScan_aux x F.tail (dist x F.headI)
  have hval : (minDistScan x F).value =
      (F.tail.foldlM (fun acc c => do
        let dv ← distQuery (fun a b => dist a b) x c
        let b ← cmpLe dv acc
        pure (if b then dv else acc)) (dist x F.headI) : Counted ℝ).value := by
    simp only [minDistScan, Counted.bind_value, distQuery_value]
  rw [hval]
  refine le_antisymm ?_ ?_
  · refine Finset.le_inf' _ _ fun c hc => ?_
    refine h2 (dist x c) ?_
    have hcF : c ∈ F := List.mem_toFinset.1 hc
    rw [← cons_headI_tail hF] at hcF
    rcases List.mem_cons.1 hcF with rfl | hc'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hc')
  · rcases List.mem_cons.1 h1 with h | h
    · rw [h]
      exact Finset.inf'_le _ (List.mem_toFinset.2 (headI_mem_ne hF))
    · obtain ⟨c, hc, hceq⟩ := List.mem_map.1 h
      rw [← hceq]
      refine Finset.inf'_le _ (List.mem_toFinset.2 ?_)
      rw [← cons_headI_tail hF]
      exact List.mem_cons_of_mem _ hc

lemma minDistScan_work (x : α) (F : List α) : (minDistScan x F).ops.work ≤ 3 * F.length + 1 := by
  have h : ((F.tail).foldlM (fun acc c => do
      let dv ← distQuery (fun a b => dist a b) x c
      let b ← cmpLe dv acc
      pure (if b then dv else acc)) (dist x F.headI) : Counted ℝ).ops.work ≤ 3 * F.tail.length := by
    refine foldlM_ops_work_le _ 3 (fun acc c => ?_) F.tail _
    simp [Counted.bind, Counted.charge, cmpLe, distQuery, OpCount.work, OpCount.add_eq,
      OpCount.plus]
  have hops : (minDistScan x F).ops = ({ distanceQueries := 1 } : OpCount) +
      ((F.tail).foldlM (fun acc c => do
        let dv ← distQuery (fun a b => dist a b) x c
        let b ← cmpLe dv acc
        pure (if b then dv else acc)) (dist x F.headI) : Counted ℝ).ops := by
    simp only [minDistScan, Counted.bind_ops, distQuery_ops, distQuery_value]
  rw [hops]
  simp only [OpCount.add_work]
  have h3 : ({ distanceQueries := 1 } : OpCount).work = 1 := by simp [OpCount.work]
  have h4 : F.tail.length ≤ F.length := by simp [List.length_tail]
  have h5 : 3 * F.tail.length ≤ 3 * F.length := by omega
  omega

/-- Costed evaluation of the covering radius of a set of centers. -/
noncomputable def radiusScan (pts : List α) (F : List α) : Counted ℝ := do
  let r0 ← minDistScan pts.headI F
  pts.tail.foldlM (fun acc x => do
    let v ← minDistScan x F
    let b ← cmpLe acc v
    pure (if b then v else acc)) r0

lemma radiusScan_aux (pts : List α) (F : List α) (l : List α) (a : ℝ) :
    ((l.foldlM (fun acc x => do
      let v ← minDistScan x F
      let b ← cmpLe acc v
      pure (if b then v else acc)) a : Counted ℝ).value ∈
        a :: l.map (fun x => (minDistScan x F).value)) ∧
    (∀ v ∈ a :: l.map (fun x => (minDistScan x F).value),
      v ≤ (l.foldlM (fun acc x => do
      let v ← minDistScan x F
      let b ← cmpLe acc v
      pure (if b then v else acc)) a : Counted ℝ).value) := by
  induction l generalizing a with
  | nil => simp [List.foldlM]
  | cons b t ih =>
      have hrw : ((b :: t).foldlM (fun acc x => do
          let v ← minDistScan x F
          let bb ← cmpLe acc v
          pure (if bb then v else acc)) a : Counted ℝ).value
          = (t.foldlM (fun acc x => do
          let v ← minDistScan x F
          let bb ← cmpLe acc v
          pure (if bb then v else acc))
            (if a ≤ (minDistScan b F).value then (minDistScan b F).value else a) :
              Counted ℝ).value := by
        simp [List.foldlM, Counted.bind, cmpLe]
      obtain ⟨h1, h2⟩ := ih (if a ≤ (minDistScan b F).value then (minDistScan b F).value else a)
      rw [hrw]
      constructor
      · rcases List.mem_cons.1 h1 with h | h
        · rw [h]
          split_ifs
          · exact List.mem_cons_of_mem _ (by simp)
          · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
      · intro v hv
        have hkey : a ≤ (if a ≤ (minDistScan b F).value then (minDistScan b F).value else a) ∧
            (minDistScan b F).value ≤
              (if a ≤ (minDistScan b F).value then (minDistScan b F).value else a) := by
          split_ifs with hc
          · exact ⟨hc, le_rfl⟩
          · exact ⟨le_rfl, le_of_not_ge hc⟩
        rcases List.mem_cons.1 hv with rfl | hv
        · exact le_trans hkey.1 (h2 _ List.mem_cons_self)
        rcases List.mem_cons.1 hv with rfl | hv
        · exact le_trans hkey.2 (h2 _ List.mem_cons_self)
        · exact h2 v (List.mem_cons_of_mem _ hv)

/-- The radius scan computes the covering radius. -/
lemma radiusScan_spec {pts F : List α} (hpts : pts ≠ []) (hF : F ≠ []) :
    (radiusScan pts F).value = covRad' pts.toFinset F.toFinset := by
  have hXne : pts.toFinset.Nonempty := (List.toFinset_nonempty_iff pts).2 hpts
  have hFne : F.toFinset.Nonempty := (List.toFinset_nonempty_iff F).2 hF
  rw [covRad'_eq_covRad hXne hFne, covRad]
  obtain ⟨h1, h2⟩ := radiusScan_aux pts F pts.tail (minDistScan pts.headI F).value
  have hval : (radiusScan pts F).value =
      (pts.tail.foldlM (fun acc x => do
        let v ← minDistScan x F
        let b ← cmpLe acc v
        pure (if b then v else acc)) (minDistScan pts.headI F).value : Counted ℝ).value := by
    simp only [radiusScan, Counted.bind_value]
  rw [hval]
  refine le_antisymm ?_ ?_
  · rcases List.mem_cons.1 h1 with h | h
    · rw [h, minDistScan_spec _ hF]
      exact Finset.le_sup' _ (List.mem_toFinset.2 (headI_mem_ne hpts))
    · obtain ⟨x, hx, hxeq⟩ := List.mem_map.1 h
      rw [← hxeq, minDistScan_spec _ hF]
      refine Finset.le_sup' _ (List.mem_toFinset.2 ?_)
      rw [← cons_headI_tail hpts]
      exact List.mem_cons_of_mem _ hx
  · refine Finset.sup'_le _ _ fun x hx => ?_
    rw [← minDistScan_spec x hF]
    refine h2 _ ?_
    have hxp : x ∈ pts := List.mem_toFinset.1 hx
    rw [← cons_headI_tail hpts] at hxp
    rcases List.mem_cons.1 hxp with rfl | hx'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hx')

lemma radiusScan_work (pts F : List α) :
    (radiusScan pts F).ops.work ≤ (3 * F.length + 2) * (pts.length + 1) := by
  have h : ((pts.tail).foldlM (fun acc x => do
      let v ← minDistScan x F
      let b ← cmpLe acc v
      pure (if b then v else acc)) (minDistScan pts.headI F).value : Counted ℝ).ops.work
      ≤ (3 * F.length + 2) * pts.tail.length := by
    refine foldlM_ops_work_le _ (3 * F.length + 2) (fun acc x => ?_) pts.tail _
    simp only [Counted.bind_ops, Counted.pure_ops, cmpLe_ops, OpCount.add_work,
      OpCount.work_zero, Nat.add_zero]
    have := minDistScan_work x F
    have h2 : ({ comparisons := 1 } : OpCount).work = 1 := by simp [OpCount.work]
    omega
  have hops : (radiusScan pts F).ops = (minDistScan pts.headI F).ops +
      ((pts.tail).foldlM (fun acc x => do
        let v ← minDistScan x F
        let b ← cmpLe acc v
        pure (if b then v else acc)) (minDistScan pts.headI F).value : Counted ℝ).ops := by
    simp only [radiusScan, Counted.bind_ops]
  rw [hops]
  simp only [OpCount.add_work]
  have h1 := minDistScan_work pts.headI F
  have h4 : pts.tail.length ≤ pts.length := by simp [List.length_tail]
  have h5 : (3 * F.length + 2) * pts.tail.length ≤ (3 * F.length + 2) * pts.length :=
    Nat.mul_le_mul_left _ h4
  have h6 : (3 * F.length + 2) * pts.length + (3 * F.length + 2)
      = (3 * F.length + 2) * (pts.length + 1) := by ring
  omega

/-- Scan for a subset of least radius. -/
noncomputable def argminScan (init : List α × ℝ) (l : List (List α × ℝ)) :
    Counted (List α × ℝ) :=
  l.foldlM (fun best p => do
    let _ ← Counted.charge { reads := 1 }
    let b ← cmpLe best.2 p.2
    pure (if b then best else p)) init

lemma argminScan_mem (init : List α × ℝ) (l : List (List α × ℝ)) :
    (argminScan init l).value ∈ init :: l := by
  induction l generalizing init with
  | nil => simp [argminScan, List.foldlM]
  | cons a t ih =>
      have hstep : (argminScan init (a :: t)).value =
          (argminScan (if init.2 ≤ a.2 then init else a) t).value := by
        simp [argminScan, List.foldlM, Counted.bind, Counted.charge, cmpLe]
      rw [hstep]
      rcases List.mem_cons.1 (ih (if init.2 ≤ a.2 then init else a)) with h | h
      · rw [h]
        split_ifs with hc
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_self)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

lemma argminScan_le (init : List α × ℝ) (l : List (List α × ℝ)) :
    ∀ p ∈ init :: l, (argminScan init l).value.2 ≤ p.2 := by
  induction l generalizing init with
  | nil => simp [argminScan, List.foldlM]
  | cons a t ih =>
      have hstep : (argminScan init (a :: t)).value =
          (argminScan (if init.2 ≤ a.2 then init else a) t).value := by
        simp [argminScan, List.foldlM, Counted.bind, Counted.charge, cmpLe]
      intro p hp
      rw [hstep]
      have hkey : (if init.2 ≤ a.2 then init else a).2 ≤ init.2 ∧
          (if init.2 ≤ a.2 then init else a).2 ≤ a.2 := by
        split_ifs with hc
        · exact ⟨le_rfl, hc⟩
        · exact ⟨le_of_not_ge hc, le_rfl⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · exact le_trans (ih _ _ List.mem_cons_self) hkey.1
      rcases List.mem_cons.1 hp with rfl | hp
      · exact le_trans (ih _ _ List.mem_cons_self) hkey.2
      · exact ih _ p (List.mem_cons_of_mem _ hp)

lemma argminScan_work (init : List α × ℝ) (l : List (List α × ℝ)) :
    (argminScan init l).ops.work ≤ 2 * l.length := by
  refine foldlM_ops_work_le _ 2 (fun best p => ?_) l init
  simp [Counted.bind, Counted.charge, cmpLe, OpCount.work, OpCount.add_eq, OpCount.plus]

/-- Generation of all `k`-element sublists, charged one write per emitted symbol. -/
noncomputable def enumerateSubsets (k : ℕ) (pts : List α) : Counted (List (List α)) :=
  ⟨List.sublistsLen k pts, { writes := (List.sublistsLen k pts).length * k }⟩

/-- Evaluation of the radius of every enumerated subset. -/
noncomputable def radiiScan (pts : List α) (subs : List (List α)) :
    Counted (List (List α × ℝ)) :=
  subs.foldlM (fun acc F => do
    let r ← radiusScan pts F
    let _ ← Counted.charge { writes := 1 }
    pure (acc ++ [(F, r)])) []

lemma radiiScan_aux (pts : List α) (subs : List (List α)) (acc : List (List α × ℝ)) :
    (subs.foldlM (fun acc F => do
      let r ← radiusScan pts F
      let _ ← Counted.charge { writes := 1 }
      pure (acc ++ [(F, r)])) acc : Counted (List (List α × ℝ))).value
      = acc ++ subs.map (fun F => (F, (radiusScan pts F).value)) := by
  induction subs generalizing acc with
  | nil => simp [List.foldlM]
  | cons a t ih =>
      have hrw : ((a :: t).foldlM (fun acc F => do
          let r ← radiusScan pts F
          let _ ← Counted.charge { writes := 1 }
          pure (acc ++ [(F, r)])) acc : Counted (List (List α × ℝ))).value
          = (t.foldlM (fun acc F => do
          let r ← radiusScan pts F
          let _ ← Counted.charge { writes := 1 }
          pure (acc ++ [(F, r)])) (acc ++ [(a, (radiusScan pts a).value)]) :
            Counted (List (List α × ℝ))).value := by
        simp [List.foldlM, Counted.bind, Counted.charge]
      rw [hrw, ih]
      simp [List.append_assoc]

lemma radiiScan_value (pts : List α) (subs : List (List α)) :
    (radiiScan pts subs).value = subs.map (fun F => (F, (radiusScan pts F).value)) := by
  have := radiiScan_aux pts subs []
  simpa [radiiScan] using this

/-- **The exact enumeration algorithm.** -/
noncomputable def exhaustiveMetricRun (pts : List α) (k : ℕ) : Counted (List α) := do
  let subs ← enumerateSubsets k pts
  let rs ← radiiScan pts subs
  let r0 ← radiusScan pts (pts.take k)
  let best ← argminScan (pts.take k, r0) rs
  pure best.1


/-! ## Correctness and cost of the exhaustive enumeration -/

/-- Every candidate inspected by the running minimum is a `k`-element sublist of the
input whose recorded value is its covering radius. -/
lemma exhaustive_candidate {pts : List α} {k : ℕ} (hkn : k ≤ pts.length)
    (p : List α × ℝ)
    (hp : p ∈ (pts.take k, (radiusScan pts (pts.take k)).value) ::
      (radiiScan pts (List.sublistsLen k pts)).value) :
    p.1.Sublist pts ∧ p.1.length = k ∧ p.2 = (radiusScan pts p.1).value := by
  rcases List.mem_cons.1 hp with rfl | hp
  · exact ⟨List.take_sublist _ _, by simp [Nat.min_eq_left hkn], rfl⟩
  · rw [radiiScan_value] at hp
    obtain ⟨F, hF, hFeq⟩ := List.mem_map.1 hp
    obtain ⟨h1, h2⟩ := List.mem_sublistsLen.1 hF
    subst hFeq
    exact ⟨h1, h2, rfl⟩

/-- **Stage 2**: the enumeration algorithm returns an exactly optimal `k`-element set of
centers. -/
theorem exhaustiveMetric_correct {pts : List α} (hnd : pts.Nodup) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ pts.length) :
    ((exhaustiveMetricRun pts k).value.toFinset.card = k ∧
      (exhaustiveMetricRun pts k).value.toFinset ⊆ pts.toFinset ∧
      ∀ F ⊆ pts.toFinset, F.card = k →
        covRad' pts.toFinset (exhaustiveMetricRun pts k).value.toFinset ≤
          covRad' pts.toFinset F) := by
  have hptsne : pts ≠ [] := by
    intro h; rw [h] at hkn; simp at hkn; omega
  set init : List α × ℝ := (pts.take k, (radiusScan pts (pts.take k)).value) with hinit
  set rs := (radiiScan pts (List.sublistsLen k pts)).value with hrs
  set best := (argminScan init rs).value with hbest
  have hval : (exhaustiveMetricRun pts k).value = best.1 := by
    simp only [exhaustiveMetricRun, Counted.bind_value, Counted.pure_value, hbest, hrs,
      hinit, enumerateSubsets]
  have hbestmem := argminScan_mem init rs
  obtain ⟨hsub, hlen, hveq⟩ := exhaustive_candidate hkn best hbestmem
  have hbnd : best.1.Nodup := List.Nodup.sublist hsub hnd
  have hbne : best.1 ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hval, List.toFinset_card_of_nodup hbnd, hlen]
  · rw [hval]
    intro x hx
    exact List.mem_toFinset.2 (hsub.subset (List.mem_toFinset.1 hx))
  · intro F hF hFcard
    classical
    set l := pts.filter (fun x => decide (x ∈ F)) with hl
    have hlsub : l.Sublist pts := List.filter_sublist
    have hlnd : l.Nodup := List.Nodup.sublist hlsub hnd
    have hlF : l.toFinset = F := by
      ext x
      simp only [List.mem_toFinset, hl, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨List.mem_toFinset.1 (hF h), h⟩
    have hllen : l.length = k := by
      rw [← List.toFinset_card_of_nodup hlnd, hlF, hFcard]
    have hlne : l ≠ [] := by
      intro h; rw [h] at hllen; simp at hllen; omega
    have hlmem : (l, (radiusScan pts l).value) ∈ rs := by
      rw [hrs, radiiScan_value]
      exact List.mem_map_of_mem (List.mem_sublistsLen.2 ⟨hlsub, hllen⟩)
    have hle := argminScan_le init rs (l, (radiusScan pts l).value)
      (List.mem_cons_of_mem _ hlmem)
    rw [← hbest] at hle
    rw [radiusScan_spec hptsne hbne] at hveq
    rw [hval, ← hlF, ← hveq, ← radiusScan_spec hptsne hlne]
    exact hle

/-- The arithmetic behind the `O((n choose k) * n * k)` bound. -/
lemma exhaustive_arith {C n k : ℕ} (hn1 : 1 ≤ n) (hk : 1 ≤ k) (hC : 1 ≤ C) :
    C * k + (10 * n * k + 1) * C + 10 * n * k + 2 * C
      ≤ 24 * C * n * k + 24 * (n + 1) := by
  have h1 : C * k ≤ C * n * k := Nat.mul_le_mul_right k (Nat.le_mul_of_pos_right C hn1)
  have h2 : (10 * n * k + 1) * C ≤ 11 * (C * n * k) := by
    have hnk : 1 ≤ n * k := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hmul : 10 * n * k = 10 * (n * k) := by ring
    calc (10 * n * k + 1) * C ≤ (11 * (n * k)) * C := Nat.mul_le_mul_right C (by omega)
      _ = 11 * (C * n * k) := by ring
  have h3 : 10 * n * k ≤ 10 * (C * n * k) := by
    calc 10 * n * k = 10 * (1 * n * k) := by ring
      _ ≤ 10 * (C * n * k) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hC))
  have h4 : 2 * C ≤ 2 * (C * n * k) := by
    refine Nat.mul_le_mul_left _ ?_
    calc C = C * 1 * 1 := by ring
      _ ≤ C * n * k := Nat.mul_le_mul (Nat.mul_le_mul_left _ hn1) hk
  have hfin : C * k + (10 * n * k + 1) * C + 10 * n * k + 2 * C ≤ 24 * (C * n * k) := by
    calc C * k + (10 * n * k + 1) * C + 10 * n * k + 2 * C
        ≤ C * n * k + 11 * (C * n * k) + 10 * (C * n * k) + 2 * (C * n * k) :=
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 h2) h3) h4
      _ = 24 * (C * n * k) := by ring
  calc C * k + (10 * n * k + 1) * C + 10 * n * k + 2 * C
      ≤ 24 * (C * n * k) := hfin
    _ = 24 * C * n * k := by ring
    _ ≤ 24 * C * n * k + 24 * (n + 1) := Nat.le_add_right _ _

/-- **Stage 2**: the enumeration algorithm runs in `O((n choose k) * n * k)` unit-cost
operations. -/
theorem exhaustiveMetric_work_le {pts : List α} {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ pts.length) :
    (exhaustiveMetricRun pts k).ops.work ≤
      24 * (pts.length.choose k) * pts.length * k + 24 * (pts.length + 1) := by
  have hn1 : 1 ≤ pts.length := le_trans hk hkn
  have hsubslen : (List.sublistsLen k pts).length = pts.length.choose k :=
    List.length_sublistsLen k pts
  have hrad : ∀ F : List α, F.length = k →
      (radiusScan pts F).ops.work ≤ 10 * pts.length * k := by
    intro F hF
    have h := radiusScan_work pts F
    rw [hF] at h
    refine le_trans h ?_
    calc (3 * k + 2) * (pts.length + 1) ≤ (5 * k) * (2 * pts.length) := by
          apply Nat.mul_le_mul <;> omega
      _ = 10 * pts.length * k := by ring
  have hops : (exhaustiveMetricRun pts k).ops.work =
      (enumerateSubsets k pts).ops.work + (radiiScan pts (List.sublistsLen k pts)).ops.work
        + (radiusScan pts (pts.take k)).ops.work
        + (argminScan (pts.take k, (radiusScan pts (pts.take k)).value)
            (radiiScan pts (List.sublistsLen k pts)).value).ops.work := by
    simp only [exhaustiveMetricRun, Counted.bind_ops, Counted.pure_ops,
      enumerateSubsets, OpCount.add_work, OpCount.work_zero, Nat.add_zero]
    omega
  rw [hops]
  have h1 : (enumerateSubsets k pts).ops.work = (List.sublistsLen k pts).length * k := by
    simp [enumerateSubsets, OpCount.work]
  have h2 : (radiiScan pts (List.sublistsLen k pts)).ops.work
      ≤ (10 * pts.length * k + 1) * (List.sublistsLen k pts).length := by
    refine foldlM_ops_work_le_mem _ (10 * pts.length * k + 1) _ [] ?_
    intro b F hFmem
    have hFlen : F.length = k := (List.mem_sublistsLen.1 hFmem).2
    simp only [Counted.bind_ops, Counted.pure_ops, Counted.charge_ops, OpCount.add_work,
      OpCount.work_zero, Nat.add_zero]
    have h := hrad F hFlen
    have h3 : ({ writes := 1 } : OpCount).work = 1 := by simp [OpCount.work]
    omega
  have h3 : (radiusScan pts (pts.take k)).ops.work ≤ 10 * pts.length * k :=
    hrad _ (by rw [List.length_take, Nat.min_eq_left hkn])
  have h4 : (argminScan (pts.take k, (radiusScan pts (pts.take k)).value)
      (radiiScan pts (List.sublistsLen k pts)).value).ops.work
      ≤ 2 * (List.sublistsLen k pts).length := by
    refine le_trans (argminScan_work _ _) ?_
    rw [radiiScan_value]
    simp
  refine le_trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (le_of_eq h1) h2) h3) h4) ?_
  rw [hsubslen]
  exact exhaustive_arith hn1 hk (Nat.choose_pos hkn)

end Q764
