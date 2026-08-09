import Mathlib

/-!
# The space `E` of Q867 and its subspace `F`

`E` is the space of all smooth functions `f : ℝ → ℂ` for which there is a single
constant `M` with `‖f⁽ⁿ⁾(x)‖ ≤ M` for all `n : ℕ` (including `n = 0`) and all `x : ℝ`,
normed by `‖f‖ = sup_{n, x} ‖f⁽ⁿ⁾(x)‖`.

`F` is the closure in `E` of the complex linear span of the exponentials
`x ↦ exp (I * l * x)` for `l ∈ [-1, 1]`.
-/

noncomputable section

open Filter Topology Complex BoundedContinuousFunction

namespace Q867

/-- The "tower" space: bounded sequences of bounded continuous functions.  Used to
put the norm `sup_{n,x} ‖f⁽ⁿ⁾(x)‖` on `E`. -/
abbrev Tower := ℕ →ᵇ (ℝ →ᵇ ℂ)

/-- `f` is smooth and all its derivatives are bounded by one common constant. -/
def IsE (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ ∃ M : ℝ, ∀ (n : ℕ) (x : ℝ), ‖iteratedDeriv n f x‖ ≤ M

lemma IsE.contDiff {f : ℝ → ℂ} (hf : IsE f) : ContDiff ℝ (⊤ : ℕ∞) f := hf.1

lemma IsE.contDiffAt {f : ℝ → ℂ} (hf : IsE f) (n : ℕ) (x : ℝ) : ContDiffAt ℝ n f x :=
  (hf.1.of_le (by exact_mod_cast le_top)).contDiffAt

/-- The carrier of `E`, as a submodule of all functions `ℝ → ℂ`. -/
def Ecarrier : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | IsE f}
  add_mem' := by
    rintro f g ⟨hf, Mf, hMf⟩ ⟨hg, Mg, hMg⟩
    refine ⟨hf.add hg, Mf + Mg, fun n x => ?_⟩
    have : iteratedDeriv n (f + g) x = iteratedDeriv n f x + iteratedDeriv n g x :=
      iteratedDeriv_add (IsE.contDiffAt ⟨hf, Mf, hMf⟩ n x) (IsE.contDiffAt ⟨hg, Mg, hMg⟩ n x)
    rw [this]
    exact (norm_add_le _ _).trans (add_le_add (hMf n x) (hMg n x))
  zero_mem' := by
    refine ⟨contDiff_const, 0, fun n x => ?_⟩
    have : ∀ n : ℕ, iteratedDeriv n (0 : ℝ → ℂ) = 0 := by
      intro n
      induction n with
      | zero => funext y; simp
      | succ n ih => rw [iteratedDeriv_succ, ih]; funext y; simp
    simp [this n]
  smul_mem' := by
    rintro c f ⟨hf, M, hM⟩
    refine ⟨hf.const_smul c, ‖c‖ * M, fun n x => ?_⟩
    have : iteratedDeriv n (c • f) x = c • iteratedDeriv n f x :=
      iteratedDeriv_const_smul (IsE.contDiffAt ⟨hf, M, hM⟩ n x) c
    rw [this, norm_smul]
    exact mul_le_mul_of_nonneg_left (hM n x) (norm_nonneg _)

/-- The space `E` of Q867. -/
def E : Type := Ecarrier

namespace E

instance : AddCommGroup E := inferInstanceAs (AddCommGroup Ecarrier)
instance : Module ℂ E := inferInstanceAs (Module ℂ Ecarrier)

/-- An element of `E`, viewed in the carrier submodule. -/
def toSub (f : E) : ↥Ecarrier := f

/-- The function underlying an element of `E`. -/
def fn (f : E) : ℝ → ℂ := (f.toSub : ℝ → ℂ)

lemma isE (f : E) : IsE f.fn := f.toSub.2

/-- Build an element of `E` from a function together with a proof. -/
def mk (f : ℝ → ℂ) (hf : IsE f) : E := (⟨f, hf⟩ : ↥Ecarrier)

@[simp] lemma fn_mk (f : ℝ → ℂ) (hf : IsE f) : (mk f hf).fn = f := rfl

@[ext] lemma ext {f g : E} (h : f.fn = g.fn) : f = g := Subtype.ext h

@[simp] lemma fn_add (f g : E) : (f + g).fn = f.fn + g.fn := rfl
@[simp] lemma fn_smul (c : ℂ) (f : E) : (c • f).fn = c • f.fn := rfl
@[simp] lemma fn_zero : (0 : E).fn = 0 := rfl
@[simp] lemma fn_sub (f g : E) : (f - g).fn = f.fn - g.fn := rfl

/-- The tower of derivatives of an element of `E`, as an element of `Tower`. -/
def tower (f : E) : Tower :=
  ofNormedAddCommGroupDiscrete
    (fun n => ofNormedAddCommGroup (iteratedDeriv n f.fn)
      (f.isE.1.continuous_iteratedDeriv n (by exact_mod_cast le_top))
      (Classical.choose f.isE.2) (Classical.choose_spec f.isE.2 n))
    (Classical.choose f.isE.2)
    (by
      intro n
      refine (BoundedContinuousFunction.norm_le ?_).2 ?_
      · exact le_trans (norm_nonneg _) (Classical.choose_spec f.isE.2 0 0)
      · intro x
        exact Classical.choose_spec f.isE.2 n x)

@[simp] lemma tower_apply (f : E) (n : ℕ) (x : ℝ) : f.tower n x = iteratedDeriv n f.fn x := rfl

/-- The tower map is `ℂ`-linear. -/
def towerL : E →ₗ[ℂ] Tower where
  toFun := tower
  map_add' := by
    intro f g
    ext n x
    simp only [tower_apply, BoundedContinuousFunction.coe_add, Pi.add_apply, fn_add]
    exact iteratedDeriv_add (f.isE.contDiffAt n x) (g.isE.contDiffAt n x)
  map_smul' := by
    intro c f
    ext n x
    simp only [tower_apply, BoundedContinuousFunction.coe_smul, Pi.smul_apply, fn_smul,
      RingHom.id_apply]
    exact iteratedDeriv_const_smul (f.isE.contDiffAt n x) c

lemma towerL_injective : Function.Injective towerL := by
  intro f g hfg
  apply E.ext
  funext x
  have := congrArg (fun T => T 0 x) hfg
  simpa [towerL, iteratedDeriv_zero] using this

instance : NormedAddCommGroup E :=
  NormedAddCommGroup.induced E Tower (towerL : E →ₗ[ℂ] Tower).toAddMonoidHom towerL_injective

instance : NormedSpace ℂ E := NormedSpace.induced ℂ E Tower towerL

lemma norm_def (f : E) : ‖f‖ = ‖towerL f‖ := rfl

lemma norm_le_iff {f : E} {C : ℝ} (hC : 0 ≤ C) :
    ‖f‖ ≤ C ↔ ∀ (n : ℕ) (x : ℝ), ‖iteratedDeriv n f.fn x‖ ≤ C := by
  rw [E.norm_def, BoundedContinuousFunction.norm_le hC]
  constructor
  · intro h n x
    exact ((BoundedContinuousFunction.norm_le hC).1 (h n)) x
  · intro h n
    exact (BoundedContinuousFunction.norm_le hC).2 (fun x => h n x)

lemma norm_iteratedDeriv_le (f : E) (n : ℕ) (x : ℝ) : ‖iteratedDeriv n f.fn x‖ ≤ ‖f‖ :=
  le_trans (BoundedContinuousFunction.norm_coe_le_norm (E.towerL f n) x)
    (BoundedContinuousFunction.norm_coe_le_norm (E.towerL f) n)

lemma norm_fn_le (f : E) (x : ℝ) : ‖f.fn x‖ ≤ ‖f‖ := by
  simpa using norm_iteratedDeriv_le f 0 x

/-- The norm of `E` really is the supremum of `‖f⁽ⁿ⁾(x)‖` over all `n` and `x`. -/
theorem isLUB_norm (f : E) :
    IsLUB {r : ℝ | ∃ (n : ℕ) (x : ℝ), ‖iteratedDeriv n f.fn x‖ = r} ‖f‖ := by
  constructor
  · rintro r ⟨n, x, rfl⟩
    exact norm_iteratedDeriv_le f n x
  · intro b hb
    have hb0 : 0 ≤ b := le_trans (norm_nonneg _) (hb ⟨0, 0, rfl⟩)
    exact (norm_le_iff hb0).2 (fun n x => hb ⟨n, x, rfl⟩)

lemma hasDerivAt_iteratedDeriv_of_isE {f : ℝ → ℂ} (hf : IsE f) (n : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f x) x := by
  have hd : Differentiable ℝ (iteratedDeriv n f) :=
    hf.1.differentiable_iteratedDeriv n (compareOfLessAndEq_eq_lt.mp rfl)
  simpa [iteratedDeriv_succ] using (hd x).hasDerivAt

lemma tower_contDiff {T : Tower} (hT : ∀ (n : ℕ) (x : ℝ), HasDerivAt (T n) (T (n + 1) x) x)
    (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => T n x) := by
  rw [contDiff_infty]
  intro m
  induction m generalizing n with
  | zero => exact contDiff_zero.mpr (T n).continuous
  | succ m ih =>
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; ring,
        contDiff_succ_iff_deriv]
      refine ⟨fun x => (hT n x).differentiableAt, by simp, ?_⟩
      have hd : deriv (fun x : ℝ => T n x) = fun x => T (n + 1) x := funext fun x => (hT n x).deriv
      rw [hd]
      exact ih (n + 1)

lemma tower_iteratedDeriv {T : Tower} (hT : ∀ (n : ℕ) (x : ℝ), HasDerivAt (T n) (T (n + 1) x) x)
    (n : ℕ) : iteratedDeriv n (fun x : ℝ => T 0 x) = fun x => T n x := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih => rw [iteratedDeriv_succ, ih]; exact funext fun x => (hT n x).deriv

lemma range_towerL :
    Set.range (towerL : E → Tower)
      = {T : Tower | ∀ (n : ℕ) (x : ℝ), HasDerivAt (T n) (T (n + 1) x) x} := by
  ext T
  constructor
  · rintro ⟨f, rfl⟩ n x
    have h1 : ⇑(towerL f n) = iteratedDeriv n f.fn := rfl
    have h2 : (towerL f (n + 1)) x = iteratedDeriv (n + 1) f.fn x := rfl
    rw [h1, h2]
    exact hasDerivAt_iteratedDeriv_of_isE f.isE n x
  · intro hT
    have hE : IsE (fun x : ℝ => T 0 x) := by
      refine ⟨tower_contDiff hT 0, ‖T‖, fun n x => ?_⟩
      rw [tower_iteratedDeriv hT n]
      exact le_trans (BoundedContinuousFunction.norm_coe_le_norm (T n) x)
        (BoundedContinuousFunction.norm_coe_le_norm T n)
    refine ⟨mk _ hE, ?_⟩
    ext n x
    show iteratedDeriv n (fun x : ℝ => T 0 x) x = T n x
    rw [tower_iteratedDeriv hT n]

lemma isClosed_range_towerL : IsClosed (Set.range (towerL : E → Tower)) := by
  rw [range_towerL]
  refine IsSeqClosed.isClosed ?_
  intro Ts T hmem hlim n
  have hd : TendstoUniformly (fun j => ⇑(Ts j (n + 1))) (⇑(T (n + 1))) atTop := by
    rw [← BoundedContinuousFunction.tendsto_iff_tendstoUniformly]
    exact (ContinuousEvalConst.continuous_eval_const (n + 1)).continuousAt.tendsto.comp hlim
  refine hasDerivAt_of_tendstoUniformly hd (.of_forall fun j x => hmem j n x) (fun x => ?_)
  have h : Tendsto (fun j => Ts j n) atTop (𝓝 (T n)) :=
    (ContinuousEvalConst.continuous_eval_const n).continuousAt.tendsto.comp hlim
  exact ((ContinuousEvalConst.continuous_eval_const x).continuousAt.tendsto.comp h)

lemma towerL_isometry : Isometry (towerL : E → Tower) :=
  AddMonoidHomClass.isometry_of_norm _ (fun _ => rfl)

instance : CompleteSpace E := by
  refine Metric.complete_of_cauchySeq_tendsto (fun u hu => ?_)
  have hcau : CauchySeq (fun j => towerL (u j)) :=
    towerL_isometry.uniformContinuous.comp_cauchySeq hu
  obtain ⟨T, hT⟩ := cauchySeq_tendsto_of_complete hcau
  have hmem : T ∈ Set.range (towerL : E → Tower) :=
    isClosed_range_towerL.mem_of_tendsto hT (.of_forall fun j => ⟨u j, rfl⟩)
  obtain ⟨f, rfl⟩ := hmem
  refine ⟨f, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have : ∀ j, dist (u j) f = dist (towerL (u j)) (towerL f) := fun j =>
    (towerL_isometry.dist_eq _ _).symm
  simp only [this]
  rw [← tendsto_iff_dist_tendsto_zero] at *
  exact hT

end E

/-! ### The exponentials and the subspace `F` -/

/-- `expFn l x = exp (i l x)`. -/
def expFn (l : ℝ) : ℝ → ℂ := fun x => Complex.exp (Complex.I * (l * x))

lemma hasDerivAt_expFn (l : ℝ) (c : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => c * expFn l t) (Complex.I * l * (c * expFn l x)) x := by
  have h1 : HasDerivAt (fun t : ℝ => (Complex.I * (l * t) : ℂ)) (Complex.I * l) x := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using
      ((hasDerivAt_id x).ofReal_comp.const_mul (Complex.I * l))
  have h2 := (h1.cexp).const_mul c
  convert h2 using 1
  simp only [expFn]
  ring

lemma iteratedDeriv_expFn (l : ℝ) (n : ℕ) :
    iteratedDeriv n (expFn l) = fun x => (Complex.I * l) ^ n * expFn l x := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      rw [(hasDerivAt_expFn l ((Complex.I * l) ^ n) x).deriv]
      ring

lemma contDiff_expFn (l : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (expFn l) := by
  have heq : expFn l = fun t : ℝ => Complex.exp ((Complex.I * l) • (t : ℂ)) := by
    funext t; simp [expFn, smul_eq_mul, mul_assoc]
  rw [heq]
  exact Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.const_smul (Complex.I * l))

lemma isE_expFn {l : ℝ} (hl : |l| ≤ 1) : IsE (expFn l) := by
  refine ⟨contDiff_expFn l, 1, fun n x => ?_⟩
  rw [iteratedDeriv_expFn l n]
  simp only [expFn, norm_mul, norm_pow, Complex.norm_exp]
  have h2 : (Complex.I * ((l : ℂ) * (x : ℂ))).re = 0 := by simp
  rw [h2]
  simp only [Real.exp_zero, mul_one, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  exact pow_le_one₀ (abs_nonneg l) hl

/-- The exponential `x ↦ exp (i l x)` as an element of `E`, for `|l| ≤ 1`. -/
def expE {l : ℝ} (hl : |l| ≤ 1) : E := E.mk (expFn l) (isE_expFn hl)

/-- The set of exponentials `e_l`, `|l| ≤ 1`, inside `E`. -/
def expSet : Set E := {f : E | ∃ l : ℝ, |l| ≤ 1 ∧ f.fn = expFn l}

/-- The subspace `F`: the closure of the span of the exponentials with frequency in `[-1,1]`. -/
def F : Submodule ℂ E := (Submodule.span ℂ expSet).topologicalClosure

lemma F_isClosed : IsClosed (F : Set E) := Submodule.isClosed_topologicalClosure _

lemma expE_mem_F {l : ℝ} (hl : |l| ≤ 1) : expE hl ∈ F :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨l, hl, rfl⟩)

lemma E.fn_sum {ι : Type*} (s : Finset ι) (g : ι → E) :
    (∑ i ∈ s, g i).fn = fun x => ∑ i ∈ s, (g i).fn x := by
  classical
  induction s using Finset.induction with
  | empty => funext x; simp
  | insert i s hi ih =>
      funext x
      rw [Finset.sum_insert hi, Finset.sum_insert hi, E.fn_add]
      simp [ih]

/-- A finite linear combination of exponentials with frequencies in `[-1,1]` lies in `F`. -/
lemma mem_F_of_finite_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (l : ι → ℝ)
    (hl : ∀ i, |l i| ≤ 1) (f : E) (hf : f.fn = fun x => ∑ i ∈ s, c i * expFn (l i) x) :
    f ∈ F := by
  have hsum : f = ∑ i ∈ s, c i • expE (hl i) := by
    apply E.ext
    rw [hf, E.fn_sum]
    funext x
    exact Finset.sum_congr rfl (fun i _ => rfl)
  rw [hsum]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (expE_mem_F (hl i)))

/-! ### The lattice spacing and the sampling map -/

/-- The sampling lattice spacing. -/
def hstep : ℝ := 8 * Real.pi

lemma hstep_pos : 0 < hstep := by
  have := Real.pi_pos; unfold hstep; linarith

/-- The sampling map `R : E → ℓ^∞(ℤ)`, `R f k = f (8 π k)`. -/
def Rmap : E →L[ℂ] (ℤ →ᵇ ℂ) := by
  refine LinearMap.mkContinuous
    { toFun := fun f => BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
        (fun k : ℤ => f.fn (hstep * k)) ‖f‖ (fun k => E.norm_fn_le f _)
      map_add' := by intro f g; ext k; simp [E.fn_add]
      map_smul' := by intro c f; ext k; simp [E.fn_smul] } 1 ?_
  intro f
  refine (BoundedContinuousFunction.norm_le (by simpa using norm_nonneg f)).2 (fun k => ?_)
  simpa using E.norm_fn_le f (hstep * k)

@[simp] lemma Rmap_apply (f : E) (k : ℤ) : Rmap f k = f.fn (hstep * k) := rfl

lemma norm_Rmap_le (f : E) : ‖Rmap f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).2 (fun k => E.norm_fn_le f _)

/-! ### The differentiation operator -/

lemma isE_deriv {f : ℝ → ℂ} (hf : IsE f) : IsE (deriv f) := by
  obtain ⟨hsm, M, hM⟩ := hf
  refine ⟨(contDiff_infty_iff_deriv.mp hsm).2, M, fun n x => ?_⟩
  rw [← iteratedDeriv_succ']
  exact hM (n + 1) x

/-- Differentiation, as a map `E → E`. -/
def Dmap (f : E) : E := E.mk (deriv f.fn) (isE_deriv f.isE)

@[simp] lemma Dmap_fn (f : E) : (Dmap f).fn = deriv f.fn := rfl

end Q867
