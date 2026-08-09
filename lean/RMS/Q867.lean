import RMS.Q867Means

/-!
# Q867: `F` is not complemented in `E`

Main results:

* `Q867.no_bounded_projection`: there is no continuous linear projection of `E` onto `F`;
* `Q867.F_not_complemented`: there is no closed subspace `G` of `E` with `E = F ⊕ G`;
* `Q867.no_deriv_invariant_complement`: in particular there is no such `G` which is
  moreover invariant under differentiation.
-/

noncomputable section

open Filter Topology Complex BoundedContinuousFunction

namespace Q867

/-- **Main theorem.**  There is no continuous linear projection from `E` onto `F`. -/
theorem no_bounded_projection (P : E →L[ℂ] E) (hP : ∀ f, P f ∈ F) (hPid : ∀ f ∈ F, P f = f) :
    False := by
  refine no_projection_onto_c0 (Tmap.comp (P.comp Smap)) ?_ ?_
  · intro a
    have h : Rmap (P (Smap a)) ∈ AP := Rmap_mem_AP (hP _)
    simpa using xi_tendsto_zero h
  · intro a ha
    have h1 : P (Smap a) = Smap a := hPid _ (Smap_mem_F ha)
    ext n
    simp [h1, Rmap_Smap, xi_Sseq ha n]

/-- **Main theorem, complement form.**  `F` has no closed topological complement in `E`. -/
theorem F_not_complemented (G : Submodule ℂ E) (hGclosed : IsClosed (G : Set E))
    (hcompl : IsCompl F G) : False := by
  classical
  set p : E →ₗ[ℂ] E := F.subtype.comp (F.linearProjOfIsCompl G hcompl) with hp
  have hmem : ∀ f, p f ∈ F := fun f => (F.linearProjOfIsCompl G hcompl f).2
  have hid : ∀ f ∈ F, p f = f := by
    intro f hf
    simpa [hp] using congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hcompl ⟨f, hf⟩)
  have hker : ∀ f ∈ G, p f = 0 := by
    intro f hf
    simpa [hp] using congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hcompl ⟨f, hf⟩)
  have hsub : ∀ f, f - p f ∈ G := by
    intro f
    have hx : f ∈ F ⊔ G := by rw [hcompl.sup_eq_top]; trivial
    rw [Submodule.mem_sup] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have hval : p (a + b) = a := by rw [map_add, hid a ha, hker b hb, add_zero]
    rw [hval]
    simpa using hb
  have hcont : Continuous p := by
    refine LinearMap.continuous_of_isClosed_graph p (IsSeqClosed.isClosed ?_)
    intro u z hu hlim
    have h1 : Tendsto (fun j => (u j).1) atTop (𝓝 z.1) := (continuous_fst.tendsto z).comp hlim
    have h2 : Tendsto (fun j => (u j).2) atTop (𝓝 z.2) := (continuous_snd.tendsto z).comp hlim
    have hu' : ∀ j, (u j).2 = p (u j).1 := fun j => (LinearMap.mem_graph_iff p (u j)).1 (hu j)
    have hz2F : z.2 ∈ F := by
      refine F_isClosed.mem_of_tendsto h2 (.of_forall fun j => ?_)
      rw [hu' j]; exact hmem _
    have hzG : z.1 - z.2 ∈ G := by
      refine hGclosed.mem_of_tendsto (h1.sub h2) (.of_forall fun j => ?_)
      rw [hu' j]; exact hsub _
    rw [SetLike.mem_coe, LinearMap.mem_graph_iff]
    have hz : z.1 = z.2 + (z.1 - z.2) := by abel
    rw [hz, map_add, hid _ hz2F, hker _ hzG, add_zero]
  exact no_bounded_projection ⟨p, hcont⟩ hmem hid

/-- **Corollary.** There is in particular no closed complement of `F` in `E` that is
invariant under differentiation. -/
theorem no_deriv_invariant_complement (G : Submodule ℂ E) (hGclosed : IsClosed (G : Set E))
    (hcompl : IsCompl F G) (_hinv : ∀ f ∈ G, Dmap f ∈ G) : False :=
  F_not_complemented G hGclosed hcompl

end Q867
