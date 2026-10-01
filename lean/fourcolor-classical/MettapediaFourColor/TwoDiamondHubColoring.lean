import MettapediaFourColor.TwoDiamondBoundaryHub

/-!
# Transport supplied cycle colourings to the ordered boundary hub

The map on face colours keeps every exterior dart. A hub dart is read at
the exterior dart reached by its next face step. Exact exterior cofaciality
makes this a face-colouring transport; the original edge inequalities are
retained. No extension of arbitrary boundary assignments is assumed.
-/

namespace FourColor.TwoDiamondHubColoring

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamCubic
open GoertzelV24TwoEdgeCutMinimality
open OpenTangleVertexReflection
open TwoDiamondCycleReplacement TwoDiamondBoundaryHub

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
variable {V I B : Type u} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
  (outside : OpenTangleData V I B) (seam : B ≃ Fin 8)

/-- Read a face at an exterior dart, including the faces meeting the hub. -/
def project : (capped outside seam).D → I ⊕ B
  | .inl (.inl i) => .inl i
  | .inl (.inr e) => nomatch e
  | .inr (.inl b) => .inr b
  | .inr (.inr i) => outside.rho (.inr (seam.symm i))

@[simp] theorem project_left (d : I ⊕ B) :
    project outside seam (composeDartEquiv (.inl d)) = d := by cases d <;> rfl

theorem phi_hub (i : Fin 8) :
    (capped outside seam).phi (composeDartEquiv (.inr (.inr i))) =
      composeDartEquiv (.inl (outside.rho (.inr (seam.symm i)))) := by
  rw [RotationSystem.phi_apply]
  exact rho_left outside seam (.inr (seam.symm i))

theorem project_face (d : (capped outside seam).D) :
    (capped outside seam).phi.SameCycle d (composeDartEquiv (.inl (project outside seam d))) := by
  obtain ⟨(d | (e | i)), rfl⟩ := composeDartEquiv.surjective d
  · rw [project_left]
  · exact nomatch e
  · exact (Equiv.Perm.SameCycle.refl _ _).apply_right.trans
      (by rw [phi_hub]; exact .rfl)

theorem cycle_exterior_faces (a b : I ⊕ B) :
    (reduced outside seam).phi.SameCycle
      (composeDartEquiv (.inl a)) (composeDartEquiv (.inl b)) ↔
    (capped outside seam).phi.SameCycle
      (composeDartEquiv (.inl a)) (composeDartEquiv (.inl b)) :=
  OpenTanglePortReplacement.exterior_sameCycle_iff _ _
    (cycle_returnCode.trans (OpenTangleBoundaryHub.boundary_return 8).symm) outside seam a b

/-- Every colour is read from the supplied smaller-map face witness. -/
def lift (k : (reduced outside seam).D → Color) : (capped outside seam).D → Color :=
  fun d => k (composeDartEquiv (.inl (project outside seam d)))

@[simp] theorem lift_left (k : (reduced outside seam).D → Color) (d : I ⊕ B) :
    lift outside seam k (composeDartEquiv (.inl d)) = k (composeDartEquiv (.inl d)) := by
  simp only [lift, project_left]

private theorem reduced_rho_left (d : I ⊕ B) :
    (reduced outside seam).rho (composeDartEquiv (.inl d)) =
      composeDartEquiv (.inl (outside.rho d)) := by
  change (outside.composeData cycle seam).rho _ = _
  rw [OpenTangleData.composeData_rho_apply]
  simp

theorem lift_alpha_left {k : (reduced outside seam).D → Color}
    (hk : (SourceConstruction.sourceMap (reduced outside seam)).Coloring k) (d : I ⊕ B) :
    lift outside seam k ((capped outside seam).alpha (composeDartEquiv (.inl d))) =
      k ((reduced outside seam).alpha (composeDartEquiv (.inl d))) := by
  rcases d with i | b
  · rfl
  · change k (composeDartEquiv (.inl (outside.rho (.inr (seam.symm (seam b)))))) = _
    rw [Equiv.symm_apply_apply, ← reduced_rho_left]
    exact SourceConstruction.faceColor_rho hk _

theorem lift_colouring {k : (reduced outside seam).D → Color}
    (hk : (SourceConstruction.sourceMap (reduced outside seam)).Coloring k) :
    (SourceConstruction.sourceMap (capped outside seam)).Coloring (lift outside seam k) := by
  have proper (d : I ⊕ B) :
      lift outside seam k ((capped outside seam).alpha (composeDartEquiv (.inl d))) ≠
        lift outside seam k (composeDartEquiv (.inl d)) := by
    rw [lift_alpha_left outside seam hk, lift_left]
    exact hk.edge _
  constructor
  · intro d
    obtain ⟨(d | (e | i)), rfl⟩ := composeDartEquiv.surjective d
    · exact proper d
    · exact nomatch e
    · have h := proper (.inr (seam.symm i))
      change lift outside seam k (composeDartEquiv (.inr (.inr (seam (seam.symm i))))) ≠
        lift outside seam k (composeDartEquiv (.inl (.inr (seam.symm i)))) at h
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
  · intro d
    apply hk.cface
    apply (cycle_exterior_faces outside seam _ _).mpr
    exact (project_face outside seam ((capped outside seam).phi d)).symm.trans
      ((Equiv.Perm.SameCycle.refl (capped outside seam).phi d).apply_right.symm.trans
        (project_face outside seam d))

/-- Read the actual exterior edge differences of a hub face colouring. -/
def read (k : (capped outside seam).D → Color) (d : I ⊕ B) :
    Mettapedia.GraphTheory.FourColor.Color :=
  SourceConstruction.palette (SourceConstruction.dartTrace (capped outside seam) k
    (composeDartEquiv (.inl d)))

theorem read_proper
    (h : BridgelessSphericalCubicMapData (original outside seam))
    {k : (capped outside seam).D → Color}
    (hk : (SourceConstruction.sourceMap (capped outside seam)).Coloring k) :
    OpenTangleClosedWitness.IsColor outside (read outside seam k) := by
  have adjacent (d : I ⊕ B) : read outside seam k d ≠ read outside seam k (outside.rho d) := by
    intro he
    apply SourceConstruction.dartTrace_ne_rho_of_three hk (composeDartEquiv (.inl d))
      (by simp only [rho_left, outside_three outside seam h])
    rw [rho_left]
    exact SourceConstruction.palette.injective he
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact congrArg SourceConstruction.palette
      (SourceConstruction.dartTrace_alpha (capped outside seam) k (.inl (.inl i)))
  · intro d e hv hne
    let a : VertexCodeCyclicEncoder.At (original outside seam)
        ((original outside seam).vertOf (composeDartEquiv (.inl d))) :=
      ⟨composeDartEquiv (.inl d), rfl⟩
    have hv' : (original outside seam).vertOf (composeDartEquiv (.inl e)) =
        (original outside seam).vertOf (composeDartEquiv (.inl d)) := by
      change (outside.composeData TwoDiamondTangle.piece seam).vertOf
        (composeDartEquiv (.inl e)) = (outside.composeData TwoDiamondTangle.piece seam).vertOf
        (composeDartEquiv (.inl d))
      rw [OpenTangleData.composeData_vertOf_composeDartEquiv,
        OpenTangleData.composeData_vertOf_composeDartEquiv]
      exact congrArg Sum.inl hv.symm
    have hs : Function.Surjective (VertexCodeCyclicEncoder.cyc a) :=
      ((Fintype.bijective_iff_injective_and_card _).mpr
        ⟨VertexCodeCyclicEncoder.cyc_injective h.spherical.cubic h.vertexRotationCyclic a, by
          simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using
            (VertexCodeCyclicEncoder.card_at (v := (original outside seam).vertOf
              (composeDartEquiv (.inl d))) h.spherical.cubic).symm⟩).2
    obtain ⟨i, hi⟩ := hs ⟨composeDartEquiv (.inl e), hv'⟩
    have he := congrArg Subtype.val hi
    fin_cases i
    · exact (hne (Sum.inl.inj (composeDartEquiv.injective he))).elim
    · change (original outside seam).rho (composeDartEquiv (.inl d)) =
        composeDartEquiv (.inl e) at he
      rw [original_rho_left] at he
      have he' := Sum.inl.inj (composeDartEquiv.injective he)
      rw [← he']
      exact adjacent d
    · change (original outside seam).rho ((original outside seam).rho
        (composeDartEquiv (.inl d))) = composeDartEquiv (.inl e) at he
      rw [original_rho_left, original_rho_left] at he
      have he' := Sum.inl.inj (composeDartEquiv.injective he)
      rw [← he']
      have hn := (adjacent (outside.rho (outside.rho d))).symm
      simpa only [outside_three outside seam h] using hn
  · intro d he
    have he' := SourceConstruction.palette.injective (he.trans SourceConstruction.palette_zero.symm)
    exact hk.edge (composeDartEquiv (.inl d)) ((Color.add_eq_zero_iff.mp he').symm)

private theorem trace_ofFn_eight (f : Fin 8 → Color) :
    trace (List.ofFn f) = List.ofFn (fun i => f i + f (finRotate 8 i)) := by
  rw [trace_eq_zipWith]
  rfl

/-- The complete ordered trace is preserved, including the closing seam. -/
theorem read_word {k : (capped outside seam).D → Color}
    (hk : (SourceConstruction.sourceMap (capped outside seam)).Coloring k) :
    (List.finRange 8).map (fun i => read outside seam k (.inr (seam.symm i))) =
      (trace ((ring outside seam).map k)).map PhysicalKempeBoundary.palette := by
  rw [ring, List.map_ofFn, trace_ofFn_eight, List.map_ofFn, List.ofFn_eq_map]
  apply List.map_congr_left
  intro i _
  change SourceConstruction.palette (k (composeDartEquiv (.inl (.inr (seam.symm i)))) +
    k (composeDartEquiv (.inr (.inr (seam (seam.symm i)))))) = _
  rw [Equiv.apply_symm_apply]
  have hf := SourceConstruction.faceColor_rho hk (Sum.inr (Sum.inr i))
  rw [rho_hub] at hf
  change k (Sum.inr (Sum.inr (finRotate 8 i))) =
    k (composeDartEquiv (.inl (.inr (seam.symm i)))) at hf
  rw [← hf, add_comm]
  rfl

/-- A reference repair always reads back to a genuine exterior colouring. -/
theorem read_trace
    (h : BridgelessSphericalCubicMapData (original outside seam))
    {et : List Color}
    (ht : (SourceConstruction.sourceMap (capped outside seam)).mirror.RingTrace
      (ring outside seam) et) :
    OpenTangleKempeRepair.Trace outside seam.symm et := by
  obtain ⟨k, hk, rfl⟩ := ht
  exact ⟨read outside seam k, read_proper outside seam h hk.of_mirror,
    read_word outside seam hk.of_mirror⟩

/-- Repair a supplied smaller-map colouring through the closed cap observation.
The exterior may be disconnected and may be recoloured. No exterior closure
hypothesis or Four Colour existence theorem is used. -/
theorem reconstruct
    (h : BridgelessSphericalCubicMapData (original outside seam))
    (hc : RotationSystemTaitColorable (reduced outside seam)) :
    RotationSystemTaitColorable (original outside seam) := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨k, hk, _⟩ := SourceConstruction.reference_colouring_of_tait
    (replacement_class outside seam h) c hc
  have hcap := lift_colouring outside seam hk
  let E := (SourceConstruction.sourceMap (capped outside seam)).mirror.RingTrace
    (ring outside seam)
  let et := trace ((ring outside seam).map (lift outside seam k))
  have het : E et := ⟨lift outside seam k,
    (SourceConstruction.reference_mirror_colouring_iff _).mpr hcap, rfl⟩
  obtain ⟨hlen, hzero, hsum⟩ := OpenTangleKempeRepair.trace_valid outside seam.symm
    (GoertzelV24PortTangleCutParity.isCubic_ofOpenTangleData outside
      (exterior_isCubic outside _ seam h.spherical.cubic)) (read_trace outside seam h het)
  exact OpenTangleKempeRepair.glue_of_closed_observation TwoDiamondTangle.piece outside
    seam.symm TwoDiamondTangle.open_repair E (reference_closed outside seam h)
    (fun _ ht => read_trace outside seam h ht) et hlen hzero hsum het

/-- The full operation removes twelve vertices, preserves the intended
map class and reconstructs an actual original colouring. Recognition of
this disk in an arbitrary source remains a separate geometric obligation. -/
theorem strict_reduction
    (h : BridgelessSphericalCubicMapData (original outside seam)) :
    Fintype.card (V ⊕ Fin 8) + 12 = Fintype.card (V ⊕ Fin 20) ∧
      Fintype.card (V ⊕ Fin 8) < Fintype.card (V ⊕ Fin 20) ∧
      BridgelessSphericalCubicMapData (reduced outside seam) ∧
      (RotationSystemTaitColorable (reduced outside seam) →
        RotationSystemTaitColorable (original outside seam)) :=
  ⟨whole_vertex_loss (V := V), replacement_strict (V := V),
    replacement_class outside seam h, reconstruct outside seam h⟩

end
end FourColor.TwoDiamondHubColoring
