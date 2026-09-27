import Mettapedia.GraphTheory.FourColor.SourceVertexCodeTrace
import Mettapedia.GraphTheory.FourColor.VertexCodeLosslessPruning

/-!
# Transport from decoded source traces to literal ambient sides

The constructed source model identifies internal darts, faces, and Euler
mass with the existing vertex-side tangle. This makes the geometric round
trip usable by the planar-prefix semantics, not just by incidence clients.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexCodeSourceSemantics

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open GoertzelV24RotationCutDartDecomposition
open VertexCodeSourceGeometry VertexCodeDartGeometry
open GoertzelV24CompositeSeamMultigraph SerialTangleSmallCutTransfer
open OpenTangleReplacementEuler OpenTangleMarkedFace
open GoertzelV24RetainedSpliceFaceCount
open GoertzelV24CanonicalHubCyclicity

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem.{u,u,u} V E} {inner : V → Prop}
variable {W I : Type*} {l : ℕ}
variable {T : TwoSidedOpenTangleData W I (Fin 0) (Fin l)}
  {mi : Fin l ≃ BoundaryDart RS inner} (M : Model T mi)

def internalMap (i : I) : InternalDart RS inner :=
  ⟨M.dart (.inl i), (M.mate i) ▸ (M.dart (.inl (T.interiorAlpha i))).2⟩

theorem internalMap_bijective : Function.Bijective (internalMap M) := by
  constructor
  · intro i j h
    exact Sum.inl_injective (M.dart.injective (congrArg Subtype.val h))
  · intro d
    obtain ⟨i | j, hi⟩ := M.dart.surjective d.1
    · exact ⟨i, Subtype.ext hi⟩
    · have he : (mi j).1.1 = d.1.1 := (M.port j).symm.trans (congrArg Subtype.val hi)
      exact ((mi j).2 (he ▸ d.2)).elim

def internalEquiv : I ≃ InternalDart RS inner := Equiv.ofBijective _ (internalMap_bijective M)

def sourceDarts : I ⊕ (Fin 0 ⊕ Fin l) ≃ InternalDart RS inner ⊕ BoundaryDart RS inner :=
  (compact.symm.trans M.dart).trans (retainedDartEquivInternalSumBoundary RS inner)

theorem sourceDarts_underlying (d : I ⊕ (Fin 0 ⊕ Fin l)) :
    (retainedDartEquivInternalSumBoundary RS inner).symm (sourceDarts M d) =
      M.dart (compact.symm d) := by
  simp only [sourceDarts, Equiv.trans_apply, Equiv.symm_apply_apply]

theorem sourceDarts_internal (i : I) : sourceDarts M (.inl i) = .inl (internalEquiv M i) := by
  apply (retainedDartEquivInternalSumBoundary RS inner).symm.injective
  rw [sourceDarts_underlying]
  rfl

theorem sourceDarts_port (j : Fin l) : sourceDarts M (.inr (.inr j)) = .inr (mi j) := by
  apply (retainedDartEquivInternalSumBoundary RS inner).symm.injective
  rw [sourceDarts_underlying]
  exact Subtype.ext (M.port j)

theorem sourceDarts_rho (outer : RetainedDart RS inner) (d : I ⊕ (Fin 0 ⊕ Fin l)) :
    sourceDarts M (T.rho d) = (OpenTangleData.ofVertexSide RS inner outer).rho (sourceDarts M d) := by
  apply (retainedDartEquivInternalSumBoundary RS inner).symm.injective
  rw [sourceDarts_underlying, OpenTangleData.ofVertexSide_rho_underlying, sourceDarts_underlying]
  apply Subtype.ext
  simpa only [Equiv.apply_symm_apply, retainedRho_val] using M.rho (compact.symm d)

theorem internalEquiv_alpha (i : I) :
    internalEquiv M (T.interiorAlpha i) = internalAlpha RS inner (internalEquiv M i) :=
  Subtype.ext (Subtype.ext (M.mate i))

theorem sourceDarts_alpha (outer : RetainedDart RS inner) (d : I ⊕ (Fin 0 ⊕ Fin l)) :
    sourceDarts M (OpenTangleEulerPresentation.alpha (asOpen T) d) =
      OpenTangleEulerPresentation.alpha (OpenTangleData.ofVertexSide RS inner outer) (sourceDarts M d) := by
  rcases d with i | (e | j)
  · change sourceDarts M (.inl (T.interiorAlpha i)) = _
    rw [sourceDarts_internal, sourceDarts_internal]
    exact congrArg Sum.inl (internalEquiv_alpha M i)
  · exact e.elim0
  · change sourceDarts M (.inr (.inr j)) = _
    rw [sourceDarts_port]
    rfl

theorem sourceDarts_phi (outer : RetainedDart RS inner) (d : I ⊕ (Fin 0 ⊕ Fin l)) :
    sourceDarts M (openPhi (asOpen T) d) =
      openPhi (OpenTangleData.ofVertexSide RS inner outer) (sourceDarts M d) := by
  change sourceDarts M (T.rho (OpenTangleEulerPresentation.alpha (asOpen T) d)) = _
  rw [sourceDarts_rho M outer, sourceDarts_alpha M outer]
  rfl

theorem sourcePhi (outer : RetainedDart RS inner) :
    openPhi (OpenTangleData.ofVertexSide RS inner outer) =
      (sourceDarts M).permCongr (openPhi (asOpen T)) := by
  ext d
  obtain ⟨x, rfl⟩ := (sourceDarts M).surjective d
  simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using (sourceDarts_phi M outer x).symm

variable [Fintype W] [Fintype I] [DecidableEq I]

include M in
omit [Fintype W] in
theorem source_faces (outer : RetainedDart RS inner) :
    (openPhi (asOpen T)).partition.parts.card =
      (openPhi (OpenTangleData.ofVertexSide RS inner outer)).partition.parts.card := by
  rw [sourcePhi M outer, card_permCongr_partition_parts]

include M in
theorem source_mass (outer : RetainedDart RS inner) :
    eulerMass (asOpen T) = eulerMass (OpenTangleData.ofVertexSide RS inner outer) := by
  have hv := Fintype.card_congr M.vertex
  have hi := Fintype.card_congr (internalEquiv M)
  unfold eulerMass
  rw [source_faces M outer, hv, hi]

omit [Fintype W] [Fintype I] [DecidableEq I] in
theorem internal_vertex (outer : RetainedDart RS inner) (i : I) :
    M.vertex (T.interiorVert i) =
      (OpenTangleData.ofVertexSide RS inner outer).interiorVert (internalEquiv M i) :=
  Subtype.ext (M.vert (.inl i))

omit [Fintype W] [Fintype I] [DecidableEq I] in
theorem boundary_vertex (outer : RetainedDart RS inner) (j : Fin l) :
    M.vertex (T.rightVert j) =
      (OpenTangleData.ofVertexSide RS inner outer).boundaryVert (mi j) := by
  apply Subtype.ext
  exact (M.vert (.inr j)).trans (congrArg RS.vertOf (M.port j))

theorem step_iff_dart {X J B : Type*} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
    [Fintype B] [DecidableEq B] (A : OpenTangleData X J B) (x y : X) :
    (sideMultigraph A).Step x y ↔ ∃ i, A.interiorVert i = x ∧ A.interiorVert (A.interiorAlpha i) = y := by
  refine ⟨exists_interiorDart_of_sideStep A, ?_⟩
  rintro ⟨i, rfl, rfl⟩
  refine ⟨sideEdgeOf A i, by simp, ?_⟩
  rcases sideMultigraph_ends A i with h | h
  · exact Or.inl h
  · exact Or.inr h

variable [DecidableEq W]

theorem source_step (outer : RetainedDart RS inner) (x y : W) :
    (sideMultigraph (asOpen T)).Step x y ↔
      (sideMultigraph (OpenTangleData.ofVertexSide RS inner outer)).Step (M.vertex x) (M.vertex y) := by
  rw [step_iff_dart, step_iff_dart]
  constructor
  · rintro ⟨i, hi, hj⟩
    refine ⟨internalEquiv M i, ?_, ?_⟩
    · exact (internal_vertex M outer i).symm.trans (congrArg M.vertex hi)
    · change (OpenTangleData.ofVertexSide RS inner outer).interiorVert
        (internalAlpha RS inner (internalEquiv M i)) = _
      rw [← internalEquiv_alpha]
      exact (internal_vertex M outer _).symm.trans (congrArg M.vertex hj)
  · rintro ⟨j, hx, hy⟩
    obtain ⟨i, rfl⟩ := (internalEquiv M).surjective j
    refine ⟨i, M.vertex.injective ?_, M.vertex.injective ?_⟩
    · exact (internal_vertex M outer i).trans hx
    · change M.vertex (T.interiorVert (T.interiorAlpha i)) = _
      rw [internal_vertex M outer, internalEquiv_alpha]
      exact hy

theorem source_reach (outer : RetainedDart RS inner) (x y : W) :
    (sideMultigraph (asOpen T)).Reach x y ↔
      (sideMultigraph (OpenTangleData.ofVertexSide RS inner outer)).Reach (M.vertex x) (M.vertex y) := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hs ih => exact ih.tail ((source_step M outer _ _).mp hs)
  · intro h
    have lift {u v} (h : (sideMultigraph (OpenTangleData.ofVertexSide RS inner outer)).Reach u v) :
        (sideMultigraph (asOpen T)).Reach (M.vertex.symm u) (M.vertex.symm v) := by
      induction h with
      | refl => exact .refl
      | tail _ hs ih =>
        exact ih.tail ((source_step M outer _ _).mpr (by simpa only [Equiv.apply_symm_apply] using hs))
    simpa only [Equiv.symm_apply_apply] using lift h

def sourceComponents (outer : RetainedDart RS inner) :
    Quotient (BoundarySmallCutViability.componentSetoid (sideMultigraph (asOpen T))) ≃
      Quotient (BoundarySmallCutViability.componentSetoid
        (sideMultigraph (OpenTangleData.ofVertexSide RS inner outer))) :=
  Quotient.congr M.vertex (source_reach M outer)

include M in
theorem source_defect (outer : RetainedDart RS inner) :
    VertexAttachmentTransfer.defect T =
      OpenTangleEulerPresentation.defect (OpenTangleData.ofVertexSide RS inner outer) := by
  have hc := Nat.card_congr (sourceComponents M outer)
  unfold VertexAttachmentTransfer.defect OpenTangleEulerPresentation.defect
  rw [hc, source_mass M outer]

end
end Mettapedia.GraphTheory.FourColor.VertexCodeSourceSemantics
