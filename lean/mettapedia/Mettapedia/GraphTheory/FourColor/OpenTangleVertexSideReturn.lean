import Mettapedia.GraphTheory.FourColor.OpenTanglePortReplacement
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedRegionBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24CanonicalHubCyclicity

/-! # First return on a literal vertex shore

The open-tangle port code and the ambient retained-region successor compute
the same walk. The internal/boundary partition changes only its coordinates.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleVertexSideReturn

open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24OrderedCutFaceReturnProfile OpenTangleMarkedFace
open OpenTanglePortReplacement SerialTangleFaceTransfer SerialTangleFaceCode
open GoertzelV24CompositeSeamMultigraph GoertzelV24CanonicalHubCyclicity
open GoertzelV24FaceDualConnectedness

noncomputable section
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem V E) (keep : V → Prop) (outer : RetainedDart RS keep)

theorem face_perm :
    retainedCappedFacePerm RS keep =
      (retainedDartEquivInternalSumBoundary RS keep).symm.permCongr
        (openPhi (ofVertexSide RS keep outer)) := by
  apply Equiv.ext
  intro d
  obtain ⟨x, rfl⟩ := (retainedDartEquivInternalSumBoundary RS keep).symm.surjective d
  rw [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  change retainedRho RS keep (retainedCappedAlpha RS keep _) =
    (retainedDartEquivInternalSumBoundary RS keep).symm
      ((ofVertexSide RS keep outer).rho _)
  rw [ofVertexSide_rho_underlying]
  apply congrArg (retainedRho RS keep)
  cases x with
  | inl i =>
    apply Subtype.ext
    exact retainedCappedAlpha_apply_internal RS keep i.1 i.2
  | inr b =>
    exact retainedCappedAlpha_apply_boundary RS keep b.1 b.2

theorem boundary_iff (d : InternalDart RS keep ⊕ BoundaryDart RS keep) :
    Boundary d ↔ ¬ keep (RS.vertOf (RS.alpha
      ((retainedDartEquivInternalSumBoundary RS keep).symm d).1)) := by
  cases d with
  | inl i => exact iff_of_false id (not_not_intro i.2)
  | inr b => exact iff_of_true trivial b.2

/-- This equality links literal graph recognition to cyclic boundary geometry. -/
theorem returnCode_eq :
    returnCode (ofVertexSide RS keep outer) = retainedRegionBoundarySuccessor RS keep := by
  classical
  let e := (retainedDartEquivInternalSumBoundary RS keep).symm
  have hb : e.subtypeEquiv (boundary_iff RS keep) =
      boundaryCoordinate (InternalDart RS keep) (BoundaryDart RS keep) := by
    apply Equiv.ext
    rintro ⟨i | b, h⟩
    · exact h.elim
    · rfl
  unfold retainedRegionBoundarySuccessor
  rw [face_perm RS keep outer,
    nextHitPerm_permCongr e _ Boundary _ (boundary_iff RS keep), hb]
  rfl

/-- Connectivity of the literal internal edges is connectivity of the
induced ambient graph. Nonemptiness is witnessed by the retained root. -/
theorem induce_connected
    (h : (sideMultigraph (ofVertexSide RS keep outer)).Connected) :
    ((rotationPrimalGraph RS).induce {v | keep v}).Connected := by
  refine { nonempty := ⟨⟨RS.vertOf outer.1, outer.2⟩⟩, preconnected := ?_ }
  intro u v
  have hp := h u v
  induction hp with
  | refl => exact .refl _
  | tail _ hs ih =>
    obtain ⟨i, hi, hj⟩ := exists_interiorDart_of_sideStep (ofVertexSide RS keep outer) hs
    have ha : (rotationPrimalGraph RS).Adj _ _ :=
      (rotationPrimalGraph_adj_iff RS).mpr
        ⟨i.1.1, congrArg Subtype.val hi, congrArg Subtype.val hj⟩
    exact ih.trans (SimpleGraph.Adj.reachable
      (G := (rotationPrimalGraph RS).induce {v | keep v}) ha)

end
end Mettapedia.GraphTheory.FourColor.OpenTangleVertexSideReturn
