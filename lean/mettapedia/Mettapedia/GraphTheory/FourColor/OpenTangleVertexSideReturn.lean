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
open GoertzelV24CanonicalHubClosure GoertzelV24CompositeSeamCubic
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24VertexSideOpenTangle

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

section GraphBacked

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance sideReturnEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance sideReturnEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- A connected shore with connected complement in a spherical map exposes
all its ports on one open face. The conclusion uses the actual retained darts. -/
theorem ports_cofacial_of_planarBond
    (rotation : SimpleGraphDartRotation.Data G) (deleted : Finset V)
    (root : RetainedDart rotation.toRotationSystem (deletedRegionKeep deleted))
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hretained : (G.induce {v | deletedRegionKeep deleted v}).Connected)
    (hdeleted : (G.induce {v | ¬ deletedRegionKeep deleted v}).Connected)
    (b c : BoundaryDart rotation.toRotationSystem (deletedRegionKeep deleted)) :
    (openPhi (ofVertexSide rotation.toRotationSystem (deletedRegionKeep deleted) root)).SameCycle
      (.inr b) (.inr c) := by
  let RS := rotation.toRotationSystem
  let side := deletedRegionKeep deleted
  let T := ofVertexSide RS side root
  have hretained' : ((rotationPrimalGraph RS).induce {v | side v}).Connected := by
    simpa [RS, side,
      GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq]
      using hretained
  have hside : (sideMultigraph T).Connected :=
    sideMultigraph_connected_of_induce_connected RS side root hretained'
  have hr : OpenRotationCyclic T := openRotationCyclic_ofVertexSide RS side root hrotation
  have hc : OpenIsCubic T := openIsCubic_ofVertexSide RS side root hsphere.cubic
  have hclosed := closedSideSpherical_canonical_of_planarBond rotation deleted root
    hsphere htwo hconnected hrotation hretained hdeleted
  have hcount := orbitCount_hubRotation_eq_one_of_closedSideSpherical T
    (canonicalHubRotation RS side) hside hr hc b hclosed
  have hhub := sameCycle_all_of_orbitCount_eq_one _ hcount b c
  have hsuccessor : (retainedRegionBoundarySuccessor RS side).SameCycle b c :=
    hhub.of_inv
  rw [← returnCode_eq RS side root] at hsuccessor
  let first : {d // Boundary (I := InternalDart RS side) d} := ⟨.inr b, trivial⟩
  let last : {d // Boundary (I := InternalDart RS side) d} := ⟨.inr c, trivial⟩
  have hnext : (nextHitPerm (openPhi T) Boundary).SameCycle first last :=
    (permCongr_sameCycle_iff
      (boundaryCoordinate (InternalDart RS side) (BoundaryDart RS side))
      (nextHitPerm (openPhi T) Boundary) first last).1 hsuccessor
  exact (nextHitPerm_sameCycle_iff (openPhi T) Boundary first last).1 hnext

end GraphBacked

end
end Mettapedia.GraphTheory.FourColor.OpenTangleVertexSideReturn
