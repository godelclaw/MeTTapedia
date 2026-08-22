import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseSuccessorTrackedProfile

/-!
# A complete finite successor-profile receipt for an actual source rebase

The successor tracked state and successor facial receipt now describe the
same literal terminal-aware cut.  Their product is therefore one finite packet
for all five source-profile coordinates: crossing colour, tracked
connectivity, ambient-face continuation, port incidence, and capped regional
progress.  The fieldwise theorems below decode each observation exactly from
the actual successor profile.

This packet is relational evidence carried by a literal rebase.  It does not
claim that the predecessor packet determines it, identify its support with a
positive `Count` entry, or bound the reachable closure.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseFiniteProfileReceiptEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- One fixed finite packet carrying every successor profile observation. -/
structure SourceLocalLayerBoundaryRebaseFiniteProfileReceipt where
  tracked : SourceLocalLayerBoundaryRebaseTrackedState
  facial : SourceLocalLayerBoundaryRebaseFiniteFaceReceipt

noncomputable instance :
    DecidableEq SourceLocalLayerBoundaryRebaseFiniteProfileReceipt :=
  Classical.decEq _

private def sourceLocalLayerBoundaryRebaseFiniteProfileReceiptEquiv :
    SourceLocalLayerBoundaryRebaseFiniteProfileReceipt ≃
      SourceLocalLayerBoundaryRebaseTrackedState ×
        SourceLocalLayerBoundaryRebaseFiniteFaceReceipt where
  toFun := fun receipt => ⟨receipt.tracked, receipt.facial⟩
  invFun := fun receipt => ⟨receipt.1, receipt.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

noncomputable instance :
    Fintype SourceLocalLayerBoundaryRebaseFiniteProfileReceipt :=
  Fintype.ofEquiv _ sourceLocalLayerBoundaryRebaseFiniteProfileReceiptEquiv.symm

/-- Extract the complete finite successor packet of one literal rebase. -/
noncomputable def sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerBoundaryRebaseFiniteProfileReceipt where
  tracked := sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt corridor
    hunique offset hnext
  facial := sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique
    offset hnext

/-- The joint packet decodes the literal successor crossing colours. -/
theorem sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_edgeColor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (crossing : Fin 2) :
    (sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt corridor hunique
      offset hnext).tracked.roleColor
        (sourceLocalLayerBoundaryRebaseSuccessorPortRole (.inl crossing)) =
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).profile.edgeColor crossing :=
  sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt_edgeColor_profile
    corridor hunique offset hnext crossing

/-- The joint packet decodes every literal successor tracked-connectivity
bit. -/
theorem sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_strandConnected
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair) (left right : CorridorPort 2 1) :
    (sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt corridor hunique
      offset hnext).tracked.connected pair
        (sourceLocalLayerBoundaryRebaseSuccessorPortRole left)
        (sourceLocalLayerBoundaryRebaseSuccessorPortRole right) ↔
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).profile.strandConnected
          pair left right = true :=
  sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt_connected_profile
    corridor hunique offset hnext pair left right

/-- The joint packet decodes every literal successor ambient-face bit. -/
theorem sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_faceContinues
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : Fin (Fintype.card
      (SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor hunique
        offset hnext))) :
    (sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt corridor hunique
      offset hnext).facial.faceContinues
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext
          (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
            hunique offset hnext left))
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext
          (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
            hunique offset hnext right)) =
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).profile.faceContinues
          left right :=
  sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_faceContinues_profile
    corridor hunique offset hnext left right

/-- The joint packet decodes every literal successor port-incidence bit. -/
theorem sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_fragmentContainsPort
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (fragment : Fin (Fintype.card
      (SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor hunique
        offset hnext)))
    (port : CorridorPort 2 1) :
    (sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt corridor hunique
      offset hnext).facial.fragmentContainsPort
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext
          (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
            hunique offset hnext fragment)) port =
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).profile.fragmentContainsPort
          fragment port :=
  sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_fragmentContainsPort_profile
    corridor hunique offset hnext fragment port

/-- The joint packet decodes every literal successor capped-progress row. -/
theorem sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_faceLengthCap
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (fragment : Fin (Fintype.card
      (SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor hunique
        offset hnext))) :
    (sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt corridor hunique
      offset hnext).facial.faceLengthCap
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext
          (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
            hunique offset hnext fragment)) =
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).profile.faceLengthCap
          fragment :=
  sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_faceLengthCap_profile
    corridor hunique offset hnext fragment

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
