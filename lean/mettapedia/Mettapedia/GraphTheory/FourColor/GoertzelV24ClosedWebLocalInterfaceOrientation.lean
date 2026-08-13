import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalInterfaceMatching

/-!
# Orientation at consecutive source-local Cell-3 interfaces

The local Cell-3 construction already knows that the outgoing rung of one
corridor face is the incoming rung of the next.  This file records the
oriented-dart form of that fact directly on the closed-web carrier.  It is a
local interface fact only: it neither constructs a long annular transversal
nor treats overlapping local layer windows as a serial open-tangle composite.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance

namespace LocalLayerFormation

/-- Advancing one internal corridor face makes its incoming corridor step
definitionally the preceding face's outgoing step.  This is index arithmetic,
not a global annular construction. -/
theorem nextLocalCorridorInterior_incoming_eq_outgoing
    {corridorLength : Nat} (interior : CorridorInterior corridorLength)
    (hnext : interior.center.val + 2 < corridorLength) :
    (nextCorridorInterior interior hnext).incoming = interior.outgoing := by
  have hleft : (nextCorridorInterior interior hnext).incoming.left =
      interior.outgoing.left := by
    simp [nextCorridorInterior, CorridorInterior.incoming,
      CorridorInterior.outgoing]
  cases hright : (nextCorridorInterior interior hnext).incoming with
  | mk rightLeft rightProof =>
      cases hleftStep : interior.outgoing with
      | mk leftLeft leftProof =>
          simp only [hright, hleftStep, CorridorStep.mk.injEq] at hleft ⊢
          exact hleft

/-- **L9 (local interface orientation).** The literal incoming dart of a
consecutive Cell-3 face is the `alpha`-opposite of the preceding outgoing
dart.  The proof uses the actual local interior-face certificate, rather than
assuming globally two-sided annular faces. -/
theorem nextLocalPlacement_incomingDart_eq_alpha_outgoingDart
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (leftPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique leftInterior)
    (rightPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique (nextCorridorInterior leftInterior hnext)) :
    faceCycleDart web.annular.RS rightPlacement.root rightPlacement.incomingPosition =
      web.annular.RS.alpha
        (faceCycleDart web.annular.RS leftPlacement.root
          leftPlacement.outgoingPosition) := by
  let rightInterior := nextCorridorInterior leftInterior hnext
  let leftDart :=
    faceCycleDart web.annular.RS leftPlacement.root leftPlacement.outgoingPosition
  let rightDart :=
    faceCycleDart web.annular.RS rightPlacement.root rightPlacement.incomingPosition
  have hsteps : rightInterior.incoming = leftInterior.outgoing := by
    simpa [rightInterior] using
      nextLocalCorridorInterior_incoming_eq_outgoing leftInterior hnext
  have hedge : web.annular.RS.edgeOf rightDart = web.annular.RS.edgeOf leftDart := by
    calc
      web.annular.RS.edgeOf rightDart =
          corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.rungEdge
            hunique rightInterior.incoming := rightPlacement.incoming_edge
      _ = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.rungEdge
            hunique leftInterior.outgoing := by rw [hsteps]
      _ = web.annular.RS.edgeOf leftDart := leftPlacement.outgoing_edge.symm
  have hleftFace : dartOrbitFace web.annular.RS leftDart =
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        leftInterior.center).1 := by
    calc
      dartOrbitFace web.annular.RS leftDart =
          dartOrbitFace web.annular.RS leftPlacement.root :=
        dartOrbitFace_faceCycleDart web.annular.RS leftPlacement.root
          leftPlacement.outgoingPosition
      _ = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        leftInterior.center).1 := leftPlacement.root_face
  have hleftInternal : dartOrbitFace web.annular.RS leftDart ∈
      web.annular.cellulation.interiorFaces := by
    rw [hleftFace]
    exact corridor.face_internal leftInterior.center
  have hrightFace : dartOrbitFace web.annular.RS rightDart =
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        rightInterior.center).1 := by
    calc
      dartOrbitFace web.annular.RS rightDart =
          dartOrbitFace web.annular.RS rightPlacement.root :=
        dartOrbitFace_faceCycleDart web.annular.RS rightPlacement.root
          rightPlacement.incomingPosition
      _ = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        rightInterior.center).1 := rightPlacement.root_face
  have halphaFace : dartOrbitFace web.annular.RS (web.annular.RS.alpha leftDart) =
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        rightInterior.center).1 := by
    simpa [rightInterior, nextCorridorInterior] using
      localOutgoingAlphaFace_eq_nextCenter (corridor := corridor) hnext leftPlacement
  rcases web.annular.RS.edge_fiber_two_cases
      (e := web.annular.RS.edgeOf leftDart) (d := leftDart) (y := rightDart)
      rfl hedge with hsame | hopposite
  · exfalso
    apply InteriorFace.dartOrbitFace_ne_alpha web leftDart hleftInternal
    calc
      dartOrbitFace web.annular.RS leftDart =
          dartOrbitFace web.annular.RS rightDart :=
        congrArg (dartOrbitFace web.annular.RS) hsame.symm
      _ = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        rightInterior.center).1 := hrightFace
      _ = dartOrbitFace web.annular.RS (web.annular.RS.alpha leftDart) :=
        halphaFace.symm
  · exact hopposite

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
