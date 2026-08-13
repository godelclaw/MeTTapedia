import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalCorridorCommonNeighbors
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionCleanHexCorridorTransport

/-!
# L1 common-neighbour classification through a literal opening

The closed minimal-counterexample theorem classifies every common neighbour
of two consecutive corridor faces as one of the two literal outgoing side
faces.  This file transports that classification across an arbitrary literal
opening whose radius-one corridor neighbourhood is fully retained.

The conclusion deliberately retains an ambient representative of the open
face.  It does not identify dependent open and closed face carriers by
cardinality, and it does not assume that the opened carrier itself satisfies
closed cubic minimality.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionMinimalCorridorCommonNeighbors

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24MinimalCorridorCommonNeighbors
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OpenRegionCleanHexCorridorTransport
open GoertzelV24OpenRegionFaceTransport
open GoertzelV24OpenRegionHexCorridorTransport
open GoertzelV24OpenRegionRotation
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrientedHexSlab
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

-- The proposition-generic retained-vertex instances would otherwise also
-- match the ambient edge subtype `G.edgeSet`.
attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Full retention depends only on the ambient face orbit, not on its chosen
root dart. -/
theorem faceFullyRetained_of_dartOrbitFace_eq
    (RS : RotationSystem V G.edgeSet) (keep : V → Prop)
    {leftRoot rightRoot : RS.D}
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hfaces : dartOrbitFace RS leftRoot = dartOrbitFace RS rightRoot) :
    FaceFullyRetained RS keep rightRoot := by
  intro point hrightPoint
  apply hleft point
  exact (Quotient.exact hfaces).trans hrightPoint

/-- Equality of fully retained open-face images reflects equality of their
ambient face orbits. -/
theorem dartOrbitFace_eq_of_openFaceOrbit_eq
    (RS : RotationSystem V G.edgeSet) (keep : V → Prop)
    (outer : Dart RS keep) (leftRoot rightRoot : RS.D)
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hright : FaceFullyRetained RS keep rightRoot)
    (hopen : openFaceOrbit RS keep outer leftRoot hleft =
      openFaceOrbit RS keep outer rightRoot hright) :
    dartOrbitFace RS leftRoot = dartOrbitFace RS rightRoot := by
  by_contra hambient
  exact (openFaceOrbit_ne_of_ambient_ne RS keep outer leftRoot rightRoot
    hleft hright hambient) hopen

/-- **L1 (closed classification transported through opening).** Every common
open neighbour of two consecutive images of a closed minimal corridor has a
fully retained ambient representative, and that representative is one of the
two literal side faces selected by the closed Cell-3 placement.

The radius-one retention hypothesis is explicit.  Without it an open face can
be a boundary-spliced fragment rather than the image of one ambient face. -/
theorem exists_ambient_side_rep_of_open_commonNeighbor
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton graphData.toRotationSystem
      corridorLength)
    (keep : V → Prop) (outer : Dart graphData.toRotationSystem keep)
    (hretained : ∀ offset,
      FaceFullyRetained graphData.toRotationSystem keep
        (orbitFaceRoot graphData.toRotationSystem
          (corridor.faceAt offset).1))
    (hneighborRetained : ∀ offset,
      ∀ neighbor : AmbientFace
        (Finset.univ : Finset (OrbitFace graphData.toRotationSystem)),
        (interiorDualGraph
          (orbitFaceBoundary graphData.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace graphData.toRotationSystem))).Adj
            (corridor.faceAt offset) neighbor →
          FaceFullyRetained graphData.toRotationSystem keep
            (orbitFaceRoot graphData.toRotationSystem neighbor.1))
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor
      (pairwiseUniqueSharedInteriorEdges graphData minimal) interior)
    (before after : {position // position ∈ placementSidePositions placement})
    (hbefore : placement.outgoingPosition.val ≡ before.1.val + 1 [MOD 6])
    (hafter : after.1.val ≡ placement.outgoingPosition.val + 1 [MOD 6])
    (neighbor : AmbientFace
      (Finset.univ : Finset
        (OrbitFace (rotationSystem graphData.toRotationSystem keep outer))))
    (hleft : (interiorDualGraph
      (orbitFaceBoundary
        (rotationSystem graphData.toRotationSystem keep outer))
      (Finset.univ : Finset
        (OrbitFace
          (rotationSystem graphData.toRotationSystem keep outer)))).Adj
        (openOrbitHexCorridorSkeleton graphData.toRotationSystem
          minimal.facesTwoSided corridor keep outer hretained |>.faceAt
            interior.center)
        neighbor)
    (hright : (interiorDualGraph
      (orbitFaceBoundary
        (rotationSystem graphData.toRotationSystem keep outer))
      (Finset.univ : Finset
        (OrbitFace
          (rotationSystem graphData.toRotationSystem keep outer)))).Adj
        (openOrbitHexCorridorSkeleton graphData.toRotationSystem
          minimal.facesTwoSided corridor keep outer hretained |>.faceAt
            interior.outgoing.right)
        neighbor) :
    ∃ neighborRoot : graphData.toRotationSystem.D,
      ∃ hneighbor : FaceFullyRetained graphData.toRotationSystem keep
          neighborRoot,
        neighbor.1 = openFaceOrbit graphData.toRotationSystem keep outer
            neighborRoot hneighbor ∧
          (dartOrbitFace graphData.toRotationSystem neighborRoot =
              (placementSideFace placement before).1 ∨
            dartOrbitFace graphData.toRotationSystem neighborRoot =
              (placementSideFace placement after).1) := by
  let RS := graphData.toRotationSystem
  let centerRoot := orbitFaceRoot RS (corridor.faceAt interior.center).1
  let nextRoot := orbitFaceRoot RS
    (corridor.faceAt interior.outgoing.right).1
  have hleft' : (interiorDualGraph
      (orbitFaceBoundary (rotationSystem RS keep outer))
      (Finset.univ : Finset
        (OrbitFace (rotationSystem RS keep outer)))).Adj
        ⟨openFaceOrbit RS keep outer centerRoot (hretained interior.center),
          Finset.mem_univ _⟩ neighbor := by
    simpa [openOrbitHexCorridorSkeleton, centerRoot] using hleft
  have hright' : (interiorDualGraph
      (orbitFaceBoundary (rotationSystem RS keep outer))
      (Finset.univ : Finset
        (OrbitFace (rotationSystem RS keep outer)))).Adj
        ⟨openFaceOrbit RS keep outer nextRoot
          (hretained interior.outgoing.right), Finset.mem_univ _⟩ neighbor := by
    simpa [openOrbitHexCorridorSkeleton, nextRoot] using hright
  have neighborRetainedAt (offset : Fin corridorLength)
      (root : RS.D)
      (hadj : (interiorDualGraph (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).Adj
          (corridor.faceAt offset)
          ⟨dartOrbitFace RS root, Finset.mem_univ _⟩) :
      FaceFullyRetained RS keep root := by
    apply faceFullyRetained_of_dartOrbitFace_eq RS keep
      (hneighborRetained offset
        ⟨dartOrbitFace RS root, Finset.mem_univ _⟩ hadj)
    exact GoertzelV24OpenRegionHexCorridorTransport.dartOrbitFace_orbitFaceRoot
      RS (dartOrbitFace RS root)
  rcases exists_retained_ambient_neighbor_of_openFaceOrbit_adj
      RS minimal.facesTwoSided keep outer centerRoot
      (hretained interior.center)
      (fun root hadj => neighborRetainedAt interior.center root (by
        simpa [centerRoot] using hadj)) neighbor hleft' with
    ⟨leftRoot, hleftRetained, hleftAmbient, hleftImage⟩
  rcases exists_retained_ambient_neighbor_of_openFaceOrbit_adj
      RS minimal.facesTwoSided keep outer nextRoot
      (hretained interior.outgoing.right)
      (fun root hadj => neighborRetainedAt interior.outgoing.right root (by
        simpa [nextRoot] using hadj)) neighbor hright' with
    ⟨rightRoot, hrightRetained, hrightAmbient, hrightImage⟩
  have hopenImages : openFaceOrbit RS keep outer leftRoot hleftRetained =
      openFaceOrbit RS keep outer rightRoot hrightRetained := by
    exact hleftImage.symm.trans hrightImage
  have hambientFaces : dartOrbitFace RS leftRoot =
      dartOrbitFace RS rightRoot :=
    dartOrbitFace_eq_of_openFaceOrbit_eq RS keep outer leftRoot rightRoot
      hleftRetained hrightRetained hopenImages
  have hleftClosed : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        (corridor.faceAt interior.center)
        ⟨dartOrbitFace RS leftRoot, Finset.mem_univ _⟩ := by
    simpa [centerRoot] using hleftAmbient
  have hrightClosed : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        (corridor.faceAt interior.outgoing.right)
        ⟨dartOrbitFace RS leftRoot, Finset.mem_univ _⟩ := by
    have hrightAmbient' := hrightAmbient
    simpa [nextRoot, hambientFaces] using hrightAmbient'
  have hclassified := commonNeighbor_eq_outgoing_sideFace graphData minimal
    corridor placement before after hbefore hafter
      ⟨dartOrbitFace RS leftRoot, Finset.mem_univ _⟩
      hleftClosed hrightClosed
  refine ⟨leftRoot, hleftRetained, hleftImage, ?_⟩
  rcases hclassified with hbeforeFace | hafterFace
  · exact Or.inl (congrArg Subtype.val hbeforeFace)
  · exact Or.inr (congrArg Subtype.val hafterFace)

end

end GoertzelV24OpenRegionMinimalCorridorCommonNeighbors

end Mettapedia.GraphTheory.FourColor
