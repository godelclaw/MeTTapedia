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
    ambientFaceOrbit_eq_of_openFaceOrbit_eq RS keep outer leftRoot rightRoot
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

/-- **L1 (literal side-face images after opening).** Under the same local
retention hypotheses as the ambient classification, every open common
neighbour is one of the two explicit opposite-dart side-face images of the
closed Cell-3 placement.

This removes the arbitrary ambient representative from the conclusion.  It
still does not identify the opened rotation system with the source-local
annular carrier; that source formation theorem remains a separate adapter. -/
theorem open_commonNeighbor_eq_sideFaceImage
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
    (∃ hbeforeRetained : FaceFullyRetained graphData.toRotationSystem keep
        (graphData.toRotationSystem.alpha
          (faceCycleDart graphData.toRotationSystem placement.root before.1)),
      neighbor.1 = openFaceOrbit graphData.toRotationSystem keep outer
        (graphData.toRotationSystem.alpha
          (faceCycleDart graphData.toRotationSystem placement.root before.1))
        hbeforeRetained) ∨
      (∃ hafterRetained : FaceFullyRetained graphData.toRotationSystem keep
          (graphData.toRotationSystem.alpha
            (faceCycleDart graphData.toRotationSystem placement.root after.1)),
        neighbor.1 = openFaceOrbit graphData.toRotationSystem keep outer
          (graphData.toRotationSystem.alpha
            (faceCycleDart graphData.toRotationSystem placement.root after.1))
          hafterRetained) := by
  rcases exists_ambient_side_rep_of_open_commonNeighbor graphData minimal
      corridor keep outer hretained hneighborRetained placement before after
      hbefore hafter neighbor hleft hright with
    ⟨neighborRoot, hneighborRoot, hneighborImage,
      hbeforeFace | hafterFace⟩
  · left
    let beforeRoot := graphData.toRotationSystem.alpha
      (faceCycleDart graphData.toRotationSystem placement.root before.1)
    have hbeforeFace' :
        dartOrbitFace graphData.toRotationSystem neighborRoot =
          dartOrbitFace graphData.toRotationSystem beforeRoot := by
      change dartOrbitFace graphData.toRotationSystem neighborRoot =
        dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha
            (faceCycleDart graphData.toRotationSystem placement.root before.1))
        at hbeforeFace
      exact hbeforeFace
    have hbeforeRoot : FaceFullyRetained graphData.toRotationSystem keep
        beforeRoot :=
      faceFullyRetained_of_dartOrbitFace_eq graphData.toRotationSystem keep
        hneighborRoot hbeforeFace'
    refine ⟨hbeforeRoot, hneighborImage.trans ?_⟩
    apply openFaceOrbit_eq_of_ambientFaceOrbit_eq graphData.toRotationSystem
      keep outer
      neighborRoot beforeRoot hneighborRoot hbeforeRoot
    exact hbeforeFace'
  · right
    let afterRoot := graphData.toRotationSystem.alpha
      (faceCycleDart graphData.toRotationSystem placement.root after.1)
    have hafterFace' :
        dartOrbitFace graphData.toRotationSystem neighborRoot =
          dartOrbitFace graphData.toRotationSystem afterRoot := by
      change dartOrbitFace graphData.toRotationSystem neighborRoot =
        dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha
            (faceCycleDart graphData.toRotationSystem placement.root after.1))
        at hafterFace
      exact hafterFace
    have hafterRoot : FaceFullyRetained graphData.toRotationSystem keep
        afterRoot :=
      faceFullyRetained_of_dartOrbitFace_eq graphData.toRotationSystem keep
        hneighborRoot hafterFace'
    refine ⟨hafterRoot, hneighborImage.trans ?_⟩
    apply openFaceOrbit_eq_of_ambientFaceOrbit_eq graphData.toRotationSystem
      keep outer
      neighborRoot afterRoot hneighborRoot hafterRoot
    exact hafterFace'

end

end GoertzelV24OpenRegionMinimalCorridorCommonNeighbors

end Mettapedia.GraphTheory.FourColor
