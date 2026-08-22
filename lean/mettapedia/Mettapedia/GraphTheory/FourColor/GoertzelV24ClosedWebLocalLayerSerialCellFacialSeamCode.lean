import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedFaceSeamFamilyCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellTrackedSeamFamilyCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFullProfileRelation
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialTerminalProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationAllFaceCutProfile

/-!
# Finite occurrence code for one opened-source facial Cell seam

The opened annulus is not globally face-two-sided: a boundary-stub edge has
both darts on the same hole face.  Hence the facial residue must not be
compressed by pretending that a face contains each underlying edge once.

Instead this module counts actual cyclic occurrences.  Each of the two
outgoing portal edges has at most two dart occurrences on a fixed face, and
each occurrence has at most two cyclic neighbors.  Portal completeness then
places the complete non-isolated facial seam in a twelve-position carrier.
The resulting support code preserves the occurrence-sensitive graph exactly.

This is the facial connectivity residue.  Its subsequent attachment to the
finite face-continuation, port-incidence, and capped-progress receipt remains
a separate theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundedSupportGraphCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24FramedTrail
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace FacialOccurrenceCarrier

/-- Positions on one facial orbit whose underlying edge lies in a selected
finite edge set. -/
def positionsOnEdges (RS : RotationSystem V E) (root : RS.D)
    (edges : Finset E) : Finset (Fin (RS.faceOrbit root).card) :=
  Finset.univ.filter fun position => faceCycleEdge RS root position ∈ edges

@[simp]
theorem mem_positionsOnEdges_iff (RS : RotationSystem V E) (root : RS.D)
    (edges : Finset E) (position : Fin (RS.faceOrbit root).card) :
    position ∈ positionsOnEdges RS root edges ↔
      faceCycleEdge RS root position ∈ edges := by
  simp [positionsOnEdges]

/-- Every selected edge contributes at most its two dart occurrences to one
facial cycle, even when both occurrences lie on the same face. -/
theorem positionsOnEdges_card_le_two_mul
    (RS : RotationSystem V E) (root : RS.D) (edges : Finset E) :
    (positionsOnEdges RS root edges).card ≤ 2 * edges.card := by
  let positions := positionsOnEdges RS root edges
  let darts := edges.biUnion RS.dartsOn
  have hsubset :
      positions.image (faceCycleDart RS root) ⊆ darts := by
    intro dart hdart
    rcases Finset.mem_image.1 hdart with ⟨position, hposition, rfl⟩
    apply Finset.mem_biUnion.2
    exact ⟨faceCycleEdge RS root position,
      (mem_positionsOnEdges_iff RS root edges position).1 hposition,
      (RS.mem_dartsOn).2 rfl⟩
  calc
    positions.card =
        (positions.image (faceCycleDart RS root)).card :=
      (Finset.card_image_of_injective positions
        (faceCycleDart_injective RS root)).symm
    _ ≤ darts.card := Finset.card_le_card hsubset
    _ ≤ edges.card * 2 :=
      Finset.card_biUnion_le_card_mul _ _ _ fun edge _ =>
        le_of_eq (RS.dartsOn_card_two edge)
    _ = 2 * edges.card := by omega

/-- The finite set of cyclic neighbors of one facial position.  Defining the
finset directly avoids depending on a choice of local-finiteness instance. -/
def positionNeighbors (RS : RotationSystem V E) (root : RS.D)
    (position : Fin (RS.faceOrbit root).card) :
    Finset (Fin (RS.faceOrbit root).card) := by
  classical
  exact Finset.univ.filter fun neighbor =>
    (faceCyclePositionGraph RS root).Adj position neighbor

@[simp]
theorem mem_positionNeighbors_iff (RS : RotationSystem V E) (root : RS.D)
    (position neighbor : Fin (RS.faceOrbit root).card) :
    neighbor ∈ positionNeighbors RS root position ↔
      (faceCyclePositionGraph RS root).Adj position neighbor := by
  classical
  simp [positionNeighbors]

/-- A cyclic facial position has at most its successor and predecessor as
neighbors.  This proof uses dart occurrences, not edge injectivity. -/
theorem positionNeighbors_card_le_two
    (RS : RotationSystem V E) (root : RS.D)
    (position : Fin (RS.faceOrbit root).card) :
    (positionNeighbors RS root position).card ≤ 2 := by
  let neighbors := positionNeighbors RS root position
  let dart := faceCycleDart RS root position
  have hsubset :
      neighbors.image (faceCycleDart RS root) ⊆
        {RS.phi dart, RS.phi.symm dart} := by
    intro neighborDart hneighborDart
    rcases Finset.mem_image.1 hneighborDart with
      ⟨neighbor, hneighbor, rfl⟩
    have hadj : (faceCyclePositionGraph RS root).Adj position neighbor := by
      exact (mem_positionNeighbors_iff RS root position neighbor).1 hneighbor
    rcases hadj.2 with hforward | hbackward
    · simp [dart, hforward]
    · have hprev : faceCycleDart RS root neighbor = RS.phi.symm dart := by
        apply RS.phi.injective
        simpa [dart] using hbackward.symm
      simp [hprev]
  calc
    neighbors.card = (neighbors.image (faceCycleDart RS root)).card :=
      (Finset.card_image_of_injective neighbors
        (faceCycleDart_injective RS root)).symm
    _ ≤ ({RS.phi dart, RS.phi.symm dart} : Finset RS.D).card :=
      Finset.card_le_card hsubset
    _ ≤ 2 := Finset.card_le_two

/-- The cyclic closed neighborhood of every selected occurrence. -/
def closedCarrier (RS : RotationSystem V E) (root : RS.D)
    (edges : Finset E) : Finset (Fin (RS.faceOrbit root).card) :=
  (positionsOnEdges RS root edges).biUnion fun position =>
    insert position (positionNeighbors RS root position)

/-- Two dart occurrences per edge and three positions per closed cyclic
neighborhood give the uniform factor six. -/
theorem closedCarrier_card_le_six_mul
    (RS : RotationSystem V E) (root : RS.D) (edges : Finset E) :
    (closedCarrier RS root edges).card ≤ 6 * edges.card := by
  calc
    (closedCarrier RS root edges).card ≤
        (positionsOnEdges RS root edges).card * 3 := by
      apply Finset.card_biUnion_le_card_mul
      intro position _hposition
      calc
        (insert position (positionNeighbors RS root position)).card ≤
            (positionNeighbors RS root position).card + 1 :=
          Finset.card_insert_le _ _
        _ ≤ 2 + 1 := Nat.add_le_add_right
          (positionNeighbors_card_le_two RS root position) 1
        _ = 3 := by omega
    _ ≤ (2 * edges.card) * 3 :=
      Nat.mul_le_mul_right 3
        (positionsOnEdges_card_le_two_mul RS root edges)
    _ = 6 * edges.card := by omega

end FacialOccurrenceCarrier

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance closedWebLocalLayerSerialCellFacialSeamCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The actual occurrence carrier around the two outgoing source crossings
on one ambient face. -/
noncomputable def sourceLocalLayerSerialFaceOutgoingCarrierAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (root : web.annular.RS.D) :=
  FacialOccurrenceCarrier.closedCarrier web.annular.RS root
    (GoertzelV24RegionalBoundaryProfileFiniteState.indexedCrossingEdgeSet
      (sourceLocalLayerRightCrossingAt corridor hunique offset))

/-- The occurrence carrier of one actual facial Cell seam has at most twelve
positions, with no two-sidedness premise. -/
theorem sourceLocalLayerSerialFaceOutgoingCarrierAt_card_le_twelve
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (root : web.annular.RS.D) :
    (sourceLocalLayerSerialFaceOutgoingCarrierAt corridor hunique offset root
      ).card ≤ 12 := by
  calc
    (sourceLocalLayerSerialFaceOutgoingCarrierAt corridor hunique offset root
      ).card ≤
        6 * (GoertzelV24RegionalBoundaryProfileFiniteState.indexedCrossingEdgeSet
          (sourceLocalLayerRightCrossingAt corridor hunique offset)).card :=
      FacialOccurrenceCarrier.closedCarrier_card_le_six_mul
        web.annular.RS root _
    _ ≤ 6 * 2 := Nat.mul_le_mul_left 6
      (GoertzelV24RegionalBoundaryProfileFiniteState.card_indexedCrossingEdgeSet_le
        (sourceLocalLayerRightCrossingAt corridor hunique offset))
    _ = 12 := by norm_num

/-- Every non-isolated facial residual occurrence lies in the twelve-position
outgoing occurrence carrier. -/
theorem sourceLocalLayerSerialTerminalFaceSeamAt_support_subset_outgoingCarrier
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (root : web.annular.RS.D) :
    (sourceLocalLayerSerialTerminalFaceSeamAt corridor hunique offset root
      ).support ⊆
      sourceLocalLayerSerialFaceOutgoingCarrierAt corridor hunique offset root := by
  intro position hposition
  rcases (SimpleGraph.mem_support _).1 hposition with ⟨neighbor, hadj⟩
  have hfaceAdj : (faceCyclePositionGraph web.annular.RS root).Adj
      position neighbor :=
    ((GoertzelV24TerminalProfileSeamResidual.faceRegionalSeamGraph_adj_iff
      web.annular.RS root _ _ position neighbor).1 hadj).1
  rcases sourceLocalLayerSerialTerminalFaceSeamAt_adj_touches_rightCrossing
      corridor hunique offset root hadj with
    ⟨step, hpositionRight | hneighborRight⟩
  · apply Finset.mem_biUnion.2
    refine ⟨position, ?_, Finset.mem_insert_self _ _⟩
    exact (FacialOccurrenceCarrier.mem_positionsOnEdges_iff _ _ _ _).2
      (GoertzelV24RegionalBoundaryProfileFiniteState.mem_indexedCrossingEdgeSet_iff
        _ _ |>.2 ⟨step, hpositionRight.symm⟩)
  · apply Finset.mem_biUnion.2
    refine ⟨neighbor, ?_, Finset.mem_insert.2 (Or.inr ?_)⟩
    · exact (FacialOccurrenceCarrier.mem_positionsOnEdges_iff _ _ _ _).2
        (GoertzelV24RegionalBoundaryProfileFiniteState.mem_indexedCrossingEdgeSet_iff
          _ _ |>.2 ⟨step, hneighborRight.symm⟩)
    · exact (FacialOccurrenceCarrier.mem_positionNeighbors_iff _ _ _ _).2
        hfaceAdj.symm

/-- The actual facial residual has at most twelve participating occurrences. -/
theorem sourceLocalLayerSerialTerminalFaceSeamAt_support_card_le_twelve
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (root : web.annular.RS.D) :
    (sourceLocalLayerSerialTerminalFaceSeamAt corridor hunique offset root
      ).support.ncard ≤ 12 := by
  calc
    (sourceLocalLayerSerialTerminalFaceSeamAt corridor hunique offset root
      ).support.ncard ≤
        (sourceLocalLayerSerialFaceOutgoingCarrierAt corridor hunique offset
          root : Set _).ncard :=
      Set.ncard_le_ncard
        (sourceLocalLayerSerialTerminalFaceSeamAt_support_subset_outgoingCarrier
          corridor hunique offset root)
    _ = (sourceLocalLayerSerialFaceOutgoingCarrierAt corridor hunique offset
          root).card := Set.ncard_coe_finset _
    _ ≤ 12 := sourceLocalLayerSerialFaceOutgoingCarrierAt_card_le_twelve
      corridor hunique offset root

/-- The exact occurrence-sensitive facial seam stripped of isolated ambient
positions and transported to at most twelve finite coordinates. -/
noncomputable def sourceLocalLayerSerialTerminalFaceSeamCodeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (root : web.annular.RS.D) :
    BoundedSupportGraphCode 12 :=
  boundedSupportCode
    (sourceLocalLayerSerialTerminalFaceSeamAt corridor hunique offset root)
    12
    (sourceLocalLayerSerialTerminalFaceSeamAt_support_card_le_twelve corridor
      hunique offset root)

/-- The participating occurrence graph is isomorphic to its finite code. -/
noncomputable def sourceLocalLayerSerialTerminalFaceSeamCodeIsoAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (root : web.annular.RS.D) :
    let seam := sourceLocalLayerSerialTerminalFaceSeamAt corridor hunique offset
      root
    seam.induce seam.support ≃g
      (sourceLocalLayerSerialTerminalFaceSeamCodeAt corridor hunique offset
        root).graph := by
  dsimp only
  exact boundedSupportCodeIso _ 12
    (sourceLocalLayerSerialTerminalFaceSeamAt_support_card_le_twelve corridor
      hunique offset root)

/-- The occurrence-sensitive facial seam family, indexed by exactly the
actual output boundary fragments of the pre-rebase source cut. -/
noncomputable def sourceLocalLayerSerialTerminalFaceSeamFamilyCodeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    BoundedFaceSeamFamilyCode 4 12 := by
  let outputData :=
    sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique offset
  let fragmentCount := Fintype.card (BoundaryRegionalFragment
    web.annular.RS
    (indexedCrossingEdgeSet
      (sourceLocalLayerRightCrossingAt corridor hunique offset))
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset))
  have hfragmentCount : fragmentCount ≤ 4 := by
    exact regionalBoundaryGraphCutData_fragmentCount_le_two_mul
      web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      (sourceLocalLayerRightCrossingAt corridor hunique offset)
  refine
    { faceFragmentCount := ⟨fragmentCount, Nat.lt_succ_of_le hfragmentCount⟩
      seamCode := fun fragment =>
        sourceLocalLayerSerialTerminalFaceSeamCodeAt corridor hunique offset
          (orbitFaceRoot web.annular.RS
            (outputData.fragmentFace fragment)) }

/-- The family count is the literal output cut's canonical dependent fragment
count; no padded coordinate is identified with a real fragment. -/
theorem sourceLocalLayerSerialTerminalFaceSeamFamilyCodeAt_count
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    (sourceLocalLayerSerialTerminalFaceSeamFamilyCodeAt corridor hunique offset
      ).faceFragmentCount.val =
      Fintype.card (BoundaryRegionalFragment web.annular.RS
        (indexedCrossingEdgeSet
          (sourceLocalLayerRightCrossingAt corridor hunique offset))
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)) := by
  rfl

/-- One fixed finite packet for the complete source Cell update: its two
bounded profiles and the exact tracked and facial residual seam codes. -/
structure SourceLocalLayerSerialCellFiniteProfileReceipt where
  input : BoundedCorridorCutProfile 2 1 4
  output : BoundedCorridorCutProfile 2 0 4
  trackedSeam : BoundedCarrierGraphFamilyCode 14 2 TrackedColorPair
  facialSeam : BoundedFaceSeamFamilyCode 4 12

noncomputable instance :
    DecidableEq SourceLocalLayerSerialCellFiniteProfileReceipt :=
  Classical.decEq _

private def sourceLocalLayerSerialCellFiniteProfileReceiptEquiv :
    SourceLocalLayerSerialCellFiniteProfileReceipt ≃
      (BoundedCorridorCutProfile 2 1 4 ×
        BoundedCorridorCutProfile 2 0 4) ×
      (BoundedCarrierGraphFamilyCode 14 2 TrackedColorPair ×
        BoundedFaceSeamFamilyCode 4 12) where
  toFun receipt :=
    ⟨⟨receipt.input, receipt.output⟩,
      ⟨receipt.trackedSeam, receipt.facialSeam⟩⟩
  invFun receipt :=
    { input := receipt.1.1
      output := receipt.1.2
      trackedSeam := receipt.2.1
      facialSeam := receipt.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance :
    Fintype SourceLocalLayerSerialCellFiniteProfileReceipt :=
  Fintype.ofEquiv _ sourceLocalLayerSerialCellFiniteProfileReceiptEquiv.symm

/-- Extract the complete finite packet of one literal opened-source Cell. -/
noncomputable def sourceLocalLayerSerialCellFiniteProfileReceiptAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    SourceLocalLayerSerialCellFiniteProfileReceipt where
  input := sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
    offset
  output := sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt corridor
    hunique offset
  trackedSeam :=
    sourceLocalLayerSerialTerminalTrackedSeamFamilyCodeAt corridor hunique
      offset coloring
  facialSeam :=
    sourceLocalLayerSerialTerminalFaceSeamFamilyCodeAt corridor hunique offset

/-- The profiles stored in the finite packet satisfy the complete five-field
actual-source relation and its exact tracked/facial factorization laws. -/
theorem sourceLocalLayerSerialCellFiniteProfileReceiptAt_fullProfileRelation
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    SourceLocalLayerSerialCellFullProfileRelation corridor hunique offset
      coloring
      (sourceLocalLayerSerialCellFiniteProfileReceiptAt corridor hunique offset
        ).input.profile
      (sourceLocalLayerSerialCellFiniteProfileReceiptAt corridor hunique offset
        ).output.profile := by
  change SourceLocalLayerSerialCellFullProfileRelation corridor hunique offset
    coloring
    (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
      offset).profile
    (sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt corridor hunique
      offset).profile
  exact sourceLocalLayerSerialCellFullProfileRelation_of_ambientColoring
    corridor hunique offset

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
