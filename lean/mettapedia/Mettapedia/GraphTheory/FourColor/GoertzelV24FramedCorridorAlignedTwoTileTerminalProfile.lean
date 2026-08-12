import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorProfilePortPartition
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileProfileRestriction

/-!
# Terminal presentation of the aligned two-tile profile

The source-aligned two-tile boundary has six crossed edges: two on the first
transversal, two on the following transversal, and two on the exterior rails.
For serial composition the transverse blocks are the moving input/output
ports, while the lateral rail crossings are fixed terminals of this slab.

This file gives that `4 + 2` presentation directly from the already proved
ordered six-edge profile.  All five profile fields are transported by one
port partition; no new region, coloring, or connectivity witness is chosen.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24ClosedWebProfileFiniteness
open GoertzelV24CorridorProfilePortPartition
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileTerminalProfileEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Source order on the four transverse crossings: first interface, then
second interface. -/
noncomputable def sourceTwoTileAlignedTransverseProfileIndexAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) (crossing : Fin 4) :
    Fin (Fintype.card (VertexSetCrossingEdge
      embedded.cellulation.rotation.toRotationSystem
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).componentSide)) := by
  rcases (finSumFinEquiv.symm crossing : Fin 2 ⊕ Fin 2) with first | second
  · exact sourceTwoTileAlignedFirstProfileIndexAt realization hcubic
      hrotation htwoSided hunique offset first
  · exact sourceTwoTileAlignedSecondProfileIndexAt realization hcubic
      hrotation htwoSided hunique offset second

/-- The two rail positions in the literal six-step boundary order.  The
three source cases have rail lengths `0+2`, `1+1`, or `2+0`; the sum
equivalence gives one uniform `Fin 2` coordinate. -/
noncomputable def sourceTwoTileAlignedRailCrossingIndexAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) (terminal : Fin 2) : Fin 6 := by
  let pair := sourceTwoTileRailPairAt realization hcubic hrotation htwoSided
    hunique offset
  have hrails : pair.secondRail.length + pair.firstRail.length = 2 := by
    have hsum := pair.firstRail_length_add_secondRail_length_eq_two
    omega
  let railStep : Fin (pair.secondRail.length + pair.firstRail.length) :=
    Fin.cast hrails.symm terminal
  rcases (finSumFinEquiv.symm railStep :
      Fin pair.secondRail.length ⊕ Fin pair.firstRail.length) with
    secondStep | firstStep
  · exact ⟨2 + secondStep.val, by
      have hstep := secondStep.isLt
      have hbound := pair.secondRail_length_le_two
      omega⟩
  · exact ⟨2 + pair.secondRail.length + 2 + firstStep.val, by
      have hstep := firstStep.isLt
      have hsum := pair.firstRail_length_add_secondRail_length_eq_two
      omega⟩

/-- Convert the two ordered rail positions to the dependent crossing carrier
used by the graph-derived six-edge profile. -/
noncomputable def sourceTwoTileAlignedRailProfileIndexAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) (terminal : Fin 2) :
    Fin (Fintype.card (VertexSetCrossingEdge
      embedded.cellulation.rotation.toRotationSystem
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).componentSide)) :=
  Fin.cast
    (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
      htwoSided hunique offset).crossingCard_eq_six.symm
    (sourceTwoTileAlignedRailCrossingIndexAt realization hcubic hrotation
      htwoSided hunique offset terminal)

/-- The aligned slab as one four-crossing, two-terminal graph-derived cut.
Its edge region and fragment carrier are exactly those of the ordered
six-edge boundary profile. -/
noncomputable def sourceTwoTileAlignedTerminalProfileDataAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) :=
  GoertzelV24CorridorProfilePortPartition.GraphCorridorCutData.partitionCrossings
    (sourceTwoTileAlignedOrderedProfileDataAt realization hcubic hrotation
      htwoSided hunique offset)
    (sourceTwoTileAlignedTransverseProfileIndexAt realization hcubic hrotation
      htwoSided hunique offset)
    (sourceTwoTileAlignedRailProfileIndexAt realization hcubic hrotation
      htwoSided hunique offset)

/-- The first two combined crossing coordinates are the first source
transversal. -/
theorem sourceTwoTileAlignedTerminalProfileDataAt_crossingEdge_first
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) (step : Fin 2) :
    (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
        htwoSided hunique offset).crossingEdge
          (finSumFinEquiv (Sum.inl step : Fin 2 ⊕ Fin 2)) =
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailStartOffset offset)).localLayerPrefixCrossing step := by
  simpa [sourceTwoTileAlignedTerminalProfileDataAt,
    GoertzelV24CorridorProfilePortPartition.GraphCorridorCutData.partitionCrossings,
    sourceTwoTileAlignedTransverseProfileIndexAt] using
    sourceTwoTileAlignedOrderedProfileDataAt_crossingEdge_first_serial
      realization hcubic hrotation htwoSided hunique offset step

/-- The last two combined crossing coordinates are the following source
transversal. -/
theorem sourceTwoTileAlignedTerminalProfileDataAt_crossingEdge_second
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) (step : Fin 2) :
    (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
        htwoSided hunique offset).crossingEdge
          (finSumFinEquiv (Sum.inr step : Fin 2 ⊕ Fin 2)) =
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailFinishOffset offset)).localLayerPrefixCrossing step := by
  simpa [sourceTwoTileAlignedTerminalProfileDataAt,
    GoertzelV24CorridorProfilePortPartition.GraphCorridorCutData.partitionCrossings,
    sourceTwoTileAlignedTransverseProfileIndexAt] using
    sourceTwoTileAlignedOrderedProfileDataAt_crossingEdge_second_serial
      realization hcubic hrotation htwoSided hunique offset step

/-- The terminal coordinates are literally the two rail crossings in the
ordered six-step boundary. -/
@[simp]
theorem sourceTwoTileAlignedTerminalProfileDataAt_terminalEdge
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) (terminal : Fin 2) :
    (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
        htwoSided hunique offset).terminalEdge terminal =
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).orderedCrossing
          (sourceTwoTileAlignedRailCrossingIndexAt realization hcubic
            hrotation htwoSided hunique offset terminal) := by
  unfold sourceTwoTileAlignedTerminalProfileDataAt
  unfold GoertzelV24CorridorProfilePortPartition.GraphCorridorCutData.partitionCrossings
  change
    (sourceTwoTileAlignedOrderedProfileDataAt realization hcubic hrotation
        htwoSided hunique offset).crossingEdge
          (sourceTwoTileAlignedRailProfileIndexAt realization hcubic hrotation
            htwoSided hunique offset terminal) = _
  unfold sourceTwoTileAlignedOrderedProfileDataAt
  rw [(sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
    htwoSided hunique offset).orderedProfileData_crossingEdge]
  simp [sourceTwoTileAlignedRailProfileIndexAt]

/-- Embed the incoming two-crossing interface in the combined four-crossing
coordinate. -/
def sourceTwoTileAlignedFirstTerminalCrossingIndex (step : Fin 2) : Fin 4 :=
  finSumFinEquiv (Sum.inl step : Fin 2 ⊕ Fin 2)

/-- Embed the outgoing two-crossing interface in the combined four-crossing
coordinate. -/
def sourceTwoTileAlignedSecondTerminalCrossingIndex (step : Fin 2) : Fin 4 :=
  finSumFinEquiv (Sum.inr step : Fin 2 ⊕ Fin 2)

/-- The incoming presentation retains both rail terminals and all regional
face fragments while exposing only the first transverse block. -/
noncomputable def sourceTwoTileAlignedFirstTerminalProfileDataAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) :=
  GoertzelV24CorridorProfileRestriction.GraphCorridorCutData.restrictCrossings
    (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
      htwoSided hunique offset)
    sourceTwoTileAlignedFirstTerminalCrossingIndex

/-- The outgoing presentation retains the same two rail terminals and
regional fragments while exposing only the following transverse block. -/
noncomputable def sourceTwoTileAlignedSecondTerminalProfileDataAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) :=
  GoertzelV24CorridorProfileRestriction.GraphCorridorCutData.restrictCrossings
    (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
      htwoSided hunique offset)
    sourceTwoTileAlignedSecondTerminalCrossingIndex

/-- The incoming terminal presentation exposes the literal first source
transversal. -/
@[simp]
theorem sourceTwoTileAlignedFirstTerminalProfileDataAt_crossingEdge
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) (step : Fin 2) :
    (sourceTwoTileAlignedFirstTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge step =
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailStartOffset offset)).localLayerPrefixCrossing step := by
  simpa [sourceTwoTileAlignedFirstTerminalProfileDataAt,
    GoertzelV24CorridorProfileRestriction.GraphCorridorCutData.restrictCrossings,
    sourceTwoTileAlignedFirstTerminalCrossingIndex] using
    sourceTwoTileAlignedTerminalProfileDataAt_crossingEdge_first realization
      hcubic hrotation htwoSided hunique offset step

/-- The outgoing terminal presentation exposes the literal following source
transversal. -/
@[simp]
theorem sourceTwoTileAlignedSecondTerminalProfileDataAt_crossingEdge
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) (step : Fin 2) :
    (sourceTwoTileAlignedSecondTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge step =
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailFinishOffset offset)).localLayerPrefixCrossing step := by
  simpa [sourceTwoTileAlignedSecondTerminalProfileDataAt,
    GoertzelV24CorridorProfileRestriction.GraphCorridorCutData.restrictCrossings,
    sourceTwoTileAlignedSecondTerminalCrossingIndex] using
    sourceTwoTileAlignedTerminalProfileDataAt_crossingEdge_second realization
      hcubic hrotation htwoSided hunique offset step

/-- Restricting to the incoming crossings leaves each rail terminal
unchanged. -/
@[simp]
theorem sourceTwoTileAlignedFirstTerminalProfileDataAt_terminalEdge
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) (terminal : Fin 2) :
    (sourceTwoTileAlignedFirstTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).terminalEdge terminal =
      (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
        htwoSided hunique offset).terminalEdge terminal := by
  rfl

/-- Restricting to the outgoing crossings leaves each rail terminal
unchanged. -/
@[simp]
theorem sourceTwoTileAlignedSecondTerminalProfileDataAt_terminalEdge
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) (terminal : Fin 2) :
    (sourceTwoTileAlignedSecondTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).terminalEdge terminal =
      (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
        htwoSided hunique offset).terminalEdge terminal := by
  rfl

/-- Computing the complete terminal-aware profile and then exposing the
incoming interface is the same as first restricting the raw graph cut.  The
equality covers colors, connectivity, face continuation, fragment incidence,
and capped face length together. -/
theorem sourceTwoTileAlignedTerminalProfile_restrict_first
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4))
    (color : G.edgeSet → Color)
    (hcolor : ∀ crossing,
      color ((sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge crossing) ≠ 0) :
    GoertzelV24CorridorProfileRestriction.CorridorCutProfile.restrictCrossings
        ((sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
          hrotation htwoSided hunique offset).regionalProfile color hcolor)
        sourceTwoTileAlignedFirstTerminalCrossingIndex =
      (sourceTwoTileAlignedFirstTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).regionalProfile color
          (fun step => hcolor
            (sourceTwoTileAlignedFirstTerminalCrossingIndex step)) := by
  exact GoertzelV24CorridorProfileRestriction.GraphCorridorCutData.restrictCrossings_regionalProfile
    (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
      htwoSided hunique offset)
    sourceTwoTileAlignedFirstTerminalCrossingIndex color hcolor

/-- The analogous complete five-field equality for the outgoing source
interface. -/
theorem sourceTwoTileAlignedTerminalProfile_restrict_second
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4))
    (color : G.edgeSet → Color)
    (hcolor : ∀ crossing,
      color ((sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge crossing) ≠ 0) :
    GoertzelV24CorridorProfileRestriction.CorridorCutProfile.restrictCrossings
        ((sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
          hrotation htwoSided hunique offset).regionalProfile color hcolor)
        sourceTwoTileAlignedSecondTerminalCrossingIndex =
      (sourceTwoTileAlignedSecondTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).regionalProfile color
          (fun step => hcolor
            (sourceTwoTileAlignedSecondTerminalCrossingIndex step)) := by
  exact GoertzelV24CorridorProfileRestriction.GraphCorridorCutData.restrictCrossings_regionalProfile
    (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
      htwoSided hunique offset)
    sourceTwoTileAlignedSecondTerminalCrossingIndex color hcolor

/-- Computing the `4+2` profile is exactly the common port partition of the
already proved ordered six-edge profile. -/
theorem sourceTwoTileAlignedTerminalProfile_partition
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4))
    (color : G.edgeSet → Color)
    (hcolor : ∀ crossing,
      color ((sourceTwoTileAlignedOrderedProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge crossing) ≠ 0) :
    GoertzelV24CorridorProfilePortPartition.CorridorCutProfile.partitionCrossings
        ((sourceTwoTileAlignedOrderedProfileDataAt realization hcubic hrotation
          htwoSided hunique offset).regionalProfile color hcolor)
        (sourceTwoTileAlignedTransverseProfileIndexAt realization hcubic
          hrotation htwoSided hunique offset)
        (sourceTwoTileAlignedRailProfileIndexAt realization hcubic hrotation
          htwoSided hunique offset) =
      (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
        htwoSided hunique offset).regionalProfile color
          (fun crossing => hcolor
            (sourceTwoTileAlignedTransverseProfileIndexAt realization hcubic
              hrotation htwoSided hunique offset crossing)) := by
  exact GoertzelV24CorridorProfilePortPartition.GraphCorridorCutData.partitionCrossings_regionalProfile
    (sourceTwoTileAlignedOrderedProfileDataAt realization hcubic hrotation
      htwoSided hunique offset)
    (sourceTwoTileAlignedTransverseProfileIndexAt realization hcubic hrotation
      htwoSided hunique offset)
    (sourceTwoTileAlignedRailProfileIndexAt realization hcubic hrotation
      htwoSided hunique offset) color hcolor

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
