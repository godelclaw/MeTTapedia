import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileRailTerminalExact

/-!
# Physical boundary ports of the aligned two-tile slab

The source-aligned slab has a certified six-edge primal boundary.  Its
terminal-aware profile presents that boundary as four transverse coordinates
and two rail coordinates.  This file identifies each displayed profile port
with its literal boundary crossing.

This is a local port-realization result.  It does not identify the slab with
an ambient cumulative prefix, make rail edges persistent serial terminals, or
claim a raw-prefix frontier cancellation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTilePortBoundaryEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The first transverse block of the terminal-aware profile is literally
the first pair of crossings in the six-step source boundary. -/
theorem sourceTwoTileAlignedTerminalProfileDataAt_crossingEdge_first_ordered
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
          (sourceTwoTileAlignedFirstTerminalCrossingIndex step) =
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).orderedCrossing
          (sourceTwoTileAlignedFirstCrossingIndex step) := by
  rw [sourceTwoTileAlignedFirstTerminalCrossingIndex,
    sourceTwoTileAlignedTerminalProfileDataAt_crossingEdge_first]
  symm
  exact sourceTwoTileAlignedOrderedCrossing_first_serial realization hcubic
    hrotation htwoSided hunique offset step

/-- The second transverse block of the terminal-aware profile is literally
the following pair of crossings in the six-step source boundary. -/
theorem sourceTwoTileAlignedTerminalProfileDataAt_crossingEdge_second_ordered
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
          (sourceTwoTileAlignedSecondTerminalCrossingIndex step) =
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).orderedCrossing
          (sourceTwoTileAlignedSecondCrossingIndexAt realization hcubic
            hrotation htwoSided hunique offset step) := by
  rw [sourceTwoTileAlignedSecondTerminalCrossingIndex,
    sourceTwoTileAlignedTerminalProfileDataAt_crossingEdge_second]
  symm
  exact sourceTwoTileAlignedOrderedCrossing_second_serial realization hcubic
    hrotation htwoSided hunique offset step

/-- Each ordered crossing of the literal six-step slab boundary belongs to
the certified six-edge crossing support. -/
theorem sourceTwoTileAlignedLayerBoundaryAt_orderedCrossing_mem_boundary
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
    (offset : Fin (blockLength - 4)) (step : Fin 6) :
    (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
      htwoSided hunique offset).orderedCrossing step ∈
        sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic
          hrotation htwoSided hunique offset := by
  rw [← sourceTwoTileAlignedLayerBoundaryAt_cutEdges,
    ← (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
      htwoSided hunique offset).vertexSetCrossingEdges_componentSide_eq_cutEdges]
  exact (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
    htwoSided hunique offset).orderedCrossing_mem step

/-- Every displayed `4 + 2` profile port is a literal crossing edge of the
certified aligned slab boundary. -/
theorem sourceTwoTileAlignedTerminalProfileDataAt_portEdge_mem_boundary
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
    (offset : Fin (blockLength - 4)) (port : CorridorPort 4 2) :
    (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
      htwoSided hunique offset).portEdge port ∈
        sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic
          hrotation htwoSided hunique offset := by
  rcases port with crossing | terminal
  · rcases hcrossing : (finSumFinEquiv.symm crossing : Fin 2 ⊕ Fin 2) with
      first | second
    · have hcrossingEq : crossing =
          sourceTwoTileAlignedFirstTerminalCrossingIndex first := by
        let e : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv
        change e.symm crossing = Sum.inl first at hcrossing
        change crossing = e (Sum.inl first)
        apply e.symm.injective
        simp [hcrossing]
      change (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge crossing ∈ _
      rw [hcrossingEq,
        sourceTwoTileAlignedTerminalProfileDataAt_crossingEdge_first_ordered]
      exact sourceTwoTileAlignedLayerBoundaryAt_orderedCrossing_mem_boundary
        realization hcubic hrotation htwoSided hunique offset
          (sourceTwoTileAlignedFirstCrossingIndex first)
    · have hcrossingEq : crossing =
          sourceTwoTileAlignedSecondTerminalCrossingIndex second := by
        let e : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv
        change e.symm crossing = Sum.inr second at hcrossing
        change crossing = e (Sum.inr second)
        apply e.symm.injective
        simp [hcrossing]
      change (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge crossing ∈ _
      rw [hcrossingEq,
        sourceTwoTileAlignedTerminalProfileDataAt_crossingEdge_second_ordered]
      exact sourceTwoTileAlignedLayerBoundaryAt_orderedCrossing_mem_boundary
        realization hcubic hrotation htwoSided hunique offset
          (sourceTwoTileAlignedSecondCrossingIndexAt realization hcubic
            hrotation htwoSided hunique offset second)
  · change (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset).terminalEdge terminal ∈ _
    rw [sourceTwoTileAlignedTerminalProfileDataAt_terminalEdge]
    exact sourceTwoTileAlignedLayerBoundaryAt_orderedCrossing_mem_boundary
      realization hcubic hrotation htwoSided hunique offset
        (sourceTwoTileAlignedRailCrossingIndexAt realization hcubic hrotation
          htwoSided hunique offset terminal)

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
