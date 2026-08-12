import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTilePortBoundary

/-!
# Physical port coordinates of an aligned two-tile slab

The source-aligned slab is a literal six-edge boundary: two incoming
transverse crossings, two outgoing transverse crossings, and two rail
crossings.  The preceding module proved that each displayed `4 + 2` port lies
on that boundary.  This module records the common source-boundary coordinate
of each port.  It is a coordinate identification only; boundary completeness
and serial realization remain separate obligations.

This is still local slab geometry.  In particular, it does not identify
successive moving cuts, assert raw-prefix rail absorption, or make a rail
terminal persistent between distinct slabs.
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

local instance framedCorridorAlignedTwoTilePortCoordinatesEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The literal six-step boundary coordinate of a displayed `4 + 2` slab
port.  The transverse port is first split into its incoming or outgoing
two-edge block; the rail port retains the rail-length-aware source coordinate.
-/
noncomputable def sourceTwoTileAlignedTerminalPortBoundaryIndexAt
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
    (offset : Fin (blockLength - 4)) (port : CorridorPort 4 2) : Fin 6 := by
  rcases port with crossing | terminal
  · rcases (finSumFinEquiv.symm crossing : Fin 2 ⊕ Fin 2) with first | second
    · exact sourceTwoTileAlignedFirstCrossingIndex first
    · exact sourceTwoTileAlignedSecondCrossingIndexAt realization hcubic
        hrotation htwoSided hunique offset second
  · exact sourceTwoTileAlignedRailCrossingIndexAt realization hcubic hrotation
      htwoSided hunique offset terminal

/-- Reading a displayed slab port is exactly reading the corresponding edge
of the literal six-step source boundary. -/
theorem sourceTwoTileAlignedTerminalProfileDataAt_portEdge_eq_orderedCrossing
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
      htwoSided hunique offset).portEdge port =
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).orderedCrossing
        (sourceTwoTileAlignedTerminalPortBoundaryIndexAt realization hcubic
          hrotation htwoSided hunique offset port) := by
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
        hrotation htwoSided hunique offset).crossingEdge crossing = _
      rw [hcrossingEq,
        sourceTwoTileAlignedTerminalProfileDataAt_crossingEdge_first_ordered]
      simp [sourceTwoTileAlignedTerminalPortBoundaryIndexAt,
        sourceTwoTileAlignedFirstTerminalCrossingIndex]
    · have hcrossingEq : crossing =
          sourceTwoTileAlignedSecondTerminalCrossingIndex second := by
        let e : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv
        change e.symm crossing = Sum.inr second at hcrossing
        change crossing = e (Sum.inr second)
        apply e.symm.injective
        simp [hcrossing]
      change (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge crossing = _
      rw [hcrossingEq,
        sourceTwoTileAlignedTerminalProfileDataAt_crossingEdge_second_ordered]
      simp [sourceTwoTileAlignedTerminalPortBoundaryIndexAt,
        sourceTwoTileAlignedSecondTerminalCrossingIndex]
  · change (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset).terminalEdge terminal = _
    rw [sourceTwoTileAlignedTerminalProfileDataAt_terminalEdge]
    rfl

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
