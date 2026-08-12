import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileEnclosedProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorProfileRestriction

/-!
# Endpoint restrictions of the enclosed aligned-slab profile

The literal aligned slab is an open morphism with a two-edge input and a
two-edge output.  Its enclosing-side `4 + 2` profile has already been
computed from the literal complementary region.  This file exposes each
transverse endpoint while retaining the slab-local rail ports and the same
enclosed regional fragment carrier.

These are endpoint views of one local generator.  They are not cumulative
prefix profiles, nor do they assert that rail terminals persist between
successive slabs.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorProfileRestriction
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileEnclosedProfileRestrictionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The input view of the enclosed aligned slab, retaining its two local rail
ports and all data calculated from the enclosed region. -/
noncomputable def sourceTwoTileAlignedEnclosedFirstTerminalProfileDataAt
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
  GraphCorridorCutData.restrictCrossings
    (sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset)
    sourceTwoTileAlignedFirstTerminalCrossingIndex

/-- The output view of the enclosed aligned slab, retaining the same two
local rail ports and all data calculated from the enclosed region. -/
noncomputable def sourceTwoTileAlignedEnclosedSecondTerminalProfileDataAt
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
  GraphCorridorCutData.restrictCrossings
    (sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset)
    sourceTwoTileAlignedSecondTerminalCrossingIndex

/-- The input view exposes exactly the first literal source transversal. -/
@[simp]
theorem sourceTwoTileAlignedEnclosedFirstTerminalProfileDataAt_crossingEdge
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
    (sourceTwoTileAlignedEnclosedFirstTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset).crossingEdge step =
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailStartOffset offset)).localLayerPrefixCrossing step := by
  change
    (sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset).portEdge
        (.inl (sourceTwoTileAlignedFirstTerminalCrossingIndex step)) = _
  rw [sourceTwoTileAlignedEnclosedTerminalProfileDataAt_portEdge]
  exact sourceTwoTileAlignedTerminalProfileDataAt_crossingEdge_first
    realization hcubic hrotation htwoSided hunique offset step

/-- The output view exposes exactly the following literal source
transversal. -/
@[simp]
theorem sourceTwoTileAlignedEnclosedSecondTerminalProfileDataAt_crossingEdge
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
    (sourceTwoTileAlignedEnclosedSecondTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset).crossingEdge step =
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailFinishOffset offset)).localLayerPrefixCrossing step := by
  change
    (sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset).portEdge
        (.inl (sourceTwoTileAlignedSecondTerminalCrossingIndex step)) = _
  rw [sourceTwoTileAlignedEnclosedTerminalProfileDataAt_portEdge]
  exact sourceTwoTileAlignedTerminalProfileDataAt_crossingEdge_second
    realization hcubic hrotation htwoSided hunique offset step

/-- Restriction to the input block does not replace the slab's rail ports:
they remain the same literal rail edges. -/
@[simp]
theorem sourceTwoTileAlignedEnclosedFirstTerminalProfileDataAt_terminalEdge
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
    (sourceTwoTileAlignedEnclosedFirstTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset).terminalEdge terminal =
      (sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).terminalEdge terminal :=
  rfl

/-- The analogous output restriction retains exactly the same local rail
ports. -/
@[simp]
theorem sourceTwoTileAlignedEnclosedSecondTerminalProfileDataAt_terminalEdge
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
    (sourceTwoTileAlignedEnclosedSecondTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset).terminalEdge terminal =
      (sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).terminalEdge terminal :=
  rfl

/-- Computing the five-coordinate enclosed slab profile and exposing its
input is exactly the graph-derived profile on the input restriction. -/
theorem sourceTwoTileAlignedEnclosedTerminalProfile_restrict_first
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
      color ((sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization
        hcubic hrotation htwoSided hunique offset).crossingEdge crossing) ≠ 0) :
    CorridorCutProfile.restrictCrossings
        ((sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
          hrotation htwoSided hunique offset).regionalProfile color hcolor)
        sourceTwoTileAlignedFirstTerminalCrossingIndex =
      (sourceTwoTileAlignedEnclosedFirstTerminalProfileDataAt realization
        hcubic hrotation htwoSided hunique offset).regionalProfile color
          (fun step => hcolor
            (sourceTwoTileAlignedFirstTerminalCrossingIndex step)) := by
  exact GraphCorridorCutData.restrictCrossings_regionalProfile
    (sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset)
    sourceTwoTileAlignedFirstTerminalCrossingIndex color hcolor

/-- The same complete five-field statement holds at the output interface. -/
theorem sourceTwoTileAlignedEnclosedTerminalProfile_restrict_second
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
      color ((sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization
        hcubic hrotation htwoSided hunique offset).crossingEdge crossing) ≠ 0) :
    CorridorCutProfile.restrictCrossings
        ((sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
          hrotation htwoSided hunique offset).regionalProfile color hcolor)
        sourceTwoTileAlignedSecondTerminalCrossingIndex =
      (sourceTwoTileAlignedEnclosedSecondTerminalProfileDataAt realization
        hcubic hrotation htwoSided hunique offset).regionalProfile color
          (fun step => hcolor
            (sourceTwoTileAlignedSecondTerminalCrossingIndex step)) := by
  exact GraphCorridorCutData.restrictCrossings_regionalProfile
    (sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset)
    sourceTwoTileAlignedSecondTerminalCrossingIndex color hcolor

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
