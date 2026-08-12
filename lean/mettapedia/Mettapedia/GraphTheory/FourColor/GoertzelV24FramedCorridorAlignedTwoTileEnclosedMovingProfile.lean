import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileEnclosedLiteralProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24RegionalBoundaryProfileFiniteState

/-!
# Moving two-edge profile of a literal enclosed aligned slab

An aligned source slab has a physical `4 + 2` boundary, but its two transverse
ends are observations at individual corridor cuts.  This file computes those
observations afresh from an actual coloring of the *enclosed* slab region.
Consequently each endpoint uses the canonical width-two, zero-terminal,
four-fragment carrier rather than a restriction of the slab's twelve-fragment
generator profile.

The construction is local to one literal open tangle.  It does not identify
either endpoint with a cumulative prefix profile, assert that adjacent slabs
glue, or construct a serial transfer word.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileEnclosedMovingProfileEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The canonical state carrier observed at either transverse end of one
literal enclosed aligned slab. -/
abbrev AlignedTwoTileEnclosedMovingProfile :=
  BoundedCorridorCutProfile 2 0 4

/-- The first transverse block lies in the enclosed vertex-side edge region,
so a literal open Tait coloring assigns it a nonzero colour. -/
theorem sourceTwoTileAlignedEnclosedLiteralColorOnInputCrossing_ne_zero
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
    (coloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).EdgeColoring Color)
    (hcoloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).IsTaitEdgeColoring coloring)
    (step : Fin 2) :
    sourceTwoTileAlignedEnclosedLiteralColorOnVertexSide realization hcubic
      hrotation htwoSided hunique offset coloring
      ((sourceTwoTileAlignedEnclosedFirstTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge step) ≠ 0 := by
  apply sourceTwoTileAlignedEnclosedLiteralColorOnVertexSide_ne_zero
    realization hcubic hrotation htwoSided hunique offset coloring hcoloring
  apply sourceTwoTileAlignedEnclosedTerminalProfileDataAt_regionEdges_subset
    realization hcubic hrotation htwoSided hunique offset
  change (sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
    hrotation htwoSided hunique offset).portEdge
      (.inl (sourceTwoTileAlignedFirstTerminalCrossingIndex step)) ∈
    (sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset).regionEdges
  exact sourceTwoTileAlignedEnclosedTerminalProfileDataAt_portsInRegion
    realization hcubic hrotation htwoSided hunique offset _

/-- The second transverse block lies in the same enclosed vertex-side edge
region, so a literal open Tait coloring assigns it a nonzero colour. -/
theorem sourceTwoTileAlignedEnclosedLiteralColorOnOutputCrossing_ne_zero
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
    (coloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).EdgeColoring Color)
    (hcoloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).IsTaitEdgeColoring coloring)
    (step : Fin 2) :
    sourceTwoTileAlignedEnclosedLiteralColorOnVertexSide realization hcubic
      hrotation htwoSided hunique offset coloring
      ((sourceTwoTileAlignedEnclosedSecondTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge step) ≠ 0 := by
  apply sourceTwoTileAlignedEnclosedLiteralColorOnVertexSide_ne_zero
    realization hcubic hrotation htwoSided hunique offset coloring hcoloring
  apply sourceTwoTileAlignedEnclosedTerminalProfileDataAt_regionEdges_subset
    realization hcubic hrotation htwoSided hunique offset
  change (sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
    hrotation htwoSided hunique offset).portEdge
      (.inl (sourceTwoTileAlignedSecondTerminalCrossingIndex step)) ∈
    (sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset).regionEdges
  exact sourceTwoTileAlignedEnclosedTerminalProfileDataAt_portsInRegion
    realization hcubic hrotation htwoSided hunique offset _

/-- Recompute the incoming moving profile on the literal enclosed region and
its displayed first transverse cut.  The local rail observations are not
silently retained as terminals. -/
noncomputable def sourceTwoTileAlignedEnclosedLiteralMovingInputProfile
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
    (coloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).EdgeColoring Color)
    (hcoloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).IsTaitEdgeColoring coloring) :
    AlignedTwoTileEnclosedMovingProfile :=
  regionalBoundaryBoundedProfile
    embedded.cellulation.rotation.toRotationSystem
    (vertexSetRegionEdges embedded.cellulation.rotation.toRotationSystem
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).componentSideᶜ)
    (sourceTwoTileAlignedEnclosedFirstTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset).crossingEdge
    (sourceTwoTileAlignedEnclosedLiteralColorOnVertexSide realization hcubic
      hrotation htwoSided hunique offset coloring)
    (sourceTwoTileAlignedEnclosedLiteralColorOnInputCrossing_ne_zero
      realization hcubic hrotation htwoSided hunique offset coloring hcoloring)

/-- Recompute the outgoing moving profile on the literal enclosed region and
its displayed second transverse cut. -/
noncomputable def sourceTwoTileAlignedEnclosedLiteralMovingOutputProfile
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
    (coloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).EdgeColoring Color)
    (hcoloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).IsTaitEdgeColoring coloring) :
    AlignedTwoTileEnclosedMovingProfile :=
  regionalBoundaryBoundedProfile
    embedded.cellulation.rotation.toRotationSystem
    (vertexSetRegionEdges embedded.cellulation.rotation.toRotationSystem
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique offset).componentSideᶜ)
    (sourceTwoTileAlignedEnclosedSecondTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique offset).crossingEdge
    (sourceTwoTileAlignedEnclosedLiteralColorOnVertexSide realization hcubic
      hrotation htwoSided hunique offset coloring)
    (sourceTwoTileAlignedEnclosedLiteralColorOnOutputCrossing_ne_zero
      realization hcubic hrotation htwoSided hunique offset coloring hcoloring)

/-- Support of the literal enclosed slab on its canonical moving interfaces.
The witness is the actual open-tangle coloring, not an arbitrary Boolean
encoding of a profile. -/
def sourceTwoTileAlignedEnclosedMovingProfileSupport
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
    (input output : AlignedTwoTileEnclosedMovingProfile) : Prop :=
  ∃ coloring : { coloring :
      (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic hrotation
        htwoSided hunique offset).EdgeColoring Color //
      (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic hrotation
        htwoSided hunique offset).IsTaitEdgeColoring coloring },
    sourceTwoTileAlignedEnclosedLiteralMovingInputProfile realization hcubic
      hrotation htwoSided hunique offset coloring.1 coloring.2 = input ∧
      sourceTwoTileAlignedEnclosedLiteralMovingOutputProfile realization hcubic
        hrotation htwoSided hunique offset coloring.1 coloring.2 = output

/-- Every literal enclosed-slab Tait coloring supplies a supported transition
between the two directly recomputed moving profiles. -/
theorem sourceTwoTileAlignedEnclosedLiteralMovingProfiles_supported
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
    (coloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).EdgeColoring Color)
    (hcoloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).IsTaitEdgeColoring coloring) :
    sourceTwoTileAlignedEnclosedMovingProfileSupport realization hcubic
      hrotation htwoSided hunique offset
      (sourceTwoTileAlignedEnclosedLiteralMovingInputProfile realization hcubic
        hrotation htwoSided hunique offset coloring hcoloring)
      (sourceTwoTileAlignedEnclosedLiteralMovingOutputProfile realization hcubic
        hrotation htwoSided hunique offset coloring hcoloring) :=
  ⟨⟨coloring, hcoloring⟩, rfl, rfl⟩

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
