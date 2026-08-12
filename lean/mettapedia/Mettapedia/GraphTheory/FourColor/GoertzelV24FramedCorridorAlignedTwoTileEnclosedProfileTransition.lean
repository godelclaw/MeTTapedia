import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileEnclosedLiteralProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileProfileTransition

/-!
# Literal full-profile transition of an enclosed aligned slab

The aligned source slab is an actual open morphism with two transverse input
ports, two transverse output ports, and two local rail ports.  Its profile
must be read from the enclosed open tangle, rather than from the retained
component of the same six-edge cut.  This file packages that literal profile
as the existing relational common-profile transition.

It does not identify the endpoint views with cumulative prefix profiles, make
the rail ports persistent, or prove a serial realization of adjacent slabs.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorProfile
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

local instance framedCorridorAlignedTwoTileEnclosedProfileTransitionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The input view of the full profile read from a literal enclosed aligned
slab coloring.  The two local rail ports remain visible in this local view. -/
noncomputable def sourceTwoTileAlignedEnclosedLiteralInputProfile
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
      hrotation htwoSided hunique offset).IsTaitEdgeColoring coloring) :=
  CorridorCutProfile.restrictCrossings
    (sourceTwoTileAlignedEnclosedLiteralOpenProfile realization hcubic
      hrotation htwoSided hunique offset coloring hcoloring)
    sourceTwoTileAlignedFirstTerminalCrossingIndex

/-- The output view of the same literal enclosed aligned slab coloring. -/
noncomputable def sourceTwoTileAlignedEnclosedLiteralOutputProfile
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
      hrotation htwoSided hunique offset).IsTaitEdgeColoring coloring) :=
  CorridorCutProfile.restrictCrossings
    (sourceTwoTileAlignedEnclosedLiteralOpenProfile realization hcubic
      hrotation htwoSided hunique offset coloring hcoloring)
    sourceTwoTileAlignedSecondTerminalCrossingIndex

/-- Every literal enclosed-slab Tait coloring realizes one finite,
rail-mediated transition between its actual source input and output profiles.
The common witness is the full `4 + 2` profile of that very same coloring. -/
theorem sourceTwoTileAlignedEnclosedLiteralProfiles_commonProfileRelation
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
    AlignedTwoTileCommonProfileRelation
      (sourceTwoTileAlignedEnclosedLiteralInputProfile realization hcubic
        hrotation htwoSided hunique offset coloring hcoloring)
      (sourceTwoTileAlignedEnclosedLiteralOutputProfile realization hcubic
        hrotation htwoSided hunique offset coloring hcoloring) := by
  exact ⟨sourceTwoTileAlignedEnclosedLiteralOpenProfile realization hcubic
    hrotation htwoSided hunique offset coloring hcoloring, rfl, rfl⟩

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
