import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalDepthProfile

/-!
# A source-indexed finite profile word along a clean corridor

The L1 realization supplies a literal clean dual geodesic.  Every consecutive
internal pair of that geodesic now determines its own source-local layer
interface, deletion component, and L7 profile.  This file packages those
constructions as one indexed word, so the finite repetition theorem applies
to actual source positions rather than to an externally supplied profile map.

An equality in this word is only the finite-state event.  The subsequent
formation theorem must use the same indexed source layers to construct the
complementary open corridor pieces required by the splice; it is not replaced
by this pigeonhole result.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24CleanHexCorridor
open GoertzelV24ClosedWebProfileFiniteness
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance corridorSourceProfileWordGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The left internal face of an indexed pair of consecutive corridor slabs. -/
def sourceSlabLeftInterior {blockLength : Nat}
    (offset : Fin (blockLength - 3)) : CorridorInterior blockLength :=
  corridorInteriorOfOffset ⟨offset.val, by
    have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
    omega⟩

/-- The indexed source slab has a real successor face, so it is eligible for
the source interface construction rather than merely an abstract corridor
position. -/
theorem sourceSlabLeftInterior_hasNext {blockLength : Nat}
    (offset : Fin (blockLength - 3)) :
    (sourceSlabLeftInterior offset).center.val + 2 < blockLength := by
  have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
  change offset.val + 1 + 2 < blockLength
  omega

/-- Choose the source-certified two-port interface at one actual consecutive
pair of corridor cells.  The choice resolves only the finite local orientation
whose existence was proved from the facial rotations. -/
noncomputable def sourceSlabInterfaceAt
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
    (offset : Fin (blockLength - 3)) :
    SourceConsecutiveSlabInterface realization htwoSided hunique
      (sourceSlabLeftInterior offset)
      (sourceSlabLeftInterior_hasNext offset) :=
  realization.sourceConsecutiveSlabInterface hcubic hrotation htwoSided hunique
    (sourceSlabLeftInterior offset) (sourceSlabLeftInterior_hasNext offset)

/-- The finite profile at a literal source corridor position.  It is computed
from that position's deletion component, including actual colors, connectivity
and capped face fragments. -/
noncomputable def sourceSlabDepthProfile
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
    (offset : Fin (blockLength - 3))
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ClosedWebDepthProfile 4 :=
  (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique offset).localLayerDepthProfile
    coloring hcoloring

/-- One more actual source slab than the width-four L7 state count forces two
different source positions to have exactly the same computed profile. -/
theorem exists_equal_sourceSlabDepthProfiles
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
    (hlarge : closedWebCutProfileCount 4 + 1 ≤ blockLength - 3)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ∃ first second : Fin (closedWebCutProfileCount 4 + 1), first ≠ second ∧
      sourceSlabDepthProfile realization hcubic hrotation htwoSided hunique
        (Fin.castLE hlarge first) coloring hcoloring =
      sourceSlabDepthProfile realization hcubic hrotation htwoSided hunique
        (Fin.castLE hlarge second) coloring hcoloring := by
  let profiles : Fin (closedWebCutProfileCount 4 + 1) →
      ClosedWebDepthProfile 4 := fun offset =>
    sourceSlabDepthProfile realization hcubic hrotation htwoSided hunique
      (Fin.castLE hlarge offset) coloring hcoloring
  rcases exists_depthProfile_repeat 4 profiles with ⟨first, second, hne, heq⟩
  exact ⟨first, second, hne, heq⟩

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
