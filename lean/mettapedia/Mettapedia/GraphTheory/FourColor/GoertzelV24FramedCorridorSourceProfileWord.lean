import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalDepthProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceInterface

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
open GoertzelV24HexCorridorInterfaceMatching
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

/-- The profile-facing projection of the corner-aligned source interface.
It has the ordinary layer type consumed by existing finite-profile code, while
the richer object above retains the real continuation data for the splice. -/
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
  (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
    offset).toInterface

/-- At every indexed source position, the first left port is the literal side
slot immediately before that slab's outgoing rung. -/
theorem sourceSlabInterfaceAt_leftBefore_precedesOutgoing
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
    (realization.slabPlacementAt htwoSided hunique
      (sourceSlabLeftInterior offset)).outgoingPosition.val ≡
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).leftBeforePos.1.val + 1 [MOD 6] := by
  simpa [sourceSlabInterfaceAt] using
    (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).leftBefore_precedesOutgoing

/-- The second left port is the literal side slot immediately after the
outgoing rung. -/
theorem sourceSlabInterfaceAt_leftAfter_followsOutgoing
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
    (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).leftAfterPos.1.val ≡
      (realization.slabPlacementAt htwoSided hunique
        (sourceSlabLeftInterior offset)).outgoingPosition.val + 1 [MOD 6] := by
  simpa [sourceSlabInterfaceAt] using
    (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).leftAfter_followsOutgoing

/-- The first right port continues at the side slot immediately after the
next slab's incoming rung. -/
theorem sourceSlabInterfaceAt_rightBefore_followsIncoming
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
    (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).rightBeforePos.1.val ≡
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior (sourceSlabLeftInterior offset)
          (sourceSlabLeftInterior_hasNext offset))).incomingPosition.val + 1 [MOD 6] := by
  simpa [sourceSlabInterfaceAt] using
    (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).rightBefore_followsIncoming

/-- The second right port continues at the side slot immediately before the
next slab's incoming rung. -/
theorem sourceSlabInterfaceAt_rightAfter_precedesIncoming
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
    (realization.slabPlacementAt htwoSided hunique
      (nextCorridorInterior (sourceSlabLeftInterior offset)
        (sourceSlabLeftInterior_hasNext offset))).incomingPosition.val ≡
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).rightAfterPos.1.val + 1 [MOD 6] := by
  simpa [sourceSlabInterfaceAt] using
    (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).rightAfter_precedesIncoming

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
