import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorRailPair
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceInterface

/-!
# Source-profile indexing for concrete corridor rails

The rail geometry itself is independent of finite profile coding.  This small
adapter connects actual consecutive positions of the source profile word to
the concrete rail-pair construction, keeping that heavier profile dependency
out of geometry-only corridor modules.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CleanHexCorridor
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance corridorSourceRailPairGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The left endpoint of an indexed rail step is an actual source-profile
position; one slot remains available for its successor interface. -/
def sourceSlabRailStartOffset {blockLength : Nat}
    (offset : Fin (blockLength - 4)) : Fin (blockLength - 3) :=
  ⟨offset.val, by
    have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
    apply (Nat.lt_sub_iff_add_lt).2
    omega⟩

/-- The second source-profile position adjacent to a rail-step start. -/
def sourceSlabRailFinishOffset {blockLength : Nat}
    (offset : Fin (blockLength - 4)) : Fin (blockLength - 3) :=
  ⟨offset.val + 1, by
    have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
    apply (Nat.lt_sub_iff_add_lt).2
    omega⟩

/-- The adjacent source-profile index names exactly the next corridor
interior used by the rail construction. -/
theorem sourceSlabLeftInterior_railFinish_eq_next {blockLength : Nat}
    (offset : Fin (blockLength - 4)) :
    sourceSlabLeftInterior (sourceSlabRailFinishOffset offset) =
      nextCorridorInterior
        (sourceSlabLeftInterior (sourceSlabRailStartOffset offset))
        (sourceSlabLeftInterior_hasNext (sourceSlabRailStartOffset offset)) := by
  have hcenter :
      (sourceSlabLeftInterior (sourceSlabRailFinishOffset offset)).center =
        (nextCorridorInterior
          (sourceSlabLeftInterior (sourceSlabRailStartOffset offset))
          (sourceSlabLeftInterior_hasNext (sourceSlabRailStartOffset offset))).center := by
    apply Fin.ext
    rfl
  cases hleft : sourceSlabLeftInterior (sourceSlabRailFinishOffset offset) with
  | mk leftCenter leftPositive leftSuccessor =>
    cases hright : nextCorridorInterior
        (sourceSlabLeftInterior (sourceSlabRailStartOffset offset))
        (sourceSlabLeftInterior_hasNext (sourceSlabRailStartOffset offset)) with
    | mk rightCenter rightPositive rightSuccessor =>
      simp only [hleft, hright, CorridorInterior.mk.injEq] at hcenter ⊢
      exact hcenter

/-- A rail-step start has a second successor corridor face, so the next
corner-aligned source interface is a real object rather than a profile-only
index. -/
theorem sourceSlabRailStart_hasNextNext {blockLength : Nat}
    (offset : Fin (blockLength - 4)) :
    (nextCorridorInterior
      (sourceSlabLeftInterior (sourceSlabRailStartOffset offset))
      (sourceSlabLeftInterior_hasNext (sourceSlabRailStartOffset offset))).center.val + 2 <
      blockLength := by
  have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
  change offset.val + 2 + 2 < blockLength
  omega

/-- The next concrete corner-aligned interface along the source-profile
word.  Its underlying corridor interior is definitionally the successor of
the first one, which is the endpoint required by a rail pair. -/
noncomputable def sourceSlabRailNextCornerInterfaceAt
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
    (offset : Fin (blockLength - 4)) :
    SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior
        (sourceSlabLeftInterior (sourceSlabRailStartOffset offset))
        (sourceSlabLeftInterior_hasNext (sourceSlabRailStartOffset offset)))
      (sourceSlabRailStart_hasNextNext offset) :=
  realization.sourceCornerAlignedSlabInterface hcubic hrotation htwoSided hunique
    (nextCorridorInterior
      (sourceSlabLeftInterior (sourceSlabRailStartOffset offset))
      (sourceSlabLeftInterior_hasNext (sourceSlabRailStartOffset offset)))
    (sourceSlabRailStart_hasNextNext offset)

/-- At every source-profile position with one following position, the two
literal interfaces carry an actual bounded rail pair.  This is the direct
link from the finite profile word to the geometry that a later splice
formation appends. -/
theorem sourceSlabCornerInterfaceAt_hasRailPair
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
    (offset : Fin (blockLength - 4)) :
    Nonempty (SourceCornerAlignedRailPair
      (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailStartOffset offset))
      (sourceSlabRailNextCornerInterfaceAt realization hcubic hrotation htwoSided hunique
        offset)) := by
  exact exists_sourceCornerAlignedRailPair hcubic hrotation
    (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
      (sourceSlabRailStartOffset offset))
    (sourceSlabRailNextCornerInterfaceAt realization hcubic hrotation htwoSided hunique
      offset)

/-- The preceding rail pair is indexed by two genuinely consecutive entries
of the source profile word, not merely by an isomorphic successor interior. -/
theorem sourceSlabCornerInterfaces_adjacent_hasRailPair
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
    (offset : Fin (blockLength - 4)) :
    Nonempty (SourceCornerAlignedRailPair
      (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailStartOffset offset))
      (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceSlabRailFinishOffset offset))) := by
  have hinterior := sourceSlabLeftInterior_railFinish_eq_next offset
  cases hinterior
  exact exists_sourceCornerAlignedRailPair hcubic hrotation
    (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
      (sourceSlabRailStartOffset offset))
    (sourceSlabCornerInterfaceAt realization hcubic hrotation htwoSided hunique
      (sourceSlabRailFinishOffset offset))

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
