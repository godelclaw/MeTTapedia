import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorCanonicalInterface

/-!
# Concrete source positions along a clean corridor

This light module turns an index in the realized source corridor into its
actual corner-aligned interface.  It deliberately contains no finite profile
or repetition machinery, so later geometry can use source positions without
importing the profile-computation branch.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CleanHexCorridor
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance corridorSourceInterfaceGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
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

/-- The corner-aligned source interface at one actual consecutive pair of
corridor cells.  Keeping this richer object available lets the later rail
induction use the checked continuation coordinates rather than reconstruct
them from a bare profile. -/
noncomputable def sourceSlabCornerInterfaceAt
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
    SourceCornerAlignedSlabInterface realization htwoSided hunique
      (sourceSlabLeftInterior offset)
      (sourceSlabLeftInterior_hasNext offset) :=
  realization.sourceCornerAlignedSlabInterface hcubic hrotation htwoSided hunique
    (sourceSlabLeftInterior offset) (sourceSlabLeftInterior_hasNext offset)

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
