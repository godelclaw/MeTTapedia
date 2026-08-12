import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileSuccessorInterface

/-!
# Shared dual interface of consecutive physical aligned slabs

The source coordinates identify the output transverse *edges* of one aligned
two-tile slab with the input transverse edges of its successor.  This adapter
also identifies the complete dual interface that presents those edges.  It is
still only a coordinate fact: it does not orient the two boundary darts,
establish enclosed-region disjointness, or construct an ambient serial
open-tangle composite.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/- Keep edge equality definitionally aligned with the source-aligned boundary
   modules, whose crossing carriers use the ordinary subtype instance. -/
local instance framedCorridorAlignedTwoTileSuccessorDualInterfaceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The output source interface of a physical aligned slab is exactly the
input source interface of its successor.  This strengthens the existing
coordinate equality of their two transverse primal edges to the complete
source dual interface, while deliberately making no claim about the primal
regions on either side. -/
theorem sourceTwoTileSecondInterfaceAt_toInterface_eq_successorFirst
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
    (offset : Fin (blockLength - 5)) :
    (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
      hunique (sourceTwoTileSuccessorStartOffset offset)).toInterface =
    (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique (sourceTwoTileSuccessorNextOffset offset)).toInterface := by
  rfl

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
