import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileEnclosedProfileRestriction

/-!
# Consecutive transverse interfaces of physical aligned slabs

An aligned two-tile slab runs from one source transversal to the next one.
This file records the exact primal-edge match between the output transverse
block of one such slab and the input transverse block of its successor.

The result is intentionally only an edge-coordinate fact.  It does not
identify boundary darts, prove that the enclosed regions are disjoint, or
construct their serial open-tangle composite.
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

local instance framedCorridorAlignedTwoTileSuccessorInterfaceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Embed a position admitting a successor physical slab as the left position
of the corresponding consecutive aligned pair. -/
def sourceTwoTileSuccessorStartOffset {blockLength : Nat}
    (offset : Fin (blockLength - 5)) : Fin (blockLength - 4) :=
  ⟨offset.val, by
    have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
    apply (Nat.lt_sub_iff_add_lt).2
    omega⟩

/-- The following physical aligned slab position. -/
def sourceTwoTileSuccessorNextOffset {blockLength : Nat}
    (offset : Fin (blockLength - 5)) : Fin (blockLength - 4) :=
  ⟨offset.val + 1, by
    have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
    apply (Nat.lt_sub_iff_add_lt).2
    omega⟩

/-- The output source-word interface of one physical slab is literally the
input source-word interface of its successor. -/
theorem sourceSlabRailFinishOffset_eq_successorStart
    {blockLength : Nat} (offset : Fin (blockLength - 5)) :
    sourceSlabRailFinishOffset (sourceTwoTileSuccessorStartOffset offset) =
      sourceSlabRailStartOffset (sourceTwoTileSuccessorNextOffset offset) := by
  apply Fin.ext
  rfl

/-- Consecutive physical aligned slabs expose the same two primal edges at
their adjoining transverse interface.  This is a necessary coordinate match
for serial gluing, not the gluing theorem itself. -/
theorem sourceTwoTileAlignedEnclosedOutputCrossing_eq_successorInputCrossing
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
    (offset : Fin (blockLength - 5)) (step : Fin 2) :
    (sourceTwoTileAlignedEnclosedSecondTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique (sourceTwoTileSuccessorStartOffset offset)
      |>.crossingEdge step) =
      (sourceTwoTileAlignedEnclosedFirstTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique (sourceTwoTileSuccessorNextOffset offset)
        |>.crossingEdge step) := by
  rw [sourceTwoTileAlignedEnclosedSecondTerminalProfileDataAt_crossingEdge,
    sourceTwoTileAlignedEnclosedFirstTerminalProfileDataAt_crossingEdge,
    sourceSlabRailFinishOffset_eq_successorStart]

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
