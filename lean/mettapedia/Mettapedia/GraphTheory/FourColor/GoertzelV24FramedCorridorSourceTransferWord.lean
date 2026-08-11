import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorTransferWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalBoundedCountSupport
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceProfileWord

/-!
# The heterogeneous local-Cell support word of a realized corridor

Each literal Cell-3 region of a clean source corridor has its own transfer
relation on the common bounded zero-terminal local-profile carrier.  Reading
those relations in source order gives a concrete word of local Cell supports.
No homogeneity of successive Cells is asserted here.

This is an input to the generic heterogeneous word semantics in
`GoertzelV24CorridorTransferWord`.  It is not yet the manuscript's completed
cross-section word: a terminal-aware update theorem must connect cumulative
connectivity to the five cap feet before endpoint acceptance or Menu-B can
factor through it.
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

local instance framedCorridorSourceTransferWordEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The literal positive-support relation of the Cell at one indexed source
position, transported to the common bounded full-profile carrier. -/
noncomputable def sourceSlabCellBoundedProfileTransferAt
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
    SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile →
      SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile → Prop :=
  (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique offset)
    |>.localLayerPairCellBoundedProfileTransfer hcubic

/-- The heterogeneous word of all indexed local Cell-3 support relations in
one realized corridor.  Its order is the source order on
`Fin (blockLength - 3)`, not an arbitrary enumeration of Cells. -/
noncomputable def sourceCorridorCellTransferWord
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
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))) :
    List (SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile →
      SourceConsecutiveSlabInterface.LocalLayerPairCellBoundedProfile → Prop) :=
  List.ofFn fun offset =>
    sourceSlabCellBoundedProfileTransferAt realization hcubic hrotation
      htwoSided hunique offset

/-- The source transfer word has exactly one relation for every indexed
Cell-3 region. -/
@[simp]
theorem sourceCorridorCellTransferWord_length
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
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))) :
    (sourceCorridorCellTransferWord realization hcubic hrotation htwoSided
      hunique).length = blockLength - 3 := by
  simp [sourceCorridorCellTransferWord]

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
