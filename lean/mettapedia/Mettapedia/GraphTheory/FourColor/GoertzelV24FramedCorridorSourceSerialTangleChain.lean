import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceSerialTransfer
import Mettapedia.GraphTheory.FourColor.GoertzelV24SerialOpenTangleChain

/-!
# The source corridor as a heterogeneous literal tangle chain

Every source Cell already has a complementary removed-region presentation as
a two-sided open tangle.  Its literal boundary carriers have dependent
lengths, although the source geometry proves both lengths are two.  Here those
proofs become explicit coordinate equivalences from the common `Fin 2`
interface, and the Cells are listed in their source order.

The resulting nonempty chain has exact `ExactTransferWord` support by the
generic literal composition theorem.  This is the concrete color-support
assembly of the Cell word.  It does not identify the carrier of the iterated
composition with a separately constructed ambient prefix region, and it does
not project complete profiles to color words.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24CorridorTransferWord
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OpenTangleComposition
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSourceSerialTangleChainEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- One literal complementary source Cell with both interfaces reindexed by
the common two-position source coordinate. -/
noncomputable def sourceSlabCoordinatizedComplementTangleAt
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
    CoordinatizedTwoSidedOpenTangle (Fin 2) :=
  let interface :=
    sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique offset
  let pair := interface.separatedLocalLayerPair
  let boundary := interface.localLayerPairSourceCrosscutBoundaryData hcubic
  {
    V := { vertex : V // vertex ∉ pair.componentSide boundary.component }
    I := InternalDart embedded.cellulation.rotation.toRotationSystem
      (fun vertex => vertex ∉ pair.componentSide boundary.component)
    L := Fin pair.left.walk.length
    R := Fin pair.right.walk.length
    data := pair.sourceCrosscutComplementTwoSidedOpenTangle
      embedded.cellulation.rotation boundary hcubic
    leftCoordinate := finCongr interface.localLayer_walk_length_eq_two.symm
    rightCoordinate := finCongr
      interface.nextLocalLayer_walk_length_eq_two.symm
  }

/-- The source-ordered list of all literal complementary Cells in one
realized corridor. -/
noncomputable def sourceCorridorCoordinatizedComplementTangles
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
    List (CoordinatizedTwoSidedOpenTangle (Fin 2)) :=
  List.ofFn fun offset =>
    sourceSlabCoordinatizedComplementTangleAt realization hcubic hrotation
      htwoSided hunique offset

@[simp]
theorem sourceCorridorCoordinatizedComplementTangles_length
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
    (sourceCorridorCoordinatizedComplementTangles realization hcubic hrotation
      htwoSided hunique).length = blockLength - 3 := by
  simp [sourceCorridorCoordinatizedComplementTangles]

/-- A positive-length source corridor has a literal heterogeneous serial
composite.  The changing internal carriers remain hidden by the generic
coordinatized package. -/
noncomputable def sourceCorridorComplementSerialComposite
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
    (hcells : 0 < blockLength - 3) :
    CoordinatizedTwoSidedOpenTangle (Fin 2) := by
  let cells := sourceCorridorCoordinatizedComplementTangles realization
    hcubic hrotation htwoSided hunique
  have hcellsNe : cells ≠ [] := by
    intro hempty
    have hlength : cells.length = 0 := by rw [hempty]; rfl
    have hsourceLength : cells.length = blockLength - 3 := by
      exact sourceCorridorCoordinatizedComplementTangles_length realization
        hcubic hrotation htwoSided hunique
    omega
  exact CoordinatizedTwoSidedOpenTangle.composeNonempty
    (cells.head hcellsNe) cells.tail

/-- The assembled literal source corridor accepts exactly the heterogeneous
support paths of its source-ordered Cell list. -/
theorem sourceCorridorComplementSerialComposite_acceptsBoundaryWords_iff
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
    (hcells : 0 < blockLength - 3)
    (leftWord rightWord : Fin 2 → Color) :
    (sourceCorridorComplementSerialComposite realization hcubic hrotation
        htwoSided hunique hcells).AcceptsBoundaryWords leftWord rightWord ↔
      ExactTransferWord
        ((sourceCorridorCoordinatizedComplementTangles realization hcubic
          hrotation htwoSided hunique).map
            CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords)
        leftWord rightWord := by
  let cells := sourceCorridorCoordinatizedComplementTangles realization
    hcubic hrotation htwoSided hunique
  have hcellsNe : cells ≠ [] := by
    intro hempty
    have hlength : cells.length = 0 := by rw [hempty]; rfl
    have hsourceLength : cells.length = blockLength - 3 := by
      exact sourceCorridorCoordinatizedComplementTangles_length realization
        hcubic hrotation htwoSided hunique
    omega
  change
    (CoordinatizedTwoSidedOpenTangle.composeNonempty
        (cells.head hcellsNe) cells.tail).AcceptsBoundaryWords
        leftWord rightWord ↔
      ExactTransferWord (cells.map
        CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords)
        leftWord rightWord
  rw [CoordinatizedTwoSidedOpenTangle.composeNonempty_acceptsBoundaryWords_iff_exactTransferWord]
  have hcons : cells.head hcellsNe :: cells.tail = cells :=
    List.cons_head_tail hcellsNe
  have hsupport :
      CoordinatizedTwoSidedOpenTangle.supportWord
          (cells.head hcellsNe) cells.tail =
        cells.map CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords := by
    change
      CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords
          (cells.head hcellsNe) ::
          cells.tail.map
            CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords =
        cells.map CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords
    exact congrArg
      (List.map CoordinatizedTwoSidedOpenTangle.AcceptsBoundaryWords) hcons
  rw [hsupport]

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
