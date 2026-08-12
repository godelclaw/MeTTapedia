import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixSeamSupport
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSetRegionUnion

/-!
# The literal source prefix is a vertex-side carrier

Each literal source Cell is the regional edge carrier induced by the
complementary side of its source crosscut.  Since regional edge carriers
commute with finite unions, the cumulative literal prefix is itself the
carrier induced by the union of those Cell sides.

This identifies the real vertex side underlying the prefix.  It deliberately
does not identify the true crossing-edge frontier of that side with the two
caller-supplied moving-cut edges; that is the next geometric question.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialPrefixVertexSideEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The vertex side whose regional carrier is one literal source Cell. -/
noncomputable def sourceSlabLiteralCellVertexSideAt
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
    (offset : Fin (blockLength - 3)) : Finset V :=
  ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).separatedLocalLayerPair.componentSide
    ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).localLayerPairSourceCrosscutBoundaryData hcubic).component)ᶜ

/-- One literal Cell is exactly the edge carrier induced by its named vertex
side. -/
theorem sourceSlabLiteralCellRegionAt_eq_vertexSetRegionEdges_cellSide
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
    sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
        hunique offset =
      vertexSetRegionEdges embedded.cellulation.rotation.toRotationSystem
        (sourceSlabLiteralCellVertexSideAt realization hcubic hrotation
          htwoSided hunique offset) := by
  simpa [sourceSlabLiteralCellVertexSideAt] using
    sourceSlabLiteralCellRegionAt_eq_vertexSetRegionEdges_compl realization
      hcubic hrotation htwoSided hunique offset

/-- A literal Cell has four genuine vertex-side frontier edges: its two
incoming source crossings and its two outgoing source crossings.  In
particular, the displayed two-edge moving cut is one interface of the Cell,
not the whole graph-theoretic frontier of its vertex side. -/
theorem sourceSlabLiteralCellTrueCrossingEdges_card_eq_four
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
    (vertexSetCrossingEdges
      embedded.cellulation.rotation.toRotationSystem
      (sourceSlabLiteralCellVertexSideAt realization hcubic hrotation
        htwoSided hunique offset)).card = 4 := by
  let interface :=
    sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique offset
  let pair := interface.separatedLocalLayerPair
  let boundary := interface.localLayerPairSourceCrosscutBoundaryData hcubic
  rw [← card_vertexSetCrossingEdge]
  calc
    Fintype.card (VertexSetCrossingEdge
        embedded.cellulation.rotation.toRotationSystem
        (sourceSlabLiteralCellVertexSideAt realization hcubic hrotation
          htwoSided hunique offset)) =
        Fintype.card
          (Fin pair.left.walk.length ⊕ Fin pair.right.walk.length) := by
      apply Fintype.card_congr
      simpa [sourceSlabLiteralCellVertexSideAt, interface, pair, boundary] using
        (pair.sourceCrosscutComplementPort
          embedded.cellulation.rotation boundary).symm
    _ = 4 := by
      simp [pair, interface,
        SourceConsecutiveSlabInterface.separatedLocalLayerPair,
        interface.localLayer_walk_length_eq_two,
        interface.nextLocalLayer_walk_length_eq_two]

/-- The two outgoing crossings are not, by themselves, the true boundary of
the literal Cell vertex side.  They are the moving output interface; the two
incoming crossings remain the fixed input interface. -/
theorem sourceSlabLiteralCellTrueCrossingEdges_ne_outputCut
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
    vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
        (sourceSlabLiteralCellVertexSideAt realization hcubic hrotation
          htwoSided hunique offset) ≠
      Finset.univ.image ((sourceSlabInterfaceAt realization hcubic hrotation
        htwoSided hunique offset).nextLocalLayerPrefixCrossing) := by
  intro heq
  have hcard := congrArg Finset.card heq
  rw [sourceSlabLiteralCellTrueCrossingEdges_card_eq_four realization hcubic
      hrotation htwoSided hunique offset,
    Finset.card_image_iff.mpr
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing_injective.injOn)] at hcard
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- The retained vertex data of the first `cut` literal Cells. -/
noncomputable def sourceCorridorSerialPrefixVertexSide
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
    (cut : Nat) : Finset V :=
  (Finset.univ.filter fun offset : Fin (blockLength - 3) => offset.val < cut)
    |>.biUnion
      (sourceSlabLiteralCellVertexSideAt realization hcubic hrotation
        htwoSided hunique)

/-- The cumulative literal prefix is not an arbitrary edge region: it is
exactly the regional edge carrier induced by the union of its Cell sides. -/
theorem sourceCorridorSerialPrefixRegion_eq_vertexSetRegionEdges
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
    (cut : Nat) :
    sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
        hunique cut =
      vertexSetRegionEdges embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixVertexSide realization hcubic hrotation
          htwoSided hunique cut) := by
  unfold sourceCorridorSerialPrefixRegion
  unfold sourceCorridorSerialPrefixVertexSide
  rw [← vertexSetRegionEdges_biUnion]
  ext edge
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨offset, hoffset, hedge⟩
    refine ⟨offset, hoffset, ?_⟩
    rw [← sourceSlabLiteralCellRegionAt_eq_vertexSetRegionEdges_cellSide]
    exact hedge
  · rintro ⟨offset, hoffset, hedge⟩
    refine ⟨offset, hoffset, ?_⟩
    rw [sourceSlabLiteralCellRegionAt_eq_vertexSetRegionEdges_cellSide]
    exact hedge

/-- The actual graph-theoretic frontier of the cumulative literal prefix.
Unlike the displayed `Fin 2` moving cut, this definition computes every edge
crossing the prefix's proved vertex side. -/
noncomputable def sourceCorridorSerialPrefixTrueCrossingEdges
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
    (cut : Nat) : Finset G.edgeSet :=
  vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialPrefixVertexSide realization hcubic hrotation
      htwoSided hunique cut)

/-- A genuine frontier edge of the cumulative prefix must be an incoming or
outgoing crossing of one of its literal Cells.  This is an exact finite
classification of the candidates, but not yet the cancellation theorem that
would reduce them to the two ends of the serial prefix. -/
theorem sourceCorridorSerialPrefixTrueCrossingEdge_eq_cell_input_or_output
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
    (cut : Nat) {edge : G.edgeSet}
    (hedge : edge ∈ sourceCorridorSerialPrefixTrueCrossingEdges realization
      hcubic hrotation htwoSided hunique cut) :
    ∃ offset : Fin (blockLength - 3), offset.val < cut ∧
      ((∃ step : Fin 2,
          edge = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique offset).localLayerPrefixCrossing step) ∨
        ∃ step : Fin 2,
          edge = (sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique offset).nextLocalLayerPrefixCrossing step) := by
  let indices :=
    Finset.univ.filter fun offset : Fin (blockLength - 3) => offset.val < cut
  have hcandidate := vertexSetCrossingEdges_biUnion_subset
    embedded.cellulation.rotation.toRotationSystem indices
      (sourceSlabLiteralCellVertexSideAt realization hcubic hrotation
        htwoSided hunique) hedge
  rcases Finset.mem_biUnion.mp hcandidate with
    ⟨offset, hoffset, hedgeCell⟩
  have hoffsetLt : offset.val < cut := by
    simpa [indices] using hoffset
  have hedgeCell' : edge ∈
      vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
        ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
            offset).separatedLocalLayerPair.componentSide
          ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
              hunique offset).localLayerPairSourceCrosscutBoundaryData
            hcubic).component)ᶜ := by
    simpa [sourceSlabLiteralCellVertexSideAt] using hedgeCell
  exact ⟨offset, hoffsetLt,
    sourceSlabLiteralCellCrossing_eq_input_or_output realization hcubic
      hrotation htwoSided hunique offset hedgeCell'⟩

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
