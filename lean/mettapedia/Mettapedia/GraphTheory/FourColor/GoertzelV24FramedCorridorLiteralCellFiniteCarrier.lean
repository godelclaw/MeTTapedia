import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFourEdgeConnectedSides
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutConnectedSides
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixVertexSide

/-!
# A finite-carrier dichotomy for one literal source Cell

In a closed cubic cyclically five-edge-connected ambient carrier, the literal
Cell side and its retained complement are connected and have an exact
four-edge frontier.  The generic cubic count therefore makes one side a
two-vertex side.  If it is the Cell side, its complete regional edge carrier
has at most six edges.

The theorem is intentionally a dichotomy.  It neither assumes that a
well-formed open source carrier is globally cubic nor silently chooses which
side of the separator is small.  Ruling out a two-vertex retained side at the
closed-web use site is the remaining orientation obligation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24CubicFourEdgeConnectedSides
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

local instance framedCorridorLiteralCellFiniteCarrierEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance framedCorridorLiteralCellFiniteCarrierLocallyFinite :
    G.LocallyFinite :=
  fun vertex =>
    @Subtype.fintype V (Membership.mem (G.neighborSet vertex))
      (inferInstance : DecidablePred (Membership.mem (G.neighborSet vertex)))
      inferInstance

namespace SourceTrail

namespace AnnularEmbedding

/-- One side of every literal Cell four-edge separator in a closed cubic
cyclically five-edge-connected ambient carrier has exactly two vertices. -/
theorem sourceSlabLiteralCell_card_eq_two_or_compl_card_eq_two
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (offset : Fin (blockLength - 3)) :
    Nat.card {vertex : V // vertex ∈
        sourceSlabLiteralCellVertexSideAt realization hcubic hrotation
          htwoSided hunique offset} = 2 ∨
      Nat.card {vertex : V // vertex ∉
        sourceSlabLiteralCellVertexSideAt realization hcubic hrotation
          htwoSided hunique offset} = 2 := by
  let interface :=
    sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique offset
  let pair := interface.separatedLocalLayerPair
  let boundary := interface.localLayerPairSourceCrosscutBoundaryData hcubic
  let side := sourceSlabLiteralCellVertexSideAt realization hcubic hrotation
    htwoSided hunique offset
  have hregular : G.IsRegularOfDegree 3 :=
    embedded.cellulation.rotation.toRotationSystem_isCubic_iff.mp hcubic
  have hsideNonempty : ∃ vertex, vertex ∈ side := by
    refine ⟨boundary.removed, ?_⟩
    simpa [side, sourceSlabLiteralCellVertexSideAt, interface, pair, boundary]
      using boundary.removed_not_kept
  have hcomplNonempty : ∃ vertex, vertex ∉ side := by
    refine ⟨embedded.cellulation.rotation.toRotationSystem.vertOf
      embedded.cellulation.rotation.toRotationSystem.outer, ?_⟩
    simpa [side, sourceSlabLiteralCellVertexSideAt, interface, pair, boundary]
      using boundary.outer_kept
  have hsideConnected :
      (G.induce {vertex | vertex ∈ side}).Connected := by
    have h :=
      SeparatedAlignedSimpleDualCrosscuts.SourceCrosscutBoundaryData.componentSide_complement_connected
        embedded.cellulation.rotation htwoSided embedded.cellulation.connected
          pair boundary
    have hsideEq :
        {vertex : V | vertex ∈ side} =
          {vertex : V | vertex ∉ pair.componentSide boundary.component} := by
      ext vertex
      simp [side, sourceSlabLiteralCellVertexSideAt, interface, pair, boundary]
    rw [hsideEq]
    exact h
  have hcomplConnected :
      (G.induce {vertex | vertex ∉ side}).Connected := by
    have h :=
      SeparatedAlignedSimpleDualCrosscuts.SourceCrosscutBoundaryData.componentSide_connected
        embedded.cellulation.rotation pair boundary
    have hcomplEq :
        {vertex : V | vertex ∉ side} =
          {vertex : V | vertex ∈ pair.componentSide boundary.component} := by
      ext vertex
      simp [side, sourceSlabLiteralCellVertexSideAt, interface, pair, boundary]
    rw [hcomplEq]
    exact h
  have hboundaryCard :
      (GoertzelV24CubicSmallBoundaryCycle.crossingEdgeFinset G
        (fun vertex => vertex ∈ side)).card = 4 := by
    have hfinset :
        GoertzelV24CubicSmallBoundaryCycle.crossingEdgeFinset G
            (fun vertex => vertex ∈ side) =
          vertexSetCrossingEdges
            embedded.cellulation.rotation.toRotationSystem side := by
      ext edge
      rw [GoertzelV24CubicSmallBoundaryCycle.mem_crossingEdgeFinset_iff,
        mem_simpleGraph_vertexSetCrossingEdges_iff]
    rw [hfinset]
    simpa [side] using
      sourceSlabLiteralCellTrueCrossingEdges_card_eq_four realization hcubic
        hrotation htwoSided hunique offset
  exact
    card_eq_two_or_compl_card_eq_two_of_cubic_of_connected_sides_of_boundary_card_eq_four
      hregular hcyclic (fun vertex => vertex ∈ side) hsideNonempty
        hsideConnected hcomplNonempty hcomplConnected hboundaryCard

/-- If the two-vertex side is the literal Cell side, the complete Cell region
has a six-edge graph-independent carrier bound. -/
theorem sourceSlabLiteralCellRegionAt_card_le_six_of_cell_card_eq_two
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
    (hcell : Nat.card {vertex : V // vertex ∈
      sourceSlabLiteralCellVertexSideAt realization hcubic hrotation
        htwoSided hunique offset} = 2) :
    (sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
      hunique offset).card ≤ 6 := by
  let side := sourceSlabLiteralCellVertexSideAt realization hcubic hrotation
    htwoSided hunique offset
  have hsideCard : side.card = 2 := by
    simpa [side] using hcell
  rw [sourceSlabLiteralCellRegionAt_eq_vertexSetRegionEdges_cellSide]
  exact vertexSetRegionEdges_card_le_six_of_cubic_of_card_eq_two
    embedded.cellulation.rotation.toRotationSystem hcubic side hsideCard

/-- The source separator therefore yields either the desired six-edge Cell
carrier or one sharply named orientation residue: the retained side has two
vertices. -/
theorem sourceSlabLiteralCellRegionAt_card_le_six_or_retained_card_eq_two
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (offset : Fin (blockLength - 3)) :
    (sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
      hunique offset).card ≤ 6 ∨
      Nat.card {vertex : V // vertex ∉
        sourceSlabLiteralCellVertexSideAt realization hcubic hrotation
          htwoSided hunique offset} = 2 := by
  rcases sourceSlabLiteralCell_card_eq_two_or_compl_card_eq_two realization
      hcubic hrotation htwoSided hunique hcyclic offset with hcell | hretained
  · exact Or.inl
      (sourceSlabLiteralCellRegionAt_card_le_six_of_cell_card_eq_two
        realization hcubic hrotation htwoSided hunique offset hcell)
  · exact Or.inr hretained

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
