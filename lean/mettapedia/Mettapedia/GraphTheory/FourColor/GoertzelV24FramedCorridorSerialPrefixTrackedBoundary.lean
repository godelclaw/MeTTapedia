import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixVertexSide
import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphBackedTrackedDegree
import Mettapedia.GraphTheory.FourColor.GoertzelV24RegionalTrackedVertexBoundary

/-!
# Tracked components reach the true serial-prefix boundary

The cumulative literal-Cell prefix is already identified with a genuine
vertex-side carrier.  In a cubic Tait coloring, every selected ambient
two-colour edge has even degree.  Regional handshaking therefore sends any
odd endpoint of the restricted prefix graph to a distinct edge of the true
vertex-side boundary.

The source geometry then classifies that boundary edge as an input or output
crossing of one of the historical literal Cells in the prefix.  This is the
parity-to-source-boundary step of portal completeness.  It deliberately does
not assert that all historical interfaces have cancelled to the current
two-edge moving cut; that internal-interface cancellation remains a separate
geometric theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SimpleGraphTaitBridge
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialPrefixTrackedBoundaryEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Degree is invariant under graph equality and under the finite presentation
chosen for the common neighbor set. -/
private theorem degree_eq_of_graph_eq {W : Type*}
    {H K : SimpleGraph W} (hHK : H = K) (vertex : W)
    (hH : Fintype (H.neighborSet vertex))
    (hK : Fintype (K.neighborSet vertex)) :
    @SimpleGraph.degree W H vertex hH =
      @SimpleGraph.degree W K vertex hK := by
  subst K
  apply congrArg Finset.card
  ext neighbor
  simp

/-- An odd endpoint of a tracked graph restricted to the literal serial
prefix reaches a distinct edge of the prefix's actual vertex-side boundary.
The statement uses the true boundary, not the displayed moving cut. -/
theorem exists_distinct_reachable_truePrefixCrossing_of_odd_degree
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
    (cut : Nat)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcolor : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring color)
    {first second : Color} (hpair : ValidColorPair first second)
    (start : G.edgeSet)
    (hstartOdd : Odd ((regionalTrackedEdgeGraph
      embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialPrefixRegion realization hcubic hrotation
        htwoSided hunique cut) color first second).degree start)) :
    ∃ finish : G.edgeSet, finish ≠ start ∧
      finish ∈ sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
        hrotation htwoSided hunique cut ∧
      (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixRegion realization hcubic hrotation
          htwoSided hunique cut) color first second).Reachable start finish := by
  let side := sourceCorridorSerialPrefixVertexSide realization hcubic hrotation
    htwoSided hunique cut
  have hregion :
      sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
          hunique cut =
        vertexSetRegionEdges embedded.cellulation.rotation.toRotationSystem
          side := by
    simpa [side] using
      sourceCorridorSerialPrefixRegion_eq_vertexSetRegionEdges realization
        hcubic hrotation htwoSided hunique cut
  have hregionalGraph :
      regionalTrackedEdgeGraph embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialPrefixRegion realization hcubic hrotation
            htwoSided hunique cut) color first second =
        regionalTrackedEdgeGraph embedded.cellulation.rotation.toRotationSystem
          (vertexSetRegionEdges embedded.cellulation.rotation.toRotationSystem
            side) color first second := by
    rw [hregion]
  have hboundary :=
    exists_distinct_reachable_vertexSetCrossingEdge_of_odd_regional_degree
      embedded.cellulation.rotation.toRotationSystem side color first second
      start (by
        rw [← degree_eq_of_graph_eq hregionalGraph start _ _]
        exact hstartOdd) (by
          intro edge hedgeOdd
          let regional := regionalTrackedEdgeGraph
            embedded.cellulation.rotation.toRotationSystem
            (vertexSetRegionEdges
              embedded.cellulation.rotation.toRotationSystem side)
            color first second
          have hedgeOdd' : Odd (regional.degree edge) := by
            rcases hedgeOdd with ⟨multiple, hmultiple⟩
            refine ⟨multiple, ?_⟩
            rw [← hmultiple]
            exact degree_eq_of_graph_eq rfl edge _ _
          rcases (regional.degree_pos_iff_exists_adj edge).1 hedgeOdd'.pos with
            ⟨neighbor, hadj⟩
          have heven := trackedEdgeGraph_degree_even_of_cubic_tait
            embedded.cellulation.rotation hcubic color hcolor hpair edge
              hadj.1.2.1
          rw [← degree_eq_of_graph_eq rfl edge _ _]
          exact heven)
  rcases hboundary with ⟨finish, hne, hcrossing, hreachable⟩
  refine ⟨finish, hne, ?_, ?_⟩
  · simpa [sourceCorridorSerialPrefixTrueCrossingEdges, side] using hcrossing
  · simpa only [hregion] using hreachable

/-- The boundary edge reached by parity is one of the input or output
crossings of a literal Cell already present in the prefix.  This is the exact
finite source classification available before internal interfaces are
cancelled to the two surviving end portals. -/
theorem exists_distinct_reachable_historicalCellCrossing_of_odd_degree
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
    (cut : Nat)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcolor : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring color)
    {first second : Color} (hpair : ValidColorPair first second)
    (start : G.edgeSet)
    (hstartOdd : Odd ((regionalTrackedEdgeGraph
      embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialPrefixRegion realization hcubic hrotation
        htwoSided hunique cut) color first second).degree start)) :
    ∃ finish : G.edgeSet, finish ≠ start ∧
      (∃ offset : Fin (blockLength - 3), offset.val < cut ∧
        ((∃ step : Fin 2,
            finish = (sourceSlabInterfaceAt realization hcubic hrotation
              htwoSided hunique offset).localLayerPrefixCrossing step) ∨
          ∃ step : Fin 2,
            finish = (sourceSlabInterfaceAt realization hcubic hrotation
              htwoSided hunique offset).nextLocalLayerPrefixCrossing step)) ∧
      (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixRegion realization hcubic hrotation
          htwoSided hunique cut) color first second).Reachable start finish := by
  rcases exists_distinct_reachable_truePrefixCrossing_of_odd_degree
      realization hcubic hrotation htwoSided hunique cut color hcolor hpair
      start hstartOdd with ⟨finish, hne, hboundary, hreachable⟩
  rcases sourceCorridorSerialPrefixTrueCrossingEdge_eq_cell_input_or_output
      realization hcubic hrotation htwoSided hunique cut hboundary with
    ⟨offset, hoffset, hinterface⟩
  exact ⟨finish, hne, ⟨offset, hoffset, hinterface⟩, hreachable⟩

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
