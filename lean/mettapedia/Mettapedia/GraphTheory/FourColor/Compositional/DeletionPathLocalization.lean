import Mettapedia.GraphTheory.FourColor.Compositional.AlternatingComponentLocalization
import Mettapedia.GraphTheory.FourColor.Compositional.DeletionAtlasPath

/-!
# Alternating-component localization along a coherent deletion path

A coherent deletion path only requires common-core agreement at consecutive
coordinates.  Nevertheless, any ambient edge retained by every deletion has
the same colour at every coordinate: evaluate the path section on that edge
and telescope the consecutive equalities.

If two coordinates use the same absent Tait colour, their completed matchings
therefore agree outside the union of the nine deletion footprints.  This union
has at most forty-five edges.  Taking symmetric difference with one fixed
matching preserves that agreement, so every walk in the source alternating
graph which avoids the footprint remains inside one target alternating
component.

This is deliberately a localization theorem.  It does not identify that
target component with the target coordinate's distinguished central
component.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.DeletionPathLocalization

open Amplitude
open AlternatingComponentLocalization
open AlternatingOverlapGeometry
open AlternatingSiteGeometry
open DeletionAtlasPath
open DeletionColorMatching
open DeletionSiteGeometry
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24AdjacentPairCommonCoreLocalization
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairMatchingExtraction.AdjacentPairData
open GoertzelV24AlternatingMatchingComponent
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.Logic
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The ambient edges removed by at least one coordinate of a nine-deletion
path. -/
def pathFootprint
    (family : PairDeletionColoringFamily (G := G) (Fin 9)) :
    Finset G.edgeSet :=
  Finset.univ.biUnion fun index : Fin 9 =>
    deletionFootprint (family.data index)

/-- Nine adjacent-pair deletion footprints contain at most forty-five
ambient edges. -/
theorem card_pathFootprint_le
    (family : PairDeletionColoringFamily (G := G) (Fin 9)) :
    (pathFootprint family).card ≤ 45 := by
  calc
    _ ≤ ∑ index : Fin 9,
        (deletionFootprint (family.data index)).card :=
      Finset.card_biUnion_le
    _ = ∑ _index : Fin 9, 5 := by
      apply Finset.sum_congr rfl
      intro index _
      exact card_deletionFootprint _
    _ = 45 := by norm_num

/-- A coherent path gives the same colour to an ambient edge at every
coordinate, provided every deletion retains that edge. -/
theorem pathColor_eq
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family))
    (edge : G.edgeSet)
    (hretained : ∀ index : Fin 9,
      IsRetainedAmbientEdge (family.data index) edge)
    (first second : Fin 9) :
    (pathSection.state first).1
        (ambientEdgeToRetainedEdge
          (family.data first) edge (hretained first)) =
      (pathSection.state second).1
        (ambientEdgeToRetainedEdge
          (family.data second) edge (hretained second)) := by
  let observe := fun (index : Fin 9)
      (coloring : TaitColoringAt family index) =>
    coloring.1 (ambientEdgeToRetainedEdge
      (family.data index) edge (hretained index))
  have hobserve : ∀ (index : Fin 8)
      (source : TaitColoringAt family index.castSucc)
      (target : TaitColoringAt family index.succ),
      ConsecutiveRepairCompatible family index source target →
        observe index.castSucc source = observe index.succ target := by
    intro index source target hcompatible
    exact (commonCoreAgrees_iff_ambient
      (family.data index.castSucc) (family.data index.succ)
      source.1 target.1).1 hcompatible.2 edge
        (hretained index.castSucc) (hretained index.succ)
  have hfirst := PathConstraint.section_observe_eq_last
    pathSection observe hobserve first
  have hsecond := PathConstraint.section_observe_eq_last
    pathSection observe hobserve second
  exact hfirst.trans hsecond.symm

/-- Equal absent colours make two completed path matchings agree outside the
whole path footprint. -/
theorem matchingStates_agree_outside_pathFootprint
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family))
    (first second : Fin 9)
    (habsent :
      (matchingState rotation minimal family pathSection first).absentColor =
        (matchingState rotation minimal family pathSection second).absentColor)
    (edge : G.edgeSet) (houtside : edge ∉ pathFootprint family) :
    edge.1 ∈ edges
        ((matchingState rotation minimal family pathSection first).pairing
          (ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
            rotation minimal)).toPerm ↔
      edge.1 ∈ edges
        ((matchingState rotation minimal family pathSection second).pairing
          (ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
            rotation minimal)).toPerm := by
  have hretained : ∀ index : Fin 9,
      IsRetainedAmbientEdge (family.data index) edge := by
    intro index
    by_contra hnot
    apply houtside
    exact Finset.mem_biUnion.2
      ⟨index, Finset.mem_univ _, (mem_deletionFootprint_iff _ _).2 hnot⟩
  have hcolor := pathColor_eq family pathSection edge hretained first second
  let hcubic :=
    ResidualSiteProvenance.incidentEdgeFinset_card_eq_three rotation minimal
  simp only [DeletionMatchingState.pairing]
  rw [centralCompletionPairing_mem_retainedEdge_iff
    (family.data first) hcubic
    (matchingState rotation minimal family pathSection first).coloring
    (matchingState rotation minimal family pathSection first).isTait
    (matchingState rotation minimal family pathSection first).absentColor
    (matchingState rotation minimal family pathSection first).absentAtBoundary
    edge (hretained first)]
  rw [centralCompletionPairing_mem_retainedEdge_iff
    (family.data second) hcubic
    (matchingState rotation minimal family pathSection second).coloring
    (matchingState rotation minimal family pathSection second).isTait
    (matchingState rotation minimal family pathSection second).absentColor
    (matchingState rotation minimal family pathSection second).absentAtBoundary
    edge (hretained second)]
  change (pathSection.state first).1 _ = _ ↔
    (pathSection.state second).1 _ = _
  rw [hcolor, habsent]

/-- Taking symmetric difference with a common supported matching preserves
the endpoint agreement outside the path footprint. -/
theorem alternatingGraphs_agree_outside_pathFootprint
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family))
    (sigma : Pairing V)
    (first second : Fin 9)
    (habsent :
      (matchingState rotation minimal family pathSection first).absentColor =
        (matchingState rotation minimal family pathSection second).absentColor)
    (edge : G.edgeSet) (houtside : edge ∉ pathFootprint family) :
    edge.1 ∈ (alternatingGraph sigma
        ((matchingState rotation minimal family pathSection first).pairing
          (ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
            rotation minimal))).edgeSet ↔
      edge.1 ∈ (alternatingGraph sigma
        ((matchingState rotation minimal family pathSection second).pairing
          (ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
            rotation minimal))).edgeSet := by
  apply alternatingGraph_mem_edgeSet_congr_right
  exact matchingStates_agree_outside_pathFootprint
    rotation minimal family pathSection first second habsent edge houtside

/-- The two endpoint alternating graphs disagree on at most the forty-five
edges of the path footprint. -/
theorem card_alternatingGraph_edgeDisagreement_le
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family))
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    (first second : Fin 9)
    (habsent :
      (matchingState rotation minimal family pathSection first).absentColor =
        (matchingState rotation minimal family pathSection second).absentColor) :
    (SimpleGraph.edgeDisagreementFinset
      (alternatingGraph sigma
        ((matchingState rotation minimal family pathSection first).pairing
          (ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
            rotation minimal)))
      (alternatingGraph sigma
        ((matchingState rotation minimal family pathSection second).pairing
          (ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
            rotation minimal)))).card ≤ 45 := by
  let hcubic :=
    ResidualSiteProvenance.incidentEdgeFinset_card_eq_three rotation minimal
  calc
    _ ≤ (pathFootprint family).card :=
      AlternatingOverlapGeometry.card_alternatingGraph_edgeDisagreement_le_of_pairings_agree_outside
        sigma
        ((matchingState rotation minimal family pathSection first).pairing hcubic)
        ((matchingState rotation minimal family pathSection second).pairing hcubic)
        hSigma
        ((matchingState rotation minimal family pathSection first).pairing_supported hcubic)
        ((matchingState rotation minimal family pathSection second).pairing_supported hcubic)
        (pathFootprint family)
        (matchingStates_agree_outside_pathFootprint
          rotation minimal family pathSection first second habsent)
    _ ≤ 45 := card_pathFootprint_le family

/-- A source alternating-graph walk avoiding the path footprint remains a
walk, hence a reachability witness, in the target alternating graph. -/
theorem alternatingWalk_reachable_in_target
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family))
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    (first second : Fin 9)
    (habsent :
      (matchingState rotation minimal family pathSection first).absentColor =
        (matchingState rotation minimal family pathSection second).absentColor)
    {left right : V}
    (walk : (alternatingGraph sigma
      ((matchingState rotation minimal family pathSection first).pairing
        (ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
          rotation minimal))).Walk left right)
    (havoids : ∀ edge : G.edgeSet, edge.1 ∈ walk.edges →
      edge ∉ pathFootprint family) :
    (alternatingGraph sigma
      ((matchingState rotation minimal family pathSection second).pairing
        (ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
          rotation minimal))).Reachable left right := by
  let hcubic :=
    ResidualSiteProvenance.incidentEdgeFinset_card_eq_three rotation minimal
  let sourceGraph := alternatingGraph sigma
    ((matchingState rotation minimal family pathSection first).pairing hcubic)
  let targetGraph := alternatingGraph sigma
    ((matchingState rotation minimal family pathSection second).pairing hcubic)
  have hsourceLe : sourceGraph ≤ G :=
    alternatingGraph_le sigma
      ((matchingState rotation minimal family pathSection first).pairing hcubic)
      hSigma
      ((matchingState rotation minimal family pathSection first).pairing_supported hcubic)
  have htransfer : ∀ edge, edge ∈ walk.edges → edge ∈ targetGraph.edgeSet := by
    intro edge hedge
    let ambient : G.edgeSet :=
      ⟨edge, SimpleGraph.edgeSet_mono hsourceLe
        (walk.edges_subset_edgeSet hedge)⟩
    have hagrees := alternatingGraphs_agree_outside_pathFootprint
      rotation minimal family pathSection sigma first second habsent ambient
        (havoids ambient hedge)
    exact hagrees.mp (walk.edges_subset_edgeSet hedge)
  exact (walk.transfer targetGraph htransfer).reachable

/-- Component-valued form of `alternatingWalk_reachable_in_target`. -/
theorem alternatingWalk_component_eq_in_target
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family))
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    (first second : Fin 9)
    (habsent :
      (matchingState rotation minimal family pathSection first).absentColor =
        (matchingState rotation minimal family pathSection second).absentColor)
    {left right : V}
    (walk : (alternatingGraph sigma
      ((matchingState rotation minimal family pathSection first).pairing
        (ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
          rotation minimal))).Walk left right)
    (havoids : ∀ edge : G.edgeSet, edge.1 ∈ walk.edges →
      edge ∉ pathFootprint family) :
    (alternatingGraph sigma
      ((matchingState rotation minimal family pathSection second).pairing
        (ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
          rotation minimal))).connectedComponentMk left =
      (alternatingGraph sigma
        ((matchingState rotation minimal family pathSection second).pairing
          (ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
            rotation minimal))).connectedComponentMk right :=
  SimpleGraph.ConnectedComponent.sound
    (alternatingWalk_reachable_in_target rotation minimal family pathSection
      sigma hSigma first second habsent walk havoids)

/-- Consumer-facing localization of a coherent two-sector pair.  The two
receipt-bearing coordinates supplied by the finite path have endpoint
alternating graphs whose edge disagreement is bounded by the forty-five-edge
path footprint. -/
theorem exists_endpoint_edgeDisagreement_le_of_hasCoherentTwoSectorPair
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (hcoherent : HasCoherentTwoSectorPair rotation minimal family minimizer) :
    ∃ pathSection : PathConstraint.Section
        (fun index : Fin 9 => TaitColoringAt family index)
        (ConsecutiveRepairCompatible family),
      pathSection.state (Fin.last 8) =
          (baseAssignment family) (Fin.last 8) ∧
        ∃ first second : Fin 9, first ≠ second ∧
          (matchingState rotation minimal family pathSection first).absentColor =
            (matchingState rotation minimal family pathSection second).absentColor ∧
          Nonempty (DeletionTwoSectorReturnReceipt rotation minimal minimizer
            (family.data first)
            (matchingState rotation minimal family pathSection first)) ∧
          Nonempty (DeletionTwoSectorReturnReceipt rotation minimal minimizer
            (family.data second)
            (matchingState rotation minimal family pathSection second)) ∧
          (SimpleGraph.edgeDisagreementFinset
            (alternatingGraph minimizer.pairing
              ((matchingState rotation minimal family pathSection first).pairing
                (ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
                  rotation minimal)))
            (alternatingGraph minimizer.pairing
              ((matchingState rotation minimal family pathSection second).pairing
                (ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
                  rotation minimal)))).card ≤ 45 := by
  rcases hcoherent with
    ⟨pathSection, hterminal, first, second, hne, habsent,
      hfirstReceipt, hsecondReceipt⟩
  refine ⟨pathSection, hterminal, first, second, hne, habsent,
    hfirstReceipt, hsecondReceipt, ?_⟩
  exact card_alternatingGraph_edgeDisagreement_le rotation minimal family
    pathSection minimizer.pairing minimizer.supported first second habsent

end

end Mettapedia.GraphTheory.FourColor.Compositional.DeletionPathLocalization
