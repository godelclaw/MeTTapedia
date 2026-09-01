import Mettapedia.GraphTheory.FourColor.Compositional.CoherentResidualReturnSweep
import Mettapedia.GraphTheory.FourColor.Compositional.DeletionPathConnectivityState

/-!
# Connectivity synchronization for coherent residual sweeps

A coherent geometric sweep pair already fixes two deletion colorings on one
common-core-compatible path.  This module compares their alternating
components through the fixed ninety-slot boundary state.

There are exactly two outcomes.  Either the two labelled connectivity states
are equal, or two explicit boundary slots change connectivity.  In the latter
case the represented vertices cannot be joined in the common graph obtained
by deleting the forty-five-edge path footprint.  Thus every failure of
synchronization is localized inside the finite exceptional patch.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace CoherentResidualReturnConnectivity

open AlternatingSiteGeometry
open AlternatingComponentLocalization
open CoherentResidualReturnSweep
open DeletionAtlasPath
open DeletionPathConnectivity
open DeletionPathConnectivityState
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24ResidualDefectDescent
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.Logic
open ResidualSiteMatchingOverlap
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The fixed boundary connectivity state at one coordinate of a coherent
geometric sweep pair. -/
def connectivityStateAt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (index : Fin 9) : SimpleGraph PathBoundarySlot :=
  pathConnectivityState
    (pathAlternatingGraph rotation minimal family pair.pathSection minimizer index)
    family

/-- A concrete failure of connectivity synchronization.  The two labelled
ports are connected in exactly one of the endpoint alternating graphs. -/
structure ConnectivityTransitionWitness
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) where
  left : PathBoundarySlot
  right : PathBoundarySlot
  reachabilityDiffers : ¬
    ((pathAlternatingGraph rotation minimal family pair.pathSection minimizer
        pair.first).Reachable
          (pathBoundaryVertex family left) (pathBoundaryVertex family right) ↔
      (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
        pair.second).Reachable
          (pathBoundaryVertex family left) (pathBoundaryVertex family right))

/-- The endpoint sweep pair is synchronized when its two fixed labelled
boundary connectivity states coincide. -/
def ConnectivitySynchronized
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) : Prop :=
  connectivityStateAt rotation minimal family minimizer pair pair.first =
    connectivityStateAt rotation minimal family minimizer pair pair.second

/-- Inequality of two normalized connectivity states exposes two exact fixed
boundary slots whose represented ambient reachability differs. -/
theorem exists_boundary_slots_of_connectivityStateAt_ne
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (first second : Fin 9)
    (hne : connectivityStateAt rotation minimal family minimizer pair first ≠
      connectivityStateAt rotation minimal family minimizer pair second) :
    ∃ left right : PathBoundarySlot, ¬
      ((pathAlternatingGraph rotation minimal family pair.pathSection minimizer
          first).Reachable
            (pathBoundaryVertex family left) (pathBoundaryVertex family right) ↔
        (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
          second).Reachable
            (pathBoundaryVertex family left)
            (pathBoundaryVertex family right)) := by
  classical
  have hnotAll : ¬ ∀ left right : PathBoundarySlot,
      (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
          first).Reachable
            (pathBoundaryVertex family left) (pathBoundaryVertex family right) ↔
        (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
          second).Reachable
            (pathBoundaryVertex family left)
            (pathBoundaryVertex family right) := by
    intro hall
    apply hne
    exact (pathConnectivityState_eq_iff
      (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
        first)
      (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
        second) family).2 hall
  by_contra hnone
  apply hnotAll
  intro left right
  by_contra hdiffers
  exact hnone ⟨left, right, hdiffers⟩

/-- One adjacent repair changes the chosen absent Tait colour.  This is a
finite colour-gauge transition, distinct from a geometric connectivity
transition at fixed colour. -/
structure AdjacentAbsentColorChangeReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) where
  index : Fin 8
  absentColor_ne :
    (matchingState rotation minimal family pair.pathSection
        index.castSucc).absentColor ≠
      (matchingState rotation minimal family pair.pathSection
        index.succ).absentColor

/-- A genuine adjacent connectivity transition at fixed absent colour.  Its
two endpoint graphs agree outside the two local deletion footprints. -/
structure LocalConnectivityTransitionReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) where
  index : Fin 8
  absentColor_eq :
    (matchingState rotation minimal family pair.pathSection
        index.castSucc).absentColor =
      (matchingState rotation minimal family pair.pathSection
        index.succ).absentColor
  left : PathBoundarySlot
  right : PathBoundarySlot
  reachabilityDiffers : ¬
    ((pathAlternatingGraph rotation minimal family pair.pathSection minimizer
        index.castSucc).Reachable
          (pathBoundaryVertex family left) (pathBoundaryVertex family right) ↔
      (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
        index.succ).Reachable
          (pathBoundaryVertex family left) (pathBoundaryVertex family right))

/-- The endpoint alternating graphs of a coherent pair are literally equal
away from the common forty-five-edge path footprint. -/
theorem deleteFootprint_eq
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) :
    (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
        pair.first).deleteEdges
          (pathFootprintValues family : Set (Sym2 V)) =
      (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
        pair.second).deleteEdges
          (pathFootprintValues family : Set (Sym2 V)) :=
  pathAlternatingGraphs_deleteFootprint_eq rotation minimal family
    pair.pathSection minimizer pair.first pair.second pair.absentColor_eq

/-- Every coherent geometric sweep pair is either connectivity-synchronized
or exposes two exact boundary ports whose component relation changes. -/
theorem synchronized_or_transition
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) :
    ConnectivitySynchronized rotation minimal family minimizer pair ∨
      Nonempty (ConnectivityTransitionWitness
        rotation minimal family minimizer pair) := by
  classical
  by_cases hsynchronized :
      ConnectivitySynchronized rotation minimal family minimizer pair
  · exact Or.inl hsynchronized
  · right
    rcases exists_boundary_slots_of_connectivityStateAt_ne
      rotation minimal family minimizer pair pair.first pair.second
        hsynchronized with ⟨left, right, hdiffers⟩
    exact ⟨⟨left, right, hdiffers⟩⟩

/-- The endpoint sweep states either synchronize, or one adjacent repair
changes the absent-colour gauge, or one same-colour adjacent repair changes
connectivity.  The last alternative is the genuinely local geometric
obstruction. -/
theorem synchronized_or_adjacentColorChange_or_localTransition
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) :
    ConnectivitySynchronized rotation minimal family minimizer pair ∨
      Nonempty (AdjacentAbsentColorChangeReceipt
        rotation minimal family minimizer pair) ∨
      Nonempty (LocalConnectivityTransitionReceipt
        rotation minimal family minimizer pair) := by
  classical
  by_cases hsynchronized :
      ConnectivitySynchronized rotation minimal family minimizer pair
  · exact Or.inl hsynchronized
  · have hadjacent := PathConstraint.exists_adjacent_ne_of_ne
        (fun index : Fin 9 ↦
          connectivityStateAt rotation minimal family minimizer pair index)
        hsynchronized
    rcases hadjacent with ⟨index, hstate⟩
    by_cases habsent :
        (matchingState rotation minimal family pair.pathSection
            index.castSucc).absentColor =
          (matchingState rotation minimal family pair.pathSection
            index.succ).absentColor
    · rcases exists_boundary_slots_of_connectivityStateAt_ne
        rotation minimal family minimizer pair index.castSucc index.succ
          hstate with ⟨left, right, hdiffers⟩
      exact Or.inr (Or.inr ⟨⟨index, habsent, left, right, hdiffers⟩⟩)
    · exact Or.inr (Or.inl ⟨⟨index, habsent⟩⟩)

/-- A same-colour adjacent transition has a compatible finite matching-overlap
state: consecutive path compatibility supplies the common-core coordinate. -/
theorem LocalConnectivityTransitionReceipt.matchingOverlapCompatible
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (receipt : LocalConnectivityTransitionReceipt
      rotation minimal family minimizer pair) :
    (matchingOverlapState
      (matchingState rotation minimal family pair.pathSection
        receipt.index.castSucc)
      (matchingState rotation minimal family pair.pathSection
        receipt.index.succ)).Compatible := by
  change
    (matchingState rotation minimal family pair.pathSection
        receipt.index.castSucc).absentColor =
        (matchingState rotation minimal family pair.pathSection
          receipt.index.succ).absentColor ∧
      commonRestrictionAgreementBit
        (family.data receipt.index.castSucc)
        (family.data receipt.index.succ)
        (matchingState rotation minimal family pair.pathSection
          receipt.index.castSucc).coloring
        (matchingState rotation minimal family pair.pathSection
          receipt.index.succ).coloring = true
  refine ⟨receipt.absentColor_eq, ?_⟩
  apply (commonRestrictionAgreementBit_eq_true_iff
    (family.data receipt.index.castSucc)
    (family.data receipt.index.succ)
    (matchingState rotation minimal family pair.pathSection
      receipt.index.castSucc).coloring
    (matchingState rotation minimal family pair.pathSection
      receipt.index.succ).coloring).2
  exact (pair.pathSection.compatible receipt.index).2

/-- A same-colour adjacent transition becomes literally equal after deleting
the union of its two five-edge footprints. -/
theorem LocalConnectivityTransitionReceipt.deleteLocalFootprint_eq
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (receipt : LocalConnectivityTransitionReceipt
      rotation minimal family minimizer pair) :
    (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
        receipt.index.castSucc).deleteEdges
          (overlapFootprintValues
            (family.data receipt.index.castSucc)
            (family.data receipt.index.succ) : Set (Sym2 V)) =
      (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
        receipt.index.succ).deleteEdges
          (overlapFootprintValues
            (family.data receipt.index.castSucc)
            (family.data receipt.index.succ) : Set (Sym2 V)) := by
  let hcubic :=
    ResidualSiteProvenance.incidentEdgeFinset_card_eq_three rotation minimal
  simpa only [pathAlternatingGraph, hcubic] using
    (alternatingGraphs_delete_overlapFootprints_eq
      minimizer.pairing minimizer.supported
      (matchingState rotation minimal family pair.pathSection
        receipt.index.castSucc)
      (matchingState rotation minimal family pair.pathSection
        receipt.index.succ)
      hcubic
      (receipt.matchingOverlapCompatible
        rotation minimal family minimizer pair))

/-- The exceptional carrier of a local connectivity transition contains at
most ten ambient edge values. -/
theorem LocalConnectivityTransitionReceipt.card_localFootprint_le
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (receipt : LocalConnectivityTransitionReceipt
      rotation minimal family minimizer pair) :
    (overlapFootprintValues
      (family.data receipt.index.castSucc)
      (family.data receipt.index.succ)).card ≤ 10 :=
  card_overlapFootprintValues_le _ _

/-- The changed boundary ports are disconnected in the graph common to the
two adjacent repairs after their ten-edge local footprint is deleted. -/
theorem LocalConnectivityTransitionReceipt.not_reachable_deleteLocalFootprint
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (receipt : LocalConnectivityTransitionReceipt
      rotation minimal family minimizer pair) :
    ¬ ((pathAlternatingGraph rotation minimal family pair.pathSection minimizer
          receipt.index.castSucc).deleteEdges
        (overlapFootprintValues
          (family.data receipt.index.castSucc)
          (family.data receipt.index.succ) : Set (Sym2 V))).Reachable
      (pathBoundaryVertex family receipt.left)
      (pathBoundaryVertex family receipt.right) := by
  exact SimpleGraph.not_reachable_deleteEdges_of_reachability_differs
    (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
      receipt.index.castSucc)
    (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
      receipt.index.succ)
    (overlapFootprintValues
      (family.data receipt.index.castSucc)
      (family.data receipt.index.succ))
    (receipt.deleteLocalFootprint_eq
      rotation minimal family minimizer pair)
    receipt.reachabilityDiffers

/-- One adjacent graph contains a connecting walk that necessarily traverses
one of the at most ten local footprint edges. -/
theorem LocalConnectivityTransitionReceipt.exists_walk_hitting_localFootprint
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (receipt : LocalConnectivityTransitionReceipt
      rotation minimal family minimizer pair) :
    (∃ walk : (pathAlternatingGraph rotation minimal family pair.pathSection
          minimizer receipt.index.castSucc).Walk
            (pathBoundaryVertex family receipt.left)
            (pathBoundaryVertex family receipt.right),
        ∃ edge ∈ walk.edges, edge ∈ overlapFootprintValues
          (family.data receipt.index.castSucc)
          (family.data receipt.index.succ)) ∨
      (∃ walk : (pathAlternatingGraph rotation minimal family pair.pathSection
          minimizer receipt.index.succ).Walk
            (pathBoundaryVertex family receipt.left)
            (pathBoundaryVertex family receipt.right),
        ∃ edge ∈ walk.edges, edge ∈ overlapFootprintValues
          (family.data receipt.index.castSucc)
          (family.data receipt.index.succ)) := by
  exact SimpleGraph.exists_walk_hitting_of_deleteEdges_eq_of_reachability_differs
    (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
      receipt.index.castSucc)
    (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
      receipt.index.succ)
    (overlapFootprintValues
      (family.data receipt.index.castSucc)
      (family.data receipt.index.succ))
    (receipt.deleteLocalFootprint_eq
      rotation minimal family minimizer pair)
    receipt.reachabilityDiffers

/-- A connectivity transition cannot be witnessed by a path in the common
outside-footprint graph.  Hence every changed component relation genuinely
uses the finite exceptional patch. -/
theorem ConnectivityTransitionWitness.not_reachable_deleteFootprint
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (witness : ConnectivityTransitionWitness
      rotation minimal family minimizer pair) :
    ¬ ((pathAlternatingGraph rotation minimal family pair.pathSection minimizer
          pair.first).deleteEdges
        (pathFootprintValues family : Set (Sym2 V))).Reachable
          (pathBoundaryVertex family witness.left)
          (pathBoundaryVertex family witness.right) := by
  intro hcommon
  let firstGraph := pathAlternatingGraph rotation minimal family
    pair.pathSection minimizer pair.first
  let secondGraph := pathAlternatingGraph rotation minimal family
    pair.pathSection minimizer pair.second
  have hfirst : firstGraph.Reachable
      (pathBoundaryVertex family witness.left)
      (pathBoundaryVertex family witness.right) :=
    hcommon.mono (firstGraph.deleteEdges_le
      (pathFootprintValues family : Set (Sym2 V)))
  have hdeletedEq : firstGraph.deleteEdges
        (pathFootprintValues family : Set (Sym2 V)) =
      secondGraph.deleteEdges
        (pathFootprintValues family : Set (Sym2 V)) := by
    simpa only [firstGraph, secondGraph] using
      deleteFootprint_eq rotation minimal family minimizer pair
  have hsecondDeleted : (secondGraph.deleteEdges
      (pathFootprintValues family : Set (Sym2 V))).Reachable
        (pathBoundaryVertex family witness.left)
        (pathBoundaryVertex family witness.right) := by
    rw [← hdeletedEq]
    exact hcommon
  have hsecond : secondGraph.Reachable
      (pathBoundaryVertex family witness.left)
      (pathBoundaryVertex family witness.right) :=
    hsecondDeleted.mono (secondGraph.deleteEdges_le
      (pathFootprintValues family : Set (Sym2 V)))
  exact witness.reachabilityDiffers ⟨fun _ => hsecond, fun _ => hfirst⟩

set_option maxHeartbeats 800000 in
/-- The exact finite boundary closures at the two endpoint coordinates differ
on the transition witness.  This is the finite-state form of the remaining
component synchronization obstruction. -/
theorem ConnectivityTransitionWitness.boundaryClosureDiffers
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (witness : ConnectivityTransitionWitness
      rotation minimal family minimizer pair) :
    let left : PathBoundary family :=
      ⟨pathBoundaryVertex family witness.left,
        pathBoundaryVertex_mem family witness.left⟩
    let right : PathBoundary family :=
      ⟨pathBoundaryVertex family witness.right,
        pathBoundaryVertex_mem family witness.right⟩
    ¬ (Relation.ReflTransGen
          (pathBoundaryStep rotation minimal family pair.pathSection minimizer
            pair.first) left right ↔
        Relation.ReflTransGen
          (pathBoundaryStep rotation minimal family pair.pathSection minimizer
            pair.second) left right) := by
  dsimp only
  let firstGraph := pathAlternatingGraph rotation minimal family
    pair.pathSection minimizer pair.first
  let secondGraph := pathAlternatingGraph rotation minimal family
    pair.pathSection minimizer pair.second
  have hfirst := pathAlternatingGraph_reachable_iff_boundaryClosure
    rotation minimal family pair.pathSection minimizer pair.first
      (pathBoundaryVertex_mem family witness.left)
      (pathBoundaryVertex_mem family witness.right)
  have hsecond := pathAlternatingGraph_reachable_iff_boundaryClosure
    rotation minimal family pair.pathSection minimizer pair.second
      (pathBoundaryVertex_mem family witness.left)
      (pathBoundaryVertex_mem family witness.right)
  intro hclosure
  apply witness.reachabilityDiffers
  exact hfirst.trans (hclosure.trans hsecond.symm)

/-- In the nonsynchronized case, one endpoint graph has a connecting walk
which necessarily traverses a named edge of the finite path footprint. -/
theorem ConnectivityTransitionWitness.exists_walk_hitting_pathFootprint
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (witness : ConnectivityTransitionWitness
      rotation minimal family minimizer pair) :
    (∃ walk : (pathAlternatingGraph rotation minimal family pair.pathSection
          minimizer pair.first).Walk
            (pathBoundaryVertex family witness.left)
            (pathBoundaryVertex family witness.right),
        ∃ edge ∈ walk.edges, edge ∈ pathFootprintValues family) ∨
      (∃ walk : (pathAlternatingGraph rotation minimal family pair.pathSection
          minimizer pair.second).Walk
            (pathBoundaryVertex family witness.left)
            (pathBoundaryVertex family witness.right),
        ∃ edge ∈ walk.edges, edge ∈ pathFootprintValues family) := by
  classical
  let firstGraph := pathAlternatingGraph rotation minimal family
    pair.pathSection minimizer pair.first
  let secondGraph := pathAlternatingGraph rotation minimal family
    pair.pathSection minimizer pair.second
  have hdeletedEq : firstGraph.deleteEdges
        (pathFootprintValues family : Set (Sym2 V)) =
      secondGraph.deleteEdges
        (pathFootprintValues family : Set (Sym2 V)) := by
    simpa only [firstGraph, secondGraph] using
      deleteFootprint_eq rotation minimal family minimizer pair
  by_cases hfirst : firstGraph.Reachable
      (pathBoundaryVertex family witness.left)
      (pathBoundaryVertex family witness.right)
  · have hnotSecond : ¬ secondGraph.Reachable
        (pathBoundaryVertex family witness.left)
        (pathBoundaryVertex family witness.right) := by
      intro hsecond
      exact witness.reachabilityDiffers
        ⟨fun _ => hsecond, fun _ => hfirst⟩
    rcases hfirst with ⟨walk⟩
    rcases walk.exists_edgeDisagreement_of_not_reachable hnotSecond with
      ⟨edge, hedgeWalk, hedgeDifference⟩
    left
    refine ⟨walk, edge, hedgeWalk, ?_⟩
    exact SimpleGraph.edgeDisagreementFinset_subset_of_deleteEdges_eq
      firstGraph secondGraph (pathFootprintValues family) hdeletedEq
        hedgeDifference
  · have hsecond : secondGraph.Reachable
        (pathBoundaryVertex family witness.left)
        (pathBoundaryVertex family witness.right) := by
      by_contra hnotSecond
      apply witness.reachabilityDiffers
      exact ⟨fun h => False.elim (hfirst h),
        fun h => False.elim (hnotSecond h)⟩
    rcases hsecond with ⟨walk⟩
    rcases walk.exists_edgeDisagreement_of_not_reachable hfirst with
      ⟨edge, hedgeWalk, hedgeDifference⟩
    right
    refine ⟨walk, edge, hedgeWalk, ?_⟩
    exact SimpleGraph.edgeDisagreementFinset_subset_of_deleteEdges_eq
      secondGraph firstGraph (pathFootprintValues family) hdeletedEq.symm
        hedgeDifference

end

end CoherentResidualReturnConnectivity

end Mettapedia.GraphTheory.FourColor.Compositional
