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
open CoherentResidualReturnSweep
open DeletionAtlasPath
open DeletionPathConnectivity
open DeletionPathConnectivityState
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24ResidualDefectDescent
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.Logic
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
    have hnotAll : ¬ ∀ left right : PathBoundarySlot,
        (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
            pair.first).Reachable
              (pathBoundaryVertex family left) (pathBoundaryVertex family right) ↔
          (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
            pair.second).Reachable
              (pathBoundaryVertex family left)
              (pathBoundaryVertex family right) := by
      intro hall
      apply hsynchronized
      exact (pathConnectivityState_eq_iff
        (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
          pair.first)
        (pathAlternatingGraph rotation minimal family pair.pathSection minimizer
          pair.second) family).2 hall
    push Not at hnotAll
    rcases hnotAll with ⟨left, right, hdiffers⟩
    refine ⟨⟨left, right, ?_⟩⟩
    rcases hdiffers with ⟨hfirst, hnotSecond⟩ | ⟨hnotFirst, hsecond⟩
    · intro heq
      exact hnotSecond (heq.mp hfirst)
    · intro heq
      exact hnotFirst (heq.mpr hsecond)

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
