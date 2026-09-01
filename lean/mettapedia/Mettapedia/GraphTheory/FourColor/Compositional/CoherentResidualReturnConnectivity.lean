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
      pathAlternatingGraphs_deleteFootprint_eq rotation minimal family
        pair.pathSection minimizer pair.first pair.second pair.absentColor_eq
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

end

end CoherentResidualReturnConnectivity

end Mettapedia.GraphTheory.FourColor.Compositional
