import Mettapedia.GraphTheory.FourColor.Compositional.CentralAugmentedColorClass
import Mettapedia.GraphTheory.FourColor.Compositional.CoherentResidualReturnConnectivity

/-!
# Fixed-colour connectivity transitions along a coherent deletion path

The colour absent from one deletion boundary is a local completion choice; it
need not remain the chosen absent colour at intermediate path coordinates.
This file therefore follows one fixed ambient Tait colour through the whole
path.  Its total central-augmented colour-class graph is meaningful at every
coordinate and agrees with the completed matching graph wherever that colour
is locally absent.

For a coherent sweep pair, choose the common absent colour of its two selected
endpoints.  If their boundary connectivity states differ, an adjacent pair of
fixed-colour graphs already differs.  Consecutive common-core agreement makes
those graphs equal after deleting the union of their two five-edge deletion
footprints.  Thus synchronization failure has a ten-edge local witness without
an additional colour-change alternative.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace FixedColorConnectivityTransition

open CentralAugmentedColorClass
open AlternatingComponentLocalization
open AlternatingSiteGeometry
open CoherentResidualReturnConnectivity
open CoherentResidualReturnSweep
open DeletionAtlasPath
open DeletionPathConnectivity
open DeletionPathConnectivityState
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24ResidualDefectDescent
open GoertzelV24TwoEdgeCutMinimality
open Mettapedia.Logic
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype

local instance deletionRetainedFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

/-- The alternating graph of one fixed Tait colour at one deletion-path
coordinate.  Unlike the locally completed matching, it is defined at every
coordinate without an absent-colour hypothesis. -/
def pathFixedColorAlternatingGraph
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family))
    (minimizer : ResidualDefectMinimizer G)
    (colour : Fin 3) (index : Fin 9) : SimpleGraph V :=
  fixedColorAlternatingGraph minimizer.pairing (family.data index)
    (matchingState rotation minimal family pathSection index).coloring colour

/-- At a coordinate where the fixed colour is locally absent, the total
fixed-colour graph is the original completed-matching alternating graph. -/
theorem pathFixedColorAlternatingGraph_eq_pathAlternatingGraph_of_eq_absent
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family))
    (minimizer : ResidualDefectMinimizer G)
    (colour : Fin 3) (index : Fin 9)
    (hcolour : colour =
      (matchingState rotation minimal family pathSection index).absentColor) :
    pathFixedColorAlternatingGraph rotation minimal family pathSection
        minimizer colour index =
      pathAlternatingGraph rotation minimal family pathSection minimizer
        index := by
  subst colour
  let state := matchingState rotation minimal family pathSection index
  let hcubic :=
    ResidualSiteProvenance.incidentEdgeFinset_card_eq_three rotation minimal
  unfold pathFixedColorAlternatingGraph pathAlternatingGraph
  change fixedColorAlternatingGraph minimizer.pairing (family.data index)
      state.coloring state.absentColor =
    GoertzelV24AlternatingMatchingComponent.alternatingGraph minimizer.pairing
      (state.pairing hcubic)
  unfold fixedColorAlternatingGraph
  rw [centralAugmentedColorClassGraph_eq_pairingGraph
    (family.data index) hcubic state.coloring state.isTait state.absentColor
      state.absentAtBoundary]
  rfl

/-- The one colour followed through a coherent sweep pair: the common absent
colour at its two selected endpoints. -/
def sweepColour
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) : Fin 3 :=
  (matchingState rotation minimal family pair.pathSection
    pair.first).absentColor

/-- The fixed finite boundary-connectivity state obtained by following the
selected endpoint colour through every coordinate. -/
def fixedConnectivityStateAt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (index : Fin 9) : SimpleGraph PathBoundarySlot :=
  pathConnectivityState
    (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
      minimizer (sweepColour rotation minimal family minimizer pair) index)
    family

/-- The fixed state is semantically exact: reachability of two labelled slots
is precisely ambient reachability of the physical vertices that they name in
the fixed-colour graph. -/
theorem fixedConnectivityStateAt_reachable_iff
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (index : Fin 9) (left right : PathBoundarySlot) :
    (fixedConnectivityStateAt rotation minimal family minimizer pair index).Reachable
        left right ↔
      (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
          minimizer (sweepColour rotation minimal family minimizer pair)
          index).Reachable
        (pathBoundaryVertex family left) (pathBoundaryVertex family right) := by
  exact pathConnectivityState_reachable_iff _ _ _ _

/-- At the first selected endpoint, the fixed-colour and original component
states coincide. -/
theorem fixedConnectivityStateAt_first
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) :
    fixedConnectivityStateAt rotation minimal family minimizer pair pair.first =
      connectivityStateAt rotation minimal family minimizer pair pair.first := by
  unfold fixedConnectivityStateAt connectivityStateAt
  rw [pathFixedColorAlternatingGraph_eq_pathAlternatingGraph_of_eq_absent]
  rfl

/-- At the second selected endpoint, endpoint colour coherence identifies the
fixed-colour and original component states. -/
theorem fixedConnectivityStateAt_second
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) :
    fixedConnectivityStateAt rotation minimal family minimizer pair pair.second =
      connectivityStateAt rotation minimal family minimizer pair pair.second := by
  unfold fixedConnectivityStateAt connectivityStateAt
  rw [pathFixedColorAlternatingGraph_eq_pathAlternatingGraph_of_eq_absent]
  simpa [sweepColour] using pair.absentColor_eq

/-- An adjacent connectivity change for the one fixed endpoint colour.  No
comparison of the locally chosen absent colours is part of this receipt. -/
structure FixedColorLocalConnectivityTransitionReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) where
  index : Fin 8
  left : PathBoundarySlot
  right : PathBoundarySlot
  reachabilityDiffers : ¬
    ((pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
        minimizer (sweepColour rotation minimal family minimizer pair)
        index.castSucc).Reachable
          (pathBoundaryVertex family left) (pathBoundaryVertex family right) ↔
      (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
        minimizer (sweepColour rotation minimal family minimizer pair)
        index.succ).Reachable
          (pathBoundaryVertex family left) (pathBoundaryVertex family right))

/-- Inequality of adjacent fixed-colour states exposes two exact labelled
boundary slots whose ambient reachability changes. -/
theorem exists_boundary_slots_of_fixedConnectivityStateAt_ne
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (first second : Fin 9)
    (hne : fixedConnectivityStateAt rotation minimal family minimizer pair
        first ≠
      fixedConnectivityStateAt rotation minimal family minimizer pair second) :
    ∃ left right : PathBoundarySlot, ¬
      ((pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
          minimizer (sweepColour rotation minimal family minimizer pair)
          first).Reachable
            (pathBoundaryVertex family left) (pathBoundaryVertex family right) ↔
        (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
          minimizer (sweepColour rotation minimal family minimizer pair)
          second).Reachable
            (pathBoundaryVertex family left)
            (pathBoundaryVertex family right)) := by
  classical
  have hnotAll : ¬ ∀ left right : PathBoundarySlot,
      (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
          minimizer (sweepColour rotation minimal family minimizer pair)
          first).Reachable
            (pathBoundaryVertex family left) (pathBoundaryVertex family right) ↔
        (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
          minimizer (sweepColour rotation minimal family minimizer pair)
          second).Reachable
            (pathBoundaryVertex family left)
            (pathBoundaryVertex family right) := by
    intro hall
    apply hne
    exact (pathConnectivityState_eq_iff
      (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
        minimizer (sweepColour rotation minimal family minimizer pair) first)
      (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
        minimizer (sweepColour rotation minimal family minimizer pair) second)
      family).2 hall
  by_contra hnone
  apply hnotAll
  intro left right
  by_contra hdiffers
  exact hnone ⟨left, right, hdiffers⟩

/-- Endpoint synchronization either holds, or a single adjacent step changes
connectivity for one fixed colour.  This strengthens the earlier trichotomy:
an intermediate change of locally selected absent colour is not a separate
obstruction. -/
theorem synchronized_or_fixedColorLocalTransition
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) :
    ConnectivitySynchronized rotation minimal family minimizer pair ∨
      Nonempty (FixedColorLocalConnectivityTransitionReceipt
        rotation minimal family minimizer pair) := by
  classical
  by_cases hsynchronized :
      ConnectivitySynchronized rotation minimal family minimizer pair
  · exact Or.inl hsynchronized
  · right
    have hfixedEndpoints :
        fixedConnectivityStateAt rotation minimal family minimizer pair
            pair.first ≠
          fixedConnectivityStateAt rotation minimal family minimizer pair
            pair.second := by
      intro heq
      apply hsynchronized
      unfold ConnectivitySynchronized
      rw [← fixedConnectivityStateAt_first rotation minimal family minimizer
        pair, ← fixedConnectivityStateAt_second rotation minimal family
        minimizer pair]
      exact heq
    rcases PathConstraint.exists_adjacent_ne_of_ne
        (fun index : Fin 9 ↦
          fixedConnectivityStateAt rotation minimal family minimizer pair index)
        hfixedEndpoints with ⟨index, hstate⟩
    rcases exists_boundary_slots_of_fixedConnectivityStateAt_ne rotation
        minimal family minimizer pair index.castSucc index.succ hstate with
      ⟨left, right, hdiffers⟩
    exact ⟨⟨index, left, right, hdiffers⟩⟩

/-- Consecutive fixed-colour graphs become literally equal after deleting the
union of their two local five-edge footprints. -/
theorem FixedColorLocalConnectivityTransitionReceipt.deleteLocalFootprint_eq
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (receipt : FixedColorLocalConnectivityTransitionReceipt
      rotation minimal family minimizer pair) :
    (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
        minimizer (sweepColour rotation minimal family minimizer pair)
        receipt.index.castSucc).deleteEdges
          (overlapFootprintValues
            (family.data receipt.index.castSucc)
            (family.data receipt.index.succ) : Set (Sym2 V)) =
      (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
        minimizer (sweepColour rotation minimal family minimizer pair)
        receipt.index.succ).deleteEdges
          (overlapFootprintValues
            (family.data receipt.index.castSucc)
            (family.data receipt.index.succ) : Set (Sym2 V)) := by
  simpa only [pathFixedColorAlternatingGraph] using
    (fixedColorAlternatingGraphs_delete_overlapFootprints_eq
      minimizer.pairing minimizer.supported
      (family.data receipt.index.castSucc)
      (family.data receipt.index.succ)
      (matchingState rotation minimal family pair.pathSection
        receipt.index.castSucc).coloring
      (matchingState rotation minimal family pair.pathSection
        receipt.index.succ).coloring
      (pair.pathSection.compatible receipt.index).2
      (sweepColour rotation minimal family minimizer pair))

/-- The exceptional carrier of a fixed-colour local transition contains at
most ten ambient edge values. -/
theorem FixedColorLocalConnectivityTransitionReceipt.card_localFootprint_le
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (receipt : FixedColorLocalConnectivityTransitionReceipt
      rotation minimal family minimizer pair) :
    (overlapFootprintValues
      (family.data receipt.index.castSucc)
      (family.data receipt.index.succ)).card ≤ 10 :=
  card_overlapFootprintValues_le _ _

/-- The changed boundary vertices are disconnected in the graph common to the
two adjacent fixed-colour states after deleting their local footprint. -/
theorem FixedColorLocalConnectivityTransitionReceipt.not_reachable_deleteLocalFootprint
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (receipt : FixedColorLocalConnectivityTransitionReceipt
      rotation minimal family minimizer pair) :
    ¬ ((pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
          minimizer (sweepColour rotation minimal family minimizer pair)
          receipt.index.castSucc).deleteEdges
        (overlapFootprintValues
          (family.data receipt.index.castSucc)
          (family.data receipt.index.succ) : Set (Sym2 V))).Reachable
      (pathBoundaryVertex family receipt.left)
      (pathBoundaryVertex family receipt.right) := by
  exact SimpleGraph.not_reachable_deleteEdges_of_reachability_differs
    (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
      minimizer (sweepColour rotation minimal family minimizer pair)
      receipt.index.castSucc)
    (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
      minimizer (sweepColour rotation minimal family minimizer pair)
      receipt.index.succ)
    (overlapFootprintValues
      (family.data receipt.index.castSucc)
      (family.data receipt.index.succ))
    (receipt.deleteLocalFootprint_eq rotation minimal family minimizer pair)
    receipt.reachabilityDiffers

/-- One adjacent fixed-colour graph contains a connecting walk that traverses
one of the at most ten local footprint edges. -/
theorem FixedColorLocalConnectivityTransitionReceipt.exists_walk_hitting_localFootprint
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer)
    (receipt : FixedColorLocalConnectivityTransitionReceipt
      rotation minimal family minimizer pair) :
    (∃ walk : (pathFixedColorAlternatingGraph rotation minimal family
          pair.pathSection minimizer
          (sweepColour rotation minimal family minimizer pair)
          receipt.index.castSucc).Walk
            (pathBoundaryVertex family receipt.left)
            (pathBoundaryVertex family receipt.right),
        ∃ edge ∈ walk.edges, edge ∈ overlapFootprintValues
          (family.data receipt.index.castSucc)
          (family.data receipt.index.succ)) ∨
      (∃ walk : (pathFixedColorAlternatingGraph rotation minimal family
          pair.pathSection minimizer
          (sweepColour rotation minimal family minimizer pair)
          receipt.index.succ).Walk
            (pathBoundaryVertex family receipt.left)
            (pathBoundaryVertex family receipt.right),
        ∃ edge ∈ walk.edges, edge ∈ overlapFootprintValues
          (family.data receipt.index.castSucc)
          (family.data receipt.index.succ)) := by
  exact SimpleGraph.exists_walk_hitting_of_deleteEdges_eq_of_reachability_differs
    (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
      minimizer (sweepColour rotation minimal family minimizer pair)
      receipt.index.castSucc)
    (pathFixedColorAlternatingGraph rotation minimal family pair.pathSection
      minimizer (sweepColour rotation minimal family minimizer pair)
      receipt.index.succ)
    (overlapFootprintValues
      (family.data receipt.index.castSucc)
      (family.data receipt.index.succ))
    (receipt.deleteLocalFootprint_eq rotation minimal family minimizer pair)
    receipt.reachabilityDiffers

end

end FixedColorConnectivityTransition

end Mettapedia.GraphTheory.FourColor.Compositional
