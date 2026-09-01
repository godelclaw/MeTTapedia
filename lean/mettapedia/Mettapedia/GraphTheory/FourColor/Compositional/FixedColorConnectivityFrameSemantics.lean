import Mettapedia.GraphTheory.FourColor.Compositional.FixedColorConnectivityFrame

/-!
# Semantics of equal fixed-colour connectivity frames

An equality of finite frame codes lives on the common ninety-slot carrier.
This file eliminates that equality into the two facts needed by a later
physical comparison: the same incoming/outgoing arm orientation and the same
ambient fixed-colour reachability relation under the slot labelling.

No ambient vertex identification or colouring-support transport is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace FixedColorConnectivityFrameSemantics

open CoherentResidualReturnConnectivity
open CoherentResidualReturnSweep
open DeletionAtlasPath
open DeletionPathConnectivityState
open AlternatingSiteGeometry
open FixedColorConnectivityFrame
open FixedColorConnectivityPigeonhole
open FixedColorConnectivityTransition
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open MeshJunctionAlternatingGeometry
open SimpleGraph
open SimpleGraphDartRotation
open SparseNoncentralMeshAtlas

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a : Nat}

/-- The Boolean frame bit is exactly the choice of the incoming row arm. -/
theorem selectedIncomingArmBit_eq_true_iff_selectedRowStep_eq_incoming
    (rotation : Data G)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (row : Fin a) (index : Fin 9) :
    selectedIncomingArmBit rotation ordered minimizer row index = true ↔
      selectedRowStep rotation ordered minimizer row index =
        incomingRowStep rotation ordered row (sparseJunctionColumn index) := by
  by_cases hcentral : minimizer.pairing.partner
        (globalFirstVertex rotation ordered
          (outgoingGlobalStep rotation ordered row
            (sparseJunctionColumn index))) =
      globalSecondVertex rotation ordered
        (outgoingGlobalStep rotation ordered row
          (sparseJunctionColumn index))
  · simp [selectedIncomingArmBit, selectedRowStep, hcentral]
  · simp [selectedIncomingArmBit, selectedRowStep, hcentral,
      (incomingRowStep_ne_outgoingRowStep rotation ordered row
        (sparseJunctionColumn index)).symm]

/-- The semantic content of two equal transition frames.  The two ambient
graphs may have different physical vertices; the fixed slot carrier provides
their common observation coordinates. -/
structure FixedColorTransitionSemanticAgreement
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (firstRow secondRow : Fin a)
    (first : FixedColorRowTransitionReceipt rotation minimal ordered
      minimizer firstRow)
    (second : FixedColorRowTransitionReceipt rotation minimal ordered
      minimizer secondRow) : Prop where
  transitionCode :
    first.toCode rotation minimal ordered minimizer firstRow =
      second.toCode rotation minimal ordered minimizer secondRow
  beforeUsesIncoming :
    (selectedRowStep rotation ordered minimizer firstRow
          first.transition.index.castSucc =
        incomingRowStep rotation ordered firstRow
          (sparseJunctionColumn first.transition.index.castSucc)) ↔
      selectedRowStep rotation ordered minimizer secondRow
          second.transition.index.castSucc =
        incomingRowStep rotation ordered secondRow
          (sparseJunctionColumn second.transition.index.castSucc)
  afterUsesIncoming :
    (selectedRowStep rotation ordered minimizer firstRow
          first.transition.index.succ =
        incomingRowStep rotation ordered firstRow
          (sparseJunctionColumn first.transition.index.succ)) ↔
      selectedRowStep rotation ordered minimizer secondRow
          second.transition.index.succ =
        incomingRowStep rotation ordered secondRow
          (sparseJunctionColumn second.transition.index.succ)
  beforeReachability : ∀ left right : PathBoundarySlot,
    (pathFixedColorAlternatingGraph rotation minimal
          (coloringFamily rotation minimal ordered minimizer firstRow)
          first.pair.pathSection minimizer
          (sweepColour rotation minimal
            (coloringFamily rotation minimal ordered minimizer firstRow)
            minimizer first.pair)
          first.transition.index.castSucc).Reachable
        (pathBoundaryVertex
          (coloringFamily rotation minimal ordered minimizer firstRow) left)
        (pathBoundaryVertex
          (coloringFamily rotation minimal ordered minimizer firstRow) right) ↔
      (pathFixedColorAlternatingGraph rotation minimal
          (coloringFamily rotation minimal ordered minimizer secondRow)
          second.pair.pathSection minimizer
          (sweepColour rotation minimal
            (coloringFamily rotation minimal ordered minimizer secondRow)
            minimizer second.pair)
          second.transition.index.castSucc).Reachable
        (pathBoundaryVertex
          (coloringFamily rotation minimal ordered minimizer secondRow) left)
        (pathBoundaryVertex
          (coloringFamily rotation minimal ordered minimizer secondRow) right)
  afterReachability : ∀ left right : PathBoundarySlot,
    (pathFixedColorAlternatingGraph rotation minimal
          (coloringFamily rotation minimal ordered minimizer firstRow)
          first.pair.pathSection minimizer
          (sweepColour rotation minimal
            (coloringFamily rotation minimal ordered minimizer firstRow)
            minimizer first.pair)
          first.transition.index.succ).Reachable
        (pathBoundaryVertex
          (coloringFamily rotation minimal ordered minimizer firstRow) left)
        (pathBoundaryVertex
          (coloringFamily rotation minimal ordered minimizer firstRow) right) ↔
      (pathFixedColorAlternatingGraph rotation minimal
          (coloringFamily rotation minimal ordered minimizer secondRow)
          second.pair.pathSection minimizer
          (sweepColour rotation minimal
            (coloringFamily rotation minimal ordered minimizer secondRow)
            minimizer second.pair)
          second.transition.index.succ).Reachable
        (pathBoundaryVertex
          (coloringFamily rotation minimal ordered minimizer secondRow) left)
        (pathBoundaryVertex
          (coloringFamily rotation minimal ordered minimizer secondRow) right)

/-- Equal finite frames give the full semantic agreement on their common
labelled boundary carrier. -/
theorem semanticAgreement_of_fixedColorRowTransitionFrameCode_eq
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (firstRow secondRow : Fin a)
    (first : FixedColorRowTransitionReceipt rotation minimal ordered
      minimizer firstRow)
    (second : FixedColorRowTransitionReceipt rotation minimal ordered
      minimizer secondRow)
    (hframe :
      fixedColorRowTransitionFrameCode rotation minimal ordered minimizer
          firstRow first =
        fixedColorRowTransitionFrameCode rotation minimal ordered minimizer
          secondRow second) :
    FixedColorTransitionSemanticAgreement rotation minimal ordered minimizer
      firstRow secondRow first second := by
  have hcomponents :=
    (fixedColorRowTransitionFrameCode_eq_iff rotation minimal ordered minimizer
      firstRow secondRow first second).1 hframe
  refine
    { transitionCode := hcomponents.1
      beforeUsesIncoming := ?_
      afterUsesIncoming := ?_
      beforeReachability := ?_
      afterReachability := ?_ }
  · rw [← selectedIncomingArmBit_eq_true_iff_selectedRowStep_eq_incoming,
      ← selectedIncomingArmBit_eq_true_iff_selectedRowStep_eq_incoming,
      hcomponents.2.1]
  · rw [← selectedIncomingArmBit_eq_true_iff_selectedRowStep_eq_incoming,
      ← selectedIncomingArmBit_eq_true_iff_selectedRowStep_eq_incoming,
      hcomponents.2.2.1]
  · intro left right
    rw [← fixedConnectivityStateAt_reachable_iff rotation minimal
        (coloringFamily rotation minimal ordered minimizer firstRow) minimizer
        first.pair first.transition.index.castSucc left right,
      hcomponents.2.2.2.1,
      fixedConnectivityStateAt_reachable_iff rotation minimal
        (coloringFamily rotation minimal ordered minimizer secondRow) minimizer
        second.pair second.transition.index.castSucc left right]
  · intro left right
    rw [← fixedConnectivityStateAt_reachable_iff rotation minimal
        (coloringFamily rotation minimal ordered minimizer firstRow) minimizer
        first.pair first.transition.index.succ left right,
      hcomponents.2.2.2.2,
      fixedConnectivityStateAt_reachable_iff rotation minimal
        (coloringFamily rotation minimal ordered minimizer secondRow) minimizer
        second.pair second.transition.index.succ left right]

end

end FixedColorConnectivityFrameSemantics

end Mettapedia.GraphTheory.FourColor.Compositional
