import Mettapedia.GraphTheory.FourColor.Compositional.FixedColorConnectivityPigeonhole

/-!
# Geometrically framed fixed-colour connectivity transitions

The small transition code records which reachability query changes, but a
physical comparison also needs the local row-arm choices and the complete
connectivity states on both sides of the change.  This file adds precisely
those finite observables.

The resulting framed code is still only semantic boundary data.  Equality of
framed codes does not identify ambient vertices or assert that the slab
between two rows is replaceable.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace FixedColorConnectivityFrame

open AlternatingSiteGeometry
open CoherentResidualReturnConnectivity
open CoherentResidualReturnSweep
open DeletionAtlasPath
open DeletionPathConnectivityState
open FixedColorConnectivityPigeonhole
open FixedColorConnectivityTransition
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

/-- The bit used by the sparse atlas to choose the incoming row arm.  It is
true exactly when the outgoing arm is already used by the fixed residual
matching. -/
def selectedIncomingArmBit
    (rotation : Data G)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (row : Fin a) (index : Fin 9) : Bool :=
  decide (minimizer.pairing.partner
      (globalFirstVertex rotation ordered
        (outgoingGlobalStep rotation ordered row
          (sparseJunctionColumn index))) =
    globalSecondVertex rotation ordered
      (outgoingGlobalStep rotation ordered row
        (sparseJunctionColumn index)))

theorem selectedIncomingArmBit_eq_true_iff
    (rotation : Data G)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (row : Fin a) (index : Fin 9) :
    selectedIncomingArmBit rotation ordered minimizer row index = true ↔
      minimizer.pairing.partner
          (globalFirstVertex rotation ordered
            (outgoingGlobalStep rotation ordered row
              (sparseJunctionColumn index))) =
        globalSecondVertex rotation ordered
          (outgoingGlobalStep rotation ordered row
            (sparseJunctionColumn index)) := by
  simp [selectedIncomingArmBit]

/-- A framed transition records the small transition code, both local arm
bits, and the complete labelled boundary-connectivity states immediately
before and after the change. -/
abbrev FixedColorRowTransitionFrameCode :=
  FixedColorRowTransitionCode × Bool × Bool ×
    SimpleGraph PathBoundarySlot × SimpleGraph PathBoundarySlot

/-- Add the finite geometric frame and both full connectivity states to a row
transition receipt. -/
def fixedColorRowTransitionFrameCode
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (row : Fin a)
    (receipt : FixedColorRowTransitionReceipt rotation minimal ordered
      minimizer row) : FixedColorRowTransitionFrameCode :=
  (receipt.toCode rotation minimal ordered minimizer row,
    selectedIncomingArmBit rotation ordered minimizer row
      receipt.transition.index.castSucc,
    selectedIncomingArmBit rotation ordered minimizer row
      receipt.transition.index.succ,
    fixedConnectivityStateAt rotation minimal
      (coloringFamily rotation minimal ordered minimizer row) minimizer
      receipt.pair receipt.transition.index.castSucc,
    fixedConnectivityStateAt rotation minimal
      (coloringFamily rotation minimal ordered minimizer row) minimizer
      receipt.pair receipt.transition.index.succ)

/-- Equality of framed codes is exactly equality of the small transition,
both arm choices, and both complete boundary-connectivity states. -/
theorem fixedColorRowTransitionFrameCode_eq_iff
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (firstRow secondRow : Fin a)
    (first : FixedColorRowTransitionReceipt rotation minimal ordered
      minimizer firstRow)
    (second : FixedColorRowTransitionReceipt rotation minimal ordered
      minimizer secondRow) :
    fixedColorRowTransitionFrameCode rotation minimal ordered minimizer
        firstRow first =
      fixedColorRowTransitionFrameCode rotation minimal ordered minimizer
        secondRow second ↔
      first.toCode rotation minimal ordered minimizer firstRow =
          second.toCode rotation minimal ordered minimizer secondRow ∧
      selectedIncomingArmBit rotation ordered minimizer firstRow
          first.transition.index.castSucc =
        selectedIncomingArmBit rotation ordered minimizer secondRow
          second.transition.index.castSucc ∧
      selectedIncomingArmBit rotation ordered minimizer firstRow
          first.transition.index.succ =
        selectedIncomingArmBit rotation ordered minimizer secondRow
          second.transition.index.succ ∧
      fixedConnectivityStateAt rotation minimal
          (coloringFamily rotation minimal ordered minimizer firstRow) minimizer
          first.pair first.transition.index.castSucc =
        fixedConnectivityStateAt rotation minimal
          (coloringFamily rotation minimal ordered minimizer secondRow) minimizer
          second.pair second.transition.index.castSucc ∧
      fixedConnectivityStateAt rotation minimal
          (coloringFamily rotation minimal ordered minimizer firstRow) minimizer
          first.pair first.transition.index.succ =
        fixedConnectivityStateAt rotation minimal
          (coloringFamily rotation minimal ordered minimizer secondRow) minimizer
          second.pair second.transition.index.succ := by
  simp only [fixedColorRowTransitionFrameCode, Prod.mk.injEq]

/-- If there are more rows than framed transition states and every row reaches
the local transition alternative, two distinct rows have equal framed codes.

The threshold remains symbolic here.  Expanding the adjacency-matrix cardinal
of a complete boundary-connectivity state is mathematically unnecessary and
would manufacture a huge closed numeral in the kernel term. -/
theorem exists_distinct_rows_with_equal_fixedColorTransitionFrameCode
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (hrows : Nat.card FixedColorRowTransitionFrameCode < a)
    (supply : ∀ row : Fin a,
      Nonempty (FixedColorRowTransitionReceipt rotation minimal ordered
        minimizer row)) :
    ∃ (first second : Fin a)
        (firstReceipt : FixedColorRowTransitionReceipt rotation minimal
          ordered minimizer first)
        (secondReceipt : FixedColorRowTransitionReceipt rotation minimal
          ordered minimizer second),
      first ≠ second ∧
        fixedColorRowTransitionFrameCode rotation minimal ordered minimizer
            first firstReceipt =
          fixedColorRowTransitionFrameCode rotation minimal ordered minimizer
            second secondReceipt := by
  letI : Fintype FixedColorRowTransitionFrameCode := Fintype.ofFinite _
  let receipt : ∀ row : Fin a,
      FixedColorRowTransitionReceipt rotation minimal ordered minimizer row :=
    fun row => Classical.choice (supply row)
  let code : Fin a → FixedColorRowTransitionFrameCode := fun row =>
    fixedColorRowTransitionFrameCode rotation minimal ordered minimizer row
      (receipt row)
  have hcard : Fintype.card FixedColorRowTransitionFrameCode <
      Fintype.card (Fin a) := by
    simpa only [Fintype.card_eq_nat_card, Nat.card_fin] using hrows
  obtain ⟨first, second, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt code hcard
  exact ⟨first, second, receipt first, receipt second, hne, heq⟩

/-- Consumer-facing framed mesh alternative. -/
theorem branchingOrBoundary_or_synchronized_or_repeatedFixedColorTransitionFrame
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G)
    (hrows : Nat.card FixedColorRowTransitionFrameCode < a) :
    (∃ (row : Fin a) (assignment : TaitAssignment
        (coloringFamily rotation minimal ordered minimizer row)),
      HasBranchingOrBoundary
        (coloringFamily rotation minimal ordered minimizer row) assignment) ∨
      (∃ (row : Fin a)
          (pair : CoherentGeometricSweepPairReceipt rotation minimal
            (coloringFamily rotation minimal ordered minimizer row) minimizer),
        ConnectivitySynchronized rotation minimal
          (coloringFamily rotation minimal ordered minimizer row) minimizer pair) ∨
      ∃ (first second : Fin a)
          (firstReceipt : FixedColorRowTransitionReceipt rotation minimal
            ordered minimizer first)
          (secondReceipt : FixedColorRowTransitionReceipt rotation minimal
            ordered minimizer second),
        first ≠ second ∧
          fixedColorRowTransitionFrameCode rotation minimal ordered minimizer
              first firstReceipt =
            fixedColorRowTransitionFrameCode rotation minimal ordered minimizer
              second secondReceipt := by
  classical
  by_cases hhorn : ∃ (row : Fin a) (assignment : TaitAssignment
      (coloringFamily rotation minimal ordered minimizer row)),
    HasBranchingOrBoundary
      (coloringFamily rotation minimal ordered minimizer row) assignment
  · exact Or.inl hhorn
  · right
    by_cases hsynchronized : ∃ (row : Fin a)
        (pair : CoherentGeometricSweepPairReceipt rotation minimal
          (coloringFamily rotation minimal ordered minimizer row) minimizer),
      ConnectivitySynchronized rotation minimal
        (coloringFamily rotation minimal ordered minimizer row) minimizer pair
    · exact Or.inl hsynchronized
    · right
      exact exists_distinct_rows_with_equal_fixedColorTransitionFrameCode
        rotation minimal ordered minimizer hrows fun row =>
          nonempty_fixedColorRowTransitionReceipt_of_no_horn_of_no_synchronized
            rotation minimal ordered minimizer row
            (fun assignment hbranchingOrBoundary =>
              hhorn ⟨row, assignment, hbranchingOrBoundary⟩)
            (fun pair hsynchronization =>
              hsynchronized ⟨row, pair, hsynchronization⟩)

end

end FixedColorConnectivityFrame

end Mettapedia.GraphTheory.FourColor.Compositional
