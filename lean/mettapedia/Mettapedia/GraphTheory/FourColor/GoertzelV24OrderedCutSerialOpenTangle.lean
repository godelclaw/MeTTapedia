import Mettapedia.GraphTheory.FourColor.GoertzelV24SerialOpenTangleComposition
import Mettapedia.GraphTheory.FourColor.GoertzelV24SpliceUnification

/-!
# Serial open tangles from ordered corridor cuts

The compositional source orders every corridor interface by its transversal
position.  This file turns the already certified two-cut side data into a
literal two-sided open tangle and uses that same source order to glue two
successive pieces.  The matching is therefore not an arbitrary equivalence
between finite boundary carriers: both carriers are identified with their
common `Fin n` of source positions.

This is generic ordered-cut theory.  It introduces no configuration
catalogue or covering-style reduction, and it makes no claim that a local
serial composite is already the global annular splice.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SpliceUnification.OrderedCutSidesData

open GoertzelV24OpenTangleComposition
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RotationCutDartDecomposition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
  {RS : RotationSystem V E}
  {n leftTerminalCount leftFaceFragmentCount : Nat}
  {rightTerminalCount rightFaceFragmentCount : Nat}

noncomputable section

/-- Read certified left/right cut sides as a literal two-sided open tangle.
The two boundary carriers are exactly the ordered cut interfaces supplied by
the source geometry. -/
noncomputable def toTwoSidedOpenTangle
    (data : OrderedCutSidesData RS n leftTerminalCount
      leftFaceFragmentCount) :
    TwoSidedOpenTangleData
      { vertex : V // data.keep vertex }
      (InternalDart RS data.keep)
      (BoundaryDartOn RS data.keep (orderedCut data.left.crossingEdge))
      (BoundaryDartOn RS data.keep (orderedCut data.right.crossingEdge)) :=
  let outer : RetainedDart RS data.keep :=
    ⟨RS.outer, data.outer_kept⟩
  (OpenTangleData.ofVertexSide RS data.keep outer).splitBoundary
    (boundaryDartEquivCutSum RS data.keep
      (orderedCut data.left.crossingEdge)
      (orderedCut data.right.crossingEdge)
      data.cover data.disjoint)

/-- Match the output cut of one source piece to the input cut of the next by
their common ordered transversal position.  The retained vertex predicates
may differ; only the source port order is shared. -/
noncomputable def rightToLeftBoundaryMatching
    (left : OrderedCutSidesData RS n leftTerminalCount
      leftFaceFragmentCount)
    (right : OrderedCutSidesData RS n rightTerminalCount
      rightFaceFragmentCount) :
    BoundaryDartOn RS left.keep (orderedCut left.right.crossingEdge) ≃
      BoundaryDartOn RS right.keep (orderedCut right.left.crossingEdge) :=
  (orderedBoundaryDartEquiv RS left.keep left.right.crossingEdge
    left.rightCrosses left.rightInjective).symm.trans
      (orderedBoundaryDartEquiv RS right.keep right.left.crossingEdge
        right.leftCrosses right.leftInjective)

/-- The serial matching sends the output dart at a source position to the
input dart at that exact same source position. -/
@[simp]
theorem rightToLeftBoundaryMatching_orderedBoundaryDart
    (left : OrderedCutSidesData RS n leftTerminalCount
      leftFaceFragmentCount)
    (right : OrderedCutSidesData RS n rightTerminalCount
      rightFaceFragmentCount)
    (step : Fin n) :
    rightToLeftBoundaryMatching left right
        (orderedBoundaryDart RS left.keep left.right.crossingEdge
          left.rightCrosses step) =
      orderedBoundaryDart RS right.keep right.left.crossingEdge
        right.leftCrosses step := by
  let leftEquiv := orderedBoundaryDartEquiv RS left.keep
    left.right.crossingEdge left.rightCrosses left.rightInjective
  let rightEquiv := orderedBoundaryDartEquiv RS right.keep
    right.left.crossingEdge right.leftCrosses right.leftInjective
  change rightEquiv (leftEquiv.symm (leftEquiv step)) = rightEquiv step
  rw [leftEquiv.symm_apply_apply]

/-- The inverse serial matching also preserves the common source position. -/
@[simp]
theorem rightToLeftBoundaryMatching_symm_orderedBoundaryDart
    (left : OrderedCutSidesData RS n leftTerminalCount
      leftFaceFragmentCount)
    (right : OrderedCutSidesData RS n rightTerminalCount
      rightFaceFragmentCount)
    (step : Fin n) :
    (rightToLeftBoundaryMatching left right).symm
        (orderedBoundaryDart RS right.keep right.left.crossingEdge
          right.leftCrosses step) =
      orderedBoundaryDart RS left.keep left.right.crossingEdge
        left.rightCrosses step := by
  apply (rightToLeftBoundaryMatching left right).injective
  rw [Equiv.apply_symm_apply,
    rightToLeftBoundaryMatching_orderedBoundaryDart]

/-- Serially compose two certified ordered-cut pieces using the source port
order.  The result remains an open tangle: the first input and last output
interfaces are still exposed. -/
noncomputable def serialCompose
    (left : OrderedCutSidesData RS n leftTerminalCount
      leftFaceFragmentCount)
    (right : OrderedCutSidesData RS n rightTerminalCount
      rightFaceFragmentCount) :=
  TwoSidedOpenTangleData.serialCompose
    left.toTwoSidedOpenTangle right.toTwoSidedOpenTangle
    (rightToLeftBoundaryMatching left right)

end

end GoertzelV24SpliceUnification.OrderedCutSidesData

end Mettapedia.GraphTheory.FourColor
