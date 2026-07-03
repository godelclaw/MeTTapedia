import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoDirectClosurePrototype

namespace Mettapedia.GraphTheory.FourColor

/-!
# Shape-A direct closure bridge for remaining generated length-two fibers

This module reuses the audited eight-state shape-A closure template from
`GoertzelLemma818LengthTwoDirectClosurePrototype` for the remaining generated
`tau,tau` fibers whose parent tree has the same source-to-root shape.
-/

namespace GoertzelLemma818LengthTwoShapeABridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818LengthTwoDirectClosurePrototype

theorem directReverseSingleStepOfRow (key : List LColor) (expected : List Nat)
    (row : DirectChainParentRow)
    (hne : row.source ≠ row.parent)
    (hpair : colorPairs.contains (row.move.a, row.move.c) = true)
    (hseed : (chainEdges ttWord).contains row.move.seed = true)
    (hrow : directRowReverseValid key expected row = true) :
    chainSingleKempeStep ttWord
      (directStates row.parentLeft row.parentRight)
      (directStates row.sourceLeft row.sourceRight) = true :=
  chainSpecifiedKempeStep_implies_single ttWord
    (directStates row.parentLeft row.parentRight)
    (directStates row.sourceLeft row.sourceRight)
    row.move hpair hseed
    (directRowReverseValid_step_of_ne key expected row hne hrow)

def ttFiber69StateAt (i : Nat) : List TauState :=
  directStates (ttFiber69RowAt i).sourceLeft (ttFiber69RowAt i).sourceRight

def ttFiber69DirectStates : List (List TauState) :=
  [ ttFiber69StateAt 0, ttFiber69StateAt 1, ttFiber69StateAt 2, ttFiber69StateAt 3
  , ttFiber69StateAt 4, ttFiber69StateAt 5, ttFiber69StateAt 6, ttFiber69StateAt 7
  ]

theorem ttFiber69ReverseRow_1_ok :
    directRowReverseValid ttFiber69Key ttFiber69Expected (ttFiber69RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber69Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber69Chunk0] at h
  exact h.2

theorem ttFiber69ReverseRow_2_ok :
    directRowReverseValid ttFiber69Key ttFiber69Expected (ttFiber69RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber69Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber69Chunk1] at h
  exact h.1

theorem ttFiber69ReverseRow_3_ok :
    directRowReverseValid ttFiber69Key ttFiber69Expected (ttFiber69RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber69Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber69Chunk1] at h
  exact h.2

theorem ttFiber69ReverseRow_4_ok :
    directRowReverseValid ttFiber69Key ttFiber69Expected (ttFiber69RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber69Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber69Chunk2] at h
  exact h.1

theorem ttFiber69ReverseRow_5_ok :
    directRowReverseValid ttFiber69Key ttFiber69Expected (ttFiber69RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber69Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber69Chunk2] at h
  exact h.2

theorem ttFiber69ReverseRow_6_ok :
    directRowReverseValid ttFiber69Key ttFiber69Expected (ttFiber69RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber69Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber69Chunk3] at h
  exact h.1

theorem ttFiber69ReverseRow_7_ok :
    directRowReverseValid ttFiber69Key ttFiber69Expected (ttFiber69RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber69Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber69Chunk3] at h
  exact h.2

theorem ttFiber69DirectConnected :
    chainFiberConnected ttWord ttFiber69DirectStates = true := by
  simpa [ttFiber69DirectStates] using
    directConnected8ShapeA ttWord ttFiber69StateAt
      (by
        simpa [ttFiber69StateAt, ttFiber69RowAt, ttFiber69Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber69Key ttFiber69Expected (ttFiber69RowAt 1)
            (by decide) (by decide) (by decide) ttFiber69ReverseRow_1_ok)
      (by
        simpa [ttFiber69StateAt, ttFiber69RowAt, ttFiber69Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber69Key ttFiber69Expected (ttFiber69RowAt 2)
            (by decide) (by decide) (by decide) ttFiber69ReverseRow_2_ok)
      (by
        simpa [ttFiber69StateAt, ttFiber69RowAt, ttFiber69Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber69Key ttFiber69Expected (ttFiber69RowAt 3)
            (by decide) (by decide) (by decide) ttFiber69ReverseRow_3_ok)
      (by
        simpa [ttFiber69StateAt, ttFiber69RowAt, ttFiber69Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber69Key ttFiber69Expected (ttFiber69RowAt 4)
            (by decide) (by decide) (by decide) ttFiber69ReverseRow_4_ok)
      (by
        simpa [ttFiber69StateAt, ttFiber69RowAt, ttFiber69Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber69Key ttFiber69Expected (ttFiber69RowAt 5)
            (by decide) (by decide) (by decide) ttFiber69ReverseRow_5_ok)
      (by
        simpa [ttFiber69StateAt, ttFiber69RowAt, ttFiber69Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber69Key ttFiber69Expected (ttFiber69RowAt 6)
            (by decide) (by decide) (by decide) ttFiber69ReverseRow_6_ok)
      (by
        simpa [ttFiber69StateAt, ttFiber69RowAt, ttFiber69Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber69Key ttFiber69Expected (ttFiber69RowAt 7)
            (by decide) (by decide) (by decide) ttFiber69ReverseRow_7_ok)

def ttFiber71StateAt (i : Nat) : List TauState :=
  directStates (ttFiber71RowAt i).sourceLeft (ttFiber71RowAt i).sourceRight

def ttFiber71DirectStates : List (List TauState) :=
  [ ttFiber71StateAt 0, ttFiber71StateAt 1, ttFiber71StateAt 2, ttFiber71StateAt 3
  , ttFiber71StateAt 4, ttFiber71StateAt 5, ttFiber71StateAt 6, ttFiber71StateAt 7
  ]

theorem ttFiber71ReverseRow_1_ok :
    directRowReverseValid ttFiber71Key ttFiber71Expected (ttFiber71RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber71Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber71Chunk0] at h
  exact h.2

theorem ttFiber71ReverseRow_2_ok :
    directRowReverseValid ttFiber71Key ttFiber71Expected (ttFiber71RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber71Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber71Chunk1] at h
  exact h.1

theorem ttFiber71ReverseRow_3_ok :
    directRowReverseValid ttFiber71Key ttFiber71Expected (ttFiber71RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber71Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber71Chunk1] at h
  exact h.2

theorem ttFiber71ReverseRow_4_ok :
    directRowReverseValid ttFiber71Key ttFiber71Expected (ttFiber71RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber71Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber71Chunk2] at h
  exact h.1

theorem ttFiber71ReverseRow_5_ok :
    directRowReverseValid ttFiber71Key ttFiber71Expected (ttFiber71RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber71Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber71Chunk2] at h
  exact h.2

theorem ttFiber71ReverseRow_6_ok :
    directRowReverseValid ttFiber71Key ttFiber71Expected (ttFiber71RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber71Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber71Chunk3] at h
  exact h.1

theorem ttFiber71ReverseRow_7_ok :
    directRowReverseValid ttFiber71Key ttFiber71Expected (ttFiber71RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber71Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber71Chunk3] at h
  exact h.2

theorem ttFiber71DirectConnected :
    chainFiberConnected ttWord ttFiber71DirectStates = true := by
  simpa [ttFiber71DirectStates] using
    directConnected8ShapeA ttWord ttFiber71StateAt
      (by
        simpa [ttFiber71StateAt, ttFiber71RowAt, ttFiber71Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber71Key ttFiber71Expected (ttFiber71RowAt 1)
            (by decide) (by decide) (by decide) ttFiber71ReverseRow_1_ok)
      (by
        simpa [ttFiber71StateAt, ttFiber71RowAt, ttFiber71Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber71Key ttFiber71Expected (ttFiber71RowAt 2)
            (by decide) (by decide) (by decide) ttFiber71ReverseRow_2_ok)
      (by
        simpa [ttFiber71StateAt, ttFiber71RowAt, ttFiber71Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber71Key ttFiber71Expected (ttFiber71RowAt 3)
            (by decide) (by decide) (by decide) ttFiber71ReverseRow_3_ok)
      (by
        simpa [ttFiber71StateAt, ttFiber71RowAt, ttFiber71Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber71Key ttFiber71Expected (ttFiber71RowAt 4)
            (by decide) (by decide) (by decide) ttFiber71ReverseRow_4_ok)
      (by
        simpa [ttFiber71StateAt, ttFiber71RowAt, ttFiber71Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber71Key ttFiber71Expected (ttFiber71RowAt 5)
            (by decide) (by decide) (by decide) ttFiber71ReverseRow_5_ok)
      (by
        simpa [ttFiber71StateAt, ttFiber71RowAt, ttFiber71Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber71Key ttFiber71Expected (ttFiber71RowAt 6)
            (by decide) (by decide) (by decide) ttFiber71ReverseRow_6_ok)
      (by
        simpa [ttFiber71StateAt, ttFiber71RowAt, ttFiber71Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber71Key ttFiber71Expected (ttFiber71RowAt 7)
            (by decide) (by decide) (by decide) ttFiber71ReverseRow_7_ok)

def ttFiber75StateAt (i : Nat) : List TauState :=
  directStates (ttFiber75RowAt i).sourceLeft (ttFiber75RowAt i).sourceRight

def ttFiber75DirectStates : List (List TauState) :=
  [ ttFiber75StateAt 0, ttFiber75StateAt 1, ttFiber75StateAt 2, ttFiber75StateAt 3
  , ttFiber75StateAt 4, ttFiber75StateAt 5, ttFiber75StateAt 6, ttFiber75StateAt 7
  ]

theorem ttFiber75ReverseRow_1_ok :
    directRowReverseValid ttFiber75Key ttFiber75Expected (ttFiber75RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber75Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber75Chunk0] at h
  exact h.2

theorem ttFiber75ReverseRow_2_ok :
    directRowReverseValid ttFiber75Key ttFiber75Expected (ttFiber75RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber75Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber75Chunk1] at h
  exact h.1

theorem ttFiber75ReverseRow_3_ok :
    directRowReverseValid ttFiber75Key ttFiber75Expected (ttFiber75RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber75Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber75Chunk1] at h
  exact h.2

theorem ttFiber75ReverseRow_4_ok :
    directRowReverseValid ttFiber75Key ttFiber75Expected (ttFiber75RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber75Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber75Chunk2] at h
  exact h.1

theorem ttFiber75ReverseRow_5_ok :
    directRowReverseValid ttFiber75Key ttFiber75Expected (ttFiber75RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber75Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber75Chunk2] at h
  exact h.2

theorem ttFiber75ReverseRow_6_ok :
    directRowReverseValid ttFiber75Key ttFiber75Expected (ttFiber75RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber75Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber75Chunk3] at h
  exact h.1

theorem ttFiber75ReverseRow_7_ok :
    directRowReverseValid ttFiber75Key ttFiber75Expected (ttFiber75RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber75Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber75Chunk3] at h
  exact h.2

theorem ttFiber75DirectConnected :
    chainFiberConnected ttWord ttFiber75DirectStates = true := by
  simpa [ttFiber75DirectStates] using
    directConnected8ShapeA ttWord ttFiber75StateAt
      (by
        simpa [ttFiber75StateAt, ttFiber75RowAt, ttFiber75Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber75Key ttFiber75Expected (ttFiber75RowAt 1)
            (by decide) (by decide) (by decide) ttFiber75ReverseRow_1_ok)
      (by
        simpa [ttFiber75StateAt, ttFiber75RowAt, ttFiber75Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber75Key ttFiber75Expected (ttFiber75RowAt 2)
            (by decide) (by decide) (by decide) ttFiber75ReverseRow_2_ok)
      (by
        simpa [ttFiber75StateAt, ttFiber75RowAt, ttFiber75Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber75Key ttFiber75Expected (ttFiber75RowAt 3)
            (by decide) (by decide) (by decide) ttFiber75ReverseRow_3_ok)
      (by
        simpa [ttFiber75StateAt, ttFiber75RowAt, ttFiber75Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber75Key ttFiber75Expected (ttFiber75RowAt 4)
            (by decide) (by decide) (by decide) ttFiber75ReverseRow_4_ok)
      (by
        simpa [ttFiber75StateAt, ttFiber75RowAt, ttFiber75Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber75Key ttFiber75Expected (ttFiber75RowAt 5)
            (by decide) (by decide) (by decide) ttFiber75ReverseRow_5_ok)
      (by
        simpa [ttFiber75StateAt, ttFiber75RowAt, ttFiber75Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber75Key ttFiber75Expected (ttFiber75RowAt 6)
            (by decide) (by decide) (by decide) ttFiber75ReverseRow_6_ok)
      (by
        simpa [ttFiber75StateAt, ttFiber75RowAt, ttFiber75Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber75Key ttFiber75Expected (ttFiber75RowAt 7)
            (by decide) (by decide) (by decide) ttFiber75ReverseRow_7_ok)

def ttFiber77StateAt (i : Nat) : List TauState :=
  directStates (ttFiber77RowAt i).sourceLeft (ttFiber77RowAt i).sourceRight

def ttFiber77DirectStates : List (List TauState) :=
  [ ttFiber77StateAt 0, ttFiber77StateAt 1, ttFiber77StateAt 2, ttFiber77StateAt 3
  , ttFiber77StateAt 4, ttFiber77StateAt 5, ttFiber77StateAt 6, ttFiber77StateAt 7
  ]

theorem ttFiber77ReverseRow_1_ok :
    directRowReverseValid ttFiber77Key ttFiber77Expected (ttFiber77RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber77Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber77Chunk0] at h
  exact h.2

theorem ttFiber77ReverseRow_2_ok :
    directRowReverseValid ttFiber77Key ttFiber77Expected (ttFiber77RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber77Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber77Chunk1] at h
  exact h.1

theorem ttFiber77ReverseRow_3_ok :
    directRowReverseValid ttFiber77Key ttFiber77Expected (ttFiber77RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber77Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber77Chunk1] at h
  exact h.2

theorem ttFiber77ReverseRow_4_ok :
    directRowReverseValid ttFiber77Key ttFiber77Expected (ttFiber77RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber77Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber77Chunk2] at h
  exact h.1

theorem ttFiber77ReverseRow_5_ok :
    directRowReverseValid ttFiber77Key ttFiber77Expected (ttFiber77RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber77Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber77Chunk2] at h
  exact h.2

theorem ttFiber77ReverseRow_6_ok :
    directRowReverseValid ttFiber77Key ttFiber77Expected (ttFiber77RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber77Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber77Chunk3] at h
  exact h.1

theorem ttFiber77ReverseRow_7_ok :
    directRowReverseValid ttFiber77Key ttFiber77Expected (ttFiber77RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber77Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber77Chunk3] at h
  exact h.2

theorem ttFiber77DirectConnected :
    chainFiberConnected ttWord ttFiber77DirectStates = true := by
  simpa [ttFiber77DirectStates] using
    directConnected8ShapeA ttWord ttFiber77StateAt
      (by
        simpa [ttFiber77StateAt, ttFiber77RowAt, ttFiber77Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber77Key ttFiber77Expected (ttFiber77RowAt 1)
            (by decide) (by decide) (by decide) ttFiber77ReverseRow_1_ok)
      (by
        simpa [ttFiber77StateAt, ttFiber77RowAt, ttFiber77Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber77Key ttFiber77Expected (ttFiber77RowAt 2)
            (by decide) (by decide) (by decide) ttFiber77ReverseRow_2_ok)
      (by
        simpa [ttFiber77StateAt, ttFiber77RowAt, ttFiber77Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber77Key ttFiber77Expected (ttFiber77RowAt 3)
            (by decide) (by decide) (by decide) ttFiber77ReverseRow_3_ok)
      (by
        simpa [ttFiber77StateAt, ttFiber77RowAt, ttFiber77Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber77Key ttFiber77Expected (ttFiber77RowAt 4)
            (by decide) (by decide) (by decide) ttFiber77ReverseRow_4_ok)
      (by
        simpa [ttFiber77StateAt, ttFiber77RowAt, ttFiber77Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber77Key ttFiber77Expected (ttFiber77RowAt 5)
            (by decide) (by decide) (by decide) ttFiber77ReverseRow_5_ok)
      (by
        simpa [ttFiber77StateAt, ttFiber77RowAt, ttFiber77Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber77Key ttFiber77Expected (ttFiber77RowAt 6)
            (by decide) (by decide) (by decide) ttFiber77ReverseRow_6_ok)
      (by
        simpa [ttFiber77StateAt, ttFiber77RowAt, ttFiber77Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber77Key ttFiber77Expected (ttFiber77RowAt 7)
            (by decide) (by decide) (by decide) ttFiber77ReverseRow_7_ok)

end GoertzelLemma818LengthTwoShapeABridge

end Mettapedia.GraphTheory.FourColor
