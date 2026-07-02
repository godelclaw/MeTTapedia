import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoDirectClosurePrototype

namespace Mettapedia.GraphTheory.FourColor

/-!
# Shape-B direct closure bridge for additional generated length-two fibers

This module reuses the audited eight-state shape-B closure template from
`GoertzelLemma818LengthTwoDirectClosurePrototype` for generated `tau,tau`
fibers whose parent tree has the same source-to-root shape.
-/

namespace GoertzelLemma818LengthTwoShapeBBridge

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

def ttFiber18StateAt (i : Nat) : List TauState :=
  directStates (ttFiber18RowAt i).sourceLeft (ttFiber18RowAt i).sourceRight

def ttFiber18DirectStates : List (List TauState) :=
  [ ttFiber18StateAt 0, ttFiber18StateAt 1, ttFiber18StateAt 2, ttFiber18StateAt 3
  , ttFiber18StateAt 4, ttFiber18StateAt 5, ttFiber18StateAt 6, ttFiber18StateAt 7
  ]

theorem ttFiber18ReverseRow_1_ok :
    directRowReverseValid ttFiber18Key ttFiber18Expected (ttFiber18RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber18Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber18Chunk0] at h
  exact h.2

theorem ttFiber18ReverseRow_2_ok :
    directRowReverseValid ttFiber18Key ttFiber18Expected (ttFiber18RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber18Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber18Chunk1] at h
  exact h.1

theorem ttFiber18ReverseRow_3_ok :
    directRowReverseValid ttFiber18Key ttFiber18Expected (ttFiber18RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber18Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber18Chunk1] at h
  exact h.2

theorem ttFiber18ReverseRow_4_ok :
    directRowReverseValid ttFiber18Key ttFiber18Expected (ttFiber18RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber18Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber18Chunk2] at h
  exact h.1

theorem ttFiber18ReverseRow_5_ok :
    directRowReverseValid ttFiber18Key ttFiber18Expected (ttFiber18RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber18Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber18Chunk2] at h
  exact h.2

theorem ttFiber18ReverseRow_6_ok :
    directRowReverseValid ttFiber18Key ttFiber18Expected (ttFiber18RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber18Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber18Chunk3] at h
  exact h.1

theorem ttFiber18ReverseRow_7_ok :
    directRowReverseValid ttFiber18Key ttFiber18Expected (ttFiber18RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber18Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber18Chunk3] at h
  exact h.2

theorem ttFiber18ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber18StateAt 0) (ttFiber18StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber18StateAt 0) (ttFiber18StateAt 1)
    (ttFiber18RowAt 1).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber18Key ttFiber18Expected
        (ttFiber18RowAt 1) (by decide) ttFiber18ReverseRow_1_ok
      simpa [ttFiber18StateAt, ttFiber18RowAt, ttFiber18Rows, listGetD, directRow] using h)

theorem ttFiber18ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber18StateAt 0) (ttFiber18StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber18StateAt 0) (ttFiber18StateAt 2)
    (ttFiber18RowAt 2).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber18Key ttFiber18Expected
        (ttFiber18RowAt 2) (by decide) ttFiber18ReverseRow_2_ok
      simpa [ttFiber18StateAt, ttFiber18RowAt, ttFiber18Rows, listGetD, directRow] using h)

theorem ttFiber18ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber18StateAt 1) (ttFiber18StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber18StateAt 1) (ttFiber18StateAt 3)
    (ttFiber18RowAt 3).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber18Key ttFiber18Expected
        (ttFiber18RowAt 3) (by decide) ttFiber18ReverseRow_3_ok
      simpa [ttFiber18StateAt, ttFiber18RowAt, ttFiber18Rows, listGetD, directRow] using h)

theorem ttFiber18ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber18StateAt 0) (ttFiber18StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber18StateAt 0) (ttFiber18StateAt 4)
    (ttFiber18RowAt 4).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber18Key ttFiber18Expected
        (ttFiber18RowAt 4) (by decide) ttFiber18ReverseRow_4_ok
      simpa [ttFiber18StateAt, ttFiber18RowAt, ttFiber18Rows, listGetD, directRow] using h)

theorem ttFiber18ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber18StateAt 1) (ttFiber18StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber18StateAt 1) (ttFiber18StateAt 5)
    (ttFiber18RowAt 5).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber18Key ttFiber18Expected
        (ttFiber18RowAt 5) (by decide) ttFiber18ReverseRow_5_ok
      simpa [ttFiber18StateAt, ttFiber18RowAt, ttFiber18Rows, listGetD, directRow] using h)

theorem ttFiber18ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber18StateAt 2) (ttFiber18StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber18StateAt 2) (ttFiber18StateAt 6)
    (ttFiber18RowAt 6).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber18Key ttFiber18Expected
        (ttFiber18RowAt 6) (by decide) ttFiber18ReverseRow_6_ok
      simpa [ttFiber18StateAt, ttFiber18RowAt, ttFiber18Rows, listGetD, directRow] using h)

theorem ttFiber18ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber18StateAt 3) (ttFiber18StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber18StateAt 3) (ttFiber18StateAt 7)
    (ttFiber18RowAt 7).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber18Key ttFiber18Expected
        (ttFiber18RowAt 7) (by decide) ttFiber18ReverseRow_7_ok
      simpa [ttFiber18StateAt, ttFiber18RowAt, ttFiber18Rows, listGetD, directRow] using h)

theorem ttFiber18DirectConnected :
    chainFiberConnected ttWord ttFiber18DirectStates = true := by
  simpa [ttFiber18DirectStates] using
    directConnected8ShapeB ttWord ttFiber18StateAt
      ttFiber18ReverseSingleStep1
      ttFiber18ReverseSingleStep2
      ttFiber18ReverseSingleStep3
      ttFiber18ReverseSingleStep4
      ttFiber18ReverseSingleStep5
      ttFiber18ReverseSingleStep6
      ttFiber18ReverseSingleStep7

def ttFiber19StateAt (i : Nat) : List TauState :=
  directStates (ttFiber19RowAt i).sourceLeft (ttFiber19RowAt i).sourceRight

def ttFiber19DirectStates : List (List TauState) :=
  [ ttFiber19StateAt 0, ttFiber19StateAt 1, ttFiber19StateAt 2, ttFiber19StateAt 3
  , ttFiber19StateAt 4, ttFiber19StateAt 5, ttFiber19StateAt 6, ttFiber19StateAt 7
  ]

theorem ttFiber19ReverseRow_1_ok :
    directRowReverseValid ttFiber19Key ttFiber19Expected (ttFiber19RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber19Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber19Chunk0] at h
  exact h.2

theorem ttFiber19ReverseRow_2_ok :
    directRowReverseValid ttFiber19Key ttFiber19Expected (ttFiber19RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber19Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber19Chunk1] at h
  exact h.1

theorem ttFiber19ReverseRow_3_ok :
    directRowReverseValid ttFiber19Key ttFiber19Expected (ttFiber19RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber19Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber19Chunk1] at h
  exact h.2

theorem ttFiber19ReverseRow_4_ok :
    directRowReverseValid ttFiber19Key ttFiber19Expected (ttFiber19RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber19Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber19Chunk2] at h
  exact h.1

theorem ttFiber19ReverseRow_5_ok :
    directRowReverseValid ttFiber19Key ttFiber19Expected (ttFiber19RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber19Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber19Chunk2] at h
  exact h.2

theorem ttFiber19ReverseRow_6_ok :
    directRowReverseValid ttFiber19Key ttFiber19Expected (ttFiber19RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber19Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber19Chunk3] at h
  exact h.1

theorem ttFiber19ReverseRow_7_ok :
    directRowReverseValid ttFiber19Key ttFiber19Expected (ttFiber19RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber19Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber19Chunk3] at h
  exact h.2

theorem ttFiber19ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber19StateAt 0) (ttFiber19StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber19StateAt 0) (ttFiber19StateAt 1)
    (ttFiber19RowAt 1).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber19Key ttFiber19Expected
        (ttFiber19RowAt 1) (by decide) ttFiber19ReverseRow_1_ok
      simpa [ttFiber19StateAt, ttFiber19RowAt, ttFiber19Rows, listGetD, directRow] using h)

theorem ttFiber19ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber19StateAt 0) (ttFiber19StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber19StateAt 0) (ttFiber19StateAt 2)
    (ttFiber19RowAt 2).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber19Key ttFiber19Expected
        (ttFiber19RowAt 2) (by decide) ttFiber19ReverseRow_2_ok
      simpa [ttFiber19StateAt, ttFiber19RowAt, ttFiber19Rows, listGetD, directRow] using h)

theorem ttFiber19ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber19StateAt 1) (ttFiber19StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber19StateAt 1) (ttFiber19StateAt 3)
    (ttFiber19RowAt 3).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber19Key ttFiber19Expected
        (ttFiber19RowAt 3) (by decide) ttFiber19ReverseRow_3_ok
      simpa [ttFiber19StateAt, ttFiber19RowAt, ttFiber19Rows, listGetD, directRow] using h)

theorem ttFiber19ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber19StateAt 0) (ttFiber19StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber19StateAt 0) (ttFiber19StateAt 4)
    (ttFiber19RowAt 4).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber19Key ttFiber19Expected
        (ttFiber19RowAt 4) (by decide) ttFiber19ReverseRow_4_ok
      simpa [ttFiber19StateAt, ttFiber19RowAt, ttFiber19Rows, listGetD, directRow] using h)

theorem ttFiber19ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber19StateAt 1) (ttFiber19StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber19StateAt 1) (ttFiber19StateAt 5)
    (ttFiber19RowAt 5).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber19Key ttFiber19Expected
        (ttFiber19RowAt 5) (by decide) ttFiber19ReverseRow_5_ok
      simpa [ttFiber19StateAt, ttFiber19RowAt, ttFiber19Rows, listGetD, directRow] using h)

theorem ttFiber19ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber19StateAt 2) (ttFiber19StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber19StateAt 2) (ttFiber19StateAt 6)
    (ttFiber19RowAt 6).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber19Key ttFiber19Expected
        (ttFiber19RowAt 6) (by decide) ttFiber19ReverseRow_6_ok
      simpa [ttFiber19StateAt, ttFiber19RowAt, ttFiber19Rows, listGetD, directRow] using h)

theorem ttFiber19ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber19StateAt 3) (ttFiber19StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber19StateAt 3) (ttFiber19StateAt 7)
    (ttFiber19RowAt 7).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber19Key ttFiber19Expected
        (ttFiber19RowAt 7) (by decide) ttFiber19ReverseRow_7_ok
      simpa [ttFiber19StateAt, ttFiber19RowAt, ttFiber19Rows, listGetD, directRow] using h)

theorem ttFiber19DirectConnected :
    chainFiberConnected ttWord ttFiber19DirectStates = true := by
  simpa [ttFiber19DirectStates] using
    directConnected8ShapeB ttWord ttFiber19StateAt
      ttFiber19ReverseSingleStep1
      ttFiber19ReverseSingleStep2
      ttFiber19ReverseSingleStep3
      ttFiber19ReverseSingleStep4
      ttFiber19ReverseSingleStep5
      ttFiber19ReverseSingleStep6
      ttFiber19ReverseSingleStep7

def ttFiber31StateAt (i : Nat) : List TauState :=
  directStates (ttFiber31RowAt i).sourceLeft (ttFiber31RowAt i).sourceRight

def ttFiber31DirectStates : List (List TauState) :=
  [ ttFiber31StateAt 0, ttFiber31StateAt 1, ttFiber31StateAt 2, ttFiber31StateAt 3
  , ttFiber31StateAt 4, ttFiber31StateAt 5, ttFiber31StateAt 6, ttFiber31StateAt 7
  ]

theorem ttFiber31ReverseRow_1_ok :
    directRowReverseValid ttFiber31Key ttFiber31Expected (ttFiber31RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber31Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber31Chunk0] at h
  exact h.2

theorem ttFiber31ReverseRow_2_ok :
    directRowReverseValid ttFiber31Key ttFiber31Expected (ttFiber31RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber31Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber31Chunk1] at h
  exact h.1

theorem ttFiber31ReverseRow_3_ok :
    directRowReverseValid ttFiber31Key ttFiber31Expected (ttFiber31RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber31Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber31Chunk1] at h
  exact h.2

theorem ttFiber31ReverseRow_4_ok :
    directRowReverseValid ttFiber31Key ttFiber31Expected (ttFiber31RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber31Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber31Chunk2] at h
  exact h.1

theorem ttFiber31ReverseRow_5_ok :
    directRowReverseValid ttFiber31Key ttFiber31Expected (ttFiber31RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber31Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber31Chunk2] at h
  exact h.2

theorem ttFiber31ReverseRow_6_ok :
    directRowReverseValid ttFiber31Key ttFiber31Expected (ttFiber31RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber31Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber31Chunk3] at h
  exact h.1

theorem ttFiber31ReverseRow_7_ok :
    directRowReverseValid ttFiber31Key ttFiber31Expected (ttFiber31RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber31Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber31Chunk3] at h
  exact h.2

theorem ttFiber31ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber31StateAt 0) (ttFiber31StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber31StateAt 0) (ttFiber31StateAt 1)
    (ttFiber31RowAt 1).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber31Key ttFiber31Expected
        (ttFiber31RowAt 1) (by decide) ttFiber31ReverseRow_1_ok
      simpa [ttFiber31StateAt, ttFiber31RowAt, ttFiber31Rows, listGetD, directRow] using h)

theorem ttFiber31ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber31StateAt 0) (ttFiber31StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber31StateAt 0) (ttFiber31StateAt 2)
    (ttFiber31RowAt 2).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber31Key ttFiber31Expected
        (ttFiber31RowAt 2) (by decide) ttFiber31ReverseRow_2_ok
      simpa [ttFiber31StateAt, ttFiber31RowAt, ttFiber31Rows, listGetD, directRow] using h)

theorem ttFiber31ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber31StateAt 1) (ttFiber31StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber31StateAt 1) (ttFiber31StateAt 3)
    (ttFiber31RowAt 3).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber31Key ttFiber31Expected
        (ttFiber31RowAt 3) (by decide) ttFiber31ReverseRow_3_ok
      simpa [ttFiber31StateAt, ttFiber31RowAt, ttFiber31Rows, listGetD, directRow] using h)

theorem ttFiber31ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber31StateAt 0) (ttFiber31StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber31StateAt 0) (ttFiber31StateAt 4)
    (ttFiber31RowAt 4).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber31Key ttFiber31Expected
        (ttFiber31RowAt 4) (by decide) ttFiber31ReverseRow_4_ok
      simpa [ttFiber31StateAt, ttFiber31RowAt, ttFiber31Rows, listGetD, directRow] using h)

theorem ttFiber31ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber31StateAt 1) (ttFiber31StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber31StateAt 1) (ttFiber31StateAt 5)
    (ttFiber31RowAt 5).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber31Key ttFiber31Expected
        (ttFiber31RowAt 5) (by decide) ttFiber31ReverseRow_5_ok
      simpa [ttFiber31StateAt, ttFiber31RowAt, ttFiber31Rows, listGetD, directRow] using h)

theorem ttFiber31ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber31StateAt 2) (ttFiber31StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber31StateAt 2) (ttFiber31StateAt 6)
    (ttFiber31RowAt 6).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber31Key ttFiber31Expected
        (ttFiber31RowAt 6) (by decide) ttFiber31ReverseRow_6_ok
      simpa [ttFiber31StateAt, ttFiber31RowAt, ttFiber31Rows, listGetD, directRow] using h)

theorem ttFiber31ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber31StateAt 3) (ttFiber31StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber31StateAt 3) (ttFiber31StateAt 7)
    (ttFiber31RowAt 7).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber31Key ttFiber31Expected
        (ttFiber31RowAt 7) (by decide) ttFiber31ReverseRow_7_ok
      simpa [ttFiber31StateAt, ttFiber31RowAt, ttFiber31Rows, listGetD, directRow] using h)

theorem ttFiber31DirectConnected :
    chainFiberConnected ttWord ttFiber31DirectStates = true := by
  simpa [ttFiber31DirectStates] using
    directConnected8ShapeB ttWord ttFiber31StateAt
      ttFiber31ReverseSingleStep1
      ttFiber31ReverseSingleStep2
      ttFiber31ReverseSingleStep3
      ttFiber31ReverseSingleStep4
      ttFiber31ReverseSingleStep5
      ttFiber31ReverseSingleStep6
      ttFiber31ReverseSingleStep7

def ttFiber32StateAt (i : Nat) : List TauState :=
  directStates (ttFiber32RowAt i).sourceLeft (ttFiber32RowAt i).sourceRight

def ttFiber32DirectStates : List (List TauState) :=
  [ ttFiber32StateAt 0, ttFiber32StateAt 1, ttFiber32StateAt 2, ttFiber32StateAt 3
  , ttFiber32StateAt 4, ttFiber32StateAt 5, ttFiber32StateAt 6, ttFiber32StateAt 7
  ]

theorem ttFiber32ReverseRow_1_ok :
    directRowReverseValid ttFiber32Key ttFiber32Expected (ttFiber32RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber32Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber32Chunk0] at h
  exact h.2

theorem ttFiber32ReverseRow_2_ok :
    directRowReverseValid ttFiber32Key ttFiber32Expected (ttFiber32RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber32Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber32Chunk1] at h
  exact h.1

theorem ttFiber32ReverseRow_3_ok :
    directRowReverseValid ttFiber32Key ttFiber32Expected (ttFiber32RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber32Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber32Chunk1] at h
  exact h.2

theorem ttFiber32ReverseRow_4_ok :
    directRowReverseValid ttFiber32Key ttFiber32Expected (ttFiber32RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber32Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber32Chunk2] at h
  exact h.1

theorem ttFiber32ReverseRow_5_ok :
    directRowReverseValid ttFiber32Key ttFiber32Expected (ttFiber32RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber32Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber32Chunk2] at h
  exact h.2

theorem ttFiber32ReverseRow_6_ok :
    directRowReverseValid ttFiber32Key ttFiber32Expected (ttFiber32RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber32Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber32Chunk3] at h
  exact h.1

theorem ttFiber32ReverseRow_7_ok :
    directRowReverseValid ttFiber32Key ttFiber32Expected (ttFiber32RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber32Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber32Chunk3] at h
  exact h.2

theorem ttFiber32ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber32StateAt 0) (ttFiber32StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber32StateAt 0) (ttFiber32StateAt 1)
    (ttFiber32RowAt 1).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber32Key ttFiber32Expected
        (ttFiber32RowAt 1) (by decide) ttFiber32ReverseRow_1_ok
      simpa [ttFiber32StateAt, ttFiber32RowAt, ttFiber32Rows, listGetD, directRow] using h)

theorem ttFiber32ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber32StateAt 0) (ttFiber32StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber32StateAt 0) (ttFiber32StateAt 2)
    (ttFiber32RowAt 2).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber32Key ttFiber32Expected
        (ttFiber32RowAt 2) (by decide) ttFiber32ReverseRow_2_ok
      simpa [ttFiber32StateAt, ttFiber32RowAt, ttFiber32Rows, listGetD, directRow] using h)

theorem ttFiber32ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber32StateAt 1) (ttFiber32StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber32StateAt 1) (ttFiber32StateAt 3)
    (ttFiber32RowAt 3).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber32Key ttFiber32Expected
        (ttFiber32RowAt 3) (by decide) ttFiber32ReverseRow_3_ok
      simpa [ttFiber32StateAt, ttFiber32RowAt, ttFiber32Rows, listGetD, directRow] using h)

theorem ttFiber32ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber32StateAt 0) (ttFiber32StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber32StateAt 0) (ttFiber32StateAt 4)
    (ttFiber32RowAt 4).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber32Key ttFiber32Expected
        (ttFiber32RowAt 4) (by decide) ttFiber32ReverseRow_4_ok
      simpa [ttFiber32StateAt, ttFiber32RowAt, ttFiber32Rows, listGetD, directRow] using h)

theorem ttFiber32ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber32StateAt 1) (ttFiber32StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber32StateAt 1) (ttFiber32StateAt 5)
    (ttFiber32RowAt 5).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber32Key ttFiber32Expected
        (ttFiber32RowAt 5) (by decide) ttFiber32ReverseRow_5_ok
      simpa [ttFiber32StateAt, ttFiber32RowAt, ttFiber32Rows, listGetD, directRow] using h)

theorem ttFiber32ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber32StateAt 2) (ttFiber32StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber32StateAt 2) (ttFiber32StateAt 6)
    (ttFiber32RowAt 6).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber32Key ttFiber32Expected
        (ttFiber32RowAt 6) (by decide) ttFiber32ReverseRow_6_ok
      simpa [ttFiber32StateAt, ttFiber32RowAt, ttFiber32Rows, listGetD, directRow] using h)

theorem ttFiber32ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber32StateAt 3) (ttFiber32StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber32StateAt 3) (ttFiber32StateAt 7)
    (ttFiber32RowAt 7).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber32Key ttFiber32Expected
        (ttFiber32RowAt 7) (by decide) ttFiber32ReverseRow_7_ok
      simpa [ttFiber32StateAt, ttFiber32RowAt, ttFiber32Rows, listGetD, directRow] using h)

theorem ttFiber32DirectConnected :
    chainFiberConnected ttWord ttFiber32DirectStates = true := by
  simpa [ttFiber32DirectStates] using
    directConnected8ShapeB ttWord ttFiber32StateAt
      ttFiber32ReverseSingleStep1
      ttFiber32ReverseSingleStep2
      ttFiber32ReverseSingleStep3
      ttFiber32ReverseSingleStep4
      ttFiber32ReverseSingleStep5
      ttFiber32ReverseSingleStep6
      ttFiber32ReverseSingleStep7

def ttFiber37StateAt (i : Nat) : List TauState :=
  directStates (ttFiber37RowAt i).sourceLeft (ttFiber37RowAt i).sourceRight

def ttFiber37DirectStates : List (List TauState) :=
  [ ttFiber37StateAt 0, ttFiber37StateAt 1, ttFiber37StateAt 2, ttFiber37StateAt 3
  , ttFiber37StateAt 4, ttFiber37StateAt 5, ttFiber37StateAt 6, ttFiber37StateAt 7
  ]

theorem ttFiber37ReverseRow_1_ok :
    directRowReverseValid ttFiber37Key ttFiber37Expected (ttFiber37RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber37Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber37Chunk0] at h
  exact h.2

theorem ttFiber37ReverseRow_2_ok :
    directRowReverseValid ttFiber37Key ttFiber37Expected (ttFiber37RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber37Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber37Chunk1] at h
  exact h.1

theorem ttFiber37ReverseRow_3_ok :
    directRowReverseValid ttFiber37Key ttFiber37Expected (ttFiber37RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber37Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber37Chunk1] at h
  exact h.2

theorem ttFiber37ReverseRow_4_ok :
    directRowReverseValid ttFiber37Key ttFiber37Expected (ttFiber37RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber37Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber37Chunk2] at h
  exact h.1

theorem ttFiber37ReverseRow_5_ok :
    directRowReverseValid ttFiber37Key ttFiber37Expected (ttFiber37RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber37Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber37Chunk2] at h
  exact h.2

theorem ttFiber37ReverseRow_6_ok :
    directRowReverseValid ttFiber37Key ttFiber37Expected (ttFiber37RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber37Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber37Chunk3] at h
  exact h.1

theorem ttFiber37ReverseRow_7_ok :
    directRowReverseValid ttFiber37Key ttFiber37Expected (ttFiber37RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber37Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber37Chunk3] at h
  exact h.2

theorem ttFiber37DirectConnected :
    chainFiberConnected ttWord ttFiber37DirectStates = true := by
  simpa [ttFiber37DirectStates] using
    directConnected8ShapeB ttWord ttFiber37StateAt
      (by
        simpa [ttFiber37StateAt, ttFiber37RowAt, ttFiber37Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber37Key ttFiber37Expected (ttFiber37RowAt 1)
            (by decide) (by decide) (by decide) ttFiber37ReverseRow_1_ok)
      (by
        simpa [ttFiber37StateAt, ttFiber37RowAt, ttFiber37Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber37Key ttFiber37Expected (ttFiber37RowAt 2)
            (by decide) (by decide) (by decide) ttFiber37ReverseRow_2_ok)
      (by
        simpa [ttFiber37StateAt, ttFiber37RowAt, ttFiber37Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber37Key ttFiber37Expected (ttFiber37RowAt 3)
            (by decide) (by decide) (by decide) ttFiber37ReverseRow_3_ok)
      (by
        simpa [ttFiber37StateAt, ttFiber37RowAt, ttFiber37Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber37Key ttFiber37Expected (ttFiber37RowAt 4)
            (by decide) (by decide) (by decide) ttFiber37ReverseRow_4_ok)
      (by
        simpa [ttFiber37StateAt, ttFiber37RowAt, ttFiber37Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber37Key ttFiber37Expected (ttFiber37RowAt 5)
            (by decide) (by decide) (by decide) ttFiber37ReverseRow_5_ok)
      (by
        simpa [ttFiber37StateAt, ttFiber37RowAt, ttFiber37Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber37Key ttFiber37Expected (ttFiber37RowAt 6)
            (by decide) (by decide) (by decide) ttFiber37ReverseRow_6_ok)
      (by
        simpa [ttFiber37StateAt, ttFiber37RowAt, ttFiber37Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber37Key ttFiber37Expected (ttFiber37RowAt 7)
            (by decide) (by decide) (by decide) ttFiber37ReverseRow_7_ok)

def ttFiber38StateAt (i : Nat) : List TauState :=
  directStates (ttFiber38RowAt i).sourceLeft (ttFiber38RowAt i).sourceRight

def ttFiber38DirectStates : List (List TauState) :=
  [ ttFiber38StateAt 0, ttFiber38StateAt 1, ttFiber38StateAt 2, ttFiber38StateAt 3
  , ttFiber38StateAt 4, ttFiber38StateAt 5, ttFiber38StateAt 6, ttFiber38StateAt 7
  ]

theorem ttFiber38ReverseRow_1_ok :
    directRowReverseValid ttFiber38Key ttFiber38Expected (ttFiber38RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber38Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber38Chunk0] at h
  exact h.2

theorem ttFiber38ReverseRow_2_ok :
    directRowReverseValid ttFiber38Key ttFiber38Expected (ttFiber38RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber38Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber38Chunk1] at h
  exact h.1

theorem ttFiber38ReverseRow_3_ok :
    directRowReverseValid ttFiber38Key ttFiber38Expected (ttFiber38RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber38Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber38Chunk1] at h
  exact h.2

theorem ttFiber38ReverseRow_4_ok :
    directRowReverseValid ttFiber38Key ttFiber38Expected (ttFiber38RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber38Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber38Chunk2] at h
  exact h.1

theorem ttFiber38ReverseRow_5_ok :
    directRowReverseValid ttFiber38Key ttFiber38Expected (ttFiber38RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber38Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber38Chunk2] at h
  exact h.2

theorem ttFiber38ReverseRow_6_ok :
    directRowReverseValid ttFiber38Key ttFiber38Expected (ttFiber38RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber38Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber38Chunk3] at h
  exact h.1

theorem ttFiber38ReverseRow_7_ok :
    directRowReverseValid ttFiber38Key ttFiber38Expected (ttFiber38RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber38Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber38Chunk3] at h
  exact h.2

theorem ttFiber38DirectConnected :
    chainFiberConnected ttWord ttFiber38DirectStates = true := by
  simpa [ttFiber38DirectStates] using
    directConnected8ShapeB ttWord ttFiber38StateAt
      (by
        simpa [ttFiber38StateAt, ttFiber38RowAt, ttFiber38Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber38Key ttFiber38Expected (ttFiber38RowAt 1)
            (by decide) (by decide) (by decide) ttFiber38ReverseRow_1_ok)
      (by
        simpa [ttFiber38StateAt, ttFiber38RowAt, ttFiber38Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber38Key ttFiber38Expected (ttFiber38RowAt 2)
            (by decide) (by decide) (by decide) ttFiber38ReverseRow_2_ok)
      (by
        simpa [ttFiber38StateAt, ttFiber38RowAt, ttFiber38Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber38Key ttFiber38Expected (ttFiber38RowAt 3)
            (by decide) (by decide) (by decide) ttFiber38ReverseRow_3_ok)
      (by
        simpa [ttFiber38StateAt, ttFiber38RowAt, ttFiber38Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber38Key ttFiber38Expected (ttFiber38RowAt 4)
            (by decide) (by decide) (by decide) ttFiber38ReverseRow_4_ok)
      (by
        simpa [ttFiber38StateAt, ttFiber38RowAt, ttFiber38Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber38Key ttFiber38Expected (ttFiber38RowAt 5)
            (by decide) (by decide) (by decide) ttFiber38ReverseRow_5_ok)
      (by
        simpa [ttFiber38StateAt, ttFiber38RowAt, ttFiber38Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber38Key ttFiber38Expected (ttFiber38RowAt 6)
            (by decide) (by decide) (by decide) ttFiber38ReverseRow_6_ok)
      (by
        simpa [ttFiber38StateAt, ttFiber38RowAt, ttFiber38Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber38Key ttFiber38Expected (ttFiber38RowAt 7)
            (by decide) (by decide) (by decide) ttFiber38ReverseRow_7_ok)

def ttFiber42StateAt (i : Nat) : List TauState :=
  directStates (ttFiber42RowAt i).sourceLeft (ttFiber42RowAt i).sourceRight

def ttFiber42DirectStates : List (List TauState) :=
  [ ttFiber42StateAt 0, ttFiber42StateAt 1, ttFiber42StateAt 2, ttFiber42StateAt 3
  , ttFiber42StateAt 4, ttFiber42StateAt 5, ttFiber42StateAt 6, ttFiber42StateAt 7
  ]

theorem ttFiber42ReverseRow_1_ok :
    directRowReverseValid ttFiber42Key ttFiber42Expected (ttFiber42RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber42Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber42Chunk0] at h
  exact h.2

theorem ttFiber42ReverseRow_2_ok :
    directRowReverseValid ttFiber42Key ttFiber42Expected (ttFiber42RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber42Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber42Chunk1] at h
  exact h.1

theorem ttFiber42ReverseRow_3_ok :
    directRowReverseValid ttFiber42Key ttFiber42Expected (ttFiber42RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber42Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber42Chunk1] at h
  exact h.2

theorem ttFiber42ReverseRow_4_ok :
    directRowReverseValid ttFiber42Key ttFiber42Expected (ttFiber42RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber42Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber42Chunk2] at h
  exact h.1

theorem ttFiber42ReverseRow_5_ok :
    directRowReverseValid ttFiber42Key ttFiber42Expected (ttFiber42RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber42Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber42Chunk2] at h
  exact h.2

theorem ttFiber42ReverseRow_6_ok :
    directRowReverseValid ttFiber42Key ttFiber42Expected (ttFiber42RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber42Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber42Chunk3] at h
  exact h.1

theorem ttFiber42ReverseRow_7_ok :
    directRowReverseValid ttFiber42Key ttFiber42Expected (ttFiber42RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber42Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber42Chunk3] at h
  exact h.2

theorem ttFiber42DirectConnected :
    chainFiberConnected ttWord ttFiber42DirectStates = true := by
  simpa [ttFiber42DirectStates] using
    directConnected8ShapeB ttWord ttFiber42StateAt
      (by
        simpa [ttFiber42StateAt, ttFiber42RowAt, ttFiber42Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber42Key ttFiber42Expected (ttFiber42RowAt 1)
            (by decide) (by decide) (by decide) ttFiber42ReverseRow_1_ok)
      (by
        simpa [ttFiber42StateAt, ttFiber42RowAt, ttFiber42Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber42Key ttFiber42Expected (ttFiber42RowAt 2)
            (by decide) (by decide) (by decide) ttFiber42ReverseRow_2_ok)
      (by
        simpa [ttFiber42StateAt, ttFiber42RowAt, ttFiber42Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber42Key ttFiber42Expected (ttFiber42RowAt 3)
            (by decide) (by decide) (by decide) ttFiber42ReverseRow_3_ok)
      (by
        simpa [ttFiber42StateAt, ttFiber42RowAt, ttFiber42Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber42Key ttFiber42Expected (ttFiber42RowAt 4)
            (by decide) (by decide) (by decide) ttFiber42ReverseRow_4_ok)
      (by
        simpa [ttFiber42StateAt, ttFiber42RowAt, ttFiber42Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber42Key ttFiber42Expected (ttFiber42RowAt 5)
            (by decide) (by decide) (by decide) ttFiber42ReverseRow_5_ok)
      (by
        simpa [ttFiber42StateAt, ttFiber42RowAt, ttFiber42Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber42Key ttFiber42Expected (ttFiber42RowAt 6)
            (by decide) (by decide) (by decide) ttFiber42ReverseRow_6_ok)
      (by
        simpa [ttFiber42StateAt, ttFiber42RowAt, ttFiber42Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber42Key ttFiber42Expected (ttFiber42RowAt 7)
            (by decide) (by decide) (by decide) ttFiber42ReverseRow_7_ok)

def ttFiber43StateAt (i : Nat) : List TauState :=
  directStates (ttFiber43RowAt i).sourceLeft (ttFiber43RowAt i).sourceRight

def ttFiber43DirectStates : List (List TauState) :=
  [ ttFiber43StateAt 0, ttFiber43StateAt 1, ttFiber43StateAt 2, ttFiber43StateAt 3
  , ttFiber43StateAt 4, ttFiber43StateAt 5, ttFiber43StateAt 6, ttFiber43StateAt 7
  ]

theorem ttFiber43ReverseRow_1_ok :
    directRowReverseValid ttFiber43Key ttFiber43Expected (ttFiber43RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber43Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber43Chunk0] at h
  exact h.2

theorem ttFiber43ReverseRow_2_ok :
    directRowReverseValid ttFiber43Key ttFiber43Expected (ttFiber43RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber43Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber43Chunk1] at h
  exact h.1

theorem ttFiber43ReverseRow_3_ok :
    directRowReverseValid ttFiber43Key ttFiber43Expected (ttFiber43RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber43Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber43Chunk1] at h
  exact h.2

theorem ttFiber43ReverseRow_4_ok :
    directRowReverseValid ttFiber43Key ttFiber43Expected (ttFiber43RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber43Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber43Chunk2] at h
  exact h.1

theorem ttFiber43ReverseRow_5_ok :
    directRowReverseValid ttFiber43Key ttFiber43Expected (ttFiber43RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber43Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber43Chunk2] at h
  exact h.2

theorem ttFiber43ReverseRow_6_ok :
    directRowReverseValid ttFiber43Key ttFiber43Expected (ttFiber43RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber43Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber43Chunk3] at h
  exact h.1

theorem ttFiber43ReverseRow_7_ok :
    directRowReverseValid ttFiber43Key ttFiber43Expected (ttFiber43RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber43Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber43Chunk3] at h
  exact h.2

theorem ttFiber43DirectConnected :
    chainFiberConnected ttWord ttFiber43DirectStates = true := by
  simpa [ttFiber43DirectStates] using
    directConnected8ShapeB ttWord ttFiber43StateAt
      (by
        simpa [ttFiber43StateAt, ttFiber43RowAt, ttFiber43Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber43Key ttFiber43Expected (ttFiber43RowAt 1)
            (by decide) (by decide) (by decide) ttFiber43ReverseRow_1_ok)
      (by
        simpa [ttFiber43StateAt, ttFiber43RowAt, ttFiber43Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber43Key ttFiber43Expected (ttFiber43RowAt 2)
            (by decide) (by decide) (by decide) ttFiber43ReverseRow_2_ok)
      (by
        simpa [ttFiber43StateAt, ttFiber43RowAt, ttFiber43Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber43Key ttFiber43Expected (ttFiber43RowAt 3)
            (by decide) (by decide) (by decide) ttFiber43ReverseRow_3_ok)
      (by
        simpa [ttFiber43StateAt, ttFiber43RowAt, ttFiber43Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber43Key ttFiber43Expected (ttFiber43RowAt 4)
            (by decide) (by decide) (by decide) ttFiber43ReverseRow_4_ok)
      (by
        simpa [ttFiber43StateAt, ttFiber43RowAt, ttFiber43Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber43Key ttFiber43Expected (ttFiber43RowAt 5)
            (by decide) (by decide) (by decide) ttFiber43ReverseRow_5_ok)
      (by
        simpa [ttFiber43StateAt, ttFiber43RowAt, ttFiber43Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber43Key ttFiber43Expected (ttFiber43RowAt 6)
            (by decide) (by decide) (by decide) ttFiber43ReverseRow_6_ok)
      (by
        simpa [ttFiber43StateAt, ttFiber43RowAt, ttFiber43Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber43Key ttFiber43Expected (ttFiber43RowAt 7)
            (by decide) (by decide) (by decide) ttFiber43ReverseRow_7_ok)

def ttFiber48StateAt (i : Nat) : List TauState :=
  directStates (ttFiber48RowAt i).sourceLeft (ttFiber48RowAt i).sourceRight

def ttFiber48DirectStates : List (List TauState) :=
  [ ttFiber48StateAt 0, ttFiber48StateAt 1, ttFiber48StateAt 2, ttFiber48StateAt 3
  , ttFiber48StateAt 4, ttFiber48StateAt 5, ttFiber48StateAt 6, ttFiber48StateAt 7
  ]

theorem ttFiber48ReverseRow_1_ok :
    directRowReverseValid ttFiber48Key ttFiber48Expected (ttFiber48RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber48Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber48Chunk0] at h
  exact h.2

theorem ttFiber48ReverseRow_2_ok :
    directRowReverseValid ttFiber48Key ttFiber48Expected (ttFiber48RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber48Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber48Chunk1] at h
  exact h.1

theorem ttFiber48ReverseRow_3_ok :
    directRowReverseValid ttFiber48Key ttFiber48Expected (ttFiber48RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber48Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber48Chunk1] at h
  exact h.2

theorem ttFiber48ReverseRow_4_ok :
    directRowReverseValid ttFiber48Key ttFiber48Expected (ttFiber48RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber48Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber48Chunk2] at h
  exact h.1

theorem ttFiber48ReverseRow_5_ok :
    directRowReverseValid ttFiber48Key ttFiber48Expected (ttFiber48RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber48Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber48Chunk2] at h
  exact h.2

theorem ttFiber48ReverseRow_6_ok :
    directRowReverseValid ttFiber48Key ttFiber48Expected (ttFiber48RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber48Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber48Chunk3] at h
  exact h.1

theorem ttFiber48ReverseRow_7_ok :
    directRowReverseValid ttFiber48Key ttFiber48Expected (ttFiber48RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber48Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber48Chunk3] at h
  exact h.2

theorem ttFiber48DirectConnected :
    chainFiberConnected ttWord ttFiber48DirectStates = true := by
  simpa [ttFiber48DirectStates] using
    directConnected8ShapeB ttWord ttFiber48StateAt
      (by
        simpa [ttFiber48StateAt, ttFiber48RowAt, ttFiber48Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber48Key ttFiber48Expected (ttFiber48RowAt 1)
            (by decide) (by decide) (by decide) ttFiber48ReverseRow_1_ok)
      (by
        simpa [ttFiber48StateAt, ttFiber48RowAt, ttFiber48Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber48Key ttFiber48Expected (ttFiber48RowAt 2)
            (by decide) (by decide) (by decide) ttFiber48ReverseRow_2_ok)
      (by
        simpa [ttFiber48StateAt, ttFiber48RowAt, ttFiber48Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber48Key ttFiber48Expected (ttFiber48RowAt 3)
            (by decide) (by decide) (by decide) ttFiber48ReverseRow_3_ok)
      (by
        simpa [ttFiber48StateAt, ttFiber48RowAt, ttFiber48Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber48Key ttFiber48Expected (ttFiber48RowAt 4)
            (by decide) (by decide) (by decide) ttFiber48ReverseRow_4_ok)
      (by
        simpa [ttFiber48StateAt, ttFiber48RowAt, ttFiber48Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber48Key ttFiber48Expected (ttFiber48RowAt 5)
            (by decide) (by decide) (by decide) ttFiber48ReverseRow_5_ok)
      (by
        simpa [ttFiber48StateAt, ttFiber48RowAt, ttFiber48Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber48Key ttFiber48Expected (ttFiber48RowAt 6)
            (by decide) (by decide) (by decide) ttFiber48ReverseRow_6_ok)
      (by
        simpa [ttFiber48StateAt, ttFiber48RowAt, ttFiber48Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber48Key ttFiber48Expected (ttFiber48RowAt 7)
            (by decide) (by decide) (by decide) ttFiber48ReverseRow_7_ok)

def ttFiber49StateAt (i : Nat) : List TauState :=
  directStates (ttFiber49RowAt i).sourceLeft (ttFiber49RowAt i).sourceRight

def ttFiber49DirectStates : List (List TauState) :=
  [ ttFiber49StateAt 0, ttFiber49StateAt 1, ttFiber49StateAt 2, ttFiber49StateAt 3
  , ttFiber49StateAt 4, ttFiber49StateAt 5, ttFiber49StateAt 6, ttFiber49StateAt 7
  ]

theorem ttFiber49ReverseRow_1_ok :
    directRowReverseValid ttFiber49Key ttFiber49Expected (ttFiber49RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber49Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber49Chunk0] at h
  exact h.2

theorem ttFiber49ReverseRow_2_ok :
    directRowReverseValid ttFiber49Key ttFiber49Expected (ttFiber49RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber49Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber49Chunk1] at h
  exact h.1

theorem ttFiber49ReverseRow_3_ok :
    directRowReverseValid ttFiber49Key ttFiber49Expected (ttFiber49RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber49Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber49Chunk1] at h
  exact h.2

theorem ttFiber49ReverseRow_4_ok :
    directRowReverseValid ttFiber49Key ttFiber49Expected (ttFiber49RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber49Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber49Chunk2] at h
  exact h.1

theorem ttFiber49ReverseRow_5_ok :
    directRowReverseValid ttFiber49Key ttFiber49Expected (ttFiber49RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber49Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber49Chunk2] at h
  exact h.2

theorem ttFiber49ReverseRow_6_ok :
    directRowReverseValid ttFiber49Key ttFiber49Expected (ttFiber49RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber49Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber49Chunk3] at h
  exact h.1

theorem ttFiber49ReverseRow_7_ok :
    directRowReverseValid ttFiber49Key ttFiber49Expected (ttFiber49RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber49Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber49Chunk3] at h
  exact h.2

theorem ttFiber49DirectConnected :
    chainFiberConnected ttWord ttFiber49DirectStates = true := by
  simpa [ttFiber49DirectStates] using
    directConnected8ShapeB ttWord ttFiber49StateAt
      (by
        simpa [ttFiber49StateAt, ttFiber49RowAt, ttFiber49Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber49Key ttFiber49Expected (ttFiber49RowAt 1)
            (by decide) (by decide) (by decide) ttFiber49ReverseRow_1_ok)
      (by
        simpa [ttFiber49StateAt, ttFiber49RowAt, ttFiber49Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber49Key ttFiber49Expected (ttFiber49RowAt 2)
            (by decide) (by decide) (by decide) ttFiber49ReverseRow_2_ok)
      (by
        simpa [ttFiber49StateAt, ttFiber49RowAt, ttFiber49Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber49Key ttFiber49Expected (ttFiber49RowAt 3)
            (by decide) (by decide) (by decide) ttFiber49ReverseRow_3_ok)
      (by
        simpa [ttFiber49StateAt, ttFiber49RowAt, ttFiber49Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber49Key ttFiber49Expected (ttFiber49RowAt 4)
            (by decide) (by decide) (by decide) ttFiber49ReverseRow_4_ok)
      (by
        simpa [ttFiber49StateAt, ttFiber49RowAt, ttFiber49Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber49Key ttFiber49Expected (ttFiber49RowAt 5)
            (by decide) (by decide) (by decide) ttFiber49ReverseRow_5_ok)
      (by
        simpa [ttFiber49StateAt, ttFiber49RowAt, ttFiber49Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber49Key ttFiber49Expected (ttFiber49RowAt 6)
            (by decide) (by decide) (by decide) ttFiber49ReverseRow_6_ok)
      (by
        simpa [ttFiber49StateAt, ttFiber49RowAt, ttFiber49Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber49Key ttFiber49Expected (ttFiber49RowAt 7)
            (by decide) (by decide) (by decide) ttFiber49ReverseRow_7_ok)

def ttFiber61StateAt (i : Nat) : List TauState :=
  directStates (ttFiber61RowAt i).sourceLeft (ttFiber61RowAt i).sourceRight

def ttFiber61DirectStates : List (List TauState) :=
  [ ttFiber61StateAt 0, ttFiber61StateAt 1, ttFiber61StateAt 2, ttFiber61StateAt 3
  , ttFiber61StateAt 4, ttFiber61StateAt 5, ttFiber61StateAt 6, ttFiber61StateAt 7
  ]

theorem ttFiber61ReverseRow_1_ok :
    directRowReverseValid ttFiber61Key ttFiber61Expected (ttFiber61RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber61Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber61Chunk0] at h
  exact h.2

theorem ttFiber61ReverseRow_2_ok :
    directRowReverseValid ttFiber61Key ttFiber61Expected (ttFiber61RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber61Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber61Chunk1] at h
  exact h.1

theorem ttFiber61ReverseRow_3_ok :
    directRowReverseValid ttFiber61Key ttFiber61Expected (ttFiber61RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber61Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber61Chunk1] at h
  exact h.2

theorem ttFiber61ReverseRow_4_ok :
    directRowReverseValid ttFiber61Key ttFiber61Expected (ttFiber61RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber61Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber61Chunk2] at h
  exact h.1

theorem ttFiber61ReverseRow_5_ok :
    directRowReverseValid ttFiber61Key ttFiber61Expected (ttFiber61RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber61Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber61Chunk2] at h
  exact h.2

theorem ttFiber61ReverseRow_6_ok :
    directRowReverseValid ttFiber61Key ttFiber61Expected (ttFiber61RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber61Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber61Chunk3] at h
  exact h.1

theorem ttFiber61ReverseRow_7_ok :
    directRowReverseValid ttFiber61Key ttFiber61Expected (ttFiber61RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber61Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber61Chunk3] at h
  exact h.2

theorem ttFiber61DirectConnected :
    chainFiberConnected ttWord ttFiber61DirectStates = true := by
  simpa [ttFiber61DirectStates] using
    directConnected8ShapeB ttWord ttFiber61StateAt
      (by
        simpa [ttFiber61StateAt, ttFiber61RowAt, ttFiber61Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber61Key ttFiber61Expected (ttFiber61RowAt 1)
            (by decide) (by decide) (by decide) ttFiber61ReverseRow_1_ok)
      (by
        simpa [ttFiber61StateAt, ttFiber61RowAt, ttFiber61Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber61Key ttFiber61Expected (ttFiber61RowAt 2)
            (by decide) (by decide) (by decide) ttFiber61ReverseRow_2_ok)
      (by
        simpa [ttFiber61StateAt, ttFiber61RowAt, ttFiber61Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber61Key ttFiber61Expected (ttFiber61RowAt 3)
            (by decide) (by decide) (by decide) ttFiber61ReverseRow_3_ok)
      (by
        simpa [ttFiber61StateAt, ttFiber61RowAt, ttFiber61Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber61Key ttFiber61Expected (ttFiber61RowAt 4)
            (by decide) (by decide) (by decide) ttFiber61ReverseRow_4_ok)
      (by
        simpa [ttFiber61StateAt, ttFiber61RowAt, ttFiber61Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber61Key ttFiber61Expected (ttFiber61RowAt 5)
            (by decide) (by decide) (by decide) ttFiber61ReverseRow_5_ok)
      (by
        simpa [ttFiber61StateAt, ttFiber61RowAt, ttFiber61Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber61Key ttFiber61Expected (ttFiber61RowAt 6)
            (by decide) (by decide) (by decide) ttFiber61ReverseRow_6_ok)
      (by
        simpa [ttFiber61StateAt, ttFiber61RowAt, ttFiber61Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber61Key ttFiber61Expected (ttFiber61RowAt 7)
            (by decide) (by decide) (by decide) ttFiber61ReverseRow_7_ok)

def ttFiber62StateAt (i : Nat) : List TauState :=
  directStates (ttFiber62RowAt i).sourceLeft (ttFiber62RowAt i).sourceRight

def ttFiber62DirectStates : List (List TauState) :=
  [ ttFiber62StateAt 0, ttFiber62StateAt 1, ttFiber62StateAt 2, ttFiber62StateAt 3
  , ttFiber62StateAt 4, ttFiber62StateAt 5, ttFiber62StateAt 6, ttFiber62StateAt 7
  ]

theorem ttFiber62ReverseRow_1_ok :
    directRowReverseValid ttFiber62Key ttFiber62Expected (ttFiber62RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber62Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber62Chunk0] at h
  exact h.2

theorem ttFiber62ReverseRow_2_ok :
    directRowReverseValid ttFiber62Key ttFiber62Expected (ttFiber62RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber62Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber62Chunk1] at h
  exact h.1

theorem ttFiber62ReverseRow_3_ok :
    directRowReverseValid ttFiber62Key ttFiber62Expected (ttFiber62RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber62Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber62Chunk1] at h
  exact h.2

theorem ttFiber62ReverseRow_4_ok :
    directRowReverseValid ttFiber62Key ttFiber62Expected (ttFiber62RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber62Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber62Chunk2] at h
  exact h.1

theorem ttFiber62ReverseRow_5_ok :
    directRowReverseValid ttFiber62Key ttFiber62Expected (ttFiber62RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber62Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber62Chunk2] at h
  exact h.2

theorem ttFiber62ReverseRow_6_ok :
    directRowReverseValid ttFiber62Key ttFiber62Expected (ttFiber62RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber62Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber62Chunk3] at h
  exact h.1

theorem ttFiber62ReverseRow_7_ok :
    directRowReverseValid ttFiber62Key ttFiber62Expected (ttFiber62RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber62Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber62Chunk3] at h
  exact h.2

theorem ttFiber62DirectConnected :
    chainFiberConnected ttWord ttFiber62DirectStates = true := by
  simpa [ttFiber62DirectStates] using
    directConnected8ShapeB ttWord ttFiber62StateAt
      (by
        simpa [ttFiber62StateAt, ttFiber62RowAt, ttFiber62Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber62Key ttFiber62Expected (ttFiber62RowAt 1)
            (by decide) (by decide) (by decide) ttFiber62ReverseRow_1_ok)
      (by
        simpa [ttFiber62StateAt, ttFiber62RowAt, ttFiber62Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber62Key ttFiber62Expected (ttFiber62RowAt 2)
            (by decide) (by decide) (by decide) ttFiber62ReverseRow_2_ok)
      (by
        simpa [ttFiber62StateAt, ttFiber62RowAt, ttFiber62Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber62Key ttFiber62Expected (ttFiber62RowAt 3)
            (by decide) (by decide) (by decide) ttFiber62ReverseRow_3_ok)
      (by
        simpa [ttFiber62StateAt, ttFiber62RowAt, ttFiber62Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber62Key ttFiber62Expected (ttFiber62RowAt 4)
            (by decide) (by decide) (by decide) ttFiber62ReverseRow_4_ok)
      (by
        simpa [ttFiber62StateAt, ttFiber62RowAt, ttFiber62Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber62Key ttFiber62Expected (ttFiber62RowAt 5)
            (by decide) (by decide) (by decide) ttFiber62ReverseRow_5_ok)
      (by
        simpa [ttFiber62StateAt, ttFiber62RowAt, ttFiber62Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber62Key ttFiber62Expected (ttFiber62RowAt 6)
            (by decide) (by decide) (by decide) ttFiber62ReverseRow_6_ok)
      (by
        simpa [ttFiber62StateAt, ttFiber62RowAt, ttFiber62Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber62Key ttFiber62Expected (ttFiber62RowAt 7)
            (by decide) (by decide) (by decide) ttFiber62ReverseRow_7_ok)

def ttFiber73StateAt (i : Nat) : List TauState :=
  directStates (ttFiber73RowAt i).sourceLeft (ttFiber73RowAt i).sourceRight

def ttFiber73DirectStates : List (List TauState) :=
  [ ttFiber73StateAt 0, ttFiber73StateAt 1, ttFiber73StateAt 2, ttFiber73StateAt 3
  , ttFiber73StateAt 4, ttFiber73StateAt 5, ttFiber73StateAt 6, ttFiber73StateAt 7
  ]

theorem ttFiber73ReverseRow_1_ok :
    directRowReverseValid ttFiber73Key ttFiber73Expected (ttFiber73RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber73Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber73Chunk0] at h
  exact h.2

theorem ttFiber73ReverseRow_2_ok :
    directRowReverseValid ttFiber73Key ttFiber73Expected (ttFiber73RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber73Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber73Chunk1] at h
  exact h.1

theorem ttFiber73ReverseRow_3_ok :
    directRowReverseValid ttFiber73Key ttFiber73Expected (ttFiber73RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber73Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber73Chunk1] at h
  exact h.2

theorem ttFiber73ReverseRow_4_ok :
    directRowReverseValid ttFiber73Key ttFiber73Expected (ttFiber73RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber73Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber73Chunk2] at h
  exact h.1

theorem ttFiber73ReverseRow_5_ok :
    directRowReverseValid ttFiber73Key ttFiber73Expected (ttFiber73RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber73Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber73Chunk2] at h
  exact h.2

theorem ttFiber73ReverseRow_6_ok :
    directRowReverseValid ttFiber73Key ttFiber73Expected (ttFiber73RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber73Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber73Chunk3] at h
  exact h.1

theorem ttFiber73ReverseRow_7_ok :
    directRowReverseValid ttFiber73Key ttFiber73Expected (ttFiber73RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber73Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber73Chunk3] at h
  exact h.2

theorem ttFiber73DirectConnected :
    chainFiberConnected ttWord ttFiber73DirectStates = true := by
  simpa [ttFiber73DirectStates] using
    directConnected8ShapeB ttWord ttFiber73StateAt
      (by
        simpa [ttFiber73StateAt, ttFiber73RowAt, ttFiber73Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber73Key ttFiber73Expected (ttFiber73RowAt 1)
            (by decide) (by decide) (by decide) ttFiber73ReverseRow_1_ok)
      (by
        simpa [ttFiber73StateAt, ttFiber73RowAt, ttFiber73Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber73Key ttFiber73Expected (ttFiber73RowAt 2)
            (by decide) (by decide) (by decide) ttFiber73ReverseRow_2_ok)
      (by
        simpa [ttFiber73StateAt, ttFiber73RowAt, ttFiber73Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber73Key ttFiber73Expected (ttFiber73RowAt 3)
            (by decide) (by decide) (by decide) ttFiber73ReverseRow_3_ok)
      (by
        simpa [ttFiber73StateAt, ttFiber73RowAt, ttFiber73Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber73Key ttFiber73Expected (ttFiber73RowAt 4)
            (by decide) (by decide) (by decide) ttFiber73ReverseRow_4_ok)
      (by
        simpa [ttFiber73StateAt, ttFiber73RowAt, ttFiber73Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber73Key ttFiber73Expected (ttFiber73RowAt 5)
            (by decide) (by decide) (by decide) ttFiber73ReverseRow_5_ok)
      (by
        simpa [ttFiber73StateAt, ttFiber73RowAt, ttFiber73Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber73Key ttFiber73Expected (ttFiber73RowAt 6)
            (by decide) (by decide) (by decide) ttFiber73ReverseRow_6_ok)
      (by
        simpa [ttFiber73StateAt, ttFiber73RowAt, ttFiber73Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber73Key ttFiber73Expected (ttFiber73RowAt 7)
            (by decide) (by decide) (by decide) ttFiber73ReverseRow_7_ok)

def ttFiber74StateAt (i : Nat) : List TauState :=
  directStates (ttFiber74RowAt i).sourceLeft (ttFiber74RowAt i).sourceRight

def ttFiber74DirectStates : List (List TauState) :=
  [ ttFiber74StateAt 0, ttFiber74StateAt 1, ttFiber74StateAt 2, ttFiber74StateAt 3
  , ttFiber74StateAt 4, ttFiber74StateAt 5, ttFiber74StateAt 6, ttFiber74StateAt 7
  ]

theorem ttFiber74ReverseRow_1_ok :
    directRowReverseValid ttFiber74Key ttFiber74Expected (ttFiber74RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber74Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber74Chunk0] at h
  exact h.2

theorem ttFiber74ReverseRow_2_ok :
    directRowReverseValid ttFiber74Key ttFiber74Expected (ttFiber74RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber74Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber74Chunk1] at h
  exact h.1

theorem ttFiber74ReverseRow_3_ok :
    directRowReverseValid ttFiber74Key ttFiber74Expected (ttFiber74RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber74Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber74Chunk1] at h
  exact h.2

theorem ttFiber74ReverseRow_4_ok :
    directRowReverseValid ttFiber74Key ttFiber74Expected (ttFiber74RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber74Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber74Chunk2] at h
  exact h.1

theorem ttFiber74ReverseRow_5_ok :
    directRowReverseValid ttFiber74Key ttFiber74Expected (ttFiber74RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber74Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber74Chunk2] at h
  exact h.2

theorem ttFiber74ReverseRow_6_ok :
    directRowReverseValid ttFiber74Key ttFiber74Expected (ttFiber74RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber74Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber74Chunk3] at h
  exact h.1

theorem ttFiber74ReverseRow_7_ok :
    directRowReverseValid ttFiber74Key ttFiber74Expected (ttFiber74RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber74Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber74Chunk3] at h
  exact h.2

theorem ttFiber74DirectConnected :
    chainFiberConnected ttWord ttFiber74DirectStates = true := by
  simpa [ttFiber74DirectStates] using
    directConnected8ShapeB ttWord ttFiber74StateAt
      (by
        simpa [ttFiber74StateAt, ttFiber74RowAt, ttFiber74Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber74Key ttFiber74Expected (ttFiber74RowAt 1)
            (by decide) (by decide) (by decide) ttFiber74ReverseRow_1_ok)
      (by
        simpa [ttFiber74StateAt, ttFiber74RowAt, ttFiber74Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber74Key ttFiber74Expected (ttFiber74RowAt 2)
            (by decide) (by decide) (by decide) ttFiber74ReverseRow_2_ok)
      (by
        simpa [ttFiber74StateAt, ttFiber74RowAt, ttFiber74Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber74Key ttFiber74Expected (ttFiber74RowAt 3)
            (by decide) (by decide) (by decide) ttFiber74ReverseRow_3_ok)
      (by
        simpa [ttFiber74StateAt, ttFiber74RowAt, ttFiber74Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber74Key ttFiber74Expected (ttFiber74RowAt 4)
            (by decide) (by decide) (by decide) ttFiber74ReverseRow_4_ok)
      (by
        simpa [ttFiber74StateAt, ttFiber74RowAt, ttFiber74Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber74Key ttFiber74Expected (ttFiber74RowAt 5)
            (by decide) (by decide) (by decide) ttFiber74ReverseRow_5_ok)
      (by
        simpa [ttFiber74StateAt, ttFiber74RowAt, ttFiber74Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber74Key ttFiber74Expected (ttFiber74RowAt 6)
            (by decide) (by decide) (by decide) ttFiber74ReverseRow_6_ok)
      (by
        simpa [ttFiber74StateAt, ttFiber74RowAt, ttFiber74Rows, listGetD, directRow] using
          directReverseSingleStepOfRow ttFiber74Key ttFiber74Expected (ttFiber74RowAt 7)
            (by decide) (by decide) (by decide) ttFiber74ReverseRow_7_ok)

end GoertzelLemma818LengthTwoShapeBBridge

end Mettapedia.GraphTheory.FourColor
