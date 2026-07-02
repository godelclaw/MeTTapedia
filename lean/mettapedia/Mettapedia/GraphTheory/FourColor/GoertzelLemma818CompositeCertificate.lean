import Mettapedia.GraphTheory.FourColor.GoertzelLemma814

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: generated `tau,tau` composite certificate

This file checks the generated direct parent/path table for all 81 fixed-input
keys of the two-gadget `tau,tau` composite: 36 nonempty fibers, 960 generated
states, and parent depth at most 4.  The checks are row-split so Lean never
reduces one monolithic closure search.  The remaining 8.18/8.19 bridge is the
frontier/DFA consequence for all chains, not this base `tau,tau` table.
-/

namespace GoertzelLemma818CompositeCertificate

open GoertzelLemma814

def ttWord : List TauOrient :=
  [TauOrient.normal, TauOrient.normal]

structure DirectChainParentRow where
  source : Nat
  parent : Nat
  sourceLeft : Nat
  sourceRight : Nat
  parentLeft : Nat
  parentRight : Nat
  move : ChainMove
  deriving DecidableEq, BEq, Repr, Inhabited

def directRow (source parent sourceLeft sourceRight parentLeft parentRight : Nat)
    (move : ChainMove) : DirectChainParentRow :=
  { source := source, parent := parent, sourceLeft := sourceLeft,
    sourceRight := sourceRight, parentLeft := parentLeft,
    parentRight := parentRight, move := move }

def directStates (left right : Nat) : List TauState :=
  [stateAt left, stateAt right]

def directChainFiberRow (row : DirectChainParentRow) : ChainFiberParentRow :=
  { source := row.source, parent := row.parent, move := row.move }

def directChainFiberRoot : List DirectChainParentRow → Nat
  | [] => 0
  | row :: _ => row.source

def directChainFiberCertificate (key : List LColor) (maxDepth : Nat)
    (rows : List DirectChainParentRow) : ChainFiberCertificate :=
  { key := key
    root := directChainFiberRoot rows
    maxDepth := maxDepth
    rows := rows.map directChainFiberRow }

def directParentFromRows : List DirectChainParentRow → Nat → Nat
  | [], i => i
  | row :: rows, i =>
      if row.source == i then row.parent else directParentFromRows rows i

def directParentIter (rows : List DirectChainParentRow) : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i => directParentIter rows n (directParentFromRows rows i)

def directRowValid (key : List LColor) (expected : List Nat)
    (row : DirectChainParentRow) : Bool :=
  expected.contains row.source && expected.contains row.parent &&
    let s := directStates row.sourceLeft row.sourceRight
    let t := directStates row.parentLeft row.parentRight
    compatibleChainStates ttWord s && compatibleChainStates ttWord t &&
      chainInputKey ttWord s == key && chainInputKey ttWord t == key &&
        (row.source == row.parent || chainSpecifiedKempeStep ttWord s t row.move)

/--
Reverse-direction row check for the parent-tree certificates.

The generated rows point from a source state toward its parent.  A real
`chainFiberConnected` proof grows the closure from the root outward, so a
parent row also needs the reverse Kempe step from parent to source.  This
checker records that missing direction as a small, row-local condition.
-/
def directRowReverseValid (key : List LColor) (expected : List Nat)
    (row : DirectChainParentRow) : Bool :=
  expected.contains row.source && expected.contains row.parent &&
    let s := directStates row.sourceLeft row.sourceRight
    let t := directStates row.parentLeft row.parentRight
    compatibleChainStates ttWord s && compatibleChainStates ttWord t &&
      chainInputKey ttWord s == key && chainInputKey ttWord t == key &&
        (row.source == row.parent || chainSpecifiedKempeStep ttWord t s row.move)

theorem directRowReverseValid_step_of_ne (key : List LColor) (expected : List Nat)
    (row : DirectChainParentRow) (hne : row.source ≠ row.parent)
    (h : directRowReverseValid key expected row = true) :
    chainSpecifiedKempeStep ttWord
      (directStates row.parentLeft row.parentRight)
      (directStates row.sourceLeft row.sourceRight) row.move = true := by
  simp [directRowReverseValid] at h
  rcases h with ⟨_, hrest⟩
  rcases hrest.2 with heq | hstep
  · exact False.elim (hne heq)
  · exact hstep

def directRowsReverseAudit (key : List LColor) (expected : List Nat)
    (rows : List DirectChainParentRow) : Bool :=
  rows.all (directRowReverseValid key expected)

def ttNonemptyFiberCount : Nat := 36
def ttCompositeStateCount : Nat := 960
def ttMaxParentDepth : Nat := 4

def ttFiber0Key : List LColor :=
  [LColor.r, LColor.r, LColor.r, LColor.r]

def ttFiber0Expected : List Nat :=
  []

def ttFiber0Rows : List DirectChainParentRow :=
  []

def ttFiber0RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber0Rows i default

def ttFiber0SourcesCheck : Bool :=
  (ttFiber0Rows.map fun row => row.source) == ttFiber0Expected

theorem ttFiber0SourcesCheck_ok :
    ttFiber0SourcesCheck = true := by
  decide

def ttFiber0RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber0Key ttFiber0Expected (ttFiber0RowAt i)

def ttFiber0ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber0Rows ttMaxParentDepth (listGetD ttFiber0Expected i 0) == 0

def ttFiber0CertificateAudit : Bool :=
  ttFiber0SourcesCheck

theorem ttFiber0CertificateAudit_ok :
    ttFiber0CertificateAudit = true := by
  simp [ttFiber0CertificateAudit,
    ttFiber0SourcesCheck_ok]

def ttFiber1Key : List LColor :=
  [LColor.r, LColor.r, LColor.r, LColor.b]

def ttFiber1Expected : List Nat :=
  []

def ttFiber1Rows : List DirectChainParentRow :=
  []

def ttFiber1RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber1Rows i default

def ttFiber1SourcesCheck : Bool :=
  (ttFiber1Rows.map fun row => row.source) == ttFiber1Expected

theorem ttFiber1SourcesCheck_ok :
    ttFiber1SourcesCheck = true := by
  decide

def ttFiber1RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber1Key ttFiber1Expected (ttFiber1RowAt i)

def ttFiber1ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber1Rows ttMaxParentDepth (listGetD ttFiber1Expected i 0) == 0

def ttFiber1CertificateAudit : Bool :=
  ttFiber1SourcesCheck

theorem ttFiber1CertificateAudit_ok :
    ttFiber1CertificateAudit = true := by
  simp [ttFiber1CertificateAudit,
    ttFiber1SourcesCheck_ok]

def ttFiber2Key : List LColor :=
  [LColor.r, LColor.r, LColor.r, LColor.p]

def ttFiber2Expected : List Nat :=
  []

def ttFiber2Rows : List DirectChainParentRow :=
  []

def ttFiber2RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber2Rows i default

def ttFiber2SourcesCheck : Bool :=
  (ttFiber2Rows.map fun row => row.source) == ttFiber2Expected

theorem ttFiber2SourcesCheck_ok :
    ttFiber2SourcesCheck = true := by
  decide

def ttFiber2RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber2Key ttFiber2Expected (ttFiber2RowAt i)

def ttFiber2ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber2Rows ttMaxParentDepth (listGetD ttFiber2Expected i 0) == 0

def ttFiber2CertificateAudit : Bool :=
  ttFiber2SourcesCheck

theorem ttFiber2CertificateAudit_ok :
    ttFiber2CertificateAudit = true := by
  simp [ttFiber2CertificateAudit,
    ttFiber2SourcesCheck_ok]

def ttFiber3Key : List LColor :=
  [LColor.r, LColor.r, LColor.b, LColor.r]

def ttFiber3Expected : List Nat :=
  [560, 561, 562, 563, 564, 565, 566, 567]

def ttFiber3Rows : List DirectChainParentRow :=
  [ directRow 560 560 114 52 114 52 default
  , directRow 561 560 114 53 114 52 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 562 561 114 54 114 53 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 563 560 114 55 114 52 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 564 560 115 60 114 52 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 565 561 115 61 114 53 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 566 562 115 62 114 54 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 567 563 115 63 114 55 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  ]

def ttFiber3RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber3Rows i default

def ttFiber3SourcesCheck : Bool :=
  (ttFiber3Rows.map fun row => row.source) == ttFiber3Expected

theorem ttFiber3SourcesCheck_ok :
    ttFiber3SourcesCheck = true := by
  decide

def ttFiber3RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber3Key ttFiber3Expected (ttFiber3RowAt i)

theorem ttFiber3Row_0_ok : ttFiber3RowCheck 0 = true := by decide
theorem ttFiber3Row_1_ok : ttFiber3RowCheck 1 = true := by decide
theorem ttFiber3Row_2_ok : ttFiber3RowCheck 2 = true := by decide
theorem ttFiber3Row_3_ok : ttFiber3RowCheck 3 = true := by decide
theorem ttFiber3Row_4_ok : ttFiber3RowCheck 4 = true := by decide
theorem ttFiber3Row_5_ok : ttFiber3RowCheck 5 = true := by decide
theorem ttFiber3Row_6_ok : ttFiber3RowCheck 6 = true := by decide
theorem ttFiber3Row_7_ok : ttFiber3RowCheck 7 = true := by decide

def ttFiber3ReverseRowCheck (i : Nat) : Bool :=
  directRowReverseValid ttFiber3Key ttFiber3Expected (ttFiber3RowAt i)

theorem ttFiber3ReverseRow_0_ok : ttFiber3ReverseRowCheck 0 = true := by decide
theorem ttFiber3ReverseRow_1_ok : ttFiber3ReverseRowCheck 1 = true := by decide
theorem ttFiber3ReverseRow_2_ok : ttFiber3ReverseRowCheck 2 = true := by decide
theorem ttFiber3ReverseRow_3_ok : ttFiber3ReverseRowCheck 3 = true := by decide
theorem ttFiber3ReverseRow_4_ok : ttFiber3ReverseRowCheck 4 = true := by decide
theorem ttFiber3ReverseRow_5_ok : ttFiber3ReverseRowCheck 5 = true := by decide
theorem ttFiber3ReverseRow_6_ok : ttFiber3ReverseRowCheck 6 = true := by decide
theorem ttFiber3ReverseRow_7_ok : ttFiber3ReverseRowCheck 7 = true := by decide

def ttFiber3ReverseCertificateAudit : Bool :=
  ttFiber3ReverseRowCheck 0 &&
    ttFiber3ReverseRowCheck 1 &&
    ttFiber3ReverseRowCheck 2 &&
    ttFiber3ReverseRowCheck 3 &&
    ttFiber3ReverseRowCheck 4 &&
    ttFiber3ReverseRowCheck 5 &&
    ttFiber3ReverseRowCheck 6 &&
    ttFiber3ReverseRowCheck 7

theorem ttFiber3ReverseCertificateAudit_ok :
    ttFiber3ReverseCertificateAudit = true := by
  simp [ttFiber3ReverseCertificateAudit,
    ttFiber3ReverseRow_0_ok,
    ttFiber3ReverseRow_1_ok,
    ttFiber3ReverseRow_2_ok,
    ttFiber3ReverseRow_3_ok,
    ttFiber3ReverseRow_4_ok,
    ttFiber3ReverseRow_5_ok,
    ttFiber3ReverseRow_6_ok,
    ttFiber3ReverseRow_7_ok]

def ttFiber3ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber3Rows ttMaxParentDepth (listGetD ttFiber3Expected i 0) == 560

theorem ttFiber3Parent_0_ok : ttFiber3ParentCheck 0 = true := by decide
theorem ttFiber3Parent_1_ok : ttFiber3ParentCheck 1 = true := by decide
theorem ttFiber3Parent_2_ok : ttFiber3ParentCheck 2 = true := by decide
theorem ttFiber3Parent_3_ok : ttFiber3ParentCheck 3 = true := by decide
theorem ttFiber3Parent_4_ok : ttFiber3ParentCheck 4 = true := by decide
theorem ttFiber3Parent_5_ok : ttFiber3ParentCheck 5 = true := by decide
theorem ttFiber3Parent_6_ok : ttFiber3ParentCheck 6 = true := by decide
theorem ttFiber3Parent_7_ok : ttFiber3ParentCheck 7 = true := by decide

def ttFiber3CertificateAudit : Bool :=
  ttFiber3SourcesCheck &&
    ttFiber3RowCheck 0 &&
    ttFiber3RowCheck 1 &&
    ttFiber3RowCheck 2 &&
    ttFiber3RowCheck 3 &&
    ttFiber3RowCheck 4 &&
    ttFiber3RowCheck 5 &&
    ttFiber3RowCheck 6 &&
    ttFiber3RowCheck 7 &&
    ttFiber3ParentCheck 0 &&
    ttFiber3ParentCheck 1 &&
    ttFiber3ParentCheck 2 &&
    ttFiber3ParentCheck 3 &&
    ttFiber3ParentCheck 4 &&
    ttFiber3ParentCheck 5 &&
    ttFiber3ParentCheck 6 &&
    ttFiber3ParentCheck 7

theorem ttFiber3CertificateAudit_ok :
    ttFiber3CertificateAudit = true := by
  simp [ttFiber3CertificateAudit,
    ttFiber3SourcesCheck_ok,
    ttFiber3Row_0_ok,
    ttFiber3Row_1_ok,
    ttFiber3Row_2_ok,
    ttFiber3Row_3_ok,
    ttFiber3Row_4_ok,
    ttFiber3Row_5_ok,
    ttFiber3Row_6_ok,
    ttFiber3Row_7_ok,
    ttFiber3Parent_0_ok,
    ttFiber3Parent_1_ok,
    ttFiber3Parent_2_ok,
    ttFiber3Parent_3_ok,
    ttFiber3Parent_4_ok,
    ttFiber3Parent_5_ok,
    ttFiber3Parent_6_ok,
    ttFiber3Parent_7_ok]

def ttFiber4Key : List LColor :=
  [LColor.r, LColor.r, LColor.b, LColor.b]

def ttFiber4Expected : List Nat :=
  [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 568, 569, 570, 571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599]

def ttFiber4Rows : List DirectChainParentRow :=
  [ directRow 320 320 64 80 64 80 default
  , directRow 321 320 64 81 64 80 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 322 320 64 82 64 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 323 321 64 83 64 81 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 324 322 64 100 64 82 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 325 327 64 101 64 103 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 326 321 64 102 64 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 327 320 64 103 64 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 328 320 65 88 64 80 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 329 321 65 89 64 81 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 330 322 65 90 64 82 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 331 323 65 91 64 83 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 332 324 65 108 64 100 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 333 325 65 109 64 101 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 334 326 65 110 64 102 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 335 327 65 111 64 103 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 336 320 66 16 64 80 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 337 321 66 17 64 81 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 338 322 66 18 64 82 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 339 323 66 19 64 83 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 340 336 66 32 66 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 341 337 66 33 66 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 342 326 66 34 64 102 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 343 327 66 35 64 103 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 344 328 67 24 65 88 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 345 329 67 25 65 89 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 346 330 67 26 65 90 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 347 331 67 27 65 91 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 348 344 67 40 67 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 349 345 67 41 67 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 350 334 67 42 65 110 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 351 335 67 43 65 111 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 568 584 116 132 118 64 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 569 585 116 133 118 65 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 570 342 116 134 66 34 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 571 343 116 135 66 35 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 572 338 116 180 66 18 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 573 575 116 181 116 183 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 574 337 116 182 66 17 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 575 336 116 183 66 16 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 576 592 117 140 119 72 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 577 593 117 141 119 73 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 578 594 117 142 119 74 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 579 576 117 143 117 140 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 580 576 117 188 117 140 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 581 577 117 189 117 141 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 582 598 117 190 119 126 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 583 599 117 191 119 127 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 584 328 118 64 65 88 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 585 329 118 65 65 89 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 586 330 118 66 65 90 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 587 331 118 67 65 91 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 588 332 118 116 65 108 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 589 333 118 117 65 109 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 590 334 118 118 65 110 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 591 335 118 119 65 111 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 592 320 119 72 64 80 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 593 321 119 73 64 81 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 594 322 119 74 64 82 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 595 323 119 75 64 83 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 596 324 119 124 64 100 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 597 325 119 125 64 101 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 598 326 119 126 64 102 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 599 327 119 127 64 103 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  ]

def ttFiber4RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber4Rows i default

def ttFiber4SourcesCheck : Bool :=
  (ttFiber4Rows.map fun row => row.source) == ttFiber4Expected

theorem ttFiber4SourcesCheck_ok :
    ttFiber4SourcesCheck = true := by
  decide

def ttFiber4RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt i)

theorem ttFiber4Row_0_ok : ttFiber4RowCheck 0 = true := by decide
theorem ttFiber4Row_1_ok : ttFiber4RowCheck 1 = true := by decide
theorem ttFiber4Row_2_ok : ttFiber4RowCheck 2 = true := by decide
theorem ttFiber4Row_3_ok : ttFiber4RowCheck 3 = true := by decide
theorem ttFiber4Row_4_ok : ttFiber4RowCheck 4 = true := by decide
theorem ttFiber4Row_5_ok : ttFiber4RowCheck 5 = true := by decide
theorem ttFiber4Row_6_ok : ttFiber4RowCheck 6 = true := by decide
theorem ttFiber4Row_7_ok : ttFiber4RowCheck 7 = true := by decide
theorem ttFiber4Row_8_ok : ttFiber4RowCheck 8 = true := by decide
theorem ttFiber4Row_9_ok : ttFiber4RowCheck 9 = true := by decide
theorem ttFiber4Row_10_ok : ttFiber4RowCheck 10 = true := by decide
theorem ttFiber4Row_11_ok : ttFiber4RowCheck 11 = true := by decide
theorem ttFiber4Row_12_ok : ttFiber4RowCheck 12 = true := by decide
theorem ttFiber4Row_13_ok : ttFiber4RowCheck 13 = true := by decide
theorem ttFiber4Row_14_ok : ttFiber4RowCheck 14 = true := by decide
theorem ttFiber4Row_15_ok : ttFiber4RowCheck 15 = true := by decide
theorem ttFiber4Row_16_ok : ttFiber4RowCheck 16 = true := by decide
theorem ttFiber4Row_17_ok : ttFiber4RowCheck 17 = true := by decide
theorem ttFiber4Row_18_ok : ttFiber4RowCheck 18 = true := by decide
theorem ttFiber4Row_19_ok : ttFiber4RowCheck 19 = true := by decide
theorem ttFiber4Row_20_ok : ttFiber4RowCheck 20 = true := by decide
theorem ttFiber4Row_21_ok : ttFiber4RowCheck 21 = true := by decide
theorem ttFiber4Row_22_ok : ttFiber4RowCheck 22 = true := by decide
theorem ttFiber4Row_23_ok : ttFiber4RowCheck 23 = true := by decide
theorem ttFiber4Row_24_ok : ttFiber4RowCheck 24 = true := by decide
theorem ttFiber4Row_25_ok : ttFiber4RowCheck 25 = true := by decide
theorem ttFiber4Row_26_ok : ttFiber4RowCheck 26 = true := by decide
theorem ttFiber4Row_27_ok : ttFiber4RowCheck 27 = true := by decide
theorem ttFiber4Row_28_ok : ttFiber4RowCheck 28 = true := by decide
theorem ttFiber4Row_29_ok : ttFiber4RowCheck 29 = true := by decide
theorem ttFiber4Row_30_ok : ttFiber4RowCheck 30 = true := by decide
theorem ttFiber4Row_31_ok : ttFiber4RowCheck 31 = true := by decide
theorem ttFiber4Row_32_ok : ttFiber4RowCheck 32 = true := by decide
theorem ttFiber4Row_33_ok : ttFiber4RowCheck 33 = true := by decide
theorem ttFiber4Row_34_ok : ttFiber4RowCheck 34 = true := by decide
theorem ttFiber4Row_35_ok : ttFiber4RowCheck 35 = true := by decide
theorem ttFiber4Row_36_ok : ttFiber4RowCheck 36 = true := by decide
theorem ttFiber4Row_37_ok : ttFiber4RowCheck 37 = true := by decide
theorem ttFiber4Row_38_ok : ttFiber4RowCheck 38 = true := by decide
theorem ttFiber4Row_39_ok : ttFiber4RowCheck 39 = true := by decide
theorem ttFiber4Row_40_ok : ttFiber4RowCheck 40 = true := by decide
theorem ttFiber4Row_41_ok : ttFiber4RowCheck 41 = true := by decide
theorem ttFiber4Row_42_ok : ttFiber4RowCheck 42 = true := by decide
theorem ttFiber4Row_43_ok : ttFiber4RowCheck 43 = true := by decide
theorem ttFiber4Row_44_ok : ttFiber4RowCheck 44 = true := by decide
theorem ttFiber4Row_45_ok : ttFiber4RowCheck 45 = true := by decide
theorem ttFiber4Row_46_ok : ttFiber4RowCheck 46 = true := by decide
theorem ttFiber4Row_47_ok : ttFiber4RowCheck 47 = true := by decide
theorem ttFiber4Row_48_ok : ttFiber4RowCheck 48 = true := by decide
theorem ttFiber4Row_49_ok : ttFiber4RowCheck 49 = true := by decide
theorem ttFiber4Row_50_ok : ttFiber4RowCheck 50 = true := by decide
theorem ttFiber4Row_51_ok : ttFiber4RowCheck 51 = true := by decide
theorem ttFiber4Row_52_ok : ttFiber4RowCheck 52 = true := by decide
theorem ttFiber4Row_53_ok : ttFiber4RowCheck 53 = true := by decide
theorem ttFiber4Row_54_ok : ttFiber4RowCheck 54 = true := by decide
theorem ttFiber4Row_55_ok : ttFiber4RowCheck 55 = true := by decide
theorem ttFiber4Row_56_ok : ttFiber4RowCheck 56 = true := by decide
theorem ttFiber4Row_57_ok : ttFiber4RowCheck 57 = true := by decide
theorem ttFiber4Row_58_ok : ttFiber4RowCheck 58 = true := by decide
theorem ttFiber4Row_59_ok : ttFiber4RowCheck 59 = true := by decide
theorem ttFiber4Row_60_ok : ttFiber4RowCheck 60 = true := by decide
theorem ttFiber4Row_61_ok : ttFiber4RowCheck 61 = true := by decide
theorem ttFiber4Row_62_ok : ttFiber4RowCheck 62 = true := by decide
theorem ttFiber4Row_63_ok : ttFiber4RowCheck 63 = true := by decide

def ttFiber4ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber4Rows ttMaxParentDepth (listGetD ttFiber4Expected i 0) == 320

theorem ttFiber4Parent_0_ok : ttFiber4ParentCheck 0 = true := by decide
theorem ttFiber4Parent_1_ok : ttFiber4ParentCheck 1 = true := by decide
theorem ttFiber4Parent_2_ok : ttFiber4ParentCheck 2 = true := by decide
theorem ttFiber4Parent_3_ok : ttFiber4ParentCheck 3 = true := by decide
theorem ttFiber4Parent_4_ok : ttFiber4ParentCheck 4 = true := by decide
theorem ttFiber4Parent_5_ok : ttFiber4ParentCheck 5 = true := by decide
theorem ttFiber4Parent_6_ok : ttFiber4ParentCheck 6 = true := by decide
theorem ttFiber4Parent_7_ok : ttFiber4ParentCheck 7 = true := by decide
theorem ttFiber4Parent_8_ok : ttFiber4ParentCheck 8 = true := by decide
theorem ttFiber4Parent_9_ok : ttFiber4ParentCheck 9 = true := by decide
theorem ttFiber4Parent_10_ok : ttFiber4ParentCheck 10 = true := by decide
theorem ttFiber4Parent_11_ok : ttFiber4ParentCheck 11 = true := by decide
theorem ttFiber4Parent_12_ok : ttFiber4ParentCheck 12 = true := by decide
theorem ttFiber4Parent_13_ok : ttFiber4ParentCheck 13 = true := by decide
theorem ttFiber4Parent_14_ok : ttFiber4ParentCheck 14 = true := by decide
theorem ttFiber4Parent_15_ok : ttFiber4ParentCheck 15 = true := by decide
theorem ttFiber4Parent_16_ok : ttFiber4ParentCheck 16 = true := by decide
theorem ttFiber4Parent_17_ok : ttFiber4ParentCheck 17 = true := by decide
theorem ttFiber4Parent_18_ok : ttFiber4ParentCheck 18 = true := by decide
theorem ttFiber4Parent_19_ok : ttFiber4ParentCheck 19 = true := by decide
theorem ttFiber4Parent_20_ok : ttFiber4ParentCheck 20 = true := by decide
theorem ttFiber4Parent_21_ok : ttFiber4ParentCheck 21 = true := by decide
theorem ttFiber4Parent_22_ok : ttFiber4ParentCheck 22 = true := by decide
theorem ttFiber4Parent_23_ok : ttFiber4ParentCheck 23 = true := by decide
theorem ttFiber4Parent_24_ok : ttFiber4ParentCheck 24 = true := by decide
theorem ttFiber4Parent_25_ok : ttFiber4ParentCheck 25 = true := by decide
theorem ttFiber4Parent_26_ok : ttFiber4ParentCheck 26 = true := by decide
theorem ttFiber4Parent_27_ok : ttFiber4ParentCheck 27 = true := by decide
theorem ttFiber4Parent_28_ok : ttFiber4ParentCheck 28 = true := by decide
theorem ttFiber4Parent_29_ok : ttFiber4ParentCheck 29 = true := by decide
theorem ttFiber4Parent_30_ok : ttFiber4ParentCheck 30 = true := by decide
theorem ttFiber4Parent_31_ok : ttFiber4ParentCheck 31 = true := by decide
theorem ttFiber4Parent_32_ok : ttFiber4ParentCheck 32 = true := by decide
theorem ttFiber4Parent_33_ok : ttFiber4ParentCheck 33 = true := by decide
theorem ttFiber4Parent_34_ok : ttFiber4ParentCheck 34 = true := by decide
theorem ttFiber4Parent_35_ok : ttFiber4ParentCheck 35 = true := by decide
theorem ttFiber4Parent_36_ok : ttFiber4ParentCheck 36 = true := by decide
theorem ttFiber4Parent_37_ok : ttFiber4ParentCheck 37 = true := by decide
theorem ttFiber4Parent_38_ok : ttFiber4ParentCheck 38 = true := by decide
theorem ttFiber4Parent_39_ok : ttFiber4ParentCheck 39 = true := by decide
theorem ttFiber4Parent_40_ok : ttFiber4ParentCheck 40 = true := by decide
theorem ttFiber4Parent_41_ok : ttFiber4ParentCheck 41 = true := by decide
theorem ttFiber4Parent_42_ok : ttFiber4ParentCheck 42 = true := by decide
theorem ttFiber4Parent_43_ok : ttFiber4ParentCheck 43 = true := by decide
theorem ttFiber4Parent_44_ok : ttFiber4ParentCheck 44 = true := by decide
theorem ttFiber4Parent_45_ok : ttFiber4ParentCheck 45 = true := by decide
theorem ttFiber4Parent_46_ok : ttFiber4ParentCheck 46 = true := by decide
theorem ttFiber4Parent_47_ok : ttFiber4ParentCheck 47 = true := by decide
theorem ttFiber4Parent_48_ok : ttFiber4ParentCheck 48 = true := by decide
theorem ttFiber4Parent_49_ok : ttFiber4ParentCheck 49 = true := by decide
theorem ttFiber4Parent_50_ok : ttFiber4ParentCheck 50 = true := by decide
theorem ttFiber4Parent_51_ok : ttFiber4ParentCheck 51 = true := by decide
theorem ttFiber4Parent_52_ok : ttFiber4ParentCheck 52 = true := by decide
theorem ttFiber4Parent_53_ok : ttFiber4ParentCheck 53 = true := by decide
theorem ttFiber4Parent_54_ok : ttFiber4ParentCheck 54 = true := by decide
theorem ttFiber4Parent_55_ok : ttFiber4ParentCheck 55 = true := by decide
theorem ttFiber4Parent_56_ok : ttFiber4ParentCheck 56 = true := by decide
theorem ttFiber4Parent_57_ok : ttFiber4ParentCheck 57 = true := by decide
theorem ttFiber4Parent_58_ok : ttFiber4ParentCheck 58 = true := by decide
theorem ttFiber4Parent_59_ok : ttFiber4ParentCheck 59 = true := by decide
theorem ttFiber4Parent_60_ok : ttFiber4ParentCheck 60 = true := by decide
theorem ttFiber4Parent_61_ok : ttFiber4ParentCheck 61 = true := by decide
theorem ttFiber4Parent_62_ok : ttFiber4ParentCheck 62 = true := by decide
theorem ttFiber4Parent_63_ok : ttFiber4ParentCheck 63 = true := by decide

def ttFiber4CertificateAudit : Bool :=
  ttFiber4SourcesCheck &&
    ttFiber4RowCheck 0 &&
    ttFiber4RowCheck 1 &&
    ttFiber4RowCheck 2 &&
    ttFiber4RowCheck 3 &&
    ttFiber4RowCheck 4 &&
    ttFiber4RowCheck 5 &&
    ttFiber4RowCheck 6 &&
    ttFiber4RowCheck 7 &&
    ttFiber4RowCheck 8 &&
    ttFiber4RowCheck 9 &&
    ttFiber4RowCheck 10 &&
    ttFiber4RowCheck 11 &&
    ttFiber4RowCheck 12 &&
    ttFiber4RowCheck 13 &&
    ttFiber4RowCheck 14 &&
    ttFiber4RowCheck 15 &&
    ttFiber4RowCheck 16 &&
    ttFiber4RowCheck 17 &&
    ttFiber4RowCheck 18 &&
    ttFiber4RowCheck 19 &&
    ttFiber4RowCheck 20 &&
    ttFiber4RowCheck 21 &&
    ttFiber4RowCheck 22 &&
    ttFiber4RowCheck 23 &&
    ttFiber4RowCheck 24 &&
    ttFiber4RowCheck 25 &&
    ttFiber4RowCheck 26 &&
    ttFiber4RowCheck 27 &&
    ttFiber4RowCheck 28 &&
    ttFiber4RowCheck 29 &&
    ttFiber4RowCheck 30 &&
    ttFiber4RowCheck 31 &&
    ttFiber4RowCheck 32 &&
    ttFiber4RowCheck 33 &&
    ttFiber4RowCheck 34 &&
    ttFiber4RowCheck 35 &&
    ttFiber4RowCheck 36 &&
    ttFiber4RowCheck 37 &&
    ttFiber4RowCheck 38 &&
    ttFiber4RowCheck 39 &&
    ttFiber4RowCheck 40 &&
    ttFiber4RowCheck 41 &&
    ttFiber4RowCheck 42 &&
    ttFiber4RowCheck 43 &&
    ttFiber4RowCheck 44 &&
    ttFiber4RowCheck 45 &&
    ttFiber4RowCheck 46 &&
    ttFiber4RowCheck 47 &&
    ttFiber4RowCheck 48 &&
    ttFiber4RowCheck 49 &&
    ttFiber4RowCheck 50 &&
    ttFiber4RowCheck 51 &&
    ttFiber4RowCheck 52 &&
    ttFiber4RowCheck 53 &&
    ttFiber4RowCheck 54 &&
    ttFiber4RowCheck 55 &&
    ttFiber4RowCheck 56 &&
    ttFiber4RowCheck 57 &&
    ttFiber4RowCheck 58 &&
    ttFiber4RowCheck 59 &&
    ttFiber4RowCheck 60 &&
    ttFiber4RowCheck 61 &&
    ttFiber4RowCheck 62 &&
    ttFiber4RowCheck 63 &&
    ttFiber4ParentCheck 0 &&
    ttFiber4ParentCheck 1 &&
    ttFiber4ParentCheck 2 &&
    ttFiber4ParentCheck 3 &&
    ttFiber4ParentCheck 4 &&
    ttFiber4ParentCheck 5 &&
    ttFiber4ParentCheck 6 &&
    ttFiber4ParentCheck 7 &&
    ttFiber4ParentCheck 8 &&
    ttFiber4ParentCheck 9 &&
    ttFiber4ParentCheck 10 &&
    ttFiber4ParentCheck 11 &&
    ttFiber4ParentCheck 12 &&
    ttFiber4ParentCheck 13 &&
    ttFiber4ParentCheck 14 &&
    ttFiber4ParentCheck 15 &&
    ttFiber4ParentCheck 16 &&
    ttFiber4ParentCheck 17 &&
    ttFiber4ParentCheck 18 &&
    ttFiber4ParentCheck 19 &&
    ttFiber4ParentCheck 20 &&
    ttFiber4ParentCheck 21 &&
    ttFiber4ParentCheck 22 &&
    ttFiber4ParentCheck 23 &&
    ttFiber4ParentCheck 24 &&
    ttFiber4ParentCheck 25 &&
    ttFiber4ParentCheck 26 &&
    ttFiber4ParentCheck 27 &&
    ttFiber4ParentCheck 28 &&
    ttFiber4ParentCheck 29 &&
    ttFiber4ParentCheck 30 &&
    ttFiber4ParentCheck 31 &&
    ttFiber4ParentCheck 32 &&
    ttFiber4ParentCheck 33 &&
    ttFiber4ParentCheck 34 &&
    ttFiber4ParentCheck 35 &&
    ttFiber4ParentCheck 36 &&
    ttFiber4ParentCheck 37 &&
    ttFiber4ParentCheck 38 &&
    ttFiber4ParentCheck 39 &&
    ttFiber4ParentCheck 40 &&
    ttFiber4ParentCheck 41 &&
    ttFiber4ParentCheck 42 &&
    ttFiber4ParentCheck 43 &&
    ttFiber4ParentCheck 44 &&
    ttFiber4ParentCheck 45 &&
    ttFiber4ParentCheck 46 &&
    ttFiber4ParentCheck 47 &&
    ttFiber4ParentCheck 48 &&
    ttFiber4ParentCheck 49 &&
    ttFiber4ParentCheck 50 &&
    ttFiber4ParentCheck 51 &&
    ttFiber4ParentCheck 52 &&
    ttFiber4ParentCheck 53 &&
    ttFiber4ParentCheck 54 &&
    ttFiber4ParentCheck 55 &&
    ttFiber4ParentCheck 56 &&
    ttFiber4ParentCheck 57 &&
    ttFiber4ParentCheck 58 &&
    ttFiber4ParentCheck 59 &&
    ttFiber4ParentCheck 60 &&
    ttFiber4ParentCheck 61 &&
    ttFiber4ParentCheck 62 &&
    ttFiber4ParentCheck 63

theorem ttFiber4CertificateAudit_ok :
    ttFiber4CertificateAudit = true := by
  simp [ttFiber4CertificateAudit,
    ttFiber4SourcesCheck_ok,
    ttFiber4Row_0_ok,
    ttFiber4Row_1_ok,
    ttFiber4Row_2_ok,
    ttFiber4Row_3_ok,
    ttFiber4Row_4_ok,
    ttFiber4Row_5_ok,
    ttFiber4Row_6_ok,
    ttFiber4Row_7_ok,
    ttFiber4Row_8_ok,
    ttFiber4Row_9_ok,
    ttFiber4Row_10_ok,
    ttFiber4Row_11_ok,
    ttFiber4Row_12_ok,
    ttFiber4Row_13_ok,
    ttFiber4Row_14_ok,
    ttFiber4Row_15_ok,
    ttFiber4Row_16_ok,
    ttFiber4Row_17_ok,
    ttFiber4Row_18_ok,
    ttFiber4Row_19_ok,
    ttFiber4Row_20_ok,
    ttFiber4Row_21_ok,
    ttFiber4Row_22_ok,
    ttFiber4Row_23_ok,
    ttFiber4Row_24_ok,
    ttFiber4Row_25_ok,
    ttFiber4Row_26_ok,
    ttFiber4Row_27_ok,
    ttFiber4Row_28_ok,
    ttFiber4Row_29_ok,
    ttFiber4Row_30_ok,
    ttFiber4Row_31_ok,
    ttFiber4Row_32_ok,
    ttFiber4Row_33_ok,
    ttFiber4Row_34_ok,
    ttFiber4Row_35_ok,
    ttFiber4Row_36_ok,
    ttFiber4Row_37_ok,
    ttFiber4Row_38_ok,
    ttFiber4Row_39_ok,
    ttFiber4Row_40_ok,
    ttFiber4Row_41_ok,
    ttFiber4Row_42_ok,
    ttFiber4Row_43_ok,
    ttFiber4Row_44_ok,
    ttFiber4Row_45_ok,
    ttFiber4Row_46_ok,
    ttFiber4Row_47_ok,
    ttFiber4Row_48_ok,
    ttFiber4Row_49_ok,
    ttFiber4Row_50_ok,
    ttFiber4Row_51_ok,
    ttFiber4Row_52_ok,
    ttFiber4Row_53_ok,
    ttFiber4Row_54_ok,
    ttFiber4Row_55_ok,
    ttFiber4Row_56_ok,
    ttFiber4Row_57_ok,
    ttFiber4Row_58_ok,
    ttFiber4Row_59_ok,
    ttFiber4Row_60_ok,
    ttFiber4Row_61_ok,
    ttFiber4Row_62_ok,
    ttFiber4Row_63_ok,
    ttFiber4Parent_0_ok,
    ttFiber4Parent_1_ok,
    ttFiber4Parent_2_ok,
    ttFiber4Parent_3_ok,
    ttFiber4Parent_4_ok,
    ttFiber4Parent_5_ok,
    ttFiber4Parent_6_ok,
    ttFiber4Parent_7_ok,
    ttFiber4Parent_8_ok,
    ttFiber4Parent_9_ok,
    ttFiber4Parent_10_ok,
    ttFiber4Parent_11_ok,
    ttFiber4Parent_12_ok,
    ttFiber4Parent_13_ok,
    ttFiber4Parent_14_ok,
    ttFiber4Parent_15_ok,
    ttFiber4Parent_16_ok,
    ttFiber4Parent_17_ok,
    ttFiber4Parent_18_ok,
    ttFiber4Parent_19_ok,
    ttFiber4Parent_20_ok,
    ttFiber4Parent_21_ok,
    ttFiber4Parent_22_ok,
    ttFiber4Parent_23_ok,
    ttFiber4Parent_24_ok,
    ttFiber4Parent_25_ok,
    ttFiber4Parent_26_ok,
    ttFiber4Parent_27_ok,
    ttFiber4Parent_28_ok,
    ttFiber4Parent_29_ok,
    ttFiber4Parent_30_ok,
    ttFiber4Parent_31_ok,
    ttFiber4Parent_32_ok,
    ttFiber4Parent_33_ok,
    ttFiber4Parent_34_ok,
    ttFiber4Parent_35_ok,
    ttFiber4Parent_36_ok,
    ttFiber4Parent_37_ok,
    ttFiber4Parent_38_ok,
    ttFiber4Parent_39_ok,
    ttFiber4Parent_40_ok,
    ttFiber4Parent_41_ok,
    ttFiber4Parent_42_ok,
    ttFiber4Parent_43_ok,
    ttFiber4Parent_44_ok,
    ttFiber4Parent_45_ok,
    ttFiber4Parent_46_ok,
    ttFiber4Parent_47_ok,
    ttFiber4Parent_48_ok,
    ttFiber4Parent_49_ok,
    ttFiber4Parent_50_ok,
    ttFiber4Parent_51_ok,
    ttFiber4Parent_52_ok,
    ttFiber4Parent_53_ok,
    ttFiber4Parent_54_ok,
    ttFiber4Parent_55_ok,
    ttFiber4Parent_56_ok,
    ttFiber4Parent_57_ok,
    ttFiber4Parent_58_ok,
    ttFiber4Parent_59_ok,
    ttFiber4Parent_60_ok,
    ttFiber4Parent_61_ok,
    ttFiber4Parent_62_ok,
    ttFiber4Parent_63_ok]

def ttFiber5Key : List LColor :=
  [LColor.r, LColor.r, LColor.b, LColor.p]

def ttFiber5Expected : List Nat :=
  [352, 353, 354, 355, 356, 357, 358, 359]

def ttFiber5Rows : List DirectChainParentRow :=
  [ directRow 352 352 68 144 68 144 default
  , directRow 353 352 68 145 68 144 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 354 353 68 146 68 145 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 355 352 68 147 68 144 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 356 352 69 152 68 144 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 357 353 69 153 68 145 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 358 354 69 154 68 146 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 359 355 69 155 68 147 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  ]

def ttFiber5RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber5Rows i default

def ttFiber5SourcesCheck : Bool :=
  (ttFiber5Rows.map fun row => row.source) == ttFiber5Expected

theorem ttFiber5SourcesCheck_ok :
    ttFiber5SourcesCheck = true := by
  decide

def ttFiber5RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber5Key ttFiber5Expected (ttFiber5RowAt i)

theorem ttFiber5Row_0_ok : ttFiber5RowCheck 0 = true := by decide
theorem ttFiber5Row_1_ok : ttFiber5RowCheck 1 = true := by decide
theorem ttFiber5Row_2_ok : ttFiber5RowCheck 2 = true := by decide
theorem ttFiber5Row_3_ok : ttFiber5RowCheck 3 = true := by decide
theorem ttFiber5Row_4_ok : ttFiber5RowCheck 4 = true := by decide
theorem ttFiber5Row_5_ok : ttFiber5RowCheck 5 = true := by decide
theorem ttFiber5Row_6_ok : ttFiber5RowCheck 6 = true := by decide
theorem ttFiber5Row_7_ok : ttFiber5RowCheck 7 = true := by decide

def ttFiber5ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber5Rows ttMaxParentDepth (listGetD ttFiber5Expected i 0) == 352

theorem ttFiber5Parent_0_ok : ttFiber5ParentCheck 0 = true := by decide
theorem ttFiber5Parent_1_ok : ttFiber5ParentCheck 1 = true := by decide
theorem ttFiber5Parent_2_ok : ttFiber5ParentCheck 2 = true := by decide
theorem ttFiber5Parent_3_ok : ttFiber5ParentCheck 3 = true := by decide
theorem ttFiber5Parent_4_ok : ttFiber5ParentCheck 4 = true := by decide
theorem ttFiber5Parent_5_ok : ttFiber5ParentCheck 5 = true := by decide
theorem ttFiber5Parent_6_ok : ttFiber5ParentCheck 6 = true := by decide
theorem ttFiber5Parent_7_ok : ttFiber5ParentCheck 7 = true := by decide

def ttFiber5CertificateAudit : Bool :=
  ttFiber5SourcesCheck &&
    ttFiber5RowCheck 0 &&
    ttFiber5RowCheck 1 &&
    ttFiber5RowCheck 2 &&
    ttFiber5RowCheck 3 &&
    ttFiber5RowCheck 4 &&
    ttFiber5RowCheck 5 &&
    ttFiber5RowCheck 6 &&
    ttFiber5RowCheck 7 &&
    ttFiber5ParentCheck 0 &&
    ttFiber5ParentCheck 1 &&
    ttFiber5ParentCheck 2 &&
    ttFiber5ParentCheck 3 &&
    ttFiber5ParentCheck 4 &&
    ttFiber5ParentCheck 5 &&
    ttFiber5ParentCheck 6 &&
    ttFiber5ParentCheck 7

theorem ttFiber5CertificateAudit_ok :
    ttFiber5CertificateAudit = true := by
  simp [ttFiber5CertificateAudit,
    ttFiber5SourcesCheck_ok,
    ttFiber5Row_0_ok,
    ttFiber5Row_1_ok,
    ttFiber5Row_2_ok,
    ttFiber5Row_3_ok,
    ttFiber5Row_4_ok,
    ttFiber5Row_5_ok,
    ttFiber5Row_6_ok,
    ttFiber5Row_7_ok,
    ttFiber5Parent_0_ok,
    ttFiber5Parent_1_ok,
    ttFiber5Parent_2_ok,
    ttFiber5Parent_3_ok,
    ttFiber5Parent_4_ok,
    ttFiber5Parent_5_ok,
    ttFiber5Parent_6_ok,
    ttFiber5Parent_7_ok]

def ttFiber6Key : List LColor :=
  [LColor.r, LColor.r, LColor.p, LColor.r]

def ttFiber6Expected : List Nat :=
  [880, 881, 882, 883, 884, 885, 886, 887]

def ttFiber6Rows : List DirectChainParentRow :=
  [ directRow 880 880 176 20 176 20 default
  , directRow 881 880 176 21 176 20 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 882 880 176 22 176 20 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 883 881 176 23 176 21 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 884 880 177 28 176 20 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 885 881 177 29 176 21 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 886 882 177 30 176 22 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 887 883 177 31 176 23 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  ]

def ttFiber6RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber6Rows i default

def ttFiber6SourcesCheck : Bool :=
  (ttFiber6Rows.map fun row => row.source) == ttFiber6Expected

theorem ttFiber6SourcesCheck_ok :
    ttFiber6SourcesCheck = true := by
  decide

def ttFiber6RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber6Key ttFiber6Expected (ttFiber6RowAt i)

theorem ttFiber6Row_0_ok : ttFiber6RowCheck 0 = true := by decide
theorem ttFiber6Row_1_ok : ttFiber6RowCheck 1 = true := by decide
theorem ttFiber6Row_2_ok : ttFiber6RowCheck 2 = true := by decide
theorem ttFiber6Row_3_ok : ttFiber6RowCheck 3 = true := by decide
theorem ttFiber6Row_4_ok : ttFiber6RowCheck 4 = true := by decide
theorem ttFiber6Row_5_ok : ttFiber6RowCheck 5 = true := by decide
theorem ttFiber6Row_6_ok : ttFiber6RowCheck 6 = true := by decide
theorem ttFiber6Row_7_ok : ttFiber6RowCheck 7 = true := by decide

def ttFiber6ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber6Rows ttMaxParentDepth (listGetD ttFiber6Expected i 0) == 880

theorem ttFiber6Parent_0_ok : ttFiber6ParentCheck 0 = true := by decide
theorem ttFiber6Parent_1_ok : ttFiber6ParentCheck 1 = true := by decide
theorem ttFiber6Parent_2_ok : ttFiber6ParentCheck 2 = true := by decide
theorem ttFiber6Parent_3_ok : ttFiber6ParentCheck 3 = true := by decide
theorem ttFiber6Parent_4_ok : ttFiber6ParentCheck 4 = true := by decide
theorem ttFiber6Parent_5_ok : ttFiber6ParentCheck 5 = true := by decide
theorem ttFiber6Parent_6_ok : ttFiber6ParentCheck 6 = true := by decide
theorem ttFiber6Parent_7_ok : ttFiber6ParentCheck 7 = true := by decide

def ttFiber6CertificateAudit : Bool :=
  ttFiber6SourcesCheck &&
    ttFiber6RowCheck 0 &&
    ttFiber6RowCheck 1 &&
    ttFiber6RowCheck 2 &&
    ttFiber6RowCheck 3 &&
    ttFiber6RowCheck 4 &&
    ttFiber6RowCheck 5 &&
    ttFiber6RowCheck 6 &&
    ttFiber6RowCheck 7 &&
    ttFiber6ParentCheck 0 &&
    ttFiber6ParentCheck 1 &&
    ttFiber6ParentCheck 2 &&
    ttFiber6ParentCheck 3 &&
    ttFiber6ParentCheck 4 &&
    ttFiber6ParentCheck 5 &&
    ttFiber6ParentCheck 6 &&
    ttFiber6ParentCheck 7

theorem ttFiber6CertificateAudit_ok :
    ttFiber6CertificateAudit = true := by
  simp [ttFiber6CertificateAudit,
    ttFiber6SourcesCheck_ok,
    ttFiber6Row_0_ok,
    ttFiber6Row_1_ok,
    ttFiber6Row_2_ok,
    ttFiber6Row_3_ok,
    ttFiber6Row_4_ok,
    ttFiber6Row_5_ok,
    ttFiber6Row_6_ok,
    ttFiber6Row_7_ok,
    ttFiber6Parent_0_ok,
    ttFiber6Parent_1_ok,
    ttFiber6Parent_2_ok,
    ttFiber6Parent_3_ok,
    ttFiber6Parent_4_ok,
    ttFiber6Parent_5_ok,
    ttFiber6Parent_6_ok,
    ttFiber6Parent_7_ok]

def ttFiber7Key : List LColor :=
  [LColor.r, LColor.r, LColor.p, LColor.b]

def ttFiber7Expected : List Nat :=
  [640, 641, 642, 643, 644, 645, 646, 647]

def ttFiber7Rows : List DirectChainParentRow :=
  [ directRow 640 640 128 84 128 84 default
  , directRow 641 640 128 85 128 84 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 642 640 128 86 128 84 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 643 641 128 87 128 85 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 644 640 129 92 128 84 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 645 641 129 93 128 85 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 646 642 129 94 128 86 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 647 643 129 95 128 87 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  ]

def ttFiber7RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber7Rows i default

def ttFiber7SourcesCheck : Bool :=
  (ttFiber7Rows.map fun row => row.source) == ttFiber7Expected

theorem ttFiber7SourcesCheck_ok :
    ttFiber7SourcesCheck = true := by
  decide

def ttFiber7RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber7Key ttFiber7Expected (ttFiber7RowAt i)

theorem ttFiber7Row_0_ok : ttFiber7RowCheck 0 = true := by decide
theorem ttFiber7Row_1_ok : ttFiber7RowCheck 1 = true := by decide
theorem ttFiber7Row_2_ok : ttFiber7RowCheck 2 = true := by decide
theorem ttFiber7Row_3_ok : ttFiber7RowCheck 3 = true := by decide
theorem ttFiber7Row_4_ok : ttFiber7RowCheck 4 = true := by decide
theorem ttFiber7Row_5_ok : ttFiber7RowCheck 5 = true := by decide
theorem ttFiber7Row_6_ok : ttFiber7RowCheck 6 = true := by decide
theorem ttFiber7Row_7_ok : ttFiber7RowCheck 7 = true := by decide

def ttFiber7ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber7Rows ttMaxParentDepth (listGetD ttFiber7Expected i 0) == 640

theorem ttFiber7Parent_0_ok : ttFiber7ParentCheck 0 = true := by decide
theorem ttFiber7Parent_1_ok : ttFiber7ParentCheck 1 = true := by decide
theorem ttFiber7Parent_2_ok : ttFiber7ParentCheck 2 = true := by decide
theorem ttFiber7Parent_3_ok : ttFiber7ParentCheck 3 = true := by decide
theorem ttFiber7Parent_4_ok : ttFiber7ParentCheck 4 = true := by decide
theorem ttFiber7Parent_5_ok : ttFiber7ParentCheck 5 = true := by decide
theorem ttFiber7Parent_6_ok : ttFiber7ParentCheck 6 = true := by decide
theorem ttFiber7Parent_7_ok : ttFiber7ParentCheck 7 = true := by decide

def ttFiber7CertificateAudit : Bool :=
  ttFiber7SourcesCheck &&
    ttFiber7RowCheck 0 &&
    ttFiber7RowCheck 1 &&
    ttFiber7RowCheck 2 &&
    ttFiber7RowCheck 3 &&
    ttFiber7RowCheck 4 &&
    ttFiber7RowCheck 5 &&
    ttFiber7RowCheck 6 &&
    ttFiber7RowCheck 7 &&
    ttFiber7ParentCheck 0 &&
    ttFiber7ParentCheck 1 &&
    ttFiber7ParentCheck 2 &&
    ttFiber7ParentCheck 3 &&
    ttFiber7ParentCheck 4 &&
    ttFiber7ParentCheck 5 &&
    ttFiber7ParentCheck 6 &&
    ttFiber7ParentCheck 7

theorem ttFiber7CertificateAudit_ok :
    ttFiber7CertificateAudit = true := by
  simp [ttFiber7CertificateAudit,
    ttFiber7SourcesCheck_ok,
    ttFiber7Row_0_ok,
    ttFiber7Row_1_ok,
    ttFiber7Row_2_ok,
    ttFiber7Row_3_ok,
    ttFiber7Row_4_ok,
    ttFiber7Row_5_ok,
    ttFiber7Row_6_ok,
    ttFiber7Row_7_ok,
    ttFiber7Parent_0_ok,
    ttFiber7Parent_1_ok,
    ttFiber7Parent_2_ok,
    ttFiber7Parent_3_ok,
    ttFiber7Parent_4_ok,
    ttFiber7Parent_5_ok,
    ttFiber7Parent_6_ok,
    ttFiber7Parent_7_ok]

def ttFiber8Key : List LColor :=
  [LColor.r, LColor.r, LColor.p, LColor.p]

def ttFiber8Expected : List Nat :=
  [648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 888, 889, 890, 891, 892, 893, 894, 895, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919]

def ttFiber8Rows : List DirectChainParentRow :=
  [ directRow 648 648 132 148 132 148 default
  , directRow 649 648 132 149 132 148 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 650 649 132 150 132 149 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 651 648 132 151 132 148 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 652 648 132 164 132 148 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 653 649 132 165 132 149 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 654 652 132 166 132 164 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 655 651 132 167 132 151 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 656 648 133 156 132 148 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 657 649 133 157 132 149 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 658 650 133 158 132 150 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 659 651 133 159 132 151 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 660 652 133 172 132 164 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 661 653 133 173 132 165 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 662 654 133 174 132 166 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 663 655 133 175 132 167 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 664 668 134 0 134 48 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 665 669 134 1 134 49 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 666 660 134 2 133 172 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 667 661 134 3 133 173 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 668 656 134 48 133 156 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 669 657 134 49 133 157 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 670 658 134 50 133 158 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 671 659 134 51 133 159 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 672 676 135 8 135 56 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 673 677 135 9 135 57 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 674 652 135 10 132 164 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 675 653 135 11 132 165 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 676 648 135 56 132 148 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 677 649 135 57 132 149 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 678 650 135 58 132 150 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 679 651 135 59 132 151 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 888 648 180 132 132 148 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 889 649 180 133 132 149 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 890 650 180 134 132 150 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 891 651 180 135 132 151 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 892 652 180 180 132 164 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 893 653 180 181 132 165 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 894 654 180 182 132 166 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 895 655 180 183 132 167 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 896 656 181 140 133 156 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 897 657 181 141 133 157 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 898 658 181 142 133 158 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 899 659 181 143 133 159 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 900 660 181 188 133 172 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 901 661 181 189 133 173 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 902 662 181 190 133 174 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 903 663 181 191 133 175 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 904 888 182 64 180 132 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 905 889 182 65 180 133 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 906 904 182 66 182 64 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 907 891 182 67 180 135 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 908 892 182 116 180 180 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 909 893 182 117 180 181 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 910 905 182 118 182 65 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 911 904 182 119 182 64 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 912 896 183 72 181 140 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 913 897 183 73 181 141 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 914 674 183 74 135 10 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 915 675 183 75 135 11 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 916 676 183 124 135 56 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 917 677 183 125 135 57 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 918 916 183 126 183 124 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 919 679 183 127 135 59 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  ]

def ttFiber8RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber8Rows i default

def ttFiber8SourcesCheck : Bool :=
  (ttFiber8Rows.map fun row => row.source) == ttFiber8Expected

theorem ttFiber8SourcesCheck_ok :
    ttFiber8SourcesCheck = true := by
  decide

def ttFiber8RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt i)

theorem ttFiber8Row_0_ok : ttFiber8RowCheck 0 = true := by decide
theorem ttFiber8Row_1_ok : ttFiber8RowCheck 1 = true := by decide
theorem ttFiber8Row_2_ok : ttFiber8RowCheck 2 = true := by decide
theorem ttFiber8Row_3_ok : ttFiber8RowCheck 3 = true := by decide
theorem ttFiber8Row_4_ok : ttFiber8RowCheck 4 = true := by decide
theorem ttFiber8Row_5_ok : ttFiber8RowCheck 5 = true := by decide
theorem ttFiber8Row_6_ok : ttFiber8RowCheck 6 = true := by decide
theorem ttFiber8Row_7_ok : ttFiber8RowCheck 7 = true := by decide
theorem ttFiber8Row_8_ok : ttFiber8RowCheck 8 = true := by decide
theorem ttFiber8Row_9_ok : ttFiber8RowCheck 9 = true := by decide
theorem ttFiber8Row_10_ok : ttFiber8RowCheck 10 = true := by decide
theorem ttFiber8Row_11_ok : ttFiber8RowCheck 11 = true := by decide
theorem ttFiber8Row_12_ok : ttFiber8RowCheck 12 = true := by decide
theorem ttFiber8Row_13_ok : ttFiber8RowCheck 13 = true := by decide
theorem ttFiber8Row_14_ok : ttFiber8RowCheck 14 = true := by decide
theorem ttFiber8Row_15_ok : ttFiber8RowCheck 15 = true := by decide
theorem ttFiber8Row_16_ok : ttFiber8RowCheck 16 = true := by decide
theorem ttFiber8Row_17_ok : ttFiber8RowCheck 17 = true := by decide
theorem ttFiber8Row_18_ok : ttFiber8RowCheck 18 = true := by decide
theorem ttFiber8Row_19_ok : ttFiber8RowCheck 19 = true := by decide
theorem ttFiber8Row_20_ok : ttFiber8RowCheck 20 = true := by decide
theorem ttFiber8Row_21_ok : ttFiber8RowCheck 21 = true := by decide
theorem ttFiber8Row_22_ok : ttFiber8RowCheck 22 = true := by decide
theorem ttFiber8Row_23_ok : ttFiber8RowCheck 23 = true := by decide
theorem ttFiber8Row_24_ok : ttFiber8RowCheck 24 = true := by decide
theorem ttFiber8Row_25_ok : ttFiber8RowCheck 25 = true := by decide
theorem ttFiber8Row_26_ok : ttFiber8RowCheck 26 = true := by decide
theorem ttFiber8Row_27_ok : ttFiber8RowCheck 27 = true := by decide
theorem ttFiber8Row_28_ok : ttFiber8RowCheck 28 = true := by decide
theorem ttFiber8Row_29_ok : ttFiber8RowCheck 29 = true := by decide
theorem ttFiber8Row_30_ok : ttFiber8RowCheck 30 = true := by decide
theorem ttFiber8Row_31_ok : ttFiber8RowCheck 31 = true := by decide
theorem ttFiber8Row_32_ok : ttFiber8RowCheck 32 = true := by decide
theorem ttFiber8Row_33_ok : ttFiber8RowCheck 33 = true := by decide
theorem ttFiber8Row_34_ok : ttFiber8RowCheck 34 = true := by decide
theorem ttFiber8Row_35_ok : ttFiber8RowCheck 35 = true := by decide
theorem ttFiber8Row_36_ok : ttFiber8RowCheck 36 = true := by decide
theorem ttFiber8Row_37_ok : ttFiber8RowCheck 37 = true := by decide
theorem ttFiber8Row_38_ok : ttFiber8RowCheck 38 = true := by decide
theorem ttFiber8Row_39_ok : ttFiber8RowCheck 39 = true := by decide
theorem ttFiber8Row_40_ok : ttFiber8RowCheck 40 = true := by decide
theorem ttFiber8Row_41_ok : ttFiber8RowCheck 41 = true := by decide
theorem ttFiber8Row_42_ok : ttFiber8RowCheck 42 = true := by decide
theorem ttFiber8Row_43_ok : ttFiber8RowCheck 43 = true := by decide
theorem ttFiber8Row_44_ok : ttFiber8RowCheck 44 = true := by decide
theorem ttFiber8Row_45_ok : ttFiber8RowCheck 45 = true := by decide
theorem ttFiber8Row_46_ok : ttFiber8RowCheck 46 = true := by decide
theorem ttFiber8Row_47_ok : ttFiber8RowCheck 47 = true := by decide
theorem ttFiber8Row_48_ok : ttFiber8RowCheck 48 = true := by decide
theorem ttFiber8Row_49_ok : ttFiber8RowCheck 49 = true := by decide
theorem ttFiber8Row_50_ok : ttFiber8RowCheck 50 = true := by decide
theorem ttFiber8Row_51_ok : ttFiber8RowCheck 51 = true := by decide
theorem ttFiber8Row_52_ok : ttFiber8RowCheck 52 = true := by decide
theorem ttFiber8Row_53_ok : ttFiber8RowCheck 53 = true := by decide
theorem ttFiber8Row_54_ok : ttFiber8RowCheck 54 = true := by decide
theorem ttFiber8Row_55_ok : ttFiber8RowCheck 55 = true := by decide
theorem ttFiber8Row_56_ok : ttFiber8RowCheck 56 = true := by decide
theorem ttFiber8Row_57_ok : ttFiber8RowCheck 57 = true := by decide
theorem ttFiber8Row_58_ok : ttFiber8RowCheck 58 = true := by decide
theorem ttFiber8Row_59_ok : ttFiber8RowCheck 59 = true := by decide
theorem ttFiber8Row_60_ok : ttFiber8RowCheck 60 = true := by decide
theorem ttFiber8Row_61_ok : ttFiber8RowCheck 61 = true := by decide
theorem ttFiber8Row_62_ok : ttFiber8RowCheck 62 = true := by decide
theorem ttFiber8Row_63_ok : ttFiber8RowCheck 63 = true := by decide

def ttFiber8ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber8Rows ttMaxParentDepth (listGetD ttFiber8Expected i 0) == 648

theorem ttFiber8Parent_0_ok : ttFiber8ParentCheck 0 = true := by decide
theorem ttFiber8Parent_1_ok : ttFiber8ParentCheck 1 = true := by decide
theorem ttFiber8Parent_2_ok : ttFiber8ParentCheck 2 = true := by decide
theorem ttFiber8Parent_3_ok : ttFiber8ParentCheck 3 = true := by decide
theorem ttFiber8Parent_4_ok : ttFiber8ParentCheck 4 = true := by decide
theorem ttFiber8Parent_5_ok : ttFiber8ParentCheck 5 = true := by decide
theorem ttFiber8Parent_6_ok : ttFiber8ParentCheck 6 = true := by decide
theorem ttFiber8Parent_7_ok : ttFiber8ParentCheck 7 = true := by decide
theorem ttFiber8Parent_8_ok : ttFiber8ParentCheck 8 = true := by decide
theorem ttFiber8Parent_9_ok : ttFiber8ParentCheck 9 = true := by decide
theorem ttFiber8Parent_10_ok : ttFiber8ParentCheck 10 = true := by decide
theorem ttFiber8Parent_11_ok : ttFiber8ParentCheck 11 = true := by decide
theorem ttFiber8Parent_12_ok : ttFiber8ParentCheck 12 = true := by decide
theorem ttFiber8Parent_13_ok : ttFiber8ParentCheck 13 = true := by decide
theorem ttFiber8Parent_14_ok : ttFiber8ParentCheck 14 = true := by decide
theorem ttFiber8Parent_15_ok : ttFiber8ParentCheck 15 = true := by decide
theorem ttFiber8Parent_16_ok : ttFiber8ParentCheck 16 = true := by decide
theorem ttFiber8Parent_17_ok : ttFiber8ParentCheck 17 = true := by decide
theorem ttFiber8Parent_18_ok : ttFiber8ParentCheck 18 = true := by decide
theorem ttFiber8Parent_19_ok : ttFiber8ParentCheck 19 = true := by decide
theorem ttFiber8Parent_20_ok : ttFiber8ParentCheck 20 = true := by decide
theorem ttFiber8Parent_21_ok : ttFiber8ParentCheck 21 = true := by decide
theorem ttFiber8Parent_22_ok : ttFiber8ParentCheck 22 = true := by decide
theorem ttFiber8Parent_23_ok : ttFiber8ParentCheck 23 = true := by decide
theorem ttFiber8Parent_24_ok : ttFiber8ParentCheck 24 = true := by decide
theorem ttFiber8Parent_25_ok : ttFiber8ParentCheck 25 = true := by decide
theorem ttFiber8Parent_26_ok : ttFiber8ParentCheck 26 = true := by decide
theorem ttFiber8Parent_27_ok : ttFiber8ParentCheck 27 = true := by decide
theorem ttFiber8Parent_28_ok : ttFiber8ParentCheck 28 = true := by decide
theorem ttFiber8Parent_29_ok : ttFiber8ParentCheck 29 = true := by decide
theorem ttFiber8Parent_30_ok : ttFiber8ParentCheck 30 = true := by decide
theorem ttFiber8Parent_31_ok : ttFiber8ParentCheck 31 = true := by decide
theorem ttFiber8Parent_32_ok : ttFiber8ParentCheck 32 = true := by decide
theorem ttFiber8Parent_33_ok : ttFiber8ParentCheck 33 = true := by decide
theorem ttFiber8Parent_34_ok : ttFiber8ParentCheck 34 = true := by decide
theorem ttFiber8Parent_35_ok : ttFiber8ParentCheck 35 = true := by decide
theorem ttFiber8Parent_36_ok : ttFiber8ParentCheck 36 = true := by decide
theorem ttFiber8Parent_37_ok : ttFiber8ParentCheck 37 = true := by decide
theorem ttFiber8Parent_38_ok : ttFiber8ParentCheck 38 = true := by decide
theorem ttFiber8Parent_39_ok : ttFiber8ParentCheck 39 = true := by decide
theorem ttFiber8Parent_40_ok : ttFiber8ParentCheck 40 = true := by decide
theorem ttFiber8Parent_41_ok : ttFiber8ParentCheck 41 = true := by decide
theorem ttFiber8Parent_42_ok : ttFiber8ParentCheck 42 = true := by decide
theorem ttFiber8Parent_43_ok : ttFiber8ParentCheck 43 = true := by decide
theorem ttFiber8Parent_44_ok : ttFiber8ParentCheck 44 = true := by decide
theorem ttFiber8Parent_45_ok : ttFiber8ParentCheck 45 = true := by decide
theorem ttFiber8Parent_46_ok : ttFiber8ParentCheck 46 = true := by decide
theorem ttFiber8Parent_47_ok : ttFiber8ParentCheck 47 = true := by decide
theorem ttFiber8Parent_48_ok : ttFiber8ParentCheck 48 = true := by decide
theorem ttFiber8Parent_49_ok : ttFiber8ParentCheck 49 = true := by decide
theorem ttFiber8Parent_50_ok : ttFiber8ParentCheck 50 = true := by decide
theorem ttFiber8Parent_51_ok : ttFiber8ParentCheck 51 = true := by decide
theorem ttFiber8Parent_52_ok : ttFiber8ParentCheck 52 = true := by decide
theorem ttFiber8Parent_53_ok : ttFiber8ParentCheck 53 = true := by decide
theorem ttFiber8Parent_54_ok : ttFiber8ParentCheck 54 = true := by decide
theorem ttFiber8Parent_55_ok : ttFiber8ParentCheck 55 = true := by decide
theorem ttFiber8Parent_56_ok : ttFiber8ParentCheck 56 = true := by decide
theorem ttFiber8Parent_57_ok : ttFiber8ParentCheck 57 = true := by decide
theorem ttFiber8Parent_58_ok : ttFiber8ParentCheck 58 = true := by decide
theorem ttFiber8Parent_59_ok : ttFiber8ParentCheck 59 = true := by decide
theorem ttFiber8Parent_60_ok : ttFiber8ParentCheck 60 = true := by decide
theorem ttFiber8Parent_61_ok : ttFiber8ParentCheck 61 = true := by decide
theorem ttFiber8Parent_62_ok : ttFiber8ParentCheck 62 = true := by decide
theorem ttFiber8Parent_63_ok : ttFiber8ParentCheck 63 = true := by decide

def ttFiber8CertificateAudit : Bool :=
  ttFiber8SourcesCheck &&
    ttFiber8RowCheck 0 &&
    ttFiber8RowCheck 1 &&
    ttFiber8RowCheck 2 &&
    ttFiber8RowCheck 3 &&
    ttFiber8RowCheck 4 &&
    ttFiber8RowCheck 5 &&
    ttFiber8RowCheck 6 &&
    ttFiber8RowCheck 7 &&
    ttFiber8RowCheck 8 &&
    ttFiber8RowCheck 9 &&
    ttFiber8RowCheck 10 &&
    ttFiber8RowCheck 11 &&
    ttFiber8RowCheck 12 &&
    ttFiber8RowCheck 13 &&
    ttFiber8RowCheck 14 &&
    ttFiber8RowCheck 15 &&
    ttFiber8RowCheck 16 &&
    ttFiber8RowCheck 17 &&
    ttFiber8RowCheck 18 &&
    ttFiber8RowCheck 19 &&
    ttFiber8RowCheck 20 &&
    ttFiber8RowCheck 21 &&
    ttFiber8RowCheck 22 &&
    ttFiber8RowCheck 23 &&
    ttFiber8RowCheck 24 &&
    ttFiber8RowCheck 25 &&
    ttFiber8RowCheck 26 &&
    ttFiber8RowCheck 27 &&
    ttFiber8RowCheck 28 &&
    ttFiber8RowCheck 29 &&
    ttFiber8RowCheck 30 &&
    ttFiber8RowCheck 31 &&
    ttFiber8RowCheck 32 &&
    ttFiber8RowCheck 33 &&
    ttFiber8RowCheck 34 &&
    ttFiber8RowCheck 35 &&
    ttFiber8RowCheck 36 &&
    ttFiber8RowCheck 37 &&
    ttFiber8RowCheck 38 &&
    ttFiber8RowCheck 39 &&
    ttFiber8RowCheck 40 &&
    ttFiber8RowCheck 41 &&
    ttFiber8RowCheck 42 &&
    ttFiber8RowCheck 43 &&
    ttFiber8RowCheck 44 &&
    ttFiber8RowCheck 45 &&
    ttFiber8RowCheck 46 &&
    ttFiber8RowCheck 47 &&
    ttFiber8RowCheck 48 &&
    ttFiber8RowCheck 49 &&
    ttFiber8RowCheck 50 &&
    ttFiber8RowCheck 51 &&
    ttFiber8RowCheck 52 &&
    ttFiber8RowCheck 53 &&
    ttFiber8RowCheck 54 &&
    ttFiber8RowCheck 55 &&
    ttFiber8RowCheck 56 &&
    ttFiber8RowCheck 57 &&
    ttFiber8RowCheck 58 &&
    ttFiber8RowCheck 59 &&
    ttFiber8RowCheck 60 &&
    ttFiber8RowCheck 61 &&
    ttFiber8RowCheck 62 &&
    ttFiber8RowCheck 63 &&
    ttFiber8ParentCheck 0 &&
    ttFiber8ParentCheck 1 &&
    ttFiber8ParentCheck 2 &&
    ttFiber8ParentCheck 3 &&
    ttFiber8ParentCheck 4 &&
    ttFiber8ParentCheck 5 &&
    ttFiber8ParentCheck 6 &&
    ttFiber8ParentCheck 7 &&
    ttFiber8ParentCheck 8 &&
    ttFiber8ParentCheck 9 &&
    ttFiber8ParentCheck 10 &&
    ttFiber8ParentCheck 11 &&
    ttFiber8ParentCheck 12 &&
    ttFiber8ParentCheck 13 &&
    ttFiber8ParentCheck 14 &&
    ttFiber8ParentCheck 15 &&
    ttFiber8ParentCheck 16 &&
    ttFiber8ParentCheck 17 &&
    ttFiber8ParentCheck 18 &&
    ttFiber8ParentCheck 19 &&
    ttFiber8ParentCheck 20 &&
    ttFiber8ParentCheck 21 &&
    ttFiber8ParentCheck 22 &&
    ttFiber8ParentCheck 23 &&
    ttFiber8ParentCheck 24 &&
    ttFiber8ParentCheck 25 &&
    ttFiber8ParentCheck 26 &&
    ttFiber8ParentCheck 27 &&
    ttFiber8ParentCheck 28 &&
    ttFiber8ParentCheck 29 &&
    ttFiber8ParentCheck 30 &&
    ttFiber8ParentCheck 31 &&
    ttFiber8ParentCheck 32 &&
    ttFiber8ParentCheck 33 &&
    ttFiber8ParentCheck 34 &&
    ttFiber8ParentCheck 35 &&
    ttFiber8ParentCheck 36 &&
    ttFiber8ParentCheck 37 &&
    ttFiber8ParentCheck 38 &&
    ttFiber8ParentCheck 39 &&
    ttFiber8ParentCheck 40 &&
    ttFiber8ParentCheck 41 &&
    ttFiber8ParentCheck 42 &&
    ttFiber8ParentCheck 43 &&
    ttFiber8ParentCheck 44 &&
    ttFiber8ParentCheck 45 &&
    ttFiber8ParentCheck 46 &&
    ttFiber8ParentCheck 47 &&
    ttFiber8ParentCheck 48 &&
    ttFiber8ParentCheck 49 &&
    ttFiber8ParentCheck 50 &&
    ttFiber8ParentCheck 51 &&
    ttFiber8ParentCheck 52 &&
    ttFiber8ParentCheck 53 &&
    ttFiber8ParentCheck 54 &&
    ttFiber8ParentCheck 55 &&
    ttFiber8ParentCheck 56 &&
    ttFiber8ParentCheck 57 &&
    ttFiber8ParentCheck 58 &&
    ttFiber8ParentCheck 59 &&
    ttFiber8ParentCheck 60 &&
    ttFiber8ParentCheck 61 &&
    ttFiber8ParentCheck 62 &&
    ttFiber8ParentCheck 63

theorem ttFiber8CertificateAudit_ok :
    ttFiber8CertificateAudit = true := by
  simp [ttFiber8CertificateAudit,
    ttFiber8SourcesCheck_ok,
    ttFiber8Row_0_ok,
    ttFiber8Row_1_ok,
    ttFiber8Row_2_ok,
    ttFiber8Row_3_ok,
    ttFiber8Row_4_ok,
    ttFiber8Row_5_ok,
    ttFiber8Row_6_ok,
    ttFiber8Row_7_ok,
    ttFiber8Row_8_ok,
    ttFiber8Row_9_ok,
    ttFiber8Row_10_ok,
    ttFiber8Row_11_ok,
    ttFiber8Row_12_ok,
    ttFiber8Row_13_ok,
    ttFiber8Row_14_ok,
    ttFiber8Row_15_ok,
    ttFiber8Row_16_ok,
    ttFiber8Row_17_ok,
    ttFiber8Row_18_ok,
    ttFiber8Row_19_ok,
    ttFiber8Row_20_ok,
    ttFiber8Row_21_ok,
    ttFiber8Row_22_ok,
    ttFiber8Row_23_ok,
    ttFiber8Row_24_ok,
    ttFiber8Row_25_ok,
    ttFiber8Row_26_ok,
    ttFiber8Row_27_ok,
    ttFiber8Row_28_ok,
    ttFiber8Row_29_ok,
    ttFiber8Row_30_ok,
    ttFiber8Row_31_ok,
    ttFiber8Row_32_ok,
    ttFiber8Row_33_ok,
    ttFiber8Row_34_ok,
    ttFiber8Row_35_ok,
    ttFiber8Row_36_ok,
    ttFiber8Row_37_ok,
    ttFiber8Row_38_ok,
    ttFiber8Row_39_ok,
    ttFiber8Row_40_ok,
    ttFiber8Row_41_ok,
    ttFiber8Row_42_ok,
    ttFiber8Row_43_ok,
    ttFiber8Row_44_ok,
    ttFiber8Row_45_ok,
    ttFiber8Row_46_ok,
    ttFiber8Row_47_ok,
    ttFiber8Row_48_ok,
    ttFiber8Row_49_ok,
    ttFiber8Row_50_ok,
    ttFiber8Row_51_ok,
    ttFiber8Row_52_ok,
    ttFiber8Row_53_ok,
    ttFiber8Row_54_ok,
    ttFiber8Row_55_ok,
    ttFiber8Row_56_ok,
    ttFiber8Row_57_ok,
    ttFiber8Row_58_ok,
    ttFiber8Row_59_ok,
    ttFiber8Row_60_ok,
    ttFiber8Row_61_ok,
    ttFiber8Row_62_ok,
    ttFiber8Row_63_ok,
    ttFiber8Parent_0_ok,
    ttFiber8Parent_1_ok,
    ttFiber8Parent_2_ok,
    ttFiber8Parent_3_ok,
    ttFiber8Parent_4_ok,
    ttFiber8Parent_5_ok,
    ttFiber8Parent_6_ok,
    ttFiber8Parent_7_ok,
    ttFiber8Parent_8_ok,
    ttFiber8Parent_9_ok,
    ttFiber8Parent_10_ok,
    ttFiber8Parent_11_ok,
    ttFiber8Parent_12_ok,
    ttFiber8Parent_13_ok,
    ttFiber8Parent_14_ok,
    ttFiber8Parent_15_ok,
    ttFiber8Parent_16_ok,
    ttFiber8Parent_17_ok,
    ttFiber8Parent_18_ok,
    ttFiber8Parent_19_ok,
    ttFiber8Parent_20_ok,
    ttFiber8Parent_21_ok,
    ttFiber8Parent_22_ok,
    ttFiber8Parent_23_ok,
    ttFiber8Parent_24_ok,
    ttFiber8Parent_25_ok,
    ttFiber8Parent_26_ok,
    ttFiber8Parent_27_ok,
    ttFiber8Parent_28_ok,
    ttFiber8Parent_29_ok,
    ttFiber8Parent_30_ok,
    ttFiber8Parent_31_ok,
    ttFiber8Parent_32_ok,
    ttFiber8Parent_33_ok,
    ttFiber8Parent_34_ok,
    ttFiber8Parent_35_ok,
    ttFiber8Parent_36_ok,
    ttFiber8Parent_37_ok,
    ttFiber8Parent_38_ok,
    ttFiber8Parent_39_ok,
    ttFiber8Parent_40_ok,
    ttFiber8Parent_41_ok,
    ttFiber8Parent_42_ok,
    ttFiber8Parent_43_ok,
    ttFiber8Parent_44_ok,
    ttFiber8Parent_45_ok,
    ttFiber8Parent_46_ok,
    ttFiber8Parent_47_ok,
    ttFiber8Parent_48_ok,
    ttFiber8Parent_49_ok,
    ttFiber8Parent_50_ok,
    ttFiber8Parent_51_ok,
    ttFiber8Parent_52_ok,
    ttFiber8Parent_53_ok,
    ttFiber8Parent_54_ok,
    ttFiber8Parent_55_ok,
    ttFiber8Parent_56_ok,
    ttFiber8Parent_57_ok,
    ttFiber8Parent_58_ok,
    ttFiber8Parent_59_ok,
    ttFiber8Parent_60_ok,
    ttFiber8Parent_61_ok,
    ttFiber8Parent_62_ok,
    ttFiber8Parent_63_ok]

def ttFiber9Key : List LColor :=
  [LColor.r, LColor.b, LColor.r, LColor.r]

def ttFiber9Expected : List Nat :=
  [600, 601, 602, 603, 604, 605, 606, 607]

def ttFiber9Rows : List DirectChainParentRow :=
  [ directRow 600 600 122 52 122 52 default
  , directRow 601 600 122 53 122 52 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 602 601 122 54 122 53 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 603 600 122 55 122 52 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 604 600 123 60 122 52 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 605 601 123 61 122 53 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 606 602 123 62 122 54 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 607 603 123 63 122 55 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  ]

def ttFiber9RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber9Rows i default

def ttFiber9SourcesCheck : Bool :=
  (ttFiber9Rows.map fun row => row.source) == ttFiber9Expected

theorem ttFiber9SourcesCheck_ok :
    ttFiber9SourcesCheck = true := by
  decide

def ttFiber9RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber9Key ttFiber9Expected (ttFiber9RowAt i)

theorem ttFiber9Row_0_ok : ttFiber9RowCheck 0 = true := by decide
theorem ttFiber9Row_1_ok : ttFiber9RowCheck 1 = true := by decide
theorem ttFiber9Row_2_ok : ttFiber9RowCheck 2 = true := by decide
theorem ttFiber9Row_3_ok : ttFiber9RowCheck 3 = true := by decide
theorem ttFiber9Row_4_ok : ttFiber9RowCheck 4 = true := by decide
theorem ttFiber9Row_5_ok : ttFiber9RowCheck 5 = true := by decide
theorem ttFiber9Row_6_ok : ttFiber9RowCheck 6 = true := by decide
theorem ttFiber9Row_7_ok : ttFiber9RowCheck 7 = true := by decide

def ttFiber9ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber9Rows ttMaxParentDepth (listGetD ttFiber9Expected i 0) == 600

theorem ttFiber9Parent_0_ok : ttFiber9ParentCheck 0 = true := by decide
theorem ttFiber9Parent_1_ok : ttFiber9ParentCheck 1 = true := by decide
theorem ttFiber9Parent_2_ok : ttFiber9ParentCheck 2 = true := by decide
theorem ttFiber9Parent_3_ok : ttFiber9ParentCheck 3 = true := by decide
theorem ttFiber9Parent_4_ok : ttFiber9ParentCheck 4 = true := by decide
theorem ttFiber9Parent_5_ok : ttFiber9ParentCheck 5 = true := by decide
theorem ttFiber9Parent_6_ok : ttFiber9ParentCheck 6 = true := by decide
theorem ttFiber9Parent_7_ok : ttFiber9ParentCheck 7 = true := by decide

def ttFiber9CertificateAudit : Bool :=
  ttFiber9SourcesCheck &&
    ttFiber9RowCheck 0 &&
    ttFiber9RowCheck 1 &&
    ttFiber9RowCheck 2 &&
    ttFiber9RowCheck 3 &&
    ttFiber9RowCheck 4 &&
    ttFiber9RowCheck 5 &&
    ttFiber9RowCheck 6 &&
    ttFiber9RowCheck 7 &&
    ttFiber9ParentCheck 0 &&
    ttFiber9ParentCheck 1 &&
    ttFiber9ParentCheck 2 &&
    ttFiber9ParentCheck 3 &&
    ttFiber9ParentCheck 4 &&
    ttFiber9ParentCheck 5 &&
    ttFiber9ParentCheck 6 &&
    ttFiber9ParentCheck 7

theorem ttFiber9CertificateAudit_ok :
    ttFiber9CertificateAudit = true := by
  simp [ttFiber9CertificateAudit,
    ttFiber9SourcesCheck_ok,
    ttFiber9Row_0_ok,
    ttFiber9Row_1_ok,
    ttFiber9Row_2_ok,
    ttFiber9Row_3_ok,
    ttFiber9Row_4_ok,
    ttFiber9Row_5_ok,
    ttFiber9Row_6_ok,
    ttFiber9Row_7_ok,
    ttFiber9Parent_0_ok,
    ttFiber9Parent_1_ok,
    ttFiber9Parent_2_ok,
    ttFiber9Parent_3_ok,
    ttFiber9Parent_4_ok,
    ttFiber9Parent_5_ok,
    ttFiber9Parent_6_ok,
    ttFiber9Parent_7_ok]

def ttFiber10Key : List LColor :=
  [LColor.r, LColor.b, LColor.r, LColor.b]

def ttFiber10Expected : List Nat :=
  [360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]

def ttFiber10Rows : List DirectChainParentRow :=
  [ directRow 360 360 72 80 72 80 default
  , directRow 361 360 72 81 72 80 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 362 360 72 82 72 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 363 361 72 83 72 81 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 364 362 72 100 72 82 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 365 367 72 101 72 103 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 366 361 72 102 72 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 367 360 72 103 72 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 368 360 73 88 72 80 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 369 361 73 89 72 81 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 370 362 73 90 72 82 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 371 363 73 91 72 83 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 372 364 73 108 72 100 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 373 365 73 109 72 101 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 374 366 73 110 72 102 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 375 367 73 111 72 103 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 376 360 74 16 72 80 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 377 361 74 17 72 81 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 378 362 74 18 72 82 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 379 363 74 19 72 83 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 380 376 74 32 74 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 381 377 74 33 74 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 382 366 74 34 72 102 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 383 367 74 35 72 103 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 384 368 75 24 73 88 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 385 369 75 25 73 89 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 386 370 75 26 73 90 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 387 371 75 27 73 91 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 388 384 75 40 75 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 389 385 75 41 75 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 390 374 75 42 73 110 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 391 375 75 43 73 111 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 608 624 124 132 126 64 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 609 625 124 133 126 65 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 610 382 124 134 74 34 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 611 383 124 135 74 35 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 612 378 124 180 74 18 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 613 615 124 181 124 183 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 614 377 124 182 74 17 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 615 376 124 183 74 16 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 616 632 125 140 127 72 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 617 633 125 141 127 73 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 618 634 125 142 127 74 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 619 616 125 143 125 140 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 620 616 125 188 125 140 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 621 617 125 189 125 141 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 622 638 125 190 127 126 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 623 639 125 191 127 127 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 624 368 126 64 73 88 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 625 369 126 65 73 89 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 626 370 126 66 73 90 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 627 371 126 67 73 91 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 628 372 126 116 73 108 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 629 373 126 117 73 109 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 630 374 126 118 73 110 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 631 375 126 119 73 111 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 632 360 127 72 72 80 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 633 361 127 73 72 81 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 634 362 127 74 72 82 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 635 363 127 75 72 83 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 636 364 127 124 72 100 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 637 365 127 125 72 101 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 638 366 127 126 72 102 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 639 367 127 127 72 103 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  ]

def ttFiber10RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber10Rows i default

def ttFiber10SourcesCheck : Bool :=
  (ttFiber10Rows.map fun row => row.source) == ttFiber10Expected

theorem ttFiber10SourcesCheck_ok :
    ttFiber10SourcesCheck = true := by
  decide

def ttFiber10RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt i)

theorem ttFiber10Row_0_ok : ttFiber10RowCheck 0 = true := by decide
theorem ttFiber10Row_1_ok : ttFiber10RowCheck 1 = true := by decide
theorem ttFiber10Row_2_ok : ttFiber10RowCheck 2 = true := by decide
theorem ttFiber10Row_3_ok : ttFiber10RowCheck 3 = true := by decide
theorem ttFiber10Row_4_ok : ttFiber10RowCheck 4 = true := by decide
theorem ttFiber10Row_5_ok : ttFiber10RowCheck 5 = true := by decide
theorem ttFiber10Row_6_ok : ttFiber10RowCheck 6 = true := by decide
theorem ttFiber10Row_7_ok : ttFiber10RowCheck 7 = true := by decide
theorem ttFiber10Row_8_ok : ttFiber10RowCheck 8 = true := by decide
theorem ttFiber10Row_9_ok : ttFiber10RowCheck 9 = true := by decide
theorem ttFiber10Row_10_ok : ttFiber10RowCheck 10 = true := by decide
theorem ttFiber10Row_11_ok : ttFiber10RowCheck 11 = true := by decide
theorem ttFiber10Row_12_ok : ttFiber10RowCheck 12 = true := by decide
theorem ttFiber10Row_13_ok : ttFiber10RowCheck 13 = true := by decide
theorem ttFiber10Row_14_ok : ttFiber10RowCheck 14 = true := by decide
theorem ttFiber10Row_15_ok : ttFiber10RowCheck 15 = true := by decide
theorem ttFiber10Row_16_ok : ttFiber10RowCheck 16 = true := by decide
theorem ttFiber10Row_17_ok : ttFiber10RowCheck 17 = true := by decide
theorem ttFiber10Row_18_ok : ttFiber10RowCheck 18 = true := by decide
theorem ttFiber10Row_19_ok : ttFiber10RowCheck 19 = true := by decide
theorem ttFiber10Row_20_ok : ttFiber10RowCheck 20 = true := by decide
theorem ttFiber10Row_21_ok : ttFiber10RowCheck 21 = true := by decide
theorem ttFiber10Row_22_ok : ttFiber10RowCheck 22 = true := by decide
theorem ttFiber10Row_23_ok : ttFiber10RowCheck 23 = true := by decide
theorem ttFiber10Row_24_ok : ttFiber10RowCheck 24 = true := by decide
theorem ttFiber10Row_25_ok : ttFiber10RowCheck 25 = true := by decide
theorem ttFiber10Row_26_ok : ttFiber10RowCheck 26 = true := by decide
theorem ttFiber10Row_27_ok : ttFiber10RowCheck 27 = true := by decide
theorem ttFiber10Row_28_ok : ttFiber10RowCheck 28 = true := by decide
theorem ttFiber10Row_29_ok : ttFiber10RowCheck 29 = true := by decide
theorem ttFiber10Row_30_ok : ttFiber10RowCheck 30 = true := by decide
theorem ttFiber10Row_31_ok : ttFiber10RowCheck 31 = true := by decide
theorem ttFiber10Row_32_ok : ttFiber10RowCheck 32 = true := by decide
theorem ttFiber10Row_33_ok : ttFiber10RowCheck 33 = true := by decide
theorem ttFiber10Row_34_ok : ttFiber10RowCheck 34 = true := by decide
theorem ttFiber10Row_35_ok : ttFiber10RowCheck 35 = true := by decide
theorem ttFiber10Row_36_ok : ttFiber10RowCheck 36 = true := by decide
theorem ttFiber10Row_37_ok : ttFiber10RowCheck 37 = true := by decide
theorem ttFiber10Row_38_ok : ttFiber10RowCheck 38 = true := by decide
theorem ttFiber10Row_39_ok : ttFiber10RowCheck 39 = true := by decide
theorem ttFiber10Row_40_ok : ttFiber10RowCheck 40 = true := by decide
theorem ttFiber10Row_41_ok : ttFiber10RowCheck 41 = true := by decide
theorem ttFiber10Row_42_ok : ttFiber10RowCheck 42 = true := by decide
theorem ttFiber10Row_43_ok : ttFiber10RowCheck 43 = true := by decide
theorem ttFiber10Row_44_ok : ttFiber10RowCheck 44 = true := by decide
theorem ttFiber10Row_45_ok : ttFiber10RowCheck 45 = true := by decide
theorem ttFiber10Row_46_ok : ttFiber10RowCheck 46 = true := by decide
theorem ttFiber10Row_47_ok : ttFiber10RowCheck 47 = true := by decide
theorem ttFiber10Row_48_ok : ttFiber10RowCheck 48 = true := by decide
theorem ttFiber10Row_49_ok : ttFiber10RowCheck 49 = true := by decide
theorem ttFiber10Row_50_ok : ttFiber10RowCheck 50 = true := by decide
theorem ttFiber10Row_51_ok : ttFiber10RowCheck 51 = true := by decide
theorem ttFiber10Row_52_ok : ttFiber10RowCheck 52 = true := by decide
theorem ttFiber10Row_53_ok : ttFiber10RowCheck 53 = true := by decide
theorem ttFiber10Row_54_ok : ttFiber10RowCheck 54 = true := by decide
theorem ttFiber10Row_55_ok : ttFiber10RowCheck 55 = true := by decide
theorem ttFiber10Row_56_ok : ttFiber10RowCheck 56 = true := by decide
theorem ttFiber10Row_57_ok : ttFiber10RowCheck 57 = true := by decide
theorem ttFiber10Row_58_ok : ttFiber10RowCheck 58 = true := by decide
theorem ttFiber10Row_59_ok : ttFiber10RowCheck 59 = true := by decide
theorem ttFiber10Row_60_ok : ttFiber10RowCheck 60 = true := by decide
theorem ttFiber10Row_61_ok : ttFiber10RowCheck 61 = true := by decide
theorem ttFiber10Row_62_ok : ttFiber10RowCheck 62 = true := by decide
theorem ttFiber10Row_63_ok : ttFiber10RowCheck 63 = true := by decide

def ttFiber10ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber10Rows ttMaxParentDepth (listGetD ttFiber10Expected i 0) == 360

theorem ttFiber10Parent_0_ok : ttFiber10ParentCheck 0 = true := by decide
theorem ttFiber10Parent_1_ok : ttFiber10ParentCheck 1 = true := by decide
theorem ttFiber10Parent_2_ok : ttFiber10ParentCheck 2 = true := by decide
theorem ttFiber10Parent_3_ok : ttFiber10ParentCheck 3 = true := by decide
theorem ttFiber10Parent_4_ok : ttFiber10ParentCheck 4 = true := by decide
theorem ttFiber10Parent_5_ok : ttFiber10ParentCheck 5 = true := by decide
theorem ttFiber10Parent_6_ok : ttFiber10ParentCheck 6 = true := by decide
theorem ttFiber10Parent_7_ok : ttFiber10ParentCheck 7 = true := by decide
theorem ttFiber10Parent_8_ok : ttFiber10ParentCheck 8 = true := by decide
theorem ttFiber10Parent_9_ok : ttFiber10ParentCheck 9 = true := by decide
theorem ttFiber10Parent_10_ok : ttFiber10ParentCheck 10 = true := by decide
theorem ttFiber10Parent_11_ok : ttFiber10ParentCheck 11 = true := by decide
theorem ttFiber10Parent_12_ok : ttFiber10ParentCheck 12 = true := by decide
theorem ttFiber10Parent_13_ok : ttFiber10ParentCheck 13 = true := by decide
theorem ttFiber10Parent_14_ok : ttFiber10ParentCheck 14 = true := by decide
theorem ttFiber10Parent_15_ok : ttFiber10ParentCheck 15 = true := by decide
theorem ttFiber10Parent_16_ok : ttFiber10ParentCheck 16 = true := by decide
theorem ttFiber10Parent_17_ok : ttFiber10ParentCheck 17 = true := by decide
theorem ttFiber10Parent_18_ok : ttFiber10ParentCheck 18 = true := by decide
theorem ttFiber10Parent_19_ok : ttFiber10ParentCheck 19 = true := by decide
theorem ttFiber10Parent_20_ok : ttFiber10ParentCheck 20 = true := by decide
theorem ttFiber10Parent_21_ok : ttFiber10ParentCheck 21 = true := by decide
theorem ttFiber10Parent_22_ok : ttFiber10ParentCheck 22 = true := by decide
theorem ttFiber10Parent_23_ok : ttFiber10ParentCheck 23 = true := by decide
theorem ttFiber10Parent_24_ok : ttFiber10ParentCheck 24 = true := by decide
theorem ttFiber10Parent_25_ok : ttFiber10ParentCheck 25 = true := by decide
theorem ttFiber10Parent_26_ok : ttFiber10ParentCheck 26 = true := by decide
theorem ttFiber10Parent_27_ok : ttFiber10ParentCheck 27 = true := by decide
theorem ttFiber10Parent_28_ok : ttFiber10ParentCheck 28 = true := by decide
theorem ttFiber10Parent_29_ok : ttFiber10ParentCheck 29 = true := by decide
theorem ttFiber10Parent_30_ok : ttFiber10ParentCheck 30 = true := by decide
theorem ttFiber10Parent_31_ok : ttFiber10ParentCheck 31 = true := by decide
theorem ttFiber10Parent_32_ok : ttFiber10ParentCheck 32 = true := by decide
theorem ttFiber10Parent_33_ok : ttFiber10ParentCheck 33 = true := by decide
theorem ttFiber10Parent_34_ok : ttFiber10ParentCheck 34 = true := by decide
theorem ttFiber10Parent_35_ok : ttFiber10ParentCheck 35 = true := by decide
theorem ttFiber10Parent_36_ok : ttFiber10ParentCheck 36 = true := by decide
theorem ttFiber10Parent_37_ok : ttFiber10ParentCheck 37 = true := by decide
theorem ttFiber10Parent_38_ok : ttFiber10ParentCheck 38 = true := by decide
theorem ttFiber10Parent_39_ok : ttFiber10ParentCheck 39 = true := by decide
theorem ttFiber10Parent_40_ok : ttFiber10ParentCheck 40 = true := by decide
theorem ttFiber10Parent_41_ok : ttFiber10ParentCheck 41 = true := by decide
theorem ttFiber10Parent_42_ok : ttFiber10ParentCheck 42 = true := by decide
theorem ttFiber10Parent_43_ok : ttFiber10ParentCheck 43 = true := by decide
theorem ttFiber10Parent_44_ok : ttFiber10ParentCheck 44 = true := by decide
theorem ttFiber10Parent_45_ok : ttFiber10ParentCheck 45 = true := by decide
theorem ttFiber10Parent_46_ok : ttFiber10ParentCheck 46 = true := by decide
theorem ttFiber10Parent_47_ok : ttFiber10ParentCheck 47 = true := by decide
theorem ttFiber10Parent_48_ok : ttFiber10ParentCheck 48 = true := by decide
theorem ttFiber10Parent_49_ok : ttFiber10ParentCheck 49 = true := by decide
theorem ttFiber10Parent_50_ok : ttFiber10ParentCheck 50 = true := by decide
theorem ttFiber10Parent_51_ok : ttFiber10ParentCheck 51 = true := by decide
theorem ttFiber10Parent_52_ok : ttFiber10ParentCheck 52 = true := by decide
theorem ttFiber10Parent_53_ok : ttFiber10ParentCheck 53 = true := by decide
theorem ttFiber10Parent_54_ok : ttFiber10ParentCheck 54 = true := by decide
theorem ttFiber10Parent_55_ok : ttFiber10ParentCheck 55 = true := by decide
theorem ttFiber10Parent_56_ok : ttFiber10ParentCheck 56 = true := by decide
theorem ttFiber10Parent_57_ok : ttFiber10ParentCheck 57 = true := by decide
theorem ttFiber10Parent_58_ok : ttFiber10ParentCheck 58 = true := by decide
theorem ttFiber10Parent_59_ok : ttFiber10ParentCheck 59 = true := by decide
theorem ttFiber10Parent_60_ok : ttFiber10ParentCheck 60 = true := by decide
theorem ttFiber10Parent_61_ok : ttFiber10ParentCheck 61 = true := by decide
theorem ttFiber10Parent_62_ok : ttFiber10ParentCheck 62 = true := by decide
theorem ttFiber10Parent_63_ok : ttFiber10ParentCheck 63 = true := by decide

def ttFiber10CertificateAudit : Bool :=
  ttFiber10SourcesCheck &&
    ttFiber10RowCheck 0 &&
    ttFiber10RowCheck 1 &&
    ttFiber10RowCheck 2 &&
    ttFiber10RowCheck 3 &&
    ttFiber10RowCheck 4 &&
    ttFiber10RowCheck 5 &&
    ttFiber10RowCheck 6 &&
    ttFiber10RowCheck 7 &&
    ttFiber10RowCheck 8 &&
    ttFiber10RowCheck 9 &&
    ttFiber10RowCheck 10 &&
    ttFiber10RowCheck 11 &&
    ttFiber10RowCheck 12 &&
    ttFiber10RowCheck 13 &&
    ttFiber10RowCheck 14 &&
    ttFiber10RowCheck 15 &&
    ttFiber10RowCheck 16 &&
    ttFiber10RowCheck 17 &&
    ttFiber10RowCheck 18 &&
    ttFiber10RowCheck 19 &&
    ttFiber10RowCheck 20 &&
    ttFiber10RowCheck 21 &&
    ttFiber10RowCheck 22 &&
    ttFiber10RowCheck 23 &&
    ttFiber10RowCheck 24 &&
    ttFiber10RowCheck 25 &&
    ttFiber10RowCheck 26 &&
    ttFiber10RowCheck 27 &&
    ttFiber10RowCheck 28 &&
    ttFiber10RowCheck 29 &&
    ttFiber10RowCheck 30 &&
    ttFiber10RowCheck 31 &&
    ttFiber10RowCheck 32 &&
    ttFiber10RowCheck 33 &&
    ttFiber10RowCheck 34 &&
    ttFiber10RowCheck 35 &&
    ttFiber10RowCheck 36 &&
    ttFiber10RowCheck 37 &&
    ttFiber10RowCheck 38 &&
    ttFiber10RowCheck 39 &&
    ttFiber10RowCheck 40 &&
    ttFiber10RowCheck 41 &&
    ttFiber10RowCheck 42 &&
    ttFiber10RowCheck 43 &&
    ttFiber10RowCheck 44 &&
    ttFiber10RowCheck 45 &&
    ttFiber10RowCheck 46 &&
    ttFiber10RowCheck 47 &&
    ttFiber10RowCheck 48 &&
    ttFiber10RowCheck 49 &&
    ttFiber10RowCheck 50 &&
    ttFiber10RowCheck 51 &&
    ttFiber10RowCheck 52 &&
    ttFiber10RowCheck 53 &&
    ttFiber10RowCheck 54 &&
    ttFiber10RowCheck 55 &&
    ttFiber10RowCheck 56 &&
    ttFiber10RowCheck 57 &&
    ttFiber10RowCheck 58 &&
    ttFiber10RowCheck 59 &&
    ttFiber10RowCheck 60 &&
    ttFiber10RowCheck 61 &&
    ttFiber10RowCheck 62 &&
    ttFiber10RowCheck 63 &&
    ttFiber10ParentCheck 0 &&
    ttFiber10ParentCheck 1 &&
    ttFiber10ParentCheck 2 &&
    ttFiber10ParentCheck 3 &&
    ttFiber10ParentCheck 4 &&
    ttFiber10ParentCheck 5 &&
    ttFiber10ParentCheck 6 &&
    ttFiber10ParentCheck 7 &&
    ttFiber10ParentCheck 8 &&
    ttFiber10ParentCheck 9 &&
    ttFiber10ParentCheck 10 &&
    ttFiber10ParentCheck 11 &&
    ttFiber10ParentCheck 12 &&
    ttFiber10ParentCheck 13 &&
    ttFiber10ParentCheck 14 &&
    ttFiber10ParentCheck 15 &&
    ttFiber10ParentCheck 16 &&
    ttFiber10ParentCheck 17 &&
    ttFiber10ParentCheck 18 &&
    ttFiber10ParentCheck 19 &&
    ttFiber10ParentCheck 20 &&
    ttFiber10ParentCheck 21 &&
    ttFiber10ParentCheck 22 &&
    ttFiber10ParentCheck 23 &&
    ttFiber10ParentCheck 24 &&
    ttFiber10ParentCheck 25 &&
    ttFiber10ParentCheck 26 &&
    ttFiber10ParentCheck 27 &&
    ttFiber10ParentCheck 28 &&
    ttFiber10ParentCheck 29 &&
    ttFiber10ParentCheck 30 &&
    ttFiber10ParentCheck 31 &&
    ttFiber10ParentCheck 32 &&
    ttFiber10ParentCheck 33 &&
    ttFiber10ParentCheck 34 &&
    ttFiber10ParentCheck 35 &&
    ttFiber10ParentCheck 36 &&
    ttFiber10ParentCheck 37 &&
    ttFiber10ParentCheck 38 &&
    ttFiber10ParentCheck 39 &&
    ttFiber10ParentCheck 40 &&
    ttFiber10ParentCheck 41 &&
    ttFiber10ParentCheck 42 &&
    ttFiber10ParentCheck 43 &&
    ttFiber10ParentCheck 44 &&
    ttFiber10ParentCheck 45 &&
    ttFiber10ParentCheck 46 &&
    ttFiber10ParentCheck 47 &&
    ttFiber10ParentCheck 48 &&
    ttFiber10ParentCheck 49 &&
    ttFiber10ParentCheck 50 &&
    ttFiber10ParentCheck 51 &&
    ttFiber10ParentCheck 52 &&
    ttFiber10ParentCheck 53 &&
    ttFiber10ParentCheck 54 &&
    ttFiber10ParentCheck 55 &&
    ttFiber10ParentCheck 56 &&
    ttFiber10ParentCheck 57 &&
    ttFiber10ParentCheck 58 &&
    ttFiber10ParentCheck 59 &&
    ttFiber10ParentCheck 60 &&
    ttFiber10ParentCheck 61 &&
    ttFiber10ParentCheck 62 &&
    ttFiber10ParentCheck 63

theorem ttFiber10CertificateAudit_ok :
    ttFiber10CertificateAudit = true := by
  simp [ttFiber10CertificateAudit,
    ttFiber10SourcesCheck_ok,
    ttFiber10Row_0_ok,
    ttFiber10Row_1_ok,
    ttFiber10Row_2_ok,
    ttFiber10Row_3_ok,
    ttFiber10Row_4_ok,
    ttFiber10Row_5_ok,
    ttFiber10Row_6_ok,
    ttFiber10Row_7_ok,
    ttFiber10Row_8_ok,
    ttFiber10Row_9_ok,
    ttFiber10Row_10_ok,
    ttFiber10Row_11_ok,
    ttFiber10Row_12_ok,
    ttFiber10Row_13_ok,
    ttFiber10Row_14_ok,
    ttFiber10Row_15_ok,
    ttFiber10Row_16_ok,
    ttFiber10Row_17_ok,
    ttFiber10Row_18_ok,
    ttFiber10Row_19_ok,
    ttFiber10Row_20_ok,
    ttFiber10Row_21_ok,
    ttFiber10Row_22_ok,
    ttFiber10Row_23_ok,
    ttFiber10Row_24_ok,
    ttFiber10Row_25_ok,
    ttFiber10Row_26_ok,
    ttFiber10Row_27_ok,
    ttFiber10Row_28_ok,
    ttFiber10Row_29_ok,
    ttFiber10Row_30_ok,
    ttFiber10Row_31_ok,
    ttFiber10Row_32_ok,
    ttFiber10Row_33_ok,
    ttFiber10Row_34_ok,
    ttFiber10Row_35_ok,
    ttFiber10Row_36_ok,
    ttFiber10Row_37_ok,
    ttFiber10Row_38_ok,
    ttFiber10Row_39_ok,
    ttFiber10Row_40_ok,
    ttFiber10Row_41_ok,
    ttFiber10Row_42_ok,
    ttFiber10Row_43_ok,
    ttFiber10Row_44_ok,
    ttFiber10Row_45_ok,
    ttFiber10Row_46_ok,
    ttFiber10Row_47_ok,
    ttFiber10Row_48_ok,
    ttFiber10Row_49_ok,
    ttFiber10Row_50_ok,
    ttFiber10Row_51_ok,
    ttFiber10Row_52_ok,
    ttFiber10Row_53_ok,
    ttFiber10Row_54_ok,
    ttFiber10Row_55_ok,
    ttFiber10Row_56_ok,
    ttFiber10Row_57_ok,
    ttFiber10Row_58_ok,
    ttFiber10Row_59_ok,
    ttFiber10Row_60_ok,
    ttFiber10Row_61_ok,
    ttFiber10Row_62_ok,
    ttFiber10Row_63_ok,
    ttFiber10Parent_0_ok,
    ttFiber10Parent_1_ok,
    ttFiber10Parent_2_ok,
    ttFiber10Parent_3_ok,
    ttFiber10Parent_4_ok,
    ttFiber10Parent_5_ok,
    ttFiber10Parent_6_ok,
    ttFiber10Parent_7_ok,
    ttFiber10Parent_8_ok,
    ttFiber10Parent_9_ok,
    ttFiber10Parent_10_ok,
    ttFiber10Parent_11_ok,
    ttFiber10Parent_12_ok,
    ttFiber10Parent_13_ok,
    ttFiber10Parent_14_ok,
    ttFiber10Parent_15_ok,
    ttFiber10Parent_16_ok,
    ttFiber10Parent_17_ok,
    ttFiber10Parent_18_ok,
    ttFiber10Parent_19_ok,
    ttFiber10Parent_20_ok,
    ttFiber10Parent_21_ok,
    ttFiber10Parent_22_ok,
    ttFiber10Parent_23_ok,
    ttFiber10Parent_24_ok,
    ttFiber10Parent_25_ok,
    ttFiber10Parent_26_ok,
    ttFiber10Parent_27_ok,
    ttFiber10Parent_28_ok,
    ttFiber10Parent_29_ok,
    ttFiber10Parent_30_ok,
    ttFiber10Parent_31_ok,
    ttFiber10Parent_32_ok,
    ttFiber10Parent_33_ok,
    ttFiber10Parent_34_ok,
    ttFiber10Parent_35_ok,
    ttFiber10Parent_36_ok,
    ttFiber10Parent_37_ok,
    ttFiber10Parent_38_ok,
    ttFiber10Parent_39_ok,
    ttFiber10Parent_40_ok,
    ttFiber10Parent_41_ok,
    ttFiber10Parent_42_ok,
    ttFiber10Parent_43_ok,
    ttFiber10Parent_44_ok,
    ttFiber10Parent_45_ok,
    ttFiber10Parent_46_ok,
    ttFiber10Parent_47_ok,
    ttFiber10Parent_48_ok,
    ttFiber10Parent_49_ok,
    ttFiber10Parent_50_ok,
    ttFiber10Parent_51_ok,
    ttFiber10Parent_52_ok,
    ttFiber10Parent_53_ok,
    ttFiber10Parent_54_ok,
    ttFiber10Parent_55_ok,
    ttFiber10Parent_56_ok,
    ttFiber10Parent_57_ok,
    ttFiber10Parent_58_ok,
    ttFiber10Parent_59_ok,
    ttFiber10Parent_60_ok,
    ttFiber10Parent_61_ok,
    ttFiber10Parent_62_ok,
    ttFiber10Parent_63_ok]

def ttFiber11Key : List LColor :=
  [LColor.r, LColor.b, LColor.r, LColor.p]

def ttFiber11Expected : List Nat :=
  [392, 393, 394, 395, 396, 397, 398, 399]

def ttFiber11Rows : List DirectChainParentRow :=
  [ directRow 392 392 76 144 76 144 default
  , directRow 393 392 76 145 76 144 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 394 393 76 146 76 145 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 395 392 76 147 76 144 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 396 392 77 152 76 144 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 397 393 77 153 76 145 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 398 394 77 154 76 146 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 399 395 77 155 76 147 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  ]

def ttFiber11RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber11Rows i default

def ttFiber11SourcesCheck : Bool :=
  (ttFiber11Rows.map fun row => row.source) == ttFiber11Expected

theorem ttFiber11SourcesCheck_ok :
    ttFiber11SourcesCheck = true := by
  decide

def ttFiber11RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber11Key ttFiber11Expected (ttFiber11RowAt i)

theorem ttFiber11Row_0_ok : ttFiber11RowCheck 0 = true := by decide
theorem ttFiber11Row_1_ok : ttFiber11RowCheck 1 = true := by decide
theorem ttFiber11Row_2_ok : ttFiber11RowCheck 2 = true := by decide
theorem ttFiber11Row_3_ok : ttFiber11RowCheck 3 = true := by decide
theorem ttFiber11Row_4_ok : ttFiber11RowCheck 4 = true := by decide
theorem ttFiber11Row_5_ok : ttFiber11RowCheck 5 = true := by decide
theorem ttFiber11Row_6_ok : ttFiber11RowCheck 6 = true := by decide
theorem ttFiber11Row_7_ok : ttFiber11RowCheck 7 = true := by decide

def ttFiber11ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber11Rows ttMaxParentDepth (listGetD ttFiber11Expected i 0) == 392

theorem ttFiber11Parent_0_ok : ttFiber11ParentCheck 0 = true := by decide
theorem ttFiber11Parent_1_ok : ttFiber11ParentCheck 1 = true := by decide
theorem ttFiber11Parent_2_ok : ttFiber11ParentCheck 2 = true := by decide
theorem ttFiber11Parent_3_ok : ttFiber11ParentCheck 3 = true := by decide
theorem ttFiber11Parent_4_ok : ttFiber11ParentCheck 4 = true := by decide
theorem ttFiber11Parent_5_ok : ttFiber11ParentCheck 5 = true := by decide
theorem ttFiber11Parent_6_ok : ttFiber11ParentCheck 6 = true := by decide
theorem ttFiber11Parent_7_ok : ttFiber11ParentCheck 7 = true := by decide

def ttFiber11CertificateAudit : Bool :=
  ttFiber11SourcesCheck &&
    ttFiber11RowCheck 0 &&
    ttFiber11RowCheck 1 &&
    ttFiber11RowCheck 2 &&
    ttFiber11RowCheck 3 &&
    ttFiber11RowCheck 4 &&
    ttFiber11RowCheck 5 &&
    ttFiber11RowCheck 6 &&
    ttFiber11RowCheck 7 &&
    ttFiber11ParentCheck 0 &&
    ttFiber11ParentCheck 1 &&
    ttFiber11ParentCheck 2 &&
    ttFiber11ParentCheck 3 &&
    ttFiber11ParentCheck 4 &&
    ttFiber11ParentCheck 5 &&
    ttFiber11ParentCheck 6 &&
    ttFiber11ParentCheck 7

theorem ttFiber11CertificateAudit_ok :
    ttFiber11CertificateAudit = true := by
  simp [ttFiber11CertificateAudit,
    ttFiber11SourcesCheck_ok,
    ttFiber11Row_0_ok,
    ttFiber11Row_1_ok,
    ttFiber11Row_2_ok,
    ttFiber11Row_3_ok,
    ttFiber11Row_4_ok,
    ttFiber11Row_5_ok,
    ttFiber11Row_6_ok,
    ttFiber11Row_7_ok,
    ttFiber11Parent_0_ok,
    ttFiber11Parent_1_ok,
    ttFiber11Parent_2_ok,
    ttFiber11Parent_3_ok,
    ttFiber11Parent_4_ok,
    ttFiber11Parent_5_ok,
    ttFiber11Parent_6_ok,
    ttFiber11Parent_7_ok]

def ttFiber12Key : List LColor :=
  [LColor.r, LColor.b, LColor.b, LColor.r]

def ttFiber12Expected : List Nat :=
  []

def ttFiber12Rows : List DirectChainParentRow :=
  []

def ttFiber12RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber12Rows i default

def ttFiber12SourcesCheck : Bool :=
  (ttFiber12Rows.map fun row => row.source) == ttFiber12Expected

theorem ttFiber12SourcesCheck_ok :
    ttFiber12SourcesCheck = true := by
  decide

def ttFiber12RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber12Key ttFiber12Expected (ttFiber12RowAt i)

def ttFiber12ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber12Rows ttMaxParentDepth (listGetD ttFiber12Expected i 0) == 0

def ttFiber12CertificateAudit : Bool :=
  ttFiber12SourcesCheck

theorem ttFiber12CertificateAudit_ok :
    ttFiber12CertificateAudit = true := by
  simp [ttFiber12CertificateAudit,
    ttFiber12SourcesCheck_ok]

def ttFiber13Key : List LColor :=
  [LColor.r, LColor.b, LColor.b, LColor.b]

def ttFiber13Expected : List Nat :=
  []

def ttFiber13Rows : List DirectChainParentRow :=
  []

def ttFiber13RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber13Rows i default

def ttFiber13SourcesCheck : Bool :=
  (ttFiber13Rows.map fun row => row.source) == ttFiber13Expected

theorem ttFiber13SourcesCheck_ok :
    ttFiber13SourcesCheck = true := by
  decide

def ttFiber13RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber13Key ttFiber13Expected (ttFiber13RowAt i)

def ttFiber13ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber13Rows ttMaxParentDepth (listGetD ttFiber13Expected i 0) == 0

def ttFiber13CertificateAudit : Bool :=
  ttFiber13SourcesCheck

theorem ttFiber13CertificateAudit_ok :
    ttFiber13CertificateAudit = true := by
  simp [ttFiber13CertificateAudit,
    ttFiber13SourcesCheck_ok]

def ttFiber14Key : List LColor :=
  [LColor.r, LColor.b, LColor.b, LColor.p]

def ttFiber14Expected : List Nat :=
  []

def ttFiber14Rows : List DirectChainParentRow :=
  []

def ttFiber14RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber14Rows i default

def ttFiber14SourcesCheck : Bool :=
  (ttFiber14Rows.map fun row => row.source) == ttFiber14Expected

theorem ttFiber14SourcesCheck_ok :
    ttFiber14SourcesCheck = true := by
  decide

def ttFiber14RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber14Key ttFiber14Expected (ttFiber14RowAt i)

def ttFiber14ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber14Rows ttMaxParentDepth (listGetD ttFiber14Expected i 0) == 0

def ttFiber14CertificateAudit : Bool :=
  ttFiber14SourcesCheck

theorem ttFiber14CertificateAudit_ok :
    ttFiber14CertificateAudit = true := by
  simp [ttFiber14CertificateAudit,
    ttFiber14SourcesCheck_ok]

def ttFiber15Key : List LColor :=
  [LColor.r, LColor.b, LColor.p, LColor.r]

def ttFiber15Expected : List Nat :=
  []

def ttFiber15Rows : List DirectChainParentRow :=
  []

def ttFiber15RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber15Rows i default

def ttFiber15SourcesCheck : Bool :=
  (ttFiber15Rows.map fun row => row.source) == ttFiber15Expected

theorem ttFiber15SourcesCheck_ok :
    ttFiber15SourcesCheck = true := by
  decide

def ttFiber15RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber15Key ttFiber15Expected (ttFiber15RowAt i)

def ttFiber15ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber15Rows ttMaxParentDepth (listGetD ttFiber15Expected i 0) == 0

def ttFiber15CertificateAudit : Bool :=
  ttFiber15SourcesCheck

theorem ttFiber15CertificateAudit_ok :
    ttFiber15CertificateAudit = true := by
  simp [ttFiber15CertificateAudit,
    ttFiber15SourcesCheck_ok]

def ttFiber16Key : List LColor :=
  [LColor.r, LColor.b, LColor.p, LColor.b]

def ttFiber16Expected : List Nat :=
  []

def ttFiber16Rows : List DirectChainParentRow :=
  []

def ttFiber16RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber16Rows i default

def ttFiber16SourcesCheck : Bool :=
  (ttFiber16Rows.map fun row => row.source) == ttFiber16Expected

theorem ttFiber16SourcesCheck_ok :
    ttFiber16SourcesCheck = true := by
  decide

def ttFiber16RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber16Key ttFiber16Expected (ttFiber16RowAt i)

def ttFiber16ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber16Rows ttMaxParentDepth (listGetD ttFiber16Expected i 0) == 0

def ttFiber16CertificateAudit : Bool :=
  ttFiber16SourcesCheck

theorem ttFiber16CertificateAudit_ok :
    ttFiber16CertificateAudit = true := by
  simp [ttFiber16CertificateAudit,
    ttFiber16SourcesCheck_ok]

def ttFiber17Key : List LColor :=
  [LColor.r, LColor.b, LColor.p, LColor.p]

def ttFiber17Expected : List Nat :=
  []

def ttFiber17Rows : List DirectChainParentRow :=
  []

def ttFiber17RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber17Rows i default

def ttFiber17SourcesCheck : Bool :=
  (ttFiber17Rows.map fun row => row.source) == ttFiber17Expected

theorem ttFiber17SourcesCheck_ok :
    ttFiber17SourcesCheck = true := by
  decide

def ttFiber17RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber17Key ttFiber17Expected (ttFiber17RowAt i)

def ttFiber17ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber17Rows ttMaxParentDepth (listGetD ttFiber17Expected i 0) == 0

def ttFiber17CertificateAudit : Bool :=
  ttFiber17SourcesCheck

theorem ttFiber17CertificateAudit_ok :
    ttFiber17CertificateAudit = true := by
  simp [ttFiber17CertificateAudit,
    ttFiber17SourcesCheck_ok]

def ttFiber18Key : List LColor :=
  [LColor.r, LColor.p, LColor.r, LColor.r]

def ttFiber18Expected : List Nat :=
  [920, 921, 922, 923, 924, 925, 926, 927]

def ttFiber18Rows : List DirectChainParentRow :=
  [ directRow 920 920 184 20 184 20 default
  , directRow 921 920 184 21 184 20 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 922 920 184 22 184 20 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 923 921 184 23 184 21 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 924 920 185 28 184 20 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 925 921 185 29 184 21 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 926 922 185 30 184 22 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 927 923 185 31 184 23 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  ]

def ttFiber18RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber18Rows i default

def ttFiber18SourcesCheck : Bool :=
  (ttFiber18Rows.map fun row => row.source) == ttFiber18Expected

theorem ttFiber18SourcesCheck_ok :
    ttFiber18SourcesCheck = true := by
  decide

def ttFiber18RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber18Key ttFiber18Expected (ttFiber18RowAt i)

theorem ttFiber18Row_0_ok : ttFiber18RowCheck 0 = true := by decide
theorem ttFiber18Row_1_ok : ttFiber18RowCheck 1 = true := by decide
theorem ttFiber18Row_2_ok : ttFiber18RowCheck 2 = true := by decide
theorem ttFiber18Row_3_ok : ttFiber18RowCheck 3 = true := by decide
theorem ttFiber18Row_4_ok : ttFiber18RowCheck 4 = true := by decide
theorem ttFiber18Row_5_ok : ttFiber18RowCheck 5 = true := by decide
theorem ttFiber18Row_6_ok : ttFiber18RowCheck 6 = true := by decide
theorem ttFiber18Row_7_ok : ttFiber18RowCheck 7 = true := by decide

def ttFiber18ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber18Rows ttMaxParentDepth (listGetD ttFiber18Expected i 0) == 920

theorem ttFiber18Parent_0_ok : ttFiber18ParentCheck 0 = true := by decide
theorem ttFiber18Parent_1_ok : ttFiber18ParentCheck 1 = true := by decide
theorem ttFiber18Parent_2_ok : ttFiber18ParentCheck 2 = true := by decide
theorem ttFiber18Parent_3_ok : ttFiber18ParentCheck 3 = true := by decide
theorem ttFiber18Parent_4_ok : ttFiber18ParentCheck 4 = true := by decide
theorem ttFiber18Parent_5_ok : ttFiber18ParentCheck 5 = true := by decide
theorem ttFiber18Parent_6_ok : ttFiber18ParentCheck 6 = true := by decide
theorem ttFiber18Parent_7_ok : ttFiber18ParentCheck 7 = true := by decide

def ttFiber18CertificateAudit : Bool :=
  ttFiber18SourcesCheck &&
    ttFiber18RowCheck 0 &&
    ttFiber18RowCheck 1 &&
    ttFiber18RowCheck 2 &&
    ttFiber18RowCheck 3 &&
    ttFiber18RowCheck 4 &&
    ttFiber18RowCheck 5 &&
    ttFiber18RowCheck 6 &&
    ttFiber18RowCheck 7 &&
    ttFiber18ParentCheck 0 &&
    ttFiber18ParentCheck 1 &&
    ttFiber18ParentCheck 2 &&
    ttFiber18ParentCheck 3 &&
    ttFiber18ParentCheck 4 &&
    ttFiber18ParentCheck 5 &&
    ttFiber18ParentCheck 6 &&
    ttFiber18ParentCheck 7

theorem ttFiber18CertificateAudit_ok :
    ttFiber18CertificateAudit = true := by
  simp [ttFiber18CertificateAudit,
    ttFiber18SourcesCheck_ok,
    ttFiber18Row_0_ok,
    ttFiber18Row_1_ok,
    ttFiber18Row_2_ok,
    ttFiber18Row_3_ok,
    ttFiber18Row_4_ok,
    ttFiber18Row_5_ok,
    ttFiber18Row_6_ok,
    ttFiber18Row_7_ok,
    ttFiber18Parent_0_ok,
    ttFiber18Parent_1_ok,
    ttFiber18Parent_2_ok,
    ttFiber18Parent_3_ok,
    ttFiber18Parent_4_ok,
    ttFiber18Parent_5_ok,
    ttFiber18Parent_6_ok,
    ttFiber18Parent_7_ok]

def ttFiber19Key : List LColor :=
  [LColor.r, LColor.p, LColor.r, LColor.b]

def ttFiber19Expected : List Nat :=
  [680, 681, 682, 683, 684, 685, 686, 687]

def ttFiber19Rows : List DirectChainParentRow :=
  [ directRow 680 680 136 84 136 84 default
  , directRow 681 680 136 85 136 84 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 682 680 136 86 136 84 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 683 681 136 87 136 85 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 684 680 137 92 136 84 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 685 681 137 93 136 85 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 686 682 137 94 136 86 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 687 683 137 95 136 87 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  ]

def ttFiber19RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber19Rows i default

def ttFiber19SourcesCheck : Bool :=
  (ttFiber19Rows.map fun row => row.source) == ttFiber19Expected

theorem ttFiber19SourcesCheck_ok :
    ttFiber19SourcesCheck = true := by
  decide

def ttFiber19RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber19Key ttFiber19Expected (ttFiber19RowAt i)

theorem ttFiber19Row_0_ok : ttFiber19RowCheck 0 = true := by decide
theorem ttFiber19Row_1_ok : ttFiber19RowCheck 1 = true := by decide
theorem ttFiber19Row_2_ok : ttFiber19RowCheck 2 = true := by decide
theorem ttFiber19Row_3_ok : ttFiber19RowCheck 3 = true := by decide
theorem ttFiber19Row_4_ok : ttFiber19RowCheck 4 = true := by decide
theorem ttFiber19Row_5_ok : ttFiber19RowCheck 5 = true := by decide
theorem ttFiber19Row_6_ok : ttFiber19RowCheck 6 = true := by decide
theorem ttFiber19Row_7_ok : ttFiber19RowCheck 7 = true := by decide

def ttFiber19ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber19Rows ttMaxParentDepth (listGetD ttFiber19Expected i 0) == 680

theorem ttFiber19Parent_0_ok : ttFiber19ParentCheck 0 = true := by decide
theorem ttFiber19Parent_1_ok : ttFiber19ParentCheck 1 = true := by decide
theorem ttFiber19Parent_2_ok : ttFiber19ParentCheck 2 = true := by decide
theorem ttFiber19Parent_3_ok : ttFiber19ParentCheck 3 = true := by decide
theorem ttFiber19Parent_4_ok : ttFiber19ParentCheck 4 = true := by decide
theorem ttFiber19Parent_5_ok : ttFiber19ParentCheck 5 = true := by decide
theorem ttFiber19Parent_6_ok : ttFiber19ParentCheck 6 = true := by decide
theorem ttFiber19Parent_7_ok : ttFiber19ParentCheck 7 = true := by decide

def ttFiber19CertificateAudit : Bool :=
  ttFiber19SourcesCheck &&
    ttFiber19RowCheck 0 &&
    ttFiber19RowCheck 1 &&
    ttFiber19RowCheck 2 &&
    ttFiber19RowCheck 3 &&
    ttFiber19RowCheck 4 &&
    ttFiber19RowCheck 5 &&
    ttFiber19RowCheck 6 &&
    ttFiber19RowCheck 7 &&
    ttFiber19ParentCheck 0 &&
    ttFiber19ParentCheck 1 &&
    ttFiber19ParentCheck 2 &&
    ttFiber19ParentCheck 3 &&
    ttFiber19ParentCheck 4 &&
    ttFiber19ParentCheck 5 &&
    ttFiber19ParentCheck 6 &&
    ttFiber19ParentCheck 7

theorem ttFiber19CertificateAudit_ok :
    ttFiber19CertificateAudit = true := by
  simp [ttFiber19CertificateAudit,
    ttFiber19SourcesCheck_ok,
    ttFiber19Row_0_ok,
    ttFiber19Row_1_ok,
    ttFiber19Row_2_ok,
    ttFiber19Row_3_ok,
    ttFiber19Row_4_ok,
    ttFiber19Row_5_ok,
    ttFiber19Row_6_ok,
    ttFiber19Row_7_ok,
    ttFiber19Parent_0_ok,
    ttFiber19Parent_1_ok,
    ttFiber19Parent_2_ok,
    ttFiber19Parent_3_ok,
    ttFiber19Parent_4_ok,
    ttFiber19Parent_5_ok,
    ttFiber19Parent_6_ok,
    ttFiber19Parent_7_ok]

def ttFiber20Key : List LColor :=
  [LColor.r, LColor.p, LColor.r, LColor.p]

def ttFiber20Expected : List Nat :=
  [688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959]

def ttFiber20Rows : List DirectChainParentRow :=
  [ directRow 688 688 140 148 140 148 default
  , directRow 689 688 140 149 140 148 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 690 689 140 150 140 149 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 691 688 140 151 140 148 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 692 688 140 164 140 148 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 693 689 140 165 140 149 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 694 692 140 166 140 164 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 695 691 140 167 140 151 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 696 688 141 156 140 148 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 697 689 141 157 140 149 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 698 690 141 158 140 150 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 699 691 141 159 140 151 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 700 692 141 172 140 164 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 701 693 141 173 140 165 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 702 694 141 174 140 166 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 703 695 141 175 140 167 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 704 708 142 0 142 48 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 705 709 142 1 142 49 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 706 700 142 2 141 172 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 707 701 142 3 141 173 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 708 696 142 48 141 156 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 709 697 142 49 141 157 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 710 698 142 50 141 158 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 711 699 142 51 141 159 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 712 716 143 8 143 56 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 713 717 143 9 143 57 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 714 692 143 10 140 164 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 715 693 143 11 140 165 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 716 688 143 56 140 148 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 717 689 143 57 140 149 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 718 690 143 58 140 150 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 719 691 143 59 140 151 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 928 688 188 132 140 148 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 929 689 188 133 140 149 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 930 690 188 134 140 150 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 931 691 188 135 140 151 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 932 692 188 180 140 164 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 933 693 188 181 140 165 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 934 694 188 182 140 166 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 935 695 188 183 140 167 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 936 696 189 140 141 156 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 937 697 189 141 141 157 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 938 698 189 142 141 158 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 939 699 189 143 141 159 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 940 700 189 188 141 172 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 941 701 189 189 141 173 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 942 702 189 190 141 174 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 943 703 189 191 141 175 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 944 928 190 64 188 132 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 945 929 190 65 188 133 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 946 944 190 66 190 64 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 947 931 190 67 188 135 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 948 932 190 116 188 180 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 949 933 190 117 188 181 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 950 945 190 118 190 65 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 951 944 190 119 190 64 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 952 936 191 72 189 140 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 953 937 191 73 189 141 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 954 714 191 74 143 10 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 955 715 191 75 143 11 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 956 716 191 124 143 56 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 957 717 191 125 143 57 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 958 956 191 126 191 124 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 959 719 191 127 143 59 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  ]

def ttFiber20RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber20Rows i default

def ttFiber20SourcesCheck : Bool :=
  (ttFiber20Rows.map fun row => row.source) == ttFiber20Expected

theorem ttFiber20SourcesCheck_ok :
    ttFiber20SourcesCheck = true := by
  decide

def ttFiber20RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt i)

theorem ttFiber20Row_0_ok : ttFiber20RowCheck 0 = true := by decide
theorem ttFiber20Row_1_ok : ttFiber20RowCheck 1 = true := by decide
theorem ttFiber20Row_2_ok : ttFiber20RowCheck 2 = true := by decide
theorem ttFiber20Row_3_ok : ttFiber20RowCheck 3 = true := by decide
theorem ttFiber20Row_4_ok : ttFiber20RowCheck 4 = true := by decide
theorem ttFiber20Row_5_ok : ttFiber20RowCheck 5 = true := by decide
theorem ttFiber20Row_6_ok : ttFiber20RowCheck 6 = true := by decide
theorem ttFiber20Row_7_ok : ttFiber20RowCheck 7 = true := by decide
theorem ttFiber20Row_8_ok : ttFiber20RowCheck 8 = true := by decide
theorem ttFiber20Row_9_ok : ttFiber20RowCheck 9 = true := by decide
theorem ttFiber20Row_10_ok : ttFiber20RowCheck 10 = true := by decide
theorem ttFiber20Row_11_ok : ttFiber20RowCheck 11 = true := by decide
theorem ttFiber20Row_12_ok : ttFiber20RowCheck 12 = true := by decide
theorem ttFiber20Row_13_ok : ttFiber20RowCheck 13 = true := by decide
theorem ttFiber20Row_14_ok : ttFiber20RowCheck 14 = true := by decide
theorem ttFiber20Row_15_ok : ttFiber20RowCheck 15 = true := by decide
theorem ttFiber20Row_16_ok : ttFiber20RowCheck 16 = true := by decide
theorem ttFiber20Row_17_ok : ttFiber20RowCheck 17 = true := by decide
theorem ttFiber20Row_18_ok : ttFiber20RowCheck 18 = true := by decide
theorem ttFiber20Row_19_ok : ttFiber20RowCheck 19 = true := by decide
theorem ttFiber20Row_20_ok : ttFiber20RowCheck 20 = true := by decide
theorem ttFiber20Row_21_ok : ttFiber20RowCheck 21 = true := by decide
theorem ttFiber20Row_22_ok : ttFiber20RowCheck 22 = true := by decide
theorem ttFiber20Row_23_ok : ttFiber20RowCheck 23 = true := by decide
theorem ttFiber20Row_24_ok : ttFiber20RowCheck 24 = true := by decide
theorem ttFiber20Row_25_ok : ttFiber20RowCheck 25 = true := by decide
theorem ttFiber20Row_26_ok : ttFiber20RowCheck 26 = true := by decide
theorem ttFiber20Row_27_ok : ttFiber20RowCheck 27 = true := by decide
theorem ttFiber20Row_28_ok : ttFiber20RowCheck 28 = true := by decide
theorem ttFiber20Row_29_ok : ttFiber20RowCheck 29 = true := by decide
theorem ttFiber20Row_30_ok : ttFiber20RowCheck 30 = true := by decide
theorem ttFiber20Row_31_ok : ttFiber20RowCheck 31 = true := by decide
theorem ttFiber20Row_32_ok : ttFiber20RowCheck 32 = true := by decide
theorem ttFiber20Row_33_ok : ttFiber20RowCheck 33 = true := by decide
theorem ttFiber20Row_34_ok : ttFiber20RowCheck 34 = true := by decide
theorem ttFiber20Row_35_ok : ttFiber20RowCheck 35 = true := by decide
theorem ttFiber20Row_36_ok : ttFiber20RowCheck 36 = true := by decide
theorem ttFiber20Row_37_ok : ttFiber20RowCheck 37 = true := by decide
theorem ttFiber20Row_38_ok : ttFiber20RowCheck 38 = true := by decide
theorem ttFiber20Row_39_ok : ttFiber20RowCheck 39 = true := by decide
theorem ttFiber20Row_40_ok : ttFiber20RowCheck 40 = true := by decide
theorem ttFiber20Row_41_ok : ttFiber20RowCheck 41 = true := by decide
theorem ttFiber20Row_42_ok : ttFiber20RowCheck 42 = true := by decide
theorem ttFiber20Row_43_ok : ttFiber20RowCheck 43 = true := by decide
theorem ttFiber20Row_44_ok : ttFiber20RowCheck 44 = true := by decide
theorem ttFiber20Row_45_ok : ttFiber20RowCheck 45 = true := by decide
theorem ttFiber20Row_46_ok : ttFiber20RowCheck 46 = true := by decide
theorem ttFiber20Row_47_ok : ttFiber20RowCheck 47 = true := by decide
theorem ttFiber20Row_48_ok : ttFiber20RowCheck 48 = true := by decide
theorem ttFiber20Row_49_ok : ttFiber20RowCheck 49 = true := by decide
theorem ttFiber20Row_50_ok : ttFiber20RowCheck 50 = true := by decide
theorem ttFiber20Row_51_ok : ttFiber20RowCheck 51 = true := by decide
theorem ttFiber20Row_52_ok : ttFiber20RowCheck 52 = true := by decide
theorem ttFiber20Row_53_ok : ttFiber20RowCheck 53 = true := by decide
theorem ttFiber20Row_54_ok : ttFiber20RowCheck 54 = true := by decide
theorem ttFiber20Row_55_ok : ttFiber20RowCheck 55 = true := by decide
theorem ttFiber20Row_56_ok : ttFiber20RowCheck 56 = true := by decide
theorem ttFiber20Row_57_ok : ttFiber20RowCheck 57 = true := by decide
theorem ttFiber20Row_58_ok : ttFiber20RowCheck 58 = true := by decide
theorem ttFiber20Row_59_ok : ttFiber20RowCheck 59 = true := by decide
theorem ttFiber20Row_60_ok : ttFiber20RowCheck 60 = true := by decide
theorem ttFiber20Row_61_ok : ttFiber20RowCheck 61 = true := by decide
theorem ttFiber20Row_62_ok : ttFiber20RowCheck 62 = true := by decide
theorem ttFiber20Row_63_ok : ttFiber20RowCheck 63 = true := by decide

def ttFiber20ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber20Rows ttMaxParentDepth (listGetD ttFiber20Expected i 0) == 688

theorem ttFiber20Parent_0_ok : ttFiber20ParentCheck 0 = true := by decide
theorem ttFiber20Parent_1_ok : ttFiber20ParentCheck 1 = true := by decide
theorem ttFiber20Parent_2_ok : ttFiber20ParentCheck 2 = true := by decide
theorem ttFiber20Parent_3_ok : ttFiber20ParentCheck 3 = true := by decide
theorem ttFiber20Parent_4_ok : ttFiber20ParentCheck 4 = true := by decide
theorem ttFiber20Parent_5_ok : ttFiber20ParentCheck 5 = true := by decide
theorem ttFiber20Parent_6_ok : ttFiber20ParentCheck 6 = true := by decide
theorem ttFiber20Parent_7_ok : ttFiber20ParentCheck 7 = true := by decide
theorem ttFiber20Parent_8_ok : ttFiber20ParentCheck 8 = true := by decide
theorem ttFiber20Parent_9_ok : ttFiber20ParentCheck 9 = true := by decide
theorem ttFiber20Parent_10_ok : ttFiber20ParentCheck 10 = true := by decide
theorem ttFiber20Parent_11_ok : ttFiber20ParentCheck 11 = true := by decide
theorem ttFiber20Parent_12_ok : ttFiber20ParentCheck 12 = true := by decide
theorem ttFiber20Parent_13_ok : ttFiber20ParentCheck 13 = true := by decide
theorem ttFiber20Parent_14_ok : ttFiber20ParentCheck 14 = true := by decide
theorem ttFiber20Parent_15_ok : ttFiber20ParentCheck 15 = true := by decide
theorem ttFiber20Parent_16_ok : ttFiber20ParentCheck 16 = true := by decide
theorem ttFiber20Parent_17_ok : ttFiber20ParentCheck 17 = true := by decide
theorem ttFiber20Parent_18_ok : ttFiber20ParentCheck 18 = true := by decide
theorem ttFiber20Parent_19_ok : ttFiber20ParentCheck 19 = true := by decide
theorem ttFiber20Parent_20_ok : ttFiber20ParentCheck 20 = true := by decide
theorem ttFiber20Parent_21_ok : ttFiber20ParentCheck 21 = true := by decide
theorem ttFiber20Parent_22_ok : ttFiber20ParentCheck 22 = true := by decide
theorem ttFiber20Parent_23_ok : ttFiber20ParentCheck 23 = true := by decide
theorem ttFiber20Parent_24_ok : ttFiber20ParentCheck 24 = true := by decide
theorem ttFiber20Parent_25_ok : ttFiber20ParentCheck 25 = true := by decide
theorem ttFiber20Parent_26_ok : ttFiber20ParentCheck 26 = true := by decide
theorem ttFiber20Parent_27_ok : ttFiber20ParentCheck 27 = true := by decide
theorem ttFiber20Parent_28_ok : ttFiber20ParentCheck 28 = true := by decide
theorem ttFiber20Parent_29_ok : ttFiber20ParentCheck 29 = true := by decide
theorem ttFiber20Parent_30_ok : ttFiber20ParentCheck 30 = true := by decide
theorem ttFiber20Parent_31_ok : ttFiber20ParentCheck 31 = true := by decide
theorem ttFiber20Parent_32_ok : ttFiber20ParentCheck 32 = true := by decide
theorem ttFiber20Parent_33_ok : ttFiber20ParentCheck 33 = true := by decide
theorem ttFiber20Parent_34_ok : ttFiber20ParentCheck 34 = true := by decide
theorem ttFiber20Parent_35_ok : ttFiber20ParentCheck 35 = true := by decide
theorem ttFiber20Parent_36_ok : ttFiber20ParentCheck 36 = true := by decide
theorem ttFiber20Parent_37_ok : ttFiber20ParentCheck 37 = true := by decide
theorem ttFiber20Parent_38_ok : ttFiber20ParentCheck 38 = true := by decide
theorem ttFiber20Parent_39_ok : ttFiber20ParentCheck 39 = true := by decide
theorem ttFiber20Parent_40_ok : ttFiber20ParentCheck 40 = true := by decide
theorem ttFiber20Parent_41_ok : ttFiber20ParentCheck 41 = true := by decide
theorem ttFiber20Parent_42_ok : ttFiber20ParentCheck 42 = true := by decide
theorem ttFiber20Parent_43_ok : ttFiber20ParentCheck 43 = true := by decide
theorem ttFiber20Parent_44_ok : ttFiber20ParentCheck 44 = true := by decide
theorem ttFiber20Parent_45_ok : ttFiber20ParentCheck 45 = true := by decide
theorem ttFiber20Parent_46_ok : ttFiber20ParentCheck 46 = true := by decide
theorem ttFiber20Parent_47_ok : ttFiber20ParentCheck 47 = true := by decide
theorem ttFiber20Parent_48_ok : ttFiber20ParentCheck 48 = true := by decide
theorem ttFiber20Parent_49_ok : ttFiber20ParentCheck 49 = true := by decide
theorem ttFiber20Parent_50_ok : ttFiber20ParentCheck 50 = true := by decide
theorem ttFiber20Parent_51_ok : ttFiber20ParentCheck 51 = true := by decide
theorem ttFiber20Parent_52_ok : ttFiber20ParentCheck 52 = true := by decide
theorem ttFiber20Parent_53_ok : ttFiber20ParentCheck 53 = true := by decide
theorem ttFiber20Parent_54_ok : ttFiber20ParentCheck 54 = true := by decide
theorem ttFiber20Parent_55_ok : ttFiber20ParentCheck 55 = true := by decide
theorem ttFiber20Parent_56_ok : ttFiber20ParentCheck 56 = true := by decide
theorem ttFiber20Parent_57_ok : ttFiber20ParentCheck 57 = true := by decide
theorem ttFiber20Parent_58_ok : ttFiber20ParentCheck 58 = true := by decide
theorem ttFiber20Parent_59_ok : ttFiber20ParentCheck 59 = true := by decide
theorem ttFiber20Parent_60_ok : ttFiber20ParentCheck 60 = true := by decide
theorem ttFiber20Parent_61_ok : ttFiber20ParentCheck 61 = true := by decide
theorem ttFiber20Parent_62_ok : ttFiber20ParentCheck 62 = true := by decide
theorem ttFiber20Parent_63_ok : ttFiber20ParentCheck 63 = true := by decide

def ttFiber20CertificateAudit : Bool :=
  ttFiber20SourcesCheck &&
    ttFiber20RowCheck 0 &&
    ttFiber20RowCheck 1 &&
    ttFiber20RowCheck 2 &&
    ttFiber20RowCheck 3 &&
    ttFiber20RowCheck 4 &&
    ttFiber20RowCheck 5 &&
    ttFiber20RowCheck 6 &&
    ttFiber20RowCheck 7 &&
    ttFiber20RowCheck 8 &&
    ttFiber20RowCheck 9 &&
    ttFiber20RowCheck 10 &&
    ttFiber20RowCheck 11 &&
    ttFiber20RowCheck 12 &&
    ttFiber20RowCheck 13 &&
    ttFiber20RowCheck 14 &&
    ttFiber20RowCheck 15 &&
    ttFiber20RowCheck 16 &&
    ttFiber20RowCheck 17 &&
    ttFiber20RowCheck 18 &&
    ttFiber20RowCheck 19 &&
    ttFiber20RowCheck 20 &&
    ttFiber20RowCheck 21 &&
    ttFiber20RowCheck 22 &&
    ttFiber20RowCheck 23 &&
    ttFiber20RowCheck 24 &&
    ttFiber20RowCheck 25 &&
    ttFiber20RowCheck 26 &&
    ttFiber20RowCheck 27 &&
    ttFiber20RowCheck 28 &&
    ttFiber20RowCheck 29 &&
    ttFiber20RowCheck 30 &&
    ttFiber20RowCheck 31 &&
    ttFiber20RowCheck 32 &&
    ttFiber20RowCheck 33 &&
    ttFiber20RowCheck 34 &&
    ttFiber20RowCheck 35 &&
    ttFiber20RowCheck 36 &&
    ttFiber20RowCheck 37 &&
    ttFiber20RowCheck 38 &&
    ttFiber20RowCheck 39 &&
    ttFiber20RowCheck 40 &&
    ttFiber20RowCheck 41 &&
    ttFiber20RowCheck 42 &&
    ttFiber20RowCheck 43 &&
    ttFiber20RowCheck 44 &&
    ttFiber20RowCheck 45 &&
    ttFiber20RowCheck 46 &&
    ttFiber20RowCheck 47 &&
    ttFiber20RowCheck 48 &&
    ttFiber20RowCheck 49 &&
    ttFiber20RowCheck 50 &&
    ttFiber20RowCheck 51 &&
    ttFiber20RowCheck 52 &&
    ttFiber20RowCheck 53 &&
    ttFiber20RowCheck 54 &&
    ttFiber20RowCheck 55 &&
    ttFiber20RowCheck 56 &&
    ttFiber20RowCheck 57 &&
    ttFiber20RowCheck 58 &&
    ttFiber20RowCheck 59 &&
    ttFiber20RowCheck 60 &&
    ttFiber20RowCheck 61 &&
    ttFiber20RowCheck 62 &&
    ttFiber20RowCheck 63 &&
    ttFiber20ParentCheck 0 &&
    ttFiber20ParentCheck 1 &&
    ttFiber20ParentCheck 2 &&
    ttFiber20ParentCheck 3 &&
    ttFiber20ParentCheck 4 &&
    ttFiber20ParentCheck 5 &&
    ttFiber20ParentCheck 6 &&
    ttFiber20ParentCheck 7 &&
    ttFiber20ParentCheck 8 &&
    ttFiber20ParentCheck 9 &&
    ttFiber20ParentCheck 10 &&
    ttFiber20ParentCheck 11 &&
    ttFiber20ParentCheck 12 &&
    ttFiber20ParentCheck 13 &&
    ttFiber20ParentCheck 14 &&
    ttFiber20ParentCheck 15 &&
    ttFiber20ParentCheck 16 &&
    ttFiber20ParentCheck 17 &&
    ttFiber20ParentCheck 18 &&
    ttFiber20ParentCheck 19 &&
    ttFiber20ParentCheck 20 &&
    ttFiber20ParentCheck 21 &&
    ttFiber20ParentCheck 22 &&
    ttFiber20ParentCheck 23 &&
    ttFiber20ParentCheck 24 &&
    ttFiber20ParentCheck 25 &&
    ttFiber20ParentCheck 26 &&
    ttFiber20ParentCheck 27 &&
    ttFiber20ParentCheck 28 &&
    ttFiber20ParentCheck 29 &&
    ttFiber20ParentCheck 30 &&
    ttFiber20ParentCheck 31 &&
    ttFiber20ParentCheck 32 &&
    ttFiber20ParentCheck 33 &&
    ttFiber20ParentCheck 34 &&
    ttFiber20ParentCheck 35 &&
    ttFiber20ParentCheck 36 &&
    ttFiber20ParentCheck 37 &&
    ttFiber20ParentCheck 38 &&
    ttFiber20ParentCheck 39 &&
    ttFiber20ParentCheck 40 &&
    ttFiber20ParentCheck 41 &&
    ttFiber20ParentCheck 42 &&
    ttFiber20ParentCheck 43 &&
    ttFiber20ParentCheck 44 &&
    ttFiber20ParentCheck 45 &&
    ttFiber20ParentCheck 46 &&
    ttFiber20ParentCheck 47 &&
    ttFiber20ParentCheck 48 &&
    ttFiber20ParentCheck 49 &&
    ttFiber20ParentCheck 50 &&
    ttFiber20ParentCheck 51 &&
    ttFiber20ParentCheck 52 &&
    ttFiber20ParentCheck 53 &&
    ttFiber20ParentCheck 54 &&
    ttFiber20ParentCheck 55 &&
    ttFiber20ParentCheck 56 &&
    ttFiber20ParentCheck 57 &&
    ttFiber20ParentCheck 58 &&
    ttFiber20ParentCheck 59 &&
    ttFiber20ParentCheck 60 &&
    ttFiber20ParentCheck 61 &&
    ttFiber20ParentCheck 62 &&
    ttFiber20ParentCheck 63

theorem ttFiber20CertificateAudit_ok :
    ttFiber20CertificateAudit = true := by
  simp [ttFiber20CertificateAudit,
    ttFiber20SourcesCheck_ok,
    ttFiber20Row_0_ok,
    ttFiber20Row_1_ok,
    ttFiber20Row_2_ok,
    ttFiber20Row_3_ok,
    ttFiber20Row_4_ok,
    ttFiber20Row_5_ok,
    ttFiber20Row_6_ok,
    ttFiber20Row_7_ok,
    ttFiber20Row_8_ok,
    ttFiber20Row_9_ok,
    ttFiber20Row_10_ok,
    ttFiber20Row_11_ok,
    ttFiber20Row_12_ok,
    ttFiber20Row_13_ok,
    ttFiber20Row_14_ok,
    ttFiber20Row_15_ok,
    ttFiber20Row_16_ok,
    ttFiber20Row_17_ok,
    ttFiber20Row_18_ok,
    ttFiber20Row_19_ok,
    ttFiber20Row_20_ok,
    ttFiber20Row_21_ok,
    ttFiber20Row_22_ok,
    ttFiber20Row_23_ok,
    ttFiber20Row_24_ok,
    ttFiber20Row_25_ok,
    ttFiber20Row_26_ok,
    ttFiber20Row_27_ok,
    ttFiber20Row_28_ok,
    ttFiber20Row_29_ok,
    ttFiber20Row_30_ok,
    ttFiber20Row_31_ok,
    ttFiber20Row_32_ok,
    ttFiber20Row_33_ok,
    ttFiber20Row_34_ok,
    ttFiber20Row_35_ok,
    ttFiber20Row_36_ok,
    ttFiber20Row_37_ok,
    ttFiber20Row_38_ok,
    ttFiber20Row_39_ok,
    ttFiber20Row_40_ok,
    ttFiber20Row_41_ok,
    ttFiber20Row_42_ok,
    ttFiber20Row_43_ok,
    ttFiber20Row_44_ok,
    ttFiber20Row_45_ok,
    ttFiber20Row_46_ok,
    ttFiber20Row_47_ok,
    ttFiber20Row_48_ok,
    ttFiber20Row_49_ok,
    ttFiber20Row_50_ok,
    ttFiber20Row_51_ok,
    ttFiber20Row_52_ok,
    ttFiber20Row_53_ok,
    ttFiber20Row_54_ok,
    ttFiber20Row_55_ok,
    ttFiber20Row_56_ok,
    ttFiber20Row_57_ok,
    ttFiber20Row_58_ok,
    ttFiber20Row_59_ok,
    ttFiber20Row_60_ok,
    ttFiber20Row_61_ok,
    ttFiber20Row_62_ok,
    ttFiber20Row_63_ok,
    ttFiber20Parent_0_ok,
    ttFiber20Parent_1_ok,
    ttFiber20Parent_2_ok,
    ttFiber20Parent_3_ok,
    ttFiber20Parent_4_ok,
    ttFiber20Parent_5_ok,
    ttFiber20Parent_6_ok,
    ttFiber20Parent_7_ok,
    ttFiber20Parent_8_ok,
    ttFiber20Parent_9_ok,
    ttFiber20Parent_10_ok,
    ttFiber20Parent_11_ok,
    ttFiber20Parent_12_ok,
    ttFiber20Parent_13_ok,
    ttFiber20Parent_14_ok,
    ttFiber20Parent_15_ok,
    ttFiber20Parent_16_ok,
    ttFiber20Parent_17_ok,
    ttFiber20Parent_18_ok,
    ttFiber20Parent_19_ok,
    ttFiber20Parent_20_ok,
    ttFiber20Parent_21_ok,
    ttFiber20Parent_22_ok,
    ttFiber20Parent_23_ok,
    ttFiber20Parent_24_ok,
    ttFiber20Parent_25_ok,
    ttFiber20Parent_26_ok,
    ttFiber20Parent_27_ok,
    ttFiber20Parent_28_ok,
    ttFiber20Parent_29_ok,
    ttFiber20Parent_30_ok,
    ttFiber20Parent_31_ok,
    ttFiber20Parent_32_ok,
    ttFiber20Parent_33_ok,
    ttFiber20Parent_34_ok,
    ttFiber20Parent_35_ok,
    ttFiber20Parent_36_ok,
    ttFiber20Parent_37_ok,
    ttFiber20Parent_38_ok,
    ttFiber20Parent_39_ok,
    ttFiber20Parent_40_ok,
    ttFiber20Parent_41_ok,
    ttFiber20Parent_42_ok,
    ttFiber20Parent_43_ok,
    ttFiber20Parent_44_ok,
    ttFiber20Parent_45_ok,
    ttFiber20Parent_46_ok,
    ttFiber20Parent_47_ok,
    ttFiber20Parent_48_ok,
    ttFiber20Parent_49_ok,
    ttFiber20Parent_50_ok,
    ttFiber20Parent_51_ok,
    ttFiber20Parent_52_ok,
    ttFiber20Parent_53_ok,
    ttFiber20Parent_54_ok,
    ttFiber20Parent_55_ok,
    ttFiber20Parent_56_ok,
    ttFiber20Parent_57_ok,
    ttFiber20Parent_58_ok,
    ttFiber20Parent_59_ok,
    ttFiber20Parent_60_ok,
    ttFiber20Parent_61_ok,
    ttFiber20Parent_62_ok,
    ttFiber20Parent_63_ok]

def ttFiber21Key : List LColor :=
  [LColor.r, LColor.p, LColor.b, LColor.r]

def ttFiber21Expected : List Nat :=
  []

def ttFiber21Rows : List DirectChainParentRow :=
  []

def ttFiber21RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber21Rows i default

def ttFiber21SourcesCheck : Bool :=
  (ttFiber21Rows.map fun row => row.source) == ttFiber21Expected

theorem ttFiber21SourcesCheck_ok :
    ttFiber21SourcesCheck = true := by
  decide

def ttFiber21RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber21Key ttFiber21Expected (ttFiber21RowAt i)

def ttFiber21ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber21Rows ttMaxParentDepth (listGetD ttFiber21Expected i 0) == 0

def ttFiber21CertificateAudit : Bool :=
  ttFiber21SourcesCheck

theorem ttFiber21CertificateAudit_ok :
    ttFiber21CertificateAudit = true := by
  simp [ttFiber21CertificateAudit,
    ttFiber21SourcesCheck_ok]

def ttFiber22Key : List LColor :=
  [LColor.r, LColor.p, LColor.b, LColor.b]

def ttFiber22Expected : List Nat :=
  []

def ttFiber22Rows : List DirectChainParentRow :=
  []

def ttFiber22RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber22Rows i default

def ttFiber22SourcesCheck : Bool :=
  (ttFiber22Rows.map fun row => row.source) == ttFiber22Expected

theorem ttFiber22SourcesCheck_ok :
    ttFiber22SourcesCheck = true := by
  decide

def ttFiber22RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber22Key ttFiber22Expected (ttFiber22RowAt i)

def ttFiber22ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber22Rows ttMaxParentDepth (listGetD ttFiber22Expected i 0) == 0

def ttFiber22CertificateAudit : Bool :=
  ttFiber22SourcesCheck

theorem ttFiber22CertificateAudit_ok :
    ttFiber22CertificateAudit = true := by
  simp [ttFiber22CertificateAudit,
    ttFiber22SourcesCheck_ok]

def ttFiber23Key : List LColor :=
  [LColor.r, LColor.p, LColor.b, LColor.p]

def ttFiber23Expected : List Nat :=
  []

def ttFiber23Rows : List DirectChainParentRow :=
  []

def ttFiber23RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber23Rows i default

def ttFiber23SourcesCheck : Bool :=
  (ttFiber23Rows.map fun row => row.source) == ttFiber23Expected

theorem ttFiber23SourcesCheck_ok :
    ttFiber23SourcesCheck = true := by
  decide

def ttFiber23RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber23Key ttFiber23Expected (ttFiber23RowAt i)

def ttFiber23ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber23Rows ttMaxParentDepth (listGetD ttFiber23Expected i 0) == 0

def ttFiber23CertificateAudit : Bool :=
  ttFiber23SourcesCheck

theorem ttFiber23CertificateAudit_ok :
    ttFiber23CertificateAudit = true := by
  simp [ttFiber23CertificateAudit,
    ttFiber23SourcesCheck_ok]

def ttFiber24Key : List LColor :=
  [LColor.r, LColor.p, LColor.p, LColor.r]

def ttFiber24Expected : List Nat :=
  []

def ttFiber24Rows : List DirectChainParentRow :=
  []

def ttFiber24RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber24Rows i default

def ttFiber24SourcesCheck : Bool :=
  (ttFiber24Rows.map fun row => row.source) == ttFiber24Expected

theorem ttFiber24SourcesCheck_ok :
    ttFiber24SourcesCheck = true := by
  decide

def ttFiber24RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber24Key ttFiber24Expected (ttFiber24RowAt i)

def ttFiber24ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber24Rows ttMaxParentDepth (listGetD ttFiber24Expected i 0) == 0

def ttFiber24CertificateAudit : Bool :=
  ttFiber24SourcesCheck

theorem ttFiber24CertificateAudit_ok :
    ttFiber24CertificateAudit = true := by
  simp [ttFiber24CertificateAudit,
    ttFiber24SourcesCheck_ok]

def ttFiber25Key : List LColor :=
  [LColor.r, LColor.p, LColor.p, LColor.b]

def ttFiber25Expected : List Nat :=
  []

def ttFiber25Rows : List DirectChainParentRow :=
  []

def ttFiber25RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber25Rows i default

def ttFiber25SourcesCheck : Bool :=
  (ttFiber25Rows.map fun row => row.source) == ttFiber25Expected

theorem ttFiber25SourcesCheck_ok :
    ttFiber25SourcesCheck = true := by
  decide

def ttFiber25RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber25Key ttFiber25Expected (ttFiber25RowAt i)

def ttFiber25ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber25Rows ttMaxParentDepth (listGetD ttFiber25Expected i 0) == 0

def ttFiber25CertificateAudit : Bool :=
  ttFiber25SourcesCheck

theorem ttFiber25CertificateAudit_ok :
    ttFiber25CertificateAudit = true := by
  simp [ttFiber25CertificateAudit,
    ttFiber25SourcesCheck_ok]

def ttFiber26Key : List LColor :=
  [LColor.r, LColor.p, LColor.p, LColor.p]

def ttFiber26Expected : List Nat :=
  []

def ttFiber26Rows : List DirectChainParentRow :=
  []

def ttFiber26RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber26Rows i default

def ttFiber26SourcesCheck : Bool :=
  (ttFiber26Rows.map fun row => row.source) == ttFiber26Expected

theorem ttFiber26SourcesCheck_ok :
    ttFiber26SourcesCheck = true := by
  decide

def ttFiber26RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber26Key ttFiber26Expected (ttFiber26RowAt i)

def ttFiber26ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber26Rows ttMaxParentDepth (listGetD ttFiber26Expected i 0) == 0

def ttFiber26CertificateAudit : Bool :=
  ttFiber26SourcesCheck

theorem ttFiber26CertificateAudit_ok :
    ttFiber26CertificateAudit = true := by
  simp [ttFiber26CertificateAudit,
    ttFiber26SourcesCheck_ok]

def ttFiber27Key : List LColor :=
  [LColor.b, LColor.r, LColor.r, LColor.r]

def ttFiber27Expected : List Nat :=
  []

def ttFiber27Rows : List DirectChainParentRow :=
  []

def ttFiber27RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber27Rows i default

def ttFiber27SourcesCheck : Bool :=
  (ttFiber27Rows.map fun row => row.source) == ttFiber27Expected

theorem ttFiber27SourcesCheck_ok :
    ttFiber27SourcesCheck = true := by
  decide

def ttFiber27RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber27Key ttFiber27Expected (ttFiber27RowAt i)

def ttFiber27ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber27Rows ttMaxParentDepth (listGetD ttFiber27Expected i 0) == 0

def ttFiber27CertificateAudit : Bool :=
  ttFiber27SourcesCheck

theorem ttFiber27CertificateAudit_ok :
    ttFiber27CertificateAudit = true := by
  simp [ttFiber27CertificateAudit,
    ttFiber27SourcesCheck_ok]

def ttFiber28Key : List LColor :=
  [LColor.b, LColor.r, LColor.r, LColor.b]

def ttFiber28Expected : List Nat :=
  []

def ttFiber28Rows : List DirectChainParentRow :=
  []

def ttFiber28RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber28Rows i default

def ttFiber28SourcesCheck : Bool :=
  (ttFiber28Rows.map fun row => row.source) == ttFiber28Expected

theorem ttFiber28SourcesCheck_ok :
    ttFiber28SourcesCheck = true := by
  decide

def ttFiber28RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber28Key ttFiber28Expected (ttFiber28RowAt i)

def ttFiber28ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber28Rows ttMaxParentDepth (listGetD ttFiber28Expected i 0) == 0

def ttFiber28CertificateAudit : Bool :=
  ttFiber28SourcesCheck

theorem ttFiber28CertificateAudit_ok :
    ttFiber28CertificateAudit = true := by
  simp [ttFiber28CertificateAudit,
    ttFiber28SourcesCheck_ok]

def ttFiber29Key : List LColor :=
  [LColor.b, LColor.r, LColor.r, LColor.p]

def ttFiber29Expected : List Nat :=
  []

def ttFiber29Rows : List DirectChainParentRow :=
  []

def ttFiber29RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber29Rows i default

def ttFiber29SourcesCheck : Bool :=
  (ttFiber29Rows.map fun row => row.source) == ttFiber29Expected

theorem ttFiber29SourcesCheck_ok :
    ttFiber29SourcesCheck = true := by
  decide

def ttFiber29RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber29Key ttFiber29Expected (ttFiber29RowAt i)

def ttFiber29ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber29Rows ttMaxParentDepth (listGetD ttFiber29Expected i 0) == 0

def ttFiber29CertificateAudit : Bool :=
  ttFiber29SourcesCheck

theorem ttFiber29CertificateAudit_ok :
    ttFiber29CertificateAudit = true := by
  simp [ttFiber29CertificateAudit,
    ttFiber29SourcesCheck_ok]

def ttFiber30Key : List LColor :=
  [LColor.b, LColor.r, LColor.b, LColor.r]

def ttFiber30Expected : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]

def ttFiber30Rows : List DirectChainParentRow :=
  [ directRow 0 0 0 80 0 80 default
  , directRow 1 0 0 81 0 80 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 2 0 0 82 0 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 3 1 0 83 0 81 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 4 2 0 100 0 82 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 5 7 0 101 0 103 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 6 1 0 102 0 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 7 0 0 103 0 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 8 0 1 88 0 80 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 9 1 1 89 0 81 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 10 2 1 90 0 82 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 11 3 1 91 0 83 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 12 4 1 108 0 100 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 13 5 1 109 0 101 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 14 6 1 110 0 102 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 15 7 1 111 0 103 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 16 0 2 16 0 80 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 17 1 2 17 0 81 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 18 2 2 18 0 82 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 19 3 2 19 0 83 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 20 16 2 32 2 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 21 17 2 33 2 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 22 6 2 34 0 102 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 23 7 2 35 0 103 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 24 8 3 24 1 88 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 25 9 3 25 1 89 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 26 10 3 26 1 90 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 27 11 3 27 1 91 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 28 24 3 40 3 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 29 25 3 41 3 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 30 14 3 42 1 110 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 31 15 3 43 1 111 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 240 0 48 148 0 80 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 241 1 48 149 0 81 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 242 2 48 150 0 82 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 243 240 48 151 48 148 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 244 240 48 164 48 148 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 245 241 48 165 48 149 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 246 6 48 166 0 102 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 247 7 48 167 0 103 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 248 8 49 156 1 88 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 249 9 49 157 1 89 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 250 10 49 158 1 90 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 251 248 49 159 49 156 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 252 248 49 172 49 156 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 253 249 49 173 49 157 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 254 14 49 174 1 110 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 255 15 49 175 1 111 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 256 16 50 0 2 16 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 257 17 50 1 2 17 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 258 18 50 2 2 18 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 259 19 50 3 2 19 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 260 248 50 48 49 156 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 261 249 50 49 49 157 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 262 22 50 50 2 34 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 263 23 50 51 2 35 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 264 247 51 8 48 167 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 265 246 51 9 48 166 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 266 244 51 10 48 164 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 267 245 51 11 48 165 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 268 240 51 56 48 148 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 269 241 51 57 48 149 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 270 242 51 58 48 150 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 271 243 51 59 48 151 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def ttFiber30RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber30Rows i default

def ttFiber30SourcesCheck : Bool :=
  (ttFiber30Rows.map fun row => row.source) == ttFiber30Expected

theorem ttFiber30SourcesCheck_ok :
    ttFiber30SourcesCheck = true := by
  decide

def ttFiber30RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt i)

theorem ttFiber30Row_0_ok : ttFiber30RowCheck 0 = true := by decide
theorem ttFiber30Row_1_ok : ttFiber30RowCheck 1 = true := by decide
theorem ttFiber30Row_2_ok : ttFiber30RowCheck 2 = true := by decide
theorem ttFiber30Row_3_ok : ttFiber30RowCheck 3 = true := by decide
theorem ttFiber30Row_4_ok : ttFiber30RowCheck 4 = true := by decide
theorem ttFiber30Row_5_ok : ttFiber30RowCheck 5 = true := by decide
theorem ttFiber30Row_6_ok : ttFiber30RowCheck 6 = true := by decide
theorem ttFiber30Row_7_ok : ttFiber30RowCheck 7 = true := by decide
theorem ttFiber30Row_8_ok : ttFiber30RowCheck 8 = true := by decide
theorem ttFiber30Row_9_ok : ttFiber30RowCheck 9 = true := by decide
theorem ttFiber30Row_10_ok : ttFiber30RowCheck 10 = true := by decide
theorem ttFiber30Row_11_ok : ttFiber30RowCheck 11 = true := by decide
theorem ttFiber30Row_12_ok : ttFiber30RowCheck 12 = true := by decide
theorem ttFiber30Row_13_ok : ttFiber30RowCheck 13 = true := by decide
theorem ttFiber30Row_14_ok : ttFiber30RowCheck 14 = true := by decide
theorem ttFiber30Row_15_ok : ttFiber30RowCheck 15 = true := by decide
theorem ttFiber30Row_16_ok : ttFiber30RowCheck 16 = true := by decide
theorem ttFiber30Row_17_ok : ttFiber30RowCheck 17 = true := by decide
theorem ttFiber30Row_18_ok : ttFiber30RowCheck 18 = true := by decide
theorem ttFiber30Row_19_ok : ttFiber30RowCheck 19 = true := by decide
theorem ttFiber30Row_20_ok : ttFiber30RowCheck 20 = true := by decide
theorem ttFiber30Row_21_ok : ttFiber30RowCheck 21 = true := by decide
theorem ttFiber30Row_22_ok : ttFiber30RowCheck 22 = true := by decide
theorem ttFiber30Row_23_ok : ttFiber30RowCheck 23 = true := by decide
theorem ttFiber30Row_24_ok : ttFiber30RowCheck 24 = true := by decide
theorem ttFiber30Row_25_ok : ttFiber30RowCheck 25 = true := by decide
theorem ttFiber30Row_26_ok : ttFiber30RowCheck 26 = true := by decide
theorem ttFiber30Row_27_ok : ttFiber30RowCheck 27 = true := by decide
theorem ttFiber30Row_28_ok : ttFiber30RowCheck 28 = true := by decide
theorem ttFiber30Row_29_ok : ttFiber30RowCheck 29 = true := by decide
theorem ttFiber30Row_30_ok : ttFiber30RowCheck 30 = true := by decide
theorem ttFiber30Row_31_ok : ttFiber30RowCheck 31 = true := by decide
theorem ttFiber30Row_32_ok : ttFiber30RowCheck 32 = true := by decide
theorem ttFiber30Row_33_ok : ttFiber30RowCheck 33 = true := by decide
theorem ttFiber30Row_34_ok : ttFiber30RowCheck 34 = true := by decide
theorem ttFiber30Row_35_ok : ttFiber30RowCheck 35 = true := by decide
theorem ttFiber30Row_36_ok : ttFiber30RowCheck 36 = true := by decide
theorem ttFiber30Row_37_ok : ttFiber30RowCheck 37 = true := by decide
theorem ttFiber30Row_38_ok : ttFiber30RowCheck 38 = true := by decide
theorem ttFiber30Row_39_ok : ttFiber30RowCheck 39 = true := by decide
theorem ttFiber30Row_40_ok : ttFiber30RowCheck 40 = true := by decide
theorem ttFiber30Row_41_ok : ttFiber30RowCheck 41 = true := by decide
theorem ttFiber30Row_42_ok : ttFiber30RowCheck 42 = true := by decide
theorem ttFiber30Row_43_ok : ttFiber30RowCheck 43 = true := by decide
theorem ttFiber30Row_44_ok : ttFiber30RowCheck 44 = true := by decide
theorem ttFiber30Row_45_ok : ttFiber30RowCheck 45 = true := by decide
theorem ttFiber30Row_46_ok : ttFiber30RowCheck 46 = true := by decide
theorem ttFiber30Row_47_ok : ttFiber30RowCheck 47 = true := by decide
theorem ttFiber30Row_48_ok : ttFiber30RowCheck 48 = true := by decide
theorem ttFiber30Row_49_ok : ttFiber30RowCheck 49 = true := by decide
theorem ttFiber30Row_50_ok : ttFiber30RowCheck 50 = true := by decide
theorem ttFiber30Row_51_ok : ttFiber30RowCheck 51 = true := by decide
theorem ttFiber30Row_52_ok : ttFiber30RowCheck 52 = true := by decide
theorem ttFiber30Row_53_ok : ttFiber30RowCheck 53 = true := by decide
theorem ttFiber30Row_54_ok : ttFiber30RowCheck 54 = true := by decide
theorem ttFiber30Row_55_ok : ttFiber30RowCheck 55 = true := by decide
theorem ttFiber30Row_56_ok : ttFiber30RowCheck 56 = true := by decide
theorem ttFiber30Row_57_ok : ttFiber30RowCheck 57 = true := by decide
theorem ttFiber30Row_58_ok : ttFiber30RowCheck 58 = true := by decide
theorem ttFiber30Row_59_ok : ttFiber30RowCheck 59 = true := by decide
theorem ttFiber30Row_60_ok : ttFiber30RowCheck 60 = true := by decide
theorem ttFiber30Row_61_ok : ttFiber30RowCheck 61 = true := by decide
theorem ttFiber30Row_62_ok : ttFiber30RowCheck 62 = true := by decide
theorem ttFiber30Row_63_ok : ttFiber30RowCheck 63 = true := by decide

def ttFiber30ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber30Rows ttMaxParentDepth (listGetD ttFiber30Expected i 0) == 0

theorem ttFiber30Parent_0_ok : ttFiber30ParentCheck 0 = true := by decide
theorem ttFiber30Parent_1_ok : ttFiber30ParentCheck 1 = true := by decide
theorem ttFiber30Parent_2_ok : ttFiber30ParentCheck 2 = true := by decide
theorem ttFiber30Parent_3_ok : ttFiber30ParentCheck 3 = true := by decide
theorem ttFiber30Parent_4_ok : ttFiber30ParentCheck 4 = true := by decide
theorem ttFiber30Parent_5_ok : ttFiber30ParentCheck 5 = true := by decide
theorem ttFiber30Parent_6_ok : ttFiber30ParentCheck 6 = true := by decide
theorem ttFiber30Parent_7_ok : ttFiber30ParentCheck 7 = true := by decide
theorem ttFiber30Parent_8_ok : ttFiber30ParentCheck 8 = true := by decide
theorem ttFiber30Parent_9_ok : ttFiber30ParentCheck 9 = true := by decide
theorem ttFiber30Parent_10_ok : ttFiber30ParentCheck 10 = true := by decide
theorem ttFiber30Parent_11_ok : ttFiber30ParentCheck 11 = true := by decide
theorem ttFiber30Parent_12_ok : ttFiber30ParentCheck 12 = true := by decide
theorem ttFiber30Parent_13_ok : ttFiber30ParentCheck 13 = true := by decide
theorem ttFiber30Parent_14_ok : ttFiber30ParentCheck 14 = true := by decide
theorem ttFiber30Parent_15_ok : ttFiber30ParentCheck 15 = true := by decide
theorem ttFiber30Parent_16_ok : ttFiber30ParentCheck 16 = true := by decide
theorem ttFiber30Parent_17_ok : ttFiber30ParentCheck 17 = true := by decide
theorem ttFiber30Parent_18_ok : ttFiber30ParentCheck 18 = true := by decide
theorem ttFiber30Parent_19_ok : ttFiber30ParentCheck 19 = true := by decide
theorem ttFiber30Parent_20_ok : ttFiber30ParentCheck 20 = true := by decide
theorem ttFiber30Parent_21_ok : ttFiber30ParentCheck 21 = true := by decide
theorem ttFiber30Parent_22_ok : ttFiber30ParentCheck 22 = true := by decide
theorem ttFiber30Parent_23_ok : ttFiber30ParentCheck 23 = true := by decide
theorem ttFiber30Parent_24_ok : ttFiber30ParentCheck 24 = true := by decide
theorem ttFiber30Parent_25_ok : ttFiber30ParentCheck 25 = true := by decide
theorem ttFiber30Parent_26_ok : ttFiber30ParentCheck 26 = true := by decide
theorem ttFiber30Parent_27_ok : ttFiber30ParentCheck 27 = true := by decide
theorem ttFiber30Parent_28_ok : ttFiber30ParentCheck 28 = true := by decide
theorem ttFiber30Parent_29_ok : ttFiber30ParentCheck 29 = true := by decide
theorem ttFiber30Parent_30_ok : ttFiber30ParentCheck 30 = true := by decide
theorem ttFiber30Parent_31_ok : ttFiber30ParentCheck 31 = true := by decide
theorem ttFiber30Parent_32_ok : ttFiber30ParentCheck 32 = true := by decide
theorem ttFiber30Parent_33_ok : ttFiber30ParentCheck 33 = true := by decide
theorem ttFiber30Parent_34_ok : ttFiber30ParentCheck 34 = true := by decide
theorem ttFiber30Parent_35_ok : ttFiber30ParentCheck 35 = true := by decide
theorem ttFiber30Parent_36_ok : ttFiber30ParentCheck 36 = true := by decide
theorem ttFiber30Parent_37_ok : ttFiber30ParentCheck 37 = true := by decide
theorem ttFiber30Parent_38_ok : ttFiber30ParentCheck 38 = true := by decide
theorem ttFiber30Parent_39_ok : ttFiber30ParentCheck 39 = true := by decide
theorem ttFiber30Parent_40_ok : ttFiber30ParentCheck 40 = true := by decide
theorem ttFiber30Parent_41_ok : ttFiber30ParentCheck 41 = true := by decide
theorem ttFiber30Parent_42_ok : ttFiber30ParentCheck 42 = true := by decide
theorem ttFiber30Parent_43_ok : ttFiber30ParentCheck 43 = true := by decide
theorem ttFiber30Parent_44_ok : ttFiber30ParentCheck 44 = true := by decide
theorem ttFiber30Parent_45_ok : ttFiber30ParentCheck 45 = true := by decide
theorem ttFiber30Parent_46_ok : ttFiber30ParentCheck 46 = true := by decide
theorem ttFiber30Parent_47_ok : ttFiber30ParentCheck 47 = true := by decide
theorem ttFiber30Parent_48_ok : ttFiber30ParentCheck 48 = true := by decide
theorem ttFiber30Parent_49_ok : ttFiber30ParentCheck 49 = true := by decide
theorem ttFiber30Parent_50_ok : ttFiber30ParentCheck 50 = true := by decide
theorem ttFiber30Parent_51_ok : ttFiber30ParentCheck 51 = true := by decide
theorem ttFiber30Parent_52_ok : ttFiber30ParentCheck 52 = true := by decide
theorem ttFiber30Parent_53_ok : ttFiber30ParentCheck 53 = true := by decide
theorem ttFiber30Parent_54_ok : ttFiber30ParentCheck 54 = true := by decide
theorem ttFiber30Parent_55_ok : ttFiber30ParentCheck 55 = true := by decide
theorem ttFiber30Parent_56_ok : ttFiber30ParentCheck 56 = true := by decide
theorem ttFiber30Parent_57_ok : ttFiber30ParentCheck 57 = true := by decide
theorem ttFiber30Parent_58_ok : ttFiber30ParentCheck 58 = true := by decide
theorem ttFiber30Parent_59_ok : ttFiber30ParentCheck 59 = true := by decide
theorem ttFiber30Parent_60_ok : ttFiber30ParentCheck 60 = true := by decide
theorem ttFiber30Parent_61_ok : ttFiber30ParentCheck 61 = true := by decide
theorem ttFiber30Parent_62_ok : ttFiber30ParentCheck 62 = true := by decide
theorem ttFiber30Parent_63_ok : ttFiber30ParentCheck 63 = true := by decide

def ttFiber30CertificateAudit : Bool :=
  ttFiber30SourcesCheck &&
    ttFiber30RowCheck 0 &&
    ttFiber30RowCheck 1 &&
    ttFiber30RowCheck 2 &&
    ttFiber30RowCheck 3 &&
    ttFiber30RowCheck 4 &&
    ttFiber30RowCheck 5 &&
    ttFiber30RowCheck 6 &&
    ttFiber30RowCheck 7 &&
    ttFiber30RowCheck 8 &&
    ttFiber30RowCheck 9 &&
    ttFiber30RowCheck 10 &&
    ttFiber30RowCheck 11 &&
    ttFiber30RowCheck 12 &&
    ttFiber30RowCheck 13 &&
    ttFiber30RowCheck 14 &&
    ttFiber30RowCheck 15 &&
    ttFiber30RowCheck 16 &&
    ttFiber30RowCheck 17 &&
    ttFiber30RowCheck 18 &&
    ttFiber30RowCheck 19 &&
    ttFiber30RowCheck 20 &&
    ttFiber30RowCheck 21 &&
    ttFiber30RowCheck 22 &&
    ttFiber30RowCheck 23 &&
    ttFiber30RowCheck 24 &&
    ttFiber30RowCheck 25 &&
    ttFiber30RowCheck 26 &&
    ttFiber30RowCheck 27 &&
    ttFiber30RowCheck 28 &&
    ttFiber30RowCheck 29 &&
    ttFiber30RowCheck 30 &&
    ttFiber30RowCheck 31 &&
    ttFiber30RowCheck 32 &&
    ttFiber30RowCheck 33 &&
    ttFiber30RowCheck 34 &&
    ttFiber30RowCheck 35 &&
    ttFiber30RowCheck 36 &&
    ttFiber30RowCheck 37 &&
    ttFiber30RowCheck 38 &&
    ttFiber30RowCheck 39 &&
    ttFiber30RowCheck 40 &&
    ttFiber30RowCheck 41 &&
    ttFiber30RowCheck 42 &&
    ttFiber30RowCheck 43 &&
    ttFiber30RowCheck 44 &&
    ttFiber30RowCheck 45 &&
    ttFiber30RowCheck 46 &&
    ttFiber30RowCheck 47 &&
    ttFiber30RowCheck 48 &&
    ttFiber30RowCheck 49 &&
    ttFiber30RowCheck 50 &&
    ttFiber30RowCheck 51 &&
    ttFiber30RowCheck 52 &&
    ttFiber30RowCheck 53 &&
    ttFiber30RowCheck 54 &&
    ttFiber30RowCheck 55 &&
    ttFiber30RowCheck 56 &&
    ttFiber30RowCheck 57 &&
    ttFiber30RowCheck 58 &&
    ttFiber30RowCheck 59 &&
    ttFiber30RowCheck 60 &&
    ttFiber30RowCheck 61 &&
    ttFiber30RowCheck 62 &&
    ttFiber30RowCheck 63 &&
    ttFiber30ParentCheck 0 &&
    ttFiber30ParentCheck 1 &&
    ttFiber30ParentCheck 2 &&
    ttFiber30ParentCheck 3 &&
    ttFiber30ParentCheck 4 &&
    ttFiber30ParentCheck 5 &&
    ttFiber30ParentCheck 6 &&
    ttFiber30ParentCheck 7 &&
    ttFiber30ParentCheck 8 &&
    ttFiber30ParentCheck 9 &&
    ttFiber30ParentCheck 10 &&
    ttFiber30ParentCheck 11 &&
    ttFiber30ParentCheck 12 &&
    ttFiber30ParentCheck 13 &&
    ttFiber30ParentCheck 14 &&
    ttFiber30ParentCheck 15 &&
    ttFiber30ParentCheck 16 &&
    ttFiber30ParentCheck 17 &&
    ttFiber30ParentCheck 18 &&
    ttFiber30ParentCheck 19 &&
    ttFiber30ParentCheck 20 &&
    ttFiber30ParentCheck 21 &&
    ttFiber30ParentCheck 22 &&
    ttFiber30ParentCheck 23 &&
    ttFiber30ParentCheck 24 &&
    ttFiber30ParentCheck 25 &&
    ttFiber30ParentCheck 26 &&
    ttFiber30ParentCheck 27 &&
    ttFiber30ParentCheck 28 &&
    ttFiber30ParentCheck 29 &&
    ttFiber30ParentCheck 30 &&
    ttFiber30ParentCheck 31 &&
    ttFiber30ParentCheck 32 &&
    ttFiber30ParentCheck 33 &&
    ttFiber30ParentCheck 34 &&
    ttFiber30ParentCheck 35 &&
    ttFiber30ParentCheck 36 &&
    ttFiber30ParentCheck 37 &&
    ttFiber30ParentCheck 38 &&
    ttFiber30ParentCheck 39 &&
    ttFiber30ParentCheck 40 &&
    ttFiber30ParentCheck 41 &&
    ttFiber30ParentCheck 42 &&
    ttFiber30ParentCheck 43 &&
    ttFiber30ParentCheck 44 &&
    ttFiber30ParentCheck 45 &&
    ttFiber30ParentCheck 46 &&
    ttFiber30ParentCheck 47 &&
    ttFiber30ParentCheck 48 &&
    ttFiber30ParentCheck 49 &&
    ttFiber30ParentCheck 50 &&
    ttFiber30ParentCheck 51 &&
    ttFiber30ParentCheck 52 &&
    ttFiber30ParentCheck 53 &&
    ttFiber30ParentCheck 54 &&
    ttFiber30ParentCheck 55 &&
    ttFiber30ParentCheck 56 &&
    ttFiber30ParentCheck 57 &&
    ttFiber30ParentCheck 58 &&
    ttFiber30ParentCheck 59 &&
    ttFiber30ParentCheck 60 &&
    ttFiber30ParentCheck 61 &&
    ttFiber30ParentCheck 62 &&
    ttFiber30ParentCheck 63

theorem ttFiber30CertificateAudit_ok :
    ttFiber30CertificateAudit = true := by
  simp [ttFiber30CertificateAudit,
    ttFiber30SourcesCheck_ok,
    ttFiber30Row_0_ok,
    ttFiber30Row_1_ok,
    ttFiber30Row_2_ok,
    ttFiber30Row_3_ok,
    ttFiber30Row_4_ok,
    ttFiber30Row_5_ok,
    ttFiber30Row_6_ok,
    ttFiber30Row_7_ok,
    ttFiber30Row_8_ok,
    ttFiber30Row_9_ok,
    ttFiber30Row_10_ok,
    ttFiber30Row_11_ok,
    ttFiber30Row_12_ok,
    ttFiber30Row_13_ok,
    ttFiber30Row_14_ok,
    ttFiber30Row_15_ok,
    ttFiber30Row_16_ok,
    ttFiber30Row_17_ok,
    ttFiber30Row_18_ok,
    ttFiber30Row_19_ok,
    ttFiber30Row_20_ok,
    ttFiber30Row_21_ok,
    ttFiber30Row_22_ok,
    ttFiber30Row_23_ok,
    ttFiber30Row_24_ok,
    ttFiber30Row_25_ok,
    ttFiber30Row_26_ok,
    ttFiber30Row_27_ok,
    ttFiber30Row_28_ok,
    ttFiber30Row_29_ok,
    ttFiber30Row_30_ok,
    ttFiber30Row_31_ok,
    ttFiber30Row_32_ok,
    ttFiber30Row_33_ok,
    ttFiber30Row_34_ok,
    ttFiber30Row_35_ok,
    ttFiber30Row_36_ok,
    ttFiber30Row_37_ok,
    ttFiber30Row_38_ok,
    ttFiber30Row_39_ok,
    ttFiber30Row_40_ok,
    ttFiber30Row_41_ok,
    ttFiber30Row_42_ok,
    ttFiber30Row_43_ok,
    ttFiber30Row_44_ok,
    ttFiber30Row_45_ok,
    ttFiber30Row_46_ok,
    ttFiber30Row_47_ok,
    ttFiber30Row_48_ok,
    ttFiber30Row_49_ok,
    ttFiber30Row_50_ok,
    ttFiber30Row_51_ok,
    ttFiber30Row_52_ok,
    ttFiber30Row_53_ok,
    ttFiber30Row_54_ok,
    ttFiber30Row_55_ok,
    ttFiber30Row_56_ok,
    ttFiber30Row_57_ok,
    ttFiber30Row_58_ok,
    ttFiber30Row_59_ok,
    ttFiber30Row_60_ok,
    ttFiber30Row_61_ok,
    ttFiber30Row_62_ok,
    ttFiber30Row_63_ok,
    ttFiber30Parent_0_ok,
    ttFiber30Parent_1_ok,
    ttFiber30Parent_2_ok,
    ttFiber30Parent_3_ok,
    ttFiber30Parent_4_ok,
    ttFiber30Parent_5_ok,
    ttFiber30Parent_6_ok,
    ttFiber30Parent_7_ok,
    ttFiber30Parent_8_ok,
    ttFiber30Parent_9_ok,
    ttFiber30Parent_10_ok,
    ttFiber30Parent_11_ok,
    ttFiber30Parent_12_ok,
    ttFiber30Parent_13_ok,
    ttFiber30Parent_14_ok,
    ttFiber30Parent_15_ok,
    ttFiber30Parent_16_ok,
    ttFiber30Parent_17_ok,
    ttFiber30Parent_18_ok,
    ttFiber30Parent_19_ok,
    ttFiber30Parent_20_ok,
    ttFiber30Parent_21_ok,
    ttFiber30Parent_22_ok,
    ttFiber30Parent_23_ok,
    ttFiber30Parent_24_ok,
    ttFiber30Parent_25_ok,
    ttFiber30Parent_26_ok,
    ttFiber30Parent_27_ok,
    ttFiber30Parent_28_ok,
    ttFiber30Parent_29_ok,
    ttFiber30Parent_30_ok,
    ttFiber30Parent_31_ok,
    ttFiber30Parent_32_ok,
    ttFiber30Parent_33_ok,
    ttFiber30Parent_34_ok,
    ttFiber30Parent_35_ok,
    ttFiber30Parent_36_ok,
    ttFiber30Parent_37_ok,
    ttFiber30Parent_38_ok,
    ttFiber30Parent_39_ok,
    ttFiber30Parent_40_ok,
    ttFiber30Parent_41_ok,
    ttFiber30Parent_42_ok,
    ttFiber30Parent_43_ok,
    ttFiber30Parent_44_ok,
    ttFiber30Parent_45_ok,
    ttFiber30Parent_46_ok,
    ttFiber30Parent_47_ok,
    ttFiber30Parent_48_ok,
    ttFiber30Parent_49_ok,
    ttFiber30Parent_50_ok,
    ttFiber30Parent_51_ok,
    ttFiber30Parent_52_ok,
    ttFiber30Parent_53_ok,
    ttFiber30Parent_54_ok,
    ttFiber30Parent_55_ok,
    ttFiber30Parent_56_ok,
    ttFiber30Parent_57_ok,
    ttFiber30Parent_58_ok,
    ttFiber30Parent_59_ok,
    ttFiber30Parent_60_ok,
    ttFiber30Parent_61_ok,
    ttFiber30Parent_62_ok,
    ttFiber30Parent_63_ok]

def ttFiber31Key : List LColor :=
  [LColor.b, LColor.r, LColor.b, LColor.b]

def ttFiber31Expected : List Nat :=
  [272, 273, 274, 275, 276, 277, 278, 279]

def ttFiber31Rows : List DirectChainParentRow :=
  [ directRow 272 272 54 112 54 112 default
  , directRow 273 272 54 113 54 112 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 274 272 54 114 54 112 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 275 273 54 115 54 113 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 276 272 55 120 54 112 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 277 273 55 121 54 113 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 278 274 55 122 54 114 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 279 275 55 123 54 115 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  ]

def ttFiber31RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber31Rows i default

def ttFiber31SourcesCheck : Bool :=
  (ttFiber31Rows.map fun row => row.source) == ttFiber31Expected

theorem ttFiber31SourcesCheck_ok :
    ttFiber31SourcesCheck = true := by
  decide

def ttFiber31RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber31Key ttFiber31Expected (ttFiber31RowAt i)

theorem ttFiber31Row_0_ok : ttFiber31RowCheck 0 = true := by decide
theorem ttFiber31Row_1_ok : ttFiber31RowCheck 1 = true := by decide
theorem ttFiber31Row_2_ok : ttFiber31RowCheck 2 = true := by decide
theorem ttFiber31Row_3_ok : ttFiber31RowCheck 3 = true := by decide
theorem ttFiber31Row_4_ok : ttFiber31RowCheck 4 = true := by decide
theorem ttFiber31Row_5_ok : ttFiber31RowCheck 5 = true := by decide
theorem ttFiber31Row_6_ok : ttFiber31RowCheck 6 = true := by decide
theorem ttFiber31Row_7_ok : ttFiber31RowCheck 7 = true := by decide

def ttFiber31ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber31Rows ttMaxParentDepth (listGetD ttFiber31Expected i 0) == 272

theorem ttFiber31Parent_0_ok : ttFiber31ParentCheck 0 = true := by decide
theorem ttFiber31Parent_1_ok : ttFiber31ParentCheck 1 = true := by decide
theorem ttFiber31Parent_2_ok : ttFiber31ParentCheck 2 = true := by decide
theorem ttFiber31Parent_3_ok : ttFiber31ParentCheck 3 = true := by decide
theorem ttFiber31Parent_4_ok : ttFiber31ParentCheck 4 = true := by decide
theorem ttFiber31Parent_5_ok : ttFiber31ParentCheck 5 = true := by decide
theorem ttFiber31Parent_6_ok : ttFiber31ParentCheck 6 = true := by decide
theorem ttFiber31Parent_7_ok : ttFiber31ParentCheck 7 = true := by decide

def ttFiber31CertificateAudit : Bool :=
  ttFiber31SourcesCheck &&
    ttFiber31RowCheck 0 &&
    ttFiber31RowCheck 1 &&
    ttFiber31RowCheck 2 &&
    ttFiber31RowCheck 3 &&
    ttFiber31RowCheck 4 &&
    ttFiber31RowCheck 5 &&
    ttFiber31RowCheck 6 &&
    ttFiber31RowCheck 7 &&
    ttFiber31ParentCheck 0 &&
    ttFiber31ParentCheck 1 &&
    ttFiber31ParentCheck 2 &&
    ttFiber31ParentCheck 3 &&
    ttFiber31ParentCheck 4 &&
    ttFiber31ParentCheck 5 &&
    ttFiber31ParentCheck 6 &&
    ttFiber31ParentCheck 7

theorem ttFiber31CertificateAudit_ok :
    ttFiber31CertificateAudit = true := by
  simp [ttFiber31CertificateAudit,
    ttFiber31SourcesCheck_ok,
    ttFiber31Row_0_ok,
    ttFiber31Row_1_ok,
    ttFiber31Row_2_ok,
    ttFiber31Row_3_ok,
    ttFiber31Row_4_ok,
    ttFiber31Row_5_ok,
    ttFiber31Row_6_ok,
    ttFiber31Row_7_ok,
    ttFiber31Parent_0_ok,
    ttFiber31Parent_1_ok,
    ttFiber31Parent_2_ok,
    ttFiber31Parent_3_ok,
    ttFiber31Parent_4_ok,
    ttFiber31Parent_5_ok,
    ttFiber31Parent_6_ok,
    ttFiber31Parent_7_ok]

def ttFiber32Key : List LColor :=
  [LColor.b, LColor.r, LColor.b, LColor.p]

def ttFiber32Expected : List Nat :=
  [32, 33, 34, 35, 36, 37, 38, 39]

def ttFiber32Rows : List DirectChainParentRow :=
  [ directRow 32 32 6 176 6 176 default
  , directRow 33 32 6 177 6 176 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 34 32 6 178 6 176 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 35 33 6 179 6 177 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 36 32 7 184 6 176 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 37 33 7 185 6 177 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 38 34 7 186 6 178 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 39 35 7 187 6 179 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  ]

def ttFiber32RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber32Rows i default

def ttFiber32SourcesCheck : Bool :=
  (ttFiber32Rows.map fun row => row.source) == ttFiber32Expected

theorem ttFiber32SourcesCheck_ok :
    ttFiber32SourcesCheck = true := by
  decide

def ttFiber32RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber32Key ttFiber32Expected (ttFiber32RowAt i)

theorem ttFiber32Row_0_ok : ttFiber32RowCheck 0 = true := by decide
theorem ttFiber32Row_1_ok : ttFiber32RowCheck 1 = true := by decide
theorem ttFiber32Row_2_ok : ttFiber32RowCheck 2 = true := by decide
theorem ttFiber32Row_3_ok : ttFiber32RowCheck 3 = true := by decide
theorem ttFiber32Row_4_ok : ttFiber32RowCheck 4 = true := by decide
theorem ttFiber32Row_5_ok : ttFiber32RowCheck 5 = true := by decide
theorem ttFiber32Row_6_ok : ttFiber32RowCheck 6 = true := by decide
theorem ttFiber32Row_7_ok : ttFiber32RowCheck 7 = true := by decide

def ttFiber32ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber32Rows ttMaxParentDepth (listGetD ttFiber32Expected i 0) == 32

theorem ttFiber32Parent_0_ok : ttFiber32ParentCheck 0 = true := by decide
theorem ttFiber32Parent_1_ok : ttFiber32ParentCheck 1 = true := by decide
theorem ttFiber32Parent_2_ok : ttFiber32ParentCheck 2 = true := by decide
theorem ttFiber32Parent_3_ok : ttFiber32ParentCheck 3 = true := by decide
theorem ttFiber32Parent_4_ok : ttFiber32ParentCheck 4 = true := by decide
theorem ttFiber32Parent_5_ok : ttFiber32ParentCheck 5 = true := by decide
theorem ttFiber32Parent_6_ok : ttFiber32ParentCheck 6 = true := by decide
theorem ttFiber32Parent_7_ok : ttFiber32ParentCheck 7 = true := by decide

def ttFiber32CertificateAudit : Bool :=
  ttFiber32SourcesCheck &&
    ttFiber32RowCheck 0 &&
    ttFiber32RowCheck 1 &&
    ttFiber32RowCheck 2 &&
    ttFiber32RowCheck 3 &&
    ttFiber32RowCheck 4 &&
    ttFiber32RowCheck 5 &&
    ttFiber32RowCheck 6 &&
    ttFiber32RowCheck 7 &&
    ttFiber32ParentCheck 0 &&
    ttFiber32ParentCheck 1 &&
    ttFiber32ParentCheck 2 &&
    ttFiber32ParentCheck 3 &&
    ttFiber32ParentCheck 4 &&
    ttFiber32ParentCheck 5 &&
    ttFiber32ParentCheck 6 &&
    ttFiber32ParentCheck 7

theorem ttFiber32CertificateAudit_ok :
    ttFiber32CertificateAudit = true := by
  simp [ttFiber32CertificateAudit,
    ttFiber32SourcesCheck_ok,
    ttFiber32Row_0_ok,
    ttFiber32Row_1_ok,
    ttFiber32Row_2_ok,
    ttFiber32Row_3_ok,
    ttFiber32Row_4_ok,
    ttFiber32Row_5_ok,
    ttFiber32Row_6_ok,
    ttFiber32Row_7_ok,
    ttFiber32Parent_0_ok,
    ttFiber32Parent_1_ok,
    ttFiber32Parent_2_ok,
    ttFiber32Parent_3_ok,
    ttFiber32Parent_4_ok,
    ttFiber32Parent_5_ok,
    ttFiber32Parent_6_ok,
    ttFiber32Parent_7_ok]

def ttFiber33Key : List LColor :=
  [LColor.b, LColor.r, LColor.p, LColor.r]

def ttFiber33Expected : List Nat :=
  []

def ttFiber33Rows : List DirectChainParentRow :=
  []

def ttFiber33RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber33Rows i default

def ttFiber33SourcesCheck : Bool :=
  (ttFiber33Rows.map fun row => row.source) == ttFiber33Expected

theorem ttFiber33SourcesCheck_ok :
    ttFiber33SourcesCheck = true := by
  decide

def ttFiber33RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber33Key ttFiber33Expected (ttFiber33RowAt i)

def ttFiber33ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber33Rows ttMaxParentDepth (listGetD ttFiber33Expected i 0) == 0

def ttFiber33CertificateAudit : Bool :=
  ttFiber33SourcesCheck

theorem ttFiber33CertificateAudit_ok :
    ttFiber33CertificateAudit = true := by
  simp [ttFiber33CertificateAudit,
    ttFiber33SourcesCheck_ok]

def ttFiber34Key : List LColor :=
  [LColor.b, LColor.r, LColor.p, LColor.b]

def ttFiber34Expected : List Nat :=
  []

def ttFiber34Rows : List DirectChainParentRow :=
  []

def ttFiber34RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber34Rows i default

def ttFiber34SourcesCheck : Bool :=
  (ttFiber34Rows.map fun row => row.source) == ttFiber34Expected

theorem ttFiber34SourcesCheck_ok :
    ttFiber34SourcesCheck = true := by
  decide

def ttFiber34RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber34Key ttFiber34Expected (ttFiber34RowAt i)

def ttFiber34ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber34Rows ttMaxParentDepth (listGetD ttFiber34Expected i 0) == 0

def ttFiber34CertificateAudit : Bool :=
  ttFiber34SourcesCheck

theorem ttFiber34CertificateAudit_ok :
    ttFiber34CertificateAudit = true := by
  simp [ttFiber34CertificateAudit,
    ttFiber34SourcesCheck_ok]

def ttFiber35Key : List LColor :=
  [LColor.b, LColor.r, LColor.p, LColor.p]

def ttFiber35Expected : List Nat :=
  []

def ttFiber35Rows : List DirectChainParentRow :=
  []

def ttFiber35RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber35Rows i default

def ttFiber35SourcesCheck : Bool :=
  (ttFiber35Rows.map fun row => row.source) == ttFiber35Expected

theorem ttFiber35SourcesCheck_ok :
    ttFiber35SourcesCheck = true := by
  decide

def ttFiber35RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber35Key ttFiber35Expected (ttFiber35RowAt i)

def ttFiber35ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber35Rows ttMaxParentDepth (listGetD ttFiber35Expected i 0) == 0

def ttFiber35CertificateAudit : Bool :=
  ttFiber35SourcesCheck

theorem ttFiber35CertificateAudit_ok :
    ttFiber35CertificateAudit = true := by
  simp [ttFiber35CertificateAudit,
    ttFiber35SourcesCheck_ok]

def ttFiber36Key : List LColor :=
  [LColor.b, LColor.b, LColor.r, LColor.r]

def ttFiber36Expected : List Nat :=
  [40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311]

def ttFiber36Rows : List DirectChainParentRow :=
  [ directRow 40 40 8 80 8 80 default
  , directRow 41 40 8 81 8 80 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 42 40 8 82 8 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 43 41 8 83 8 81 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 44 42 8 100 8 82 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 45 47 8 101 8 103 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 46 41 8 102 8 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 47 40 8 103 8 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 48 40 9 88 8 80 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 49 41 9 89 8 81 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 50 42 9 90 8 82 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 51 43 9 91 8 83 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 52 44 9 108 8 100 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 53 45 9 109 8 101 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 54 46 9 110 8 102 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 55 47 9 111 8 103 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 56 40 10 16 8 80 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 57 41 10 17 8 81 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 58 42 10 18 8 82 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 59 43 10 19 8 83 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 60 56 10 32 10 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 61 57 10 33 10 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 62 46 10 34 8 102 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 63 47 10 35 8 103 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 64 48 11 24 9 88 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 65 49 11 25 9 89 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 66 50 11 26 9 90 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 67 51 11 27 9 91 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 68 64 11 40 11 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 69 65 11 41 11 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 70 54 11 42 9 110 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 71 55 11 43 9 111 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 280 40 56 148 8 80 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 281 41 56 149 8 81 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 282 42 56 150 8 82 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 283 280 56 151 56 148 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 284 280 56 164 56 148 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 285 281 56 165 56 149 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 286 46 56 166 8 102 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 287 47 56 167 8 103 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 288 48 57 156 9 88 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 289 49 57 157 9 89 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 290 50 57 158 9 90 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 291 288 57 159 57 156 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 292 288 57 172 57 156 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 293 289 57 173 57 157 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 294 54 57 174 9 110 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 295 55 57 175 9 111 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 296 56 58 0 10 16 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 297 57 58 1 10 17 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 298 58 58 2 10 18 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 299 59 58 3 10 19 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 300 288 58 48 57 156 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 301 289 58 49 57 157 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 302 62 58 50 10 34 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 303 63 58 51 10 35 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 304 287 59 8 56 167 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 305 286 59 9 56 166 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 306 284 59 10 56 164 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 307 285 59 11 56 165 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 308 280 59 56 56 148 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 309 281 59 57 56 149 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 310 282 59 58 56 150 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 311 283 59 59 56 151 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def ttFiber36RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber36Rows i default

def ttFiber36SourcesCheck : Bool :=
  (ttFiber36Rows.map fun row => row.source) == ttFiber36Expected

theorem ttFiber36SourcesCheck_ok :
    ttFiber36SourcesCheck = true := by
  decide

def ttFiber36RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt i)

theorem ttFiber36Row_0_ok : ttFiber36RowCheck 0 = true := by decide
theorem ttFiber36Row_1_ok : ttFiber36RowCheck 1 = true := by decide
theorem ttFiber36Row_2_ok : ttFiber36RowCheck 2 = true := by decide
theorem ttFiber36Row_3_ok : ttFiber36RowCheck 3 = true := by decide
theorem ttFiber36Row_4_ok : ttFiber36RowCheck 4 = true := by decide
theorem ttFiber36Row_5_ok : ttFiber36RowCheck 5 = true := by decide
theorem ttFiber36Row_6_ok : ttFiber36RowCheck 6 = true := by decide
theorem ttFiber36Row_7_ok : ttFiber36RowCheck 7 = true := by decide
theorem ttFiber36Row_8_ok : ttFiber36RowCheck 8 = true := by decide
theorem ttFiber36Row_9_ok : ttFiber36RowCheck 9 = true := by decide
theorem ttFiber36Row_10_ok : ttFiber36RowCheck 10 = true := by decide
theorem ttFiber36Row_11_ok : ttFiber36RowCheck 11 = true := by decide
theorem ttFiber36Row_12_ok : ttFiber36RowCheck 12 = true := by decide
theorem ttFiber36Row_13_ok : ttFiber36RowCheck 13 = true := by decide
theorem ttFiber36Row_14_ok : ttFiber36RowCheck 14 = true := by decide
theorem ttFiber36Row_15_ok : ttFiber36RowCheck 15 = true := by decide
theorem ttFiber36Row_16_ok : ttFiber36RowCheck 16 = true := by decide
theorem ttFiber36Row_17_ok : ttFiber36RowCheck 17 = true := by decide
theorem ttFiber36Row_18_ok : ttFiber36RowCheck 18 = true := by decide
theorem ttFiber36Row_19_ok : ttFiber36RowCheck 19 = true := by decide
theorem ttFiber36Row_20_ok : ttFiber36RowCheck 20 = true := by decide
theorem ttFiber36Row_21_ok : ttFiber36RowCheck 21 = true := by decide
theorem ttFiber36Row_22_ok : ttFiber36RowCheck 22 = true := by decide
theorem ttFiber36Row_23_ok : ttFiber36RowCheck 23 = true := by decide
theorem ttFiber36Row_24_ok : ttFiber36RowCheck 24 = true := by decide
theorem ttFiber36Row_25_ok : ttFiber36RowCheck 25 = true := by decide
theorem ttFiber36Row_26_ok : ttFiber36RowCheck 26 = true := by decide
theorem ttFiber36Row_27_ok : ttFiber36RowCheck 27 = true := by decide
theorem ttFiber36Row_28_ok : ttFiber36RowCheck 28 = true := by decide
theorem ttFiber36Row_29_ok : ttFiber36RowCheck 29 = true := by decide
theorem ttFiber36Row_30_ok : ttFiber36RowCheck 30 = true := by decide
theorem ttFiber36Row_31_ok : ttFiber36RowCheck 31 = true := by decide
theorem ttFiber36Row_32_ok : ttFiber36RowCheck 32 = true := by decide
theorem ttFiber36Row_33_ok : ttFiber36RowCheck 33 = true := by decide
theorem ttFiber36Row_34_ok : ttFiber36RowCheck 34 = true := by decide
theorem ttFiber36Row_35_ok : ttFiber36RowCheck 35 = true := by decide
theorem ttFiber36Row_36_ok : ttFiber36RowCheck 36 = true := by decide
theorem ttFiber36Row_37_ok : ttFiber36RowCheck 37 = true := by decide
theorem ttFiber36Row_38_ok : ttFiber36RowCheck 38 = true := by decide
theorem ttFiber36Row_39_ok : ttFiber36RowCheck 39 = true := by decide
theorem ttFiber36Row_40_ok : ttFiber36RowCheck 40 = true := by decide
theorem ttFiber36Row_41_ok : ttFiber36RowCheck 41 = true := by decide
theorem ttFiber36Row_42_ok : ttFiber36RowCheck 42 = true := by decide
theorem ttFiber36Row_43_ok : ttFiber36RowCheck 43 = true := by decide
theorem ttFiber36Row_44_ok : ttFiber36RowCheck 44 = true := by decide
theorem ttFiber36Row_45_ok : ttFiber36RowCheck 45 = true := by decide
theorem ttFiber36Row_46_ok : ttFiber36RowCheck 46 = true := by decide
theorem ttFiber36Row_47_ok : ttFiber36RowCheck 47 = true := by decide
theorem ttFiber36Row_48_ok : ttFiber36RowCheck 48 = true := by decide
theorem ttFiber36Row_49_ok : ttFiber36RowCheck 49 = true := by decide
theorem ttFiber36Row_50_ok : ttFiber36RowCheck 50 = true := by decide
theorem ttFiber36Row_51_ok : ttFiber36RowCheck 51 = true := by decide
theorem ttFiber36Row_52_ok : ttFiber36RowCheck 52 = true := by decide
theorem ttFiber36Row_53_ok : ttFiber36RowCheck 53 = true := by decide
theorem ttFiber36Row_54_ok : ttFiber36RowCheck 54 = true := by decide
theorem ttFiber36Row_55_ok : ttFiber36RowCheck 55 = true := by decide
theorem ttFiber36Row_56_ok : ttFiber36RowCheck 56 = true := by decide
theorem ttFiber36Row_57_ok : ttFiber36RowCheck 57 = true := by decide
theorem ttFiber36Row_58_ok : ttFiber36RowCheck 58 = true := by decide
theorem ttFiber36Row_59_ok : ttFiber36RowCheck 59 = true := by decide
theorem ttFiber36Row_60_ok : ttFiber36RowCheck 60 = true := by decide
theorem ttFiber36Row_61_ok : ttFiber36RowCheck 61 = true := by decide
theorem ttFiber36Row_62_ok : ttFiber36RowCheck 62 = true := by decide
theorem ttFiber36Row_63_ok : ttFiber36RowCheck 63 = true := by decide

def ttFiber36ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber36Rows ttMaxParentDepth (listGetD ttFiber36Expected i 0) == 40

theorem ttFiber36Parent_0_ok : ttFiber36ParentCheck 0 = true := by decide
theorem ttFiber36Parent_1_ok : ttFiber36ParentCheck 1 = true := by decide
theorem ttFiber36Parent_2_ok : ttFiber36ParentCheck 2 = true := by decide
theorem ttFiber36Parent_3_ok : ttFiber36ParentCheck 3 = true := by decide
theorem ttFiber36Parent_4_ok : ttFiber36ParentCheck 4 = true := by decide
theorem ttFiber36Parent_5_ok : ttFiber36ParentCheck 5 = true := by decide
theorem ttFiber36Parent_6_ok : ttFiber36ParentCheck 6 = true := by decide
theorem ttFiber36Parent_7_ok : ttFiber36ParentCheck 7 = true := by decide
theorem ttFiber36Parent_8_ok : ttFiber36ParentCheck 8 = true := by decide
theorem ttFiber36Parent_9_ok : ttFiber36ParentCheck 9 = true := by decide
theorem ttFiber36Parent_10_ok : ttFiber36ParentCheck 10 = true := by decide
theorem ttFiber36Parent_11_ok : ttFiber36ParentCheck 11 = true := by decide
theorem ttFiber36Parent_12_ok : ttFiber36ParentCheck 12 = true := by decide
theorem ttFiber36Parent_13_ok : ttFiber36ParentCheck 13 = true := by decide
theorem ttFiber36Parent_14_ok : ttFiber36ParentCheck 14 = true := by decide
theorem ttFiber36Parent_15_ok : ttFiber36ParentCheck 15 = true := by decide
theorem ttFiber36Parent_16_ok : ttFiber36ParentCheck 16 = true := by decide
theorem ttFiber36Parent_17_ok : ttFiber36ParentCheck 17 = true := by decide
theorem ttFiber36Parent_18_ok : ttFiber36ParentCheck 18 = true := by decide
theorem ttFiber36Parent_19_ok : ttFiber36ParentCheck 19 = true := by decide
theorem ttFiber36Parent_20_ok : ttFiber36ParentCheck 20 = true := by decide
theorem ttFiber36Parent_21_ok : ttFiber36ParentCheck 21 = true := by decide
theorem ttFiber36Parent_22_ok : ttFiber36ParentCheck 22 = true := by decide
theorem ttFiber36Parent_23_ok : ttFiber36ParentCheck 23 = true := by decide
theorem ttFiber36Parent_24_ok : ttFiber36ParentCheck 24 = true := by decide
theorem ttFiber36Parent_25_ok : ttFiber36ParentCheck 25 = true := by decide
theorem ttFiber36Parent_26_ok : ttFiber36ParentCheck 26 = true := by decide
theorem ttFiber36Parent_27_ok : ttFiber36ParentCheck 27 = true := by decide
theorem ttFiber36Parent_28_ok : ttFiber36ParentCheck 28 = true := by decide
theorem ttFiber36Parent_29_ok : ttFiber36ParentCheck 29 = true := by decide
theorem ttFiber36Parent_30_ok : ttFiber36ParentCheck 30 = true := by decide
theorem ttFiber36Parent_31_ok : ttFiber36ParentCheck 31 = true := by decide
theorem ttFiber36Parent_32_ok : ttFiber36ParentCheck 32 = true := by decide
theorem ttFiber36Parent_33_ok : ttFiber36ParentCheck 33 = true := by decide
theorem ttFiber36Parent_34_ok : ttFiber36ParentCheck 34 = true := by decide
theorem ttFiber36Parent_35_ok : ttFiber36ParentCheck 35 = true := by decide
theorem ttFiber36Parent_36_ok : ttFiber36ParentCheck 36 = true := by decide
theorem ttFiber36Parent_37_ok : ttFiber36ParentCheck 37 = true := by decide
theorem ttFiber36Parent_38_ok : ttFiber36ParentCheck 38 = true := by decide
theorem ttFiber36Parent_39_ok : ttFiber36ParentCheck 39 = true := by decide
theorem ttFiber36Parent_40_ok : ttFiber36ParentCheck 40 = true := by decide
theorem ttFiber36Parent_41_ok : ttFiber36ParentCheck 41 = true := by decide
theorem ttFiber36Parent_42_ok : ttFiber36ParentCheck 42 = true := by decide
theorem ttFiber36Parent_43_ok : ttFiber36ParentCheck 43 = true := by decide
theorem ttFiber36Parent_44_ok : ttFiber36ParentCheck 44 = true := by decide
theorem ttFiber36Parent_45_ok : ttFiber36ParentCheck 45 = true := by decide
theorem ttFiber36Parent_46_ok : ttFiber36ParentCheck 46 = true := by decide
theorem ttFiber36Parent_47_ok : ttFiber36ParentCheck 47 = true := by decide
theorem ttFiber36Parent_48_ok : ttFiber36ParentCheck 48 = true := by decide
theorem ttFiber36Parent_49_ok : ttFiber36ParentCheck 49 = true := by decide
theorem ttFiber36Parent_50_ok : ttFiber36ParentCheck 50 = true := by decide
theorem ttFiber36Parent_51_ok : ttFiber36ParentCheck 51 = true := by decide
theorem ttFiber36Parent_52_ok : ttFiber36ParentCheck 52 = true := by decide
theorem ttFiber36Parent_53_ok : ttFiber36ParentCheck 53 = true := by decide
theorem ttFiber36Parent_54_ok : ttFiber36ParentCheck 54 = true := by decide
theorem ttFiber36Parent_55_ok : ttFiber36ParentCheck 55 = true := by decide
theorem ttFiber36Parent_56_ok : ttFiber36ParentCheck 56 = true := by decide
theorem ttFiber36Parent_57_ok : ttFiber36ParentCheck 57 = true := by decide
theorem ttFiber36Parent_58_ok : ttFiber36ParentCheck 58 = true := by decide
theorem ttFiber36Parent_59_ok : ttFiber36ParentCheck 59 = true := by decide
theorem ttFiber36Parent_60_ok : ttFiber36ParentCheck 60 = true := by decide
theorem ttFiber36Parent_61_ok : ttFiber36ParentCheck 61 = true := by decide
theorem ttFiber36Parent_62_ok : ttFiber36ParentCheck 62 = true := by decide
theorem ttFiber36Parent_63_ok : ttFiber36ParentCheck 63 = true := by decide

def ttFiber36CertificateAudit : Bool :=
  ttFiber36SourcesCheck &&
    ttFiber36RowCheck 0 &&
    ttFiber36RowCheck 1 &&
    ttFiber36RowCheck 2 &&
    ttFiber36RowCheck 3 &&
    ttFiber36RowCheck 4 &&
    ttFiber36RowCheck 5 &&
    ttFiber36RowCheck 6 &&
    ttFiber36RowCheck 7 &&
    ttFiber36RowCheck 8 &&
    ttFiber36RowCheck 9 &&
    ttFiber36RowCheck 10 &&
    ttFiber36RowCheck 11 &&
    ttFiber36RowCheck 12 &&
    ttFiber36RowCheck 13 &&
    ttFiber36RowCheck 14 &&
    ttFiber36RowCheck 15 &&
    ttFiber36RowCheck 16 &&
    ttFiber36RowCheck 17 &&
    ttFiber36RowCheck 18 &&
    ttFiber36RowCheck 19 &&
    ttFiber36RowCheck 20 &&
    ttFiber36RowCheck 21 &&
    ttFiber36RowCheck 22 &&
    ttFiber36RowCheck 23 &&
    ttFiber36RowCheck 24 &&
    ttFiber36RowCheck 25 &&
    ttFiber36RowCheck 26 &&
    ttFiber36RowCheck 27 &&
    ttFiber36RowCheck 28 &&
    ttFiber36RowCheck 29 &&
    ttFiber36RowCheck 30 &&
    ttFiber36RowCheck 31 &&
    ttFiber36RowCheck 32 &&
    ttFiber36RowCheck 33 &&
    ttFiber36RowCheck 34 &&
    ttFiber36RowCheck 35 &&
    ttFiber36RowCheck 36 &&
    ttFiber36RowCheck 37 &&
    ttFiber36RowCheck 38 &&
    ttFiber36RowCheck 39 &&
    ttFiber36RowCheck 40 &&
    ttFiber36RowCheck 41 &&
    ttFiber36RowCheck 42 &&
    ttFiber36RowCheck 43 &&
    ttFiber36RowCheck 44 &&
    ttFiber36RowCheck 45 &&
    ttFiber36RowCheck 46 &&
    ttFiber36RowCheck 47 &&
    ttFiber36RowCheck 48 &&
    ttFiber36RowCheck 49 &&
    ttFiber36RowCheck 50 &&
    ttFiber36RowCheck 51 &&
    ttFiber36RowCheck 52 &&
    ttFiber36RowCheck 53 &&
    ttFiber36RowCheck 54 &&
    ttFiber36RowCheck 55 &&
    ttFiber36RowCheck 56 &&
    ttFiber36RowCheck 57 &&
    ttFiber36RowCheck 58 &&
    ttFiber36RowCheck 59 &&
    ttFiber36RowCheck 60 &&
    ttFiber36RowCheck 61 &&
    ttFiber36RowCheck 62 &&
    ttFiber36RowCheck 63 &&
    ttFiber36ParentCheck 0 &&
    ttFiber36ParentCheck 1 &&
    ttFiber36ParentCheck 2 &&
    ttFiber36ParentCheck 3 &&
    ttFiber36ParentCheck 4 &&
    ttFiber36ParentCheck 5 &&
    ttFiber36ParentCheck 6 &&
    ttFiber36ParentCheck 7 &&
    ttFiber36ParentCheck 8 &&
    ttFiber36ParentCheck 9 &&
    ttFiber36ParentCheck 10 &&
    ttFiber36ParentCheck 11 &&
    ttFiber36ParentCheck 12 &&
    ttFiber36ParentCheck 13 &&
    ttFiber36ParentCheck 14 &&
    ttFiber36ParentCheck 15 &&
    ttFiber36ParentCheck 16 &&
    ttFiber36ParentCheck 17 &&
    ttFiber36ParentCheck 18 &&
    ttFiber36ParentCheck 19 &&
    ttFiber36ParentCheck 20 &&
    ttFiber36ParentCheck 21 &&
    ttFiber36ParentCheck 22 &&
    ttFiber36ParentCheck 23 &&
    ttFiber36ParentCheck 24 &&
    ttFiber36ParentCheck 25 &&
    ttFiber36ParentCheck 26 &&
    ttFiber36ParentCheck 27 &&
    ttFiber36ParentCheck 28 &&
    ttFiber36ParentCheck 29 &&
    ttFiber36ParentCheck 30 &&
    ttFiber36ParentCheck 31 &&
    ttFiber36ParentCheck 32 &&
    ttFiber36ParentCheck 33 &&
    ttFiber36ParentCheck 34 &&
    ttFiber36ParentCheck 35 &&
    ttFiber36ParentCheck 36 &&
    ttFiber36ParentCheck 37 &&
    ttFiber36ParentCheck 38 &&
    ttFiber36ParentCheck 39 &&
    ttFiber36ParentCheck 40 &&
    ttFiber36ParentCheck 41 &&
    ttFiber36ParentCheck 42 &&
    ttFiber36ParentCheck 43 &&
    ttFiber36ParentCheck 44 &&
    ttFiber36ParentCheck 45 &&
    ttFiber36ParentCheck 46 &&
    ttFiber36ParentCheck 47 &&
    ttFiber36ParentCheck 48 &&
    ttFiber36ParentCheck 49 &&
    ttFiber36ParentCheck 50 &&
    ttFiber36ParentCheck 51 &&
    ttFiber36ParentCheck 52 &&
    ttFiber36ParentCheck 53 &&
    ttFiber36ParentCheck 54 &&
    ttFiber36ParentCheck 55 &&
    ttFiber36ParentCheck 56 &&
    ttFiber36ParentCheck 57 &&
    ttFiber36ParentCheck 58 &&
    ttFiber36ParentCheck 59 &&
    ttFiber36ParentCheck 60 &&
    ttFiber36ParentCheck 61 &&
    ttFiber36ParentCheck 62 &&
    ttFiber36ParentCheck 63

theorem ttFiber36CertificateAudit_ok :
    ttFiber36CertificateAudit = true := by
  simp [ttFiber36CertificateAudit,
    ttFiber36SourcesCheck_ok,
    ttFiber36Row_0_ok,
    ttFiber36Row_1_ok,
    ttFiber36Row_2_ok,
    ttFiber36Row_3_ok,
    ttFiber36Row_4_ok,
    ttFiber36Row_5_ok,
    ttFiber36Row_6_ok,
    ttFiber36Row_7_ok,
    ttFiber36Row_8_ok,
    ttFiber36Row_9_ok,
    ttFiber36Row_10_ok,
    ttFiber36Row_11_ok,
    ttFiber36Row_12_ok,
    ttFiber36Row_13_ok,
    ttFiber36Row_14_ok,
    ttFiber36Row_15_ok,
    ttFiber36Row_16_ok,
    ttFiber36Row_17_ok,
    ttFiber36Row_18_ok,
    ttFiber36Row_19_ok,
    ttFiber36Row_20_ok,
    ttFiber36Row_21_ok,
    ttFiber36Row_22_ok,
    ttFiber36Row_23_ok,
    ttFiber36Row_24_ok,
    ttFiber36Row_25_ok,
    ttFiber36Row_26_ok,
    ttFiber36Row_27_ok,
    ttFiber36Row_28_ok,
    ttFiber36Row_29_ok,
    ttFiber36Row_30_ok,
    ttFiber36Row_31_ok,
    ttFiber36Row_32_ok,
    ttFiber36Row_33_ok,
    ttFiber36Row_34_ok,
    ttFiber36Row_35_ok,
    ttFiber36Row_36_ok,
    ttFiber36Row_37_ok,
    ttFiber36Row_38_ok,
    ttFiber36Row_39_ok,
    ttFiber36Row_40_ok,
    ttFiber36Row_41_ok,
    ttFiber36Row_42_ok,
    ttFiber36Row_43_ok,
    ttFiber36Row_44_ok,
    ttFiber36Row_45_ok,
    ttFiber36Row_46_ok,
    ttFiber36Row_47_ok,
    ttFiber36Row_48_ok,
    ttFiber36Row_49_ok,
    ttFiber36Row_50_ok,
    ttFiber36Row_51_ok,
    ttFiber36Row_52_ok,
    ttFiber36Row_53_ok,
    ttFiber36Row_54_ok,
    ttFiber36Row_55_ok,
    ttFiber36Row_56_ok,
    ttFiber36Row_57_ok,
    ttFiber36Row_58_ok,
    ttFiber36Row_59_ok,
    ttFiber36Row_60_ok,
    ttFiber36Row_61_ok,
    ttFiber36Row_62_ok,
    ttFiber36Row_63_ok,
    ttFiber36Parent_0_ok,
    ttFiber36Parent_1_ok,
    ttFiber36Parent_2_ok,
    ttFiber36Parent_3_ok,
    ttFiber36Parent_4_ok,
    ttFiber36Parent_5_ok,
    ttFiber36Parent_6_ok,
    ttFiber36Parent_7_ok,
    ttFiber36Parent_8_ok,
    ttFiber36Parent_9_ok,
    ttFiber36Parent_10_ok,
    ttFiber36Parent_11_ok,
    ttFiber36Parent_12_ok,
    ttFiber36Parent_13_ok,
    ttFiber36Parent_14_ok,
    ttFiber36Parent_15_ok,
    ttFiber36Parent_16_ok,
    ttFiber36Parent_17_ok,
    ttFiber36Parent_18_ok,
    ttFiber36Parent_19_ok,
    ttFiber36Parent_20_ok,
    ttFiber36Parent_21_ok,
    ttFiber36Parent_22_ok,
    ttFiber36Parent_23_ok,
    ttFiber36Parent_24_ok,
    ttFiber36Parent_25_ok,
    ttFiber36Parent_26_ok,
    ttFiber36Parent_27_ok,
    ttFiber36Parent_28_ok,
    ttFiber36Parent_29_ok,
    ttFiber36Parent_30_ok,
    ttFiber36Parent_31_ok,
    ttFiber36Parent_32_ok,
    ttFiber36Parent_33_ok,
    ttFiber36Parent_34_ok,
    ttFiber36Parent_35_ok,
    ttFiber36Parent_36_ok,
    ttFiber36Parent_37_ok,
    ttFiber36Parent_38_ok,
    ttFiber36Parent_39_ok,
    ttFiber36Parent_40_ok,
    ttFiber36Parent_41_ok,
    ttFiber36Parent_42_ok,
    ttFiber36Parent_43_ok,
    ttFiber36Parent_44_ok,
    ttFiber36Parent_45_ok,
    ttFiber36Parent_46_ok,
    ttFiber36Parent_47_ok,
    ttFiber36Parent_48_ok,
    ttFiber36Parent_49_ok,
    ttFiber36Parent_50_ok,
    ttFiber36Parent_51_ok,
    ttFiber36Parent_52_ok,
    ttFiber36Parent_53_ok,
    ttFiber36Parent_54_ok,
    ttFiber36Parent_55_ok,
    ttFiber36Parent_56_ok,
    ttFiber36Parent_57_ok,
    ttFiber36Parent_58_ok,
    ttFiber36Parent_59_ok,
    ttFiber36Parent_60_ok,
    ttFiber36Parent_61_ok,
    ttFiber36Parent_62_ok,
    ttFiber36Parent_63_ok]

def ttFiber37Key : List LColor :=
  [LColor.b, LColor.b, LColor.r, LColor.b]

def ttFiber37Expected : List Nat :=
  [312, 313, 314, 315, 316, 317, 318, 319]

def ttFiber37Rows : List DirectChainParentRow :=
  [ directRow 312 312 62 112 62 112 default
  , directRow 313 312 62 113 62 112 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 314 312 62 114 62 112 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 315 313 62 115 62 113 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 316 312 63 120 62 112 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 317 313 63 121 62 113 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 318 314 63 122 62 114 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 319 315 63 123 62 115 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  ]

def ttFiber37RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber37Rows i default

def ttFiber37SourcesCheck : Bool :=
  (ttFiber37Rows.map fun row => row.source) == ttFiber37Expected

theorem ttFiber37SourcesCheck_ok :
    ttFiber37SourcesCheck = true := by
  decide

def ttFiber37RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber37Key ttFiber37Expected (ttFiber37RowAt i)

theorem ttFiber37Row_0_ok : ttFiber37RowCheck 0 = true := by decide
theorem ttFiber37Row_1_ok : ttFiber37RowCheck 1 = true := by decide
theorem ttFiber37Row_2_ok : ttFiber37RowCheck 2 = true := by decide
theorem ttFiber37Row_3_ok : ttFiber37RowCheck 3 = true := by decide
theorem ttFiber37Row_4_ok : ttFiber37RowCheck 4 = true := by decide
theorem ttFiber37Row_5_ok : ttFiber37RowCheck 5 = true := by decide
theorem ttFiber37Row_6_ok : ttFiber37RowCheck 6 = true := by decide
theorem ttFiber37Row_7_ok : ttFiber37RowCheck 7 = true := by decide

def ttFiber37ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber37Rows ttMaxParentDepth (listGetD ttFiber37Expected i 0) == 312

theorem ttFiber37Parent_0_ok : ttFiber37ParentCheck 0 = true := by decide
theorem ttFiber37Parent_1_ok : ttFiber37ParentCheck 1 = true := by decide
theorem ttFiber37Parent_2_ok : ttFiber37ParentCheck 2 = true := by decide
theorem ttFiber37Parent_3_ok : ttFiber37ParentCheck 3 = true := by decide
theorem ttFiber37Parent_4_ok : ttFiber37ParentCheck 4 = true := by decide
theorem ttFiber37Parent_5_ok : ttFiber37ParentCheck 5 = true := by decide
theorem ttFiber37Parent_6_ok : ttFiber37ParentCheck 6 = true := by decide
theorem ttFiber37Parent_7_ok : ttFiber37ParentCheck 7 = true := by decide

def ttFiber37CertificateAudit : Bool :=
  ttFiber37SourcesCheck &&
    ttFiber37RowCheck 0 &&
    ttFiber37RowCheck 1 &&
    ttFiber37RowCheck 2 &&
    ttFiber37RowCheck 3 &&
    ttFiber37RowCheck 4 &&
    ttFiber37RowCheck 5 &&
    ttFiber37RowCheck 6 &&
    ttFiber37RowCheck 7 &&
    ttFiber37ParentCheck 0 &&
    ttFiber37ParentCheck 1 &&
    ttFiber37ParentCheck 2 &&
    ttFiber37ParentCheck 3 &&
    ttFiber37ParentCheck 4 &&
    ttFiber37ParentCheck 5 &&
    ttFiber37ParentCheck 6 &&
    ttFiber37ParentCheck 7

theorem ttFiber37CertificateAudit_ok :
    ttFiber37CertificateAudit = true := by
  simp [ttFiber37CertificateAudit,
    ttFiber37SourcesCheck_ok,
    ttFiber37Row_0_ok,
    ttFiber37Row_1_ok,
    ttFiber37Row_2_ok,
    ttFiber37Row_3_ok,
    ttFiber37Row_4_ok,
    ttFiber37Row_5_ok,
    ttFiber37Row_6_ok,
    ttFiber37Row_7_ok,
    ttFiber37Parent_0_ok,
    ttFiber37Parent_1_ok,
    ttFiber37Parent_2_ok,
    ttFiber37Parent_3_ok,
    ttFiber37Parent_4_ok,
    ttFiber37Parent_5_ok,
    ttFiber37Parent_6_ok,
    ttFiber37Parent_7_ok]

def ttFiber38Key : List LColor :=
  [LColor.b, LColor.b, LColor.r, LColor.p]

def ttFiber38Expected : List Nat :=
  [72, 73, 74, 75, 76, 77, 78, 79]

def ttFiber38Rows : List DirectChainParentRow :=
  [ directRow 72 72 14 176 14 176 default
  , directRow 73 72 14 177 14 176 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 74 72 14 178 14 176 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 75 73 14 179 14 177 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 76 72 15 184 14 176 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 77 73 15 185 14 177 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 78 74 15 186 14 178 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 79 75 15 187 14 179 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  ]

def ttFiber38RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber38Rows i default

def ttFiber38SourcesCheck : Bool :=
  (ttFiber38Rows.map fun row => row.source) == ttFiber38Expected

theorem ttFiber38SourcesCheck_ok :
    ttFiber38SourcesCheck = true := by
  decide

def ttFiber38RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber38Key ttFiber38Expected (ttFiber38RowAt i)

theorem ttFiber38Row_0_ok : ttFiber38RowCheck 0 = true := by decide
theorem ttFiber38Row_1_ok : ttFiber38RowCheck 1 = true := by decide
theorem ttFiber38Row_2_ok : ttFiber38RowCheck 2 = true := by decide
theorem ttFiber38Row_3_ok : ttFiber38RowCheck 3 = true := by decide
theorem ttFiber38Row_4_ok : ttFiber38RowCheck 4 = true := by decide
theorem ttFiber38Row_5_ok : ttFiber38RowCheck 5 = true := by decide
theorem ttFiber38Row_6_ok : ttFiber38RowCheck 6 = true := by decide
theorem ttFiber38Row_7_ok : ttFiber38RowCheck 7 = true := by decide

def ttFiber38ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber38Rows ttMaxParentDepth (listGetD ttFiber38Expected i 0) == 72

theorem ttFiber38Parent_0_ok : ttFiber38ParentCheck 0 = true := by decide
theorem ttFiber38Parent_1_ok : ttFiber38ParentCheck 1 = true := by decide
theorem ttFiber38Parent_2_ok : ttFiber38ParentCheck 2 = true := by decide
theorem ttFiber38Parent_3_ok : ttFiber38ParentCheck 3 = true := by decide
theorem ttFiber38Parent_4_ok : ttFiber38ParentCheck 4 = true := by decide
theorem ttFiber38Parent_5_ok : ttFiber38ParentCheck 5 = true := by decide
theorem ttFiber38Parent_6_ok : ttFiber38ParentCheck 6 = true := by decide
theorem ttFiber38Parent_7_ok : ttFiber38ParentCheck 7 = true := by decide

def ttFiber38CertificateAudit : Bool :=
  ttFiber38SourcesCheck &&
    ttFiber38RowCheck 0 &&
    ttFiber38RowCheck 1 &&
    ttFiber38RowCheck 2 &&
    ttFiber38RowCheck 3 &&
    ttFiber38RowCheck 4 &&
    ttFiber38RowCheck 5 &&
    ttFiber38RowCheck 6 &&
    ttFiber38RowCheck 7 &&
    ttFiber38ParentCheck 0 &&
    ttFiber38ParentCheck 1 &&
    ttFiber38ParentCheck 2 &&
    ttFiber38ParentCheck 3 &&
    ttFiber38ParentCheck 4 &&
    ttFiber38ParentCheck 5 &&
    ttFiber38ParentCheck 6 &&
    ttFiber38ParentCheck 7

theorem ttFiber38CertificateAudit_ok :
    ttFiber38CertificateAudit = true := by
  simp [ttFiber38CertificateAudit,
    ttFiber38SourcesCheck_ok,
    ttFiber38Row_0_ok,
    ttFiber38Row_1_ok,
    ttFiber38Row_2_ok,
    ttFiber38Row_3_ok,
    ttFiber38Row_4_ok,
    ttFiber38Row_5_ok,
    ttFiber38Row_6_ok,
    ttFiber38Row_7_ok,
    ttFiber38Parent_0_ok,
    ttFiber38Parent_1_ok,
    ttFiber38Parent_2_ok,
    ttFiber38Parent_3_ok,
    ttFiber38Parent_4_ok,
    ttFiber38Parent_5_ok,
    ttFiber38Parent_6_ok,
    ttFiber38Parent_7_ok]

def ttFiber39Key : List LColor :=
  [LColor.b, LColor.b, LColor.b, LColor.r]

def ttFiber39Expected : List Nat :=
  []

def ttFiber39Rows : List DirectChainParentRow :=
  []

def ttFiber39RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber39Rows i default

def ttFiber39SourcesCheck : Bool :=
  (ttFiber39Rows.map fun row => row.source) == ttFiber39Expected

theorem ttFiber39SourcesCheck_ok :
    ttFiber39SourcesCheck = true := by
  decide

def ttFiber39RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber39Key ttFiber39Expected (ttFiber39RowAt i)

def ttFiber39ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber39Rows ttMaxParentDepth (listGetD ttFiber39Expected i 0) == 0

def ttFiber39CertificateAudit : Bool :=
  ttFiber39SourcesCheck

theorem ttFiber39CertificateAudit_ok :
    ttFiber39CertificateAudit = true := by
  simp [ttFiber39CertificateAudit,
    ttFiber39SourcesCheck_ok]

def ttFiber40Key : List LColor :=
  [LColor.b, LColor.b, LColor.b, LColor.b]

def ttFiber40Expected : List Nat :=
  []

def ttFiber40Rows : List DirectChainParentRow :=
  []

def ttFiber40RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber40Rows i default

def ttFiber40SourcesCheck : Bool :=
  (ttFiber40Rows.map fun row => row.source) == ttFiber40Expected

theorem ttFiber40SourcesCheck_ok :
    ttFiber40SourcesCheck = true := by
  decide

def ttFiber40RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber40Key ttFiber40Expected (ttFiber40RowAt i)

def ttFiber40ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber40Rows ttMaxParentDepth (listGetD ttFiber40Expected i 0) == 0

def ttFiber40CertificateAudit : Bool :=
  ttFiber40SourcesCheck

theorem ttFiber40CertificateAudit_ok :
    ttFiber40CertificateAudit = true := by
  simp [ttFiber40CertificateAudit,
    ttFiber40SourcesCheck_ok]

def ttFiber41Key : List LColor :=
  [LColor.b, LColor.b, LColor.b, LColor.p]

def ttFiber41Expected : List Nat :=
  []

def ttFiber41Rows : List DirectChainParentRow :=
  []

def ttFiber41RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber41Rows i default

def ttFiber41SourcesCheck : Bool :=
  (ttFiber41Rows.map fun row => row.source) == ttFiber41Expected

theorem ttFiber41SourcesCheck_ok :
    ttFiber41SourcesCheck = true := by
  decide

def ttFiber41RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber41Key ttFiber41Expected (ttFiber41RowAt i)

def ttFiber41ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber41Rows ttMaxParentDepth (listGetD ttFiber41Expected i 0) == 0

def ttFiber41CertificateAudit : Bool :=
  ttFiber41SourcesCheck

theorem ttFiber41CertificateAudit_ok :
    ttFiber41CertificateAudit = true := by
  simp [ttFiber41CertificateAudit,
    ttFiber41SourcesCheck_ok]

def ttFiber42Key : List LColor :=
  [LColor.b, LColor.b, LColor.p, LColor.r]

def ttFiber42Expected : List Nat :=
  [800, 801, 802, 803, 804, 805, 806, 807]

def ttFiber42Rows : List DirectChainParentRow :=
  [ directRow 800 800 160 20 160 20 default
  , directRow 801 800 160 21 160 20 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 802 800 160 22 160 20 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 803 801 160 23 160 21 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 804 800 161 28 160 20 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 805 801 161 29 160 21 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 806 802 161 30 160 22 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 807 803 161 31 160 23 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  ]

def ttFiber42RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber42Rows i default

def ttFiber42SourcesCheck : Bool :=
  (ttFiber42Rows.map fun row => row.source) == ttFiber42Expected

theorem ttFiber42SourcesCheck_ok :
    ttFiber42SourcesCheck = true := by
  decide

def ttFiber42RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber42Key ttFiber42Expected (ttFiber42RowAt i)

theorem ttFiber42Row_0_ok : ttFiber42RowCheck 0 = true := by decide
theorem ttFiber42Row_1_ok : ttFiber42RowCheck 1 = true := by decide
theorem ttFiber42Row_2_ok : ttFiber42RowCheck 2 = true := by decide
theorem ttFiber42Row_3_ok : ttFiber42RowCheck 3 = true := by decide
theorem ttFiber42Row_4_ok : ttFiber42RowCheck 4 = true := by decide
theorem ttFiber42Row_5_ok : ttFiber42RowCheck 5 = true := by decide
theorem ttFiber42Row_6_ok : ttFiber42RowCheck 6 = true := by decide
theorem ttFiber42Row_7_ok : ttFiber42RowCheck 7 = true := by decide

def ttFiber42ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber42Rows ttMaxParentDepth (listGetD ttFiber42Expected i 0) == 800

theorem ttFiber42Parent_0_ok : ttFiber42ParentCheck 0 = true := by decide
theorem ttFiber42Parent_1_ok : ttFiber42ParentCheck 1 = true := by decide
theorem ttFiber42Parent_2_ok : ttFiber42ParentCheck 2 = true := by decide
theorem ttFiber42Parent_3_ok : ttFiber42ParentCheck 3 = true := by decide
theorem ttFiber42Parent_4_ok : ttFiber42ParentCheck 4 = true := by decide
theorem ttFiber42Parent_5_ok : ttFiber42ParentCheck 5 = true := by decide
theorem ttFiber42Parent_6_ok : ttFiber42ParentCheck 6 = true := by decide
theorem ttFiber42Parent_7_ok : ttFiber42ParentCheck 7 = true := by decide

def ttFiber42CertificateAudit : Bool :=
  ttFiber42SourcesCheck &&
    ttFiber42RowCheck 0 &&
    ttFiber42RowCheck 1 &&
    ttFiber42RowCheck 2 &&
    ttFiber42RowCheck 3 &&
    ttFiber42RowCheck 4 &&
    ttFiber42RowCheck 5 &&
    ttFiber42RowCheck 6 &&
    ttFiber42RowCheck 7 &&
    ttFiber42ParentCheck 0 &&
    ttFiber42ParentCheck 1 &&
    ttFiber42ParentCheck 2 &&
    ttFiber42ParentCheck 3 &&
    ttFiber42ParentCheck 4 &&
    ttFiber42ParentCheck 5 &&
    ttFiber42ParentCheck 6 &&
    ttFiber42ParentCheck 7

theorem ttFiber42CertificateAudit_ok :
    ttFiber42CertificateAudit = true := by
  simp [ttFiber42CertificateAudit,
    ttFiber42SourcesCheck_ok,
    ttFiber42Row_0_ok,
    ttFiber42Row_1_ok,
    ttFiber42Row_2_ok,
    ttFiber42Row_3_ok,
    ttFiber42Row_4_ok,
    ttFiber42Row_5_ok,
    ttFiber42Row_6_ok,
    ttFiber42Row_7_ok,
    ttFiber42Parent_0_ok,
    ttFiber42Parent_1_ok,
    ttFiber42Parent_2_ok,
    ttFiber42Parent_3_ok,
    ttFiber42Parent_4_ok,
    ttFiber42Parent_5_ok,
    ttFiber42Parent_6_ok,
    ttFiber42Parent_7_ok]

def ttFiber43Key : List LColor :=
  [LColor.b, LColor.b, LColor.p, LColor.b]

def ttFiber43Expected : List Nat :=
  [720, 721, 722, 723, 724, 725, 726, 727]

def ttFiber43Rows : List DirectChainParentRow :=
  [ directRow 720 720 144 84 144 84 default
  , directRow 721 720 144 85 144 84 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 722 720 144 86 144 84 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 723 721 144 87 144 85 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 724 720 145 92 144 84 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 725 721 145 93 144 85 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 726 722 145 94 144 86 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 727 723 145 95 144 87 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  ]

def ttFiber43RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber43Rows i default

def ttFiber43SourcesCheck : Bool :=
  (ttFiber43Rows.map fun row => row.source) == ttFiber43Expected

theorem ttFiber43SourcesCheck_ok :
    ttFiber43SourcesCheck = true := by
  decide

def ttFiber43RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber43Key ttFiber43Expected (ttFiber43RowAt i)

theorem ttFiber43Row_0_ok : ttFiber43RowCheck 0 = true := by decide
theorem ttFiber43Row_1_ok : ttFiber43RowCheck 1 = true := by decide
theorem ttFiber43Row_2_ok : ttFiber43RowCheck 2 = true := by decide
theorem ttFiber43Row_3_ok : ttFiber43RowCheck 3 = true := by decide
theorem ttFiber43Row_4_ok : ttFiber43RowCheck 4 = true := by decide
theorem ttFiber43Row_5_ok : ttFiber43RowCheck 5 = true := by decide
theorem ttFiber43Row_6_ok : ttFiber43RowCheck 6 = true := by decide
theorem ttFiber43Row_7_ok : ttFiber43RowCheck 7 = true := by decide

def ttFiber43ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber43Rows ttMaxParentDepth (listGetD ttFiber43Expected i 0) == 720

theorem ttFiber43Parent_0_ok : ttFiber43ParentCheck 0 = true := by decide
theorem ttFiber43Parent_1_ok : ttFiber43ParentCheck 1 = true := by decide
theorem ttFiber43Parent_2_ok : ttFiber43ParentCheck 2 = true := by decide
theorem ttFiber43Parent_3_ok : ttFiber43ParentCheck 3 = true := by decide
theorem ttFiber43Parent_4_ok : ttFiber43ParentCheck 4 = true := by decide
theorem ttFiber43Parent_5_ok : ttFiber43ParentCheck 5 = true := by decide
theorem ttFiber43Parent_6_ok : ttFiber43ParentCheck 6 = true := by decide
theorem ttFiber43Parent_7_ok : ttFiber43ParentCheck 7 = true := by decide

def ttFiber43CertificateAudit : Bool :=
  ttFiber43SourcesCheck &&
    ttFiber43RowCheck 0 &&
    ttFiber43RowCheck 1 &&
    ttFiber43RowCheck 2 &&
    ttFiber43RowCheck 3 &&
    ttFiber43RowCheck 4 &&
    ttFiber43RowCheck 5 &&
    ttFiber43RowCheck 6 &&
    ttFiber43RowCheck 7 &&
    ttFiber43ParentCheck 0 &&
    ttFiber43ParentCheck 1 &&
    ttFiber43ParentCheck 2 &&
    ttFiber43ParentCheck 3 &&
    ttFiber43ParentCheck 4 &&
    ttFiber43ParentCheck 5 &&
    ttFiber43ParentCheck 6 &&
    ttFiber43ParentCheck 7

theorem ttFiber43CertificateAudit_ok :
    ttFiber43CertificateAudit = true := by
  simp [ttFiber43CertificateAudit,
    ttFiber43SourcesCheck_ok,
    ttFiber43Row_0_ok,
    ttFiber43Row_1_ok,
    ttFiber43Row_2_ok,
    ttFiber43Row_3_ok,
    ttFiber43Row_4_ok,
    ttFiber43Row_5_ok,
    ttFiber43Row_6_ok,
    ttFiber43Row_7_ok,
    ttFiber43Parent_0_ok,
    ttFiber43Parent_1_ok,
    ttFiber43Parent_2_ok,
    ttFiber43Parent_3_ok,
    ttFiber43Parent_4_ok,
    ttFiber43Parent_5_ok,
    ttFiber43Parent_6_ok,
    ttFiber43Parent_7_ok]

def ttFiber44Key : List LColor :=
  [LColor.b, LColor.b, LColor.p, LColor.p]

def ttFiber44Expected : List Nat :=
  [728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 808, 809, 810, 811, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839]

def ttFiber44Rows : List DirectChainParentRow :=
  [ directRow 728 728 148 148 148 148 default
  , directRow 729 728 148 149 148 148 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 730 729 148 150 148 149 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 731 728 148 151 148 148 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 732 728 148 164 148 148 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 733 729 148 165 148 149 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 734 732 148 166 148 164 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 735 731 148 167 148 151 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 736 728 149 156 148 148 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 737 729 149 157 148 149 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 738 730 149 158 148 150 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 739 731 149 159 148 151 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 740 732 149 172 148 164 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 741 733 149 173 148 165 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 742 734 149 174 148 166 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 743 735 149 175 148 167 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 744 748 150 0 150 48 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 745 749 150 1 150 49 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 746 740 150 2 149 172 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 747 741 150 3 149 173 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 748 736 150 48 149 156 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 749 737 150 49 149 157 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 750 738 150 50 149 158 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 751 739 150 51 149 159 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 752 756 151 8 151 56 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 753 757 151 9 151 57 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 754 732 151 10 148 164 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 755 733 151 11 148 165 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 756 728 151 56 148 148 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 757 729 151 57 148 149 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 758 730 151 58 148 150 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 759 731 151 59 148 151 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 808 728 164 132 148 148 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 809 729 164 133 148 149 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 810 730 164 134 148 150 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 811 731 164 135 148 151 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 812 732 164 180 148 164 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 813 733 164 181 148 165 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 814 734 164 182 148 166 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 815 735 164 183 148 167 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 816 736 165 140 149 156 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 817 737 165 141 149 157 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 818 738 165 142 149 158 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 819 739 165 143 149 159 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 820 740 165 188 149 172 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 821 741 165 189 149 173 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 822 742 165 190 149 174 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 823 743 165 191 149 175 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 824 808 166 64 164 132 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 825 809 166 65 164 133 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 826 824 166 66 166 64 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 827 811 166 67 164 135 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 828 812 166 116 164 180 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 829 813 166 117 164 181 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 830 825 166 118 166 65 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 831 824 166 119 166 64 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 832 816 167 72 165 140 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 833 817 167 73 165 141 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 834 754 167 74 151 10 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 835 755 167 75 151 11 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 836 756 167 124 151 56 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 837 757 167 125 151 57 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 838 836 167 126 167 124 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 839 759 167 127 151 59 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  ]

def ttFiber44RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber44Rows i default

def ttFiber44SourcesCheck : Bool :=
  (ttFiber44Rows.map fun row => row.source) == ttFiber44Expected

theorem ttFiber44SourcesCheck_ok :
    ttFiber44SourcesCheck = true := by
  decide

def ttFiber44RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt i)

theorem ttFiber44Row_0_ok : ttFiber44RowCheck 0 = true := by decide
theorem ttFiber44Row_1_ok : ttFiber44RowCheck 1 = true := by decide
theorem ttFiber44Row_2_ok : ttFiber44RowCheck 2 = true := by decide
theorem ttFiber44Row_3_ok : ttFiber44RowCheck 3 = true := by decide
theorem ttFiber44Row_4_ok : ttFiber44RowCheck 4 = true := by decide
theorem ttFiber44Row_5_ok : ttFiber44RowCheck 5 = true := by decide
theorem ttFiber44Row_6_ok : ttFiber44RowCheck 6 = true := by decide
theorem ttFiber44Row_7_ok : ttFiber44RowCheck 7 = true := by decide
theorem ttFiber44Row_8_ok : ttFiber44RowCheck 8 = true := by decide
theorem ttFiber44Row_9_ok : ttFiber44RowCheck 9 = true := by decide
theorem ttFiber44Row_10_ok : ttFiber44RowCheck 10 = true := by decide
theorem ttFiber44Row_11_ok : ttFiber44RowCheck 11 = true := by decide
theorem ttFiber44Row_12_ok : ttFiber44RowCheck 12 = true := by decide
theorem ttFiber44Row_13_ok : ttFiber44RowCheck 13 = true := by decide
theorem ttFiber44Row_14_ok : ttFiber44RowCheck 14 = true := by decide
theorem ttFiber44Row_15_ok : ttFiber44RowCheck 15 = true := by decide
theorem ttFiber44Row_16_ok : ttFiber44RowCheck 16 = true := by decide
theorem ttFiber44Row_17_ok : ttFiber44RowCheck 17 = true := by decide
theorem ttFiber44Row_18_ok : ttFiber44RowCheck 18 = true := by decide
theorem ttFiber44Row_19_ok : ttFiber44RowCheck 19 = true := by decide
theorem ttFiber44Row_20_ok : ttFiber44RowCheck 20 = true := by decide
theorem ttFiber44Row_21_ok : ttFiber44RowCheck 21 = true := by decide
theorem ttFiber44Row_22_ok : ttFiber44RowCheck 22 = true := by decide
theorem ttFiber44Row_23_ok : ttFiber44RowCheck 23 = true := by decide
theorem ttFiber44Row_24_ok : ttFiber44RowCheck 24 = true := by decide
theorem ttFiber44Row_25_ok : ttFiber44RowCheck 25 = true := by decide
theorem ttFiber44Row_26_ok : ttFiber44RowCheck 26 = true := by decide
theorem ttFiber44Row_27_ok : ttFiber44RowCheck 27 = true := by decide
theorem ttFiber44Row_28_ok : ttFiber44RowCheck 28 = true := by decide
theorem ttFiber44Row_29_ok : ttFiber44RowCheck 29 = true := by decide
theorem ttFiber44Row_30_ok : ttFiber44RowCheck 30 = true := by decide
theorem ttFiber44Row_31_ok : ttFiber44RowCheck 31 = true := by decide
theorem ttFiber44Row_32_ok : ttFiber44RowCheck 32 = true := by decide
theorem ttFiber44Row_33_ok : ttFiber44RowCheck 33 = true := by decide
theorem ttFiber44Row_34_ok : ttFiber44RowCheck 34 = true := by decide
theorem ttFiber44Row_35_ok : ttFiber44RowCheck 35 = true := by decide
theorem ttFiber44Row_36_ok : ttFiber44RowCheck 36 = true := by decide
theorem ttFiber44Row_37_ok : ttFiber44RowCheck 37 = true := by decide
theorem ttFiber44Row_38_ok : ttFiber44RowCheck 38 = true := by decide
theorem ttFiber44Row_39_ok : ttFiber44RowCheck 39 = true := by decide
theorem ttFiber44Row_40_ok : ttFiber44RowCheck 40 = true := by decide
theorem ttFiber44Row_41_ok : ttFiber44RowCheck 41 = true := by decide
theorem ttFiber44Row_42_ok : ttFiber44RowCheck 42 = true := by decide
theorem ttFiber44Row_43_ok : ttFiber44RowCheck 43 = true := by decide
theorem ttFiber44Row_44_ok : ttFiber44RowCheck 44 = true := by decide
theorem ttFiber44Row_45_ok : ttFiber44RowCheck 45 = true := by decide
theorem ttFiber44Row_46_ok : ttFiber44RowCheck 46 = true := by decide
theorem ttFiber44Row_47_ok : ttFiber44RowCheck 47 = true := by decide
theorem ttFiber44Row_48_ok : ttFiber44RowCheck 48 = true := by decide
theorem ttFiber44Row_49_ok : ttFiber44RowCheck 49 = true := by decide
theorem ttFiber44Row_50_ok : ttFiber44RowCheck 50 = true := by decide
theorem ttFiber44Row_51_ok : ttFiber44RowCheck 51 = true := by decide
theorem ttFiber44Row_52_ok : ttFiber44RowCheck 52 = true := by decide
theorem ttFiber44Row_53_ok : ttFiber44RowCheck 53 = true := by decide
theorem ttFiber44Row_54_ok : ttFiber44RowCheck 54 = true := by decide
theorem ttFiber44Row_55_ok : ttFiber44RowCheck 55 = true := by decide
theorem ttFiber44Row_56_ok : ttFiber44RowCheck 56 = true := by decide
theorem ttFiber44Row_57_ok : ttFiber44RowCheck 57 = true := by decide
theorem ttFiber44Row_58_ok : ttFiber44RowCheck 58 = true := by decide
theorem ttFiber44Row_59_ok : ttFiber44RowCheck 59 = true := by decide
theorem ttFiber44Row_60_ok : ttFiber44RowCheck 60 = true := by decide
theorem ttFiber44Row_61_ok : ttFiber44RowCheck 61 = true := by decide
theorem ttFiber44Row_62_ok : ttFiber44RowCheck 62 = true := by decide
theorem ttFiber44Row_63_ok : ttFiber44RowCheck 63 = true := by decide

def ttFiber44ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber44Rows ttMaxParentDepth (listGetD ttFiber44Expected i 0) == 728

theorem ttFiber44Parent_0_ok : ttFiber44ParentCheck 0 = true := by decide
theorem ttFiber44Parent_1_ok : ttFiber44ParentCheck 1 = true := by decide
theorem ttFiber44Parent_2_ok : ttFiber44ParentCheck 2 = true := by decide
theorem ttFiber44Parent_3_ok : ttFiber44ParentCheck 3 = true := by decide
theorem ttFiber44Parent_4_ok : ttFiber44ParentCheck 4 = true := by decide
theorem ttFiber44Parent_5_ok : ttFiber44ParentCheck 5 = true := by decide
theorem ttFiber44Parent_6_ok : ttFiber44ParentCheck 6 = true := by decide
theorem ttFiber44Parent_7_ok : ttFiber44ParentCheck 7 = true := by decide
theorem ttFiber44Parent_8_ok : ttFiber44ParentCheck 8 = true := by decide
theorem ttFiber44Parent_9_ok : ttFiber44ParentCheck 9 = true := by decide
theorem ttFiber44Parent_10_ok : ttFiber44ParentCheck 10 = true := by decide
theorem ttFiber44Parent_11_ok : ttFiber44ParentCheck 11 = true := by decide
theorem ttFiber44Parent_12_ok : ttFiber44ParentCheck 12 = true := by decide
theorem ttFiber44Parent_13_ok : ttFiber44ParentCheck 13 = true := by decide
theorem ttFiber44Parent_14_ok : ttFiber44ParentCheck 14 = true := by decide
theorem ttFiber44Parent_15_ok : ttFiber44ParentCheck 15 = true := by decide
theorem ttFiber44Parent_16_ok : ttFiber44ParentCheck 16 = true := by decide
theorem ttFiber44Parent_17_ok : ttFiber44ParentCheck 17 = true := by decide
theorem ttFiber44Parent_18_ok : ttFiber44ParentCheck 18 = true := by decide
theorem ttFiber44Parent_19_ok : ttFiber44ParentCheck 19 = true := by decide
theorem ttFiber44Parent_20_ok : ttFiber44ParentCheck 20 = true := by decide
theorem ttFiber44Parent_21_ok : ttFiber44ParentCheck 21 = true := by decide
theorem ttFiber44Parent_22_ok : ttFiber44ParentCheck 22 = true := by decide
theorem ttFiber44Parent_23_ok : ttFiber44ParentCheck 23 = true := by decide
theorem ttFiber44Parent_24_ok : ttFiber44ParentCheck 24 = true := by decide
theorem ttFiber44Parent_25_ok : ttFiber44ParentCheck 25 = true := by decide
theorem ttFiber44Parent_26_ok : ttFiber44ParentCheck 26 = true := by decide
theorem ttFiber44Parent_27_ok : ttFiber44ParentCheck 27 = true := by decide
theorem ttFiber44Parent_28_ok : ttFiber44ParentCheck 28 = true := by decide
theorem ttFiber44Parent_29_ok : ttFiber44ParentCheck 29 = true := by decide
theorem ttFiber44Parent_30_ok : ttFiber44ParentCheck 30 = true := by decide
theorem ttFiber44Parent_31_ok : ttFiber44ParentCheck 31 = true := by decide
theorem ttFiber44Parent_32_ok : ttFiber44ParentCheck 32 = true := by decide
theorem ttFiber44Parent_33_ok : ttFiber44ParentCheck 33 = true := by decide
theorem ttFiber44Parent_34_ok : ttFiber44ParentCheck 34 = true := by decide
theorem ttFiber44Parent_35_ok : ttFiber44ParentCheck 35 = true := by decide
theorem ttFiber44Parent_36_ok : ttFiber44ParentCheck 36 = true := by decide
theorem ttFiber44Parent_37_ok : ttFiber44ParentCheck 37 = true := by decide
theorem ttFiber44Parent_38_ok : ttFiber44ParentCheck 38 = true := by decide
theorem ttFiber44Parent_39_ok : ttFiber44ParentCheck 39 = true := by decide
theorem ttFiber44Parent_40_ok : ttFiber44ParentCheck 40 = true := by decide
theorem ttFiber44Parent_41_ok : ttFiber44ParentCheck 41 = true := by decide
theorem ttFiber44Parent_42_ok : ttFiber44ParentCheck 42 = true := by decide
theorem ttFiber44Parent_43_ok : ttFiber44ParentCheck 43 = true := by decide
theorem ttFiber44Parent_44_ok : ttFiber44ParentCheck 44 = true := by decide
theorem ttFiber44Parent_45_ok : ttFiber44ParentCheck 45 = true := by decide
theorem ttFiber44Parent_46_ok : ttFiber44ParentCheck 46 = true := by decide
theorem ttFiber44Parent_47_ok : ttFiber44ParentCheck 47 = true := by decide
theorem ttFiber44Parent_48_ok : ttFiber44ParentCheck 48 = true := by decide
theorem ttFiber44Parent_49_ok : ttFiber44ParentCheck 49 = true := by decide
theorem ttFiber44Parent_50_ok : ttFiber44ParentCheck 50 = true := by decide
theorem ttFiber44Parent_51_ok : ttFiber44ParentCheck 51 = true := by decide
theorem ttFiber44Parent_52_ok : ttFiber44ParentCheck 52 = true := by decide
theorem ttFiber44Parent_53_ok : ttFiber44ParentCheck 53 = true := by decide
theorem ttFiber44Parent_54_ok : ttFiber44ParentCheck 54 = true := by decide
theorem ttFiber44Parent_55_ok : ttFiber44ParentCheck 55 = true := by decide
theorem ttFiber44Parent_56_ok : ttFiber44ParentCheck 56 = true := by decide
theorem ttFiber44Parent_57_ok : ttFiber44ParentCheck 57 = true := by decide
theorem ttFiber44Parent_58_ok : ttFiber44ParentCheck 58 = true := by decide
theorem ttFiber44Parent_59_ok : ttFiber44ParentCheck 59 = true := by decide
theorem ttFiber44Parent_60_ok : ttFiber44ParentCheck 60 = true := by decide
theorem ttFiber44Parent_61_ok : ttFiber44ParentCheck 61 = true := by decide
theorem ttFiber44Parent_62_ok : ttFiber44ParentCheck 62 = true := by decide
theorem ttFiber44Parent_63_ok : ttFiber44ParentCheck 63 = true := by decide

def ttFiber44CertificateAudit : Bool :=
  ttFiber44SourcesCheck &&
    ttFiber44RowCheck 0 &&
    ttFiber44RowCheck 1 &&
    ttFiber44RowCheck 2 &&
    ttFiber44RowCheck 3 &&
    ttFiber44RowCheck 4 &&
    ttFiber44RowCheck 5 &&
    ttFiber44RowCheck 6 &&
    ttFiber44RowCheck 7 &&
    ttFiber44RowCheck 8 &&
    ttFiber44RowCheck 9 &&
    ttFiber44RowCheck 10 &&
    ttFiber44RowCheck 11 &&
    ttFiber44RowCheck 12 &&
    ttFiber44RowCheck 13 &&
    ttFiber44RowCheck 14 &&
    ttFiber44RowCheck 15 &&
    ttFiber44RowCheck 16 &&
    ttFiber44RowCheck 17 &&
    ttFiber44RowCheck 18 &&
    ttFiber44RowCheck 19 &&
    ttFiber44RowCheck 20 &&
    ttFiber44RowCheck 21 &&
    ttFiber44RowCheck 22 &&
    ttFiber44RowCheck 23 &&
    ttFiber44RowCheck 24 &&
    ttFiber44RowCheck 25 &&
    ttFiber44RowCheck 26 &&
    ttFiber44RowCheck 27 &&
    ttFiber44RowCheck 28 &&
    ttFiber44RowCheck 29 &&
    ttFiber44RowCheck 30 &&
    ttFiber44RowCheck 31 &&
    ttFiber44RowCheck 32 &&
    ttFiber44RowCheck 33 &&
    ttFiber44RowCheck 34 &&
    ttFiber44RowCheck 35 &&
    ttFiber44RowCheck 36 &&
    ttFiber44RowCheck 37 &&
    ttFiber44RowCheck 38 &&
    ttFiber44RowCheck 39 &&
    ttFiber44RowCheck 40 &&
    ttFiber44RowCheck 41 &&
    ttFiber44RowCheck 42 &&
    ttFiber44RowCheck 43 &&
    ttFiber44RowCheck 44 &&
    ttFiber44RowCheck 45 &&
    ttFiber44RowCheck 46 &&
    ttFiber44RowCheck 47 &&
    ttFiber44RowCheck 48 &&
    ttFiber44RowCheck 49 &&
    ttFiber44RowCheck 50 &&
    ttFiber44RowCheck 51 &&
    ttFiber44RowCheck 52 &&
    ttFiber44RowCheck 53 &&
    ttFiber44RowCheck 54 &&
    ttFiber44RowCheck 55 &&
    ttFiber44RowCheck 56 &&
    ttFiber44RowCheck 57 &&
    ttFiber44RowCheck 58 &&
    ttFiber44RowCheck 59 &&
    ttFiber44RowCheck 60 &&
    ttFiber44RowCheck 61 &&
    ttFiber44RowCheck 62 &&
    ttFiber44RowCheck 63 &&
    ttFiber44ParentCheck 0 &&
    ttFiber44ParentCheck 1 &&
    ttFiber44ParentCheck 2 &&
    ttFiber44ParentCheck 3 &&
    ttFiber44ParentCheck 4 &&
    ttFiber44ParentCheck 5 &&
    ttFiber44ParentCheck 6 &&
    ttFiber44ParentCheck 7 &&
    ttFiber44ParentCheck 8 &&
    ttFiber44ParentCheck 9 &&
    ttFiber44ParentCheck 10 &&
    ttFiber44ParentCheck 11 &&
    ttFiber44ParentCheck 12 &&
    ttFiber44ParentCheck 13 &&
    ttFiber44ParentCheck 14 &&
    ttFiber44ParentCheck 15 &&
    ttFiber44ParentCheck 16 &&
    ttFiber44ParentCheck 17 &&
    ttFiber44ParentCheck 18 &&
    ttFiber44ParentCheck 19 &&
    ttFiber44ParentCheck 20 &&
    ttFiber44ParentCheck 21 &&
    ttFiber44ParentCheck 22 &&
    ttFiber44ParentCheck 23 &&
    ttFiber44ParentCheck 24 &&
    ttFiber44ParentCheck 25 &&
    ttFiber44ParentCheck 26 &&
    ttFiber44ParentCheck 27 &&
    ttFiber44ParentCheck 28 &&
    ttFiber44ParentCheck 29 &&
    ttFiber44ParentCheck 30 &&
    ttFiber44ParentCheck 31 &&
    ttFiber44ParentCheck 32 &&
    ttFiber44ParentCheck 33 &&
    ttFiber44ParentCheck 34 &&
    ttFiber44ParentCheck 35 &&
    ttFiber44ParentCheck 36 &&
    ttFiber44ParentCheck 37 &&
    ttFiber44ParentCheck 38 &&
    ttFiber44ParentCheck 39 &&
    ttFiber44ParentCheck 40 &&
    ttFiber44ParentCheck 41 &&
    ttFiber44ParentCheck 42 &&
    ttFiber44ParentCheck 43 &&
    ttFiber44ParentCheck 44 &&
    ttFiber44ParentCheck 45 &&
    ttFiber44ParentCheck 46 &&
    ttFiber44ParentCheck 47 &&
    ttFiber44ParentCheck 48 &&
    ttFiber44ParentCheck 49 &&
    ttFiber44ParentCheck 50 &&
    ttFiber44ParentCheck 51 &&
    ttFiber44ParentCheck 52 &&
    ttFiber44ParentCheck 53 &&
    ttFiber44ParentCheck 54 &&
    ttFiber44ParentCheck 55 &&
    ttFiber44ParentCheck 56 &&
    ttFiber44ParentCheck 57 &&
    ttFiber44ParentCheck 58 &&
    ttFiber44ParentCheck 59 &&
    ttFiber44ParentCheck 60 &&
    ttFiber44ParentCheck 61 &&
    ttFiber44ParentCheck 62 &&
    ttFiber44ParentCheck 63

theorem ttFiber44CertificateAudit_ok :
    ttFiber44CertificateAudit = true := by
  simp [ttFiber44CertificateAudit,
    ttFiber44SourcesCheck_ok,
    ttFiber44Row_0_ok,
    ttFiber44Row_1_ok,
    ttFiber44Row_2_ok,
    ttFiber44Row_3_ok,
    ttFiber44Row_4_ok,
    ttFiber44Row_5_ok,
    ttFiber44Row_6_ok,
    ttFiber44Row_7_ok,
    ttFiber44Row_8_ok,
    ttFiber44Row_9_ok,
    ttFiber44Row_10_ok,
    ttFiber44Row_11_ok,
    ttFiber44Row_12_ok,
    ttFiber44Row_13_ok,
    ttFiber44Row_14_ok,
    ttFiber44Row_15_ok,
    ttFiber44Row_16_ok,
    ttFiber44Row_17_ok,
    ttFiber44Row_18_ok,
    ttFiber44Row_19_ok,
    ttFiber44Row_20_ok,
    ttFiber44Row_21_ok,
    ttFiber44Row_22_ok,
    ttFiber44Row_23_ok,
    ttFiber44Row_24_ok,
    ttFiber44Row_25_ok,
    ttFiber44Row_26_ok,
    ttFiber44Row_27_ok,
    ttFiber44Row_28_ok,
    ttFiber44Row_29_ok,
    ttFiber44Row_30_ok,
    ttFiber44Row_31_ok,
    ttFiber44Row_32_ok,
    ttFiber44Row_33_ok,
    ttFiber44Row_34_ok,
    ttFiber44Row_35_ok,
    ttFiber44Row_36_ok,
    ttFiber44Row_37_ok,
    ttFiber44Row_38_ok,
    ttFiber44Row_39_ok,
    ttFiber44Row_40_ok,
    ttFiber44Row_41_ok,
    ttFiber44Row_42_ok,
    ttFiber44Row_43_ok,
    ttFiber44Row_44_ok,
    ttFiber44Row_45_ok,
    ttFiber44Row_46_ok,
    ttFiber44Row_47_ok,
    ttFiber44Row_48_ok,
    ttFiber44Row_49_ok,
    ttFiber44Row_50_ok,
    ttFiber44Row_51_ok,
    ttFiber44Row_52_ok,
    ttFiber44Row_53_ok,
    ttFiber44Row_54_ok,
    ttFiber44Row_55_ok,
    ttFiber44Row_56_ok,
    ttFiber44Row_57_ok,
    ttFiber44Row_58_ok,
    ttFiber44Row_59_ok,
    ttFiber44Row_60_ok,
    ttFiber44Row_61_ok,
    ttFiber44Row_62_ok,
    ttFiber44Row_63_ok,
    ttFiber44Parent_0_ok,
    ttFiber44Parent_1_ok,
    ttFiber44Parent_2_ok,
    ttFiber44Parent_3_ok,
    ttFiber44Parent_4_ok,
    ttFiber44Parent_5_ok,
    ttFiber44Parent_6_ok,
    ttFiber44Parent_7_ok,
    ttFiber44Parent_8_ok,
    ttFiber44Parent_9_ok,
    ttFiber44Parent_10_ok,
    ttFiber44Parent_11_ok,
    ttFiber44Parent_12_ok,
    ttFiber44Parent_13_ok,
    ttFiber44Parent_14_ok,
    ttFiber44Parent_15_ok,
    ttFiber44Parent_16_ok,
    ttFiber44Parent_17_ok,
    ttFiber44Parent_18_ok,
    ttFiber44Parent_19_ok,
    ttFiber44Parent_20_ok,
    ttFiber44Parent_21_ok,
    ttFiber44Parent_22_ok,
    ttFiber44Parent_23_ok,
    ttFiber44Parent_24_ok,
    ttFiber44Parent_25_ok,
    ttFiber44Parent_26_ok,
    ttFiber44Parent_27_ok,
    ttFiber44Parent_28_ok,
    ttFiber44Parent_29_ok,
    ttFiber44Parent_30_ok,
    ttFiber44Parent_31_ok,
    ttFiber44Parent_32_ok,
    ttFiber44Parent_33_ok,
    ttFiber44Parent_34_ok,
    ttFiber44Parent_35_ok,
    ttFiber44Parent_36_ok,
    ttFiber44Parent_37_ok,
    ttFiber44Parent_38_ok,
    ttFiber44Parent_39_ok,
    ttFiber44Parent_40_ok,
    ttFiber44Parent_41_ok,
    ttFiber44Parent_42_ok,
    ttFiber44Parent_43_ok,
    ttFiber44Parent_44_ok,
    ttFiber44Parent_45_ok,
    ttFiber44Parent_46_ok,
    ttFiber44Parent_47_ok,
    ttFiber44Parent_48_ok,
    ttFiber44Parent_49_ok,
    ttFiber44Parent_50_ok,
    ttFiber44Parent_51_ok,
    ttFiber44Parent_52_ok,
    ttFiber44Parent_53_ok,
    ttFiber44Parent_54_ok,
    ttFiber44Parent_55_ok,
    ttFiber44Parent_56_ok,
    ttFiber44Parent_57_ok,
    ttFiber44Parent_58_ok,
    ttFiber44Parent_59_ok,
    ttFiber44Parent_60_ok,
    ttFiber44Parent_61_ok,
    ttFiber44Parent_62_ok,
    ttFiber44Parent_63_ok]

def ttFiber45Key : List LColor :=
  [LColor.b, LColor.p, LColor.r, LColor.r]

def ttFiber45Expected : List Nat :=
  []

def ttFiber45Rows : List DirectChainParentRow :=
  []

def ttFiber45RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber45Rows i default

def ttFiber45SourcesCheck : Bool :=
  (ttFiber45Rows.map fun row => row.source) == ttFiber45Expected

theorem ttFiber45SourcesCheck_ok :
    ttFiber45SourcesCheck = true := by
  decide

def ttFiber45RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber45Key ttFiber45Expected (ttFiber45RowAt i)

def ttFiber45ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber45Rows ttMaxParentDepth (listGetD ttFiber45Expected i 0) == 0

def ttFiber45CertificateAudit : Bool :=
  ttFiber45SourcesCheck

theorem ttFiber45CertificateAudit_ok :
    ttFiber45CertificateAudit = true := by
  simp [ttFiber45CertificateAudit,
    ttFiber45SourcesCheck_ok]

def ttFiber46Key : List LColor :=
  [LColor.b, LColor.p, LColor.r, LColor.b]

def ttFiber46Expected : List Nat :=
  []

def ttFiber46Rows : List DirectChainParentRow :=
  []

def ttFiber46RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber46Rows i default

def ttFiber46SourcesCheck : Bool :=
  (ttFiber46Rows.map fun row => row.source) == ttFiber46Expected

theorem ttFiber46SourcesCheck_ok :
    ttFiber46SourcesCheck = true := by
  decide

def ttFiber46RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber46Key ttFiber46Expected (ttFiber46RowAt i)

def ttFiber46ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber46Rows ttMaxParentDepth (listGetD ttFiber46Expected i 0) == 0

def ttFiber46CertificateAudit : Bool :=
  ttFiber46SourcesCheck

theorem ttFiber46CertificateAudit_ok :
    ttFiber46CertificateAudit = true := by
  simp [ttFiber46CertificateAudit,
    ttFiber46SourcesCheck_ok]

def ttFiber47Key : List LColor :=
  [LColor.b, LColor.p, LColor.r, LColor.p]

def ttFiber47Expected : List Nat :=
  []

def ttFiber47Rows : List DirectChainParentRow :=
  []

def ttFiber47RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber47Rows i default

def ttFiber47SourcesCheck : Bool :=
  (ttFiber47Rows.map fun row => row.source) == ttFiber47Expected

theorem ttFiber47SourcesCheck_ok :
    ttFiber47SourcesCheck = true := by
  decide

def ttFiber47RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber47Key ttFiber47Expected (ttFiber47RowAt i)

def ttFiber47ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber47Rows ttMaxParentDepth (listGetD ttFiber47Expected i 0) == 0

def ttFiber47CertificateAudit : Bool :=
  ttFiber47SourcesCheck

theorem ttFiber47CertificateAudit_ok :
    ttFiber47CertificateAudit = true := by
  simp [ttFiber47CertificateAudit,
    ttFiber47SourcesCheck_ok]

def ttFiber48Key : List LColor :=
  [LColor.b, LColor.p, LColor.b, LColor.r]

def ttFiber48Expected : List Nat :=
  [840, 841, 842, 843, 844, 845, 846, 847]

def ttFiber48Rows : List DirectChainParentRow :=
  [ directRow 840 840 168 20 168 20 default
  , directRow 841 840 168 21 168 20 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 842 840 168 22 168 20 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 843 841 168 23 168 21 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 844 840 169 28 168 20 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 845 841 169 29 168 21 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 846 842 169 30 168 22 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 847 843 169 31 168 23 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  ]

def ttFiber48RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber48Rows i default

def ttFiber48SourcesCheck : Bool :=
  (ttFiber48Rows.map fun row => row.source) == ttFiber48Expected

theorem ttFiber48SourcesCheck_ok :
    ttFiber48SourcesCheck = true := by
  decide

def ttFiber48RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber48Key ttFiber48Expected (ttFiber48RowAt i)

theorem ttFiber48Row_0_ok : ttFiber48RowCheck 0 = true := by decide
theorem ttFiber48Row_1_ok : ttFiber48RowCheck 1 = true := by decide
theorem ttFiber48Row_2_ok : ttFiber48RowCheck 2 = true := by decide
theorem ttFiber48Row_3_ok : ttFiber48RowCheck 3 = true := by decide
theorem ttFiber48Row_4_ok : ttFiber48RowCheck 4 = true := by decide
theorem ttFiber48Row_5_ok : ttFiber48RowCheck 5 = true := by decide
theorem ttFiber48Row_6_ok : ttFiber48RowCheck 6 = true := by decide
theorem ttFiber48Row_7_ok : ttFiber48RowCheck 7 = true := by decide

def ttFiber48ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber48Rows ttMaxParentDepth (listGetD ttFiber48Expected i 0) == 840

theorem ttFiber48Parent_0_ok : ttFiber48ParentCheck 0 = true := by decide
theorem ttFiber48Parent_1_ok : ttFiber48ParentCheck 1 = true := by decide
theorem ttFiber48Parent_2_ok : ttFiber48ParentCheck 2 = true := by decide
theorem ttFiber48Parent_3_ok : ttFiber48ParentCheck 3 = true := by decide
theorem ttFiber48Parent_4_ok : ttFiber48ParentCheck 4 = true := by decide
theorem ttFiber48Parent_5_ok : ttFiber48ParentCheck 5 = true := by decide
theorem ttFiber48Parent_6_ok : ttFiber48ParentCheck 6 = true := by decide
theorem ttFiber48Parent_7_ok : ttFiber48ParentCheck 7 = true := by decide

def ttFiber48CertificateAudit : Bool :=
  ttFiber48SourcesCheck &&
    ttFiber48RowCheck 0 &&
    ttFiber48RowCheck 1 &&
    ttFiber48RowCheck 2 &&
    ttFiber48RowCheck 3 &&
    ttFiber48RowCheck 4 &&
    ttFiber48RowCheck 5 &&
    ttFiber48RowCheck 6 &&
    ttFiber48RowCheck 7 &&
    ttFiber48ParentCheck 0 &&
    ttFiber48ParentCheck 1 &&
    ttFiber48ParentCheck 2 &&
    ttFiber48ParentCheck 3 &&
    ttFiber48ParentCheck 4 &&
    ttFiber48ParentCheck 5 &&
    ttFiber48ParentCheck 6 &&
    ttFiber48ParentCheck 7

theorem ttFiber48CertificateAudit_ok :
    ttFiber48CertificateAudit = true := by
  simp [ttFiber48CertificateAudit,
    ttFiber48SourcesCheck_ok,
    ttFiber48Row_0_ok,
    ttFiber48Row_1_ok,
    ttFiber48Row_2_ok,
    ttFiber48Row_3_ok,
    ttFiber48Row_4_ok,
    ttFiber48Row_5_ok,
    ttFiber48Row_6_ok,
    ttFiber48Row_7_ok,
    ttFiber48Parent_0_ok,
    ttFiber48Parent_1_ok,
    ttFiber48Parent_2_ok,
    ttFiber48Parent_3_ok,
    ttFiber48Parent_4_ok,
    ttFiber48Parent_5_ok,
    ttFiber48Parent_6_ok,
    ttFiber48Parent_7_ok]

def ttFiber49Key : List LColor :=
  [LColor.b, LColor.p, LColor.b, LColor.b]

def ttFiber49Expected : List Nat :=
  [760, 761, 762, 763, 764, 765, 766, 767]

def ttFiber49Rows : List DirectChainParentRow :=
  [ directRow 760 760 152 84 152 84 default
  , directRow 761 760 152 85 152 84 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 762 760 152 86 152 84 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 763 761 152 87 152 85 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 764 760 153 92 152 84 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 765 761 153 93 152 85 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 766 762 153 94 152 86 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 767 763 153 95 152 87 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  ]

def ttFiber49RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber49Rows i default

def ttFiber49SourcesCheck : Bool :=
  (ttFiber49Rows.map fun row => row.source) == ttFiber49Expected

theorem ttFiber49SourcesCheck_ok :
    ttFiber49SourcesCheck = true := by
  decide

def ttFiber49RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber49Key ttFiber49Expected (ttFiber49RowAt i)

theorem ttFiber49Row_0_ok : ttFiber49RowCheck 0 = true := by decide
theorem ttFiber49Row_1_ok : ttFiber49RowCheck 1 = true := by decide
theorem ttFiber49Row_2_ok : ttFiber49RowCheck 2 = true := by decide
theorem ttFiber49Row_3_ok : ttFiber49RowCheck 3 = true := by decide
theorem ttFiber49Row_4_ok : ttFiber49RowCheck 4 = true := by decide
theorem ttFiber49Row_5_ok : ttFiber49RowCheck 5 = true := by decide
theorem ttFiber49Row_6_ok : ttFiber49RowCheck 6 = true := by decide
theorem ttFiber49Row_7_ok : ttFiber49RowCheck 7 = true := by decide

def ttFiber49ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber49Rows ttMaxParentDepth (listGetD ttFiber49Expected i 0) == 760

theorem ttFiber49Parent_0_ok : ttFiber49ParentCheck 0 = true := by decide
theorem ttFiber49Parent_1_ok : ttFiber49ParentCheck 1 = true := by decide
theorem ttFiber49Parent_2_ok : ttFiber49ParentCheck 2 = true := by decide
theorem ttFiber49Parent_3_ok : ttFiber49ParentCheck 3 = true := by decide
theorem ttFiber49Parent_4_ok : ttFiber49ParentCheck 4 = true := by decide
theorem ttFiber49Parent_5_ok : ttFiber49ParentCheck 5 = true := by decide
theorem ttFiber49Parent_6_ok : ttFiber49ParentCheck 6 = true := by decide
theorem ttFiber49Parent_7_ok : ttFiber49ParentCheck 7 = true := by decide

def ttFiber49CertificateAudit : Bool :=
  ttFiber49SourcesCheck &&
    ttFiber49RowCheck 0 &&
    ttFiber49RowCheck 1 &&
    ttFiber49RowCheck 2 &&
    ttFiber49RowCheck 3 &&
    ttFiber49RowCheck 4 &&
    ttFiber49RowCheck 5 &&
    ttFiber49RowCheck 6 &&
    ttFiber49RowCheck 7 &&
    ttFiber49ParentCheck 0 &&
    ttFiber49ParentCheck 1 &&
    ttFiber49ParentCheck 2 &&
    ttFiber49ParentCheck 3 &&
    ttFiber49ParentCheck 4 &&
    ttFiber49ParentCheck 5 &&
    ttFiber49ParentCheck 6 &&
    ttFiber49ParentCheck 7

theorem ttFiber49CertificateAudit_ok :
    ttFiber49CertificateAudit = true := by
  simp [ttFiber49CertificateAudit,
    ttFiber49SourcesCheck_ok,
    ttFiber49Row_0_ok,
    ttFiber49Row_1_ok,
    ttFiber49Row_2_ok,
    ttFiber49Row_3_ok,
    ttFiber49Row_4_ok,
    ttFiber49Row_5_ok,
    ttFiber49Row_6_ok,
    ttFiber49Row_7_ok,
    ttFiber49Parent_0_ok,
    ttFiber49Parent_1_ok,
    ttFiber49Parent_2_ok,
    ttFiber49Parent_3_ok,
    ttFiber49Parent_4_ok,
    ttFiber49Parent_5_ok,
    ttFiber49Parent_6_ok,
    ttFiber49Parent_7_ok]

def ttFiber50Key : List LColor :=
  [LColor.b, LColor.p, LColor.b, LColor.p]

def ttFiber50Expected : List Nat :=
  [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879]

def ttFiber50Rows : List DirectChainParentRow :=
  [ directRow 768 768 156 148 156 148 default
  , directRow 769 768 156 149 156 148 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 770 769 156 150 156 149 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 771 768 156 151 156 148 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 772 768 156 164 156 148 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 773 769 156 165 156 149 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 774 772 156 166 156 164 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 775 771 156 167 156 151 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 776 768 157 156 156 148 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 777 769 157 157 156 149 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 778 770 157 158 156 150 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 779 771 157 159 156 151 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 780 772 157 172 156 164 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 781 773 157 173 156 165 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 782 774 157 174 156 166 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 783 775 157 175 156 167 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 784 788 158 0 158 48 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 785 789 158 1 158 49 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 786 780 158 2 157 172 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 787 781 158 3 157 173 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 788 776 158 48 157 156 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 789 777 158 49 157 157 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 790 778 158 50 157 158 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 791 779 158 51 157 159 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 792 796 159 8 159 56 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 793 797 159 9 159 57 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 794 772 159 10 156 164 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 795 773 159 11 156 165 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 796 768 159 56 156 148 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 797 769 159 57 156 149 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 798 770 159 58 156 150 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 799 771 159 59 156 151 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 848 768 172 132 156 148 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 849 769 172 133 156 149 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 850 770 172 134 156 150 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 851 771 172 135 156 151 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 852 772 172 180 156 164 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 853 773 172 181 156 165 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 854 774 172 182 156 166 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 855 775 172 183 156 167 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 856 776 173 140 157 156 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 857 777 173 141 157 157 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 858 778 173 142 157 158 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 859 779 173 143 157 159 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 860 780 173 188 157 172 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 861 781 173 189 157 173 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 862 782 173 190 157 174 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 863 783 173 191 157 175 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 864 848 174 64 172 132 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 865 849 174 65 172 133 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 866 864 174 66 174 64 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 867 851 174 67 172 135 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 868 852 174 116 172 180 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 869 853 174 117 172 181 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 870 865 174 118 174 65 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 871 864 174 119 174 64 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 872 856 175 72 173 140 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 873 857 175 73 173 141 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 874 794 175 74 159 10 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 875 795 175 75 159 11 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 876 796 175 124 159 56 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 877 797 175 125 159 57 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  , directRow 878 876 175 126 175 124 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 879 799 175 127 159 59 (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
  ]

def ttFiber50RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber50Rows i default

def ttFiber50SourcesCheck : Bool :=
  (ttFiber50Rows.map fun row => row.source) == ttFiber50Expected

theorem ttFiber50SourcesCheck_ok :
    ttFiber50SourcesCheck = true := by
  decide

def ttFiber50RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt i)

theorem ttFiber50Row_0_ok : ttFiber50RowCheck 0 = true := by decide
theorem ttFiber50Row_1_ok : ttFiber50RowCheck 1 = true := by decide
theorem ttFiber50Row_2_ok : ttFiber50RowCheck 2 = true := by decide
theorem ttFiber50Row_3_ok : ttFiber50RowCheck 3 = true := by decide
theorem ttFiber50Row_4_ok : ttFiber50RowCheck 4 = true := by decide
theorem ttFiber50Row_5_ok : ttFiber50RowCheck 5 = true := by decide
theorem ttFiber50Row_6_ok : ttFiber50RowCheck 6 = true := by decide
theorem ttFiber50Row_7_ok : ttFiber50RowCheck 7 = true := by decide
theorem ttFiber50Row_8_ok : ttFiber50RowCheck 8 = true := by decide
theorem ttFiber50Row_9_ok : ttFiber50RowCheck 9 = true := by decide
theorem ttFiber50Row_10_ok : ttFiber50RowCheck 10 = true := by decide
theorem ttFiber50Row_11_ok : ttFiber50RowCheck 11 = true := by decide
theorem ttFiber50Row_12_ok : ttFiber50RowCheck 12 = true := by decide
theorem ttFiber50Row_13_ok : ttFiber50RowCheck 13 = true := by decide
theorem ttFiber50Row_14_ok : ttFiber50RowCheck 14 = true := by decide
theorem ttFiber50Row_15_ok : ttFiber50RowCheck 15 = true := by decide
theorem ttFiber50Row_16_ok : ttFiber50RowCheck 16 = true := by decide
theorem ttFiber50Row_17_ok : ttFiber50RowCheck 17 = true := by decide
theorem ttFiber50Row_18_ok : ttFiber50RowCheck 18 = true := by decide
theorem ttFiber50Row_19_ok : ttFiber50RowCheck 19 = true := by decide
theorem ttFiber50Row_20_ok : ttFiber50RowCheck 20 = true := by decide
theorem ttFiber50Row_21_ok : ttFiber50RowCheck 21 = true := by decide
theorem ttFiber50Row_22_ok : ttFiber50RowCheck 22 = true := by decide
theorem ttFiber50Row_23_ok : ttFiber50RowCheck 23 = true := by decide
theorem ttFiber50Row_24_ok : ttFiber50RowCheck 24 = true := by decide
theorem ttFiber50Row_25_ok : ttFiber50RowCheck 25 = true := by decide
theorem ttFiber50Row_26_ok : ttFiber50RowCheck 26 = true := by decide
theorem ttFiber50Row_27_ok : ttFiber50RowCheck 27 = true := by decide
theorem ttFiber50Row_28_ok : ttFiber50RowCheck 28 = true := by decide
theorem ttFiber50Row_29_ok : ttFiber50RowCheck 29 = true := by decide
theorem ttFiber50Row_30_ok : ttFiber50RowCheck 30 = true := by decide
theorem ttFiber50Row_31_ok : ttFiber50RowCheck 31 = true := by decide
theorem ttFiber50Row_32_ok : ttFiber50RowCheck 32 = true := by decide
theorem ttFiber50Row_33_ok : ttFiber50RowCheck 33 = true := by decide
theorem ttFiber50Row_34_ok : ttFiber50RowCheck 34 = true := by decide
theorem ttFiber50Row_35_ok : ttFiber50RowCheck 35 = true := by decide
theorem ttFiber50Row_36_ok : ttFiber50RowCheck 36 = true := by decide
theorem ttFiber50Row_37_ok : ttFiber50RowCheck 37 = true := by decide
theorem ttFiber50Row_38_ok : ttFiber50RowCheck 38 = true := by decide
theorem ttFiber50Row_39_ok : ttFiber50RowCheck 39 = true := by decide
theorem ttFiber50Row_40_ok : ttFiber50RowCheck 40 = true := by decide
theorem ttFiber50Row_41_ok : ttFiber50RowCheck 41 = true := by decide
theorem ttFiber50Row_42_ok : ttFiber50RowCheck 42 = true := by decide
theorem ttFiber50Row_43_ok : ttFiber50RowCheck 43 = true := by decide
theorem ttFiber50Row_44_ok : ttFiber50RowCheck 44 = true := by decide
theorem ttFiber50Row_45_ok : ttFiber50RowCheck 45 = true := by decide
theorem ttFiber50Row_46_ok : ttFiber50RowCheck 46 = true := by decide
theorem ttFiber50Row_47_ok : ttFiber50RowCheck 47 = true := by decide
theorem ttFiber50Row_48_ok : ttFiber50RowCheck 48 = true := by decide
theorem ttFiber50Row_49_ok : ttFiber50RowCheck 49 = true := by decide
theorem ttFiber50Row_50_ok : ttFiber50RowCheck 50 = true := by decide
theorem ttFiber50Row_51_ok : ttFiber50RowCheck 51 = true := by decide
theorem ttFiber50Row_52_ok : ttFiber50RowCheck 52 = true := by decide
theorem ttFiber50Row_53_ok : ttFiber50RowCheck 53 = true := by decide
theorem ttFiber50Row_54_ok : ttFiber50RowCheck 54 = true := by decide
theorem ttFiber50Row_55_ok : ttFiber50RowCheck 55 = true := by decide
theorem ttFiber50Row_56_ok : ttFiber50RowCheck 56 = true := by decide
theorem ttFiber50Row_57_ok : ttFiber50RowCheck 57 = true := by decide
theorem ttFiber50Row_58_ok : ttFiber50RowCheck 58 = true := by decide
theorem ttFiber50Row_59_ok : ttFiber50RowCheck 59 = true := by decide
theorem ttFiber50Row_60_ok : ttFiber50RowCheck 60 = true := by decide
theorem ttFiber50Row_61_ok : ttFiber50RowCheck 61 = true := by decide
theorem ttFiber50Row_62_ok : ttFiber50RowCheck 62 = true := by decide
theorem ttFiber50Row_63_ok : ttFiber50RowCheck 63 = true := by decide

def ttFiber50ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber50Rows ttMaxParentDepth (listGetD ttFiber50Expected i 0) == 768

theorem ttFiber50Parent_0_ok : ttFiber50ParentCheck 0 = true := by decide
theorem ttFiber50Parent_1_ok : ttFiber50ParentCheck 1 = true := by decide
theorem ttFiber50Parent_2_ok : ttFiber50ParentCheck 2 = true := by decide
theorem ttFiber50Parent_3_ok : ttFiber50ParentCheck 3 = true := by decide
theorem ttFiber50Parent_4_ok : ttFiber50ParentCheck 4 = true := by decide
theorem ttFiber50Parent_5_ok : ttFiber50ParentCheck 5 = true := by decide
theorem ttFiber50Parent_6_ok : ttFiber50ParentCheck 6 = true := by decide
theorem ttFiber50Parent_7_ok : ttFiber50ParentCheck 7 = true := by decide
theorem ttFiber50Parent_8_ok : ttFiber50ParentCheck 8 = true := by decide
theorem ttFiber50Parent_9_ok : ttFiber50ParentCheck 9 = true := by decide
theorem ttFiber50Parent_10_ok : ttFiber50ParentCheck 10 = true := by decide
theorem ttFiber50Parent_11_ok : ttFiber50ParentCheck 11 = true := by decide
theorem ttFiber50Parent_12_ok : ttFiber50ParentCheck 12 = true := by decide
theorem ttFiber50Parent_13_ok : ttFiber50ParentCheck 13 = true := by decide
theorem ttFiber50Parent_14_ok : ttFiber50ParentCheck 14 = true := by decide
theorem ttFiber50Parent_15_ok : ttFiber50ParentCheck 15 = true := by decide
theorem ttFiber50Parent_16_ok : ttFiber50ParentCheck 16 = true := by decide
theorem ttFiber50Parent_17_ok : ttFiber50ParentCheck 17 = true := by decide
theorem ttFiber50Parent_18_ok : ttFiber50ParentCheck 18 = true := by decide
theorem ttFiber50Parent_19_ok : ttFiber50ParentCheck 19 = true := by decide
theorem ttFiber50Parent_20_ok : ttFiber50ParentCheck 20 = true := by decide
theorem ttFiber50Parent_21_ok : ttFiber50ParentCheck 21 = true := by decide
theorem ttFiber50Parent_22_ok : ttFiber50ParentCheck 22 = true := by decide
theorem ttFiber50Parent_23_ok : ttFiber50ParentCheck 23 = true := by decide
theorem ttFiber50Parent_24_ok : ttFiber50ParentCheck 24 = true := by decide
theorem ttFiber50Parent_25_ok : ttFiber50ParentCheck 25 = true := by decide
theorem ttFiber50Parent_26_ok : ttFiber50ParentCheck 26 = true := by decide
theorem ttFiber50Parent_27_ok : ttFiber50ParentCheck 27 = true := by decide
theorem ttFiber50Parent_28_ok : ttFiber50ParentCheck 28 = true := by decide
theorem ttFiber50Parent_29_ok : ttFiber50ParentCheck 29 = true := by decide
theorem ttFiber50Parent_30_ok : ttFiber50ParentCheck 30 = true := by decide
theorem ttFiber50Parent_31_ok : ttFiber50ParentCheck 31 = true := by decide
theorem ttFiber50Parent_32_ok : ttFiber50ParentCheck 32 = true := by decide
theorem ttFiber50Parent_33_ok : ttFiber50ParentCheck 33 = true := by decide
theorem ttFiber50Parent_34_ok : ttFiber50ParentCheck 34 = true := by decide
theorem ttFiber50Parent_35_ok : ttFiber50ParentCheck 35 = true := by decide
theorem ttFiber50Parent_36_ok : ttFiber50ParentCheck 36 = true := by decide
theorem ttFiber50Parent_37_ok : ttFiber50ParentCheck 37 = true := by decide
theorem ttFiber50Parent_38_ok : ttFiber50ParentCheck 38 = true := by decide
theorem ttFiber50Parent_39_ok : ttFiber50ParentCheck 39 = true := by decide
theorem ttFiber50Parent_40_ok : ttFiber50ParentCheck 40 = true := by decide
theorem ttFiber50Parent_41_ok : ttFiber50ParentCheck 41 = true := by decide
theorem ttFiber50Parent_42_ok : ttFiber50ParentCheck 42 = true := by decide
theorem ttFiber50Parent_43_ok : ttFiber50ParentCheck 43 = true := by decide
theorem ttFiber50Parent_44_ok : ttFiber50ParentCheck 44 = true := by decide
theorem ttFiber50Parent_45_ok : ttFiber50ParentCheck 45 = true := by decide
theorem ttFiber50Parent_46_ok : ttFiber50ParentCheck 46 = true := by decide
theorem ttFiber50Parent_47_ok : ttFiber50ParentCheck 47 = true := by decide
theorem ttFiber50Parent_48_ok : ttFiber50ParentCheck 48 = true := by decide
theorem ttFiber50Parent_49_ok : ttFiber50ParentCheck 49 = true := by decide
theorem ttFiber50Parent_50_ok : ttFiber50ParentCheck 50 = true := by decide
theorem ttFiber50Parent_51_ok : ttFiber50ParentCheck 51 = true := by decide
theorem ttFiber50Parent_52_ok : ttFiber50ParentCheck 52 = true := by decide
theorem ttFiber50Parent_53_ok : ttFiber50ParentCheck 53 = true := by decide
theorem ttFiber50Parent_54_ok : ttFiber50ParentCheck 54 = true := by decide
theorem ttFiber50Parent_55_ok : ttFiber50ParentCheck 55 = true := by decide
theorem ttFiber50Parent_56_ok : ttFiber50ParentCheck 56 = true := by decide
theorem ttFiber50Parent_57_ok : ttFiber50ParentCheck 57 = true := by decide
theorem ttFiber50Parent_58_ok : ttFiber50ParentCheck 58 = true := by decide
theorem ttFiber50Parent_59_ok : ttFiber50ParentCheck 59 = true := by decide
theorem ttFiber50Parent_60_ok : ttFiber50ParentCheck 60 = true := by decide
theorem ttFiber50Parent_61_ok : ttFiber50ParentCheck 61 = true := by decide
theorem ttFiber50Parent_62_ok : ttFiber50ParentCheck 62 = true := by decide
theorem ttFiber50Parent_63_ok : ttFiber50ParentCheck 63 = true := by decide

def ttFiber50CertificateAudit : Bool :=
  ttFiber50SourcesCheck &&
    ttFiber50RowCheck 0 &&
    ttFiber50RowCheck 1 &&
    ttFiber50RowCheck 2 &&
    ttFiber50RowCheck 3 &&
    ttFiber50RowCheck 4 &&
    ttFiber50RowCheck 5 &&
    ttFiber50RowCheck 6 &&
    ttFiber50RowCheck 7 &&
    ttFiber50RowCheck 8 &&
    ttFiber50RowCheck 9 &&
    ttFiber50RowCheck 10 &&
    ttFiber50RowCheck 11 &&
    ttFiber50RowCheck 12 &&
    ttFiber50RowCheck 13 &&
    ttFiber50RowCheck 14 &&
    ttFiber50RowCheck 15 &&
    ttFiber50RowCheck 16 &&
    ttFiber50RowCheck 17 &&
    ttFiber50RowCheck 18 &&
    ttFiber50RowCheck 19 &&
    ttFiber50RowCheck 20 &&
    ttFiber50RowCheck 21 &&
    ttFiber50RowCheck 22 &&
    ttFiber50RowCheck 23 &&
    ttFiber50RowCheck 24 &&
    ttFiber50RowCheck 25 &&
    ttFiber50RowCheck 26 &&
    ttFiber50RowCheck 27 &&
    ttFiber50RowCheck 28 &&
    ttFiber50RowCheck 29 &&
    ttFiber50RowCheck 30 &&
    ttFiber50RowCheck 31 &&
    ttFiber50RowCheck 32 &&
    ttFiber50RowCheck 33 &&
    ttFiber50RowCheck 34 &&
    ttFiber50RowCheck 35 &&
    ttFiber50RowCheck 36 &&
    ttFiber50RowCheck 37 &&
    ttFiber50RowCheck 38 &&
    ttFiber50RowCheck 39 &&
    ttFiber50RowCheck 40 &&
    ttFiber50RowCheck 41 &&
    ttFiber50RowCheck 42 &&
    ttFiber50RowCheck 43 &&
    ttFiber50RowCheck 44 &&
    ttFiber50RowCheck 45 &&
    ttFiber50RowCheck 46 &&
    ttFiber50RowCheck 47 &&
    ttFiber50RowCheck 48 &&
    ttFiber50RowCheck 49 &&
    ttFiber50RowCheck 50 &&
    ttFiber50RowCheck 51 &&
    ttFiber50RowCheck 52 &&
    ttFiber50RowCheck 53 &&
    ttFiber50RowCheck 54 &&
    ttFiber50RowCheck 55 &&
    ttFiber50RowCheck 56 &&
    ttFiber50RowCheck 57 &&
    ttFiber50RowCheck 58 &&
    ttFiber50RowCheck 59 &&
    ttFiber50RowCheck 60 &&
    ttFiber50RowCheck 61 &&
    ttFiber50RowCheck 62 &&
    ttFiber50RowCheck 63 &&
    ttFiber50ParentCheck 0 &&
    ttFiber50ParentCheck 1 &&
    ttFiber50ParentCheck 2 &&
    ttFiber50ParentCheck 3 &&
    ttFiber50ParentCheck 4 &&
    ttFiber50ParentCheck 5 &&
    ttFiber50ParentCheck 6 &&
    ttFiber50ParentCheck 7 &&
    ttFiber50ParentCheck 8 &&
    ttFiber50ParentCheck 9 &&
    ttFiber50ParentCheck 10 &&
    ttFiber50ParentCheck 11 &&
    ttFiber50ParentCheck 12 &&
    ttFiber50ParentCheck 13 &&
    ttFiber50ParentCheck 14 &&
    ttFiber50ParentCheck 15 &&
    ttFiber50ParentCheck 16 &&
    ttFiber50ParentCheck 17 &&
    ttFiber50ParentCheck 18 &&
    ttFiber50ParentCheck 19 &&
    ttFiber50ParentCheck 20 &&
    ttFiber50ParentCheck 21 &&
    ttFiber50ParentCheck 22 &&
    ttFiber50ParentCheck 23 &&
    ttFiber50ParentCheck 24 &&
    ttFiber50ParentCheck 25 &&
    ttFiber50ParentCheck 26 &&
    ttFiber50ParentCheck 27 &&
    ttFiber50ParentCheck 28 &&
    ttFiber50ParentCheck 29 &&
    ttFiber50ParentCheck 30 &&
    ttFiber50ParentCheck 31 &&
    ttFiber50ParentCheck 32 &&
    ttFiber50ParentCheck 33 &&
    ttFiber50ParentCheck 34 &&
    ttFiber50ParentCheck 35 &&
    ttFiber50ParentCheck 36 &&
    ttFiber50ParentCheck 37 &&
    ttFiber50ParentCheck 38 &&
    ttFiber50ParentCheck 39 &&
    ttFiber50ParentCheck 40 &&
    ttFiber50ParentCheck 41 &&
    ttFiber50ParentCheck 42 &&
    ttFiber50ParentCheck 43 &&
    ttFiber50ParentCheck 44 &&
    ttFiber50ParentCheck 45 &&
    ttFiber50ParentCheck 46 &&
    ttFiber50ParentCheck 47 &&
    ttFiber50ParentCheck 48 &&
    ttFiber50ParentCheck 49 &&
    ttFiber50ParentCheck 50 &&
    ttFiber50ParentCheck 51 &&
    ttFiber50ParentCheck 52 &&
    ttFiber50ParentCheck 53 &&
    ttFiber50ParentCheck 54 &&
    ttFiber50ParentCheck 55 &&
    ttFiber50ParentCheck 56 &&
    ttFiber50ParentCheck 57 &&
    ttFiber50ParentCheck 58 &&
    ttFiber50ParentCheck 59 &&
    ttFiber50ParentCheck 60 &&
    ttFiber50ParentCheck 61 &&
    ttFiber50ParentCheck 62 &&
    ttFiber50ParentCheck 63

theorem ttFiber50CertificateAudit_ok :
    ttFiber50CertificateAudit = true := by
  simp [ttFiber50CertificateAudit,
    ttFiber50SourcesCheck_ok,
    ttFiber50Row_0_ok,
    ttFiber50Row_1_ok,
    ttFiber50Row_2_ok,
    ttFiber50Row_3_ok,
    ttFiber50Row_4_ok,
    ttFiber50Row_5_ok,
    ttFiber50Row_6_ok,
    ttFiber50Row_7_ok,
    ttFiber50Row_8_ok,
    ttFiber50Row_9_ok,
    ttFiber50Row_10_ok,
    ttFiber50Row_11_ok,
    ttFiber50Row_12_ok,
    ttFiber50Row_13_ok,
    ttFiber50Row_14_ok,
    ttFiber50Row_15_ok,
    ttFiber50Row_16_ok,
    ttFiber50Row_17_ok,
    ttFiber50Row_18_ok,
    ttFiber50Row_19_ok,
    ttFiber50Row_20_ok,
    ttFiber50Row_21_ok,
    ttFiber50Row_22_ok,
    ttFiber50Row_23_ok,
    ttFiber50Row_24_ok,
    ttFiber50Row_25_ok,
    ttFiber50Row_26_ok,
    ttFiber50Row_27_ok,
    ttFiber50Row_28_ok,
    ttFiber50Row_29_ok,
    ttFiber50Row_30_ok,
    ttFiber50Row_31_ok,
    ttFiber50Row_32_ok,
    ttFiber50Row_33_ok,
    ttFiber50Row_34_ok,
    ttFiber50Row_35_ok,
    ttFiber50Row_36_ok,
    ttFiber50Row_37_ok,
    ttFiber50Row_38_ok,
    ttFiber50Row_39_ok,
    ttFiber50Row_40_ok,
    ttFiber50Row_41_ok,
    ttFiber50Row_42_ok,
    ttFiber50Row_43_ok,
    ttFiber50Row_44_ok,
    ttFiber50Row_45_ok,
    ttFiber50Row_46_ok,
    ttFiber50Row_47_ok,
    ttFiber50Row_48_ok,
    ttFiber50Row_49_ok,
    ttFiber50Row_50_ok,
    ttFiber50Row_51_ok,
    ttFiber50Row_52_ok,
    ttFiber50Row_53_ok,
    ttFiber50Row_54_ok,
    ttFiber50Row_55_ok,
    ttFiber50Row_56_ok,
    ttFiber50Row_57_ok,
    ttFiber50Row_58_ok,
    ttFiber50Row_59_ok,
    ttFiber50Row_60_ok,
    ttFiber50Row_61_ok,
    ttFiber50Row_62_ok,
    ttFiber50Row_63_ok,
    ttFiber50Parent_0_ok,
    ttFiber50Parent_1_ok,
    ttFiber50Parent_2_ok,
    ttFiber50Parent_3_ok,
    ttFiber50Parent_4_ok,
    ttFiber50Parent_5_ok,
    ttFiber50Parent_6_ok,
    ttFiber50Parent_7_ok,
    ttFiber50Parent_8_ok,
    ttFiber50Parent_9_ok,
    ttFiber50Parent_10_ok,
    ttFiber50Parent_11_ok,
    ttFiber50Parent_12_ok,
    ttFiber50Parent_13_ok,
    ttFiber50Parent_14_ok,
    ttFiber50Parent_15_ok,
    ttFiber50Parent_16_ok,
    ttFiber50Parent_17_ok,
    ttFiber50Parent_18_ok,
    ttFiber50Parent_19_ok,
    ttFiber50Parent_20_ok,
    ttFiber50Parent_21_ok,
    ttFiber50Parent_22_ok,
    ttFiber50Parent_23_ok,
    ttFiber50Parent_24_ok,
    ttFiber50Parent_25_ok,
    ttFiber50Parent_26_ok,
    ttFiber50Parent_27_ok,
    ttFiber50Parent_28_ok,
    ttFiber50Parent_29_ok,
    ttFiber50Parent_30_ok,
    ttFiber50Parent_31_ok,
    ttFiber50Parent_32_ok,
    ttFiber50Parent_33_ok,
    ttFiber50Parent_34_ok,
    ttFiber50Parent_35_ok,
    ttFiber50Parent_36_ok,
    ttFiber50Parent_37_ok,
    ttFiber50Parent_38_ok,
    ttFiber50Parent_39_ok,
    ttFiber50Parent_40_ok,
    ttFiber50Parent_41_ok,
    ttFiber50Parent_42_ok,
    ttFiber50Parent_43_ok,
    ttFiber50Parent_44_ok,
    ttFiber50Parent_45_ok,
    ttFiber50Parent_46_ok,
    ttFiber50Parent_47_ok,
    ttFiber50Parent_48_ok,
    ttFiber50Parent_49_ok,
    ttFiber50Parent_50_ok,
    ttFiber50Parent_51_ok,
    ttFiber50Parent_52_ok,
    ttFiber50Parent_53_ok,
    ttFiber50Parent_54_ok,
    ttFiber50Parent_55_ok,
    ttFiber50Parent_56_ok,
    ttFiber50Parent_57_ok,
    ttFiber50Parent_58_ok,
    ttFiber50Parent_59_ok,
    ttFiber50Parent_60_ok,
    ttFiber50Parent_61_ok,
    ttFiber50Parent_62_ok,
    ttFiber50Parent_63_ok]

def ttFiber51Key : List LColor :=
  [LColor.b, LColor.p, LColor.p, LColor.r]

def ttFiber51Expected : List Nat :=
  []

def ttFiber51Rows : List DirectChainParentRow :=
  []

def ttFiber51RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber51Rows i default

def ttFiber51SourcesCheck : Bool :=
  (ttFiber51Rows.map fun row => row.source) == ttFiber51Expected

theorem ttFiber51SourcesCheck_ok :
    ttFiber51SourcesCheck = true := by
  decide

def ttFiber51RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber51Key ttFiber51Expected (ttFiber51RowAt i)

def ttFiber51ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber51Rows ttMaxParentDepth (listGetD ttFiber51Expected i 0) == 0

def ttFiber51CertificateAudit : Bool :=
  ttFiber51SourcesCheck

theorem ttFiber51CertificateAudit_ok :
    ttFiber51CertificateAudit = true := by
  simp [ttFiber51CertificateAudit,
    ttFiber51SourcesCheck_ok]

def ttFiber52Key : List LColor :=
  [LColor.b, LColor.p, LColor.p, LColor.b]

def ttFiber52Expected : List Nat :=
  []

def ttFiber52Rows : List DirectChainParentRow :=
  []

def ttFiber52RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber52Rows i default

def ttFiber52SourcesCheck : Bool :=
  (ttFiber52Rows.map fun row => row.source) == ttFiber52Expected

theorem ttFiber52SourcesCheck_ok :
    ttFiber52SourcesCheck = true := by
  decide

def ttFiber52RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber52Key ttFiber52Expected (ttFiber52RowAt i)

def ttFiber52ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber52Rows ttMaxParentDepth (listGetD ttFiber52Expected i 0) == 0

def ttFiber52CertificateAudit : Bool :=
  ttFiber52SourcesCheck

theorem ttFiber52CertificateAudit_ok :
    ttFiber52CertificateAudit = true := by
  simp [ttFiber52CertificateAudit,
    ttFiber52SourcesCheck_ok]

def ttFiber53Key : List LColor :=
  [LColor.b, LColor.p, LColor.p, LColor.p]

def ttFiber53Expected : List Nat :=
  []

def ttFiber53Rows : List DirectChainParentRow :=
  []

def ttFiber53RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber53Rows i default

def ttFiber53SourcesCheck : Bool :=
  (ttFiber53Rows.map fun row => row.source) == ttFiber53Expected

theorem ttFiber53SourcesCheck_ok :
    ttFiber53SourcesCheck = true := by
  decide

def ttFiber53RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber53Key ttFiber53Expected (ttFiber53RowAt i)

def ttFiber53ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber53Rows ttMaxParentDepth (listGetD ttFiber53Expected i 0) == 0

def ttFiber53CertificateAudit : Bool :=
  ttFiber53SourcesCheck

theorem ttFiber53CertificateAudit_ok :
    ttFiber53CertificateAudit = true := by
  simp [ttFiber53CertificateAudit,
    ttFiber53SourcesCheck_ok]

def ttFiber54Key : List LColor :=
  [LColor.p, LColor.r, LColor.r, LColor.r]

def ttFiber54Expected : List Nat :=
  []

def ttFiber54Rows : List DirectChainParentRow :=
  []

def ttFiber54RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber54Rows i default

def ttFiber54SourcesCheck : Bool :=
  (ttFiber54Rows.map fun row => row.source) == ttFiber54Expected

theorem ttFiber54SourcesCheck_ok :
    ttFiber54SourcesCheck = true := by
  decide

def ttFiber54RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber54Key ttFiber54Expected (ttFiber54RowAt i)

def ttFiber54ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber54Rows ttMaxParentDepth (listGetD ttFiber54Expected i 0) == 0

def ttFiber54CertificateAudit : Bool :=
  ttFiber54SourcesCheck

theorem ttFiber54CertificateAudit_ok :
    ttFiber54CertificateAudit = true := by
  simp [ttFiber54CertificateAudit,
    ttFiber54SourcesCheck_ok]

def ttFiber55Key : List LColor :=
  [LColor.p, LColor.r, LColor.r, LColor.b]

def ttFiber55Expected : List Nat :=
  []

def ttFiber55Rows : List DirectChainParentRow :=
  []

def ttFiber55RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber55Rows i default

def ttFiber55SourcesCheck : Bool :=
  (ttFiber55Rows.map fun row => row.source) == ttFiber55Expected

theorem ttFiber55SourcesCheck_ok :
    ttFiber55SourcesCheck = true := by
  decide

def ttFiber55RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber55Key ttFiber55Expected (ttFiber55RowAt i)

def ttFiber55ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber55Rows ttMaxParentDepth (listGetD ttFiber55Expected i 0) == 0

def ttFiber55CertificateAudit : Bool :=
  ttFiber55SourcesCheck

theorem ttFiber55CertificateAudit_ok :
    ttFiber55CertificateAudit = true := by
  simp [ttFiber55CertificateAudit,
    ttFiber55SourcesCheck_ok]

def ttFiber56Key : List LColor :=
  [LColor.p, LColor.r, LColor.r, LColor.p]

def ttFiber56Expected : List Nat :=
  []

def ttFiber56Rows : List DirectChainParentRow :=
  []

def ttFiber56RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber56Rows i default

def ttFiber56SourcesCheck : Bool :=
  (ttFiber56Rows.map fun row => row.source) == ttFiber56Expected

theorem ttFiber56SourcesCheck_ok :
    ttFiber56SourcesCheck = true := by
  decide

def ttFiber56RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber56Key ttFiber56Expected (ttFiber56RowAt i)

def ttFiber56ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber56Rows ttMaxParentDepth (listGetD ttFiber56Expected i 0) == 0

def ttFiber56CertificateAudit : Bool :=
  ttFiber56SourcesCheck

theorem ttFiber56CertificateAudit_ok :
    ttFiber56CertificateAudit = true := by
  simp [ttFiber56CertificateAudit,
    ttFiber56SourcesCheck_ok]

def ttFiber57Key : List LColor :=
  [LColor.p, LColor.r, LColor.b, LColor.r]

def ttFiber57Expected : List Nat :=
  []

def ttFiber57Rows : List DirectChainParentRow :=
  []

def ttFiber57RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber57Rows i default

def ttFiber57SourcesCheck : Bool :=
  (ttFiber57Rows.map fun row => row.source) == ttFiber57Expected

theorem ttFiber57SourcesCheck_ok :
    ttFiber57SourcesCheck = true := by
  decide

def ttFiber57RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber57Key ttFiber57Expected (ttFiber57RowAt i)

def ttFiber57ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber57Rows ttMaxParentDepth (listGetD ttFiber57Expected i 0) == 0

def ttFiber57CertificateAudit : Bool :=
  ttFiber57SourcesCheck

theorem ttFiber57CertificateAudit_ok :
    ttFiber57CertificateAudit = true := by
  simp [ttFiber57CertificateAudit,
    ttFiber57SourcesCheck_ok]

def ttFiber58Key : List LColor :=
  [LColor.p, LColor.r, LColor.b, LColor.b]

def ttFiber58Expected : List Nat :=
  []

def ttFiber58Rows : List DirectChainParentRow :=
  []

def ttFiber58RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber58Rows i default

def ttFiber58SourcesCheck : Bool :=
  (ttFiber58Rows.map fun row => row.source) == ttFiber58Expected

theorem ttFiber58SourcesCheck_ok :
    ttFiber58SourcesCheck = true := by
  decide

def ttFiber58RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber58Key ttFiber58Expected (ttFiber58RowAt i)

def ttFiber58ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber58Rows ttMaxParentDepth (listGetD ttFiber58Expected i 0) == 0

def ttFiber58CertificateAudit : Bool :=
  ttFiber58SourcesCheck

theorem ttFiber58CertificateAudit_ok :
    ttFiber58CertificateAudit = true := by
  simp [ttFiber58CertificateAudit,
    ttFiber58SourcesCheck_ok]

def ttFiber59Key : List LColor :=
  [LColor.p, LColor.r, LColor.b, LColor.p]

def ttFiber59Expected : List Nat :=
  []

def ttFiber59Rows : List DirectChainParentRow :=
  []

def ttFiber59RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber59Rows i default

def ttFiber59SourcesCheck : Bool :=
  (ttFiber59Rows.map fun row => row.source) == ttFiber59Expected

theorem ttFiber59SourcesCheck_ok :
    ttFiber59SourcesCheck = true := by
  decide

def ttFiber59RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber59Key ttFiber59Expected (ttFiber59RowAt i)

def ttFiber59ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber59Rows ttMaxParentDepth (listGetD ttFiber59Expected i 0) == 0

def ttFiber59CertificateAudit : Bool :=
  ttFiber59SourcesCheck

theorem ttFiber59CertificateAudit_ok :
    ttFiber59CertificateAudit = true := by
  simp [ttFiber59CertificateAudit,
    ttFiber59SourcesCheck_ok]

def ttFiber60Key : List LColor :=
  [LColor.p, LColor.r, LColor.p, LColor.r]

def ttFiber60Expected : List Nat :=
  [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]

def ttFiber60Rows : List DirectChainParentRow :=
  [ directRow 80 80 16 80 16 80 default
  , directRow 81 80 16 81 16 80 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 82 80 16 82 16 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 83 81 16 83 16 81 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 84 82 16 100 16 82 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 85 87 16 101 16 103 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 86 81 16 102 16 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 87 80 16 103 16 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 88 80 17 88 16 80 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 89 81 17 89 16 81 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 90 82 17 90 16 82 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 91 83 17 91 16 83 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 92 84 17 108 16 100 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 93 85 17 109 16 101 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 94 86 17 110 16 102 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 95 87 17 111 16 103 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 96 80 18 16 16 80 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 97 81 18 17 16 81 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 98 82 18 18 16 82 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 99 83 18 19 16 83 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 100 96 18 32 18 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 101 97 18 33 18 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 102 86 18 34 16 102 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 103 87 18 35 16 103 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 104 88 19 24 17 88 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 105 89 19 25 17 89 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 106 90 19 26 17 90 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 107 91 19 27 17 91 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 108 104 19 40 19 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 109 105 19 41 19 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 110 94 19 42 17 110 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 111 95 19 43 17 111 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 160 80 32 148 16 80 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 161 81 32 149 16 81 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 162 82 32 150 16 82 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 163 160 32 151 32 148 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 164 160 32 164 32 148 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 165 161 32 165 32 149 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 166 86 32 166 16 102 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 167 87 32 167 16 103 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 168 88 33 156 17 88 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 169 89 33 157 17 89 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 170 90 33 158 17 90 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 171 168 33 159 33 156 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 172 168 33 172 33 156 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 173 169 33 173 33 157 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 174 94 33 174 17 110 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 175 95 33 175 17 111 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 176 96 34 0 18 16 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 177 97 34 1 18 17 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 178 98 34 2 18 18 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 179 99 34 3 18 19 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 180 168 34 48 33 156 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 181 169 34 49 33 157 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 182 102 34 50 18 34 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 183 103 34 51 18 35 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 184 167 35 8 32 167 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 185 166 35 9 32 166 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 186 164 35 10 32 164 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 187 165 35 11 32 165 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 188 160 35 56 32 148 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 189 161 35 57 32 149 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 190 162 35 58 32 150 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 191 163 35 59 32 151 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def ttFiber60RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber60Rows i default

def ttFiber60SourcesCheck : Bool :=
  (ttFiber60Rows.map fun row => row.source) == ttFiber60Expected

theorem ttFiber60SourcesCheck_ok :
    ttFiber60SourcesCheck = true := by
  decide

def ttFiber60RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt i)

theorem ttFiber60Row_0_ok : ttFiber60RowCheck 0 = true := by decide
theorem ttFiber60Row_1_ok : ttFiber60RowCheck 1 = true := by decide
theorem ttFiber60Row_2_ok : ttFiber60RowCheck 2 = true := by decide
theorem ttFiber60Row_3_ok : ttFiber60RowCheck 3 = true := by decide
theorem ttFiber60Row_4_ok : ttFiber60RowCheck 4 = true := by decide
theorem ttFiber60Row_5_ok : ttFiber60RowCheck 5 = true := by decide
theorem ttFiber60Row_6_ok : ttFiber60RowCheck 6 = true := by decide
theorem ttFiber60Row_7_ok : ttFiber60RowCheck 7 = true := by decide
theorem ttFiber60Row_8_ok : ttFiber60RowCheck 8 = true := by decide
theorem ttFiber60Row_9_ok : ttFiber60RowCheck 9 = true := by decide
theorem ttFiber60Row_10_ok : ttFiber60RowCheck 10 = true := by decide
theorem ttFiber60Row_11_ok : ttFiber60RowCheck 11 = true := by decide
theorem ttFiber60Row_12_ok : ttFiber60RowCheck 12 = true := by decide
theorem ttFiber60Row_13_ok : ttFiber60RowCheck 13 = true := by decide
theorem ttFiber60Row_14_ok : ttFiber60RowCheck 14 = true := by decide
theorem ttFiber60Row_15_ok : ttFiber60RowCheck 15 = true := by decide
theorem ttFiber60Row_16_ok : ttFiber60RowCheck 16 = true := by decide
theorem ttFiber60Row_17_ok : ttFiber60RowCheck 17 = true := by decide
theorem ttFiber60Row_18_ok : ttFiber60RowCheck 18 = true := by decide
theorem ttFiber60Row_19_ok : ttFiber60RowCheck 19 = true := by decide
theorem ttFiber60Row_20_ok : ttFiber60RowCheck 20 = true := by decide
theorem ttFiber60Row_21_ok : ttFiber60RowCheck 21 = true := by decide
theorem ttFiber60Row_22_ok : ttFiber60RowCheck 22 = true := by decide
theorem ttFiber60Row_23_ok : ttFiber60RowCheck 23 = true := by decide
theorem ttFiber60Row_24_ok : ttFiber60RowCheck 24 = true := by decide
theorem ttFiber60Row_25_ok : ttFiber60RowCheck 25 = true := by decide
theorem ttFiber60Row_26_ok : ttFiber60RowCheck 26 = true := by decide
theorem ttFiber60Row_27_ok : ttFiber60RowCheck 27 = true := by decide
theorem ttFiber60Row_28_ok : ttFiber60RowCheck 28 = true := by decide
theorem ttFiber60Row_29_ok : ttFiber60RowCheck 29 = true := by decide
theorem ttFiber60Row_30_ok : ttFiber60RowCheck 30 = true := by decide
theorem ttFiber60Row_31_ok : ttFiber60RowCheck 31 = true := by decide
theorem ttFiber60Row_32_ok : ttFiber60RowCheck 32 = true := by decide
theorem ttFiber60Row_33_ok : ttFiber60RowCheck 33 = true := by decide
theorem ttFiber60Row_34_ok : ttFiber60RowCheck 34 = true := by decide
theorem ttFiber60Row_35_ok : ttFiber60RowCheck 35 = true := by decide
theorem ttFiber60Row_36_ok : ttFiber60RowCheck 36 = true := by decide
theorem ttFiber60Row_37_ok : ttFiber60RowCheck 37 = true := by decide
theorem ttFiber60Row_38_ok : ttFiber60RowCheck 38 = true := by decide
theorem ttFiber60Row_39_ok : ttFiber60RowCheck 39 = true := by decide
theorem ttFiber60Row_40_ok : ttFiber60RowCheck 40 = true := by decide
theorem ttFiber60Row_41_ok : ttFiber60RowCheck 41 = true := by decide
theorem ttFiber60Row_42_ok : ttFiber60RowCheck 42 = true := by decide
theorem ttFiber60Row_43_ok : ttFiber60RowCheck 43 = true := by decide
theorem ttFiber60Row_44_ok : ttFiber60RowCheck 44 = true := by decide
theorem ttFiber60Row_45_ok : ttFiber60RowCheck 45 = true := by decide
theorem ttFiber60Row_46_ok : ttFiber60RowCheck 46 = true := by decide
theorem ttFiber60Row_47_ok : ttFiber60RowCheck 47 = true := by decide
theorem ttFiber60Row_48_ok : ttFiber60RowCheck 48 = true := by decide
theorem ttFiber60Row_49_ok : ttFiber60RowCheck 49 = true := by decide
theorem ttFiber60Row_50_ok : ttFiber60RowCheck 50 = true := by decide
theorem ttFiber60Row_51_ok : ttFiber60RowCheck 51 = true := by decide
theorem ttFiber60Row_52_ok : ttFiber60RowCheck 52 = true := by decide
theorem ttFiber60Row_53_ok : ttFiber60RowCheck 53 = true := by decide
theorem ttFiber60Row_54_ok : ttFiber60RowCheck 54 = true := by decide
theorem ttFiber60Row_55_ok : ttFiber60RowCheck 55 = true := by decide
theorem ttFiber60Row_56_ok : ttFiber60RowCheck 56 = true := by decide
theorem ttFiber60Row_57_ok : ttFiber60RowCheck 57 = true := by decide
theorem ttFiber60Row_58_ok : ttFiber60RowCheck 58 = true := by decide
theorem ttFiber60Row_59_ok : ttFiber60RowCheck 59 = true := by decide
theorem ttFiber60Row_60_ok : ttFiber60RowCheck 60 = true := by decide
theorem ttFiber60Row_61_ok : ttFiber60RowCheck 61 = true := by decide
theorem ttFiber60Row_62_ok : ttFiber60RowCheck 62 = true := by decide
theorem ttFiber60Row_63_ok : ttFiber60RowCheck 63 = true := by decide

def ttFiber60ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber60Rows ttMaxParentDepth (listGetD ttFiber60Expected i 0) == 80

theorem ttFiber60Parent_0_ok : ttFiber60ParentCheck 0 = true := by decide
theorem ttFiber60Parent_1_ok : ttFiber60ParentCheck 1 = true := by decide
theorem ttFiber60Parent_2_ok : ttFiber60ParentCheck 2 = true := by decide
theorem ttFiber60Parent_3_ok : ttFiber60ParentCheck 3 = true := by decide
theorem ttFiber60Parent_4_ok : ttFiber60ParentCheck 4 = true := by decide
theorem ttFiber60Parent_5_ok : ttFiber60ParentCheck 5 = true := by decide
theorem ttFiber60Parent_6_ok : ttFiber60ParentCheck 6 = true := by decide
theorem ttFiber60Parent_7_ok : ttFiber60ParentCheck 7 = true := by decide
theorem ttFiber60Parent_8_ok : ttFiber60ParentCheck 8 = true := by decide
theorem ttFiber60Parent_9_ok : ttFiber60ParentCheck 9 = true := by decide
theorem ttFiber60Parent_10_ok : ttFiber60ParentCheck 10 = true := by decide
theorem ttFiber60Parent_11_ok : ttFiber60ParentCheck 11 = true := by decide
theorem ttFiber60Parent_12_ok : ttFiber60ParentCheck 12 = true := by decide
theorem ttFiber60Parent_13_ok : ttFiber60ParentCheck 13 = true := by decide
theorem ttFiber60Parent_14_ok : ttFiber60ParentCheck 14 = true := by decide
theorem ttFiber60Parent_15_ok : ttFiber60ParentCheck 15 = true := by decide
theorem ttFiber60Parent_16_ok : ttFiber60ParentCheck 16 = true := by decide
theorem ttFiber60Parent_17_ok : ttFiber60ParentCheck 17 = true := by decide
theorem ttFiber60Parent_18_ok : ttFiber60ParentCheck 18 = true := by decide
theorem ttFiber60Parent_19_ok : ttFiber60ParentCheck 19 = true := by decide
theorem ttFiber60Parent_20_ok : ttFiber60ParentCheck 20 = true := by decide
theorem ttFiber60Parent_21_ok : ttFiber60ParentCheck 21 = true := by decide
theorem ttFiber60Parent_22_ok : ttFiber60ParentCheck 22 = true := by decide
theorem ttFiber60Parent_23_ok : ttFiber60ParentCheck 23 = true := by decide
theorem ttFiber60Parent_24_ok : ttFiber60ParentCheck 24 = true := by decide
theorem ttFiber60Parent_25_ok : ttFiber60ParentCheck 25 = true := by decide
theorem ttFiber60Parent_26_ok : ttFiber60ParentCheck 26 = true := by decide
theorem ttFiber60Parent_27_ok : ttFiber60ParentCheck 27 = true := by decide
theorem ttFiber60Parent_28_ok : ttFiber60ParentCheck 28 = true := by decide
theorem ttFiber60Parent_29_ok : ttFiber60ParentCheck 29 = true := by decide
theorem ttFiber60Parent_30_ok : ttFiber60ParentCheck 30 = true := by decide
theorem ttFiber60Parent_31_ok : ttFiber60ParentCheck 31 = true := by decide
theorem ttFiber60Parent_32_ok : ttFiber60ParentCheck 32 = true := by decide
theorem ttFiber60Parent_33_ok : ttFiber60ParentCheck 33 = true := by decide
theorem ttFiber60Parent_34_ok : ttFiber60ParentCheck 34 = true := by decide
theorem ttFiber60Parent_35_ok : ttFiber60ParentCheck 35 = true := by decide
theorem ttFiber60Parent_36_ok : ttFiber60ParentCheck 36 = true := by decide
theorem ttFiber60Parent_37_ok : ttFiber60ParentCheck 37 = true := by decide
theorem ttFiber60Parent_38_ok : ttFiber60ParentCheck 38 = true := by decide
theorem ttFiber60Parent_39_ok : ttFiber60ParentCheck 39 = true := by decide
theorem ttFiber60Parent_40_ok : ttFiber60ParentCheck 40 = true := by decide
theorem ttFiber60Parent_41_ok : ttFiber60ParentCheck 41 = true := by decide
theorem ttFiber60Parent_42_ok : ttFiber60ParentCheck 42 = true := by decide
theorem ttFiber60Parent_43_ok : ttFiber60ParentCheck 43 = true := by decide
theorem ttFiber60Parent_44_ok : ttFiber60ParentCheck 44 = true := by decide
theorem ttFiber60Parent_45_ok : ttFiber60ParentCheck 45 = true := by decide
theorem ttFiber60Parent_46_ok : ttFiber60ParentCheck 46 = true := by decide
theorem ttFiber60Parent_47_ok : ttFiber60ParentCheck 47 = true := by decide
theorem ttFiber60Parent_48_ok : ttFiber60ParentCheck 48 = true := by decide
theorem ttFiber60Parent_49_ok : ttFiber60ParentCheck 49 = true := by decide
theorem ttFiber60Parent_50_ok : ttFiber60ParentCheck 50 = true := by decide
theorem ttFiber60Parent_51_ok : ttFiber60ParentCheck 51 = true := by decide
theorem ttFiber60Parent_52_ok : ttFiber60ParentCheck 52 = true := by decide
theorem ttFiber60Parent_53_ok : ttFiber60ParentCheck 53 = true := by decide
theorem ttFiber60Parent_54_ok : ttFiber60ParentCheck 54 = true := by decide
theorem ttFiber60Parent_55_ok : ttFiber60ParentCheck 55 = true := by decide
theorem ttFiber60Parent_56_ok : ttFiber60ParentCheck 56 = true := by decide
theorem ttFiber60Parent_57_ok : ttFiber60ParentCheck 57 = true := by decide
theorem ttFiber60Parent_58_ok : ttFiber60ParentCheck 58 = true := by decide
theorem ttFiber60Parent_59_ok : ttFiber60ParentCheck 59 = true := by decide
theorem ttFiber60Parent_60_ok : ttFiber60ParentCheck 60 = true := by decide
theorem ttFiber60Parent_61_ok : ttFiber60ParentCheck 61 = true := by decide
theorem ttFiber60Parent_62_ok : ttFiber60ParentCheck 62 = true := by decide
theorem ttFiber60Parent_63_ok : ttFiber60ParentCheck 63 = true := by decide

def ttFiber60CertificateAudit : Bool :=
  ttFiber60SourcesCheck &&
    ttFiber60RowCheck 0 &&
    ttFiber60RowCheck 1 &&
    ttFiber60RowCheck 2 &&
    ttFiber60RowCheck 3 &&
    ttFiber60RowCheck 4 &&
    ttFiber60RowCheck 5 &&
    ttFiber60RowCheck 6 &&
    ttFiber60RowCheck 7 &&
    ttFiber60RowCheck 8 &&
    ttFiber60RowCheck 9 &&
    ttFiber60RowCheck 10 &&
    ttFiber60RowCheck 11 &&
    ttFiber60RowCheck 12 &&
    ttFiber60RowCheck 13 &&
    ttFiber60RowCheck 14 &&
    ttFiber60RowCheck 15 &&
    ttFiber60RowCheck 16 &&
    ttFiber60RowCheck 17 &&
    ttFiber60RowCheck 18 &&
    ttFiber60RowCheck 19 &&
    ttFiber60RowCheck 20 &&
    ttFiber60RowCheck 21 &&
    ttFiber60RowCheck 22 &&
    ttFiber60RowCheck 23 &&
    ttFiber60RowCheck 24 &&
    ttFiber60RowCheck 25 &&
    ttFiber60RowCheck 26 &&
    ttFiber60RowCheck 27 &&
    ttFiber60RowCheck 28 &&
    ttFiber60RowCheck 29 &&
    ttFiber60RowCheck 30 &&
    ttFiber60RowCheck 31 &&
    ttFiber60RowCheck 32 &&
    ttFiber60RowCheck 33 &&
    ttFiber60RowCheck 34 &&
    ttFiber60RowCheck 35 &&
    ttFiber60RowCheck 36 &&
    ttFiber60RowCheck 37 &&
    ttFiber60RowCheck 38 &&
    ttFiber60RowCheck 39 &&
    ttFiber60RowCheck 40 &&
    ttFiber60RowCheck 41 &&
    ttFiber60RowCheck 42 &&
    ttFiber60RowCheck 43 &&
    ttFiber60RowCheck 44 &&
    ttFiber60RowCheck 45 &&
    ttFiber60RowCheck 46 &&
    ttFiber60RowCheck 47 &&
    ttFiber60RowCheck 48 &&
    ttFiber60RowCheck 49 &&
    ttFiber60RowCheck 50 &&
    ttFiber60RowCheck 51 &&
    ttFiber60RowCheck 52 &&
    ttFiber60RowCheck 53 &&
    ttFiber60RowCheck 54 &&
    ttFiber60RowCheck 55 &&
    ttFiber60RowCheck 56 &&
    ttFiber60RowCheck 57 &&
    ttFiber60RowCheck 58 &&
    ttFiber60RowCheck 59 &&
    ttFiber60RowCheck 60 &&
    ttFiber60RowCheck 61 &&
    ttFiber60RowCheck 62 &&
    ttFiber60RowCheck 63 &&
    ttFiber60ParentCheck 0 &&
    ttFiber60ParentCheck 1 &&
    ttFiber60ParentCheck 2 &&
    ttFiber60ParentCheck 3 &&
    ttFiber60ParentCheck 4 &&
    ttFiber60ParentCheck 5 &&
    ttFiber60ParentCheck 6 &&
    ttFiber60ParentCheck 7 &&
    ttFiber60ParentCheck 8 &&
    ttFiber60ParentCheck 9 &&
    ttFiber60ParentCheck 10 &&
    ttFiber60ParentCheck 11 &&
    ttFiber60ParentCheck 12 &&
    ttFiber60ParentCheck 13 &&
    ttFiber60ParentCheck 14 &&
    ttFiber60ParentCheck 15 &&
    ttFiber60ParentCheck 16 &&
    ttFiber60ParentCheck 17 &&
    ttFiber60ParentCheck 18 &&
    ttFiber60ParentCheck 19 &&
    ttFiber60ParentCheck 20 &&
    ttFiber60ParentCheck 21 &&
    ttFiber60ParentCheck 22 &&
    ttFiber60ParentCheck 23 &&
    ttFiber60ParentCheck 24 &&
    ttFiber60ParentCheck 25 &&
    ttFiber60ParentCheck 26 &&
    ttFiber60ParentCheck 27 &&
    ttFiber60ParentCheck 28 &&
    ttFiber60ParentCheck 29 &&
    ttFiber60ParentCheck 30 &&
    ttFiber60ParentCheck 31 &&
    ttFiber60ParentCheck 32 &&
    ttFiber60ParentCheck 33 &&
    ttFiber60ParentCheck 34 &&
    ttFiber60ParentCheck 35 &&
    ttFiber60ParentCheck 36 &&
    ttFiber60ParentCheck 37 &&
    ttFiber60ParentCheck 38 &&
    ttFiber60ParentCheck 39 &&
    ttFiber60ParentCheck 40 &&
    ttFiber60ParentCheck 41 &&
    ttFiber60ParentCheck 42 &&
    ttFiber60ParentCheck 43 &&
    ttFiber60ParentCheck 44 &&
    ttFiber60ParentCheck 45 &&
    ttFiber60ParentCheck 46 &&
    ttFiber60ParentCheck 47 &&
    ttFiber60ParentCheck 48 &&
    ttFiber60ParentCheck 49 &&
    ttFiber60ParentCheck 50 &&
    ttFiber60ParentCheck 51 &&
    ttFiber60ParentCheck 52 &&
    ttFiber60ParentCheck 53 &&
    ttFiber60ParentCheck 54 &&
    ttFiber60ParentCheck 55 &&
    ttFiber60ParentCheck 56 &&
    ttFiber60ParentCheck 57 &&
    ttFiber60ParentCheck 58 &&
    ttFiber60ParentCheck 59 &&
    ttFiber60ParentCheck 60 &&
    ttFiber60ParentCheck 61 &&
    ttFiber60ParentCheck 62 &&
    ttFiber60ParentCheck 63

theorem ttFiber60CertificateAudit_ok :
    ttFiber60CertificateAudit = true := by
  simp [ttFiber60CertificateAudit,
    ttFiber60SourcesCheck_ok,
    ttFiber60Row_0_ok,
    ttFiber60Row_1_ok,
    ttFiber60Row_2_ok,
    ttFiber60Row_3_ok,
    ttFiber60Row_4_ok,
    ttFiber60Row_5_ok,
    ttFiber60Row_6_ok,
    ttFiber60Row_7_ok,
    ttFiber60Row_8_ok,
    ttFiber60Row_9_ok,
    ttFiber60Row_10_ok,
    ttFiber60Row_11_ok,
    ttFiber60Row_12_ok,
    ttFiber60Row_13_ok,
    ttFiber60Row_14_ok,
    ttFiber60Row_15_ok,
    ttFiber60Row_16_ok,
    ttFiber60Row_17_ok,
    ttFiber60Row_18_ok,
    ttFiber60Row_19_ok,
    ttFiber60Row_20_ok,
    ttFiber60Row_21_ok,
    ttFiber60Row_22_ok,
    ttFiber60Row_23_ok,
    ttFiber60Row_24_ok,
    ttFiber60Row_25_ok,
    ttFiber60Row_26_ok,
    ttFiber60Row_27_ok,
    ttFiber60Row_28_ok,
    ttFiber60Row_29_ok,
    ttFiber60Row_30_ok,
    ttFiber60Row_31_ok,
    ttFiber60Row_32_ok,
    ttFiber60Row_33_ok,
    ttFiber60Row_34_ok,
    ttFiber60Row_35_ok,
    ttFiber60Row_36_ok,
    ttFiber60Row_37_ok,
    ttFiber60Row_38_ok,
    ttFiber60Row_39_ok,
    ttFiber60Row_40_ok,
    ttFiber60Row_41_ok,
    ttFiber60Row_42_ok,
    ttFiber60Row_43_ok,
    ttFiber60Row_44_ok,
    ttFiber60Row_45_ok,
    ttFiber60Row_46_ok,
    ttFiber60Row_47_ok,
    ttFiber60Row_48_ok,
    ttFiber60Row_49_ok,
    ttFiber60Row_50_ok,
    ttFiber60Row_51_ok,
    ttFiber60Row_52_ok,
    ttFiber60Row_53_ok,
    ttFiber60Row_54_ok,
    ttFiber60Row_55_ok,
    ttFiber60Row_56_ok,
    ttFiber60Row_57_ok,
    ttFiber60Row_58_ok,
    ttFiber60Row_59_ok,
    ttFiber60Row_60_ok,
    ttFiber60Row_61_ok,
    ttFiber60Row_62_ok,
    ttFiber60Row_63_ok,
    ttFiber60Parent_0_ok,
    ttFiber60Parent_1_ok,
    ttFiber60Parent_2_ok,
    ttFiber60Parent_3_ok,
    ttFiber60Parent_4_ok,
    ttFiber60Parent_5_ok,
    ttFiber60Parent_6_ok,
    ttFiber60Parent_7_ok,
    ttFiber60Parent_8_ok,
    ttFiber60Parent_9_ok,
    ttFiber60Parent_10_ok,
    ttFiber60Parent_11_ok,
    ttFiber60Parent_12_ok,
    ttFiber60Parent_13_ok,
    ttFiber60Parent_14_ok,
    ttFiber60Parent_15_ok,
    ttFiber60Parent_16_ok,
    ttFiber60Parent_17_ok,
    ttFiber60Parent_18_ok,
    ttFiber60Parent_19_ok,
    ttFiber60Parent_20_ok,
    ttFiber60Parent_21_ok,
    ttFiber60Parent_22_ok,
    ttFiber60Parent_23_ok,
    ttFiber60Parent_24_ok,
    ttFiber60Parent_25_ok,
    ttFiber60Parent_26_ok,
    ttFiber60Parent_27_ok,
    ttFiber60Parent_28_ok,
    ttFiber60Parent_29_ok,
    ttFiber60Parent_30_ok,
    ttFiber60Parent_31_ok,
    ttFiber60Parent_32_ok,
    ttFiber60Parent_33_ok,
    ttFiber60Parent_34_ok,
    ttFiber60Parent_35_ok,
    ttFiber60Parent_36_ok,
    ttFiber60Parent_37_ok,
    ttFiber60Parent_38_ok,
    ttFiber60Parent_39_ok,
    ttFiber60Parent_40_ok,
    ttFiber60Parent_41_ok,
    ttFiber60Parent_42_ok,
    ttFiber60Parent_43_ok,
    ttFiber60Parent_44_ok,
    ttFiber60Parent_45_ok,
    ttFiber60Parent_46_ok,
    ttFiber60Parent_47_ok,
    ttFiber60Parent_48_ok,
    ttFiber60Parent_49_ok,
    ttFiber60Parent_50_ok,
    ttFiber60Parent_51_ok,
    ttFiber60Parent_52_ok,
    ttFiber60Parent_53_ok,
    ttFiber60Parent_54_ok,
    ttFiber60Parent_55_ok,
    ttFiber60Parent_56_ok,
    ttFiber60Parent_57_ok,
    ttFiber60Parent_58_ok,
    ttFiber60Parent_59_ok,
    ttFiber60Parent_60_ok,
    ttFiber60Parent_61_ok,
    ttFiber60Parent_62_ok,
    ttFiber60Parent_63_ok]

def ttFiber61Key : List LColor :=
  [LColor.p, LColor.r, LColor.p, LColor.b]

def ttFiber61Expected : List Nat :=
  [192, 193, 194, 195, 196, 197, 198, 199]

def ttFiber61Rows : List DirectChainParentRow :=
  [ directRow 192 192 38 112 38 112 default
  , directRow 193 192 38 113 38 112 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 194 192 38 114 38 112 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 195 193 38 115 38 113 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 196 192 39 120 38 112 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 197 193 39 121 38 113 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 198 194 39 122 38 114 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 199 195 39 123 38 115 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  ]

def ttFiber61RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber61Rows i default

def ttFiber61SourcesCheck : Bool :=
  (ttFiber61Rows.map fun row => row.source) == ttFiber61Expected

theorem ttFiber61SourcesCheck_ok :
    ttFiber61SourcesCheck = true := by
  decide

def ttFiber61RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber61Key ttFiber61Expected (ttFiber61RowAt i)

theorem ttFiber61Row_0_ok : ttFiber61RowCheck 0 = true := by decide
theorem ttFiber61Row_1_ok : ttFiber61RowCheck 1 = true := by decide
theorem ttFiber61Row_2_ok : ttFiber61RowCheck 2 = true := by decide
theorem ttFiber61Row_3_ok : ttFiber61RowCheck 3 = true := by decide
theorem ttFiber61Row_4_ok : ttFiber61RowCheck 4 = true := by decide
theorem ttFiber61Row_5_ok : ttFiber61RowCheck 5 = true := by decide
theorem ttFiber61Row_6_ok : ttFiber61RowCheck 6 = true := by decide
theorem ttFiber61Row_7_ok : ttFiber61RowCheck 7 = true := by decide

def ttFiber61ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber61Rows ttMaxParentDepth (listGetD ttFiber61Expected i 0) == 192

theorem ttFiber61Parent_0_ok : ttFiber61ParentCheck 0 = true := by decide
theorem ttFiber61Parent_1_ok : ttFiber61ParentCheck 1 = true := by decide
theorem ttFiber61Parent_2_ok : ttFiber61ParentCheck 2 = true := by decide
theorem ttFiber61Parent_3_ok : ttFiber61ParentCheck 3 = true := by decide
theorem ttFiber61Parent_4_ok : ttFiber61ParentCheck 4 = true := by decide
theorem ttFiber61Parent_5_ok : ttFiber61ParentCheck 5 = true := by decide
theorem ttFiber61Parent_6_ok : ttFiber61ParentCheck 6 = true := by decide
theorem ttFiber61Parent_7_ok : ttFiber61ParentCheck 7 = true := by decide

def ttFiber61CertificateAudit : Bool :=
  ttFiber61SourcesCheck &&
    ttFiber61RowCheck 0 &&
    ttFiber61RowCheck 1 &&
    ttFiber61RowCheck 2 &&
    ttFiber61RowCheck 3 &&
    ttFiber61RowCheck 4 &&
    ttFiber61RowCheck 5 &&
    ttFiber61RowCheck 6 &&
    ttFiber61RowCheck 7 &&
    ttFiber61ParentCheck 0 &&
    ttFiber61ParentCheck 1 &&
    ttFiber61ParentCheck 2 &&
    ttFiber61ParentCheck 3 &&
    ttFiber61ParentCheck 4 &&
    ttFiber61ParentCheck 5 &&
    ttFiber61ParentCheck 6 &&
    ttFiber61ParentCheck 7

theorem ttFiber61CertificateAudit_ok :
    ttFiber61CertificateAudit = true := by
  simp [ttFiber61CertificateAudit,
    ttFiber61SourcesCheck_ok,
    ttFiber61Row_0_ok,
    ttFiber61Row_1_ok,
    ttFiber61Row_2_ok,
    ttFiber61Row_3_ok,
    ttFiber61Row_4_ok,
    ttFiber61Row_5_ok,
    ttFiber61Row_6_ok,
    ttFiber61Row_7_ok,
    ttFiber61Parent_0_ok,
    ttFiber61Parent_1_ok,
    ttFiber61Parent_2_ok,
    ttFiber61Parent_3_ok,
    ttFiber61Parent_4_ok,
    ttFiber61Parent_5_ok,
    ttFiber61Parent_6_ok,
    ttFiber61Parent_7_ok]

def ttFiber62Key : List LColor :=
  [LColor.p, LColor.r, LColor.p, LColor.p]

def ttFiber62Expected : List Nat :=
  [112, 113, 114, 115, 116, 117, 118, 119]

def ttFiber62Rows : List DirectChainParentRow :=
  [ directRow 112 112 22 176 22 176 default
  , directRow 113 112 22 177 22 176 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 114 112 22 178 22 176 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 115 113 22 179 22 177 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 116 112 23 184 22 176 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 117 113 23 185 22 177 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 118 114 23 186 22 178 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 119 115 23 187 22 179 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  ]

def ttFiber62RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber62Rows i default

def ttFiber62SourcesCheck : Bool :=
  (ttFiber62Rows.map fun row => row.source) == ttFiber62Expected

theorem ttFiber62SourcesCheck_ok :
    ttFiber62SourcesCheck = true := by
  decide

def ttFiber62RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber62Key ttFiber62Expected (ttFiber62RowAt i)

theorem ttFiber62Row_0_ok : ttFiber62RowCheck 0 = true := by decide
theorem ttFiber62Row_1_ok : ttFiber62RowCheck 1 = true := by decide
theorem ttFiber62Row_2_ok : ttFiber62RowCheck 2 = true := by decide
theorem ttFiber62Row_3_ok : ttFiber62RowCheck 3 = true := by decide
theorem ttFiber62Row_4_ok : ttFiber62RowCheck 4 = true := by decide
theorem ttFiber62Row_5_ok : ttFiber62RowCheck 5 = true := by decide
theorem ttFiber62Row_6_ok : ttFiber62RowCheck 6 = true := by decide
theorem ttFiber62Row_7_ok : ttFiber62RowCheck 7 = true := by decide

def ttFiber62ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber62Rows ttMaxParentDepth (listGetD ttFiber62Expected i 0) == 112

theorem ttFiber62Parent_0_ok : ttFiber62ParentCheck 0 = true := by decide
theorem ttFiber62Parent_1_ok : ttFiber62ParentCheck 1 = true := by decide
theorem ttFiber62Parent_2_ok : ttFiber62ParentCheck 2 = true := by decide
theorem ttFiber62Parent_3_ok : ttFiber62ParentCheck 3 = true := by decide
theorem ttFiber62Parent_4_ok : ttFiber62ParentCheck 4 = true := by decide
theorem ttFiber62Parent_5_ok : ttFiber62ParentCheck 5 = true := by decide
theorem ttFiber62Parent_6_ok : ttFiber62ParentCheck 6 = true := by decide
theorem ttFiber62Parent_7_ok : ttFiber62ParentCheck 7 = true := by decide

def ttFiber62CertificateAudit : Bool :=
  ttFiber62SourcesCheck &&
    ttFiber62RowCheck 0 &&
    ttFiber62RowCheck 1 &&
    ttFiber62RowCheck 2 &&
    ttFiber62RowCheck 3 &&
    ttFiber62RowCheck 4 &&
    ttFiber62RowCheck 5 &&
    ttFiber62RowCheck 6 &&
    ttFiber62RowCheck 7 &&
    ttFiber62ParentCheck 0 &&
    ttFiber62ParentCheck 1 &&
    ttFiber62ParentCheck 2 &&
    ttFiber62ParentCheck 3 &&
    ttFiber62ParentCheck 4 &&
    ttFiber62ParentCheck 5 &&
    ttFiber62ParentCheck 6 &&
    ttFiber62ParentCheck 7

theorem ttFiber62CertificateAudit_ok :
    ttFiber62CertificateAudit = true := by
  simp [ttFiber62CertificateAudit,
    ttFiber62SourcesCheck_ok,
    ttFiber62Row_0_ok,
    ttFiber62Row_1_ok,
    ttFiber62Row_2_ok,
    ttFiber62Row_3_ok,
    ttFiber62Row_4_ok,
    ttFiber62Row_5_ok,
    ttFiber62Row_6_ok,
    ttFiber62Row_7_ok,
    ttFiber62Parent_0_ok,
    ttFiber62Parent_1_ok,
    ttFiber62Parent_2_ok,
    ttFiber62Parent_3_ok,
    ttFiber62Parent_4_ok,
    ttFiber62Parent_5_ok,
    ttFiber62Parent_6_ok,
    ttFiber62Parent_7_ok]

def ttFiber63Key : List LColor :=
  [LColor.p, LColor.b, LColor.r, LColor.r]

def ttFiber63Expected : List Nat :=
  []

def ttFiber63Rows : List DirectChainParentRow :=
  []

def ttFiber63RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber63Rows i default

def ttFiber63SourcesCheck : Bool :=
  (ttFiber63Rows.map fun row => row.source) == ttFiber63Expected

theorem ttFiber63SourcesCheck_ok :
    ttFiber63SourcesCheck = true := by
  decide

def ttFiber63RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber63Key ttFiber63Expected (ttFiber63RowAt i)

def ttFiber63ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber63Rows ttMaxParentDepth (listGetD ttFiber63Expected i 0) == 0

def ttFiber63CertificateAudit : Bool :=
  ttFiber63SourcesCheck

theorem ttFiber63CertificateAudit_ok :
    ttFiber63CertificateAudit = true := by
  simp [ttFiber63CertificateAudit,
    ttFiber63SourcesCheck_ok]

def ttFiber64Key : List LColor :=
  [LColor.p, LColor.b, LColor.r, LColor.b]

def ttFiber64Expected : List Nat :=
  []

def ttFiber64Rows : List DirectChainParentRow :=
  []

def ttFiber64RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber64Rows i default

def ttFiber64SourcesCheck : Bool :=
  (ttFiber64Rows.map fun row => row.source) == ttFiber64Expected

theorem ttFiber64SourcesCheck_ok :
    ttFiber64SourcesCheck = true := by
  decide

def ttFiber64RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber64Key ttFiber64Expected (ttFiber64RowAt i)

def ttFiber64ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber64Rows ttMaxParentDepth (listGetD ttFiber64Expected i 0) == 0

def ttFiber64CertificateAudit : Bool :=
  ttFiber64SourcesCheck

theorem ttFiber64CertificateAudit_ok :
    ttFiber64CertificateAudit = true := by
  simp [ttFiber64CertificateAudit,
    ttFiber64SourcesCheck_ok]

def ttFiber65Key : List LColor :=
  [LColor.p, LColor.b, LColor.r, LColor.p]

def ttFiber65Expected : List Nat :=
  []

def ttFiber65Rows : List DirectChainParentRow :=
  []

def ttFiber65RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber65Rows i default

def ttFiber65SourcesCheck : Bool :=
  (ttFiber65Rows.map fun row => row.source) == ttFiber65Expected

theorem ttFiber65SourcesCheck_ok :
    ttFiber65SourcesCheck = true := by
  decide

def ttFiber65RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber65Key ttFiber65Expected (ttFiber65RowAt i)

def ttFiber65ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber65Rows ttMaxParentDepth (listGetD ttFiber65Expected i 0) == 0

def ttFiber65CertificateAudit : Bool :=
  ttFiber65SourcesCheck

theorem ttFiber65CertificateAudit_ok :
    ttFiber65CertificateAudit = true := by
  simp [ttFiber65CertificateAudit,
    ttFiber65SourcesCheck_ok]

def ttFiber66Key : List LColor :=
  [LColor.p, LColor.b, LColor.b, LColor.r]

def ttFiber66Expected : List Nat :=
  []

def ttFiber66Rows : List DirectChainParentRow :=
  []

def ttFiber66RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber66Rows i default

def ttFiber66SourcesCheck : Bool :=
  (ttFiber66Rows.map fun row => row.source) == ttFiber66Expected

theorem ttFiber66SourcesCheck_ok :
    ttFiber66SourcesCheck = true := by
  decide

def ttFiber66RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber66Key ttFiber66Expected (ttFiber66RowAt i)

def ttFiber66ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber66Rows ttMaxParentDepth (listGetD ttFiber66Expected i 0) == 0

def ttFiber66CertificateAudit : Bool :=
  ttFiber66SourcesCheck

theorem ttFiber66CertificateAudit_ok :
    ttFiber66CertificateAudit = true := by
  simp [ttFiber66CertificateAudit,
    ttFiber66SourcesCheck_ok]

def ttFiber67Key : List LColor :=
  [LColor.p, LColor.b, LColor.b, LColor.b]

def ttFiber67Expected : List Nat :=
  []

def ttFiber67Rows : List DirectChainParentRow :=
  []

def ttFiber67RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber67Rows i default

def ttFiber67SourcesCheck : Bool :=
  (ttFiber67Rows.map fun row => row.source) == ttFiber67Expected

theorem ttFiber67SourcesCheck_ok :
    ttFiber67SourcesCheck = true := by
  decide

def ttFiber67RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber67Key ttFiber67Expected (ttFiber67RowAt i)

def ttFiber67ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber67Rows ttMaxParentDepth (listGetD ttFiber67Expected i 0) == 0

def ttFiber67CertificateAudit : Bool :=
  ttFiber67SourcesCheck

theorem ttFiber67CertificateAudit_ok :
    ttFiber67CertificateAudit = true := by
  simp [ttFiber67CertificateAudit,
    ttFiber67SourcesCheck_ok]

def ttFiber68Key : List LColor :=
  [LColor.p, LColor.b, LColor.b, LColor.p]

def ttFiber68Expected : List Nat :=
  []

def ttFiber68Rows : List DirectChainParentRow :=
  []

def ttFiber68RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber68Rows i default

def ttFiber68SourcesCheck : Bool :=
  (ttFiber68Rows.map fun row => row.source) == ttFiber68Expected

theorem ttFiber68SourcesCheck_ok :
    ttFiber68SourcesCheck = true := by
  decide

def ttFiber68RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber68Key ttFiber68Expected (ttFiber68RowAt i)

def ttFiber68ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber68Rows ttMaxParentDepth (listGetD ttFiber68Expected i 0) == 0

def ttFiber68CertificateAudit : Bool :=
  ttFiber68SourcesCheck

theorem ttFiber68CertificateAudit_ok :
    ttFiber68CertificateAudit = true := by
  simp [ttFiber68CertificateAudit,
    ttFiber68SourcesCheck_ok]

def ttFiber69Key : List LColor :=
  [LColor.p, LColor.b, LColor.p, LColor.r]

def ttFiber69Expected : List Nat :=
  [480, 481, 482, 483, 484, 485, 486, 487]

def ttFiber69Rows : List DirectChainParentRow :=
  [ directRow 480 480 98 52 98 52 default
  , directRow 481 480 98 53 98 52 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 482 481 98 54 98 53 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 483 480 98 55 98 52 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 484 480 99 60 98 52 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 485 481 99 61 98 53 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 486 482 99 62 98 54 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 487 483 99 63 98 55 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  ]

def ttFiber69RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber69Rows i default

def ttFiber69SourcesCheck : Bool :=
  (ttFiber69Rows.map fun row => row.source) == ttFiber69Expected

theorem ttFiber69SourcesCheck_ok :
    ttFiber69SourcesCheck = true := by
  decide

def ttFiber69RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber69Key ttFiber69Expected (ttFiber69RowAt i)

theorem ttFiber69Row_0_ok : ttFiber69RowCheck 0 = true := by decide
theorem ttFiber69Row_1_ok : ttFiber69RowCheck 1 = true := by decide
theorem ttFiber69Row_2_ok : ttFiber69RowCheck 2 = true := by decide
theorem ttFiber69Row_3_ok : ttFiber69RowCheck 3 = true := by decide
theorem ttFiber69Row_4_ok : ttFiber69RowCheck 4 = true := by decide
theorem ttFiber69Row_5_ok : ttFiber69RowCheck 5 = true := by decide
theorem ttFiber69Row_6_ok : ttFiber69RowCheck 6 = true := by decide
theorem ttFiber69Row_7_ok : ttFiber69RowCheck 7 = true := by decide

def ttFiber69ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber69Rows ttMaxParentDepth (listGetD ttFiber69Expected i 0) == 480

theorem ttFiber69Parent_0_ok : ttFiber69ParentCheck 0 = true := by decide
theorem ttFiber69Parent_1_ok : ttFiber69ParentCheck 1 = true := by decide
theorem ttFiber69Parent_2_ok : ttFiber69ParentCheck 2 = true := by decide
theorem ttFiber69Parent_3_ok : ttFiber69ParentCheck 3 = true := by decide
theorem ttFiber69Parent_4_ok : ttFiber69ParentCheck 4 = true := by decide
theorem ttFiber69Parent_5_ok : ttFiber69ParentCheck 5 = true := by decide
theorem ttFiber69Parent_6_ok : ttFiber69ParentCheck 6 = true := by decide
theorem ttFiber69Parent_7_ok : ttFiber69ParentCheck 7 = true := by decide

def ttFiber69CertificateAudit : Bool :=
  ttFiber69SourcesCheck &&
    ttFiber69RowCheck 0 &&
    ttFiber69RowCheck 1 &&
    ttFiber69RowCheck 2 &&
    ttFiber69RowCheck 3 &&
    ttFiber69RowCheck 4 &&
    ttFiber69RowCheck 5 &&
    ttFiber69RowCheck 6 &&
    ttFiber69RowCheck 7 &&
    ttFiber69ParentCheck 0 &&
    ttFiber69ParentCheck 1 &&
    ttFiber69ParentCheck 2 &&
    ttFiber69ParentCheck 3 &&
    ttFiber69ParentCheck 4 &&
    ttFiber69ParentCheck 5 &&
    ttFiber69ParentCheck 6 &&
    ttFiber69ParentCheck 7

theorem ttFiber69CertificateAudit_ok :
    ttFiber69CertificateAudit = true := by
  simp [ttFiber69CertificateAudit,
    ttFiber69SourcesCheck_ok,
    ttFiber69Row_0_ok,
    ttFiber69Row_1_ok,
    ttFiber69Row_2_ok,
    ttFiber69Row_3_ok,
    ttFiber69Row_4_ok,
    ttFiber69Row_5_ok,
    ttFiber69Row_6_ok,
    ttFiber69Row_7_ok,
    ttFiber69Parent_0_ok,
    ttFiber69Parent_1_ok,
    ttFiber69Parent_2_ok,
    ttFiber69Parent_3_ok,
    ttFiber69Parent_4_ok,
    ttFiber69Parent_5_ok,
    ttFiber69Parent_6_ok,
    ttFiber69Parent_7_ok]

def ttFiber70Key : List LColor :=
  [LColor.p, LColor.b, LColor.p, LColor.b]

def ttFiber70Expected : List Nat :=
  [400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519]

def ttFiber70Rows : List DirectChainParentRow :=
  [ directRow 400 400 80 80 80 80 default
  , directRow 401 400 80 81 80 80 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 402 400 80 82 80 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 403 401 80 83 80 81 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 404 402 80 100 80 82 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 405 407 80 101 80 103 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 406 401 80 102 80 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 407 400 80 103 80 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 408 400 81 88 80 80 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 409 401 81 89 80 81 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 410 402 81 90 80 82 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 411 403 81 91 80 83 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 412 404 81 108 80 100 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 413 405 81 109 80 101 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 414 406 81 110 80 102 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 415 407 81 111 80 103 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 416 400 82 16 80 80 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 417 401 82 17 80 81 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 418 402 82 18 80 82 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 419 403 82 19 80 83 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 420 416 82 32 82 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 421 417 82 33 82 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 422 406 82 34 80 102 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 423 407 82 35 80 103 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 424 408 83 24 81 88 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 425 409 83 25 81 89 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 426 410 83 26 81 90 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 427 411 83 27 81 91 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 428 424 83 40 83 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 429 425 83 41 83 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 430 414 83 42 81 110 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 431 415 83 43 81 111 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 488 504 100 132 102 64 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 489 505 100 133 102 65 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 490 422 100 134 82 34 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 491 423 100 135 82 35 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 492 418 100 180 82 18 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 493 495 100 181 100 183 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 494 417 100 182 82 17 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 495 416 100 183 82 16 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 496 512 101 140 103 72 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 497 513 101 141 103 73 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 498 514 101 142 103 74 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 499 496 101 143 101 140 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 500 496 101 188 101 140 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 501 497 101 189 101 141 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 502 518 101 190 103 126 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 503 519 101 191 103 127 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 504 408 102 64 81 88 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 505 409 102 65 81 89 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 506 410 102 66 81 90 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 507 411 102 67 81 91 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 508 412 102 116 81 108 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 509 413 102 117 81 109 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 510 414 102 118 81 110 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 511 415 102 119 81 111 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 512 400 103 72 80 80 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 513 401 103 73 80 81 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 514 402 103 74 80 82 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 515 403 103 75 80 83 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 516 404 103 124 80 100 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 517 405 103 125 80 101 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 518 406 103 126 80 102 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 519 407 103 127 80 103 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  ]

def ttFiber70RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber70Rows i default

def ttFiber70SourcesCheck : Bool :=
  (ttFiber70Rows.map fun row => row.source) == ttFiber70Expected

theorem ttFiber70SourcesCheck_ok :
    ttFiber70SourcesCheck = true := by
  decide

def ttFiber70RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt i)

theorem ttFiber70Row_0_ok : ttFiber70RowCheck 0 = true := by decide
theorem ttFiber70Row_1_ok : ttFiber70RowCheck 1 = true := by decide
theorem ttFiber70Row_2_ok : ttFiber70RowCheck 2 = true := by decide
theorem ttFiber70Row_3_ok : ttFiber70RowCheck 3 = true := by decide
theorem ttFiber70Row_4_ok : ttFiber70RowCheck 4 = true := by decide
theorem ttFiber70Row_5_ok : ttFiber70RowCheck 5 = true := by decide
theorem ttFiber70Row_6_ok : ttFiber70RowCheck 6 = true := by decide
theorem ttFiber70Row_7_ok : ttFiber70RowCheck 7 = true := by decide
theorem ttFiber70Row_8_ok : ttFiber70RowCheck 8 = true := by decide
theorem ttFiber70Row_9_ok : ttFiber70RowCheck 9 = true := by decide
theorem ttFiber70Row_10_ok : ttFiber70RowCheck 10 = true := by decide
theorem ttFiber70Row_11_ok : ttFiber70RowCheck 11 = true := by decide
theorem ttFiber70Row_12_ok : ttFiber70RowCheck 12 = true := by decide
theorem ttFiber70Row_13_ok : ttFiber70RowCheck 13 = true := by decide
theorem ttFiber70Row_14_ok : ttFiber70RowCheck 14 = true := by decide
theorem ttFiber70Row_15_ok : ttFiber70RowCheck 15 = true := by decide
theorem ttFiber70Row_16_ok : ttFiber70RowCheck 16 = true := by decide
theorem ttFiber70Row_17_ok : ttFiber70RowCheck 17 = true := by decide
theorem ttFiber70Row_18_ok : ttFiber70RowCheck 18 = true := by decide
theorem ttFiber70Row_19_ok : ttFiber70RowCheck 19 = true := by decide
theorem ttFiber70Row_20_ok : ttFiber70RowCheck 20 = true := by decide
theorem ttFiber70Row_21_ok : ttFiber70RowCheck 21 = true := by decide
theorem ttFiber70Row_22_ok : ttFiber70RowCheck 22 = true := by decide
theorem ttFiber70Row_23_ok : ttFiber70RowCheck 23 = true := by decide
theorem ttFiber70Row_24_ok : ttFiber70RowCheck 24 = true := by decide
theorem ttFiber70Row_25_ok : ttFiber70RowCheck 25 = true := by decide
theorem ttFiber70Row_26_ok : ttFiber70RowCheck 26 = true := by decide
theorem ttFiber70Row_27_ok : ttFiber70RowCheck 27 = true := by decide
theorem ttFiber70Row_28_ok : ttFiber70RowCheck 28 = true := by decide
theorem ttFiber70Row_29_ok : ttFiber70RowCheck 29 = true := by decide
theorem ttFiber70Row_30_ok : ttFiber70RowCheck 30 = true := by decide
theorem ttFiber70Row_31_ok : ttFiber70RowCheck 31 = true := by decide
theorem ttFiber70Row_32_ok : ttFiber70RowCheck 32 = true := by decide
theorem ttFiber70Row_33_ok : ttFiber70RowCheck 33 = true := by decide
theorem ttFiber70Row_34_ok : ttFiber70RowCheck 34 = true := by decide
theorem ttFiber70Row_35_ok : ttFiber70RowCheck 35 = true := by decide
theorem ttFiber70Row_36_ok : ttFiber70RowCheck 36 = true := by decide
theorem ttFiber70Row_37_ok : ttFiber70RowCheck 37 = true := by decide
theorem ttFiber70Row_38_ok : ttFiber70RowCheck 38 = true := by decide
theorem ttFiber70Row_39_ok : ttFiber70RowCheck 39 = true := by decide
theorem ttFiber70Row_40_ok : ttFiber70RowCheck 40 = true := by decide
theorem ttFiber70Row_41_ok : ttFiber70RowCheck 41 = true := by decide
theorem ttFiber70Row_42_ok : ttFiber70RowCheck 42 = true := by decide
theorem ttFiber70Row_43_ok : ttFiber70RowCheck 43 = true := by decide
theorem ttFiber70Row_44_ok : ttFiber70RowCheck 44 = true := by decide
theorem ttFiber70Row_45_ok : ttFiber70RowCheck 45 = true := by decide
theorem ttFiber70Row_46_ok : ttFiber70RowCheck 46 = true := by decide
theorem ttFiber70Row_47_ok : ttFiber70RowCheck 47 = true := by decide
theorem ttFiber70Row_48_ok : ttFiber70RowCheck 48 = true := by decide
theorem ttFiber70Row_49_ok : ttFiber70RowCheck 49 = true := by decide
theorem ttFiber70Row_50_ok : ttFiber70RowCheck 50 = true := by decide
theorem ttFiber70Row_51_ok : ttFiber70RowCheck 51 = true := by decide
theorem ttFiber70Row_52_ok : ttFiber70RowCheck 52 = true := by decide
theorem ttFiber70Row_53_ok : ttFiber70RowCheck 53 = true := by decide
theorem ttFiber70Row_54_ok : ttFiber70RowCheck 54 = true := by decide
theorem ttFiber70Row_55_ok : ttFiber70RowCheck 55 = true := by decide
theorem ttFiber70Row_56_ok : ttFiber70RowCheck 56 = true := by decide
theorem ttFiber70Row_57_ok : ttFiber70RowCheck 57 = true := by decide
theorem ttFiber70Row_58_ok : ttFiber70RowCheck 58 = true := by decide
theorem ttFiber70Row_59_ok : ttFiber70RowCheck 59 = true := by decide
theorem ttFiber70Row_60_ok : ttFiber70RowCheck 60 = true := by decide
theorem ttFiber70Row_61_ok : ttFiber70RowCheck 61 = true := by decide
theorem ttFiber70Row_62_ok : ttFiber70RowCheck 62 = true := by decide
theorem ttFiber70Row_63_ok : ttFiber70RowCheck 63 = true := by decide

def ttFiber70ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber70Rows ttMaxParentDepth (listGetD ttFiber70Expected i 0) == 400

theorem ttFiber70Parent_0_ok : ttFiber70ParentCheck 0 = true := by decide
theorem ttFiber70Parent_1_ok : ttFiber70ParentCheck 1 = true := by decide
theorem ttFiber70Parent_2_ok : ttFiber70ParentCheck 2 = true := by decide
theorem ttFiber70Parent_3_ok : ttFiber70ParentCheck 3 = true := by decide
theorem ttFiber70Parent_4_ok : ttFiber70ParentCheck 4 = true := by decide
theorem ttFiber70Parent_5_ok : ttFiber70ParentCheck 5 = true := by decide
theorem ttFiber70Parent_6_ok : ttFiber70ParentCheck 6 = true := by decide
theorem ttFiber70Parent_7_ok : ttFiber70ParentCheck 7 = true := by decide
theorem ttFiber70Parent_8_ok : ttFiber70ParentCheck 8 = true := by decide
theorem ttFiber70Parent_9_ok : ttFiber70ParentCheck 9 = true := by decide
theorem ttFiber70Parent_10_ok : ttFiber70ParentCheck 10 = true := by decide
theorem ttFiber70Parent_11_ok : ttFiber70ParentCheck 11 = true := by decide
theorem ttFiber70Parent_12_ok : ttFiber70ParentCheck 12 = true := by decide
theorem ttFiber70Parent_13_ok : ttFiber70ParentCheck 13 = true := by decide
theorem ttFiber70Parent_14_ok : ttFiber70ParentCheck 14 = true := by decide
theorem ttFiber70Parent_15_ok : ttFiber70ParentCheck 15 = true := by decide
theorem ttFiber70Parent_16_ok : ttFiber70ParentCheck 16 = true := by decide
theorem ttFiber70Parent_17_ok : ttFiber70ParentCheck 17 = true := by decide
theorem ttFiber70Parent_18_ok : ttFiber70ParentCheck 18 = true := by decide
theorem ttFiber70Parent_19_ok : ttFiber70ParentCheck 19 = true := by decide
theorem ttFiber70Parent_20_ok : ttFiber70ParentCheck 20 = true := by decide
theorem ttFiber70Parent_21_ok : ttFiber70ParentCheck 21 = true := by decide
theorem ttFiber70Parent_22_ok : ttFiber70ParentCheck 22 = true := by decide
theorem ttFiber70Parent_23_ok : ttFiber70ParentCheck 23 = true := by decide
theorem ttFiber70Parent_24_ok : ttFiber70ParentCheck 24 = true := by decide
theorem ttFiber70Parent_25_ok : ttFiber70ParentCheck 25 = true := by decide
theorem ttFiber70Parent_26_ok : ttFiber70ParentCheck 26 = true := by decide
theorem ttFiber70Parent_27_ok : ttFiber70ParentCheck 27 = true := by decide
theorem ttFiber70Parent_28_ok : ttFiber70ParentCheck 28 = true := by decide
theorem ttFiber70Parent_29_ok : ttFiber70ParentCheck 29 = true := by decide
theorem ttFiber70Parent_30_ok : ttFiber70ParentCheck 30 = true := by decide
theorem ttFiber70Parent_31_ok : ttFiber70ParentCheck 31 = true := by decide
theorem ttFiber70Parent_32_ok : ttFiber70ParentCheck 32 = true := by decide
theorem ttFiber70Parent_33_ok : ttFiber70ParentCheck 33 = true := by decide
theorem ttFiber70Parent_34_ok : ttFiber70ParentCheck 34 = true := by decide
theorem ttFiber70Parent_35_ok : ttFiber70ParentCheck 35 = true := by decide
theorem ttFiber70Parent_36_ok : ttFiber70ParentCheck 36 = true := by decide
theorem ttFiber70Parent_37_ok : ttFiber70ParentCheck 37 = true := by decide
theorem ttFiber70Parent_38_ok : ttFiber70ParentCheck 38 = true := by decide
theorem ttFiber70Parent_39_ok : ttFiber70ParentCheck 39 = true := by decide
theorem ttFiber70Parent_40_ok : ttFiber70ParentCheck 40 = true := by decide
theorem ttFiber70Parent_41_ok : ttFiber70ParentCheck 41 = true := by decide
theorem ttFiber70Parent_42_ok : ttFiber70ParentCheck 42 = true := by decide
theorem ttFiber70Parent_43_ok : ttFiber70ParentCheck 43 = true := by decide
theorem ttFiber70Parent_44_ok : ttFiber70ParentCheck 44 = true := by decide
theorem ttFiber70Parent_45_ok : ttFiber70ParentCheck 45 = true := by decide
theorem ttFiber70Parent_46_ok : ttFiber70ParentCheck 46 = true := by decide
theorem ttFiber70Parent_47_ok : ttFiber70ParentCheck 47 = true := by decide
theorem ttFiber70Parent_48_ok : ttFiber70ParentCheck 48 = true := by decide
theorem ttFiber70Parent_49_ok : ttFiber70ParentCheck 49 = true := by decide
theorem ttFiber70Parent_50_ok : ttFiber70ParentCheck 50 = true := by decide
theorem ttFiber70Parent_51_ok : ttFiber70ParentCheck 51 = true := by decide
theorem ttFiber70Parent_52_ok : ttFiber70ParentCheck 52 = true := by decide
theorem ttFiber70Parent_53_ok : ttFiber70ParentCheck 53 = true := by decide
theorem ttFiber70Parent_54_ok : ttFiber70ParentCheck 54 = true := by decide
theorem ttFiber70Parent_55_ok : ttFiber70ParentCheck 55 = true := by decide
theorem ttFiber70Parent_56_ok : ttFiber70ParentCheck 56 = true := by decide
theorem ttFiber70Parent_57_ok : ttFiber70ParentCheck 57 = true := by decide
theorem ttFiber70Parent_58_ok : ttFiber70ParentCheck 58 = true := by decide
theorem ttFiber70Parent_59_ok : ttFiber70ParentCheck 59 = true := by decide
theorem ttFiber70Parent_60_ok : ttFiber70ParentCheck 60 = true := by decide
theorem ttFiber70Parent_61_ok : ttFiber70ParentCheck 61 = true := by decide
theorem ttFiber70Parent_62_ok : ttFiber70ParentCheck 62 = true := by decide
theorem ttFiber70Parent_63_ok : ttFiber70ParentCheck 63 = true := by decide

def ttFiber70CertificateAudit : Bool :=
  ttFiber70SourcesCheck &&
    ttFiber70RowCheck 0 &&
    ttFiber70RowCheck 1 &&
    ttFiber70RowCheck 2 &&
    ttFiber70RowCheck 3 &&
    ttFiber70RowCheck 4 &&
    ttFiber70RowCheck 5 &&
    ttFiber70RowCheck 6 &&
    ttFiber70RowCheck 7 &&
    ttFiber70RowCheck 8 &&
    ttFiber70RowCheck 9 &&
    ttFiber70RowCheck 10 &&
    ttFiber70RowCheck 11 &&
    ttFiber70RowCheck 12 &&
    ttFiber70RowCheck 13 &&
    ttFiber70RowCheck 14 &&
    ttFiber70RowCheck 15 &&
    ttFiber70RowCheck 16 &&
    ttFiber70RowCheck 17 &&
    ttFiber70RowCheck 18 &&
    ttFiber70RowCheck 19 &&
    ttFiber70RowCheck 20 &&
    ttFiber70RowCheck 21 &&
    ttFiber70RowCheck 22 &&
    ttFiber70RowCheck 23 &&
    ttFiber70RowCheck 24 &&
    ttFiber70RowCheck 25 &&
    ttFiber70RowCheck 26 &&
    ttFiber70RowCheck 27 &&
    ttFiber70RowCheck 28 &&
    ttFiber70RowCheck 29 &&
    ttFiber70RowCheck 30 &&
    ttFiber70RowCheck 31 &&
    ttFiber70RowCheck 32 &&
    ttFiber70RowCheck 33 &&
    ttFiber70RowCheck 34 &&
    ttFiber70RowCheck 35 &&
    ttFiber70RowCheck 36 &&
    ttFiber70RowCheck 37 &&
    ttFiber70RowCheck 38 &&
    ttFiber70RowCheck 39 &&
    ttFiber70RowCheck 40 &&
    ttFiber70RowCheck 41 &&
    ttFiber70RowCheck 42 &&
    ttFiber70RowCheck 43 &&
    ttFiber70RowCheck 44 &&
    ttFiber70RowCheck 45 &&
    ttFiber70RowCheck 46 &&
    ttFiber70RowCheck 47 &&
    ttFiber70RowCheck 48 &&
    ttFiber70RowCheck 49 &&
    ttFiber70RowCheck 50 &&
    ttFiber70RowCheck 51 &&
    ttFiber70RowCheck 52 &&
    ttFiber70RowCheck 53 &&
    ttFiber70RowCheck 54 &&
    ttFiber70RowCheck 55 &&
    ttFiber70RowCheck 56 &&
    ttFiber70RowCheck 57 &&
    ttFiber70RowCheck 58 &&
    ttFiber70RowCheck 59 &&
    ttFiber70RowCheck 60 &&
    ttFiber70RowCheck 61 &&
    ttFiber70RowCheck 62 &&
    ttFiber70RowCheck 63 &&
    ttFiber70ParentCheck 0 &&
    ttFiber70ParentCheck 1 &&
    ttFiber70ParentCheck 2 &&
    ttFiber70ParentCheck 3 &&
    ttFiber70ParentCheck 4 &&
    ttFiber70ParentCheck 5 &&
    ttFiber70ParentCheck 6 &&
    ttFiber70ParentCheck 7 &&
    ttFiber70ParentCheck 8 &&
    ttFiber70ParentCheck 9 &&
    ttFiber70ParentCheck 10 &&
    ttFiber70ParentCheck 11 &&
    ttFiber70ParentCheck 12 &&
    ttFiber70ParentCheck 13 &&
    ttFiber70ParentCheck 14 &&
    ttFiber70ParentCheck 15 &&
    ttFiber70ParentCheck 16 &&
    ttFiber70ParentCheck 17 &&
    ttFiber70ParentCheck 18 &&
    ttFiber70ParentCheck 19 &&
    ttFiber70ParentCheck 20 &&
    ttFiber70ParentCheck 21 &&
    ttFiber70ParentCheck 22 &&
    ttFiber70ParentCheck 23 &&
    ttFiber70ParentCheck 24 &&
    ttFiber70ParentCheck 25 &&
    ttFiber70ParentCheck 26 &&
    ttFiber70ParentCheck 27 &&
    ttFiber70ParentCheck 28 &&
    ttFiber70ParentCheck 29 &&
    ttFiber70ParentCheck 30 &&
    ttFiber70ParentCheck 31 &&
    ttFiber70ParentCheck 32 &&
    ttFiber70ParentCheck 33 &&
    ttFiber70ParentCheck 34 &&
    ttFiber70ParentCheck 35 &&
    ttFiber70ParentCheck 36 &&
    ttFiber70ParentCheck 37 &&
    ttFiber70ParentCheck 38 &&
    ttFiber70ParentCheck 39 &&
    ttFiber70ParentCheck 40 &&
    ttFiber70ParentCheck 41 &&
    ttFiber70ParentCheck 42 &&
    ttFiber70ParentCheck 43 &&
    ttFiber70ParentCheck 44 &&
    ttFiber70ParentCheck 45 &&
    ttFiber70ParentCheck 46 &&
    ttFiber70ParentCheck 47 &&
    ttFiber70ParentCheck 48 &&
    ttFiber70ParentCheck 49 &&
    ttFiber70ParentCheck 50 &&
    ttFiber70ParentCheck 51 &&
    ttFiber70ParentCheck 52 &&
    ttFiber70ParentCheck 53 &&
    ttFiber70ParentCheck 54 &&
    ttFiber70ParentCheck 55 &&
    ttFiber70ParentCheck 56 &&
    ttFiber70ParentCheck 57 &&
    ttFiber70ParentCheck 58 &&
    ttFiber70ParentCheck 59 &&
    ttFiber70ParentCheck 60 &&
    ttFiber70ParentCheck 61 &&
    ttFiber70ParentCheck 62 &&
    ttFiber70ParentCheck 63

theorem ttFiber70CertificateAudit_ok :
    ttFiber70CertificateAudit = true := by
  simp [ttFiber70CertificateAudit,
    ttFiber70SourcesCheck_ok,
    ttFiber70Row_0_ok,
    ttFiber70Row_1_ok,
    ttFiber70Row_2_ok,
    ttFiber70Row_3_ok,
    ttFiber70Row_4_ok,
    ttFiber70Row_5_ok,
    ttFiber70Row_6_ok,
    ttFiber70Row_7_ok,
    ttFiber70Row_8_ok,
    ttFiber70Row_9_ok,
    ttFiber70Row_10_ok,
    ttFiber70Row_11_ok,
    ttFiber70Row_12_ok,
    ttFiber70Row_13_ok,
    ttFiber70Row_14_ok,
    ttFiber70Row_15_ok,
    ttFiber70Row_16_ok,
    ttFiber70Row_17_ok,
    ttFiber70Row_18_ok,
    ttFiber70Row_19_ok,
    ttFiber70Row_20_ok,
    ttFiber70Row_21_ok,
    ttFiber70Row_22_ok,
    ttFiber70Row_23_ok,
    ttFiber70Row_24_ok,
    ttFiber70Row_25_ok,
    ttFiber70Row_26_ok,
    ttFiber70Row_27_ok,
    ttFiber70Row_28_ok,
    ttFiber70Row_29_ok,
    ttFiber70Row_30_ok,
    ttFiber70Row_31_ok,
    ttFiber70Row_32_ok,
    ttFiber70Row_33_ok,
    ttFiber70Row_34_ok,
    ttFiber70Row_35_ok,
    ttFiber70Row_36_ok,
    ttFiber70Row_37_ok,
    ttFiber70Row_38_ok,
    ttFiber70Row_39_ok,
    ttFiber70Row_40_ok,
    ttFiber70Row_41_ok,
    ttFiber70Row_42_ok,
    ttFiber70Row_43_ok,
    ttFiber70Row_44_ok,
    ttFiber70Row_45_ok,
    ttFiber70Row_46_ok,
    ttFiber70Row_47_ok,
    ttFiber70Row_48_ok,
    ttFiber70Row_49_ok,
    ttFiber70Row_50_ok,
    ttFiber70Row_51_ok,
    ttFiber70Row_52_ok,
    ttFiber70Row_53_ok,
    ttFiber70Row_54_ok,
    ttFiber70Row_55_ok,
    ttFiber70Row_56_ok,
    ttFiber70Row_57_ok,
    ttFiber70Row_58_ok,
    ttFiber70Row_59_ok,
    ttFiber70Row_60_ok,
    ttFiber70Row_61_ok,
    ttFiber70Row_62_ok,
    ttFiber70Row_63_ok,
    ttFiber70Parent_0_ok,
    ttFiber70Parent_1_ok,
    ttFiber70Parent_2_ok,
    ttFiber70Parent_3_ok,
    ttFiber70Parent_4_ok,
    ttFiber70Parent_5_ok,
    ttFiber70Parent_6_ok,
    ttFiber70Parent_7_ok,
    ttFiber70Parent_8_ok,
    ttFiber70Parent_9_ok,
    ttFiber70Parent_10_ok,
    ttFiber70Parent_11_ok,
    ttFiber70Parent_12_ok,
    ttFiber70Parent_13_ok,
    ttFiber70Parent_14_ok,
    ttFiber70Parent_15_ok,
    ttFiber70Parent_16_ok,
    ttFiber70Parent_17_ok,
    ttFiber70Parent_18_ok,
    ttFiber70Parent_19_ok,
    ttFiber70Parent_20_ok,
    ttFiber70Parent_21_ok,
    ttFiber70Parent_22_ok,
    ttFiber70Parent_23_ok,
    ttFiber70Parent_24_ok,
    ttFiber70Parent_25_ok,
    ttFiber70Parent_26_ok,
    ttFiber70Parent_27_ok,
    ttFiber70Parent_28_ok,
    ttFiber70Parent_29_ok,
    ttFiber70Parent_30_ok,
    ttFiber70Parent_31_ok,
    ttFiber70Parent_32_ok,
    ttFiber70Parent_33_ok,
    ttFiber70Parent_34_ok,
    ttFiber70Parent_35_ok,
    ttFiber70Parent_36_ok,
    ttFiber70Parent_37_ok,
    ttFiber70Parent_38_ok,
    ttFiber70Parent_39_ok,
    ttFiber70Parent_40_ok,
    ttFiber70Parent_41_ok,
    ttFiber70Parent_42_ok,
    ttFiber70Parent_43_ok,
    ttFiber70Parent_44_ok,
    ttFiber70Parent_45_ok,
    ttFiber70Parent_46_ok,
    ttFiber70Parent_47_ok,
    ttFiber70Parent_48_ok,
    ttFiber70Parent_49_ok,
    ttFiber70Parent_50_ok,
    ttFiber70Parent_51_ok,
    ttFiber70Parent_52_ok,
    ttFiber70Parent_53_ok,
    ttFiber70Parent_54_ok,
    ttFiber70Parent_55_ok,
    ttFiber70Parent_56_ok,
    ttFiber70Parent_57_ok,
    ttFiber70Parent_58_ok,
    ttFiber70Parent_59_ok,
    ttFiber70Parent_60_ok,
    ttFiber70Parent_61_ok,
    ttFiber70Parent_62_ok,
    ttFiber70Parent_63_ok]

def ttFiber71Key : List LColor :=
  [LColor.p, LColor.b, LColor.p, LColor.p]

def ttFiber71Expected : List Nat :=
  [432, 433, 434, 435, 436, 437, 438, 439]

def ttFiber71Rows : List DirectChainParentRow :=
  [ directRow 432 432 84 144 84 144 default
  , directRow 433 432 84 145 84 144 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 434 433 84 146 84 145 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 435 432 84 147 84 144 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 436 432 85 152 84 144 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 437 433 85 153 84 145 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 438 434 85 154 84 146 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 439 435 85 155 84 147 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  ]

def ttFiber71RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber71Rows i default

def ttFiber71SourcesCheck : Bool :=
  (ttFiber71Rows.map fun row => row.source) == ttFiber71Expected

theorem ttFiber71SourcesCheck_ok :
    ttFiber71SourcesCheck = true := by
  decide

def ttFiber71RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber71Key ttFiber71Expected (ttFiber71RowAt i)

theorem ttFiber71Row_0_ok : ttFiber71RowCheck 0 = true := by decide
theorem ttFiber71Row_1_ok : ttFiber71RowCheck 1 = true := by decide
theorem ttFiber71Row_2_ok : ttFiber71RowCheck 2 = true := by decide
theorem ttFiber71Row_3_ok : ttFiber71RowCheck 3 = true := by decide
theorem ttFiber71Row_4_ok : ttFiber71RowCheck 4 = true := by decide
theorem ttFiber71Row_5_ok : ttFiber71RowCheck 5 = true := by decide
theorem ttFiber71Row_6_ok : ttFiber71RowCheck 6 = true := by decide
theorem ttFiber71Row_7_ok : ttFiber71RowCheck 7 = true := by decide

def ttFiber71ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber71Rows ttMaxParentDepth (listGetD ttFiber71Expected i 0) == 432

theorem ttFiber71Parent_0_ok : ttFiber71ParentCheck 0 = true := by decide
theorem ttFiber71Parent_1_ok : ttFiber71ParentCheck 1 = true := by decide
theorem ttFiber71Parent_2_ok : ttFiber71ParentCheck 2 = true := by decide
theorem ttFiber71Parent_3_ok : ttFiber71ParentCheck 3 = true := by decide
theorem ttFiber71Parent_4_ok : ttFiber71ParentCheck 4 = true := by decide
theorem ttFiber71Parent_5_ok : ttFiber71ParentCheck 5 = true := by decide
theorem ttFiber71Parent_6_ok : ttFiber71ParentCheck 6 = true := by decide
theorem ttFiber71Parent_7_ok : ttFiber71ParentCheck 7 = true := by decide

def ttFiber71CertificateAudit : Bool :=
  ttFiber71SourcesCheck &&
    ttFiber71RowCheck 0 &&
    ttFiber71RowCheck 1 &&
    ttFiber71RowCheck 2 &&
    ttFiber71RowCheck 3 &&
    ttFiber71RowCheck 4 &&
    ttFiber71RowCheck 5 &&
    ttFiber71RowCheck 6 &&
    ttFiber71RowCheck 7 &&
    ttFiber71ParentCheck 0 &&
    ttFiber71ParentCheck 1 &&
    ttFiber71ParentCheck 2 &&
    ttFiber71ParentCheck 3 &&
    ttFiber71ParentCheck 4 &&
    ttFiber71ParentCheck 5 &&
    ttFiber71ParentCheck 6 &&
    ttFiber71ParentCheck 7

theorem ttFiber71CertificateAudit_ok :
    ttFiber71CertificateAudit = true := by
  simp [ttFiber71CertificateAudit,
    ttFiber71SourcesCheck_ok,
    ttFiber71Row_0_ok,
    ttFiber71Row_1_ok,
    ttFiber71Row_2_ok,
    ttFiber71Row_3_ok,
    ttFiber71Row_4_ok,
    ttFiber71Row_5_ok,
    ttFiber71Row_6_ok,
    ttFiber71Row_7_ok,
    ttFiber71Parent_0_ok,
    ttFiber71Parent_1_ok,
    ttFiber71Parent_2_ok,
    ttFiber71Parent_3_ok,
    ttFiber71Parent_4_ok,
    ttFiber71Parent_5_ok,
    ttFiber71Parent_6_ok,
    ttFiber71Parent_7_ok]

def ttFiber72Key : List LColor :=
  [LColor.p, LColor.p, LColor.r, LColor.r]

def ttFiber72Expected : List Nat :=
  [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231]

def ttFiber72Rows : List DirectChainParentRow :=
  [ directRow 120 120 24 80 24 80 default
  , directRow 121 120 24 81 24 80 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 122 120 24 82 24 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 123 121 24 83 24 81 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 124 122 24 100 24 82 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 125 127 24 101 24 103 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 126 121 24 102 24 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 127 120 24 103 24 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 128 120 25 88 24 80 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 129 121 25 89 24 81 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 130 122 25 90 24 82 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 131 123 25 91 24 83 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 132 124 25 108 24 100 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 133 125 25 109 24 101 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 134 126 25 110 24 102 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 135 127 25 111 24 103 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 136 120 26 16 24 80 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 137 121 26 17 24 81 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 138 122 26 18 24 82 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 139 123 26 19 24 83 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 140 136 26 32 26 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 141 137 26 33 26 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 142 126 26 34 24 102 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 143 127 26 35 24 103 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 144 128 27 24 25 88 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 145 129 27 25 25 89 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 146 130 27 26 25 90 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 147 131 27 27 25 91 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 148 144 27 40 27 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 149 145 27 41 27 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 150 134 27 42 25 110 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 151 135 27 43 25 111 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 200 120 40 148 24 80 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 201 121 40 149 24 81 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 202 122 40 150 24 82 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 203 200 40 151 40 148 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 204 200 40 164 40 148 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 205 201 40 165 40 149 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 206 126 40 166 24 102 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 207 127 40 167 24 103 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 208 128 41 156 25 88 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 209 129 41 157 25 89 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 210 130 41 158 25 90 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 211 208 41 159 41 156 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 212 208 41 172 41 156 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 213 209 41 173 41 157 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 214 134 41 174 25 110 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 215 135 41 175 25 111 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 216 136 42 0 26 16 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 217 137 42 1 26 17 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 218 138 42 2 26 18 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 219 139 42 3 26 19 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 220 208 42 48 41 156 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 221 209 42 49 41 157 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 222 142 42 50 26 34 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 223 143 42 51 26 35 (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
  , directRow 224 207 43 8 40 167 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 225 206 43 9 40 166 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 226 204 43 10 40 164 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 227 205 43 11 40 165 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 228 200 43 56 40 148 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 229 201 43 57 40 149 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 230 202 43 58 40 150 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  , directRow 231 203 43 59 40 151 (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
  ]

def ttFiber72RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber72Rows i default

def ttFiber72SourcesCheck : Bool :=
  (ttFiber72Rows.map fun row => row.source) == ttFiber72Expected

theorem ttFiber72SourcesCheck_ok :
    ttFiber72SourcesCheck = true := by
  decide

def ttFiber72RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt i)

theorem ttFiber72Row_0_ok : ttFiber72RowCheck 0 = true := by decide
theorem ttFiber72Row_1_ok : ttFiber72RowCheck 1 = true := by decide
theorem ttFiber72Row_2_ok : ttFiber72RowCheck 2 = true := by decide
theorem ttFiber72Row_3_ok : ttFiber72RowCheck 3 = true := by decide
theorem ttFiber72Row_4_ok : ttFiber72RowCheck 4 = true := by decide
theorem ttFiber72Row_5_ok : ttFiber72RowCheck 5 = true := by decide
theorem ttFiber72Row_6_ok : ttFiber72RowCheck 6 = true := by decide
theorem ttFiber72Row_7_ok : ttFiber72RowCheck 7 = true := by decide
theorem ttFiber72Row_8_ok : ttFiber72RowCheck 8 = true := by decide
theorem ttFiber72Row_9_ok : ttFiber72RowCheck 9 = true := by decide
theorem ttFiber72Row_10_ok : ttFiber72RowCheck 10 = true := by decide
theorem ttFiber72Row_11_ok : ttFiber72RowCheck 11 = true := by decide
theorem ttFiber72Row_12_ok : ttFiber72RowCheck 12 = true := by decide
theorem ttFiber72Row_13_ok : ttFiber72RowCheck 13 = true := by decide
theorem ttFiber72Row_14_ok : ttFiber72RowCheck 14 = true := by decide
theorem ttFiber72Row_15_ok : ttFiber72RowCheck 15 = true := by decide
theorem ttFiber72Row_16_ok : ttFiber72RowCheck 16 = true := by decide
theorem ttFiber72Row_17_ok : ttFiber72RowCheck 17 = true := by decide
theorem ttFiber72Row_18_ok : ttFiber72RowCheck 18 = true := by decide
theorem ttFiber72Row_19_ok : ttFiber72RowCheck 19 = true := by decide
theorem ttFiber72Row_20_ok : ttFiber72RowCheck 20 = true := by decide
theorem ttFiber72Row_21_ok : ttFiber72RowCheck 21 = true := by decide
theorem ttFiber72Row_22_ok : ttFiber72RowCheck 22 = true := by decide
theorem ttFiber72Row_23_ok : ttFiber72RowCheck 23 = true := by decide
theorem ttFiber72Row_24_ok : ttFiber72RowCheck 24 = true := by decide
theorem ttFiber72Row_25_ok : ttFiber72RowCheck 25 = true := by decide
theorem ttFiber72Row_26_ok : ttFiber72RowCheck 26 = true := by decide
theorem ttFiber72Row_27_ok : ttFiber72RowCheck 27 = true := by decide
theorem ttFiber72Row_28_ok : ttFiber72RowCheck 28 = true := by decide
theorem ttFiber72Row_29_ok : ttFiber72RowCheck 29 = true := by decide
theorem ttFiber72Row_30_ok : ttFiber72RowCheck 30 = true := by decide
theorem ttFiber72Row_31_ok : ttFiber72RowCheck 31 = true := by decide
theorem ttFiber72Row_32_ok : ttFiber72RowCheck 32 = true := by decide
theorem ttFiber72Row_33_ok : ttFiber72RowCheck 33 = true := by decide
theorem ttFiber72Row_34_ok : ttFiber72RowCheck 34 = true := by decide
theorem ttFiber72Row_35_ok : ttFiber72RowCheck 35 = true := by decide
theorem ttFiber72Row_36_ok : ttFiber72RowCheck 36 = true := by decide
theorem ttFiber72Row_37_ok : ttFiber72RowCheck 37 = true := by decide
theorem ttFiber72Row_38_ok : ttFiber72RowCheck 38 = true := by decide
theorem ttFiber72Row_39_ok : ttFiber72RowCheck 39 = true := by decide
theorem ttFiber72Row_40_ok : ttFiber72RowCheck 40 = true := by decide
theorem ttFiber72Row_41_ok : ttFiber72RowCheck 41 = true := by decide
theorem ttFiber72Row_42_ok : ttFiber72RowCheck 42 = true := by decide
theorem ttFiber72Row_43_ok : ttFiber72RowCheck 43 = true := by decide
theorem ttFiber72Row_44_ok : ttFiber72RowCheck 44 = true := by decide
theorem ttFiber72Row_45_ok : ttFiber72RowCheck 45 = true := by decide
theorem ttFiber72Row_46_ok : ttFiber72RowCheck 46 = true := by decide
theorem ttFiber72Row_47_ok : ttFiber72RowCheck 47 = true := by decide
theorem ttFiber72Row_48_ok : ttFiber72RowCheck 48 = true := by decide
theorem ttFiber72Row_49_ok : ttFiber72RowCheck 49 = true := by decide
theorem ttFiber72Row_50_ok : ttFiber72RowCheck 50 = true := by decide
theorem ttFiber72Row_51_ok : ttFiber72RowCheck 51 = true := by decide
theorem ttFiber72Row_52_ok : ttFiber72RowCheck 52 = true := by decide
theorem ttFiber72Row_53_ok : ttFiber72RowCheck 53 = true := by decide
theorem ttFiber72Row_54_ok : ttFiber72RowCheck 54 = true := by decide
theorem ttFiber72Row_55_ok : ttFiber72RowCheck 55 = true := by decide
theorem ttFiber72Row_56_ok : ttFiber72RowCheck 56 = true := by decide
theorem ttFiber72Row_57_ok : ttFiber72RowCheck 57 = true := by decide
theorem ttFiber72Row_58_ok : ttFiber72RowCheck 58 = true := by decide
theorem ttFiber72Row_59_ok : ttFiber72RowCheck 59 = true := by decide
theorem ttFiber72Row_60_ok : ttFiber72RowCheck 60 = true := by decide
theorem ttFiber72Row_61_ok : ttFiber72RowCheck 61 = true := by decide
theorem ttFiber72Row_62_ok : ttFiber72RowCheck 62 = true := by decide
theorem ttFiber72Row_63_ok : ttFiber72RowCheck 63 = true := by decide

def ttFiber72ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber72Rows ttMaxParentDepth (listGetD ttFiber72Expected i 0) == 120

theorem ttFiber72Parent_0_ok : ttFiber72ParentCheck 0 = true := by decide
theorem ttFiber72Parent_1_ok : ttFiber72ParentCheck 1 = true := by decide
theorem ttFiber72Parent_2_ok : ttFiber72ParentCheck 2 = true := by decide
theorem ttFiber72Parent_3_ok : ttFiber72ParentCheck 3 = true := by decide
theorem ttFiber72Parent_4_ok : ttFiber72ParentCheck 4 = true := by decide
theorem ttFiber72Parent_5_ok : ttFiber72ParentCheck 5 = true := by decide
theorem ttFiber72Parent_6_ok : ttFiber72ParentCheck 6 = true := by decide
theorem ttFiber72Parent_7_ok : ttFiber72ParentCheck 7 = true := by decide
theorem ttFiber72Parent_8_ok : ttFiber72ParentCheck 8 = true := by decide
theorem ttFiber72Parent_9_ok : ttFiber72ParentCheck 9 = true := by decide
theorem ttFiber72Parent_10_ok : ttFiber72ParentCheck 10 = true := by decide
theorem ttFiber72Parent_11_ok : ttFiber72ParentCheck 11 = true := by decide
theorem ttFiber72Parent_12_ok : ttFiber72ParentCheck 12 = true := by decide
theorem ttFiber72Parent_13_ok : ttFiber72ParentCheck 13 = true := by decide
theorem ttFiber72Parent_14_ok : ttFiber72ParentCheck 14 = true := by decide
theorem ttFiber72Parent_15_ok : ttFiber72ParentCheck 15 = true := by decide
theorem ttFiber72Parent_16_ok : ttFiber72ParentCheck 16 = true := by decide
theorem ttFiber72Parent_17_ok : ttFiber72ParentCheck 17 = true := by decide
theorem ttFiber72Parent_18_ok : ttFiber72ParentCheck 18 = true := by decide
theorem ttFiber72Parent_19_ok : ttFiber72ParentCheck 19 = true := by decide
theorem ttFiber72Parent_20_ok : ttFiber72ParentCheck 20 = true := by decide
theorem ttFiber72Parent_21_ok : ttFiber72ParentCheck 21 = true := by decide
theorem ttFiber72Parent_22_ok : ttFiber72ParentCheck 22 = true := by decide
theorem ttFiber72Parent_23_ok : ttFiber72ParentCheck 23 = true := by decide
theorem ttFiber72Parent_24_ok : ttFiber72ParentCheck 24 = true := by decide
theorem ttFiber72Parent_25_ok : ttFiber72ParentCheck 25 = true := by decide
theorem ttFiber72Parent_26_ok : ttFiber72ParentCheck 26 = true := by decide
theorem ttFiber72Parent_27_ok : ttFiber72ParentCheck 27 = true := by decide
theorem ttFiber72Parent_28_ok : ttFiber72ParentCheck 28 = true := by decide
theorem ttFiber72Parent_29_ok : ttFiber72ParentCheck 29 = true := by decide
theorem ttFiber72Parent_30_ok : ttFiber72ParentCheck 30 = true := by decide
theorem ttFiber72Parent_31_ok : ttFiber72ParentCheck 31 = true := by decide
theorem ttFiber72Parent_32_ok : ttFiber72ParentCheck 32 = true := by decide
theorem ttFiber72Parent_33_ok : ttFiber72ParentCheck 33 = true := by decide
theorem ttFiber72Parent_34_ok : ttFiber72ParentCheck 34 = true := by decide
theorem ttFiber72Parent_35_ok : ttFiber72ParentCheck 35 = true := by decide
theorem ttFiber72Parent_36_ok : ttFiber72ParentCheck 36 = true := by decide
theorem ttFiber72Parent_37_ok : ttFiber72ParentCheck 37 = true := by decide
theorem ttFiber72Parent_38_ok : ttFiber72ParentCheck 38 = true := by decide
theorem ttFiber72Parent_39_ok : ttFiber72ParentCheck 39 = true := by decide
theorem ttFiber72Parent_40_ok : ttFiber72ParentCheck 40 = true := by decide
theorem ttFiber72Parent_41_ok : ttFiber72ParentCheck 41 = true := by decide
theorem ttFiber72Parent_42_ok : ttFiber72ParentCheck 42 = true := by decide
theorem ttFiber72Parent_43_ok : ttFiber72ParentCheck 43 = true := by decide
theorem ttFiber72Parent_44_ok : ttFiber72ParentCheck 44 = true := by decide
theorem ttFiber72Parent_45_ok : ttFiber72ParentCheck 45 = true := by decide
theorem ttFiber72Parent_46_ok : ttFiber72ParentCheck 46 = true := by decide
theorem ttFiber72Parent_47_ok : ttFiber72ParentCheck 47 = true := by decide
theorem ttFiber72Parent_48_ok : ttFiber72ParentCheck 48 = true := by decide
theorem ttFiber72Parent_49_ok : ttFiber72ParentCheck 49 = true := by decide
theorem ttFiber72Parent_50_ok : ttFiber72ParentCheck 50 = true := by decide
theorem ttFiber72Parent_51_ok : ttFiber72ParentCheck 51 = true := by decide
theorem ttFiber72Parent_52_ok : ttFiber72ParentCheck 52 = true := by decide
theorem ttFiber72Parent_53_ok : ttFiber72ParentCheck 53 = true := by decide
theorem ttFiber72Parent_54_ok : ttFiber72ParentCheck 54 = true := by decide
theorem ttFiber72Parent_55_ok : ttFiber72ParentCheck 55 = true := by decide
theorem ttFiber72Parent_56_ok : ttFiber72ParentCheck 56 = true := by decide
theorem ttFiber72Parent_57_ok : ttFiber72ParentCheck 57 = true := by decide
theorem ttFiber72Parent_58_ok : ttFiber72ParentCheck 58 = true := by decide
theorem ttFiber72Parent_59_ok : ttFiber72ParentCheck 59 = true := by decide
theorem ttFiber72Parent_60_ok : ttFiber72ParentCheck 60 = true := by decide
theorem ttFiber72Parent_61_ok : ttFiber72ParentCheck 61 = true := by decide
theorem ttFiber72Parent_62_ok : ttFiber72ParentCheck 62 = true := by decide
theorem ttFiber72Parent_63_ok : ttFiber72ParentCheck 63 = true := by decide

def ttFiber72CertificateAudit : Bool :=
  ttFiber72SourcesCheck &&
    ttFiber72RowCheck 0 &&
    ttFiber72RowCheck 1 &&
    ttFiber72RowCheck 2 &&
    ttFiber72RowCheck 3 &&
    ttFiber72RowCheck 4 &&
    ttFiber72RowCheck 5 &&
    ttFiber72RowCheck 6 &&
    ttFiber72RowCheck 7 &&
    ttFiber72RowCheck 8 &&
    ttFiber72RowCheck 9 &&
    ttFiber72RowCheck 10 &&
    ttFiber72RowCheck 11 &&
    ttFiber72RowCheck 12 &&
    ttFiber72RowCheck 13 &&
    ttFiber72RowCheck 14 &&
    ttFiber72RowCheck 15 &&
    ttFiber72RowCheck 16 &&
    ttFiber72RowCheck 17 &&
    ttFiber72RowCheck 18 &&
    ttFiber72RowCheck 19 &&
    ttFiber72RowCheck 20 &&
    ttFiber72RowCheck 21 &&
    ttFiber72RowCheck 22 &&
    ttFiber72RowCheck 23 &&
    ttFiber72RowCheck 24 &&
    ttFiber72RowCheck 25 &&
    ttFiber72RowCheck 26 &&
    ttFiber72RowCheck 27 &&
    ttFiber72RowCheck 28 &&
    ttFiber72RowCheck 29 &&
    ttFiber72RowCheck 30 &&
    ttFiber72RowCheck 31 &&
    ttFiber72RowCheck 32 &&
    ttFiber72RowCheck 33 &&
    ttFiber72RowCheck 34 &&
    ttFiber72RowCheck 35 &&
    ttFiber72RowCheck 36 &&
    ttFiber72RowCheck 37 &&
    ttFiber72RowCheck 38 &&
    ttFiber72RowCheck 39 &&
    ttFiber72RowCheck 40 &&
    ttFiber72RowCheck 41 &&
    ttFiber72RowCheck 42 &&
    ttFiber72RowCheck 43 &&
    ttFiber72RowCheck 44 &&
    ttFiber72RowCheck 45 &&
    ttFiber72RowCheck 46 &&
    ttFiber72RowCheck 47 &&
    ttFiber72RowCheck 48 &&
    ttFiber72RowCheck 49 &&
    ttFiber72RowCheck 50 &&
    ttFiber72RowCheck 51 &&
    ttFiber72RowCheck 52 &&
    ttFiber72RowCheck 53 &&
    ttFiber72RowCheck 54 &&
    ttFiber72RowCheck 55 &&
    ttFiber72RowCheck 56 &&
    ttFiber72RowCheck 57 &&
    ttFiber72RowCheck 58 &&
    ttFiber72RowCheck 59 &&
    ttFiber72RowCheck 60 &&
    ttFiber72RowCheck 61 &&
    ttFiber72RowCheck 62 &&
    ttFiber72RowCheck 63 &&
    ttFiber72ParentCheck 0 &&
    ttFiber72ParentCheck 1 &&
    ttFiber72ParentCheck 2 &&
    ttFiber72ParentCheck 3 &&
    ttFiber72ParentCheck 4 &&
    ttFiber72ParentCheck 5 &&
    ttFiber72ParentCheck 6 &&
    ttFiber72ParentCheck 7 &&
    ttFiber72ParentCheck 8 &&
    ttFiber72ParentCheck 9 &&
    ttFiber72ParentCheck 10 &&
    ttFiber72ParentCheck 11 &&
    ttFiber72ParentCheck 12 &&
    ttFiber72ParentCheck 13 &&
    ttFiber72ParentCheck 14 &&
    ttFiber72ParentCheck 15 &&
    ttFiber72ParentCheck 16 &&
    ttFiber72ParentCheck 17 &&
    ttFiber72ParentCheck 18 &&
    ttFiber72ParentCheck 19 &&
    ttFiber72ParentCheck 20 &&
    ttFiber72ParentCheck 21 &&
    ttFiber72ParentCheck 22 &&
    ttFiber72ParentCheck 23 &&
    ttFiber72ParentCheck 24 &&
    ttFiber72ParentCheck 25 &&
    ttFiber72ParentCheck 26 &&
    ttFiber72ParentCheck 27 &&
    ttFiber72ParentCheck 28 &&
    ttFiber72ParentCheck 29 &&
    ttFiber72ParentCheck 30 &&
    ttFiber72ParentCheck 31 &&
    ttFiber72ParentCheck 32 &&
    ttFiber72ParentCheck 33 &&
    ttFiber72ParentCheck 34 &&
    ttFiber72ParentCheck 35 &&
    ttFiber72ParentCheck 36 &&
    ttFiber72ParentCheck 37 &&
    ttFiber72ParentCheck 38 &&
    ttFiber72ParentCheck 39 &&
    ttFiber72ParentCheck 40 &&
    ttFiber72ParentCheck 41 &&
    ttFiber72ParentCheck 42 &&
    ttFiber72ParentCheck 43 &&
    ttFiber72ParentCheck 44 &&
    ttFiber72ParentCheck 45 &&
    ttFiber72ParentCheck 46 &&
    ttFiber72ParentCheck 47 &&
    ttFiber72ParentCheck 48 &&
    ttFiber72ParentCheck 49 &&
    ttFiber72ParentCheck 50 &&
    ttFiber72ParentCheck 51 &&
    ttFiber72ParentCheck 52 &&
    ttFiber72ParentCheck 53 &&
    ttFiber72ParentCheck 54 &&
    ttFiber72ParentCheck 55 &&
    ttFiber72ParentCheck 56 &&
    ttFiber72ParentCheck 57 &&
    ttFiber72ParentCheck 58 &&
    ttFiber72ParentCheck 59 &&
    ttFiber72ParentCheck 60 &&
    ttFiber72ParentCheck 61 &&
    ttFiber72ParentCheck 62 &&
    ttFiber72ParentCheck 63

theorem ttFiber72CertificateAudit_ok :
    ttFiber72CertificateAudit = true := by
  simp [ttFiber72CertificateAudit,
    ttFiber72SourcesCheck_ok,
    ttFiber72Row_0_ok,
    ttFiber72Row_1_ok,
    ttFiber72Row_2_ok,
    ttFiber72Row_3_ok,
    ttFiber72Row_4_ok,
    ttFiber72Row_5_ok,
    ttFiber72Row_6_ok,
    ttFiber72Row_7_ok,
    ttFiber72Row_8_ok,
    ttFiber72Row_9_ok,
    ttFiber72Row_10_ok,
    ttFiber72Row_11_ok,
    ttFiber72Row_12_ok,
    ttFiber72Row_13_ok,
    ttFiber72Row_14_ok,
    ttFiber72Row_15_ok,
    ttFiber72Row_16_ok,
    ttFiber72Row_17_ok,
    ttFiber72Row_18_ok,
    ttFiber72Row_19_ok,
    ttFiber72Row_20_ok,
    ttFiber72Row_21_ok,
    ttFiber72Row_22_ok,
    ttFiber72Row_23_ok,
    ttFiber72Row_24_ok,
    ttFiber72Row_25_ok,
    ttFiber72Row_26_ok,
    ttFiber72Row_27_ok,
    ttFiber72Row_28_ok,
    ttFiber72Row_29_ok,
    ttFiber72Row_30_ok,
    ttFiber72Row_31_ok,
    ttFiber72Row_32_ok,
    ttFiber72Row_33_ok,
    ttFiber72Row_34_ok,
    ttFiber72Row_35_ok,
    ttFiber72Row_36_ok,
    ttFiber72Row_37_ok,
    ttFiber72Row_38_ok,
    ttFiber72Row_39_ok,
    ttFiber72Row_40_ok,
    ttFiber72Row_41_ok,
    ttFiber72Row_42_ok,
    ttFiber72Row_43_ok,
    ttFiber72Row_44_ok,
    ttFiber72Row_45_ok,
    ttFiber72Row_46_ok,
    ttFiber72Row_47_ok,
    ttFiber72Row_48_ok,
    ttFiber72Row_49_ok,
    ttFiber72Row_50_ok,
    ttFiber72Row_51_ok,
    ttFiber72Row_52_ok,
    ttFiber72Row_53_ok,
    ttFiber72Row_54_ok,
    ttFiber72Row_55_ok,
    ttFiber72Row_56_ok,
    ttFiber72Row_57_ok,
    ttFiber72Row_58_ok,
    ttFiber72Row_59_ok,
    ttFiber72Row_60_ok,
    ttFiber72Row_61_ok,
    ttFiber72Row_62_ok,
    ttFiber72Row_63_ok,
    ttFiber72Parent_0_ok,
    ttFiber72Parent_1_ok,
    ttFiber72Parent_2_ok,
    ttFiber72Parent_3_ok,
    ttFiber72Parent_4_ok,
    ttFiber72Parent_5_ok,
    ttFiber72Parent_6_ok,
    ttFiber72Parent_7_ok,
    ttFiber72Parent_8_ok,
    ttFiber72Parent_9_ok,
    ttFiber72Parent_10_ok,
    ttFiber72Parent_11_ok,
    ttFiber72Parent_12_ok,
    ttFiber72Parent_13_ok,
    ttFiber72Parent_14_ok,
    ttFiber72Parent_15_ok,
    ttFiber72Parent_16_ok,
    ttFiber72Parent_17_ok,
    ttFiber72Parent_18_ok,
    ttFiber72Parent_19_ok,
    ttFiber72Parent_20_ok,
    ttFiber72Parent_21_ok,
    ttFiber72Parent_22_ok,
    ttFiber72Parent_23_ok,
    ttFiber72Parent_24_ok,
    ttFiber72Parent_25_ok,
    ttFiber72Parent_26_ok,
    ttFiber72Parent_27_ok,
    ttFiber72Parent_28_ok,
    ttFiber72Parent_29_ok,
    ttFiber72Parent_30_ok,
    ttFiber72Parent_31_ok,
    ttFiber72Parent_32_ok,
    ttFiber72Parent_33_ok,
    ttFiber72Parent_34_ok,
    ttFiber72Parent_35_ok,
    ttFiber72Parent_36_ok,
    ttFiber72Parent_37_ok,
    ttFiber72Parent_38_ok,
    ttFiber72Parent_39_ok,
    ttFiber72Parent_40_ok,
    ttFiber72Parent_41_ok,
    ttFiber72Parent_42_ok,
    ttFiber72Parent_43_ok,
    ttFiber72Parent_44_ok,
    ttFiber72Parent_45_ok,
    ttFiber72Parent_46_ok,
    ttFiber72Parent_47_ok,
    ttFiber72Parent_48_ok,
    ttFiber72Parent_49_ok,
    ttFiber72Parent_50_ok,
    ttFiber72Parent_51_ok,
    ttFiber72Parent_52_ok,
    ttFiber72Parent_53_ok,
    ttFiber72Parent_54_ok,
    ttFiber72Parent_55_ok,
    ttFiber72Parent_56_ok,
    ttFiber72Parent_57_ok,
    ttFiber72Parent_58_ok,
    ttFiber72Parent_59_ok,
    ttFiber72Parent_60_ok,
    ttFiber72Parent_61_ok,
    ttFiber72Parent_62_ok,
    ttFiber72Parent_63_ok]

def ttFiber73Key : List LColor :=
  [LColor.p, LColor.p, LColor.r, LColor.b]

def ttFiber73Expected : List Nat :=
  [232, 233, 234, 235, 236, 237, 238, 239]

def ttFiber73Rows : List DirectChainParentRow :=
  [ directRow 232 232 46 112 46 112 default
  , directRow 233 232 46 113 46 112 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 234 232 46 114 46 112 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 235 233 46 115 46 113 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 236 232 47 120 46 112 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 237 233 47 121 46 113 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 238 234 47 122 46 114 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 239 235 47 123 46 115 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  ]

def ttFiber73RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber73Rows i default

def ttFiber73SourcesCheck : Bool :=
  (ttFiber73Rows.map fun row => row.source) == ttFiber73Expected

theorem ttFiber73SourcesCheck_ok :
    ttFiber73SourcesCheck = true := by
  decide

def ttFiber73RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber73Key ttFiber73Expected (ttFiber73RowAt i)

theorem ttFiber73Row_0_ok : ttFiber73RowCheck 0 = true := by decide
theorem ttFiber73Row_1_ok : ttFiber73RowCheck 1 = true := by decide
theorem ttFiber73Row_2_ok : ttFiber73RowCheck 2 = true := by decide
theorem ttFiber73Row_3_ok : ttFiber73RowCheck 3 = true := by decide
theorem ttFiber73Row_4_ok : ttFiber73RowCheck 4 = true := by decide
theorem ttFiber73Row_5_ok : ttFiber73RowCheck 5 = true := by decide
theorem ttFiber73Row_6_ok : ttFiber73RowCheck 6 = true := by decide
theorem ttFiber73Row_7_ok : ttFiber73RowCheck 7 = true := by decide

def ttFiber73ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber73Rows ttMaxParentDepth (listGetD ttFiber73Expected i 0) == 232

theorem ttFiber73Parent_0_ok : ttFiber73ParentCheck 0 = true := by decide
theorem ttFiber73Parent_1_ok : ttFiber73ParentCheck 1 = true := by decide
theorem ttFiber73Parent_2_ok : ttFiber73ParentCheck 2 = true := by decide
theorem ttFiber73Parent_3_ok : ttFiber73ParentCheck 3 = true := by decide
theorem ttFiber73Parent_4_ok : ttFiber73ParentCheck 4 = true := by decide
theorem ttFiber73Parent_5_ok : ttFiber73ParentCheck 5 = true := by decide
theorem ttFiber73Parent_6_ok : ttFiber73ParentCheck 6 = true := by decide
theorem ttFiber73Parent_7_ok : ttFiber73ParentCheck 7 = true := by decide

def ttFiber73CertificateAudit : Bool :=
  ttFiber73SourcesCheck &&
    ttFiber73RowCheck 0 &&
    ttFiber73RowCheck 1 &&
    ttFiber73RowCheck 2 &&
    ttFiber73RowCheck 3 &&
    ttFiber73RowCheck 4 &&
    ttFiber73RowCheck 5 &&
    ttFiber73RowCheck 6 &&
    ttFiber73RowCheck 7 &&
    ttFiber73ParentCheck 0 &&
    ttFiber73ParentCheck 1 &&
    ttFiber73ParentCheck 2 &&
    ttFiber73ParentCheck 3 &&
    ttFiber73ParentCheck 4 &&
    ttFiber73ParentCheck 5 &&
    ttFiber73ParentCheck 6 &&
    ttFiber73ParentCheck 7

theorem ttFiber73CertificateAudit_ok :
    ttFiber73CertificateAudit = true := by
  simp [ttFiber73CertificateAudit,
    ttFiber73SourcesCheck_ok,
    ttFiber73Row_0_ok,
    ttFiber73Row_1_ok,
    ttFiber73Row_2_ok,
    ttFiber73Row_3_ok,
    ttFiber73Row_4_ok,
    ttFiber73Row_5_ok,
    ttFiber73Row_6_ok,
    ttFiber73Row_7_ok,
    ttFiber73Parent_0_ok,
    ttFiber73Parent_1_ok,
    ttFiber73Parent_2_ok,
    ttFiber73Parent_3_ok,
    ttFiber73Parent_4_ok,
    ttFiber73Parent_5_ok,
    ttFiber73Parent_6_ok,
    ttFiber73Parent_7_ok]

def ttFiber74Key : List LColor :=
  [LColor.p, LColor.p, LColor.r, LColor.p]

def ttFiber74Expected : List Nat :=
  [152, 153, 154, 155, 156, 157, 158, 159]

def ttFiber74Rows : List DirectChainParentRow :=
  [ directRow 152 152 30 176 30 176 default
  , directRow 153 152 30 177 30 176 (chainMove LColor.r LColor.p 1 TauEdge.B5)
  , directRow 154 152 30 178 30 176 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 155 153 30 179 30 177 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 156 152 31 184 30 176 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 157 153 31 185 30 177 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 158 154 31 186 30 178 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  , directRow 159 155 31 187 30 179 (chainMove LColor.r LColor.p 0 TauEdge.B5)
  ]

def ttFiber74RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber74Rows i default

def ttFiber74SourcesCheck : Bool :=
  (ttFiber74Rows.map fun row => row.source) == ttFiber74Expected

theorem ttFiber74SourcesCheck_ok :
    ttFiber74SourcesCheck = true := by
  decide

def ttFiber74RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber74Key ttFiber74Expected (ttFiber74RowAt i)

theorem ttFiber74Row_0_ok : ttFiber74RowCheck 0 = true := by decide
theorem ttFiber74Row_1_ok : ttFiber74RowCheck 1 = true := by decide
theorem ttFiber74Row_2_ok : ttFiber74RowCheck 2 = true := by decide
theorem ttFiber74Row_3_ok : ttFiber74RowCheck 3 = true := by decide
theorem ttFiber74Row_4_ok : ttFiber74RowCheck 4 = true := by decide
theorem ttFiber74Row_5_ok : ttFiber74RowCheck 5 = true := by decide
theorem ttFiber74Row_6_ok : ttFiber74RowCheck 6 = true := by decide
theorem ttFiber74Row_7_ok : ttFiber74RowCheck 7 = true := by decide

def ttFiber74ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber74Rows ttMaxParentDepth (listGetD ttFiber74Expected i 0) == 152

theorem ttFiber74Parent_0_ok : ttFiber74ParentCheck 0 = true := by decide
theorem ttFiber74Parent_1_ok : ttFiber74ParentCheck 1 = true := by decide
theorem ttFiber74Parent_2_ok : ttFiber74ParentCheck 2 = true := by decide
theorem ttFiber74Parent_3_ok : ttFiber74ParentCheck 3 = true := by decide
theorem ttFiber74Parent_4_ok : ttFiber74ParentCheck 4 = true := by decide
theorem ttFiber74Parent_5_ok : ttFiber74ParentCheck 5 = true := by decide
theorem ttFiber74Parent_6_ok : ttFiber74ParentCheck 6 = true := by decide
theorem ttFiber74Parent_7_ok : ttFiber74ParentCheck 7 = true := by decide

def ttFiber74CertificateAudit : Bool :=
  ttFiber74SourcesCheck &&
    ttFiber74RowCheck 0 &&
    ttFiber74RowCheck 1 &&
    ttFiber74RowCheck 2 &&
    ttFiber74RowCheck 3 &&
    ttFiber74RowCheck 4 &&
    ttFiber74RowCheck 5 &&
    ttFiber74RowCheck 6 &&
    ttFiber74RowCheck 7 &&
    ttFiber74ParentCheck 0 &&
    ttFiber74ParentCheck 1 &&
    ttFiber74ParentCheck 2 &&
    ttFiber74ParentCheck 3 &&
    ttFiber74ParentCheck 4 &&
    ttFiber74ParentCheck 5 &&
    ttFiber74ParentCheck 6 &&
    ttFiber74ParentCheck 7

theorem ttFiber74CertificateAudit_ok :
    ttFiber74CertificateAudit = true := by
  simp [ttFiber74CertificateAudit,
    ttFiber74SourcesCheck_ok,
    ttFiber74Row_0_ok,
    ttFiber74Row_1_ok,
    ttFiber74Row_2_ok,
    ttFiber74Row_3_ok,
    ttFiber74Row_4_ok,
    ttFiber74Row_5_ok,
    ttFiber74Row_6_ok,
    ttFiber74Row_7_ok,
    ttFiber74Parent_0_ok,
    ttFiber74Parent_1_ok,
    ttFiber74Parent_2_ok,
    ttFiber74Parent_3_ok,
    ttFiber74Parent_4_ok,
    ttFiber74Parent_5_ok,
    ttFiber74Parent_6_ok,
    ttFiber74Parent_7_ok]

def ttFiber75Key : List LColor :=
  [LColor.p, LColor.p, LColor.b, LColor.r]

def ttFiber75Expected : List Nat :=
  [520, 521, 522, 523, 524, 525, 526, 527]

def ttFiber75Rows : List DirectChainParentRow :=
  [ directRow 520 520 106 52 106 52 default
  , directRow 521 520 106 53 106 52 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 522 521 106 54 106 53 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 523 520 106 55 106 52 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 524 520 107 60 106 52 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 525 521 107 61 106 53 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 526 522 107 62 106 54 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  , directRow 527 523 107 63 106 55 (chainMove LColor.r LColor.b 0 TauEdge.B5)
  ]

def ttFiber75RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber75Rows i default

def ttFiber75SourcesCheck : Bool :=
  (ttFiber75Rows.map fun row => row.source) == ttFiber75Expected

theorem ttFiber75SourcesCheck_ok :
    ttFiber75SourcesCheck = true := by
  decide

def ttFiber75RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber75Key ttFiber75Expected (ttFiber75RowAt i)

theorem ttFiber75Row_0_ok : ttFiber75RowCheck 0 = true := by decide
theorem ttFiber75Row_1_ok : ttFiber75RowCheck 1 = true := by decide
theorem ttFiber75Row_2_ok : ttFiber75RowCheck 2 = true := by decide
theorem ttFiber75Row_3_ok : ttFiber75RowCheck 3 = true := by decide
theorem ttFiber75Row_4_ok : ttFiber75RowCheck 4 = true := by decide
theorem ttFiber75Row_5_ok : ttFiber75RowCheck 5 = true := by decide
theorem ttFiber75Row_6_ok : ttFiber75RowCheck 6 = true := by decide
theorem ttFiber75Row_7_ok : ttFiber75RowCheck 7 = true := by decide

def ttFiber75ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber75Rows ttMaxParentDepth (listGetD ttFiber75Expected i 0) == 520

theorem ttFiber75Parent_0_ok : ttFiber75ParentCheck 0 = true := by decide
theorem ttFiber75Parent_1_ok : ttFiber75ParentCheck 1 = true := by decide
theorem ttFiber75Parent_2_ok : ttFiber75ParentCheck 2 = true := by decide
theorem ttFiber75Parent_3_ok : ttFiber75ParentCheck 3 = true := by decide
theorem ttFiber75Parent_4_ok : ttFiber75ParentCheck 4 = true := by decide
theorem ttFiber75Parent_5_ok : ttFiber75ParentCheck 5 = true := by decide
theorem ttFiber75Parent_6_ok : ttFiber75ParentCheck 6 = true := by decide
theorem ttFiber75Parent_7_ok : ttFiber75ParentCheck 7 = true := by decide

def ttFiber75CertificateAudit : Bool :=
  ttFiber75SourcesCheck &&
    ttFiber75RowCheck 0 &&
    ttFiber75RowCheck 1 &&
    ttFiber75RowCheck 2 &&
    ttFiber75RowCheck 3 &&
    ttFiber75RowCheck 4 &&
    ttFiber75RowCheck 5 &&
    ttFiber75RowCheck 6 &&
    ttFiber75RowCheck 7 &&
    ttFiber75ParentCheck 0 &&
    ttFiber75ParentCheck 1 &&
    ttFiber75ParentCheck 2 &&
    ttFiber75ParentCheck 3 &&
    ttFiber75ParentCheck 4 &&
    ttFiber75ParentCheck 5 &&
    ttFiber75ParentCheck 6 &&
    ttFiber75ParentCheck 7

theorem ttFiber75CertificateAudit_ok :
    ttFiber75CertificateAudit = true := by
  simp [ttFiber75CertificateAudit,
    ttFiber75SourcesCheck_ok,
    ttFiber75Row_0_ok,
    ttFiber75Row_1_ok,
    ttFiber75Row_2_ok,
    ttFiber75Row_3_ok,
    ttFiber75Row_4_ok,
    ttFiber75Row_5_ok,
    ttFiber75Row_6_ok,
    ttFiber75Row_7_ok,
    ttFiber75Parent_0_ok,
    ttFiber75Parent_1_ok,
    ttFiber75Parent_2_ok,
    ttFiber75Parent_3_ok,
    ttFiber75Parent_4_ok,
    ttFiber75Parent_5_ok,
    ttFiber75Parent_6_ok,
    ttFiber75Parent_7_ok]

def ttFiber76Key : List LColor :=
  [LColor.p, LColor.p, LColor.b, LColor.b]

def ttFiber76Expected : List Nat :=
  [440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559]

def ttFiber76Rows : List DirectChainParentRow :=
  [ directRow 440 440 88 80 88 80 default
  , directRow 441 440 88 81 88 80 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 442 440 88 82 88 80 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 443 441 88 83 88 81 (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
  , directRow 444 442 88 100 88 82 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 445 447 88 101 88 103 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 446 441 88 102 88 81 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 447 440 88 103 88 80 (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
  , directRow 448 440 89 88 88 80 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 449 441 89 89 88 81 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 450 442 89 90 88 82 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 451 443 89 91 88 83 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 452 444 89 108 88 100 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 453 445 89 109 88 101 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 454 446 89 110 88 102 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 455 447 89 111 88 103 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 456 440 90 16 88 80 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 457 441 90 17 88 81 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 458 442 90 18 88 82 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 459 443 90 19 88 83 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 460 456 90 32 90 16 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 461 457 90 33 90 17 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 462 446 90 34 88 102 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 463 447 90 35 88 103 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 464 448 91 24 89 88 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 465 449 91 25 89 89 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 466 450 91 26 89 90 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 467 451 91 27 89 91 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 468 464 91 40 91 24 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 469 465 91 41 91 25 (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
  , directRow 470 454 91 42 89 110 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 471 455 91 43 89 111 (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
  , directRow 528 544 108 132 110 64 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 529 545 108 133 110 65 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 530 462 108 134 90 34 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 531 463 108 135 90 35 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 532 458 108 180 90 18 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 533 535 108 181 108 183 (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
  , directRow 534 457 108 182 90 17 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 535 456 108 183 90 16 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 536 552 109 140 111 72 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 537 553 109 141 111 73 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 538 554 109 142 111 74 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 539 536 109 143 109 140 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 540 536 109 188 109 140 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 541 537 109 189 109 141 (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
  , directRow 542 558 109 190 111 126 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 543 559 109 191 111 127 (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
  , directRow 544 448 110 64 89 88 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 545 449 110 65 89 89 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 546 450 110 66 89 90 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 547 451 110 67 89 91 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 548 452 110 116 89 108 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 549 453 110 117 89 109 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 550 454 110 118 89 110 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 551 455 110 119 89 111 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 552 440 111 72 88 80 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 553 441 111 73 88 81 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 554 442 111 74 88 82 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 555 443 111 75 88 83 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 556 444 111 124 88 100 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 557 445 111 125 88 101 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 558 446 111 126 88 102 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  , directRow 559 447 111 127 88 103 (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
  ]

def ttFiber76RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber76Rows i default

def ttFiber76SourcesCheck : Bool :=
  (ttFiber76Rows.map fun row => row.source) == ttFiber76Expected

theorem ttFiber76SourcesCheck_ok :
    ttFiber76SourcesCheck = true := by
  decide

def ttFiber76RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt i)

theorem ttFiber76Row_0_ok : ttFiber76RowCheck 0 = true := by decide
theorem ttFiber76Row_1_ok : ttFiber76RowCheck 1 = true := by decide
theorem ttFiber76Row_2_ok : ttFiber76RowCheck 2 = true := by decide
theorem ttFiber76Row_3_ok : ttFiber76RowCheck 3 = true := by decide
theorem ttFiber76Row_4_ok : ttFiber76RowCheck 4 = true := by decide
theorem ttFiber76Row_5_ok : ttFiber76RowCheck 5 = true := by decide
theorem ttFiber76Row_6_ok : ttFiber76RowCheck 6 = true := by decide
theorem ttFiber76Row_7_ok : ttFiber76RowCheck 7 = true := by decide
theorem ttFiber76Row_8_ok : ttFiber76RowCheck 8 = true := by decide
theorem ttFiber76Row_9_ok : ttFiber76RowCheck 9 = true := by decide
theorem ttFiber76Row_10_ok : ttFiber76RowCheck 10 = true := by decide
theorem ttFiber76Row_11_ok : ttFiber76RowCheck 11 = true := by decide
theorem ttFiber76Row_12_ok : ttFiber76RowCheck 12 = true := by decide
theorem ttFiber76Row_13_ok : ttFiber76RowCheck 13 = true := by decide
theorem ttFiber76Row_14_ok : ttFiber76RowCheck 14 = true := by decide
theorem ttFiber76Row_15_ok : ttFiber76RowCheck 15 = true := by decide
theorem ttFiber76Row_16_ok : ttFiber76RowCheck 16 = true := by decide
theorem ttFiber76Row_17_ok : ttFiber76RowCheck 17 = true := by decide
theorem ttFiber76Row_18_ok : ttFiber76RowCheck 18 = true := by decide
theorem ttFiber76Row_19_ok : ttFiber76RowCheck 19 = true := by decide
theorem ttFiber76Row_20_ok : ttFiber76RowCheck 20 = true := by decide
theorem ttFiber76Row_21_ok : ttFiber76RowCheck 21 = true := by decide
theorem ttFiber76Row_22_ok : ttFiber76RowCheck 22 = true := by decide
theorem ttFiber76Row_23_ok : ttFiber76RowCheck 23 = true := by decide
theorem ttFiber76Row_24_ok : ttFiber76RowCheck 24 = true := by decide
theorem ttFiber76Row_25_ok : ttFiber76RowCheck 25 = true := by decide
theorem ttFiber76Row_26_ok : ttFiber76RowCheck 26 = true := by decide
theorem ttFiber76Row_27_ok : ttFiber76RowCheck 27 = true := by decide
theorem ttFiber76Row_28_ok : ttFiber76RowCheck 28 = true := by decide
theorem ttFiber76Row_29_ok : ttFiber76RowCheck 29 = true := by decide
theorem ttFiber76Row_30_ok : ttFiber76RowCheck 30 = true := by decide
theorem ttFiber76Row_31_ok : ttFiber76RowCheck 31 = true := by decide
theorem ttFiber76Row_32_ok : ttFiber76RowCheck 32 = true := by decide
theorem ttFiber76Row_33_ok : ttFiber76RowCheck 33 = true := by decide
theorem ttFiber76Row_34_ok : ttFiber76RowCheck 34 = true := by decide
theorem ttFiber76Row_35_ok : ttFiber76RowCheck 35 = true := by decide
theorem ttFiber76Row_36_ok : ttFiber76RowCheck 36 = true := by decide
theorem ttFiber76Row_37_ok : ttFiber76RowCheck 37 = true := by decide
theorem ttFiber76Row_38_ok : ttFiber76RowCheck 38 = true := by decide
theorem ttFiber76Row_39_ok : ttFiber76RowCheck 39 = true := by decide
theorem ttFiber76Row_40_ok : ttFiber76RowCheck 40 = true := by decide
theorem ttFiber76Row_41_ok : ttFiber76RowCheck 41 = true := by decide
theorem ttFiber76Row_42_ok : ttFiber76RowCheck 42 = true := by decide
theorem ttFiber76Row_43_ok : ttFiber76RowCheck 43 = true := by decide
theorem ttFiber76Row_44_ok : ttFiber76RowCheck 44 = true := by decide
theorem ttFiber76Row_45_ok : ttFiber76RowCheck 45 = true := by decide
theorem ttFiber76Row_46_ok : ttFiber76RowCheck 46 = true := by decide
theorem ttFiber76Row_47_ok : ttFiber76RowCheck 47 = true := by decide
theorem ttFiber76Row_48_ok : ttFiber76RowCheck 48 = true := by decide
theorem ttFiber76Row_49_ok : ttFiber76RowCheck 49 = true := by decide
theorem ttFiber76Row_50_ok : ttFiber76RowCheck 50 = true := by decide
theorem ttFiber76Row_51_ok : ttFiber76RowCheck 51 = true := by decide
theorem ttFiber76Row_52_ok : ttFiber76RowCheck 52 = true := by decide
theorem ttFiber76Row_53_ok : ttFiber76RowCheck 53 = true := by decide
theorem ttFiber76Row_54_ok : ttFiber76RowCheck 54 = true := by decide
theorem ttFiber76Row_55_ok : ttFiber76RowCheck 55 = true := by decide
theorem ttFiber76Row_56_ok : ttFiber76RowCheck 56 = true := by decide
theorem ttFiber76Row_57_ok : ttFiber76RowCheck 57 = true := by decide
theorem ttFiber76Row_58_ok : ttFiber76RowCheck 58 = true := by decide
theorem ttFiber76Row_59_ok : ttFiber76RowCheck 59 = true := by decide
theorem ttFiber76Row_60_ok : ttFiber76RowCheck 60 = true := by decide
theorem ttFiber76Row_61_ok : ttFiber76RowCheck 61 = true := by decide
theorem ttFiber76Row_62_ok : ttFiber76RowCheck 62 = true := by decide
theorem ttFiber76Row_63_ok : ttFiber76RowCheck 63 = true := by decide

def ttFiber76ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber76Rows ttMaxParentDepth (listGetD ttFiber76Expected i 0) == 440

theorem ttFiber76Parent_0_ok : ttFiber76ParentCheck 0 = true := by decide
theorem ttFiber76Parent_1_ok : ttFiber76ParentCheck 1 = true := by decide
theorem ttFiber76Parent_2_ok : ttFiber76ParentCheck 2 = true := by decide
theorem ttFiber76Parent_3_ok : ttFiber76ParentCheck 3 = true := by decide
theorem ttFiber76Parent_4_ok : ttFiber76ParentCheck 4 = true := by decide
theorem ttFiber76Parent_5_ok : ttFiber76ParentCheck 5 = true := by decide
theorem ttFiber76Parent_6_ok : ttFiber76ParentCheck 6 = true := by decide
theorem ttFiber76Parent_7_ok : ttFiber76ParentCheck 7 = true := by decide
theorem ttFiber76Parent_8_ok : ttFiber76ParentCheck 8 = true := by decide
theorem ttFiber76Parent_9_ok : ttFiber76ParentCheck 9 = true := by decide
theorem ttFiber76Parent_10_ok : ttFiber76ParentCheck 10 = true := by decide
theorem ttFiber76Parent_11_ok : ttFiber76ParentCheck 11 = true := by decide
theorem ttFiber76Parent_12_ok : ttFiber76ParentCheck 12 = true := by decide
theorem ttFiber76Parent_13_ok : ttFiber76ParentCheck 13 = true := by decide
theorem ttFiber76Parent_14_ok : ttFiber76ParentCheck 14 = true := by decide
theorem ttFiber76Parent_15_ok : ttFiber76ParentCheck 15 = true := by decide
theorem ttFiber76Parent_16_ok : ttFiber76ParentCheck 16 = true := by decide
theorem ttFiber76Parent_17_ok : ttFiber76ParentCheck 17 = true := by decide
theorem ttFiber76Parent_18_ok : ttFiber76ParentCheck 18 = true := by decide
theorem ttFiber76Parent_19_ok : ttFiber76ParentCheck 19 = true := by decide
theorem ttFiber76Parent_20_ok : ttFiber76ParentCheck 20 = true := by decide
theorem ttFiber76Parent_21_ok : ttFiber76ParentCheck 21 = true := by decide
theorem ttFiber76Parent_22_ok : ttFiber76ParentCheck 22 = true := by decide
theorem ttFiber76Parent_23_ok : ttFiber76ParentCheck 23 = true := by decide
theorem ttFiber76Parent_24_ok : ttFiber76ParentCheck 24 = true := by decide
theorem ttFiber76Parent_25_ok : ttFiber76ParentCheck 25 = true := by decide
theorem ttFiber76Parent_26_ok : ttFiber76ParentCheck 26 = true := by decide
theorem ttFiber76Parent_27_ok : ttFiber76ParentCheck 27 = true := by decide
theorem ttFiber76Parent_28_ok : ttFiber76ParentCheck 28 = true := by decide
theorem ttFiber76Parent_29_ok : ttFiber76ParentCheck 29 = true := by decide
theorem ttFiber76Parent_30_ok : ttFiber76ParentCheck 30 = true := by decide
theorem ttFiber76Parent_31_ok : ttFiber76ParentCheck 31 = true := by decide
theorem ttFiber76Parent_32_ok : ttFiber76ParentCheck 32 = true := by decide
theorem ttFiber76Parent_33_ok : ttFiber76ParentCheck 33 = true := by decide
theorem ttFiber76Parent_34_ok : ttFiber76ParentCheck 34 = true := by decide
theorem ttFiber76Parent_35_ok : ttFiber76ParentCheck 35 = true := by decide
theorem ttFiber76Parent_36_ok : ttFiber76ParentCheck 36 = true := by decide
theorem ttFiber76Parent_37_ok : ttFiber76ParentCheck 37 = true := by decide
theorem ttFiber76Parent_38_ok : ttFiber76ParentCheck 38 = true := by decide
theorem ttFiber76Parent_39_ok : ttFiber76ParentCheck 39 = true := by decide
theorem ttFiber76Parent_40_ok : ttFiber76ParentCheck 40 = true := by decide
theorem ttFiber76Parent_41_ok : ttFiber76ParentCheck 41 = true := by decide
theorem ttFiber76Parent_42_ok : ttFiber76ParentCheck 42 = true := by decide
theorem ttFiber76Parent_43_ok : ttFiber76ParentCheck 43 = true := by decide
theorem ttFiber76Parent_44_ok : ttFiber76ParentCheck 44 = true := by decide
theorem ttFiber76Parent_45_ok : ttFiber76ParentCheck 45 = true := by decide
theorem ttFiber76Parent_46_ok : ttFiber76ParentCheck 46 = true := by decide
theorem ttFiber76Parent_47_ok : ttFiber76ParentCheck 47 = true := by decide
theorem ttFiber76Parent_48_ok : ttFiber76ParentCheck 48 = true := by decide
theorem ttFiber76Parent_49_ok : ttFiber76ParentCheck 49 = true := by decide
theorem ttFiber76Parent_50_ok : ttFiber76ParentCheck 50 = true := by decide
theorem ttFiber76Parent_51_ok : ttFiber76ParentCheck 51 = true := by decide
theorem ttFiber76Parent_52_ok : ttFiber76ParentCheck 52 = true := by decide
theorem ttFiber76Parent_53_ok : ttFiber76ParentCheck 53 = true := by decide
theorem ttFiber76Parent_54_ok : ttFiber76ParentCheck 54 = true := by decide
theorem ttFiber76Parent_55_ok : ttFiber76ParentCheck 55 = true := by decide
theorem ttFiber76Parent_56_ok : ttFiber76ParentCheck 56 = true := by decide
theorem ttFiber76Parent_57_ok : ttFiber76ParentCheck 57 = true := by decide
theorem ttFiber76Parent_58_ok : ttFiber76ParentCheck 58 = true := by decide
theorem ttFiber76Parent_59_ok : ttFiber76ParentCheck 59 = true := by decide
theorem ttFiber76Parent_60_ok : ttFiber76ParentCheck 60 = true := by decide
theorem ttFiber76Parent_61_ok : ttFiber76ParentCheck 61 = true := by decide
theorem ttFiber76Parent_62_ok : ttFiber76ParentCheck 62 = true := by decide
theorem ttFiber76Parent_63_ok : ttFiber76ParentCheck 63 = true := by decide

def ttFiber76CertificateAudit : Bool :=
  ttFiber76SourcesCheck &&
    ttFiber76RowCheck 0 &&
    ttFiber76RowCheck 1 &&
    ttFiber76RowCheck 2 &&
    ttFiber76RowCheck 3 &&
    ttFiber76RowCheck 4 &&
    ttFiber76RowCheck 5 &&
    ttFiber76RowCheck 6 &&
    ttFiber76RowCheck 7 &&
    ttFiber76RowCheck 8 &&
    ttFiber76RowCheck 9 &&
    ttFiber76RowCheck 10 &&
    ttFiber76RowCheck 11 &&
    ttFiber76RowCheck 12 &&
    ttFiber76RowCheck 13 &&
    ttFiber76RowCheck 14 &&
    ttFiber76RowCheck 15 &&
    ttFiber76RowCheck 16 &&
    ttFiber76RowCheck 17 &&
    ttFiber76RowCheck 18 &&
    ttFiber76RowCheck 19 &&
    ttFiber76RowCheck 20 &&
    ttFiber76RowCheck 21 &&
    ttFiber76RowCheck 22 &&
    ttFiber76RowCheck 23 &&
    ttFiber76RowCheck 24 &&
    ttFiber76RowCheck 25 &&
    ttFiber76RowCheck 26 &&
    ttFiber76RowCheck 27 &&
    ttFiber76RowCheck 28 &&
    ttFiber76RowCheck 29 &&
    ttFiber76RowCheck 30 &&
    ttFiber76RowCheck 31 &&
    ttFiber76RowCheck 32 &&
    ttFiber76RowCheck 33 &&
    ttFiber76RowCheck 34 &&
    ttFiber76RowCheck 35 &&
    ttFiber76RowCheck 36 &&
    ttFiber76RowCheck 37 &&
    ttFiber76RowCheck 38 &&
    ttFiber76RowCheck 39 &&
    ttFiber76RowCheck 40 &&
    ttFiber76RowCheck 41 &&
    ttFiber76RowCheck 42 &&
    ttFiber76RowCheck 43 &&
    ttFiber76RowCheck 44 &&
    ttFiber76RowCheck 45 &&
    ttFiber76RowCheck 46 &&
    ttFiber76RowCheck 47 &&
    ttFiber76RowCheck 48 &&
    ttFiber76RowCheck 49 &&
    ttFiber76RowCheck 50 &&
    ttFiber76RowCheck 51 &&
    ttFiber76RowCheck 52 &&
    ttFiber76RowCheck 53 &&
    ttFiber76RowCheck 54 &&
    ttFiber76RowCheck 55 &&
    ttFiber76RowCheck 56 &&
    ttFiber76RowCheck 57 &&
    ttFiber76RowCheck 58 &&
    ttFiber76RowCheck 59 &&
    ttFiber76RowCheck 60 &&
    ttFiber76RowCheck 61 &&
    ttFiber76RowCheck 62 &&
    ttFiber76RowCheck 63 &&
    ttFiber76ParentCheck 0 &&
    ttFiber76ParentCheck 1 &&
    ttFiber76ParentCheck 2 &&
    ttFiber76ParentCheck 3 &&
    ttFiber76ParentCheck 4 &&
    ttFiber76ParentCheck 5 &&
    ttFiber76ParentCheck 6 &&
    ttFiber76ParentCheck 7 &&
    ttFiber76ParentCheck 8 &&
    ttFiber76ParentCheck 9 &&
    ttFiber76ParentCheck 10 &&
    ttFiber76ParentCheck 11 &&
    ttFiber76ParentCheck 12 &&
    ttFiber76ParentCheck 13 &&
    ttFiber76ParentCheck 14 &&
    ttFiber76ParentCheck 15 &&
    ttFiber76ParentCheck 16 &&
    ttFiber76ParentCheck 17 &&
    ttFiber76ParentCheck 18 &&
    ttFiber76ParentCheck 19 &&
    ttFiber76ParentCheck 20 &&
    ttFiber76ParentCheck 21 &&
    ttFiber76ParentCheck 22 &&
    ttFiber76ParentCheck 23 &&
    ttFiber76ParentCheck 24 &&
    ttFiber76ParentCheck 25 &&
    ttFiber76ParentCheck 26 &&
    ttFiber76ParentCheck 27 &&
    ttFiber76ParentCheck 28 &&
    ttFiber76ParentCheck 29 &&
    ttFiber76ParentCheck 30 &&
    ttFiber76ParentCheck 31 &&
    ttFiber76ParentCheck 32 &&
    ttFiber76ParentCheck 33 &&
    ttFiber76ParentCheck 34 &&
    ttFiber76ParentCheck 35 &&
    ttFiber76ParentCheck 36 &&
    ttFiber76ParentCheck 37 &&
    ttFiber76ParentCheck 38 &&
    ttFiber76ParentCheck 39 &&
    ttFiber76ParentCheck 40 &&
    ttFiber76ParentCheck 41 &&
    ttFiber76ParentCheck 42 &&
    ttFiber76ParentCheck 43 &&
    ttFiber76ParentCheck 44 &&
    ttFiber76ParentCheck 45 &&
    ttFiber76ParentCheck 46 &&
    ttFiber76ParentCheck 47 &&
    ttFiber76ParentCheck 48 &&
    ttFiber76ParentCheck 49 &&
    ttFiber76ParentCheck 50 &&
    ttFiber76ParentCheck 51 &&
    ttFiber76ParentCheck 52 &&
    ttFiber76ParentCheck 53 &&
    ttFiber76ParentCheck 54 &&
    ttFiber76ParentCheck 55 &&
    ttFiber76ParentCheck 56 &&
    ttFiber76ParentCheck 57 &&
    ttFiber76ParentCheck 58 &&
    ttFiber76ParentCheck 59 &&
    ttFiber76ParentCheck 60 &&
    ttFiber76ParentCheck 61 &&
    ttFiber76ParentCheck 62 &&
    ttFiber76ParentCheck 63

theorem ttFiber76CertificateAudit_ok :
    ttFiber76CertificateAudit = true := by
  simp [ttFiber76CertificateAudit,
    ttFiber76SourcesCheck_ok,
    ttFiber76Row_0_ok,
    ttFiber76Row_1_ok,
    ttFiber76Row_2_ok,
    ttFiber76Row_3_ok,
    ttFiber76Row_4_ok,
    ttFiber76Row_5_ok,
    ttFiber76Row_6_ok,
    ttFiber76Row_7_ok,
    ttFiber76Row_8_ok,
    ttFiber76Row_9_ok,
    ttFiber76Row_10_ok,
    ttFiber76Row_11_ok,
    ttFiber76Row_12_ok,
    ttFiber76Row_13_ok,
    ttFiber76Row_14_ok,
    ttFiber76Row_15_ok,
    ttFiber76Row_16_ok,
    ttFiber76Row_17_ok,
    ttFiber76Row_18_ok,
    ttFiber76Row_19_ok,
    ttFiber76Row_20_ok,
    ttFiber76Row_21_ok,
    ttFiber76Row_22_ok,
    ttFiber76Row_23_ok,
    ttFiber76Row_24_ok,
    ttFiber76Row_25_ok,
    ttFiber76Row_26_ok,
    ttFiber76Row_27_ok,
    ttFiber76Row_28_ok,
    ttFiber76Row_29_ok,
    ttFiber76Row_30_ok,
    ttFiber76Row_31_ok,
    ttFiber76Row_32_ok,
    ttFiber76Row_33_ok,
    ttFiber76Row_34_ok,
    ttFiber76Row_35_ok,
    ttFiber76Row_36_ok,
    ttFiber76Row_37_ok,
    ttFiber76Row_38_ok,
    ttFiber76Row_39_ok,
    ttFiber76Row_40_ok,
    ttFiber76Row_41_ok,
    ttFiber76Row_42_ok,
    ttFiber76Row_43_ok,
    ttFiber76Row_44_ok,
    ttFiber76Row_45_ok,
    ttFiber76Row_46_ok,
    ttFiber76Row_47_ok,
    ttFiber76Row_48_ok,
    ttFiber76Row_49_ok,
    ttFiber76Row_50_ok,
    ttFiber76Row_51_ok,
    ttFiber76Row_52_ok,
    ttFiber76Row_53_ok,
    ttFiber76Row_54_ok,
    ttFiber76Row_55_ok,
    ttFiber76Row_56_ok,
    ttFiber76Row_57_ok,
    ttFiber76Row_58_ok,
    ttFiber76Row_59_ok,
    ttFiber76Row_60_ok,
    ttFiber76Row_61_ok,
    ttFiber76Row_62_ok,
    ttFiber76Row_63_ok,
    ttFiber76Parent_0_ok,
    ttFiber76Parent_1_ok,
    ttFiber76Parent_2_ok,
    ttFiber76Parent_3_ok,
    ttFiber76Parent_4_ok,
    ttFiber76Parent_5_ok,
    ttFiber76Parent_6_ok,
    ttFiber76Parent_7_ok,
    ttFiber76Parent_8_ok,
    ttFiber76Parent_9_ok,
    ttFiber76Parent_10_ok,
    ttFiber76Parent_11_ok,
    ttFiber76Parent_12_ok,
    ttFiber76Parent_13_ok,
    ttFiber76Parent_14_ok,
    ttFiber76Parent_15_ok,
    ttFiber76Parent_16_ok,
    ttFiber76Parent_17_ok,
    ttFiber76Parent_18_ok,
    ttFiber76Parent_19_ok,
    ttFiber76Parent_20_ok,
    ttFiber76Parent_21_ok,
    ttFiber76Parent_22_ok,
    ttFiber76Parent_23_ok,
    ttFiber76Parent_24_ok,
    ttFiber76Parent_25_ok,
    ttFiber76Parent_26_ok,
    ttFiber76Parent_27_ok,
    ttFiber76Parent_28_ok,
    ttFiber76Parent_29_ok,
    ttFiber76Parent_30_ok,
    ttFiber76Parent_31_ok,
    ttFiber76Parent_32_ok,
    ttFiber76Parent_33_ok,
    ttFiber76Parent_34_ok,
    ttFiber76Parent_35_ok,
    ttFiber76Parent_36_ok,
    ttFiber76Parent_37_ok,
    ttFiber76Parent_38_ok,
    ttFiber76Parent_39_ok,
    ttFiber76Parent_40_ok,
    ttFiber76Parent_41_ok,
    ttFiber76Parent_42_ok,
    ttFiber76Parent_43_ok,
    ttFiber76Parent_44_ok,
    ttFiber76Parent_45_ok,
    ttFiber76Parent_46_ok,
    ttFiber76Parent_47_ok,
    ttFiber76Parent_48_ok,
    ttFiber76Parent_49_ok,
    ttFiber76Parent_50_ok,
    ttFiber76Parent_51_ok,
    ttFiber76Parent_52_ok,
    ttFiber76Parent_53_ok,
    ttFiber76Parent_54_ok,
    ttFiber76Parent_55_ok,
    ttFiber76Parent_56_ok,
    ttFiber76Parent_57_ok,
    ttFiber76Parent_58_ok,
    ttFiber76Parent_59_ok,
    ttFiber76Parent_60_ok,
    ttFiber76Parent_61_ok,
    ttFiber76Parent_62_ok,
    ttFiber76Parent_63_ok]

def ttFiber77Key : List LColor :=
  [LColor.p, LColor.p, LColor.b, LColor.p]

def ttFiber77Expected : List Nat :=
  [472, 473, 474, 475, 476, 477, 478, 479]

def ttFiber77Rows : List DirectChainParentRow :=
  [ directRow 472 472 92 144 92 144 default
  , directRow 473 472 92 145 92 144 (chainMove LColor.b LColor.p 1 TauEdge.B5)
  , directRow 474 473 92 146 92 145 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 475 472 92 147 92 144 (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
  , directRow 476 472 93 152 92 144 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 477 473 93 153 92 145 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 478 474 93 154 92 146 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  , directRow 479 475 93 155 92 147 (chainMove LColor.b LColor.p 0 TauEdge.B5)
  ]

def ttFiber77RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber77Rows i default

def ttFiber77SourcesCheck : Bool :=
  (ttFiber77Rows.map fun row => row.source) == ttFiber77Expected

theorem ttFiber77SourcesCheck_ok :
    ttFiber77SourcesCheck = true := by
  decide

def ttFiber77RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber77Key ttFiber77Expected (ttFiber77RowAt i)

theorem ttFiber77Row_0_ok : ttFiber77RowCheck 0 = true := by decide
theorem ttFiber77Row_1_ok : ttFiber77RowCheck 1 = true := by decide
theorem ttFiber77Row_2_ok : ttFiber77RowCheck 2 = true := by decide
theorem ttFiber77Row_3_ok : ttFiber77RowCheck 3 = true := by decide
theorem ttFiber77Row_4_ok : ttFiber77RowCheck 4 = true := by decide
theorem ttFiber77Row_5_ok : ttFiber77RowCheck 5 = true := by decide
theorem ttFiber77Row_6_ok : ttFiber77RowCheck 6 = true := by decide
theorem ttFiber77Row_7_ok : ttFiber77RowCheck 7 = true := by decide

def ttFiber77ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber77Rows ttMaxParentDepth (listGetD ttFiber77Expected i 0) == 472

theorem ttFiber77Parent_0_ok : ttFiber77ParentCheck 0 = true := by decide
theorem ttFiber77Parent_1_ok : ttFiber77ParentCheck 1 = true := by decide
theorem ttFiber77Parent_2_ok : ttFiber77ParentCheck 2 = true := by decide
theorem ttFiber77Parent_3_ok : ttFiber77ParentCheck 3 = true := by decide
theorem ttFiber77Parent_4_ok : ttFiber77ParentCheck 4 = true := by decide
theorem ttFiber77Parent_5_ok : ttFiber77ParentCheck 5 = true := by decide
theorem ttFiber77Parent_6_ok : ttFiber77ParentCheck 6 = true := by decide
theorem ttFiber77Parent_7_ok : ttFiber77ParentCheck 7 = true := by decide

def ttFiber77CertificateAudit : Bool :=
  ttFiber77SourcesCheck &&
    ttFiber77RowCheck 0 &&
    ttFiber77RowCheck 1 &&
    ttFiber77RowCheck 2 &&
    ttFiber77RowCheck 3 &&
    ttFiber77RowCheck 4 &&
    ttFiber77RowCheck 5 &&
    ttFiber77RowCheck 6 &&
    ttFiber77RowCheck 7 &&
    ttFiber77ParentCheck 0 &&
    ttFiber77ParentCheck 1 &&
    ttFiber77ParentCheck 2 &&
    ttFiber77ParentCheck 3 &&
    ttFiber77ParentCheck 4 &&
    ttFiber77ParentCheck 5 &&
    ttFiber77ParentCheck 6 &&
    ttFiber77ParentCheck 7

theorem ttFiber77CertificateAudit_ok :
    ttFiber77CertificateAudit = true := by
  simp [ttFiber77CertificateAudit,
    ttFiber77SourcesCheck_ok,
    ttFiber77Row_0_ok,
    ttFiber77Row_1_ok,
    ttFiber77Row_2_ok,
    ttFiber77Row_3_ok,
    ttFiber77Row_4_ok,
    ttFiber77Row_5_ok,
    ttFiber77Row_6_ok,
    ttFiber77Row_7_ok,
    ttFiber77Parent_0_ok,
    ttFiber77Parent_1_ok,
    ttFiber77Parent_2_ok,
    ttFiber77Parent_3_ok,
    ttFiber77Parent_4_ok,
    ttFiber77Parent_5_ok,
    ttFiber77Parent_6_ok,
    ttFiber77Parent_7_ok]

def ttFiber78Key : List LColor :=
  [LColor.p, LColor.p, LColor.p, LColor.r]

def ttFiber78Expected : List Nat :=
  []

def ttFiber78Rows : List DirectChainParentRow :=
  []

def ttFiber78RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber78Rows i default

def ttFiber78SourcesCheck : Bool :=
  (ttFiber78Rows.map fun row => row.source) == ttFiber78Expected

theorem ttFiber78SourcesCheck_ok :
    ttFiber78SourcesCheck = true := by
  decide

def ttFiber78RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber78Key ttFiber78Expected (ttFiber78RowAt i)

def ttFiber78ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber78Rows ttMaxParentDepth (listGetD ttFiber78Expected i 0) == 0

def ttFiber78CertificateAudit : Bool :=
  ttFiber78SourcesCheck

theorem ttFiber78CertificateAudit_ok :
    ttFiber78CertificateAudit = true := by
  simp [ttFiber78CertificateAudit,
    ttFiber78SourcesCheck_ok]

def ttFiber79Key : List LColor :=
  [LColor.p, LColor.p, LColor.p, LColor.b]

def ttFiber79Expected : List Nat :=
  []

def ttFiber79Rows : List DirectChainParentRow :=
  []

def ttFiber79RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber79Rows i default

def ttFiber79SourcesCheck : Bool :=
  (ttFiber79Rows.map fun row => row.source) == ttFiber79Expected

theorem ttFiber79SourcesCheck_ok :
    ttFiber79SourcesCheck = true := by
  decide

def ttFiber79RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber79Key ttFiber79Expected (ttFiber79RowAt i)

def ttFiber79ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber79Rows ttMaxParentDepth (listGetD ttFiber79Expected i 0) == 0

def ttFiber79CertificateAudit : Bool :=
  ttFiber79SourcesCheck

theorem ttFiber79CertificateAudit_ok :
    ttFiber79CertificateAudit = true := by
  simp [ttFiber79CertificateAudit,
    ttFiber79SourcesCheck_ok]

def ttFiber80Key : List LColor :=
  [LColor.p, LColor.p, LColor.p, LColor.p]

def ttFiber80Expected : List Nat :=
  []

def ttFiber80Rows : List DirectChainParentRow :=
  []

def ttFiber80RowAt (i : Nat) : DirectChainParentRow :=
  listGetD ttFiber80Rows i default

def ttFiber80SourcesCheck : Bool :=
  (ttFiber80Rows.map fun row => row.source) == ttFiber80Expected

theorem ttFiber80SourcesCheck_ok :
    ttFiber80SourcesCheck = true := by
  decide

def ttFiber80RowCheck (i : Nat) : Bool :=
  directRowValid ttFiber80Key ttFiber80Expected (ttFiber80RowAt i)

def ttFiber80ParentCheck (i : Nat) : Bool :=
  directParentIter ttFiber80Rows ttMaxParentDepth (listGetD ttFiber80Expected i 0) == 0

def ttFiber80CertificateAudit : Bool :=
  ttFiber80SourcesCheck

theorem ttFiber80CertificateAudit_ok :
    ttFiber80CertificateAudit = true := by
  simp [ttFiber80CertificateAudit,
    ttFiber80SourcesCheck_ok]

def ttAllFiberCertificateAudit : Bool :=
  ttFiber0CertificateAudit &&
    ttFiber1CertificateAudit &&
    ttFiber2CertificateAudit &&
    ttFiber3CertificateAudit &&
    ttFiber4CertificateAudit &&
    ttFiber5CertificateAudit &&
    ttFiber6CertificateAudit &&
    ttFiber7CertificateAudit &&
    ttFiber8CertificateAudit &&
    ttFiber9CertificateAudit &&
    ttFiber10CertificateAudit &&
    ttFiber11CertificateAudit &&
    ttFiber12CertificateAudit &&
    ttFiber13CertificateAudit &&
    ttFiber14CertificateAudit &&
    ttFiber15CertificateAudit &&
    ttFiber16CertificateAudit &&
    ttFiber17CertificateAudit &&
    ttFiber18CertificateAudit &&
    ttFiber19CertificateAudit &&
    ttFiber20CertificateAudit &&
    ttFiber21CertificateAudit &&
    ttFiber22CertificateAudit &&
    ttFiber23CertificateAudit &&
    ttFiber24CertificateAudit &&
    ttFiber25CertificateAudit &&
    ttFiber26CertificateAudit &&
    ttFiber27CertificateAudit &&
    ttFiber28CertificateAudit &&
    ttFiber29CertificateAudit &&
    ttFiber30CertificateAudit &&
    ttFiber31CertificateAudit &&
    ttFiber32CertificateAudit &&
    ttFiber33CertificateAudit &&
    ttFiber34CertificateAudit &&
    ttFiber35CertificateAudit &&
    ttFiber36CertificateAudit &&
    ttFiber37CertificateAudit &&
    ttFiber38CertificateAudit &&
    ttFiber39CertificateAudit &&
    ttFiber40CertificateAudit &&
    ttFiber41CertificateAudit &&
    ttFiber42CertificateAudit &&
    ttFiber43CertificateAudit &&
    ttFiber44CertificateAudit &&
    ttFiber45CertificateAudit &&
    ttFiber46CertificateAudit &&
    ttFiber47CertificateAudit &&
    ttFiber48CertificateAudit &&
    ttFiber49CertificateAudit &&
    ttFiber50CertificateAudit &&
    ttFiber51CertificateAudit &&
    ttFiber52CertificateAudit &&
    ttFiber53CertificateAudit &&
    ttFiber54CertificateAudit &&
    ttFiber55CertificateAudit &&
    ttFiber56CertificateAudit &&
    ttFiber57CertificateAudit &&
    ttFiber58CertificateAudit &&
    ttFiber59CertificateAudit &&
    ttFiber60CertificateAudit &&
    ttFiber61CertificateAudit &&
    ttFiber62CertificateAudit &&
    ttFiber63CertificateAudit &&
    ttFiber64CertificateAudit &&
    ttFiber65CertificateAudit &&
    ttFiber66CertificateAudit &&
    ttFiber67CertificateAudit &&
    ttFiber68CertificateAudit &&
    ttFiber69CertificateAudit &&
    ttFiber70CertificateAudit &&
    ttFiber71CertificateAudit &&
    ttFiber72CertificateAudit &&
    ttFiber73CertificateAudit &&
    ttFiber74CertificateAudit &&
    ttFiber75CertificateAudit &&
    ttFiber76CertificateAudit &&
    ttFiber77CertificateAudit &&
    ttFiber78CertificateAudit &&
    ttFiber79CertificateAudit &&
    ttFiber80CertificateAudit

theorem ttAllFiberCertificateAudit_ok :
    ttAllFiberCertificateAudit = true := by
  simp [ttAllFiberCertificateAudit,
    ttFiber0CertificateAudit_ok,
    ttFiber1CertificateAudit_ok,
    ttFiber2CertificateAudit_ok,
    ttFiber3CertificateAudit_ok,
    ttFiber4CertificateAudit_ok,
    ttFiber5CertificateAudit_ok,
    ttFiber6CertificateAudit_ok,
    ttFiber7CertificateAudit_ok,
    ttFiber8CertificateAudit_ok,
    ttFiber9CertificateAudit_ok,
    ttFiber10CertificateAudit_ok,
    ttFiber11CertificateAudit_ok,
    ttFiber12CertificateAudit_ok,
    ttFiber13CertificateAudit_ok,
    ttFiber14CertificateAudit_ok,
    ttFiber15CertificateAudit_ok,
    ttFiber16CertificateAudit_ok,
    ttFiber17CertificateAudit_ok,
    ttFiber18CertificateAudit_ok,
    ttFiber19CertificateAudit_ok,
    ttFiber20CertificateAudit_ok,
    ttFiber21CertificateAudit_ok,
    ttFiber22CertificateAudit_ok,
    ttFiber23CertificateAudit_ok,
    ttFiber24CertificateAudit_ok,
    ttFiber25CertificateAudit_ok,
    ttFiber26CertificateAudit_ok,
    ttFiber27CertificateAudit_ok,
    ttFiber28CertificateAudit_ok,
    ttFiber29CertificateAudit_ok,
    ttFiber30CertificateAudit_ok,
    ttFiber31CertificateAudit_ok,
    ttFiber32CertificateAudit_ok,
    ttFiber33CertificateAudit_ok,
    ttFiber34CertificateAudit_ok,
    ttFiber35CertificateAudit_ok,
    ttFiber36CertificateAudit_ok,
    ttFiber37CertificateAudit_ok,
    ttFiber38CertificateAudit_ok,
    ttFiber39CertificateAudit_ok,
    ttFiber40CertificateAudit_ok,
    ttFiber41CertificateAudit_ok,
    ttFiber42CertificateAudit_ok,
    ttFiber43CertificateAudit_ok,
    ttFiber44CertificateAudit_ok,
    ttFiber45CertificateAudit_ok,
    ttFiber46CertificateAudit_ok,
    ttFiber47CertificateAudit_ok,
    ttFiber48CertificateAudit_ok,
    ttFiber49CertificateAudit_ok,
    ttFiber50CertificateAudit_ok,
    ttFiber51CertificateAudit_ok,
    ttFiber52CertificateAudit_ok,
    ttFiber53CertificateAudit_ok,
    ttFiber54CertificateAudit_ok,
    ttFiber55CertificateAudit_ok,
    ttFiber56CertificateAudit_ok,
    ttFiber57CertificateAudit_ok,
    ttFiber58CertificateAudit_ok,
    ttFiber59CertificateAudit_ok,
    ttFiber60CertificateAudit_ok,
    ttFiber61CertificateAudit_ok,
    ttFiber62CertificateAudit_ok,
    ttFiber63CertificateAudit_ok,
    ttFiber64CertificateAudit_ok,
    ttFiber65CertificateAudit_ok,
    ttFiber66CertificateAudit_ok,
    ttFiber67CertificateAudit_ok,
    ttFiber68CertificateAudit_ok,
    ttFiber69CertificateAudit_ok,
    ttFiber70CertificateAudit_ok,
    ttFiber71CertificateAudit_ok,
    ttFiber72CertificateAudit_ok,
    ttFiber73CertificateAudit_ok,
    ttFiber74CertificateAudit_ok,
    ttFiber75CertificateAudit_ok,
    ttFiber76CertificateAudit_ok,
    ttFiber77CertificateAudit_ok,
    ttFiber78CertificateAudit_ok,
    ttFiber79CertificateAudit_ok,
    ttFiber80CertificateAudit_ok]

def ttFiberRowsAt : Nat → List DirectChainParentRow
  | 0 => ttFiber0Rows
  | 1 => ttFiber1Rows
  | 2 => ttFiber2Rows
  | 3 => ttFiber3Rows
  | 4 => ttFiber4Rows
  | 5 => ttFiber5Rows
  | 6 => ttFiber6Rows
  | 7 => ttFiber7Rows
  | 8 => ttFiber8Rows
  | 9 => ttFiber9Rows
  | 10 => ttFiber10Rows
  | 11 => ttFiber11Rows
  | 12 => ttFiber12Rows
  | 13 => ttFiber13Rows
  | 14 => ttFiber14Rows
  | 15 => ttFiber15Rows
  | 16 => ttFiber16Rows
  | 17 => ttFiber17Rows
  | 18 => ttFiber18Rows
  | 19 => ttFiber19Rows
  | 20 => ttFiber20Rows
  | 21 => ttFiber21Rows
  | 22 => ttFiber22Rows
  | 23 => ttFiber23Rows
  | 24 => ttFiber24Rows
  | 25 => ttFiber25Rows
  | 26 => ttFiber26Rows
  | 27 => ttFiber27Rows
  | 28 => ttFiber28Rows
  | 29 => ttFiber29Rows
  | 30 => ttFiber30Rows
  | 31 => ttFiber31Rows
  | 32 => ttFiber32Rows
  | 33 => ttFiber33Rows
  | 34 => ttFiber34Rows
  | 35 => ttFiber35Rows
  | 36 => ttFiber36Rows
  | 37 => ttFiber37Rows
  | 38 => ttFiber38Rows
  | 39 => ttFiber39Rows
  | 40 => ttFiber40Rows
  | 41 => ttFiber41Rows
  | 42 => ttFiber42Rows
  | 43 => ttFiber43Rows
  | 44 => ttFiber44Rows
  | 45 => ttFiber45Rows
  | 46 => ttFiber46Rows
  | 47 => ttFiber47Rows
  | 48 => ttFiber48Rows
  | 49 => ttFiber49Rows
  | 50 => ttFiber50Rows
  | 51 => ttFiber51Rows
  | 52 => ttFiber52Rows
  | 53 => ttFiber53Rows
  | 54 => ttFiber54Rows
  | 55 => ttFiber55Rows
  | 56 => ttFiber56Rows
  | 57 => ttFiber57Rows
  | 58 => ttFiber58Rows
  | 59 => ttFiber59Rows
  | 60 => ttFiber60Rows
  | 61 => ttFiber61Rows
  | 62 => ttFiber62Rows
  | 63 => ttFiber63Rows
  | 64 => ttFiber64Rows
  | 65 => ttFiber65Rows
  | 66 => ttFiber66Rows
  | 67 => ttFiber67Rows
  | 68 => ttFiber68Rows
  | 69 => ttFiber69Rows
  | 70 => ttFiber70Rows
  | 71 => ttFiber71Rows
  | 72 => ttFiber72Rows
  | 73 => ttFiber73Rows
  | 74 => ttFiber74Rows
  | 75 => ttFiber75Rows
  | 76 => ttFiber76Rows
  | 77 => ttFiber77Rows
  | 78 => ttFiber78Rows
  | 79 => ttFiber79Rows
  | 80 => ttFiber80Rows
  | _ => []

def ttRealFiberCertificateAt (i : Nat) : ChainFiberCertificate :=
  directChainFiberCertificate (listGetD colorAssignments4 i []) ttMaxParentDepth
    (ttFiberRowsAt i)

def ttRealFiberCertificates : List ChainFiberCertificate :=
  (List.range 81).map ttRealFiberCertificateAt

def ttRealFiberCertificateKeysCheck : Bool :=
  (ttRealFiberCertificates.map fun cert => cert.key) == colorAssignments4

def ttRealFiberCertificateAuditAt (i : Nat) : Bool :=
  chainFiberParentCertificateAudit ttWord (ttRealFiberCertificateAt i)

def ttRealFiberSmokeAudit : Bool :=
  ttRealFiberCertificateKeysCheck &&
    ttRealFiberCertificateAuditAt 0 &&
    ttRealFiberCertificateAuditAt 3

theorem ttRealFiberCertificateKeysCheck_ok :
    ttRealFiberCertificateKeysCheck = true := by
  decide

end GoertzelLemma818CompositeCertificate

end Mettapedia.GraphTheory.FourColor
