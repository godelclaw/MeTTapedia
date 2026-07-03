import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818RepresentativeTargets

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: `TTT` light-fiber component certificates

This generated module checks explicit component certificates for the empty and
size-16 fixed-input fibers of the non-base `tau,tau,tau` representative word.
It covers 69 of the 81 fixed-input fibers: 45 empty fibers and 24 nonempty
light fibers, for 384 chain states total. The remaining 12 fibers have size
512 and are intentionally left to a smaller transition/component certificate.

The checker never asks Lean to compute a full `chainComponent`; each row names
the component and Lean verifies pair-color membership, connectedness, closure,
input avoidance, and switch agreement locally.
-/

namespace GoertzelLemma818TripleTauLightComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate

def tttWord : List TauOrient :=
  [TauOrient.normal, TauOrient.normal, TauOrient.normal]

def tttFrontierWord :
    List GoertzelLemma818FrontierMode.TauOrient :=
  [ GoertzelLemma818FrontierMode.TauOrient.tau
  , GoertzelLemma818FrontierMode.TauOrient.tau
  , GoertzelLemma818FrontierMode.TauOrient.tau
  ]

def tttRepresentativeModeAudit : Bool :=
  GoertzelLemma818RepresentativeTargets.targetFrontierWord
      GoertzelLemma818RepresentativeTargets.RepresentativeSemanticTarget.ttt ==
    tttFrontierWord
  && GoertzelLemma818RepresentativeTargets.targetFrontierMode
      GoertzelLemma818RepresentativeTargets.RepresentativeSemanticTarget.ttt ==
    GoertzelLemma818FrontierMode.FrontierMode.mode09
  && GoertzelLemma818FrontierMode.wordMode tttFrontierWord ==
    some GoertzelLemma818FrontierMode.FrontierMode.mode09

theorem tttRepresentativeModeAudit_ok :
    tttRepresentativeModeAudit = true := by
  decide

def tttCompositeStateCount : Nat := 6528
def tttLightFiberCount : Nat := 69
def tttLightEmptyFiberCount : Nat := 45
def tttLightNonemptyFiberCount : Nat := 24
def tttLightStateCount : Nat := 384
def tttRemainingLargeFiberCount : Nat := 12
def tttRemainingLargeFiberSize : Nat := 512
def tttLightMaxParentDepth : Nat := 6

def tttLightCertifiedFiberIds : List Nat :=
  [0, 1, 2, 3, 5, 6, 7, 9,
   11, 12, 13, 14, 15, 16, 17, 18,
   19, 21, 22, 23, 24, 25, 26, 27,
   28, 29, 31, 32, 33, 34, 35, 37,
   38, 39, 40, 41, 42, 43, 45, 46,
   47, 48, 49, 51, 52, 53, 54, 55,
   56, 57, 58, 59, 61, 62, 63, 64,
   65, 66, 67, 68, 69, 71, 73, 74,
   75, 77, 78, 79, 80]

def tttLightNonemptyFiberIds : List Nat :=
  [3, 5, 6, 7, 9, 11, 18, 19,
   31, 32, 37, 38, 42, 43, 48, 49,
   61, 62, 69, 71, 73, 74, 75, 77]

def tttLightEmptyFiberIds : List Nat :=
  [0, 1, 2, 12, 13, 14, 15, 16,
   17, 21, 22, 23, 24, 25, 26, 27,
   28, 29, 33, 34, 35, 39, 40, 41,
   45, 46, 47, 51, 52, 53, 54, 55,
   56, 57, 58, 59, 63, 64, 65, 66,
   67, 68, 78, 79, 80]

def tttLargeFiberKeys : List (List LColor) :=
  [ [LColor.r, LColor.r, LColor.b, LColor.b]
  , [LColor.r, LColor.r, LColor.p, LColor.p]
  , [LColor.r, LColor.b, LColor.r, LColor.b]
  , [LColor.r, LColor.p, LColor.r, LColor.p]
  , [LColor.b, LColor.r, LColor.b, LColor.r]
  , [LColor.b, LColor.b, LColor.r, LColor.r]
  , [LColor.b, LColor.b, LColor.p, LColor.p]
  , [LColor.b, LColor.p, LColor.b, LColor.p]
  , [LColor.p, LColor.r, LColor.p, LColor.r]
  , [LColor.p, LColor.b, LColor.p, LColor.b]
  , [LColor.p, LColor.p, LColor.r, LColor.r]
  , [LColor.p, LColor.p, LColor.b, LColor.b]
  ]

def tttLightComponentCountsAudit : Bool :=
  tttCompositeStateCount == 6528 &&
    tttLightCertifiedFiberIds.length == tttLightFiberCount &&
    tttLightEmptyFiberIds.length == tttLightEmptyFiberCount &&
    tttLightNonemptyFiberIds.length == tttLightNonemptyFiberCount &&
    tttLightStateCount == tttLightNonemptyFiberCount * 16 &&
    tttLargeFiberKeys.length == tttRemainingLargeFiberCount &&
    tttRemainingLargeFiberSize == 512

theorem tttLightComponentCountsAudit_ok :
    tttLightComponentCountsAudit = true := by
  decide

structure TripleComponentParentRow where
  source : Nat
  parent : Nat
  sourceLeft : Nat
  sourceMiddle : Nat
  sourceRight : Nat
  parentLeft : Nat
  parentMiddle : Nat
  parentRight : Nat
  cert : ChainComponentMoveCertificate
  deriving DecidableEq, BEq, Repr, Inhabited

def tripleRow (source parent sourceLeft sourceMiddle sourceRight
    parentLeft parentMiddle parentRight : Nat)
    (move : ChainMove) (component : List ChainEdge) :
    TripleComponentParentRow :=
  { source := source
    parent := parent
    sourceLeft := sourceLeft
    sourceMiddle := sourceMiddle
    sourceRight := sourceRight
    parentLeft := parentLeft
    parentMiddle := parentMiddle
    parentRight := parentRight
    cert := componentCert move component }

def tripleStates (left middle right : Nat) : List TauState :=
  [stateAt left, stateAt middle, stateAt right]

def tripleComponentRowValid (key : List LColor) (expected : List Nat)
    (row : TripleComponentParentRow) : Bool :=
  expected.contains row.source && expected.contains row.parent &&
    let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
    let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
    compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
      chainInputKey tttWord s == key && chainInputKey tttWord t == key &&
        (row.source == row.parent ||
          chainCertifiedKempeStep tttWord s t row.cert)

theorem tripleComponentRowValid_chainCertifiedKempeStep_of_source_beq_false
    {key : List LColor} {expected : List Nat}
    {row : TripleComponentParentRow}
    (hrow : tripleComponentRowValid key expected row = true)
    (hsource : (row.source == row.parent) = false) :
    chainCertifiedKempeStep tttWord
      (tripleStates row.sourceLeft row.sourceMiddle row.sourceRight)
      (tripleStates row.parentLeft row.parentMiddle row.parentRight)
      row.cert = true := by
  by_cases hstep :
      chainCertifiedKempeStep tttWord
        (tripleStates row.sourceLeft row.sourceMiddle row.sourceRight)
        (tripleStates row.parentLeft row.parentMiddle row.parentRight)
        row.cert = true
  · exact hstep
  · have hstepFalse :
        chainCertifiedKempeStep tttWord
          (tripleStates row.sourceLeft row.sourceMiddle row.sourceRight)
          (tripleStates row.parentLeft row.parentMiddle row.parentRight)
          row.cert = false :=
      bool_false_of_not_true hstep
    have hrowFalse : tripleComponentRowValid key expected row = false := by
      simp [tripleComponentRowValid, hsource, hstepFalse]
    rw [hrow] at hrowFalse
    cases hrowFalse

theorem tripleComponentRowValid_chainSingleKempeStep_of_source_beq_false
    {key : List LColor} {expected : List Nat}
    {row : TripleComponentParentRow}
    (hrow : tripleComponentRowValid key expected row = true)
    (hsource : (row.source == row.parent) = false)
    (hcolorPair :
      colorPairs.contains (row.cert.move.a, row.cert.move.c) = true)
    (hnodup : row.cert.component.Nodup) :
    chainSingleKempeStep tttWord
      (tripleStates row.sourceLeft row.sourceMiddle row.sourceRight)
      (tripleStates row.parentLeft row.parentMiddle row.parentRight) = true :=
  chainCertifiedKempeStep_implies_single tttWord
    (tripleStates row.sourceLeft row.sourceMiddle row.sourceRight)
    (tripleStates row.parentLeft row.parentMiddle row.parentRight)
    row.cert hcolorPair hnodup
    (tripleComponentRowValid_chainCertifiedKempeStep_of_source_beq_false
      hrow hsource)

theorem tripleComponentRowValid_source_eq_or_chainSingleKempeStep
    {key : List LColor} {expected : List Nat}
    {row : TripleComponentParentRow}
    (hrow : tripleComponentRowValid key expected row = true)
    (hcolorPair :
      colorPairs.contains (row.cert.move.a, row.cert.move.c) = true)
    (hnodup : row.cert.component.Nodup) :
    row.source = row.parent ∨
      chainSingleKempeStep tttWord
        (tripleStates row.sourceLeft row.sourceMiddle row.sourceRight)
        (tripleStates row.parentLeft row.parentMiddle row.parentRight) =
          true := by
  by_cases hsourceTrue : (row.source == row.parent) = true
  · exact Or.inl (by simpa using hsourceTrue)
  · exact Or.inr
      (tripleComponentRowValid_chainSingleKempeStep_of_source_beq_false
        hrow (bool_false_of_not_true hsourceTrue) hcolorPair hnodup)

def tripleComponentRowSingleStepSideConditions
    (row : TripleComponentParentRow) : Bool :=
  colorPairs.contains (row.cert.move.a, row.cert.move.c)
    && decide row.cert.component.Nodup

def tripleComponentRowSingleStepReady
    (row : TripleComponentParentRow) : Bool :=
  (row.source == row.parent)
    || tripleComponentRowSingleStepSideConditions row

def tripleComponentRowValidWithSingleStepReady
    (key : List LColor) (expected : List Nat)
    (row : TripleComponentParentRow) : Bool :=
  tripleComponentRowValid key expected row
    && tripleComponentRowSingleStepReady row

theorem tripleComponentRowValid_source_eq_or_chainSingleKempeStep_of_ready
    {key : List LColor} {expected : List Nat}
    {row : TripleComponentParentRow}
    (hrow : tripleComponentRowValid key expected row = true)
    (hready : tripleComponentRowSingleStepReady row = true) :
    row.source = row.parent ∨
      chainSingleKempeStep tttWord
        (tripleStates row.sourceLeft row.sourceMiddle row.sourceRight)
        (tripleStates row.parentLeft row.parentMiddle row.parentRight) =
          true := by
  by_cases hsourceTrue : (row.source == row.parent) = true
  · exact Or.inl (by simpa using hsourceTrue)
  · have hsourceFalse : (row.source == row.parent) = false :=
      bool_false_of_not_true hsourceTrue
    have hside :
        tripleComponentRowSingleStepSideConditions row = true := by
      simpa [tripleComponentRowSingleStepReady, hsourceFalse] using hready
    rw [tripleComponentRowSingleStepSideConditions, Bool.and_eq_true] at hside
    exact Or.inr
      (tripleComponentRowValid_chainSingleKempeStep_of_source_beq_false
        hrow hsourceFalse hside.1 (of_decide_eq_true hside.2))

def tripleParentFromRows : List TripleComponentParentRow -> Nat -> Nat
  | [], i => i
  | row :: rows, i =>
      if row.source == i then row.parent else tripleParentFromRows rows i

def tripleParentIter
    (rows : List TripleComponentParentRow) : Nat -> Nat -> Nat
  | 0, i => i
  | n + 1, i => tripleParentIter rows n (tripleParentFromRows rows i)


def tttFiber0Key : List LColor :=
  [LColor.r, LColor.r, LColor.r, LColor.r]

def tttFiber0Expected : List Nat :=
  []

def tttFiber0Rows : List TripleComponentParentRow :=
  []

def tttFiber0SourcesCheck : Bool :=
  (tttFiber0Rows.map fun row => row.source) == tttFiber0Expected

theorem tttFiber0SourcesCheck_ok :
    tttFiber0SourcesCheck = true := by
  decide

def tttFiber0CertificateAudit : Bool :=
  tttFiber0SourcesCheck

theorem tttFiber0CertificateAudit_ok :
    tttFiber0CertificateAudit = true := by
  simp [tttFiber0CertificateAudit,
    tttFiber0SourcesCheck_ok]

def tttFiber1Key : List LColor :=
  [LColor.r, LColor.r, LColor.r, LColor.b]

def tttFiber1Expected : List Nat :=
  []

def tttFiber1Rows : List TripleComponentParentRow :=
  []

def tttFiber1SourcesCheck : Bool :=
  (tttFiber1Rows.map fun row => row.source) == tttFiber1Expected

theorem tttFiber1SourcesCheck_ok :
    tttFiber1SourcesCheck = true := by
  decide

def tttFiber1CertificateAudit : Bool :=
  tttFiber1SourcesCheck

theorem tttFiber1CertificateAudit_ok :
    tttFiber1CertificateAudit = true := by
  simp [tttFiber1CertificateAudit,
    tttFiber1SourcesCheck_ok]

def tttFiber2Key : List LColor :=
  [LColor.r, LColor.r, LColor.r, LColor.p]

def tttFiber2Expected : List Nat :=
  []

def tttFiber2Rows : List TripleComponentParentRow :=
  []

def tttFiber2SourcesCheck : Bool :=
  (tttFiber2Rows.map fun row => row.source) == tttFiber2Expected

theorem tttFiber2SourcesCheck_ok :
    tttFiber2SourcesCheck = true := by
  decide

def tttFiber2CertificateAudit : Bool :=
  tttFiber2SourcesCheck

theorem tttFiber2CertificateAudit_ok :
    tttFiber2CertificateAudit = true := by
  simp [tttFiber2CertificateAudit,
    tttFiber2SourcesCheck_ok]

def tttFiber3Key : List LColor :=
  [LColor.r, LColor.r, LColor.b, LColor.r]

def tttFiber3Expected : List Nat :=
  [3808, 3809, 3810, 3811, 3812, 3813, 3814, 3815,
   3816, 3817, 3818, 3819, 3820, 3821, 3822, 3823]

def tttFiber3Row0 : TripleComponentParentRow :=
  tripleRow 3808 3808 114 54 112 114 54 112
    default
    []

def tttFiber3Row1 : TripleComponentParentRow :=
  tripleRow 3809 3808 114 54 113 114 54 112
    (chainMove LColor.r LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber3Row2 : TripleComponentParentRow :=
  tripleRow 3810 3808 114 54 114 114 54 112
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber3Row3 : TripleComponentParentRow :=
  tripleRow 3811 3809 114 54 115 114 54 113
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber3Row4 : TripleComponentParentRow :=
  tripleRow 3812 3808 114 55 120 114 54 112
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber3Row5 : TripleComponentParentRow :=
  tripleRow 3813 3809 114 55 121 114 54 113
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber3Row6 : TripleComponentParentRow :=
  tripleRow 3814 3810 114 55 122 114 54 114
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber3Row7 : TripleComponentParentRow :=
  tripleRow 3815 3811 114 55 123 114 54 115
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber3Row8 : TripleComponentParentRow :=
  tripleRow 3816 3808 115 62 112 114 54 112
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber3Row9 : TripleComponentParentRow :=
  tripleRow 3817 3809 115 62 113 114 54 113
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber3Row10 : TripleComponentParentRow :=
  tripleRow 3818 3810 115 62 114 114 54 114
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber3Row11 : TripleComponentParentRow :=
  tripleRow 3819 3811 115 62 115 114 54 115
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber3Row12 : TripleComponentParentRow :=
  tripleRow 3820 3812 115 63 120 114 55 120
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber3Row13 : TripleComponentParentRow :=
  tripleRow 3821 3813 115 63 121 114 55 121
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber3Row14 : TripleComponentParentRow :=
  tripleRow 3822 3814 115 63 122 114 55 122
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber3Row15 : TripleComponentParentRow :=
  tripleRow 3823 3815 115 63 123 114 55 123
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber3Rows : List TripleComponentParentRow :=
  [ tttFiber3Row0
  , tttFiber3Row1
  , tttFiber3Row2
  , tttFiber3Row3
  , tttFiber3Row4
  , tttFiber3Row5
  , tttFiber3Row6
  , tttFiber3Row7
  , tttFiber3Row8
  , tttFiber3Row9
  , tttFiber3Row10
  , tttFiber3Row11
  , tttFiber3Row12
  , tttFiber3Row13
  , tttFiber3Row14
  , tttFiber3Row15
  ]

def tttFiber3SourcesCheck : Bool :=
  (tttFiber3Rows.map fun row => row.source) == tttFiber3Expected

theorem tttFiber3SourcesCheck_ok :
    tttFiber3SourcesCheck = true := by
  decide

def tttFiber3RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber3Key tttFiber3Expected
    (listGetD tttFiber3Rows i default)

theorem tttFiber3Row_0_ok : tttFiber3RowCheck 0 = true := by
  decide
theorem tttFiber3Row_1_ok : tttFiber3RowCheck 1 = true := by
  decide
theorem tttFiber3Row_2_ok : tttFiber3RowCheck 2 = true := by
  decide
theorem tttFiber3Row_3_ok : tttFiber3RowCheck 3 = true := by
  decide
theorem tttFiber3Row_4_ok : tttFiber3RowCheck 4 = true := by
  decide
theorem tttFiber3Row_5_ok : tttFiber3RowCheck 5 = true := by
  decide
theorem tttFiber3Row_6_ok : tttFiber3RowCheck 6 = true := by
  decide
theorem tttFiber3Row_7_ok : tttFiber3RowCheck 7 = true := by
  decide
theorem tttFiber3Row_8_ok : tttFiber3RowCheck 8 = true := by
  decide
theorem tttFiber3Row_9_ok : tttFiber3RowCheck 9 = true := by
  decide
theorem tttFiber3Row_10_ok : tttFiber3RowCheck 10 = true := by
  decide
theorem tttFiber3Row_11_ok : tttFiber3RowCheck 11 = true := by
  decide
theorem tttFiber3Row_12_ok : tttFiber3RowCheck 12 = true := by
  decide
theorem tttFiber3Row_13_ok : tttFiber3RowCheck 13 = true := by
  decide
theorem tttFiber3Row_14_ok : tttFiber3RowCheck 14 = true := by
  decide
theorem tttFiber3Row_15_ok : tttFiber3RowCheck 15 = true := by
  decide

def tttFiber3ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber3Rows tttLightMaxParentDepth
    (listGetD tttFiber3Expected i 0) == 3808

theorem tttFiber3Parent_0_ok : tttFiber3ParentCheck 0 = true := by
  decide
theorem tttFiber3Parent_1_ok : tttFiber3ParentCheck 1 = true := by
  decide
theorem tttFiber3Parent_2_ok : tttFiber3ParentCheck 2 = true := by
  decide
theorem tttFiber3Parent_3_ok : tttFiber3ParentCheck 3 = true := by
  decide
theorem tttFiber3Parent_4_ok : tttFiber3ParentCheck 4 = true := by
  decide
theorem tttFiber3Parent_5_ok : tttFiber3ParentCheck 5 = true := by
  decide
theorem tttFiber3Parent_6_ok : tttFiber3ParentCheck 6 = true := by
  decide
theorem tttFiber3Parent_7_ok : tttFiber3ParentCheck 7 = true := by
  decide
theorem tttFiber3Parent_8_ok : tttFiber3ParentCheck 8 = true := by
  decide
theorem tttFiber3Parent_9_ok : tttFiber3ParentCheck 9 = true := by
  decide
theorem tttFiber3Parent_10_ok : tttFiber3ParentCheck 10 = true := by
  decide
theorem tttFiber3Parent_11_ok : tttFiber3ParentCheck 11 = true := by
  decide
theorem tttFiber3Parent_12_ok : tttFiber3ParentCheck 12 = true := by
  decide
theorem tttFiber3Parent_13_ok : tttFiber3ParentCheck 13 = true := by
  decide
theorem tttFiber3Parent_14_ok : tttFiber3ParentCheck 14 = true := by
  decide
theorem tttFiber3Parent_15_ok : tttFiber3ParentCheck 15 = true := by
  decide

def tttFiber3CertificateAudit : Bool :=
  tttFiber3SourcesCheck
    && tttFiber3RowCheck 0
    && tttFiber3RowCheck 1
    && tttFiber3RowCheck 2
    && tttFiber3RowCheck 3
    && tttFiber3RowCheck 4
    && tttFiber3RowCheck 5
    && tttFiber3RowCheck 6
    && tttFiber3RowCheck 7
    && tttFiber3RowCheck 8
    && tttFiber3RowCheck 9
    && tttFiber3RowCheck 10
    && tttFiber3RowCheck 11
    && tttFiber3RowCheck 12
    && tttFiber3RowCheck 13
    && tttFiber3RowCheck 14
    && tttFiber3RowCheck 15
    && tttFiber3ParentCheck 0
    && tttFiber3ParentCheck 1
    && tttFiber3ParentCheck 2
    && tttFiber3ParentCheck 3
    && tttFiber3ParentCheck 4
    && tttFiber3ParentCheck 5
    && tttFiber3ParentCheck 6
    && tttFiber3ParentCheck 7
    && tttFiber3ParentCheck 8
    && tttFiber3ParentCheck 9
    && tttFiber3ParentCheck 10
    && tttFiber3ParentCheck 11
    && tttFiber3ParentCheck 12
    && tttFiber3ParentCheck 13
    && tttFiber3ParentCheck 14
    && tttFiber3ParentCheck 15

theorem tttFiber3CertificateAudit_ok :
    tttFiber3CertificateAudit = true := by
  simp [tttFiber3CertificateAudit,
    tttFiber3SourcesCheck_ok,
    tttFiber3Row_0_ok,
    tttFiber3Row_1_ok,
    tttFiber3Row_2_ok,
    tttFiber3Row_3_ok,
    tttFiber3Row_4_ok,
    tttFiber3Row_5_ok,
    tttFiber3Row_6_ok,
    tttFiber3Row_7_ok,
    tttFiber3Row_8_ok,
    tttFiber3Row_9_ok,
    tttFiber3Row_10_ok,
    tttFiber3Row_11_ok,
    tttFiber3Row_12_ok,
    tttFiber3Row_13_ok,
    tttFiber3Row_14_ok,
    tttFiber3Row_15_ok,
    tttFiber3Parent_0_ok,
    tttFiber3Parent_1_ok,
    tttFiber3Parent_2_ok,
    tttFiber3Parent_3_ok,
    tttFiber3Parent_4_ok,
    tttFiber3Parent_5_ok,
    tttFiber3Parent_6_ok,
    tttFiber3Parent_7_ok,
    tttFiber3Parent_8_ok,
    tttFiber3Parent_9_ok,
    tttFiber3Parent_10_ok,
    tttFiber3Parent_11_ok,
    tttFiber3Parent_12_ok,
    tttFiber3Parent_13_ok,
    tttFiber3Parent_14_ok,
    tttFiber3Parent_15_ok]

def tttFiber5Key : List LColor :=
  [LColor.r, LColor.r, LColor.b, LColor.p]

def tttFiber5Expected : List Nat :=
  [2432, 2433, 2434, 2435, 2436, 2437, 2438, 2439,
   2440, 2441, 2442, 2443, 2444, 2445, 2446, 2447]

def tttFiber5Row0 : TripleComponentParentRow :=
  tripleRow 2432 2432 68 144 84 68 144 84
    default
    []

def tttFiber5Row1 : TripleComponentParentRow :=
  tripleRow 2433 2432 68 144 85 68 144 84
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber5Row2 : TripleComponentParentRow :=
  tripleRow 2434 2432 68 144 86 68 144 84
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber5Row3 : TripleComponentParentRow :=
  tripleRow 2435 2433 68 144 87 68 144 85
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber5Row4 : TripleComponentParentRow :=
  tripleRow 2436 2432 68 145 92 68 144 84
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber5Row5 : TripleComponentParentRow :=
  tripleRow 2437 2433 68 145 93 68 144 85
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber5Row6 : TripleComponentParentRow :=
  tripleRow 2438 2434 68 145 94 68 144 86
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber5Row7 : TripleComponentParentRow :=
  tripleRow 2439 2435 68 145 95 68 144 87
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber5Row8 : TripleComponentParentRow :=
  tripleRow 2440 2432 69 152 84 68 144 84
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber5Row9 : TripleComponentParentRow :=
  tripleRow 2441 2433 69 152 85 68 144 85
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber5Row10 : TripleComponentParentRow :=
  tripleRow 2442 2434 69 152 86 68 144 86
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber5Row11 : TripleComponentParentRow :=
  tripleRow 2443 2435 69 152 87 68 144 87
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber5Row12 : TripleComponentParentRow :=
  tripleRow 2444 2436 69 153 92 68 145 92
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber5Row13 : TripleComponentParentRow :=
  tripleRow 2445 2437 69 153 93 68 145 93
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber5Row14 : TripleComponentParentRow :=
  tripleRow 2446 2438 69 153 94 68 145 94
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber5Row15 : TripleComponentParentRow :=
  tripleRow 2447 2439 69 153 95 68 145 95
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber5Rows : List TripleComponentParentRow :=
  [ tttFiber5Row0
  , tttFiber5Row1
  , tttFiber5Row2
  , tttFiber5Row3
  , tttFiber5Row4
  , tttFiber5Row5
  , tttFiber5Row6
  , tttFiber5Row7
  , tttFiber5Row8
  , tttFiber5Row9
  , tttFiber5Row10
  , tttFiber5Row11
  , tttFiber5Row12
  , tttFiber5Row13
  , tttFiber5Row14
  , tttFiber5Row15
  ]

def tttFiber5SourcesCheck : Bool :=
  (tttFiber5Rows.map fun row => row.source) == tttFiber5Expected

theorem tttFiber5SourcesCheck_ok :
    tttFiber5SourcesCheck = true := by
  decide

def tttFiber5RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber5Key tttFiber5Expected
    (listGetD tttFiber5Rows i default)

theorem tttFiber5Row_0_ok : tttFiber5RowCheck 0 = true := by
  decide
theorem tttFiber5Row_1_ok : tttFiber5RowCheck 1 = true := by
  decide
theorem tttFiber5Row_2_ok : tttFiber5RowCheck 2 = true := by
  decide
theorem tttFiber5Row_3_ok : tttFiber5RowCheck 3 = true := by
  decide
theorem tttFiber5Row_4_ok : tttFiber5RowCheck 4 = true := by
  decide
theorem tttFiber5Row_5_ok : tttFiber5RowCheck 5 = true := by
  decide
theorem tttFiber5Row_6_ok : tttFiber5RowCheck 6 = true := by
  decide
theorem tttFiber5Row_7_ok : tttFiber5RowCheck 7 = true := by
  decide
theorem tttFiber5Row_8_ok : tttFiber5RowCheck 8 = true := by
  decide
theorem tttFiber5Row_9_ok : tttFiber5RowCheck 9 = true := by
  decide
theorem tttFiber5Row_10_ok : tttFiber5RowCheck 10 = true := by
  decide
theorem tttFiber5Row_11_ok : tttFiber5RowCheck 11 = true := by
  decide
theorem tttFiber5Row_12_ok : tttFiber5RowCheck 12 = true := by
  decide
theorem tttFiber5Row_13_ok : tttFiber5RowCheck 13 = true := by
  decide
theorem tttFiber5Row_14_ok : tttFiber5RowCheck 14 = true := by
  decide
theorem tttFiber5Row_15_ok : tttFiber5RowCheck 15 = true := by
  decide

def tttFiber5ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber5Rows tttLightMaxParentDepth
    (listGetD tttFiber5Expected i 0) == 2432

theorem tttFiber5Parent_0_ok : tttFiber5ParentCheck 0 = true := by
  decide
theorem tttFiber5Parent_1_ok : tttFiber5ParentCheck 1 = true := by
  decide
theorem tttFiber5Parent_2_ok : tttFiber5ParentCheck 2 = true := by
  decide
theorem tttFiber5Parent_3_ok : tttFiber5ParentCheck 3 = true := by
  decide
theorem tttFiber5Parent_4_ok : tttFiber5ParentCheck 4 = true := by
  decide
theorem tttFiber5Parent_5_ok : tttFiber5ParentCheck 5 = true := by
  decide
theorem tttFiber5Parent_6_ok : tttFiber5ParentCheck 6 = true := by
  decide
theorem tttFiber5Parent_7_ok : tttFiber5ParentCheck 7 = true := by
  decide
theorem tttFiber5Parent_8_ok : tttFiber5ParentCheck 8 = true := by
  decide
theorem tttFiber5Parent_9_ok : tttFiber5ParentCheck 9 = true := by
  decide
theorem tttFiber5Parent_10_ok : tttFiber5ParentCheck 10 = true := by
  decide
theorem tttFiber5Parent_11_ok : tttFiber5ParentCheck 11 = true := by
  decide
theorem tttFiber5Parent_12_ok : tttFiber5ParentCheck 12 = true := by
  decide
theorem tttFiber5Parent_13_ok : tttFiber5ParentCheck 13 = true := by
  decide
theorem tttFiber5Parent_14_ok : tttFiber5ParentCheck 14 = true := by
  decide
theorem tttFiber5Parent_15_ok : tttFiber5ParentCheck 15 = true := by
  decide

def tttFiber5CertificateAudit : Bool :=
  tttFiber5SourcesCheck
    && tttFiber5RowCheck 0
    && tttFiber5RowCheck 1
    && tttFiber5RowCheck 2
    && tttFiber5RowCheck 3
    && tttFiber5RowCheck 4
    && tttFiber5RowCheck 5
    && tttFiber5RowCheck 6
    && tttFiber5RowCheck 7
    && tttFiber5RowCheck 8
    && tttFiber5RowCheck 9
    && tttFiber5RowCheck 10
    && tttFiber5RowCheck 11
    && tttFiber5RowCheck 12
    && tttFiber5RowCheck 13
    && tttFiber5RowCheck 14
    && tttFiber5RowCheck 15
    && tttFiber5ParentCheck 0
    && tttFiber5ParentCheck 1
    && tttFiber5ParentCheck 2
    && tttFiber5ParentCheck 3
    && tttFiber5ParentCheck 4
    && tttFiber5ParentCheck 5
    && tttFiber5ParentCheck 6
    && tttFiber5ParentCheck 7
    && tttFiber5ParentCheck 8
    && tttFiber5ParentCheck 9
    && tttFiber5ParentCheck 10
    && tttFiber5ParentCheck 11
    && tttFiber5ParentCheck 12
    && tttFiber5ParentCheck 13
    && tttFiber5ParentCheck 14
    && tttFiber5ParentCheck 15

theorem tttFiber5CertificateAudit_ok :
    tttFiber5CertificateAudit = true := by
  simp [tttFiber5CertificateAudit,
    tttFiber5SourcesCheck_ok,
    tttFiber5Row_0_ok,
    tttFiber5Row_1_ok,
    tttFiber5Row_2_ok,
    tttFiber5Row_3_ok,
    tttFiber5Row_4_ok,
    tttFiber5Row_5_ok,
    tttFiber5Row_6_ok,
    tttFiber5Row_7_ok,
    tttFiber5Row_8_ok,
    tttFiber5Row_9_ok,
    tttFiber5Row_10_ok,
    tttFiber5Row_11_ok,
    tttFiber5Row_12_ok,
    tttFiber5Row_13_ok,
    tttFiber5Row_14_ok,
    tttFiber5Row_15_ok,
    tttFiber5Parent_0_ok,
    tttFiber5Parent_1_ok,
    tttFiber5Parent_2_ok,
    tttFiber5Parent_3_ok,
    tttFiber5Parent_4_ok,
    tttFiber5Parent_5_ok,
    tttFiber5Parent_6_ok,
    tttFiber5Parent_7_ok,
    tttFiber5Parent_8_ok,
    tttFiber5Parent_9_ok,
    tttFiber5Parent_10_ok,
    tttFiber5Parent_11_ok,
    tttFiber5Parent_12_ok,
    tttFiber5Parent_13_ok,
    tttFiber5Parent_14_ok,
    tttFiber5Parent_15_ok]

def tttFiber6Key : List LColor :=
  [LColor.r, LColor.r, LColor.p, LColor.r]

def tttFiber6Expected : List Nat :=
  [5984, 5985, 5986, 5987, 5988, 5989, 5990, 5991,
   5992, 5993, 5994, 5995, 5996, 5997, 5998, 5999]

def tttFiber6Row0 : TripleComponentParentRow :=
  tripleRow 5984 5984 176 22 176 176 22 176
    default
    []

def tttFiber6Row1 : TripleComponentParentRow :=
  tripleRow 5985 5984 176 22 177 176 22 176
    (chainMove LColor.r LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber6Row2 : TripleComponentParentRow :=
  tripleRow 5986 5984 176 22 178 176 22 176
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber6Row3 : TripleComponentParentRow :=
  tripleRow 5987 5985 176 22 179 176 22 177
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber6Row4 : TripleComponentParentRow :=
  tripleRow 5988 5984 176 23 184 176 22 176
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber6Row5 : TripleComponentParentRow :=
  tripleRow 5989 5985 176 23 185 176 22 177
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber6Row6 : TripleComponentParentRow :=
  tripleRow 5990 5986 176 23 186 176 22 178
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber6Row7 : TripleComponentParentRow :=
  tripleRow 5991 5987 176 23 187 176 22 179
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber6Row8 : TripleComponentParentRow :=
  tripleRow 5992 5984 177 30 176 176 22 176
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber6Row9 : TripleComponentParentRow :=
  tripleRow 5993 5985 177 30 177 176 22 177
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber6Row10 : TripleComponentParentRow :=
  tripleRow 5994 5986 177 30 178 176 22 178
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber6Row11 : TripleComponentParentRow :=
  tripleRow 5995 5987 177 30 179 176 22 179
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber6Row12 : TripleComponentParentRow :=
  tripleRow 5996 5988 177 31 184 176 23 184
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber6Row13 : TripleComponentParentRow :=
  tripleRow 5997 5989 177 31 185 176 23 185
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber6Row14 : TripleComponentParentRow :=
  tripleRow 5998 5990 177 31 186 176 23 186
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber6Row15 : TripleComponentParentRow :=
  tripleRow 5999 5991 177 31 187 176 23 187
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber6Rows : List TripleComponentParentRow :=
  [ tttFiber6Row0
  , tttFiber6Row1
  , tttFiber6Row2
  , tttFiber6Row3
  , tttFiber6Row4
  , tttFiber6Row5
  , tttFiber6Row6
  , tttFiber6Row7
  , tttFiber6Row8
  , tttFiber6Row9
  , tttFiber6Row10
  , tttFiber6Row11
  , tttFiber6Row12
  , tttFiber6Row13
  , tttFiber6Row14
  , tttFiber6Row15
  ]

def tttFiber6SourcesCheck : Bool :=
  (tttFiber6Rows.map fun row => row.source) == tttFiber6Expected

theorem tttFiber6SourcesCheck_ok :
    tttFiber6SourcesCheck = true := by
  decide

def tttFiber6RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber6Key tttFiber6Expected
    (listGetD tttFiber6Rows i default)

theorem tttFiber6Row_0_ok : tttFiber6RowCheck 0 = true := by
  decide
theorem tttFiber6Row_1_ok : tttFiber6RowCheck 1 = true := by
  decide
theorem tttFiber6Row_2_ok : tttFiber6RowCheck 2 = true := by
  decide
theorem tttFiber6Row_3_ok : tttFiber6RowCheck 3 = true := by
  decide
theorem tttFiber6Row_4_ok : tttFiber6RowCheck 4 = true := by
  decide
theorem tttFiber6Row_5_ok : tttFiber6RowCheck 5 = true := by
  decide
theorem tttFiber6Row_6_ok : tttFiber6RowCheck 6 = true := by
  decide
theorem tttFiber6Row_7_ok : tttFiber6RowCheck 7 = true := by
  decide
theorem tttFiber6Row_8_ok : tttFiber6RowCheck 8 = true := by
  decide
theorem tttFiber6Row_9_ok : tttFiber6RowCheck 9 = true := by
  decide
theorem tttFiber6Row_10_ok : tttFiber6RowCheck 10 = true := by
  decide
theorem tttFiber6Row_11_ok : tttFiber6RowCheck 11 = true := by
  decide
theorem tttFiber6Row_12_ok : tttFiber6RowCheck 12 = true := by
  decide
theorem tttFiber6Row_13_ok : tttFiber6RowCheck 13 = true := by
  decide
theorem tttFiber6Row_14_ok : tttFiber6RowCheck 14 = true := by
  decide
theorem tttFiber6Row_15_ok : tttFiber6RowCheck 15 = true := by
  decide

def tttFiber6ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber6Rows tttLightMaxParentDepth
    (listGetD tttFiber6Expected i 0) == 5984

theorem tttFiber6Parent_0_ok : tttFiber6ParentCheck 0 = true := by
  decide
theorem tttFiber6Parent_1_ok : tttFiber6ParentCheck 1 = true := by
  decide
theorem tttFiber6Parent_2_ok : tttFiber6ParentCheck 2 = true := by
  decide
theorem tttFiber6Parent_3_ok : tttFiber6ParentCheck 3 = true := by
  decide
theorem tttFiber6Parent_4_ok : tttFiber6ParentCheck 4 = true := by
  decide
theorem tttFiber6Parent_5_ok : tttFiber6ParentCheck 5 = true := by
  decide
theorem tttFiber6Parent_6_ok : tttFiber6ParentCheck 6 = true := by
  decide
theorem tttFiber6Parent_7_ok : tttFiber6ParentCheck 7 = true := by
  decide
theorem tttFiber6Parent_8_ok : tttFiber6ParentCheck 8 = true := by
  decide
theorem tttFiber6Parent_9_ok : tttFiber6ParentCheck 9 = true := by
  decide
theorem tttFiber6Parent_10_ok : tttFiber6ParentCheck 10 = true := by
  decide
theorem tttFiber6Parent_11_ok : tttFiber6ParentCheck 11 = true := by
  decide
theorem tttFiber6Parent_12_ok : tttFiber6ParentCheck 12 = true := by
  decide
theorem tttFiber6Parent_13_ok : tttFiber6ParentCheck 13 = true := by
  decide
theorem tttFiber6Parent_14_ok : tttFiber6ParentCheck 14 = true := by
  decide
theorem tttFiber6Parent_15_ok : tttFiber6ParentCheck 15 = true := by
  decide

def tttFiber6CertificateAudit : Bool :=
  tttFiber6SourcesCheck
    && tttFiber6RowCheck 0
    && tttFiber6RowCheck 1
    && tttFiber6RowCheck 2
    && tttFiber6RowCheck 3
    && tttFiber6RowCheck 4
    && tttFiber6RowCheck 5
    && tttFiber6RowCheck 6
    && tttFiber6RowCheck 7
    && tttFiber6RowCheck 8
    && tttFiber6RowCheck 9
    && tttFiber6RowCheck 10
    && tttFiber6RowCheck 11
    && tttFiber6RowCheck 12
    && tttFiber6RowCheck 13
    && tttFiber6RowCheck 14
    && tttFiber6RowCheck 15
    && tttFiber6ParentCheck 0
    && tttFiber6ParentCheck 1
    && tttFiber6ParentCheck 2
    && tttFiber6ParentCheck 3
    && tttFiber6ParentCheck 4
    && tttFiber6ParentCheck 5
    && tttFiber6ParentCheck 6
    && tttFiber6ParentCheck 7
    && tttFiber6ParentCheck 8
    && tttFiber6ParentCheck 9
    && tttFiber6ParentCheck 10
    && tttFiber6ParentCheck 11
    && tttFiber6ParentCheck 12
    && tttFiber6ParentCheck 13
    && tttFiber6ParentCheck 14
    && tttFiber6ParentCheck 15

theorem tttFiber6CertificateAudit_ok :
    tttFiber6CertificateAudit = true := by
  simp [tttFiber6CertificateAudit,
    tttFiber6SourcesCheck_ok,
    tttFiber6Row_0_ok,
    tttFiber6Row_1_ok,
    tttFiber6Row_2_ok,
    tttFiber6Row_3_ok,
    tttFiber6Row_4_ok,
    tttFiber6Row_5_ok,
    tttFiber6Row_6_ok,
    tttFiber6Row_7_ok,
    tttFiber6Row_8_ok,
    tttFiber6Row_9_ok,
    tttFiber6Row_10_ok,
    tttFiber6Row_11_ok,
    tttFiber6Row_12_ok,
    tttFiber6Row_13_ok,
    tttFiber6Row_14_ok,
    tttFiber6Row_15_ok,
    tttFiber6Parent_0_ok,
    tttFiber6Parent_1_ok,
    tttFiber6Parent_2_ok,
    tttFiber6Parent_3_ok,
    tttFiber6Parent_4_ok,
    tttFiber6Parent_5_ok,
    tttFiber6Parent_6_ok,
    tttFiber6Parent_7_ok,
    tttFiber6Parent_8_ok,
    tttFiber6Parent_9_ok,
    tttFiber6Parent_10_ok,
    tttFiber6Parent_11_ok,
    tttFiber6Parent_12_ok,
    tttFiber6Parent_13_ok,
    tttFiber6Parent_14_ok,
    tttFiber6Parent_15_ok]

def tttFiber7Key : List LColor :=
  [LColor.r, LColor.r, LColor.p, LColor.b]

def tttFiber7Expected : List Nat :=
  [4352, 4353, 4354, 4355, 4356, 4357, 4358, 4359,
   4360, 4361, 4362, 4363, 4364, 4365, 4366, 4367]

def tttFiber7Row0 : TripleComponentParentRow :=
  tripleRow 4352 4352 128 84 144 128 84 144
    default
    []

def tttFiber7Row1 : TripleComponentParentRow :=
  tripleRow 4353 4352 128 84 145 128 84 144
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber7Row2 : TripleComponentParentRow :=
  tripleRow 4354 4353 128 84 146 128 84 145
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber7Row3 : TripleComponentParentRow :=
  tripleRow 4355 4352 128 84 147 128 84 144
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber7Row4 : TripleComponentParentRow :=
  tripleRow 4356 4352 128 85 152 128 84 144
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber7Row5 : TripleComponentParentRow :=
  tripleRow 4357 4353 128 85 153 128 84 145
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber7Row6 : TripleComponentParentRow :=
  tripleRow 4358 4354 128 85 154 128 84 146
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber7Row7 : TripleComponentParentRow :=
  tripleRow 4359 4355 128 85 155 128 84 147
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber7Row8 : TripleComponentParentRow :=
  tripleRow 4360 4352 129 92 144 128 84 144
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber7Row9 : TripleComponentParentRow :=
  tripleRow 4361 4353 129 92 145 128 84 145
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber7Row10 : TripleComponentParentRow :=
  tripleRow 4362 4354 129 92 146 128 84 146
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber7Row11 : TripleComponentParentRow :=
  tripleRow 4363 4355 129 92 147 128 84 147
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber7Row12 : TripleComponentParentRow :=
  tripleRow 4364 4356 129 93 152 128 85 152
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber7Row13 : TripleComponentParentRow :=
  tripleRow 4365 4357 129 93 153 128 85 153
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber7Row14 : TripleComponentParentRow :=
  tripleRow 4366 4358 129 93 154 128 85 154
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber7Row15 : TripleComponentParentRow :=
  tripleRow 4367 4359 129 93 155 128 85 155
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber7Rows : List TripleComponentParentRow :=
  [ tttFiber7Row0
  , tttFiber7Row1
  , tttFiber7Row2
  , tttFiber7Row3
  , tttFiber7Row4
  , tttFiber7Row5
  , tttFiber7Row6
  , tttFiber7Row7
  , tttFiber7Row8
  , tttFiber7Row9
  , tttFiber7Row10
  , tttFiber7Row11
  , tttFiber7Row12
  , tttFiber7Row13
  , tttFiber7Row14
  , tttFiber7Row15
  ]

def tttFiber7SourcesCheck : Bool :=
  (tttFiber7Rows.map fun row => row.source) == tttFiber7Expected

theorem tttFiber7SourcesCheck_ok :
    tttFiber7SourcesCheck = true := by
  decide

def tttFiber7RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber7Key tttFiber7Expected
    (listGetD tttFiber7Rows i default)

theorem tttFiber7Row_0_ok : tttFiber7RowCheck 0 = true := by
  decide
theorem tttFiber7Row_1_ok : tttFiber7RowCheck 1 = true := by
  decide
theorem tttFiber7Row_2_ok : tttFiber7RowCheck 2 = true := by
  decide
theorem tttFiber7Row_3_ok : tttFiber7RowCheck 3 = true := by
  decide
theorem tttFiber7Row_4_ok : tttFiber7RowCheck 4 = true := by
  decide
theorem tttFiber7Row_5_ok : tttFiber7RowCheck 5 = true := by
  decide
theorem tttFiber7Row_6_ok : tttFiber7RowCheck 6 = true := by
  decide
theorem tttFiber7Row_7_ok : tttFiber7RowCheck 7 = true := by
  decide
theorem tttFiber7Row_8_ok : tttFiber7RowCheck 8 = true := by
  decide
theorem tttFiber7Row_9_ok : tttFiber7RowCheck 9 = true := by
  decide
theorem tttFiber7Row_10_ok : tttFiber7RowCheck 10 = true := by
  decide
theorem tttFiber7Row_11_ok : tttFiber7RowCheck 11 = true := by
  decide
theorem tttFiber7Row_12_ok : tttFiber7RowCheck 12 = true := by
  decide
theorem tttFiber7Row_13_ok : tttFiber7RowCheck 13 = true := by
  decide
theorem tttFiber7Row_14_ok : tttFiber7RowCheck 14 = true := by
  decide
theorem tttFiber7Row_15_ok : tttFiber7RowCheck 15 = true := by
  decide

def tttFiber7ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber7Rows tttLightMaxParentDepth
    (listGetD tttFiber7Expected i 0) == 4352

theorem tttFiber7Parent_0_ok : tttFiber7ParentCheck 0 = true := by
  decide
theorem tttFiber7Parent_1_ok : tttFiber7ParentCheck 1 = true := by
  decide
theorem tttFiber7Parent_2_ok : tttFiber7ParentCheck 2 = true := by
  decide
theorem tttFiber7Parent_3_ok : tttFiber7ParentCheck 3 = true := by
  decide
theorem tttFiber7Parent_4_ok : tttFiber7ParentCheck 4 = true := by
  decide
theorem tttFiber7Parent_5_ok : tttFiber7ParentCheck 5 = true := by
  decide
theorem tttFiber7Parent_6_ok : tttFiber7ParentCheck 6 = true := by
  decide
theorem tttFiber7Parent_7_ok : tttFiber7ParentCheck 7 = true := by
  decide
theorem tttFiber7Parent_8_ok : tttFiber7ParentCheck 8 = true := by
  decide
theorem tttFiber7Parent_9_ok : tttFiber7ParentCheck 9 = true := by
  decide
theorem tttFiber7Parent_10_ok : tttFiber7ParentCheck 10 = true := by
  decide
theorem tttFiber7Parent_11_ok : tttFiber7ParentCheck 11 = true := by
  decide
theorem tttFiber7Parent_12_ok : tttFiber7ParentCheck 12 = true := by
  decide
theorem tttFiber7Parent_13_ok : tttFiber7ParentCheck 13 = true := by
  decide
theorem tttFiber7Parent_14_ok : tttFiber7ParentCheck 14 = true := by
  decide
theorem tttFiber7Parent_15_ok : tttFiber7ParentCheck 15 = true := by
  decide

def tttFiber7CertificateAudit : Bool :=
  tttFiber7SourcesCheck
    && tttFiber7RowCheck 0
    && tttFiber7RowCheck 1
    && tttFiber7RowCheck 2
    && tttFiber7RowCheck 3
    && tttFiber7RowCheck 4
    && tttFiber7RowCheck 5
    && tttFiber7RowCheck 6
    && tttFiber7RowCheck 7
    && tttFiber7RowCheck 8
    && tttFiber7RowCheck 9
    && tttFiber7RowCheck 10
    && tttFiber7RowCheck 11
    && tttFiber7RowCheck 12
    && tttFiber7RowCheck 13
    && tttFiber7RowCheck 14
    && tttFiber7RowCheck 15
    && tttFiber7ParentCheck 0
    && tttFiber7ParentCheck 1
    && tttFiber7ParentCheck 2
    && tttFiber7ParentCheck 3
    && tttFiber7ParentCheck 4
    && tttFiber7ParentCheck 5
    && tttFiber7ParentCheck 6
    && tttFiber7ParentCheck 7
    && tttFiber7ParentCheck 8
    && tttFiber7ParentCheck 9
    && tttFiber7ParentCheck 10
    && tttFiber7ParentCheck 11
    && tttFiber7ParentCheck 12
    && tttFiber7ParentCheck 13
    && tttFiber7ParentCheck 14
    && tttFiber7ParentCheck 15

theorem tttFiber7CertificateAudit_ok :
    tttFiber7CertificateAudit = true := by
  simp [tttFiber7CertificateAudit,
    tttFiber7SourcesCheck_ok,
    tttFiber7Row_0_ok,
    tttFiber7Row_1_ok,
    tttFiber7Row_2_ok,
    tttFiber7Row_3_ok,
    tttFiber7Row_4_ok,
    tttFiber7Row_5_ok,
    tttFiber7Row_6_ok,
    tttFiber7Row_7_ok,
    tttFiber7Row_8_ok,
    tttFiber7Row_9_ok,
    tttFiber7Row_10_ok,
    tttFiber7Row_11_ok,
    tttFiber7Row_12_ok,
    tttFiber7Row_13_ok,
    tttFiber7Row_14_ok,
    tttFiber7Row_15_ok,
    tttFiber7Parent_0_ok,
    tttFiber7Parent_1_ok,
    tttFiber7Parent_2_ok,
    tttFiber7Parent_3_ok,
    tttFiber7Parent_4_ok,
    tttFiber7Parent_5_ok,
    tttFiber7Parent_6_ok,
    tttFiber7Parent_7_ok,
    tttFiber7Parent_8_ok,
    tttFiber7Parent_9_ok,
    tttFiber7Parent_10_ok,
    tttFiber7Parent_11_ok,
    tttFiber7Parent_12_ok,
    tttFiber7Parent_13_ok,
    tttFiber7Parent_14_ok,
    tttFiber7Parent_15_ok]

def tttFiber9Key : List LColor :=
  [LColor.r, LColor.b, LColor.r, LColor.r]

def tttFiber9Expected : List Nat :=
  [4080, 4081, 4082, 4083, 4084, 4085, 4086, 4087,
   4088, 4089, 4090, 4091, 4092, 4093, 4094, 4095]

def tttFiber9Row0 : TripleComponentParentRow :=
  tripleRow 4080 4080 122 54 112 122 54 112
    default
    []

def tttFiber9Row1 : TripleComponentParentRow :=
  tripleRow 4081 4080 122 54 113 122 54 112
    (chainMove LColor.r LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber9Row2 : TripleComponentParentRow :=
  tripleRow 4082 4080 122 54 114 122 54 112
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber9Row3 : TripleComponentParentRow :=
  tripleRow 4083 4081 122 54 115 122 54 113
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber9Row4 : TripleComponentParentRow :=
  tripleRow 4084 4080 122 55 120 122 54 112
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber9Row5 : TripleComponentParentRow :=
  tripleRow 4085 4081 122 55 121 122 54 113
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber9Row6 : TripleComponentParentRow :=
  tripleRow 4086 4082 122 55 122 122 54 114
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber9Row7 : TripleComponentParentRow :=
  tripleRow 4087 4083 122 55 123 122 54 115
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber9Row8 : TripleComponentParentRow :=
  tripleRow 4088 4080 123 62 112 122 54 112
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber9Row9 : TripleComponentParentRow :=
  tripleRow 4089 4081 123 62 113 122 54 113
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber9Row10 : TripleComponentParentRow :=
  tripleRow 4090 4082 123 62 114 122 54 114
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber9Row11 : TripleComponentParentRow :=
  tripleRow 4091 4083 123 62 115 122 54 115
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber9Row12 : TripleComponentParentRow :=
  tripleRow 4092 4084 123 63 120 122 55 120
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber9Row13 : TripleComponentParentRow :=
  tripleRow 4093 4085 123 63 121 122 55 121
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber9Row14 : TripleComponentParentRow :=
  tripleRow 4094 4086 123 63 122 122 55 122
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber9Row15 : TripleComponentParentRow :=
  tripleRow 4095 4087 123 63 123 122 55 123
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber9Rows : List TripleComponentParentRow :=
  [ tttFiber9Row0
  , tttFiber9Row1
  , tttFiber9Row2
  , tttFiber9Row3
  , tttFiber9Row4
  , tttFiber9Row5
  , tttFiber9Row6
  , tttFiber9Row7
  , tttFiber9Row8
  , tttFiber9Row9
  , tttFiber9Row10
  , tttFiber9Row11
  , tttFiber9Row12
  , tttFiber9Row13
  , tttFiber9Row14
  , tttFiber9Row15
  ]

def tttFiber9SourcesCheck : Bool :=
  (tttFiber9Rows.map fun row => row.source) == tttFiber9Expected

theorem tttFiber9SourcesCheck_ok :
    tttFiber9SourcesCheck = true := by
  decide

def tttFiber9RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber9Key tttFiber9Expected
    (listGetD tttFiber9Rows i default)

theorem tttFiber9Row_0_ok : tttFiber9RowCheck 0 = true := by
  decide
theorem tttFiber9Row_1_ok : tttFiber9RowCheck 1 = true := by
  decide
theorem tttFiber9Row_2_ok : tttFiber9RowCheck 2 = true := by
  decide
theorem tttFiber9Row_3_ok : tttFiber9RowCheck 3 = true := by
  decide
theorem tttFiber9Row_4_ok : tttFiber9RowCheck 4 = true := by
  decide
theorem tttFiber9Row_5_ok : tttFiber9RowCheck 5 = true := by
  decide
theorem tttFiber9Row_6_ok : tttFiber9RowCheck 6 = true := by
  decide
theorem tttFiber9Row_7_ok : tttFiber9RowCheck 7 = true := by
  decide
theorem tttFiber9Row_8_ok : tttFiber9RowCheck 8 = true := by
  decide
theorem tttFiber9Row_9_ok : tttFiber9RowCheck 9 = true := by
  decide
theorem tttFiber9Row_10_ok : tttFiber9RowCheck 10 = true := by
  decide
theorem tttFiber9Row_11_ok : tttFiber9RowCheck 11 = true := by
  decide
theorem tttFiber9Row_12_ok : tttFiber9RowCheck 12 = true := by
  decide
theorem tttFiber9Row_13_ok : tttFiber9RowCheck 13 = true := by
  decide
theorem tttFiber9Row_14_ok : tttFiber9RowCheck 14 = true := by
  decide
theorem tttFiber9Row_15_ok : tttFiber9RowCheck 15 = true := by
  decide

def tttFiber9ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber9Rows tttLightMaxParentDepth
    (listGetD tttFiber9Expected i 0) == 4080

theorem tttFiber9Parent_0_ok : tttFiber9ParentCheck 0 = true := by
  decide
theorem tttFiber9Parent_1_ok : tttFiber9ParentCheck 1 = true := by
  decide
theorem tttFiber9Parent_2_ok : tttFiber9ParentCheck 2 = true := by
  decide
theorem tttFiber9Parent_3_ok : tttFiber9ParentCheck 3 = true := by
  decide
theorem tttFiber9Parent_4_ok : tttFiber9ParentCheck 4 = true := by
  decide
theorem tttFiber9Parent_5_ok : tttFiber9ParentCheck 5 = true := by
  decide
theorem tttFiber9Parent_6_ok : tttFiber9ParentCheck 6 = true := by
  decide
theorem tttFiber9Parent_7_ok : tttFiber9ParentCheck 7 = true := by
  decide
theorem tttFiber9Parent_8_ok : tttFiber9ParentCheck 8 = true := by
  decide
theorem tttFiber9Parent_9_ok : tttFiber9ParentCheck 9 = true := by
  decide
theorem tttFiber9Parent_10_ok : tttFiber9ParentCheck 10 = true := by
  decide
theorem tttFiber9Parent_11_ok : tttFiber9ParentCheck 11 = true := by
  decide
theorem tttFiber9Parent_12_ok : tttFiber9ParentCheck 12 = true := by
  decide
theorem tttFiber9Parent_13_ok : tttFiber9ParentCheck 13 = true := by
  decide
theorem tttFiber9Parent_14_ok : tttFiber9ParentCheck 14 = true := by
  decide
theorem tttFiber9Parent_15_ok : tttFiber9ParentCheck 15 = true := by
  decide

def tttFiber9CertificateAudit : Bool :=
  tttFiber9SourcesCheck
    && tttFiber9RowCheck 0
    && tttFiber9RowCheck 1
    && tttFiber9RowCheck 2
    && tttFiber9RowCheck 3
    && tttFiber9RowCheck 4
    && tttFiber9RowCheck 5
    && tttFiber9RowCheck 6
    && tttFiber9RowCheck 7
    && tttFiber9RowCheck 8
    && tttFiber9RowCheck 9
    && tttFiber9RowCheck 10
    && tttFiber9RowCheck 11
    && tttFiber9RowCheck 12
    && tttFiber9RowCheck 13
    && tttFiber9RowCheck 14
    && tttFiber9RowCheck 15
    && tttFiber9ParentCheck 0
    && tttFiber9ParentCheck 1
    && tttFiber9ParentCheck 2
    && tttFiber9ParentCheck 3
    && tttFiber9ParentCheck 4
    && tttFiber9ParentCheck 5
    && tttFiber9ParentCheck 6
    && tttFiber9ParentCheck 7
    && tttFiber9ParentCheck 8
    && tttFiber9ParentCheck 9
    && tttFiber9ParentCheck 10
    && tttFiber9ParentCheck 11
    && tttFiber9ParentCheck 12
    && tttFiber9ParentCheck 13
    && tttFiber9ParentCheck 14
    && tttFiber9ParentCheck 15

theorem tttFiber9CertificateAudit_ok :
    tttFiber9CertificateAudit = true := by
  simp [tttFiber9CertificateAudit,
    tttFiber9SourcesCheck_ok,
    tttFiber9Row_0_ok,
    tttFiber9Row_1_ok,
    tttFiber9Row_2_ok,
    tttFiber9Row_3_ok,
    tttFiber9Row_4_ok,
    tttFiber9Row_5_ok,
    tttFiber9Row_6_ok,
    tttFiber9Row_7_ok,
    tttFiber9Row_8_ok,
    tttFiber9Row_9_ok,
    tttFiber9Row_10_ok,
    tttFiber9Row_11_ok,
    tttFiber9Row_12_ok,
    tttFiber9Row_13_ok,
    tttFiber9Row_14_ok,
    tttFiber9Row_15_ok,
    tttFiber9Parent_0_ok,
    tttFiber9Parent_1_ok,
    tttFiber9Parent_2_ok,
    tttFiber9Parent_3_ok,
    tttFiber9Parent_4_ok,
    tttFiber9Parent_5_ok,
    tttFiber9Parent_6_ok,
    tttFiber9Parent_7_ok,
    tttFiber9Parent_8_ok,
    tttFiber9Parent_9_ok,
    tttFiber9Parent_10_ok,
    tttFiber9Parent_11_ok,
    tttFiber9Parent_12_ok,
    tttFiber9Parent_13_ok,
    tttFiber9Parent_14_ok,
    tttFiber9Parent_15_ok]

def tttFiber11Key : List LColor :=
  [LColor.r, LColor.b, LColor.r, LColor.p]

def tttFiber11Expected : List Nat :=
  [2704, 2705, 2706, 2707, 2708, 2709, 2710, 2711,
   2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719]

def tttFiber11Row0 : TripleComponentParentRow :=
  tripleRow 2704 2704 76 144 84 76 144 84
    default
    []

def tttFiber11Row1 : TripleComponentParentRow :=
  tripleRow 2705 2704 76 144 85 76 144 84
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber11Row2 : TripleComponentParentRow :=
  tripleRow 2706 2704 76 144 86 76 144 84
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber11Row3 : TripleComponentParentRow :=
  tripleRow 2707 2705 76 144 87 76 144 85
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber11Row4 : TripleComponentParentRow :=
  tripleRow 2708 2704 76 145 92 76 144 84
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber11Row5 : TripleComponentParentRow :=
  tripleRow 2709 2705 76 145 93 76 144 85
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber11Row6 : TripleComponentParentRow :=
  tripleRow 2710 2706 76 145 94 76 144 86
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber11Row7 : TripleComponentParentRow :=
  tripleRow 2711 2707 76 145 95 76 144 87
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber11Row8 : TripleComponentParentRow :=
  tripleRow 2712 2704 77 152 84 76 144 84
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber11Row9 : TripleComponentParentRow :=
  tripleRow 2713 2705 77 152 85 76 144 85
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber11Row10 : TripleComponentParentRow :=
  tripleRow 2714 2706 77 152 86 76 144 86
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber11Row11 : TripleComponentParentRow :=
  tripleRow 2715 2707 77 152 87 76 144 87
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber11Row12 : TripleComponentParentRow :=
  tripleRow 2716 2708 77 153 92 76 145 92
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber11Row13 : TripleComponentParentRow :=
  tripleRow 2717 2709 77 153 93 76 145 93
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber11Row14 : TripleComponentParentRow :=
  tripleRow 2718 2710 77 153 94 76 145 94
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber11Row15 : TripleComponentParentRow :=
  tripleRow 2719 2711 77 153 95 76 145 95
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber11Rows : List TripleComponentParentRow :=
  [ tttFiber11Row0
  , tttFiber11Row1
  , tttFiber11Row2
  , tttFiber11Row3
  , tttFiber11Row4
  , tttFiber11Row5
  , tttFiber11Row6
  , tttFiber11Row7
  , tttFiber11Row8
  , tttFiber11Row9
  , tttFiber11Row10
  , tttFiber11Row11
  , tttFiber11Row12
  , tttFiber11Row13
  , tttFiber11Row14
  , tttFiber11Row15
  ]

def tttFiber11SourcesCheck : Bool :=
  (tttFiber11Rows.map fun row => row.source) == tttFiber11Expected

theorem tttFiber11SourcesCheck_ok :
    tttFiber11SourcesCheck = true := by
  decide

def tttFiber11RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber11Key tttFiber11Expected
    (listGetD tttFiber11Rows i default)

theorem tttFiber11Row_0_ok : tttFiber11RowCheck 0 = true := by
  decide
theorem tttFiber11Row_1_ok : tttFiber11RowCheck 1 = true := by
  decide
theorem tttFiber11Row_2_ok : tttFiber11RowCheck 2 = true := by
  decide
theorem tttFiber11Row_3_ok : tttFiber11RowCheck 3 = true := by
  decide
theorem tttFiber11Row_4_ok : tttFiber11RowCheck 4 = true := by
  decide
theorem tttFiber11Row_5_ok : tttFiber11RowCheck 5 = true := by
  decide
theorem tttFiber11Row_6_ok : tttFiber11RowCheck 6 = true := by
  decide
theorem tttFiber11Row_7_ok : tttFiber11RowCheck 7 = true := by
  decide
theorem tttFiber11Row_8_ok : tttFiber11RowCheck 8 = true := by
  decide
theorem tttFiber11Row_9_ok : tttFiber11RowCheck 9 = true := by
  decide
theorem tttFiber11Row_10_ok : tttFiber11RowCheck 10 = true := by
  decide
theorem tttFiber11Row_11_ok : tttFiber11RowCheck 11 = true := by
  decide
theorem tttFiber11Row_12_ok : tttFiber11RowCheck 12 = true := by
  decide
theorem tttFiber11Row_13_ok : tttFiber11RowCheck 13 = true := by
  decide
theorem tttFiber11Row_14_ok : tttFiber11RowCheck 14 = true := by
  decide
theorem tttFiber11Row_15_ok : tttFiber11RowCheck 15 = true := by
  decide

def tttFiber11ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber11Rows tttLightMaxParentDepth
    (listGetD tttFiber11Expected i 0) == 2704

theorem tttFiber11Parent_0_ok : tttFiber11ParentCheck 0 = true := by
  decide
theorem tttFiber11Parent_1_ok : tttFiber11ParentCheck 1 = true := by
  decide
theorem tttFiber11Parent_2_ok : tttFiber11ParentCheck 2 = true := by
  decide
theorem tttFiber11Parent_3_ok : tttFiber11ParentCheck 3 = true := by
  decide
theorem tttFiber11Parent_4_ok : tttFiber11ParentCheck 4 = true := by
  decide
theorem tttFiber11Parent_5_ok : tttFiber11ParentCheck 5 = true := by
  decide
theorem tttFiber11Parent_6_ok : tttFiber11ParentCheck 6 = true := by
  decide
theorem tttFiber11Parent_7_ok : tttFiber11ParentCheck 7 = true := by
  decide
theorem tttFiber11Parent_8_ok : tttFiber11ParentCheck 8 = true := by
  decide
theorem tttFiber11Parent_9_ok : tttFiber11ParentCheck 9 = true := by
  decide
theorem tttFiber11Parent_10_ok : tttFiber11ParentCheck 10 = true := by
  decide
theorem tttFiber11Parent_11_ok : tttFiber11ParentCheck 11 = true := by
  decide
theorem tttFiber11Parent_12_ok : tttFiber11ParentCheck 12 = true := by
  decide
theorem tttFiber11Parent_13_ok : tttFiber11ParentCheck 13 = true := by
  decide
theorem tttFiber11Parent_14_ok : tttFiber11ParentCheck 14 = true := by
  decide
theorem tttFiber11Parent_15_ok : tttFiber11ParentCheck 15 = true := by
  decide

def tttFiber11CertificateAudit : Bool :=
  tttFiber11SourcesCheck
    && tttFiber11RowCheck 0
    && tttFiber11RowCheck 1
    && tttFiber11RowCheck 2
    && tttFiber11RowCheck 3
    && tttFiber11RowCheck 4
    && tttFiber11RowCheck 5
    && tttFiber11RowCheck 6
    && tttFiber11RowCheck 7
    && tttFiber11RowCheck 8
    && tttFiber11RowCheck 9
    && tttFiber11RowCheck 10
    && tttFiber11RowCheck 11
    && tttFiber11RowCheck 12
    && tttFiber11RowCheck 13
    && tttFiber11RowCheck 14
    && tttFiber11RowCheck 15
    && tttFiber11ParentCheck 0
    && tttFiber11ParentCheck 1
    && tttFiber11ParentCheck 2
    && tttFiber11ParentCheck 3
    && tttFiber11ParentCheck 4
    && tttFiber11ParentCheck 5
    && tttFiber11ParentCheck 6
    && tttFiber11ParentCheck 7
    && tttFiber11ParentCheck 8
    && tttFiber11ParentCheck 9
    && tttFiber11ParentCheck 10
    && tttFiber11ParentCheck 11
    && tttFiber11ParentCheck 12
    && tttFiber11ParentCheck 13
    && tttFiber11ParentCheck 14
    && tttFiber11ParentCheck 15

theorem tttFiber11CertificateAudit_ok :
    tttFiber11CertificateAudit = true := by
  simp [tttFiber11CertificateAudit,
    tttFiber11SourcesCheck_ok,
    tttFiber11Row_0_ok,
    tttFiber11Row_1_ok,
    tttFiber11Row_2_ok,
    tttFiber11Row_3_ok,
    tttFiber11Row_4_ok,
    tttFiber11Row_5_ok,
    tttFiber11Row_6_ok,
    tttFiber11Row_7_ok,
    tttFiber11Row_8_ok,
    tttFiber11Row_9_ok,
    tttFiber11Row_10_ok,
    tttFiber11Row_11_ok,
    tttFiber11Row_12_ok,
    tttFiber11Row_13_ok,
    tttFiber11Row_14_ok,
    tttFiber11Row_15_ok,
    tttFiber11Parent_0_ok,
    tttFiber11Parent_1_ok,
    tttFiber11Parent_2_ok,
    tttFiber11Parent_3_ok,
    tttFiber11Parent_4_ok,
    tttFiber11Parent_5_ok,
    tttFiber11Parent_6_ok,
    tttFiber11Parent_7_ok,
    tttFiber11Parent_8_ok,
    tttFiber11Parent_9_ok,
    tttFiber11Parent_10_ok,
    tttFiber11Parent_11_ok,
    tttFiber11Parent_12_ok,
    tttFiber11Parent_13_ok,
    tttFiber11Parent_14_ok,
    tttFiber11Parent_15_ok]

def tttFiber12Key : List LColor :=
  [LColor.r, LColor.b, LColor.b, LColor.r]

def tttFiber12Expected : List Nat :=
  []

def tttFiber12Rows : List TripleComponentParentRow :=
  []

def tttFiber12SourcesCheck : Bool :=
  (tttFiber12Rows.map fun row => row.source) == tttFiber12Expected

theorem tttFiber12SourcesCheck_ok :
    tttFiber12SourcesCheck = true := by
  decide

def tttFiber12CertificateAudit : Bool :=
  tttFiber12SourcesCheck

theorem tttFiber12CertificateAudit_ok :
    tttFiber12CertificateAudit = true := by
  simp [tttFiber12CertificateAudit,
    tttFiber12SourcesCheck_ok]

def tttFiber13Key : List LColor :=
  [LColor.r, LColor.b, LColor.b, LColor.b]

def tttFiber13Expected : List Nat :=
  []

def tttFiber13Rows : List TripleComponentParentRow :=
  []

def tttFiber13SourcesCheck : Bool :=
  (tttFiber13Rows.map fun row => row.source) == tttFiber13Expected

theorem tttFiber13SourcesCheck_ok :
    tttFiber13SourcesCheck = true := by
  decide

def tttFiber13CertificateAudit : Bool :=
  tttFiber13SourcesCheck

theorem tttFiber13CertificateAudit_ok :
    tttFiber13CertificateAudit = true := by
  simp [tttFiber13CertificateAudit,
    tttFiber13SourcesCheck_ok]

def tttFiber14Key : List LColor :=
  [LColor.r, LColor.b, LColor.b, LColor.p]

def tttFiber14Expected : List Nat :=
  []

def tttFiber14Rows : List TripleComponentParentRow :=
  []

def tttFiber14SourcesCheck : Bool :=
  (tttFiber14Rows.map fun row => row.source) == tttFiber14Expected

theorem tttFiber14SourcesCheck_ok :
    tttFiber14SourcesCheck = true := by
  decide

def tttFiber14CertificateAudit : Bool :=
  tttFiber14SourcesCheck

theorem tttFiber14CertificateAudit_ok :
    tttFiber14CertificateAudit = true := by
  simp [tttFiber14CertificateAudit,
    tttFiber14SourcesCheck_ok]

def tttFiber15Key : List LColor :=
  [LColor.r, LColor.b, LColor.p, LColor.r]

def tttFiber15Expected : List Nat :=
  []

def tttFiber15Rows : List TripleComponentParentRow :=
  []

def tttFiber15SourcesCheck : Bool :=
  (tttFiber15Rows.map fun row => row.source) == tttFiber15Expected

theorem tttFiber15SourcesCheck_ok :
    tttFiber15SourcesCheck = true := by
  decide

def tttFiber15CertificateAudit : Bool :=
  tttFiber15SourcesCheck

theorem tttFiber15CertificateAudit_ok :
    tttFiber15CertificateAudit = true := by
  simp [tttFiber15CertificateAudit,
    tttFiber15SourcesCheck_ok]

def tttFiber16Key : List LColor :=
  [LColor.r, LColor.b, LColor.p, LColor.b]

def tttFiber16Expected : List Nat :=
  []

def tttFiber16Rows : List TripleComponentParentRow :=
  []

def tttFiber16SourcesCheck : Bool :=
  (tttFiber16Rows.map fun row => row.source) == tttFiber16Expected

theorem tttFiber16SourcesCheck_ok :
    tttFiber16SourcesCheck = true := by
  decide

def tttFiber16CertificateAudit : Bool :=
  tttFiber16SourcesCheck

theorem tttFiber16CertificateAudit_ok :
    tttFiber16CertificateAudit = true := by
  simp [tttFiber16CertificateAudit,
    tttFiber16SourcesCheck_ok]

def tttFiber17Key : List LColor :=
  [LColor.r, LColor.b, LColor.p, LColor.p]

def tttFiber17Expected : List Nat :=
  []

def tttFiber17Rows : List TripleComponentParentRow :=
  []

def tttFiber17SourcesCheck : Bool :=
  (tttFiber17Rows.map fun row => row.source) == tttFiber17Expected

theorem tttFiber17SourcesCheck_ok :
    tttFiber17SourcesCheck = true := by
  decide

def tttFiber17CertificateAudit : Bool :=
  tttFiber17SourcesCheck

theorem tttFiber17CertificateAudit_ok :
    tttFiber17CertificateAudit = true := by
  simp [tttFiber17CertificateAudit,
    tttFiber17SourcesCheck_ok]

def tttFiber18Key : List LColor :=
  [LColor.r, LColor.p, LColor.r, LColor.r]

def tttFiber18Expected : List Nat :=
  [6256, 6257, 6258, 6259, 6260, 6261, 6262, 6263,
   6264, 6265, 6266, 6267, 6268, 6269, 6270, 6271]

def tttFiber18Row0 : TripleComponentParentRow :=
  tripleRow 6256 6256 184 22 176 184 22 176
    default
    []

def tttFiber18Row1 : TripleComponentParentRow :=
  tripleRow 6257 6256 184 22 177 184 22 176
    (chainMove LColor.r LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber18Row2 : TripleComponentParentRow :=
  tripleRow 6258 6256 184 22 178 184 22 176
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber18Row3 : TripleComponentParentRow :=
  tripleRow 6259 6257 184 22 179 184 22 177
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber18Row4 : TripleComponentParentRow :=
  tripleRow 6260 6256 184 23 184 184 22 176
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber18Row5 : TripleComponentParentRow :=
  tripleRow 6261 6257 184 23 185 184 22 177
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber18Row6 : TripleComponentParentRow :=
  tripleRow 6262 6258 184 23 186 184 22 178
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber18Row7 : TripleComponentParentRow :=
  tripleRow 6263 6259 184 23 187 184 22 179
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber18Row8 : TripleComponentParentRow :=
  tripleRow 6264 6256 185 30 176 184 22 176
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber18Row9 : TripleComponentParentRow :=
  tripleRow 6265 6257 185 30 177 184 22 177
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber18Row10 : TripleComponentParentRow :=
  tripleRow 6266 6258 185 30 178 184 22 178
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber18Row11 : TripleComponentParentRow :=
  tripleRow 6267 6259 185 30 179 184 22 179
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber18Row12 : TripleComponentParentRow :=
  tripleRow 6268 6260 185 31 184 184 23 184
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber18Row13 : TripleComponentParentRow :=
  tripleRow 6269 6261 185 31 185 184 23 185
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber18Row14 : TripleComponentParentRow :=
  tripleRow 6270 6262 185 31 186 184 23 186
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber18Row15 : TripleComponentParentRow :=
  tripleRow 6271 6263 185 31 187 184 23 187
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber18Rows : List TripleComponentParentRow :=
  [ tttFiber18Row0
  , tttFiber18Row1
  , tttFiber18Row2
  , tttFiber18Row3
  , tttFiber18Row4
  , tttFiber18Row5
  , tttFiber18Row6
  , tttFiber18Row7
  , tttFiber18Row8
  , tttFiber18Row9
  , tttFiber18Row10
  , tttFiber18Row11
  , tttFiber18Row12
  , tttFiber18Row13
  , tttFiber18Row14
  , tttFiber18Row15
  ]

def tttFiber18SourcesCheck : Bool :=
  (tttFiber18Rows.map fun row => row.source) == tttFiber18Expected

theorem tttFiber18SourcesCheck_ok :
    tttFiber18SourcesCheck = true := by
  decide

def tttFiber18RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber18Key tttFiber18Expected
    (listGetD tttFiber18Rows i default)

theorem tttFiber18Row_0_ok : tttFiber18RowCheck 0 = true := by
  decide
theorem tttFiber18Row_1_ok : tttFiber18RowCheck 1 = true := by
  decide
theorem tttFiber18Row_2_ok : tttFiber18RowCheck 2 = true := by
  decide
theorem tttFiber18Row_3_ok : tttFiber18RowCheck 3 = true := by
  decide
theorem tttFiber18Row_4_ok : tttFiber18RowCheck 4 = true := by
  decide
theorem tttFiber18Row_5_ok : tttFiber18RowCheck 5 = true := by
  decide
theorem tttFiber18Row_6_ok : tttFiber18RowCheck 6 = true := by
  decide
theorem tttFiber18Row_7_ok : tttFiber18RowCheck 7 = true := by
  decide
theorem tttFiber18Row_8_ok : tttFiber18RowCheck 8 = true := by
  decide
theorem tttFiber18Row_9_ok : tttFiber18RowCheck 9 = true := by
  decide
theorem tttFiber18Row_10_ok : tttFiber18RowCheck 10 = true := by
  decide
theorem tttFiber18Row_11_ok : tttFiber18RowCheck 11 = true := by
  decide
theorem tttFiber18Row_12_ok : tttFiber18RowCheck 12 = true := by
  decide
theorem tttFiber18Row_13_ok : tttFiber18RowCheck 13 = true := by
  decide
theorem tttFiber18Row_14_ok : tttFiber18RowCheck 14 = true := by
  decide
theorem tttFiber18Row_15_ok : tttFiber18RowCheck 15 = true := by
  decide

def tttFiber18ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber18Rows tttLightMaxParentDepth
    (listGetD tttFiber18Expected i 0) == 6256

theorem tttFiber18Parent_0_ok : tttFiber18ParentCheck 0 = true := by
  decide
theorem tttFiber18Parent_1_ok : tttFiber18ParentCheck 1 = true := by
  decide
theorem tttFiber18Parent_2_ok : tttFiber18ParentCheck 2 = true := by
  decide
theorem tttFiber18Parent_3_ok : tttFiber18ParentCheck 3 = true := by
  decide
theorem tttFiber18Parent_4_ok : tttFiber18ParentCheck 4 = true := by
  decide
theorem tttFiber18Parent_5_ok : tttFiber18ParentCheck 5 = true := by
  decide
theorem tttFiber18Parent_6_ok : tttFiber18ParentCheck 6 = true := by
  decide
theorem tttFiber18Parent_7_ok : tttFiber18ParentCheck 7 = true := by
  decide
theorem tttFiber18Parent_8_ok : tttFiber18ParentCheck 8 = true := by
  decide
theorem tttFiber18Parent_9_ok : tttFiber18ParentCheck 9 = true := by
  decide
theorem tttFiber18Parent_10_ok : tttFiber18ParentCheck 10 = true := by
  decide
theorem tttFiber18Parent_11_ok : tttFiber18ParentCheck 11 = true := by
  decide
theorem tttFiber18Parent_12_ok : tttFiber18ParentCheck 12 = true := by
  decide
theorem tttFiber18Parent_13_ok : tttFiber18ParentCheck 13 = true := by
  decide
theorem tttFiber18Parent_14_ok : tttFiber18ParentCheck 14 = true := by
  decide
theorem tttFiber18Parent_15_ok : tttFiber18ParentCheck 15 = true := by
  decide

def tttFiber18CertificateAudit : Bool :=
  tttFiber18SourcesCheck
    && tttFiber18RowCheck 0
    && tttFiber18RowCheck 1
    && tttFiber18RowCheck 2
    && tttFiber18RowCheck 3
    && tttFiber18RowCheck 4
    && tttFiber18RowCheck 5
    && tttFiber18RowCheck 6
    && tttFiber18RowCheck 7
    && tttFiber18RowCheck 8
    && tttFiber18RowCheck 9
    && tttFiber18RowCheck 10
    && tttFiber18RowCheck 11
    && tttFiber18RowCheck 12
    && tttFiber18RowCheck 13
    && tttFiber18RowCheck 14
    && tttFiber18RowCheck 15
    && tttFiber18ParentCheck 0
    && tttFiber18ParentCheck 1
    && tttFiber18ParentCheck 2
    && tttFiber18ParentCheck 3
    && tttFiber18ParentCheck 4
    && tttFiber18ParentCheck 5
    && tttFiber18ParentCheck 6
    && tttFiber18ParentCheck 7
    && tttFiber18ParentCheck 8
    && tttFiber18ParentCheck 9
    && tttFiber18ParentCheck 10
    && tttFiber18ParentCheck 11
    && tttFiber18ParentCheck 12
    && tttFiber18ParentCheck 13
    && tttFiber18ParentCheck 14
    && tttFiber18ParentCheck 15

theorem tttFiber18CertificateAudit_ok :
    tttFiber18CertificateAudit = true := by
  simp [tttFiber18CertificateAudit,
    tttFiber18SourcesCheck_ok,
    tttFiber18Row_0_ok,
    tttFiber18Row_1_ok,
    tttFiber18Row_2_ok,
    tttFiber18Row_3_ok,
    tttFiber18Row_4_ok,
    tttFiber18Row_5_ok,
    tttFiber18Row_6_ok,
    tttFiber18Row_7_ok,
    tttFiber18Row_8_ok,
    tttFiber18Row_9_ok,
    tttFiber18Row_10_ok,
    tttFiber18Row_11_ok,
    tttFiber18Row_12_ok,
    tttFiber18Row_13_ok,
    tttFiber18Row_14_ok,
    tttFiber18Row_15_ok,
    tttFiber18Parent_0_ok,
    tttFiber18Parent_1_ok,
    tttFiber18Parent_2_ok,
    tttFiber18Parent_3_ok,
    tttFiber18Parent_4_ok,
    tttFiber18Parent_5_ok,
    tttFiber18Parent_6_ok,
    tttFiber18Parent_7_ok,
    tttFiber18Parent_8_ok,
    tttFiber18Parent_9_ok,
    tttFiber18Parent_10_ok,
    tttFiber18Parent_11_ok,
    tttFiber18Parent_12_ok,
    tttFiber18Parent_13_ok,
    tttFiber18Parent_14_ok,
    tttFiber18Parent_15_ok]

def tttFiber19Key : List LColor :=
  [LColor.r, LColor.p, LColor.r, LColor.b]

def tttFiber19Expected : List Nat :=
  [4624, 4625, 4626, 4627, 4628, 4629, 4630, 4631,
   4632, 4633, 4634, 4635, 4636, 4637, 4638, 4639]

def tttFiber19Row0 : TripleComponentParentRow :=
  tripleRow 4624 4624 136 84 144 136 84 144
    default
    []

def tttFiber19Row1 : TripleComponentParentRow :=
  tripleRow 4625 4624 136 84 145 136 84 144
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber19Row2 : TripleComponentParentRow :=
  tripleRow 4626 4625 136 84 146 136 84 145
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber19Row3 : TripleComponentParentRow :=
  tripleRow 4627 4624 136 84 147 136 84 144
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber19Row4 : TripleComponentParentRow :=
  tripleRow 4628 4624 136 85 152 136 84 144
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber19Row5 : TripleComponentParentRow :=
  tripleRow 4629 4625 136 85 153 136 84 145
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber19Row6 : TripleComponentParentRow :=
  tripleRow 4630 4626 136 85 154 136 84 146
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber19Row7 : TripleComponentParentRow :=
  tripleRow 4631 4627 136 85 155 136 84 147
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber19Row8 : TripleComponentParentRow :=
  tripleRow 4632 4624 137 92 144 136 84 144
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber19Row9 : TripleComponentParentRow :=
  tripleRow 4633 4625 137 92 145 136 84 145
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber19Row10 : TripleComponentParentRow :=
  tripleRow 4634 4626 137 92 146 136 84 146
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber19Row11 : TripleComponentParentRow :=
  tripleRow 4635 4627 137 92 147 136 84 147
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber19Row12 : TripleComponentParentRow :=
  tripleRow 4636 4628 137 93 152 136 85 152
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber19Row13 : TripleComponentParentRow :=
  tripleRow 4637 4629 137 93 153 136 85 153
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber19Row14 : TripleComponentParentRow :=
  tripleRow 4638 4630 137 93 154 136 85 154
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber19Row15 : TripleComponentParentRow :=
  tripleRow 4639 4631 137 93 155 136 85 155
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber19Rows : List TripleComponentParentRow :=
  [ tttFiber19Row0
  , tttFiber19Row1
  , tttFiber19Row2
  , tttFiber19Row3
  , tttFiber19Row4
  , tttFiber19Row5
  , tttFiber19Row6
  , tttFiber19Row7
  , tttFiber19Row8
  , tttFiber19Row9
  , tttFiber19Row10
  , tttFiber19Row11
  , tttFiber19Row12
  , tttFiber19Row13
  , tttFiber19Row14
  , tttFiber19Row15
  ]

def tttFiber19SourcesCheck : Bool :=
  (tttFiber19Rows.map fun row => row.source) == tttFiber19Expected

theorem tttFiber19SourcesCheck_ok :
    tttFiber19SourcesCheck = true := by
  decide

def tttFiber19RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber19Key tttFiber19Expected
    (listGetD tttFiber19Rows i default)

theorem tttFiber19Row_0_ok : tttFiber19RowCheck 0 = true := by
  decide
theorem tttFiber19Row_1_ok : tttFiber19RowCheck 1 = true := by
  decide
theorem tttFiber19Row_2_ok : tttFiber19RowCheck 2 = true := by
  decide
theorem tttFiber19Row_3_ok : tttFiber19RowCheck 3 = true := by
  decide
theorem tttFiber19Row_4_ok : tttFiber19RowCheck 4 = true := by
  decide
theorem tttFiber19Row_5_ok : tttFiber19RowCheck 5 = true := by
  decide
theorem tttFiber19Row_6_ok : tttFiber19RowCheck 6 = true := by
  decide
theorem tttFiber19Row_7_ok : tttFiber19RowCheck 7 = true := by
  decide
theorem tttFiber19Row_8_ok : tttFiber19RowCheck 8 = true := by
  decide
theorem tttFiber19Row_9_ok : tttFiber19RowCheck 9 = true := by
  decide
theorem tttFiber19Row_10_ok : tttFiber19RowCheck 10 = true := by
  decide
theorem tttFiber19Row_11_ok : tttFiber19RowCheck 11 = true := by
  decide
theorem tttFiber19Row_12_ok : tttFiber19RowCheck 12 = true := by
  decide
theorem tttFiber19Row_13_ok : tttFiber19RowCheck 13 = true := by
  decide
theorem tttFiber19Row_14_ok : tttFiber19RowCheck 14 = true := by
  decide
theorem tttFiber19Row_15_ok : tttFiber19RowCheck 15 = true := by
  decide

def tttFiber19ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber19Rows tttLightMaxParentDepth
    (listGetD tttFiber19Expected i 0) == 4624

theorem tttFiber19Parent_0_ok : tttFiber19ParentCheck 0 = true := by
  decide
theorem tttFiber19Parent_1_ok : tttFiber19ParentCheck 1 = true := by
  decide
theorem tttFiber19Parent_2_ok : tttFiber19ParentCheck 2 = true := by
  decide
theorem tttFiber19Parent_3_ok : tttFiber19ParentCheck 3 = true := by
  decide
theorem tttFiber19Parent_4_ok : tttFiber19ParentCheck 4 = true := by
  decide
theorem tttFiber19Parent_5_ok : tttFiber19ParentCheck 5 = true := by
  decide
theorem tttFiber19Parent_6_ok : tttFiber19ParentCheck 6 = true := by
  decide
theorem tttFiber19Parent_7_ok : tttFiber19ParentCheck 7 = true := by
  decide
theorem tttFiber19Parent_8_ok : tttFiber19ParentCheck 8 = true := by
  decide
theorem tttFiber19Parent_9_ok : tttFiber19ParentCheck 9 = true := by
  decide
theorem tttFiber19Parent_10_ok : tttFiber19ParentCheck 10 = true := by
  decide
theorem tttFiber19Parent_11_ok : tttFiber19ParentCheck 11 = true := by
  decide
theorem tttFiber19Parent_12_ok : tttFiber19ParentCheck 12 = true := by
  decide
theorem tttFiber19Parent_13_ok : tttFiber19ParentCheck 13 = true := by
  decide
theorem tttFiber19Parent_14_ok : tttFiber19ParentCheck 14 = true := by
  decide
theorem tttFiber19Parent_15_ok : tttFiber19ParentCheck 15 = true := by
  decide

def tttFiber19CertificateAudit : Bool :=
  tttFiber19SourcesCheck
    && tttFiber19RowCheck 0
    && tttFiber19RowCheck 1
    && tttFiber19RowCheck 2
    && tttFiber19RowCheck 3
    && tttFiber19RowCheck 4
    && tttFiber19RowCheck 5
    && tttFiber19RowCheck 6
    && tttFiber19RowCheck 7
    && tttFiber19RowCheck 8
    && tttFiber19RowCheck 9
    && tttFiber19RowCheck 10
    && tttFiber19RowCheck 11
    && tttFiber19RowCheck 12
    && tttFiber19RowCheck 13
    && tttFiber19RowCheck 14
    && tttFiber19RowCheck 15
    && tttFiber19ParentCheck 0
    && tttFiber19ParentCheck 1
    && tttFiber19ParentCheck 2
    && tttFiber19ParentCheck 3
    && tttFiber19ParentCheck 4
    && tttFiber19ParentCheck 5
    && tttFiber19ParentCheck 6
    && tttFiber19ParentCheck 7
    && tttFiber19ParentCheck 8
    && tttFiber19ParentCheck 9
    && tttFiber19ParentCheck 10
    && tttFiber19ParentCheck 11
    && tttFiber19ParentCheck 12
    && tttFiber19ParentCheck 13
    && tttFiber19ParentCheck 14
    && tttFiber19ParentCheck 15

theorem tttFiber19CertificateAudit_ok :
    tttFiber19CertificateAudit = true := by
  simp [tttFiber19CertificateAudit,
    tttFiber19SourcesCheck_ok,
    tttFiber19Row_0_ok,
    tttFiber19Row_1_ok,
    tttFiber19Row_2_ok,
    tttFiber19Row_3_ok,
    tttFiber19Row_4_ok,
    tttFiber19Row_5_ok,
    tttFiber19Row_6_ok,
    tttFiber19Row_7_ok,
    tttFiber19Row_8_ok,
    tttFiber19Row_9_ok,
    tttFiber19Row_10_ok,
    tttFiber19Row_11_ok,
    tttFiber19Row_12_ok,
    tttFiber19Row_13_ok,
    tttFiber19Row_14_ok,
    tttFiber19Row_15_ok,
    tttFiber19Parent_0_ok,
    tttFiber19Parent_1_ok,
    tttFiber19Parent_2_ok,
    tttFiber19Parent_3_ok,
    tttFiber19Parent_4_ok,
    tttFiber19Parent_5_ok,
    tttFiber19Parent_6_ok,
    tttFiber19Parent_7_ok,
    tttFiber19Parent_8_ok,
    tttFiber19Parent_9_ok,
    tttFiber19Parent_10_ok,
    tttFiber19Parent_11_ok,
    tttFiber19Parent_12_ok,
    tttFiber19Parent_13_ok,
    tttFiber19Parent_14_ok,
    tttFiber19Parent_15_ok]

def tttFiber21Key : List LColor :=
  [LColor.r, LColor.p, LColor.b, LColor.r]

def tttFiber21Expected : List Nat :=
  []

def tttFiber21Rows : List TripleComponentParentRow :=
  []

def tttFiber21SourcesCheck : Bool :=
  (tttFiber21Rows.map fun row => row.source) == tttFiber21Expected

theorem tttFiber21SourcesCheck_ok :
    tttFiber21SourcesCheck = true := by
  decide

def tttFiber21CertificateAudit : Bool :=
  tttFiber21SourcesCheck

theorem tttFiber21CertificateAudit_ok :
    tttFiber21CertificateAudit = true := by
  simp [tttFiber21CertificateAudit,
    tttFiber21SourcesCheck_ok]

def tttFiber22Key : List LColor :=
  [LColor.r, LColor.p, LColor.b, LColor.b]

def tttFiber22Expected : List Nat :=
  []

def tttFiber22Rows : List TripleComponentParentRow :=
  []

def tttFiber22SourcesCheck : Bool :=
  (tttFiber22Rows.map fun row => row.source) == tttFiber22Expected

theorem tttFiber22SourcesCheck_ok :
    tttFiber22SourcesCheck = true := by
  decide

def tttFiber22CertificateAudit : Bool :=
  tttFiber22SourcesCheck

theorem tttFiber22CertificateAudit_ok :
    tttFiber22CertificateAudit = true := by
  simp [tttFiber22CertificateAudit,
    tttFiber22SourcesCheck_ok]

def tttFiber23Key : List LColor :=
  [LColor.r, LColor.p, LColor.b, LColor.p]

def tttFiber23Expected : List Nat :=
  []

def tttFiber23Rows : List TripleComponentParentRow :=
  []

def tttFiber23SourcesCheck : Bool :=
  (tttFiber23Rows.map fun row => row.source) == tttFiber23Expected

theorem tttFiber23SourcesCheck_ok :
    tttFiber23SourcesCheck = true := by
  decide

def tttFiber23CertificateAudit : Bool :=
  tttFiber23SourcesCheck

theorem tttFiber23CertificateAudit_ok :
    tttFiber23CertificateAudit = true := by
  simp [tttFiber23CertificateAudit,
    tttFiber23SourcesCheck_ok]

def tttFiber24Key : List LColor :=
  [LColor.r, LColor.p, LColor.p, LColor.r]

def tttFiber24Expected : List Nat :=
  []

def tttFiber24Rows : List TripleComponentParentRow :=
  []

def tttFiber24SourcesCheck : Bool :=
  (tttFiber24Rows.map fun row => row.source) == tttFiber24Expected

theorem tttFiber24SourcesCheck_ok :
    tttFiber24SourcesCheck = true := by
  decide

def tttFiber24CertificateAudit : Bool :=
  tttFiber24SourcesCheck

theorem tttFiber24CertificateAudit_ok :
    tttFiber24CertificateAudit = true := by
  simp [tttFiber24CertificateAudit,
    tttFiber24SourcesCheck_ok]

def tttFiber25Key : List LColor :=
  [LColor.r, LColor.p, LColor.p, LColor.b]

def tttFiber25Expected : List Nat :=
  []

def tttFiber25Rows : List TripleComponentParentRow :=
  []

def tttFiber25SourcesCheck : Bool :=
  (tttFiber25Rows.map fun row => row.source) == tttFiber25Expected

theorem tttFiber25SourcesCheck_ok :
    tttFiber25SourcesCheck = true := by
  decide

def tttFiber25CertificateAudit : Bool :=
  tttFiber25SourcesCheck

theorem tttFiber25CertificateAudit_ok :
    tttFiber25CertificateAudit = true := by
  simp [tttFiber25CertificateAudit,
    tttFiber25SourcesCheck_ok]

def tttFiber26Key : List LColor :=
  [LColor.r, LColor.p, LColor.p, LColor.p]

def tttFiber26Expected : List Nat :=
  []

def tttFiber26Rows : List TripleComponentParentRow :=
  []

def tttFiber26SourcesCheck : Bool :=
  (tttFiber26Rows.map fun row => row.source) == tttFiber26Expected

theorem tttFiber26SourcesCheck_ok :
    tttFiber26SourcesCheck = true := by
  decide

def tttFiber26CertificateAudit : Bool :=
  tttFiber26SourcesCheck

theorem tttFiber26CertificateAudit_ok :
    tttFiber26CertificateAudit = true := by
  simp [tttFiber26CertificateAudit,
    tttFiber26SourcesCheck_ok]

def tttFiber27Key : List LColor :=
  [LColor.b, LColor.r, LColor.r, LColor.r]

def tttFiber27Expected : List Nat :=
  []

def tttFiber27Rows : List TripleComponentParentRow :=
  []

def tttFiber27SourcesCheck : Bool :=
  (tttFiber27Rows.map fun row => row.source) == tttFiber27Expected

theorem tttFiber27SourcesCheck_ok :
    tttFiber27SourcesCheck = true := by
  decide

def tttFiber27CertificateAudit : Bool :=
  tttFiber27SourcesCheck

theorem tttFiber27CertificateAudit_ok :
    tttFiber27CertificateAudit = true := by
  simp [tttFiber27CertificateAudit,
    tttFiber27SourcesCheck_ok]

def tttFiber28Key : List LColor :=
  [LColor.b, LColor.r, LColor.r, LColor.b]

def tttFiber28Expected : List Nat :=
  []

def tttFiber28Rows : List TripleComponentParentRow :=
  []

def tttFiber28SourcesCheck : Bool :=
  (tttFiber28Rows.map fun row => row.source) == tttFiber28Expected

theorem tttFiber28SourcesCheck_ok :
    tttFiber28SourcesCheck = true := by
  decide

def tttFiber28CertificateAudit : Bool :=
  tttFiber28SourcesCheck

theorem tttFiber28CertificateAudit_ok :
    tttFiber28CertificateAudit = true := by
  simp [tttFiber28CertificateAudit,
    tttFiber28SourcesCheck_ok]

def tttFiber29Key : List LColor :=
  [LColor.b, LColor.r, LColor.r, LColor.p]

def tttFiber29Expected : List Nat :=
  []

def tttFiber29Rows : List TripleComponentParentRow :=
  []

def tttFiber29SourcesCheck : Bool :=
  (tttFiber29Rows.map fun row => row.source) == tttFiber29Expected

theorem tttFiber29SourcesCheck_ok :
    tttFiber29SourcesCheck = true := by
  decide

def tttFiber29CertificateAudit : Bool :=
  tttFiber29SourcesCheck

theorem tttFiber29CertificateAudit_ok :
    tttFiber29CertificateAudit = true := by
  simp [tttFiber29CertificateAudit,
    tttFiber29SourcesCheck_ok]

def tttFiber31Key : List LColor :=
  [LColor.b, LColor.r, LColor.b, LColor.b]

def tttFiber31Expected : List Nat :=
  [1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895,
   1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903]

def tttFiber31Row0 : TripleComponentParentRow :=
  tripleRow 1888 1888 54 114 52 54 114 52
    default
    []

def tttFiber31Row1 : TripleComponentParentRow :=
  tripleRow 1889 1888 54 114 53 54 114 52
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber31Row2 : TripleComponentParentRow :=
  tripleRow 1890 1889 54 114 54 54 114 53
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber31Row3 : TripleComponentParentRow :=
  tripleRow 1891 1888 54 114 55 54 114 52
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber31Row4 : TripleComponentParentRow :=
  tripleRow 1892 1888 54 115 60 54 114 52
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber31Row5 : TripleComponentParentRow :=
  tripleRow 1893 1889 54 115 61 54 114 53
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber31Row6 : TripleComponentParentRow :=
  tripleRow 1894 1890 54 115 62 54 114 54
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber31Row7 : TripleComponentParentRow :=
  tripleRow 1895 1891 54 115 63 54 114 55
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber31Row8 : TripleComponentParentRow :=
  tripleRow 1896 1888 55 122 52 54 114 52
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber31Row9 : TripleComponentParentRow :=
  tripleRow 1897 1889 55 122 53 54 114 53
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber31Row10 : TripleComponentParentRow :=
  tripleRow 1898 1890 55 122 54 54 114 54
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber31Row11 : TripleComponentParentRow :=
  tripleRow 1899 1891 55 122 55 54 114 55
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber31Row12 : TripleComponentParentRow :=
  tripleRow 1900 1892 55 123 60 54 115 60
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber31Row13 : TripleComponentParentRow :=
  tripleRow 1901 1893 55 123 61 54 115 61
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber31Row14 : TripleComponentParentRow :=
  tripleRow 1902 1894 55 123 62 54 115 62
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber31Row15 : TripleComponentParentRow :=
  tripleRow 1903 1895 55 123 63 54 115 63
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber31Rows : List TripleComponentParentRow :=
  [ tttFiber31Row0
  , tttFiber31Row1
  , tttFiber31Row2
  , tttFiber31Row3
  , tttFiber31Row4
  , tttFiber31Row5
  , tttFiber31Row6
  , tttFiber31Row7
  , tttFiber31Row8
  , tttFiber31Row9
  , tttFiber31Row10
  , tttFiber31Row11
  , tttFiber31Row12
  , tttFiber31Row13
  , tttFiber31Row14
  , tttFiber31Row15
  ]

def tttFiber31SourcesCheck : Bool :=
  (tttFiber31Rows.map fun row => row.source) == tttFiber31Expected

theorem tttFiber31SourcesCheck_ok :
    tttFiber31SourcesCheck = true := by
  decide

def tttFiber31RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber31Key tttFiber31Expected
    (listGetD tttFiber31Rows i default)

theorem tttFiber31Row_0_ok : tttFiber31RowCheck 0 = true := by
  decide
theorem tttFiber31Row_1_ok : tttFiber31RowCheck 1 = true := by
  decide
theorem tttFiber31Row_2_ok : tttFiber31RowCheck 2 = true := by
  decide
theorem tttFiber31Row_3_ok : tttFiber31RowCheck 3 = true := by
  decide
theorem tttFiber31Row_4_ok : tttFiber31RowCheck 4 = true := by
  decide
theorem tttFiber31Row_5_ok : tttFiber31RowCheck 5 = true := by
  decide
theorem tttFiber31Row_6_ok : tttFiber31RowCheck 6 = true := by
  decide
theorem tttFiber31Row_7_ok : tttFiber31RowCheck 7 = true := by
  decide
theorem tttFiber31Row_8_ok : tttFiber31RowCheck 8 = true := by
  decide
theorem tttFiber31Row_9_ok : tttFiber31RowCheck 9 = true := by
  decide
theorem tttFiber31Row_10_ok : tttFiber31RowCheck 10 = true := by
  decide
theorem tttFiber31Row_11_ok : tttFiber31RowCheck 11 = true := by
  decide
theorem tttFiber31Row_12_ok : tttFiber31RowCheck 12 = true := by
  decide
theorem tttFiber31Row_13_ok : tttFiber31RowCheck 13 = true := by
  decide
theorem tttFiber31Row_14_ok : tttFiber31RowCheck 14 = true := by
  decide
theorem tttFiber31Row_15_ok : tttFiber31RowCheck 15 = true := by
  decide

def tttFiber31ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber31Rows tttLightMaxParentDepth
    (listGetD tttFiber31Expected i 0) == 1888

theorem tttFiber31Parent_0_ok : tttFiber31ParentCheck 0 = true := by
  decide
theorem tttFiber31Parent_1_ok : tttFiber31ParentCheck 1 = true := by
  decide
theorem tttFiber31Parent_2_ok : tttFiber31ParentCheck 2 = true := by
  decide
theorem tttFiber31Parent_3_ok : tttFiber31ParentCheck 3 = true := by
  decide
theorem tttFiber31Parent_4_ok : tttFiber31ParentCheck 4 = true := by
  decide
theorem tttFiber31Parent_5_ok : tttFiber31ParentCheck 5 = true := by
  decide
theorem tttFiber31Parent_6_ok : tttFiber31ParentCheck 6 = true := by
  decide
theorem tttFiber31Parent_7_ok : tttFiber31ParentCheck 7 = true := by
  decide
theorem tttFiber31Parent_8_ok : tttFiber31ParentCheck 8 = true := by
  decide
theorem tttFiber31Parent_9_ok : tttFiber31ParentCheck 9 = true := by
  decide
theorem tttFiber31Parent_10_ok : tttFiber31ParentCheck 10 = true := by
  decide
theorem tttFiber31Parent_11_ok : tttFiber31ParentCheck 11 = true := by
  decide
theorem tttFiber31Parent_12_ok : tttFiber31ParentCheck 12 = true := by
  decide
theorem tttFiber31Parent_13_ok : tttFiber31ParentCheck 13 = true := by
  decide
theorem tttFiber31Parent_14_ok : tttFiber31ParentCheck 14 = true := by
  decide
theorem tttFiber31Parent_15_ok : tttFiber31ParentCheck 15 = true := by
  decide

def tttFiber31CertificateAudit : Bool :=
  tttFiber31SourcesCheck
    && tttFiber31RowCheck 0
    && tttFiber31RowCheck 1
    && tttFiber31RowCheck 2
    && tttFiber31RowCheck 3
    && tttFiber31RowCheck 4
    && tttFiber31RowCheck 5
    && tttFiber31RowCheck 6
    && tttFiber31RowCheck 7
    && tttFiber31RowCheck 8
    && tttFiber31RowCheck 9
    && tttFiber31RowCheck 10
    && tttFiber31RowCheck 11
    && tttFiber31RowCheck 12
    && tttFiber31RowCheck 13
    && tttFiber31RowCheck 14
    && tttFiber31RowCheck 15
    && tttFiber31ParentCheck 0
    && tttFiber31ParentCheck 1
    && tttFiber31ParentCheck 2
    && tttFiber31ParentCheck 3
    && tttFiber31ParentCheck 4
    && tttFiber31ParentCheck 5
    && tttFiber31ParentCheck 6
    && tttFiber31ParentCheck 7
    && tttFiber31ParentCheck 8
    && tttFiber31ParentCheck 9
    && tttFiber31ParentCheck 10
    && tttFiber31ParentCheck 11
    && tttFiber31ParentCheck 12
    && tttFiber31ParentCheck 13
    && tttFiber31ParentCheck 14
    && tttFiber31ParentCheck 15

theorem tttFiber31CertificateAudit_ok :
    tttFiber31CertificateAudit = true := by
  simp [tttFiber31CertificateAudit,
    tttFiber31SourcesCheck_ok,
    tttFiber31Row_0_ok,
    tttFiber31Row_1_ok,
    tttFiber31Row_2_ok,
    tttFiber31Row_3_ok,
    tttFiber31Row_4_ok,
    tttFiber31Row_5_ok,
    tttFiber31Row_6_ok,
    tttFiber31Row_7_ok,
    tttFiber31Row_8_ok,
    tttFiber31Row_9_ok,
    tttFiber31Row_10_ok,
    tttFiber31Row_11_ok,
    tttFiber31Row_12_ok,
    tttFiber31Row_13_ok,
    tttFiber31Row_14_ok,
    tttFiber31Row_15_ok,
    tttFiber31Parent_0_ok,
    tttFiber31Parent_1_ok,
    tttFiber31Parent_2_ok,
    tttFiber31Parent_3_ok,
    tttFiber31Parent_4_ok,
    tttFiber31Parent_5_ok,
    tttFiber31Parent_6_ok,
    tttFiber31Parent_7_ok,
    tttFiber31Parent_8_ok,
    tttFiber31Parent_9_ok,
    tttFiber31Parent_10_ok,
    tttFiber31Parent_11_ok,
    tttFiber31Parent_12_ok,
    tttFiber31Parent_13_ok,
    tttFiber31Parent_14_ok,
    tttFiber31Parent_15_ok]

def tttFiber32Key : List LColor :=
  [LColor.b, LColor.r, LColor.b, LColor.p]

def tttFiber32Expected : List Nat :=
  [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]

def tttFiber32Row0 : TripleComponentParentRow :=
  tripleRow 256 256 6 176 20 6 176 20
    default
    []

def tttFiber32Row1 : TripleComponentParentRow :=
  tripleRow 257 256 6 176 21 6 176 20
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber32Row2 : TripleComponentParentRow :=
  tripleRow 258 256 6 176 22 6 176 20
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber32Row3 : TripleComponentParentRow :=
  tripleRow 259 257 6 176 23 6 176 21
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber32Row4 : TripleComponentParentRow :=
  tripleRow 260 256 6 177 28 6 176 20
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber32Row5 : TripleComponentParentRow :=
  tripleRow 261 257 6 177 29 6 176 21
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber32Row6 : TripleComponentParentRow :=
  tripleRow 262 258 6 177 30 6 176 22
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber32Row7 : TripleComponentParentRow :=
  tripleRow 263 259 6 177 31 6 176 23
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber32Row8 : TripleComponentParentRow :=
  tripleRow 264 256 7 184 20 6 176 20
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber32Row9 : TripleComponentParentRow :=
  tripleRow 265 257 7 184 21 6 176 21
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber32Row10 : TripleComponentParentRow :=
  tripleRow 266 258 7 184 22 6 176 22
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber32Row11 : TripleComponentParentRow :=
  tripleRow 267 259 7 184 23 6 176 23
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber32Row12 : TripleComponentParentRow :=
  tripleRow 268 260 7 185 28 6 177 28
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber32Row13 : TripleComponentParentRow :=
  tripleRow 269 261 7 185 29 6 177 29
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber32Row14 : TripleComponentParentRow :=
  tripleRow 270 262 7 185 30 6 177 30
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber32Row15 : TripleComponentParentRow :=
  tripleRow 271 263 7 185 31 6 177 31
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber32Rows : List TripleComponentParentRow :=
  [ tttFiber32Row0
  , tttFiber32Row1
  , tttFiber32Row2
  , tttFiber32Row3
  , tttFiber32Row4
  , tttFiber32Row5
  , tttFiber32Row6
  , tttFiber32Row7
  , tttFiber32Row8
  , tttFiber32Row9
  , tttFiber32Row10
  , tttFiber32Row11
  , tttFiber32Row12
  , tttFiber32Row13
  , tttFiber32Row14
  , tttFiber32Row15
  ]

def tttFiber32SourcesCheck : Bool :=
  (tttFiber32Rows.map fun row => row.source) == tttFiber32Expected

theorem tttFiber32SourcesCheck_ok :
    tttFiber32SourcesCheck = true := by
  decide

def tttFiber32RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber32Key tttFiber32Expected
    (listGetD tttFiber32Rows i default)

theorem tttFiber32Row_0_ok : tttFiber32RowCheck 0 = true := by
  decide
theorem tttFiber32Row_1_ok : tttFiber32RowCheck 1 = true := by
  decide
theorem tttFiber32Row_2_ok : tttFiber32RowCheck 2 = true := by
  decide
theorem tttFiber32Row_3_ok : tttFiber32RowCheck 3 = true := by
  decide
theorem tttFiber32Row_4_ok : tttFiber32RowCheck 4 = true := by
  decide
theorem tttFiber32Row_5_ok : tttFiber32RowCheck 5 = true := by
  decide
theorem tttFiber32Row_6_ok : tttFiber32RowCheck 6 = true := by
  decide
theorem tttFiber32Row_7_ok : tttFiber32RowCheck 7 = true := by
  decide
theorem tttFiber32Row_8_ok : tttFiber32RowCheck 8 = true := by
  decide
theorem tttFiber32Row_9_ok : tttFiber32RowCheck 9 = true := by
  decide
theorem tttFiber32Row_10_ok : tttFiber32RowCheck 10 = true := by
  decide
theorem tttFiber32Row_11_ok : tttFiber32RowCheck 11 = true := by
  decide
theorem tttFiber32Row_12_ok : tttFiber32RowCheck 12 = true := by
  decide
theorem tttFiber32Row_13_ok : tttFiber32RowCheck 13 = true := by
  decide
theorem tttFiber32Row_14_ok : tttFiber32RowCheck 14 = true := by
  decide
theorem tttFiber32Row_15_ok : tttFiber32RowCheck 15 = true := by
  decide

theorem tttFiber32Row1_chainSingleKempeStep :
    chainSingleKempeStep tttWord
      (tripleStates 6 176 21) (tripleStates 6 176 20) = true := by
  exact
    tripleComponentRowValid_chainSingleKempeStep_of_source_beq_false
      (key := tttFiber32Key) (expected := tttFiber32Expected)
      (row := tttFiber32Row1)
      (by
        simpa [tttFiber32RowCheck, tttFiber32Rows, listGetD] using
          tttFiber32Row_1_ok)
      (by decide)
      (by decide)
      (by decide)

def tttFiber32RowsSingleStepReadyCheck : Bool :=
  tttFiber32Rows.all
    (tripleComponentRowValidWithSingleStepReady
      tttFiber32Key tttFiber32Expected)

theorem tttFiber32RowsSingleStepReadyCheck_ok :
    tttFiber32RowsSingleStepReadyCheck = true := by
  decide

theorem tttFiber32Rows_mem_source_eq_or_chainSingleKempeStep
    {row : TripleComponentParentRow} (hmem : row ∈ tttFiber32Rows) :
    row.source = row.parent ∨
      chainSingleKempeStep tttWord
        (tripleStates row.sourceLeft row.sourceMiddle row.sourceRight)
        (tripleStates row.parentLeft row.parentMiddle row.parentRight) =
          true := by
  have hrowReady :
      tripleComponentRowValidWithSingleStepReady
        tttFiber32Key tttFiber32Expected row = true :=
    (List.all_eq_true.mp tttFiber32RowsSingleStepReadyCheck_ok) row hmem
  rw [tripleComponentRowValidWithSingleStepReady, Bool.and_eq_true]
    at hrowReady
  exact tripleComponentRowValid_source_eq_or_chainSingleKempeStep_of_ready
    hrowReady.1 hrowReady.2

def tttFiber32ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber32Rows tttLightMaxParentDepth
    (listGetD tttFiber32Expected i 0) == 256

theorem tttFiber32Parent_0_ok : tttFiber32ParentCheck 0 = true := by
  decide
theorem tttFiber32Parent_1_ok : tttFiber32ParentCheck 1 = true := by
  decide
theorem tttFiber32Parent_2_ok : tttFiber32ParentCheck 2 = true := by
  decide
theorem tttFiber32Parent_3_ok : tttFiber32ParentCheck 3 = true := by
  decide
theorem tttFiber32Parent_4_ok : tttFiber32ParentCheck 4 = true := by
  decide
theorem tttFiber32Parent_5_ok : tttFiber32ParentCheck 5 = true := by
  decide
theorem tttFiber32Parent_6_ok : tttFiber32ParentCheck 6 = true := by
  decide
theorem tttFiber32Parent_7_ok : tttFiber32ParentCheck 7 = true := by
  decide
theorem tttFiber32Parent_8_ok : tttFiber32ParentCheck 8 = true := by
  decide
theorem tttFiber32Parent_9_ok : tttFiber32ParentCheck 9 = true := by
  decide
theorem tttFiber32Parent_10_ok : tttFiber32ParentCheck 10 = true := by
  decide
theorem tttFiber32Parent_11_ok : tttFiber32ParentCheck 11 = true := by
  decide
theorem tttFiber32Parent_12_ok : tttFiber32ParentCheck 12 = true := by
  decide
theorem tttFiber32Parent_13_ok : tttFiber32ParentCheck 13 = true := by
  decide
theorem tttFiber32Parent_14_ok : tttFiber32ParentCheck 14 = true := by
  decide
theorem tttFiber32Parent_15_ok : tttFiber32ParentCheck 15 = true := by
  decide

def tttFiber32CertificateAudit : Bool :=
  tttFiber32SourcesCheck
    && tttFiber32RowCheck 0
    && tttFiber32RowCheck 1
    && tttFiber32RowCheck 2
    && tttFiber32RowCheck 3
    && tttFiber32RowCheck 4
    && tttFiber32RowCheck 5
    && tttFiber32RowCheck 6
    && tttFiber32RowCheck 7
    && tttFiber32RowCheck 8
    && tttFiber32RowCheck 9
    && tttFiber32RowCheck 10
    && tttFiber32RowCheck 11
    && tttFiber32RowCheck 12
    && tttFiber32RowCheck 13
    && tttFiber32RowCheck 14
    && tttFiber32RowCheck 15
    && tttFiber32ParentCheck 0
    && tttFiber32ParentCheck 1
    && tttFiber32ParentCheck 2
    && tttFiber32ParentCheck 3
    && tttFiber32ParentCheck 4
    && tttFiber32ParentCheck 5
    && tttFiber32ParentCheck 6
    && tttFiber32ParentCheck 7
    && tttFiber32ParentCheck 8
    && tttFiber32ParentCheck 9
    && tttFiber32ParentCheck 10
    && tttFiber32ParentCheck 11
    && tttFiber32ParentCheck 12
    && tttFiber32ParentCheck 13
    && tttFiber32ParentCheck 14
    && tttFiber32ParentCheck 15

theorem tttFiber32CertificateAudit_ok :
    tttFiber32CertificateAudit = true := by
  simp [tttFiber32CertificateAudit,
    tttFiber32SourcesCheck_ok,
    tttFiber32Row_0_ok,
    tttFiber32Row_1_ok,
    tttFiber32Row_2_ok,
    tttFiber32Row_3_ok,
    tttFiber32Row_4_ok,
    tttFiber32Row_5_ok,
    tttFiber32Row_6_ok,
    tttFiber32Row_7_ok,
    tttFiber32Row_8_ok,
    tttFiber32Row_9_ok,
    tttFiber32Row_10_ok,
    tttFiber32Row_11_ok,
    tttFiber32Row_12_ok,
    tttFiber32Row_13_ok,
    tttFiber32Row_14_ok,
    tttFiber32Row_15_ok,
    tttFiber32Parent_0_ok,
    tttFiber32Parent_1_ok,
    tttFiber32Parent_2_ok,
    tttFiber32Parent_3_ok,
    tttFiber32Parent_4_ok,
    tttFiber32Parent_5_ok,
    tttFiber32Parent_6_ok,
    tttFiber32Parent_7_ok,
    tttFiber32Parent_8_ok,
    tttFiber32Parent_9_ok,
    tttFiber32Parent_10_ok,
    tttFiber32Parent_11_ok,
    tttFiber32Parent_12_ok,
    tttFiber32Parent_13_ok,
    tttFiber32Parent_14_ok,
    tttFiber32Parent_15_ok]

def tttFiber33Key : List LColor :=
  [LColor.b, LColor.r, LColor.p, LColor.r]

def tttFiber33Expected : List Nat :=
  []

def tttFiber33Rows : List TripleComponentParentRow :=
  []

def tttFiber33SourcesCheck : Bool :=
  (tttFiber33Rows.map fun row => row.source) == tttFiber33Expected

theorem tttFiber33SourcesCheck_ok :
    tttFiber33SourcesCheck = true := by
  decide

def tttFiber33CertificateAudit : Bool :=
  tttFiber33SourcesCheck

theorem tttFiber33CertificateAudit_ok :
    tttFiber33CertificateAudit = true := by
  simp [tttFiber33CertificateAudit,
    tttFiber33SourcesCheck_ok]

def tttFiber34Key : List LColor :=
  [LColor.b, LColor.r, LColor.p, LColor.b]

def tttFiber34Expected : List Nat :=
  []

def tttFiber34Rows : List TripleComponentParentRow :=
  []

def tttFiber34SourcesCheck : Bool :=
  (tttFiber34Rows.map fun row => row.source) == tttFiber34Expected

theorem tttFiber34SourcesCheck_ok :
    tttFiber34SourcesCheck = true := by
  decide

def tttFiber34CertificateAudit : Bool :=
  tttFiber34SourcesCheck

theorem tttFiber34CertificateAudit_ok :
    tttFiber34CertificateAudit = true := by
  simp [tttFiber34CertificateAudit,
    tttFiber34SourcesCheck_ok]

def tttFiber35Key : List LColor :=
  [LColor.b, LColor.r, LColor.p, LColor.p]

def tttFiber35Expected : List Nat :=
  []

def tttFiber35Rows : List TripleComponentParentRow :=
  []

def tttFiber35SourcesCheck : Bool :=
  (tttFiber35Rows.map fun row => row.source) == tttFiber35Expected

theorem tttFiber35SourcesCheck_ok :
    tttFiber35SourcesCheck = true := by
  decide

def tttFiber35CertificateAudit : Bool :=
  tttFiber35SourcesCheck

theorem tttFiber35CertificateAudit_ok :
    tttFiber35CertificateAudit = true := by
  simp [tttFiber35CertificateAudit,
    tttFiber35SourcesCheck_ok]

def tttFiber37Key : List LColor :=
  [LColor.b, LColor.b, LColor.r, LColor.b]

def tttFiber37Expected : List Nat :=
  [2160, 2161, 2162, 2163, 2164, 2165, 2166, 2167,
   2168, 2169, 2170, 2171, 2172, 2173, 2174, 2175]

def tttFiber37Row0 : TripleComponentParentRow :=
  tripleRow 2160 2160 62 114 52 62 114 52
    default
    []

def tttFiber37Row1 : TripleComponentParentRow :=
  tripleRow 2161 2160 62 114 53 62 114 52
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber37Row2 : TripleComponentParentRow :=
  tripleRow 2162 2161 62 114 54 62 114 53
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber37Row3 : TripleComponentParentRow :=
  tripleRow 2163 2160 62 114 55 62 114 52
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber37Row4 : TripleComponentParentRow :=
  tripleRow 2164 2160 62 115 60 62 114 52
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber37Row5 : TripleComponentParentRow :=
  tripleRow 2165 2161 62 115 61 62 114 53
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber37Row6 : TripleComponentParentRow :=
  tripleRow 2166 2162 62 115 62 62 114 54
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber37Row7 : TripleComponentParentRow :=
  tripleRow 2167 2163 62 115 63 62 114 55
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber37Row8 : TripleComponentParentRow :=
  tripleRow 2168 2160 63 122 52 62 114 52
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber37Row9 : TripleComponentParentRow :=
  tripleRow 2169 2161 63 122 53 62 114 53
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber37Row10 : TripleComponentParentRow :=
  tripleRow 2170 2162 63 122 54 62 114 54
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber37Row11 : TripleComponentParentRow :=
  tripleRow 2171 2163 63 122 55 62 114 55
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber37Row12 : TripleComponentParentRow :=
  tripleRow 2172 2164 63 123 60 62 115 60
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber37Row13 : TripleComponentParentRow :=
  tripleRow 2173 2165 63 123 61 62 115 61
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber37Row14 : TripleComponentParentRow :=
  tripleRow 2174 2166 63 123 62 62 115 62
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber37Row15 : TripleComponentParentRow :=
  tripleRow 2175 2167 63 123 63 62 115 63
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber37Rows : List TripleComponentParentRow :=
  [ tttFiber37Row0
  , tttFiber37Row1
  , tttFiber37Row2
  , tttFiber37Row3
  , tttFiber37Row4
  , tttFiber37Row5
  , tttFiber37Row6
  , tttFiber37Row7
  , tttFiber37Row8
  , tttFiber37Row9
  , tttFiber37Row10
  , tttFiber37Row11
  , tttFiber37Row12
  , tttFiber37Row13
  , tttFiber37Row14
  , tttFiber37Row15
  ]

def tttFiber37SourcesCheck : Bool :=
  (tttFiber37Rows.map fun row => row.source) == tttFiber37Expected

theorem tttFiber37SourcesCheck_ok :
    tttFiber37SourcesCheck = true := by
  decide

def tttFiber37RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber37Key tttFiber37Expected
    (listGetD tttFiber37Rows i default)

theorem tttFiber37Row_0_ok : tttFiber37RowCheck 0 = true := by
  decide
theorem tttFiber37Row_1_ok : tttFiber37RowCheck 1 = true := by
  decide
theorem tttFiber37Row_2_ok : tttFiber37RowCheck 2 = true := by
  decide
theorem tttFiber37Row_3_ok : tttFiber37RowCheck 3 = true := by
  decide
theorem tttFiber37Row_4_ok : tttFiber37RowCheck 4 = true := by
  decide
theorem tttFiber37Row_5_ok : tttFiber37RowCheck 5 = true := by
  decide
theorem tttFiber37Row_6_ok : tttFiber37RowCheck 6 = true := by
  decide
theorem tttFiber37Row_7_ok : tttFiber37RowCheck 7 = true := by
  decide
theorem tttFiber37Row_8_ok : tttFiber37RowCheck 8 = true := by
  decide
theorem tttFiber37Row_9_ok : tttFiber37RowCheck 9 = true := by
  decide
theorem tttFiber37Row_10_ok : tttFiber37RowCheck 10 = true := by
  decide
theorem tttFiber37Row_11_ok : tttFiber37RowCheck 11 = true := by
  decide
theorem tttFiber37Row_12_ok : tttFiber37RowCheck 12 = true := by
  decide
theorem tttFiber37Row_13_ok : tttFiber37RowCheck 13 = true := by
  decide
theorem tttFiber37Row_14_ok : tttFiber37RowCheck 14 = true := by
  decide
theorem tttFiber37Row_15_ok : tttFiber37RowCheck 15 = true := by
  decide

def tttFiber37ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber37Rows tttLightMaxParentDepth
    (listGetD tttFiber37Expected i 0) == 2160

theorem tttFiber37Parent_0_ok : tttFiber37ParentCheck 0 = true := by
  decide
theorem tttFiber37Parent_1_ok : tttFiber37ParentCheck 1 = true := by
  decide
theorem tttFiber37Parent_2_ok : tttFiber37ParentCheck 2 = true := by
  decide
theorem tttFiber37Parent_3_ok : tttFiber37ParentCheck 3 = true := by
  decide
theorem tttFiber37Parent_4_ok : tttFiber37ParentCheck 4 = true := by
  decide
theorem tttFiber37Parent_5_ok : tttFiber37ParentCheck 5 = true := by
  decide
theorem tttFiber37Parent_6_ok : tttFiber37ParentCheck 6 = true := by
  decide
theorem tttFiber37Parent_7_ok : tttFiber37ParentCheck 7 = true := by
  decide
theorem tttFiber37Parent_8_ok : tttFiber37ParentCheck 8 = true := by
  decide
theorem tttFiber37Parent_9_ok : tttFiber37ParentCheck 9 = true := by
  decide
theorem tttFiber37Parent_10_ok : tttFiber37ParentCheck 10 = true := by
  decide
theorem tttFiber37Parent_11_ok : tttFiber37ParentCheck 11 = true := by
  decide
theorem tttFiber37Parent_12_ok : tttFiber37ParentCheck 12 = true := by
  decide
theorem tttFiber37Parent_13_ok : tttFiber37ParentCheck 13 = true := by
  decide
theorem tttFiber37Parent_14_ok : tttFiber37ParentCheck 14 = true := by
  decide
theorem tttFiber37Parent_15_ok : tttFiber37ParentCheck 15 = true := by
  decide

def tttFiber37CertificateAudit : Bool :=
  tttFiber37SourcesCheck
    && tttFiber37RowCheck 0
    && tttFiber37RowCheck 1
    && tttFiber37RowCheck 2
    && tttFiber37RowCheck 3
    && tttFiber37RowCheck 4
    && tttFiber37RowCheck 5
    && tttFiber37RowCheck 6
    && tttFiber37RowCheck 7
    && tttFiber37RowCheck 8
    && tttFiber37RowCheck 9
    && tttFiber37RowCheck 10
    && tttFiber37RowCheck 11
    && tttFiber37RowCheck 12
    && tttFiber37RowCheck 13
    && tttFiber37RowCheck 14
    && tttFiber37RowCheck 15
    && tttFiber37ParentCheck 0
    && tttFiber37ParentCheck 1
    && tttFiber37ParentCheck 2
    && tttFiber37ParentCheck 3
    && tttFiber37ParentCheck 4
    && tttFiber37ParentCheck 5
    && tttFiber37ParentCheck 6
    && tttFiber37ParentCheck 7
    && tttFiber37ParentCheck 8
    && tttFiber37ParentCheck 9
    && tttFiber37ParentCheck 10
    && tttFiber37ParentCheck 11
    && tttFiber37ParentCheck 12
    && tttFiber37ParentCheck 13
    && tttFiber37ParentCheck 14
    && tttFiber37ParentCheck 15

theorem tttFiber37CertificateAudit_ok :
    tttFiber37CertificateAudit = true := by
  simp [tttFiber37CertificateAudit,
    tttFiber37SourcesCheck_ok,
    tttFiber37Row_0_ok,
    tttFiber37Row_1_ok,
    tttFiber37Row_2_ok,
    tttFiber37Row_3_ok,
    tttFiber37Row_4_ok,
    tttFiber37Row_5_ok,
    tttFiber37Row_6_ok,
    tttFiber37Row_7_ok,
    tttFiber37Row_8_ok,
    tttFiber37Row_9_ok,
    tttFiber37Row_10_ok,
    tttFiber37Row_11_ok,
    tttFiber37Row_12_ok,
    tttFiber37Row_13_ok,
    tttFiber37Row_14_ok,
    tttFiber37Row_15_ok,
    tttFiber37Parent_0_ok,
    tttFiber37Parent_1_ok,
    tttFiber37Parent_2_ok,
    tttFiber37Parent_3_ok,
    tttFiber37Parent_4_ok,
    tttFiber37Parent_5_ok,
    tttFiber37Parent_6_ok,
    tttFiber37Parent_7_ok,
    tttFiber37Parent_8_ok,
    tttFiber37Parent_9_ok,
    tttFiber37Parent_10_ok,
    tttFiber37Parent_11_ok,
    tttFiber37Parent_12_ok,
    tttFiber37Parent_13_ok,
    tttFiber37Parent_14_ok,
    tttFiber37Parent_15_ok]

def tttFiber38Key : List LColor :=
  [LColor.b, LColor.b, LColor.r, LColor.p]

def tttFiber38Expected : List Nat :=
  [528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543]

def tttFiber38Row0 : TripleComponentParentRow :=
  tripleRow 528 528 14 176 20 14 176 20
    default
    []

def tttFiber38Row1 : TripleComponentParentRow :=
  tripleRow 529 528 14 176 21 14 176 20
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber38Row2 : TripleComponentParentRow :=
  tripleRow 530 528 14 176 22 14 176 20
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber38Row3 : TripleComponentParentRow :=
  tripleRow 531 529 14 176 23 14 176 21
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber38Row4 : TripleComponentParentRow :=
  tripleRow 532 528 14 177 28 14 176 20
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber38Row5 : TripleComponentParentRow :=
  tripleRow 533 529 14 177 29 14 176 21
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber38Row6 : TripleComponentParentRow :=
  tripleRow 534 530 14 177 30 14 176 22
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber38Row7 : TripleComponentParentRow :=
  tripleRow 535 531 14 177 31 14 176 23
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber38Row8 : TripleComponentParentRow :=
  tripleRow 536 528 15 184 20 14 176 20
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber38Row9 : TripleComponentParentRow :=
  tripleRow 537 529 15 184 21 14 176 21
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber38Row10 : TripleComponentParentRow :=
  tripleRow 538 530 15 184 22 14 176 22
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber38Row11 : TripleComponentParentRow :=
  tripleRow 539 531 15 184 23 14 176 23
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber38Row12 : TripleComponentParentRow :=
  tripleRow 540 532 15 185 28 14 177 28
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber38Row13 : TripleComponentParentRow :=
  tripleRow 541 533 15 185 29 14 177 29
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber38Row14 : TripleComponentParentRow :=
  tripleRow 542 534 15 185 30 14 177 30
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber38Row15 : TripleComponentParentRow :=
  tripleRow 543 535 15 185 31 14 177 31
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber38Rows : List TripleComponentParentRow :=
  [ tttFiber38Row0
  , tttFiber38Row1
  , tttFiber38Row2
  , tttFiber38Row3
  , tttFiber38Row4
  , tttFiber38Row5
  , tttFiber38Row6
  , tttFiber38Row7
  , tttFiber38Row8
  , tttFiber38Row9
  , tttFiber38Row10
  , tttFiber38Row11
  , tttFiber38Row12
  , tttFiber38Row13
  , tttFiber38Row14
  , tttFiber38Row15
  ]

def tttFiber38SourcesCheck : Bool :=
  (tttFiber38Rows.map fun row => row.source) == tttFiber38Expected

theorem tttFiber38SourcesCheck_ok :
    tttFiber38SourcesCheck = true := by
  decide

def tttFiber38RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber38Key tttFiber38Expected
    (listGetD tttFiber38Rows i default)

theorem tttFiber38Row_0_ok : tttFiber38RowCheck 0 = true := by
  decide
theorem tttFiber38Row_1_ok : tttFiber38RowCheck 1 = true := by
  decide
theorem tttFiber38Row_2_ok : tttFiber38RowCheck 2 = true := by
  decide
theorem tttFiber38Row_3_ok : tttFiber38RowCheck 3 = true := by
  decide
theorem tttFiber38Row_4_ok : tttFiber38RowCheck 4 = true := by
  decide
theorem tttFiber38Row_5_ok : tttFiber38RowCheck 5 = true := by
  decide
theorem tttFiber38Row_6_ok : tttFiber38RowCheck 6 = true := by
  decide
theorem tttFiber38Row_7_ok : tttFiber38RowCheck 7 = true := by
  decide
theorem tttFiber38Row_8_ok : tttFiber38RowCheck 8 = true := by
  decide
theorem tttFiber38Row_9_ok : tttFiber38RowCheck 9 = true := by
  decide
theorem tttFiber38Row_10_ok : tttFiber38RowCheck 10 = true := by
  decide
theorem tttFiber38Row_11_ok : tttFiber38RowCheck 11 = true := by
  decide
theorem tttFiber38Row_12_ok : tttFiber38RowCheck 12 = true := by
  decide
theorem tttFiber38Row_13_ok : tttFiber38RowCheck 13 = true := by
  decide
theorem tttFiber38Row_14_ok : tttFiber38RowCheck 14 = true := by
  decide
theorem tttFiber38Row_15_ok : tttFiber38RowCheck 15 = true := by
  decide

def tttFiber38ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber38Rows tttLightMaxParentDepth
    (listGetD tttFiber38Expected i 0) == 528

theorem tttFiber38Parent_0_ok : tttFiber38ParentCheck 0 = true := by
  decide
theorem tttFiber38Parent_1_ok : tttFiber38ParentCheck 1 = true := by
  decide
theorem tttFiber38Parent_2_ok : tttFiber38ParentCheck 2 = true := by
  decide
theorem tttFiber38Parent_3_ok : tttFiber38ParentCheck 3 = true := by
  decide
theorem tttFiber38Parent_4_ok : tttFiber38ParentCheck 4 = true := by
  decide
theorem tttFiber38Parent_5_ok : tttFiber38ParentCheck 5 = true := by
  decide
theorem tttFiber38Parent_6_ok : tttFiber38ParentCheck 6 = true := by
  decide
theorem tttFiber38Parent_7_ok : tttFiber38ParentCheck 7 = true := by
  decide
theorem tttFiber38Parent_8_ok : tttFiber38ParentCheck 8 = true := by
  decide
theorem tttFiber38Parent_9_ok : tttFiber38ParentCheck 9 = true := by
  decide
theorem tttFiber38Parent_10_ok : tttFiber38ParentCheck 10 = true := by
  decide
theorem tttFiber38Parent_11_ok : tttFiber38ParentCheck 11 = true := by
  decide
theorem tttFiber38Parent_12_ok : tttFiber38ParentCheck 12 = true := by
  decide
theorem tttFiber38Parent_13_ok : tttFiber38ParentCheck 13 = true := by
  decide
theorem tttFiber38Parent_14_ok : tttFiber38ParentCheck 14 = true := by
  decide
theorem tttFiber38Parent_15_ok : tttFiber38ParentCheck 15 = true := by
  decide

def tttFiber38CertificateAudit : Bool :=
  tttFiber38SourcesCheck
    && tttFiber38RowCheck 0
    && tttFiber38RowCheck 1
    && tttFiber38RowCheck 2
    && tttFiber38RowCheck 3
    && tttFiber38RowCheck 4
    && tttFiber38RowCheck 5
    && tttFiber38RowCheck 6
    && tttFiber38RowCheck 7
    && tttFiber38RowCheck 8
    && tttFiber38RowCheck 9
    && tttFiber38RowCheck 10
    && tttFiber38RowCheck 11
    && tttFiber38RowCheck 12
    && tttFiber38RowCheck 13
    && tttFiber38RowCheck 14
    && tttFiber38RowCheck 15
    && tttFiber38ParentCheck 0
    && tttFiber38ParentCheck 1
    && tttFiber38ParentCheck 2
    && tttFiber38ParentCheck 3
    && tttFiber38ParentCheck 4
    && tttFiber38ParentCheck 5
    && tttFiber38ParentCheck 6
    && tttFiber38ParentCheck 7
    && tttFiber38ParentCheck 8
    && tttFiber38ParentCheck 9
    && tttFiber38ParentCheck 10
    && tttFiber38ParentCheck 11
    && tttFiber38ParentCheck 12
    && tttFiber38ParentCheck 13
    && tttFiber38ParentCheck 14
    && tttFiber38ParentCheck 15

theorem tttFiber38CertificateAudit_ok :
    tttFiber38CertificateAudit = true := by
  simp [tttFiber38CertificateAudit,
    tttFiber38SourcesCheck_ok,
    tttFiber38Row_0_ok,
    tttFiber38Row_1_ok,
    tttFiber38Row_2_ok,
    tttFiber38Row_3_ok,
    tttFiber38Row_4_ok,
    tttFiber38Row_5_ok,
    tttFiber38Row_6_ok,
    tttFiber38Row_7_ok,
    tttFiber38Row_8_ok,
    tttFiber38Row_9_ok,
    tttFiber38Row_10_ok,
    tttFiber38Row_11_ok,
    tttFiber38Row_12_ok,
    tttFiber38Row_13_ok,
    tttFiber38Row_14_ok,
    tttFiber38Row_15_ok,
    tttFiber38Parent_0_ok,
    tttFiber38Parent_1_ok,
    tttFiber38Parent_2_ok,
    tttFiber38Parent_3_ok,
    tttFiber38Parent_4_ok,
    tttFiber38Parent_5_ok,
    tttFiber38Parent_6_ok,
    tttFiber38Parent_7_ok,
    tttFiber38Parent_8_ok,
    tttFiber38Parent_9_ok,
    tttFiber38Parent_10_ok,
    tttFiber38Parent_11_ok,
    tttFiber38Parent_12_ok,
    tttFiber38Parent_13_ok,
    tttFiber38Parent_14_ok,
    tttFiber38Parent_15_ok]

def tttFiber39Key : List LColor :=
  [LColor.b, LColor.b, LColor.b, LColor.r]

def tttFiber39Expected : List Nat :=
  []

def tttFiber39Rows : List TripleComponentParentRow :=
  []

def tttFiber39SourcesCheck : Bool :=
  (tttFiber39Rows.map fun row => row.source) == tttFiber39Expected

theorem tttFiber39SourcesCheck_ok :
    tttFiber39SourcesCheck = true := by
  decide

def tttFiber39CertificateAudit : Bool :=
  tttFiber39SourcesCheck

theorem tttFiber39CertificateAudit_ok :
    tttFiber39CertificateAudit = true := by
  simp [tttFiber39CertificateAudit,
    tttFiber39SourcesCheck_ok]

def tttFiber40Key : List LColor :=
  [LColor.b, LColor.b, LColor.b, LColor.b]

def tttFiber40Expected : List Nat :=
  []

def tttFiber40Rows : List TripleComponentParentRow :=
  []

def tttFiber40SourcesCheck : Bool :=
  (tttFiber40Rows.map fun row => row.source) == tttFiber40Expected

theorem tttFiber40SourcesCheck_ok :
    tttFiber40SourcesCheck = true := by
  decide

def tttFiber40CertificateAudit : Bool :=
  tttFiber40SourcesCheck

theorem tttFiber40CertificateAudit_ok :
    tttFiber40CertificateAudit = true := by
  simp [tttFiber40CertificateAudit,
    tttFiber40SourcesCheck_ok]

def tttFiber41Key : List LColor :=
  [LColor.b, LColor.b, LColor.b, LColor.p]

def tttFiber41Expected : List Nat :=
  []

def tttFiber41Rows : List TripleComponentParentRow :=
  []

def tttFiber41SourcesCheck : Bool :=
  (tttFiber41Rows.map fun row => row.source) == tttFiber41Expected

theorem tttFiber41SourcesCheck_ok :
    tttFiber41SourcesCheck = true := by
  decide

def tttFiber41CertificateAudit : Bool :=
  tttFiber41SourcesCheck

theorem tttFiber41CertificateAudit_ok :
    tttFiber41CertificateAudit = true := by
  simp [tttFiber41CertificateAudit,
    tttFiber41SourcesCheck_ok]

def tttFiber42Key : List LColor :=
  [LColor.b, LColor.b, LColor.p, LColor.r]

def tttFiber42Expected : List Nat :=
  [5440, 5441, 5442, 5443, 5444, 5445, 5446, 5447,
   5448, 5449, 5450, 5451, 5452, 5453, 5454, 5455]

def tttFiber42Row0 : TripleComponentParentRow :=
  tripleRow 5440 5440 160 22 176 160 22 176
    default
    []

def tttFiber42Row1 : TripleComponentParentRow :=
  tripleRow 5441 5440 160 22 177 160 22 176
    (chainMove LColor.r LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber42Row2 : TripleComponentParentRow :=
  tripleRow 5442 5440 160 22 178 160 22 176
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber42Row3 : TripleComponentParentRow :=
  tripleRow 5443 5441 160 22 179 160 22 177
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber42Row4 : TripleComponentParentRow :=
  tripleRow 5444 5440 160 23 184 160 22 176
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber42Row5 : TripleComponentParentRow :=
  tripleRow 5445 5441 160 23 185 160 22 177
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber42Row6 : TripleComponentParentRow :=
  tripleRow 5446 5442 160 23 186 160 22 178
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber42Row7 : TripleComponentParentRow :=
  tripleRow 5447 5443 160 23 187 160 22 179
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber42Row8 : TripleComponentParentRow :=
  tripleRow 5448 5440 161 30 176 160 22 176
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber42Row9 : TripleComponentParentRow :=
  tripleRow 5449 5441 161 30 177 160 22 177
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber42Row10 : TripleComponentParentRow :=
  tripleRow 5450 5442 161 30 178 160 22 178
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber42Row11 : TripleComponentParentRow :=
  tripleRow 5451 5443 161 30 179 160 22 179
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber42Row12 : TripleComponentParentRow :=
  tripleRow 5452 5444 161 31 184 160 23 184
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber42Row13 : TripleComponentParentRow :=
  tripleRow 5453 5445 161 31 185 160 23 185
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber42Row14 : TripleComponentParentRow :=
  tripleRow 5454 5446 161 31 186 160 23 186
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber42Row15 : TripleComponentParentRow :=
  tripleRow 5455 5447 161 31 187 160 23 187
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber42Rows : List TripleComponentParentRow :=
  [ tttFiber42Row0
  , tttFiber42Row1
  , tttFiber42Row2
  , tttFiber42Row3
  , tttFiber42Row4
  , tttFiber42Row5
  , tttFiber42Row6
  , tttFiber42Row7
  , tttFiber42Row8
  , tttFiber42Row9
  , tttFiber42Row10
  , tttFiber42Row11
  , tttFiber42Row12
  , tttFiber42Row13
  , tttFiber42Row14
  , tttFiber42Row15
  ]

def tttFiber42SourcesCheck : Bool :=
  (tttFiber42Rows.map fun row => row.source) == tttFiber42Expected

theorem tttFiber42SourcesCheck_ok :
    tttFiber42SourcesCheck = true := by
  decide

def tttFiber42RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber42Key tttFiber42Expected
    (listGetD tttFiber42Rows i default)

theorem tttFiber42Row_0_ok : tttFiber42RowCheck 0 = true := by
  decide
theorem tttFiber42Row_1_ok : tttFiber42RowCheck 1 = true := by
  decide
theorem tttFiber42Row_2_ok : tttFiber42RowCheck 2 = true := by
  decide
theorem tttFiber42Row_3_ok : tttFiber42RowCheck 3 = true := by
  decide
theorem tttFiber42Row_4_ok : tttFiber42RowCheck 4 = true := by
  decide
theorem tttFiber42Row_5_ok : tttFiber42RowCheck 5 = true := by
  decide
theorem tttFiber42Row_6_ok : tttFiber42RowCheck 6 = true := by
  decide
theorem tttFiber42Row_7_ok : tttFiber42RowCheck 7 = true := by
  decide
theorem tttFiber42Row_8_ok : tttFiber42RowCheck 8 = true := by
  decide
theorem tttFiber42Row_9_ok : tttFiber42RowCheck 9 = true := by
  decide
theorem tttFiber42Row_10_ok : tttFiber42RowCheck 10 = true := by
  decide
theorem tttFiber42Row_11_ok : tttFiber42RowCheck 11 = true := by
  decide
theorem tttFiber42Row_12_ok : tttFiber42RowCheck 12 = true := by
  decide
theorem tttFiber42Row_13_ok : tttFiber42RowCheck 13 = true := by
  decide
theorem tttFiber42Row_14_ok : tttFiber42RowCheck 14 = true := by
  decide
theorem tttFiber42Row_15_ok : tttFiber42RowCheck 15 = true := by
  decide

def tttFiber42ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber42Rows tttLightMaxParentDepth
    (listGetD tttFiber42Expected i 0) == 5440

theorem tttFiber42Parent_0_ok : tttFiber42ParentCheck 0 = true := by
  decide
theorem tttFiber42Parent_1_ok : tttFiber42ParentCheck 1 = true := by
  decide
theorem tttFiber42Parent_2_ok : tttFiber42ParentCheck 2 = true := by
  decide
theorem tttFiber42Parent_3_ok : tttFiber42ParentCheck 3 = true := by
  decide
theorem tttFiber42Parent_4_ok : tttFiber42ParentCheck 4 = true := by
  decide
theorem tttFiber42Parent_5_ok : tttFiber42ParentCheck 5 = true := by
  decide
theorem tttFiber42Parent_6_ok : tttFiber42ParentCheck 6 = true := by
  decide
theorem tttFiber42Parent_7_ok : tttFiber42ParentCheck 7 = true := by
  decide
theorem tttFiber42Parent_8_ok : tttFiber42ParentCheck 8 = true := by
  decide
theorem tttFiber42Parent_9_ok : tttFiber42ParentCheck 9 = true := by
  decide
theorem tttFiber42Parent_10_ok : tttFiber42ParentCheck 10 = true := by
  decide
theorem tttFiber42Parent_11_ok : tttFiber42ParentCheck 11 = true := by
  decide
theorem tttFiber42Parent_12_ok : tttFiber42ParentCheck 12 = true := by
  decide
theorem tttFiber42Parent_13_ok : tttFiber42ParentCheck 13 = true := by
  decide
theorem tttFiber42Parent_14_ok : tttFiber42ParentCheck 14 = true := by
  decide
theorem tttFiber42Parent_15_ok : tttFiber42ParentCheck 15 = true := by
  decide

def tttFiber42CertificateAudit : Bool :=
  tttFiber42SourcesCheck
    && tttFiber42RowCheck 0
    && tttFiber42RowCheck 1
    && tttFiber42RowCheck 2
    && tttFiber42RowCheck 3
    && tttFiber42RowCheck 4
    && tttFiber42RowCheck 5
    && tttFiber42RowCheck 6
    && tttFiber42RowCheck 7
    && tttFiber42RowCheck 8
    && tttFiber42RowCheck 9
    && tttFiber42RowCheck 10
    && tttFiber42RowCheck 11
    && tttFiber42RowCheck 12
    && tttFiber42RowCheck 13
    && tttFiber42RowCheck 14
    && tttFiber42RowCheck 15
    && tttFiber42ParentCheck 0
    && tttFiber42ParentCheck 1
    && tttFiber42ParentCheck 2
    && tttFiber42ParentCheck 3
    && tttFiber42ParentCheck 4
    && tttFiber42ParentCheck 5
    && tttFiber42ParentCheck 6
    && tttFiber42ParentCheck 7
    && tttFiber42ParentCheck 8
    && tttFiber42ParentCheck 9
    && tttFiber42ParentCheck 10
    && tttFiber42ParentCheck 11
    && tttFiber42ParentCheck 12
    && tttFiber42ParentCheck 13
    && tttFiber42ParentCheck 14
    && tttFiber42ParentCheck 15

theorem tttFiber42CertificateAudit_ok :
    tttFiber42CertificateAudit = true := by
  simp [tttFiber42CertificateAudit,
    tttFiber42SourcesCheck_ok,
    tttFiber42Row_0_ok,
    tttFiber42Row_1_ok,
    tttFiber42Row_2_ok,
    tttFiber42Row_3_ok,
    tttFiber42Row_4_ok,
    tttFiber42Row_5_ok,
    tttFiber42Row_6_ok,
    tttFiber42Row_7_ok,
    tttFiber42Row_8_ok,
    tttFiber42Row_9_ok,
    tttFiber42Row_10_ok,
    tttFiber42Row_11_ok,
    tttFiber42Row_12_ok,
    tttFiber42Row_13_ok,
    tttFiber42Row_14_ok,
    tttFiber42Row_15_ok,
    tttFiber42Parent_0_ok,
    tttFiber42Parent_1_ok,
    tttFiber42Parent_2_ok,
    tttFiber42Parent_3_ok,
    tttFiber42Parent_4_ok,
    tttFiber42Parent_5_ok,
    tttFiber42Parent_6_ok,
    tttFiber42Parent_7_ok,
    tttFiber42Parent_8_ok,
    tttFiber42Parent_9_ok,
    tttFiber42Parent_10_ok,
    tttFiber42Parent_11_ok,
    tttFiber42Parent_12_ok,
    tttFiber42Parent_13_ok,
    tttFiber42Parent_14_ok,
    tttFiber42Parent_15_ok]

def tttFiber43Key : List LColor :=
  [LColor.b, LColor.b, LColor.p, LColor.b]

def tttFiber43Expected : List Nat :=
  [4896, 4897, 4898, 4899, 4900, 4901, 4902, 4903,
   4904, 4905, 4906, 4907, 4908, 4909, 4910, 4911]

def tttFiber43Row0 : TripleComponentParentRow :=
  tripleRow 4896 4896 144 84 144 144 84 144
    default
    []

def tttFiber43Row1 : TripleComponentParentRow :=
  tripleRow 4897 4896 144 84 145 144 84 144
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber43Row2 : TripleComponentParentRow :=
  tripleRow 4898 4897 144 84 146 144 84 145
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber43Row3 : TripleComponentParentRow :=
  tripleRow 4899 4896 144 84 147 144 84 144
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber43Row4 : TripleComponentParentRow :=
  tripleRow 4900 4896 144 85 152 144 84 144
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber43Row5 : TripleComponentParentRow :=
  tripleRow 4901 4897 144 85 153 144 84 145
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber43Row6 : TripleComponentParentRow :=
  tripleRow 4902 4898 144 85 154 144 84 146
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber43Row7 : TripleComponentParentRow :=
  tripleRow 4903 4899 144 85 155 144 84 147
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber43Row8 : TripleComponentParentRow :=
  tripleRow 4904 4896 145 92 144 144 84 144
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber43Row9 : TripleComponentParentRow :=
  tripleRow 4905 4897 145 92 145 144 84 145
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber43Row10 : TripleComponentParentRow :=
  tripleRow 4906 4898 145 92 146 144 84 146
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber43Row11 : TripleComponentParentRow :=
  tripleRow 4907 4899 145 92 147 144 84 147
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber43Row12 : TripleComponentParentRow :=
  tripleRow 4908 4900 145 93 152 144 85 152
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber43Row13 : TripleComponentParentRow :=
  tripleRow 4909 4901 145 93 153 144 85 153
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber43Row14 : TripleComponentParentRow :=
  tripleRow 4910 4902 145 93 154 144 85 154
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber43Row15 : TripleComponentParentRow :=
  tripleRow 4911 4903 145 93 155 144 85 155
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber43Rows : List TripleComponentParentRow :=
  [ tttFiber43Row0
  , tttFiber43Row1
  , tttFiber43Row2
  , tttFiber43Row3
  , tttFiber43Row4
  , tttFiber43Row5
  , tttFiber43Row6
  , tttFiber43Row7
  , tttFiber43Row8
  , tttFiber43Row9
  , tttFiber43Row10
  , tttFiber43Row11
  , tttFiber43Row12
  , tttFiber43Row13
  , tttFiber43Row14
  , tttFiber43Row15
  ]

def tttFiber43SourcesCheck : Bool :=
  (tttFiber43Rows.map fun row => row.source) == tttFiber43Expected

theorem tttFiber43SourcesCheck_ok :
    tttFiber43SourcesCheck = true := by
  decide

def tttFiber43RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber43Key tttFiber43Expected
    (listGetD tttFiber43Rows i default)

theorem tttFiber43Row_0_ok : tttFiber43RowCheck 0 = true := by
  decide
theorem tttFiber43Row_1_ok : tttFiber43RowCheck 1 = true := by
  decide
theorem tttFiber43Row_2_ok : tttFiber43RowCheck 2 = true := by
  decide
theorem tttFiber43Row_3_ok : tttFiber43RowCheck 3 = true := by
  decide
theorem tttFiber43Row_4_ok : tttFiber43RowCheck 4 = true := by
  decide
theorem tttFiber43Row_5_ok : tttFiber43RowCheck 5 = true := by
  decide
theorem tttFiber43Row_6_ok : tttFiber43RowCheck 6 = true := by
  decide
theorem tttFiber43Row_7_ok : tttFiber43RowCheck 7 = true := by
  decide
theorem tttFiber43Row_8_ok : tttFiber43RowCheck 8 = true := by
  decide
theorem tttFiber43Row_9_ok : tttFiber43RowCheck 9 = true := by
  decide
theorem tttFiber43Row_10_ok : tttFiber43RowCheck 10 = true := by
  decide
theorem tttFiber43Row_11_ok : tttFiber43RowCheck 11 = true := by
  decide
theorem tttFiber43Row_12_ok : tttFiber43RowCheck 12 = true := by
  decide
theorem tttFiber43Row_13_ok : tttFiber43RowCheck 13 = true := by
  decide
theorem tttFiber43Row_14_ok : tttFiber43RowCheck 14 = true := by
  decide
theorem tttFiber43Row_15_ok : tttFiber43RowCheck 15 = true := by
  decide

def tttFiber43ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber43Rows tttLightMaxParentDepth
    (listGetD tttFiber43Expected i 0) == 4896

theorem tttFiber43Parent_0_ok : tttFiber43ParentCheck 0 = true := by
  decide
theorem tttFiber43Parent_1_ok : tttFiber43ParentCheck 1 = true := by
  decide
theorem tttFiber43Parent_2_ok : tttFiber43ParentCheck 2 = true := by
  decide
theorem tttFiber43Parent_3_ok : tttFiber43ParentCheck 3 = true := by
  decide
theorem tttFiber43Parent_4_ok : tttFiber43ParentCheck 4 = true := by
  decide
theorem tttFiber43Parent_5_ok : tttFiber43ParentCheck 5 = true := by
  decide
theorem tttFiber43Parent_6_ok : tttFiber43ParentCheck 6 = true := by
  decide
theorem tttFiber43Parent_7_ok : tttFiber43ParentCheck 7 = true := by
  decide
theorem tttFiber43Parent_8_ok : tttFiber43ParentCheck 8 = true := by
  decide
theorem tttFiber43Parent_9_ok : tttFiber43ParentCheck 9 = true := by
  decide
theorem tttFiber43Parent_10_ok : tttFiber43ParentCheck 10 = true := by
  decide
theorem tttFiber43Parent_11_ok : tttFiber43ParentCheck 11 = true := by
  decide
theorem tttFiber43Parent_12_ok : tttFiber43ParentCheck 12 = true := by
  decide
theorem tttFiber43Parent_13_ok : tttFiber43ParentCheck 13 = true := by
  decide
theorem tttFiber43Parent_14_ok : tttFiber43ParentCheck 14 = true := by
  decide
theorem tttFiber43Parent_15_ok : tttFiber43ParentCheck 15 = true := by
  decide

def tttFiber43CertificateAudit : Bool :=
  tttFiber43SourcesCheck
    && tttFiber43RowCheck 0
    && tttFiber43RowCheck 1
    && tttFiber43RowCheck 2
    && tttFiber43RowCheck 3
    && tttFiber43RowCheck 4
    && tttFiber43RowCheck 5
    && tttFiber43RowCheck 6
    && tttFiber43RowCheck 7
    && tttFiber43RowCheck 8
    && tttFiber43RowCheck 9
    && tttFiber43RowCheck 10
    && tttFiber43RowCheck 11
    && tttFiber43RowCheck 12
    && tttFiber43RowCheck 13
    && tttFiber43RowCheck 14
    && tttFiber43RowCheck 15
    && tttFiber43ParentCheck 0
    && tttFiber43ParentCheck 1
    && tttFiber43ParentCheck 2
    && tttFiber43ParentCheck 3
    && tttFiber43ParentCheck 4
    && tttFiber43ParentCheck 5
    && tttFiber43ParentCheck 6
    && tttFiber43ParentCheck 7
    && tttFiber43ParentCheck 8
    && tttFiber43ParentCheck 9
    && tttFiber43ParentCheck 10
    && tttFiber43ParentCheck 11
    && tttFiber43ParentCheck 12
    && tttFiber43ParentCheck 13
    && tttFiber43ParentCheck 14
    && tttFiber43ParentCheck 15

theorem tttFiber43CertificateAudit_ok :
    tttFiber43CertificateAudit = true := by
  simp [tttFiber43CertificateAudit,
    tttFiber43SourcesCheck_ok,
    tttFiber43Row_0_ok,
    tttFiber43Row_1_ok,
    tttFiber43Row_2_ok,
    tttFiber43Row_3_ok,
    tttFiber43Row_4_ok,
    tttFiber43Row_5_ok,
    tttFiber43Row_6_ok,
    tttFiber43Row_7_ok,
    tttFiber43Row_8_ok,
    tttFiber43Row_9_ok,
    tttFiber43Row_10_ok,
    tttFiber43Row_11_ok,
    tttFiber43Row_12_ok,
    tttFiber43Row_13_ok,
    tttFiber43Row_14_ok,
    tttFiber43Row_15_ok,
    tttFiber43Parent_0_ok,
    tttFiber43Parent_1_ok,
    tttFiber43Parent_2_ok,
    tttFiber43Parent_3_ok,
    tttFiber43Parent_4_ok,
    tttFiber43Parent_5_ok,
    tttFiber43Parent_6_ok,
    tttFiber43Parent_7_ok,
    tttFiber43Parent_8_ok,
    tttFiber43Parent_9_ok,
    tttFiber43Parent_10_ok,
    tttFiber43Parent_11_ok,
    tttFiber43Parent_12_ok,
    tttFiber43Parent_13_ok,
    tttFiber43Parent_14_ok,
    tttFiber43Parent_15_ok]

def tttFiber45Key : List LColor :=
  [LColor.b, LColor.p, LColor.r, LColor.r]

def tttFiber45Expected : List Nat :=
  []

def tttFiber45Rows : List TripleComponentParentRow :=
  []

def tttFiber45SourcesCheck : Bool :=
  (tttFiber45Rows.map fun row => row.source) == tttFiber45Expected

theorem tttFiber45SourcesCheck_ok :
    tttFiber45SourcesCheck = true := by
  decide

def tttFiber45CertificateAudit : Bool :=
  tttFiber45SourcesCheck

theorem tttFiber45CertificateAudit_ok :
    tttFiber45CertificateAudit = true := by
  simp [tttFiber45CertificateAudit,
    tttFiber45SourcesCheck_ok]

def tttFiber46Key : List LColor :=
  [LColor.b, LColor.p, LColor.r, LColor.b]

def tttFiber46Expected : List Nat :=
  []

def tttFiber46Rows : List TripleComponentParentRow :=
  []

def tttFiber46SourcesCheck : Bool :=
  (tttFiber46Rows.map fun row => row.source) == tttFiber46Expected

theorem tttFiber46SourcesCheck_ok :
    tttFiber46SourcesCheck = true := by
  decide

def tttFiber46CertificateAudit : Bool :=
  tttFiber46SourcesCheck

theorem tttFiber46CertificateAudit_ok :
    tttFiber46CertificateAudit = true := by
  simp [tttFiber46CertificateAudit,
    tttFiber46SourcesCheck_ok]

def tttFiber47Key : List LColor :=
  [LColor.b, LColor.p, LColor.r, LColor.p]

def tttFiber47Expected : List Nat :=
  []

def tttFiber47Rows : List TripleComponentParentRow :=
  []

def tttFiber47SourcesCheck : Bool :=
  (tttFiber47Rows.map fun row => row.source) == tttFiber47Expected

theorem tttFiber47SourcesCheck_ok :
    tttFiber47SourcesCheck = true := by
  decide

def tttFiber47CertificateAudit : Bool :=
  tttFiber47SourcesCheck

theorem tttFiber47CertificateAudit_ok :
    tttFiber47CertificateAudit = true := by
  simp [tttFiber47CertificateAudit,
    tttFiber47SourcesCheck_ok]

def tttFiber48Key : List LColor :=
  [LColor.b, LColor.p, LColor.b, LColor.r]

def tttFiber48Expected : List Nat :=
  [5712, 5713, 5714, 5715, 5716, 5717, 5718, 5719,
   5720, 5721, 5722, 5723, 5724, 5725, 5726, 5727]

def tttFiber48Row0 : TripleComponentParentRow :=
  tripleRow 5712 5712 168 22 176 168 22 176
    default
    []

def tttFiber48Row1 : TripleComponentParentRow :=
  tripleRow 5713 5712 168 22 177 168 22 176
    (chainMove LColor.r LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber48Row2 : TripleComponentParentRow :=
  tripleRow 5714 5712 168 22 178 168 22 176
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber48Row3 : TripleComponentParentRow :=
  tripleRow 5715 5713 168 22 179 168 22 177
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber48Row4 : TripleComponentParentRow :=
  tripleRow 5716 5712 168 23 184 168 22 176
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber48Row5 : TripleComponentParentRow :=
  tripleRow 5717 5713 168 23 185 168 22 177
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber48Row6 : TripleComponentParentRow :=
  tripleRow 5718 5714 168 23 186 168 22 178
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber48Row7 : TripleComponentParentRow :=
  tripleRow 5719 5715 168 23 187 168 22 179
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber48Row8 : TripleComponentParentRow :=
  tripleRow 5720 5712 169 30 176 168 22 176
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber48Row9 : TripleComponentParentRow :=
  tripleRow 5721 5713 169 30 177 168 22 177
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber48Row10 : TripleComponentParentRow :=
  tripleRow 5722 5714 169 30 178 168 22 178
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber48Row11 : TripleComponentParentRow :=
  tripleRow 5723 5715 169 30 179 168 22 179
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber48Row12 : TripleComponentParentRow :=
  tripleRow 5724 5716 169 31 184 168 23 184
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber48Row13 : TripleComponentParentRow :=
  tripleRow 5725 5717 169 31 185 168 23 185
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber48Row14 : TripleComponentParentRow :=
  tripleRow 5726 5718 169 31 186 168 23 186
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber48Row15 : TripleComponentParentRow :=
  tripleRow 5727 5719 169 31 187 168 23 187
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber48Rows : List TripleComponentParentRow :=
  [ tttFiber48Row0
  , tttFiber48Row1
  , tttFiber48Row2
  , tttFiber48Row3
  , tttFiber48Row4
  , tttFiber48Row5
  , tttFiber48Row6
  , tttFiber48Row7
  , tttFiber48Row8
  , tttFiber48Row9
  , tttFiber48Row10
  , tttFiber48Row11
  , tttFiber48Row12
  , tttFiber48Row13
  , tttFiber48Row14
  , tttFiber48Row15
  ]

def tttFiber48SourcesCheck : Bool :=
  (tttFiber48Rows.map fun row => row.source) == tttFiber48Expected

theorem tttFiber48SourcesCheck_ok :
    tttFiber48SourcesCheck = true := by
  decide

def tttFiber48RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber48Key tttFiber48Expected
    (listGetD tttFiber48Rows i default)

theorem tttFiber48Row_0_ok : tttFiber48RowCheck 0 = true := by
  decide
theorem tttFiber48Row_1_ok : tttFiber48RowCheck 1 = true := by
  decide
theorem tttFiber48Row_2_ok : tttFiber48RowCheck 2 = true := by
  decide
theorem tttFiber48Row_3_ok : tttFiber48RowCheck 3 = true := by
  decide
theorem tttFiber48Row_4_ok : tttFiber48RowCheck 4 = true := by
  decide
theorem tttFiber48Row_5_ok : tttFiber48RowCheck 5 = true := by
  decide
theorem tttFiber48Row_6_ok : tttFiber48RowCheck 6 = true := by
  decide
theorem tttFiber48Row_7_ok : tttFiber48RowCheck 7 = true := by
  decide
theorem tttFiber48Row_8_ok : tttFiber48RowCheck 8 = true := by
  decide
theorem tttFiber48Row_9_ok : tttFiber48RowCheck 9 = true := by
  decide
theorem tttFiber48Row_10_ok : tttFiber48RowCheck 10 = true := by
  decide
theorem tttFiber48Row_11_ok : tttFiber48RowCheck 11 = true := by
  decide
theorem tttFiber48Row_12_ok : tttFiber48RowCheck 12 = true := by
  decide
theorem tttFiber48Row_13_ok : tttFiber48RowCheck 13 = true := by
  decide
theorem tttFiber48Row_14_ok : tttFiber48RowCheck 14 = true := by
  decide
theorem tttFiber48Row_15_ok : tttFiber48RowCheck 15 = true := by
  decide

def tttFiber48ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber48Rows tttLightMaxParentDepth
    (listGetD tttFiber48Expected i 0) == 5712

theorem tttFiber48Parent_0_ok : tttFiber48ParentCheck 0 = true := by
  decide
theorem tttFiber48Parent_1_ok : tttFiber48ParentCheck 1 = true := by
  decide
theorem tttFiber48Parent_2_ok : tttFiber48ParentCheck 2 = true := by
  decide
theorem tttFiber48Parent_3_ok : tttFiber48ParentCheck 3 = true := by
  decide
theorem tttFiber48Parent_4_ok : tttFiber48ParentCheck 4 = true := by
  decide
theorem tttFiber48Parent_5_ok : tttFiber48ParentCheck 5 = true := by
  decide
theorem tttFiber48Parent_6_ok : tttFiber48ParentCheck 6 = true := by
  decide
theorem tttFiber48Parent_7_ok : tttFiber48ParentCheck 7 = true := by
  decide
theorem tttFiber48Parent_8_ok : tttFiber48ParentCheck 8 = true := by
  decide
theorem tttFiber48Parent_9_ok : tttFiber48ParentCheck 9 = true := by
  decide
theorem tttFiber48Parent_10_ok : tttFiber48ParentCheck 10 = true := by
  decide
theorem tttFiber48Parent_11_ok : tttFiber48ParentCheck 11 = true := by
  decide
theorem tttFiber48Parent_12_ok : tttFiber48ParentCheck 12 = true := by
  decide
theorem tttFiber48Parent_13_ok : tttFiber48ParentCheck 13 = true := by
  decide
theorem tttFiber48Parent_14_ok : tttFiber48ParentCheck 14 = true := by
  decide
theorem tttFiber48Parent_15_ok : tttFiber48ParentCheck 15 = true := by
  decide

def tttFiber48CertificateAudit : Bool :=
  tttFiber48SourcesCheck
    && tttFiber48RowCheck 0
    && tttFiber48RowCheck 1
    && tttFiber48RowCheck 2
    && tttFiber48RowCheck 3
    && tttFiber48RowCheck 4
    && tttFiber48RowCheck 5
    && tttFiber48RowCheck 6
    && tttFiber48RowCheck 7
    && tttFiber48RowCheck 8
    && tttFiber48RowCheck 9
    && tttFiber48RowCheck 10
    && tttFiber48RowCheck 11
    && tttFiber48RowCheck 12
    && tttFiber48RowCheck 13
    && tttFiber48RowCheck 14
    && tttFiber48RowCheck 15
    && tttFiber48ParentCheck 0
    && tttFiber48ParentCheck 1
    && tttFiber48ParentCheck 2
    && tttFiber48ParentCheck 3
    && tttFiber48ParentCheck 4
    && tttFiber48ParentCheck 5
    && tttFiber48ParentCheck 6
    && tttFiber48ParentCheck 7
    && tttFiber48ParentCheck 8
    && tttFiber48ParentCheck 9
    && tttFiber48ParentCheck 10
    && tttFiber48ParentCheck 11
    && tttFiber48ParentCheck 12
    && tttFiber48ParentCheck 13
    && tttFiber48ParentCheck 14
    && tttFiber48ParentCheck 15

theorem tttFiber48CertificateAudit_ok :
    tttFiber48CertificateAudit = true := by
  simp [tttFiber48CertificateAudit,
    tttFiber48SourcesCheck_ok,
    tttFiber48Row_0_ok,
    tttFiber48Row_1_ok,
    tttFiber48Row_2_ok,
    tttFiber48Row_3_ok,
    tttFiber48Row_4_ok,
    tttFiber48Row_5_ok,
    tttFiber48Row_6_ok,
    tttFiber48Row_7_ok,
    tttFiber48Row_8_ok,
    tttFiber48Row_9_ok,
    tttFiber48Row_10_ok,
    tttFiber48Row_11_ok,
    tttFiber48Row_12_ok,
    tttFiber48Row_13_ok,
    tttFiber48Row_14_ok,
    tttFiber48Row_15_ok,
    tttFiber48Parent_0_ok,
    tttFiber48Parent_1_ok,
    tttFiber48Parent_2_ok,
    tttFiber48Parent_3_ok,
    tttFiber48Parent_4_ok,
    tttFiber48Parent_5_ok,
    tttFiber48Parent_6_ok,
    tttFiber48Parent_7_ok,
    tttFiber48Parent_8_ok,
    tttFiber48Parent_9_ok,
    tttFiber48Parent_10_ok,
    tttFiber48Parent_11_ok,
    tttFiber48Parent_12_ok,
    tttFiber48Parent_13_ok,
    tttFiber48Parent_14_ok,
    tttFiber48Parent_15_ok]

def tttFiber49Key : List LColor :=
  [LColor.b, LColor.p, LColor.b, LColor.b]

def tttFiber49Expected : List Nat :=
  [5168, 5169, 5170, 5171, 5172, 5173, 5174, 5175,
   5176, 5177, 5178, 5179, 5180, 5181, 5182, 5183]

def tttFiber49Row0 : TripleComponentParentRow :=
  tripleRow 5168 5168 152 84 144 152 84 144
    default
    []

def tttFiber49Row1 : TripleComponentParentRow :=
  tripleRow 5169 5168 152 84 145 152 84 144
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber49Row2 : TripleComponentParentRow :=
  tripleRow 5170 5169 152 84 146 152 84 145
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber49Row3 : TripleComponentParentRow :=
  tripleRow 5171 5168 152 84 147 152 84 144
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber49Row4 : TripleComponentParentRow :=
  tripleRow 5172 5168 152 85 152 152 84 144
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber49Row5 : TripleComponentParentRow :=
  tripleRow 5173 5169 152 85 153 152 84 145
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber49Row6 : TripleComponentParentRow :=
  tripleRow 5174 5170 152 85 154 152 84 146
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber49Row7 : TripleComponentParentRow :=
  tripleRow 5175 5171 152 85 155 152 84 147
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber49Row8 : TripleComponentParentRow :=
  tripleRow 5176 5168 153 92 144 152 84 144
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber49Row9 : TripleComponentParentRow :=
  tripleRow 5177 5169 153 92 145 152 84 145
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber49Row10 : TripleComponentParentRow :=
  tripleRow 5178 5170 153 92 146 152 84 146
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber49Row11 : TripleComponentParentRow :=
  tripleRow 5179 5171 153 92 147 152 84 147
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber49Row12 : TripleComponentParentRow :=
  tripleRow 5180 5172 153 93 152 152 85 152
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber49Row13 : TripleComponentParentRow :=
  tripleRow 5181 5173 153 93 153 152 85 153
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber49Row14 : TripleComponentParentRow :=
  tripleRow 5182 5174 153 93 154 152 85 154
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber49Row15 : TripleComponentParentRow :=
  tripleRow 5183 5175 153 93 155 152 85 155
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber49Rows : List TripleComponentParentRow :=
  [ tttFiber49Row0
  , tttFiber49Row1
  , tttFiber49Row2
  , tttFiber49Row3
  , tttFiber49Row4
  , tttFiber49Row5
  , tttFiber49Row6
  , tttFiber49Row7
  , tttFiber49Row8
  , tttFiber49Row9
  , tttFiber49Row10
  , tttFiber49Row11
  , tttFiber49Row12
  , tttFiber49Row13
  , tttFiber49Row14
  , tttFiber49Row15
  ]

def tttFiber49SourcesCheck : Bool :=
  (tttFiber49Rows.map fun row => row.source) == tttFiber49Expected

theorem tttFiber49SourcesCheck_ok :
    tttFiber49SourcesCheck = true := by
  decide

def tttFiber49RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber49Key tttFiber49Expected
    (listGetD tttFiber49Rows i default)

theorem tttFiber49Row_0_ok : tttFiber49RowCheck 0 = true := by
  decide
theorem tttFiber49Row_1_ok : tttFiber49RowCheck 1 = true := by
  decide
theorem tttFiber49Row_2_ok : tttFiber49RowCheck 2 = true := by
  decide
theorem tttFiber49Row_3_ok : tttFiber49RowCheck 3 = true := by
  decide
theorem tttFiber49Row_4_ok : tttFiber49RowCheck 4 = true := by
  decide
theorem tttFiber49Row_5_ok : tttFiber49RowCheck 5 = true := by
  decide
theorem tttFiber49Row_6_ok : tttFiber49RowCheck 6 = true := by
  decide
theorem tttFiber49Row_7_ok : tttFiber49RowCheck 7 = true := by
  decide
theorem tttFiber49Row_8_ok : tttFiber49RowCheck 8 = true := by
  decide
theorem tttFiber49Row_9_ok : tttFiber49RowCheck 9 = true := by
  decide
theorem tttFiber49Row_10_ok : tttFiber49RowCheck 10 = true := by
  decide
theorem tttFiber49Row_11_ok : tttFiber49RowCheck 11 = true := by
  decide
theorem tttFiber49Row_12_ok : tttFiber49RowCheck 12 = true := by
  decide
theorem tttFiber49Row_13_ok : tttFiber49RowCheck 13 = true := by
  decide
theorem tttFiber49Row_14_ok : tttFiber49RowCheck 14 = true := by
  decide
theorem tttFiber49Row_15_ok : tttFiber49RowCheck 15 = true := by
  decide

def tttFiber49ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber49Rows tttLightMaxParentDepth
    (listGetD tttFiber49Expected i 0) == 5168

theorem tttFiber49Parent_0_ok : tttFiber49ParentCheck 0 = true := by
  decide
theorem tttFiber49Parent_1_ok : tttFiber49ParentCheck 1 = true := by
  decide
theorem tttFiber49Parent_2_ok : tttFiber49ParentCheck 2 = true := by
  decide
theorem tttFiber49Parent_3_ok : tttFiber49ParentCheck 3 = true := by
  decide
theorem tttFiber49Parent_4_ok : tttFiber49ParentCheck 4 = true := by
  decide
theorem tttFiber49Parent_5_ok : tttFiber49ParentCheck 5 = true := by
  decide
theorem tttFiber49Parent_6_ok : tttFiber49ParentCheck 6 = true := by
  decide
theorem tttFiber49Parent_7_ok : tttFiber49ParentCheck 7 = true := by
  decide
theorem tttFiber49Parent_8_ok : tttFiber49ParentCheck 8 = true := by
  decide
theorem tttFiber49Parent_9_ok : tttFiber49ParentCheck 9 = true := by
  decide
theorem tttFiber49Parent_10_ok : tttFiber49ParentCheck 10 = true := by
  decide
theorem tttFiber49Parent_11_ok : tttFiber49ParentCheck 11 = true := by
  decide
theorem tttFiber49Parent_12_ok : tttFiber49ParentCheck 12 = true := by
  decide
theorem tttFiber49Parent_13_ok : tttFiber49ParentCheck 13 = true := by
  decide
theorem tttFiber49Parent_14_ok : tttFiber49ParentCheck 14 = true := by
  decide
theorem tttFiber49Parent_15_ok : tttFiber49ParentCheck 15 = true := by
  decide

def tttFiber49CertificateAudit : Bool :=
  tttFiber49SourcesCheck
    && tttFiber49RowCheck 0
    && tttFiber49RowCheck 1
    && tttFiber49RowCheck 2
    && tttFiber49RowCheck 3
    && tttFiber49RowCheck 4
    && tttFiber49RowCheck 5
    && tttFiber49RowCheck 6
    && tttFiber49RowCheck 7
    && tttFiber49RowCheck 8
    && tttFiber49RowCheck 9
    && tttFiber49RowCheck 10
    && tttFiber49RowCheck 11
    && tttFiber49RowCheck 12
    && tttFiber49RowCheck 13
    && tttFiber49RowCheck 14
    && tttFiber49RowCheck 15
    && tttFiber49ParentCheck 0
    && tttFiber49ParentCheck 1
    && tttFiber49ParentCheck 2
    && tttFiber49ParentCheck 3
    && tttFiber49ParentCheck 4
    && tttFiber49ParentCheck 5
    && tttFiber49ParentCheck 6
    && tttFiber49ParentCheck 7
    && tttFiber49ParentCheck 8
    && tttFiber49ParentCheck 9
    && tttFiber49ParentCheck 10
    && tttFiber49ParentCheck 11
    && tttFiber49ParentCheck 12
    && tttFiber49ParentCheck 13
    && tttFiber49ParentCheck 14
    && tttFiber49ParentCheck 15

theorem tttFiber49CertificateAudit_ok :
    tttFiber49CertificateAudit = true := by
  simp [tttFiber49CertificateAudit,
    tttFiber49SourcesCheck_ok,
    tttFiber49Row_0_ok,
    tttFiber49Row_1_ok,
    tttFiber49Row_2_ok,
    tttFiber49Row_3_ok,
    tttFiber49Row_4_ok,
    tttFiber49Row_5_ok,
    tttFiber49Row_6_ok,
    tttFiber49Row_7_ok,
    tttFiber49Row_8_ok,
    tttFiber49Row_9_ok,
    tttFiber49Row_10_ok,
    tttFiber49Row_11_ok,
    tttFiber49Row_12_ok,
    tttFiber49Row_13_ok,
    tttFiber49Row_14_ok,
    tttFiber49Row_15_ok,
    tttFiber49Parent_0_ok,
    tttFiber49Parent_1_ok,
    tttFiber49Parent_2_ok,
    tttFiber49Parent_3_ok,
    tttFiber49Parent_4_ok,
    tttFiber49Parent_5_ok,
    tttFiber49Parent_6_ok,
    tttFiber49Parent_7_ok,
    tttFiber49Parent_8_ok,
    tttFiber49Parent_9_ok,
    tttFiber49Parent_10_ok,
    tttFiber49Parent_11_ok,
    tttFiber49Parent_12_ok,
    tttFiber49Parent_13_ok,
    tttFiber49Parent_14_ok,
    tttFiber49Parent_15_ok]

def tttFiber51Key : List LColor :=
  [LColor.b, LColor.p, LColor.p, LColor.r]

def tttFiber51Expected : List Nat :=
  []

def tttFiber51Rows : List TripleComponentParentRow :=
  []

def tttFiber51SourcesCheck : Bool :=
  (tttFiber51Rows.map fun row => row.source) == tttFiber51Expected

theorem tttFiber51SourcesCheck_ok :
    tttFiber51SourcesCheck = true := by
  decide

def tttFiber51CertificateAudit : Bool :=
  tttFiber51SourcesCheck

theorem tttFiber51CertificateAudit_ok :
    tttFiber51CertificateAudit = true := by
  simp [tttFiber51CertificateAudit,
    tttFiber51SourcesCheck_ok]

def tttFiber52Key : List LColor :=
  [LColor.b, LColor.p, LColor.p, LColor.b]

def tttFiber52Expected : List Nat :=
  []

def tttFiber52Rows : List TripleComponentParentRow :=
  []

def tttFiber52SourcesCheck : Bool :=
  (tttFiber52Rows.map fun row => row.source) == tttFiber52Expected

theorem tttFiber52SourcesCheck_ok :
    tttFiber52SourcesCheck = true := by
  decide

def tttFiber52CertificateAudit : Bool :=
  tttFiber52SourcesCheck

theorem tttFiber52CertificateAudit_ok :
    tttFiber52CertificateAudit = true := by
  simp [tttFiber52CertificateAudit,
    tttFiber52SourcesCheck_ok]

def tttFiber53Key : List LColor :=
  [LColor.b, LColor.p, LColor.p, LColor.p]

def tttFiber53Expected : List Nat :=
  []

def tttFiber53Rows : List TripleComponentParentRow :=
  []

def tttFiber53SourcesCheck : Bool :=
  (tttFiber53Rows.map fun row => row.source) == tttFiber53Expected

theorem tttFiber53SourcesCheck_ok :
    tttFiber53SourcesCheck = true := by
  decide

def tttFiber53CertificateAudit : Bool :=
  tttFiber53SourcesCheck

theorem tttFiber53CertificateAudit_ok :
    tttFiber53CertificateAudit = true := by
  simp [tttFiber53CertificateAudit,
    tttFiber53SourcesCheck_ok]

def tttFiber54Key : List LColor :=
  [LColor.p, LColor.r, LColor.r, LColor.r]

def tttFiber54Expected : List Nat :=
  []

def tttFiber54Rows : List TripleComponentParentRow :=
  []

def tttFiber54SourcesCheck : Bool :=
  (tttFiber54Rows.map fun row => row.source) == tttFiber54Expected

theorem tttFiber54SourcesCheck_ok :
    tttFiber54SourcesCheck = true := by
  decide

def tttFiber54CertificateAudit : Bool :=
  tttFiber54SourcesCheck

theorem tttFiber54CertificateAudit_ok :
    tttFiber54CertificateAudit = true := by
  simp [tttFiber54CertificateAudit,
    tttFiber54SourcesCheck_ok]

def tttFiber55Key : List LColor :=
  [LColor.p, LColor.r, LColor.r, LColor.b]

def tttFiber55Expected : List Nat :=
  []

def tttFiber55Rows : List TripleComponentParentRow :=
  []

def tttFiber55SourcesCheck : Bool :=
  (tttFiber55Rows.map fun row => row.source) == tttFiber55Expected

theorem tttFiber55SourcesCheck_ok :
    tttFiber55SourcesCheck = true := by
  decide

def tttFiber55CertificateAudit : Bool :=
  tttFiber55SourcesCheck

theorem tttFiber55CertificateAudit_ok :
    tttFiber55CertificateAudit = true := by
  simp [tttFiber55CertificateAudit,
    tttFiber55SourcesCheck_ok]

def tttFiber56Key : List LColor :=
  [LColor.p, LColor.r, LColor.r, LColor.p]

def tttFiber56Expected : List Nat :=
  []

def tttFiber56Rows : List TripleComponentParentRow :=
  []

def tttFiber56SourcesCheck : Bool :=
  (tttFiber56Rows.map fun row => row.source) == tttFiber56Expected

theorem tttFiber56SourcesCheck_ok :
    tttFiber56SourcesCheck = true := by
  decide

def tttFiber56CertificateAudit : Bool :=
  tttFiber56SourcesCheck

theorem tttFiber56CertificateAudit_ok :
    tttFiber56CertificateAudit = true := by
  simp [tttFiber56CertificateAudit,
    tttFiber56SourcesCheck_ok]

def tttFiber57Key : List LColor :=
  [LColor.p, LColor.r, LColor.b, LColor.r]

def tttFiber57Expected : List Nat :=
  []

def tttFiber57Rows : List TripleComponentParentRow :=
  []

def tttFiber57SourcesCheck : Bool :=
  (tttFiber57Rows.map fun row => row.source) == tttFiber57Expected

theorem tttFiber57SourcesCheck_ok :
    tttFiber57SourcesCheck = true := by
  decide

def tttFiber57CertificateAudit : Bool :=
  tttFiber57SourcesCheck

theorem tttFiber57CertificateAudit_ok :
    tttFiber57CertificateAudit = true := by
  simp [tttFiber57CertificateAudit,
    tttFiber57SourcesCheck_ok]

def tttFiber58Key : List LColor :=
  [LColor.p, LColor.r, LColor.b, LColor.b]

def tttFiber58Expected : List Nat :=
  []

def tttFiber58Rows : List TripleComponentParentRow :=
  []

def tttFiber58SourcesCheck : Bool :=
  (tttFiber58Rows.map fun row => row.source) == tttFiber58Expected

theorem tttFiber58SourcesCheck_ok :
    tttFiber58SourcesCheck = true := by
  decide

def tttFiber58CertificateAudit : Bool :=
  tttFiber58SourcesCheck

theorem tttFiber58CertificateAudit_ok :
    tttFiber58CertificateAudit = true := by
  simp [tttFiber58CertificateAudit,
    tttFiber58SourcesCheck_ok]

def tttFiber59Key : List LColor :=
  [LColor.p, LColor.r, LColor.b, LColor.p]

def tttFiber59Expected : List Nat :=
  []

def tttFiber59Rows : List TripleComponentParentRow :=
  []

def tttFiber59SourcesCheck : Bool :=
  (tttFiber59Rows.map fun row => row.source) == tttFiber59Expected

theorem tttFiber59SourcesCheck_ok :
    tttFiber59SourcesCheck = true := by
  decide

def tttFiber59CertificateAudit : Bool :=
  tttFiber59SourcesCheck

theorem tttFiber59CertificateAudit_ok :
    tttFiber59CertificateAudit = true := by
  simp [tttFiber59CertificateAudit,
    tttFiber59SourcesCheck_ok]

def tttFiber61Key : List LColor :=
  [LColor.p, LColor.r, LColor.p, LColor.b]

def tttFiber61Expected : List Nat :=
  [1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351,
   1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359]

def tttFiber61Row0 : TripleComponentParentRow :=
  tripleRow 1344 1344 38 114 52 38 114 52
    default
    []

def tttFiber61Row1 : TripleComponentParentRow :=
  tripleRow 1345 1344 38 114 53 38 114 52
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber61Row2 : TripleComponentParentRow :=
  tripleRow 1346 1345 38 114 54 38 114 53
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber61Row3 : TripleComponentParentRow :=
  tripleRow 1347 1344 38 114 55 38 114 52
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber61Row4 : TripleComponentParentRow :=
  tripleRow 1348 1344 38 115 60 38 114 52
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber61Row5 : TripleComponentParentRow :=
  tripleRow 1349 1345 38 115 61 38 114 53
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber61Row6 : TripleComponentParentRow :=
  tripleRow 1350 1346 38 115 62 38 114 54
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber61Row7 : TripleComponentParentRow :=
  tripleRow 1351 1347 38 115 63 38 114 55
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber61Row8 : TripleComponentParentRow :=
  tripleRow 1352 1344 39 122 52 38 114 52
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber61Row9 : TripleComponentParentRow :=
  tripleRow 1353 1345 39 122 53 38 114 53
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber61Row10 : TripleComponentParentRow :=
  tripleRow 1354 1346 39 122 54 38 114 54
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber61Row11 : TripleComponentParentRow :=
  tripleRow 1355 1347 39 122 55 38 114 55
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber61Row12 : TripleComponentParentRow :=
  tripleRow 1356 1348 39 123 60 38 115 60
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber61Row13 : TripleComponentParentRow :=
  tripleRow 1357 1349 39 123 61 38 115 61
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber61Row14 : TripleComponentParentRow :=
  tripleRow 1358 1350 39 123 62 38 115 62
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber61Row15 : TripleComponentParentRow :=
  tripleRow 1359 1351 39 123 63 38 115 63
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber61Rows : List TripleComponentParentRow :=
  [ tttFiber61Row0
  , tttFiber61Row1
  , tttFiber61Row2
  , tttFiber61Row3
  , tttFiber61Row4
  , tttFiber61Row5
  , tttFiber61Row6
  , tttFiber61Row7
  , tttFiber61Row8
  , tttFiber61Row9
  , tttFiber61Row10
  , tttFiber61Row11
  , tttFiber61Row12
  , tttFiber61Row13
  , tttFiber61Row14
  , tttFiber61Row15
  ]

def tttFiber61SourcesCheck : Bool :=
  (tttFiber61Rows.map fun row => row.source) == tttFiber61Expected

theorem tttFiber61SourcesCheck_ok :
    tttFiber61SourcesCheck = true := by
  decide

def tttFiber61RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber61Key tttFiber61Expected
    (listGetD tttFiber61Rows i default)

theorem tttFiber61Row_0_ok : tttFiber61RowCheck 0 = true := by
  decide
theorem tttFiber61Row_1_ok : tttFiber61RowCheck 1 = true := by
  decide
theorem tttFiber61Row_2_ok : tttFiber61RowCheck 2 = true := by
  decide
theorem tttFiber61Row_3_ok : tttFiber61RowCheck 3 = true := by
  decide
theorem tttFiber61Row_4_ok : tttFiber61RowCheck 4 = true := by
  decide
theorem tttFiber61Row_5_ok : tttFiber61RowCheck 5 = true := by
  decide
theorem tttFiber61Row_6_ok : tttFiber61RowCheck 6 = true := by
  decide
theorem tttFiber61Row_7_ok : tttFiber61RowCheck 7 = true := by
  decide
theorem tttFiber61Row_8_ok : tttFiber61RowCheck 8 = true := by
  decide
theorem tttFiber61Row_9_ok : tttFiber61RowCheck 9 = true := by
  decide
theorem tttFiber61Row_10_ok : tttFiber61RowCheck 10 = true := by
  decide
theorem tttFiber61Row_11_ok : tttFiber61RowCheck 11 = true := by
  decide
theorem tttFiber61Row_12_ok : tttFiber61RowCheck 12 = true := by
  decide
theorem tttFiber61Row_13_ok : tttFiber61RowCheck 13 = true := by
  decide
theorem tttFiber61Row_14_ok : tttFiber61RowCheck 14 = true := by
  decide
theorem tttFiber61Row_15_ok : tttFiber61RowCheck 15 = true := by
  decide

def tttFiber61ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber61Rows tttLightMaxParentDepth
    (listGetD tttFiber61Expected i 0) == 1344

theorem tttFiber61Parent_0_ok : tttFiber61ParentCheck 0 = true := by
  decide
theorem tttFiber61Parent_1_ok : tttFiber61ParentCheck 1 = true := by
  decide
theorem tttFiber61Parent_2_ok : tttFiber61ParentCheck 2 = true := by
  decide
theorem tttFiber61Parent_3_ok : tttFiber61ParentCheck 3 = true := by
  decide
theorem tttFiber61Parent_4_ok : tttFiber61ParentCheck 4 = true := by
  decide
theorem tttFiber61Parent_5_ok : tttFiber61ParentCheck 5 = true := by
  decide
theorem tttFiber61Parent_6_ok : tttFiber61ParentCheck 6 = true := by
  decide
theorem tttFiber61Parent_7_ok : tttFiber61ParentCheck 7 = true := by
  decide
theorem tttFiber61Parent_8_ok : tttFiber61ParentCheck 8 = true := by
  decide
theorem tttFiber61Parent_9_ok : tttFiber61ParentCheck 9 = true := by
  decide
theorem tttFiber61Parent_10_ok : tttFiber61ParentCheck 10 = true := by
  decide
theorem tttFiber61Parent_11_ok : tttFiber61ParentCheck 11 = true := by
  decide
theorem tttFiber61Parent_12_ok : tttFiber61ParentCheck 12 = true := by
  decide
theorem tttFiber61Parent_13_ok : tttFiber61ParentCheck 13 = true := by
  decide
theorem tttFiber61Parent_14_ok : tttFiber61ParentCheck 14 = true := by
  decide
theorem tttFiber61Parent_15_ok : tttFiber61ParentCheck 15 = true := by
  decide

def tttFiber61CertificateAudit : Bool :=
  tttFiber61SourcesCheck
    && tttFiber61RowCheck 0
    && tttFiber61RowCheck 1
    && tttFiber61RowCheck 2
    && tttFiber61RowCheck 3
    && tttFiber61RowCheck 4
    && tttFiber61RowCheck 5
    && tttFiber61RowCheck 6
    && tttFiber61RowCheck 7
    && tttFiber61RowCheck 8
    && tttFiber61RowCheck 9
    && tttFiber61RowCheck 10
    && tttFiber61RowCheck 11
    && tttFiber61RowCheck 12
    && tttFiber61RowCheck 13
    && tttFiber61RowCheck 14
    && tttFiber61RowCheck 15
    && tttFiber61ParentCheck 0
    && tttFiber61ParentCheck 1
    && tttFiber61ParentCheck 2
    && tttFiber61ParentCheck 3
    && tttFiber61ParentCheck 4
    && tttFiber61ParentCheck 5
    && tttFiber61ParentCheck 6
    && tttFiber61ParentCheck 7
    && tttFiber61ParentCheck 8
    && tttFiber61ParentCheck 9
    && tttFiber61ParentCheck 10
    && tttFiber61ParentCheck 11
    && tttFiber61ParentCheck 12
    && tttFiber61ParentCheck 13
    && tttFiber61ParentCheck 14
    && tttFiber61ParentCheck 15

theorem tttFiber61CertificateAudit_ok :
    tttFiber61CertificateAudit = true := by
  simp [tttFiber61CertificateAudit,
    tttFiber61SourcesCheck_ok,
    tttFiber61Row_0_ok,
    tttFiber61Row_1_ok,
    tttFiber61Row_2_ok,
    tttFiber61Row_3_ok,
    tttFiber61Row_4_ok,
    tttFiber61Row_5_ok,
    tttFiber61Row_6_ok,
    tttFiber61Row_7_ok,
    tttFiber61Row_8_ok,
    tttFiber61Row_9_ok,
    tttFiber61Row_10_ok,
    tttFiber61Row_11_ok,
    tttFiber61Row_12_ok,
    tttFiber61Row_13_ok,
    tttFiber61Row_14_ok,
    tttFiber61Row_15_ok,
    tttFiber61Parent_0_ok,
    tttFiber61Parent_1_ok,
    tttFiber61Parent_2_ok,
    tttFiber61Parent_3_ok,
    tttFiber61Parent_4_ok,
    tttFiber61Parent_5_ok,
    tttFiber61Parent_6_ok,
    tttFiber61Parent_7_ok,
    tttFiber61Parent_8_ok,
    tttFiber61Parent_9_ok,
    tttFiber61Parent_10_ok,
    tttFiber61Parent_11_ok,
    tttFiber61Parent_12_ok,
    tttFiber61Parent_13_ok,
    tttFiber61Parent_14_ok,
    tttFiber61Parent_15_ok]

def tttFiber62Key : List LColor :=
  [LColor.p, LColor.r, LColor.p, LColor.p]

def tttFiber62Expected : List Nat :=
  [800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815]

def tttFiber62Row0 : TripleComponentParentRow :=
  tripleRow 800 800 22 176 20 22 176 20
    default
    []

def tttFiber62Row1 : TripleComponentParentRow :=
  tripleRow 801 800 22 176 21 22 176 20
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber62Row2 : TripleComponentParentRow :=
  tripleRow 802 800 22 176 22 22 176 20
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber62Row3 : TripleComponentParentRow :=
  tripleRow 803 801 22 176 23 22 176 21
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber62Row4 : TripleComponentParentRow :=
  tripleRow 804 800 22 177 28 22 176 20
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber62Row5 : TripleComponentParentRow :=
  tripleRow 805 801 22 177 29 22 176 21
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber62Row6 : TripleComponentParentRow :=
  tripleRow 806 802 22 177 30 22 176 22
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber62Row7 : TripleComponentParentRow :=
  tripleRow 807 803 22 177 31 22 176 23
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber62Row8 : TripleComponentParentRow :=
  tripleRow 808 800 23 184 20 22 176 20
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber62Row9 : TripleComponentParentRow :=
  tripleRow 809 801 23 184 21 22 176 21
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber62Row10 : TripleComponentParentRow :=
  tripleRow 810 802 23 184 22 22 176 22
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber62Row11 : TripleComponentParentRow :=
  tripleRow 811 803 23 184 23 22 176 23
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber62Row12 : TripleComponentParentRow :=
  tripleRow 812 804 23 185 28 22 177 28
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber62Row13 : TripleComponentParentRow :=
  tripleRow 813 805 23 185 29 22 177 29
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber62Row14 : TripleComponentParentRow :=
  tripleRow 814 806 23 185 30 22 177 30
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber62Row15 : TripleComponentParentRow :=
  tripleRow 815 807 23 185 31 22 177 31
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber62Rows : List TripleComponentParentRow :=
  [ tttFiber62Row0
  , tttFiber62Row1
  , tttFiber62Row2
  , tttFiber62Row3
  , tttFiber62Row4
  , tttFiber62Row5
  , tttFiber62Row6
  , tttFiber62Row7
  , tttFiber62Row8
  , tttFiber62Row9
  , tttFiber62Row10
  , tttFiber62Row11
  , tttFiber62Row12
  , tttFiber62Row13
  , tttFiber62Row14
  , tttFiber62Row15
  ]

def tttFiber62SourcesCheck : Bool :=
  (tttFiber62Rows.map fun row => row.source) == tttFiber62Expected

theorem tttFiber62SourcesCheck_ok :
    tttFiber62SourcesCheck = true := by
  decide

def tttFiber62RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber62Key tttFiber62Expected
    (listGetD tttFiber62Rows i default)

theorem tttFiber62Row_0_ok : tttFiber62RowCheck 0 = true := by
  decide
theorem tttFiber62Row_1_ok : tttFiber62RowCheck 1 = true := by
  decide
theorem tttFiber62Row_2_ok : tttFiber62RowCheck 2 = true := by
  decide
theorem tttFiber62Row_3_ok : tttFiber62RowCheck 3 = true := by
  decide
theorem tttFiber62Row_4_ok : tttFiber62RowCheck 4 = true := by
  decide
theorem tttFiber62Row_5_ok : tttFiber62RowCheck 5 = true := by
  decide
theorem tttFiber62Row_6_ok : tttFiber62RowCheck 6 = true := by
  decide
theorem tttFiber62Row_7_ok : tttFiber62RowCheck 7 = true := by
  decide
theorem tttFiber62Row_8_ok : tttFiber62RowCheck 8 = true := by
  decide
theorem tttFiber62Row_9_ok : tttFiber62RowCheck 9 = true := by
  decide
theorem tttFiber62Row_10_ok : tttFiber62RowCheck 10 = true := by
  decide
theorem tttFiber62Row_11_ok : tttFiber62RowCheck 11 = true := by
  decide
theorem tttFiber62Row_12_ok : tttFiber62RowCheck 12 = true := by
  decide
theorem tttFiber62Row_13_ok : tttFiber62RowCheck 13 = true := by
  decide
theorem tttFiber62Row_14_ok : tttFiber62RowCheck 14 = true := by
  decide
theorem tttFiber62Row_15_ok : tttFiber62RowCheck 15 = true := by
  decide

def tttFiber62ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber62Rows tttLightMaxParentDepth
    (listGetD tttFiber62Expected i 0) == 800

theorem tttFiber62Parent_0_ok : tttFiber62ParentCheck 0 = true := by
  decide
theorem tttFiber62Parent_1_ok : tttFiber62ParentCheck 1 = true := by
  decide
theorem tttFiber62Parent_2_ok : tttFiber62ParentCheck 2 = true := by
  decide
theorem tttFiber62Parent_3_ok : tttFiber62ParentCheck 3 = true := by
  decide
theorem tttFiber62Parent_4_ok : tttFiber62ParentCheck 4 = true := by
  decide
theorem tttFiber62Parent_5_ok : tttFiber62ParentCheck 5 = true := by
  decide
theorem tttFiber62Parent_6_ok : tttFiber62ParentCheck 6 = true := by
  decide
theorem tttFiber62Parent_7_ok : tttFiber62ParentCheck 7 = true := by
  decide
theorem tttFiber62Parent_8_ok : tttFiber62ParentCheck 8 = true := by
  decide
theorem tttFiber62Parent_9_ok : tttFiber62ParentCheck 9 = true := by
  decide
theorem tttFiber62Parent_10_ok : tttFiber62ParentCheck 10 = true := by
  decide
theorem tttFiber62Parent_11_ok : tttFiber62ParentCheck 11 = true := by
  decide
theorem tttFiber62Parent_12_ok : tttFiber62ParentCheck 12 = true := by
  decide
theorem tttFiber62Parent_13_ok : tttFiber62ParentCheck 13 = true := by
  decide
theorem tttFiber62Parent_14_ok : tttFiber62ParentCheck 14 = true := by
  decide
theorem tttFiber62Parent_15_ok : tttFiber62ParentCheck 15 = true := by
  decide

def tttFiber62CertificateAudit : Bool :=
  tttFiber62SourcesCheck
    && tttFiber62RowCheck 0
    && tttFiber62RowCheck 1
    && tttFiber62RowCheck 2
    && tttFiber62RowCheck 3
    && tttFiber62RowCheck 4
    && tttFiber62RowCheck 5
    && tttFiber62RowCheck 6
    && tttFiber62RowCheck 7
    && tttFiber62RowCheck 8
    && tttFiber62RowCheck 9
    && tttFiber62RowCheck 10
    && tttFiber62RowCheck 11
    && tttFiber62RowCheck 12
    && tttFiber62RowCheck 13
    && tttFiber62RowCheck 14
    && tttFiber62RowCheck 15
    && tttFiber62ParentCheck 0
    && tttFiber62ParentCheck 1
    && tttFiber62ParentCheck 2
    && tttFiber62ParentCheck 3
    && tttFiber62ParentCheck 4
    && tttFiber62ParentCheck 5
    && tttFiber62ParentCheck 6
    && tttFiber62ParentCheck 7
    && tttFiber62ParentCheck 8
    && tttFiber62ParentCheck 9
    && tttFiber62ParentCheck 10
    && tttFiber62ParentCheck 11
    && tttFiber62ParentCheck 12
    && tttFiber62ParentCheck 13
    && tttFiber62ParentCheck 14
    && tttFiber62ParentCheck 15

theorem tttFiber62CertificateAudit_ok :
    tttFiber62CertificateAudit = true := by
  simp [tttFiber62CertificateAudit,
    tttFiber62SourcesCheck_ok,
    tttFiber62Row_0_ok,
    tttFiber62Row_1_ok,
    tttFiber62Row_2_ok,
    tttFiber62Row_3_ok,
    tttFiber62Row_4_ok,
    tttFiber62Row_5_ok,
    tttFiber62Row_6_ok,
    tttFiber62Row_7_ok,
    tttFiber62Row_8_ok,
    tttFiber62Row_9_ok,
    tttFiber62Row_10_ok,
    tttFiber62Row_11_ok,
    tttFiber62Row_12_ok,
    tttFiber62Row_13_ok,
    tttFiber62Row_14_ok,
    tttFiber62Row_15_ok,
    tttFiber62Parent_0_ok,
    tttFiber62Parent_1_ok,
    tttFiber62Parent_2_ok,
    tttFiber62Parent_3_ok,
    tttFiber62Parent_4_ok,
    tttFiber62Parent_5_ok,
    tttFiber62Parent_6_ok,
    tttFiber62Parent_7_ok,
    tttFiber62Parent_8_ok,
    tttFiber62Parent_9_ok,
    tttFiber62Parent_10_ok,
    tttFiber62Parent_11_ok,
    tttFiber62Parent_12_ok,
    tttFiber62Parent_13_ok,
    tttFiber62Parent_14_ok,
    tttFiber62Parent_15_ok]

def tttFiber63Key : List LColor :=
  [LColor.p, LColor.b, LColor.r, LColor.r]

def tttFiber63Expected : List Nat :=
  []

def tttFiber63Rows : List TripleComponentParentRow :=
  []

def tttFiber63SourcesCheck : Bool :=
  (tttFiber63Rows.map fun row => row.source) == tttFiber63Expected

theorem tttFiber63SourcesCheck_ok :
    tttFiber63SourcesCheck = true := by
  decide

def tttFiber63CertificateAudit : Bool :=
  tttFiber63SourcesCheck

theorem tttFiber63CertificateAudit_ok :
    tttFiber63CertificateAudit = true := by
  simp [tttFiber63CertificateAudit,
    tttFiber63SourcesCheck_ok]

def tttFiber64Key : List LColor :=
  [LColor.p, LColor.b, LColor.r, LColor.b]

def tttFiber64Expected : List Nat :=
  []

def tttFiber64Rows : List TripleComponentParentRow :=
  []

def tttFiber64SourcesCheck : Bool :=
  (tttFiber64Rows.map fun row => row.source) == tttFiber64Expected

theorem tttFiber64SourcesCheck_ok :
    tttFiber64SourcesCheck = true := by
  decide

def tttFiber64CertificateAudit : Bool :=
  tttFiber64SourcesCheck

theorem tttFiber64CertificateAudit_ok :
    tttFiber64CertificateAudit = true := by
  simp [tttFiber64CertificateAudit,
    tttFiber64SourcesCheck_ok]

def tttFiber65Key : List LColor :=
  [LColor.p, LColor.b, LColor.r, LColor.p]

def tttFiber65Expected : List Nat :=
  []

def tttFiber65Rows : List TripleComponentParentRow :=
  []

def tttFiber65SourcesCheck : Bool :=
  (tttFiber65Rows.map fun row => row.source) == tttFiber65Expected

theorem tttFiber65SourcesCheck_ok :
    tttFiber65SourcesCheck = true := by
  decide

def tttFiber65CertificateAudit : Bool :=
  tttFiber65SourcesCheck

theorem tttFiber65CertificateAudit_ok :
    tttFiber65CertificateAudit = true := by
  simp [tttFiber65CertificateAudit,
    tttFiber65SourcesCheck_ok]

def tttFiber66Key : List LColor :=
  [LColor.p, LColor.b, LColor.b, LColor.r]

def tttFiber66Expected : List Nat :=
  []

def tttFiber66Rows : List TripleComponentParentRow :=
  []

def tttFiber66SourcesCheck : Bool :=
  (tttFiber66Rows.map fun row => row.source) == tttFiber66Expected

theorem tttFiber66SourcesCheck_ok :
    tttFiber66SourcesCheck = true := by
  decide

def tttFiber66CertificateAudit : Bool :=
  tttFiber66SourcesCheck

theorem tttFiber66CertificateAudit_ok :
    tttFiber66CertificateAudit = true := by
  simp [tttFiber66CertificateAudit,
    tttFiber66SourcesCheck_ok]

def tttFiber67Key : List LColor :=
  [LColor.p, LColor.b, LColor.b, LColor.b]

def tttFiber67Expected : List Nat :=
  []

def tttFiber67Rows : List TripleComponentParentRow :=
  []

def tttFiber67SourcesCheck : Bool :=
  (tttFiber67Rows.map fun row => row.source) == tttFiber67Expected

theorem tttFiber67SourcesCheck_ok :
    tttFiber67SourcesCheck = true := by
  decide

def tttFiber67CertificateAudit : Bool :=
  tttFiber67SourcesCheck

theorem tttFiber67CertificateAudit_ok :
    tttFiber67CertificateAudit = true := by
  simp [tttFiber67CertificateAudit,
    tttFiber67SourcesCheck_ok]

def tttFiber68Key : List LColor :=
  [LColor.p, LColor.b, LColor.b, LColor.p]

def tttFiber68Expected : List Nat :=
  []

def tttFiber68Rows : List TripleComponentParentRow :=
  []

def tttFiber68SourcesCheck : Bool :=
  (tttFiber68Rows.map fun row => row.source) == tttFiber68Expected

theorem tttFiber68SourcesCheck_ok :
    tttFiber68SourcesCheck = true := by
  decide

def tttFiber68CertificateAudit : Bool :=
  tttFiber68SourcesCheck

theorem tttFiber68CertificateAudit_ok :
    tttFiber68CertificateAudit = true := by
  simp [tttFiber68CertificateAudit,
    tttFiber68SourcesCheck_ok]

def tttFiber69Key : List LColor :=
  [LColor.p, LColor.b, LColor.p, LColor.r]

def tttFiber69Expected : List Nat :=
  [3264, 3265, 3266, 3267, 3268, 3269, 3270, 3271,
   3272, 3273, 3274, 3275, 3276, 3277, 3278, 3279]

def tttFiber69Row0 : TripleComponentParentRow :=
  tripleRow 3264 3264 98 54 112 98 54 112
    default
    []

def tttFiber69Row1 : TripleComponentParentRow :=
  tripleRow 3265 3264 98 54 113 98 54 112
    (chainMove LColor.r LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber69Row2 : TripleComponentParentRow :=
  tripleRow 3266 3264 98 54 114 98 54 112
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber69Row3 : TripleComponentParentRow :=
  tripleRow 3267 3265 98 54 115 98 54 113
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber69Row4 : TripleComponentParentRow :=
  tripleRow 3268 3264 98 55 120 98 54 112
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber69Row5 : TripleComponentParentRow :=
  tripleRow 3269 3265 98 55 121 98 54 113
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber69Row6 : TripleComponentParentRow :=
  tripleRow 3270 3266 98 55 122 98 54 114
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber69Row7 : TripleComponentParentRow :=
  tripleRow 3271 3267 98 55 123 98 54 115
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber69Row8 : TripleComponentParentRow :=
  tripleRow 3272 3264 99 62 112 98 54 112
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber69Row9 : TripleComponentParentRow :=
  tripleRow 3273 3265 99 62 113 98 54 113
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber69Row10 : TripleComponentParentRow :=
  tripleRow 3274 3266 99 62 114 98 54 114
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber69Row11 : TripleComponentParentRow :=
  tripleRow 3275 3267 99 62 115 98 54 115
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber69Row12 : TripleComponentParentRow :=
  tripleRow 3276 3268 99 63 120 98 55 120
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber69Row13 : TripleComponentParentRow :=
  tripleRow 3277 3269 99 63 121 98 55 121
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber69Row14 : TripleComponentParentRow :=
  tripleRow 3278 3270 99 63 122 98 55 122
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber69Row15 : TripleComponentParentRow :=
  tripleRow 3279 3271 99 63 123 98 55 123
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber69Rows : List TripleComponentParentRow :=
  [ tttFiber69Row0
  , tttFiber69Row1
  , tttFiber69Row2
  , tttFiber69Row3
  , tttFiber69Row4
  , tttFiber69Row5
  , tttFiber69Row6
  , tttFiber69Row7
  , tttFiber69Row8
  , tttFiber69Row9
  , tttFiber69Row10
  , tttFiber69Row11
  , tttFiber69Row12
  , tttFiber69Row13
  , tttFiber69Row14
  , tttFiber69Row15
  ]

def tttFiber69SourcesCheck : Bool :=
  (tttFiber69Rows.map fun row => row.source) == tttFiber69Expected

theorem tttFiber69SourcesCheck_ok :
    tttFiber69SourcesCheck = true := by
  decide

def tttFiber69RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber69Key tttFiber69Expected
    (listGetD tttFiber69Rows i default)

theorem tttFiber69Row_0_ok : tttFiber69RowCheck 0 = true := by
  decide
theorem tttFiber69Row_1_ok : tttFiber69RowCheck 1 = true := by
  decide
theorem tttFiber69Row_2_ok : tttFiber69RowCheck 2 = true := by
  decide
theorem tttFiber69Row_3_ok : tttFiber69RowCheck 3 = true := by
  decide
theorem tttFiber69Row_4_ok : tttFiber69RowCheck 4 = true := by
  decide
theorem tttFiber69Row_5_ok : tttFiber69RowCheck 5 = true := by
  decide
theorem tttFiber69Row_6_ok : tttFiber69RowCheck 6 = true := by
  decide
theorem tttFiber69Row_7_ok : tttFiber69RowCheck 7 = true := by
  decide
theorem tttFiber69Row_8_ok : tttFiber69RowCheck 8 = true := by
  decide
theorem tttFiber69Row_9_ok : tttFiber69RowCheck 9 = true := by
  decide
theorem tttFiber69Row_10_ok : tttFiber69RowCheck 10 = true := by
  decide
theorem tttFiber69Row_11_ok : tttFiber69RowCheck 11 = true := by
  decide
theorem tttFiber69Row_12_ok : tttFiber69RowCheck 12 = true := by
  decide
theorem tttFiber69Row_13_ok : tttFiber69RowCheck 13 = true := by
  decide
theorem tttFiber69Row_14_ok : tttFiber69RowCheck 14 = true := by
  decide
theorem tttFiber69Row_15_ok : tttFiber69RowCheck 15 = true := by
  decide

def tttFiber69ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber69Rows tttLightMaxParentDepth
    (listGetD tttFiber69Expected i 0) == 3264

theorem tttFiber69Parent_0_ok : tttFiber69ParentCheck 0 = true := by
  decide
theorem tttFiber69Parent_1_ok : tttFiber69ParentCheck 1 = true := by
  decide
theorem tttFiber69Parent_2_ok : tttFiber69ParentCheck 2 = true := by
  decide
theorem tttFiber69Parent_3_ok : tttFiber69ParentCheck 3 = true := by
  decide
theorem tttFiber69Parent_4_ok : tttFiber69ParentCheck 4 = true := by
  decide
theorem tttFiber69Parent_5_ok : tttFiber69ParentCheck 5 = true := by
  decide
theorem tttFiber69Parent_6_ok : tttFiber69ParentCheck 6 = true := by
  decide
theorem tttFiber69Parent_7_ok : tttFiber69ParentCheck 7 = true := by
  decide
theorem tttFiber69Parent_8_ok : tttFiber69ParentCheck 8 = true := by
  decide
theorem tttFiber69Parent_9_ok : tttFiber69ParentCheck 9 = true := by
  decide
theorem tttFiber69Parent_10_ok : tttFiber69ParentCheck 10 = true := by
  decide
theorem tttFiber69Parent_11_ok : tttFiber69ParentCheck 11 = true := by
  decide
theorem tttFiber69Parent_12_ok : tttFiber69ParentCheck 12 = true := by
  decide
theorem tttFiber69Parent_13_ok : tttFiber69ParentCheck 13 = true := by
  decide
theorem tttFiber69Parent_14_ok : tttFiber69ParentCheck 14 = true := by
  decide
theorem tttFiber69Parent_15_ok : tttFiber69ParentCheck 15 = true := by
  decide

def tttFiber69CertificateAudit : Bool :=
  tttFiber69SourcesCheck
    && tttFiber69RowCheck 0
    && tttFiber69RowCheck 1
    && tttFiber69RowCheck 2
    && tttFiber69RowCheck 3
    && tttFiber69RowCheck 4
    && tttFiber69RowCheck 5
    && tttFiber69RowCheck 6
    && tttFiber69RowCheck 7
    && tttFiber69RowCheck 8
    && tttFiber69RowCheck 9
    && tttFiber69RowCheck 10
    && tttFiber69RowCheck 11
    && tttFiber69RowCheck 12
    && tttFiber69RowCheck 13
    && tttFiber69RowCheck 14
    && tttFiber69RowCheck 15
    && tttFiber69ParentCheck 0
    && tttFiber69ParentCheck 1
    && tttFiber69ParentCheck 2
    && tttFiber69ParentCheck 3
    && tttFiber69ParentCheck 4
    && tttFiber69ParentCheck 5
    && tttFiber69ParentCheck 6
    && tttFiber69ParentCheck 7
    && tttFiber69ParentCheck 8
    && tttFiber69ParentCheck 9
    && tttFiber69ParentCheck 10
    && tttFiber69ParentCheck 11
    && tttFiber69ParentCheck 12
    && tttFiber69ParentCheck 13
    && tttFiber69ParentCheck 14
    && tttFiber69ParentCheck 15

theorem tttFiber69CertificateAudit_ok :
    tttFiber69CertificateAudit = true := by
  simp [tttFiber69CertificateAudit,
    tttFiber69SourcesCheck_ok,
    tttFiber69Row_0_ok,
    tttFiber69Row_1_ok,
    tttFiber69Row_2_ok,
    tttFiber69Row_3_ok,
    tttFiber69Row_4_ok,
    tttFiber69Row_5_ok,
    tttFiber69Row_6_ok,
    tttFiber69Row_7_ok,
    tttFiber69Row_8_ok,
    tttFiber69Row_9_ok,
    tttFiber69Row_10_ok,
    tttFiber69Row_11_ok,
    tttFiber69Row_12_ok,
    tttFiber69Row_13_ok,
    tttFiber69Row_14_ok,
    tttFiber69Row_15_ok,
    tttFiber69Parent_0_ok,
    tttFiber69Parent_1_ok,
    tttFiber69Parent_2_ok,
    tttFiber69Parent_3_ok,
    tttFiber69Parent_4_ok,
    tttFiber69Parent_5_ok,
    tttFiber69Parent_6_ok,
    tttFiber69Parent_7_ok,
    tttFiber69Parent_8_ok,
    tttFiber69Parent_9_ok,
    tttFiber69Parent_10_ok,
    tttFiber69Parent_11_ok,
    tttFiber69Parent_12_ok,
    tttFiber69Parent_13_ok,
    tttFiber69Parent_14_ok,
    tttFiber69Parent_15_ok]

def tttFiber71Key : List LColor :=
  [LColor.p, LColor.b, LColor.p, LColor.p]

def tttFiber71Expected : List Nat :=
  [2976, 2977, 2978, 2979, 2980, 2981, 2982, 2983,
   2984, 2985, 2986, 2987, 2988, 2989, 2990, 2991]

def tttFiber71Row0 : TripleComponentParentRow :=
  tripleRow 2976 2976 84 144 84 84 144 84
    default
    []

def tttFiber71Row1 : TripleComponentParentRow :=
  tripleRow 2977 2976 84 144 85 84 144 84
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber71Row2 : TripleComponentParentRow :=
  tripleRow 2978 2976 84 144 86 84 144 84
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber71Row3 : TripleComponentParentRow :=
  tripleRow 2979 2977 84 144 87 84 144 85
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber71Row4 : TripleComponentParentRow :=
  tripleRow 2980 2976 84 145 92 84 144 84
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber71Row5 : TripleComponentParentRow :=
  tripleRow 2981 2977 84 145 93 84 144 85
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber71Row6 : TripleComponentParentRow :=
  tripleRow 2982 2978 84 145 94 84 144 86
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber71Row7 : TripleComponentParentRow :=
  tripleRow 2983 2979 84 145 95 84 144 87
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber71Row8 : TripleComponentParentRow :=
  tripleRow 2984 2976 85 152 84 84 144 84
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber71Row9 : TripleComponentParentRow :=
  tripleRow 2985 2977 85 152 85 84 144 85
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber71Row10 : TripleComponentParentRow :=
  tripleRow 2986 2978 85 152 86 84 144 86
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber71Row11 : TripleComponentParentRow :=
  tripleRow 2987 2979 85 152 87 84 144 87
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber71Row12 : TripleComponentParentRow :=
  tripleRow 2988 2980 85 153 92 84 145 92
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber71Row13 : TripleComponentParentRow :=
  tripleRow 2989 2981 85 153 93 84 145 93
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber71Row14 : TripleComponentParentRow :=
  tripleRow 2990 2982 85 153 94 84 145 94
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber71Row15 : TripleComponentParentRow :=
  tripleRow 2991 2983 85 153 95 84 145 95
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber71Rows : List TripleComponentParentRow :=
  [ tttFiber71Row0
  , tttFiber71Row1
  , tttFiber71Row2
  , tttFiber71Row3
  , tttFiber71Row4
  , tttFiber71Row5
  , tttFiber71Row6
  , tttFiber71Row7
  , tttFiber71Row8
  , tttFiber71Row9
  , tttFiber71Row10
  , tttFiber71Row11
  , tttFiber71Row12
  , tttFiber71Row13
  , tttFiber71Row14
  , tttFiber71Row15
  ]

def tttFiber71SourcesCheck : Bool :=
  (tttFiber71Rows.map fun row => row.source) == tttFiber71Expected

theorem tttFiber71SourcesCheck_ok :
    tttFiber71SourcesCheck = true := by
  decide

def tttFiber71RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber71Key tttFiber71Expected
    (listGetD tttFiber71Rows i default)

theorem tttFiber71Row_0_ok : tttFiber71RowCheck 0 = true := by
  decide
theorem tttFiber71Row_1_ok : tttFiber71RowCheck 1 = true := by
  decide
theorem tttFiber71Row_2_ok : tttFiber71RowCheck 2 = true := by
  decide
theorem tttFiber71Row_3_ok : tttFiber71RowCheck 3 = true := by
  decide
theorem tttFiber71Row_4_ok : tttFiber71RowCheck 4 = true := by
  decide
theorem tttFiber71Row_5_ok : tttFiber71RowCheck 5 = true := by
  decide
theorem tttFiber71Row_6_ok : tttFiber71RowCheck 6 = true := by
  decide
theorem tttFiber71Row_7_ok : tttFiber71RowCheck 7 = true := by
  decide
theorem tttFiber71Row_8_ok : tttFiber71RowCheck 8 = true := by
  decide
theorem tttFiber71Row_9_ok : tttFiber71RowCheck 9 = true := by
  decide
theorem tttFiber71Row_10_ok : tttFiber71RowCheck 10 = true := by
  decide
theorem tttFiber71Row_11_ok : tttFiber71RowCheck 11 = true := by
  decide
theorem tttFiber71Row_12_ok : tttFiber71RowCheck 12 = true := by
  decide
theorem tttFiber71Row_13_ok : tttFiber71RowCheck 13 = true := by
  decide
theorem tttFiber71Row_14_ok : tttFiber71RowCheck 14 = true := by
  decide
theorem tttFiber71Row_15_ok : tttFiber71RowCheck 15 = true := by
  decide

def tttFiber71ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber71Rows tttLightMaxParentDepth
    (listGetD tttFiber71Expected i 0) == 2976

theorem tttFiber71Parent_0_ok : tttFiber71ParentCheck 0 = true := by
  decide
theorem tttFiber71Parent_1_ok : tttFiber71ParentCheck 1 = true := by
  decide
theorem tttFiber71Parent_2_ok : tttFiber71ParentCheck 2 = true := by
  decide
theorem tttFiber71Parent_3_ok : tttFiber71ParentCheck 3 = true := by
  decide
theorem tttFiber71Parent_4_ok : tttFiber71ParentCheck 4 = true := by
  decide
theorem tttFiber71Parent_5_ok : tttFiber71ParentCheck 5 = true := by
  decide
theorem tttFiber71Parent_6_ok : tttFiber71ParentCheck 6 = true := by
  decide
theorem tttFiber71Parent_7_ok : tttFiber71ParentCheck 7 = true := by
  decide
theorem tttFiber71Parent_8_ok : tttFiber71ParentCheck 8 = true := by
  decide
theorem tttFiber71Parent_9_ok : tttFiber71ParentCheck 9 = true := by
  decide
theorem tttFiber71Parent_10_ok : tttFiber71ParentCheck 10 = true := by
  decide
theorem tttFiber71Parent_11_ok : tttFiber71ParentCheck 11 = true := by
  decide
theorem tttFiber71Parent_12_ok : tttFiber71ParentCheck 12 = true := by
  decide
theorem tttFiber71Parent_13_ok : tttFiber71ParentCheck 13 = true := by
  decide
theorem tttFiber71Parent_14_ok : tttFiber71ParentCheck 14 = true := by
  decide
theorem tttFiber71Parent_15_ok : tttFiber71ParentCheck 15 = true := by
  decide

def tttFiber71CertificateAudit : Bool :=
  tttFiber71SourcesCheck
    && tttFiber71RowCheck 0
    && tttFiber71RowCheck 1
    && tttFiber71RowCheck 2
    && tttFiber71RowCheck 3
    && tttFiber71RowCheck 4
    && tttFiber71RowCheck 5
    && tttFiber71RowCheck 6
    && tttFiber71RowCheck 7
    && tttFiber71RowCheck 8
    && tttFiber71RowCheck 9
    && tttFiber71RowCheck 10
    && tttFiber71RowCheck 11
    && tttFiber71RowCheck 12
    && tttFiber71RowCheck 13
    && tttFiber71RowCheck 14
    && tttFiber71RowCheck 15
    && tttFiber71ParentCheck 0
    && tttFiber71ParentCheck 1
    && tttFiber71ParentCheck 2
    && tttFiber71ParentCheck 3
    && tttFiber71ParentCheck 4
    && tttFiber71ParentCheck 5
    && tttFiber71ParentCheck 6
    && tttFiber71ParentCheck 7
    && tttFiber71ParentCheck 8
    && tttFiber71ParentCheck 9
    && tttFiber71ParentCheck 10
    && tttFiber71ParentCheck 11
    && tttFiber71ParentCheck 12
    && tttFiber71ParentCheck 13
    && tttFiber71ParentCheck 14
    && tttFiber71ParentCheck 15

theorem tttFiber71CertificateAudit_ok :
    tttFiber71CertificateAudit = true := by
  simp [tttFiber71CertificateAudit,
    tttFiber71SourcesCheck_ok,
    tttFiber71Row_0_ok,
    tttFiber71Row_1_ok,
    tttFiber71Row_2_ok,
    tttFiber71Row_3_ok,
    tttFiber71Row_4_ok,
    tttFiber71Row_5_ok,
    tttFiber71Row_6_ok,
    tttFiber71Row_7_ok,
    tttFiber71Row_8_ok,
    tttFiber71Row_9_ok,
    tttFiber71Row_10_ok,
    tttFiber71Row_11_ok,
    tttFiber71Row_12_ok,
    tttFiber71Row_13_ok,
    tttFiber71Row_14_ok,
    tttFiber71Row_15_ok,
    tttFiber71Parent_0_ok,
    tttFiber71Parent_1_ok,
    tttFiber71Parent_2_ok,
    tttFiber71Parent_3_ok,
    tttFiber71Parent_4_ok,
    tttFiber71Parent_5_ok,
    tttFiber71Parent_6_ok,
    tttFiber71Parent_7_ok,
    tttFiber71Parent_8_ok,
    tttFiber71Parent_9_ok,
    tttFiber71Parent_10_ok,
    tttFiber71Parent_11_ok,
    tttFiber71Parent_12_ok,
    tttFiber71Parent_13_ok,
    tttFiber71Parent_14_ok,
    tttFiber71Parent_15_ok]

def tttFiber73Key : List LColor :=
  [LColor.p, LColor.p, LColor.r, LColor.b]

def tttFiber73Expected : List Nat :=
  [1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623,
   1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631]

def tttFiber73Row0 : TripleComponentParentRow :=
  tripleRow 1616 1616 46 114 52 46 114 52
    default
    []

def tttFiber73Row1 : TripleComponentParentRow :=
  tripleRow 1617 1616 46 114 53 46 114 52
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber73Row2 : TripleComponentParentRow :=
  tripleRow 1618 1617 46 114 54 46 114 53
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber73Row3 : TripleComponentParentRow :=
  tripleRow 1619 1616 46 114 55 46 114 52
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber73Row4 : TripleComponentParentRow :=
  tripleRow 1620 1616 46 115 60 46 114 52
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber73Row5 : TripleComponentParentRow :=
  tripleRow 1621 1617 46 115 61 46 114 53
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber73Row6 : TripleComponentParentRow :=
  tripleRow 1622 1618 46 115 62 46 114 54
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber73Row7 : TripleComponentParentRow :=
  tripleRow 1623 1619 46 115 63 46 114 55
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber73Row8 : TripleComponentParentRow :=
  tripleRow 1624 1616 47 122 52 46 114 52
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber73Row9 : TripleComponentParentRow :=
  tripleRow 1625 1617 47 122 53 46 114 53
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber73Row10 : TripleComponentParentRow :=
  tripleRow 1626 1618 47 122 54 46 114 54
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber73Row11 : TripleComponentParentRow :=
  tripleRow 1627 1619 47 122 55 46 114 55
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber73Row12 : TripleComponentParentRow :=
  tripleRow 1628 1620 47 123 60 46 115 60
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber73Row13 : TripleComponentParentRow :=
  tripleRow 1629 1621 47 123 61 46 115 61
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber73Row14 : TripleComponentParentRow :=
  tripleRow 1630 1622 47 123 62 46 115 62
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber73Row15 : TripleComponentParentRow :=
  tripleRow 1631 1623 47 123 63 46 115 63
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber73Rows : List TripleComponentParentRow :=
  [ tttFiber73Row0
  , tttFiber73Row1
  , tttFiber73Row2
  , tttFiber73Row3
  , tttFiber73Row4
  , tttFiber73Row5
  , tttFiber73Row6
  , tttFiber73Row7
  , tttFiber73Row8
  , tttFiber73Row9
  , tttFiber73Row10
  , tttFiber73Row11
  , tttFiber73Row12
  , tttFiber73Row13
  , tttFiber73Row14
  , tttFiber73Row15
  ]

def tttFiber73SourcesCheck : Bool :=
  (tttFiber73Rows.map fun row => row.source) == tttFiber73Expected

theorem tttFiber73SourcesCheck_ok :
    tttFiber73SourcesCheck = true := by
  decide

def tttFiber73RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber73Key tttFiber73Expected
    (listGetD tttFiber73Rows i default)

theorem tttFiber73Row_0_ok : tttFiber73RowCheck 0 = true := by
  decide
theorem tttFiber73Row_1_ok : tttFiber73RowCheck 1 = true := by
  decide
theorem tttFiber73Row_2_ok : tttFiber73RowCheck 2 = true := by
  decide
theorem tttFiber73Row_3_ok : tttFiber73RowCheck 3 = true := by
  decide
theorem tttFiber73Row_4_ok : tttFiber73RowCheck 4 = true := by
  decide
theorem tttFiber73Row_5_ok : tttFiber73RowCheck 5 = true := by
  decide
theorem tttFiber73Row_6_ok : tttFiber73RowCheck 6 = true := by
  decide
theorem tttFiber73Row_7_ok : tttFiber73RowCheck 7 = true := by
  decide
theorem tttFiber73Row_8_ok : tttFiber73RowCheck 8 = true := by
  decide
theorem tttFiber73Row_9_ok : tttFiber73RowCheck 9 = true := by
  decide
theorem tttFiber73Row_10_ok : tttFiber73RowCheck 10 = true := by
  decide
theorem tttFiber73Row_11_ok : tttFiber73RowCheck 11 = true := by
  decide
theorem tttFiber73Row_12_ok : tttFiber73RowCheck 12 = true := by
  decide
theorem tttFiber73Row_13_ok : tttFiber73RowCheck 13 = true := by
  decide
theorem tttFiber73Row_14_ok : tttFiber73RowCheck 14 = true := by
  decide
theorem tttFiber73Row_15_ok : tttFiber73RowCheck 15 = true := by
  decide

def tttFiber73ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber73Rows tttLightMaxParentDepth
    (listGetD tttFiber73Expected i 0) == 1616

theorem tttFiber73Parent_0_ok : tttFiber73ParentCheck 0 = true := by
  decide
theorem tttFiber73Parent_1_ok : tttFiber73ParentCheck 1 = true := by
  decide
theorem tttFiber73Parent_2_ok : tttFiber73ParentCheck 2 = true := by
  decide
theorem tttFiber73Parent_3_ok : tttFiber73ParentCheck 3 = true := by
  decide
theorem tttFiber73Parent_4_ok : tttFiber73ParentCheck 4 = true := by
  decide
theorem tttFiber73Parent_5_ok : tttFiber73ParentCheck 5 = true := by
  decide
theorem tttFiber73Parent_6_ok : tttFiber73ParentCheck 6 = true := by
  decide
theorem tttFiber73Parent_7_ok : tttFiber73ParentCheck 7 = true := by
  decide
theorem tttFiber73Parent_8_ok : tttFiber73ParentCheck 8 = true := by
  decide
theorem tttFiber73Parent_9_ok : tttFiber73ParentCheck 9 = true := by
  decide
theorem tttFiber73Parent_10_ok : tttFiber73ParentCheck 10 = true := by
  decide
theorem tttFiber73Parent_11_ok : tttFiber73ParentCheck 11 = true := by
  decide
theorem tttFiber73Parent_12_ok : tttFiber73ParentCheck 12 = true := by
  decide
theorem tttFiber73Parent_13_ok : tttFiber73ParentCheck 13 = true := by
  decide
theorem tttFiber73Parent_14_ok : tttFiber73ParentCheck 14 = true := by
  decide
theorem tttFiber73Parent_15_ok : tttFiber73ParentCheck 15 = true := by
  decide

def tttFiber73CertificateAudit : Bool :=
  tttFiber73SourcesCheck
    && tttFiber73RowCheck 0
    && tttFiber73RowCheck 1
    && tttFiber73RowCheck 2
    && tttFiber73RowCheck 3
    && tttFiber73RowCheck 4
    && tttFiber73RowCheck 5
    && tttFiber73RowCheck 6
    && tttFiber73RowCheck 7
    && tttFiber73RowCheck 8
    && tttFiber73RowCheck 9
    && tttFiber73RowCheck 10
    && tttFiber73RowCheck 11
    && tttFiber73RowCheck 12
    && tttFiber73RowCheck 13
    && tttFiber73RowCheck 14
    && tttFiber73RowCheck 15
    && tttFiber73ParentCheck 0
    && tttFiber73ParentCheck 1
    && tttFiber73ParentCheck 2
    && tttFiber73ParentCheck 3
    && tttFiber73ParentCheck 4
    && tttFiber73ParentCheck 5
    && tttFiber73ParentCheck 6
    && tttFiber73ParentCheck 7
    && tttFiber73ParentCheck 8
    && tttFiber73ParentCheck 9
    && tttFiber73ParentCheck 10
    && tttFiber73ParentCheck 11
    && tttFiber73ParentCheck 12
    && tttFiber73ParentCheck 13
    && tttFiber73ParentCheck 14
    && tttFiber73ParentCheck 15

theorem tttFiber73CertificateAudit_ok :
    tttFiber73CertificateAudit = true := by
  simp [tttFiber73CertificateAudit,
    tttFiber73SourcesCheck_ok,
    tttFiber73Row_0_ok,
    tttFiber73Row_1_ok,
    tttFiber73Row_2_ok,
    tttFiber73Row_3_ok,
    tttFiber73Row_4_ok,
    tttFiber73Row_5_ok,
    tttFiber73Row_6_ok,
    tttFiber73Row_7_ok,
    tttFiber73Row_8_ok,
    tttFiber73Row_9_ok,
    tttFiber73Row_10_ok,
    tttFiber73Row_11_ok,
    tttFiber73Row_12_ok,
    tttFiber73Row_13_ok,
    tttFiber73Row_14_ok,
    tttFiber73Row_15_ok,
    tttFiber73Parent_0_ok,
    tttFiber73Parent_1_ok,
    tttFiber73Parent_2_ok,
    tttFiber73Parent_3_ok,
    tttFiber73Parent_4_ok,
    tttFiber73Parent_5_ok,
    tttFiber73Parent_6_ok,
    tttFiber73Parent_7_ok,
    tttFiber73Parent_8_ok,
    tttFiber73Parent_9_ok,
    tttFiber73Parent_10_ok,
    tttFiber73Parent_11_ok,
    tttFiber73Parent_12_ok,
    tttFiber73Parent_13_ok,
    tttFiber73Parent_14_ok,
    tttFiber73Parent_15_ok]

def tttFiber74Key : List LColor :=
  [LColor.p, LColor.p, LColor.r, LColor.p]

def tttFiber74Expected : List Nat :=
  [1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079,
   1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087]

def tttFiber74Row0 : TripleComponentParentRow :=
  tripleRow 1072 1072 30 176 20 30 176 20
    default
    []

def tttFiber74Row1 : TripleComponentParentRow :=
  tripleRow 1073 1072 30 176 21 30 176 20
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber74Row2 : TripleComponentParentRow :=
  tripleRow 1074 1072 30 176 22 30 176 20
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber74Row3 : TripleComponentParentRow :=
  tripleRow 1075 1073 30 176 23 30 176 21
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber74Row4 : TripleComponentParentRow :=
  tripleRow 1076 1072 30 177 28 30 176 20
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber74Row5 : TripleComponentParentRow :=
  tripleRow 1077 1073 30 177 29 30 176 21
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber74Row6 : TripleComponentParentRow :=
  tripleRow 1078 1074 30 177 30 30 176 22
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber74Row7 : TripleComponentParentRow :=
  tripleRow 1079 1075 30 177 31 30 176 23
    (chainMove LColor.r LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber74Row8 : TripleComponentParentRow :=
  tripleRow 1080 1072 31 184 20 30 176 20
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber74Row9 : TripleComponentParentRow :=
  tripleRow 1081 1073 31 184 21 30 176 21
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber74Row10 : TripleComponentParentRow :=
  tripleRow 1082 1074 31 184 22 30 176 22
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber74Row11 : TripleComponentParentRow :=
  tripleRow 1083 1075 31 184 23 30 176 23
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber74Row12 : TripleComponentParentRow :=
  tripleRow 1084 1076 31 185 28 30 177 28
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber74Row13 : TripleComponentParentRow :=
  tripleRow 1085 1077 31 185 29 30 177 29
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber74Row14 : TripleComponentParentRow :=
  tripleRow 1086 1078 31 185 30 30 177 30
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber74Row15 : TripleComponentParentRow :=
  tripleRow 1087 1079 31 185 31 30 177 31
    (chainMove LColor.r LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber74Rows : List TripleComponentParentRow :=
  [ tttFiber74Row0
  , tttFiber74Row1
  , tttFiber74Row2
  , tttFiber74Row3
  , tttFiber74Row4
  , tttFiber74Row5
  , tttFiber74Row6
  , tttFiber74Row7
  , tttFiber74Row8
  , tttFiber74Row9
  , tttFiber74Row10
  , tttFiber74Row11
  , tttFiber74Row12
  , tttFiber74Row13
  , tttFiber74Row14
  , tttFiber74Row15
  ]

def tttFiber74SourcesCheck : Bool :=
  (tttFiber74Rows.map fun row => row.source) == tttFiber74Expected

theorem tttFiber74SourcesCheck_ok :
    tttFiber74SourcesCheck = true := by
  decide

def tttFiber74RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber74Key tttFiber74Expected
    (listGetD tttFiber74Rows i default)

theorem tttFiber74Row_0_ok : tttFiber74RowCheck 0 = true := by
  decide
theorem tttFiber74Row_1_ok : tttFiber74RowCheck 1 = true := by
  decide
theorem tttFiber74Row_2_ok : tttFiber74RowCheck 2 = true := by
  decide
theorem tttFiber74Row_3_ok : tttFiber74RowCheck 3 = true := by
  decide
theorem tttFiber74Row_4_ok : tttFiber74RowCheck 4 = true := by
  decide
theorem tttFiber74Row_5_ok : tttFiber74RowCheck 5 = true := by
  decide
theorem tttFiber74Row_6_ok : tttFiber74RowCheck 6 = true := by
  decide
theorem tttFiber74Row_7_ok : tttFiber74RowCheck 7 = true := by
  decide
theorem tttFiber74Row_8_ok : tttFiber74RowCheck 8 = true := by
  decide
theorem tttFiber74Row_9_ok : tttFiber74RowCheck 9 = true := by
  decide
theorem tttFiber74Row_10_ok : tttFiber74RowCheck 10 = true := by
  decide
theorem tttFiber74Row_11_ok : tttFiber74RowCheck 11 = true := by
  decide
theorem tttFiber74Row_12_ok : tttFiber74RowCheck 12 = true := by
  decide
theorem tttFiber74Row_13_ok : tttFiber74RowCheck 13 = true := by
  decide
theorem tttFiber74Row_14_ok : tttFiber74RowCheck 14 = true := by
  decide
theorem tttFiber74Row_15_ok : tttFiber74RowCheck 15 = true := by
  decide

def tttFiber74ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber74Rows tttLightMaxParentDepth
    (listGetD tttFiber74Expected i 0) == 1072

theorem tttFiber74Parent_0_ok : tttFiber74ParentCheck 0 = true := by
  decide
theorem tttFiber74Parent_1_ok : tttFiber74ParentCheck 1 = true := by
  decide
theorem tttFiber74Parent_2_ok : tttFiber74ParentCheck 2 = true := by
  decide
theorem tttFiber74Parent_3_ok : tttFiber74ParentCheck 3 = true := by
  decide
theorem tttFiber74Parent_4_ok : tttFiber74ParentCheck 4 = true := by
  decide
theorem tttFiber74Parent_5_ok : tttFiber74ParentCheck 5 = true := by
  decide
theorem tttFiber74Parent_6_ok : tttFiber74ParentCheck 6 = true := by
  decide
theorem tttFiber74Parent_7_ok : tttFiber74ParentCheck 7 = true := by
  decide
theorem tttFiber74Parent_8_ok : tttFiber74ParentCheck 8 = true := by
  decide
theorem tttFiber74Parent_9_ok : tttFiber74ParentCheck 9 = true := by
  decide
theorem tttFiber74Parent_10_ok : tttFiber74ParentCheck 10 = true := by
  decide
theorem tttFiber74Parent_11_ok : tttFiber74ParentCheck 11 = true := by
  decide
theorem tttFiber74Parent_12_ok : tttFiber74ParentCheck 12 = true := by
  decide
theorem tttFiber74Parent_13_ok : tttFiber74ParentCheck 13 = true := by
  decide
theorem tttFiber74Parent_14_ok : tttFiber74ParentCheck 14 = true := by
  decide
theorem tttFiber74Parent_15_ok : tttFiber74ParentCheck 15 = true := by
  decide

def tttFiber74CertificateAudit : Bool :=
  tttFiber74SourcesCheck
    && tttFiber74RowCheck 0
    && tttFiber74RowCheck 1
    && tttFiber74RowCheck 2
    && tttFiber74RowCheck 3
    && tttFiber74RowCheck 4
    && tttFiber74RowCheck 5
    && tttFiber74RowCheck 6
    && tttFiber74RowCheck 7
    && tttFiber74RowCheck 8
    && tttFiber74RowCheck 9
    && tttFiber74RowCheck 10
    && tttFiber74RowCheck 11
    && tttFiber74RowCheck 12
    && tttFiber74RowCheck 13
    && tttFiber74RowCheck 14
    && tttFiber74RowCheck 15
    && tttFiber74ParentCheck 0
    && tttFiber74ParentCheck 1
    && tttFiber74ParentCheck 2
    && tttFiber74ParentCheck 3
    && tttFiber74ParentCheck 4
    && tttFiber74ParentCheck 5
    && tttFiber74ParentCheck 6
    && tttFiber74ParentCheck 7
    && tttFiber74ParentCheck 8
    && tttFiber74ParentCheck 9
    && tttFiber74ParentCheck 10
    && tttFiber74ParentCheck 11
    && tttFiber74ParentCheck 12
    && tttFiber74ParentCheck 13
    && tttFiber74ParentCheck 14
    && tttFiber74ParentCheck 15

theorem tttFiber74CertificateAudit_ok :
    tttFiber74CertificateAudit = true := by
  simp [tttFiber74CertificateAudit,
    tttFiber74SourcesCheck_ok,
    tttFiber74Row_0_ok,
    tttFiber74Row_1_ok,
    tttFiber74Row_2_ok,
    tttFiber74Row_3_ok,
    tttFiber74Row_4_ok,
    tttFiber74Row_5_ok,
    tttFiber74Row_6_ok,
    tttFiber74Row_7_ok,
    tttFiber74Row_8_ok,
    tttFiber74Row_9_ok,
    tttFiber74Row_10_ok,
    tttFiber74Row_11_ok,
    tttFiber74Row_12_ok,
    tttFiber74Row_13_ok,
    tttFiber74Row_14_ok,
    tttFiber74Row_15_ok,
    tttFiber74Parent_0_ok,
    tttFiber74Parent_1_ok,
    tttFiber74Parent_2_ok,
    tttFiber74Parent_3_ok,
    tttFiber74Parent_4_ok,
    tttFiber74Parent_5_ok,
    tttFiber74Parent_6_ok,
    tttFiber74Parent_7_ok,
    tttFiber74Parent_8_ok,
    tttFiber74Parent_9_ok,
    tttFiber74Parent_10_ok,
    tttFiber74Parent_11_ok,
    tttFiber74Parent_12_ok,
    tttFiber74Parent_13_ok,
    tttFiber74Parent_14_ok,
    tttFiber74Parent_15_ok]

def tttFiber75Key : List LColor :=
  [LColor.p, LColor.p, LColor.b, LColor.r]

def tttFiber75Expected : List Nat :=
  [3536, 3537, 3538, 3539, 3540, 3541, 3542, 3543,
   3544, 3545, 3546, 3547, 3548, 3549, 3550, 3551]

def tttFiber75Row0 : TripleComponentParentRow :=
  tripleRow 3536 3536 106 54 112 106 54 112
    default
    []

def tttFiber75Row1 : TripleComponentParentRow :=
  tripleRow 3537 3536 106 54 113 106 54 112
    (chainMove LColor.r LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber75Row2 : TripleComponentParentRow :=
  tripleRow 3538 3536 106 54 114 106 54 112
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber75Row3 : TripleComponentParentRow :=
  tripleRow 3539 3537 106 54 115 106 54 113
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber75Row4 : TripleComponentParentRow :=
  tripleRow 3540 3536 106 55 120 106 54 112
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber75Row5 : TripleComponentParentRow :=
  tripleRow 3541 3537 106 55 121 106 54 113
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber75Row6 : TripleComponentParentRow :=
  tripleRow 3542 3538 106 55 122 106 54 114
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber75Row7 : TripleComponentParentRow :=
  tripleRow 3543 3539 106 55 123 106 54 115
    (chainMove LColor.r LColor.b 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber75Row8 : TripleComponentParentRow :=
  tripleRow 3544 3536 107 62 112 106 54 112
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber75Row9 : TripleComponentParentRow :=
  tripleRow 3545 3537 107 62 113 106 54 113
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber75Row10 : TripleComponentParentRow :=
  tripleRow 3546 3538 107 62 114 106 54 114
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber75Row11 : TripleComponentParentRow :=
  tripleRow 3547 3539 107 62 115 106 54 115
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber75Row12 : TripleComponentParentRow :=
  tripleRow 3548 3540 107 63 120 106 55 120
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber75Row13 : TripleComponentParentRow :=
  tripleRow 3549 3541 107 63 121 106 55 121
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber75Row14 : TripleComponentParentRow :=
  tripleRow 3550 3542 107 63 122 106 55 122
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber75Row15 : TripleComponentParentRow :=
  tripleRow 3551 3543 107 63 123 106 55 123
    (chainMove LColor.r LColor.b 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber75Rows : List TripleComponentParentRow :=
  [ tttFiber75Row0
  , tttFiber75Row1
  , tttFiber75Row2
  , tttFiber75Row3
  , tttFiber75Row4
  , tttFiber75Row5
  , tttFiber75Row6
  , tttFiber75Row7
  , tttFiber75Row8
  , tttFiber75Row9
  , tttFiber75Row10
  , tttFiber75Row11
  , tttFiber75Row12
  , tttFiber75Row13
  , tttFiber75Row14
  , tttFiber75Row15
  ]

def tttFiber75SourcesCheck : Bool :=
  (tttFiber75Rows.map fun row => row.source) == tttFiber75Expected

theorem tttFiber75SourcesCheck_ok :
    tttFiber75SourcesCheck = true := by
  decide

def tttFiber75RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber75Key tttFiber75Expected
    (listGetD tttFiber75Rows i default)

theorem tttFiber75Row_0_ok : tttFiber75RowCheck 0 = true := by
  decide
theorem tttFiber75Row_1_ok : tttFiber75RowCheck 1 = true := by
  decide
theorem tttFiber75Row_2_ok : tttFiber75RowCheck 2 = true := by
  decide
theorem tttFiber75Row_3_ok : tttFiber75RowCheck 3 = true := by
  decide
theorem tttFiber75Row_4_ok : tttFiber75RowCheck 4 = true := by
  decide
theorem tttFiber75Row_5_ok : tttFiber75RowCheck 5 = true := by
  decide
theorem tttFiber75Row_6_ok : tttFiber75RowCheck 6 = true := by
  decide
theorem tttFiber75Row_7_ok : tttFiber75RowCheck 7 = true := by
  decide
theorem tttFiber75Row_8_ok : tttFiber75RowCheck 8 = true := by
  decide
theorem tttFiber75Row_9_ok : tttFiber75RowCheck 9 = true := by
  decide
theorem tttFiber75Row_10_ok : tttFiber75RowCheck 10 = true := by
  decide
theorem tttFiber75Row_11_ok : tttFiber75RowCheck 11 = true := by
  decide
theorem tttFiber75Row_12_ok : tttFiber75RowCheck 12 = true := by
  decide
theorem tttFiber75Row_13_ok : tttFiber75RowCheck 13 = true := by
  decide
theorem tttFiber75Row_14_ok : tttFiber75RowCheck 14 = true := by
  decide
theorem tttFiber75Row_15_ok : tttFiber75RowCheck 15 = true := by
  decide

def tttFiber75ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber75Rows tttLightMaxParentDepth
    (listGetD tttFiber75Expected i 0) == 3536

theorem tttFiber75Parent_0_ok : tttFiber75ParentCheck 0 = true := by
  decide
theorem tttFiber75Parent_1_ok : tttFiber75ParentCheck 1 = true := by
  decide
theorem tttFiber75Parent_2_ok : tttFiber75ParentCheck 2 = true := by
  decide
theorem tttFiber75Parent_3_ok : tttFiber75ParentCheck 3 = true := by
  decide
theorem tttFiber75Parent_4_ok : tttFiber75ParentCheck 4 = true := by
  decide
theorem tttFiber75Parent_5_ok : tttFiber75ParentCheck 5 = true := by
  decide
theorem tttFiber75Parent_6_ok : tttFiber75ParentCheck 6 = true := by
  decide
theorem tttFiber75Parent_7_ok : tttFiber75ParentCheck 7 = true := by
  decide
theorem tttFiber75Parent_8_ok : tttFiber75ParentCheck 8 = true := by
  decide
theorem tttFiber75Parent_9_ok : tttFiber75ParentCheck 9 = true := by
  decide
theorem tttFiber75Parent_10_ok : tttFiber75ParentCheck 10 = true := by
  decide
theorem tttFiber75Parent_11_ok : tttFiber75ParentCheck 11 = true := by
  decide
theorem tttFiber75Parent_12_ok : tttFiber75ParentCheck 12 = true := by
  decide
theorem tttFiber75Parent_13_ok : tttFiber75ParentCheck 13 = true := by
  decide
theorem tttFiber75Parent_14_ok : tttFiber75ParentCheck 14 = true := by
  decide
theorem tttFiber75Parent_15_ok : tttFiber75ParentCheck 15 = true := by
  decide

def tttFiber75CertificateAudit : Bool :=
  tttFiber75SourcesCheck
    && tttFiber75RowCheck 0
    && tttFiber75RowCheck 1
    && tttFiber75RowCheck 2
    && tttFiber75RowCheck 3
    && tttFiber75RowCheck 4
    && tttFiber75RowCheck 5
    && tttFiber75RowCheck 6
    && tttFiber75RowCheck 7
    && tttFiber75RowCheck 8
    && tttFiber75RowCheck 9
    && tttFiber75RowCheck 10
    && tttFiber75RowCheck 11
    && tttFiber75RowCheck 12
    && tttFiber75RowCheck 13
    && tttFiber75RowCheck 14
    && tttFiber75RowCheck 15
    && tttFiber75ParentCheck 0
    && tttFiber75ParentCheck 1
    && tttFiber75ParentCheck 2
    && tttFiber75ParentCheck 3
    && tttFiber75ParentCheck 4
    && tttFiber75ParentCheck 5
    && tttFiber75ParentCheck 6
    && tttFiber75ParentCheck 7
    && tttFiber75ParentCheck 8
    && tttFiber75ParentCheck 9
    && tttFiber75ParentCheck 10
    && tttFiber75ParentCheck 11
    && tttFiber75ParentCheck 12
    && tttFiber75ParentCheck 13
    && tttFiber75ParentCheck 14
    && tttFiber75ParentCheck 15

theorem tttFiber75CertificateAudit_ok :
    tttFiber75CertificateAudit = true := by
  simp [tttFiber75CertificateAudit,
    tttFiber75SourcesCheck_ok,
    tttFiber75Row_0_ok,
    tttFiber75Row_1_ok,
    tttFiber75Row_2_ok,
    tttFiber75Row_3_ok,
    tttFiber75Row_4_ok,
    tttFiber75Row_5_ok,
    tttFiber75Row_6_ok,
    tttFiber75Row_7_ok,
    tttFiber75Row_8_ok,
    tttFiber75Row_9_ok,
    tttFiber75Row_10_ok,
    tttFiber75Row_11_ok,
    tttFiber75Row_12_ok,
    tttFiber75Row_13_ok,
    tttFiber75Row_14_ok,
    tttFiber75Row_15_ok,
    tttFiber75Parent_0_ok,
    tttFiber75Parent_1_ok,
    tttFiber75Parent_2_ok,
    tttFiber75Parent_3_ok,
    tttFiber75Parent_4_ok,
    tttFiber75Parent_5_ok,
    tttFiber75Parent_6_ok,
    tttFiber75Parent_7_ok,
    tttFiber75Parent_8_ok,
    tttFiber75Parent_9_ok,
    tttFiber75Parent_10_ok,
    tttFiber75Parent_11_ok,
    tttFiber75Parent_12_ok,
    tttFiber75Parent_13_ok,
    tttFiber75Parent_14_ok,
    tttFiber75Parent_15_ok]

def tttFiber77Key : List LColor :=
  [LColor.p, LColor.p, LColor.b, LColor.p]

def tttFiber77Expected : List Nat :=
  [3248, 3249, 3250, 3251, 3252, 3253, 3254, 3255,
   3256, 3257, 3258, 3259, 3260, 3261, 3262, 3263]

def tttFiber77Row0 : TripleComponentParentRow :=
  tripleRow 3248 3248 92 144 84 92 144 84
    default
    []

def tttFiber77Row1 : TripleComponentParentRow :=
  tripleRow 3249 3248 92 144 85 92 144 84
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttFiber77Row2 : TripleComponentParentRow :=
  tripleRow 3250 3248 92 144 86 92 144 84
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber77Row3 : TripleComponentParentRow :=
  tripleRow 3251 3249 92 144 87 92 144 85
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttFiber77Row4 : TripleComponentParentRow :=
  tripleRow 3252 3248 92 145 92 92 144 84
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber77Row5 : TripleComponentParentRow :=
  tripleRow 3253 3249 92 145 93 92 144 85
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber77Row6 : TripleComponentParentRow :=
  tripleRow 3254 3250 92 145 94 92 144 86
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber77Row7 : TripleComponentParentRow :=
  tripleRow 3255 3251 92 145 95 92 144 87
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttFiber77Row8 : TripleComponentParentRow :=
  tripleRow 3256 3248 93 152 84 92 144 84
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber77Row9 : TripleComponentParentRow :=
  tripleRow 3257 3249 93 152 85 92 144 85
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber77Row10 : TripleComponentParentRow :=
  tripleRow 3258 3250 93 152 86 92 144 86
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber77Row11 : TripleComponentParentRow :=
  tripleRow 3259 3251 93 152 87 92 144 87
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber77Row12 : TripleComponentParentRow :=
  tripleRow 3260 3252 93 153 92 92 145 92
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber77Row13 : TripleComponentParentRow :=
  tripleRow 3261 3253 93 153 93 92 145 93
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber77Row14 : TripleComponentParentRow :=
  tripleRow 3262 3254 93 153 94 92 145 94
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber77Row15 : TripleComponentParentRow :=
  tripleRow 3263 3255 93 153 95 92 145 95
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttFiber77Rows : List TripleComponentParentRow :=
  [ tttFiber77Row0
  , tttFiber77Row1
  , tttFiber77Row2
  , tttFiber77Row3
  , tttFiber77Row4
  , tttFiber77Row5
  , tttFiber77Row6
  , tttFiber77Row7
  , tttFiber77Row8
  , tttFiber77Row9
  , tttFiber77Row10
  , tttFiber77Row11
  , tttFiber77Row12
  , tttFiber77Row13
  , tttFiber77Row14
  , tttFiber77Row15
  ]

def tttFiber77SourcesCheck : Bool :=
  (tttFiber77Rows.map fun row => row.source) == tttFiber77Expected

theorem tttFiber77SourcesCheck_ok :
    tttFiber77SourcesCheck = true := by
  decide

def tttFiber77RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttFiber77Key tttFiber77Expected
    (listGetD tttFiber77Rows i default)

theorem tttFiber77Row_0_ok : tttFiber77RowCheck 0 = true := by
  decide
theorem tttFiber77Row_1_ok : tttFiber77RowCheck 1 = true := by
  decide
theorem tttFiber77Row_2_ok : tttFiber77RowCheck 2 = true := by
  decide
theorem tttFiber77Row_3_ok : tttFiber77RowCheck 3 = true := by
  decide
theorem tttFiber77Row_4_ok : tttFiber77RowCheck 4 = true := by
  decide
theorem tttFiber77Row_5_ok : tttFiber77RowCheck 5 = true := by
  decide
theorem tttFiber77Row_6_ok : tttFiber77RowCheck 6 = true := by
  decide
theorem tttFiber77Row_7_ok : tttFiber77RowCheck 7 = true := by
  decide
theorem tttFiber77Row_8_ok : tttFiber77RowCheck 8 = true := by
  decide
theorem tttFiber77Row_9_ok : tttFiber77RowCheck 9 = true := by
  decide
theorem tttFiber77Row_10_ok : tttFiber77RowCheck 10 = true := by
  decide
theorem tttFiber77Row_11_ok : tttFiber77RowCheck 11 = true := by
  decide
theorem tttFiber77Row_12_ok : tttFiber77RowCheck 12 = true := by
  decide
theorem tttFiber77Row_13_ok : tttFiber77RowCheck 13 = true := by
  decide
theorem tttFiber77Row_14_ok : tttFiber77RowCheck 14 = true := by
  decide
theorem tttFiber77Row_15_ok : tttFiber77RowCheck 15 = true := by
  decide

def tttFiber77ParentCheck (i : Nat) : Bool :=
  tripleParentIter tttFiber77Rows tttLightMaxParentDepth
    (listGetD tttFiber77Expected i 0) == 3248

theorem tttFiber77Parent_0_ok : tttFiber77ParentCheck 0 = true := by
  decide
theorem tttFiber77Parent_1_ok : tttFiber77ParentCheck 1 = true := by
  decide
theorem tttFiber77Parent_2_ok : tttFiber77ParentCheck 2 = true := by
  decide
theorem tttFiber77Parent_3_ok : tttFiber77ParentCheck 3 = true := by
  decide
theorem tttFiber77Parent_4_ok : tttFiber77ParentCheck 4 = true := by
  decide
theorem tttFiber77Parent_5_ok : tttFiber77ParentCheck 5 = true := by
  decide
theorem tttFiber77Parent_6_ok : tttFiber77ParentCheck 6 = true := by
  decide
theorem tttFiber77Parent_7_ok : tttFiber77ParentCheck 7 = true := by
  decide
theorem tttFiber77Parent_8_ok : tttFiber77ParentCheck 8 = true := by
  decide
theorem tttFiber77Parent_9_ok : tttFiber77ParentCheck 9 = true := by
  decide
theorem tttFiber77Parent_10_ok : tttFiber77ParentCheck 10 = true := by
  decide
theorem tttFiber77Parent_11_ok : tttFiber77ParentCheck 11 = true := by
  decide
theorem tttFiber77Parent_12_ok : tttFiber77ParentCheck 12 = true := by
  decide
theorem tttFiber77Parent_13_ok : tttFiber77ParentCheck 13 = true := by
  decide
theorem tttFiber77Parent_14_ok : tttFiber77ParentCheck 14 = true := by
  decide
theorem tttFiber77Parent_15_ok : tttFiber77ParentCheck 15 = true := by
  decide

def tttFiber77CertificateAudit : Bool :=
  tttFiber77SourcesCheck
    && tttFiber77RowCheck 0
    && tttFiber77RowCheck 1
    && tttFiber77RowCheck 2
    && tttFiber77RowCheck 3
    && tttFiber77RowCheck 4
    && tttFiber77RowCheck 5
    && tttFiber77RowCheck 6
    && tttFiber77RowCheck 7
    && tttFiber77RowCheck 8
    && tttFiber77RowCheck 9
    && tttFiber77RowCheck 10
    && tttFiber77RowCheck 11
    && tttFiber77RowCheck 12
    && tttFiber77RowCheck 13
    && tttFiber77RowCheck 14
    && tttFiber77RowCheck 15
    && tttFiber77ParentCheck 0
    && tttFiber77ParentCheck 1
    && tttFiber77ParentCheck 2
    && tttFiber77ParentCheck 3
    && tttFiber77ParentCheck 4
    && tttFiber77ParentCheck 5
    && tttFiber77ParentCheck 6
    && tttFiber77ParentCheck 7
    && tttFiber77ParentCheck 8
    && tttFiber77ParentCheck 9
    && tttFiber77ParentCheck 10
    && tttFiber77ParentCheck 11
    && tttFiber77ParentCheck 12
    && tttFiber77ParentCheck 13
    && tttFiber77ParentCheck 14
    && tttFiber77ParentCheck 15

theorem tttFiber77CertificateAudit_ok :
    tttFiber77CertificateAudit = true := by
  simp [tttFiber77CertificateAudit,
    tttFiber77SourcesCheck_ok,
    tttFiber77Row_0_ok,
    tttFiber77Row_1_ok,
    tttFiber77Row_2_ok,
    tttFiber77Row_3_ok,
    tttFiber77Row_4_ok,
    tttFiber77Row_5_ok,
    tttFiber77Row_6_ok,
    tttFiber77Row_7_ok,
    tttFiber77Row_8_ok,
    tttFiber77Row_9_ok,
    tttFiber77Row_10_ok,
    tttFiber77Row_11_ok,
    tttFiber77Row_12_ok,
    tttFiber77Row_13_ok,
    tttFiber77Row_14_ok,
    tttFiber77Row_15_ok,
    tttFiber77Parent_0_ok,
    tttFiber77Parent_1_ok,
    tttFiber77Parent_2_ok,
    tttFiber77Parent_3_ok,
    tttFiber77Parent_4_ok,
    tttFiber77Parent_5_ok,
    tttFiber77Parent_6_ok,
    tttFiber77Parent_7_ok,
    tttFiber77Parent_8_ok,
    tttFiber77Parent_9_ok,
    tttFiber77Parent_10_ok,
    tttFiber77Parent_11_ok,
    tttFiber77Parent_12_ok,
    tttFiber77Parent_13_ok,
    tttFiber77Parent_14_ok,
    tttFiber77Parent_15_ok]

def tttFiber78Key : List LColor :=
  [LColor.p, LColor.p, LColor.p, LColor.r]

def tttFiber78Expected : List Nat :=
  []

def tttFiber78Rows : List TripleComponentParentRow :=
  []

def tttFiber78SourcesCheck : Bool :=
  (tttFiber78Rows.map fun row => row.source) == tttFiber78Expected

theorem tttFiber78SourcesCheck_ok :
    tttFiber78SourcesCheck = true := by
  decide

def tttFiber78CertificateAudit : Bool :=
  tttFiber78SourcesCheck

theorem tttFiber78CertificateAudit_ok :
    tttFiber78CertificateAudit = true := by
  simp [tttFiber78CertificateAudit,
    tttFiber78SourcesCheck_ok]

def tttFiber79Key : List LColor :=
  [LColor.p, LColor.p, LColor.p, LColor.b]

def tttFiber79Expected : List Nat :=
  []

def tttFiber79Rows : List TripleComponentParentRow :=
  []

def tttFiber79SourcesCheck : Bool :=
  (tttFiber79Rows.map fun row => row.source) == tttFiber79Expected

theorem tttFiber79SourcesCheck_ok :
    tttFiber79SourcesCheck = true := by
  decide

def tttFiber79CertificateAudit : Bool :=
  tttFiber79SourcesCheck

theorem tttFiber79CertificateAudit_ok :
    tttFiber79CertificateAudit = true := by
  simp [tttFiber79CertificateAudit,
    tttFiber79SourcesCheck_ok]

def tttFiber80Key : List LColor :=
  [LColor.p, LColor.p, LColor.p, LColor.p]

def tttFiber80Expected : List Nat :=
  []

def tttFiber80Rows : List TripleComponentParentRow :=
  []

def tttFiber80SourcesCheck : Bool :=
  (tttFiber80Rows.map fun row => row.source) == tttFiber80Expected

theorem tttFiber80SourcesCheck_ok :
    tttFiber80SourcesCheck = true := by
  decide

def tttFiber80CertificateAudit : Bool :=
  tttFiber80SourcesCheck

theorem tttFiber80CertificateAudit_ok :
    tttFiber80CertificateAudit = true := by
  simp [tttFiber80CertificateAudit,
    tttFiber80SourcesCheck_ok]

def tttLightComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit
    && tttLightComponentCountsAudit
    && tttFiber0CertificateAudit
    && tttFiber1CertificateAudit
    && tttFiber2CertificateAudit
    && tttFiber3CertificateAudit
    && tttFiber5CertificateAudit
    && tttFiber6CertificateAudit
    && tttFiber7CertificateAudit
    && tttFiber9CertificateAudit
    && tttFiber11CertificateAudit
    && tttFiber12CertificateAudit
    && tttFiber13CertificateAudit
    && tttFiber14CertificateAudit
    && tttFiber15CertificateAudit
    && tttFiber16CertificateAudit
    && tttFiber17CertificateAudit
    && tttFiber18CertificateAudit
    && tttFiber19CertificateAudit
    && tttFiber21CertificateAudit
    && tttFiber22CertificateAudit
    && tttFiber23CertificateAudit
    && tttFiber24CertificateAudit
    && tttFiber25CertificateAudit
    && tttFiber26CertificateAudit
    && tttFiber27CertificateAudit
    && tttFiber28CertificateAudit
    && tttFiber29CertificateAudit
    && tttFiber31CertificateAudit
    && tttFiber32CertificateAudit
    && tttFiber33CertificateAudit
    && tttFiber34CertificateAudit
    && tttFiber35CertificateAudit
    && tttFiber37CertificateAudit
    && tttFiber38CertificateAudit
    && tttFiber39CertificateAudit
    && tttFiber40CertificateAudit
    && tttFiber41CertificateAudit
    && tttFiber42CertificateAudit
    && tttFiber43CertificateAudit
    && tttFiber45CertificateAudit
    && tttFiber46CertificateAudit
    && tttFiber47CertificateAudit
    && tttFiber48CertificateAudit
    && tttFiber49CertificateAudit
    && tttFiber51CertificateAudit
    && tttFiber52CertificateAudit
    && tttFiber53CertificateAudit
    && tttFiber54CertificateAudit
    && tttFiber55CertificateAudit
    && tttFiber56CertificateAudit
    && tttFiber57CertificateAudit
    && tttFiber58CertificateAudit
    && tttFiber59CertificateAudit
    && tttFiber61CertificateAudit
    && tttFiber62CertificateAudit
    && tttFiber63CertificateAudit
    && tttFiber64CertificateAudit
    && tttFiber65CertificateAudit
    && tttFiber66CertificateAudit
    && tttFiber67CertificateAudit
    && tttFiber68CertificateAudit
    && tttFiber69CertificateAudit
    && tttFiber71CertificateAudit
    && tttFiber73CertificateAudit
    && tttFiber74CertificateAudit
    && tttFiber75CertificateAudit
    && tttFiber77CertificateAudit
    && tttFiber78CertificateAudit
    && tttFiber79CertificateAudit
    && tttFiber80CertificateAudit

theorem tttLightComponentCertificateAudit_ok :
    tttLightComponentCertificateAudit = true := by
  simp [tttLightComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLightComponentCountsAudit_ok,
    tttFiber0CertificateAudit_ok,
    tttFiber1CertificateAudit_ok,
    tttFiber2CertificateAudit_ok,
    tttFiber3CertificateAudit_ok,
    tttFiber5CertificateAudit_ok,
    tttFiber6CertificateAudit_ok,
    tttFiber7CertificateAudit_ok,
    tttFiber9CertificateAudit_ok,
    tttFiber11CertificateAudit_ok,
    tttFiber12CertificateAudit_ok,
    tttFiber13CertificateAudit_ok,
    tttFiber14CertificateAudit_ok,
    tttFiber15CertificateAudit_ok,
    tttFiber16CertificateAudit_ok,
    tttFiber17CertificateAudit_ok,
    tttFiber18CertificateAudit_ok,
    tttFiber19CertificateAudit_ok,
    tttFiber21CertificateAudit_ok,
    tttFiber22CertificateAudit_ok,
    tttFiber23CertificateAudit_ok,
    tttFiber24CertificateAudit_ok,
    tttFiber25CertificateAudit_ok,
    tttFiber26CertificateAudit_ok,
    tttFiber27CertificateAudit_ok,
    tttFiber28CertificateAudit_ok,
    tttFiber29CertificateAudit_ok,
    tttFiber31CertificateAudit_ok,
    tttFiber32CertificateAudit_ok,
    tttFiber33CertificateAudit_ok,
    tttFiber34CertificateAudit_ok,
    tttFiber35CertificateAudit_ok,
    tttFiber37CertificateAudit_ok,
    tttFiber38CertificateAudit_ok,
    tttFiber39CertificateAudit_ok,
    tttFiber40CertificateAudit_ok,
    tttFiber41CertificateAudit_ok,
    tttFiber42CertificateAudit_ok,
    tttFiber43CertificateAudit_ok,
    tttFiber45CertificateAudit_ok,
    tttFiber46CertificateAudit_ok,
    tttFiber47CertificateAudit_ok,
    tttFiber48CertificateAudit_ok,
    tttFiber49CertificateAudit_ok,
    tttFiber51CertificateAudit_ok,
    tttFiber52CertificateAudit_ok,
    tttFiber53CertificateAudit_ok,
    tttFiber54CertificateAudit_ok,
    tttFiber55CertificateAudit_ok,
    tttFiber56CertificateAudit_ok,
    tttFiber57CertificateAudit_ok,
    tttFiber58CertificateAudit_ok,
    tttFiber59CertificateAudit_ok,
    tttFiber61CertificateAudit_ok,
    tttFiber62CertificateAudit_ok,
    tttFiber63CertificateAudit_ok,
    tttFiber64CertificateAudit_ok,
    tttFiber65CertificateAudit_ok,
    tttFiber66CertificateAudit_ok,
    tttFiber67CertificateAudit_ok,
    tttFiber68CertificateAudit_ok,
    tttFiber69CertificateAudit_ok,
    tttFiber71CertificateAudit_ok,
    tttFiber73CertificateAudit_ok,
    tttFiber74CertificateAudit_ok,
    tttFiber75CertificateAudit_ok,
    tttFiber77CertificateAudit_ok,
    tttFiber78CertificateAudit_ok,
    tttFiber79CertificateAudit_ok,
    tttFiber80CertificateAudit_ok]

end GoertzelLemma818TripleTauLightComponentCertificate

end Mettapedia.GraphTheory.FourColor
