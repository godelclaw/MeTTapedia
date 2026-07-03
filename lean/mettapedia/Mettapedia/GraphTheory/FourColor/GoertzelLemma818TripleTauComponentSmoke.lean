import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818RepresentativeTargets

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: `TTT` representative component smoke check

This module checks one small fixed-input fiber of the non-base representative
word `tau,tau,tau` (`RepresentativeSemanticTarget.ttt`, profile `mode09`).
It is a row-split component-certificate slice for the remaining semantic
target work, not the full `TTT` target audit and not the all-chain `LKR_in`
consequence.
-/

namespace GoertzelLemma818TripleTauComponentSmoke

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

def tttRepresentativeModeSliceAudit : Bool :=
  GoertzelLemma818RepresentativeTargets.targetFrontierWord
      GoertzelLemma818RepresentativeTargets.RepresentativeSemanticTarget.ttt ==
    tttFrontierWord
  && GoertzelLemma818RepresentativeTargets.targetFrontierMode
      GoertzelLemma818RepresentativeTargets.RepresentativeSemanticTarget.ttt ==
    GoertzelLemma818FrontierMode.FrontierMode.mode09
  && GoertzelLemma818FrontierMode.wordMode tttFrontierWord ==
    some GoertzelLemma818FrontierMode.FrontierMode.mode09

theorem tttRepresentativeModeSliceAudit_ok :
    tttRepresentativeModeSliceAudit = true := by
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

def tttFiber3Key : List LColor :=
  [LColor.r, LColor.r, LColor.b, LColor.r]

def tttFiber3Expected : List Nat :=
  [3808, 3809, 3810, 3811, 3812, 3813, 3814, 3815,
    3816, 3817, 3818, 3819, 3820, 3821, 3822, 3823]

def tttFiber3Row0 : TripleComponentParentRow :=
  tripleRow 3808 3808 114 54 112 114 54 112 default []

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

theorem tttFiber3Row_0_ok : tttFiber3RowCheck 0 = true := by decide
theorem tttFiber3Row_1_ok : tttFiber3RowCheck 1 = true := by decide
theorem tttFiber3Row_2_ok : tttFiber3RowCheck 2 = true := by decide
theorem tttFiber3Row_3_ok : tttFiber3RowCheck 3 = true := by decide
theorem tttFiber3Row_4_ok : tttFiber3RowCheck 4 = true := by decide
theorem tttFiber3Row_5_ok : tttFiber3RowCheck 5 = true := by decide
theorem tttFiber3Row_6_ok : tttFiber3RowCheck 6 = true := by decide
theorem tttFiber3Row_7_ok : tttFiber3RowCheck 7 = true := by decide
theorem tttFiber3Row_8_ok : tttFiber3RowCheck 8 = true := by decide
theorem tttFiber3Row_9_ok : tttFiber3RowCheck 9 = true := by decide
theorem tttFiber3Row_10_ok : tttFiber3RowCheck 10 = true := by decide
theorem tttFiber3Row_11_ok : tttFiber3RowCheck 11 = true := by decide
theorem tttFiber3Row_12_ok : tttFiber3RowCheck 12 = true := by decide
theorem tttFiber3Row_13_ok : tttFiber3RowCheck 13 = true := by decide
theorem tttFiber3Row_14_ok : tttFiber3RowCheck 14 = true := by decide
theorem tttFiber3Row_15_ok : tttFiber3RowCheck 15 = true := by decide

def tttFiber3ParentFromRows : List TripleComponentParentRow → Nat → Nat
  | [], i => i
  | row :: rows, i =>
      if row.source == i then row.parent else tttFiber3ParentFromRows rows i

def tttFiber3ParentIter
    (rows : List TripleComponentParentRow) : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i => tttFiber3ParentIter rows n (tttFiber3ParentFromRows rows i)

def tttFiber3ParentCheck (i : Nat) : Bool :=
  tttFiber3ParentIter tttFiber3Rows 6 (listGetD tttFiber3Expected i 0) == 3808

theorem tttFiber3Parent_0_ok : tttFiber3ParentCheck 0 = true := by decide
theorem tttFiber3Parent_1_ok : tttFiber3ParentCheck 1 = true := by decide
theorem tttFiber3Parent_2_ok : tttFiber3ParentCheck 2 = true := by decide
theorem tttFiber3Parent_3_ok : tttFiber3ParentCheck 3 = true := by decide
theorem tttFiber3Parent_4_ok : tttFiber3ParentCheck 4 = true := by decide
theorem tttFiber3Parent_5_ok : tttFiber3ParentCheck 5 = true := by decide
theorem tttFiber3Parent_6_ok : tttFiber3ParentCheck 6 = true := by decide
theorem tttFiber3Parent_7_ok : tttFiber3ParentCheck 7 = true := by decide
theorem tttFiber3Parent_8_ok : tttFiber3ParentCheck 8 = true := by decide
theorem tttFiber3Parent_9_ok : tttFiber3ParentCheck 9 = true := by decide
theorem tttFiber3Parent_10_ok : tttFiber3ParentCheck 10 = true := by decide
theorem tttFiber3Parent_11_ok : tttFiber3ParentCheck 11 = true := by decide
theorem tttFiber3Parent_12_ok : tttFiber3ParentCheck 12 = true := by decide
theorem tttFiber3Parent_13_ok : tttFiber3ParentCheck 13 = true := by decide
theorem tttFiber3Parent_14_ok : tttFiber3ParentCheck 14 = true := by decide
theorem tttFiber3Parent_15_ok : tttFiber3ParentCheck 15 = true := by decide

def tttFiber3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeSliceAudit &&
    tttFiber3SourcesCheck &&
    tttFiber3RowCheck 0 &&
    tttFiber3RowCheck 1 &&
    tttFiber3RowCheck 2 &&
    tttFiber3RowCheck 3 &&
    tttFiber3RowCheck 4 &&
    tttFiber3RowCheck 5 &&
    tttFiber3RowCheck 6 &&
    tttFiber3RowCheck 7 &&
    tttFiber3RowCheck 8 &&
    tttFiber3RowCheck 9 &&
    tttFiber3RowCheck 10 &&
    tttFiber3RowCheck 11 &&
    tttFiber3RowCheck 12 &&
    tttFiber3RowCheck 13 &&
    tttFiber3RowCheck 14 &&
    tttFiber3RowCheck 15 &&
    tttFiber3ParentCheck 0 &&
    tttFiber3ParentCheck 1 &&
    tttFiber3ParentCheck 2 &&
    tttFiber3ParentCheck 3 &&
    tttFiber3ParentCheck 4 &&
    tttFiber3ParentCheck 5 &&
    tttFiber3ParentCheck 6 &&
    tttFiber3ParentCheck 7 &&
    tttFiber3ParentCheck 8 &&
    tttFiber3ParentCheck 9 &&
    tttFiber3ParentCheck 10 &&
    tttFiber3ParentCheck 11 &&
    tttFiber3ParentCheck 12 &&
    tttFiber3ParentCheck 13 &&
    tttFiber3ParentCheck 14 &&
    tttFiber3ParentCheck 15

theorem tttFiber3ComponentCertificateAudit_ok :
    tttFiber3ComponentCertificateAudit = true := by
  simp [tttFiber3ComponentCertificateAudit,
    tttRepresentativeModeSliceAudit_ok,
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

end GoertzelLemma818TripleTauComponentSmoke

end Mettapedia.GraphTheory.FourColor
