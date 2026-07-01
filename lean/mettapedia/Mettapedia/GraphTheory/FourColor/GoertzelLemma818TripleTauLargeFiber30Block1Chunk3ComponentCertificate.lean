import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 1 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block1Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block1Chunk3Sources : List Nat :=
  [   112, 113, 114, 115, 116, 117, 118, 119,
   120, 121, 122, 123, 124, 125, 126, 127]

def tttLargeFiber30Row112 : TripleComponentParentRow :=
  tripleRow 112 48 1 110 64 0 102 64
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row113 : TripleComponentParentRow :=
  tripleRow 113 49 1 110 65 0 102 65
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row114 : TripleComponentParentRow :=
  tripleRow 114 50 1 110 66 0 102 66
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row115 : TripleComponentParentRow :=
  tripleRow 115 51 1 110 67 0 102 67
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row116 : TripleComponentParentRow :=
  tripleRow 116 52 1 110 116 0 102 116
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row117 : TripleComponentParentRow :=
  tripleRow 117 53 1 110 117 0 102 117
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row118 : TripleComponentParentRow :=
  tripleRow 118 54 1 110 118 0 102 118
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row119 : TripleComponentParentRow :=
  tripleRow 119 55 1 110 119 0 102 119
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row120 : TripleComponentParentRow :=
  tripleRow 120 56 1 111 72 0 103 72
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row121 : TripleComponentParentRow :=
  tripleRow 121 57 1 111 73 0 103 73
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row122 : TripleComponentParentRow :=
  tripleRow 122 58 1 111 74 0 103 74
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row123 : TripleComponentParentRow :=
  tripleRow 123 59 1 111 75 0 103 75
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row124 : TripleComponentParentRow :=
  tripleRow 124 60 1 111 124 0 103 124
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row125 : TripleComponentParentRow :=
  tripleRow 125 61 1 111 125 0 103 125
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row126 : TripleComponentParentRow :=
  tripleRow 126 62 1 111 126 0 103 126
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row127 : TripleComponentParentRow :=
  tripleRow 127 63 1 111 127 0 103 127
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Block1Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row112
  , tttLargeFiber30Row113
  , tttLargeFiber30Row114
  , tttLargeFiber30Row115
  , tttLargeFiber30Row116
  , tttLargeFiber30Row117
  , tttLargeFiber30Row118
  , tttLargeFiber30Row119
  , tttLargeFiber30Row120
  , tttLargeFiber30Row121
  , tttLargeFiber30Row122
  , tttLargeFiber30Row123
  , tttLargeFiber30Row124
  , tttLargeFiber30Row125
  , tttLargeFiber30Row126
  , tttLargeFiber30Row127
  ]

def tttLargeFiber30Block1Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block1Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block1Chunk3ExpectedContains row.source &&
    tttLargeFiber30Block1Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block1Chunk3SourcesCheck : Bool :=
  (tttLargeFiber30Block1Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber30Block1Chunk3Sources

theorem tttLargeFiber30Block1Chunk3SourcesCheck_ok :
    tttLargeFiber30Block1Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber30Block1Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block1Chunk3RowValid
    (listGetD tttLargeFiber30Block1Chunk3Rows i default)

def tttLargeFiber30Block1Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block1Chunk3Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block1Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block1Chunk3Sources 0 0 == 112
      && tttLargeFiber30ParentOf 112 == 48
      && tttLargeFiber30ParentOf 48 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block1Chunk3Sources 1 0 == 113
      && tttLargeFiber30ParentOf 113 == 49
      && tttLargeFiber30ParentOf 49 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block1Chunk3Sources 2 0 == 114
      && tttLargeFiber30ParentOf 114 == 50
      && tttLargeFiber30ParentOf 50 == 10
      && tttLargeFiber30ParentOf 10 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block1Chunk3Sources 3 0 == 115
      && tttLargeFiber30ParentOf 115 == 51
      && tttLargeFiber30ParentOf 51 == 11
      && tttLargeFiber30ParentOf 11 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block1Chunk3Sources 4 0 == 116
      && tttLargeFiber30ParentOf 116 == 52
      && tttLargeFiber30ParentOf 52 == 12
      && tttLargeFiber30ParentOf 12 == 4
      && tttLargeFiber30ParentOf 4 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block1Chunk3Sources 5 0 == 117
      && tttLargeFiber30ParentOf 117 == 53
      && tttLargeFiber30ParentOf 53 == 13
      && tttLargeFiber30ParentOf 13 == 5
      && tttLargeFiber30ParentOf 5 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block1Chunk3Sources 6 0 == 118
      && tttLargeFiber30ParentOf 118 == 54
      && tttLargeFiber30ParentOf 54 == 14
      && tttLargeFiber30ParentOf 14 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block1Chunk3Sources 7 0 == 119
      && tttLargeFiber30ParentOf 119 == 55
      && tttLargeFiber30ParentOf 55 == 15
      && tttLargeFiber30ParentOf 15 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block1Chunk3Sources 8 0 == 120
      && tttLargeFiber30ParentOf 120 == 56
      && tttLargeFiber30ParentOf 56 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block1Chunk3Sources 9 0 == 121
      && tttLargeFiber30ParentOf 121 == 57
      && tttLargeFiber30ParentOf 57 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block1Chunk3Sources 10 0 == 122
      && tttLargeFiber30ParentOf 122 == 58
      && tttLargeFiber30ParentOf 58 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block1Chunk3Sources 11 0 == 123
      && tttLargeFiber30ParentOf 123 == 59
      && tttLargeFiber30ParentOf 59 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block1Chunk3Sources 12 0 == 124
      && tttLargeFiber30ParentOf 124 == 60
      && tttLargeFiber30ParentOf 60 == 4
      && tttLargeFiber30ParentOf 4 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block1Chunk3Sources 13 0 == 125
      && tttLargeFiber30ParentOf 125 == 61
      && tttLargeFiber30ParentOf 61 == 5
      && tttLargeFiber30ParentOf 5 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block1Chunk3Sources 14 0 == 126
      && tttLargeFiber30ParentOf 126 == 62
      && tttLargeFiber30ParentOf 62 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block1Chunk3Sources 15 0 == 127
      && tttLargeFiber30ParentOf 127 == 63
      && tttLargeFiber30ParentOf 63 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block1Chunk3Row_0_ok :
    tttLargeFiber30Block1Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3Row_1_ok :
    tttLargeFiber30Block1Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3Row_2_ok :
    tttLargeFiber30Block1Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3Row_3_ok :
    tttLargeFiber30Block1Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3Row_4_ok :
    tttLargeFiber30Block1Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3Row_5_ok :
    tttLargeFiber30Block1Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3Row_6_ok :
    tttLargeFiber30Block1Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3Row_7_ok :
    tttLargeFiber30Block1Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3Row_8_ok :
    tttLargeFiber30Block1Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3Row_9_ok :
    tttLargeFiber30Block1Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3Row_10_ok :
    tttLargeFiber30Block1Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3Row_11_ok :
    tttLargeFiber30Block1Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3Row_12_ok :
    tttLargeFiber30Block1Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3Row_13_ok :
    tttLargeFiber30Block1Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3Row_14_ok :
    tttLargeFiber30Block1Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3Row_15_ok :
    tttLargeFiber30Block1Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentMap_0_ok :
    tttLargeFiber30Block1Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentMap_1_ok :
    tttLargeFiber30Block1Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentMap_2_ok :
    tttLargeFiber30Block1Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentMap_3_ok :
    tttLargeFiber30Block1Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentMap_4_ok :
    tttLargeFiber30Block1Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentMap_5_ok :
    tttLargeFiber30Block1Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentMap_6_ok :
    tttLargeFiber30Block1Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentMap_7_ok :
    tttLargeFiber30Block1Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentMap_8_ok :
    tttLargeFiber30Block1Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentMap_9_ok :
    tttLargeFiber30Block1Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentMap_10_ok :
    tttLargeFiber30Block1Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentMap_11_ok :
    tttLargeFiber30Block1Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentMap_12_ok :
    tttLargeFiber30Block1Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentMap_13_ok :
    tttLargeFiber30Block1Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentMap_14_ok :
    tttLargeFiber30Block1Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentMap_15_ok :
    tttLargeFiber30Block1Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentPath_0_ok :
    tttLargeFiber30Block1Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentPath_1_ok :
    tttLargeFiber30Block1Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentPath_2_ok :
    tttLargeFiber30Block1Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentPath_3_ok :
    tttLargeFiber30Block1Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentPath_4_ok :
    tttLargeFiber30Block1Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentPath_5_ok :
    tttLargeFiber30Block1Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentPath_6_ok :
    tttLargeFiber30Block1Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentPath_7_ok :
    tttLargeFiber30Block1Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentPath_8_ok :
    tttLargeFiber30Block1Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentPath_9_ok :
    tttLargeFiber30Block1Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentPath_10_ok :
    tttLargeFiber30Block1Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentPath_11_ok :
    tttLargeFiber30Block1Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentPath_12_ok :
    tttLargeFiber30Block1Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentPath_13_ok :
    tttLargeFiber30Block1Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentPath_14_ok :
    tttLargeFiber30Block1Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block1Chunk3ParentPath_15_ok :
    tttLargeFiber30Block1Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block1Chunk3RowsAudit : Bool :=
  tttLargeFiber30Block1Chunk3RowCheck 0
    && tttLargeFiber30Block1Chunk3RowCheck 1
    && tttLargeFiber30Block1Chunk3RowCheck 2
    && tttLargeFiber30Block1Chunk3RowCheck 3
    && tttLargeFiber30Block1Chunk3RowCheck 4
    && tttLargeFiber30Block1Chunk3RowCheck 5
    && tttLargeFiber30Block1Chunk3RowCheck 6
    && tttLargeFiber30Block1Chunk3RowCheck 7
    && tttLargeFiber30Block1Chunk3RowCheck 8
    && tttLargeFiber30Block1Chunk3RowCheck 9
    && tttLargeFiber30Block1Chunk3RowCheck 10
    && tttLargeFiber30Block1Chunk3RowCheck 11
    && tttLargeFiber30Block1Chunk3RowCheck 12
    && tttLargeFiber30Block1Chunk3RowCheck 13
    && tttLargeFiber30Block1Chunk3RowCheck 14
    && tttLargeFiber30Block1Chunk3RowCheck 15

theorem tttLargeFiber30Block1Chunk3RowsAudit_ok :
    tttLargeFiber30Block1Chunk3RowsAudit = true := by
  simp [tttLargeFiber30Block1Chunk3RowsAudit,
    tttLargeFiber30Block1Chunk3Row_0_ok,
    tttLargeFiber30Block1Chunk3Row_1_ok,
    tttLargeFiber30Block1Chunk3Row_2_ok,
    tttLargeFiber30Block1Chunk3Row_3_ok,
    tttLargeFiber30Block1Chunk3Row_4_ok,
    tttLargeFiber30Block1Chunk3Row_5_ok,
    tttLargeFiber30Block1Chunk3Row_6_ok,
    tttLargeFiber30Block1Chunk3Row_7_ok,
    tttLargeFiber30Block1Chunk3Row_8_ok,
    tttLargeFiber30Block1Chunk3Row_9_ok,
    tttLargeFiber30Block1Chunk3Row_10_ok,
    tttLargeFiber30Block1Chunk3Row_11_ok,
    tttLargeFiber30Block1Chunk3Row_12_ok,
    tttLargeFiber30Block1Chunk3Row_13_ok,
    tttLargeFiber30Block1Chunk3Row_14_ok,
    tttLargeFiber30Block1Chunk3Row_15_ok]

def tttLargeFiber30Block1Chunk3ParentMapAudit : Bool :=
  tttLargeFiber30Block1Chunk3ParentMapCheck 0
    && tttLargeFiber30Block1Chunk3ParentMapCheck 1
    && tttLargeFiber30Block1Chunk3ParentMapCheck 2
    && tttLargeFiber30Block1Chunk3ParentMapCheck 3
    && tttLargeFiber30Block1Chunk3ParentMapCheck 4
    && tttLargeFiber30Block1Chunk3ParentMapCheck 5
    && tttLargeFiber30Block1Chunk3ParentMapCheck 6
    && tttLargeFiber30Block1Chunk3ParentMapCheck 7
    && tttLargeFiber30Block1Chunk3ParentMapCheck 8
    && tttLargeFiber30Block1Chunk3ParentMapCheck 9
    && tttLargeFiber30Block1Chunk3ParentMapCheck 10
    && tttLargeFiber30Block1Chunk3ParentMapCheck 11
    && tttLargeFiber30Block1Chunk3ParentMapCheck 12
    && tttLargeFiber30Block1Chunk3ParentMapCheck 13
    && tttLargeFiber30Block1Chunk3ParentMapCheck 14
    && tttLargeFiber30Block1Chunk3ParentMapCheck 15

theorem tttLargeFiber30Block1Chunk3ParentMapAudit_ok :
    tttLargeFiber30Block1Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber30Block1Chunk3ParentMapAudit,
    tttLargeFiber30Block1Chunk3ParentMap_0_ok,
    tttLargeFiber30Block1Chunk3ParentMap_1_ok,
    tttLargeFiber30Block1Chunk3ParentMap_2_ok,
    tttLargeFiber30Block1Chunk3ParentMap_3_ok,
    tttLargeFiber30Block1Chunk3ParentMap_4_ok,
    tttLargeFiber30Block1Chunk3ParentMap_5_ok,
    tttLargeFiber30Block1Chunk3ParentMap_6_ok,
    tttLargeFiber30Block1Chunk3ParentMap_7_ok,
    tttLargeFiber30Block1Chunk3ParentMap_8_ok,
    tttLargeFiber30Block1Chunk3ParentMap_9_ok,
    tttLargeFiber30Block1Chunk3ParentMap_10_ok,
    tttLargeFiber30Block1Chunk3ParentMap_11_ok,
    tttLargeFiber30Block1Chunk3ParentMap_12_ok,
    tttLargeFiber30Block1Chunk3ParentMap_13_ok,
    tttLargeFiber30Block1Chunk3ParentMap_14_ok,
    tttLargeFiber30Block1Chunk3ParentMap_15_ok]

def tttLargeFiber30Block1Chunk3ParentsAudit : Bool :=
  tttLargeFiber30Block1Chunk3ParentPathCheck 0
    && tttLargeFiber30Block1Chunk3ParentPathCheck 1
    && tttLargeFiber30Block1Chunk3ParentPathCheck 2
    && tttLargeFiber30Block1Chunk3ParentPathCheck 3
    && tttLargeFiber30Block1Chunk3ParentPathCheck 4
    && tttLargeFiber30Block1Chunk3ParentPathCheck 5
    && tttLargeFiber30Block1Chunk3ParentPathCheck 6
    && tttLargeFiber30Block1Chunk3ParentPathCheck 7
    && tttLargeFiber30Block1Chunk3ParentPathCheck 8
    && tttLargeFiber30Block1Chunk3ParentPathCheck 9
    && tttLargeFiber30Block1Chunk3ParentPathCheck 10
    && tttLargeFiber30Block1Chunk3ParentPathCheck 11
    && tttLargeFiber30Block1Chunk3ParentPathCheck 12
    && tttLargeFiber30Block1Chunk3ParentPathCheck 13
    && tttLargeFiber30Block1Chunk3ParentPathCheck 14
    && tttLargeFiber30Block1Chunk3ParentPathCheck 15

theorem tttLargeFiber30Block1Chunk3ParentsAudit_ok :
    tttLargeFiber30Block1Chunk3ParentsAudit = true := by
  simp [tttLargeFiber30Block1Chunk3ParentsAudit,
    tttLargeFiber30Block1Chunk3ParentPath_0_ok,
    tttLargeFiber30Block1Chunk3ParentPath_1_ok,
    tttLargeFiber30Block1Chunk3ParentPath_2_ok,
    tttLargeFiber30Block1Chunk3ParentPath_3_ok,
    tttLargeFiber30Block1Chunk3ParentPath_4_ok,
    tttLargeFiber30Block1Chunk3ParentPath_5_ok,
    tttLargeFiber30Block1Chunk3ParentPath_6_ok,
    tttLargeFiber30Block1Chunk3ParentPath_7_ok,
    tttLargeFiber30Block1Chunk3ParentPath_8_ok,
    tttLargeFiber30Block1Chunk3ParentPath_9_ok,
    tttLargeFiber30Block1Chunk3ParentPath_10_ok,
    tttLargeFiber30Block1Chunk3ParentPath_11_ok,
    tttLargeFiber30Block1Chunk3ParentPath_12_ok,
    tttLargeFiber30Block1Chunk3ParentPath_13_ok,
    tttLargeFiber30Block1Chunk3ParentPath_14_ok,
    tttLargeFiber30Block1Chunk3ParentPath_15_ok]

def tttLargeFiber30Block1Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block1Chunk3SourcesCheck &&
    tttLargeFiber30Block1Chunk3RowsAudit &&
    tttLargeFiber30Block1Chunk3ParentMapAudit &&
    tttLargeFiber30Block1Chunk3ParentsAudit

theorem tttLargeFiber30Block1Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber30Block1Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block1Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block1Chunk3SourcesCheck_ok,
    tttLargeFiber30Block1Chunk3RowsAudit_ok,
    tttLargeFiber30Block1Chunk3ParentMapAudit_ok,
    tttLargeFiber30Block1Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block1Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
