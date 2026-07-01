import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 1 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block1Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block1Chunk0Sources : List Nat :=
  [   64, 65, 66, 67, 68, 69, 70, 71,
   72, 73, 74, 75, 76, 77, 78, 79]

def tttLargeFiber30Row64 : TripleComponentParentRow :=
  tripleRow 64 0 1 88 80 0 80 80
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row65 : TripleComponentParentRow :=
  tripleRow 65 1 1 88 81 0 80 81
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row66 : TripleComponentParentRow :=
  tripleRow 66 2 1 88 82 0 80 82
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row67 : TripleComponentParentRow :=
  tripleRow 67 3 1 88 83 0 80 83
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row68 : TripleComponentParentRow :=
  tripleRow 68 4 1 88 100 0 80 100
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row69 : TripleComponentParentRow :=
  tripleRow 69 5 1 88 101 0 80 101
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row70 : TripleComponentParentRow :=
  tripleRow 70 6 1 88 102 0 80 102
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row71 : TripleComponentParentRow :=
  tripleRow 71 7 1 88 103 0 80 103
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row72 : TripleComponentParentRow :=
  tripleRow 72 8 1 89 88 0 81 88
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row73 : TripleComponentParentRow :=
  tripleRow 73 9 1 89 89 0 81 89
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row74 : TripleComponentParentRow :=
  tripleRow 74 10 1 89 90 0 81 90
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row75 : TripleComponentParentRow :=
  tripleRow 75 11 1 89 91 0 81 91
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row76 : TripleComponentParentRow :=
  tripleRow 76 12 1 89 108 0 81 108
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row77 : TripleComponentParentRow :=
  tripleRow 77 13 1 89 109 0 81 109
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row78 : TripleComponentParentRow :=
  tripleRow 78 14 1 89 110 0 81 110
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Row79 : TripleComponentParentRow :=
  tripleRow 79 15 1 89 111 0 81 111
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber30Block1Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row64
  , tttLargeFiber30Row65
  , tttLargeFiber30Row66
  , tttLargeFiber30Row67
  , tttLargeFiber30Row68
  , tttLargeFiber30Row69
  , tttLargeFiber30Row70
  , tttLargeFiber30Row71
  , tttLargeFiber30Row72
  , tttLargeFiber30Row73
  , tttLargeFiber30Row74
  , tttLargeFiber30Row75
  , tttLargeFiber30Row76
  , tttLargeFiber30Row77
  , tttLargeFiber30Row78
  , tttLargeFiber30Row79
  ]

def tttLargeFiber30Block1Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block1Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block1Chunk0ExpectedContains row.source &&
    tttLargeFiber30Block1Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block1Chunk0SourcesCheck : Bool :=
  (tttLargeFiber30Block1Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber30Block1Chunk0Sources

theorem tttLargeFiber30Block1Chunk0SourcesCheck_ok :
    tttLargeFiber30Block1Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber30Block1Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block1Chunk0RowValid
    (listGetD tttLargeFiber30Block1Chunk0Rows i default)

def tttLargeFiber30Block1Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block1Chunk0Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block1Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block1Chunk0Sources 0 0 == 64
      && tttLargeFiber30ParentOf 64 == 0
      && 0 == tttLargeFiber30Root
      && decide (1 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block1Chunk0Sources 1 0 == 65
      && tttLargeFiber30ParentOf 65 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block1Chunk0Sources 2 0 == 66
      && tttLargeFiber30ParentOf 66 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block1Chunk0Sources 3 0 == 67
      && tttLargeFiber30ParentOf 67 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block1Chunk0Sources 4 0 == 68
      && tttLargeFiber30ParentOf 68 == 4
      && tttLargeFiber30ParentOf 4 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block1Chunk0Sources 5 0 == 69
      && tttLargeFiber30ParentOf 69 == 5
      && tttLargeFiber30ParentOf 5 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block1Chunk0Sources 6 0 == 70
      && tttLargeFiber30ParentOf 70 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block1Chunk0Sources 7 0 == 71
      && tttLargeFiber30ParentOf 71 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block1Chunk0Sources 8 0 == 72
      && tttLargeFiber30ParentOf 72 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block1Chunk0Sources 9 0 == 73
      && tttLargeFiber30ParentOf 73 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block1Chunk0Sources 10 0 == 74
      && tttLargeFiber30ParentOf 74 == 10
      && tttLargeFiber30ParentOf 10 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block1Chunk0Sources 11 0 == 75
      && tttLargeFiber30ParentOf 75 == 11
      && tttLargeFiber30ParentOf 11 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block1Chunk0Sources 12 0 == 76
      && tttLargeFiber30ParentOf 76 == 12
      && tttLargeFiber30ParentOf 12 == 4
      && tttLargeFiber30ParentOf 4 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block1Chunk0Sources 13 0 == 77
      && tttLargeFiber30ParentOf 77 == 13
      && tttLargeFiber30ParentOf 13 == 5
      && tttLargeFiber30ParentOf 5 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block1Chunk0Sources 14 0 == 78
      && tttLargeFiber30ParentOf 78 == 14
      && tttLargeFiber30ParentOf 14 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block1Chunk0Sources 15 0 == 79
      && tttLargeFiber30ParentOf 79 == 15
      && tttLargeFiber30ParentOf 15 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block1Chunk0Row_0_ok :
    tttLargeFiber30Block1Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0Row_1_ok :
    tttLargeFiber30Block1Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0Row_2_ok :
    tttLargeFiber30Block1Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0Row_3_ok :
    tttLargeFiber30Block1Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0Row_4_ok :
    tttLargeFiber30Block1Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0Row_5_ok :
    tttLargeFiber30Block1Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0Row_6_ok :
    tttLargeFiber30Block1Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0Row_7_ok :
    tttLargeFiber30Block1Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0Row_8_ok :
    tttLargeFiber30Block1Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0Row_9_ok :
    tttLargeFiber30Block1Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0Row_10_ok :
    tttLargeFiber30Block1Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0Row_11_ok :
    tttLargeFiber30Block1Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0Row_12_ok :
    tttLargeFiber30Block1Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0Row_13_ok :
    tttLargeFiber30Block1Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0Row_14_ok :
    tttLargeFiber30Block1Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0Row_15_ok :
    tttLargeFiber30Block1Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentMap_0_ok :
    tttLargeFiber30Block1Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentMap_1_ok :
    tttLargeFiber30Block1Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentMap_2_ok :
    tttLargeFiber30Block1Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentMap_3_ok :
    tttLargeFiber30Block1Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentMap_4_ok :
    tttLargeFiber30Block1Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentMap_5_ok :
    tttLargeFiber30Block1Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentMap_6_ok :
    tttLargeFiber30Block1Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentMap_7_ok :
    tttLargeFiber30Block1Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentMap_8_ok :
    tttLargeFiber30Block1Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentMap_9_ok :
    tttLargeFiber30Block1Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentMap_10_ok :
    tttLargeFiber30Block1Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentMap_11_ok :
    tttLargeFiber30Block1Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentMap_12_ok :
    tttLargeFiber30Block1Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentMap_13_ok :
    tttLargeFiber30Block1Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentMap_14_ok :
    tttLargeFiber30Block1Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentMap_15_ok :
    tttLargeFiber30Block1Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentPath_0_ok :
    tttLargeFiber30Block1Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentPath_1_ok :
    tttLargeFiber30Block1Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentPath_2_ok :
    tttLargeFiber30Block1Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentPath_3_ok :
    tttLargeFiber30Block1Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentPath_4_ok :
    tttLargeFiber30Block1Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentPath_5_ok :
    tttLargeFiber30Block1Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentPath_6_ok :
    tttLargeFiber30Block1Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentPath_7_ok :
    tttLargeFiber30Block1Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentPath_8_ok :
    tttLargeFiber30Block1Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentPath_9_ok :
    tttLargeFiber30Block1Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentPath_10_ok :
    tttLargeFiber30Block1Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentPath_11_ok :
    tttLargeFiber30Block1Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentPath_12_ok :
    tttLargeFiber30Block1Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentPath_13_ok :
    tttLargeFiber30Block1Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentPath_14_ok :
    tttLargeFiber30Block1Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block1Chunk0ParentPath_15_ok :
    tttLargeFiber30Block1Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block1Chunk0RowsAudit : Bool :=
  tttLargeFiber30Block1Chunk0RowCheck 0
    && tttLargeFiber30Block1Chunk0RowCheck 1
    && tttLargeFiber30Block1Chunk0RowCheck 2
    && tttLargeFiber30Block1Chunk0RowCheck 3
    && tttLargeFiber30Block1Chunk0RowCheck 4
    && tttLargeFiber30Block1Chunk0RowCheck 5
    && tttLargeFiber30Block1Chunk0RowCheck 6
    && tttLargeFiber30Block1Chunk0RowCheck 7
    && tttLargeFiber30Block1Chunk0RowCheck 8
    && tttLargeFiber30Block1Chunk0RowCheck 9
    && tttLargeFiber30Block1Chunk0RowCheck 10
    && tttLargeFiber30Block1Chunk0RowCheck 11
    && tttLargeFiber30Block1Chunk0RowCheck 12
    && tttLargeFiber30Block1Chunk0RowCheck 13
    && tttLargeFiber30Block1Chunk0RowCheck 14
    && tttLargeFiber30Block1Chunk0RowCheck 15

theorem tttLargeFiber30Block1Chunk0RowsAudit_ok :
    tttLargeFiber30Block1Chunk0RowsAudit = true := by
  simp [tttLargeFiber30Block1Chunk0RowsAudit,
    tttLargeFiber30Block1Chunk0Row_0_ok,
    tttLargeFiber30Block1Chunk0Row_1_ok,
    tttLargeFiber30Block1Chunk0Row_2_ok,
    tttLargeFiber30Block1Chunk0Row_3_ok,
    tttLargeFiber30Block1Chunk0Row_4_ok,
    tttLargeFiber30Block1Chunk0Row_5_ok,
    tttLargeFiber30Block1Chunk0Row_6_ok,
    tttLargeFiber30Block1Chunk0Row_7_ok,
    tttLargeFiber30Block1Chunk0Row_8_ok,
    tttLargeFiber30Block1Chunk0Row_9_ok,
    tttLargeFiber30Block1Chunk0Row_10_ok,
    tttLargeFiber30Block1Chunk0Row_11_ok,
    tttLargeFiber30Block1Chunk0Row_12_ok,
    tttLargeFiber30Block1Chunk0Row_13_ok,
    tttLargeFiber30Block1Chunk0Row_14_ok,
    tttLargeFiber30Block1Chunk0Row_15_ok]

def tttLargeFiber30Block1Chunk0ParentMapAudit : Bool :=
  tttLargeFiber30Block1Chunk0ParentMapCheck 0
    && tttLargeFiber30Block1Chunk0ParentMapCheck 1
    && tttLargeFiber30Block1Chunk0ParentMapCheck 2
    && tttLargeFiber30Block1Chunk0ParentMapCheck 3
    && tttLargeFiber30Block1Chunk0ParentMapCheck 4
    && tttLargeFiber30Block1Chunk0ParentMapCheck 5
    && tttLargeFiber30Block1Chunk0ParentMapCheck 6
    && tttLargeFiber30Block1Chunk0ParentMapCheck 7
    && tttLargeFiber30Block1Chunk0ParentMapCheck 8
    && tttLargeFiber30Block1Chunk0ParentMapCheck 9
    && tttLargeFiber30Block1Chunk0ParentMapCheck 10
    && tttLargeFiber30Block1Chunk0ParentMapCheck 11
    && tttLargeFiber30Block1Chunk0ParentMapCheck 12
    && tttLargeFiber30Block1Chunk0ParentMapCheck 13
    && tttLargeFiber30Block1Chunk0ParentMapCheck 14
    && tttLargeFiber30Block1Chunk0ParentMapCheck 15

theorem tttLargeFiber30Block1Chunk0ParentMapAudit_ok :
    tttLargeFiber30Block1Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber30Block1Chunk0ParentMapAudit,
    tttLargeFiber30Block1Chunk0ParentMap_0_ok,
    tttLargeFiber30Block1Chunk0ParentMap_1_ok,
    tttLargeFiber30Block1Chunk0ParentMap_2_ok,
    tttLargeFiber30Block1Chunk0ParentMap_3_ok,
    tttLargeFiber30Block1Chunk0ParentMap_4_ok,
    tttLargeFiber30Block1Chunk0ParentMap_5_ok,
    tttLargeFiber30Block1Chunk0ParentMap_6_ok,
    tttLargeFiber30Block1Chunk0ParentMap_7_ok,
    tttLargeFiber30Block1Chunk0ParentMap_8_ok,
    tttLargeFiber30Block1Chunk0ParentMap_9_ok,
    tttLargeFiber30Block1Chunk0ParentMap_10_ok,
    tttLargeFiber30Block1Chunk0ParentMap_11_ok,
    tttLargeFiber30Block1Chunk0ParentMap_12_ok,
    tttLargeFiber30Block1Chunk0ParentMap_13_ok,
    tttLargeFiber30Block1Chunk0ParentMap_14_ok,
    tttLargeFiber30Block1Chunk0ParentMap_15_ok]

def tttLargeFiber30Block1Chunk0ParentsAudit : Bool :=
  tttLargeFiber30Block1Chunk0ParentPathCheck 0
    && tttLargeFiber30Block1Chunk0ParentPathCheck 1
    && tttLargeFiber30Block1Chunk0ParentPathCheck 2
    && tttLargeFiber30Block1Chunk0ParentPathCheck 3
    && tttLargeFiber30Block1Chunk0ParentPathCheck 4
    && tttLargeFiber30Block1Chunk0ParentPathCheck 5
    && tttLargeFiber30Block1Chunk0ParentPathCheck 6
    && tttLargeFiber30Block1Chunk0ParentPathCheck 7
    && tttLargeFiber30Block1Chunk0ParentPathCheck 8
    && tttLargeFiber30Block1Chunk0ParentPathCheck 9
    && tttLargeFiber30Block1Chunk0ParentPathCheck 10
    && tttLargeFiber30Block1Chunk0ParentPathCheck 11
    && tttLargeFiber30Block1Chunk0ParentPathCheck 12
    && tttLargeFiber30Block1Chunk0ParentPathCheck 13
    && tttLargeFiber30Block1Chunk0ParentPathCheck 14
    && tttLargeFiber30Block1Chunk0ParentPathCheck 15

theorem tttLargeFiber30Block1Chunk0ParentsAudit_ok :
    tttLargeFiber30Block1Chunk0ParentsAudit = true := by
  simp [tttLargeFiber30Block1Chunk0ParentsAudit,
    tttLargeFiber30Block1Chunk0ParentPath_0_ok,
    tttLargeFiber30Block1Chunk0ParentPath_1_ok,
    tttLargeFiber30Block1Chunk0ParentPath_2_ok,
    tttLargeFiber30Block1Chunk0ParentPath_3_ok,
    tttLargeFiber30Block1Chunk0ParentPath_4_ok,
    tttLargeFiber30Block1Chunk0ParentPath_5_ok,
    tttLargeFiber30Block1Chunk0ParentPath_6_ok,
    tttLargeFiber30Block1Chunk0ParentPath_7_ok,
    tttLargeFiber30Block1Chunk0ParentPath_8_ok,
    tttLargeFiber30Block1Chunk0ParentPath_9_ok,
    tttLargeFiber30Block1Chunk0ParentPath_10_ok,
    tttLargeFiber30Block1Chunk0ParentPath_11_ok,
    tttLargeFiber30Block1Chunk0ParentPath_12_ok,
    tttLargeFiber30Block1Chunk0ParentPath_13_ok,
    tttLargeFiber30Block1Chunk0ParentPath_14_ok,
    tttLargeFiber30Block1Chunk0ParentPath_15_ok]

def tttLargeFiber30Block1Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block1Chunk0SourcesCheck &&
    tttLargeFiber30Block1Chunk0RowsAudit &&
    tttLargeFiber30Block1Chunk0ParentMapAudit &&
    tttLargeFiber30Block1Chunk0ParentsAudit

theorem tttLargeFiber30Block1Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber30Block1Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block1Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block1Chunk0SourcesCheck_ok,
    tttLargeFiber30Block1Chunk0RowsAudit_ok,
    tttLargeFiber30Block1Chunk0ParentMapAudit_ok,
    tttLargeFiber30Block1Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block1Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
