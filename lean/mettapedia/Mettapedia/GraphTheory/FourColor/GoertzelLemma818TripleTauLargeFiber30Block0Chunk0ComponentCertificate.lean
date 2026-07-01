import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 0 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block0Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block0Chunk0Sources : List Nat :=
  [   0, 1, 2, 3, 4, 5, 6, 7,
   8, 9, 10, 11, 12, 13, 14, 15]

def tttLargeFiber30Row0 : TripleComponentParentRow :=
  tripleRow 0 0 0 80 80 0 80 80
    default
    []

def tttLargeFiber30Row1 : TripleComponentParentRow :=
  tripleRow 1 0 0 80 81 0 80 80
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber30Row2 : TripleComponentParentRow :=
  tripleRow 2 0 0 80 82 0 80 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row3 : TripleComponentParentRow :=
  tripleRow 3 1 0 80 83 0 80 81
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row4 : TripleComponentParentRow :=
  tripleRow 4 2 0 80 100 0 80 82
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row5 : TripleComponentParentRow :=
  tripleRow 5 7 0 80 101 0 80 103
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row6 : TripleComponentParentRow :=
  tripleRow 6 1 0 80 102 0 80 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber30Row7 : TripleComponentParentRow :=
  tripleRow 7 0 0 80 103 0 80 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber30Row8 : TripleComponentParentRow :=
  tripleRow 8 0 0 81 88 0 80 80
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber30Row9 : TripleComponentParentRow :=
  tripleRow 9 1 0 81 89 0 80 81
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber30Row10 : TripleComponentParentRow :=
  tripleRow 10 2 0 81 90 0 80 82
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber30Row11 : TripleComponentParentRow :=
  tripleRow 11 3 0 81 91 0 80 83
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber30Row12 : TripleComponentParentRow :=
  tripleRow 12 4 0 81 108 0 80 100
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber30Row13 : TripleComponentParentRow :=
  tripleRow 13 5 0 81 109 0 80 101
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber30Row14 : TripleComponentParentRow :=
  tripleRow 14 6 0 81 110 0 80 102
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber30Row15 : TripleComponentParentRow :=
  tripleRow 15 7 0 81 111 0 80 103
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber30Block0Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row0
  , tttLargeFiber30Row1
  , tttLargeFiber30Row2
  , tttLargeFiber30Row3
  , tttLargeFiber30Row4
  , tttLargeFiber30Row5
  , tttLargeFiber30Row6
  , tttLargeFiber30Row7
  , tttLargeFiber30Row8
  , tttLargeFiber30Row9
  , tttLargeFiber30Row10
  , tttLargeFiber30Row11
  , tttLargeFiber30Row12
  , tttLargeFiber30Row13
  , tttLargeFiber30Row14
  , tttLargeFiber30Row15
  ]

def tttLargeFiber30Block0Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block0Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block0Chunk0ExpectedContains row.source &&
    tttLargeFiber30Block0Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block0Chunk0SourcesCheck : Bool :=
  (tttLargeFiber30Block0Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber30Block0Chunk0Sources

theorem tttLargeFiber30Block0Chunk0SourcesCheck_ok :
    tttLargeFiber30Block0Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber30Block0Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block0Chunk0RowValid
    (listGetD tttLargeFiber30Block0Chunk0Rows i default)

def tttLargeFiber30Block0Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block0Chunk0Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block0Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block0Chunk0Sources 0 0 == 0
      && 0 == tttLargeFiber30Root
      && decide (0 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block0Chunk0Sources 1 0 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (1 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block0Chunk0Sources 2 0 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (1 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block0Chunk0Sources 3 0 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block0Chunk0Sources 4 0 == 4
      && tttLargeFiber30ParentOf 4 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block0Chunk0Sources 5 0 == 5
      && tttLargeFiber30ParentOf 5 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block0Chunk0Sources 6 0 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block0Chunk0Sources 7 0 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (1 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block0Chunk0Sources 8 0 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (1 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block0Chunk0Sources 9 0 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block0Chunk0Sources 10 0 == 10
      && tttLargeFiber30ParentOf 10 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block0Chunk0Sources 11 0 == 11
      && tttLargeFiber30ParentOf 11 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block0Chunk0Sources 12 0 == 12
      && tttLargeFiber30ParentOf 12 == 4
      && tttLargeFiber30ParentOf 4 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block0Chunk0Sources 13 0 == 13
      && tttLargeFiber30ParentOf 13 == 5
      && tttLargeFiber30ParentOf 5 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block0Chunk0Sources 14 0 == 14
      && tttLargeFiber30ParentOf 14 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block0Chunk0Sources 15 0 == 15
      && tttLargeFiber30ParentOf 15 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block0Chunk0Row_0_ok :
    tttLargeFiber30Block0Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0Row_1_ok :
    tttLargeFiber30Block0Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0Row_2_ok :
    tttLargeFiber30Block0Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0Row_3_ok :
    tttLargeFiber30Block0Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0Row_4_ok :
    tttLargeFiber30Block0Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0Row_5_ok :
    tttLargeFiber30Block0Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0Row_6_ok :
    tttLargeFiber30Block0Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0Row_7_ok :
    tttLargeFiber30Block0Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0Row_8_ok :
    tttLargeFiber30Block0Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0Row_9_ok :
    tttLargeFiber30Block0Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0Row_10_ok :
    tttLargeFiber30Block0Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0Row_11_ok :
    tttLargeFiber30Block0Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0Row_12_ok :
    tttLargeFiber30Block0Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0Row_13_ok :
    tttLargeFiber30Block0Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0Row_14_ok :
    tttLargeFiber30Block0Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0Row_15_ok :
    tttLargeFiber30Block0Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentMap_0_ok :
    tttLargeFiber30Block0Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentMap_1_ok :
    tttLargeFiber30Block0Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentMap_2_ok :
    tttLargeFiber30Block0Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentMap_3_ok :
    tttLargeFiber30Block0Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentMap_4_ok :
    tttLargeFiber30Block0Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentMap_5_ok :
    tttLargeFiber30Block0Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentMap_6_ok :
    tttLargeFiber30Block0Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentMap_7_ok :
    tttLargeFiber30Block0Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentMap_8_ok :
    tttLargeFiber30Block0Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentMap_9_ok :
    tttLargeFiber30Block0Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentMap_10_ok :
    tttLargeFiber30Block0Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentMap_11_ok :
    tttLargeFiber30Block0Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentMap_12_ok :
    tttLargeFiber30Block0Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentMap_13_ok :
    tttLargeFiber30Block0Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentMap_14_ok :
    tttLargeFiber30Block0Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentMap_15_ok :
    tttLargeFiber30Block0Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentPath_0_ok :
    tttLargeFiber30Block0Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentPath_1_ok :
    tttLargeFiber30Block0Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentPath_2_ok :
    tttLargeFiber30Block0Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentPath_3_ok :
    tttLargeFiber30Block0Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentPath_4_ok :
    tttLargeFiber30Block0Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentPath_5_ok :
    tttLargeFiber30Block0Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentPath_6_ok :
    tttLargeFiber30Block0Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentPath_7_ok :
    tttLargeFiber30Block0Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentPath_8_ok :
    tttLargeFiber30Block0Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentPath_9_ok :
    tttLargeFiber30Block0Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentPath_10_ok :
    tttLargeFiber30Block0Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentPath_11_ok :
    tttLargeFiber30Block0Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentPath_12_ok :
    tttLargeFiber30Block0Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentPath_13_ok :
    tttLargeFiber30Block0Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentPath_14_ok :
    tttLargeFiber30Block0Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block0Chunk0ParentPath_15_ok :
    tttLargeFiber30Block0Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block0Chunk0RowsAudit : Bool :=
  tttLargeFiber30Block0Chunk0RowCheck 0
    && tttLargeFiber30Block0Chunk0RowCheck 1
    && tttLargeFiber30Block0Chunk0RowCheck 2
    && tttLargeFiber30Block0Chunk0RowCheck 3
    && tttLargeFiber30Block0Chunk0RowCheck 4
    && tttLargeFiber30Block0Chunk0RowCheck 5
    && tttLargeFiber30Block0Chunk0RowCheck 6
    && tttLargeFiber30Block0Chunk0RowCheck 7
    && tttLargeFiber30Block0Chunk0RowCheck 8
    && tttLargeFiber30Block0Chunk0RowCheck 9
    && tttLargeFiber30Block0Chunk0RowCheck 10
    && tttLargeFiber30Block0Chunk0RowCheck 11
    && tttLargeFiber30Block0Chunk0RowCheck 12
    && tttLargeFiber30Block0Chunk0RowCheck 13
    && tttLargeFiber30Block0Chunk0RowCheck 14
    && tttLargeFiber30Block0Chunk0RowCheck 15

theorem tttLargeFiber30Block0Chunk0RowsAudit_ok :
    tttLargeFiber30Block0Chunk0RowsAudit = true := by
  simp [tttLargeFiber30Block0Chunk0RowsAudit,
    tttLargeFiber30Block0Chunk0Row_0_ok,
    tttLargeFiber30Block0Chunk0Row_1_ok,
    tttLargeFiber30Block0Chunk0Row_2_ok,
    tttLargeFiber30Block0Chunk0Row_3_ok,
    tttLargeFiber30Block0Chunk0Row_4_ok,
    tttLargeFiber30Block0Chunk0Row_5_ok,
    tttLargeFiber30Block0Chunk0Row_6_ok,
    tttLargeFiber30Block0Chunk0Row_7_ok,
    tttLargeFiber30Block0Chunk0Row_8_ok,
    tttLargeFiber30Block0Chunk0Row_9_ok,
    tttLargeFiber30Block0Chunk0Row_10_ok,
    tttLargeFiber30Block0Chunk0Row_11_ok,
    tttLargeFiber30Block0Chunk0Row_12_ok,
    tttLargeFiber30Block0Chunk0Row_13_ok,
    tttLargeFiber30Block0Chunk0Row_14_ok,
    tttLargeFiber30Block0Chunk0Row_15_ok]

def tttLargeFiber30Block0Chunk0ParentMapAudit : Bool :=
  tttLargeFiber30Block0Chunk0ParentMapCheck 0
    && tttLargeFiber30Block0Chunk0ParentMapCheck 1
    && tttLargeFiber30Block0Chunk0ParentMapCheck 2
    && tttLargeFiber30Block0Chunk0ParentMapCheck 3
    && tttLargeFiber30Block0Chunk0ParentMapCheck 4
    && tttLargeFiber30Block0Chunk0ParentMapCheck 5
    && tttLargeFiber30Block0Chunk0ParentMapCheck 6
    && tttLargeFiber30Block0Chunk0ParentMapCheck 7
    && tttLargeFiber30Block0Chunk0ParentMapCheck 8
    && tttLargeFiber30Block0Chunk0ParentMapCheck 9
    && tttLargeFiber30Block0Chunk0ParentMapCheck 10
    && tttLargeFiber30Block0Chunk0ParentMapCheck 11
    && tttLargeFiber30Block0Chunk0ParentMapCheck 12
    && tttLargeFiber30Block0Chunk0ParentMapCheck 13
    && tttLargeFiber30Block0Chunk0ParentMapCheck 14
    && tttLargeFiber30Block0Chunk0ParentMapCheck 15

theorem tttLargeFiber30Block0Chunk0ParentMapAudit_ok :
    tttLargeFiber30Block0Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber30Block0Chunk0ParentMapAudit,
    tttLargeFiber30Block0Chunk0ParentMap_0_ok,
    tttLargeFiber30Block0Chunk0ParentMap_1_ok,
    tttLargeFiber30Block0Chunk0ParentMap_2_ok,
    tttLargeFiber30Block0Chunk0ParentMap_3_ok,
    tttLargeFiber30Block0Chunk0ParentMap_4_ok,
    tttLargeFiber30Block0Chunk0ParentMap_5_ok,
    tttLargeFiber30Block0Chunk0ParentMap_6_ok,
    tttLargeFiber30Block0Chunk0ParentMap_7_ok,
    tttLargeFiber30Block0Chunk0ParentMap_8_ok,
    tttLargeFiber30Block0Chunk0ParentMap_9_ok,
    tttLargeFiber30Block0Chunk0ParentMap_10_ok,
    tttLargeFiber30Block0Chunk0ParentMap_11_ok,
    tttLargeFiber30Block0Chunk0ParentMap_12_ok,
    tttLargeFiber30Block0Chunk0ParentMap_13_ok,
    tttLargeFiber30Block0Chunk0ParentMap_14_ok,
    tttLargeFiber30Block0Chunk0ParentMap_15_ok]

def tttLargeFiber30Block0Chunk0ParentsAudit : Bool :=
  tttLargeFiber30Block0Chunk0ParentPathCheck 0
    && tttLargeFiber30Block0Chunk0ParentPathCheck 1
    && tttLargeFiber30Block0Chunk0ParentPathCheck 2
    && tttLargeFiber30Block0Chunk0ParentPathCheck 3
    && tttLargeFiber30Block0Chunk0ParentPathCheck 4
    && tttLargeFiber30Block0Chunk0ParentPathCheck 5
    && tttLargeFiber30Block0Chunk0ParentPathCheck 6
    && tttLargeFiber30Block0Chunk0ParentPathCheck 7
    && tttLargeFiber30Block0Chunk0ParentPathCheck 8
    && tttLargeFiber30Block0Chunk0ParentPathCheck 9
    && tttLargeFiber30Block0Chunk0ParentPathCheck 10
    && tttLargeFiber30Block0Chunk0ParentPathCheck 11
    && tttLargeFiber30Block0Chunk0ParentPathCheck 12
    && tttLargeFiber30Block0Chunk0ParentPathCheck 13
    && tttLargeFiber30Block0Chunk0ParentPathCheck 14
    && tttLargeFiber30Block0Chunk0ParentPathCheck 15

theorem tttLargeFiber30Block0Chunk0ParentsAudit_ok :
    tttLargeFiber30Block0Chunk0ParentsAudit = true := by
  simp [tttLargeFiber30Block0Chunk0ParentsAudit,
    tttLargeFiber30Block0Chunk0ParentPath_0_ok,
    tttLargeFiber30Block0Chunk0ParentPath_1_ok,
    tttLargeFiber30Block0Chunk0ParentPath_2_ok,
    tttLargeFiber30Block0Chunk0ParentPath_3_ok,
    tttLargeFiber30Block0Chunk0ParentPath_4_ok,
    tttLargeFiber30Block0Chunk0ParentPath_5_ok,
    tttLargeFiber30Block0Chunk0ParentPath_6_ok,
    tttLargeFiber30Block0Chunk0ParentPath_7_ok,
    tttLargeFiber30Block0Chunk0ParentPath_8_ok,
    tttLargeFiber30Block0Chunk0ParentPath_9_ok,
    tttLargeFiber30Block0Chunk0ParentPath_10_ok,
    tttLargeFiber30Block0Chunk0ParentPath_11_ok,
    tttLargeFiber30Block0Chunk0ParentPath_12_ok,
    tttLargeFiber30Block0Chunk0ParentPath_13_ok,
    tttLargeFiber30Block0Chunk0ParentPath_14_ok,
    tttLargeFiber30Block0Chunk0ParentPath_15_ok]

def tttLargeFiber30Block0Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block0Chunk0SourcesCheck &&
    tttLargeFiber30Block0Chunk0RowsAudit &&
    tttLargeFiber30Block0Chunk0ParentMapAudit &&
    tttLargeFiber30Block0Chunk0ParentsAudit

theorem tttLargeFiber30Block0Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber30Block0Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block0Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block0Chunk0SourcesCheck_ok,
    tttLargeFiber30Block0Chunk0RowsAudit_ok,
    tttLargeFiber30Block0Chunk0ParentMapAudit_ok,
    tttLargeFiber30Block0Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block0Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
