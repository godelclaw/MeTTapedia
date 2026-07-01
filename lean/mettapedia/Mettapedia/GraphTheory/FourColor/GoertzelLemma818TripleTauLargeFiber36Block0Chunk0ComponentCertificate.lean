import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 36, block 0 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber36Block0Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber36Data

def tttLargeFiber36Block0Chunk0Sources : List Nat :=
  [   272, 273, 274, 275, 276, 277, 278, 279,
   280, 281, 282, 283, 284, 285, 286, 287]

def tttLargeFiber36Row0 : TripleComponentParentRow :=
  tripleRow 272 272 8 80 80 8 80 80
    default
    []

def tttLargeFiber36Row1 : TripleComponentParentRow :=
  tripleRow 273 272 8 80 81 8 80 80
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber36Row2 : TripleComponentParentRow :=
  tripleRow 274 272 8 80 82 8 80 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row3 : TripleComponentParentRow :=
  tripleRow 275 273 8 80 83 8 80 81
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row4 : TripleComponentParentRow :=
  tripleRow 276 274 8 80 100 8 80 82
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row5 : TripleComponentParentRow :=
  tripleRow 277 279 8 80 101 8 80 103
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row6 : TripleComponentParentRow :=
  tripleRow 278 273 8 80 102 8 80 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber36Row7 : TripleComponentParentRow :=
  tripleRow 279 272 8 80 103 8 80 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber36Row8 : TripleComponentParentRow :=
  tripleRow 280 272 8 81 88 8 80 80
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber36Row9 : TripleComponentParentRow :=
  tripleRow 281 273 8 81 89 8 80 81
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber36Row10 : TripleComponentParentRow :=
  tripleRow 282 274 8 81 90 8 80 82
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber36Row11 : TripleComponentParentRow :=
  tripleRow 283 275 8 81 91 8 80 83
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber36Row12 : TripleComponentParentRow :=
  tripleRow 284 276 8 81 108 8 80 100
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber36Row13 : TripleComponentParentRow :=
  tripleRow 285 277 8 81 109 8 80 101
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber36Row14 : TripleComponentParentRow :=
  tripleRow 286 278 8 81 110 8 80 102
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber36Row15 : TripleComponentParentRow :=
  tripleRow 287 279 8 81 111 8 80 103
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber36Block0Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber36Row0
  , tttLargeFiber36Row1
  , tttLargeFiber36Row2
  , tttLargeFiber36Row3
  , tttLargeFiber36Row4
  , tttLargeFiber36Row5
  , tttLargeFiber36Row6
  , tttLargeFiber36Row7
  , tttLargeFiber36Row8
  , tttLargeFiber36Row9
  , tttLargeFiber36Row10
  , tttLargeFiber36Row11
  , tttLargeFiber36Row12
  , tttLargeFiber36Row13
  , tttLargeFiber36Row14
  , tttLargeFiber36Row15
  ]

def tttLargeFiber36Block0Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (272 <= i) && decide (i < 528)) ||
    (decide (1904 <= i) && decide (i < 2160))

def tttLargeFiber36Block0Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber36Block0Chunk0ExpectedContains row.source &&
    tttLargeFiber36Block0Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber36Key &&
          chainInputKey tttWord t == tttLargeFiber36Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber36Block0Chunk0SourcesCheck : Bool :=
  (tttLargeFiber36Block0Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber36Block0Chunk0Sources

theorem tttLargeFiber36Block0Chunk0SourcesCheck_ok :
    tttLargeFiber36Block0Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber36Block0Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber36Block0Chunk0RowValid
    (listGetD tttLargeFiber36Block0Chunk0Rows i default)

def tttLargeFiber36Block0Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber36Block0Chunk0Rows i default
  row.parent == tttLargeFiber36ParentOf row.source

def tttLargeFiber36Block0Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber36Block0Chunk0Sources 0 0 == 272
      && 272 == tttLargeFiber36Root
      && decide (0 <= tttLargeFiber36MaxParentDepth)
  | 1 => listGetD tttLargeFiber36Block0Chunk0Sources 1 0 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (1 <= tttLargeFiber36MaxParentDepth)
  | 2 => listGetD tttLargeFiber36Block0Chunk0Sources 2 0 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (1 <= tttLargeFiber36MaxParentDepth)
  | 3 => listGetD tttLargeFiber36Block0Chunk0Sources 3 0 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 4 => listGetD tttLargeFiber36Block0Chunk0Sources 4 0 == 276
      && tttLargeFiber36ParentOf 276 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 5 => listGetD tttLargeFiber36Block0Chunk0Sources 5 0 == 277
      && tttLargeFiber36ParentOf 277 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 6 => listGetD tttLargeFiber36Block0Chunk0Sources 6 0 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 7 => listGetD tttLargeFiber36Block0Chunk0Sources 7 0 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (1 <= tttLargeFiber36MaxParentDepth)
  | 8 => listGetD tttLargeFiber36Block0Chunk0Sources 8 0 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (1 <= tttLargeFiber36MaxParentDepth)
  | 9 => listGetD tttLargeFiber36Block0Chunk0Sources 9 0 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 10 => listGetD tttLargeFiber36Block0Chunk0Sources 10 0 == 282
      && tttLargeFiber36ParentOf 282 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 11 => listGetD tttLargeFiber36Block0Chunk0Sources 11 0 == 283
      && tttLargeFiber36ParentOf 283 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 12 => listGetD tttLargeFiber36Block0Chunk0Sources 12 0 == 284
      && tttLargeFiber36ParentOf 284 == 276
      && tttLargeFiber36ParentOf 276 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 13 => listGetD tttLargeFiber36Block0Chunk0Sources 13 0 == 285
      && tttLargeFiber36ParentOf 285 == 277
      && tttLargeFiber36ParentOf 277 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 14 => listGetD tttLargeFiber36Block0Chunk0Sources 14 0 == 286
      && tttLargeFiber36ParentOf 286 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 15 => listGetD tttLargeFiber36Block0Chunk0Sources 15 0 == 287
      && tttLargeFiber36ParentOf 287 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | _ => false

theorem tttLargeFiber36Block0Chunk0Row_0_ok :
    tttLargeFiber36Block0Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0Row_1_ok :
    tttLargeFiber36Block0Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0Row_2_ok :
    tttLargeFiber36Block0Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0Row_3_ok :
    tttLargeFiber36Block0Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0Row_4_ok :
    tttLargeFiber36Block0Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0Row_5_ok :
    tttLargeFiber36Block0Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0Row_6_ok :
    tttLargeFiber36Block0Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0Row_7_ok :
    tttLargeFiber36Block0Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0Row_8_ok :
    tttLargeFiber36Block0Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0Row_9_ok :
    tttLargeFiber36Block0Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0Row_10_ok :
    tttLargeFiber36Block0Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0Row_11_ok :
    tttLargeFiber36Block0Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0Row_12_ok :
    tttLargeFiber36Block0Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0Row_13_ok :
    tttLargeFiber36Block0Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0Row_14_ok :
    tttLargeFiber36Block0Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0Row_15_ok :
    tttLargeFiber36Block0Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentMap_0_ok :
    tttLargeFiber36Block0Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentMap_1_ok :
    tttLargeFiber36Block0Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentMap_2_ok :
    tttLargeFiber36Block0Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentMap_3_ok :
    tttLargeFiber36Block0Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentMap_4_ok :
    tttLargeFiber36Block0Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentMap_5_ok :
    tttLargeFiber36Block0Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentMap_6_ok :
    tttLargeFiber36Block0Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentMap_7_ok :
    tttLargeFiber36Block0Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentMap_8_ok :
    tttLargeFiber36Block0Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentMap_9_ok :
    tttLargeFiber36Block0Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentMap_10_ok :
    tttLargeFiber36Block0Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentMap_11_ok :
    tttLargeFiber36Block0Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentMap_12_ok :
    tttLargeFiber36Block0Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentMap_13_ok :
    tttLargeFiber36Block0Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentMap_14_ok :
    tttLargeFiber36Block0Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentMap_15_ok :
    tttLargeFiber36Block0Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentPath_0_ok :
    tttLargeFiber36Block0Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentPath_1_ok :
    tttLargeFiber36Block0Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentPath_2_ok :
    tttLargeFiber36Block0Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentPath_3_ok :
    tttLargeFiber36Block0Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentPath_4_ok :
    tttLargeFiber36Block0Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentPath_5_ok :
    tttLargeFiber36Block0Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentPath_6_ok :
    tttLargeFiber36Block0Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentPath_7_ok :
    tttLargeFiber36Block0Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentPath_8_ok :
    tttLargeFiber36Block0Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentPath_9_ok :
    tttLargeFiber36Block0Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentPath_10_ok :
    tttLargeFiber36Block0Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentPath_11_ok :
    tttLargeFiber36Block0Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentPath_12_ok :
    tttLargeFiber36Block0Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentPath_13_ok :
    tttLargeFiber36Block0Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentPath_14_ok :
    tttLargeFiber36Block0Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber36Block0Chunk0ParentPath_15_ok :
    tttLargeFiber36Block0Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber36Block0Chunk0RowsAudit : Bool :=
  tttLargeFiber36Block0Chunk0RowCheck 0
    && tttLargeFiber36Block0Chunk0RowCheck 1
    && tttLargeFiber36Block0Chunk0RowCheck 2
    && tttLargeFiber36Block0Chunk0RowCheck 3
    && tttLargeFiber36Block0Chunk0RowCheck 4
    && tttLargeFiber36Block0Chunk0RowCheck 5
    && tttLargeFiber36Block0Chunk0RowCheck 6
    && tttLargeFiber36Block0Chunk0RowCheck 7
    && tttLargeFiber36Block0Chunk0RowCheck 8
    && tttLargeFiber36Block0Chunk0RowCheck 9
    && tttLargeFiber36Block0Chunk0RowCheck 10
    && tttLargeFiber36Block0Chunk0RowCheck 11
    && tttLargeFiber36Block0Chunk0RowCheck 12
    && tttLargeFiber36Block0Chunk0RowCheck 13
    && tttLargeFiber36Block0Chunk0RowCheck 14
    && tttLargeFiber36Block0Chunk0RowCheck 15

theorem tttLargeFiber36Block0Chunk0RowsAudit_ok :
    tttLargeFiber36Block0Chunk0RowsAudit = true := by
  simp [tttLargeFiber36Block0Chunk0RowsAudit,
    tttLargeFiber36Block0Chunk0Row_0_ok,
    tttLargeFiber36Block0Chunk0Row_1_ok,
    tttLargeFiber36Block0Chunk0Row_2_ok,
    tttLargeFiber36Block0Chunk0Row_3_ok,
    tttLargeFiber36Block0Chunk0Row_4_ok,
    tttLargeFiber36Block0Chunk0Row_5_ok,
    tttLargeFiber36Block0Chunk0Row_6_ok,
    tttLargeFiber36Block0Chunk0Row_7_ok,
    tttLargeFiber36Block0Chunk0Row_8_ok,
    tttLargeFiber36Block0Chunk0Row_9_ok,
    tttLargeFiber36Block0Chunk0Row_10_ok,
    tttLargeFiber36Block0Chunk0Row_11_ok,
    tttLargeFiber36Block0Chunk0Row_12_ok,
    tttLargeFiber36Block0Chunk0Row_13_ok,
    tttLargeFiber36Block0Chunk0Row_14_ok,
    tttLargeFiber36Block0Chunk0Row_15_ok]

def tttLargeFiber36Block0Chunk0ParentMapAudit : Bool :=
  tttLargeFiber36Block0Chunk0ParentMapCheck 0
    && tttLargeFiber36Block0Chunk0ParentMapCheck 1
    && tttLargeFiber36Block0Chunk0ParentMapCheck 2
    && tttLargeFiber36Block0Chunk0ParentMapCheck 3
    && tttLargeFiber36Block0Chunk0ParentMapCheck 4
    && tttLargeFiber36Block0Chunk0ParentMapCheck 5
    && tttLargeFiber36Block0Chunk0ParentMapCheck 6
    && tttLargeFiber36Block0Chunk0ParentMapCheck 7
    && tttLargeFiber36Block0Chunk0ParentMapCheck 8
    && tttLargeFiber36Block0Chunk0ParentMapCheck 9
    && tttLargeFiber36Block0Chunk0ParentMapCheck 10
    && tttLargeFiber36Block0Chunk0ParentMapCheck 11
    && tttLargeFiber36Block0Chunk0ParentMapCheck 12
    && tttLargeFiber36Block0Chunk0ParentMapCheck 13
    && tttLargeFiber36Block0Chunk0ParentMapCheck 14
    && tttLargeFiber36Block0Chunk0ParentMapCheck 15

theorem tttLargeFiber36Block0Chunk0ParentMapAudit_ok :
    tttLargeFiber36Block0Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber36Block0Chunk0ParentMapAudit,
    tttLargeFiber36Block0Chunk0ParentMap_0_ok,
    tttLargeFiber36Block0Chunk0ParentMap_1_ok,
    tttLargeFiber36Block0Chunk0ParentMap_2_ok,
    tttLargeFiber36Block0Chunk0ParentMap_3_ok,
    tttLargeFiber36Block0Chunk0ParentMap_4_ok,
    tttLargeFiber36Block0Chunk0ParentMap_5_ok,
    tttLargeFiber36Block0Chunk0ParentMap_6_ok,
    tttLargeFiber36Block0Chunk0ParentMap_7_ok,
    tttLargeFiber36Block0Chunk0ParentMap_8_ok,
    tttLargeFiber36Block0Chunk0ParentMap_9_ok,
    tttLargeFiber36Block0Chunk0ParentMap_10_ok,
    tttLargeFiber36Block0Chunk0ParentMap_11_ok,
    tttLargeFiber36Block0Chunk0ParentMap_12_ok,
    tttLargeFiber36Block0Chunk0ParentMap_13_ok,
    tttLargeFiber36Block0Chunk0ParentMap_14_ok,
    tttLargeFiber36Block0Chunk0ParentMap_15_ok]

def tttLargeFiber36Block0Chunk0ParentsAudit : Bool :=
  tttLargeFiber36Block0Chunk0ParentPathCheck 0
    && tttLargeFiber36Block0Chunk0ParentPathCheck 1
    && tttLargeFiber36Block0Chunk0ParentPathCheck 2
    && tttLargeFiber36Block0Chunk0ParentPathCheck 3
    && tttLargeFiber36Block0Chunk0ParentPathCheck 4
    && tttLargeFiber36Block0Chunk0ParentPathCheck 5
    && tttLargeFiber36Block0Chunk0ParentPathCheck 6
    && tttLargeFiber36Block0Chunk0ParentPathCheck 7
    && tttLargeFiber36Block0Chunk0ParentPathCheck 8
    && tttLargeFiber36Block0Chunk0ParentPathCheck 9
    && tttLargeFiber36Block0Chunk0ParentPathCheck 10
    && tttLargeFiber36Block0Chunk0ParentPathCheck 11
    && tttLargeFiber36Block0Chunk0ParentPathCheck 12
    && tttLargeFiber36Block0Chunk0ParentPathCheck 13
    && tttLargeFiber36Block0Chunk0ParentPathCheck 14
    && tttLargeFiber36Block0Chunk0ParentPathCheck 15

theorem tttLargeFiber36Block0Chunk0ParentsAudit_ok :
    tttLargeFiber36Block0Chunk0ParentsAudit = true := by
  simp [tttLargeFiber36Block0Chunk0ParentsAudit,
    tttLargeFiber36Block0Chunk0ParentPath_0_ok,
    tttLargeFiber36Block0Chunk0ParentPath_1_ok,
    tttLargeFiber36Block0Chunk0ParentPath_2_ok,
    tttLargeFiber36Block0Chunk0ParentPath_3_ok,
    tttLargeFiber36Block0Chunk0ParentPath_4_ok,
    tttLargeFiber36Block0Chunk0ParentPath_5_ok,
    tttLargeFiber36Block0Chunk0ParentPath_6_ok,
    tttLargeFiber36Block0Chunk0ParentPath_7_ok,
    tttLargeFiber36Block0Chunk0ParentPath_8_ok,
    tttLargeFiber36Block0Chunk0ParentPath_9_ok,
    tttLargeFiber36Block0Chunk0ParentPath_10_ok,
    tttLargeFiber36Block0Chunk0ParentPath_11_ok,
    tttLargeFiber36Block0Chunk0ParentPath_12_ok,
    tttLargeFiber36Block0Chunk0ParentPath_13_ok,
    tttLargeFiber36Block0Chunk0ParentPath_14_ok,
    tttLargeFiber36Block0Chunk0ParentPath_15_ok]

def tttLargeFiber36Block0Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber36CountsAudit &&
    tttLargeFiber36Block0Chunk0SourcesCheck &&
    tttLargeFiber36Block0Chunk0RowsAudit &&
    tttLargeFiber36Block0Chunk0ParentMapAudit &&
    tttLargeFiber36Block0Chunk0ParentsAudit

theorem tttLargeFiber36Block0Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber36Block0Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber36Block0Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber36CountsAudit_ok,
    tttLargeFiber36Block0Chunk0SourcesCheck_ok,
    tttLargeFiber36Block0Chunk0RowsAudit_ok,
    tttLargeFiber36Block0Chunk0ParentMapAudit_ok,
    tttLargeFiber36Block0Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber36Block0Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
