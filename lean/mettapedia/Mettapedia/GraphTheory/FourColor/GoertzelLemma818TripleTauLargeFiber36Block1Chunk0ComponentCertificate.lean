import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 36, block 1 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber36Block1Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber36Data

def tttLargeFiber36Block1Chunk0Sources : List Nat :=
  [   336, 337, 338, 339, 340, 341, 342, 343,
   344, 345, 346, 347, 348, 349, 350, 351]

def tttLargeFiber36Row64 : TripleComponentParentRow :=
  tripleRow 336 272 9 88 80 8 80 80
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row65 : TripleComponentParentRow :=
  tripleRow 337 273 9 88 81 8 80 81
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row66 : TripleComponentParentRow :=
  tripleRow 338 274 9 88 82 8 80 82
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row67 : TripleComponentParentRow :=
  tripleRow 339 275 9 88 83 8 80 83
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row68 : TripleComponentParentRow :=
  tripleRow 340 276 9 88 100 8 80 100
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row69 : TripleComponentParentRow :=
  tripleRow 341 277 9 88 101 8 80 101
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row70 : TripleComponentParentRow :=
  tripleRow 342 278 9 88 102 8 80 102
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row71 : TripleComponentParentRow :=
  tripleRow 343 279 9 88 103 8 80 103
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row72 : TripleComponentParentRow :=
  tripleRow 344 280 9 89 88 8 81 88
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row73 : TripleComponentParentRow :=
  tripleRow 345 281 9 89 89 8 81 89
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row74 : TripleComponentParentRow :=
  tripleRow 346 282 9 89 90 8 81 90
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row75 : TripleComponentParentRow :=
  tripleRow 347 283 9 89 91 8 81 91
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row76 : TripleComponentParentRow :=
  tripleRow 348 284 9 89 108 8 81 108
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row77 : TripleComponentParentRow :=
  tripleRow 349 285 9 89 109 8 81 109
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row78 : TripleComponentParentRow :=
  tripleRow 350 286 9 89 110 8 81 110
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row79 : TripleComponentParentRow :=
  tripleRow 351 287 9 89 111 8 81 111
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Block1Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber36Row64
  , tttLargeFiber36Row65
  , tttLargeFiber36Row66
  , tttLargeFiber36Row67
  , tttLargeFiber36Row68
  , tttLargeFiber36Row69
  , tttLargeFiber36Row70
  , tttLargeFiber36Row71
  , tttLargeFiber36Row72
  , tttLargeFiber36Row73
  , tttLargeFiber36Row74
  , tttLargeFiber36Row75
  , tttLargeFiber36Row76
  , tttLargeFiber36Row77
  , tttLargeFiber36Row78
  , tttLargeFiber36Row79
  ]

def tttLargeFiber36Block1Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (272 <= i) && decide (i < 528)) ||
    (decide (1904 <= i) && decide (i < 2160))

def tttLargeFiber36Block1Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber36Block1Chunk0ExpectedContains row.source &&
    tttLargeFiber36Block1Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber36Key &&
          chainInputKey tttWord t == tttLargeFiber36Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber36Block1Chunk0SourcesCheck : Bool :=
  (tttLargeFiber36Block1Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber36Block1Chunk0Sources

theorem tttLargeFiber36Block1Chunk0SourcesCheck_ok :
    tttLargeFiber36Block1Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber36Block1Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber36Block1Chunk0RowValid
    (listGetD tttLargeFiber36Block1Chunk0Rows i default)

def tttLargeFiber36Block1Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber36Block1Chunk0Rows i default
  row.parent == tttLargeFiber36ParentOf row.source

def tttLargeFiber36Block1Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber36Block1Chunk0Sources 0 0 == 336
      && tttLargeFiber36ParentOf 336 == 272
      && 272 == tttLargeFiber36Root
      && decide (1 <= tttLargeFiber36MaxParentDepth)
  | 1 => listGetD tttLargeFiber36Block1Chunk0Sources 1 0 == 337
      && tttLargeFiber36ParentOf 337 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 2 => listGetD tttLargeFiber36Block1Chunk0Sources 2 0 == 338
      && tttLargeFiber36ParentOf 338 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 3 => listGetD tttLargeFiber36Block1Chunk0Sources 3 0 == 339
      && tttLargeFiber36ParentOf 339 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 4 => listGetD tttLargeFiber36Block1Chunk0Sources 4 0 == 340
      && tttLargeFiber36ParentOf 340 == 276
      && tttLargeFiber36ParentOf 276 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 5 => listGetD tttLargeFiber36Block1Chunk0Sources 5 0 == 341
      && tttLargeFiber36ParentOf 341 == 277
      && tttLargeFiber36ParentOf 277 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 6 => listGetD tttLargeFiber36Block1Chunk0Sources 6 0 == 342
      && tttLargeFiber36ParentOf 342 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 7 => listGetD tttLargeFiber36Block1Chunk0Sources 7 0 == 343
      && tttLargeFiber36ParentOf 343 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 8 => listGetD tttLargeFiber36Block1Chunk0Sources 8 0 == 344
      && tttLargeFiber36ParentOf 344 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 9 => listGetD tttLargeFiber36Block1Chunk0Sources 9 0 == 345
      && tttLargeFiber36ParentOf 345 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 10 => listGetD tttLargeFiber36Block1Chunk0Sources 10 0 == 346
      && tttLargeFiber36ParentOf 346 == 282
      && tttLargeFiber36ParentOf 282 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 11 => listGetD tttLargeFiber36Block1Chunk0Sources 11 0 == 347
      && tttLargeFiber36ParentOf 347 == 283
      && tttLargeFiber36ParentOf 283 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 12 => listGetD tttLargeFiber36Block1Chunk0Sources 12 0 == 348
      && tttLargeFiber36ParentOf 348 == 284
      && tttLargeFiber36ParentOf 284 == 276
      && tttLargeFiber36ParentOf 276 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 13 => listGetD tttLargeFiber36Block1Chunk0Sources 13 0 == 349
      && tttLargeFiber36ParentOf 349 == 285
      && tttLargeFiber36ParentOf 285 == 277
      && tttLargeFiber36ParentOf 277 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 14 => listGetD tttLargeFiber36Block1Chunk0Sources 14 0 == 350
      && tttLargeFiber36ParentOf 350 == 286
      && tttLargeFiber36ParentOf 286 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 15 => listGetD tttLargeFiber36Block1Chunk0Sources 15 0 == 351
      && tttLargeFiber36ParentOf 351 == 287
      && tttLargeFiber36ParentOf 287 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | _ => false

theorem tttLargeFiber36Block1Chunk0Row_0_ok :
    tttLargeFiber36Block1Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0Row_1_ok :
    tttLargeFiber36Block1Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0Row_2_ok :
    tttLargeFiber36Block1Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0Row_3_ok :
    tttLargeFiber36Block1Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0Row_4_ok :
    tttLargeFiber36Block1Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0Row_5_ok :
    tttLargeFiber36Block1Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0Row_6_ok :
    tttLargeFiber36Block1Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0Row_7_ok :
    tttLargeFiber36Block1Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0Row_8_ok :
    tttLargeFiber36Block1Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0Row_9_ok :
    tttLargeFiber36Block1Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0Row_10_ok :
    tttLargeFiber36Block1Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0Row_11_ok :
    tttLargeFiber36Block1Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0Row_12_ok :
    tttLargeFiber36Block1Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0Row_13_ok :
    tttLargeFiber36Block1Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0Row_14_ok :
    tttLargeFiber36Block1Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0Row_15_ok :
    tttLargeFiber36Block1Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentMap_0_ok :
    tttLargeFiber36Block1Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentMap_1_ok :
    tttLargeFiber36Block1Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentMap_2_ok :
    tttLargeFiber36Block1Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentMap_3_ok :
    tttLargeFiber36Block1Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentMap_4_ok :
    tttLargeFiber36Block1Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentMap_5_ok :
    tttLargeFiber36Block1Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentMap_6_ok :
    tttLargeFiber36Block1Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentMap_7_ok :
    tttLargeFiber36Block1Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentMap_8_ok :
    tttLargeFiber36Block1Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentMap_9_ok :
    tttLargeFiber36Block1Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentMap_10_ok :
    tttLargeFiber36Block1Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentMap_11_ok :
    tttLargeFiber36Block1Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentMap_12_ok :
    tttLargeFiber36Block1Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentMap_13_ok :
    tttLargeFiber36Block1Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentMap_14_ok :
    tttLargeFiber36Block1Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentMap_15_ok :
    tttLargeFiber36Block1Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentPath_0_ok :
    tttLargeFiber36Block1Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentPath_1_ok :
    tttLargeFiber36Block1Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentPath_2_ok :
    tttLargeFiber36Block1Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentPath_3_ok :
    tttLargeFiber36Block1Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentPath_4_ok :
    tttLargeFiber36Block1Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentPath_5_ok :
    tttLargeFiber36Block1Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentPath_6_ok :
    tttLargeFiber36Block1Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentPath_7_ok :
    tttLargeFiber36Block1Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentPath_8_ok :
    tttLargeFiber36Block1Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentPath_9_ok :
    tttLargeFiber36Block1Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentPath_10_ok :
    tttLargeFiber36Block1Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentPath_11_ok :
    tttLargeFiber36Block1Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentPath_12_ok :
    tttLargeFiber36Block1Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentPath_13_ok :
    tttLargeFiber36Block1Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentPath_14_ok :
    tttLargeFiber36Block1Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber36Block1Chunk0ParentPath_15_ok :
    tttLargeFiber36Block1Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber36Block1Chunk0RowsAudit : Bool :=
  tttLargeFiber36Block1Chunk0RowCheck 0
    && tttLargeFiber36Block1Chunk0RowCheck 1
    && tttLargeFiber36Block1Chunk0RowCheck 2
    && tttLargeFiber36Block1Chunk0RowCheck 3
    && tttLargeFiber36Block1Chunk0RowCheck 4
    && tttLargeFiber36Block1Chunk0RowCheck 5
    && tttLargeFiber36Block1Chunk0RowCheck 6
    && tttLargeFiber36Block1Chunk0RowCheck 7
    && tttLargeFiber36Block1Chunk0RowCheck 8
    && tttLargeFiber36Block1Chunk0RowCheck 9
    && tttLargeFiber36Block1Chunk0RowCheck 10
    && tttLargeFiber36Block1Chunk0RowCheck 11
    && tttLargeFiber36Block1Chunk0RowCheck 12
    && tttLargeFiber36Block1Chunk0RowCheck 13
    && tttLargeFiber36Block1Chunk0RowCheck 14
    && tttLargeFiber36Block1Chunk0RowCheck 15

theorem tttLargeFiber36Block1Chunk0RowsAudit_ok :
    tttLargeFiber36Block1Chunk0RowsAudit = true := by
  simp [tttLargeFiber36Block1Chunk0RowsAudit,
    tttLargeFiber36Block1Chunk0Row_0_ok,
    tttLargeFiber36Block1Chunk0Row_1_ok,
    tttLargeFiber36Block1Chunk0Row_2_ok,
    tttLargeFiber36Block1Chunk0Row_3_ok,
    tttLargeFiber36Block1Chunk0Row_4_ok,
    tttLargeFiber36Block1Chunk0Row_5_ok,
    tttLargeFiber36Block1Chunk0Row_6_ok,
    tttLargeFiber36Block1Chunk0Row_7_ok,
    tttLargeFiber36Block1Chunk0Row_8_ok,
    tttLargeFiber36Block1Chunk0Row_9_ok,
    tttLargeFiber36Block1Chunk0Row_10_ok,
    tttLargeFiber36Block1Chunk0Row_11_ok,
    tttLargeFiber36Block1Chunk0Row_12_ok,
    tttLargeFiber36Block1Chunk0Row_13_ok,
    tttLargeFiber36Block1Chunk0Row_14_ok,
    tttLargeFiber36Block1Chunk0Row_15_ok]

def tttLargeFiber36Block1Chunk0ParentMapAudit : Bool :=
  tttLargeFiber36Block1Chunk0ParentMapCheck 0
    && tttLargeFiber36Block1Chunk0ParentMapCheck 1
    && tttLargeFiber36Block1Chunk0ParentMapCheck 2
    && tttLargeFiber36Block1Chunk0ParentMapCheck 3
    && tttLargeFiber36Block1Chunk0ParentMapCheck 4
    && tttLargeFiber36Block1Chunk0ParentMapCheck 5
    && tttLargeFiber36Block1Chunk0ParentMapCheck 6
    && tttLargeFiber36Block1Chunk0ParentMapCheck 7
    && tttLargeFiber36Block1Chunk0ParentMapCheck 8
    && tttLargeFiber36Block1Chunk0ParentMapCheck 9
    && tttLargeFiber36Block1Chunk0ParentMapCheck 10
    && tttLargeFiber36Block1Chunk0ParentMapCheck 11
    && tttLargeFiber36Block1Chunk0ParentMapCheck 12
    && tttLargeFiber36Block1Chunk0ParentMapCheck 13
    && tttLargeFiber36Block1Chunk0ParentMapCheck 14
    && tttLargeFiber36Block1Chunk0ParentMapCheck 15

theorem tttLargeFiber36Block1Chunk0ParentMapAudit_ok :
    tttLargeFiber36Block1Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber36Block1Chunk0ParentMapAudit,
    tttLargeFiber36Block1Chunk0ParentMap_0_ok,
    tttLargeFiber36Block1Chunk0ParentMap_1_ok,
    tttLargeFiber36Block1Chunk0ParentMap_2_ok,
    tttLargeFiber36Block1Chunk0ParentMap_3_ok,
    tttLargeFiber36Block1Chunk0ParentMap_4_ok,
    tttLargeFiber36Block1Chunk0ParentMap_5_ok,
    tttLargeFiber36Block1Chunk0ParentMap_6_ok,
    tttLargeFiber36Block1Chunk0ParentMap_7_ok,
    tttLargeFiber36Block1Chunk0ParentMap_8_ok,
    tttLargeFiber36Block1Chunk0ParentMap_9_ok,
    tttLargeFiber36Block1Chunk0ParentMap_10_ok,
    tttLargeFiber36Block1Chunk0ParentMap_11_ok,
    tttLargeFiber36Block1Chunk0ParentMap_12_ok,
    tttLargeFiber36Block1Chunk0ParentMap_13_ok,
    tttLargeFiber36Block1Chunk0ParentMap_14_ok,
    tttLargeFiber36Block1Chunk0ParentMap_15_ok]

def tttLargeFiber36Block1Chunk0ParentsAudit : Bool :=
  tttLargeFiber36Block1Chunk0ParentPathCheck 0
    && tttLargeFiber36Block1Chunk0ParentPathCheck 1
    && tttLargeFiber36Block1Chunk0ParentPathCheck 2
    && tttLargeFiber36Block1Chunk0ParentPathCheck 3
    && tttLargeFiber36Block1Chunk0ParentPathCheck 4
    && tttLargeFiber36Block1Chunk0ParentPathCheck 5
    && tttLargeFiber36Block1Chunk0ParentPathCheck 6
    && tttLargeFiber36Block1Chunk0ParentPathCheck 7
    && tttLargeFiber36Block1Chunk0ParentPathCheck 8
    && tttLargeFiber36Block1Chunk0ParentPathCheck 9
    && tttLargeFiber36Block1Chunk0ParentPathCheck 10
    && tttLargeFiber36Block1Chunk0ParentPathCheck 11
    && tttLargeFiber36Block1Chunk0ParentPathCheck 12
    && tttLargeFiber36Block1Chunk0ParentPathCheck 13
    && tttLargeFiber36Block1Chunk0ParentPathCheck 14
    && tttLargeFiber36Block1Chunk0ParentPathCheck 15

theorem tttLargeFiber36Block1Chunk0ParentsAudit_ok :
    tttLargeFiber36Block1Chunk0ParentsAudit = true := by
  simp [tttLargeFiber36Block1Chunk0ParentsAudit,
    tttLargeFiber36Block1Chunk0ParentPath_0_ok,
    tttLargeFiber36Block1Chunk0ParentPath_1_ok,
    tttLargeFiber36Block1Chunk0ParentPath_2_ok,
    tttLargeFiber36Block1Chunk0ParentPath_3_ok,
    tttLargeFiber36Block1Chunk0ParentPath_4_ok,
    tttLargeFiber36Block1Chunk0ParentPath_5_ok,
    tttLargeFiber36Block1Chunk0ParentPath_6_ok,
    tttLargeFiber36Block1Chunk0ParentPath_7_ok,
    tttLargeFiber36Block1Chunk0ParentPath_8_ok,
    tttLargeFiber36Block1Chunk0ParentPath_9_ok,
    tttLargeFiber36Block1Chunk0ParentPath_10_ok,
    tttLargeFiber36Block1Chunk0ParentPath_11_ok,
    tttLargeFiber36Block1Chunk0ParentPath_12_ok,
    tttLargeFiber36Block1Chunk0ParentPath_13_ok,
    tttLargeFiber36Block1Chunk0ParentPath_14_ok,
    tttLargeFiber36Block1Chunk0ParentPath_15_ok]

def tttLargeFiber36Block1Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber36CountsAudit &&
    tttLargeFiber36Block1Chunk0SourcesCheck &&
    tttLargeFiber36Block1Chunk0RowsAudit &&
    tttLargeFiber36Block1Chunk0ParentMapAudit &&
    tttLargeFiber36Block1Chunk0ParentsAudit

theorem tttLargeFiber36Block1Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber36Block1Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber36Block1Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber36CountsAudit_ok,
    tttLargeFiber36Block1Chunk0SourcesCheck_ok,
    tttLargeFiber36Block1Chunk0RowsAudit_ok,
    tttLargeFiber36Block1Chunk0ParentMapAudit_ok,
    tttLargeFiber36Block1Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber36Block1Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
