import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 36, block 1 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber36Block1Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber36Data

def tttLargeFiber36Block1Chunk3Sources : List Nat :=
  [   384, 385, 386, 387, 388, 389, 390, 391,
   392, 393, 394, 395, 396, 397, 398, 399]

def tttLargeFiber36Row112 : TripleComponentParentRow :=
  tripleRow 384 320 9 110 64 8 102 64
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row113 : TripleComponentParentRow :=
  tripleRow 385 321 9 110 65 8 102 65
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row114 : TripleComponentParentRow :=
  tripleRow 386 322 9 110 66 8 102 66
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row115 : TripleComponentParentRow :=
  tripleRow 387 323 9 110 67 8 102 67
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row116 : TripleComponentParentRow :=
  tripleRow 388 324 9 110 116 8 102 116
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row117 : TripleComponentParentRow :=
  tripleRow 389 325 9 110 117 8 102 117
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row118 : TripleComponentParentRow :=
  tripleRow 390 326 9 110 118 8 102 118
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row119 : TripleComponentParentRow :=
  tripleRow 391 327 9 110 119 8 102 119
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row120 : TripleComponentParentRow :=
  tripleRow 392 328 9 111 72 8 103 72
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row121 : TripleComponentParentRow :=
  tripleRow 393 329 9 111 73 8 103 73
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row122 : TripleComponentParentRow :=
  tripleRow 394 330 9 111 74 8 103 74
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row123 : TripleComponentParentRow :=
  tripleRow 395 331 9 111 75 8 103 75
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row124 : TripleComponentParentRow :=
  tripleRow 396 332 9 111 124 8 103 124
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row125 : TripleComponentParentRow :=
  tripleRow 397 333 9 111 125 8 103 125
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row126 : TripleComponentParentRow :=
  tripleRow 398 334 9 111 126 8 103 126
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row127 : TripleComponentParentRow :=
  tripleRow 399 335 9 111 127 8 103 127
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Block1Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber36Row112
  , tttLargeFiber36Row113
  , tttLargeFiber36Row114
  , tttLargeFiber36Row115
  , tttLargeFiber36Row116
  , tttLargeFiber36Row117
  , tttLargeFiber36Row118
  , tttLargeFiber36Row119
  , tttLargeFiber36Row120
  , tttLargeFiber36Row121
  , tttLargeFiber36Row122
  , tttLargeFiber36Row123
  , tttLargeFiber36Row124
  , tttLargeFiber36Row125
  , tttLargeFiber36Row126
  , tttLargeFiber36Row127
  ]

def tttLargeFiber36Block1Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (272 <= i) && decide (i < 528)) ||
    (decide (1904 <= i) && decide (i < 2160))

def tttLargeFiber36Block1Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber36Block1Chunk3ExpectedContains row.source &&
    tttLargeFiber36Block1Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber36Key &&
          chainInputKey tttWord t == tttLargeFiber36Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber36Block1Chunk3SourcesCheck : Bool :=
  (tttLargeFiber36Block1Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber36Block1Chunk3Sources

theorem tttLargeFiber36Block1Chunk3SourcesCheck_ok :
    tttLargeFiber36Block1Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber36Block1Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber36Block1Chunk3RowValid
    (listGetD tttLargeFiber36Block1Chunk3Rows i default)

def tttLargeFiber36Block1Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber36Block1Chunk3Rows i default
  row.parent == tttLargeFiber36ParentOf row.source

def tttLargeFiber36Block1Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber36Block1Chunk3Sources 0 0 == 384
      && tttLargeFiber36ParentOf 384 == 320
      && tttLargeFiber36ParentOf 320 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 1 => listGetD tttLargeFiber36Block1Chunk3Sources 1 0 == 385
      && tttLargeFiber36ParentOf 385 == 321
      && tttLargeFiber36ParentOf 321 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 2 => listGetD tttLargeFiber36Block1Chunk3Sources 2 0 == 386
      && tttLargeFiber36ParentOf 386 == 322
      && tttLargeFiber36ParentOf 322 == 282
      && tttLargeFiber36ParentOf 282 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 3 => listGetD tttLargeFiber36Block1Chunk3Sources 3 0 == 387
      && tttLargeFiber36ParentOf 387 == 323
      && tttLargeFiber36ParentOf 323 == 283
      && tttLargeFiber36ParentOf 283 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 4 => listGetD tttLargeFiber36Block1Chunk3Sources 4 0 == 388
      && tttLargeFiber36ParentOf 388 == 324
      && tttLargeFiber36ParentOf 324 == 284
      && tttLargeFiber36ParentOf 284 == 276
      && tttLargeFiber36ParentOf 276 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 5 => listGetD tttLargeFiber36Block1Chunk3Sources 5 0 == 389
      && tttLargeFiber36ParentOf 389 == 325
      && tttLargeFiber36ParentOf 325 == 285
      && tttLargeFiber36ParentOf 285 == 277
      && tttLargeFiber36ParentOf 277 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 6 => listGetD tttLargeFiber36Block1Chunk3Sources 6 0 == 390
      && tttLargeFiber36ParentOf 390 == 326
      && tttLargeFiber36ParentOf 326 == 286
      && tttLargeFiber36ParentOf 286 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 7 => listGetD tttLargeFiber36Block1Chunk3Sources 7 0 == 391
      && tttLargeFiber36ParentOf 391 == 327
      && tttLargeFiber36ParentOf 327 == 287
      && tttLargeFiber36ParentOf 287 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 8 => listGetD tttLargeFiber36Block1Chunk3Sources 8 0 == 392
      && tttLargeFiber36ParentOf 392 == 328
      && tttLargeFiber36ParentOf 328 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 9 => listGetD tttLargeFiber36Block1Chunk3Sources 9 0 == 393
      && tttLargeFiber36ParentOf 393 == 329
      && tttLargeFiber36ParentOf 329 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 10 => listGetD tttLargeFiber36Block1Chunk3Sources 10 0 == 394
      && tttLargeFiber36ParentOf 394 == 330
      && tttLargeFiber36ParentOf 330 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 11 => listGetD tttLargeFiber36Block1Chunk3Sources 11 0 == 395
      && tttLargeFiber36ParentOf 395 == 331
      && tttLargeFiber36ParentOf 331 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 12 => listGetD tttLargeFiber36Block1Chunk3Sources 12 0 == 396
      && tttLargeFiber36ParentOf 396 == 332
      && tttLargeFiber36ParentOf 332 == 276
      && tttLargeFiber36ParentOf 276 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 13 => listGetD tttLargeFiber36Block1Chunk3Sources 13 0 == 397
      && tttLargeFiber36ParentOf 397 == 333
      && tttLargeFiber36ParentOf 333 == 277
      && tttLargeFiber36ParentOf 277 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 14 => listGetD tttLargeFiber36Block1Chunk3Sources 14 0 == 398
      && tttLargeFiber36ParentOf 398 == 334
      && tttLargeFiber36ParentOf 334 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 15 => listGetD tttLargeFiber36Block1Chunk3Sources 15 0 == 399
      && tttLargeFiber36ParentOf 399 == 335
      && tttLargeFiber36ParentOf 335 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | _ => false

theorem tttLargeFiber36Block1Chunk3Row_0_ok :
    tttLargeFiber36Block1Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3Row_1_ok :
    tttLargeFiber36Block1Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3Row_2_ok :
    tttLargeFiber36Block1Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3Row_3_ok :
    tttLargeFiber36Block1Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3Row_4_ok :
    tttLargeFiber36Block1Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3Row_5_ok :
    tttLargeFiber36Block1Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3Row_6_ok :
    tttLargeFiber36Block1Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3Row_7_ok :
    tttLargeFiber36Block1Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3Row_8_ok :
    tttLargeFiber36Block1Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3Row_9_ok :
    tttLargeFiber36Block1Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3Row_10_ok :
    tttLargeFiber36Block1Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3Row_11_ok :
    tttLargeFiber36Block1Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3Row_12_ok :
    tttLargeFiber36Block1Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3Row_13_ok :
    tttLargeFiber36Block1Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3Row_14_ok :
    tttLargeFiber36Block1Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3Row_15_ok :
    tttLargeFiber36Block1Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentMap_0_ok :
    tttLargeFiber36Block1Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentMap_1_ok :
    tttLargeFiber36Block1Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentMap_2_ok :
    tttLargeFiber36Block1Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentMap_3_ok :
    tttLargeFiber36Block1Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentMap_4_ok :
    tttLargeFiber36Block1Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentMap_5_ok :
    tttLargeFiber36Block1Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentMap_6_ok :
    tttLargeFiber36Block1Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentMap_7_ok :
    tttLargeFiber36Block1Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentMap_8_ok :
    tttLargeFiber36Block1Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentMap_9_ok :
    tttLargeFiber36Block1Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentMap_10_ok :
    tttLargeFiber36Block1Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentMap_11_ok :
    tttLargeFiber36Block1Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentMap_12_ok :
    tttLargeFiber36Block1Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentMap_13_ok :
    tttLargeFiber36Block1Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentMap_14_ok :
    tttLargeFiber36Block1Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentMap_15_ok :
    tttLargeFiber36Block1Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentPath_0_ok :
    tttLargeFiber36Block1Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentPath_1_ok :
    tttLargeFiber36Block1Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentPath_2_ok :
    tttLargeFiber36Block1Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentPath_3_ok :
    tttLargeFiber36Block1Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentPath_4_ok :
    tttLargeFiber36Block1Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentPath_5_ok :
    tttLargeFiber36Block1Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentPath_6_ok :
    tttLargeFiber36Block1Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentPath_7_ok :
    tttLargeFiber36Block1Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentPath_8_ok :
    tttLargeFiber36Block1Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentPath_9_ok :
    tttLargeFiber36Block1Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentPath_10_ok :
    tttLargeFiber36Block1Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentPath_11_ok :
    tttLargeFiber36Block1Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentPath_12_ok :
    tttLargeFiber36Block1Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentPath_13_ok :
    tttLargeFiber36Block1Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentPath_14_ok :
    tttLargeFiber36Block1Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber36Block1Chunk3ParentPath_15_ok :
    tttLargeFiber36Block1Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber36Block1Chunk3RowsAudit : Bool :=
  tttLargeFiber36Block1Chunk3RowCheck 0
    && tttLargeFiber36Block1Chunk3RowCheck 1
    && tttLargeFiber36Block1Chunk3RowCheck 2
    && tttLargeFiber36Block1Chunk3RowCheck 3
    && tttLargeFiber36Block1Chunk3RowCheck 4
    && tttLargeFiber36Block1Chunk3RowCheck 5
    && tttLargeFiber36Block1Chunk3RowCheck 6
    && tttLargeFiber36Block1Chunk3RowCheck 7
    && tttLargeFiber36Block1Chunk3RowCheck 8
    && tttLargeFiber36Block1Chunk3RowCheck 9
    && tttLargeFiber36Block1Chunk3RowCheck 10
    && tttLargeFiber36Block1Chunk3RowCheck 11
    && tttLargeFiber36Block1Chunk3RowCheck 12
    && tttLargeFiber36Block1Chunk3RowCheck 13
    && tttLargeFiber36Block1Chunk3RowCheck 14
    && tttLargeFiber36Block1Chunk3RowCheck 15

theorem tttLargeFiber36Block1Chunk3RowsAudit_ok :
    tttLargeFiber36Block1Chunk3RowsAudit = true := by
  simp [tttLargeFiber36Block1Chunk3RowsAudit,
    tttLargeFiber36Block1Chunk3Row_0_ok,
    tttLargeFiber36Block1Chunk3Row_1_ok,
    tttLargeFiber36Block1Chunk3Row_2_ok,
    tttLargeFiber36Block1Chunk3Row_3_ok,
    tttLargeFiber36Block1Chunk3Row_4_ok,
    tttLargeFiber36Block1Chunk3Row_5_ok,
    tttLargeFiber36Block1Chunk3Row_6_ok,
    tttLargeFiber36Block1Chunk3Row_7_ok,
    tttLargeFiber36Block1Chunk3Row_8_ok,
    tttLargeFiber36Block1Chunk3Row_9_ok,
    tttLargeFiber36Block1Chunk3Row_10_ok,
    tttLargeFiber36Block1Chunk3Row_11_ok,
    tttLargeFiber36Block1Chunk3Row_12_ok,
    tttLargeFiber36Block1Chunk3Row_13_ok,
    tttLargeFiber36Block1Chunk3Row_14_ok,
    tttLargeFiber36Block1Chunk3Row_15_ok]

def tttLargeFiber36Block1Chunk3ParentMapAudit : Bool :=
  tttLargeFiber36Block1Chunk3ParentMapCheck 0
    && tttLargeFiber36Block1Chunk3ParentMapCheck 1
    && tttLargeFiber36Block1Chunk3ParentMapCheck 2
    && tttLargeFiber36Block1Chunk3ParentMapCheck 3
    && tttLargeFiber36Block1Chunk3ParentMapCheck 4
    && tttLargeFiber36Block1Chunk3ParentMapCheck 5
    && tttLargeFiber36Block1Chunk3ParentMapCheck 6
    && tttLargeFiber36Block1Chunk3ParentMapCheck 7
    && tttLargeFiber36Block1Chunk3ParentMapCheck 8
    && tttLargeFiber36Block1Chunk3ParentMapCheck 9
    && tttLargeFiber36Block1Chunk3ParentMapCheck 10
    && tttLargeFiber36Block1Chunk3ParentMapCheck 11
    && tttLargeFiber36Block1Chunk3ParentMapCheck 12
    && tttLargeFiber36Block1Chunk3ParentMapCheck 13
    && tttLargeFiber36Block1Chunk3ParentMapCheck 14
    && tttLargeFiber36Block1Chunk3ParentMapCheck 15

theorem tttLargeFiber36Block1Chunk3ParentMapAudit_ok :
    tttLargeFiber36Block1Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber36Block1Chunk3ParentMapAudit,
    tttLargeFiber36Block1Chunk3ParentMap_0_ok,
    tttLargeFiber36Block1Chunk3ParentMap_1_ok,
    tttLargeFiber36Block1Chunk3ParentMap_2_ok,
    tttLargeFiber36Block1Chunk3ParentMap_3_ok,
    tttLargeFiber36Block1Chunk3ParentMap_4_ok,
    tttLargeFiber36Block1Chunk3ParentMap_5_ok,
    tttLargeFiber36Block1Chunk3ParentMap_6_ok,
    tttLargeFiber36Block1Chunk3ParentMap_7_ok,
    tttLargeFiber36Block1Chunk3ParentMap_8_ok,
    tttLargeFiber36Block1Chunk3ParentMap_9_ok,
    tttLargeFiber36Block1Chunk3ParentMap_10_ok,
    tttLargeFiber36Block1Chunk3ParentMap_11_ok,
    tttLargeFiber36Block1Chunk3ParentMap_12_ok,
    tttLargeFiber36Block1Chunk3ParentMap_13_ok,
    tttLargeFiber36Block1Chunk3ParentMap_14_ok,
    tttLargeFiber36Block1Chunk3ParentMap_15_ok]

def tttLargeFiber36Block1Chunk3ParentsAudit : Bool :=
  tttLargeFiber36Block1Chunk3ParentPathCheck 0
    && tttLargeFiber36Block1Chunk3ParentPathCheck 1
    && tttLargeFiber36Block1Chunk3ParentPathCheck 2
    && tttLargeFiber36Block1Chunk3ParentPathCheck 3
    && tttLargeFiber36Block1Chunk3ParentPathCheck 4
    && tttLargeFiber36Block1Chunk3ParentPathCheck 5
    && tttLargeFiber36Block1Chunk3ParentPathCheck 6
    && tttLargeFiber36Block1Chunk3ParentPathCheck 7
    && tttLargeFiber36Block1Chunk3ParentPathCheck 8
    && tttLargeFiber36Block1Chunk3ParentPathCheck 9
    && tttLargeFiber36Block1Chunk3ParentPathCheck 10
    && tttLargeFiber36Block1Chunk3ParentPathCheck 11
    && tttLargeFiber36Block1Chunk3ParentPathCheck 12
    && tttLargeFiber36Block1Chunk3ParentPathCheck 13
    && tttLargeFiber36Block1Chunk3ParentPathCheck 14
    && tttLargeFiber36Block1Chunk3ParentPathCheck 15

theorem tttLargeFiber36Block1Chunk3ParentsAudit_ok :
    tttLargeFiber36Block1Chunk3ParentsAudit = true := by
  simp [tttLargeFiber36Block1Chunk3ParentsAudit,
    tttLargeFiber36Block1Chunk3ParentPath_0_ok,
    tttLargeFiber36Block1Chunk3ParentPath_1_ok,
    tttLargeFiber36Block1Chunk3ParentPath_2_ok,
    tttLargeFiber36Block1Chunk3ParentPath_3_ok,
    tttLargeFiber36Block1Chunk3ParentPath_4_ok,
    tttLargeFiber36Block1Chunk3ParentPath_5_ok,
    tttLargeFiber36Block1Chunk3ParentPath_6_ok,
    tttLargeFiber36Block1Chunk3ParentPath_7_ok,
    tttLargeFiber36Block1Chunk3ParentPath_8_ok,
    tttLargeFiber36Block1Chunk3ParentPath_9_ok,
    tttLargeFiber36Block1Chunk3ParentPath_10_ok,
    tttLargeFiber36Block1Chunk3ParentPath_11_ok,
    tttLargeFiber36Block1Chunk3ParentPath_12_ok,
    tttLargeFiber36Block1Chunk3ParentPath_13_ok,
    tttLargeFiber36Block1Chunk3ParentPath_14_ok,
    tttLargeFiber36Block1Chunk3ParentPath_15_ok]

def tttLargeFiber36Block1Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber36CountsAudit &&
    tttLargeFiber36Block1Chunk3SourcesCheck &&
    tttLargeFiber36Block1Chunk3RowsAudit &&
    tttLargeFiber36Block1Chunk3ParentMapAudit &&
    tttLargeFiber36Block1Chunk3ParentsAudit

theorem tttLargeFiber36Block1Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber36Block1Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber36Block1Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber36CountsAudit_ok,
    tttLargeFiber36Block1Chunk3SourcesCheck_ok,
    tttLargeFiber36Block1Chunk3RowsAudit_ok,
    tttLargeFiber36Block1Chunk3ParentMapAudit_ok,
    tttLargeFiber36Block1Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber36Block1Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
