import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 36, block 3 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber36Block3Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber36Data

def tttLargeFiber36Block3Chunk2Sources : List Nat :=
  [   496, 497, 498, 499, 500, 501, 502, 503,
   504, 505, 506, 507, 508, 509, 510, 511]

def tttLargeFiber36Row224 : TripleComponentParentRow :=
  tripleRow 496 464 11 40 148 11 24 80
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row225 : TripleComponentParentRow :=
  tripleRow 497 465 11 40 149 11 24 81
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row226 : TripleComponentParentRow :=
  tripleRow 498 466 11 40 150 11 24 82
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber36Row227 : TripleComponentParentRow :=
  tripleRow 499 496 11 40 151 11 40 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row228 : TripleComponentParentRow :=
  tripleRow 500 496 11 40 164 11 40 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber36Row229 : TripleComponentParentRow :=
  tripleRow 501 497 11 40 165 11 40 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber36Row230 : TripleComponentParentRow :=
  tripleRow 502 470 11 40 166 11 24 102
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber36Row231 : TripleComponentParentRow :=
  tripleRow 503 471 11 40 167 11 24 103
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber36Row232 : TripleComponentParentRow :=
  tripleRow 504 472 11 41 156 11 25 88
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row233 : TripleComponentParentRow :=
  tripleRow 505 473 11 41 157 11 25 89
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row234 : TripleComponentParentRow :=
  tripleRow 506 474 11 41 158 11 25 90
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber36Row235 : TripleComponentParentRow :=
  tripleRow 507 504 11 41 159 11 41 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row236 : TripleComponentParentRow :=
  tripleRow 508 504 11 41 172 11 41 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber36Row237 : TripleComponentParentRow :=
  tripleRow 509 505 11 41 173 11 41 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber36Row238 : TripleComponentParentRow :=
  tripleRow 510 478 11 41 174 11 25 110
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber36Row239 : TripleComponentParentRow :=
  tripleRow 511 479 11 41 175 11 25 111
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber36Block3Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber36Row224
  , tttLargeFiber36Row225
  , tttLargeFiber36Row226
  , tttLargeFiber36Row227
  , tttLargeFiber36Row228
  , tttLargeFiber36Row229
  , tttLargeFiber36Row230
  , tttLargeFiber36Row231
  , tttLargeFiber36Row232
  , tttLargeFiber36Row233
  , tttLargeFiber36Row234
  , tttLargeFiber36Row235
  , tttLargeFiber36Row236
  , tttLargeFiber36Row237
  , tttLargeFiber36Row238
  , tttLargeFiber36Row239
  ]

def tttLargeFiber36Block3Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (272 <= i) && decide (i < 528)) ||
    (decide (1904 <= i) && decide (i < 2160))

def tttLargeFiber36Block3Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber36Block3Chunk2ExpectedContains row.source &&
    tttLargeFiber36Block3Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber36Key &&
          chainInputKey tttWord t == tttLargeFiber36Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber36Block3Chunk2SourcesCheck : Bool :=
  (tttLargeFiber36Block3Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber36Block3Chunk2Sources

theorem tttLargeFiber36Block3Chunk2SourcesCheck_ok :
    tttLargeFiber36Block3Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber36Block3Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber36Block3Chunk2RowValid
    (listGetD tttLargeFiber36Block3Chunk2Rows i default)

def tttLargeFiber36Block3Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber36Block3Chunk2Rows i default
  row.parent == tttLargeFiber36ParentOf row.source

def tttLargeFiber36Block3Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber36Block3Chunk2Sources 0 0 == 496
      && tttLargeFiber36ParentOf 496 == 464
      && tttLargeFiber36ParentOf 464 == 336
      && tttLargeFiber36ParentOf 336 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 1 => listGetD tttLargeFiber36Block3Chunk2Sources 1 0 == 497
      && tttLargeFiber36ParentOf 497 == 465
      && tttLargeFiber36ParentOf 465 == 337
      && tttLargeFiber36ParentOf 337 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 2 => listGetD tttLargeFiber36Block3Chunk2Sources 2 0 == 498
      && tttLargeFiber36ParentOf 498 == 466
      && tttLargeFiber36ParentOf 466 == 338
      && tttLargeFiber36ParentOf 338 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 3 => listGetD tttLargeFiber36Block3Chunk2Sources 3 0 == 499
      && tttLargeFiber36ParentOf 499 == 496
      && tttLargeFiber36ParentOf 496 == 464
      && tttLargeFiber36ParentOf 464 == 336
      && tttLargeFiber36ParentOf 336 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 4 => listGetD tttLargeFiber36Block3Chunk2Sources 4 0 == 500
      && tttLargeFiber36ParentOf 500 == 496
      && tttLargeFiber36ParentOf 496 == 464
      && tttLargeFiber36ParentOf 464 == 336
      && tttLargeFiber36ParentOf 336 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 5 => listGetD tttLargeFiber36Block3Chunk2Sources 5 0 == 501
      && tttLargeFiber36ParentOf 501 == 497
      && tttLargeFiber36ParentOf 497 == 465
      && tttLargeFiber36ParentOf 465 == 337
      && tttLargeFiber36ParentOf 337 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 6 => listGetD tttLargeFiber36Block3Chunk2Sources 6 0 == 502
      && tttLargeFiber36ParentOf 502 == 470
      && tttLargeFiber36ParentOf 470 == 342
      && tttLargeFiber36ParentOf 342 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 7 => listGetD tttLargeFiber36Block3Chunk2Sources 7 0 == 503
      && tttLargeFiber36ParentOf 503 == 471
      && tttLargeFiber36ParentOf 471 == 343
      && tttLargeFiber36ParentOf 343 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 8 => listGetD tttLargeFiber36Block3Chunk2Sources 8 0 == 504
      && tttLargeFiber36ParentOf 504 == 472
      && tttLargeFiber36ParentOf 472 == 344
      && tttLargeFiber36ParentOf 344 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 9 => listGetD tttLargeFiber36Block3Chunk2Sources 9 0 == 505
      && tttLargeFiber36ParentOf 505 == 473
      && tttLargeFiber36ParentOf 473 == 345
      && tttLargeFiber36ParentOf 345 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 10 => listGetD tttLargeFiber36Block3Chunk2Sources 10 0 == 506
      && tttLargeFiber36ParentOf 506 == 474
      && tttLargeFiber36ParentOf 474 == 346
      && tttLargeFiber36ParentOf 346 == 282
      && tttLargeFiber36ParentOf 282 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 11 => listGetD tttLargeFiber36Block3Chunk2Sources 11 0 == 507
      && tttLargeFiber36ParentOf 507 == 504
      && tttLargeFiber36ParentOf 504 == 472
      && tttLargeFiber36ParentOf 472 == 344
      && tttLargeFiber36ParentOf 344 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 12 => listGetD tttLargeFiber36Block3Chunk2Sources 12 0 == 508
      && tttLargeFiber36ParentOf 508 == 504
      && tttLargeFiber36ParentOf 504 == 472
      && tttLargeFiber36ParentOf 472 == 344
      && tttLargeFiber36ParentOf 344 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 13 => listGetD tttLargeFiber36Block3Chunk2Sources 13 0 == 509
      && tttLargeFiber36ParentOf 509 == 505
      && tttLargeFiber36ParentOf 505 == 473
      && tttLargeFiber36ParentOf 473 == 345
      && tttLargeFiber36ParentOf 345 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (6 <= tttLargeFiber36MaxParentDepth)
  | 14 => listGetD tttLargeFiber36Block3Chunk2Sources 14 0 == 510
      && tttLargeFiber36ParentOf 510 == 478
      && tttLargeFiber36ParentOf 478 == 350
      && tttLargeFiber36ParentOf 350 == 286
      && tttLargeFiber36ParentOf 286 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (6 <= tttLargeFiber36MaxParentDepth)
  | 15 => listGetD tttLargeFiber36Block3Chunk2Sources 15 0 == 511
      && tttLargeFiber36ParentOf 511 == 479
      && tttLargeFiber36ParentOf 479 == 351
      && tttLargeFiber36ParentOf 351 == 287
      && tttLargeFiber36ParentOf 287 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | _ => false

theorem tttLargeFiber36Block3Chunk2Row_0_ok :
    tttLargeFiber36Block3Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2Row_1_ok :
    tttLargeFiber36Block3Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2Row_2_ok :
    tttLargeFiber36Block3Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2Row_3_ok :
    tttLargeFiber36Block3Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2Row_4_ok :
    tttLargeFiber36Block3Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2Row_5_ok :
    tttLargeFiber36Block3Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2Row_6_ok :
    tttLargeFiber36Block3Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2Row_7_ok :
    tttLargeFiber36Block3Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2Row_8_ok :
    tttLargeFiber36Block3Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2Row_9_ok :
    tttLargeFiber36Block3Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2Row_10_ok :
    tttLargeFiber36Block3Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2Row_11_ok :
    tttLargeFiber36Block3Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2Row_12_ok :
    tttLargeFiber36Block3Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2Row_13_ok :
    tttLargeFiber36Block3Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2Row_14_ok :
    tttLargeFiber36Block3Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2Row_15_ok :
    tttLargeFiber36Block3Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentMap_0_ok :
    tttLargeFiber36Block3Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentMap_1_ok :
    tttLargeFiber36Block3Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentMap_2_ok :
    tttLargeFiber36Block3Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentMap_3_ok :
    tttLargeFiber36Block3Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentMap_4_ok :
    tttLargeFiber36Block3Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentMap_5_ok :
    tttLargeFiber36Block3Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentMap_6_ok :
    tttLargeFiber36Block3Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentMap_7_ok :
    tttLargeFiber36Block3Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentMap_8_ok :
    tttLargeFiber36Block3Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentMap_9_ok :
    tttLargeFiber36Block3Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentMap_10_ok :
    tttLargeFiber36Block3Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentMap_11_ok :
    tttLargeFiber36Block3Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentMap_12_ok :
    tttLargeFiber36Block3Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentMap_13_ok :
    tttLargeFiber36Block3Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentMap_14_ok :
    tttLargeFiber36Block3Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentMap_15_ok :
    tttLargeFiber36Block3Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentPath_0_ok :
    tttLargeFiber36Block3Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentPath_1_ok :
    tttLargeFiber36Block3Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentPath_2_ok :
    tttLargeFiber36Block3Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentPath_3_ok :
    tttLargeFiber36Block3Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentPath_4_ok :
    tttLargeFiber36Block3Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentPath_5_ok :
    tttLargeFiber36Block3Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentPath_6_ok :
    tttLargeFiber36Block3Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentPath_7_ok :
    tttLargeFiber36Block3Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentPath_8_ok :
    tttLargeFiber36Block3Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentPath_9_ok :
    tttLargeFiber36Block3Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentPath_10_ok :
    tttLargeFiber36Block3Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentPath_11_ok :
    tttLargeFiber36Block3Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentPath_12_ok :
    tttLargeFiber36Block3Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentPath_13_ok :
    tttLargeFiber36Block3Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentPath_14_ok :
    tttLargeFiber36Block3Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber36Block3Chunk2ParentPath_15_ok :
    tttLargeFiber36Block3Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber36Block3Chunk2RowsAudit : Bool :=
  tttLargeFiber36Block3Chunk2RowCheck 0
    && tttLargeFiber36Block3Chunk2RowCheck 1
    && tttLargeFiber36Block3Chunk2RowCheck 2
    && tttLargeFiber36Block3Chunk2RowCheck 3
    && tttLargeFiber36Block3Chunk2RowCheck 4
    && tttLargeFiber36Block3Chunk2RowCheck 5
    && tttLargeFiber36Block3Chunk2RowCheck 6
    && tttLargeFiber36Block3Chunk2RowCheck 7
    && tttLargeFiber36Block3Chunk2RowCheck 8
    && tttLargeFiber36Block3Chunk2RowCheck 9
    && tttLargeFiber36Block3Chunk2RowCheck 10
    && tttLargeFiber36Block3Chunk2RowCheck 11
    && tttLargeFiber36Block3Chunk2RowCheck 12
    && tttLargeFiber36Block3Chunk2RowCheck 13
    && tttLargeFiber36Block3Chunk2RowCheck 14
    && tttLargeFiber36Block3Chunk2RowCheck 15

theorem tttLargeFiber36Block3Chunk2RowsAudit_ok :
    tttLargeFiber36Block3Chunk2RowsAudit = true := by
  simp [tttLargeFiber36Block3Chunk2RowsAudit,
    tttLargeFiber36Block3Chunk2Row_0_ok,
    tttLargeFiber36Block3Chunk2Row_1_ok,
    tttLargeFiber36Block3Chunk2Row_2_ok,
    tttLargeFiber36Block3Chunk2Row_3_ok,
    tttLargeFiber36Block3Chunk2Row_4_ok,
    tttLargeFiber36Block3Chunk2Row_5_ok,
    tttLargeFiber36Block3Chunk2Row_6_ok,
    tttLargeFiber36Block3Chunk2Row_7_ok,
    tttLargeFiber36Block3Chunk2Row_8_ok,
    tttLargeFiber36Block3Chunk2Row_9_ok,
    tttLargeFiber36Block3Chunk2Row_10_ok,
    tttLargeFiber36Block3Chunk2Row_11_ok,
    tttLargeFiber36Block3Chunk2Row_12_ok,
    tttLargeFiber36Block3Chunk2Row_13_ok,
    tttLargeFiber36Block3Chunk2Row_14_ok,
    tttLargeFiber36Block3Chunk2Row_15_ok]

def tttLargeFiber36Block3Chunk2ParentMapAudit : Bool :=
  tttLargeFiber36Block3Chunk2ParentMapCheck 0
    && tttLargeFiber36Block3Chunk2ParentMapCheck 1
    && tttLargeFiber36Block3Chunk2ParentMapCheck 2
    && tttLargeFiber36Block3Chunk2ParentMapCheck 3
    && tttLargeFiber36Block3Chunk2ParentMapCheck 4
    && tttLargeFiber36Block3Chunk2ParentMapCheck 5
    && tttLargeFiber36Block3Chunk2ParentMapCheck 6
    && tttLargeFiber36Block3Chunk2ParentMapCheck 7
    && tttLargeFiber36Block3Chunk2ParentMapCheck 8
    && tttLargeFiber36Block3Chunk2ParentMapCheck 9
    && tttLargeFiber36Block3Chunk2ParentMapCheck 10
    && tttLargeFiber36Block3Chunk2ParentMapCheck 11
    && tttLargeFiber36Block3Chunk2ParentMapCheck 12
    && tttLargeFiber36Block3Chunk2ParentMapCheck 13
    && tttLargeFiber36Block3Chunk2ParentMapCheck 14
    && tttLargeFiber36Block3Chunk2ParentMapCheck 15

theorem tttLargeFiber36Block3Chunk2ParentMapAudit_ok :
    tttLargeFiber36Block3Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber36Block3Chunk2ParentMapAudit,
    tttLargeFiber36Block3Chunk2ParentMap_0_ok,
    tttLargeFiber36Block3Chunk2ParentMap_1_ok,
    tttLargeFiber36Block3Chunk2ParentMap_2_ok,
    tttLargeFiber36Block3Chunk2ParentMap_3_ok,
    tttLargeFiber36Block3Chunk2ParentMap_4_ok,
    tttLargeFiber36Block3Chunk2ParentMap_5_ok,
    tttLargeFiber36Block3Chunk2ParentMap_6_ok,
    tttLargeFiber36Block3Chunk2ParentMap_7_ok,
    tttLargeFiber36Block3Chunk2ParentMap_8_ok,
    tttLargeFiber36Block3Chunk2ParentMap_9_ok,
    tttLargeFiber36Block3Chunk2ParentMap_10_ok,
    tttLargeFiber36Block3Chunk2ParentMap_11_ok,
    tttLargeFiber36Block3Chunk2ParentMap_12_ok,
    tttLargeFiber36Block3Chunk2ParentMap_13_ok,
    tttLargeFiber36Block3Chunk2ParentMap_14_ok,
    tttLargeFiber36Block3Chunk2ParentMap_15_ok]

def tttLargeFiber36Block3Chunk2ParentsAudit : Bool :=
  tttLargeFiber36Block3Chunk2ParentPathCheck 0
    && tttLargeFiber36Block3Chunk2ParentPathCheck 1
    && tttLargeFiber36Block3Chunk2ParentPathCheck 2
    && tttLargeFiber36Block3Chunk2ParentPathCheck 3
    && tttLargeFiber36Block3Chunk2ParentPathCheck 4
    && tttLargeFiber36Block3Chunk2ParentPathCheck 5
    && tttLargeFiber36Block3Chunk2ParentPathCheck 6
    && tttLargeFiber36Block3Chunk2ParentPathCheck 7
    && tttLargeFiber36Block3Chunk2ParentPathCheck 8
    && tttLargeFiber36Block3Chunk2ParentPathCheck 9
    && tttLargeFiber36Block3Chunk2ParentPathCheck 10
    && tttLargeFiber36Block3Chunk2ParentPathCheck 11
    && tttLargeFiber36Block3Chunk2ParentPathCheck 12
    && tttLargeFiber36Block3Chunk2ParentPathCheck 13
    && tttLargeFiber36Block3Chunk2ParentPathCheck 14
    && tttLargeFiber36Block3Chunk2ParentPathCheck 15

theorem tttLargeFiber36Block3Chunk2ParentsAudit_ok :
    tttLargeFiber36Block3Chunk2ParentsAudit = true := by
  simp [tttLargeFiber36Block3Chunk2ParentsAudit,
    tttLargeFiber36Block3Chunk2ParentPath_0_ok,
    tttLargeFiber36Block3Chunk2ParentPath_1_ok,
    tttLargeFiber36Block3Chunk2ParentPath_2_ok,
    tttLargeFiber36Block3Chunk2ParentPath_3_ok,
    tttLargeFiber36Block3Chunk2ParentPath_4_ok,
    tttLargeFiber36Block3Chunk2ParentPath_5_ok,
    tttLargeFiber36Block3Chunk2ParentPath_6_ok,
    tttLargeFiber36Block3Chunk2ParentPath_7_ok,
    tttLargeFiber36Block3Chunk2ParentPath_8_ok,
    tttLargeFiber36Block3Chunk2ParentPath_9_ok,
    tttLargeFiber36Block3Chunk2ParentPath_10_ok,
    tttLargeFiber36Block3Chunk2ParentPath_11_ok,
    tttLargeFiber36Block3Chunk2ParentPath_12_ok,
    tttLargeFiber36Block3Chunk2ParentPath_13_ok,
    tttLargeFiber36Block3Chunk2ParentPath_14_ok,
    tttLargeFiber36Block3Chunk2ParentPath_15_ok]

def tttLargeFiber36Block3Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber36CountsAudit &&
    tttLargeFiber36Block3Chunk2SourcesCheck &&
    tttLargeFiber36Block3Chunk2RowsAudit &&
    tttLargeFiber36Block3Chunk2ParentMapAudit &&
    tttLargeFiber36Block3Chunk2ParentsAudit

theorem tttLargeFiber36Block3Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber36Block3Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber36Block3Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber36CountsAudit_ok,
    tttLargeFiber36Block3Chunk2SourcesCheck_ok,
    tttLargeFiber36Block3Chunk2RowsAudit_ok,
    tttLargeFiber36Block3Chunk2ParentMapAudit_ok,
    tttLargeFiber36Block3Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber36Block3Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
