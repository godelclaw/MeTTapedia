import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 36, block 3 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber36Block3Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber36Data

def tttLargeFiber36Block3Chunk3Sources : List Nat :=
  [   512, 513, 514, 515, 516, 517, 518, 519,
   520, 521, 522, 523, 524, 525, 526, 527]

def tttLargeFiber36Row240 : TripleComponentParentRow :=
  tripleRow 512 384 11 42 0 9 110 64
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber36Row241 : TripleComponentParentRow :=
  tripleRow 513 385 11 42 1 9 110 65
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber36Row242 : TripleComponentParentRow :=
  tripleRow 514 386 11 42 2 9 110 66
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber36Row243 : TripleComponentParentRow :=
  tripleRow 515 387 11 42 3 9 110 67
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber36Row244 : TripleComponentParentRow :=
  tripleRow 516 512 11 42 48 11 42 0
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row245 : TripleComponentParentRow :=
  tripleRow 517 513 11 42 49 11 42 1
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row246 : TripleComponentParentRow :=
  tripleRow 518 390 11 42 50 9 110 118
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.B7
    , chainEdge 2 TauEdge.B4
    ]

def tttLargeFiber36Row247 : TripleComponentParentRow :=
  tripleRow 519 391 11 42 51 9 110 119
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.B7
    , chainEdge 2 TauEdge.B4
    ]

def tttLargeFiber36Row248 : TripleComponentParentRow :=
  tripleRow 520 392 11 43 8 9 111 72
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber36Row249 : TripleComponentParentRow :=
  tripleRow 521 393 11 43 9 9 111 73
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber36Row250 : TripleComponentParentRow :=
  tripleRow 522 394 11 43 10 9 111 74
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber36Row251 : TripleComponentParentRow :=
  tripleRow 523 395 11 43 11 9 111 75
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber36Row252 : TripleComponentParentRow :=
  tripleRow 524 520 11 43 56 11 43 8
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row253 : TripleComponentParentRow :=
  tripleRow 525 521 11 43 57 11 43 9
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row254 : TripleComponentParentRow :=
  tripleRow 526 398 11 43 58 9 111 126
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.B7
    , chainEdge 2 TauEdge.B4
    ]

def tttLargeFiber36Row255 : TripleComponentParentRow :=
  tripleRow 527 399 11 43 59 9 111 127
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.B7
    , chainEdge 2 TauEdge.B4
    ]

def tttLargeFiber36Block3Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber36Row240
  , tttLargeFiber36Row241
  , tttLargeFiber36Row242
  , tttLargeFiber36Row243
  , tttLargeFiber36Row244
  , tttLargeFiber36Row245
  , tttLargeFiber36Row246
  , tttLargeFiber36Row247
  , tttLargeFiber36Row248
  , tttLargeFiber36Row249
  , tttLargeFiber36Row250
  , tttLargeFiber36Row251
  , tttLargeFiber36Row252
  , tttLargeFiber36Row253
  , tttLargeFiber36Row254
  , tttLargeFiber36Row255
  ]

def tttLargeFiber36Block3Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (272 <= i) && decide (i < 528)) ||
    (decide (1904 <= i) && decide (i < 2160))

def tttLargeFiber36Block3Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber36Block3Chunk3ExpectedContains row.source &&
    tttLargeFiber36Block3Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber36Key &&
          chainInputKey tttWord t == tttLargeFiber36Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber36Block3Chunk3SourcesCheck : Bool :=
  (tttLargeFiber36Block3Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber36Block3Chunk3Sources

theorem tttLargeFiber36Block3Chunk3SourcesCheck_ok :
    tttLargeFiber36Block3Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber36Block3Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber36Block3Chunk3RowValid
    (listGetD tttLargeFiber36Block3Chunk3Rows i default)

def tttLargeFiber36Block3Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber36Block3Chunk3Rows i default
  row.parent == tttLargeFiber36ParentOf row.source

def tttLargeFiber36Block3Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber36Block3Chunk3Sources 0 0 == 512
      && tttLargeFiber36ParentOf 512 == 384
      && tttLargeFiber36ParentOf 384 == 320
      && tttLargeFiber36ParentOf 320 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 1 => listGetD tttLargeFiber36Block3Chunk3Sources 1 0 == 513
      && tttLargeFiber36ParentOf 513 == 385
      && tttLargeFiber36ParentOf 385 == 321
      && tttLargeFiber36ParentOf 321 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 2 => listGetD tttLargeFiber36Block3Chunk3Sources 2 0 == 514
      && tttLargeFiber36ParentOf 514 == 386
      && tttLargeFiber36ParentOf 386 == 322
      && tttLargeFiber36ParentOf 322 == 282
      && tttLargeFiber36ParentOf 282 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 3 => listGetD tttLargeFiber36Block3Chunk3Sources 3 0 == 515
      && tttLargeFiber36ParentOf 515 == 387
      && tttLargeFiber36ParentOf 387 == 323
      && tttLargeFiber36ParentOf 323 == 283
      && tttLargeFiber36ParentOf 283 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (6 <= tttLargeFiber36MaxParentDepth)
  | 4 => listGetD tttLargeFiber36Block3Chunk3Sources 4 0 == 516
      && tttLargeFiber36ParentOf 516 == 512
      && tttLargeFiber36ParentOf 512 == 384
      && tttLargeFiber36ParentOf 384 == 320
      && tttLargeFiber36ParentOf 320 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 5 => listGetD tttLargeFiber36Block3Chunk3Sources 5 0 == 517
      && tttLargeFiber36ParentOf 517 == 513
      && tttLargeFiber36ParentOf 513 == 385
      && tttLargeFiber36ParentOf 385 == 321
      && tttLargeFiber36ParentOf 321 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (6 <= tttLargeFiber36MaxParentDepth)
  | 6 => listGetD tttLargeFiber36Block3Chunk3Sources 6 0 == 518
      && tttLargeFiber36ParentOf 518 == 390
      && tttLargeFiber36ParentOf 390 == 326
      && tttLargeFiber36ParentOf 326 == 286
      && tttLargeFiber36ParentOf 286 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (6 <= tttLargeFiber36MaxParentDepth)
  | 7 => listGetD tttLargeFiber36Block3Chunk3Sources 7 0 == 519
      && tttLargeFiber36ParentOf 519 == 391
      && tttLargeFiber36ParentOf 391 == 327
      && tttLargeFiber36ParentOf 327 == 287
      && tttLargeFiber36ParentOf 287 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 8 => listGetD tttLargeFiber36Block3Chunk3Sources 8 0 == 520
      && tttLargeFiber36ParentOf 520 == 392
      && tttLargeFiber36ParentOf 392 == 328
      && tttLargeFiber36ParentOf 328 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 9 => listGetD tttLargeFiber36Block3Chunk3Sources 9 0 == 521
      && tttLargeFiber36ParentOf 521 == 393
      && tttLargeFiber36ParentOf 393 == 329
      && tttLargeFiber36ParentOf 329 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 10 => listGetD tttLargeFiber36Block3Chunk3Sources 10 0 == 522
      && tttLargeFiber36ParentOf 522 == 394
      && tttLargeFiber36ParentOf 394 == 330
      && tttLargeFiber36ParentOf 330 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 11 => listGetD tttLargeFiber36Block3Chunk3Sources 11 0 == 523
      && tttLargeFiber36ParentOf 523 == 395
      && tttLargeFiber36ParentOf 395 == 331
      && tttLargeFiber36ParentOf 331 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 12 => listGetD tttLargeFiber36Block3Chunk3Sources 12 0 == 524
      && tttLargeFiber36ParentOf 524 == 520
      && tttLargeFiber36ParentOf 520 == 392
      && tttLargeFiber36ParentOf 392 == 328
      && tttLargeFiber36ParentOf 328 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 13 => listGetD tttLargeFiber36Block3Chunk3Sources 13 0 == 525
      && tttLargeFiber36ParentOf 525 == 521
      && tttLargeFiber36ParentOf 521 == 393
      && tttLargeFiber36ParentOf 393 == 329
      && tttLargeFiber36ParentOf 329 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 14 => listGetD tttLargeFiber36Block3Chunk3Sources 14 0 == 526
      && tttLargeFiber36ParentOf 526 == 398
      && tttLargeFiber36ParentOf 398 == 334
      && tttLargeFiber36ParentOf 334 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 15 => listGetD tttLargeFiber36Block3Chunk3Sources 15 0 == 527
      && tttLargeFiber36ParentOf 527 == 399
      && tttLargeFiber36ParentOf 399 == 335
      && tttLargeFiber36ParentOf 335 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | _ => false

theorem tttLargeFiber36Block3Chunk3Row_0_ok :
    tttLargeFiber36Block3Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3Row_1_ok :
    tttLargeFiber36Block3Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3Row_2_ok :
    tttLargeFiber36Block3Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3Row_3_ok :
    tttLargeFiber36Block3Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3Row_4_ok :
    tttLargeFiber36Block3Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3Row_5_ok :
    tttLargeFiber36Block3Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3Row_6_ok :
    tttLargeFiber36Block3Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3Row_7_ok :
    tttLargeFiber36Block3Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3Row_8_ok :
    tttLargeFiber36Block3Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3Row_9_ok :
    tttLargeFiber36Block3Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3Row_10_ok :
    tttLargeFiber36Block3Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3Row_11_ok :
    tttLargeFiber36Block3Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3Row_12_ok :
    tttLargeFiber36Block3Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3Row_13_ok :
    tttLargeFiber36Block3Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3Row_14_ok :
    tttLargeFiber36Block3Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3Row_15_ok :
    tttLargeFiber36Block3Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentMap_0_ok :
    tttLargeFiber36Block3Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentMap_1_ok :
    tttLargeFiber36Block3Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentMap_2_ok :
    tttLargeFiber36Block3Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentMap_3_ok :
    tttLargeFiber36Block3Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentMap_4_ok :
    tttLargeFiber36Block3Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentMap_5_ok :
    tttLargeFiber36Block3Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentMap_6_ok :
    tttLargeFiber36Block3Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentMap_7_ok :
    tttLargeFiber36Block3Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentMap_8_ok :
    tttLargeFiber36Block3Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentMap_9_ok :
    tttLargeFiber36Block3Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentMap_10_ok :
    tttLargeFiber36Block3Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentMap_11_ok :
    tttLargeFiber36Block3Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentMap_12_ok :
    tttLargeFiber36Block3Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentMap_13_ok :
    tttLargeFiber36Block3Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentMap_14_ok :
    tttLargeFiber36Block3Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentMap_15_ok :
    tttLargeFiber36Block3Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentPath_0_ok :
    tttLargeFiber36Block3Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentPath_1_ok :
    tttLargeFiber36Block3Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentPath_2_ok :
    tttLargeFiber36Block3Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentPath_3_ok :
    tttLargeFiber36Block3Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentPath_4_ok :
    tttLargeFiber36Block3Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentPath_5_ok :
    tttLargeFiber36Block3Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentPath_6_ok :
    tttLargeFiber36Block3Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentPath_7_ok :
    tttLargeFiber36Block3Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentPath_8_ok :
    tttLargeFiber36Block3Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentPath_9_ok :
    tttLargeFiber36Block3Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentPath_10_ok :
    tttLargeFiber36Block3Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentPath_11_ok :
    tttLargeFiber36Block3Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentPath_12_ok :
    tttLargeFiber36Block3Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentPath_13_ok :
    tttLargeFiber36Block3Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentPath_14_ok :
    tttLargeFiber36Block3Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber36Block3Chunk3ParentPath_15_ok :
    tttLargeFiber36Block3Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber36Block3Chunk3RowsAudit : Bool :=
  tttLargeFiber36Block3Chunk3RowCheck 0
    && tttLargeFiber36Block3Chunk3RowCheck 1
    && tttLargeFiber36Block3Chunk3RowCheck 2
    && tttLargeFiber36Block3Chunk3RowCheck 3
    && tttLargeFiber36Block3Chunk3RowCheck 4
    && tttLargeFiber36Block3Chunk3RowCheck 5
    && tttLargeFiber36Block3Chunk3RowCheck 6
    && tttLargeFiber36Block3Chunk3RowCheck 7
    && tttLargeFiber36Block3Chunk3RowCheck 8
    && tttLargeFiber36Block3Chunk3RowCheck 9
    && tttLargeFiber36Block3Chunk3RowCheck 10
    && tttLargeFiber36Block3Chunk3RowCheck 11
    && tttLargeFiber36Block3Chunk3RowCheck 12
    && tttLargeFiber36Block3Chunk3RowCheck 13
    && tttLargeFiber36Block3Chunk3RowCheck 14
    && tttLargeFiber36Block3Chunk3RowCheck 15

theorem tttLargeFiber36Block3Chunk3RowsAudit_ok :
    tttLargeFiber36Block3Chunk3RowsAudit = true := by
  simp [tttLargeFiber36Block3Chunk3RowsAudit,
    tttLargeFiber36Block3Chunk3Row_0_ok,
    tttLargeFiber36Block3Chunk3Row_1_ok,
    tttLargeFiber36Block3Chunk3Row_2_ok,
    tttLargeFiber36Block3Chunk3Row_3_ok,
    tttLargeFiber36Block3Chunk3Row_4_ok,
    tttLargeFiber36Block3Chunk3Row_5_ok,
    tttLargeFiber36Block3Chunk3Row_6_ok,
    tttLargeFiber36Block3Chunk3Row_7_ok,
    tttLargeFiber36Block3Chunk3Row_8_ok,
    tttLargeFiber36Block3Chunk3Row_9_ok,
    tttLargeFiber36Block3Chunk3Row_10_ok,
    tttLargeFiber36Block3Chunk3Row_11_ok,
    tttLargeFiber36Block3Chunk3Row_12_ok,
    tttLargeFiber36Block3Chunk3Row_13_ok,
    tttLargeFiber36Block3Chunk3Row_14_ok,
    tttLargeFiber36Block3Chunk3Row_15_ok]

def tttLargeFiber36Block3Chunk3ParentMapAudit : Bool :=
  tttLargeFiber36Block3Chunk3ParentMapCheck 0
    && tttLargeFiber36Block3Chunk3ParentMapCheck 1
    && tttLargeFiber36Block3Chunk3ParentMapCheck 2
    && tttLargeFiber36Block3Chunk3ParentMapCheck 3
    && tttLargeFiber36Block3Chunk3ParentMapCheck 4
    && tttLargeFiber36Block3Chunk3ParentMapCheck 5
    && tttLargeFiber36Block3Chunk3ParentMapCheck 6
    && tttLargeFiber36Block3Chunk3ParentMapCheck 7
    && tttLargeFiber36Block3Chunk3ParentMapCheck 8
    && tttLargeFiber36Block3Chunk3ParentMapCheck 9
    && tttLargeFiber36Block3Chunk3ParentMapCheck 10
    && tttLargeFiber36Block3Chunk3ParentMapCheck 11
    && tttLargeFiber36Block3Chunk3ParentMapCheck 12
    && tttLargeFiber36Block3Chunk3ParentMapCheck 13
    && tttLargeFiber36Block3Chunk3ParentMapCheck 14
    && tttLargeFiber36Block3Chunk3ParentMapCheck 15

theorem tttLargeFiber36Block3Chunk3ParentMapAudit_ok :
    tttLargeFiber36Block3Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber36Block3Chunk3ParentMapAudit,
    tttLargeFiber36Block3Chunk3ParentMap_0_ok,
    tttLargeFiber36Block3Chunk3ParentMap_1_ok,
    tttLargeFiber36Block3Chunk3ParentMap_2_ok,
    tttLargeFiber36Block3Chunk3ParentMap_3_ok,
    tttLargeFiber36Block3Chunk3ParentMap_4_ok,
    tttLargeFiber36Block3Chunk3ParentMap_5_ok,
    tttLargeFiber36Block3Chunk3ParentMap_6_ok,
    tttLargeFiber36Block3Chunk3ParentMap_7_ok,
    tttLargeFiber36Block3Chunk3ParentMap_8_ok,
    tttLargeFiber36Block3Chunk3ParentMap_9_ok,
    tttLargeFiber36Block3Chunk3ParentMap_10_ok,
    tttLargeFiber36Block3Chunk3ParentMap_11_ok,
    tttLargeFiber36Block3Chunk3ParentMap_12_ok,
    tttLargeFiber36Block3Chunk3ParentMap_13_ok,
    tttLargeFiber36Block3Chunk3ParentMap_14_ok,
    tttLargeFiber36Block3Chunk3ParentMap_15_ok]

def tttLargeFiber36Block3Chunk3ParentsAudit : Bool :=
  tttLargeFiber36Block3Chunk3ParentPathCheck 0
    && tttLargeFiber36Block3Chunk3ParentPathCheck 1
    && tttLargeFiber36Block3Chunk3ParentPathCheck 2
    && tttLargeFiber36Block3Chunk3ParentPathCheck 3
    && tttLargeFiber36Block3Chunk3ParentPathCheck 4
    && tttLargeFiber36Block3Chunk3ParentPathCheck 5
    && tttLargeFiber36Block3Chunk3ParentPathCheck 6
    && tttLargeFiber36Block3Chunk3ParentPathCheck 7
    && tttLargeFiber36Block3Chunk3ParentPathCheck 8
    && tttLargeFiber36Block3Chunk3ParentPathCheck 9
    && tttLargeFiber36Block3Chunk3ParentPathCheck 10
    && tttLargeFiber36Block3Chunk3ParentPathCheck 11
    && tttLargeFiber36Block3Chunk3ParentPathCheck 12
    && tttLargeFiber36Block3Chunk3ParentPathCheck 13
    && tttLargeFiber36Block3Chunk3ParentPathCheck 14
    && tttLargeFiber36Block3Chunk3ParentPathCheck 15

theorem tttLargeFiber36Block3Chunk3ParentsAudit_ok :
    tttLargeFiber36Block3Chunk3ParentsAudit = true := by
  simp [tttLargeFiber36Block3Chunk3ParentsAudit,
    tttLargeFiber36Block3Chunk3ParentPath_0_ok,
    tttLargeFiber36Block3Chunk3ParentPath_1_ok,
    tttLargeFiber36Block3Chunk3ParentPath_2_ok,
    tttLargeFiber36Block3Chunk3ParentPath_3_ok,
    tttLargeFiber36Block3Chunk3ParentPath_4_ok,
    tttLargeFiber36Block3Chunk3ParentPath_5_ok,
    tttLargeFiber36Block3Chunk3ParentPath_6_ok,
    tttLargeFiber36Block3Chunk3ParentPath_7_ok,
    tttLargeFiber36Block3Chunk3ParentPath_8_ok,
    tttLargeFiber36Block3Chunk3ParentPath_9_ok,
    tttLargeFiber36Block3Chunk3ParentPath_10_ok,
    tttLargeFiber36Block3Chunk3ParentPath_11_ok,
    tttLargeFiber36Block3Chunk3ParentPath_12_ok,
    tttLargeFiber36Block3Chunk3ParentPath_13_ok,
    tttLargeFiber36Block3Chunk3ParentPath_14_ok,
    tttLargeFiber36Block3Chunk3ParentPath_15_ok]

def tttLargeFiber36Block3Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber36CountsAudit &&
    tttLargeFiber36Block3Chunk3SourcesCheck &&
    tttLargeFiber36Block3Chunk3RowsAudit &&
    tttLargeFiber36Block3Chunk3ParentMapAudit &&
    tttLargeFiber36Block3Chunk3ParentsAudit

theorem tttLargeFiber36Block3Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber36Block3Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber36Block3Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber36CountsAudit_ok,
    tttLargeFiber36Block3Chunk3SourcesCheck_ok,
    tttLargeFiber36Block3Chunk3RowsAudit_ok,
    tttLargeFiber36Block3Chunk3ParentMapAudit_ok,
    tttLargeFiber36Block3Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber36Block3Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
