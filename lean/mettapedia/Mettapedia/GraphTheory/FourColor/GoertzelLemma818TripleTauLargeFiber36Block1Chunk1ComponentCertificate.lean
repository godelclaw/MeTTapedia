import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 36, block 1 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber36Block1Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber36Data

def tttLargeFiber36Block1Chunk1Sources : List Nat :=
  [   352, 353, 354, 355, 356, 357, 358, 359,
   360, 361, 362, 363, 364, 365, 366, 367]

def tttLargeFiber36Row80 : TripleComponentParentRow :=
  tripleRow 352 288 9 90 16 8 82 16
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row81 : TripleComponentParentRow :=
  tripleRow 353 289 9 90 17 8 82 17
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row82 : TripleComponentParentRow :=
  tripleRow 354 290 9 90 18 8 82 18
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row83 : TripleComponentParentRow :=
  tripleRow 355 291 9 90 19 8 82 19
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row84 : TripleComponentParentRow :=
  tripleRow 356 292 9 90 32 8 82 32
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row85 : TripleComponentParentRow :=
  tripleRow 357 293 9 90 33 8 82 33
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row86 : TripleComponentParentRow :=
  tripleRow 358 294 9 90 34 8 82 34
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row87 : TripleComponentParentRow :=
  tripleRow 359 295 9 90 35 8 82 35
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row88 : TripleComponentParentRow :=
  tripleRow 360 296 9 91 24 8 83 24
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row89 : TripleComponentParentRow :=
  tripleRow 361 297 9 91 25 8 83 25
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row90 : TripleComponentParentRow :=
  tripleRow 362 298 9 91 26 8 83 26
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row91 : TripleComponentParentRow :=
  tripleRow 363 299 9 91 27 8 83 27
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row92 : TripleComponentParentRow :=
  tripleRow 364 300 9 91 40 8 83 40
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row93 : TripleComponentParentRow :=
  tripleRow 365 301 9 91 41 8 83 41
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row94 : TripleComponentParentRow :=
  tripleRow 366 302 9 91 42 8 83 42
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row95 : TripleComponentParentRow :=
  tripleRow 367 303 9 91 43 8 83 43
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Block1Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber36Row80
  , tttLargeFiber36Row81
  , tttLargeFiber36Row82
  , tttLargeFiber36Row83
  , tttLargeFiber36Row84
  , tttLargeFiber36Row85
  , tttLargeFiber36Row86
  , tttLargeFiber36Row87
  , tttLargeFiber36Row88
  , tttLargeFiber36Row89
  , tttLargeFiber36Row90
  , tttLargeFiber36Row91
  , tttLargeFiber36Row92
  , tttLargeFiber36Row93
  , tttLargeFiber36Row94
  , tttLargeFiber36Row95
  ]

def tttLargeFiber36Block1Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (272 <= i) && decide (i < 528)) ||
    (decide (1904 <= i) && decide (i < 2160))

def tttLargeFiber36Block1Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber36Block1Chunk1ExpectedContains row.source &&
    tttLargeFiber36Block1Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber36Key &&
          chainInputKey tttWord t == tttLargeFiber36Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber36Block1Chunk1SourcesCheck : Bool :=
  (tttLargeFiber36Block1Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber36Block1Chunk1Sources

theorem tttLargeFiber36Block1Chunk1SourcesCheck_ok :
    tttLargeFiber36Block1Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber36Block1Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber36Block1Chunk1RowValid
    (listGetD tttLargeFiber36Block1Chunk1Rows i default)

def tttLargeFiber36Block1Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber36Block1Chunk1Rows i default
  row.parent == tttLargeFiber36ParentOf row.source

def tttLargeFiber36Block1Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber36Block1Chunk1Sources 0 0 == 352
      && tttLargeFiber36ParentOf 352 == 288
      && tttLargeFiber36ParentOf 288 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 1 => listGetD tttLargeFiber36Block1Chunk1Sources 1 0 == 353
      && tttLargeFiber36ParentOf 353 == 289
      && tttLargeFiber36ParentOf 289 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 2 => listGetD tttLargeFiber36Block1Chunk1Sources 2 0 == 354
      && tttLargeFiber36ParentOf 354 == 290
      && tttLargeFiber36ParentOf 290 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 3 => listGetD tttLargeFiber36Block1Chunk1Sources 3 0 == 355
      && tttLargeFiber36ParentOf 355 == 291
      && tttLargeFiber36ParentOf 291 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 4 => listGetD tttLargeFiber36Block1Chunk1Sources 4 0 == 356
      && tttLargeFiber36ParentOf 356 == 292
      && tttLargeFiber36ParentOf 292 == 288
      && tttLargeFiber36ParentOf 288 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 5 => listGetD tttLargeFiber36Block1Chunk1Sources 5 0 == 357
      && tttLargeFiber36ParentOf 357 == 293
      && tttLargeFiber36ParentOf 293 == 289
      && tttLargeFiber36ParentOf 289 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 6 => listGetD tttLargeFiber36Block1Chunk1Sources 6 0 == 358
      && tttLargeFiber36ParentOf 358 == 294
      && tttLargeFiber36ParentOf 294 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 7 => listGetD tttLargeFiber36Block1Chunk1Sources 7 0 == 359
      && tttLargeFiber36ParentOf 359 == 295
      && tttLargeFiber36ParentOf 295 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 8 => listGetD tttLargeFiber36Block1Chunk1Sources 8 0 == 360
      && tttLargeFiber36ParentOf 360 == 296
      && tttLargeFiber36ParentOf 296 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 9 => listGetD tttLargeFiber36Block1Chunk1Sources 9 0 == 361
      && tttLargeFiber36ParentOf 361 == 297
      && tttLargeFiber36ParentOf 297 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 10 => listGetD tttLargeFiber36Block1Chunk1Sources 10 0 == 362
      && tttLargeFiber36ParentOf 362 == 298
      && tttLargeFiber36ParentOf 298 == 282
      && tttLargeFiber36ParentOf 282 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 11 => listGetD tttLargeFiber36Block1Chunk1Sources 11 0 == 363
      && tttLargeFiber36ParentOf 363 == 299
      && tttLargeFiber36ParentOf 299 == 283
      && tttLargeFiber36ParentOf 283 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 12 => listGetD tttLargeFiber36Block1Chunk1Sources 12 0 == 364
      && tttLargeFiber36ParentOf 364 == 300
      && tttLargeFiber36ParentOf 300 == 296
      && tttLargeFiber36ParentOf 296 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 13 => listGetD tttLargeFiber36Block1Chunk1Sources 13 0 == 365
      && tttLargeFiber36ParentOf 365 == 301
      && tttLargeFiber36ParentOf 301 == 297
      && tttLargeFiber36ParentOf 297 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 14 => listGetD tttLargeFiber36Block1Chunk1Sources 14 0 == 366
      && tttLargeFiber36ParentOf 366 == 302
      && tttLargeFiber36ParentOf 302 == 286
      && tttLargeFiber36ParentOf 286 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 15 => listGetD tttLargeFiber36Block1Chunk1Sources 15 0 == 367
      && tttLargeFiber36ParentOf 367 == 303
      && tttLargeFiber36ParentOf 303 == 287
      && tttLargeFiber36ParentOf 287 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | _ => false

theorem tttLargeFiber36Block1Chunk1Row_0_ok :
    tttLargeFiber36Block1Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1Row_1_ok :
    tttLargeFiber36Block1Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1Row_2_ok :
    tttLargeFiber36Block1Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1Row_3_ok :
    tttLargeFiber36Block1Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1Row_4_ok :
    tttLargeFiber36Block1Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1Row_5_ok :
    tttLargeFiber36Block1Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1Row_6_ok :
    tttLargeFiber36Block1Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1Row_7_ok :
    tttLargeFiber36Block1Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1Row_8_ok :
    tttLargeFiber36Block1Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1Row_9_ok :
    tttLargeFiber36Block1Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1Row_10_ok :
    tttLargeFiber36Block1Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1Row_11_ok :
    tttLargeFiber36Block1Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1Row_12_ok :
    tttLargeFiber36Block1Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1Row_13_ok :
    tttLargeFiber36Block1Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1Row_14_ok :
    tttLargeFiber36Block1Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1Row_15_ok :
    tttLargeFiber36Block1Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentMap_0_ok :
    tttLargeFiber36Block1Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentMap_1_ok :
    tttLargeFiber36Block1Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentMap_2_ok :
    tttLargeFiber36Block1Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentMap_3_ok :
    tttLargeFiber36Block1Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentMap_4_ok :
    tttLargeFiber36Block1Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentMap_5_ok :
    tttLargeFiber36Block1Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentMap_6_ok :
    tttLargeFiber36Block1Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentMap_7_ok :
    tttLargeFiber36Block1Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentMap_8_ok :
    tttLargeFiber36Block1Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentMap_9_ok :
    tttLargeFiber36Block1Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentMap_10_ok :
    tttLargeFiber36Block1Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentMap_11_ok :
    tttLargeFiber36Block1Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentMap_12_ok :
    tttLargeFiber36Block1Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentMap_13_ok :
    tttLargeFiber36Block1Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentMap_14_ok :
    tttLargeFiber36Block1Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentMap_15_ok :
    tttLargeFiber36Block1Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentPath_0_ok :
    tttLargeFiber36Block1Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentPath_1_ok :
    tttLargeFiber36Block1Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentPath_2_ok :
    tttLargeFiber36Block1Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentPath_3_ok :
    tttLargeFiber36Block1Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentPath_4_ok :
    tttLargeFiber36Block1Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentPath_5_ok :
    tttLargeFiber36Block1Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentPath_6_ok :
    tttLargeFiber36Block1Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentPath_7_ok :
    tttLargeFiber36Block1Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentPath_8_ok :
    tttLargeFiber36Block1Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentPath_9_ok :
    tttLargeFiber36Block1Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentPath_10_ok :
    tttLargeFiber36Block1Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentPath_11_ok :
    tttLargeFiber36Block1Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentPath_12_ok :
    tttLargeFiber36Block1Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentPath_13_ok :
    tttLargeFiber36Block1Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentPath_14_ok :
    tttLargeFiber36Block1Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber36Block1Chunk1ParentPath_15_ok :
    tttLargeFiber36Block1Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber36Block1Chunk1RowsAudit : Bool :=
  tttLargeFiber36Block1Chunk1RowCheck 0
    && tttLargeFiber36Block1Chunk1RowCheck 1
    && tttLargeFiber36Block1Chunk1RowCheck 2
    && tttLargeFiber36Block1Chunk1RowCheck 3
    && tttLargeFiber36Block1Chunk1RowCheck 4
    && tttLargeFiber36Block1Chunk1RowCheck 5
    && tttLargeFiber36Block1Chunk1RowCheck 6
    && tttLargeFiber36Block1Chunk1RowCheck 7
    && tttLargeFiber36Block1Chunk1RowCheck 8
    && tttLargeFiber36Block1Chunk1RowCheck 9
    && tttLargeFiber36Block1Chunk1RowCheck 10
    && tttLargeFiber36Block1Chunk1RowCheck 11
    && tttLargeFiber36Block1Chunk1RowCheck 12
    && tttLargeFiber36Block1Chunk1RowCheck 13
    && tttLargeFiber36Block1Chunk1RowCheck 14
    && tttLargeFiber36Block1Chunk1RowCheck 15

theorem tttLargeFiber36Block1Chunk1RowsAudit_ok :
    tttLargeFiber36Block1Chunk1RowsAudit = true := by
  simp [tttLargeFiber36Block1Chunk1RowsAudit,
    tttLargeFiber36Block1Chunk1Row_0_ok,
    tttLargeFiber36Block1Chunk1Row_1_ok,
    tttLargeFiber36Block1Chunk1Row_2_ok,
    tttLargeFiber36Block1Chunk1Row_3_ok,
    tttLargeFiber36Block1Chunk1Row_4_ok,
    tttLargeFiber36Block1Chunk1Row_5_ok,
    tttLargeFiber36Block1Chunk1Row_6_ok,
    tttLargeFiber36Block1Chunk1Row_7_ok,
    tttLargeFiber36Block1Chunk1Row_8_ok,
    tttLargeFiber36Block1Chunk1Row_9_ok,
    tttLargeFiber36Block1Chunk1Row_10_ok,
    tttLargeFiber36Block1Chunk1Row_11_ok,
    tttLargeFiber36Block1Chunk1Row_12_ok,
    tttLargeFiber36Block1Chunk1Row_13_ok,
    tttLargeFiber36Block1Chunk1Row_14_ok,
    tttLargeFiber36Block1Chunk1Row_15_ok]

def tttLargeFiber36Block1Chunk1ParentMapAudit : Bool :=
  tttLargeFiber36Block1Chunk1ParentMapCheck 0
    && tttLargeFiber36Block1Chunk1ParentMapCheck 1
    && tttLargeFiber36Block1Chunk1ParentMapCheck 2
    && tttLargeFiber36Block1Chunk1ParentMapCheck 3
    && tttLargeFiber36Block1Chunk1ParentMapCheck 4
    && tttLargeFiber36Block1Chunk1ParentMapCheck 5
    && tttLargeFiber36Block1Chunk1ParentMapCheck 6
    && tttLargeFiber36Block1Chunk1ParentMapCheck 7
    && tttLargeFiber36Block1Chunk1ParentMapCheck 8
    && tttLargeFiber36Block1Chunk1ParentMapCheck 9
    && tttLargeFiber36Block1Chunk1ParentMapCheck 10
    && tttLargeFiber36Block1Chunk1ParentMapCheck 11
    && tttLargeFiber36Block1Chunk1ParentMapCheck 12
    && tttLargeFiber36Block1Chunk1ParentMapCheck 13
    && tttLargeFiber36Block1Chunk1ParentMapCheck 14
    && tttLargeFiber36Block1Chunk1ParentMapCheck 15

theorem tttLargeFiber36Block1Chunk1ParentMapAudit_ok :
    tttLargeFiber36Block1Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber36Block1Chunk1ParentMapAudit,
    tttLargeFiber36Block1Chunk1ParentMap_0_ok,
    tttLargeFiber36Block1Chunk1ParentMap_1_ok,
    tttLargeFiber36Block1Chunk1ParentMap_2_ok,
    tttLargeFiber36Block1Chunk1ParentMap_3_ok,
    tttLargeFiber36Block1Chunk1ParentMap_4_ok,
    tttLargeFiber36Block1Chunk1ParentMap_5_ok,
    tttLargeFiber36Block1Chunk1ParentMap_6_ok,
    tttLargeFiber36Block1Chunk1ParentMap_7_ok,
    tttLargeFiber36Block1Chunk1ParentMap_8_ok,
    tttLargeFiber36Block1Chunk1ParentMap_9_ok,
    tttLargeFiber36Block1Chunk1ParentMap_10_ok,
    tttLargeFiber36Block1Chunk1ParentMap_11_ok,
    tttLargeFiber36Block1Chunk1ParentMap_12_ok,
    tttLargeFiber36Block1Chunk1ParentMap_13_ok,
    tttLargeFiber36Block1Chunk1ParentMap_14_ok,
    tttLargeFiber36Block1Chunk1ParentMap_15_ok]

def tttLargeFiber36Block1Chunk1ParentsAudit : Bool :=
  tttLargeFiber36Block1Chunk1ParentPathCheck 0
    && tttLargeFiber36Block1Chunk1ParentPathCheck 1
    && tttLargeFiber36Block1Chunk1ParentPathCheck 2
    && tttLargeFiber36Block1Chunk1ParentPathCheck 3
    && tttLargeFiber36Block1Chunk1ParentPathCheck 4
    && tttLargeFiber36Block1Chunk1ParentPathCheck 5
    && tttLargeFiber36Block1Chunk1ParentPathCheck 6
    && tttLargeFiber36Block1Chunk1ParentPathCheck 7
    && tttLargeFiber36Block1Chunk1ParentPathCheck 8
    && tttLargeFiber36Block1Chunk1ParentPathCheck 9
    && tttLargeFiber36Block1Chunk1ParentPathCheck 10
    && tttLargeFiber36Block1Chunk1ParentPathCheck 11
    && tttLargeFiber36Block1Chunk1ParentPathCheck 12
    && tttLargeFiber36Block1Chunk1ParentPathCheck 13
    && tttLargeFiber36Block1Chunk1ParentPathCheck 14
    && tttLargeFiber36Block1Chunk1ParentPathCheck 15

theorem tttLargeFiber36Block1Chunk1ParentsAudit_ok :
    tttLargeFiber36Block1Chunk1ParentsAudit = true := by
  simp [tttLargeFiber36Block1Chunk1ParentsAudit,
    tttLargeFiber36Block1Chunk1ParentPath_0_ok,
    tttLargeFiber36Block1Chunk1ParentPath_1_ok,
    tttLargeFiber36Block1Chunk1ParentPath_2_ok,
    tttLargeFiber36Block1Chunk1ParentPath_3_ok,
    tttLargeFiber36Block1Chunk1ParentPath_4_ok,
    tttLargeFiber36Block1Chunk1ParentPath_5_ok,
    tttLargeFiber36Block1Chunk1ParentPath_6_ok,
    tttLargeFiber36Block1Chunk1ParentPath_7_ok,
    tttLargeFiber36Block1Chunk1ParentPath_8_ok,
    tttLargeFiber36Block1Chunk1ParentPath_9_ok,
    tttLargeFiber36Block1Chunk1ParentPath_10_ok,
    tttLargeFiber36Block1Chunk1ParentPath_11_ok,
    tttLargeFiber36Block1Chunk1ParentPath_12_ok,
    tttLargeFiber36Block1Chunk1ParentPath_13_ok,
    tttLargeFiber36Block1Chunk1ParentPath_14_ok,
    tttLargeFiber36Block1Chunk1ParentPath_15_ok]

def tttLargeFiber36Block1Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber36CountsAudit &&
    tttLargeFiber36Block1Chunk1SourcesCheck &&
    tttLargeFiber36Block1Chunk1RowsAudit &&
    tttLargeFiber36Block1Chunk1ParentMapAudit &&
    tttLargeFiber36Block1Chunk1ParentsAudit

theorem tttLargeFiber36Block1Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber36Block1Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber36Block1Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber36CountsAudit_ok,
    tttLargeFiber36Block1Chunk1SourcesCheck_ok,
    tttLargeFiber36Block1Chunk1RowsAudit_ok,
    tttLargeFiber36Block1Chunk1ParentMapAudit_ok,
    tttLargeFiber36Block1Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber36Block1Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
