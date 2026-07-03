import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 36, block 6 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber36Block6Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber36Data

def tttLargeFiber36Block6Chunk1Sources : List Nat :=
  [   2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055,
   2056, 2057, 2058, 2059, 2060, 2061, 2062, 2063]

def tttLargeFiber36Row400 : TripleComponentParentRow :=
  tripleRow 2048 416 58 2 16 10 18 16
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row401 : TripleComponentParentRow :=
  tripleRow 2049 417 58 2 17 10 18 17
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row402 : TripleComponentParentRow :=
  tripleRow 2050 418 58 2 18 10 18 18
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row403 : TripleComponentParentRow :=
  tripleRow 2051 419 58 2 19 10 18 19
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row404 : TripleComponentParentRow :=
  tripleRow 2052 420 58 2 32 10 18 32
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row405 : TripleComponentParentRow :=
  tripleRow 2053 421 58 2 33 10 18 33
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row406 : TripleComponentParentRow :=
  tripleRow 2054 422 58 2 34 10 18 34
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row407 : TripleComponentParentRow :=
  tripleRow 2055 423 58 2 35 10 18 35
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row408 : TripleComponentParentRow :=
  tripleRow 2056 424 58 3 24 10 19 24
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row409 : TripleComponentParentRow :=
  tripleRow 2057 425 58 3 25 10 19 25
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row410 : TripleComponentParentRow :=
  tripleRow 2058 426 58 3 26 10 19 26
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row411 : TripleComponentParentRow :=
  tripleRow 2059 427 58 3 27 10 19 27
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row412 : TripleComponentParentRow :=
  tripleRow 2060 428 58 3 40 10 19 40
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row413 : TripleComponentParentRow :=
  tripleRow 2061 429 58 3 41 10 19 41
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row414 : TripleComponentParentRow :=
  tripleRow 2062 430 58 3 42 10 19 42
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row415 : TripleComponentParentRow :=
  tripleRow 2063 431 58 3 43 10 19 43
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Block6Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber36Row400
  , tttLargeFiber36Row401
  , tttLargeFiber36Row402
  , tttLargeFiber36Row403
  , tttLargeFiber36Row404
  , tttLargeFiber36Row405
  , tttLargeFiber36Row406
  , tttLargeFiber36Row407
  , tttLargeFiber36Row408
  , tttLargeFiber36Row409
  , tttLargeFiber36Row410
  , tttLargeFiber36Row411
  , tttLargeFiber36Row412
  , tttLargeFiber36Row413
  , tttLargeFiber36Row414
  , tttLargeFiber36Row415
  ]

def tttLargeFiber36Block6Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (272 <= i) && decide (i < 528)) ||
    (decide (1904 <= i) && decide (i < 2160))

def tttLargeFiber36Block6Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber36Block6Chunk1ExpectedContains row.source &&
    tttLargeFiber36Block6Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber36Key &&
          chainInputKey tttWord t == tttLargeFiber36Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber36Block6Chunk1SourcesCheck : Bool :=
  (tttLargeFiber36Block6Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber36Block6Chunk1Sources

theorem tttLargeFiber36Block6Chunk1SourcesCheck_ok :
    tttLargeFiber36Block6Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber36Block6Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber36Block6Chunk1RowValid
    (listGetD tttLargeFiber36Block6Chunk1Rows i default)

def tttLargeFiber36Block6Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber36Block6Chunk1Rows i default
  row.parent == tttLargeFiber36ParentOf row.source

def tttLargeFiber36Block6Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber36Block6Chunk1Sources 0 0 == 2048
      && tttLargeFiber36ParentOf 2048 == 416
      && tttLargeFiber36ParentOf 416 == 288
      && tttLargeFiber36ParentOf 288 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 1 => listGetD tttLargeFiber36Block6Chunk1Sources 1 0 == 2049
      && tttLargeFiber36ParentOf 2049 == 417
      && tttLargeFiber36ParentOf 417 == 289
      && tttLargeFiber36ParentOf 289 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 2 => listGetD tttLargeFiber36Block6Chunk1Sources 2 0 == 2050
      && tttLargeFiber36ParentOf 2050 == 418
      && tttLargeFiber36ParentOf 418 == 290
      && tttLargeFiber36ParentOf 290 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 3 => listGetD tttLargeFiber36Block6Chunk1Sources 3 0 == 2051
      && tttLargeFiber36ParentOf 2051 == 419
      && tttLargeFiber36ParentOf 419 == 291
      && tttLargeFiber36ParentOf 291 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 4 => listGetD tttLargeFiber36Block6Chunk1Sources 4 0 == 2052
      && tttLargeFiber36ParentOf 2052 == 420
      && tttLargeFiber36ParentOf 420 == 292
      && tttLargeFiber36ParentOf 292 == 288
      && tttLargeFiber36ParentOf 288 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 5 => listGetD tttLargeFiber36Block6Chunk1Sources 5 0 == 2053
      && tttLargeFiber36ParentOf 2053 == 421
      && tttLargeFiber36ParentOf 421 == 293
      && tttLargeFiber36ParentOf 293 == 289
      && tttLargeFiber36ParentOf 289 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 6 => listGetD tttLargeFiber36Block6Chunk1Sources 6 0 == 2054
      && tttLargeFiber36ParentOf 2054 == 422
      && tttLargeFiber36ParentOf 422 == 294
      && tttLargeFiber36ParentOf 294 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 7 => listGetD tttLargeFiber36Block6Chunk1Sources 7 0 == 2055
      && tttLargeFiber36ParentOf 2055 == 423
      && tttLargeFiber36ParentOf 423 == 295
      && tttLargeFiber36ParentOf 295 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 8 => listGetD tttLargeFiber36Block6Chunk1Sources 8 0 == 2056
      && tttLargeFiber36ParentOf 2056 == 424
      && tttLargeFiber36ParentOf 424 == 296
      && tttLargeFiber36ParentOf 296 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 9 => listGetD tttLargeFiber36Block6Chunk1Sources 9 0 == 2057
      && tttLargeFiber36ParentOf 2057 == 425
      && tttLargeFiber36ParentOf 425 == 297
      && tttLargeFiber36ParentOf 297 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 10 => listGetD tttLargeFiber36Block6Chunk1Sources 10 0 == 2058
      && tttLargeFiber36ParentOf 2058 == 426
      && tttLargeFiber36ParentOf 426 == 298
      && tttLargeFiber36ParentOf 298 == 282
      && tttLargeFiber36ParentOf 282 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 11 => listGetD tttLargeFiber36Block6Chunk1Sources 11 0 == 2059
      && tttLargeFiber36ParentOf 2059 == 427
      && tttLargeFiber36ParentOf 427 == 299
      && tttLargeFiber36ParentOf 299 == 283
      && tttLargeFiber36ParentOf 283 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (6 <= tttLargeFiber36MaxParentDepth)
  | 12 => listGetD tttLargeFiber36Block6Chunk1Sources 12 0 == 2060
      && tttLargeFiber36ParentOf 2060 == 428
      && tttLargeFiber36ParentOf 428 == 300
      && tttLargeFiber36ParentOf 300 == 296
      && tttLargeFiber36ParentOf 296 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 13 => listGetD tttLargeFiber36Block6Chunk1Sources 13 0 == 2061
      && tttLargeFiber36ParentOf 2061 == 429
      && tttLargeFiber36ParentOf 429 == 301
      && tttLargeFiber36ParentOf 301 == 297
      && tttLargeFiber36ParentOf 297 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (6 <= tttLargeFiber36MaxParentDepth)
  | 14 => listGetD tttLargeFiber36Block6Chunk1Sources 14 0 == 2062
      && tttLargeFiber36ParentOf 2062 == 430
      && tttLargeFiber36ParentOf 430 == 302
      && tttLargeFiber36ParentOf 302 == 286
      && tttLargeFiber36ParentOf 286 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (6 <= tttLargeFiber36MaxParentDepth)
  | 15 => listGetD tttLargeFiber36Block6Chunk1Sources 15 0 == 2063
      && tttLargeFiber36ParentOf 2063 == 431
      && tttLargeFiber36ParentOf 431 == 303
      && tttLargeFiber36ParentOf 303 == 287
      && tttLargeFiber36ParentOf 287 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | _ => false

theorem tttLargeFiber36Block6Chunk1Row_0_ok :
    tttLargeFiber36Block6Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1Row_1_ok :
    tttLargeFiber36Block6Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1Row_2_ok :
    tttLargeFiber36Block6Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1Row_3_ok :
    tttLargeFiber36Block6Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1Row_4_ok :
    tttLargeFiber36Block6Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1Row_5_ok :
    tttLargeFiber36Block6Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1Row_6_ok :
    tttLargeFiber36Block6Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1Row_7_ok :
    tttLargeFiber36Block6Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1Row_8_ok :
    tttLargeFiber36Block6Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1Row_9_ok :
    tttLargeFiber36Block6Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1Row_10_ok :
    tttLargeFiber36Block6Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1Row_11_ok :
    tttLargeFiber36Block6Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1Row_12_ok :
    tttLargeFiber36Block6Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1Row_13_ok :
    tttLargeFiber36Block6Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1Row_14_ok :
    tttLargeFiber36Block6Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1Row_15_ok :
    tttLargeFiber36Block6Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentMap_0_ok :
    tttLargeFiber36Block6Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentMap_1_ok :
    tttLargeFiber36Block6Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentMap_2_ok :
    tttLargeFiber36Block6Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentMap_3_ok :
    tttLargeFiber36Block6Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentMap_4_ok :
    tttLargeFiber36Block6Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentMap_5_ok :
    tttLargeFiber36Block6Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentMap_6_ok :
    tttLargeFiber36Block6Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentMap_7_ok :
    tttLargeFiber36Block6Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentMap_8_ok :
    tttLargeFiber36Block6Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentMap_9_ok :
    tttLargeFiber36Block6Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentMap_10_ok :
    tttLargeFiber36Block6Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentMap_11_ok :
    tttLargeFiber36Block6Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentMap_12_ok :
    tttLargeFiber36Block6Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentMap_13_ok :
    tttLargeFiber36Block6Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentMap_14_ok :
    tttLargeFiber36Block6Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentMap_15_ok :
    tttLargeFiber36Block6Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentPath_0_ok :
    tttLargeFiber36Block6Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentPath_1_ok :
    tttLargeFiber36Block6Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentPath_2_ok :
    tttLargeFiber36Block6Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentPath_3_ok :
    tttLargeFiber36Block6Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentPath_4_ok :
    tttLargeFiber36Block6Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentPath_5_ok :
    tttLargeFiber36Block6Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentPath_6_ok :
    tttLargeFiber36Block6Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentPath_7_ok :
    tttLargeFiber36Block6Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentPath_8_ok :
    tttLargeFiber36Block6Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentPath_9_ok :
    tttLargeFiber36Block6Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentPath_10_ok :
    tttLargeFiber36Block6Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentPath_11_ok :
    tttLargeFiber36Block6Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentPath_12_ok :
    tttLargeFiber36Block6Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentPath_13_ok :
    tttLargeFiber36Block6Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentPath_14_ok :
    tttLargeFiber36Block6Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber36Block6Chunk1ParentPath_15_ok :
    tttLargeFiber36Block6Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber36Block6Chunk1RowsAudit : Bool :=
  tttLargeFiber36Block6Chunk1RowCheck 0
    && tttLargeFiber36Block6Chunk1RowCheck 1
    && tttLargeFiber36Block6Chunk1RowCheck 2
    && tttLargeFiber36Block6Chunk1RowCheck 3
    && tttLargeFiber36Block6Chunk1RowCheck 4
    && tttLargeFiber36Block6Chunk1RowCheck 5
    && tttLargeFiber36Block6Chunk1RowCheck 6
    && tttLargeFiber36Block6Chunk1RowCheck 7
    && tttLargeFiber36Block6Chunk1RowCheck 8
    && tttLargeFiber36Block6Chunk1RowCheck 9
    && tttLargeFiber36Block6Chunk1RowCheck 10
    && tttLargeFiber36Block6Chunk1RowCheck 11
    && tttLargeFiber36Block6Chunk1RowCheck 12
    && tttLargeFiber36Block6Chunk1RowCheck 13
    && tttLargeFiber36Block6Chunk1RowCheck 14
    && tttLargeFiber36Block6Chunk1RowCheck 15

theorem tttLargeFiber36Block6Chunk1RowsAudit_ok :
    tttLargeFiber36Block6Chunk1RowsAudit = true := by
  simp [tttLargeFiber36Block6Chunk1RowsAudit,
    tttLargeFiber36Block6Chunk1Row_0_ok,
    tttLargeFiber36Block6Chunk1Row_1_ok,
    tttLargeFiber36Block6Chunk1Row_2_ok,
    tttLargeFiber36Block6Chunk1Row_3_ok,
    tttLargeFiber36Block6Chunk1Row_4_ok,
    tttLargeFiber36Block6Chunk1Row_5_ok,
    tttLargeFiber36Block6Chunk1Row_6_ok,
    tttLargeFiber36Block6Chunk1Row_7_ok,
    tttLargeFiber36Block6Chunk1Row_8_ok,
    tttLargeFiber36Block6Chunk1Row_9_ok,
    tttLargeFiber36Block6Chunk1Row_10_ok,
    tttLargeFiber36Block6Chunk1Row_11_ok,
    tttLargeFiber36Block6Chunk1Row_12_ok,
    tttLargeFiber36Block6Chunk1Row_13_ok,
    tttLargeFiber36Block6Chunk1Row_14_ok,
    tttLargeFiber36Block6Chunk1Row_15_ok]

def tttLargeFiber36Block6Chunk1ParentMapAudit : Bool :=
  tttLargeFiber36Block6Chunk1ParentMapCheck 0
    && tttLargeFiber36Block6Chunk1ParentMapCheck 1
    && tttLargeFiber36Block6Chunk1ParentMapCheck 2
    && tttLargeFiber36Block6Chunk1ParentMapCheck 3
    && tttLargeFiber36Block6Chunk1ParentMapCheck 4
    && tttLargeFiber36Block6Chunk1ParentMapCheck 5
    && tttLargeFiber36Block6Chunk1ParentMapCheck 6
    && tttLargeFiber36Block6Chunk1ParentMapCheck 7
    && tttLargeFiber36Block6Chunk1ParentMapCheck 8
    && tttLargeFiber36Block6Chunk1ParentMapCheck 9
    && tttLargeFiber36Block6Chunk1ParentMapCheck 10
    && tttLargeFiber36Block6Chunk1ParentMapCheck 11
    && tttLargeFiber36Block6Chunk1ParentMapCheck 12
    && tttLargeFiber36Block6Chunk1ParentMapCheck 13
    && tttLargeFiber36Block6Chunk1ParentMapCheck 14
    && tttLargeFiber36Block6Chunk1ParentMapCheck 15

theorem tttLargeFiber36Block6Chunk1ParentMapAudit_ok :
    tttLargeFiber36Block6Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber36Block6Chunk1ParentMapAudit,
    tttLargeFiber36Block6Chunk1ParentMap_0_ok,
    tttLargeFiber36Block6Chunk1ParentMap_1_ok,
    tttLargeFiber36Block6Chunk1ParentMap_2_ok,
    tttLargeFiber36Block6Chunk1ParentMap_3_ok,
    tttLargeFiber36Block6Chunk1ParentMap_4_ok,
    tttLargeFiber36Block6Chunk1ParentMap_5_ok,
    tttLargeFiber36Block6Chunk1ParentMap_6_ok,
    tttLargeFiber36Block6Chunk1ParentMap_7_ok,
    tttLargeFiber36Block6Chunk1ParentMap_8_ok,
    tttLargeFiber36Block6Chunk1ParentMap_9_ok,
    tttLargeFiber36Block6Chunk1ParentMap_10_ok,
    tttLargeFiber36Block6Chunk1ParentMap_11_ok,
    tttLargeFiber36Block6Chunk1ParentMap_12_ok,
    tttLargeFiber36Block6Chunk1ParentMap_13_ok,
    tttLargeFiber36Block6Chunk1ParentMap_14_ok,
    tttLargeFiber36Block6Chunk1ParentMap_15_ok]

def tttLargeFiber36Block6Chunk1ParentsAudit : Bool :=
  tttLargeFiber36Block6Chunk1ParentPathCheck 0
    && tttLargeFiber36Block6Chunk1ParentPathCheck 1
    && tttLargeFiber36Block6Chunk1ParentPathCheck 2
    && tttLargeFiber36Block6Chunk1ParentPathCheck 3
    && tttLargeFiber36Block6Chunk1ParentPathCheck 4
    && tttLargeFiber36Block6Chunk1ParentPathCheck 5
    && tttLargeFiber36Block6Chunk1ParentPathCheck 6
    && tttLargeFiber36Block6Chunk1ParentPathCheck 7
    && tttLargeFiber36Block6Chunk1ParentPathCheck 8
    && tttLargeFiber36Block6Chunk1ParentPathCheck 9
    && tttLargeFiber36Block6Chunk1ParentPathCheck 10
    && tttLargeFiber36Block6Chunk1ParentPathCheck 11
    && tttLargeFiber36Block6Chunk1ParentPathCheck 12
    && tttLargeFiber36Block6Chunk1ParentPathCheck 13
    && tttLargeFiber36Block6Chunk1ParentPathCheck 14
    && tttLargeFiber36Block6Chunk1ParentPathCheck 15

theorem tttLargeFiber36Block6Chunk1ParentsAudit_ok :
    tttLargeFiber36Block6Chunk1ParentsAudit = true := by
  simp [tttLargeFiber36Block6Chunk1ParentsAudit,
    tttLargeFiber36Block6Chunk1ParentPath_0_ok,
    tttLargeFiber36Block6Chunk1ParentPath_1_ok,
    tttLargeFiber36Block6Chunk1ParentPath_2_ok,
    tttLargeFiber36Block6Chunk1ParentPath_3_ok,
    tttLargeFiber36Block6Chunk1ParentPath_4_ok,
    tttLargeFiber36Block6Chunk1ParentPath_5_ok,
    tttLargeFiber36Block6Chunk1ParentPath_6_ok,
    tttLargeFiber36Block6Chunk1ParentPath_7_ok,
    tttLargeFiber36Block6Chunk1ParentPath_8_ok,
    tttLargeFiber36Block6Chunk1ParentPath_9_ok,
    tttLargeFiber36Block6Chunk1ParentPath_10_ok,
    tttLargeFiber36Block6Chunk1ParentPath_11_ok,
    tttLargeFiber36Block6Chunk1ParentPath_12_ok,
    tttLargeFiber36Block6Chunk1ParentPath_13_ok,
    tttLargeFiber36Block6Chunk1ParentPath_14_ok,
    tttLargeFiber36Block6Chunk1ParentPath_15_ok]

def tttLargeFiber36Block6Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber36CountsAudit &&
    tttLargeFiber36Block6Chunk1SourcesCheck &&
    tttLargeFiber36Block6Chunk1RowsAudit &&
    tttLargeFiber36Block6Chunk1ParentMapAudit &&
    tttLargeFiber36Block6Chunk1ParentsAudit

theorem tttLargeFiber36Block6Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber36Block6Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber36Block6Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber36CountsAudit_ok,
    tttLargeFiber36Block6Chunk1SourcesCheck_ok,
    tttLargeFiber36Block6Chunk1RowsAudit_ok,
    tttLargeFiber36Block6Chunk1ParentMapAudit_ok,
    tttLargeFiber36Block6Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber36Block6Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
