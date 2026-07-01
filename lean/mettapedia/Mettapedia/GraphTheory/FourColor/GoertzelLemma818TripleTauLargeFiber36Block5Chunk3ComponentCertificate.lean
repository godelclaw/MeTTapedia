import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 36, block 5 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber36Block5Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber36Data

def tttLargeFiber36Block5Chunk3Sources : List Nat :=
  [   2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023,
   2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031]

def tttLargeFiber36Row368 : TripleComponentParentRow :=
  tripleRow 2016 384 57 174 64 9 110 64
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row369 : TripleComponentParentRow :=
  tripleRow 2017 385 57 174 65 9 110 65
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row370 : TripleComponentParentRow :=
  tripleRow 2018 386 57 174 66 9 110 66
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row371 : TripleComponentParentRow :=
  tripleRow 2019 2003 57 174 67 57 172 135
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber36Row372 : TripleComponentParentRow :=
  tripleRow 2020 1988 57 174 116 57 158 48
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber36Row373 : TripleComponentParentRow :=
  tripleRow 2021 1989 57 174 117 57 158 49
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
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

def tttLargeFiber36Row374 : TripleComponentParentRow :=
  tripleRow 2022 390 57 174 118 9 110 118
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row375 : TripleComponentParentRow :=
  tripleRow 2023 391 57 174 119 9 110 119
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row376 : TripleComponentParentRow :=
  tripleRow 2024 392 57 175 72 9 111 72
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row377 : TripleComponentParentRow :=
  tripleRow 2025 393 57 175 73 9 111 73
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row378 : TripleComponentParentRow :=
  tripleRow 2026 394 57 175 74 9 111 74
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row379 : TripleComponentParentRow :=
  tripleRow 2027 395 57 175 75 9 111 75
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row380 : TripleComponentParentRow :=
  tripleRow 2028 1996 57 175 124 57 159 56
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber36Row381 : TripleComponentParentRow :=
  tripleRow 2029 1997 57 175 125 57 159 57
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
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

def tttLargeFiber36Row382 : TripleComponentParentRow :=
  tripleRow 2030 398 57 175 126 9 111 126
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Row383 : TripleComponentParentRow :=
  tripleRow 2031 399 57 175 127 9 111 127
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber36Block5Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber36Row368
  , tttLargeFiber36Row369
  , tttLargeFiber36Row370
  , tttLargeFiber36Row371
  , tttLargeFiber36Row372
  , tttLargeFiber36Row373
  , tttLargeFiber36Row374
  , tttLargeFiber36Row375
  , tttLargeFiber36Row376
  , tttLargeFiber36Row377
  , tttLargeFiber36Row378
  , tttLargeFiber36Row379
  , tttLargeFiber36Row380
  , tttLargeFiber36Row381
  , tttLargeFiber36Row382
  , tttLargeFiber36Row383
  ]

def tttLargeFiber36Block5Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (272 <= i) && decide (i < 528)) ||
    (decide (1904 <= i) && decide (i < 2160))

def tttLargeFiber36Block5Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber36Block5Chunk3ExpectedContains row.source &&
    tttLargeFiber36Block5Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber36Key &&
          chainInputKey tttWord t == tttLargeFiber36Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber36Block5Chunk3SourcesCheck : Bool :=
  (tttLargeFiber36Block5Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber36Block5Chunk3Sources

theorem tttLargeFiber36Block5Chunk3SourcesCheck_ok :
    tttLargeFiber36Block5Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber36Block5Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber36Block5Chunk3RowValid
    (listGetD tttLargeFiber36Block5Chunk3Rows i default)

def tttLargeFiber36Block5Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber36Block5Chunk3Rows i default
  row.parent == tttLargeFiber36ParentOf row.source

def tttLargeFiber36Block5Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber36Block5Chunk3Sources 0 0 == 2016
      && tttLargeFiber36ParentOf 2016 == 384
      && tttLargeFiber36ParentOf 384 == 320
      && tttLargeFiber36ParentOf 320 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 1 => listGetD tttLargeFiber36Block5Chunk3Sources 1 0 == 2017
      && tttLargeFiber36ParentOf 2017 == 385
      && tttLargeFiber36ParentOf 385 == 321
      && tttLargeFiber36ParentOf 321 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 2 => listGetD tttLargeFiber36Block5Chunk3Sources 2 0 == 2018
      && tttLargeFiber36ParentOf 2018 == 386
      && tttLargeFiber36ParentOf 386 == 322
      && tttLargeFiber36ParentOf 322 == 282
      && tttLargeFiber36ParentOf 282 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 3 => listGetD tttLargeFiber36Block5Chunk3Sources 3 0 == 2019
      && tttLargeFiber36ParentOf 2019 == 2003
      && tttLargeFiber36ParentOf 2003 == 1971
      && tttLargeFiber36ParentOf 1971 == 1968
      && tttLargeFiber36ParentOf 1968 == 336
      && tttLargeFiber36ParentOf 336 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 4 => listGetD tttLargeFiber36Block5Chunk3Sources 4 0 == 2020
      && tttLargeFiber36ParentOf 2020 == 1988
      && tttLargeFiber36ParentOf 1988 == 1976
      && tttLargeFiber36ParentOf 1976 == 344
      && tttLargeFiber36ParentOf 344 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 5 => listGetD tttLargeFiber36Block5Chunk3Sources 5 0 == 2021
      && tttLargeFiber36ParentOf 2021 == 1989
      && tttLargeFiber36ParentOf 1989 == 1977
      && tttLargeFiber36ParentOf 1977 == 345
      && tttLargeFiber36ParentOf 345 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (6 <= tttLargeFiber36MaxParentDepth)
  | 6 => listGetD tttLargeFiber36Block5Chunk3Sources 6 0 == 2022
      && tttLargeFiber36ParentOf 2022 == 390
      && tttLargeFiber36ParentOf 390 == 326
      && tttLargeFiber36ParentOf 326 == 286
      && tttLargeFiber36ParentOf 286 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (6 <= tttLargeFiber36MaxParentDepth)
  | 7 => listGetD tttLargeFiber36Block5Chunk3Sources 7 0 == 2023
      && tttLargeFiber36ParentOf 2023 == 391
      && tttLargeFiber36ParentOf 391 == 327
      && tttLargeFiber36ParentOf 327 == 287
      && tttLargeFiber36ParentOf 287 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 8 => listGetD tttLargeFiber36Block5Chunk3Sources 8 0 == 2024
      && tttLargeFiber36ParentOf 2024 == 392
      && tttLargeFiber36ParentOf 392 == 328
      && tttLargeFiber36ParentOf 328 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 9 => listGetD tttLargeFiber36Block5Chunk3Sources 9 0 == 2025
      && tttLargeFiber36ParentOf 2025 == 393
      && tttLargeFiber36ParentOf 393 == 329
      && tttLargeFiber36ParentOf 329 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 10 => listGetD tttLargeFiber36Block5Chunk3Sources 10 0 == 2026
      && tttLargeFiber36ParentOf 2026 == 394
      && tttLargeFiber36ParentOf 394 == 330
      && tttLargeFiber36ParentOf 330 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 11 => listGetD tttLargeFiber36Block5Chunk3Sources 11 0 == 2027
      && tttLargeFiber36ParentOf 2027 == 395
      && tttLargeFiber36ParentOf 395 == 331
      && tttLargeFiber36ParentOf 331 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 12 => listGetD tttLargeFiber36Block5Chunk3Sources 12 0 == 2028
      && tttLargeFiber36ParentOf 2028 == 1996
      && tttLargeFiber36ParentOf 1996 == 1968
      && tttLargeFiber36ParentOf 1968 == 336
      && tttLargeFiber36ParentOf 336 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 13 => listGetD tttLargeFiber36Block5Chunk3Sources 13 0 == 2029
      && tttLargeFiber36ParentOf 2029 == 1997
      && tttLargeFiber36ParentOf 1997 == 1969
      && tttLargeFiber36ParentOf 1969 == 337
      && tttLargeFiber36ParentOf 337 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 14 => listGetD tttLargeFiber36Block5Chunk3Sources 14 0 == 2030
      && tttLargeFiber36ParentOf 2030 == 398
      && tttLargeFiber36ParentOf 398 == 334
      && tttLargeFiber36ParentOf 334 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 15 => listGetD tttLargeFiber36Block5Chunk3Sources 15 0 == 2031
      && tttLargeFiber36ParentOf 2031 == 399
      && tttLargeFiber36ParentOf 399 == 335
      && tttLargeFiber36ParentOf 335 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | _ => false

theorem tttLargeFiber36Block5Chunk3Row_0_ok :
    tttLargeFiber36Block5Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3Row_1_ok :
    tttLargeFiber36Block5Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3Row_2_ok :
    tttLargeFiber36Block5Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3Row_3_ok :
    tttLargeFiber36Block5Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3Row_4_ok :
    tttLargeFiber36Block5Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3Row_5_ok :
    tttLargeFiber36Block5Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3Row_6_ok :
    tttLargeFiber36Block5Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3Row_7_ok :
    tttLargeFiber36Block5Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3Row_8_ok :
    tttLargeFiber36Block5Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3Row_9_ok :
    tttLargeFiber36Block5Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3Row_10_ok :
    tttLargeFiber36Block5Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3Row_11_ok :
    tttLargeFiber36Block5Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3Row_12_ok :
    tttLargeFiber36Block5Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3Row_13_ok :
    tttLargeFiber36Block5Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3Row_14_ok :
    tttLargeFiber36Block5Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3Row_15_ok :
    tttLargeFiber36Block5Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentMap_0_ok :
    tttLargeFiber36Block5Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentMap_1_ok :
    tttLargeFiber36Block5Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentMap_2_ok :
    tttLargeFiber36Block5Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentMap_3_ok :
    tttLargeFiber36Block5Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentMap_4_ok :
    tttLargeFiber36Block5Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentMap_5_ok :
    tttLargeFiber36Block5Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentMap_6_ok :
    tttLargeFiber36Block5Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentMap_7_ok :
    tttLargeFiber36Block5Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentMap_8_ok :
    tttLargeFiber36Block5Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentMap_9_ok :
    tttLargeFiber36Block5Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentMap_10_ok :
    tttLargeFiber36Block5Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentMap_11_ok :
    tttLargeFiber36Block5Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentMap_12_ok :
    tttLargeFiber36Block5Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentMap_13_ok :
    tttLargeFiber36Block5Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentMap_14_ok :
    tttLargeFiber36Block5Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentMap_15_ok :
    tttLargeFiber36Block5Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentPath_0_ok :
    tttLargeFiber36Block5Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentPath_1_ok :
    tttLargeFiber36Block5Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentPath_2_ok :
    tttLargeFiber36Block5Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentPath_3_ok :
    tttLargeFiber36Block5Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentPath_4_ok :
    tttLargeFiber36Block5Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentPath_5_ok :
    tttLargeFiber36Block5Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentPath_6_ok :
    tttLargeFiber36Block5Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentPath_7_ok :
    tttLargeFiber36Block5Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentPath_8_ok :
    tttLargeFiber36Block5Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentPath_9_ok :
    tttLargeFiber36Block5Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentPath_10_ok :
    tttLargeFiber36Block5Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentPath_11_ok :
    tttLargeFiber36Block5Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentPath_12_ok :
    tttLargeFiber36Block5Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentPath_13_ok :
    tttLargeFiber36Block5Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentPath_14_ok :
    tttLargeFiber36Block5Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber36Block5Chunk3ParentPath_15_ok :
    tttLargeFiber36Block5Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber36Block5Chunk3RowsAudit : Bool :=
  tttLargeFiber36Block5Chunk3RowCheck 0
    && tttLargeFiber36Block5Chunk3RowCheck 1
    && tttLargeFiber36Block5Chunk3RowCheck 2
    && tttLargeFiber36Block5Chunk3RowCheck 3
    && tttLargeFiber36Block5Chunk3RowCheck 4
    && tttLargeFiber36Block5Chunk3RowCheck 5
    && tttLargeFiber36Block5Chunk3RowCheck 6
    && tttLargeFiber36Block5Chunk3RowCheck 7
    && tttLargeFiber36Block5Chunk3RowCheck 8
    && tttLargeFiber36Block5Chunk3RowCheck 9
    && tttLargeFiber36Block5Chunk3RowCheck 10
    && tttLargeFiber36Block5Chunk3RowCheck 11
    && tttLargeFiber36Block5Chunk3RowCheck 12
    && tttLargeFiber36Block5Chunk3RowCheck 13
    && tttLargeFiber36Block5Chunk3RowCheck 14
    && tttLargeFiber36Block5Chunk3RowCheck 15

theorem tttLargeFiber36Block5Chunk3RowsAudit_ok :
    tttLargeFiber36Block5Chunk3RowsAudit = true := by
  simp [tttLargeFiber36Block5Chunk3RowsAudit,
    tttLargeFiber36Block5Chunk3Row_0_ok,
    tttLargeFiber36Block5Chunk3Row_1_ok,
    tttLargeFiber36Block5Chunk3Row_2_ok,
    tttLargeFiber36Block5Chunk3Row_3_ok,
    tttLargeFiber36Block5Chunk3Row_4_ok,
    tttLargeFiber36Block5Chunk3Row_5_ok,
    tttLargeFiber36Block5Chunk3Row_6_ok,
    tttLargeFiber36Block5Chunk3Row_7_ok,
    tttLargeFiber36Block5Chunk3Row_8_ok,
    tttLargeFiber36Block5Chunk3Row_9_ok,
    tttLargeFiber36Block5Chunk3Row_10_ok,
    tttLargeFiber36Block5Chunk3Row_11_ok,
    tttLargeFiber36Block5Chunk3Row_12_ok,
    tttLargeFiber36Block5Chunk3Row_13_ok,
    tttLargeFiber36Block5Chunk3Row_14_ok,
    tttLargeFiber36Block5Chunk3Row_15_ok]

def tttLargeFiber36Block5Chunk3ParentMapAudit : Bool :=
  tttLargeFiber36Block5Chunk3ParentMapCheck 0
    && tttLargeFiber36Block5Chunk3ParentMapCheck 1
    && tttLargeFiber36Block5Chunk3ParentMapCheck 2
    && tttLargeFiber36Block5Chunk3ParentMapCheck 3
    && tttLargeFiber36Block5Chunk3ParentMapCheck 4
    && tttLargeFiber36Block5Chunk3ParentMapCheck 5
    && tttLargeFiber36Block5Chunk3ParentMapCheck 6
    && tttLargeFiber36Block5Chunk3ParentMapCheck 7
    && tttLargeFiber36Block5Chunk3ParentMapCheck 8
    && tttLargeFiber36Block5Chunk3ParentMapCheck 9
    && tttLargeFiber36Block5Chunk3ParentMapCheck 10
    && tttLargeFiber36Block5Chunk3ParentMapCheck 11
    && tttLargeFiber36Block5Chunk3ParentMapCheck 12
    && tttLargeFiber36Block5Chunk3ParentMapCheck 13
    && tttLargeFiber36Block5Chunk3ParentMapCheck 14
    && tttLargeFiber36Block5Chunk3ParentMapCheck 15

theorem tttLargeFiber36Block5Chunk3ParentMapAudit_ok :
    tttLargeFiber36Block5Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber36Block5Chunk3ParentMapAudit,
    tttLargeFiber36Block5Chunk3ParentMap_0_ok,
    tttLargeFiber36Block5Chunk3ParentMap_1_ok,
    tttLargeFiber36Block5Chunk3ParentMap_2_ok,
    tttLargeFiber36Block5Chunk3ParentMap_3_ok,
    tttLargeFiber36Block5Chunk3ParentMap_4_ok,
    tttLargeFiber36Block5Chunk3ParentMap_5_ok,
    tttLargeFiber36Block5Chunk3ParentMap_6_ok,
    tttLargeFiber36Block5Chunk3ParentMap_7_ok,
    tttLargeFiber36Block5Chunk3ParentMap_8_ok,
    tttLargeFiber36Block5Chunk3ParentMap_9_ok,
    tttLargeFiber36Block5Chunk3ParentMap_10_ok,
    tttLargeFiber36Block5Chunk3ParentMap_11_ok,
    tttLargeFiber36Block5Chunk3ParentMap_12_ok,
    tttLargeFiber36Block5Chunk3ParentMap_13_ok,
    tttLargeFiber36Block5Chunk3ParentMap_14_ok,
    tttLargeFiber36Block5Chunk3ParentMap_15_ok]

def tttLargeFiber36Block5Chunk3ParentsAudit : Bool :=
  tttLargeFiber36Block5Chunk3ParentPathCheck 0
    && tttLargeFiber36Block5Chunk3ParentPathCheck 1
    && tttLargeFiber36Block5Chunk3ParentPathCheck 2
    && tttLargeFiber36Block5Chunk3ParentPathCheck 3
    && tttLargeFiber36Block5Chunk3ParentPathCheck 4
    && tttLargeFiber36Block5Chunk3ParentPathCheck 5
    && tttLargeFiber36Block5Chunk3ParentPathCheck 6
    && tttLargeFiber36Block5Chunk3ParentPathCheck 7
    && tttLargeFiber36Block5Chunk3ParentPathCheck 8
    && tttLargeFiber36Block5Chunk3ParentPathCheck 9
    && tttLargeFiber36Block5Chunk3ParentPathCheck 10
    && tttLargeFiber36Block5Chunk3ParentPathCheck 11
    && tttLargeFiber36Block5Chunk3ParentPathCheck 12
    && tttLargeFiber36Block5Chunk3ParentPathCheck 13
    && tttLargeFiber36Block5Chunk3ParentPathCheck 14
    && tttLargeFiber36Block5Chunk3ParentPathCheck 15

theorem tttLargeFiber36Block5Chunk3ParentsAudit_ok :
    tttLargeFiber36Block5Chunk3ParentsAudit = true := by
  simp [tttLargeFiber36Block5Chunk3ParentsAudit,
    tttLargeFiber36Block5Chunk3ParentPath_0_ok,
    tttLargeFiber36Block5Chunk3ParentPath_1_ok,
    tttLargeFiber36Block5Chunk3ParentPath_2_ok,
    tttLargeFiber36Block5Chunk3ParentPath_3_ok,
    tttLargeFiber36Block5Chunk3ParentPath_4_ok,
    tttLargeFiber36Block5Chunk3ParentPath_5_ok,
    tttLargeFiber36Block5Chunk3ParentPath_6_ok,
    tttLargeFiber36Block5Chunk3ParentPath_7_ok,
    tttLargeFiber36Block5Chunk3ParentPath_8_ok,
    tttLargeFiber36Block5Chunk3ParentPath_9_ok,
    tttLargeFiber36Block5Chunk3ParentPath_10_ok,
    tttLargeFiber36Block5Chunk3ParentPath_11_ok,
    tttLargeFiber36Block5Chunk3ParentPath_12_ok,
    tttLargeFiber36Block5Chunk3ParentPath_13_ok,
    tttLargeFiber36Block5Chunk3ParentPath_14_ok,
    tttLargeFiber36Block5Chunk3ParentPath_15_ok]

def tttLargeFiber36Block5Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber36CountsAudit &&
    tttLargeFiber36Block5Chunk3SourcesCheck &&
    tttLargeFiber36Block5Chunk3RowsAudit &&
    tttLargeFiber36Block5Chunk3ParentMapAudit &&
    tttLargeFiber36Block5Chunk3ParentsAudit

theorem tttLargeFiber36Block5Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber36Block5Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber36Block5Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber36CountsAudit_ok,
    tttLargeFiber36Block5Chunk3SourcesCheck_ok,
    tttLargeFiber36Block5Chunk3RowsAudit_ok,
    tttLargeFiber36Block5Chunk3ParentMapAudit_ok,
    tttLargeFiber36Block5Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber36Block5Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
