import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 36, block 2 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber36Block2Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber36Data

def tttLargeFiber36Block2Chunk3Sources : List Nat :=
  [   448, 449, 450, 451, 452, 453, 454, 455,
   456, 457, 458, 459, 460, 461, 462, 463]

def tttLargeFiber36Row176 : TripleComponentParentRow :=
  tripleRow 448 320 10 34 0 8 102 64
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber36Row177 : TripleComponentParentRow :=
  tripleRow 449 321 10 34 1 8 102 65
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber36Row178 : TripleComponentParentRow :=
  tripleRow 450 322 10 34 2 8 102 66
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber36Row179 : TripleComponentParentRow :=
  tripleRow 451 323 10 34 3 8 102 67
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber36Row180 : TripleComponentParentRow :=
  tripleRow 452 448 10 34 48 10 34 0
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row181 : TripleComponentParentRow :=
  tripleRow 453 449 10 34 49 10 34 1
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row182 : TripleComponentParentRow :=
  tripleRow 454 326 10 34 50 8 102 118
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber36Row183 : TripleComponentParentRow :=
  tripleRow 455 327 10 34 51 8 102 119
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber36Row184 : TripleComponentParentRow :=
  tripleRow 456 328 10 35 8 8 103 72
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber36Row185 : TripleComponentParentRow :=
  tripleRow 457 329 10 35 9 8 103 73
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber36Row186 : TripleComponentParentRow :=
  tripleRow 458 330 10 35 10 8 103 74
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber36Row187 : TripleComponentParentRow :=
  tripleRow 459 331 10 35 11 8 103 75
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber36Row188 : TripleComponentParentRow :=
  tripleRow 460 456 10 35 56 10 35 8
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row189 : TripleComponentParentRow :=
  tripleRow 461 457 10 35 57 10 35 9
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber36Row190 : TripleComponentParentRow :=
  tripleRow 462 334 10 35 58 8 103 126
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber36Row191 : TripleComponentParentRow :=
  tripleRow 463 335 10 35 59 8 103 127
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber36Block2Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber36Row176
  , tttLargeFiber36Row177
  , tttLargeFiber36Row178
  , tttLargeFiber36Row179
  , tttLargeFiber36Row180
  , tttLargeFiber36Row181
  , tttLargeFiber36Row182
  , tttLargeFiber36Row183
  , tttLargeFiber36Row184
  , tttLargeFiber36Row185
  , tttLargeFiber36Row186
  , tttLargeFiber36Row187
  , tttLargeFiber36Row188
  , tttLargeFiber36Row189
  , tttLargeFiber36Row190
  , tttLargeFiber36Row191
  ]

def tttLargeFiber36Block2Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (272 <= i) && decide (i < 528)) ||
    (decide (1904 <= i) && decide (i < 2160))

def tttLargeFiber36Block2Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber36Block2Chunk3ExpectedContains row.source &&
    tttLargeFiber36Block2Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber36Key &&
          chainInputKey tttWord t == tttLargeFiber36Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber36Block2Chunk3SourcesCheck : Bool :=
  (tttLargeFiber36Block2Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber36Block2Chunk3Sources

theorem tttLargeFiber36Block2Chunk3SourcesCheck_ok :
    tttLargeFiber36Block2Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber36Block2Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber36Block2Chunk3RowValid
    (listGetD tttLargeFiber36Block2Chunk3Rows i default)

def tttLargeFiber36Block2Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber36Block2Chunk3Rows i default
  row.parent == tttLargeFiber36ParentOf row.source

def tttLargeFiber36Block2Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber36Block2Chunk3Sources 0 0 == 448
      && tttLargeFiber36ParentOf 448 == 320
      && tttLargeFiber36ParentOf 320 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 1 => listGetD tttLargeFiber36Block2Chunk3Sources 1 0 == 449
      && tttLargeFiber36ParentOf 449 == 321
      && tttLargeFiber36ParentOf 321 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 2 => listGetD tttLargeFiber36Block2Chunk3Sources 2 0 == 450
      && tttLargeFiber36ParentOf 450 == 322
      && tttLargeFiber36ParentOf 322 == 282
      && tttLargeFiber36ParentOf 282 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 3 => listGetD tttLargeFiber36Block2Chunk3Sources 3 0 == 451
      && tttLargeFiber36ParentOf 451 == 323
      && tttLargeFiber36ParentOf 323 == 283
      && tttLargeFiber36ParentOf 283 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 4 => listGetD tttLargeFiber36Block2Chunk3Sources 4 0 == 452
      && tttLargeFiber36ParentOf 452 == 448
      && tttLargeFiber36ParentOf 448 == 320
      && tttLargeFiber36ParentOf 320 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 5 => listGetD tttLargeFiber36Block2Chunk3Sources 5 0 == 453
      && tttLargeFiber36ParentOf 453 == 449
      && tttLargeFiber36ParentOf 449 == 321
      && tttLargeFiber36ParentOf 321 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 6 => listGetD tttLargeFiber36Block2Chunk3Sources 6 0 == 454
      && tttLargeFiber36ParentOf 454 == 326
      && tttLargeFiber36ParentOf 326 == 286
      && tttLargeFiber36ParentOf 286 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 7 => listGetD tttLargeFiber36Block2Chunk3Sources 7 0 == 455
      && tttLargeFiber36ParentOf 455 == 327
      && tttLargeFiber36ParentOf 327 == 287
      && tttLargeFiber36ParentOf 287 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 8 => listGetD tttLargeFiber36Block2Chunk3Sources 8 0 == 456
      && tttLargeFiber36ParentOf 456 == 328
      && tttLargeFiber36ParentOf 328 == 272
      && 272 == tttLargeFiber36Root
      && decide (2 <= tttLargeFiber36MaxParentDepth)
  | 9 => listGetD tttLargeFiber36Block2Chunk3Sources 9 0 == 457
      && tttLargeFiber36ParentOf 457 == 329
      && tttLargeFiber36ParentOf 329 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 10 => listGetD tttLargeFiber36Block2Chunk3Sources 10 0 == 458
      && tttLargeFiber36ParentOf 458 == 330
      && tttLargeFiber36ParentOf 330 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 11 => listGetD tttLargeFiber36Block2Chunk3Sources 11 0 == 459
      && tttLargeFiber36ParentOf 459 == 331
      && tttLargeFiber36ParentOf 331 == 275
      && tttLargeFiber36ParentOf 275 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 12 => listGetD tttLargeFiber36Block2Chunk3Sources 12 0 == 460
      && tttLargeFiber36ParentOf 460 == 456
      && tttLargeFiber36ParentOf 456 == 328
      && tttLargeFiber36ParentOf 328 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 13 => listGetD tttLargeFiber36Block2Chunk3Sources 13 0 == 461
      && tttLargeFiber36ParentOf 461 == 457
      && tttLargeFiber36ParentOf 457 == 329
      && tttLargeFiber36ParentOf 329 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 14 => listGetD tttLargeFiber36Block2Chunk3Sources 14 0 == 462
      && tttLargeFiber36ParentOf 462 == 334
      && tttLargeFiber36ParentOf 334 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 15 => listGetD tttLargeFiber36Block2Chunk3Sources 15 0 == 463
      && tttLargeFiber36ParentOf 463 == 335
      && tttLargeFiber36ParentOf 335 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | _ => false

theorem tttLargeFiber36Block2Chunk3Row_0_ok :
    tttLargeFiber36Block2Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3Row_1_ok :
    tttLargeFiber36Block2Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3Row_2_ok :
    tttLargeFiber36Block2Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3Row_3_ok :
    tttLargeFiber36Block2Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3Row_4_ok :
    tttLargeFiber36Block2Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3Row_5_ok :
    tttLargeFiber36Block2Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3Row_6_ok :
    tttLargeFiber36Block2Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3Row_7_ok :
    tttLargeFiber36Block2Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3Row_8_ok :
    tttLargeFiber36Block2Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3Row_9_ok :
    tttLargeFiber36Block2Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3Row_10_ok :
    tttLargeFiber36Block2Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3Row_11_ok :
    tttLargeFiber36Block2Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3Row_12_ok :
    tttLargeFiber36Block2Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3Row_13_ok :
    tttLargeFiber36Block2Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3Row_14_ok :
    tttLargeFiber36Block2Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3Row_15_ok :
    tttLargeFiber36Block2Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentMap_0_ok :
    tttLargeFiber36Block2Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentMap_1_ok :
    tttLargeFiber36Block2Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentMap_2_ok :
    tttLargeFiber36Block2Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentMap_3_ok :
    tttLargeFiber36Block2Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentMap_4_ok :
    tttLargeFiber36Block2Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentMap_5_ok :
    tttLargeFiber36Block2Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentMap_6_ok :
    tttLargeFiber36Block2Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentMap_7_ok :
    tttLargeFiber36Block2Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentMap_8_ok :
    tttLargeFiber36Block2Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentMap_9_ok :
    tttLargeFiber36Block2Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentMap_10_ok :
    tttLargeFiber36Block2Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentMap_11_ok :
    tttLargeFiber36Block2Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentMap_12_ok :
    tttLargeFiber36Block2Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentMap_13_ok :
    tttLargeFiber36Block2Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentMap_14_ok :
    tttLargeFiber36Block2Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentMap_15_ok :
    tttLargeFiber36Block2Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentPath_0_ok :
    tttLargeFiber36Block2Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentPath_1_ok :
    tttLargeFiber36Block2Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentPath_2_ok :
    tttLargeFiber36Block2Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentPath_3_ok :
    tttLargeFiber36Block2Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentPath_4_ok :
    tttLargeFiber36Block2Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentPath_5_ok :
    tttLargeFiber36Block2Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentPath_6_ok :
    tttLargeFiber36Block2Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentPath_7_ok :
    tttLargeFiber36Block2Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentPath_8_ok :
    tttLargeFiber36Block2Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentPath_9_ok :
    tttLargeFiber36Block2Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentPath_10_ok :
    tttLargeFiber36Block2Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentPath_11_ok :
    tttLargeFiber36Block2Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentPath_12_ok :
    tttLargeFiber36Block2Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentPath_13_ok :
    tttLargeFiber36Block2Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentPath_14_ok :
    tttLargeFiber36Block2Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber36Block2Chunk3ParentPath_15_ok :
    tttLargeFiber36Block2Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber36Block2Chunk3RowsAudit : Bool :=
  tttLargeFiber36Block2Chunk3RowCheck 0
    && tttLargeFiber36Block2Chunk3RowCheck 1
    && tttLargeFiber36Block2Chunk3RowCheck 2
    && tttLargeFiber36Block2Chunk3RowCheck 3
    && tttLargeFiber36Block2Chunk3RowCheck 4
    && tttLargeFiber36Block2Chunk3RowCheck 5
    && tttLargeFiber36Block2Chunk3RowCheck 6
    && tttLargeFiber36Block2Chunk3RowCheck 7
    && tttLargeFiber36Block2Chunk3RowCheck 8
    && tttLargeFiber36Block2Chunk3RowCheck 9
    && tttLargeFiber36Block2Chunk3RowCheck 10
    && tttLargeFiber36Block2Chunk3RowCheck 11
    && tttLargeFiber36Block2Chunk3RowCheck 12
    && tttLargeFiber36Block2Chunk3RowCheck 13
    && tttLargeFiber36Block2Chunk3RowCheck 14
    && tttLargeFiber36Block2Chunk3RowCheck 15

theorem tttLargeFiber36Block2Chunk3RowsAudit_ok :
    tttLargeFiber36Block2Chunk3RowsAudit = true := by
  simp [tttLargeFiber36Block2Chunk3RowsAudit,
    tttLargeFiber36Block2Chunk3Row_0_ok,
    tttLargeFiber36Block2Chunk3Row_1_ok,
    tttLargeFiber36Block2Chunk3Row_2_ok,
    tttLargeFiber36Block2Chunk3Row_3_ok,
    tttLargeFiber36Block2Chunk3Row_4_ok,
    tttLargeFiber36Block2Chunk3Row_5_ok,
    tttLargeFiber36Block2Chunk3Row_6_ok,
    tttLargeFiber36Block2Chunk3Row_7_ok,
    tttLargeFiber36Block2Chunk3Row_8_ok,
    tttLargeFiber36Block2Chunk3Row_9_ok,
    tttLargeFiber36Block2Chunk3Row_10_ok,
    tttLargeFiber36Block2Chunk3Row_11_ok,
    tttLargeFiber36Block2Chunk3Row_12_ok,
    tttLargeFiber36Block2Chunk3Row_13_ok,
    tttLargeFiber36Block2Chunk3Row_14_ok,
    tttLargeFiber36Block2Chunk3Row_15_ok]

def tttLargeFiber36Block2Chunk3ParentMapAudit : Bool :=
  tttLargeFiber36Block2Chunk3ParentMapCheck 0
    && tttLargeFiber36Block2Chunk3ParentMapCheck 1
    && tttLargeFiber36Block2Chunk3ParentMapCheck 2
    && tttLargeFiber36Block2Chunk3ParentMapCheck 3
    && tttLargeFiber36Block2Chunk3ParentMapCheck 4
    && tttLargeFiber36Block2Chunk3ParentMapCheck 5
    && tttLargeFiber36Block2Chunk3ParentMapCheck 6
    && tttLargeFiber36Block2Chunk3ParentMapCheck 7
    && tttLargeFiber36Block2Chunk3ParentMapCheck 8
    && tttLargeFiber36Block2Chunk3ParentMapCheck 9
    && tttLargeFiber36Block2Chunk3ParentMapCheck 10
    && tttLargeFiber36Block2Chunk3ParentMapCheck 11
    && tttLargeFiber36Block2Chunk3ParentMapCheck 12
    && tttLargeFiber36Block2Chunk3ParentMapCheck 13
    && tttLargeFiber36Block2Chunk3ParentMapCheck 14
    && tttLargeFiber36Block2Chunk3ParentMapCheck 15

theorem tttLargeFiber36Block2Chunk3ParentMapAudit_ok :
    tttLargeFiber36Block2Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber36Block2Chunk3ParentMapAudit,
    tttLargeFiber36Block2Chunk3ParentMap_0_ok,
    tttLargeFiber36Block2Chunk3ParentMap_1_ok,
    tttLargeFiber36Block2Chunk3ParentMap_2_ok,
    tttLargeFiber36Block2Chunk3ParentMap_3_ok,
    tttLargeFiber36Block2Chunk3ParentMap_4_ok,
    tttLargeFiber36Block2Chunk3ParentMap_5_ok,
    tttLargeFiber36Block2Chunk3ParentMap_6_ok,
    tttLargeFiber36Block2Chunk3ParentMap_7_ok,
    tttLargeFiber36Block2Chunk3ParentMap_8_ok,
    tttLargeFiber36Block2Chunk3ParentMap_9_ok,
    tttLargeFiber36Block2Chunk3ParentMap_10_ok,
    tttLargeFiber36Block2Chunk3ParentMap_11_ok,
    tttLargeFiber36Block2Chunk3ParentMap_12_ok,
    tttLargeFiber36Block2Chunk3ParentMap_13_ok,
    tttLargeFiber36Block2Chunk3ParentMap_14_ok,
    tttLargeFiber36Block2Chunk3ParentMap_15_ok]

def tttLargeFiber36Block2Chunk3ParentsAudit : Bool :=
  tttLargeFiber36Block2Chunk3ParentPathCheck 0
    && tttLargeFiber36Block2Chunk3ParentPathCheck 1
    && tttLargeFiber36Block2Chunk3ParentPathCheck 2
    && tttLargeFiber36Block2Chunk3ParentPathCheck 3
    && tttLargeFiber36Block2Chunk3ParentPathCheck 4
    && tttLargeFiber36Block2Chunk3ParentPathCheck 5
    && tttLargeFiber36Block2Chunk3ParentPathCheck 6
    && tttLargeFiber36Block2Chunk3ParentPathCheck 7
    && tttLargeFiber36Block2Chunk3ParentPathCheck 8
    && tttLargeFiber36Block2Chunk3ParentPathCheck 9
    && tttLargeFiber36Block2Chunk3ParentPathCheck 10
    && tttLargeFiber36Block2Chunk3ParentPathCheck 11
    && tttLargeFiber36Block2Chunk3ParentPathCheck 12
    && tttLargeFiber36Block2Chunk3ParentPathCheck 13
    && tttLargeFiber36Block2Chunk3ParentPathCheck 14
    && tttLargeFiber36Block2Chunk3ParentPathCheck 15

theorem tttLargeFiber36Block2Chunk3ParentsAudit_ok :
    tttLargeFiber36Block2Chunk3ParentsAudit = true := by
  simp [tttLargeFiber36Block2Chunk3ParentsAudit,
    tttLargeFiber36Block2Chunk3ParentPath_0_ok,
    tttLargeFiber36Block2Chunk3ParentPath_1_ok,
    tttLargeFiber36Block2Chunk3ParentPath_2_ok,
    tttLargeFiber36Block2Chunk3ParentPath_3_ok,
    tttLargeFiber36Block2Chunk3ParentPath_4_ok,
    tttLargeFiber36Block2Chunk3ParentPath_5_ok,
    tttLargeFiber36Block2Chunk3ParentPath_6_ok,
    tttLargeFiber36Block2Chunk3ParentPath_7_ok,
    tttLargeFiber36Block2Chunk3ParentPath_8_ok,
    tttLargeFiber36Block2Chunk3ParentPath_9_ok,
    tttLargeFiber36Block2Chunk3ParentPath_10_ok,
    tttLargeFiber36Block2Chunk3ParentPath_11_ok,
    tttLargeFiber36Block2Chunk3ParentPath_12_ok,
    tttLargeFiber36Block2Chunk3ParentPath_13_ok,
    tttLargeFiber36Block2Chunk3ParentPath_14_ok,
    tttLargeFiber36Block2Chunk3ParentPath_15_ok]

def tttLargeFiber36Block2Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber36CountsAudit &&
    tttLargeFiber36Block2Chunk3SourcesCheck &&
    tttLargeFiber36Block2Chunk3RowsAudit &&
    tttLargeFiber36Block2Chunk3ParentMapAudit &&
    tttLargeFiber36Block2Chunk3ParentsAudit

theorem tttLargeFiber36Block2Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber36Block2Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber36Block2Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber36CountsAudit_ok,
    tttLargeFiber36Block2Chunk3SourcesCheck_ok,
    tttLargeFiber36Block2Chunk3RowsAudit_ok,
    tttLargeFiber36Block2Chunk3ParentMapAudit_ok,
    tttLargeFiber36Block2Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber36Block2Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
