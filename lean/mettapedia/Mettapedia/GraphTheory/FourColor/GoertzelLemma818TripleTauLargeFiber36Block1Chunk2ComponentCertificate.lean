import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 36, block 1 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber36Block1Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber36Data

def tttLargeFiber36Block1Chunk2Sources : List Nat :=
  [   368, 369, 370, 371, 372, 373, 374, 375,
   376, 377, 378, 379, 380, 381, 382, 383]

def tttLargeFiber36Row96 : TripleComponentParentRow :=
  tripleRow 368 304 9 108 132 8 100 132
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row97 : TripleComponentParentRow :=
  tripleRow 369 305 9 108 133 8 100 133
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row98 : TripleComponentParentRow :=
  tripleRow 370 306 9 108 134 8 100 134
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row99 : TripleComponentParentRow :=
  tripleRow 371 307 9 108 135 8 100 135
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row100 : TripleComponentParentRow :=
  tripleRow 372 308 9 108 180 8 100 180
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row101 : TripleComponentParentRow :=
  tripleRow 373 309 9 108 181 8 100 181
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row102 : TripleComponentParentRow :=
  tripleRow 374 310 9 108 182 8 100 182
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row103 : TripleComponentParentRow :=
  tripleRow 375 311 9 108 183 8 100 183
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row104 : TripleComponentParentRow :=
  tripleRow 376 312 9 109 140 8 101 140
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row105 : TripleComponentParentRow :=
  tripleRow 377 313 9 109 141 8 101 141
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row106 : TripleComponentParentRow :=
  tripleRow 378 314 9 109 142 8 101 142
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row107 : TripleComponentParentRow :=
  tripleRow 379 315 9 109 143 8 101 143
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row108 : TripleComponentParentRow :=
  tripleRow 380 316 9 109 188 8 101 188
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row109 : TripleComponentParentRow :=
  tripleRow 381 317 9 109 189 8 101 189
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row110 : TripleComponentParentRow :=
  tripleRow 382 318 9 109 190 8 101 190
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Row111 : TripleComponentParentRow :=
  tripleRow 383 319 9 109 191 8 101 191
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber36Block1Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber36Row96
  , tttLargeFiber36Row97
  , tttLargeFiber36Row98
  , tttLargeFiber36Row99
  , tttLargeFiber36Row100
  , tttLargeFiber36Row101
  , tttLargeFiber36Row102
  , tttLargeFiber36Row103
  , tttLargeFiber36Row104
  , tttLargeFiber36Row105
  , tttLargeFiber36Row106
  , tttLargeFiber36Row107
  , tttLargeFiber36Row108
  , tttLargeFiber36Row109
  , tttLargeFiber36Row110
  , tttLargeFiber36Row111
  ]

def tttLargeFiber36Block1Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (272 <= i) && decide (i < 528)) ||
    (decide (1904 <= i) && decide (i < 2160))

def tttLargeFiber36Block1Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber36Block1Chunk2ExpectedContains row.source &&
    tttLargeFiber36Block1Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber36Key &&
          chainInputKey tttWord t == tttLargeFiber36Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber36Block1Chunk2SourcesCheck : Bool :=
  (tttLargeFiber36Block1Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber36Block1Chunk2Sources

theorem tttLargeFiber36Block1Chunk2SourcesCheck_ok :
    tttLargeFiber36Block1Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber36Block1Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber36Block1Chunk2RowValid
    (listGetD tttLargeFiber36Block1Chunk2Rows i default)

def tttLargeFiber36Block1Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber36Block1Chunk2Rows i default
  row.parent == tttLargeFiber36ParentOf row.source

def tttLargeFiber36Block1Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber36Block1Chunk2Sources 0 0 == 368
      && tttLargeFiber36ParentOf 368 == 304
      && tttLargeFiber36ParentOf 304 == 320
      && tttLargeFiber36ParentOf 320 == 280
      && tttLargeFiber36ParentOf 280 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 1 => listGetD tttLargeFiber36Block1Chunk2Sources 1 0 == 369
      && tttLargeFiber36ParentOf 369 == 305
      && tttLargeFiber36ParentOf 305 == 321
      && tttLargeFiber36ParentOf 321 == 281
      && tttLargeFiber36ParentOf 281 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 2 => listGetD tttLargeFiber36Block1Chunk2Sources 2 0 == 370
      && tttLargeFiber36ParentOf 370 == 306
      && tttLargeFiber36ParentOf 306 == 294
      && tttLargeFiber36ParentOf 294 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 3 => listGetD tttLargeFiber36Block1Chunk2Sources 3 0 == 371
      && tttLargeFiber36ParentOf 371 == 307
      && tttLargeFiber36ParentOf 307 == 295
      && tttLargeFiber36ParentOf 295 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 4 => listGetD tttLargeFiber36Block1Chunk2Sources 4 0 == 372
      && tttLargeFiber36ParentOf 372 == 308
      && tttLargeFiber36ParentOf 308 == 290
      && tttLargeFiber36ParentOf 290 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 5 => listGetD tttLargeFiber36Block1Chunk2Sources 5 0 == 373
      && tttLargeFiber36ParentOf 373 == 309
      && tttLargeFiber36ParentOf 309 == 311
      && tttLargeFiber36ParentOf 311 == 288
      && tttLargeFiber36ParentOf 288 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 6 => listGetD tttLargeFiber36Block1Chunk2Sources 6 0 == 374
      && tttLargeFiber36ParentOf 374 == 310
      && tttLargeFiber36ParentOf 310 == 289
      && tttLargeFiber36ParentOf 289 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 7 => listGetD tttLargeFiber36Block1Chunk2Sources 7 0 == 375
      && tttLargeFiber36ParentOf 375 == 311
      && tttLargeFiber36ParentOf 311 == 288
      && tttLargeFiber36ParentOf 288 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 8 => listGetD tttLargeFiber36Block1Chunk2Sources 8 0 == 376
      && tttLargeFiber36ParentOf 376 == 312
      && tttLargeFiber36ParentOf 312 == 328
      && tttLargeFiber36ParentOf 328 == 272
      && 272 == tttLargeFiber36Root
      && decide (3 <= tttLargeFiber36MaxParentDepth)
  | 9 => listGetD tttLargeFiber36Block1Chunk2Sources 9 0 == 377
      && tttLargeFiber36ParentOf 377 == 313
      && tttLargeFiber36ParentOf 313 == 329
      && tttLargeFiber36ParentOf 329 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 10 => listGetD tttLargeFiber36Block1Chunk2Sources 10 0 == 378
      && tttLargeFiber36ParentOf 378 == 314
      && tttLargeFiber36ParentOf 314 == 330
      && tttLargeFiber36ParentOf 330 == 274
      && tttLargeFiber36ParentOf 274 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 11 => listGetD tttLargeFiber36Block1Chunk2Sources 11 0 == 379
      && tttLargeFiber36ParentOf 379 == 315
      && tttLargeFiber36ParentOf 315 == 312
      && tttLargeFiber36ParentOf 312 == 328
      && tttLargeFiber36ParentOf 328 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 12 => listGetD tttLargeFiber36Block1Chunk2Sources 12 0 == 380
      && tttLargeFiber36ParentOf 380 == 316
      && tttLargeFiber36ParentOf 316 == 312
      && tttLargeFiber36ParentOf 312 == 328
      && tttLargeFiber36ParentOf 328 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | 13 => listGetD tttLargeFiber36Block1Chunk2Sources 13 0 == 381
      && tttLargeFiber36ParentOf 381 == 317
      && tttLargeFiber36ParentOf 317 == 313
      && tttLargeFiber36ParentOf 313 == 329
      && tttLargeFiber36ParentOf 329 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 14 => listGetD tttLargeFiber36Block1Chunk2Sources 14 0 == 382
      && tttLargeFiber36ParentOf 382 == 318
      && tttLargeFiber36ParentOf 318 == 334
      && tttLargeFiber36ParentOf 334 == 278
      && tttLargeFiber36ParentOf 278 == 273
      && tttLargeFiber36ParentOf 273 == 272
      && 272 == tttLargeFiber36Root
      && decide (5 <= tttLargeFiber36MaxParentDepth)
  | 15 => listGetD tttLargeFiber36Block1Chunk2Sources 15 0 == 383
      && tttLargeFiber36ParentOf 383 == 319
      && tttLargeFiber36ParentOf 319 == 335
      && tttLargeFiber36ParentOf 335 == 279
      && tttLargeFiber36ParentOf 279 == 272
      && 272 == tttLargeFiber36Root
      && decide (4 <= tttLargeFiber36MaxParentDepth)
  | _ => false

theorem tttLargeFiber36Block1Chunk2Row_0_ok :
    tttLargeFiber36Block1Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2Row_1_ok :
    tttLargeFiber36Block1Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2Row_2_ok :
    tttLargeFiber36Block1Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2Row_3_ok :
    tttLargeFiber36Block1Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2Row_4_ok :
    tttLargeFiber36Block1Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2Row_5_ok :
    tttLargeFiber36Block1Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2Row_6_ok :
    tttLargeFiber36Block1Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2Row_7_ok :
    tttLargeFiber36Block1Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2Row_8_ok :
    tttLargeFiber36Block1Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2Row_9_ok :
    tttLargeFiber36Block1Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2Row_10_ok :
    tttLargeFiber36Block1Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2Row_11_ok :
    tttLargeFiber36Block1Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2Row_12_ok :
    tttLargeFiber36Block1Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2Row_13_ok :
    tttLargeFiber36Block1Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2Row_14_ok :
    tttLargeFiber36Block1Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2Row_15_ok :
    tttLargeFiber36Block1Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentMap_0_ok :
    tttLargeFiber36Block1Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentMap_1_ok :
    tttLargeFiber36Block1Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentMap_2_ok :
    tttLargeFiber36Block1Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentMap_3_ok :
    tttLargeFiber36Block1Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentMap_4_ok :
    tttLargeFiber36Block1Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentMap_5_ok :
    tttLargeFiber36Block1Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentMap_6_ok :
    tttLargeFiber36Block1Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentMap_7_ok :
    tttLargeFiber36Block1Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentMap_8_ok :
    tttLargeFiber36Block1Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentMap_9_ok :
    tttLargeFiber36Block1Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentMap_10_ok :
    tttLargeFiber36Block1Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentMap_11_ok :
    tttLargeFiber36Block1Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentMap_12_ok :
    tttLargeFiber36Block1Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentMap_13_ok :
    tttLargeFiber36Block1Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentMap_14_ok :
    tttLargeFiber36Block1Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentMap_15_ok :
    tttLargeFiber36Block1Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentPath_0_ok :
    tttLargeFiber36Block1Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentPath_1_ok :
    tttLargeFiber36Block1Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentPath_2_ok :
    tttLargeFiber36Block1Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentPath_3_ok :
    tttLargeFiber36Block1Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentPath_4_ok :
    tttLargeFiber36Block1Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentPath_5_ok :
    tttLargeFiber36Block1Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentPath_6_ok :
    tttLargeFiber36Block1Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentPath_7_ok :
    tttLargeFiber36Block1Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentPath_8_ok :
    tttLargeFiber36Block1Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentPath_9_ok :
    tttLargeFiber36Block1Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentPath_10_ok :
    tttLargeFiber36Block1Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentPath_11_ok :
    tttLargeFiber36Block1Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentPath_12_ok :
    tttLargeFiber36Block1Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentPath_13_ok :
    tttLargeFiber36Block1Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentPath_14_ok :
    tttLargeFiber36Block1Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber36Block1Chunk2ParentPath_15_ok :
    tttLargeFiber36Block1Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber36Block1Chunk2RowsAudit : Bool :=
  tttLargeFiber36Block1Chunk2RowCheck 0
    && tttLargeFiber36Block1Chunk2RowCheck 1
    && tttLargeFiber36Block1Chunk2RowCheck 2
    && tttLargeFiber36Block1Chunk2RowCheck 3
    && tttLargeFiber36Block1Chunk2RowCheck 4
    && tttLargeFiber36Block1Chunk2RowCheck 5
    && tttLargeFiber36Block1Chunk2RowCheck 6
    && tttLargeFiber36Block1Chunk2RowCheck 7
    && tttLargeFiber36Block1Chunk2RowCheck 8
    && tttLargeFiber36Block1Chunk2RowCheck 9
    && tttLargeFiber36Block1Chunk2RowCheck 10
    && tttLargeFiber36Block1Chunk2RowCheck 11
    && tttLargeFiber36Block1Chunk2RowCheck 12
    && tttLargeFiber36Block1Chunk2RowCheck 13
    && tttLargeFiber36Block1Chunk2RowCheck 14
    && tttLargeFiber36Block1Chunk2RowCheck 15

theorem tttLargeFiber36Block1Chunk2RowsAudit_ok :
    tttLargeFiber36Block1Chunk2RowsAudit = true := by
  simp [tttLargeFiber36Block1Chunk2RowsAudit,
    tttLargeFiber36Block1Chunk2Row_0_ok,
    tttLargeFiber36Block1Chunk2Row_1_ok,
    tttLargeFiber36Block1Chunk2Row_2_ok,
    tttLargeFiber36Block1Chunk2Row_3_ok,
    tttLargeFiber36Block1Chunk2Row_4_ok,
    tttLargeFiber36Block1Chunk2Row_5_ok,
    tttLargeFiber36Block1Chunk2Row_6_ok,
    tttLargeFiber36Block1Chunk2Row_7_ok,
    tttLargeFiber36Block1Chunk2Row_8_ok,
    tttLargeFiber36Block1Chunk2Row_9_ok,
    tttLargeFiber36Block1Chunk2Row_10_ok,
    tttLargeFiber36Block1Chunk2Row_11_ok,
    tttLargeFiber36Block1Chunk2Row_12_ok,
    tttLargeFiber36Block1Chunk2Row_13_ok,
    tttLargeFiber36Block1Chunk2Row_14_ok,
    tttLargeFiber36Block1Chunk2Row_15_ok]

def tttLargeFiber36Block1Chunk2ParentMapAudit : Bool :=
  tttLargeFiber36Block1Chunk2ParentMapCheck 0
    && tttLargeFiber36Block1Chunk2ParentMapCheck 1
    && tttLargeFiber36Block1Chunk2ParentMapCheck 2
    && tttLargeFiber36Block1Chunk2ParentMapCheck 3
    && tttLargeFiber36Block1Chunk2ParentMapCheck 4
    && tttLargeFiber36Block1Chunk2ParentMapCheck 5
    && tttLargeFiber36Block1Chunk2ParentMapCheck 6
    && tttLargeFiber36Block1Chunk2ParentMapCheck 7
    && tttLargeFiber36Block1Chunk2ParentMapCheck 8
    && tttLargeFiber36Block1Chunk2ParentMapCheck 9
    && tttLargeFiber36Block1Chunk2ParentMapCheck 10
    && tttLargeFiber36Block1Chunk2ParentMapCheck 11
    && tttLargeFiber36Block1Chunk2ParentMapCheck 12
    && tttLargeFiber36Block1Chunk2ParentMapCheck 13
    && tttLargeFiber36Block1Chunk2ParentMapCheck 14
    && tttLargeFiber36Block1Chunk2ParentMapCheck 15

theorem tttLargeFiber36Block1Chunk2ParentMapAudit_ok :
    tttLargeFiber36Block1Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber36Block1Chunk2ParentMapAudit,
    tttLargeFiber36Block1Chunk2ParentMap_0_ok,
    tttLargeFiber36Block1Chunk2ParentMap_1_ok,
    tttLargeFiber36Block1Chunk2ParentMap_2_ok,
    tttLargeFiber36Block1Chunk2ParentMap_3_ok,
    tttLargeFiber36Block1Chunk2ParentMap_4_ok,
    tttLargeFiber36Block1Chunk2ParentMap_5_ok,
    tttLargeFiber36Block1Chunk2ParentMap_6_ok,
    tttLargeFiber36Block1Chunk2ParentMap_7_ok,
    tttLargeFiber36Block1Chunk2ParentMap_8_ok,
    tttLargeFiber36Block1Chunk2ParentMap_9_ok,
    tttLargeFiber36Block1Chunk2ParentMap_10_ok,
    tttLargeFiber36Block1Chunk2ParentMap_11_ok,
    tttLargeFiber36Block1Chunk2ParentMap_12_ok,
    tttLargeFiber36Block1Chunk2ParentMap_13_ok,
    tttLargeFiber36Block1Chunk2ParentMap_14_ok,
    tttLargeFiber36Block1Chunk2ParentMap_15_ok]

def tttLargeFiber36Block1Chunk2ParentsAudit : Bool :=
  tttLargeFiber36Block1Chunk2ParentPathCheck 0
    && tttLargeFiber36Block1Chunk2ParentPathCheck 1
    && tttLargeFiber36Block1Chunk2ParentPathCheck 2
    && tttLargeFiber36Block1Chunk2ParentPathCheck 3
    && tttLargeFiber36Block1Chunk2ParentPathCheck 4
    && tttLargeFiber36Block1Chunk2ParentPathCheck 5
    && tttLargeFiber36Block1Chunk2ParentPathCheck 6
    && tttLargeFiber36Block1Chunk2ParentPathCheck 7
    && tttLargeFiber36Block1Chunk2ParentPathCheck 8
    && tttLargeFiber36Block1Chunk2ParentPathCheck 9
    && tttLargeFiber36Block1Chunk2ParentPathCheck 10
    && tttLargeFiber36Block1Chunk2ParentPathCheck 11
    && tttLargeFiber36Block1Chunk2ParentPathCheck 12
    && tttLargeFiber36Block1Chunk2ParentPathCheck 13
    && tttLargeFiber36Block1Chunk2ParentPathCheck 14
    && tttLargeFiber36Block1Chunk2ParentPathCheck 15

theorem tttLargeFiber36Block1Chunk2ParentsAudit_ok :
    tttLargeFiber36Block1Chunk2ParentsAudit = true := by
  simp [tttLargeFiber36Block1Chunk2ParentsAudit,
    tttLargeFiber36Block1Chunk2ParentPath_0_ok,
    tttLargeFiber36Block1Chunk2ParentPath_1_ok,
    tttLargeFiber36Block1Chunk2ParentPath_2_ok,
    tttLargeFiber36Block1Chunk2ParentPath_3_ok,
    tttLargeFiber36Block1Chunk2ParentPath_4_ok,
    tttLargeFiber36Block1Chunk2ParentPath_5_ok,
    tttLargeFiber36Block1Chunk2ParentPath_6_ok,
    tttLargeFiber36Block1Chunk2ParentPath_7_ok,
    tttLargeFiber36Block1Chunk2ParentPath_8_ok,
    tttLargeFiber36Block1Chunk2ParentPath_9_ok,
    tttLargeFiber36Block1Chunk2ParentPath_10_ok,
    tttLargeFiber36Block1Chunk2ParentPath_11_ok,
    tttLargeFiber36Block1Chunk2ParentPath_12_ok,
    tttLargeFiber36Block1Chunk2ParentPath_13_ok,
    tttLargeFiber36Block1Chunk2ParentPath_14_ok,
    tttLargeFiber36Block1Chunk2ParentPath_15_ok]

def tttLargeFiber36Block1Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber36CountsAudit &&
    tttLargeFiber36Block1Chunk2SourcesCheck &&
    tttLargeFiber36Block1Chunk2RowsAudit &&
    tttLargeFiber36Block1Chunk2ParentMapAudit &&
    tttLargeFiber36Block1Chunk2ParentsAudit

theorem tttLargeFiber36Block1Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber36Block1Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber36Block1Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber36CountsAudit_ok,
    tttLargeFiber36Block1Chunk2SourcesCheck_ok,
    tttLargeFiber36Block1Chunk2RowsAudit_ok,
    tttLargeFiber36Block1Chunk2ParentMapAudit_ok,
    tttLargeFiber36Block1Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber36Block1Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
