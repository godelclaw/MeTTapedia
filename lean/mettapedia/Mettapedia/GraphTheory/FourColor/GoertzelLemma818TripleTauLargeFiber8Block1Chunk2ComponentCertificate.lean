import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 8, block 1 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber8Block1Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Data

def tttLargeFiber8Block1Chunk2Sources : List Nat :=
  [   4464, 4465, 4466, 4467, 4468, 4469, 4470, 4471,
   4472, 4473, 4474, 4475, 4476, 4477, 4478, 4479]

def tttLargeFiber8Row96 : TripleComponentParentRow :=
  tripleRow 4464 4400 133 172 132 132 164 132
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row97 : TripleComponentParentRow :=
  tripleRow 4465 4401 133 172 133 132 164 133
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row98 : TripleComponentParentRow :=
  tripleRow 4466 4402 133 172 134 132 164 134
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row99 : TripleComponentParentRow :=
  tripleRow 4467 4403 133 172 135 132 164 135
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row100 : TripleComponentParentRow :=
  tripleRow 4468 4404 133 172 180 132 164 180
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row101 : TripleComponentParentRow :=
  tripleRow 4469 4405 133 172 181 132 164 181
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row102 : TripleComponentParentRow :=
  tripleRow 4470 4406 133 172 182 132 164 182
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row103 : TripleComponentParentRow :=
  tripleRow 4471 4407 133 172 183 132 164 183
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row104 : TripleComponentParentRow :=
  tripleRow 4472 4408 133 173 140 132 165 140
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row105 : TripleComponentParentRow :=
  tripleRow 4473 4409 133 173 141 132 165 141
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row106 : TripleComponentParentRow :=
  tripleRow 4474 4410 133 173 142 132 165 142
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row107 : TripleComponentParentRow :=
  tripleRow 4475 4411 133 173 143 132 165 143
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row108 : TripleComponentParentRow :=
  tripleRow 4476 4412 133 173 188 132 165 188
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row109 : TripleComponentParentRow :=
  tripleRow 4477 4413 133 173 189 132 165 189
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row110 : TripleComponentParentRow :=
  tripleRow 4478 4414 133 173 190 132 165 190
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row111 : TripleComponentParentRow :=
  tripleRow 4479 4415 133 173 191 132 165 191
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Block1Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber8Row96
  , tttLargeFiber8Row97
  , tttLargeFiber8Row98
  , tttLargeFiber8Row99
  , tttLargeFiber8Row100
  , tttLargeFiber8Row101
  , tttLargeFiber8Row102
  , tttLargeFiber8Row103
  , tttLargeFiber8Row104
  , tttLargeFiber8Row105
  , tttLargeFiber8Row106
  , tttLargeFiber8Row107
  , tttLargeFiber8Row108
  , tttLargeFiber8Row109
  , tttLargeFiber8Row110
  , tttLargeFiber8Row111
  ]

def tttLargeFiber8Block1Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (4368 <= i) && decide (i < 4624)) ||
    (decide (6000 <= i) && decide (i < 6256))

def tttLargeFiber8Block1Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber8Block1Chunk2ExpectedContains row.source &&
    tttLargeFiber8Block1Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber8Key &&
          chainInputKey tttWord t == tttLargeFiber8Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber8Block1Chunk2SourcesCheck : Bool :=
  (tttLargeFiber8Block1Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber8Block1Chunk2Sources

theorem tttLargeFiber8Block1Chunk2SourcesCheck_ok :
    tttLargeFiber8Block1Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber8Block1Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber8Block1Chunk2RowValid
    (listGetD tttLargeFiber8Block1Chunk2Rows i default)

def tttLargeFiber8Block1Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber8Block1Chunk2Rows i default
  row.parent == tttLargeFiber8ParentOf row.source

def tttLargeFiber8Block1Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber8Block1Chunk2Sources 0 0 == 4464
      && tttLargeFiber8ParentOf 4464 == 4400
      && tttLargeFiber8ParentOf 4400 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (2 <= tttLargeFiber8MaxParentDepth)
  | 1 => listGetD tttLargeFiber8Block1Chunk2Sources 1 0 == 4465
      && tttLargeFiber8ParentOf 4465 == 4401
      && tttLargeFiber8ParentOf 4401 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 2 => listGetD tttLargeFiber8Block1Chunk2Sources 2 0 == 4466
      && tttLargeFiber8ParentOf 4466 == 4402
      && tttLargeFiber8ParentOf 4402 == 4370
      && tttLargeFiber8ParentOf 4370 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 3 => listGetD tttLargeFiber8Block1Chunk2Sources 3 0 == 4467
      && tttLargeFiber8ParentOf 4467 == 4403
      && tttLargeFiber8ParentOf 4403 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 4 => listGetD tttLargeFiber8Block1Chunk2Sources 4 0 == 4468
      && tttLargeFiber8ParentOf 4468 == 4404
      && tttLargeFiber8ParentOf 4404 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 5 => listGetD tttLargeFiber8Block1Chunk2Sources 5 0 == 4469
      && tttLargeFiber8ParentOf 4469 == 4405
      && tttLargeFiber8ParentOf 4405 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 6 => listGetD tttLargeFiber8Block1Chunk2Sources 6 0 == 4470
      && tttLargeFiber8ParentOf 4470 == 4406
      && tttLargeFiber8ParentOf 4406 == 4374
      && tttLargeFiber8ParentOf 4374 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 7 => listGetD tttLargeFiber8Block1Chunk2Sources 7 0 == 4471
      && tttLargeFiber8ParentOf 4471 == 4407
      && tttLargeFiber8ParentOf 4407 == 4375
      && tttLargeFiber8ParentOf 4375 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 8 => listGetD tttLargeFiber8Block1Chunk2Sources 8 0 == 4472
      && tttLargeFiber8ParentOf 4472 == 4408
      && tttLargeFiber8ParentOf 4408 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 9 => listGetD tttLargeFiber8Block1Chunk2Sources 9 0 == 4473
      && tttLargeFiber8ParentOf 4473 == 4409
      && tttLargeFiber8ParentOf 4409 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 10 => listGetD tttLargeFiber8Block1Chunk2Sources 10 0 == 4474
      && tttLargeFiber8ParentOf 4474 == 4410
      && tttLargeFiber8ParentOf 4410 == 4378
      && tttLargeFiber8ParentOf 4378 == 4370
      && tttLargeFiber8ParentOf 4370 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 11 => listGetD tttLargeFiber8Block1Chunk2Sources 11 0 == 4475
      && tttLargeFiber8ParentOf 4475 == 4411
      && tttLargeFiber8ParentOf 4411 == 4379
      && tttLargeFiber8ParentOf 4379 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 12 => listGetD tttLargeFiber8Block1Chunk2Sources 12 0 == 4476
      && tttLargeFiber8ParentOf 4476 == 4412
      && tttLargeFiber8ParentOf 4412 == 4380
      && tttLargeFiber8ParentOf 4380 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 13 => listGetD tttLargeFiber8Block1Chunk2Sources 13 0 == 4477
      && tttLargeFiber8ParentOf 4477 == 4413
      && tttLargeFiber8ParentOf 4413 == 4381
      && tttLargeFiber8ParentOf 4381 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 14 => listGetD tttLargeFiber8Block1Chunk2Sources 14 0 == 4478
      && tttLargeFiber8ParentOf 4478 == 4414
      && tttLargeFiber8ParentOf 4414 == 4382
      && tttLargeFiber8ParentOf 4382 == 4374
      && tttLargeFiber8ParentOf 4374 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 15 => listGetD tttLargeFiber8Block1Chunk2Sources 15 0 == 4479
      && tttLargeFiber8ParentOf 4479 == 4415
      && tttLargeFiber8ParentOf 4415 == 4383
      && tttLargeFiber8ParentOf 4383 == 4375
      && tttLargeFiber8ParentOf 4375 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | _ => false

theorem tttLargeFiber8Block1Chunk2Row_0_ok :
    tttLargeFiber8Block1Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2Row_1_ok :
    tttLargeFiber8Block1Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2Row_2_ok :
    tttLargeFiber8Block1Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2Row_3_ok :
    tttLargeFiber8Block1Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2Row_4_ok :
    tttLargeFiber8Block1Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2Row_5_ok :
    tttLargeFiber8Block1Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2Row_6_ok :
    tttLargeFiber8Block1Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2Row_7_ok :
    tttLargeFiber8Block1Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2Row_8_ok :
    tttLargeFiber8Block1Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2Row_9_ok :
    tttLargeFiber8Block1Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2Row_10_ok :
    tttLargeFiber8Block1Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2Row_11_ok :
    tttLargeFiber8Block1Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2Row_12_ok :
    tttLargeFiber8Block1Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2Row_13_ok :
    tttLargeFiber8Block1Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2Row_14_ok :
    tttLargeFiber8Block1Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2Row_15_ok :
    tttLargeFiber8Block1Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentMap_0_ok :
    tttLargeFiber8Block1Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentMap_1_ok :
    tttLargeFiber8Block1Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentMap_2_ok :
    tttLargeFiber8Block1Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentMap_3_ok :
    tttLargeFiber8Block1Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentMap_4_ok :
    tttLargeFiber8Block1Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentMap_5_ok :
    tttLargeFiber8Block1Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentMap_6_ok :
    tttLargeFiber8Block1Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentMap_7_ok :
    tttLargeFiber8Block1Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentMap_8_ok :
    tttLargeFiber8Block1Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentMap_9_ok :
    tttLargeFiber8Block1Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentMap_10_ok :
    tttLargeFiber8Block1Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentMap_11_ok :
    tttLargeFiber8Block1Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentMap_12_ok :
    tttLargeFiber8Block1Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentMap_13_ok :
    tttLargeFiber8Block1Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentMap_14_ok :
    tttLargeFiber8Block1Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentMap_15_ok :
    tttLargeFiber8Block1Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentPath_0_ok :
    tttLargeFiber8Block1Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentPath_1_ok :
    tttLargeFiber8Block1Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentPath_2_ok :
    tttLargeFiber8Block1Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentPath_3_ok :
    tttLargeFiber8Block1Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentPath_4_ok :
    tttLargeFiber8Block1Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentPath_5_ok :
    tttLargeFiber8Block1Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentPath_6_ok :
    tttLargeFiber8Block1Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentPath_7_ok :
    tttLargeFiber8Block1Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentPath_8_ok :
    tttLargeFiber8Block1Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentPath_9_ok :
    tttLargeFiber8Block1Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentPath_10_ok :
    tttLargeFiber8Block1Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentPath_11_ok :
    tttLargeFiber8Block1Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentPath_12_ok :
    tttLargeFiber8Block1Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentPath_13_ok :
    tttLargeFiber8Block1Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentPath_14_ok :
    tttLargeFiber8Block1Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber8Block1Chunk2ParentPath_15_ok :
    tttLargeFiber8Block1Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber8Block1Chunk2RowsAudit : Bool :=
  tttLargeFiber8Block1Chunk2RowCheck 0
    && tttLargeFiber8Block1Chunk2RowCheck 1
    && tttLargeFiber8Block1Chunk2RowCheck 2
    && tttLargeFiber8Block1Chunk2RowCheck 3
    && tttLargeFiber8Block1Chunk2RowCheck 4
    && tttLargeFiber8Block1Chunk2RowCheck 5
    && tttLargeFiber8Block1Chunk2RowCheck 6
    && tttLargeFiber8Block1Chunk2RowCheck 7
    && tttLargeFiber8Block1Chunk2RowCheck 8
    && tttLargeFiber8Block1Chunk2RowCheck 9
    && tttLargeFiber8Block1Chunk2RowCheck 10
    && tttLargeFiber8Block1Chunk2RowCheck 11
    && tttLargeFiber8Block1Chunk2RowCheck 12
    && tttLargeFiber8Block1Chunk2RowCheck 13
    && tttLargeFiber8Block1Chunk2RowCheck 14
    && tttLargeFiber8Block1Chunk2RowCheck 15

theorem tttLargeFiber8Block1Chunk2RowsAudit_ok :
    tttLargeFiber8Block1Chunk2RowsAudit = true := by
  simp [tttLargeFiber8Block1Chunk2RowsAudit,
    tttLargeFiber8Block1Chunk2Row_0_ok,
    tttLargeFiber8Block1Chunk2Row_1_ok,
    tttLargeFiber8Block1Chunk2Row_2_ok,
    tttLargeFiber8Block1Chunk2Row_3_ok,
    tttLargeFiber8Block1Chunk2Row_4_ok,
    tttLargeFiber8Block1Chunk2Row_5_ok,
    tttLargeFiber8Block1Chunk2Row_6_ok,
    tttLargeFiber8Block1Chunk2Row_7_ok,
    tttLargeFiber8Block1Chunk2Row_8_ok,
    tttLargeFiber8Block1Chunk2Row_9_ok,
    tttLargeFiber8Block1Chunk2Row_10_ok,
    tttLargeFiber8Block1Chunk2Row_11_ok,
    tttLargeFiber8Block1Chunk2Row_12_ok,
    tttLargeFiber8Block1Chunk2Row_13_ok,
    tttLargeFiber8Block1Chunk2Row_14_ok,
    tttLargeFiber8Block1Chunk2Row_15_ok]

def tttLargeFiber8Block1Chunk2ParentMapAudit : Bool :=
  tttLargeFiber8Block1Chunk2ParentMapCheck 0
    && tttLargeFiber8Block1Chunk2ParentMapCheck 1
    && tttLargeFiber8Block1Chunk2ParentMapCheck 2
    && tttLargeFiber8Block1Chunk2ParentMapCheck 3
    && tttLargeFiber8Block1Chunk2ParentMapCheck 4
    && tttLargeFiber8Block1Chunk2ParentMapCheck 5
    && tttLargeFiber8Block1Chunk2ParentMapCheck 6
    && tttLargeFiber8Block1Chunk2ParentMapCheck 7
    && tttLargeFiber8Block1Chunk2ParentMapCheck 8
    && tttLargeFiber8Block1Chunk2ParentMapCheck 9
    && tttLargeFiber8Block1Chunk2ParentMapCheck 10
    && tttLargeFiber8Block1Chunk2ParentMapCheck 11
    && tttLargeFiber8Block1Chunk2ParentMapCheck 12
    && tttLargeFiber8Block1Chunk2ParentMapCheck 13
    && tttLargeFiber8Block1Chunk2ParentMapCheck 14
    && tttLargeFiber8Block1Chunk2ParentMapCheck 15

theorem tttLargeFiber8Block1Chunk2ParentMapAudit_ok :
    tttLargeFiber8Block1Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber8Block1Chunk2ParentMapAudit,
    tttLargeFiber8Block1Chunk2ParentMap_0_ok,
    tttLargeFiber8Block1Chunk2ParentMap_1_ok,
    tttLargeFiber8Block1Chunk2ParentMap_2_ok,
    tttLargeFiber8Block1Chunk2ParentMap_3_ok,
    tttLargeFiber8Block1Chunk2ParentMap_4_ok,
    tttLargeFiber8Block1Chunk2ParentMap_5_ok,
    tttLargeFiber8Block1Chunk2ParentMap_6_ok,
    tttLargeFiber8Block1Chunk2ParentMap_7_ok,
    tttLargeFiber8Block1Chunk2ParentMap_8_ok,
    tttLargeFiber8Block1Chunk2ParentMap_9_ok,
    tttLargeFiber8Block1Chunk2ParentMap_10_ok,
    tttLargeFiber8Block1Chunk2ParentMap_11_ok,
    tttLargeFiber8Block1Chunk2ParentMap_12_ok,
    tttLargeFiber8Block1Chunk2ParentMap_13_ok,
    tttLargeFiber8Block1Chunk2ParentMap_14_ok,
    tttLargeFiber8Block1Chunk2ParentMap_15_ok]

def tttLargeFiber8Block1Chunk2ParentsAudit : Bool :=
  tttLargeFiber8Block1Chunk2ParentPathCheck 0
    && tttLargeFiber8Block1Chunk2ParentPathCheck 1
    && tttLargeFiber8Block1Chunk2ParentPathCheck 2
    && tttLargeFiber8Block1Chunk2ParentPathCheck 3
    && tttLargeFiber8Block1Chunk2ParentPathCheck 4
    && tttLargeFiber8Block1Chunk2ParentPathCheck 5
    && tttLargeFiber8Block1Chunk2ParentPathCheck 6
    && tttLargeFiber8Block1Chunk2ParentPathCheck 7
    && tttLargeFiber8Block1Chunk2ParentPathCheck 8
    && tttLargeFiber8Block1Chunk2ParentPathCheck 9
    && tttLargeFiber8Block1Chunk2ParentPathCheck 10
    && tttLargeFiber8Block1Chunk2ParentPathCheck 11
    && tttLargeFiber8Block1Chunk2ParentPathCheck 12
    && tttLargeFiber8Block1Chunk2ParentPathCheck 13
    && tttLargeFiber8Block1Chunk2ParentPathCheck 14
    && tttLargeFiber8Block1Chunk2ParentPathCheck 15

theorem tttLargeFiber8Block1Chunk2ParentsAudit_ok :
    tttLargeFiber8Block1Chunk2ParentsAudit = true := by
  simp [tttLargeFiber8Block1Chunk2ParentsAudit,
    tttLargeFiber8Block1Chunk2ParentPath_0_ok,
    tttLargeFiber8Block1Chunk2ParentPath_1_ok,
    tttLargeFiber8Block1Chunk2ParentPath_2_ok,
    tttLargeFiber8Block1Chunk2ParentPath_3_ok,
    tttLargeFiber8Block1Chunk2ParentPath_4_ok,
    tttLargeFiber8Block1Chunk2ParentPath_5_ok,
    tttLargeFiber8Block1Chunk2ParentPath_6_ok,
    tttLargeFiber8Block1Chunk2ParentPath_7_ok,
    tttLargeFiber8Block1Chunk2ParentPath_8_ok,
    tttLargeFiber8Block1Chunk2ParentPath_9_ok,
    tttLargeFiber8Block1Chunk2ParentPath_10_ok,
    tttLargeFiber8Block1Chunk2ParentPath_11_ok,
    tttLargeFiber8Block1Chunk2ParentPath_12_ok,
    tttLargeFiber8Block1Chunk2ParentPath_13_ok,
    tttLargeFiber8Block1Chunk2ParentPath_14_ok,
    tttLargeFiber8Block1Chunk2ParentPath_15_ok]

def tttLargeFiber8Block1Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber8CountsAudit &&
    tttLargeFiber8Block1Chunk2SourcesCheck &&
    tttLargeFiber8Block1Chunk2RowsAudit &&
    tttLargeFiber8Block1Chunk2ParentMapAudit &&
    tttLargeFiber8Block1Chunk2ParentsAudit

theorem tttLargeFiber8Block1Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber8Block1Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber8Block1Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber8CountsAudit_ok,
    tttLargeFiber8Block1Chunk2SourcesCheck_ok,
    tttLargeFiber8Block1Chunk2RowsAudit_ok,
    tttLargeFiber8Block1Chunk2ParentMapAudit_ok,
    tttLargeFiber8Block1Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber8Block1Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
