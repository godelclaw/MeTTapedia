import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 8, block 1 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber8Block1Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Data

def tttLargeFiber8Block1Chunk3Sources : List Nat :=
  [   4480, 4481, 4482, 4483, 4484, 4485, 4486, 4487,
   4488, 4489, 4490, 4491, 4492, 4493, 4494, 4495]

def tttLargeFiber8Row112 : TripleComponentParentRow :=
  tripleRow 4480 4416 133 174 64 132 166 64
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row113 : TripleComponentParentRow :=
  tripleRow 4481 4417 133 174 65 132 166 65
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row114 : TripleComponentParentRow :=
  tripleRow 4482 4418 133 174 66 132 166 66
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row115 : TripleComponentParentRow :=
  tripleRow 4483 4419 133 174 67 132 166 67
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row116 : TripleComponentParentRow :=
  tripleRow 4484 4420 133 174 116 132 166 116
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row117 : TripleComponentParentRow :=
  tripleRow 4485 4421 133 174 117 132 166 117
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row118 : TripleComponentParentRow :=
  tripleRow 4486 4422 133 174 118 132 166 118
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row119 : TripleComponentParentRow :=
  tripleRow 4487 4423 133 174 119 132 166 119
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row120 : TripleComponentParentRow :=
  tripleRow 4488 4424 133 175 72 132 167 72
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row121 : TripleComponentParentRow :=
  tripleRow 4489 4425 133 175 73 132 167 73
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row122 : TripleComponentParentRow :=
  tripleRow 4490 4426 133 175 74 132 167 74
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row123 : TripleComponentParentRow :=
  tripleRow 4491 4427 133 175 75 132 167 75
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row124 : TripleComponentParentRow :=
  tripleRow 4492 4428 133 175 124 132 167 124
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row125 : TripleComponentParentRow :=
  tripleRow 4493 4429 133 175 125 132 167 125
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row126 : TripleComponentParentRow :=
  tripleRow 4494 4430 133 175 126 132 167 126
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row127 : TripleComponentParentRow :=
  tripleRow 4495 4431 133 175 127 132 167 127
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Block1Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber8Row112
  , tttLargeFiber8Row113
  , tttLargeFiber8Row114
  , tttLargeFiber8Row115
  , tttLargeFiber8Row116
  , tttLargeFiber8Row117
  , tttLargeFiber8Row118
  , tttLargeFiber8Row119
  , tttLargeFiber8Row120
  , tttLargeFiber8Row121
  , tttLargeFiber8Row122
  , tttLargeFiber8Row123
  , tttLargeFiber8Row124
  , tttLargeFiber8Row125
  , tttLargeFiber8Row126
  , tttLargeFiber8Row127
  ]

def tttLargeFiber8Block1Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (4368 <= i) && decide (i < 4624)) ||
    (decide (6000 <= i) && decide (i < 6256))

def tttLargeFiber8Block1Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber8Block1Chunk3ExpectedContains row.source &&
    tttLargeFiber8Block1Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber8Key &&
          chainInputKey tttWord t == tttLargeFiber8Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber8Block1Chunk3SourcesCheck : Bool :=
  (tttLargeFiber8Block1Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber8Block1Chunk3Sources

theorem tttLargeFiber8Block1Chunk3SourcesCheck_ok :
    tttLargeFiber8Block1Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber8Block1Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber8Block1Chunk3RowValid
    (listGetD tttLargeFiber8Block1Chunk3Rows i default)

def tttLargeFiber8Block1Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber8Block1Chunk3Rows i default
  row.parent == tttLargeFiber8ParentOf row.source

def tttLargeFiber8Block1Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber8Block1Chunk3Sources 0 0 == 4480
      && tttLargeFiber8ParentOf 4480 == 4416
      && tttLargeFiber8ParentOf 4416 == 4400
      && tttLargeFiber8ParentOf 4400 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 1 => listGetD tttLargeFiber8Block1Chunk3Sources 1 0 == 4481
      && tttLargeFiber8ParentOf 4481 == 4417
      && tttLargeFiber8ParentOf 4417 == 4401
      && tttLargeFiber8ParentOf 4401 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 2 => listGetD tttLargeFiber8Block1Chunk3Sources 2 0 == 4482
      && tttLargeFiber8ParentOf 4482 == 4418
      && tttLargeFiber8ParentOf 4418 == 4416
      && tttLargeFiber8ParentOf 4416 == 4400
      && tttLargeFiber8ParentOf 4400 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 3 => listGetD tttLargeFiber8Block1Chunk3Sources 3 0 == 4483
      && tttLargeFiber8ParentOf 4483 == 4419
      && tttLargeFiber8ParentOf 4419 == 4403
      && tttLargeFiber8ParentOf 4403 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 4 => listGetD tttLargeFiber8Block1Chunk3Sources 4 0 == 4484
      && tttLargeFiber8ParentOf 4484 == 4420
      && tttLargeFiber8ParentOf 4420 == 4404
      && tttLargeFiber8ParentOf 4404 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 5 => listGetD tttLargeFiber8Block1Chunk3Sources 5 0 == 4485
      && tttLargeFiber8ParentOf 4485 == 4421
      && tttLargeFiber8ParentOf 4421 == 4405
      && tttLargeFiber8ParentOf 4405 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 6 => listGetD tttLargeFiber8Block1Chunk3Sources 6 0 == 4486
      && tttLargeFiber8ParentOf 4486 == 4422
      && tttLargeFiber8ParentOf 4422 == 4417
      && tttLargeFiber8ParentOf 4417 == 4401
      && tttLargeFiber8ParentOf 4401 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 7 => listGetD tttLargeFiber8Block1Chunk3Sources 7 0 == 4487
      && tttLargeFiber8ParentOf 4487 == 4423
      && tttLargeFiber8ParentOf 4423 == 4416
      && tttLargeFiber8ParentOf 4416 == 4400
      && tttLargeFiber8ParentOf 4400 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 8 => listGetD tttLargeFiber8Block1Chunk3Sources 8 0 == 4488
      && tttLargeFiber8ParentOf 4488 == 4424
      && tttLargeFiber8ParentOf 4424 == 4408
      && tttLargeFiber8ParentOf 4408 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 9 => listGetD tttLargeFiber8Block1Chunk3Sources 9 0 == 4489
      && tttLargeFiber8ParentOf 4489 == 4425
      && tttLargeFiber8ParentOf 4425 == 4409
      && tttLargeFiber8ParentOf 4409 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 10 => listGetD tttLargeFiber8Block1Chunk3Sources 10 0 == 4490
      && tttLargeFiber8ParentOf 4490 == 4426
      && tttLargeFiber8ParentOf 4426 == 4394
      && tttLargeFiber8ParentOf 4394 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 11 => listGetD tttLargeFiber8Block1Chunk3Sources 11 0 == 4491
      && tttLargeFiber8ParentOf 4491 == 4427
      && tttLargeFiber8ParentOf 4427 == 4395
      && tttLargeFiber8ParentOf 4395 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 12 => listGetD tttLargeFiber8Block1Chunk3Sources 12 0 == 4492
      && tttLargeFiber8ParentOf 4492 == 4428
      && tttLargeFiber8ParentOf 4428 == 4396
      && tttLargeFiber8ParentOf 4396 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 13 => listGetD tttLargeFiber8Block1Chunk3Sources 13 0 == 4493
      && tttLargeFiber8ParentOf 4493 == 4429
      && tttLargeFiber8ParentOf 4429 == 4397
      && tttLargeFiber8ParentOf 4397 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 14 => listGetD tttLargeFiber8Block1Chunk3Sources 14 0 == 4494
      && tttLargeFiber8ParentOf 4494 == 4430
      && tttLargeFiber8ParentOf 4430 == 4428
      && tttLargeFiber8ParentOf 4428 == 4396
      && tttLargeFiber8ParentOf 4396 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 15 => listGetD tttLargeFiber8Block1Chunk3Sources 15 0 == 4495
      && tttLargeFiber8ParentOf 4495 == 4431
      && tttLargeFiber8ParentOf 4431 == 4399
      && tttLargeFiber8ParentOf 4399 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | _ => false

theorem tttLargeFiber8Block1Chunk3Row_0_ok :
    tttLargeFiber8Block1Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3Row_1_ok :
    tttLargeFiber8Block1Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3Row_2_ok :
    tttLargeFiber8Block1Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3Row_3_ok :
    tttLargeFiber8Block1Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3Row_4_ok :
    tttLargeFiber8Block1Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3Row_5_ok :
    tttLargeFiber8Block1Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3Row_6_ok :
    tttLargeFiber8Block1Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3Row_7_ok :
    tttLargeFiber8Block1Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3Row_8_ok :
    tttLargeFiber8Block1Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3Row_9_ok :
    tttLargeFiber8Block1Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3Row_10_ok :
    tttLargeFiber8Block1Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3Row_11_ok :
    tttLargeFiber8Block1Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3Row_12_ok :
    tttLargeFiber8Block1Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3Row_13_ok :
    tttLargeFiber8Block1Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3Row_14_ok :
    tttLargeFiber8Block1Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3Row_15_ok :
    tttLargeFiber8Block1Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentMap_0_ok :
    tttLargeFiber8Block1Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentMap_1_ok :
    tttLargeFiber8Block1Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentMap_2_ok :
    tttLargeFiber8Block1Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentMap_3_ok :
    tttLargeFiber8Block1Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentMap_4_ok :
    tttLargeFiber8Block1Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentMap_5_ok :
    tttLargeFiber8Block1Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentMap_6_ok :
    tttLargeFiber8Block1Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentMap_7_ok :
    tttLargeFiber8Block1Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentMap_8_ok :
    tttLargeFiber8Block1Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentMap_9_ok :
    tttLargeFiber8Block1Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentMap_10_ok :
    tttLargeFiber8Block1Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentMap_11_ok :
    tttLargeFiber8Block1Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentMap_12_ok :
    tttLargeFiber8Block1Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentMap_13_ok :
    tttLargeFiber8Block1Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentMap_14_ok :
    tttLargeFiber8Block1Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentMap_15_ok :
    tttLargeFiber8Block1Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentPath_0_ok :
    tttLargeFiber8Block1Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentPath_1_ok :
    tttLargeFiber8Block1Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentPath_2_ok :
    tttLargeFiber8Block1Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentPath_3_ok :
    tttLargeFiber8Block1Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentPath_4_ok :
    tttLargeFiber8Block1Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentPath_5_ok :
    tttLargeFiber8Block1Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentPath_6_ok :
    tttLargeFiber8Block1Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentPath_7_ok :
    tttLargeFiber8Block1Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentPath_8_ok :
    tttLargeFiber8Block1Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentPath_9_ok :
    tttLargeFiber8Block1Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentPath_10_ok :
    tttLargeFiber8Block1Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentPath_11_ok :
    tttLargeFiber8Block1Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentPath_12_ok :
    tttLargeFiber8Block1Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentPath_13_ok :
    tttLargeFiber8Block1Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentPath_14_ok :
    tttLargeFiber8Block1Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber8Block1Chunk3ParentPath_15_ok :
    tttLargeFiber8Block1Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber8Block1Chunk3RowsAudit : Bool :=
  tttLargeFiber8Block1Chunk3RowCheck 0
    && tttLargeFiber8Block1Chunk3RowCheck 1
    && tttLargeFiber8Block1Chunk3RowCheck 2
    && tttLargeFiber8Block1Chunk3RowCheck 3
    && tttLargeFiber8Block1Chunk3RowCheck 4
    && tttLargeFiber8Block1Chunk3RowCheck 5
    && tttLargeFiber8Block1Chunk3RowCheck 6
    && tttLargeFiber8Block1Chunk3RowCheck 7
    && tttLargeFiber8Block1Chunk3RowCheck 8
    && tttLargeFiber8Block1Chunk3RowCheck 9
    && tttLargeFiber8Block1Chunk3RowCheck 10
    && tttLargeFiber8Block1Chunk3RowCheck 11
    && tttLargeFiber8Block1Chunk3RowCheck 12
    && tttLargeFiber8Block1Chunk3RowCheck 13
    && tttLargeFiber8Block1Chunk3RowCheck 14
    && tttLargeFiber8Block1Chunk3RowCheck 15

theorem tttLargeFiber8Block1Chunk3RowsAudit_ok :
    tttLargeFiber8Block1Chunk3RowsAudit = true := by
  simp [tttLargeFiber8Block1Chunk3RowsAudit,
    tttLargeFiber8Block1Chunk3Row_0_ok,
    tttLargeFiber8Block1Chunk3Row_1_ok,
    tttLargeFiber8Block1Chunk3Row_2_ok,
    tttLargeFiber8Block1Chunk3Row_3_ok,
    tttLargeFiber8Block1Chunk3Row_4_ok,
    tttLargeFiber8Block1Chunk3Row_5_ok,
    tttLargeFiber8Block1Chunk3Row_6_ok,
    tttLargeFiber8Block1Chunk3Row_7_ok,
    tttLargeFiber8Block1Chunk3Row_8_ok,
    tttLargeFiber8Block1Chunk3Row_9_ok,
    tttLargeFiber8Block1Chunk3Row_10_ok,
    tttLargeFiber8Block1Chunk3Row_11_ok,
    tttLargeFiber8Block1Chunk3Row_12_ok,
    tttLargeFiber8Block1Chunk3Row_13_ok,
    tttLargeFiber8Block1Chunk3Row_14_ok,
    tttLargeFiber8Block1Chunk3Row_15_ok]

def tttLargeFiber8Block1Chunk3ParentMapAudit : Bool :=
  tttLargeFiber8Block1Chunk3ParentMapCheck 0
    && tttLargeFiber8Block1Chunk3ParentMapCheck 1
    && tttLargeFiber8Block1Chunk3ParentMapCheck 2
    && tttLargeFiber8Block1Chunk3ParentMapCheck 3
    && tttLargeFiber8Block1Chunk3ParentMapCheck 4
    && tttLargeFiber8Block1Chunk3ParentMapCheck 5
    && tttLargeFiber8Block1Chunk3ParentMapCheck 6
    && tttLargeFiber8Block1Chunk3ParentMapCheck 7
    && tttLargeFiber8Block1Chunk3ParentMapCheck 8
    && tttLargeFiber8Block1Chunk3ParentMapCheck 9
    && tttLargeFiber8Block1Chunk3ParentMapCheck 10
    && tttLargeFiber8Block1Chunk3ParentMapCheck 11
    && tttLargeFiber8Block1Chunk3ParentMapCheck 12
    && tttLargeFiber8Block1Chunk3ParentMapCheck 13
    && tttLargeFiber8Block1Chunk3ParentMapCheck 14
    && tttLargeFiber8Block1Chunk3ParentMapCheck 15

theorem tttLargeFiber8Block1Chunk3ParentMapAudit_ok :
    tttLargeFiber8Block1Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber8Block1Chunk3ParentMapAudit,
    tttLargeFiber8Block1Chunk3ParentMap_0_ok,
    tttLargeFiber8Block1Chunk3ParentMap_1_ok,
    tttLargeFiber8Block1Chunk3ParentMap_2_ok,
    tttLargeFiber8Block1Chunk3ParentMap_3_ok,
    tttLargeFiber8Block1Chunk3ParentMap_4_ok,
    tttLargeFiber8Block1Chunk3ParentMap_5_ok,
    tttLargeFiber8Block1Chunk3ParentMap_6_ok,
    tttLargeFiber8Block1Chunk3ParentMap_7_ok,
    tttLargeFiber8Block1Chunk3ParentMap_8_ok,
    tttLargeFiber8Block1Chunk3ParentMap_9_ok,
    tttLargeFiber8Block1Chunk3ParentMap_10_ok,
    tttLargeFiber8Block1Chunk3ParentMap_11_ok,
    tttLargeFiber8Block1Chunk3ParentMap_12_ok,
    tttLargeFiber8Block1Chunk3ParentMap_13_ok,
    tttLargeFiber8Block1Chunk3ParentMap_14_ok,
    tttLargeFiber8Block1Chunk3ParentMap_15_ok]

def tttLargeFiber8Block1Chunk3ParentsAudit : Bool :=
  tttLargeFiber8Block1Chunk3ParentPathCheck 0
    && tttLargeFiber8Block1Chunk3ParentPathCheck 1
    && tttLargeFiber8Block1Chunk3ParentPathCheck 2
    && tttLargeFiber8Block1Chunk3ParentPathCheck 3
    && tttLargeFiber8Block1Chunk3ParentPathCheck 4
    && tttLargeFiber8Block1Chunk3ParentPathCheck 5
    && tttLargeFiber8Block1Chunk3ParentPathCheck 6
    && tttLargeFiber8Block1Chunk3ParentPathCheck 7
    && tttLargeFiber8Block1Chunk3ParentPathCheck 8
    && tttLargeFiber8Block1Chunk3ParentPathCheck 9
    && tttLargeFiber8Block1Chunk3ParentPathCheck 10
    && tttLargeFiber8Block1Chunk3ParentPathCheck 11
    && tttLargeFiber8Block1Chunk3ParentPathCheck 12
    && tttLargeFiber8Block1Chunk3ParentPathCheck 13
    && tttLargeFiber8Block1Chunk3ParentPathCheck 14
    && tttLargeFiber8Block1Chunk3ParentPathCheck 15

theorem tttLargeFiber8Block1Chunk3ParentsAudit_ok :
    tttLargeFiber8Block1Chunk3ParentsAudit = true := by
  simp [tttLargeFiber8Block1Chunk3ParentsAudit,
    tttLargeFiber8Block1Chunk3ParentPath_0_ok,
    tttLargeFiber8Block1Chunk3ParentPath_1_ok,
    tttLargeFiber8Block1Chunk3ParentPath_2_ok,
    tttLargeFiber8Block1Chunk3ParentPath_3_ok,
    tttLargeFiber8Block1Chunk3ParentPath_4_ok,
    tttLargeFiber8Block1Chunk3ParentPath_5_ok,
    tttLargeFiber8Block1Chunk3ParentPath_6_ok,
    tttLargeFiber8Block1Chunk3ParentPath_7_ok,
    tttLargeFiber8Block1Chunk3ParentPath_8_ok,
    tttLargeFiber8Block1Chunk3ParentPath_9_ok,
    tttLargeFiber8Block1Chunk3ParentPath_10_ok,
    tttLargeFiber8Block1Chunk3ParentPath_11_ok,
    tttLargeFiber8Block1Chunk3ParentPath_12_ok,
    tttLargeFiber8Block1Chunk3ParentPath_13_ok,
    tttLargeFiber8Block1Chunk3ParentPath_14_ok,
    tttLargeFiber8Block1Chunk3ParentPath_15_ok]

def tttLargeFiber8Block1Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber8CountsAudit &&
    tttLargeFiber8Block1Chunk3SourcesCheck &&
    tttLargeFiber8Block1Chunk3RowsAudit &&
    tttLargeFiber8Block1Chunk3ParentMapAudit &&
    tttLargeFiber8Block1Chunk3ParentsAudit

theorem tttLargeFiber8Block1Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber8Block1Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber8Block1Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber8CountsAudit_ok,
    tttLargeFiber8Block1Chunk3SourcesCheck_ok,
    tttLargeFiber8Block1Chunk3RowsAudit_ok,
    tttLargeFiber8Block1Chunk3ParentMapAudit_ok,
    tttLargeFiber8Block1Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber8Block1Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
