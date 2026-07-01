import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 8, block 2 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber8Block2Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Data

def tttLargeFiber8Block2Chunk1Sources : List Nat :=
  [   4512, 4513, 4514, 4515, 4516, 4517, 4518, 4519,
   4520, 4521, 4522, 4523, 4524, 4525, 4526, 4527]

def tttLargeFiber8Row144 : TripleComponentParentRow :=
  tripleRow 4512 4516 134 2 16 134 2 32
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row145 : TripleComponentParentRow :=
  tripleRow 4513 4517 134 2 17 134 2 33
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row146 : TripleComponentParentRow :=
  tripleRow 4514 4468 134 2 18 133 172 180
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row147 : TripleComponentParentRow :=
  tripleRow 4515 4469 134 2 19 133 172 181
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row148 : TripleComponentParentRow :=
  tripleRow 4516 4464 134 2 32 133 172 132
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row149 : TripleComponentParentRow :=
  tripleRow 4517 4465 134 2 33 133 172 133
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row150 : TripleComponentParentRow :=
  tripleRow 4518 4466 134 2 34 133 172 134
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row151 : TripleComponentParentRow :=
  tripleRow 4519 4467 134 2 35 133 172 135
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row152 : TripleComponentParentRow :=
  tripleRow 4520 4524 134 3 24 134 3 40
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row153 : TripleComponentParentRow :=
  tripleRow 4521 4525 134 3 25 134 3 41
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row154 : TripleComponentParentRow :=
  tripleRow 4522 4476 134 3 26 133 173 188
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row155 : TripleComponentParentRow :=
  tripleRow 4523 4477 134 3 27 133 173 189
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row156 : TripleComponentParentRow :=
  tripleRow 4524 4472 134 3 40 133 173 140
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row157 : TripleComponentParentRow :=
  tripleRow 4525 4473 134 3 41 133 173 141
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row158 : TripleComponentParentRow :=
  tripleRow 4526 4474 134 3 42 133 173 142
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row159 : TripleComponentParentRow :=
  tripleRow 4527 4475 134 3 43 133 173 143
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Block2Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber8Row144
  , tttLargeFiber8Row145
  , tttLargeFiber8Row146
  , tttLargeFiber8Row147
  , tttLargeFiber8Row148
  , tttLargeFiber8Row149
  , tttLargeFiber8Row150
  , tttLargeFiber8Row151
  , tttLargeFiber8Row152
  , tttLargeFiber8Row153
  , tttLargeFiber8Row154
  , tttLargeFiber8Row155
  , tttLargeFiber8Row156
  , tttLargeFiber8Row157
  , tttLargeFiber8Row158
  , tttLargeFiber8Row159
  ]

def tttLargeFiber8Block2Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (4368 <= i) && decide (i < 4624)) ||
    (decide (6000 <= i) && decide (i < 6256))

def tttLargeFiber8Block2Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber8Block2Chunk1ExpectedContains row.source &&
    tttLargeFiber8Block2Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber8Key &&
          chainInputKey tttWord t == tttLargeFiber8Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber8Block2Chunk1SourcesCheck : Bool :=
  (tttLargeFiber8Block2Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber8Block2Chunk1Sources

theorem tttLargeFiber8Block2Chunk1SourcesCheck_ok :
    tttLargeFiber8Block2Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber8Block2Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber8Block2Chunk1RowValid
    (listGetD tttLargeFiber8Block2Chunk1Rows i default)

def tttLargeFiber8Block2Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber8Block2Chunk1Rows i default
  row.parent == tttLargeFiber8ParentOf row.source

def tttLargeFiber8Block2Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber8Block2Chunk1Sources 0 0 == 4512
      && tttLargeFiber8ParentOf 4512 == 4516
      && tttLargeFiber8ParentOf 4516 == 4464
      && tttLargeFiber8ParentOf 4464 == 4400
      && tttLargeFiber8ParentOf 4400 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 1 => listGetD tttLargeFiber8Block2Chunk1Sources 1 0 == 4513
      && tttLargeFiber8ParentOf 4513 == 4517
      && tttLargeFiber8ParentOf 4517 == 4465
      && tttLargeFiber8ParentOf 4465 == 4401
      && tttLargeFiber8ParentOf 4401 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 2 => listGetD tttLargeFiber8Block2Chunk1Sources 2 0 == 4514
      && tttLargeFiber8ParentOf 4514 == 4468
      && tttLargeFiber8ParentOf 4468 == 4404
      && tttLargeFiber8ParentOf 4404 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 3 => listGetD tttLargeFiber8Block2Chunk1Sources 3 0 == 4515
      && tttLargeFiber8ParentOf 4515 == 4469
      && tttLargeFiber8ParentOf 4469 == 4405
      && tttLargeFiber8ParentOf 4405 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 4 => listGetD tttLargeFiber8Block2Chunk1Sources 4 0 == 4516
      && tttLargeFiber8ParentOf 4516 == 4464
      && tttLargeFiber8ParentOf 4464 == 4400
      && tttLargeFiber8ParentOf 4400 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 5 => listGetD tttLargeFiber8Block2Chunk1Sources 5 0 == 4517
      && tttLargeFiber8ParentOf 4517 == 4465
      && tttLargeFiber8ParentOf 4465 == 4401
      && tttLargeFiber8ParentOf 4401 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 6 => listGetD tttLargeFiber8Block2Chunk1Sources 6 0 == 4518
      && tttLargeFiber8ParentOf 4518 == 4466
      && tttLargeFiber8ParentOf 4466 == 4402
      && tttLargeFiber8ParentOf 4402 == 4370
      && tttLargeFiber8ParentOf 4370 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 7 => listGetD tttLargeFiber8Block2Chunk1Sources 7 0 == 4519
      && tttLargeFiber8ParentOf 4519 == 4467
      && tttLargeFiber8ParentOf 4467 == 4403
      && tttLargeFiber8ParentOf 4403 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 8 => listGetD tttLargeFiber8Block2Chunk1Sources 8 0 == 4520
      && tttLargeFiber8ParentOf 4520 == 4524
      && tttLargeFiber8ParentOf 4524 == 4472
      && tttLargeFiber8ParentOf 4472 == 4408
      && tttLargeFiber8ParentOf 4408 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 9 => listGetD tttLargeFiber8Block2Chunk1Sources 9 0 == 4521
      && tttLargeFiber8ParentOf 4521 == 4525
      && tttLargeFiber8ParentOf 4525 == 4473
      && tttLargeFiber8ParentOf 4473 == 4409
      && tttLargeFiber8ParentOf 4409 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (6 <= tttLargeFiber8MaxParentDepth)
  | 10 => listGetD tttLargeFiber8Block2Chunk1Sources 10 0 == 4522
      && tttLargeFiber8ParentOf 4522 == 4476
      && tttLargeFiber8ParentOf 4476 == 4412
      && tttLargeFiber8ParentOf 4412 == 4380
      && tttLargeFiber8ParentOf 4380 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 11 => listGetD tttLargeFiber8Block2Chunk1Sources 11 0 == 4523
      && tttLargeFiber8ParentOf 4523 == 4477
      && tttLargeFiber8ParentOf 4477 == 4413
      && tttLargeFiber8ParentOf 4413 == 4381
      && tttLargeFiber8ParentOf 4381 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (6 <= tttLargeFiber8MaxParentDepth)
  | 12 => listGetD tttLargeFiber8Block2Chunk1Sources 12 0 == 4524
      && tttLargeFiber8ParentOf 4524 == 4472
      && tttLargeFiber8ParentOf 4472 == 4408
      && tttLargeFiber8ParentOf 4408 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 13 => listGetD tttLargeFiber8Block2Chunk1Sources 13 0 == 4525
      && tttLargeFiber8ParentOf 4525 == 4473
      && tttLargeFiber8ParentOf 4473 == 4409
      && tttLargeFiber8ParentOf 4409 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 14 => listGetD tttLargeFiber8Block2Chunk1Sources 14 0 == 4526
      && tttLargeFiber8ParentOf 4526 == 4474
      && tttLargeFiber8ParentOf 4474 == 4410
      && tttLargeFiber8ParentOf 4410 == 4378
      && tttLargeFiber8ParentOf 4378 == 4370
      && tttLargeFiber8ParentOf 4370 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (6 <= tttLargeFiber8MaxParentDepth)
  | 15 => listGetD tttLargeFiber8Block2Chunk1Sources 15 0 == 4527
      && tttLargeFiber8ParentOf 4527 == 4475
      && tttLargeFiber8ParentOf 4475 == 4411
      && tttLargeFiber8ParentOf 4411 == 4379
      && tttLargeFiber8ParentOf 4379 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | _ => false

theorem tttLargeFiber8Block2Chunk1Row_0_ok :
    tttLargeFiber8Block2Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1Row_1_ok :
    tttLargeFiber8Block2Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1Row_2_ok :
    tttLargeFiber8Block2Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1Row_3_ok :
    tttLargeFiber8Block2Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1Row_4_ok :
    tttLargeFiber8Block2Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1Row_5_ok :
    tttLargeFiber8Block2Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1Row_6_ok :
    tttLargeFiber8Block2Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1Row_7_ok :
    tttLargeFiber8Block2Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1Row_8_ok :
    tttLargeFiber8Block2Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1Row_9_ok :
    tttLargeFiber8Block2Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1Row_10_ok :
    tttLargeFiber8Block2Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1Row_11_ok :
    tttLargeFiber8Block2Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1Row_12_ok :
    tttLargeFiber8Block2Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1Row_13_ok :
    tttLargeFiber8Block2Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1Row_14_ok :
    tttLargeFiber8Block2Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1Row_15_ok :
    tttLargeFiber8Block2Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentMap_0_ok :
    tttLargeFiber8Block2Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentMap_1_ok :
    tttLargeFiber8Block2Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentMap_2_ok :
    tttLargeFiber8Block2Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentMap_3_ok :
    tttLargeFiber8Block2Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentMap_4_ok :
    tttLargeFiber8Block2Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentMap_5_ok :
    tttLargeFiber8Block2Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentMap_6_ok :
    tttLargeFiber8Block2Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentMap_7_ok :
    tttLargeFiber8Block2Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentMap_8_ok :
    tttLargeFiber8Block2Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentMap_9_ok :
    tttLargeFiber8Block2Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentMap_10_ok :
    tttLargeFiber8Block2Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentMap_11_ok :
    tttLargeFiber8Block2Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentMap_12_ok :
    tttLargeFiber8Block2Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentMap_13_ok :
    tttLargeFiber8Block2Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentMap_14_ok :
    tttLargeFiber8Block2Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentMap_15_ok :
    tttLargeFiber8Block2Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentPath_0_ok :
    tttLargeFiber8Block2Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentPath_1_ok :
    tttLargeFiber8Block2Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentPath_2_ok :
    tttLargeFiber8Block2Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentPath_3_ok :
    tttLargeFiber8Block2Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentPath_4_ok :
    tttLargeFiber8Block2Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentPath_5_ok :
    tttLargeFiber8Block2Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentPath_6_ok :
    tttLargeFiber8Block2Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentPath_7_ok :
    tttLargeFiber8Block2Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentPath_8_ok :
    tttLargeFiber8Block2Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentPath_9_ok :
    tttLargeFiber8Block2Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentPath_10_ok :
    tttLargeFiber8Block2Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentPath_11_ok :
    tttLargeFiber8Block2Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentPath_12_ok :
    tttLargeFiber8Block2Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentPath_13_ok :
    tttLargeFiber8Block2Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentPath_14_ok :
    tttLargeFiber8Block2Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber8Block2Chunk1ParentPath_15_ok :
    tttLargeFiber8Block2Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber8Block2Chunk1RowsAudit : Bool :=
  tttLargeFiber8Block2Chunk1RowCheck 0
    && tttLargeFiber8Block2Chunk1RowCheck 1
    && tttLargeFiber8Block2Chunk1RowCheck 2
    && tttLargeFiber8Block2Chunk1RowCheck 3
    && tttLargeFiber8Block2Chunk1RowCheck 4
    && tttLargeFiber8Block2Chunk1RowCheck 5
    && tttLargeFiber8Block2Chunk1RowCheck 6
    && tttLargeFiber8Block2Chunk1RowCheck 7
    && tttLargeFiber8Block2Chunk1RowCheck 8
    && tttLargeFiber8Block2Chunk1RowCheck 9
    && tttLargeFiber8Block2Chunk1RowCheck 10
    && tttLargeFiber8Block2Chunk1RowCheck 11
    && tttLargeFiber8Block2Chunk1RowCheck 12
    && tttLargeFiber8Block2Chunk1RowCheck 13
    && tttLargeFiber8Block2Chunk1RowCheck 14
    && tttLargeFiber8Block2Chunk1RowCheck 15

theorem tttLargeFiber8Block2Chunk1RowsAudit_ok :
    tttLargeFiber8Block2Chunk1RowsAudit = true := by
  simp [tttLargeFiber8Block2Chunk1RowsAudit,
    tttLargeFiber8Block2Chunk1Row_0_ok,
    tttLargeFiber8Block2Chunk1Row_1_ok,
    tttLargeFiber8Block2Chunk1Row_2_ok,
    tttLargeFiber8Block2Chunk1Row_3_ok,
    tttLargeFiber8Block2Chunk1Row_4_ok,
    tttLargeFiber8Block2Chunk1Row_5_ok,
    tttLargeFiber8Block2Chunk1Row_6_ok,
    tttLargeFiber8Block2Chunk1Row_7_ok,
    tttLargeFiber8Block2Chunk1Row_8_ok,
    tttLargeFiber8Block2Chunk1Row_9_ok,
    tttLargeFiber8Block2Chunk1Row_10_ok,
    tttLargeFiber8Block2Chunk1Row_11_ok,
    tttLargeFiber8Block2Chunk1Row_12_ok,
    tttLargeFiber8Block2Chunk1Row_13_ok,
    tttLargeFiber8Block2Chunk1Row_14_ok,
    tttLargeFiber8Block2Chunk1Row_15_ok]

def tttLargeFiber8Block2Chunk1ParentMapAudit : Bool :=
  tttLargeFiber8Block2Chunk1ParentMapCheck 0
    && tttLargeFiber8Block2Chunk1ParentMapCheck 1
    && tttLargeFiber8Block2Chunk1ParentMapCheck 2
    && tttLargeFiber8Block2Chunk1ParentMapCheck 3
    && tttLargeFiber8Block2Chunk1ParentMapCheck 4
    && tttLargeFiber8Block2Chunk1ParentMapCheck 5
    && tttLargeFiber8Block2Chunk1ParentMapCheck 6
    && tttLargeFiber8Block2Chunk1ParentMapCheck 7
    && tttLargeFiber8Block2Chunk1ParentMapCheck 8
    && tttLargeFiber8Block2Chunk1ParentMapCheck 9
    && tttLargeFiber8Block2Chunk1ParentMapCheck 10
    && tttLargeFiber8Block2Chunk1ParentMapCheck 11
    && tttLargeFiber8Block2Chunk1ParentMapCheck 12
    && tttLargeFiber8Block2Chunk1ParentMapCheck 13
    && tttLargeFiber8Block2Chunk1ParentMapCheck 14
    && tttLargeFiber8Block2Chunk1ParentMapCheck 15

theorem tttLargeFiber8Block2Chunk1ParentMapAudit_ok :
    tttLargeFiber8Block2Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber8Block2Chunk1ParentMapAudit,
    tttLargeFiber8Block2Chunk1ParentMap_0_ok,
    tttLargeFiber8Block2Chunk1ParentMap_1_ok,
    tttLargeFiber8Block2Chunk1ParentMap_2_ok,
    tttLargeFiber8Block2Chunk1ParentMap_3_ok,
    tttLargeFiber8Block2Chunk1ParentMap_4_ok,
    tttLargeFiber8Block2Chunk1ParentMap_5_ok,
    tttLargeFiber8Block2Chunk1ParentMap_6_ok,
    tttLargeFiber8Block2Chunk1ParentMap_7_ok,
    tttLargeFiber8Block2Chunk1ParentMap_8_ok,
    tttLargeFiber8Block2Chunk1ParentMap_9_ok,
    tttLargeFiber8Block2Chunk1ParentMap_10_ok,
    tttLargeFiber8Block2Chunk1ParentMap_11_ok,
    tttLargeFiber8Block2Chunk1ParentMap_12_ok,
    tttLargeFiber8Block2Chunk1ParentMap_13_ok,
    tttLargeFiber8Block2Chunk1ParentMap_14_ok,
    tttLargeFiber8Block2Chunk1ParentMap_15_ok]

def tttLargeFiber8Block2Chunk1ParentsAudit : Bool :=
  tttLargeFiber8Block2Chunk1ParentPathCheck 0
    && tttLargeFiber8Block2Chunk1ParentPathCheck 1
    && tttLargeFiber8Block2Chunk1ParentPathCheck 2
    && tttLargeFiber8Block2Chunk1ParentPathCheck 3
    && tttLargeFiber8Block2Chunk1ParentPathCheck 4
    && tttLargeFiber8Block2Chunk1ParentPathCheck 5
    && tttLargeFiber8Block2Chunk1ParentPathCheck 6
    && tttLargeFiber8Block2Chunk1ParentPathCheck 7
    && tttLargeFiber8Block2Chunk1ParentPathCheck 8
    && tttLargeFiber8Block2Chunk1ParentPathCheck 9
    && tttLargeFiber8Block2Chunk1ParentPathCheck 10
    && tttLargeFiber8Block2Chunk1ParentPathCheck 11
    && tttLargeFiber8Block2Chunk1ParentPathCheck 12
    && tttLargeFiber8Block2Chunk1ParentPathCheck 13
    && tttLargeFiber8Block2Chunk1ParentPathCheck 14
    && tttLargeFiber8Block2Chunk1ParentPathCheck 15

theorem tttLargeFiber8Block2Chunk1ParentsAudit_ok :
    tttLargeFiber8Block2Chunk1ParentsAudit = true := by
  simp [tttLargeFiber8Block2Chunk1ParentsAudit,
    tttLargeFiber8Block2Chunk1ParentPath_0_ok,
    tttLargeFiber8Block2Chunk1ParentPath_1_ok,
    tttLargeFiber8Block2Chunk1ParentPath_2_ok,
    tttLargeFiber8Block2Chunk1ParentPath_3_ok,
    tttLargeFiber8Block2Chunk1ParentPath_4_ok,
    tttLargeFiber8Block2Chunk1ParentPath_5_ok,
    tttLargeFiber8Block2Chunk1ParentPath_6_ok,
    tttLargeFiber8Block2Chunk1ParentPath_7_ok,
    tttLargeFiber8Block2Chunk1ParentPath_8_ok,
    tttLargeFiber8Block2Chunk1ParentPath_9_ok,
    tttLargeFiber8Block2Chunk1ParentPath_10_ok,
    tttLargeFiber8Block2Chunk1ParentPath_11_ok,
    tttLargeFiber8Block2Chunk1ParentPath_12_ok,
    tttLargeFiber8Block2Chunk1ParentPath_13_ok,
    tttLargeFiber8Block2Chunk1ParentPath_14_ok,
    tttLargeFiber8Block2Chunk1ParentPath_15_ok]

def tttLargeFiber8Block2Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber8CountsAudit &&
    tttLargeFiber8Block2Chunk1SourcesCheck &&
    tttLargeFiber8Block2Chunk1RowsAudit &&
    tttLargeFiber8Block2Chunk1ParentMapAudit &&
    tttLargeFiber8Block2Chunk1ParentsAudit

theorem tttLargeFiber8Block2Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber8Block2Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber8Block2Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber8CountsAudit_ok,
    tttLargeFiber8Block2Chunk1SourcesCheck_ok,
    tttLargeFiber8Block2Chunk1RowsAudit_ok,
    tttLargeFiber8Block2Chunk1ParentMapAudit_ok,
    tttLargeFiber8Block2Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber8Block2Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
