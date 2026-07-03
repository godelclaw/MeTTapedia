import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 8, block 1 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber8Block1Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Data

def tttLargeFiber8Block1Chunk1Sources : List Nat :=
  [   4448, 4449, 4450, 4451, 4452, 4453, 4454, 4455,
   4456, 4457, 4458, 4459, 4460, 4461, 4462, 4463]

def tttLargeFiber8Row80 : TripleComponentParentRow :=
  tripleRow 4448 4384 133 158 0 132 150 0
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row81 : TripleComponentParentRow :=
  tripleRow 4449 4385 133 158 1 132 150 1
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row82 : TripleComponentParentRow :=
  tripleRow 4450 4386 133 158 2 132 150 2
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row83 : TripleComponentParentRow :=
  tripleRow 4451 4387 133 158 3 132 150 3
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row84 : TripleComponentParentRow :=
  tripleRow 4452 4388 133 158 48 132 150 48
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row85 : TripleComponentParentRow :=
  tripleRow 4453 4389 133 158 49 132 150 49
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row86 : TripleComponentParentRow :=
  tripleRow 4454 4390 133 158 50 132 150 50
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row87 : TripleComponentParentRow :=
  tripleRow 4455 4391 133 158 51 132 150 51
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row88 : TripleComponentParentRow :=
  tripleRow 4456 4392 133 159 8 132 151 8
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row89 : TripleComponentParentRow :=
  tripleRow 4457 4393 133 159 9 132 151 9
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row90 : TripleComponentParentRow :=
  tripleRow 4458 4394 133 159 10 132 151 10
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row91 : TripleComponentParentRow :=
  tripleRow 4459 4395 133 159 11 132 151 11
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row92 : TripleComponentParentRow :=
  tripleRow 4460 4396 133 159 56 132 151 56
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row93 : TripleComponentParentRow :=
  tripleRow 4461 4397 133 159 57 132 151 57
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row94 : TripleComponentParentRow :=
  tripleRow 4462 4398 133 159 58 132 151 58
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row95 : TripleComponentParentRow :=
  tripleRow 4463 4399 133 159 59 132 151 59
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Block1Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber8Row80
  , tttLargeFiber8Row81
  , tttLargeFiber8Row82
  , tttLargeFiber8Row83
  , tttLargeFiber8Row84
  , tttLargeFiber8Row85
  , tttLargeFiber8Row86
  , tttLargeFiber8Row87
  , tttLargeFiber8Row88
  , tttLargeFiber8Row89
  , tttLargeFiber8Row90
  , tttLargeFiber8Row91
  , tttLargeFiber8Row92
  , tttLargeFiber8Row93
  , tttLargeFiber8Row94
  , tttLargeFiber8Row95
  ]

def tttLargeFiber8Block1Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (4368 <= i) && decide (i < 4624)) ||
    (decide (6000 <= i) && decide (i < 6256))

def tttLargeFiber8Block1Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber8Block1Chunk1ExpectedContains row.source &&
    tttLargeFiber8Block1Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber8Key &&
          chainInputKey tttWord t == tttLargeFiber8Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber8Block1Chunk1SourcesCheck : Bool :=
  (tttLargeFiber8Block1Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber8Block1Chunk1Sources

theorem tttLargeFiber8Block1Chunk1SourcesCheck_ok :
    tttLargeFiber8Block1Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber8Block1Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber8Block1Chunk1RowValid
    (listGetD tttLargeFiber8Block1Chunk1Rows i default)

def tttLargeFiber8Block1Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber8Block1Chunk1Rows i default
  row.parent == tttLargeFiber8ParentOf row.source

def tttLargeFiber8Block1Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber8Block1Chunk1Sources 0 0 == 4448
      && tttLargeFiber8ParentOf 4448 == 4384
      && tttLargeFiber8ParentOf 4384 == 4388
      && tttLargeFiber8ParentOf 4388 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 1 => listGetD tttLargeFiber8Block1Chunk1Sources 1 0 == 4449
      && tttLargeFiber8ParentOf 4449 == 4385
      && tttLargeFiber8ParentOf 4385 == 4389
      && tttLargeFiber8ParentOf 4389 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 2 => listGetD tttLargeFiber8Block1Chunk1Sources 2 0 == 4450
      && tttLargeFiber8ParentOf 4450 == 4386
      && tttLargeFiber8ParentOf 4386 == 4380
      && tttLargeFiber8ParentOf 4380 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 3 => listGetD tttLargeFiber8Block1Chunk1Sources 3 0 == 4451
      && tttLargeFiber8ParentOf 4451 == 4387
      && tttLargeFiber8ParentOf 4387 == 4381
      && tttLargeFiber8ParentOf 4381 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 4 => listGetD tttLargeFiber8Block1Chunk1Sources 4 0 == 4452
      && tttLargeFiber8ParentOf 4452 == 4388
      && tttLargeFiber8ParentOf 4388 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 5 => listGetD tttLargeFiber8Block1Chunk1Sources 5 0 == 4453
      && tttLargeFiber8ParentOf 4453 == 4389
      && tttLargeFiber8ParentOf 4389 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 6 => listGetD tttLargeFiber8Block1Chunk1Sources 6 0 == 4454
      && tttLargeFiber8ParentOf 4454 == 4390
      && tttLargeFiber8ParentOf 4390 == 4378
      && tttLargeFiber8ParentOf 4378 == 4370
      && tttLargeFiber8ParentOf 4370 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 7 => listGetD tttLargeFiber8Block1Chunk1Sources 7 0 == 4455
      && tttLargeFiber8ParentOf 4455 == 4391
      && tttLargeFiber8ParentOf 4391 == 4379
      && tttLargeFiber8ParentOf 4379 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 8 => listGetD tttLargeFiber8Block1Chunk1Sources 8 0 == 4456
      && tttLargeFiber8ParentOf 4456 == 4392
      && tttLargeFiber8ParentOf 4392 == 4396
      && tttLargeFiber8ParentOf 4396 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 9 => listGetD tttLargeFiber8Block1Chunk1Sources 9 0 == 4457
      && tttLargeFiber8ParentOf 4457 == 4393
      && tttLargeFiber8ParentOf 4393 == 4397
      && tttLargeFiber8ParentOf 4397 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 10 => listGetD tttLargeFiber8Block1Chunk1Sources 10 0 == 4458
      && tttLargeFiber8ParentOf 4458 == 4394
      && tttLargeFiber8ParentOf 4394 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 11 => listGetD tttLargeFiber8Block1Chunk1Sources 11 0 == 4459
      && tttLargeFiber8ParentOf 4459 == 4395
      && tttLargeFiber8ParentOf 4395 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 12 => listGetD tttLargeFiber8Block1Chunk1Sources 12 0 == 4460
      && tttLargeFiber8ParentOf 4460 == 4396
      && tttLargeFiber8ParentOf 4396 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (2 <= tttLargeFiber8MaxParentDepth)
  | 13 => listGetD tttLargeFiber8Block1Chunk1Sources 13 0 == 4461
      && tttLargeFiber8ParentOf 4461 == 4397
      && tttLargeFiber8ParentOf 4397 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 14 => listGetD tttLargeFiber8Block1Chunk1Sources 14 0 == 4462
      && tttLargeFiber8ParentOf 4462 == 4398
      && tttLargeFiber8ParentOf 4398 == 4370
      && tttLargeFiber8ParentOf 4370 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 15 => listGetD tttLargeFiber8Block1Chunk1Sources 15 0 == 4463
      && tttLargeFiber8ParentOf 4463 == 4399
      && tttLargeFiber8ParentOf 4399 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | _ => false

theorem tttLargeFiber8Block1Chunk1Row_0_ok :
    tttLargeFiber8Block1Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1Row_1_ok :
    tttLargeFiber8Block1Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1Row_2_ok :
    tttLargeFiber8Block1Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1Row_3_ok :
    tttLargeFiber8Block1Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1Row_4_ok :
    tttLargeFiber8Block1Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1Row_5_ok :
    tttLargeFiber8Block1Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1Row_6_ok :
    tttLargeFiber8Block1Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1Row_7_ok :
    tttLargeFiber8Block1Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1Row_8_ok :
    tttLargeFiber8Block1Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1Row_9_ok :
    tttLargeFiber8Block1Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1Row_10_ok :
    tttLargeFiber8Block1Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1Row_11_ok :
    tttLargeFiber8Block1Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1Row_12_ok :
    tttLargeFiber8Block1Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1Row_13_ok :
    tttLargeFiber8Block1Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1Row_14_ok :
    tttLargeFiber8Block1Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1Row_15_ok :
    tttLargeFiber8Block1Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentMap_0_ok :
    tttLargeFiber8Block1Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentMap_1_ok :
    tttLargeFiber8Block1Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentMap_2_ok :
    tttLargeFiber8Block1Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentMap_3_ok :
    tttLargeFiber8Block1Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentMap_4_ok :
    tttLargeFiber8Block1Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentMap_5_ok :
    tttLargeFiber8Block1Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentMap_6_ok :
    tttLargeFiber8Block1Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentMap_7_ok :
    tttLargeFiber8Block1Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentMap_8_ok :
    tttLargeFiber8Block1Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentMap_9_ok :
    tttLargeFiber8Block1Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentMap_10_ok :
    tttLargeFiber8Block1Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentMap_11_ok :
    tttLargeFiber8Block1Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentMap_12_ok :
    tttLargeFiber8Block1Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentMap_13_ok :
    tttLargeFiber8Block1Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentMap_14_ok :
    tttLargeFiber8Block1Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentMap_15_ok :
    tttLargeFiber8Block1Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentPath_0_ok :
    tttLargeFiber8Block1Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentPath_1_ok :
    tttLargeFiber8Block1Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentPath_2_ok :
    tttLargeFiber8Block1Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentPath_3_ok :
    tttLargeFiber8Block1Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentPath_4_ok :
    tttLargeFiber8Block1Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentPath_5_ok :
    tttLargeFiber8Block1Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentPath_6_ok :
    tttLargeFiber8Block1Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentPath_7_ok :
    tttLargeFiber8Block1Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentPath_8_ok :
    tttLargeFiber8Block1Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentPath_9_ok :
    tttLargeFiber8Block1Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentPath_10_ok :
    tttLargeFiber8Block1Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentPath_11_ok :
    tttLargeFiber8Block1Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentPath_12_ok :
    tttLargeFiber8Block1Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentPath_13_ok :
    tttLargeFiber8Block1Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentPath_14_ok :
    tttLargeFiber8Block1Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber8Block1Chunk1ParentPath_15_ok :
    tttLargeFiber8Block1Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber8Block1Chunk1RowsAudit : Bool :=
  tttLargeFiber8Block1Chunk1RowCheck 0
    && tttLargeFiber8Block1Chunk1RowCheck 1
    && tttLargeFiber8Block1Chunk1RowCheck 2
    && tttLargeFiber8Block1Chunk1RowCheck 3
    && tttLargeFiber8Block1Chunk1RowCheck 4
    && tttLargeFiber8Block1Chunk1RowCheck 5
    && tttLargeFiber8Block1Chunk1RowCheck 6
    && tttLargeFiber8Block1Chunk1RowCheck 7
    && tttLargeFiber8Block1Chunk1RowCheck 8
    && tttLargeFiber8Block1Chunk1RowCheck 9
    && tttLargeFiber8Block1Chunk1RowCheck 10
    && tttLargeFiber8Block1Chunk1RowCheck 11
    && tttLargeFiber8Block1Chunk1RowCheck 12
    && tttLargeFiber8Block1Chunk1RowCheck 13
    && tttLargeFiber8Block1Chunk1RowCheck 14
    && tttLargeFiber8Block1Chunk1RowCheck 15

theorem tttLargeFiber8Block1Chunk1RowsAudit_ok :
    tttLargeFiber8Block1Chunk1RowsAudit = true := by
  simp [tttLargeFiber8Block1Chunk1RowsAudit,
    tttLargeFiber8Block1Chunk1Row_0_ok,
    tttLargeFiber8Block1Chunk1Row_1_ok,
    tttLargeFiber8Block1Chunk1Row_2_ok,
    tttLargeFiber8Block1Chunk1Row_3_ok,
    tttLargeFiber8Block1Chunk1Row_4_ok,
    tttLargeFiber8Block1Chunk1Row_5_ok,
    tttLargeFiber8Block1Chunk1Row_6_ok,
    tttLargeFiber8Block1Chunk1Row_7_ok,
    tttLargeFiber8Block1Chunk1Row_8_ok,
    tttLargeFiber8Block1Chunk1Row_9_ok,
    tttLargeFiber8Block1Chunk1Row_10_ok,
    tttLargeFiber8Block1Chunk1Row_11_ok,
    tttLargeFiber8Block1Chunk1Row_12_ok,
    tttLargeFiber8Block1Chunk1Row_13_ok,
    tttLargeFiber8Block1Chunk1Row_14_ok,
    tttLargeFiber8Block1Chunk1Row_15_ok]

def tttLargeFiber8Block1Chunk1ParentMapAudit : Bool :=
  tttLargeFiber8Block1Chunk1ParentMapCheck 0
    && tttLargeFiber8Block1Chunk1ParentMapCheck 1
    && tttLargeFiber8Block1Chunk1ParentMapCheck 2
    && tttLargeFiber8Block1Chunk1ParentMapCheck 3
    && tttLargeFiber8Block1Chunk1ParentMapCheck 4
    && tttLargeFiber8Block1Chunk1ParentMapCheck 5
    && tttLargeFiber8Block1Chunk1ParentMapCheck 6
    && tttLargeFiber8Block1Chunk1ParentMapCheck 7
    && tttLargeFiber8Block1Chunk1ParentMapCheck 8
    && tttLargeFiber8Block1Chunk1ParentMapCheck 9
    && tttLargeFiber8Block1Chunk1ParentMapCheck 10
    && tttLargeFiber8Block1Chunk1ParentMapCheck 11
    && tttLargeFiber8Block1Chunk1ParentMapCheck 12
    && tttLargeFiber8Block1Chunk1ParentMapCheck 13
    && tttLargeFiber8Block1Chunk1ParentMapCheck 14
    && tttLargeFiber8Block1Chunk1ParentMapCheck 15

theorem tttLargeFiber8Block1Chunk1ParentMapAudit_ok :
    tttLargeFiber8Block1Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber8Block1Chunk1ParentMapAudit,
    tttLargeFiber8Block1Chunk1ParentMap_0_ok,
    tttLargeFiber8Block1Chunk1ParentMap_1_ok,
    tttLargeFiber8Block1Chunk1ParentMap_2_ok,
    tttLargeFiber8Block1Chunk1ParentMap_3_ok,
    tttLargeFiber8Block1Chunk1ParentMap_4_ok,
    tttLargeFiber8Block1Chunk1ParentMap_5_ok,
    tttLargeFiber8Block1Chunk1ParentMap_6_ok,
    tttLargeFiber8Block1Chunk1ParentMap_7_ok,
    tttLargeFiber8Block1Chunk1ParentMap_8_ok,
    tttLargeFiber8Block1Chunk1ParentMap_9_ok,
    tttLargeFiber8Block1Chunk1ParentMap_10_ok,
    tttLargeFiber8Block1Chunk1ParentMap_11_ok,
    tttLargeFiber8Block1Chunk1ParentMap_12_ok,
    tttLargeFiber8Block1Chunk1ParentMap_13_ok,
    tttLargeFiber8Block1Chunk1ParentMap_14_ok,
    tttLargeFiber8Block1Chunk1ParentMap_15_ok]

def tttLargeFiber8Block1Chunk1ParentsAudit : Bool :=
  tttLargeFiber8Block1Chunk1ParentPathCheck 0
    && tttLargeFiber8Block1Chunk1ParentPathCheck 1
    && tttLargeFiber8Block1Chunk1ParentPathCheck 2
    && tttLargeFiber8Block1Chunk1ParentPathCheck 3
    && tttLargeFiber8Block1Chunk1ParentPathCheck 4
    && tttLargeFiber8Block1Chunk1ParentPathCheck 5
    && tttLargeFiber8Block1Chunk1ParentPathCheck 6
    && tttLargeFiber8Block1Chunk1ParentPathCheck 7
    && tttLargeFiber8Block1Chunk1ParentPathCheck 8
    && tttLargeFiber8Block1Chunk1ParentPathCheck 9
    && tttLargeFiber8Block1Chunk1ParentPathCheck 10
    && tttLargeFiber8Block1Chunk1ParentPathCheck 11
    && tttLargeFiber8Block1Chunk1ParentPathCheck 12
    && tttLargeFiber8Block1Chunk1ParentPathCheck 13
    && tttLargeFiber8Block1Chunk1ParentPathCheck 14
    && tttLargeFiber8Block1Chunk1ParentPathCheck 15

theorem tttLargeFiber8Block1Chunk1ParentsAudit_ok :
    tttLargeFiber8Block1Chunk1ParentsAudit = true := by
  simp [tttLargeFiber8Block1Chunk1ParentsAudit,
    tttLargeFiber8Block1Chunk1ParentPath_0_ok,
    tttLargeFiber8Block1Chunk1ParentPath_1_ok,
    tttLargeFiber8Block1Chunk1ParentPath_2_ok,
    tttLargeFiber8Block1Chunk1ParentPath_3_ok,
    tttLargeFiber8Block1Chunk1ParentPath_4_ok,
    tttLargeFiber8Block1Chunk1ParentPath_5_ok,
    tttLargeFiber8Block1Chunk1ParentPath_6_ok,
    tttLargeFiber8Block1Chunk1ParentPath_7_ok,
    tttLargeFiber8Block1Chunk1ParentPath_8_ok,
    tttLargeFiber8Block1Chunk1ParentPath_9_ok,
    tttLargeFiber8Block1Chunk1ParentPath_10_ok,
    tttLargeFiber8Block1Chunk1ParentPath_11_ok,
    tttLargeFiber8Block1Chunk1ParentPath_12_ok,
    tttLargeFiber8Block1Chunk1ParentPath_13_ok,
    tttLargeFiber8Block1Chunk1ParentPath_14_ok,
    tttLargeFiber8Block1Chunk1ParentPath_15_ok]

def tttLargeFiber8Block1Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber8CountsAudit &&
    tttLargeFiber8Block1Chunk1SourcesCheck &&
    tttLargeFiber8Block1Chunk1RowsAudit &&
    tttLargeFiber8Block1Chunk1ParentMapAudit &&
    tttLargeFiber8Block1Chunk1ParentsAudit

theorem tttLargeFiber8Block1Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber8Block1Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber8Block1Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber8CountsAudit_ok,
    tttLargeFiber8Block1Chunk1SourcesCheck_ok,
    tttLargeFiber8Block1Chunk1RowsAudit_ok,
    tttLargeFiber8Block1Chunk1ParentMapAudit_ok,
    tttLargeFiber8Block1Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber8Block1Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
