import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 8, block 2 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber8Block2Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Data

def tttLargeFiber8Block2Chunk0Sources : List Nat :=
  [   4496, 4497, 4498, 4499, 4500, 4501, 4502, 4503,
   4504, 4505, 4506, 4507, 4508, 4509, 4510, 4511]

def tttLargeFiber8Row128 : TripleComponentParentRow :=
  tripleRow 4496 4528 134 0 80 134 48 148
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row129 : TripleComponentParentRow :=
  tripleRow 4497 4529 134 0 81 134 48 149
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row130 : TripleComponentParentRow :=
  tripleRow 4498 4496 134 0 82 134 0 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row131 : TripleComponentParentRow :=
  tripleRow 4499 4531 134 0 83 134 48 151
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber8Row132 : TripleComponentParentRow :=
  tripleRow 4500 4532 134 0 100 134 48 164
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber8Row133 : TripleComponentParentRow :=
  tripleRow 4501 4533 134 0 101 134 48 165
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber8Row134 : TripleComponentParentRow :=
  tripleRow 4502 4497 134 0 102 134 0 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber8Row135 : TripleComponentParentRow :=
  tripleRow 4503 4496 134 0 103 134 0 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber8Row136 : TripleComponentParentRow :=
  tripleRow 4504 4536 134 1 88 134 49 156
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row137 : TripleComponentParentRow :=
  tripleRow 4505 4537 134 1 89 134 49 157
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row138 : TripleComponentParentRow :=
  tripleRow 4506 4504 134 1 90 134 1 88
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row139 : TripleComponentParentRow :=
  tripleRow 4507 4539 134 1 91 134 49 159
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber8Row140 : TripleComponentParentRow :=
  tripleRow 4508 4540 134 1 108 134 49 172
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber8Row141 : TripleComponentParentRow :=
  tripleRow 4509 4541 134 1 109 134 49 173
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber8Row142 : TripleComponentParentRow :=
  tripleRow 4510 4505 134 1 110 134 1 89
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber8Row143 : TripleComponentParentRow :=
  tripleRow 4511 4504 134 1 111 134 1 88
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber8Block2Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber8Row128
  , tttLargeFiber8Row129
  , tttLargeFiber8Row130
  , tttLargeFiber8Row131
  , tttLargeFiber8Row132
  , tttLargeFiber8Row133
  , tttLargeFiber8Row134
  , tttLargeFiber8Row135
  , tttLargeFiber8Row136
  , tttLargeFiber8Row137
  , tttLargeFiber8Row138
  , tttLargeFiber8Row139
  , tttLargeFiber8Row140
  , tttLargeFiber8Row141
  , tttLargeFiber8Row142
  , tttLargeFiber8Row143
  ]

def tttLargeFiber8Block2Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (4368 <= i) && decide (i < 4624)) ||
    (decide (6000 <= i) && decide (i < 6256))

def tttLargeFiber8Block2Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber8Block2Chunk0ExpectedContains row.source &&
    tttLargeFiber8Block2Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber8Key &&
          chainInputKey tttWord t == tttLargeFiber8Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber8Block2Chunk0SourcesCheck : Bool :=
  (tttLargeFiber8Block2Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber8Block2Chunk0Sources

theorem tttLargeFiber8Block2Chunk0SourcesCheck_ok :
    tttLargeFiber8Block2Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber8Block2Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber8Block2Chunk0RowValid
    (listGetD tttLargeFiber8Block2Chunk0Rows i default)

def tttLargeFiber8Block2Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber8Block2Chunk0Rows i default
  row.parent == tttLargeFiber8ParentOf row.source

def tttLargeFiber8Block2Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber8Block2Chunk0Sources 0 0 == 4496
      && tttLargeFiber8ParentOf 4496 == 4528
      && tttLargeFiber8ParentOf 4528 == 4432
      && tttLargeFiber8ParentOf 4432 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 1 => listGetD tttLargeFiber8Block2Chunk0Sources 1 0 == 4497
      && tttLargeFiber8ParentOf 4497 == 4529
      && tttLargeFiber8ParentOf 4529 == 4433
      && tttLargeFiber8ParentOf 4433 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 2 => listGetD tttLargeFiber8Block2Chunk0Sources 2 0 == 4498
      && tttLargeFiber8ParentOf 4498 == 4496
      && tttLargeFiber8ParentOf 4496 == 4528
      && tttLargeFiber8ParentOf 4528 == 4432
      && tttLargeFiber8ParentOf 4432 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 3 => listGetD tttLargeFiber8Block2Chunk0Sources 3 0 == 4499
      && tttLargeFiber8ParentOf 4499 == 4531
      && tttLargeFiber8ParentOf 4531 == 4435
      && tttLargeFiber8ParentOf 4435 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 4 => listGetD tttLargeFiber8Block2Chunk0Sources 4 0 == 4500
      && tttLargeFiber8ParentOf 4500 == 4532
      && tttLargeFiber8ParentOf 4532 == 4436
      && tttLargeFiber8ParentOf 4436 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 5 => listGetD tttLargeFiber8Block2Chunk0Sources 5 0 == 4501
      && tttLargeFiber8ParentOf 4501 == 4533
      && tttLargeFiber8ParentOf 4533 == 4437
      && tttLargeFiber8ParentOf 4437 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 6 => listGetD tttLargeFiber8Block2Chunk0Sources 6 0 == 4502
      && tttLargeFiber8ParentOf 4502 == 4497
      && tttLargeFiber8ParentOf 4497 == 4529
      && tttLargeFiber8ParentOf 4529 == 4433
      && tttLargeFiber8ParentOf 4433 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 7 => listGetD tttLargeFiber8Block2Chunk0Sources 7 0 == 4503
      && tttLargeFiber8ParentOf 4503 == 4496
      && tttLargeFiber8ParentOf 4496 == 4528
      && tttLargeFiber8ParentOf 4528 == 4432
      && tttLargeFiber8ParentOf 4432 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 8 => listGetD tttLargeFiber8Block2Chunk0Sources 8 0 == 4504
      && tttLargeFiber8ParentOf 4504 == 4536
      && tttLargeFiber8ParentOf 4536 == 4440
      && tttLargeFiber8ParentOf 4440 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 9 => listGetD tttLargeFiber8Block2Chunk0Sources 9 0 == 4505
      && tttLargeFiber8ParentOf 4505 == 4537
      && tttLargeFiber8ParentOf 4537 == 4441
      && tttLargeFiber8ParentOf 4441 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 10 => listGetD tttLargeFiber8Block2Chunk0Sources 10 0 == 4506
      && tttLargeFiber8ParentOf 4506 == 4504
      && tttLargeFiber8ParentOf 4504 == 4536
      && tttLargeFiber8ParentOf 4536 == 4440
      && tttLargeFiber8ParentOf 4440 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 11 => listGetD tttLargeFiber8Block2Chunk0Sources 11 0 == 4507
      && tttLargeFiber8ParentOf 4507 == 4539
      && tttLargeFiber8ParentOf 4539 == 4443
      && tttLargeFiber8ParentOf 4443 == 4379
      && tttLargeFiber8ParentOf 4379 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 12 => listGetD tttLargeFiber8Block2Chunk0Sources 12 0 == 4508
      && tttLargeFiber8ParentOf 4508 == 4540
      && tttLargeFiber8ParentOf 4540 == 4444
      && tttLargeFiber8ParentOf 4444 == 4380
      && tttLargeFiber8ParentOf 4380 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 13 => listGetD tttLargeFiber8Block2Chunk0Sources 13 0 == 4509
      && tttLargeFiber8ParentOf 4509 == 4541
      && tttLargeFiber8ParentOf 4541 == 4445
      && tttLargeFiber8ParentOf 4445 == 4381
      && tttLargeFiber8ParentOf 4381 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (6 <= tttLargeFiber8MaxParentDepth)
  | 14 => listGetD tttLargeFiber8Block2Chunk0Sources 14 0 == 4510
      && tttLargeFiber8ParentOf 4510 == 4505
      && tttLargeFiber8ParentOf 4505 == 4537
      && tttLargeFiber8ParentOf 4537 == 4441
      && tttLargeFiber8ParentOf 4441 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (6 <= tttLargeFiber8MaxParentDepth)
  | 15 => listGetD tttLargeFiber8Block2Chunk0Sources 15 0 == 4511
      && tttLargeFiber8ParentOf 4511 == 4504
      && tttLargeFiber8ParentOf 4504 == 4536
      && tttLargeFiber8ParentOf 4536 == 4440
      && tttLargeFiber8ParentOf 4440 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | _ => false

theorem tttLargeFiber8Block2Chunk0Row_0_ok :
    tttLargeFiber8Block2Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0Row_1_ok :
    tttLargeFiber8Block2Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0Row_2_ok :
    tttLargeFiber8Block2Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0Row_3_ok :
    tttLargeFiber8Block2Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0Row_4_ok :
    tttLargeFiber8Block2Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0Row_5_ok :
    tttLargeFiber8Block2Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0Row_6_ok :
    tttLargeFiber8Block2Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0Row_7_ok :
    tttLargeFiber8Block2Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0Row_8_ok :
    tttLargeFiber8Block2Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0Row_9_ok :
    tttLargeFiber8Block2Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0Row_10_ok :
    tttLargeFiber8Block2Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0Row_11_ok :
    tttLargeFiber8Block2Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0Row_12_ok :
    tttLargeFiber8Block2Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0Row_13_ok :
    tttLargeFiber8Block2Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0Row_14_ok :
    tttLargeFiber8Block2Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0Row_15_ok :
    tttLargeFiber8Block2Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentMap_0_ok :
    tttLargeFiber8Block2Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentMap_1_ok :
    tttLargeFiber8Block2Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentMap_2_ok :
    tttLargeFiber8Block2Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentMap_3_ok :
    tttLargeFiber8Block2Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentMap_4_ok :
    tttLargeFiber8Block2Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentMap_5_ok :
    tttLargeFiber8Block2Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentMap_6_ok :
    tttLargeFiber8Block2Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentMap_7_ok :
    tttLargeFiber8Block2Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentMap_8_ok :
    tttLargeFiber8Block2Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentMap_9_ok :
    tttLargeFiber8Block2Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentMap_10_ok :
    tttLargeFiber8Block2Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentMap_11_ok :
    tttLargeFiber8Block2Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentMap_12_ok :
    tttLargeFiber8Block2Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentMap_13_ok :
    tttLargeFiber8Block2Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentMap_14_ok :
    tttLargeFiber8Block2Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentMap_15_ok :
    tttLargeFiber8Block2Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentPath_0_ok :
    tttLargeFiber8Block2Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentPath_1_ok :
    tttLargeFiber8Block2Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentPath_2_ok :
    tttLargeFiber8Block2Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentPath_3_ok :
    tttLargeFiber8Block2Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentPath_4_ok :
    tttLargeFiber8Block2Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentPath_5_ok :
    tttLargeFiber8Block2Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentPath_6_ok :
    tttLargeFiber8Block2Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentPath_7_ok :
    tttLargeFiber8Block2Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentPath_8_ok :
    tttLargeFiber8Block2Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentPath_9_ok :
    tttLargeFiber8Block2Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentPath_10_ok :
    tttLargeFiber8Block2Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentPath_11_ok :
    tttLargeFiber8Block2Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentPath_12_ok :
    tttLargeFiber8Block2Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentPath_13_ok :
    tttLargeFiber8Block2Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentPath_14_ok :
    tttLargeFiber8Block2Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber8Block2Chunk0ParentPath_15_ok :
    tttLargeFiber8Block2Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber8Block2Chunk0RowsAudit : Bool :=
  tttLargeFiber8Block2Chunk0RowCheck 0
    && tttLargeFiber8Block2Chunk0RowCheck 1
    && tttLargeFiber8Block2Chunk0RowCheck 2
    && tttLargeFiber8Block2Chunk0RowCheck 3
    && tttLargeFiber8Block2Chunk0RowCheck 4
    && tttLargeFiber8Block2Chunk0RowCheck 5
    && tttLargeFiber8Block2Chunk0RowCheck 6
    && tttLargeFiber8Block2Chunk0RowCheck 7
    && tttLargeFiber8Block2Chunk0RowCheck 8
    && tttLargeFiber8Block2Chunk0RowCheck 9
    && tttLargeFiber8Block2Chunk0RowCheck 10
    && tttLargeFiber8Block2Chunk0RowCheck 11
    && tttLargeFiber8Block2Chunk0RowCheck 12
    && tttLargeFiber8Block2Chunk0RowCheck 13
    && tttLargeFiber8Block2Chunk0RowCheck 14
    && tttLargeFiber8Block2Chunk0RowCheck 15

theorem tttLargeFiber8Block2Chunk0RowsAudit_ok :
    tttLargeFiber8Block2Chunk0RowsAudit = true := by
  simp [tttLargeFiber8Block2Chunk0RowsAudit,
    tttLargeFiber8Block2Chunk0Row_0_ok,
    tttLargeFiber8Block2Chunk0Row_1_ok,
    tttLargeFiber8Block2Chunk0Row_2_ok,
    tttLargeFiber8Block2Chunk0Row_3_ok,
    tttLargeFiber8Block2Chunk0Row_4_ok,
    tttLargeFiber8Block2Chunk0Row_5_ok,
    tttLargeFiber8Block2Chunk0Row_6_ok,
    tttLargeFiber8Block2Chunk0Row_7_ok,
    tttLargeFiber8Block2Chunk0Row_8_ok,
    tttLargeFiber8Block2Chunk0Row_9_ok,
    tttLargeFiber8Block2Chunk0Row_10_ok,
    tttLargeFiber8Block2Chunk0Row_11_ok,
    tttLargeFiber8Block2Chunk0Row_12_ok,
    tttLargeFiber8Block2Chunk0Row_13_ok,
    tttLargeFiber8Block2Chunk0Row_14_ok,
    tttLargeFiber8Block2Chunk0Row_15_ok]

def tttLargeFiber8Block2Chunk0ParentMapAudit : Bool :=
  tttLargeFiber8Block2Chunk0ParentMapCheck 0
    && tttLargeFiber8Block2Chunk0ParentMapCheck 1
    && tttLargeFiber8Block2Chunk0ParentMapCheck 2
    && tttLargeFiber8Block2Chunk0ParentMapCheck 3
    && tttLargeFiber8Block2Chunk0ParentMapCheck 4
    && tttLargeFiber8Block2Chunk0ParentMapCheck 5
    && tttLargeFiber8Block2Chunk0ParentMapCheck 6
    && tttLargeFiber8Block2Chunk0ParentMapCheck 7
    && tttLargeFiber8Block2Chunk0ParentMapCheck 8
    && tttLargeFiber8Block2Chunk0ParentMapCheck 9
    && tttLargeFiber8Block2Chunk0ParentMapCheck 10
    && tttLargeFiber8Block2Chunk0ParentMapCheck 11
    && tttLargeFiber8Block2Chunk0ParentMapCheck 12
    && tttLargeFiber8Block2Chunk0ParentMapCheck 13
    && tttLargeFiber8Block2Chunk0ParentMapCheck 14
    && tttLargeFiber8Block2Chunk0ParentMapCheck 15

theorem tttLargeFiber8Block2Chunk0ParentMapAudit_ok :
    tttLargeFiber8Block2Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber8Block2Chunk0ParentMapAudit,
    tttLargeFiber8Block2Chunk0ParentMap_0_ok,
    tttLargeFiber8Block2Chunk0ParentMap_1_ok,
    tttLargeFiber8Block2Chunk0ParentMap_2_ok,
    tttLargeFiber8Block2Chunk0ParentMap_3_ok,
    tttLargeFiber8Block2Chunk0ParentMap_4_ok,
    tttLargeFiber8Block2Chunk0ParentMap_5_ok,
    tttLargeFiber8Block2Chunk0ParentMap_6_ok,
    tttLargeFiber8Block2Chunk0ParentMap_7_ok,
    tttLargeFiber8Block2Chunk0ParentMap_8_ok,
    tttLargeFiber8Block2Chunk0ParentMap_9_ok,
    tttLargeFiber8Block2Chunk0ParentMap_10_ok,
    tttLargeFiber8Block2Chunk0ParentMap_11_ok,
    tttLargeFiber8Block2Chunk0ParentMap_12_ok,
    tttLargeFiber8Block2Chunk0ParentMap_13_ok,
    tttLargeFiber8Block2Chunk0ParentMap_14_ok,
    tttLargeFiber8Block2Chunk0ParentMap_15_ok]

def tttLargeFiber8Block2Chunk0ParentsAudit : Bool :=
  tttLargeFiber8Block2Chunk0ParentPathCheck 0
    && tttLargeFiber8Block2Chunk0ParentPathCheck 1
    && tttLargeFiber8Block2Chunk0ParentPathCheck 2
    && tttLargeFiber8Block2Chunk0ParentPathCheck 3
    && tttLargeFiber8Block2Chunk0ParentPathCheck 4
    && tttLargeFiber8Block2Chunk0ParentPathCheck 5
    && tttLargeFiber8Block2Chunk0ParentPathCheck 6
    && tttLargeFiber8Block2Chunk0ParentPathCheck 7
    && tttLargeFiber8Block2Chunk0ParentPathCheck 8
    && tttLargeFiber8Block2Chunk0ParentPathCheck 9
    && tttLargeFiber8Block2Chunk0ParentPathCheck 10
    && tttLargeFiber8Block2Chunk0ParentPathCheck 11
    && tttLargeFiber8Block2Chunk0ParentPathCheck 12
    && tttLargeFiber8Block2Chunk0ParentPathCheck 13
    && tttLargeFiber8Block2Chunk0ParentPathCheck 14
    && tttLargeFiber8Block2Chunk0ParentPathCheck 15

theorem tttLargeFiber8Block2Chunk0ParentsAudit_ok :
    tttLargeFiber8Block2Chunk0ParentsAudit = true := by
  simp [tttLargeFiber8Block2Chunk0ParentsAudit,
    tttLargeFiber8Block2Chunk0ParentPath_0_ok,
    tttLargeFiber8Block2Chunk0ParentPath_1_ok,
    tttLargeFiber8Block2Chunk0ParentPath_2_ok,
    tttLargeFiber8Block2Chunk0ParentPath_3_ok,
    tttLargeFiber8Block2Chunk0ParentPath_4_ok,
    tttLargeFiber8Block2Chunk0ParentPath_5_ok,
    tttLargeFiber8Block2Chunk0ParentPath_6_ok,
    tttLargeFiber8Block2Chunk0ParentPath_7_ok,
    tttLargeFiber8Block2Chunk0ParentPath_8_ok,
    tttLargeFiber8Block2Chunk0ParentPath_9_ok,
    tttLargeFiber8Block2Chunk0ParentPath_10_ok,
    tttLargeFiber8Block2Chunk0ParentPath_11_ok,
    tttLargeFiber8Block2Chunk0ParentPath_12_ok,
    tttLargeFiber8Block2Chunk0ParentPath_13_ok,
    tttLargeFiber8Block2Chunk0ParentPath_14_ok,
    tttLargeFiber8Block2Chunk0ParentPath_15_ok]

def tttLargeFiber8Block2Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber8CountsAudit &&
    tttLargeFiber8Block2Chunk0SourcesCheck &&
    tttLargeFiber8Block2Chunk0RowsAudit &&
    tttLargeFiber8Block2Chunk0ParentMapAudit &&
    tttLargeFiber8Block2Chunk0ParentsAudit

theorem tttLargeFiber8Block2Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber8Block2Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber8Block2Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber8CountsAudit_ok,
    tttLargeFiber8Block2Chunk0SourcesCheck_ok,
    tttLargeFiber8Block2Chunk0RowsAudit_ok,
    tttLargeFiber8Block2Chunk0ParentMapAudit_ok,
    tttLargeFiber8Block2Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber8Block2Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
