import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 8, block 3 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber8Block3Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Data

def tttLargeFiber8Block3Chunk0Sources : List Nat :=
  [   4560, 4561, 4562, 4563, 4564, 4565, 4566, 4567,
   4568, 4569, 4570, 4571, 4572, 4573, 4574, 4575]

def tttLargeFiber8Row192 : TripleComponentParentRow :=
  tripleRow 4560 4592 135 8 80 135 56 148
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

def tttLargeFiber8Row193 : TripleComponentParentRow :=
  tripleRow 4561 4593 135 8 81 135 56 149
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

def tttLargeFiber8Row194 : TripleComponentParentRow :=
  tripleRow 4562 4560 135 8 82 135 8 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row195 : TripleComponentParentRow :=
  tripleRow 4563 4595 135 8 83 135 56 151
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

def tttLargeFiber8Row196 : TripleComponentParentRow :=
  tripleRow 4564 4596 135 8 100 135 56 164
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber8Row197 : TripleComponentParentRow :=
  tripleRow 4565 4597 135 8 101 135 56 165
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber8Row198 : TripleComponentParentRow :=
  tripleRow 4566 4561 135 8 102 135 8 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber8Row199 : TripleComponentParentRow :=
  tripleRow 4567 4560 135 8 103 135 8 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber8Row200 : TripleComponentParentRow :=
  tripleRow 4568 4600 135 9 88 135 57 156
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

def tttLargeFiber8Row201 : TripleComponentParentRow :=
  tripleRow 4569 4601 135 9 89 135 57 157
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

def tttLargeFiber8Row202 : TripleComponentParentRow :=
  tripleRow 4570 4568 135 9 90 135 9 88
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row203 : TripleComponentParentRow :=
  tripleRow 4571 4603 135 9 91 135 57 159
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

def tttLargeFiber8Row204 : TripleComponentParentRow :=
  tripleRow 4572 4604 135 9 108 135 57 172
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber8Row205 : TripleComponentParentRow :=
  tripleRow 4573 4605 135 9 109 135 57 173
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber8Row206 : TripleComponentParentRow :=
  tripleRow 4574 4569 135 9 110 135 9 89
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber8Row207 : TripleComponentParentRow :=
  tripleRow 4575 4568 135 9 111 135 9 88
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber8Block3Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber8Row192
  , tttLargeFiber8Row193
  , tttLargeFiber8Row194
  , tttLargeFiber8Row195
  , tttLargeFiber8Row196
  , tttLargeFiber8Row197
  , tttLargeFiber8Row198
  , tttLargeFiber8Row199
  , tttLargeFiber8Row200
  , tttLargeFiber8Row201
  , tttLargeFiber8Row202
  , tttLargeFiber8Row203
  , tttLargeFiber8Row204
  , tttLargeFiber8Row205
  , tttLargeFiber8Row206
  , tttLargeFiber8Row207
  ]

def tttLargeFiber8Block3Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (4368 <= i) && decide (i < 4624)) ||
    (decide (6000 <= i) && decide (i < 6256))

def tttLargeFiber8Block3Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber8Block3Chunk0ExpectedContains row.source &&
    tttLargeFiber8Block3Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber8Key &&
          chainInputKey tttWord t == tttLargeFiber8Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber8Block3Chunk0SourcesCheck : Bool :=
  (tttLargeFiber8Block3Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber8Block3Chunk0Sources

theorem tttLargeFiber8Block3Chunk0SourcesCheck_ok :
    tttLargeFiber8Block3Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber8Block3Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber8Block3Chunk0RowValid
    (listGetD tttLargeFiber8Block3Chunk0Rows i default)

def tttLargeFiber8Block3Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber8Block3Chunk0Rows i default
  row.parent == tttLargeFiber8ParentOf row.source

def tttLargeFiber8Block3Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber8Block3Chunk0Sources 0 0 == 4560
      && tttLargeFiber8ParentOf 4560 == 4592
      && tttLargeFiber8ParentOf 4592 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (2 <= tttLargeFiber8MaxParentDepth)
  | 1 => listGetD tttLargeFiber8Block3Chunk0Sources 1 0 == 4561
      && tttLargeFiber8ParentOf 4561 == 4593
      && tttLargeFiber8ParentOf 4593 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 2 => listGetD tttLargeFiber8Block3Chunk0Sources 2 0 == 4562
      && tttLargeFiber8ParentOf 4562 == 4560
      && tttLargeFiber8ParentOf 4560 == 4592
      && tttLargeFiber8ParentOf 4592 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 3 => listGetD tttLargeFiber8Block3Chunk0Sources 3 0 == 4563
      && tttLargeFiber8ParentOf 4563 == 4595
      && tttLargeFiber8ParentOf 4595 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 4 => listGetD tttLargeFiber8Block3Chunk0Sources 4 0 == 4564
      && tttLargeFiber8ParentOf 4564 == 4596
      && tttLargeFiber8ParentOf 4596 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 5 => listGetD tttLargeFiber8Block3Chunk0Sources 5 0 == 4565
      && tttLargeFiber8ParentOf 4565 == 4597
      && tttLargeFiber8ParentOf 4597 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 6 => listGetD tttLargeFiber8Block3Chunk0Sources 6 0 == 4566
      && tttLargeFiber8ParentOf 4566 == 4561
      && tttLargeFiber8ParentOf 4561 == 4593
      && tttLargeFiber8ParentOf 4593 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 7 => listGetD tttLargeFiber8Block3Chunk0Sources 7 0 == 4567
      && tttLargeFiber8ParentOf 4567 == 4560
      && tttLargeFiber8ParentOf 4560 == 4592
      && tttLargeFiber8ParentOf 4592 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 8 => listGetD tttLargeFiber8Block3Chunk0Sources 8 0 == 4568
      && tttLargeFiber8ParentOf 4568 == 4600
      && tttLargeFiber8ParentOf 4600 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 9 => listGetD tttLargeFiber8Block3Chunk0Sources 9 0 == 4569
      && tttLargeFiber8ParentOf 4569 == 4601
      && tttLargeFiber8ParentOf 4601 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 10 => listGetD tttLargeFiber8Block3Chunk0Sources 10 0 == 4570
      && tttLargeFiber8ParentOf 4570 == 4568
      && tttLargeFiber8ParentOf 4568 == 4600
      && tttLargeFiber8ParentOf 4600 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 11 => listGetD tttLargeFiber8Block3Chunk0Sources 11 0 == 4571
      && tttLargeFiber8ParentOf 4571 == 4603
      && tttLargeFiber8ParentOf 4603 == 4379
      && tttLargeFiber8ParentOf 4379 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 12 => listGetD tttLargeFiber8Block3Chunk0Sources 12 0 == 4572
      && tttLargeFiber8ParentOf 4572 == 4604
      && tttLargeFiber8ParentOf 4604 == 4380
      && tttLargeFiber8ParentOf 4380 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 13 => listGetD tttLargeFiber8Block3Chunk0Sources 13 0 == 4573
      && tttLargeFiber8ParentOf 4573 == 4605
      && tttLargeFiber8ParentOf 4605 == 4381
      && tttLargeFiber8ParentOf 4381 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 14 => listGetD tttLargeFiber8Block3Chunk0Sources 14 0 == 4574
      && tttLargeFiber8ParentOf 4574 == 4569
      && tttLargeFiber8ParentOf 4569 == 4601
      && tttLargeFiber8ParentOf 4601 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 15 => listGetD tttLargeFiber8Block3Chunk0Sources 15 0 == 4575
      && tttLargeFiber8ParentOf 4575 == 4568
      && tttLargeFiber8ParentOf 4568 == 4600
      && tttLargeFiber8ParentOf 4600 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | _ => false

theorem tttLargeFiber8Block3Chunk0Row_0_ok :
    tttLargeFiber8Block3Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0Row_1_ok :
    tttLargeFiber8Block3Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0Row_2_ok :
    tttLargeFiber8Block3Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0Row_3_ok :
    tttLargeFiber8Block3Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0Row_4_ok :
    tttLargeFiber8Block3Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0Row_5_ok :
    tttLargeFiber8Block3Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0Row_6_ok :
    tttLargeFiber8Block3Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0Row_7_ok :
    tttLargeFiber8Block3Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0Row_8_ok :
    tttLargeFiber8Block3Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0Row_9_ok :
    tttLargeFiber8Block3Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0Row_10_ok :
    tttLargeFiber8Block3Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0Row_11_ok :
    tttLargeFiber8Block3Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0Row_12_ok :
    tttLargeFiber8Block3Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0Row_13_ok :
    tttLargeFiber8Block3Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0Row_14_ok :
    tttLargeFiber8Block3Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0Row_15_ok :
    tttLargeFiber8Block3Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentMap_0_ok :
    tttLargeFiber8Block3Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentMap_1_ok :
    tttLargeFiber8Block3Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentMap_2_ok :
    tttLargeFiber8Block3Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentMap_3_ok :
    tttLargeFiber8Block3Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentMap_4_ok :
    tttLargeFiber8Block3Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentMap_5_ok :
    tttLargeFiber8Block3Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentMap_6_ok :
    tttLargeFiber8Block3Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentMap_7_ok :
    tttLargeFiber8Block3Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentMap_8_ok :
    tttLargeFiber8Block3Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentMap_9_ok :
    tttLargeFiber8Block3Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentMap_10_ok :
    tttLargeFiber8Block3Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentMap_11_ok :
    tttLargeFiber8Block3Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentMap_12_ok :
    tttLargeFiber8Block3Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentMap_13_ok :
    tttLargeFiber8Block3Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentMap_14_ok :
    tttLargeFiber8Block3Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentMap_15_ok :
    tttLargeFiber8Block3Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentPath_0_ok :
    tttLargeFiber8Block3Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentPath_1_ok :
    tttLargeFiber8Block3Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentPath_2_ok :
    tttLargeFiber8Block3Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentPath_3_ok :
    tttLargeFiber8Block3Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentPath_4_ok :
    tttLargeFiber8Block3Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentPath_5_ok :
    tttLargeFiber8Block3Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentPath_6_ok :
    tttLargeFiber8Block3Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentPath_7_ok :
    tttLargeFiber8Block3Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentPath_8_ok :
    tttLargeFiber8Block3Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentPath_9_ok :
    tttLargeFiber8Block3Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentPath_10_ok :
    tttLargeFiber8Block3Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentPath_11_ok :
    tttLargeFiber8Block3Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentPath_12_ok :
    tttLargeFiber8Block3Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentPath_13_ok :
    tttLargeFiber8Block3Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentPath_14_ok :
    tttLargeFiber8Block3Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber8Block3Chunk0ParentPath_15_ok :
    tttLargeFiber8Block3Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber8Block3Chunk0RowsAudit : Bool :=
  tttLargeFiber8Block3Chunk0RowCheck 0
    && tttLargeFiber8Block3Chunk0RowCheck 1
    && tttLargeFiber8Block3Chunk0RowCheck 2
    && tttLargeFiber8Block3Chunk0RowCheck 3
    && tttLargeFiber8Block3Chunk0RowCheck 4
    && tttLargeFiber8Block3Chunk0RowCheck 5
    && tttLargeFiber8Block3Chunk0RowCheck 6
    && tttLargeFiber8Block3Chunk0RowCheck 7
    && tttLargeFiber8Block3Chunk0RowCheck 8
    && tttLargeFiber8Block3Chunk0RowCheck 9
    && tttLargeFiber8Block3Chunk0RowCheck 10
    && tttLargeFiber8Block3Chunk0RowCheck 11
    && tttLargeFiber8Block3Chunk0RowCheck 12
    && tttLargeFiber8Block3Chunk0RowCheck 13
    && tttLargeFiber8Block3Chunk0RowCheck 14
    && tttLargeFiber8Block3Chunk0RowCheck 15

theorem tttLargeFiber8Block3Chunk0RowsAudit_ok :
    tttLargeFiber8Block3Chunk0RowsAudit = true := by
  simp [tttLargeFiber8Block3Chunk0RowsAudit,
    tttLargeFiber8Block3Chunk0Row_0_ok,
    tttLargeFiber8Block3Chunk0Row_1_ok,
    tttLargeFiber8Block3Chunk0Row_2_ok,
    tttLargeFiber8Block3Chunk0Row_3_ok,
    tttLargeFiber8Block3Chunk0Row_4_ok,
    tttLargeFiber8Block3Chunk0Row_5_ok,
    tttLargeFiber8Block3Chunk0Row_6_ok,
    tttLargeFiber8Block3Chunk0Row_7_ok,
    tttLargeFiber8Block3Chunk0Row_8_ok,
    tttLargeFiber8Block3Chunk0Row_9_ok,
    tttLargeFiber8Block3Chunk0Row_10_ok,
    tttLargeFiber8Block3Chunk0Row_11_ok,
    tttLargeFiber8Block3Chunk0Row_12_ok,
    tttLargeFiber8Block3Chunk0Row_13_ok,
    tttLargeFiber8Block3Chunk0Row_14_ok,
    tttLargeFiber8Block3Chunk0Row_15_ok]

def tttLargeFiber8Block3Chunk0ParentMapAudit : Bool :=
  tttLargeFiber8Block3Chunk0ParentMapCheck 0
    && tttLargeFiber8Block3Chunk0ParentMapCheck 1
    && tttLargeFiber8Block3Chunk0ParentMapCheck 2
    && tttLargeFiber8Block3Chunk0ParentMapCheck 3
    && tttLargeFiber8Block3Chunk0ParentMapCheck 4
    && tttLargeFiber8Block3Chunk0ParentMapCheck 5
    && tttLargeFiber8Block3Chunk0ParentMapCheck 6
    && tttLargeFiber8Block3Chunk0ParentMapCheck 7
    && tttLargeFiber8Block3Chunk0ParentMapCheck 8
    && tttLargeFiber8Block3Chunk0ParentMapCheck 9
    && tttLargeFiber8Block3Chunk0ParentMapCheck 10
    && tttLargeFiber8Block3Chunk0ParentMapCheck 11
    && tttLargeFiber8Block3Chunk0ParentMapCheck 12
    && tttLargeFiber8Block3Chunk0ParentMapCheck 13
    && tttLargeFiber8Block3Chunk0ParentMapCheck 14
    && tttLargeFiber8Block3Chunk0ParentMapCheck 15

theorem tttLargeFiber8Block3Chunk0ParentMapAudit_ok :
    tttLargeFiber8Block3Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber8Block3Chunk0ParentMapAudit,
    tttLargeFiber8Block3Chunk0ParentMap_0_ok,
    tttLargeFiber8Block3Chunk0ParentMap_1_ok,
    tttLargeFiber8Block3Chunk0ParentMap_2_ok,
    tttLargeFiber8Block3Chunk0ParentMap_3_ok,
    tttLargeFiber8Block3Chunk0ParentMap_4_ok,
    tttLargeFiber8Block3Chunk0ParentMap_5_ok,
    tttLargeFiber8Block3Chunk0ParentMap_6_ok,
    tttLargeFiber8Block3Chunk0ParentMap_7_ok,
    tttLargeFiber8Block3Chunk0ParentMap_8_ok,
    tttLargeFiber8Block3Chunk0ParentMap_9_ok,
    tttLargeFiber8Block3Chunk0ParentMap_10_ok,
    tttLargeFiber8Block3Chunk0ParentMap_11_ok,
    tttLargeFiber8Block3Chunk0ParentMap_12_ok,
    tttLargeFiber8Block3Chunk0ParentMap_13_ok,
    tttLargeFiber8Block3Chunk0ParentMap_14_ok,
    tttLargeFiber8Block3Chunk0ParentMap_15_ok]

def tttLargeFiber8Block3Chunk0ParentsAudit : Bool :=
  tttLargeFiber8Block3Chunk0ParentPathCheck 0
    && tttLargeFiber8Block3Chunk0ParentPathCheck 1
    && tttLargeFiber8Block3Chunk0ParentPathCheck 2
    && tttLargeFiber8Block3Chunk0ParentPathCheck 3
    && tttLargeFiber8Block3Chunk0ParentPathCheck 4
    && tttLargeFiber8Block3Chunk0ParentPathCheck 5
    && tttLargeFiber8Block3Chunk0ParentPathCheck 6
    && tttLargeFiber8Block3Chunk0ParentPathCheck 7
    && tttLargeFiber8Block3Chunk0ParentPathCheck 8
    && tttLargeFiber8Block3Chunk0ParentPathCheck 9
    && tttLargeFiber8Block3Chunk0ParentPathCheck 10
    && tttLargeFiber8Block3Chunk0ParentPathCheck 11
    && tttLargeFiber8Block3Chunk0ParentPathCheck 12
    && tttLargeFiber8Block3Chunk0ParentPathCheck 13
    && tttLargeFiber8Block3Chunk0ParentPathCheck 14
    && tttLargeFiber8Block3Chunk0ParentPathCheck 15

theorem tttLargeFiber8Block3Chunk0ParentsAudit_ok :
    tttLargeFiber8Block3Chunk0ParentsAudit = true := by
  simp [tttLargeFiber8Block3Chunk0ParentsAudit,
    tttLargeFiber8Block3Chunk0ParentPath_0_ok,
    tttLargeFiber8Block3Chunk0ParentPath_1_ok,
    tttLargeFiber8Block3Chunk0ParentPath_2_ok,
    tttLargeFiber8Block3Chunk0ParentPath_3_ok,
    tttLargeFiber8Block3Chunk0ParentPath_4_ok,
    tttLargeFiber8Block3Chunk0ParentPath_5_ok,
    tttLargeFiber8Block3Chunk0ParentPath_6_ok,
    tttLargeFiber8Block3Chunk0ParentPath_7_ok,
    tttLargeFiber8Block3Chunk0ParentPath_8_ok,
    tttLargeFiber8Block3Chunk0ParentPath_9_ok,
    tttLargeFiber8Block3Chunk0ParentPath_10_ok,
    tttLargeFiber8Block3Chunk0ParentPath_11_ok,
    tttLargeFiber8Block3Chunk0ParentPath_12_ok,
    tttLargeFiber8Block3Chunk0ParentPath_13_ok,
    tttLargeFiber8Block3Chunk0ParentPath_14_ok,
    tttLargeFiber8Block3Chunk0ParentPath_15_ok]

def tttLargeFiber8Block3Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber8CountsAudit &&
    tttLargeFiber8Block3Chunk0SourcesCheck &&
    tttLargeFiber8Block3Chunk0RowsAudit &&
    tttLargeFiber8Block3Chunk0ParentMapAudit &&
    tttLargeFiber8Block3Chunk0ParentsAudit

theorem tttLargeFiber8Block3Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber8Block3Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber8Block3Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber8CountsAudit_ok,
    tttLargeFiber8Block3Chunk0SourcesCheck_ok,
    tttLargeFiber8Block3Chunk0RowsAudit_ok,
    tttLargeFiber8Block3Chunk0ParentMapAudit_ok,
    tttLargeFiber8Block3Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber8Block3Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
