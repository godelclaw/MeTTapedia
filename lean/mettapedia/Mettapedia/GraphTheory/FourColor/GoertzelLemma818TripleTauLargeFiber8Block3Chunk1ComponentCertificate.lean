import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 8, block 3 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber8Block3Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Data

def tttLargeFiber8Block3Chunk1Sources : List Nat :=
  [   4576, 4577, 4578, 4579, 4580, 4581, 4582, 4583,
   4584, 4585, 4586, 4587, 4588, 4589, 4590, 4591]

def tttLargeFiber8Row208 : TripleComponentParentRow :=
  tripleRow 4576 4580 135 10 16 135 10 32
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row209 : TripleComponentParentRow :=
  tripleRow 4577 4581 135 10 17 135 10 33
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row210 : TripleComponentParentRow :=
  tripleRow 4578 4404 135 10 18 132 164 180
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber8Row211 : TripleComponentParentRow :=
  tripleRow 4579 4405 135 10 19 132 164 181
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber8Row212 : TripleComponentParentRow :=
  tripleRow 4580 4400 135 10 32 132 164 132
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber8Row213 : TripleComponentParentRow :=
  tripleRow 4581 4401 135 10 33 132 164 133
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber8Row214 : TripleComponentParentRow :=
  tripleRow 4582 4402 135 10 34 132 164 134
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber8Row215 : TripleComponentParentRow :=
  tripleRow 4583 4403 135 10 35 132 164 135
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber8Row216 : TripleComponentParentRow :=
  tripleRow 4584 4588 135 11 24 135 11 40
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row217 : TripleComponentParentRow :=
  tripleRow 4585 4589 135 11 25 135 11 41
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row218 : TripleComponentParentRow :=
  tripleRow 4586 4412 135 11 26 132 165 188
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber8Row219 : TripleComponentParentRow :=
  tripleRow 4587 4413 135 11 27 132 165 189
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber8Row220 : TripleComponentParentRow :=
  tripleRow 4588 4408 135 11 40 132 165 140
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber8Row221 : TripleComponentParentRow :=
  tripleRow 4589 4409 135 11 41 132 165 141
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber8Row222 : TripleComponentParentRow :=
  tripleRow 4590 4410 135 11 42 132 165 142
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber8Row223 : TripleComponentParentRow :=
  tripleRow 4591 4411 135 11 43 132 165 143
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber8Block3Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber8Row208
  , tttLargeFiber8Row209
  , tttLargeFiber8Row210
  , tttLargeFiber8Row211
  , tttLargeFiber8Row212
  , tttLargeFiber8Row213
  , tttLargeFiber8Row214
  , tttLargeFiber8Row215
  , tttLargeFiber8Row216
  , tttLargeFiber8Row217
  , tttLargeFiber8Row218
  , tttLargeFiber8Row219
  , tttLargeFiber8Row220
  , tttLargeFiber8Row221
  , tttLargeFiber8Row222
  , tttLargeFiber8Row223
  ]

def tttLargeFiber8Block3Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (4368 <= i) && decide (i < 4624)) ||
    (decide (6000 <= i) && decide (i < 6256))

def tttLargeFiber8Block3Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber8Block3Chunk1ExpectedContains row.source &&
    tttLargeFiber8Block3Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber8Key &&
          chainInputKey tttWord t == tttLargeFiber8Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber8Block3Chunk1SourcesCheck : Bool :=
  (tttLargeFiber8Block3Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber8Block3Chunk1Sources

theorem tttLargeFiber8Block3Chunk1SourcesCheck_ok :
    tttLargeFiber8Block3Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber8Block3Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber8Block3Chunk1RowValid
    (listGetD tttLargeFiber8Block3Chunk1Rows i default)

def tttLargeFiber8Block3Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber8Block3Chunk1Rows i default
  row.parent == tttLargeFiber8ParentOf row.source

def tttLargeFiber8Block3Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber8Block3Chunk1Sources 0 0 == 4576
      && tttLargeFiber8ParentOf 4576 == 4580
      && tttLargeFiber8ParentOf 4580 == 4400
      && tttLargeFiber8ParentOf 4400 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 1 => listGetD tttLargeFiber8Block3Chunk1Sources 1 0 == 4577
      && tttLargeFiber8ParentOf 4577 == 4581
      && tttLargeFiber8ParentOf 4581 == 4401
      && tttLargeFiber8ParentOf 4401 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 2 => listGetD tttLargeFiber8Block3Chunk1Sources 2 0 == 4578
      && tttLargeFiber8ParentOf 4578 == 4404
      && tttLargeFiber8ParentOf 4404 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 3 => listGetD tttLargeFiber8Block3Chunk1Sources 3 0 == 4579
      && tttLargeFiber8ParentOf 4579 == 4405
      && tttLargeFiber8ParentOf 4405 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 4 => listGetD tttLargeFiber8Block3Chunk1Sources 4 0 == 4580
      && tttLargeFiber8ParentOf 4580 == 4400
      && tttLargeFiber8ParentOf 4400 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (2 <= tttLargeFiber8MaxParentDepth)
  | 5 => listGetD tttLargeFiber8Block3Chunk1Sources 5 0 == 4581
      && tttLargeFiber8ParentOf 4581 == 4401
      && tttLargeFiber8ParentOf 4401 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 6 => listGetD tttLargeFiber8Block3Chunk1Sources 6 0 == 4582
      && tttLargeFiber8ParentOf 4582 == 4402
      && tttLargeFiber8ParentOf 4402 == 4370
      && tttLargeFiber8ParentOf 4370 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 7 => listGetD tttLargeFiber8Block3Chunk1Sources 7 0 == 4583
      && tttLargeFiber8ParentOf 4583 == 4403
      && tttLargeFiber8ParentOf 4403 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 8 => listGetD tttLargeFiber8Block3Chunk1Sources 8 0 == 4584
      && tttLargeFiber8ParentOf 4584 == 4588
      && tttLargeFiber8ParentOf 4588 == 4408
      && tttLargeFiber8ParentOf 4408 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 9 => listGetD tttLargeFiber8Block3Chunk1Sources 9 0 == 4585
      && tttLargeFiber8ParentOf 4585 == 4589
      && tttLargeFiber8ParentOf 4589 == 4409
      && tttLargeFiber8ParentOf 4409 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 10 => listGetD tttLargeFiber8Block3Chunk1Sources 10 0 == 4586
      && tttLargeFiber8ParentOf 4586 == 4412
      && tttLargeFiber8ParentOf 4412 == 4380
      && tttLargeFiber8ParentOf 4380 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 11 => listGetD tttLargeFiber8Block3Chunk1Sources 11 0 == 4587
      && tttLargeFiber8ParentOf 4587 == 4413
      && tttLargeFiber8ParentOf 4413 == 4381
      && tttLargeFiber8ParentOf 4381 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 12 => listGetD tttLargeFiber8Block3Chunk1Sources 12 0 == 4588
      && tttLargeFiber8ParentOf 4588 == 4408
      && tttLargeFiber8ParentOf 4408 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 13 => listGetD tttLargeFiber8Block3Chunk1Sources 13 0 == 4589
      && tttLargeFiber8ParentOf 4589 == 4409
      && tttLargeFiber8ParentOf 4409 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 14 => listGetD tttLargeFiber8Block3Chunk1Sources 14 0 == 4590
      && tttLargeFiber8ParentOf 4590 == 4410
      && tttLargeFiber8ParentOf 4410 == 4378
      && tttLargeFiber8ParentOf 4378 == 4370
      && tttLargeFiber8ParentOf 4370 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 15 => listGetD tttLargeFiber8Block3Chunk1Sources 15 0 == 4591
      && tttLargeFiber8ParentOf 4591 == 4411
      && tttLargeFiber8ParentOf 4411 == 4379
      && tttLargeFiber8ParentOf 4379 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | _ => false

theorem tttLargeFiber8Block3Chunk1Row_0_ok :
    tttLargeFiber8Block3Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1Row_1_ok :
    tttLargeFiber8Block3Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1Row_2_ok :
    tttLargeFiber8Block3Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1Row_3_ok :
    tttLargeFiber8Block3Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1Row_4_ok :
    tttLargeFiber8Block3Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1Row_5_ok :
    tttLargeFiber8Block3Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1Row_6_ok :
    tttLargeFiber8Block3Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1Row_7_ok :
    tttLargeFiber8Block3Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1Row_8_ok :
    tttLargeFiber8Block3Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1Row_9_ok :
    tttLargeFiber8Block3Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1Row_10_ok :
    tttLargeFiber8Block3Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1Row_11_ok :
    tttLargeFiber8Block3Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1Row_12_ok :
    tttLargeFiber8Block3Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1Row_13_ok :
    tttLargeFiber8Block3Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1Row_14_ok :
    tttLargeFiber8Block3Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1Row_15_ok :
    tttLargeFiber8Block3Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentMap_0_ok :
    tttLargeFiber8Block3Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentMap_1_ok :
    tttLargeFiber8Block3Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentMap_2_ok :
    tttLargeFiber8Block3Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentMap_3_ok :
    tttLargeFiber8Block3Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentMap_4_ok :
    tttLargeFiber8Block3Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentMap_5_ok :
    tttLargeFiber8Block3Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentMap_6_ok :
    tttLargeFiber8Block3Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentMap_7_ok :
    tttLargeFiber8Block3Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentMap_8_ok :
    tttLargeFiber8Block3Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentMap_9_ok :
    tttLargeFiber8Block3Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentMap_10_ok :
    tttLargeFiber8Block3Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentMap_11_ok :
    tttLargeFiber8Block3Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentMap_12_ok :
    tttLargeFiber8Block3Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentMap_13_ok :
    tttLargeFiber8Block3Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentMap_14_ok :
    tttLargeFiber8Block3Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentMap_15_ok :
    tttLargeFiber8Block3Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentPath_0_ok :
    tttLargeFiber8Block3Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentPath_1_ok :
    tttLargeFiber8Block3Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentPath_2_ok :
    tttLargeFiber8Block3Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentPath_3_ok :
    tttLargeFiber8Block3Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentPath_4_ok :
    tttLargeFiber8Block3Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentPath_5_ok :
    tttLargeFiber8Block3Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentPath_6_ok :
    tttLargeFiber8Block3Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentPath_7_ok :
    tttLargeFiber8Block3Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentPath_8_ok :
    tttLargeFiber8Block3Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentPath_9_ok :
    tttLargeFiber8Block3Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentPath_10_ok :
    tttLargeFiber8Block3Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentPath_11_ok :
    tttLargeFiber8Block3Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentPath_12_ok :
    tttLargeFiber8Block3Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentPath_13_ok :
    tttLargeFiber8Block3Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentPath_14_ok :
    tttLargeFiber8Block3Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber8Block3Chunk1ParentPath_15_ok :
    tttLargeFiber8Block3Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber8Block3Chunk1RowsAudit : Bool :=
  tttLargeFiber8Block3Chunk1RowCheck 0
    && tttLargeFiber8Block3Chunk1RowCheck 1
    && tttLargeFiber8Block3Chunk1RowCheck 2
    && tttLargeFiber8Block3Chunk1RowCheck 3
    && tttLargeFiber8Block3Chunk1RowCheck 4
    && tttLargeFiber8Block3Chunk1RowCheck 5
    && tttLargeFiber8Block3Chunk1RowCheck 6
    && tttLargeFiber8Block3Chunk1RowCheck 7
    && tttLargeFiber8Block3Chunk1RowCheck 8
    && tttLargeFiber8Block3Chunk1RowCheck 9
    && tttLargeFiber8Block3Chunk1RowCheck 10
    && tttLargeFiber8Block3Chunk1RowCheck 11
    && tttLargeFiber8Block3Chunk1RowCheck 12
    && tttLargeFiber8Block3Chunk1RowCheck 13
    && tttLargeFiber8Block3Chunk1RowCheck 14
    && tttLargeFiber8Block3Chunk1RowCheck 15

theorem tttLargeFiber8Block3Chunk1RowsAudit_ok :
    tttLargeFiber8Block3Chunk1RowsAudit = true := by
  simp [tttLargeFiber8Block3Chunk1RowsAudit,
    tttLargeFiber8Block3Chunk1Row_0_ok,
    tttLargeFiber8Block3Chunk1Row_1_ok,
    tttLargeFiber8Block3Chunk1Row_2_ok,
    tttLargeFiber8Block3Chunk1Row_3_ok,
    tttLargeFiber8Block3Chunk1Row_4_ok,
    tttLargeFiber8Block3Chunk1Row_5_ok,
    tttLargeFiber8Block3Chunk1Row_6_ok,
    tttLargeFiber8Block3Chunk1Row_7_ok,
    tttLargeFiber8Block3Chunk1Row_8_ok,
    tttLargeFiber8Block3Chunk1Row_9_ok,
    tttLargeFiber8Block3Chunk1Row_10_ok,
    tttLargeFiber8Block3Chunk1Row_11_ok,
    tttLargeFiber8Block3Chunk1Row_12_ok,
    tttLargeFiber8Block3Chunk1Row_13_ok,
    tttLargeFiber8Block3Chunk1Row_14_ok,
    tttLargeFiber8Block3Chunk1Row_15_ok]

def tttLargeFiber8Block3Chunk1ParentMapAudit : Bool :=
  tttLargeFiber8Block3Chunk1ParentMapCheck 0
    && tttLargeFiber8Block3Chunk1ParentMapCheck 1
    && tttLargeFiber8Block3Chunk1ParentMapCheck 2
    && tttLargeFiber8Block3Chunk1ParentMapCheck 3
    && tttLargeFiber8Block3Chunk1ParentMapCheck 4
    && tttLargeFiber8Block3Chunk1ParentMapCheck 5
    && tttLargeFiber8Block3Chunk1ParentMapCheck 6
    && tttLargeFiber8Block3Chunk1ParentMapCheck 7
    && tttLargeFiber8Block3Chunk1ParentMapCheck 8
    && tttLargeFiber8Block3Chunk1ParentMapCheck 9
    && tttLargeFiber8Block3Chunk1ParentMapCheck 10
    && tttLargeFiber8Block3Chunk1ParentMapCheck 11
    && tttLargeFiber8Block3Chunk1ParentMapCheck 12
    && tttLargeFiber8Block3Chunk1ParentMapCheck 13
    && tttLargeFiber8Block3Chunk1ParentMapCheck 14
    && tttLargeFiber8Block3Chunk1ParentMapCheck 15

theorem tttLargeFiber8Block3Chunk1ParentMapAudit_ok :
    tttLargeFiber8Block3Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber8Block3Chunk1ParentMapAudit,
    tttLargeFiber8Block3Chunk1ParentMap_0_ok,
    tttLargeFiber8Block3Chunk1ParentMap_1_ok,
    tttLargeFiber8Block3Chunk1ParentMap_2_ok,
    tttLargeFiber8Block3Chunk1ParentMap_3_ok,
    tttLargeFiber8Block3Chunk1ParentMap_4_ok,
    tttLargeFiber8Block3Chunk1ParentMap_5_ok,
    tttLargeFiber8Block3Chunk1ParentMap_6_ok,
    tttLargeFiber8Block3Chunk1ParentMap_7_ok,
    tttLargeFiber8Block3Chunk1ParentMap_8_ok,
    tttLargeFiber8Block3Chunk1ParentMap_9_ok,
    tttLargeFiber8Block3Chunk1ParentMap_10_ok,
    tttLargeFiber8Block3Chunk1ParentMap_11_ok,
    tttLargeFiber8Block3Chunk1ParentMap_12_ok,
    tttLargeFiber8Block3Chunk1ParentMap_13_ok,
    tttLargeFiber8Block3Chunk1ParentMap_14_ok,
    tttLargeFiber8Block3Chunk1ParentMap_15_ok]

def tttLargeFiber8Block3Chunk1ParentsAudit : Bool :=
  tttLargeFiber8Block3Chunk1ParentPathCheck 0
    && tttLargeFiber8Block3Chunk1ParentPathCheck 1
    && tttLargeFiber8Block3Chunk1ParentPathCheck 2
    && tttLargeFiber8Block3Chunk1ParentPathCheck 3
    && tttLargeFiber8Block3Chunk1ParentPathCheck 4
    && tttLargeFiber8Block3Chunk1ParentPathCheck 5
    && tttLargeFiber8Block3Chunk1ParentPathCheck 6
    && tttLargeFiber8Block3Chunk1ParentPathCheck 7
    && tttLargeFiber8Block3Chunk1ParentPathCheck 8
    && tttLargeFiber8Block3Chunk1ParentPathCheck 9
    && tttLargeFiber8Block3Chunk1ParentPathCheck 10
    && tttLargeFiber8Block3Chunk1ParentPathCheck 11
    && tttLargeFiber8Block3Chunk1ParentPathCheck 12
    && tttLargeFiber8Block3Chunk1ParentPathCheck 13
    && tttLargeFiber8Block3Chunk1ParentPathCheck 14
    && tttLargeFiber8Block3Chunk1ParentPathCheck 15

theorem tttLargeFiber8Block3Chunk1ParentsAudit_ok :
    tttLargeFiber8Block3Chunk1ParentsAudit = true := by
  simp [tttLargeFiber8Block3Chunk1ParentsAudit,
    tttLargeFiber8Block3Chunk1ParentPath_0_ok,
    tttLargeFiber8Block3Chunk1ParentPath_1_ok,
    tttLargeFiber8Block3Chunk1ParentPath_2_ok,
    tttLargeFiber8Block3Chunk1ParentPath_3_ok,
    tttLargeFiber8Block3Chunk1ParentPath_4_ok,
    tttLargeFiber8Block3Chunk1ParentPath_5_ok,
    tttLargeFiber8Block3Chunk1ParentPath_6_ok,
    tttLargeFiber8Block3Chunk1ParentPath_7_ok,
    tttLargeFiber8Block3Chunk1ParentPath_8_ok,
    tttLargeFiber8Block3Chunk1ParentPath_9_ok,
    tttLargeFiber8Block3Chunk1ParentPath_10_ok,
    tttLargeFiber8Block3Chunk1ParentPath_11_ok,
    tttLargeFiber8Block3Chunk1ParentPath_12_ok,
    tttLargeFiber8Block3Chunk1ParentPath_13_ok,
    tttLargeFiber8Block3Chunk1ParentPath_14_ok,
    tttLargeFiber8Block3Chunk1ParentPath_15_ok]

def tttLargeFiber8Block3Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber8CountsAudit &&
    tttLargeFiber8Block3Chunk1SourcesCheck &&
    tttLargeFiber8Block3Chunk1RowsAudit &&
    tttLargeFiber8Block3Chunk1ParentMapAudit &&
    tttLargeFiber8Block3Chunk1ParentsAudit

theorem tttLargeFiber8Block3Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber8Block3Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber8Block3Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber8CountsAudit_ok,
    tttLargeFiber8Block3Chunk1SourcesCheck_ok,
    tttLargeFiber8Block3Chunk1RowsAudit_ok,
    tttLargeFiber8Block3Chunk1ParentMapAudit_ok,
    tttLargeFiber8Block3Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber8Block3Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
