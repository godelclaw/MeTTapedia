import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 8, block 0 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber8Block0Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Data

def tttLargeFiber8Block0Chunk3Sources : List Nat :=
  [   4416, 4417, 4418, 4419, 4420, 4421, 4422, 4423,
   4424, 4425, 4426, 4427, 4428, 4429, 4430, 4431]

def tttLargeFiber8Row48 : TripleComponentParentRow :=
  tripleRow 4416 4400 132 166 64 132 164 132
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row49 : TripleComponentParentRow :=
  tripleRow 4417 4401 132 166 65 132 164 133
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row50 : TripleComponentParentRow :=
  tripleRow 4418 4416 132 166 66 132 166 64
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row51 : TripleComponentParentRow :=
  tripleRow 4419 4403 132 166 67 132 164 135
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

def tttLargeFiber8Row52 : TripleComponentParentRow :=
  tripleRow 4420 4404 132 166 116 132 164 180
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber8Row53 : TripleComponentParentRow :=
  tripleRow 4421 4405 132 166 117 132 164 181
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber8Row54 : TripleComponentParentRow :=
  tripleRow 4422 4417 132 166 118 132 166 65
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber8Row55 : TripleComponentParentRow :=
  tripleRow 4423 4416 132 166 119 132 166 64
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber8Row56 : TripleComponentParentRow :=
  tripleRow 4424 4408 132 167 72 132 165 140
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row57 : TripleComponentParentRow :=
  tripleRow 4425 4409 132 167 73 132 165 141
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row58 : TripleComponentParentRow :=
  tripleRow 4426 4394 132 167 74 132 151 10
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber8Row59 : TripleComponentParentRow :=
  tripleRow 4427 4395 132 167 75 132 151 11
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber8Row60 : TripleComponentParentRow :=
  tripleRow 4428 4396 132 167 124 132 151 56
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

def tttLargeFiber8Row61 : TripleComponentParentRow :=
  tripleRow 4429 4397 132 167 125 132 151 57
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

def tttLargeFiber8Row62 : TripleComponentParentRow :=
  tripleRow 4430 4428 132 167 126 132 167 124
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row63 : TripleComponentParentRow :=
  tripleRow 4431 4399 132 167 127 132 151 59
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Block0Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber8Row48
  , tttLargeFiber8Row49
  , tttLargeFiber8Row50
  , tttLargeFiber8Row51
  , tttLargeFiber8Row52
  , tttLargeFiber8Row53
  , tttLargeFiber8Row54
  , tttLargeFiber8Row55
  , tttLargeFiber8Row56
  , tttLargeFiber8Row57
  , tttLargeFiber8Row58
  , tttLargeFiber8Row59
  , tttLargeFiber8Row60
  , tttLargeFiber8Row61
  , tttLargeFiber8Row62
  , tttLargeFiber8Row63
  ]

def tttLargeFiber8Block0Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (4368 <= i) && decide (i < 4624)) ||
    (decide (6000 <= i) && decide (i < 6256))

def tttLargeFiber8Block0Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber8Block0Chunk3ExpectedContains row.source &&
    tttLargeFiber8Block0Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber8Key &&
          chainInputKey tttWord t == tttLargeFiber8Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber8Block0Chunk3SourcesCheck : Bool :=
  (tttLargeFiber8Block0Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber8Block0Chunk3Sources

theorem tttLargeFiber8Block0Chunk3SourcesCheck_ok :
    tttLargeFiber8Block0Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber8Block0Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber8Block0Chunk3RowValid
    (listGetD tttLargeFiber8Block0Chunk3Rows i default)

def tttLargeFiber8Block0Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber8Block0Chunk3Rows i default
  row.parent == tttLargeFiber8ParentOf row.source

def tttLargeFiber8Block0Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber8Block0Chunk3Sources 0 0 == 4416
      && tttLargeFiber8ParentOf 4416 == 4400
      && tttLargeFiber8ParentOf 4400 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (2 <= tttLargeFiber8MaxParentDepth)
  | 1 => listGetD tttLargeFiber8Block0Chunk3Sources 1 0 == 4417
      && tttLargeFiber8ParentOf 4417 == 4401
      && tttLargeFiber8ParentOf 4401 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 2 => listGetD tttLargeFiber8Block0Chunk3Sources 2 0 == 4418
      && tttLargeFiber8ParentOf 4418 == 4416
      && tttLargeFiber8ParentOf 4416 == 4400
      && tttLargeFiber8ParentOf 4400 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 3 => listGetD tttLargeFiber8Block0Chunk3Sources 3 0 == 4419
      && tttLargeFiber8ParentOf 4419 == 4403
      && tttLargeFiber8ParentOf 4403 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 4 => listGetD tttLargeFiber8Block0Chunk3Sources 4 0 == 4420
      && tttLargeFiber8ParentOf 4420 == 4404
      && tttLargeFiber8ParentOf 4404 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 5 => listGetD tttLargeFiber8Block0Chunk3Sources 5 0 == 4421
      && tttLargeFiber8ParentOf 4421 == 4405
      && tttLargeFiber8ParentOf 4405 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 6 => listGetD tttLargeFiber8Block0Chunk3Sources 6 0 == 4422
      && tttLargeFiber8ParentOf 4422 == 4417
      && tttLargeFiber8ParentOf 4417 == 4401
      && tttLargeFiber8ParentOf 4401 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 7 => listGetD tttLargeFiber8Block0Chunk3Sources 7 0 == 4423
      && tttLargeFiber8ParentOf 4423 == 4416
      && tttLargeFiber8ParentOf 4416 == 4400
      && tttLargeFiber8ParentOf 4400 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 8 => listGetD tttLargeFiber8Block0Chunk3Sources 8 0 == 4424
      && tttLargeFiber8ParentOf 4424 == 4408
      && tttLargeFiber8ParentOf 4408 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 9 => listGetD tttLargeFiber8Block0Chunk3Sources 9 0 == 4425
      && tttLargeFiber8ParentOf 4425 == 4409
      && tttLargeFiber8ParentOf 4409 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 10 => listGetD tttLargeFiber8Block0Chunk3Sources 10 0 == 4426
      && tttLargeFiber8ParentOf 4426 == 4394
      && tttLargeFiber8ParentOf 4394 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 11 => listGetD tttLargeFiber8Block0Chunk3Sources 11 0 == 4427
      && tttLargeFiber8ParentOf 4427 == 4395
      && tttLargeFiber8ParentOf 4395 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 12 => listGetD tttLargeFiber8Block0Chunk3Sources 12 0 == 4428
      && tttLargeFiber8ParentOf 4428 == 4396
      && tttLargeFiber8ParentOf 4396 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (2 <= tttLargeFiber8MaxParentDepth)
  | 13 => listGetD tttLargeFiber8Block0Chunk3Sources 13 0 == 4429
      && tttLargeFiber8ParentOf 4429 == 4397
      && tttLargeFiber8ParentOf 4397 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 14 => listGetD tttLargeFiber8Block0Chunk3Sources 14 0 == 4430
      && tttLargeFiber8ParentOf 4430 == 4428
      && tttLargeFiber8ParentOf 4428 == 4396
      && tttLargeFiber8ParentOf 4396 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 15 => listGetD tttLargeFiber8Block0Chunk3Sources 15 0 == 4431
      && tttLargeFiber8ParentOf 4431 == 4399
      && tttLargeFiber8ParentOf 4399 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | _ => false

theorem tttLargeFiber8Block0Chunk3Row_0_ok :
    tttLargeFiber8Block0Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3Row_1_ok :
    tttLargeFiber8Block0Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3Row_2_ok :
    tttLargeFiber8Block0Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3Row_3_ok :
    tttLargeFiber8Block0Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3Row_4_ok :
    tttLargeFiber8Block0Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3Row_5_ok :
    tttLargeFiber8Block0Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3Row_6_ok :
    tttLargeFiber8Block0Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3Row_7_ok :
    tttLargeFiber8Block0Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3Row_8_ok :
    tttLargeFiber8Block0Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3Row_9_ok :
    tttLargeFiber8Block0Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3Row_10_ok :
    tttLargeFiber8Block0Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3Row_11_ok :
    tttLargeFiber8Block0Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3Row_12_ok :
    tttLargeFiber8Block0Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3Row_13_ok :
    tttLargeFiber8Block0Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3Row_14_ok :
    tttLargeFiber8Block0Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3Row_15_ok :
    tttLargeFiber8Block0Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentMap_0_ok :
    tttLargeFiber8Block0Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentMap_1_ok :
    tttLargeFiber8Block0Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentMap_2_ok :
    tttLargeFiber8Block0Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentMap_3_ok :
    tttLargeFiber8Block0Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentMap_4_ok :
    tttLargeFiber8Block0Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentMap_5_ok :
    tttLargeFiber8Block0Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentMap_6_ok :
    tttLargeFiber8Block0Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentMap_7_ok :
    tttLargeFiber8Block0Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentMap_8_ok :
    tttLargeFiber8Block0Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentMap_9_ok :
    tttLargeFiber8Block0Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentMap_10_ok :
    tttLargeFiber8Block0Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentMap_11_ok :
    tttLargeFiber8Block0Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentMap_12_ok :
    tttLargeFiber8Block0Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentMap_13_ok :
    tttLargeFiber8Block0Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentMap_14_ok :
    tttLargeFiber8Block0Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentMap_15_ok :
    tttLargeFiber8Block0Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentPath_0_ok :
    tttLargeFiber8Block0Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentPath_1_ok :
    tttLargeFiber8Block0Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentPath_2_ok :
    tttLargeFiber8Block0Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentPath_3_ok :
    tttLargeFiber8Block0Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentPath_4_ok :
    tttLargeFiber8Block0Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentPath_5_ok :
    tttLargeFiber8Block0Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentPath_6_ok :
    tttLargeFiber8Block0Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentPath_7_ok :
    tttLargeFiber8Block0Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentPath_8_ok :
    tttLargeFiber8Block0Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentPath_9_ok :
    tttLargeFiber8Block0Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentPath_10_ok :
    tttLargeFiber8Block0Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentPath_11_ok :
    tttLargeFiber8Block0Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentPath_12_ok :
    tttLargeFiber8Block0Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentPath_13_ok :
    tttLargeFiber8Block0Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentPath_14_ok :
    tttLargeFiber8Block0Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber8Block0Chunk3ParentPath_15_ok :
    tttLargeFiber8Block0Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber8Block0Chunk3RowsAudit : Bool :=
  tttLargeFiber8Block0Chunk3RowCheck 0
    && tttLargeFiber8Block0Chunk3RowCheck 1
    && tttLargeFiber8Block0Chunk3RowCheck 2
    && tttLargeFiber8Block0Chunk3RowCheck 3
    && tttLargeFiber8Block0Chunk3RowCheck 4
    && tttLargeFiber8Block0Chunk3RowCheck 5
    && tttLargeFiber8Block0Chunk3RowCheck 6
    && tttLargeFiber8Block0Chunk3RowCheck 7
    && tttLargeFiber8Block0Chunk3RowCheck 8
    && tttLargeFiber8Block0Chunk3RowCheck 9
    && tttLargeFiber8Block0Chunk3RowCheck 10
    && tttLargeFiber8Block0Chunk3RowCheck 11
    && tttLargeFiber8Block0Chunk3RowCheck 12
    && tttLargeFiber8Block0Chunk3RowCheck 13
    && tttLargeFiber8Block0Chunk3RowCheck 14
    && tttLargeFiber8Block0Chunk3RowCheck 15

theorem tttLargeFiber8Block0Chunk3RowsAudit_ok :
    tttLargeFiber8Block0Chunk3RowsAudit = true := by
  simp [tttLargeFiber8Block0Chunk3RowsAudit,
    tttLargeFiber8Block0Chunk3Row_0_ok,
    tttLargeFiber8Block0Chunk3Row_1_ok,
    tttLargeFiber8Block0Chunk3Row_2_ok,
    tttLargeFiber8Block0Chunk3Row_3_ok,
    tttLargeFiber8Block0Chunk3Row_4_ok,
    tttLargeFiber8Block0Chunk3Row_5_ok,
    tttLargeFiber8Block0Chunk3Row_6_ok,
    tttLargeFiber8Block0Chunk3Row_7_ok,
    tttLargeFiber8Block0Chunk3Row_8_ok,
    tttLargeFiber8Block0Chunk3Row_9_ok,
    tttLargeFiber8Block0Chunk3Row_10_ok,
    tttLargeFiber8Block0Chunk3Row_11_ok,
    tttLargeFiber8Block0Chunk3Row_12_ok,
    tttLargeFiber8Block0Chunk3Row_13_ok,
    tttLargeFiber8Block0Chunk3Row_14_ok,
    tttLargeFiber8Block0Chunk3Row_15_ok]

def tttLargeFiber8Block0Chunk3ParentMapAudit : Bool :=
  tttLargeFiber8Block0Chunk3ParentMapCheck 0
    && tttLargeFiber8Block0Chunk3ParentMapCheck 1
    && tttLargeFiber8Block0Chunk3ParentMapCheck 2
    && tttLargeFiber8Block0Chunk3ParentMapCheck 3
    && tttLargeFiber8Block0Chunk3ParentMapCheck 4
    && tttLargeFiber8Block0Chunk3ParentMapCheck 5
    && tttLargeFiber8Block0Chunk3ParentMapCheck 6
    && tttLargeFiber8Block0Chunk3ParentMapCheck 7
    && tttLargeFiber8Block0Chunk3ParentMapCheck 8
    && tttLargeFiber8Block0Chunk3ParentMapCheck 9
    && tttLargeFiber8Block0Chunk3ParentMapCheck 10
    && tttLargeFiber8Block0Chunk3ParentMapCheck 11
    && tttLargeFiber8Block0Chunk3ParentMapCheck 12
    && tttLargeFiber8Block0Chunk3ParentMapCheck 13
    && tttLargeFiber8Block0Chunk3ParentMapCheck 14
    && tttLargeFiber8Block0Chunk3ParentMapCheck 15

theorem tttLargeFiber8Block0Chunk3ParentMapAudit_ok :
    tttLargeFiber8Block0Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber8Block0Chunk3ParentMapAudit,
    tttLargeFiber8Block0Chunk3ParentMap_0_ok,
    tttLargeFiber8Block0Chunk3ParentMap_1_ok,
    tttLargeFiber8Block0Chunk3ParentMap_2_ok,
    tttLargeFiber8Block0Chunk3ParentMap_3_ok,
    tttLargeFiber8Block0Chunk3ParentMap_4_ok,
    tttLargeFiber8Block0Chunk3ParentMap_5_ok,
    tttLargeFiber8Block0Chunk3ParentMap_6_ok,
    tttLargeFiber8Block0Chunk3ParentMap_7_ok,
    tttLargeFiber8Block0Chunk3ParentMap_8_ok,
    tttLargeFiber8Block0Chunk3ParentMap_9_ok,
    tttLargeFiber8Block0Chunk3ParentMap_10_ok,
    tttLargeFiber8Block0Chunk3ParentMap_11_ok,
    tttLargeFiber8Block0Chunk3ParentMap_12_ok,
    tttLargeFiber8Block0Chunk3ParentMap_13_ok,
    tttLargeFiber8Block0Chunk3ParentMap_14_ok,
    tttLargeFiber8Block0Chunk3ParentMap_15_ok]

def tttLargeFiber8Block0Chunk3ParentsAudit : Bool :=
  tttLargeFiber8Block0Chunk3ParentPathCheck 0
    && tttLargeFiber8Block0Chunk3ParentPathCheck 1
    && tttLargeFiber8Block0Chunk3ParentPathCheck 2
    && tttLargeFiber8Block0Chunk3ParentPathCheck 3
    && tttLargeFiber8Block0Chunk3ParentPathCheck 4
    && tttLargeFiber8Block0Chunk3ParentPathCheck 5
    && tttLargeFiber8Block0Chunk3ParentPathCheck 6
    && tttLargeFiber8Block0Chunk3ParentPathCheck 7
    && tttLargeFiber8Block0Chunk3ParentPathCheck 8
    && tttLargeFiber8Block0Chunk3ParentPathCheck 9
    && tttLargeFiber8Block0Chunk3ParentPathCheck 10
    && tttLargeFiber8Block0Chunk3ParentPathCheck 11
    && tttLargeFiber8Block0Chunk3ParentPathCheck 12
    && tttLargeFiber8Block0Chunk3ParentPathCheck 13
    && tttLargeFiber8Block0Chunk3ParentPathCheck 14
    && tttLargeFiber8Block0Chunk3ParentPathCheck 15

theorem tttLargeFiber8Block0Chunk3ParentsAudit_ok :
    tttLargeFiber8Block0Chunk3ParentsAudit = true := by
  simp [tttLargeFiber8Block0Chunk3ParentsAudit,
    tttLargeFiber8Block0Chunk3ParentPath_0_ok,
    tttLargeFiber8Block0Chunk3ParentPath_1_ok,
    tttLargeFiber8Block0Chunk3ParentPath_2_ok,
    tttLargeFiber8Block0Chunk3ParentPath_3_ok,
    tttLargeFiber8Block0Chunk3ParentPath_4_ok,
    tttLargeFiber8Block0Chunk3ParentPath_5_ok,
    tttLargeFiber8Block0Chunk3ParentPath_6_ok,
    tttLargeFiber8Block0Chunk3ParentPath_7_ok,
    tttLargeFiber8Block0Chunk3ParentPath_8_ok,
    tttLargeFiber8Block0Chunk3ParentPath_9_ok,
    tttLargeFiber8Block0Chunk3ParentPath_10_ok,
    tttLargeFiber8Block0Chunk3ParentPath_11_ok,
    tttLargeFiber8Block0Chunk3ParentPath_12_ok,
    tttLargeFiber8Block0Chunk3ParentPath_13_ok,
    tttLargeFiber8Block0Chunk3ParentPath_14_ok,
    tttLargeFiber8Block0Chunk3ParentPath_15_ok]

def tttLargeFiber8Block0Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber8CountsAudit &&
    tttLargeFiber8Block0Chunk3SourcesCheck &&
    tttLargeFiber8Block0Chunk3RowsAudit &&
    tttLargeFiber8Block0Chunk3ParentMapAudit &&
    tttLargeFiber8Block0Chunk3ParentsAudit

theorem tttLargeFiber8Block0Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber8Block0Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber8Block0Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber8CountsAudit_ok,
    tttLargeFiber8Block0Chunk3SourcesCheck_ok,
    tttLargeFiber8Block0Chunk3RowsAudit_ok,
    tttLargeFiber8Block0Chunk3ParentMapAudit_ok,
    tttLargeFiber8Block0Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber8Block0Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
