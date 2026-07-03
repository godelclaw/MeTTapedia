import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 8, block 1 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber8Block1Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Data

def tttLargeFiber8Block1Chunk0Sources : List Nat :=
  [   4432, 4433, 4434, 4435, 4436, 4437, 4438, 4439,
   4440, 4441, 4442, 4443, 4444, 4445, 4446, 4447]

def tttLargeFiber8Row64 : TripleComponentParentRow :=
  tripleRow 4432 4368 133 156 148 132 148 148
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row65 : TripleComponentParentRow :=
  tripleRow 4433 4369 133 156 149 132 148 149
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row66 : TripleComponentParentRow :=
  tripleRow 4434 4370 133 156 150 132 148 150
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row67 : TripleComponentParentRow :=
  tripleRow 4435 4371 133 156 151 132 148 151
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row68 : TripleComponentParentRow :=
  tripleRow 4436 4372 133 156 164 132 148 164
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row69 : TripleComponentParentRow :=
  tripleRow 4437 4373 133 156 165 132 148 165
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row70 : TripleComponentParentRow :=
  tripleRow 4438 4374 133 156 166 132 148 166
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row71 : TripleComponentParentRow :=
  tripleRow 4439 4375 133 156 167 132 148 167
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row72 : TripleComponentParentRow :=
  tripleRow 4440 4376 133 157 156 132 149 156
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row73 : TripleComponentParentRow :=
  tripleRow 4441 4377 133 157 157 132 149 157
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row74 : TripleComponentParentRow :=
  tripleRow 4442 4378 133 157 158 132 149 158
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row75 : TripleComponentParentRow :=
  tripleRow 4443 4379 133 157 159 132 149 159
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row76 : TripleComponentParentRow :=
  tripleRow 4444 4380 133 157 172 132 149 172
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row77 : TripleComponentParentRow :=
  tripleRow 4445 4381 133 157 173 132 149 173
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row78 : TripleComponentParentRow :=
  tripleRow 4446 4382 133 157 174 132 149 174
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Row79 : TripleComponentParentRow :=
  tripleRow 4447 4383 133 157 175 132 149 175
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber8Block1Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber8Row64
  , tttLargeFiber8Row65
  , tttLargeFiber8Row66
  , tttLargeFiber8Row67
  , tttLargeFiber8Row68
  , tttLargeFiber8Row69
  , tttLargeFiber8Row70
  , tttLargeFiber8Row71
  , tttLargeFiber8Row72
  , tttLargeFiber8Row73
  , tttLargeFiber8Row74
  , tttLargeFiber8Row75
  , tttLargeFiber8Row76
  , tttLargeFiber8Row77
  , tttLargeFiber8Row78
  , tttLargeFiber8Row79
  ]

def tttLargeFiber8Block1Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (4368 <= i) && decide (i < 4624)) ||
    (decide (6000 <= i) && decide (i < 6256))

def tttLargeFiber8Block1Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber8Block1Chunk0ExpectedContains row.source &&
    tttLargeFiber8Block1Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber8Key &&
          chainInputKey tttWord t == tttLargeFiber8Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber8Block1Chunk0SourcesCheck : Bool :=
  (tttLargeFiber8Block1Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber8Block1Chunk0Sources

theorem tttLargeFiber8Block1Chunk0SourcesCheck_ok :
    tttLargeFiber8Block1Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber8Block1Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber8Block1Chunk0RowValid
    (listGetD tttLargeFiber8Block1Chunk0Rows i default)

def tttLargeFiber8Block1Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber8Block1Chunk0Rows i default
  row.parent == tttLargeFiber8ParentOf row.source

def tttLargeFiber8Block1Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber8Block1Chunk0Sources 0 0 == 4432
      && tttLargeFiber8ParentOf 4432 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (1 <= tttLargeFiber8MaxParentDepth)
  | 1 => listGetD tttLargeFiber8Block1Chunk0Sources 1 0 == 4433
      && tttLargeFiber8ParentOf 4433 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (2 <= tttLargeFiber8MaxParentDepth)
  | 2 => listGetD tttLargeFiber8Block1Chunk0Sources 2 0 == 4434
      && tttLargeFiber8ParentOf 4434 == 4370
      && tttLargeFiber8ParentOf 4370 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 3 => listGetD tttLargeFiber8Block1Chunk0Sources 3 0 == 4435
      && tttLargeFiber8ParentOf 4435 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (2 <= tttLargeFiber8MaxParentDepth)
  | 4 => listGetD tttLargeFiber8Block1Chunk0Sources 4 0 == 4436
      && tttLargeFiber8ParentOf 4436 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (2 <= tttLargeFiber8MaxParentDepth)
  | 5 => listGetD tttLargeFiber8Block1Chunk0Sources 5 0 == 4437
      && tttLargeFiber8ParentOf 4437 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 6 => listGetD tttLargeFiber8Block1Chunk0Sources 6 0 == 4438
      && tttLargeFiber8ParentOf 4438 == 4374
      && tttLargeFiber8ParentOf 4374 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 7 => listGetD tttLargeFiber8Block1Chunk0Sources 7 0 == 4439
      && tttLargeFiber8ParentOf 4439 == 4375
      && tttLargeFiber8ParentOf 4375 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 8 => listGetD tttLargeFiber8Block1Chunk0Sources 8 0 == 4440
      && tttLargeFiber8ParentOf 4440 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (2 <= tttLargeFiber8MaxParentDepth)
  | 9 => listGetD tttLargeFiber8Block1Chunk0Sources 9 0 == 4441
      && tttLargeFiber8ParentOf 4441 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 10 => listGetD tttLargeFiber8Block1Chunk0Sources 10 0 == 4442
      && tttLargeFiber8ParentOf 4442 == 4378
      && tttLargeFiber8ParentOf 4378 == 4370
      && tttLargeFiber8ParentOf 4370 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 11 => listGetD tttLargeFiber8Block1Chunk0Sources 11 0 == 4443
      && tttLargeFiber8ParentOf 4443 == 4379
      && tttLargeFiber8ParentOf 4379 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 12 => listGetD tttLargeFiber8Block1Chunk0Sources 12 0 == 4444
      && tttLargeFiber8ParentOf 4444 == 4380
      && tttLargeFiber8ParentOf 4380 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 13 => listGetD tttLargeFiber8Block1Chunk0Sources 13 0 == 4445
      && tttLargeFiber8ParentOf 4445 == 4381
      && tttLargeFiber8ParentOf 4381 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 14 => listGetD tttLargeFiber8Block1Chunk0Sources 14 0 == 4446
      && tttLargeFiber8ParentOf 4446 == 4382
      && tttLargeFiber8ParentOf 4382 == 4374
      && tttLargeFiber8ParentOf 4374 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 15 => listGetD tttLargeFiber8Block1Chunk0Sources 15 0 == 4447
      && tttLargeFiber8ParentOf 4447 == 4383
      && tttLargeFiber8ParentOf 4383 == 4375
      && tttLargeFiber8ParentOf 4375 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | _ => false

theorem tttLargeFiber8Block1Chunk0Row_0_ok :
    tttLargeFiber8Block1Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0Row_1_ok :
    tttLargeFiber8Block1Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0Row_2_ok :
    tttLargeFiber8Block1Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0Row_3_ok :
    tttLargeFiber8Block1Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0Row_4_ok :
    tttLargeFiber8Block1Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0Row_5_ok :
    tttLargeFiber8Block1Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0Row_6_ok :
    tttLargeFiber8Block1Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0Row_7_ok :
    tttLargeFiber8Block1Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0Row_8_ok :
    tttLargeFiber8Block1Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0Row_9_ok :
    tttLargeFiber8Block1Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0Row_10_ok :
    tttLargeFiber8Block1Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0Row_11_ok :
    tttLargeFiber8Block1Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0Row_12_ok :
    tttLargeFiber8Block1Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0Row_13_ok :
    tttLargeFiber8Block1Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0Row_14_ok :
    tttLargeFiber8Block1Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0Row_15_ok :
    tttLargeFiber8Block1Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentMap_0_ok :
    tttLargeFiber8Block1Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentMap_1_ok :
    tttLargeFiber8Block1Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentMap_2_ok :
    tttLargeFiber8Block1Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentMap_3_ok :
    tttLargeFiber8Block1Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentMap_4_ok :
    tttLargeFiber8Block1Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentMap_5_ok :
    tttLargeFiber8Block1Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentMap_6_ok :
    tttLargeFiber8Block1Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentMap_7_ok :
    tttLargeFiber8Block1Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentMap_8_ok :
    tttLargeFiber8Block1Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentMap_9_ok :
    tttLargeFiber8Block1Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentMap_10_ok :
    tttLargeFiber8Block1Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentMap_11_ok :
    tttLargeFiber8Block1Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentMap_12_ok :
    tttLargeFiber8Block1Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentMap_13_ok :
    tttLargeFiber8Block1Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentMap_14_ok :
    tttLargeFiber8Block1Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentMap_15_ok :
    tttLargeFiber8Block1Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentPath_0_ok :
    tttLargeFiber8Block1Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentPath_1_ok :
    tttLargeFiber8Block1Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentPath_2_ok :
    tttLargeFiber8Block1Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentPath_3_ok :
    tttLargeFiber8Block1Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentPath_4_ok :
    tttLargeFiber8Block1Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentPath_5_ok :
    tttLargeFiber8Block1Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentPath_6_ok :
    tttLargeFiber8Block1Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentPath_7_ok :
    tttLargeFiber8Block1Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentPath_8_ok :
    tttLargeFiber8Block1Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentPath_9_ok :
    tttLargeFiber8Block1Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentPath_10_ok :
    tttLargeFiber8Block1Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentPath_11_ok :
    tttLargeFiber8Block1Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentPath_12_ok :
    tttLargeFiber8Block1Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentPath_13_ok :
    tttLargeFiber8Block1Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentPath_14_ok :
    tttLargeFiber8Block1Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber8Block1Chunk0ParentPath_15_ok :
    tttLargeFiber8Block1Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber8Block1Chunk0RowsAudit : Bool :=
  tttLargeFiber8Block1Chunk0RowCheck 0
    && tttLargeFiber8Block1Chunk0RowCheck 1
    && tttLargeFiber8Block1Chunk0RowCheck 2
    && tttLargeFiber8Block1Chunk0RowCheck 3
    && tttLargeFiber8Block1Chunk0RowCheck 4
    && tttLargeFiber8Block1Chunk0RowCheck 5
    && tttLargeFiber8Block1Chunk0RowCheck 6
    && tttLargeFiber8Block1Chunk0RowCheck 7
    && tttLargeFiber8Block1Chunk0RowCheck 8
    && tttLargeFiber8Block1Chunk0RowCheck 9
    && tttLargeFiber8Block1Chunk0RowCheck 10
    && tttLargeFiber8Block1Chunk0RowCheck 11
    && tttLargeFiber8Block1Chunk0RowCheck 12
    && tttLargeFiber8Block1Chunk0RowCheck 13
    && tttLargeFiber8Block1Chunk0RowCheck 14
    && tttLargeFiber8Block1Chunk0RowCheck 15

theorem tttLargeFiber8Block1Chunk0RowsAudit_ok :
    tttLargeFiber8Block1Chunk0RowsAudit = true := by
  simp [tttLargeFiber8Block1Chunk0RowsAudit,
    tttLargeFiber8Block1Chunk0Row_0_ok,
    tttLargeFiber8Block1Chunk0Row_1_ok,
    tttLargeFiber8Block1Chunk0Row_2_ok,
    tttLargeFiber8Block1Chunk0Row_3_ok,
    tttLargeFiber8Block1Chunk0Row_4_ok,
    tttLargeFiber8Block1Chunk0Row_5_ok,
    tttLargeFiber8Block1Chunk0Row_6_ok,
    tttLargeFiber8Block1Chunk0Row_7_ok,
    tttLargeFiber8Block1Chunk0Row_8_ok,
    tttLargeFiber8Block1Chunk0Row_9_ok,
    tttLargeFiber8Block1Chunk0Row_10_ok,
    tttLargeFiber8Block1Chunk0Row_11_ok,
    tttLargeFiber8Block1Chunk0Row_12_ok,
    tttLargeFiber8Block1Chunk0Row_13_ok,
    tttLargeFiber8Block1Chunk0Row_14_ok,
    tttLargeFiber8Block1Chunk0Row_15_ok]

def tttLargeFiber8Block1Chunk0ParentMapAudit : Bool :=
  tttLargeFiber8Block1Chunk0ParentMapCheck 0
    && tttLargeFiber8Block1Chunk0ParentMapCheck 1
    && tttLargeFiber8Block1Chunk0ParentMapCheck 2
    && tttLargeFiber8Block1Chunk0ParentMapCheck 3
    && tttLargeFiber8Block1Chunk0ParentMapCheck 4
    && tttLargeFiber8Block1Chunk0ParentMapCheck 5
    && tttLargeFiber8Block1Chunk0ParentMapCheck 6
    && tttLargeFiber8Block1Chunk0ParentMapCheck 7
    && tttLargeFiber8Block1Chunk0ParentMapCheck 8
    && tttLargeFiber8Block1Chunk0ParentMapCheck 9
    && tttLargeFiber8Block1Chunk0ParentMapCheck 10
    && tttLargeFiber8Block1Chunk0ParentMapCheck 11
    && tttLargeFiber8Block1Chunk0ParentMapCheck 12
    && tttLargeFiber8Block1Chunk0ParentMapCheck 13
    && tttLargeFiber8Block1Chunk0ParentMapCheck 14
    && tttLargeFiber8Block1Chunk0ParentMapCheck 15

theorem tttLargeFiber8Block1Chunk0ParentMapAudit_ok :
    tttLargeFiber8Block1Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber8Block1Chunk0ParentMapAudit,
    tttLargeFiber8Block1Chunk0ParentMap_0_ok,
    tttLargeFiber8Block1Chunk0ParentMap_1_ok,
    tttLargeFiber8Block1Chunk0ParentMap_2_ok,
    tttLargeFiber8Block1Chunk0ParentMap_3_ok,
    tttLargeFiber8Block1Chunk0ParentMap_4_ok,
    tttLargeFiber8Block1Chunk0ParentMap_5_ok,
    tttLargeFiber8Block1Chunk0ParentMap_6_ok,
    tttLargeFiber8Block1Chunk0ParentMap_7_ok,
    tttLargeFiber8Block1Chunk0ParentMap_8_ok,
    tttLargeFiber8Block1Chunk0ParentMap_9_ok,
    tttLargeFiber8Block1Chunk0ParentMap_10_ok,
    tttLargeFiber8Block1Chunk0ParentMap_11_ok,
    tttLargeFiber8Block1Chunk0ParentMap_12_ok,
    tttLargeFiber8Block1Chunk0ParentMap_13_ok,
    tttLargeFiber8Block1Chunk0ParentMap_14_ok,
    tttLargeFiber8Block1Chunk0ParentMap_15_ok]

def tttLargeFiber8Block1Chunk0ParentsAudit : Bool :=
  tttLargeFiber8Block1Chunk0ParentPathCheck 0
    && tttLargeFiber8Block1Chunk0ParentPathCheck 1
    && tttLargeFiber8Block1Chunk0ParentPathCheck 2
    && tttLargeFiber8Block1Chunk0ParentPathCheck 3
    && tttLargeFiber8Block1Chunk0ParentPathCheck 4
    && tttLargeFiber8Block1Chunk0ParentPathCheck 5
    && tttLargeFiber8Block1Chunk0ParentPathCheck 6
    && tttLargeFiber8Block1Chunk0ParentPathCheck 7
    && tttLargeFiber8Block1Chunk0ParentPathCheck 8
    && tttLargeFiber8Block1Chunk0ParentPathCheck 9
    && tttLargeFiber8Block1Chunk0ParentPathCheck 10
    && tttLargeFiber8Block1Chunk0ParentPathCheck 11
    && tttLargeFiber8Block1Chunk0ParentPathCheck 12
    && tttLargeFiber8Block1Chunk0ParentPathCheck 13
    && tttLargeFiber8Block1Chunk0ParentPathCheck 14
    && tttLargeFiber8Block1Chunk0ParentPathCheck 15

theorem tttLargeFiber8Block1Chunk0ParentsAudit_ok :
    tttLargeFiber8Block1Chunk0ParentsAudit = true := by
  simp [tttLargeFiber8Block1Chunk0ParentsAudit,
    tttLargeFiber8Block1Chunk0ParentPath_0_ok,
    tttLargeFiber8Block1Chunk0ParentPath_1_ok,
    tttLargeFiber8Block1Chunk0ParentPath_2_ok,
    tttLargeFiber8Block1Chunk0ParentPath_3_ok,
    tttLargeFiber8Block1Chunk0ParentPath_4_ok,
    tttLargeFiber8Block1Chunk0ParentPath_5_ok,
    tttLargeFiber8Block1Chunk0ParentPath_6_ok,
    tttLargeFiber8Block1Chunk0ParentPath_7_ok,
    tttLargeFiber8Block1Chunk0ParentPath_8_ok,
    tttLargeFiber8Block1Chunk0ParentPath_9_ok,
    tttLargeFiber8Block1Chunk0ParentPath_10_ok,
    tttLargeFiber8Block1Chunk0ParentPath_11_ok,
    tttLargeFiber8Block1Chunk0ParentPath_12_ok,
    tttLargeFiber8Block1Chunk0ParentPath_13_ok,
    tttLargeFiber8Block1Chunk0ParentPath_14_ok,
    tttLargeFiber8Block1Chunk0ParentPath_15_ok]

def tttLargeFiber8Block1Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber8CountsAudit &&
    tttLargeFiber8Block1Chunk0SourcesCheck &&
    tttLargeFiber8Block1Chunk0RowsAudit &&
    tttLargeFiber8Block1Chunk0ParentMapAudit &&
    tttLargeFiber8Block1Chunk0ParentsAudit

theorem tttLargeFiber8Block1Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber8Block1Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber8Block1Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber8CountsAudit_ok,
    tttLargeFiber8Block1Chunk0SourcesCheck_ok,
    tttLargeFiber8Block1Chunk0RowsAudit_ok,
    tttLargeFiber8Block1Chunk0ParentMapAudit_ok,
    tttLargeFiber8Block1Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber8Block1Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
