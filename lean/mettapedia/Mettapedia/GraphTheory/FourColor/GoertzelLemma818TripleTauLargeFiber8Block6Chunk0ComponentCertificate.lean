import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 8, block 6 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber8Block6Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Data

def tttLargeFiber8Block6Chunk0Sources : List Nat :=
  [   6128, 6129, 6130, 6131, 6132, 6133, 6134, 6135,
   6136, 6137, 6138, 6139, 6140, 6141, 6142, 6143]

def tttLargeFiber8Row384 : TripleComponentParentRow :=
  tripleRow 6128 6000 182 64 80 180 132 148
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row385 : TripleComponentParentRow :=
  tripleRow 6129 6001 182 64 81 180 132 149
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row386 : TripleComponentParentRow :=
  tripleRow 6130 6128 182 64 82 182 64 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row387 : TripleComponentParentRow :=
  tripleRow 6131 6003 182 64 83 180 132 151
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber8Row388 : TripleComponentParentRow :=
  tripleRow 6132 6004 182 64 100 180 132 164
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row389 : TripleComponentParentRow :=
  tripleRow 6133 6005 182 64 101 180 132 165
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row390 : TripleComponentParentRow :=
  tripleRow 6134 6129 182 64 102 182 64 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber8Row391 : TripleComponentParentRow :=
  tripleRow 6135 6128 182 64 103 182 64 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber8Row392 : TripleComponentParentRow :=
  tripleRow 6136 6008 182 65 88 180 133 156
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row393 : TripleComponentParentRow :=
  tripleRow 6137 6009 182 65 89 180 133 157
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row394 : TripleComponentParentRow :=
  tripleRow 6138 6136 182 65 90 182 65 88
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row395 : TripleComponentParentRow :=
  tripleRow 6139 6011 182 65 91 180 133 159
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber8Row396 : TripleComponentParentRow :=
  tripleRow 6140 6012 182 65 108 180 133 172
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row397 : TripleComponentParentRow :=
  tripleRow 6141 6013 182 65 109 180 133 173
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber8Row398 : TripleComponentParentRow :=
  tripleRow 6142 6137 182 65 110 182 65 89
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber8Row399 : TripleComponentParentRow :=
  tripleRow 6143 6136 182 65 111 182 65 88
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber8Block6Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber8Row384
  , tttLargeFiber8Row385
  , tttLargeFiber8Row386
  , tttLargeFiber8Row387
  , tttLargeFiber8Row388
  , tttLargeFiber8Row389
  , tttLargeFiber8Row390
  , tttLargeFiber8Row391
  , tttLargeFiber8Row392
  , tttLargeFiber8Row393
  , tttLargeFiber8Row394
  , tttLargeFiber8Row395
  , tttLargeFiber8Row396
  , tttLargeFiber8Row397
  , tttLargeFiber8Row398
  , tttLargeFiber8Row399
  ]

def tttLargeFiber8Block6Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (4368 <= i) && decide (i < 4624)) ||
    (decide (6000 <= i) && decide (i < 6256))

def tttLargeFiber8Block6Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber8Block6Chunk0ExpectedContains row.source &&
    tttLargeFiber8Block6Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber8Key &&
          chainInputKey tttWord t == tttLargeFiber8Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber8Block6Chunk0SourcesCheck : Bool :=
  (tttLargeFiber8Block6Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber8Block6Chunk0Sources

theorem tttLargeFiber8Block6Chunk0SourcesCheck_ok :
    tttLargeFiber8Block6Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber8Block6Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber8Block6Chunk0RowValid
    (listGetD tttLargeFiber8Block6Chunk0Rows i default)

def tttLargeFiber8Block6Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber8Block6Chunk0Rows i default
  row.parent == tttLargeFiber8ParentOf row.source

def tttLargeFiber8Block6Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber8Block6Chunk0Sources 0 0 == 6128
      && tttLargeFiber8ParentOf 6128 == 6000
      && tttLargeFiber8ParentOf 6000 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (2 <= tttLargeFiber8MaxParentDepth)
  | 1 => listGetD tttLargeFiber8Block6Chunk0Sources 1 0 == 6129
      && tttLargeFiber8ParentOf 6129 == 6001
      && tttLargeFiber8ParentOf 6001 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 2 => listGetD tttLargeFiber8Block6Chunk0Sources 2 0 == 6130
      && tttLargeFiber8ParentOf 6130 == 6128
      && tttLargeFiber8ParentOf 6128 == 6000
      && tttLargeFiber8ParentOf 6000 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 3 => listGetD tttLargeFiber8Block6Chunk0Sources 3 0 == 6131
      && tttLargeFiber8ParentOf 6131 == 6003
      && tttLargeFiber8ParentOf 6003 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 4 => listGetD tttLargeFiber8Block6Chunk0Sources 4 0 == 6132
      && tttLargeFiber8ParentOf 6132 == 6004
      && tttLargeFiber8ParentOf 6004 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 5 => listGetD tttLargeFiber8Block6Chunk0Sources 5 0 == 6133
      && tttLargeFiber8ParentOf 6133 == 6005
      && tttLargeFiber8ParentOf 6005 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 6 => listGetD tttLargeFiber8Block6Chunk0Sources 6 0 == 6134
      && tttLargeFiber8ParentOf 6134 == 6129
      && tttLargeFiber8ParentOf 6129 == 6001
      && tttLargeFiber8ParentOf 6001 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 7 => listGetD tttLargeFiber8Block6Chunk0Sources 7 0 == 6135
      && tttLargeFiber8ParentOf 6135 == 6128
      && tttLargeFiber8ParentOf 6128 == 6000
      && tttLargeFiber8ParentOf 6000 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 8 => listGetD tttLargeFiber8Block6Chunk0Sources 8 0 == 6136
      && tttLargeFiber8ParentOf 6136 == 6008
      && tttLargeFiber8ParentOf 6008 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 9 => listGetD tttLargeFiber8Block6Chunk0Sources 9 0 == 6137
      && tttLargeFiber8ParentOf 6137 == 6009
      && tttLargeFiber8ParentOf 6009 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 10 => listGetD tttLargeFiber8Block6Chunk0Sources 10 0 == 6138
      && tttLargeFiber8ParentOf 6138 == 6136
      && tttLargeFiber8ParentOf 6136 == 6008
      && tttLargeFiber8ParentOf 6008 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 11 => listGetD tttLargeFiber8Block6Chunk0Sources 11 0 == 6139
      && tttLargeFiber8ParentOf 6139 == 6011
      && tttLargeFiber8ParentOf 6011 == 4379
      && tttLargeFiber8ParentOf 4379 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 12 => listGetD tttLargeFiber8Block6Chunk0Sources 12 0 == 6140
      && tttLargeFiber8ParentOf 6140 == 6012
      && tttLargeFiber8ParentOf 6012 == 4380
      && tttLargeFiber8ParentOf 4380 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 13 => listGetD tttLargeFiber8Block6Chunk0Sources 13 0 == 6141
      && tttLargeFiber8ParentOf 6141 == 6013
      && tttLargeFiber8ParentOf 6013 == 4381
      && tttLargeFiber8ParentOf 4381 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 14 => listGetD tttLargeFiber8Block6Chunk0Sources 14 0 == 6142
      && tttLargeFiber8ParentOf 6142 == 6137
      && tttLargeFiber8ParentOf 6137 == 6009
      && tttLargeFiber8ParentOf 6009 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 15 => listGetD tttLargeFiber8Block6Chunk0Sources 15 0 == 6143
      && tttLargeFiber8ParentOf 6143 == 6136
      && tttLargeFiber8ParentOf 6136 == 6008
      && tttLargeFiber8ParentOf 6008 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | _ => false

theorem tttLargeFiber8Block6Chunk0Row_0_ok :
    tttLargeFiber8Block6Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0Row_1_ok :
    tttLargeFiber8Block6Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0Row_2_ok :
    tttLargeFiber8Block6Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0Row_3_ok :
    tttLargeFiber8Block6Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0Row_4_ok :
    tttLargeFiber8Block6Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0Row_5_ok :
    tttLargeFiber8Block6Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0Row_6_ok :
    tttLargeFiber8Block6Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0Row_7_ok :
    tttLargeFiber8Block6Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0Row_8_ok :
    tttLargeFiber8Block6Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0Row_9_ok :
    tttLargeFiber8Block6Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0Row_10_ok :
    tttLargeFiber8Block6Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0Row_11_ok :
    tttLargeFiber8Block6Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0Row_12_ok :
    tttLargeFiber8Block6Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0Row_13_ok :
    tttLargeFiber8Block6Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0Row_14_ok :
    tttLargeFiber8Block6Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0Row_15_ok :
    tttLargeFiber8Block6Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentMap_0_ok :
    tttLargeFiber8Block6Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentMap_1_ok :
    tttLargeFiber8Block6Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentMap_2_ok :
    tttLargeFiber8Block6Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentMap_3_ok :
    tttLargeFiber8Block6Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentMap_4_ok :
    tttLargeFiber8Block6Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentMap_5_ok :
    tttLargeFiber8Block6Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentMap_6_ok :
    tttLargeFiber8Block6Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentMap_7_ok :
    tttLargeFiber8Block6Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentMap_8_ok :
    tttLargeFiber8Block6Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentMap_9_ok :
    tttLargeFiber8Block6Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentMap_10_ok :
    tttLargeFiber8Block6Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentMap_11_ok :
    tttLargeFiber8Block6Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentMap_12_ok :
    tttLargeFiber8Block6Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentMap_13_ok :
    tttLargeFiber8Block6Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentMap_14_ok :
    tttLargeFiber8Block6Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentMap_15_ok :
    tttLargeFiber8Block6Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentPath_0_ok :
    tttLargeFiber8Block6Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentPath_1_ok :
    tttLargeFiber8Block6Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentPath_2_ok :
    tttLargeFiber8Block6Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentPath_3_ok :
    tttLargeFiber8Block6Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentPath_4_ok :
    tttLargeFiber8Block6Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentPath_5_ok :
    tttLargeFiber8Block6Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentPath_6_ok :
    tttLargeFiber8Block6Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentPath_7_ok :
    tttLargeFiber8Block6Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentPath_8_ok :
    tttLargeFiber8Block6Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentPath_9_ok :
    tttLargeFiber8Block6Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentPath_10_ok :
    tttLargeFiber8Block6Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentPath_11_ok :
    tttLargeFiber8Block6Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentPath_12_ok :
    tttLargeFiber8Block6Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentPath_13_ok :
    tttLargeFiber8Block6Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentPath_14_ok :
    tttLargeFiber8Block6Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber8Block6Chunk0ParentPath_15_ok :
    tttLargeFiber8Block6Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber8Block6Chunk0RowsAudit : Bool :=
  tttLargeFiber8Block6Chunk0RowCheck 0
    && tttLargeFiber8Block6Chunk0RowCheck 1
    && tttLargeFiber8Block6Chunk0RowCheck 2
    && tttLargeFiber8Block6Chunk0RowCheck 3
    && tttLargeFiber8Block6Chunk0RowCheck 4
    && tttLargeFiber8Block6Chunk0RowCheck 5
    && tttLargeFiber8Block6Chunk0RowCheck 6
    && tttLargeFiber8Block6Chunk0RowCheck 7
    && tttLargeFiber8Block6Chunk0RowCheck 8
    && tttLargeFiber8Block6Chunk0RowCheck 9
    && tttLargeFiber8Block6Chunk0RowCheck 10
    && tttLargeFiber8Block6Chunk0RowCheck 11
    && tttLargeFiber8Block6Chunk0RowCheck 12
    && tttLargeFiber8Block6Chunk0RowCheck 13
    && tttLargeFiber8Block6Chunk0RowCheck 14
    && tttLargeFiber8Block6Chunk0RowCheck 15

theorem tttLargeFiber8Block6Chunk0RowsAudit_ok :
    tttLargeFiber8Block6Chunk0RowsAudit = true := by
  simp [tttLargeFiber8Block6Chunk0RowsAudit,
    tttLargeFiber8Block6Chunk0Row_0_ok,
    tttLargeFiber8Block6Chunk0Row_1_ok,
    tttLargeFiber8Block6Chunk0Row_2_ok,
    tttLargeFiber8Block6Chunk0Row_3_ok,
    tttLargeFiber8Block6Chunk0Row_4_ok,
    tttLargeFiber8Block6Chunk0Row_5_ok,
    tttLargeFiber8Block6Chunk0Row_6_ok,
    tttLargeFiber8Block6Chunk0Row_7_ok,
    tttLargeFiber8Block6Chunk0Row_8_ok,
    tttLargeFiber8Block6Chunk0Row_9_ok,
    tttLargeFiber8Block6Chunk0Row_10_ok,
    tttLargeFiber8Block6Chunk0Row_11_ok,
    tttLargeFiber8Block6Chunk0Row_12_ok,
    tttLargeFiber8Block6Chunk0Row_13_ok,
    tttLargeFiber8Block6Chunk0Row_14_ok,
    tttLargeFiber8Block6Chunk0Row_15_ok]

def tttLargeFiber8Block6Chunk0ParentMapAudit : Bool :=
  tttLargeFiber8Block6Chunk0ParentMapCheck 0
    && tttLargeFiber8Block6Chunk0ParentMapCheck 1
    && tttLargeFiber8Block6Chunk0ParentMapCheck 2
    && tttLargeFiber8Block6Chunk0ParentMapCheck 3
    && tttLargeFiber8Block6Chunk0ParentMapCheck 4
    && tttLargeFiber8Block6Chunk0ParentMapCheck 5
    && tttLargeFiber8Block6Chunk0ParentMapCheck 6
    && tttLargeFiber8Block6Chunk0ParentMapCheck 7
    && tttLargeFiber8Block6Chunk0ParentMapCheck 8
    && tttLargeFiber8Block6Chunk0ParentMapCheck 9
    && tttLargeFiber8Block6Chunk0ParentMapCheck 10
    && tttLargeFiber8Block6Chunk0ParentMapCheck 11
    && tttLargeFiber8Block6Chunk0ParentMapCheck 12
    && tttLargeFiber8Block6Chunk0ParentMapCheck 13
    && tttLargeFiber8Block6Chunk0ParentMapCheck 14
    && tttLargeFiber8Block6Chunk0ParentMapCheck 15

theorem tttLargeFiber8Block6Chunk0ParentMapAudit_ok :
    tttLargeFiber8Block6Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber8Block6Chunk0ParentMapAudit,
    tttLargeFiber8Block6Chunk0ParentMap_0_ok,
    tttLargeFiber8Block6Chunk0ParentMap_1_ok,
    tttLargeFiber8Block6Chunk0ParentMap_2_ok,
    tttLargeFiber8Block6Chunk0ParentMap_3_ok,
    tttLargeFiber8Block6Chunk0ParentMap_4_ok,
    tttLargeFiber8Block6Chunk0ParentMap_5_ok,
    tttLargeFiber8Block6Chunk0ParentMap_6_ok,
    tttLargeFiber8Block6Chunk0ParentMap_7_ok,
    tttLargeFiber8Block6Chunk0ParentMap_8_ok,
    tttLargeFiber8Block6Chunk0ParentMap_9_ok,
    tttLargeFiber8Block6Chunk0ParentMap_10_ok,
    tttLargeFiber8Block6Chunk0ParentMap_11_ok,
    tttLargeFiber8Block6Chunk0ParentMap_12_ok,
    tttLargeFiber8Block6Chunk0ParentMap_13_ok,
    tttLargeFiber8Block6Chunk0ParentMap_14_ok,
    tttLargeFiber8Block6Chunk0ParentMap_15_ok]

def tttLargeFiber8Block6Chunk0ParentsAudit : Bool :=
  tttLargeFiber8Block6Chunk0ParentPathCheck 0
    && tttLargeFiber8Block6Chunk0ParentPathCheck 1
    && tttLargeFiber8Block6Chunk0ParentPathCheck 2
    && tttLargeFiber8Block6Chunk0ParentPathCheck 3
    && tttLargeFiber8Block6Chunk0ParentPathCheck 4
    && tttLargeFiber8Block6Chunk0ParentPathCheck 5
    && tttLargeFiber8Block6Chunk0ParentPathCheck 6
    && tttLargeFiber8Block6Chunk0ParentPathCheck 7
    && tttLargeFiber8Block6Chunk0ParentPathCheck 8
    && tttLargeFiber8Block6Chunk0ParentPathCheck 9
    && tttLargeFiber8Block6Chunk0ParentPathCheck 10
    && tttLargeFiber8Block6Chunk0ParentPathCheck 11
    && tttLargeFiber8Block6Chunk0ParentPathCheck 12
    && tttLargeFiber8Block6Chunk0ParentPathCheck 13
    && tttLargeFiber8Block6Chunk0ParentPathCheck 14
    && tttLargeFiber8Block6Chunk0ParentPathCheck 15

theorem tttLargeFiber8Block6Chunk0ParentsAudit_ok :
    tttLargeFiber8Block6Chunk0ParentsAudit = true := by
  simp [tttLargeFiber8Block6Chunk0ParentsAudit,
    tttLargeFiber8Block6Chunk0ParentPath_0_ok,
    tttLargeFiber8Block6Chunk0ParentPath_1_ok,
    tttLargeFiber8Block6Chunk0ParentPath_2_ok,
    tttLargeFiber8Block6Chunk0ParentPath_3_ok,
    tttLargeFiber8Block6Chunk0ParentPath_4_ok,
    tttLargeFiber8Block6Chunk0ParentPath_5_ok,
    tttLargeFiber8Block6Chunk0ParentPath_6_ok,
    tttLargeFiber8Block6Chunk0ParentPath_7_ok,
    tttLargeFiber8Block6Chunk0ParentPath_8_ok,
    tttLargeFiber8Block6Chunk0ParentPath_9_ok,
    tttLargeFiber8Block6Chunk0ParentPath_10_ok,
    tttLargeFiber8Block6Chunk0ParentPath_11_ok,
    tttLargeFiber8Block6Chunk0ParentPath_12_ok,
    tttLargeFiber8Block6Chunk0ParentPath_13_ok,
    tttLargeFiber8Block6Chunk0ParentPath_14_ok,
    tttLargeFiber8Block6Chunk0ParentPath_15_ok]

def tttLargeFiber8Block6Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber8CountsAudit &&
    tttLargeFiber8Block6Chunk0SourcesCheck &&
    tttLargeFiber8Block6Chunk0RowsAudit &&
    tttLargeFiber8Block6Chunk0ParentMapAudit &&
    tttLargeFiber8Block6Chunk0ParentsAudit

theorem tttLargeFiber8Block6Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber8Block6Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber8Block6Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber8CountsAudit_ok,
    tttLargeFiber8Block6Chunk0SourcesCheck_ok,
    tttLargeFiber8Block6Chunk0RowsAudit_ok,
    tttLargeFiber8Block6Chunk0ParentMapAudit_ok,
    tttLargeFiber8Block6Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber8Block6Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
