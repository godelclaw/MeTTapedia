import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 8, block 6 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber8Block6Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Data

def tttLargeFiber8Block6Chunk1Sources : List Nat :=
  [   6144, 6145, 6146, 6147, 6148, 6149, 6150, 6151,
   6152, 6153, 6154, 6155, 6156, 6157, 6158, 6159]

def tttLargeFiber8Row400 : TripleComponentParentRow :=
  tripleRow 6144 6128 182 66 16 182 64 80
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber8Row401 : TripleComponentParentRow :=
  tripleRow 6145 6129 182 66 17 182 64 81
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber8Row402 : TripleComponentParentRow :=
  tripleRow 6146 6130 182 66 18 182 64 82
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber8Row403 : TripleComponentParentRow :=
  tripleRow 6147 6131 182 66 19 182 64 83
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber8Row404 : TripleComponentParentRow :=
  tripleRow 6148 6132 182 66 32 182 64 100
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber8Row405 : TripleComponentParentRow :=
  tripleRow 6149 6133 182 66 33 182 64 101
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber8Row406 : TripleComponentParentRow :=
  tripleRow 6150 6134 182 66 34 182 64 102
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row407 : TripleComponentParentRow :=
  tripleRow 6151 6135 182 66 35 182 64 103
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row408 : TripleComponentParentRow :=
  tripleRow 6152 6136 182 67 24 182 65 88
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber8Row409 : TripleComponentParentRow :=
  tripleRow 6153 6137 182 67 25 182 65 89
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber8Row410 : TripleComponentParentRow :=
  tripleRow 6154 6026 182 67 26 180 135 10
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber8Row411 : TripleComponentParentRow :=
  tripleRow 6155 6027 182 67 27 180 135 11
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber8Row412 : TripleComponentParentRow :=
  tripleRow 6156 6028 182 67 40 180 135 56
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber8Row413 : TripleComponentParentRow :=
  tripleRow 6157 6029 182 67 41 180 135 57
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber8Row414 : TripleComponentParentRow :=
  tripleRow 6158 6030 182 67 42 180 135 58
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber8Row415 : TripleComponentParentRow :=
  tripleRow 6159 6031 182 67 43 180 135 59
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber8Block6Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber8Row400
  , tttLargeFiber8Row401
  , tttLargeFiber8Row402
  , tttLargeFiber8Row403
  , tttLargeFiber8Row404
  , tttLargeFiber8Row405
  , tttLargeFiber8Row406
  , tttLargeFiber8Row407
  , tttLargeFiber8Row408
  , tttLargeFiber8Row409
  , tttLargeFiber8Row410
  , tttLargeFiber8Row411
  , tttLargeFiber8Row412
  , tttLargeFiber8Row413
  , tttLargeFiber8Row414
  , tttLargeFiber8Row415
  ]

def tttLargeFiber8Block6Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (4368 <= i) && decide (i < 4624)) ||
    (decide (6000 <= i) && decide (i < 6256))

def tttLargeFiber8Block6Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber8Block6Chunk1ExpectedContains row.source &&
    tttLargeFiber8Block6Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber8Key &&
          chainInputKey tttWord t == tttLargeFiber8Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber8Block6Chunk1SourcesCheck : Bool :=
  (tttLargeFiber8Block6Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber8Block6Chunk1Sources

theorem tttLargeFiber8Block6Chunk1SourcesCheck_ok :
    tttLargeFiber8Block6Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber8Block6Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber8Block6Chunk1RowValid
    (listGetD tttLargeFiber8Block6Chunk1Rows i default)

def tttLargeFiber8Block6Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber8Block6Chunk1Rows i default
  row.parent == tttLargeFiber8ParentOf row.source

def tttLargeFiber8Block6Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber8Block6Chunk1Sources 0 0 == 6144
      && tttLargeFiber8ParentOf 6144 == 6128
      && tttLargeFiber8ParentOf 6128 == 6000
      && tttLargeFiber8ParentOf 6000 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 1 => listGetD tttLargeFiber8Block6Chunk1Sources 1 0 == 6145
      && tttLargeFiber8ParentOf 6145 == 6129
      && tttLargeFiber8ParentOf 6129 == 6001
      && tttLargeFiber8ParentOf 6001 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 2 => listGetD tttLargeFiber8Block6Chunk1Sources 2 0 == 6146
      && tttLargeFiber8ParentOf 6146 == 6130
      && tttLargeFiber8ParentOf 6130 == 6128
      && tttLargeFiber8ParentOf 6128 == 6000
      && tttLargeFiber8ParentOf 6000 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 3 => listGetD tttLargeFiber8Block6Chunk1Sources 3 0 == 6147
      && tttLargeFiber8ParentOf 6147 == 6131
      && tttLargeFiber8ParentOf 6131 == 6003
      && tttLargeFiber8ParentOf 6003 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 4 => listGetD tttLargeFiber8Block6Chunk1Sources 4 0 == 6148
      && tttLargeFiber8ParentOf 6148 == 6132
      && tttLargeFiber8ParentOf 6132 == 6004
      && tttLargeFiber8ParentOf 6004 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 5 => listGetD tttLargeFiber8Block6Chunk1Sources 5 0 == 6149
      && tttLargeFiber8ParentOf 6149 == 6133
      && tttLargeFiber8ParentOf 6133 == 6005
      && tttLargeFiber8ParentOf 6005 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 6 => listGetD tttLargeFiber8Block6Chunk1Sources 6 0 == 6150
      && tttLargeFiber8ParentOf 6150 == 6134
      && tttLargeFiber8ParentOf 6134 == 6129
      && tttLargeFiber8ParentOf 6129 == 6001
      && tttLargeFiber8ParentOf 6001 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 7 => listGetD tttLargeFiber8Block6Chunk1Sources 7 0 == 6151
      && tttLargeFiber8ParentOf 6151 == 6135
      && tttLargeFiber8ParentOf 6135 == 6128
      && tttLargeFiber8ParentOf 6128 == 6000
      && tttLargeFiber8ParentOf 6000 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 8 => listGetD tttLargeFiber8Block6Chunk1Sources 8 0 == 6152
      && tttLargeFiber8ParentOf 6152 == 6136
      && tttLargeFiber8ParentOf 6136 == 6008
      && tttLargeFiber8ParentOf 6008 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 9 => listGetD tttLargeFiber8Block6Chunk1Sources 9 0 == 6153
      && tttLargeFiber8ParentOf 6153 == 6137
      && tttLargeFiber8ParentOf 6137 == 6009
      && tttLargeFiber8ParentOf 6009 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 10 => listGetD tttLargeFiber8Block6Chunk1Sources 10 0 == 6154
      && tttLargeFiber8ParentOf 6154 == 6026
      && tttLargeFiber8ParentOf 6026 == 4394
      && tttLargeFiber8ParentOf 4394 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 11 => listGetD tttLargeFiber8Block6Chunk1Sources 11 0 == 6155
      && tttLargeFiber8ParentOf 6155 == 6027
      && tttLargeFiber8ParentOf 6027 == 4395
      && tttLargeFiber8ParentOf 4395 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 12 => listGetD tttLargeFiber8Block6Chunk1Sources 12 0 == 6156
      && tttLargeFiber8ParentOf 6156 == 6028
      && tttLargeFiber8ParentOf 6028 == 4396
      && tttLargeFiber8ParentOf 4396 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 13 => listGetD tttLargeFiber8Block6Chunk1Sources 13 0 == 6157
      && tttLargeFiber8ParentOf 6157 == 6029
      && tttLargeFiber8ParentOf 6029 == 4397
      && tttLargeFiber8ParentOf 4397 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 14 => listGetD tttLargeFiber8Block6Chunk1Sources 14 0 == 6158
      && tttLargeFiber8ParentOf 6158 == 6030
      && tttLargeFiber8ParentOf 6030 == 4398
      && tttLargeFiber8ParentOf 4398 == 4370
      && tttLargeFiber8ParentOf 4370 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 15 => listGetD tttLargeFiber8Block6Chunk1Sources 15 0 == 6159
      && tttLargeFiber8ParentOf 6159 == 6031
      && tttLargeFiber8ParentOf 6031 == 4399
      && tttLargeFiber8ParentOf 4399 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | _ => false

theorem tttLargeFiber8Block6Chunk1Row_0_ok :
    tttLargeFiber8Block6Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1Row_1_ok :
    tttLargeFiber8Block6Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1Row_2_ok :
    tttLargeFiber8Block6Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1Row_3_ok :
    tttLargeFiber8Block6Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1Row_4_ok :
    tttLargeFiber8Block6Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1Row_5_ok :
    tttLargeFiber8Block6Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1Row_6_ok :
    tttLargeFiber8Block6Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1Row_7_ok :
    tttLargeFiber8Block6Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1Row_8_ok :
    tttLargeFiber8Block6Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1Row_9_ok :
    tttLargeFiber8Block6Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1Row_10_ok :
    tttLargeFiber8Block6Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1Row_11_ok :
    tttLargeFiber8Block6Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1Row_12_ok :
    tttLargeFiber8Block6Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1Row_13_ok :
    tttLargeFiber8Block6Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1Row_14_ok :
    tttLargeFiber8Block6Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1Row_15_ok :
    tttLargeFiber8Block6Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentMap_0_ok :
    tttLargeFiber8Block6Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentMap_1_ok :
    tttLargeFiber8Block6Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentMap_2_ok :
    tttLargeFiber8Block6Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentMap_3_ok :
    tttLargeFiber8Block6Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentMap_4_ok :
    tttLargeFiber8Block6Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentMap_5_ok :
    tttLargeFiber8Block6Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentMap_6_ok :
    tttLargeFiber8Block6Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentMap_7_ok :
    tttLargeFiber8Block6Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentMap_8_ok :
    tttLargeFiber8Block6Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentMap_9_ok :
    tttLargeFiber8Block6Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentMap_10_ok :
    tttLargeFiber8Block6Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentMap_11_ok :
    tttLargeFiber8Block6Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentMap_12_ok :
    tttLargeFiber8Block6Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentMap_13_ok :
    tttLargeFiber8Block6Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentMap_14_ok :
    tttLargeFiber8Block6Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentMap_15_ok :
    tttLargeFiber8Block6Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentPath_0_ok :
    tttLargeFiber8Block6Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentPath_1_ok :
    tttLargeFiber8Block6Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentPath_2_ok :
    tttLargeFiber8Block6Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentPath_3_ok :
    tttLargeFiber8Block6Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentPath_4_ok :
    tttLargeFiber8Block6Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentPath_5_ok :
    tttLargeFiber8Block6Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentPath_6_ok :
    tttLargeFiber8Block6Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentPath_7_ok :
    tttLargeFiber8Block6Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentPath_8_ok :
    tttLargeFiber8Block6Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentPath_9_ok :
    tttLargeFiber8Block6Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentPath_10_ok :
    tttLargeFiber8Block6Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentPath_11_ok :
    tttLargeFiber8Block6Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentPath_12_ok :
    tttLargeFiber8Block6Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentPath_13_ok :
    tttLargeFiber8Block6Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentPath_14_ok :
    tttLargeFiber8Block6Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber8Block6Chunk1ParentPath_15_ok :
    tttLargeFiber8Block6Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber8Block6Chunk1RowsAudit : Bool :=
  tttLargeFiber8Block6Chunk1RowCheck 0
    && tttLargeFiber8Block6Chunk1RowCheck 1
    && tttLargeFiber8Block6Chunk1RowCheck 2
    && tttLargeFiber8Block6Chunk1RowCheck 3
    && tttLargeFiber8Block6Chunk1RowCheck 4
    && tttLargeFiber8Block6Chunk1RowCheck 5
    && tttLargeFiber8Block6Chunk1RowCheck 6
    && tttLargeFiber8Block6Chunk1RowCheck 7
    && tttLargeFiber8Block6Chunk1RowCheck 8
    && tttLargeFiber8Block6Chunk1RowCheck 9
    && tttLargeFiber8Block6Chunk1RowCheck 10
    && tttLargeFiber8Block6Chunk1RowCheck 11
    && tttLargeFiber8Block6Chunk1RowCheck 12
    && tttLargeFiber8Block6Chunk1RowCheck 13
    && tttLargeFiber8Block6Chunk1RowCheck 14
    && tttLargeFiber8Block6Chunk1RowCheck 15

theorem tttLargeFiber8Block6Chunk1RowsAudit_ok :
    tttLargeFiber8Block6Chunk1RowsAudit = true := by
  simp [tttLargeFiber8Block6Chunk1RowsAudit,
    tttLargeFiber8Block6Chunk1Row_0_ok,
    tttLargeFiber8Block6Chunk1Row_1_ok,
    tttLargeFiber8Block6Chunk1Row_2_ok,
    tttLargeFiber8Block6Chunk1Row_3_ok,
    tttLargeFiber8Block6Chunk1Row_4_ok,
    tttLargeFiber8Block6Chunk1Row_5_ok,
    tttLargeFiber8Block6Chunk1Row_6_ok,
    tttLargeFiber8Block6Chunk1Row_7_ok,
    tttLargeFiber8Block6Chunk1Row_8_ok,
    tttLargeFiber8Block6Chunk1Row_9_ok,
    tttLargeFiber8Block6Chunk1Row_10_ok,
    tttLargeFiber8Block6Chunk1Row_11_ok,
    tttLargeFiber8Block6Chunk1Row_12_ok,
    tttLargeFiber8Block6Chunk1Row_13_ok,
    tttLargeFiber8Block6Chunk1Row_14_ok,
    tttLargeFiber8Block6Chunk1Row_15_ok]

def tttLargeFiber8Block6Chunk1ParentMapAudit : Bool :=
  tttLargeFiber8Block6Chunk1ParentMapCheck 0
    && tttLargeFiber8Block6Chunk1ParentMapCheck 1
    && tttLargeFiber8Block6Chunk1ParentMapCheck 2
    && tttLargeFiber8Block6Chunk1ParentMapCheck 3
    && tttLargeFiber8Block6Chunk1ParentMapCheck 4
    && tttLargeFiber8Block6Chunk1ParentMapCheck 5
    && tttLargeFiber8Block6Chunk1ParentMapCheck 6
    && tttLargeFiber8Block6Chunk1ParentMapCheck 7
    && tttLargeFiber8Block6Chunk1ParentMapCheck 8
    && tttLargeFiber8Block6Chunk1ParentMapCheck 9
    && tttLargeFiber8Block6Chunk1ParentMapCheck 10
    && tttLargeFiber8Block6Chunk1ParentMapCheck 11
    && tttLargeFiber8Block6Chunk1ParentMapCheck 12
    && tttLargeFiber8Block6Chunk1ParentMapCheck 13
    && tttLargeFiber8Block6Chunk1ParentMapCheck 14
    && tttLargeFiber8Block6Chunk1ParentMapCheck 15

theorem tttLargeFiber8Block6Chunk1ParentMapAudit_ok :
    tttLargeFiber8Block6Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber8Block6Chunk1ParentMapAudit,
    tttLargeFiber8Block6Chunk1ParentMap_0_ok,
    tttLargeFiber8Block6Chunk1ParentMap_1_ok,
    tttLargeFiber8Block6Chunk1ParentMap_2_ok,
    tttLargeFiber8Block6Chunk1ParentMap_3_ok,
    tttLargeFiber8Block6Chunk1ParentMap_4_ok,
    tttLargeFiber8Block6Chunk1ParentMap_5_ok,
    tttLargeFiber8Block6Chunk1ParentMap_6_ok,
    tttLargeFiber8Block6Chunk1ParentMap_7_ok,
    tttLargeFiber8Block6Chunk1ParentMap_8_ok,
    tttLargeFiber8Block6Chunk1ParentMap_9_ok,
    tttLargeFiber8Block6Chunk1ParentMap_10_ok,
    tttLargeFiber8Block6Chunk1ParentMap_11_ok,
    tttLargeFiber8Block6Chunk1ParentMap_12_ok,
    tttLargeFiber8Block6Chunk1ParentMap_13_ok,
    tttLargeFiber8Block6Chunk1ParentMap_14_ok,
    tttLargeFiber8Block6Chunk1ParentMap_15_ok]

def tttLargeFiber8Block6Chunk1ParentsAudit : Bool :=
  tttLargeFiber8Block6Chunk1ParentPathCheck 0
    && tttLargeFiber8Block6Chunk1ParentPathCheck 1
    && tttLargeFiber8Block6Chunk1ParentPathCheck 2
    && tttLargeFiber8Block6Chunk1ParentPathCheck 3
    && tttLargeFiber8Block6Chunk1ParentPathCheck 4
    && tttLargeFiber8Block6Chunk1ParentPathCheck 5
    && tttLargeFiber8Block6Chunk1ParentPathCheck 6
    && tttLargeFiber8Block6Chunk1ParentPathCheck 7
    && tttLargeFiber8Block6Chunk1ParentPathCheck 8
    && tttLargeFiber8Block6Chunk1ParentPathCheck 9
    && tttLargeFiber8Block6Chunk1ParentPathCheck 10
    && tttLargeFiber8Block6Chunk1ParentPathCheck 11
    && tttLargeFiber8Block6Chunk1ParentPathCheck 12
    && tttLargeFiber8Block6Chunk1ParentPathCheck 13
    && tttLargeFiber8Block6Chunk1ParentPathCheck 14
    && tttLargeFiber8Block6Chunk1ParentPathCheck 15

theorem tttLargeFiber8Block6Chunk1ParentsAudit_ok :
    tttLargeFiber8Block6Chunk1ParentsAudit = true := by
  simp [tttLargeFiber8Block6Chunk1ParentsAudit,
    tttLargeFiber8Block6Chunk1ParentPath_0_ok,
    tttLargeFiber8Block6Chunk1ParentPath_1_ok,
    tttLargeFiber8Block6Chunk1ParentPath_2_ok,
    tttLargeFiber8Block6Chunk1ParentPath_3_ok,
    tttLargeFiber8Block6Chunk1ParentPath_4_ok,
    tttLargeFiber8Block6Chunk1ParentPath_5_ok,
    tttLargeFiber8Block6Chunk1ParentPath_6_ok,
    tttLargeFiber8Block6Chunk1ParentPath_7_ok,
    tttLargeFiber8Block6Chunk1ParentPath_8_ok,
    tttLargeFiber8Block6Chunk1ParentPath_9_ok,
    tttLargeFiber8Block6Chunk1ParentPath_10_ok,
    tttLargeFiber8Block6Chunk1ParentPath_11_ok,
    tttLargeFiber8Block6Chunk1ParentPath_12_ok,
    tttLargeFiber8Block6Chunk1ParentPath_13_ok,
    tttLargeFiber8Block6Chunk1ParentPath_14_ok,
    tttLargeFiber8Block6Chunk1ParentPath_15_ok]

def tttLargeFiber8Block6Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber8CountsAudit &&
    tttLargeFiber8Block6Chunk1SourcesCheck &&
    tttLargeFiber8Block6Chunk1RowsAudit &&
    tttLargeFiber8Block6Chunk1ParentMapAudit &&
    tttLargeFiber8Block6Chunk1ParentsAudit

theorem tttLargeFiber8Block6Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber8Block6Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber8Block6Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber8CountsAudit_ok,
    tttLargeFiber8Block6Chunk1SourcesCheck_ok,
    tttLargeFiber8Block6Chunk1RowsAudit_ok,
    tttLargeFiber8Block6Chunk1ParentMapAudit_ok,
    tttLargeFiber8Block6Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber8Block6Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
