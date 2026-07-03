import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 8, block 6 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber8Block6Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Data

def tttLargeFiber8Block6Chunk3Sources : List Nat :=
  [   6176, 6177, 6178, 6179, 6180, 6181, 6182, 6183,
   6184, 6185, 6186, 6187, 6188, 6189, 6190, 6191]

def tttLargeFiber8Row432 : TripleComponentParentRow :=
  tripleRow 6176 6136 182 118 64 182 65 88
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber8Row433 : TripleComponentParentRow :=
  tripleRow 6177 6137 182 118 65 182 65 89
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber8Row434 : TripleComponentParentRow :=
  tripleRow 6178 6138 182 118 66 182 65 90
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber8Row435 : TripleComponentParentRow :=
  tripleRow 6179 6139 182 118 67 182 65 91
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber8Row436 : TripleComponentParentRow :=
  tripleRow 6180 6140 182 118 116 182 65 108
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber8Row437 : TripleComponentParentRow :=
  tripleRow 6181 6141 182 118 117 182 65 109
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber8Row438 : TripleComponentParentRow :=
  tripleRow 6182 6142 182 118 118 182 65 110
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber8Row439 : TripleComponentParentRow :=
  tripleRow 6183 6143 182 118 119 182 65 111
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber8Row440 : TripleComponentParentRow :=
  tripleRow 6184 6128 182 119 72 182 64 80
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber8Row441 : TripleComponentParentRow :=
  tripleRow 6185 6129 182 119 73 182 64 81
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber8Row442 : TripleComponentParentRow :=
  tripleRow 6186 6130 182 119 74 182 64 82
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber8Row443 : TripleComponentParentRow :=
  tripleRow 6187 6131 182 119 75 182 64 83
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber8Row444 : TripleComponentParentRow :=
  tripleRow 6188 6132 182 119 124 182 64 100
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber8Row445 : TripleComponentParentRow :=
  tripleRow 6189 6133 182 119 125 182 64 101
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber8Row446 : TripleComponentParentRow :=
  tripleRow 6190 6134 182 119 126 182 64 102
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber8Row447 : TripleComponentParentRow :=
  tripleRow 6191 6135 182 119 127 182 64 103
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber8Block6Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber8Row432
  , tttLargeFiber8Row433
  , tttLargeFiber8Row434
  , tttLargeFiber8Row435
  , tttLargeFiber8Row436
  , tttLargeFiber8Row437
  , tttLargeFiber8Row438
  , tttLargeFiber8Row439
  , tttLargeFiber8Row440
  , tttLargeFiber8Row441
  , tttLargeFiber8Row442
  , tttLargeFiber8Row443
  , tttLargeFiber8Row444
  , tttLargeFiber8Row445
  , tttLargeFiber8Row446
  , tttLargeFiber8Row447
  ]

def tttLargeFiber8Block6Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (4368 <= i) && decide (i < 4624)) ||
    (decide (6000 <= i) && decide (i < 6256))

def tttLargeFiber8Block6Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber8Block6Chunk3ExpectedContains row.source &&
    tttLargeFiber8Block6Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber8Key &&
          chainInputKey tttWord t == tttLargeFiber8Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber8Block6Chunk3SourcesCheck : Bool :=
  (tttLargeFiber8Block6Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber8Block6Chunk3Sources

theorem tttLargeFiber8Block6Chunk3SourcesCheck_ok :
    tttLargeFiber8Block6Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber8Block6Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber8Block6Chunk3RowValid
    (listGetD tttLargeFiber8Block6Chunk3Rows i default)

def tttLargeFiber8Block6Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber8Block6Chunk3Rows i default
  row.parent == tttLargeFiber8ParentOf row.source

def tttLargeFiber8Block6Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber8Block6Chunk3Sources 0 0 == 6176
      && tttLargeFiber8ParentOf 6176 == 6136
      && tttLargeFiber8ParentOf 6136 == 6008
      && tttLargeFiber8ParentOf 6008 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 1 => listGetD tttLargeFiber8Block6Chunk3Sources 1 0 == 6177
      && tttLargeFiber8ParentOf 6177 == 6137
      && tttLargeFiber8ParentOf 6137 == 6009
      && tttLargeFiber8ParentOf 6009 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 2 => listGetD tttLargeFiber8Block6Chunk3Sources 2 0 == 6178
      && tttLargeFiber8ParentOf 6178 == 6138
      && tttLargeFiber8ParentOf 6138 == 6136
      && tttLargeFiber8ParentOf 6136 == 6008
      && tttLargeFiber8ParentOf 6008 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 3 => listGetD tttLargeFiber8Block6Chunk3Sources 3 0 == 6179
      && tttLargeFiber8ParentOf 6179 == 6139
      && tttLargeFiber8ParentOf 6139 == 6011
      && tttLargeFiber8ParentOf 6011 == 4379
      && tttLargeFiber8ParentOf 4379 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 4 => listGetD tttLargeFiber8Block6Chunk3Sources 4 0 == 6180
      && tttLargeFiber8ParentOf 6180 == 6140
      && tttLargeFiber8ParentOf 6140 == 6012
      && tttLargeFiber8ParentOf 6012 == 4380
      && tttLargeFiber8ParentOf 4380 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 5 => listGetD tttLargeFiber8Block6Chunk3Sources 5 0 == 6181
      && tttLargeFiber8ParentOf 6181 == 6141
      && tttLargeFiber8ParentOf 6141 == 6013
      && tttLargeFiber8ParentOf 6013 == 4381
      && tttLargeFiber8ParentOf 4381 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (6 <= tttLargeFiber8MaxParentDepth)
  | 6 => listGetD tttLargeFiber8Block6Chunk3Sources 6 0 == 6182
      && tttLargeFiber8ParentOf 6182 == 6142
      && tttLargeFiber8ParentOf 6142 == 6137
      && tttLargeFiber8ParentOf 6137 == 6009
      && tttLargeFiber8ParentOf 6009 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (6 <= tttLargeFiber8MaxParentDepth)
  | 7 => listGetD tttLargeFiber8Block6Chunk3Sources 7 0 == 6183
      && tttLargeFiber8ParentOf 6183 == 6143
      && tttLargeFiber8ParentOf 6143 == 6136
      && tttLargeFiber8ParentOf 6136 == 6008
      && tttLargeFiber8ParentOf 6008 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 8 => listGetD tttLargeFiber8Block6Chunk3Sources 8 0 == 6184
      && tttLargeFiber8ParentOf 6184 == 6128
      && tttLargeFiber8ParentOf 6128 == 6000
      && tttLargeFiber8ParentOf 6000 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 9 => listGetD tttLargeFiber8Block6Chunk3Sources 9 0 == 6185
      && tttLargeFiber8ParentOf 6185 == 6129
      && tttLargeFiber8ParentOf 6129 == 6001
      && tttLargeFiber8ParentOf 6001 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 10 => listGetD tttLargeFiber8Block6Chunk3Sources 10 0 == 6186
      && tttLargeFiber8ParentOf 6186 == 6130
      && tttLargeFiber8ParentOf 6130 == 6128
      && tttLargeFiber8ParentOf 6128 == 6000
      && tttLargeFiber8ParentOf 6000 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 11 => listGetD tttLargeFiber8Block6Chunk3Sources 11 0 == 6187
      && tttLargeFiber8ParentOf 6187 == 6131
      && tttLargeFiber8ParentOf 6131 == 6003
      && tttLargeFiber8ParentOf 6003 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 12 => listGetD tttLargeFiber8Block6Chunk3Sources 12 0 == 6188
      && tttLargeFiber8ParentOf 6188 == 6132
      && tttLargeFiber8ParentOf 6132 == 6004
      && tttLargeFiber8ParentOf 6004 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 13 => listGetD tttLargeFiber8Block6Chunk3Sources 13 0 == 6189
      && tttLargeFiber8ParentOf 6189 == 6133
      && tttLargeFiber8ParentOf 6133 == 6005
      && tttLargeFiber8ParentOf 6005 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 14 => listGetD tttLargeFiber8Block6Chunk3Sources 14 0 == 6190
      && tttLargeFiber8ParentOf 6190 == 6134
      && tttLargeFiber8ParentOf 6134 == 6129
      && tttLargeFiber8ParentOf 6129 == 6001
      && tttLargeFiber8ParentOf 6001 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 15 => listGetD tttLargeFiber8Block6Chunk3Sources 15 0 == 6191
      && tttLargeFiber8ParentOf 6191 == 6135
      && tttLargeFiber8ParentOf 6135 == 6128
      && tttLargeFiber8ParentOf 6128 == 6000
      && tttLargeFiber8ParentOf 6000 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | _ => false

theorem tttLargeFiber8Block6Chunk3Row_0_ok :
    tttLargeFiber8Block6Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3Row_1_ok :
    tttLargeFiber8Block6Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3Row_2_ok :
    tttLargeFiber8Block6Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3Row_3_ok :
    tttLargeFiber8Block6Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3Row_4_ok :
    tttLargeFiber8Block6Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3Row_5_ok :
    tttLargeFiber8Block6Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3Row_6_ok :
    tttLargeFiber8Block6Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3Row_7_ok :
    tttLargeFiber8Block6Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3Row_8_ok :
    tttLargeFiber8Block6Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3Row_9_ok :
    tttLargeFiber8Block6Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3Row_10_ok :
    tttLargeFiber8Block6Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3Row_11_ok :
    tttLargeFiber8Block6Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3Row_12_ok :
    tttLargeFiber8Block6Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3Row_13_ok :
    tttLargeFiber8Block6Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3Row_14_ok :
    tttLargeFiber8Block6Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3Row_15_ok :
    tttLargeFiber8Block6Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentMap_0_ok :
    tttLargeFiber8Block6Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentMap_1_ok :
    tttLargeFiber8Block6Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentMap_2_ok :
    tttLargeFiber8Block6Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentMap_3_ok :
    tttLargeFiber8Block6Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentMap_4_ok :
    tttLargeFiber8Block6Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentMap_5_ok :
    tttLargeFiber8Block6Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentMap_6_ok :
    tttLargeFiber8Block6Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentMap_7_ok :
    tttLargeFiber8Block6Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentMap_8_ok :
    tttLargeFiber8Block6Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentMap_9_ok :
    tttLargeFiber8Block6Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentMap_10_ok :
    tttLargeFiber8Block6Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentMap_11_ok :
    tttLargeFiber8Block6Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentMap_12_ok :
    tttLargeFiber8Block6Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentMap_13_ok :
    tttLargeFiber8Block6Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentMap_14_ok :
    tttLargeFiber8Block6Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentMap_15_ok :
    tttLargeFiber8Block6Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentPath_0_ok :
    tttLargeFiber8Block6Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentPath_1_ok :
    tttLargeFiber8Block6Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentPath_2_ok :
    tttLargeFiber8Block6Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentPath_3_ok :
    tttLargeFiber8Block6Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentPath_4_ok :
    tttLargeFiber8Block6Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentPath_5_ok :
    tttLargeFiber8Block6Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentPath_6_ok :
    tttLargeFiber8Block6Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentPath_7_ok :
    tttLargeFiber8Block6Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentPath_8_ok :
    tttLargeFiber8Block6Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentPath_9_ok :
    tttLargeFiber8Block6Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentPath_10_ok :
    tttLargeFiber8Block6Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentPath_11_ok :
    tttLargeFiber8Block6Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentPath_12_ok :
    tttLargeFiber8Block6Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentPath_13_ok :
    tttLargeFiber8Block6Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentPath_14_ok :
    tttLargeFiber8Block6Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber8Block6Chunk3ParentPath_15_ok :
    tttLargeFiber8Block6Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber8Block6Chunk3RowsAudit : Bool :=
  tttLargeFiber8Block6Chunk3RowCheck 0
    && tttLargeFiber8Block6Chunk3RowCheck 1
    && tttLargeFiber8Block6Chunk3RowCheck 2
    && tttLargeFiber8Block6Chunk3RowCheck 3
    && tttLargeFiber8Block6Chunk3RowCheck 4
    && tttLargeFiber8Block6Chunk3RowCheck 5
    && tttLargeFiber8Block6Chunk3RowCheck 6
    && tttLargeFiber8Block6Chunk3RowCheck 7
    && tttLargeFiber8Block6Chunk3RowCheck 8
    && tttLargeFiber8Block6Chunk3RowCheck 9
    && tttLargeFiber8Block6Chunk3RowCheck 10
    && tttLargeFiber8Block6Chunk3RowCheck 11
    && tttLargeFiber8Block6Chunk3RowCheck 12
    && tttLargeFiber8Block6Chunk3RowCheck 13
    && tttLargeFiber8Block6Chunk3RowCheck 14
    && tttLargeFiber8Block6Chunk3RowCheck 15

theorem tttLargeFiber8Block6Chunk3RowsAudit_ok :
    tttLargeFiber8Block6Chunk3RowsAudit = true := by
  simp [tttLargeFiber8Block6Chunk3RowsAudit,
    tttLargeFiber8Block6Chunk3Row_0_ok,
    tttLargeFiber8Block6Chunk3Row_1_ok,
    tttLargeFiber8Block6Chunk3Row_2_ok,
    tttLargeFiber8Block6Chunk3Row_3_ok,
    tttLargeFiber8Block6Chunk3Row_4_ok,
    tttLargeFiber8Block6Chunk3Row_5_ok,
    tttLargeFiber8Block6Chunk3Row_6_ok,
    tttLargeFiber8Block6Chunk3Row_7_ok,
    tttLargeFiber8Block6Chunk3Row_8_ok,
    tttLargeFiber8Block6Chunk3Row_9_ok,
    tttLargeFiber8Block6Chunk3Row_10_ok,
    tttLargeFiber8Block6Chunk3Row_11_ok,
    tttLargeFiber8Block6Chunk3Row_12_ok,
    tttLargeFiber8Block6Chunk3Row_13_ok,
    tttLargeFiber8Block6Chunk3Row_14_ok,
    tttLargeFiber8Block6Chunk3Row_15_ok]

def tttLargeFiber8Block6Chunk3ParentMapAudit : Bool :=
  tttLargeFiber8Block6Chunk3ParentMapCheck 0
    && tttLargeFiber8Block6Chunk3ParentMapCheck 1
    && tttLargeFiber8Block6Chunk3ParentMapCheck 2
    && tttLargeFiber8Block6Chunk3ParentMapCheck 3
    && tttLargeFiber8Block6Chunk3ParentMapCheck 4
    && tttLargeFiber8Block6Chunk3ParentMapCheck 5
    && tttLargeFiber8Block6Chunk3ParentMapCheck 6
    && tttLargeFiber8Block6Chunk3ParentMapCheck 7
    && tttLargeFiber8Block6Chunk3ParentMapCheck 8
    && tttLargeFiber8Block6Chunk3ParentMapCheck 9
    && tttLargeFiber8Block6Chunk3ParentMapCheck 10
    && tttLargeFiber8Block6Chunk3ParentMapCheck 11
    && tttLargeFiber8Block6Chunk3ParentMapCheck 12
    && tttLargeFiber8Block6Chunk3ParentMapCheck 13
    && tttLargeFiber8Block6Chunk3ParentMapCheck 14
    && tttLargeFiber8Block6Chunk3ParentMapCheck 15

theorem tttLargeFiber8Block6Chunk3ParentMapAudit_ok :
    tttLargeFiber8Block6Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber8Block6Chunk3ParentMapAudit,
    tttLargeFiber8Block6Chunk3ParentMap_0_ok,
    tttLargeFiber8Block6Chunk3ParentMap_1_ok,
    tttLargeFiber8Block6Chunk3ParentMap_2_ok,
    tttLargeFiber8Block6Chunk3ParentMap_3_ok,
    tttLargeFiber8Block6Chunk3ParentMap_4_ok,
    tttLargeFiber8Block6Chunk3ParentMap_5_ok,
    tttLargeFiber8Block6Chunk3ParentMap_6_ok,
    tttLargeFiber8Block6Chunk3ParentMap_7_ok,
    tttLargeFiber8Block6Chunk3ParentMap_8_ok,
    tttLargeFiber8Block6Chunk3ParentMap_9_ok,
    tttLargeFiber8Block6Chunk3ParentMap_10_ok,
    tttLargeFiber8Block6Chunk3ParentMap_11_ok,
    tttLargeFiber8Block6Chunk3ParentMap_12_ok,
    tttLargeFiber8Block6Chunk3ParentMap_13_ok,
    tttLargeFiber8Block6Chunk3ParentMap_14_ok,
    tttLargeFiber8Block6Chunk3ParentMap_15_ok]

def tttLargeFiber8Block6Chunk3ParentsAudit : Bool :=
  tttLargeFiber8Block6Chunk3ParentPathCheck 0
    && tttLargeFiber8Block6Chunk3ParentPathCheck 1
    && tttLargeFiber8Block6Chunk3ParentPathCheck 2
    && tttLargeFiber8Block6Chunk3ParentPathCheck 3
    && tttLargeFiber8Block6Chunk3ParentPathCheck 4
    && tttLargeFiber8Block6Chunk3ParentPathCheck 5
    && tttLargeFiber8Block6Chunk3ParentPathCheck 6
    && tttLargeFiber8Block6Chunk3ParentPathCheck 7
    && tttLargeFiber8Block6Chunk3ParentPathCheck 8
    && tttLargeFiber8Block6Chunk3ParentPathCheck 9
    && tttLargeFiber8Block6Chunk3ParentPathCheck 10
    && tttLargeFiber8Block6Chunk3ParentPathCheck 11
    && tttLargeFiber8Block6Chunk3ParentPathCheck 12
    && tttLargeFiber8Block6Chunk3ParentPathCheck 13
    && tttLargeFiber8Block6Chunk3ParentPathCheck 14
    && tttLargeFiber8Block6Chunk3ParentPathCheck 15

theorem tttLargeFiber8Block6Chunk3ParentsAudit_ok :
    tttLargeFiber8Block6Chunk3ParentsAudit = true := by
  simp [tttLargeFiber8Block6Chunk3ParentsAudit,
    tttLargeFiber8Block6Chunk3ParentPath_0_ok,
    tttLargeFiber8Block6Chunk3ParentPath_1_ok,
    tttLargeFiber8Block6Chunk3ParentPath_2_ok,
    tttLargeFiber8Block6Chunk3ParentPath_3_ok,
    tttLargeFiber8Block6Chunk3ParentPath_4_ok,
    tttLargeFiber8Block6Chunk3ParentPath_5_ok,
    tttLargeFiber8Block6Chunk3ParentPath_6_ok,
    tttLargeFiber8Block6Chunk3ParentPath_7_ok,
    tttLargeFiber8Block6Chunk3ParentPath_8_ok,
    tttLargeFiber8Block6Chunk3ParentPath_9_ok,
    tttLargeFiber8Block6Chunk3ParentPath_10_ok,
    tttLargeFiber8Block6Chunk3ParentPath_11_ok,
    tttLargeFiber8Block6Chunk3ParentPath_12_ok,
    tttLargeFiber8Block6Chunk3ParentPath_13_ok,
    tttLargeFiber8Block6Chunk3ParentPath_14_ok,
    tttLargeFiber8Block6Chunk3ParentPath_15_ok]

def tttLargeFiber8Block6Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber8CountsAudit &&
    tttLargeFiber8Block6Chunk3SourcesCheck &&
    tttLargeFiber8Block6Chunk3RowsAudit &&
    tttLargeFiber8Block6Chunk3ParentMapAudit &&
    tttLargeFiber8Block6Chunk3ParentsAudit

theorem tttLargeFiber8Block6Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber8Block6Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber8Block6Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber8CountsAudit_ok,
    tttLargeFiber8Block6Chunk3SourcesCheck_ok,
    tttLargeFiber8Block6Chunk3RowsAudit_ok,
    tttLargeFiber8Block6Chunk3ParentMapAudit_ok,
    tttLargeFiber8Block6Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber8Block6Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
