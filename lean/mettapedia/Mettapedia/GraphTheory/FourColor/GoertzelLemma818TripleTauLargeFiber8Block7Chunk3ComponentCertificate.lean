import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 8, block 7 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber8Block7Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Data

def tttLargeFiber8Block7Chunk3Sources : List Nat :=
  [   6240, 6241, 6242, 6243, 6244, 6245, 6246, 6247,
   6248, 6249, 6250, 6251, 6252, 6253, 6254, 6255]

def tttLargeFiber8Row496 : TripleComponentParentRow :=
  tripleRow 6240 6224 183 126 64 183 124 132
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

def tttLargeFiber8Row497 : TripleComponentParentRow :=
  tripleRow 6241 6225 183 126 65 183 124 133
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

def tttLargeFiber8Row498 : TripleComponentParentRow :=
  tripleRow 6242 6240 183 126 66 183 126 64
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row499 : TripleComponentParentRow :=
  tripleRow 6243 6227 183 126 67 183 124 135
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

def tttLargeFiber8Row500 : TripleComponentParentRow :=
  tripleRow 6244 6228 183 126 116 183 124 180
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber8Row501 : TripleComponentParentRow :=
  tripleRow 6245 6229 183 126 117 183 124 181
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber8Row502 : TripleComponentParentRow :=
  tripleRow 6246 6241 183 126 118 183 126 65
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber8Row503 : TripleComponentParentRow :=
  tripleRow 6247 6240 183 126 119 183 126 64
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber8Row504 : TripleComponentParentRow :=
  tripleRow 6248 6232 183 127 72 183 125 140
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

def tttLargeFiber8Row505 : TripleComponentParentRow :=
  tripleRow 6249 6233 183 127 73 183 125 141
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

def tttLargeFiber8Row506 : TripleComponentParentRow :=
  tripleRow 6250 4618 183 127 74 135 59 10
    (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber8Row507 : TripleComponentParentRow :=
  tripleRow 6251 4619 183 127 75 135 59 11
    (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber8Row508 : TripleComponentParentRow :=
  tripleRow 6252 4620 183 127 124 135 59 56
    (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber8Row509 : TripleComponentParentRow :=
  tripleRow 6253 4621 183 127 125 135 59 57
    (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber8Row510 : TripleComponentParentRow :=
  tripleRow 6254 6252 183 127 126 183 127 124
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row511 : TripleComponentParentRow :=
  tripleRow 6255 4623 183 127 127 135 59 59
    (chainMove LColor.r LColor.b 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Block7Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber8Row496
  , tttLargeFiber8Row497
  , tttLargeFiber8Row498
  , tttLargeFiber8Row499
  , tttLargeFiber8Row500
  , tttLargeFiber8Row501
  , tttLargeFiber8Row502
  , tttLargeFiber8Row503
  , tttLargeFiber8Row504
  , tttLargeFiber8Row505
  , tttLargeFiber8Row506
  , tttLargeFiber8Row507
  , tttLargeFiber8Row508
  , tttLargeFiber8Row509
  , tttLargeFiber8Row510
  , tttLargeFiber8Row511
  ]

def tttLargeFiber8Block7Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (4368 <= i) && decide (i < 4624)) ||
    (decide (6000 <= i) && decide (i < 6256))

def tttLargeFiber8Block7Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber8Block7Chunk3ExpectedContains row.source &&
    tttLargeFiber8Block7Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber8Key &&
          chainInputKey tttWord t == tttLargeFiber8Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber8Block7Chunk3SourcesCheck : Bool :=
  (tttLargeFiber8Block7Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber8Block7Chunk3Sources

theorem tttLargeFiber8Block7Chunk3SourcesCheck_ok :
    tttLargeFiber8Block7Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber8Block7Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber8Block7Chunk3RowValid
    (listGetD tttLargeFiber8Block7Chunk3Rows i default)

def tttLargeFiber8Block7Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber8Block7Chunk3Rows i default
  row.parent == tttLargeFiber8ParentOf row.source

def tttLargeFiber8Block7Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber8Block7Chunk3Sources 0 0 == 6240
      && tttLargeFiber8ParentOf 6240 == 6224
      && tttLargeFiber8ParentOf 6224 == 4592
      && tttLargeFiber8ParentOf 4592 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 1 => listGetD tttLargeFiber8Block7Chunk3Sources 1 0 == 6241
      && tttLargeFiber8ParentOf 6241 == 6225
      && tttLargeFiber8ParentOf 6225 == 4593
      && tttLargeFiber8ParentOf 4593 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 2 => listGetD tttLargeFiber8Block7Chunk3Sources 2 0 == 6242
      && tttLargeFiber8ParentOf 6242 == 6240
      && tttLargeFiber8ParentOf 6240 == 6224
      && tttLargeFiber8ParentOf 6224 == 4592
      && tttLargeFiber8ParentOf 4592 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 3 => listGetD tttLargeFiber8Block7Chunk3Sources 3 0 == 6243
      && tttLargeFiber8ParentOf 6243 == 6227
      && tttLargeFiber8ParentOf 6227 == 4595
      && tttLargeFiber8ParentOf 4595 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 4 => listGetD tttLargeFiber8Block7Chunk3Sources 4 0 == 6244
      && tttLargeFiber8ParentOf 6244 == 6228
      && tttLargeFiber8ParentOf 6228 == 4596
      && tttLargeFiber8ParentOf 4596 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 5 => listGetD tttLargeFiber8Block7Chunk3Sources 5 0 == 6245
      && tttLargeFiber8ParentOf 6245 == 6229
      && tttLargeFiber8ParentOf 6229 == 4597
      && tttLargeFiber8ParentOf 4597 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 6 => listGetD tttLargeFiber8Block7Chunk3Sources 6 0 == 6246
      && tttLargeFiber8ParentOf 6246 == 6241
      && tttLargeFiber8ParentOf 6241 == 6225
      && tttLargeFiber8ParentOf 6225 == 4593
      && tttLargeFiber8ParentOf 4593 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 7 => listGetD tttLargeFiber8Block7Chunk3Sources 7 0 == 6247
      && tttLargeFiber8ParentOf 6247 == 6240
      && tttLargeFiber8ParentOf 6240 == 6224
      && tttLargeFiber8ParentOf 6224 == 4592
      && tttLargeFiber8ParentOf 4592 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 8 => listGetD tttLargeFiber8Block7Chunk3Sources 8 0 == 6248
      && tttLargeFiber8ParentOf 6248 == 6232
      && tttLargeFiber8ParentOf 6232 == 4600
      && tttLargeFiber8ParentOf 4600 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 9 => listGetD tttLargeFiber8Block7Chunk3Sources 9 0 == 6249
      && tttLargeFiber8ParentOf 6249 == 6233
      && tttLargeFiber8ParentOf 6233 == 4601
      && tttLargeFiber8ParentOf 4601 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 10 => listGetD tttLargeFiber8Block7Chunk3Sources 10 0 == 6250
      && tttLargeFiber8ParentOf 6250 == 4618
      && tttLargeFiber8ParentOf 4618 == 4394
      && tttLargeFiber8ParentOf 4394 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 11 => listGetD tttLargeFiber8Block7Chunk3Sources 11 0 == 6251
      && tttLargeFiber8ParentOf 6251 == 4619
      && tttLargeFiber8ParentOf 4619 == 4395
      && tttLargeFiber8ParentOf 4395 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 12 => listGetD tttLargeFiber8Block7Chunk3Sources 12 0 == 6252
      && tttLargeFiber8ParentOf 6252 == 4620
      && tttLargeFiber8ParentOf 4620 == 4396
      && tttLargeFiber8ParentOf 4396 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 13 => listGetD tttLargeFiber8Block7Chunk3Sources 13 0 == 6253
      && tttLargeFiber8ParentOf 6253 == 4621
      && tttLargeFiber8ParentOf 4621 == 4397
      && tttLargeFiber8ParentOf 4397 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 14 => listGetD tttLargeFiber8Block7Chunk3Sources 14 0 == 6254
      && tttLargeFiber8ParentOf 6254 == 6252
      && tttLargeFiber8ParentOf 6252 == 4620
      && tttLargeFiber8ParentOf 4620 == 4396
      && tttLargeFiber8ParentOf 4396 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 15 => listGetD tttLargeFiber8Block7Chunk3Sources 15 0 == 6255
      && tttLargeFiber8ParentOf 6255 == 4623
      && tttLargeFiber8ParentOf 4623 == 4399
      && tttLargeFiber8ParentOf 4399 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | _ => false

theorem tttLargeFiber8Block7Chunk3Row_0_ok :
    tttLargeFiber8Block7Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3Row_1_ok :
    tttLargeFiber8Block7Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3Row_2_ok :
    tttLargeFiber8Block7Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3Row_3_ok :
    tttLargeFiber8Block7Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3Row_4_ok :
    tttLargeFiber8Block7Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3Row_5_ok :
    tttLargeFiber8Block7Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3Row_6_ok :
    tttLargeFiber8Block7Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3Row_7_ok :
    tttLargeFiber8Block7Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3Row_8_ok :
    tttLargeFiber8Block7Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3Row_9_ok :
    tttLargeFiber8Block7Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3Row_10_ok :
    tttLargeFiber8Block7Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3Row_11_ok :
    tttLargeFiber8Block7Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3Row_12_ok :
    tttLargeFiber8Block7Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3Row_13_ok :
    tttLargeFiber8Block7Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3Row_14_ok :
    tttLargeFiber8Block7Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3Row_15_ok :
    tttLargeFiber8Block7Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentMap_0_ok :
    tttLargeFiber8Block7Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentMap_1_ok :
    tttLargeFiber8Block7Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentMap_2_ok :
    tttLargeFiber8Block7Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentMap_3_ok :
    tttLargeFiber8Block7Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentMap_4_ok :
    tttLargeFiber8Block7Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentMap_5_ok :
    tttLargeFiber8Block7Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentMap_6_ok :
    tttLargeFiber8Block7Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentMap_7_ok :
    tttLargeFiber8Block7Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentMap_8_ok :
    tttLargeFiber8Block7Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentMap_9_ok :
    tttLargeFiber8Block7Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentMap_10_ok :
    tttLargeFiber8Block7Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentMap_11_ok :
    tttLargeFiber8Block7Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentMap_12_ok :
    tttLargeFiber8Block7Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentMap_13_ok :
    tttLargeFiber8Block7Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentMap_14_ok :
    tttLargeFiber8Block7Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentMap_15_ok :
    tttLargeFiber8Block7Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentPath_0_ok :
    tttLargeFiber8Block7Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentPath_1_ok :
    tttLargeFiber8Block7Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentPath_2_ok :
    tttLargeFiber8Block7Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentPath_3_ok :
    tttLargeFiber8Block7Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentPath_4_ok :
    tttLargeFiber8Block7Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentPath_5_ok :
    tttLargeFiber8Block7Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentPath_6_ok :
    tttLargeFiber8Block7Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentPath_7_ok :
    tttLargeFiber8Block7Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentPath_8_ok :
    tttLargeFiber8Block7Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentPath_9_ok :
    tttLargeFiber8Block7Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentPath_10_ok :
    tttLargeFiber8Block7Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentPath_11_ok :
    tttLargeFiber8Block7Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentPath_12_ok :
    tttLargeFiber8Block7Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentPath_13_ok :
    tttLargeFiber8Block7Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentPath_14_ok :
    tttLargeFiber8Block7Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber8Block7Chunk3ParentPath_15_ok :
    tttLargeFiber8Block7Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber8Block7Chunk3RowsAudit : Bool :=
  tttLargeFiber8Block7Chunk3RowCheck 0
    && tttLargeFiber8Block7Chunk3RowCheck 1
    && tttLargeFiber8Block7Chunk3RowCheck 2
    && tttLargeFiber8Block7Chunk3RowCheck 3
    && tttLargeFiber8Block7Chunk3RowCheck 4
    && tttLargeFiber8Block7Chunk3RowCheck 5
    && tttLargeFiber8Block7Chunk3RowCheck 6
    && tttLargeFiber8Block7Chunk3RowCheck 7
    && tttLargeFiber8Block7Chunk3RowCheck 8
    && tttLargeFiber8Block7Chunk3RowCheck 9
    && tttLargeFiber8Block7Chunk3RowCheck 10
    && tttLargeFiber8Block7Chunk3RowCheck 11
    && tttLargeFiber8Block7Chunk3RowCheck 12
    && tttLargeFiber8Block7Chunk3RowCheck 13
    && tttLargeFiber8Block7Chunk3RowCheck 14
    && tttLargeFiber8Block7Chunk3RowCheck 15

theorem tttLargeFiber8Block7Chunk3RowsAudit_ok :
    tttLargeFiber8Block7Chunk3RowsAudit = true := by
  simp [tttLargeFiber8Block7Chunk3RowsAudit,
    tttLargeFiber8Block7Chunk3Row_0_ok,
    tttLargeFiber8Block7Chunk3Row_1_ok,
    tttLargeFiber8Block7Chunk3Row_2_ok,
    tttLargeFiber8Block7Chunk3Row_3_ok,
    tttLargeFiber8Block7Chunk3Row_4_ok,
    tttLargeFiber8Block7Chunk3Row_5_ok,
    tttLargeFiber8Block7Chunk3Row_6_ok,
    tttLargeFiber8Block7Chunk3Row_7_ok,
    tttLargeFiber8Block7Chunk3Row_8_ok,
    tttLargeFiber8Block7Chunk3Row_9_ok,
    tttLargeFiber8Block7Chunk3Row_10_ok,
    tttLargeFiber8Block7Chunk3Row_11_ok,
    tttLargeFiber8Block7Chunk3Row_12_ok,
    tttLargeFiber8Block7Chunk3Row_13_ok,
    tttLargeFiber8Block7Chunk3Row_14_ok,
    tttLargeFiber8Block7Chunk3Row_15_ok]

def tttLargeFiber8Block7Chunk3ParentMapAudit : Bool :=
  tttLargeFiber8Block7Chunk3ParentMapCheck 0
    && tttLargeFiber8Block7Chunk3ParentMapCheck 1
    && tttLargeFiber8Block7Chunk3ParentMapCheck 2
    && tttLargeFiber8Block7Chunk3ParentMapCheck 3
    && tttLargeFiber8Block7Chunk3ParentMapCheck 4
    && tttLargeFiber8Block7Chunk3ParentMapCheck 5
    && tttLargeFiber8Block7Chunk3ParentMapCheck 6
    && tttLargeFiber8Block7Chunk3ParentMapCheck 7
    && tttLargeFiber8Block7Chunk3ParentMapCheck 8
    && tttLargeFiber8Block7Chunk3ParentMapCheck 9
    && tttLargeFiber8Block7Chunk3ParentMapCheck 10
    && tttLargeFiber8Block7Chunk3ParentMapCheck 11
    && tttLargeFiber8Block7Chunk3ParentMapCheck 12
    && tttLargeFiber8Block7Chunk3ParentMapCheck 13
    && tttLargeFiber8Block7Chunk3ParentMapCheck 14
    && tttLargeFiber8Block7Chunk3ParentMapCheck 15

theorem tttLargeFiber8Block7Chunk3ParentMapAudit_ok :
    tttLargeFiber8Block7Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber8Block7Chunk3ParentMapAudit,
    tttLargeFiber8Block7Chunk3ParentMap_0_ok,
    tttLargeFiber8Block7Chunk3ParentMap_1_ok,
    tttLargeFiber8Block7Chunk3ParentMap_2_ok,
    tttLargeFiber8Block7Chunk3ParentMap_3_ok,
    tttLargeFiber8Block7Chunk3ParentMap_4_ok,
    tttLargeFiber8Block7Chunk3ParentMap_5_ok,
    tttLargeFiber8Block7Chunk3ParentMap_6_ok,
    tttLargeFiber8Block7Chunk3ParentMap_7_ok,
    tttLargeFiber8Block7Chunk3ParentMap_8_ok,
    tttLargeFiber8Block7Chunk3ParentMap_9_ok,
    tttLargeFiber8Block7Chunk3ParentMap_10_ok,
    tttLargeFiber8Block7Chunk3ParentMap_11_ok,
    tttLargeFiber8Block7Chunk3ParentMap_12_ok,
    tttLargeFiber8Block7Chunk3ParentMap_13_ok,
    tttLargeFiber8Block7Chunk3ParentMap_14_ok,
    tttLargeFiber8Block7Chunk3ParentMap_15_ok]

def tttLargeFiber8Block7Chunk3ParentsAudit : Bool :=
  tttLargeFiber8Block7Chunk3ParentPathCheck 0
    && tttLargeFiber8Block7Chunk3ParentPathCheck 1
    && tttLargeFiber8Block7Chunk3ParentPathCheck 2
    && tttLargeFiber8Block7Chunk3ParentPathCheck 3
    && tttLargeFiber8Block7Chunk3ParentPathCheck 4
    && tttLargeFiber8Block7Chunk3ParentPathCheck 5
    && tttLargeFiber8Block7Chunk3ParentPathCheck 6
    && tttLargeFiber8Block7Chunk3ParentPathCheck 7
    && tttLargeFiber8Block7Chunk3ParentPathCheck 8
    && tttLargeFiber8Block7Chunk3ParentPathCheck 9
    && tttLargeFiber8Block7Chunk3ParentPathCheck 10
    && tttLargeFiber8Block7Chunk3ParentPathCheck 11
    && tttLargeFiber8Block7Chunk3ParentPathCheck 12
    && tttLargeFiber8Block7Chunk3ParentPathCheck 13
    && tttLargeFiber8Block7Chunk3ParentPathCheck 14
    && tttLargeFiber8Block7Chunk3ParentPathCheck 15

theorem tttLargeFiber8Block7Chunk3ParentsAudit_ok :
    tttLargeFiber8Block7Chunk3ParentsAudit = true := by
  simp [tttLargeFiber8Block7Chunk3ParentsAudit,
    tttLargeFiber8Block7Chunk3ParentPath_0_ok,
    tttLargeFiber8Block7Chunk3ParentPath_1_ok,
    tttLargeFiber8Block7Chunk3ParentPath_2_ok,
    tttLargeFiber8Block7Chunk3ParentPath_3_ok,
    tttLargeFiber8Block7Chunk3ParentPath_4_ok,
    tttLargeFiber8Block7Chunk3ParentPath_5_ok,
    tttLargeFiber8Block7Chunk3ParentPath_6_ok,
    tttLargeFiber8Block7Chunk3ParentPath_7_ok,
    tttLargeFiber8Block7Chunk3ParentPath_8_ok,
    tttLargeFiber8Block7Chunk3ParentPath_9_ok,
    tttLargeFiber8Block7Chunk3ParentPath_10_ok,
    tttLargeFiber8Block7Chunk3ParentPath_11_ok,
    tttLargeFiber8Block7Chunk3ParentPath_12_ok,
    tttLargeFiber8Block7Chunk3ParentPath_13_ok,
    tttLargeFiber8Block7Chunk3ParentPath_14_ok,
    tttLargeFiber8Block7Chunk3ParentPath_15_ok]

def tttLargeFiber8Block7Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber8CountsAudit &&
    tttLargeFiber8Block7Chunk3SourcesCheck &&
    tttLargeFiber8Block7Chunk3RowsAudit &&
    tttLargeFiber8Block7Chunk3ParentMapAudit &&
    tttLargeFiber8Block7Chunk3ParentsAudit

theorem tttLargeFiber8Block7Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber8Block7Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber8Block7Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber8CountsAudit_ok,
    tttLargeFiber8Block7Chunk3SourcesCheck_ok,
    tttLargeFiber8Block7Chunk3RowsAudit_ok,
    tttLargeFiber8Block7Chunk3ParentMapAudit_ok,
    tttLargeFiber8Block7Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber8Block7Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
