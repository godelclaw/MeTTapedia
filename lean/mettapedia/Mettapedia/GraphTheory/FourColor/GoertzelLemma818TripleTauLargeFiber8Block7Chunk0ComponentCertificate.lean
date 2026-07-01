import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 8, block 7 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber8Block7Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Data

def tttLargeFiber8Block7Chunk0Sources : List Nat :=
  [   6192, 6193, 6194, 6195, 6196, 6197, 6198, 6199,
   6200, 6201, 6202, 6203, 6204, 6205, 6206, 6207]

def tttLargeFiber8Row448 : TripleComponentParentRow :=
  tripleRow 6192 6064 183 72 80 181 140 148
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber8Row449 : TripleComponentParentRow :=
  tripleRow 6193 6065 183 72 81 181 140 149
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber8Row450 : TripleComponentParentRow :=
  tripleRow 6194 6192 183 72 82 183 72 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row451 : TripleComponentParentRow :=
  tripleRow 6195 6067 183 72 83 181 140 151
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber8Row452 : TripleComponentParentRow :=
  tripleRow 6196 6068 183 72 100 181 140 164
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber8Row453 : TripleComponentParentRow :=
  tripleRow 6197 6069 183 72 101 181 140 165
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber8Row454 : TripleComponentParentRow :=
  tripleRow 6198 6193 183 72 102 183 72 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber8Row455 : TripleComponentParentRow :=
  tripleRow 6199 6192 183 72 103 183 72 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber8Row456 : TripleComponentParentRow :=
  tripleRow 6200 6072 183 73 88 181 141 156
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber8Row457 : TripleComponentParentRow :=
  tripleRow 6201 6073 183 73 89 181 141 157
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber8Row458 : TripleComponentParentRow :=
  tripleRow 6202 6200 183 73 90 183 73 88
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber8Row459 : TripleComponentParentRow :=
  tripleRow 6203 6075 183 73 91 181 141 159
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber8Row460 : TripleComponentParentRow :=
  tripleRow 6204 6076 183 73 108 181 141 172
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber8Row461 : TripleComponentParentRow :=
  tripleRow 6205 6077 183 73 109 181 141 173
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber8Row462 : TripleComponentParentRow :=
  tripleRow 6206 6201 183 73 110 183 73 89
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber8Row463 : TripleComponentParentRow :=
  tripleRow 6207 6200 183 73 111 183 73 88
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber8Block7Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber8Row448
  , tttLargeFiber8Row449
  , tttLargeFiber8Row450
  , tttLargeFiber8Row451
  , tttLargeFiber8Row452
  , tttLargeFiber8Row453
  , tttLargeFiber8Row454
  , tttLargeFiber8Row455
  , tttLargeFiber8Row456
  , tttLargeFiber8Row457
  , tttLargeFiber8Row458
  , tttLargeFiber8Row459
  , tttLargeFiber8Row460
  , tttLargeFiber8Row461
  , tttLargeFiber8Row462
  , tttLargeFiber8Row463
  ]

def tttLargeFiber8Block7Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (4368 <= i) && decide (i < 4624)) ||
    (decide (6000 <= i) && decide (i < 6256))

def tttLargeFiber8Block7Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber8Block7Chunk0ExpectedContains row.source &&
    tttLargeFiber8Block7Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber8Key &&
          chainInputKey tttWord t == tttLargeFiber8Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber8Block7Chunk0SourcesCheck : Bool :=
  (tttLargeFiber8Block7Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber8Block7Chunk0Sources

theorem tttLargeFiber8Block7Chunk0SourcesCheck_ok :
    tttLargeFiber8Block7Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber8Block7Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber8Block7Chunk0RowValid
    (listGetD tttLargeFiber8Block7Chunk0Rows i default)

def tttLargeFiber8Block7Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber8Block7Chunk0Rows i default
  row.parent == tttLargeFiber8ParentOf row.source

def tttLargeFiber8Block7Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber8Block7Chunk0Sources 0 0 == 6192
      && tttLargeFiber8ParentOf 6192 == 6064
      && tttLargeFiber8ParentOf 6064 == 4432
      && tttLargeFiber8ParentOf 4432 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (3 <= tttLargeFiber8MaxParentDepth)
  | 1 => listGetD tttLargeFiber8Block7Chunk0Sources 1 0 == 6193
      && tttLargeFiber8ParentOf 6193 == 6065
      && tttLargeFiber8ParentOf 6065 == 4433
      && tttLargeFiber8ParentOf 4433 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 2 => listGetD tttLargeFiber8Block7Chunk0Sources 2 0 == 6194
      && tttLargeFiber8ParentOf 6194 == 6192
      && tttLargeFiber8ParentOf 6192 == 6064
      && tttLargeFiber8ParentOf 6064 == 4432
      && tttLargeFiber8ParentOf 4432 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 3 => listGetD tttLargeFiber8Block7Chunk0Sources 3 0 == 6195
      && tttLargeFiber8ParentOf 6195 == 6067
      && tttLargeFiber8ParentOf 6067 == 4435
      && tttLargeFiber8ParentOf 4435 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 4 => listGetD tttLargeFiber8Block7Chunk0Sources 4 0 == 6196
      && tttLargeFiber8ParentOf 6196 == 6068
      && tttLargeFiber8ParentOf 6068 == 4436
      && tttLargeFiber8ParentOf 4436 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 5 => listGetD tttLargeFiber8Block7Chunk0Sources 5 0 == 6197
      && tttLargeFiber8ParentOf 6197 == 6069
      && tttLargeFiber8ParentOf 6069 == 4437
      && tttLargeFiber8ParentOf 4437 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 6 => listGetD tttLargeFiber8Block7Chunk0Sources 6 0 == 6198
      && tttLargeFiber8ParentOf 6198 == 6193
      && tttLargeFiber8ParentOf 6193 == 6065
      && tttLargeFiber8ParentOf 6065 == 4433
      && tttLargeFiber8ParentOf 4433 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 7 => listGetD tttLargeFiber8Block7Chunk0Sources 7 0 == 6199
      && tttLargeFiber8ParentOf 6199 == 6192
      && tttLargeFiber8ParentOf 6192 == 6064
      && tttLargeFiber8ParentOf 6064 == 4432
      && tttLargeFiber8ParentOf 4432 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 8 => listGetD tttLargeFiber8Block7Chunk0Sources 8 0 == 6200
      && tttLargeFiber8ParentOf 6200 == 6072
      && tttLargeFiber8ParentOf 6072 == 4440
      && tttLargeFiber8ParentOf 4440 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (4 <= tttLargeFiber8MaxParentDepth)
  | 9 => listGetD tttLargeFiber8Block7Chunk0Sources 9 0 == 6201
      && tttLargeFiber8ParentOf 6201 == 6073
      && tttLargeFiber8ParentOf 6073 == 4441
      && tttLargeFiber8ParentOf 4441 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 10 => listGetD tttLargeFiber8Block7Chunk0Sources 10 0 == 6202
      && tttLargeFiber8ParentOf 6202 == 6200
      && tttLargeFiber8ParentOf 6200 == 6072
      && tttLargeFiber8ParentOf 6072 == 4440
      && tttLargeFiber8ParentOf 4440 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 11 => listGetD tttLargeFiber8Block7Chunk0Sources 11 0 == 6203
      && tttLargeFiber8ParentOf 6203 == 6075
      && tttLargeFiber8ParentOf 6075 == 4443
      && tttLargeFiber8ParentOf 4443 == 4379
      && tttLargeFiber8ParentOf 4379 == 4371
      && tttLargeFiber8ParentOf 4371 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 12 => listGetD tttLargeFiber8Block7Chunk0Sources 12 0 == 6204
      && tttLargeFiber8ParentOf 6204 == 6076
      && tttLargeFiber8ParentOf 6076 == 4444
      && tttLargeFiber8ParentOf 4444 == 4380
      && tttLargeFiber8ParentOf 4380 == 4372
      && tttLargeFiber8ParentOf 4372 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | 13 => listGetD tttLargeFiber8Block7Chunk0Sources 13 0 == 6205
      && tttLargeFiber8ParentOf 6205 == 6077
      && tttLargeFiber8ParentOf 6077 == 4445
      && tttLargeFiber8ParentOf 4445 == 4381
      && tttLargeFiber8ParentOf 4381 == 4373
      && tttLargeFiber8ParentOf 4373 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (6 <= tttLargeFiber8MaxParentDepth)
  | 14 => listGetD tttLargeFiber8Block7Chunk0Sources 14 0 == 6206
      && tttLargeFiber8ParentOf 6206 == 6201
      && tttLargeFiber8ParentOf 6201 == 6073
      && tttLargeFiber8ParentOf 6073 == 4441
      && tttLargeFiber8ParentOf 4441 == 4377
      && tttLargeFiber8ParentOf 4377 == 4369
      && tttLargeFiber8ParentOf 4369 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (6 <= tttLargeFiber8MaxParentDepth)
  | 15 => listGetD tttLargeFiber8Block7Chunk0Sources 15 0 == 6207
      && tttLargeFiber8ParentOf 6207 == 6200
      && tttLargeFiber8ParentOf 6200 == 6072
      && tttLargeFiber8ParentOf 6072 == 4440
      && tttLargeFiber8ParentOf 4440 == 4376
      && tttLargeFiber8ParentOf 4376 == 4368
      && 4368 == tttLargeFiber8Root
      && decide (5 <= tttLargeFiber8MaxParentDepth)
  | _ => false

theorem tttLargeFiber8Block7Chunk0Row_0_ok :
    tttLargeFiber8Block7Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0Row_1_ok :
    tttLargeFiber8Block7Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0Row_2_ok :
    tttLargeFiber8Block7Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0Row_3_ok :
    tttLargeFiber8Block7Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0Row_4_ok :
    tttLargeFiber8Block7Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0Row_5_ok :
    tttLargeFiber8Block7Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0Row_6_ok :
    tttLargeFiber8Block7Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0Row_7_ok :
    tttLargeFiber8Block7Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0Row_8_ok :
    tttLargeFiber8Block7Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0Row_9_ok :
    tttLargeFiber8Block7Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0Row_10_ok :
    tttLargeFiber8Block7Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0Row_11_ok :
    tttLargeFiber8Block7Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0Row_12_ok :
    tttLargeFiber8Block7Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0Row_13_ok :
    tttLargeFiber8Block7Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0Row_14_ok :
    tttLargeFiber8Block7Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0Row_15_ok :
    tttLargeFiber8Block7Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentMap_0_ok :
    tttLargeFiber8Block7Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentMap_1_ok :
    tttLargeFiber8Block7Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentMap_2_ok :
    tttLargeFiber8Block7Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentMap_3_ok :
    tttLargeFiber8Block7Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentMap_4_ok :
    tttLargeFiber8Block7Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentMap_5_ok :
    tttLargeFiber8Block7Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentMap_6_ok :
    tttLargeFiber8Block7Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentMap_7_ok :
    tttLargeFiber8Block7Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentMap_8_ok :
    tttLargeFiber8Block7Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentMap_9_ok :
    tttLargeFiber8Block7Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentMap_10_ok :
    tttLargeFiber8Block7Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentMap_11_ok :
    tttLargeFiber8Block7Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentMap_12_ok :
    tttLargeFiber8Block7Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentMap_13_ok :
    tttLargeFiber8Block7Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentMap_14_ok :
    tttLargeFiber8Block7Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentMap_15_ok :
    tttLargeFiber8Block7Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentPath_0_ok :
    tttLargeFiber8Block7Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentPath_1_ok :
    tttLargeFiber8Block7Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentPath_2_ok :
    tttLargeFiber8Block7Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentPath_3_ok :
    tttLargeFiber8Block7Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentPath_4_ok :
    tttLargeFiber8Block7Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentPath_5_ok :
    tttLargeFiber8Block7Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentPath_6_ok :
    tttLargeFiber8Block7Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentPath_7_ok :
    tttLargeFiber8Block7Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentPath_8_ok :
    tttLargeFiber8Block7Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentPath_9_ok :
    tttLargeFiber8Block7Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentPath_10_ok :
    tttLargeFiber8Block7Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentPath_11_ok :
    tttLargeFiber8Block7Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentPath_12_ok :
    tttLargeFiber8Block7Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentPath_13_ok :
    tttLargeFiber8Block7Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentPath_14_ok :
    tttLargeFiber8Block7Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber8Block7Chunk0ParentPath_15_ok :
    tttLargeFiber8Block7Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber8Block7Chunk0RowsAudit : Bool :=
  tttLargeFiber8Block7Chunk0RowCheck 0
    && tttLargeFiber8Block7Chunk0RowCheck 1
    && tttLargeFiber8Block7Chunk0RowCheck 2
    && tttLargeFiber8Block7Chunk0RowCheck 3
    && tttLargeFiber8Block7Chunk0RowCheck 4
    && tttLargeFiber8Block7Chunk0RowCheck 5
    && tttLargeFiber8Block7Chunk0RowCheck 6
    && tttLargeFiber8Block7Chunk0RowCheck 7
    && tttLargeFiber8Block7Chunk0RowCheck 8
    && tttLargeFiber8Block7Chunk0RowCheck 9
    && tttLargeFiber8Block7Chunk0RowCheck 10
    && tttLargeFiber8Block7Chunk0RowCheck 11
    && tttLargeFiber8Block7Chunk0RowCheck 12
    && tttLargeFiber8Block7Chunk0RowCheck 13
    && tttLargeFiber8Block7Chunk0RowCheck 14
    && tttLargeFiber8Block7Chunk0RowCheck 15

theorem tttLargeFiber8Block7Chunk0RowsAudit_ok :
    tttLargeFiber8Block7Chunk0RowsAudit = true := by
  simp [tttLargeFiber8Block7Chunk0RowsAudit,
    tttLargeFiber8Block7Chunk0Row_0_ok,
    tttLargeFiber8Block7Chunk0Row_1_ok,
    tttLargeFiber8Block7Chunk0Row_2_ok,
    tttLargeFiber8Block7Chunk0Row_3_ok,
    tttLargeFiber8Block7Chunk0Row_4_ok,
    tttLargeFiber8Block7Chunk0Row_5_ok,
    tttLargeFiber8Block7Chunk0Row_6_ok,
    tttLargeFiber8Block7Chunk0Row_7_ok,
    tttLargeFiber8Block7Chunk0Row_8_ok,
    tttLargeFiber8Block7Chunk0Row_9_ok,
    tttLargeFiber8Block7Chunk0Row_10_ok,
    tttLargeFiber8Block7Chunk0Row_11_ok,
    tttLargeFiber8Block7Chunk0Row_12_ok,
    tttLargeFiber8Block7Chunk0Row_13_ok,
    tttLargeFiber8Block7Chunk0Row_14_ok,
    tttLargeFiber8Block7Chunk0Row_15_ok]

def tttLargeFiber8Block7Chunk0ParentMapAudit : Bool :=
  tttLargeFiber8Block7Chunk0ParentMapCheck 0
    && tttLargeFiber8Block7Chunk0ParentMapCheck 1
    && tttLargeFiber8Block7Chunk0ParentMapCheck 2
    && tttLargeFiber8Block7Chunk0ParentMapCheck 3
    && tttLargeFiber8Block7Chunk0ParentMapCheck 4
    && tttLargeFiber8Block7Chunk0ParentMapCheck 5
    && tttLargeFiber8Block7Chunk0ParentMapCheck 6
    && tttLargeFiber8Block7Chunk0ParentMapCheck 7
    && tttLargeFiber8Block7Chunk0ParentMapCheck 8
    && tttLargeFiber8Block7Chunk0ParentMapCheck 9
    && tttLargeFiber8Block7Chunk0ParentMapCheck 10
    && tttLargeFiber8Block7Chunk0ParentMapCheck 11
    && tttLargeFiber8Block7Chunk0ParentMapCheck 12
    && tttLargeFiber8Block7Chunk0ParentMapCheck 13
    && tttLargeFiber8Block7Chunk0ParentMapCheck 14
    && tttLargeFiber8Block7Chunk0ParentMapCheck 15

theorem tttLargeFiber8Block7Chunk0ParentMapAudit_ok :
    tttLargeFiber8Block7Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber8Block7Chunk0ParentMapAudit,
    tttLargeFiber8Block7Chunk0ParentMap_0_ok,
    tttLargeFiber8Block7Chunk0ParentMap_1_ok,
    tttLargeFiber8Block7Chunk0ParentMap_2_ok,
    tttLargeFiber8Block7Chunk0ParentMap_3_ok,
    tttLargeFiber8Block7Chunk0ParentMap_4_ok,
    tttLargeFiber8Block7Chunk0ParentMap_5_ok,
    tttLargeFiber8Block7Chunk0ParentMap_6_ok,
    tttLargeFiber8Block7Chunk0ParentMap_7_ok,
    tttLargeFiber8Block7Chunk0ParentMap_8_ok,
    tttLargeFiber8Block7Chunk0ParentMap_9_ok,
    tttLargeFiber8Block7Chunk0ParentMap_10_ok,
    tttLargeFiber8Block7Chunk0ParentMap_11_ok,
    tttLargeFiber8Block7Chunk0ParentMap_12_ok,
    tttLargeFiber8Block7Chunk0ParentMap_13_ok,
    tttLargeFiber8Block7Chunk0ParentMap_14_ok,
    tttLargeFiber8Block7Chunk0ParentMap_15_ok]

def tttLargeFiber8Block7Chunk0ParentsAudit : Bool :=
  tttLargeFiber8Block7Chunk0ParentPathCheck 0
    && tttLargeFiber8Block7Chunk0ParentPathCheck 1
    && tttLargeFiber8Block7Chunk0ParentPathCheck 2
    && tttLargeFiber8Block7Chunk0ParentPathCheck 3
    && tttLargeFiber8Block7Chunk0ParentPathCheck 4
    && tttLargeFiber8Block7Chunk0ParentPathCheck 5
    && tttLargeFiber8Block7Chunk0ParentPathCheck 6
    && tttLargeFiber8Block7Chunk0ParentPathCheck 7
    && tttLargeFiber8Block7Chunk0ParentPathCheck 8
    && tttLargeFiber8Block7Chunk0ParentPathCheck 9
    && tttLargeFiber8Block7Chunk0ParentPathCheck 10
    && tttLargeFiber8Block7Chunk0ParentPathCheck 11
    && tttLargeFiber8Block7Chunk0ParentPathCheck 12
    && tttLargeFiber8Block7Chunk0ParentPathCheck 13
    && tttLargeFiber8Block7Chunk0ParentPathCheck 14
    && tttLargeFiber8Block7Chunk0ParentPathCheck 15

theorem tttLargeFiber8Block7Chunk0ParentsAudit_ok :
    tttLargeFiber8Block7Chunk0ParentsAudit = true := by
  simp [tttLargeFiber8Block7Chunk0ParentsAudit,
    tttLargeFiber8Block7Chunk0ParentPath_0_ok,
    tttLargeFiber8Block7Chunk0ParentPath_1_ok,
    tttLargeFiber8Block7Chunk0ParentPath_2_ok,
    tttLargeFiber8Block7Chunk0ParentPath_3_ok,
    tttLargeFiber8Block7Chunk0ParentPath_4_ok,
    tttLargeFiber8Block7Chunk0ParentPath_5_ok,
    tttLargeFiber8Block7Chunk0ParentPath_6_ok,
    tttLargeFiber8Block7Chunk0ParentPath_7_ok,
    tttLargeFiber8Block7Chunk0ParentPath_8_ok,
    tttLargeFiber8Block7Chunk0ParentPath_9_ok,
    tttLargeFiber8Block7Chunk0ParentPath_10_ok,
    tttLargeFiber8Block7Chunk0ParentPath_11_ok,
    tttLargeFiber8Block7Chunk0ParentPath_12_ok,
    tttLargeFiber8Block7Chunk0ParentPath_13_ok,
    tttLargeFiber8Block7Chunk0ParentPath_14_ok,
    tttLargeFiber8Block7Chunk0ParentPath_15_ok]

def tttLargeFiber8Block7Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber8CountsAudit &&
    tttLargeFiber8Block7Chunk0SourcesCheck &&
    tttLargeFiber8Block7Chunk0RowsAudit &&
    tttLargeFiber8Block7Chunk0ParentMapAudit &&
    tttLargeFiber8Block7Chunk0ParentsAudit

theorem tttLargeFiber8Block7Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber8Block7Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber8Block7Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber8CountsAudit_ok,
    tttLargeFiber8Block7Chunk0SourcesCheck_ok,
    tttLargeFiber8Block7Chunk0RowsAudit_ok,
    tttLargeFiber8Block7Chunk0ParentMapAudit_ok,
    tttLargeFiber8Block7Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber8Block7Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
