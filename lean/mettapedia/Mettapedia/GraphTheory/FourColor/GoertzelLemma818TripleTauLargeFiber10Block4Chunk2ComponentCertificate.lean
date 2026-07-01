import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 10, block 4 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber10Block4Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber10Data

def tttLargeFiber10Block4Chunk2Sources : List Nat :=
  [   4128, 4129, 4130, 4131, 4132, 4133, 4134, 4135,
   4136, 4137, 4138, 4139, 4140, 4141, 4142, 4143]

def tttLargeFiber10Row288 : TripleComponentParentRow :=
  tripleRow 4128 4144 124 180 132 124 182 64
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

def tttLargeFiber10Row289 : TripleComponentParentRow :=
  tripleRow 4129 4145 124 180 133 124 182 65
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

def tttLargeFiber10Row290 : TripleComponentParentRow :=
  tripleRow 4130 2598 124 180 134 74 18 34
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
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

def tttLargeFiber10Row291 : TripleComponentParentRow :=
  tripleRow 4131 2599 124 180 135 74 18 35
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
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

def tttLargeFiber10Row292 : TripleComponentParentRow :=
  tripleRow 4132 2594 124 180 180 74 18 18
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
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

def tttLargeFiber10Row293 : TripleComponentParentRow :=
  tripleRow 4133 4135 124 180 181 124 180 183
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row294 : TripleComponentParentRow :=
  tripleRow 4134 2593 124 180 182 74 18 17
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
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

def tttLargeFiber10Row295 : TripleComponentParentRow :=
  tripleRow 4135 2592 124 180 183 74 18 16
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
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

def tttLargeFiber10Row296 : TripleComponentParentRow :=
  tripleRow 4136 4152 124 181 140 124 183 72
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

def tttLargeFiber10Row297 : TripleComponentParentRow :=
  tripleRow 4137 4153 124 181 141 124 183 73
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

def tttLargeFiber10Row298 : TripleComponentParentRow :=
  tripleRow 4138 4154 124 181 142 124 183 74
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
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

def tttLargeFiber10Row299 : TripleComponentParentRow :=
  tripleRow 4139 4136 124 181 143 124 181 140
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber10Row300 : TripleComponentParentRow :=
  tripleRow 4140 4136 124 181 188 124 181 140
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber10Row301 : TripleComponentParentRow :=
  tripleRow 4141 4137 124 181 189 124 181 141
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber10Row302 : TripleComponentParentRow :=
  tripleRow 4142 4158 124 181 190 124 183 126
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber10Row303 : TripleComponentParentRow :=
  tripleRow 4143 4159 124 181 191 124 183 127
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber10Block4Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber10Row288
  , tttLargeFiber10Row289
  , tttLargeFiber10Row290
  , tttLargeFiber10Row291
  , tttLargeFiber10Row292
  , tttLargeFiber10Row293
  , tttLargeFiber10Row294
  , tttLargeFiber10Row295
  , tttLargeFiber10Row296
  , tttLargeFiber10Row297
  , tttLargeFiber10Row298
  , tttLargeFiber10Row299
  , tttLargeFiber10Row300
  , tttLargeFiber10Row301
  , tttLargeFiber10Row302
  , tttLargeFiber10Row303
  ]

def tttLargeFiber10Block4Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (2448 <= i) && decide (i < 2704)) ||
    (decide (4096 <= i) && decide (i < 4352))

def tttLargeFiber10Block4Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber10Block4Chunk2ExpectedContains row.source &&
    tttLargeFiber10Block4Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber10Key &&
          chainInputKey tttWord t == tttLargeFiber10Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber10Block4Chunk2SourcesCheck : Bool :=
  (tttLargeFiber10Block4Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber10Block4Chunk2Sources

theorem tttLargeFiber10Block4Chunk2SourcesCheck_ok :
    tttLargeFiber10Block4Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber10Block4Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber10Block4Chunk2RowValid
    (listGetD tttLargeFiber10Block4Chunk2Rows i default)

def tttLargeFiber10Block4Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber10Block4Chunk2Rows i default
  row.parent == tttLargeFiber10ParentOf row.source

def tttLargeFiber10Block4Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber10Block4Chunk2Sources 0 0 == 4128
      && tttLargeFiber10ParentOf 4128 == 4144
      && tttLargeFiber10ParentOf 4144 == 2584
      && tttLargeFiber10ParentOf 2584 == 2456
      && tttLargeFiber10ParentOf 2456 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 1 => listGetD tttLargeFiber10Block4Chunk2Sources 1 0 == 4129
      && tttLargeFiber10ParentOf 4129 == 4145
      && tttLargeFiber10ParentOf 4145 == 2585
      && tttLargeFiber10ParentOf 2585 == 2457
      && tttLargeFiber10ParentOf 2457 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 2 => listGetD tttLargeFiber10Block4Chunk2Sources 2 0 == 4130
      && tttLargeFiber10ParentOf 4130 == 2598
      && tttLargeFiber10ParentOf 2598 == 2470
      && tttLargeFiber10ParentOf 2470 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 3 => listGetD tttLargeFiber10Block4Chunk2Sources 3 0 == 4131
      && tttLargeFiber10ParentOf 4131 == 2599
      && tttLargeFiber10ParentOf 2599 == 2471
      && tttLargeFiber10ParentOf 2471 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 4 => listGetD tttLargeFiber10Block4Chunk2Sources 4 0 == 4132
      && tttLargeFiber10ParentOf 4132 == 2594
      && tttLargeFiber10ParentOf 2594 == 2466
      && tttLargeFiber10ParentOf 2466 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 5 => listGetD tttLargeFiber10Block4Chunk2Sources 5 0 == 4133
      && tttLargeFiber10ParentOf 4133 == 4135
      && tttLargeFiber10ParentOf 4135 == 2592
      && tttLargeFiber10ParentOf 2592 == 2464
      && tttLargeFiber10ParentOf 2464 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 6 => listGetD tttLargeFiber10Block4Chunk2Sources 6 0 == 4134
      && tttLargeFiber10ParentOf 4134 == 2593
      && tttLargeFiber10ParentOf 2593 == 2465
      && tttLargeFiber10ParentOf 2465 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 7 => listGetD tttLargeFiber10Block4Chunk2Sources 7 0 == 4135
      && tttLargeFiber10ParentOf 4135 == 2592
      && tttLargeFiber10ParentOf 2592 == 2464
      && tttLargeFiber10ParentOf 2464 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 8 => listGetD tttLargeFiber10Block4Chunk2Sources 8 0 == 4136
      && tttLargeFiber10ParentOf 4136 == 4152
      && tttLargeFiber10ParentOf 4152 == 2576
      && tttLargeFiber10ParentOf 2576 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (3 <= tttLargeFiber10MaxParentDepth)
  | 9 => listGetD tttLargeFiber10Block4Chunk2Sources 9 0 == 4137
      && tttLargeFiber10ParentOf 4137 == 4153
      && tttLargeFiber10ParentOf 4153 == 2577
      && tttLargeFiber10ParentOf 2577 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 10 => listGetD tttLargeFiber10Block4Chunk2Sources 10 0 == 4138
      && tttLargeFiber10ParentOf 4138 == 4154
      && tttLargeFiber10ParentOf 4154 == 2578
      && tttLargeFiber10ParentOf 2578 == 2450
      && tttLargeFiber10ParentOf 2450 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 11 => listGetD tttLargeFiber10Block4Chunk2Sources 11 0 == 4139
      && tttLargeFiber10ParentOf 4139 == 4136
      && tttLargeFiber10ParentOf 4136 == 4152
      && tttLargeFiber10ParentOf 4152 == 2576
      && tttLargeFiber10ParentOf 2576 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 12 => listGetD tttLargeFiber10Block4Chunk2Sources 12 0 == 4140
      && tttLargeFiber10ParentOf 4140 == 4136
      && tttLargeFiber10ParentOf 4136 == 4152
      && tttLargeFiber10ParentOf 4152 == 2576
      && tttLargeFiber10ParentOf 2576 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | 13 => listGetD tttLargeFiber10Block4Chunk2Sources 13 0 == 4141
      && tttLargeFiber10ParentOf 4141 == 4137
      && tttLargeFiber10ParentOf 4137 == 4153
      && tttLargeFiber10ParentOf 4153 == 2577
      && tttLargeFiber10ParentOf 2577 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 14 => listGetD tttLargeFiber10Block4Chunk2Sources 14 0 == 4142
      && tttLargeFiber10ParentOf 4142 == 4158
      && tttLargeFiber10ParentOf 4158 == 2582
      && tttLargeFiber10ParentOf 2582 == 2454
      && tttLargeFiber10ParentOf 2454 == 2449
      && tttLargeFiber10ParentOf 2449 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (5 <= tttLargeFiber10MaxParentDepth)
  | 15 => listGetD tttLargeFiber10Block4Chunk2Sources 15 0 == 4143
      && tttLargeFiber10ParentOf 4143 == 4159
      && tttLargeFiber10ParentOf 4159 == 2583
      && tttLargeFiber10ParentOf 2583 == 2455
      && tttLargeFiber10ParentOf 2455 == 2448
      && 2448 == tttLargeFiber10Root
      && decide (4 <= tttLargeFiber10MaxParentDepth)
  | _ => false

theorem tttLargeFiber10Block4Chunk2Row_0_ok :
    tttLargeFiber10Block4Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2Row_1_ok :
    tttLargeFiber10Block4Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2Row_2_ok :
    tttLargeFiber10Block4Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2Row_3_ok :
    tttLargeFiber10Block4Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2Row_4_ok :
    tttLargeFiber10Block4Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2Row_5_ok :
    tttLargeFiber10Block4Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2Row_6_ok :
    tttLargeFiber10Block4Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2Row_7_ok :
    tttLargeFiber10Block4Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2Row_8_ok :
    tttLargeFiber10Block4Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2Row_9_ok :
    tttLargeFiber10Block4Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2Row_10_ok :
    tttLargeFiber10Block4Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2Row_11_ok :
    tttLargeFiber10Block4Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2Row_12_ok :
    tttLargeFiber10Block4Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2Row_13_ok :
    tttLargeFiber10Block4Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2Row_14_ok :
    tttLargeFiber10Block4Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2Row_15_ok :
    tttLargeFiber10Block4Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentMap_0_ok :
    tttLargeFiber10Block4Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentMap_1_ok :
    tttLargeFiber10Block4Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentMap_2_ok :
    tttLargeFiber10Block4Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentMap_3_ok :
    tttLargeFiber10Block4Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentMap_4_ok :
    tttLargeFiber10Block4Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentMap_5_ok :
    tttLargeFiber10Block4Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentMap_6_ok :
    tttLargeFiber10Block4Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentMap_7_ok :
    tttLargeFiber10Block4Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentMap_8_ok :
    tttLargeFiber10Block4Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentMap_9_ok :
    tttLargeFiber10Block4Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentMap_10_ok :
    tttLargeFiber10Block4Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentMap_11_ok :
    tttLargeFiber10Block4Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentMap_12_ok :
    tttLargeFiber10Block4Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentMap_13_ok :
    tttLargeFiber10Block4Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentMap_14_ok :
    tttLargeFiber10Block4Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentMap_15_ok :
    tttLargeFiber10Block4Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentPath_0_ok :
    tttLargeFiber10Block4Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentPath_1_ok :
    tttLargeFiber10Block4Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentPath_2_ok :
    tttLargeFiber10Block4Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentPath_3_ok :
    tttLargeFiber10Block4Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentPath_4_ok :
    tttLargeFiber10Block4Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentPath_5_ok :
    tttLargeFiber10Block4Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentPath_6_ok :
    tttLargeFiber10Block4Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentPath_7_ok :
    tttLargeFiber10Block4Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentPath_8_ok :
    tttLargeFiber10Block4Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentPath_9_ok :
    tttLargeFiber10Block4Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentPath_10_ok :
    tttLargeFiber10Block4Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentPath_11_ok :
    tttLargeFiber10Block4Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentPath_12_ok :
    tttLargeFiber10Block4Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentPath_13_ok :
    tttLargeFiber10Block4Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentPath_14_ok :
    tttLargeFiber10Block4Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber10Block4Chunk2ParentPath_15_ok :
    tttLargeFiber10Block4Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber10Block4Chunk2RowsAudit : Bool :=
  tttLargeFiber10Block4Chunk2RowCheck 0
    && tttLargeFiber10Block4Chunk2RowCheck 1
    && tttLargeFiber10Block4Chunk2RowCheck 2
    && tttLargeFiber10Block4Chunk2RowCheck 3
    && tttLargeFiber10Block4Chunk2RowCheck 4
    && tttLargeFiber10Block4Chunk2RowCheck 5
    && tttLargeFiber10Block4Chunk2RowCheck 6
    && tttLargeFiber10Block4Chunk2RowCheck 7
    && tttLargeFiber10Block4Chunk2RowCheck 8
    && tttLargeFiber10Block4Chunk2RowCheck 9
    && tttLargeFiber10Block4Chunk2RowCheck 10
    && tttLargeFiber10Block4Chunk2RowCheck 11
    && tttLargeFiber10Block4Chunk2RowCheck 12
    && tttLargeFiber10Block4Chunk2RowCheck 13
    && tttLargeFiber10Block4Chunk2RowCheck 14
    && tttLargeFiber10Block4Chunk2RowCheck 15

theorem tttLargeFiber10Block4Chunk2RowsAudit_ok :
    tttLargeFiber10Block4Chunk2RowsAudit = true := by
  simp [tttLargeFiber10Block4Chunk2RowsAudit,
    tttLargeFiber10Block4Chunk2Row_0_ok,
    tttLargeFiber10Block4Chunk2Row_1_ok,
    tttLargeFiber10Block4Chunk2Row_2_ok,
    tttLargeFiber10Block4Chunk2Row_3_ok,
    tttLargeFiber10Block4Chunk2Row_4_ok,
    tttLargeFiber10Block4Chunk2Row_5_ok,
    tttLargeFiber10Block4Chunk2Row_6_ok,
    tttLargeFiber10Block4Chunk2Row_7_ok,
    tttLargeFiber10Block4Chunk2Row_8_ok,
    tttLargeFiber10Block4Chunk2Row_9_ok,
    tttLargeFiber10Block4Chunk2Row_10_ok,
    tttLargeFiber10Block4Chunk2Row_11_ok,
    tttLargeFiber10Block4Chunk2Row_12_ok,
    tttLargeFiber10Block4Chunk2Row_13_ok,
    tttLargeFiber10Block4Chunk2Row_14_ok,
    tttLargeFiber10Block4Chunk2Row_15_ok]

def tttLargeFiber10Block4Chunk2ParentMapAudit : Bool :=
  tttLargeFiber10Block4Chunk2ParentMapCheck 0
    && tttLargeFiber10Block4Chunk2ParentMapCheck 1
    && tttLargeFiber10Block4Chunk2ParentMapCheck 2
    && tttLargeFiber10Block4Chunk2ParentMapCheck 3
    && tttLargeFiber10Block4Chunk2ParentMapCheck 4
    && tttLargeFiber10Block4Chunk2ParentMapCheck 5
    && tttLargeFiber10Block4Chunk2ParentMapCheck 6
    && tttLargeFiber10Block4Chunk2ParentMapCheck 7
    && tttLargeFiber10Block4Chunk2ParentMapCheck 8
    && tttLargeFiber10Block4Chunk2ParentMapCheck 9
    && tttLargeFiber10Block4Chunk2ParentMapCheck 10
    && tttLargeFiber10Block4Chunk2ParentMapCheck 11
    && tttLargeFiber10Block4Chunk2ParentMapCheck 12
    && tttLargeFiber10Block4Chunk2ParentMapCheck 13
    && tttLargeFiber10Block4Chunk2ParentMapCheck 14
    && tttLargeFiber10Block4Chunk2ParentMapCheck 15

theorem tttLargeFiber10Block4Chunk2ParentMapAudit_ok :
    tttLargeFiber10Block4Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber10Block4Chunk2ParentMapAudit,
    tttLargeFiber10Block4Chunk2ParentMap_0_ok,
    tttLargeFiber10Block4Chunk2ParentMap_1_ok,
    tttLargeFiber10Block4Chunk2ParentMap_2_ok,
    tttLargeFiber10Block4Chunk2ParentMap_3_ok,
    tttLargeFiber10Block4Chunk2ParentMap_4_ok,
    tttLargeFiber10Block4Chunk2ParentMap_5_ok,
    tttLargeFiber10Block4Chunk2ParentMap_6_ok,
    tttLargeFiber10Block4Chunk2ParentMap_7_ok,
    tttLargeFiber10Block4Chunk2ParentMap_8_ok,
    tttLargeFiber10Block4Chunk2ParentMap_9_ok,
    tttLargeFiber10Block4Chunk2ParentMap_10_ok,
    tttLargeFiber10Block4Chunk2ParentMap_11_ok,
    tttLargeFiber10Block4Chunk2ParentMap_12_ok,
    tttLargeFiber10Block4Chunk2ParentMap_13_ok,
    tttLargeFiber10Block4Chunk2ParentMap_14_ok,
    tttLargeFiber10Block4Chunk2ParentMap_15_ok]

def tttLargeFiber10Block4Chunk2ParentsAudit : Bool :=
  tttLargeFiber10Block4Chunk2ParentPathCheck 0
    && tttLargeFiber10Block4Chunk2ParentPathCheck 1
    && tttLargeFiber10Block4Chunk2ParentPathCheck 2
    && tttLargeFiber10Block4Chunk2ParentPathCheck 3
    && tttLargeFiber10Block4Chunk2ParentPathCheck 4
    && tttLargeFiber10Block4Chunk2ParentPathCheck 5
    && tttLargeFiber10Block4Chunk2ParentPathCheck 6
    && tttLargeFiber10Block4Chunk2ParentPathCheck 7
    && tttLargeFiber10Block4Chunk2ParentPathCheck 8
    && tttLargeFiber10Block4Chunk2ParentPathCheck 9
    && tttLargeFiber10Block4Chunk2ParentPathCheck 10
    && tttLargeFiber10Block4Chunk2ParentPathCheck 11
    && tttLargeFiber10Block4Chunk2ParentPathCheck 12
    && tttLargeFiber10Block4Chunk2ParentPathCheck 13
    && tttLargeFiber10Block4Chunk2ParentPathCheck 14
    && tttLargeFiber10Block4Chunk2ParentPathCheck 15

theorem tttLargeFiber10Block4Chunk2ParentsAudit_ok :
    tttLargeFiber10Block4Chunk2ParentsAudit = true := by
  simp [tttLargeFiber10Block4Chunk2ParentsAudit,
    tttLargeFiber10Block4Chunk2ParentPath_0_ok,
    tttLargeFiber10Block4Chunk2ParentPath_1_ok,
    tttLargeFiber10Block4Chunk2ParentPath_2_ok,
    tttLargeFiber10Block4Chunk2ParentPath_3_ok,
    tttLargeFiber10Block4Chunk2ParentPath_4_ok,
    tttLargeFiber10Block4Chunk2ParentPath_5_ok,
    tttLargeFiber10Block4Chunk2ParentPath_6_ok,
    tttLargeFiber10Block4Chunk2ParentPath_7_ok,
    tttLargeFiber10Block4Chunk2ParentPath_8_ok,
    tttLargeFiber10Block4Chunk2ParentPath_9_ok,
    tttLargeFiber10Block4Chunk2ParentPath_10_ok,
    tttLargeFiber10Block4Chunk2ParentPath_11_ok,
    tttLargeFiber10Block4Chunk2ParentPath_12_ok,
    tttLargeFiber10Block4Chunk2ParentPath_13_ok,
    tttLargeFiber10Block4Chunk2ParentPath_14_ok,
    tttLargeFiber10Block4Chunk2ParentPath_15_ok]

def tttLargeFiber10Block4Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber10CountsAudit &&
    tttLargeFiber10Block4Chunk2SourcesCheck &&
    tttLargeFiber10Block4Chunk2RowsAudit &&
    tttLargeFiber10Block4Chunk2ParentMapAudit &&
    tttLargeFiber10Block4Chunk2ParentsAudit

theorem tttLargeFiber10Block4Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber10Block4Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber10Block4Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber10CountsAudit_ok,
    tttLargeFiber10Block4Chunk2SourcesCheck_ok,
    tttLargeFiber10Block4Chunk2RowsAudit_ok,
    tttLargeFiber10Block4Chunk2ParentMapAudit_ok,
    tttLargeFiber10Block4Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber10Block4Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
