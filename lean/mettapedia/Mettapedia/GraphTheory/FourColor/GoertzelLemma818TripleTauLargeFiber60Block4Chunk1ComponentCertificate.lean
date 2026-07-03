import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 4 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block4Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block4Chunk1Sources : List Nat :=
  [   1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111,
   1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119]

def tttLargeFiber60Row272 : TripleComponentParentRow :=
  tripleRow 1104 560 32 150 0 16 82 16
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber60Row273 : TripleComponentParentRow :=
  tripleRow 1105 561 32 150 1 16 82 17
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber60Row274 : TripleComponentParentRow :=
  tripleRow 1106 562 32 150 2 16 82 18
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber60Row275 : TripleComponentParentRow :=
  tripleRow 1107 563 32 150 3 16 82 19
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber60Row276 : TripleComponentParentRow :=
  tripleRow 1108 1096 32 150 48 32 149 156
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row277 : TripleComponentParentRow :=
  tripleRow 1109 1097 32 150 49 32 149 157
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row278 : TripleComponentParentRow :=
  tripleRow 1110 566 32 150 50 16 82 34
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber60Row279 : TripleComponentParentRow :=
  tripleRow 1111 567 32 150 51 16 82 35
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber60Row280 : TripleComponentParentRow :=
  tripleRow 1112 1095 32 151 8 32 148 167
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber60Row281 : TripleComponentParentRow :=
  tripleRow 1113 1094 32 151 9 32 148 166
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
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

def tttLargeFiber60Row282 : TripleComponentParentRow :=
  tripleRow 1114 1092 32 151 10 32 148 164
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row283 : TripleComponentParentRow :=
  tripleRow 1115 1093 32 151 11 32 148 165
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row284 : TripleComponentParentRow :=
  tripleRow 1116 1088 32 151 56 32 148 148
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row285 : TripleComponentParentRow :=
  tripleRow 1117 1089 32 151 57 32 148 149
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row286 : TripleComponentParentRow :=
  tripleRow 1118 1090 32 151 58 32 148 150
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row287 : TripleComponentParentRow :=
  tripleRow 1119 1091 32 151 59 32 148 151
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Block4Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row272
  , tttLargeFiber60Row273
  , tttLargeFiber60Row274
  , tttLargeFiber60Row275
  , tttLargeFiber60Row276
  , tttLargeFiber60Row277
  , tttLargeFiber60Row278
  , tttLargeFiber60Row279
  , tttLargeFiber60Row280
  , tttLargeFiber60Row281
  , tttLargeFiber60Row282
  , tttLargeFiber60Row283
  , tttLargeFiber60Row284
  , tttLargeFiber60Row285
  , tttLargeFiber60Row286
  , tttLargeFiber60Row287
  ]

def tttLargeFiber60Block4Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block4Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block4Chunk1ExpectedContains row.source &&
    tttLargeFiber60Block4Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block4Chunk1SourcesCheck : Bool :=
  (tttLargeFiber60Block4Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber60Block4Chunk1Sources

theorem tttLargeFiber60Block4Chunk1SourcesCheck_ok :
    tttLargeFiber60Block4Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber60Block4Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block4Chunk1RowValid
    (listGetD tttLargeFiber60Block4Chunk1Rows i default)

def tttLargeFiber60Block4Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block4Chunk1Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block4Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block4Chunk1Sources 0 0 == 1104
      && tttLargeFiber60ParentOf 1104 == 560
      && tttLargeFiber60ParentOf 560 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block4Chunk1Sources 1 0 == 1105
      && tttLargeFiber60ParentOf 1105 == 561
      && tttLargeFiber60ParentOf 561 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block4Chunk1Sources 2 0 == 1106
      && tttLargeFiber60ParentOf 1106 == 562
      && tttLargeFiber60ParentOf 562 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block4Chunk1Sources 3 0 == 1107
      && tttLargeFiber60ParentOf 1107 == 563
      && tttLargeFiber60ParentOf 563 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block4Chunk1Sources 4 0 == 1108
      && tttLargeFiber60ParentOf 1108 == 1096
      && tttLargeFiber60ParentOf 1096 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block4Chunk1Sources 5 0 == 1109
      && tttLargeFiber60ParentOf 1109 == 1097
      && tttLargeFiber60ParentOf 1097 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block4Chunk1Sources 6 0 == 1110
      && tttLargeFiber60ParentOf 1110 == 566
      && tttLargeFiber60ParentOf 566 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block4Chunk1Sources 7 0 == 1111
      && tttLargeFiber60ParentOf 1111 == 567
      && tttLargeFiber60ParentOf 567 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block4Chunk1Sources 8 0 == 1112
      && tttLargeFiber60ParentOf 1112 == 1095
      && tttLargeFiber60ParentOf 1095 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block4Chunk1Sources 9 0 == 1113
      && tttLargeFiber60ParentOf 1113 == 1094
      && tttLargeFiber60ParentOf 1094 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block4Chunk1Sources 10 0 == 1114
      && tttLargeFiber60ParentOf 1114 == 1092
      && tttLargeFiber60ParentOf 1092 == 1088
      && tttLargeFiber60ParentOf 1088 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block4Chunk1Sources 11 0 == 1115
      && tttLargeFiber60ParentOf 1115 == 1093
      && tttLargeFiber60ParentOf 1093 == 1089
      && tttLargeFiber60ParentOf 1089 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block4Chunk1Sources 12 0 == 1116
      && tttLargeFiber60ParentOf 1116 == 1088
      && tttLargeFiber60ParentOf 1088 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block4Chunk1Sources 13 0 == 1117
      && tttLargeFiber60ParentOf 1117 == 1089
      && tttLargeFiber60ParentOf 1089 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block4Chunk1Sources 14 0 == 1118
      && tttLargeFiber60ParentOf 1118 == 1090
      && tttLargeFiber60ParentOf 1090 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block4Chunk1Sources 15 0 == 1119
      && tttLargeFiber60ParentOf 1119 == 1091
      && tttLargeFiber60ParentOf 1091 == 1088
      && tttLargeFiber60ParentOf 1088 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block4Chunk1Row_0_ok :
    tttLargeFiber60Block4Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1Row_1_ok :
    tttLargeFiber60Block4Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1Row_2_ok :
    tttLargeFiber60Block4Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1Row_3_ok :
    tttLargeFiber60Block4Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1Row_4_ok :
    tttLargeFiber60Block4Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1Row_5_ok :
    tttLargeFiber60Block4Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1Row_6_ok :
    tttLargeFiber60Block4Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1Row_7_ok :
    tttLargeFiber60Block4Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1Row_8_ok :
    tttLargeFiber60Block4Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1Row_9_ok :
    tttLargeFiber60Block4Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1Row_10_ok :
    tttLargeFiber60Block4Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1Row_11_ok :
    tttLargeFiber60Block4Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1Row_12_ok :
    tttLargeFiber60Block4Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1Row_13_ok :
    tttLargeFiber60Block4Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1Row_14_ok :
    tttLargeFiber60Block4Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1Row_15_ok :
    tttLargeFiber60Block4Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentMap_0_ok :
    tttLargeFiber60Block4Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentMap_1_ok :
    tttLargeFiber60Block4Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentMap_2_ok :
    tttLargeFiber60Block4Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentMap_3_ok :
    tttLargeFiber60Block4Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentMap_4_ok :
    tttLargeFiber60Block4Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentMap_5_ok :
    tttLargeFiber60Block4Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentMap_6_ok :
    tttLargeFiber60Block4Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentMap_7_ok :
    tttLargeFiber60Block4Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentMap_8_ok :
    tttLargeFiber60Block4Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentMap_9_ok :
    tttLargeFiber60Block4Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentMap_10_ok :
    tttLargeFiber60Block4Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentMap_11_ok :
    tttLargeFiber60Block4Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentMap_12_ok :
    tttLargeFiber60Block4Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentMap_13_ok :
    tttLargeFiber60Block4Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentMap_14_ok :
    tttLargeFiber60Block4Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentMap_15_ok :
    tttLargeFiber60Block4Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentPath_0_ok :
    tttLargeFiber60Block4Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentPath_1_ok :
    tttLargeFiber60Block4Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentPath_2_ok :
    tttLargeFiber60Block4Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentPath_3_ok :
    tttLargeFiber60Block4Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentPath_4_ok :
    tttLargeFiber60Block4Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentPath_5_ok :
    tttLargeFiber60Block4Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentPath_6_ok :
    tttLargeFiber60Block4Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentPath_7_ok :
    tttLargeFiber60Block4Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentPath_8_ok :
    tttLargeFiber60Block4Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentPath_9_ok :
    tttLargeFiber60Block4Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentPath_10_ok :
    tttLargeFiber60Block4Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentPath_11_ok :
    tttLargeFiber60Block4Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentPath_12_ok :
    tttLargeFiber60Block4Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentPath_13_ok :
    tttLargeFiber60Block4Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentPath_14_ok :
    tttLargeFiber60Block4Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block4Chunk1ParentPath_15_ok :
    tttLargeFiber60Block4Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block4Chunk1RowsAudit : Bool :=
  tttLargeFiber60Block4Chunk1RowCheck 0
    && tttLargeFiber60Block4Chunk1RowCheck 1
    && tttLargeFiber60Block4Chunk1RowCheck 2
    && tttLargeFiber60Block4Chunk1RowCheck 3
    && tttLargeFiber60Block4Chunk1RowCheck 4
    && tttLargeFiber60Block4Chunk1RowCheck 5
    && tttLargeFiber60Block4Chunk1RowCheck 6
    && tttLargeFiber60Block4Chunk1RowCheck 7
    && tttLargeFiber60Block4Chunk1RowCheck 8
    && tttLargeFiber60Block4Chunk1RowCheck 9
    && tttLargeFiber60Block4Chunk1RowCheck 10
    && tttLargeFiber60Block4Chunk1RowCheck 11
    && tttLargeFiber60Block4Chunk1RowCheck 12
    && tttLargeFiber60Block4Chunk1RowCheck 13
    && tttLargeFiber60Block4Chunk1RowCheck 14
    && tttLargeFiber60Block4Chunk1RowCheck 15

theorem tttLargeFiber60Block4Chunk1RowsAudit_ok :
    tttLargeFiber60Block4Chunk1RowsAudit = true := by
  simp [tttLargeFiber60Block4Chunk1RowsAudit,
    tttLargeFiber60Block4Chunk1Row_0_ok,
    tttLargeFiber60Block4Chunk1Row_1_ok,
    tttLargeFiber60Block4Chunk1Row_2_ok,
    tttLargeFiber60Block4Chunk1Row_3_ok,
    tttLargeFiber60Block4Chunk1Row_4_ok,
    tttLargeFiber60Block4Chunk1Row_5_ok,
    tttLargeFiber60Block4Chunk1Row_6_ok,
    tttLargeFiber60Block4Chunk1Row_7_ok,
    tttLargeFiber60Block4Chunk1Row_8_ok,
    tttLargeFiber60Block4Chunk1Row_9_ok,
    tttLargeFiber60Block4Chunk1Row_10_ok,
    tttLargeFiber60Block4Chunk1Row_11_ok,
    tttLargeFiber60Block4Chunk1Row_12_ok,
    tttLargeFiber60Block4Chunk1Row_13_ok,
    tttLargeFiber60Block4Chunk1Row_14_ok,
    tttLargeFiber60Block4Chunk1Row_15_ok]

def tttLargeFiber60Block4Chunk1ParentMapAudit : Bool :=
  tttLargeFiber60Block4Chunk1ParentMapCheck 0
    && tttLargeFiber60Block4Chunk1ParentMapCheck 1
    && tttLargeFiber60Block4Chunk1ParentMapCheck 2
    && tttLargeFiber60Block4Chunk1ParentMapCheck 3
    && tttLargeFiber60Block4Chunk1ParentMapCheck 4
    && tttLargeFiber60Block4Chunk1ParentMapCheck 5
    && tttLargeFiber60Block4Chunk1ParentMapCheck 6
    && tttLargeFiber60Block4Chunk1ParentMapCheck 7
    && tttLargeFiber60Block4Chunk1ParentMapCheck 8
    && tttLargeFiber60Block4Chunk1ParentMapCheck 9
    && tttLargeFiber60Block4Chunk1ParentMapCheck 10
    && tttLargeFiber60Block4Chunk1ParentMapCheck 11
    && tttLargeFiber60Block4Chunk1ParentMapCheck 12
    && tttLargeFiber60Block4Chunk1ParentMapCheck 13
    && tttLargeFiber60Block4Chunk1ParentMapCheck 14
    && tttLargeFiber60Block4Chunk1ParentMapCheck 15

theorem tttLargeFiber60Block4Chunk1ParentMapAudit_ok :
    tttLargeFiber60Block4Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber60Block4Chunk1ParentMapAudit,
    tttLargeFiber60Block4Chunk1ParentMap_0_ok,
    tttLargeFiber60Block4Chunk1ParentMap_1_ok,
    tttLargeFiber60Block4Chunk1ParentMap_2_ok,
    tttLargeFiber60Block4Chunk1ParentMap_3_ok,
    tttLargeFiber60Block4Chunk1ParentMap_4_ok,
    tttLargeFiber60Block4Chunk1ParentMap_5_ok,
    tttLargeFiber60Block4Chunk1ParentMap_6_ok,
    tttLargeFiber60Block4Chunk1ParentMap_7_ok,
    tttLargeFiber60Block4Chunk1ParentMap_8_ok,
    tttLargeFiber60Block4Chunk1ParentMap_9_ok,
    tttLargeFiber60Block4Chunk1ParentMap_10_ok,
    tttLargeFiber60Block4Chunk1ParentMap_11_ok,
    tttLargeFiber60Block4Chunk1ParentMap_12_ok,
    tttLargeFiber60Block4Chunk1ParentMap_13_ok,
    tttLargeFiber60Block4Chunk1ParentMap_14_ok,
    tttLargeFiber60Block4Chunk1ParentMap_15_ok]

def tttLargeFiber60Block4Chunk1ParentsAudit : Bool :=
  tttLargeFiber60Block4Chunk1ParentPathCheck 0
    && tttLargeFiber60Block4Chunk1ParentPathCheck 1
    && tttLargeFiber60Block4Chunk1ParentPathCheck 2
    && tttLargeFiber60Block4Chunk1ParentPathCheck 3
    && tttLargeFiber60Block4Chunk1ParentPathCheck 4
    && tttLargeFiber60Block4Chunk1ParentPathCheck 5
    && tttLargeFiber60Block4Chunk1ParentPathCheck 6
    && tttLargeFiber60Block4Chunk1ParentPathCheck 7
    && tttLargeFiber60Block4Chunk1ParentPathCheck 8
    && tttLargeFiber60Block4Chunk1ParentPathCheck 9
    && tttLargeFiber60Block4Chunk1ParentPathCheck 10
    && tttLargeFiber60Block4Chunk1ParentPathCheck 11
    && tttLargeFiber60Block4Chunk1ParentPathCheck 12
    && tttLargeFiber60Block4Chunk1ParentPathCheck 13
    && tttLargeFiber60Block4Chunk1ParentPathCheck 14
    && tttLargeFiber60Block4Chunk1ParentPathCheck 15

theorem tttLargeFiber60Block4Chunk1ParentsAudit_ok :
    tttLargeFiber60Block4Chunk1ParentsAudit = true := by
  simp [tttLargeFiber60Block4Chunk1ParentsAudit,
    tttLargeFiber60Block4Chunk1ParentPath_0_ok,
    tttLargeFiber60Block4Chunk1ParentPath_1_ok,
    tttLargeFiber60Block4Chunk1ParentPath_2_ok,
    tttLargeFiber60Block4Chunk1ParentPath_3_ok,
    tttLargeFiber60Block4Chunk1ParentPath_4_ok,
    tttLargeFiber60Block4Chunk1ParentPath_5_ok,
    tttLargeFiber60Block4Chunk1ParentPath_6_ok,
    tttLargeFiber60Block4Chunk1ParentPath_7_ok,
    tttLargeFiber60Block4Chunk1ParentPath_8_ok,
    tttLargeFiber60Block4Chunk1ParentPath_9_ok,
    tttLargeFiber60Block4Chunk1ParentPath_10_ok,
    tttLargeFiber60Block4Chunk1ParentPath_11_ok,
    tttLargeFiber60Block4Chunk1ParentPath_12_ok,
    tttLargeFiber60Block4Chunk1ParentPath_13_ok,
    tttLargeFiber60Block4Chunk1ParentPath_14_ok,
    tttLargeFiber60Block4Chunk1ParentPath_15_ok]

def tttLargeFiber60Block4Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block4Chunk1SourcesCheck &&
    tttLargeFiber60Block4Chunk1RowsAudit &&
    tttLargeFiber60Block4Chunk1ParentMapAudit &&
    tttLargeFiber60Block4Chunk1ParentsAudit

theorem tttLargeFiber60Block4Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber60Block4Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block4Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block4Chunk1SourcesCheck_ok,
    tttLargeFiber60Block4Chunk1RowsAudit_ok,
    tttLargeFiber60Block4Chunk1ParentMapAudit_ok,
    tttLargeFiber60Block4Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block4Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
