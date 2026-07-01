import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 4 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block4Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block4Chunk3Sources : List Nat :=
  [   1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143,
   1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151]

def tttLargeFiber60Row304 : TripleComponentParentRow :=
  tripleRow 1136 592 32 166 64 16 102 64
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row305 : TripleComponentParentRow :=
  tripleRow 1137 593 32 166 65 16 102 65
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row306 : TripleComponentParentRow :=
  tripleRow 1138 594 32 166 66 16 102 66
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row307 : TripleComponentParentRow :=
  tripleRow 1139 1123 32 166 67 32 164 135
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

def tttLargeFiber60Row308 : TripleComponentParentRow :=
  tripleRow 1140 1108 32 166 116 32 150 48
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

def tttLargeFiber60Row309 : TripleComponentParentRow :=
  tripleRow 1141 1109 32 166 117 32 150 49
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

def tttLargeFiber60Row310 : TripleComponentParentRow :=
  tripleRow 1142 598 32 166 118 16 102 118
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row311 : TripleComponentParentRow :=
  tripleRow 1143 599 32 166 119 16 102 119
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row312 : TripleComponentParentRow :=
  tripleRow 1144 600 32 167 72 16 103 72
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row313 : TripleComponentParentRow :=
  tripleRow 1145 601 32 167 73 16 103 73
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row314 : TripleComponentParentRow :=
  tripleRow 1146 602 32 167 74 16 103 74
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row315 : TripleComponentParentRow :=
  tripleRow 1147 603 32 167 75 16 103 75
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row316 : TripleComponentParentRow :=
  tripleRow 1148 1116 32 167 124 32 151 56
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

def tttLargeFiber60Row317 : TripleComponentParentRow :=
  tripleRow 1149 1117 32 167 125 32 151 57
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

def tttLargeFiber60Row318 : TripleComponentParentRow :=
  tripleRow 1150 606 32 167 126 16 103 126
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row319 : TripleComponentParentRow :=
  tripleRow 1151 607 32 167 127 16 103 127
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Block4Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row304
  , tttLargeFiber60Row305
  , tttLargeFiber60Row306
  , tttLargeFiber60Row307
  , tttLargeFiber60Row308
  , tttLargeFiber60Row309
  , tttLargeFiber60Row310
  , tttLargeFiber60Row311
  , tttLargeFiber60Row312
  , tttLargeFiber60Row313
  , tttLargeFiber60Row314
  , tttLargeFiber60Row315
  , tttLargeFiber60Row316
  , tttLargeFiber60Row317
  , tttLargeFiber60Row318
  , tttLargeFiber60Row319
  ]

def tttLargeFiber60Block4Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block4Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block4Chunk3ExpectedContains row.source &&
    tttLargeFiber60Block4Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block4Chunk3SourcesCheck : Bool :=
  (tttLargeFiber60Block4Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber60Block4Chunk3Sources

theorem tttLargeFiber60Block4Chunk3SourcesCheck_ok :
    tttLargeFiber60Block4Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber60Block4Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block4Chunk3RowValid
    (listGetD tttLargeFiber60Block4Chunk3Rows i default)

def tttLargeFiber60Block4Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block4Chunk3Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block4Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block4Chunk3Sources 0 0 == 1136
      && tttLargeFiber60ParentOf 1136 == 592
      && tttLargeFiber60ParentOf 592 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block4Chunk3Sources 1 0 == 1137
      && tttLargeFiber60ParentOf 1137 == 593
      && tttLargeFiber60ParentOf 593 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block4Chunk3Sources 2 0 == 1138
      && tttLargeFiber60ParentOf 1138 == 594
      && tttLargeFiber60ParentOf 594 == 554
      && tttLargeFiber60ParentOf 554 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block4Chunk3Sources 3 0 == 1139
      && tttLargeFiber60ParentOf 1139 == 1123
      && tttLargeFiber60ParentOf 1123 == 1091
      && tttLargeFiber60ParentOf 1091 == 1088
      && tttLargeFiber60ParentOf 1088 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block4Chunk3Sources 4 0 == 1140
      && tttLargeFiber60ParentOf 1140 == 1108
      && tttLargeFiber60ParentOf 1108 == 1096
      && tttLargeFiber60ParentOf 1096 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block4Chunk3Sources 5 0 == 1141
      && tttLargeFiber60ParentOf 1141 == 1109
      && tttLargeFiber60ParentOf 1109 == 1097
      && tttLargeFiber60ParentOf 1097 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block4Chunk3Sources 6 0 == 1142
      && tttLargeFiber60ParentOf 1142 == 598
      && tttLargeFiber60ParentOf 598 == 558
      && tttLargeFiber60ParentOf 558 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block4Chunk3Sources 7 0 == 1143
      && tttLargeFiber60ParentOf 1143 == 599
      && tttLargeFiber60ParentOf 599 == 559
      && tttLargeFiber60ParentOf 559 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block4Chunk3Sources 8 0 == 1144
      && tttLargeFiber60ParentOf 1144 == 600
      && tttLargeFiber60ParentOf 600 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block4Chunk3Sources 9 0 == 1145
      && tttLargeFiber60ParentOf 1145 == 601
      && tttLargeFiber60ParentOf 601 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block4Chunk3Sources 10 0 == 1146
      && tttLargeFiber60ParentOf 1146 == 602
      && tttLargeFiber60ParentOf 602 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block4Chunk3Sources 11 0 == 1147
      && tttLargeFiber60ParentOf 1147 == 603
      && tttLargeFiber60ParentOf 603 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block4Chunk3Sources 12 0 == 1148
      && tttLargeFiber60ParentOf 1148 == 1116
      && tttLargeFiber60ParentOf 1116 == 1088
      && tttLargeFiber60ParentOf 1088 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block4Chunk3Sources 13 0 == 1149
      && tttLargeFiber60ParentOf 1149 == 1117
      && tttLargeFiber60ParentOf 1117 == 1089
      && tttLargeFiber60ParentOf 1089 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block4Chunk3Sources 14 0 == 1150
      && tttLargeFiber60ParentOf 1150 == 606
      && tttLargeFiber60ParentOf 606 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block4Chunk3Sources 15 0 == 1151
      && tttLargeFiber60ParentOf 1151 == 607
      && tttLargeFiber60ParentOf 607 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block4Chunk3Row_0_ok :
    tttLargeFiber60Block4Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3Row_1_ok :
    tttLargeFiber60Block4Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3Row_2_ok :
    tttLargeFiber60Block4Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3Row_3_ok :
    tttLargeFiber60Block4Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3Row_4_ok :
    tttLargeFiber60Block4Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3Row_5_ok :
    tttLargeFiber60Block4Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3Row_6_ok :
    tttLargeFiber60Block4Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3Row_7_ok :
    tttLargeFiber60Block4Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3Row_8_ok :
    tttLargeFiber60Block4Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3Row_9_ok :
    tttLargeFiber60Block4Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3Row_10_ok :
    tttLargeFiber60Block4Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3Row_11_ok :
    tttLargeFiber60Block4Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3Row_12_ok :
    tttLargeFiber60Block4Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3Row_13_ok :
    tttLargeFiber60Block4Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3Row_14_ok :
    tttLargeFiber60Block4Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3Row_15_ok :
    tttLargeFiber60Block4Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentMap_0_ok :
    tttLargeFiber60Block4Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentMap_1_ok :
    tttLargeFiber60Block4Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentMap_2_ok :
    tttLargeFiber60Block4Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentMap_3_ok :
    tttLargeFiber60Block4Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentMap_4_ok :
    tttLargeFiber60Block4Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentMap_5_ok :
    tttLargeFiber60Block4Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentMap_6_ok :
    tttLargeFiber60Block4Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentMap_7_ok :
    tttLargeFiber60Block4Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentMap_8_ok :
    tttLargeFiber60Block4Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentMap_9_ok :
    tttLargeFiber60Block4Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentMap_10_ok :
    tttLargeFiber60Block4Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentMap_11_ok :
    tttLargeFiber60Block4Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentMap_12_ok :
    tttLargeFiber60Block4Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentMap_13_ok :
    tttLargeFiber60Block4Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentMap_14_ok :
    tttLargeFiber60Block4Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentMap_15_ok :
    tttLargeFiber60Block4Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentPath_0_ok :
    tttLargeFiber60Block4Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentPath_1_ok :
    tttLargeFiber60Block4Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentPath_2_ok :
    tttLargeFiber60Block4Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentPath_3_ok :
    tttLargeFiber60Block4Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentPath_4_ok :
    tttLargeFiber60Block4Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentPath_5_ok :
    tttLargeFiber60Block4Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentPath_6_ok :
    tttLargeFiber60Block4Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentPath_7_ok :
    tttLargeFiber60Block4Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentPath_8_ok :
    tttLargeFiber60Block4Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentPath_9_ok :
    tttLargeFiber60Block4Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentPath_10_ok :
    tttLargeFiber60Block4Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentPath_11_ok :
    tttLargeFiber60Block4Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentPath_12_ok :
    tttLargeFiber60Block4Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentPath_13_ok :
    tttLargeFiber60Block4Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentPath_14_ok :
    tttLargeFiber60Block4Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block4Chunk3ParentPath_15_ok :
    tttLargeFiber60Block4Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block4Chunk3RowsAudit : Bool :=
  tttLargeFiber60Block4Chunk3RowCheck 0
    && tttLargeFiber60Block4Chunk3RowCheck 1
    && tttLargeFiber60Block4Chunk3RowCheck 2
    && tttLargeFiber60Block4Chunk3RowCheck 3
    && tttLargeFiber60Block4Chunk3RowCheck 4
    && tttLargeFiber60Block4Chunk3RowCheck 5
    && tttLargeFiber60Block4Chunk3RowCheck 6
    && tttLargeFiber60Block4Chunk3RowCheck 7
    && tttLargeFiber60Block4Chunk3RowCheck 8
    && tttLargeFiber60Block4Chunk3RowCheck 9
    && tttLargeFiber60Block4Chunk3RowCheck 10
    && tttLargeFiber60Block4Chunk3RowCheck 11
    && tttLargeFiber60Block4Chunk3RowCheck 12
    && tttLargeFiber60Block4Chunk3RowCheck 13
    && tttLargeFiber60Block4Chunk3RowCheck 14
    && tttLargeFiber60Block4Chunk3RowCheck 15

theorem tttLargeFiber60Block4Chunk3RowsAudit_ok :
    tttLargeFiber60Block4Chunk3RowsAudit = true := by
  simp [tttLargeFiber60Block4Chunk3RowsAudit,
    tttLargeFiber60Block4Chunk3Row_0_ok,
    tttLargeFiber60Block4Chunk3Row_1_ok,
    tttLargeFiber60Block4Chunk3Row_2_ok,
    tttLargeFiber60Block4Chunk3Row_3_ok,
    tttLargeFiber60Block4Chunk3Row_4_ok,
    tttLargeFiber60Block4Chunk3Row_5_ok,
    tttLargeFiber60Block4Chunk3Row_6_ok,
    tttLargeFiber60Block4Chunk3Row_7_ok,
    tttLargeFiber60Block4Chunk3Row_8_ok,
    tttLargeFiber60Block4Chunk3Row_9_ok,
    tttLargeFiber60Block4Chunk3Row_10_ok,
    tttLargeFiber60Block4Chunk3Row_11_ok,
    tttLargeFiber60Block4Chunk3Row_12_ok,
    tttLargeFiber60Block4Chunk3Row_13_ok,
    tttLargeFiber60Block4Chunk3Row_14_ok,
    tttLargeFiber60Block4Chunk3Row_15_ok]

def tttLargeFiber60Block4Chunk3ParentMapAudit : Bool :=
  tttLargeFiber60Block4Chunk3ParentMapCheck 0
    && tttLargeFiber60Block4Chunk3ParentMapCheck 1
    && tttLargeFiber60Block4Chunk3ParentMapCheck 2
    && tttLargeFiber60Block4Chunk3ParentMapCheck 3
    && tttLargeFiber60Block4Chunk3ParentMapCheck 4
    && tttLargeFiber60Block4Chunk3ParentMapCheck 5
    && tttLargeFiber60Block4Chunk3ParentMapCheck 6
    && tttLargeFiber60Block4Chunk3ParentMapCheck 7
    && tttLargeFiber60Block4Chunk3ParentMapCheck 8
    && tttLargeFiber60Block4Chunk3ParentMapCheck 9
    && tttLargeFiber60Block4Chunk3ParentMapCheck 10
    && tttLargeFiber60Block4Chunk3ParentMapCheck 11
    && tttLargeFiber60Block4Chunk3ParentMapCheck 12
    && tttLargeFiber60Block4Chunk3ParentMapCheck 13
    && tttLargeFiber60Block4Chunk3ParentMapCheck 14
    && tttLargeFiber60Block4Chunk3ParentMapCheck 15

theorem tttLargeFiber60Block4Chunk3ParentMapAudit_ok :
    tttLargeFiber60Block4Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber60Block4Chunk3ParentMapAudit,
    tttLargeFiber60Block4Chunk3ParentMap_0_ok,
    tttLargeFiber60Block4Chunk3ParentMap_1_ok,
    tttLargeFiber60Block4Chunk3ParentMap_2_ok,
    tttLargeFiber60Block4Chunk3ParentMap_3_ok,
    tttLargeFiber60Block4Chunk3ParentMap_4_ok,
    tttLargeFiber60Block4Chunk3ParentMap_5_ok,
    tttLargeFiber60Block4Chunk3ParentMap_6_ok,
    tttLargeFiber60Block4Chunk3ParentMap_7_ok,
    tttLargeFiber60Block4Chunk3ParentMap_8_ok,
    tttLargeFiber60Block4Chunk3ParentMap_9_ok,
    tttLargeFiber60Block4Chunk3ParentMap_10_ok,
    tttLargeFiber60Block4Chunk3ParentMap_11_ok,
    tttLargeFiber60Block4Chunk3ParentMap_12_ok,
    tttLargeFiber60Block4Chunk3ParentMap_13_ok,
    tttLargeFiber60Block4Chunk3ParentMap_14_ok,
    tttLargeFiber60Block4Chunk3ParentMap_15_ok]

def tttLargeFiber60Block4Chunk3ParentsAudit : Bool :=
  tttLargeFiber60Block4Chunk3ParentPathCheck 0
    && tttLargeFiber60Block4Chunk3ParentPathCheck 1
    && tttLargeFiber60Block4Chunk3ParentPathCheck 2
    && tttLargeFiber60Block4Chunk3ParentPathCheck 3
    && tttLargeFiber60Block4Chunk3ParentPathCheck 4
    && tttLargeFiber60Block4Chunk3ParentPathCheck 5
    && tttLargeFiber60Block4Chunk3ParentPathCheck 6
    && tttLargeFiber60Block4Chunk3ParentPathCheck 7
    && tttLargeFiber60Block4Chunk3ParentPathCheck 8
    && tttLargeFiber60Block4Chunk3ParentPathCheck 9
    && tttLargeFiber60Block4Chunk3ParentPathCheck 10
    && tttLargeFiber60Block4Chunk3ParentPathCheck 11
    && tttLargeFiber60Block4Chunk3ParentPathCheck 12
    && tttLargeFiber60Block4Chunk3ParentPathCheck 13
    && tttLargeFiber60Block4Chunk3ParentPathCheck 14
    && tttLargeFiber60Block4Chunk3ParentPathCheck 15

theorem tttLargeFiber60Block4Chunk3ParentsAudit_ok :
    tttLargeFiber60Block4Chunk3ParentsAudit = true := by
  simp [tttLargeFiber60Block4Chunk3ParentsAudit,
    tttLargeFiber60Block4Chunk3ParentPath_0_ok,
    tttLargeFiber60Block4Chunk3ParentPath_1_ok,
    tttLargeFiber60Block4Chunk3ParentPath_2_ok,
    tttLargeFiber60Block4Chunk3ParentPath_3_ok,
    tttLargeFiber60Block4Chunk3ParentPath_4_ok,
    tttLargeFiber60Block4Chunk3ParentPath_5_ok,
    tttLargeFiber60Block4Chunk3ParentPath_6_ok,
    tttLargeFiber60Block4Chunk3ParentPath_7_ok,
    tttLargeFiber60Block4Chunk3ParentPath_8_ok,
    tttLargeFiber60Block4Chunk3ParentPath_9_ok,
    tttLargeFiber60Block4Chunk3ParentPath_10_ok,
    tttLargeFiber60Block4Chunk3ParentPath_11_ok,
    tttLargeFiber60Block4Chunk3ParentPath_12_ok,
    tttLargeFiber60Block4Chunk3ParentPath_13_ok,
    tttLargeFiber60Block4Chunk3ParentPath_14_ok,
    tttLargeFiber60Block4Chunk3ParentPath_15_ok]

def tttLargeFiber60Block4Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block4Chunk3SourcesCheck &&
    tttLargeFiber60Block4Chunk3RowsAudit &&
    tttLargeFiber60Block4Chunk3ParentMapAudit &&
    tttLargeFiber60Block4Chunk3ParentsAudit

theorem tttLargeFiber60Block4Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber60Block4Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block4Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block4Chunk3SourcesCheck_ok,
    tttLargeFiber60Block4Chunk3RowsAudit_ok,
    tttLargeFiber60Block4Chunk3ParentMapAudit_ok,
    tttLargeFiber60Block4Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block4Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
