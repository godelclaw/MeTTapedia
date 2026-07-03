import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 5 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block5Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block5Chunk1Sources : List Nat :=
  [   1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175,
   1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183]

def tttLargeFiber60Row336 : TripleComponentParentRow :=
  tripleRow 1168 624 33 158 0 17 90 16
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

def tttLargeFiber60Row337 : TripleComponentParentRow :=
  tripleRow 1169 625 33 158 1 17 90 17
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

def tttLargeFiber60Row338 : TripleComponentParentRow :=
  tripleRow 1170 626 33 158 2 17 90 18
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

def tttLargeFiber60Row339 : TripleComponentParentRow :=
  tripleRow 1171 627 33 158 3 17 90 19
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

def tttLargeFiber60Row340 : TripleComponentParentRow :=
  tripleRow 1172 1160 33 158 48 33 157 156
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row341 : TripleComponentParentRow :=
  tripleRow 1173 1161 33 158 49 33 157 157
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row342 : TripleComponentParentRow :=
  tripleRow 1174 630 33 158 50 17 90 34
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

def tttLargeFiber60Row343 : TripleComponentParentRow :=
  tripleRow 1175 631 33 158 51 17 90 35
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

def tttLargeFiber60Row344 : TripleComponentParentRow :=
  tripleRow 1176 1159 33 159 8 33 156 167
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

def tttLargeFiber60Row345 : TripleComponentParentRow :=
  tripleRow 1177 1158 33 159 9 33 156 166
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

def tttLargeFiber60Row346 : TripleComponentParentRow :=
  tripleRow 1178 1156 33 159 10 33 156 164
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

def tttLargeFiber60Row347 : TripleComponentParentRow :=
  tripleRow 1179 1157 33 159 11 33 156 165
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

def tttLargeFiber60Row348 : TripleComponentParentRow :=
  tripleRow 1180 1152 33 159 56 33 156 148
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row349 : TripleComponentParentRow :=
  tripleRow 1181 1153 33 159 57 33 156 149
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row350 : TripleComponentParentRow :=
  tripleRow 1182 1154 33 159 58 33 156 150
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Row351 : TripleComponentParentRow :=
  tripleRow 1183 1155 33 159 59 33 156 151
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber60Block5Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row336
  , tttLargeFiber60Row337
  , tttLargeFiber60Row338
  , tttLargeFiber60Row339
  , tttLargeFiber60Row340
  , tttLargeFiber60Row341
  , tttLargeFiber60Row342
  , tttLargeFiber60Row343
  , tttLargeFiber60Row344
  , tttLargeFiber60Row345
  , tttLargeFiber60Row346
  , tttLargeFiber60Row347
  , tttLargeFiber60Row348
  , tttLargeFiber60Row349
  , tttLargeFiber60Row350
  , tttLargeFiber60Row351
  ]

def tttLargeFiber60Block5Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block5Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block5Chunk1ExpectedContains row.source &&
    tttLargeFiber60Block5Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block5Chunk1SourcesCheck : Bool :=
  (tttLargeFiber60Block5Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber60Block5Chunk1Sources

theorem tttLargeFiber60Block5Chunk1SourcesCheck_ok :
    tttLargeFiber60Block5Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber60Block5Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block5Chunk1RowValid
    (listGetD tttLargeFiber60Block5Chunk1Rows i default)

def tttLargeFiber60Block5Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block5Chunk1Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block5Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block5Chunk1Sources 0 0 == 1168
      && tttLargeFiber60ParentOf 1168 == 624
      && tttLargeFiber60ParentOf 624 == 560
      && tttLargeFiber60ParentOf 560 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block5Chunk1Sources 1 0 == 1169
      && tttLargeFiber60ParentOf 1169 == 625
      && tttLargeFiber60ParentOf 625 == 561
      && tttLargeFiber60ParentOf 561 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block5Chunk1Sources 2 0 == 1170
      && tttLargeFiber60ParentOf 1170 == 626
      && tttLargeFiber60ParentOf 626 == 562
      && tttLargeFiber60ParentOf 562 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block5Chunk1Sources 3 0 == 1171
      && tttLargeFiber60ParentOf 1171 == 627
      && tttLargeFiber60ParentOf 627 == 563
      && tttLargeFiber60ParentOf 563 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block5Chunk1Sources 4 0 == 1172
      && tttLargeFiber60ParentOf 1172 == 1160
      && tttLargeFiber60ParentOf 1160 == 616
      && tttLargeFiber60ParentOf 616 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block5Chunk1Sources 5 0 == 1173
      && tttLargeFiber60ParentOf 1173 == 1161
      && tttLargeFiber60ParentOf 1161 == 617
      && tttLargeFiber60ParentOf 617 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block5Chunk1Sources 6 0 == 1174
      && tttLargeFiber60ParentOf 1174 == 630
      && tttLargeFiber60ParentOf 630 == 566
      && tttLargeFiber60ParentOf 566 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block5Chunk1Sources 7 0 == 1175
      && tttLargeFiber60ParentOf 1175 == 631
      && tttLargeFiber60ParentOf 631 == 567
      && tttLargeFiber60ParentOf 567 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block5Chunk1Sources 8 0 == 1176
      && tttLargeFiber60ParentOf 1176 == 1159
      && tttLargeFiber60ParentOf 1159 == 615
      && tttLargeFiber60ParentOf 615 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block5Chunk1Sources 9 0 == 1177
      && tttLargeFiber60ParentOf 1177 == 1158
      && tttLargeFiber60ParentOf 1158 == 614
      && tttLargeFiber60ParentOf 614 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block5Chunk1Sources 10 0 == 1178
      && tttLargeFiber60ParentOf 1178 == 1156
      && tttLargeFiber60ParentOf 1156 == 1152
      && tttLargeFiber60ParentOf 1152 == 608
      && tttLargeFiber60ParentOf 608 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block5Chunk1Sources 11 0 == 1179
      && tttLargeFiber60ParentOf 1179 == 1157
      && tttLargeFiber60ParentOf 1157 == 1153
      && tttLargeFiber60ParentOf 1153 == 609
      && tttLargeFiber60ParentOf 609 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block5Chunk1Sources 12 0 == 1180
      && tttLargeFiber60ParentOf 1180 == 1152
      && tttLargeFiber60ParentOf 1152 == 608
      && tttLargeFiber60ParentOf 608 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block5Chunk1Sources 13 0 == 1181
      && tttLargeFiber60ParentOf 1181 == 1153
      && tttLargeFiber60ParentOf 1153 == 609
      && tttLargeFiber60ParentOf 609 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block5Chunk1Sources 14 0 == 1182
      && tttLargeFiber60ParentOf 1182 == 1154
      && tttLargeFiber60ParentOf 1154 == 610
      && tttLargeFiber60ParentOf 610 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block5Chunk1Sources 15 0 == 1183
      && tttLargeFiber60ParentOf 1183 == 1155
      && tttLargeFiber60ParentOf 1155 == 1152
      && tttLargeFiber60ParentOf 1152 == 608
      && tttLargeFiber60ParentOf 608 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block5Chunk1Row_0_ok :
    tttLargeFiber60Block5Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1Row_1_ok :
    tttLargeFiber60Block5Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1Row_2_ok :
    tttLargeFiber60Block5Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1Row_3_ok :
    tttLargeFiber60Block5Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1Row_4_ok :
    tttLargeFiber60Block5Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1Row_5_ok :
    tttLargeFiber60Block5Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1Row_6_ok :
    tttLargeFiber60Block5Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1Row_7_ok :
    tttLargeFiber60Block5Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1Row_8_ok :
    tttLargeFiber60Block5Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1Row_9_ok :
    tttLargeFiber60Block5Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1Row_10_ok :
    tttLargeFiber60Block5Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1Row_11_ok :
    tttLargeFiber60Block5Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1Row_12_ok :
    tttLargeFiber60Block5Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1Row_13_ok :
    tttLargeFiber60Block5Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1Row_14_ok :
    tttLargeFiber60Block5Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1Row_15_ok :
    tttLargeFiber60Block5Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentMap_0_ok :
    tttLargeFiber60Block5Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentMap_1_ok :
    tttLargeFiber60Block5Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentMap_2_ok :
    tttLargeFiber60Block5Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentMap_3_ok :
    tttLargeFiber60Block5Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentMap_4_ok :
    tttLargeFiber60Block5Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentMap_5_ok :
    tttLargeFiber60Block5Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentMap_6_ok :
    tttLargeFiber60Block5Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentMap_7_ok :
    tttLargeFiber60Block5Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentMap_8_ok :
    tttLargeFiber60Block5Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentMap_9_ok :
    tttLargeFiber60Block5Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentMap_10_ok :
    tttLargeFiber60Block5Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentMap_11_ok :
    tttLargeFiber60Block5Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentMap_12_ok :
    tttLargeFiber60Block5Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentMap_13_ok :
    tttLargeFiber60Block5Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentMap_14_ok :
    tttLargeFiber60Block5Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentMap_15_ok :
    tttLargeFiber60Block5Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentPath_0_ok :
    tttLargeFiber60Block5Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentPath_1_ok :
    tttLargeFiber60Block5Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentPath_2_ok :
    tttLargeFiber60Block5Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentPath_3_ok :
    tttLargeFiber60Block5Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentPath_4_ok :
    tttLargeFiber60Block5Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentPath_5_ok :
    tttLargeFiber60Block5Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentPath_6_ok :
    tttLargeFiber60Block5Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentPath_7_ok :
    tttLargeFiber60Block5Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentPath_8_ok :
    tttLargeFiber60Block5Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentPath_9_ok :
    tttLargeFiber60Block5Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentPath_10_ok :
    tttLargeFiber60Block5Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentPath_11_ok :
    tttLargeFiber60Block5Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentPath_12_ok :
    tttLargeFiber60Block5Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentPath_13_ok :
    tttLargeFiber60Block5Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentPath_14_ok :
    tttLargeFiber60Block5Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block5Chunk1ParentPath_15_ok :
    tttLargeFiber60Block5Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block5Chunk1RowsAudit : Bool :=
  tttLargeFiber60Block5Chunk1RowCheck 0
    && tttLargeFiber60Block5Chunk1RowCheck 1
    && tttLargeFiber60Block5Chunk1RowCheck 2
    && tttLargeFiber60Block5Chunk1RowCheck 3
    && tttLargeFiber60Block5Chunk1RowCheck 4
    && tttLargeFiber60Block5Chunk1RowCheck 5
    && tttLargeFiber60Block5Chunk1RowCheck 6
    && tttLargeFiber60Block5Chunk1RowCheck 7
    && tttLargeFiber60Block5Chunk1RowCheck 8
    && tttLargeFiber60Block5Chunk1RowCheck 9
    && tttLargeFiber60Block5Chunk1RowCheck 10
    && tttLargeFiber60Block5Chunk1RowCheck 11
    && tttLargeFiber60Block5Chunk1RowCheck 12
    && tttLargeFiber60Block5Chunk1RowCheck 13
    && tttLargeFiber60Block5Chunk1RowCheck 14
    && tttLargeFiber60Block5Chunk1RowCheck 15

theorem tttLargeFiber60Block5Chunk1RowsAudit_ok :
    tttLargeFiber60Block5Chunk1RowsAudit = true := by
  simp [tttLargeFiber60Block5Chunk1RowsAudit,
    tttLargeFiber60Block5Chunk1Row_0_ok,
    tttLargeFiber60Block5Chunk1Row_1_ok,
    tttLargeFiber60Block5Chunk1Row_2_ok,
    tttLargeFiber60Block5Chunk1Row_3_ok,
    tttLargeFiber60Block5Chunk1Row_4_ok,
    tttLargeFiber60Block5Chunk1Row_5_ok,
    tttLargeFiber60Block5Chunk1Row_6_ok,
    tttLargeFiber60Block5Chunk1Row_7_ok,
    tttLargeFiber60Block5Chunk1Row_8_ok,
    tttLargeFiber60Block5Chunk1Row_9_ok,
    tttLargeFiber60Block5Chunk1Row_10_ok,
    tttLargeFiber60Block5Chunk1Row_11_ok,
    tttLargeFiber60Block5Chunk1Row_12_ok,
    tttLargeFiber60Block5Chunk1Row_13_ok,
    tttLargeFiber60Block5Chunk1Row_14_ok,
    tttLargeFiber60Block5Chunk1Row_15_ok]

def tttLargeFiber60Block5Chunk1ParentMapAudit : Bool :=
  tttLargeFiber60Block5Chunk1ParentMapCheck 0
    && tttLargeFiber60Block5Chunk1ParentMapCheck 1
    && tttLargeFiber60Block5Chunk1ParentMapCheck 2
    && tttLargeFiber60Block5Chunk1ParentMapCheck 3
    && tttLargeFiber60Block5Chunk1ParentMapCheck 4
    && tttLargeFiber60Block5Chunk1ParentMapCheck 5
    && tttLargeFiber60Block5Chunk1ParentMapCheck 6
    && tttLargeFiber60Block5Chunk1ParentMapCheck 7
    && tttLargeFiber60Block5Chunk1ParentMapCheck 8
    && tttLargeFiber60Block5Chunk1ParentMapCheck 9
    && tttLargeFiber60Block5Chunk1ParentMapCheck 10
    && tttLargeFiber60Block5Chunk1ParentMapCheck 11
    && tttLargeFiber60Block5Chunk1ParentMapCheck 12
    && tttLargeFiber60Block5Chunk1ParentMapCheck 13
    && tttLargeFiber60Block5Chunk1ParentMapCheck 14
    && tttLargeFiber60Block5Chunk1ParentMapCheck 15

theorem tttLargeFiber60Block5Chunk1ParentMapAudit_ok :
    tttLargeFiber60Block5Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber60Block5Chunk1ParentMapAudit,
    tttLargeFiber60Block5Chunk1ParentMap_0_ok,
    tttLargeFiber60Block5Chunk1ParentMap_1_ok,
    tttLargeFiber60Block5Chunk1ParentMap_2_ok,
    tttLargeFiber60Block5Chunk1ParentMap_3_ok,
    tttLargeFiber60Block5Chunk1ParentMap_4_ok,
    tttLargeFiber60Block5Chunk1ParentMap_5_ok,
    tttLargeFiber60Block5Chunk1ParentMap_6_ok,
    tttLargeFiber60Block5Chunk1ParentMap_7_ok,
    tttLargeFiber60Block5Chunk1ParentMap_8_ok,
    tttLargeFiber60Block5Chunk1ParentMap_9_ok,
    tttLargeFiber60Block5Chunk1ParentMap_10_ok,
    tttLargeFiber60Block5Chunk1ParentMap_11_ok,
    tttLargeFiber60Block5Chunk1ParentMap_12_ok,
    tttLargeFiber60Block5Chunk1ParentMap_13_ok,
    tttLargeFiber60Block5Chunk1ParentMap_14_ok,
    tttLargeFiber60Block5Chunk1ParentMap_15_ok]

def tttLargeFiber60Block5Chunk1ParentsAudit : Bool :=
  tttLargeFiber60Block5Chunk1ParentPathCheck 0
    && tttLargeFiber60Block5Chunk1ParentPathCheck 1
    && tttLargeFiber60Block5Chunk1ParentPathCheck 2
    && tttLargeFiber60Block5Chunk1ParentPathCheck 3
    && tttLargeFiber60Block5Chunk1ParentPathCheck 4
    && tttLargeFiber60Block5Chunk1ParentPathCheck 5
    && tttLargeFiber60Block5Chunk1ParentPathCheck 6
    && tttLargeFiber60Block5Chunk1ParentPathCheck 7
    && tttLargeFiber60Block5Chunk1ParentPathCheck 8
    && tttLargeFiber60Block5Chunk1ParentPathCheck 9
    && tttLargeFiber60Block5Chunk1ParentPathCheck 10
    && tttLargeFiber60Block5Chunk1ParentPathCheck 11
    && tttLargeFiber60Block5Chunk1ParentPathCheck 12
    && tttLargeFiber60Block5Chunk1ParentPathCheck 13
    && tttLargeFiber60Block5Chunk1ParentPathCheck 14
    && tttLargeFiber60Block5Chunk1ParentPathCheck 15

theorem tttLargeFiber60Block5Chunk1ParentsAudit_ok :
    tttLargeFiber60Block5Chunk1ParentsAudit = true := by
  simp [tttLargeFiber60Block5Chunk1ParentsAudit,
    tttLargeFiber60Block5Chunk1ParentPath_0_ok,
    tttLargeFiber60Block5Chunk1ParentPath_1_ok,
    tttLargeFiber60Block5Chunk1ParentPath_2_ok,
    tttLargeFiber60Block5Chunk1ParentPath_3_ok,
    tttLargeFiber60Block5Chunk1ParentPath_4_ok,
    tttLargeFiber60Block5Chunk1ParentPath_5_ok,
    tttLargeFiber60Block5Chunk1ParentPath_6_ok,
    tttLargeFiber60Block5Chunk1ParentPath_7_ok,
    tttLargeFiber60Block5Chunk1ParentPath_8_ok,
    tttLargeFiber60Block5Chunk1ParentPath_9_ok,
    tttLargeFiber60Block5Chunk1ParentPath_10_ok,
    tttLargeFiber60Block5Chunk1ParentPath_11_ok,
    tttLargeFiber60Block5Chunk1ParentPath_12_ok,
    tttLargeFiber60Block5Chunk1ParentPath_13_ok,
    tttLargeFiber60Block5Chunk1ParentPath_14_ok,
    tttLargeFiber60Block5Chunk1ParentPath_15_ok]

def tttLargeFiber60Block5Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block5Chunk1SourcesCheck &&
    tttLargeFiber60Block5Chunk1RowsAudit &&
    tttLargeFiber60Block5Chunk1ParentMapAudit &&
    tttLargeFiber60Block5Chunk1ParentsAudit

theorem tttLargeFiber60Block5Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber60Block5Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block5Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block5Chunk1SourcesCheck_ok,
    tttLargeFiber60Block5Chunk1RowsAudit_ok,
    tttLargeFiber60Block5Chunk1ParentMapAudit_ok,
    tttLargeFiber60Block5Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block5Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
