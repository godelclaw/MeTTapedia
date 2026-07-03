import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 5 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block5Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block5Chunk3Sources : List Nat :=
  [   1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207,
   1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215]

def tttLargeFiber60Row368 : TripleComponentParentRow :=
  tripleRow 1200 656 33 174 64 17 110 64
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row369 : TripleComponentParentRow :=
  tripleRow 1201 657 33 174 65 17 110 65
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row370 : TripleComponentParentRow :=
  tripleRow 1202 658 33 174 66 17 110 66
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row371 : TripleComponentParentRow :=
  tripleRow 1203 1187 33 174 67 33 172 135
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

def tttLargeFiber60Row372 : TripleComponentParentRow :=
  tripleRow 1204 1172 33 174 116 33 158 48
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

def tttLargeFiber60Row373 : TripleComponentParentRow :=
  tripleRow 1205 1173 33 174 117 33 158 49
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

def tttLargeFiber60Row374 : TripleComponentParentRow :=
  tripleRow 1206 662 33 174 118 17 110 118
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row375 : TripleComponentParentRow :=
  tripleRow 1207 663 33 174 119 17 110 119
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row376 : TripleComponentParentRow :=
  tripleRow 1208 664 33 175 72 17 111 72
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row377 : TripleComponentParentRow :=
  tripleRow 1209 665 33 175 73 17 111 73
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row378 : TripleComponentParentRow :=
  tripleRow 1210 666 33 175 74 17 111 74
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row379 : TripleComponentParentRow :=
  tripleRow 1211 667 33 175 75 17 111 75
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row380 : TripleComponentParentRow :=
  tripleRow 1212 1180 33 175 124 33 159 56
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

def tttLargeFiber60Row381 : TripleComponentParentRow :=
  tripleRow 1213 1181 33 175 125 33 159 57
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

def tttLargeFiber60Row382 : TripleComponentParentRow :=
  tripleRow 1214 670 33 175 126 17 111 126
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Row383 : TripleComponentParentRow :=
  tripleRow 1215 671 33 175 127 17 111 127
    (chainMove LColor.b LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber60Block5Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row368
  , tttLargeFiber60Row369
  , tttLargeFiber60Row370
  , tttLargeFiber60Row371
  , tttLargeFiber60Row372
  , tttLargeFiber60Row373
  , tttLargeFiber60Row374
  , tttLargeFiber60Row375
  , tttLargeFiber60Row376
  , tttLargeFiber60Row377
  , tttLargeFiber60Row378
  , tttLargeFiber60Row379
  , tttLargeFiber60Row380
  , tttLargeFiber60Row381
  , tttLargeFiber60Row382
  , tttLargeFiber60Row383
  ]

def tttLargeFiber60Block5Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block5Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block5Chunk3ExpectedContains row.source &&
    tttLargeFiber60Block5Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block5Chunk3SourcesCheck : Bool :=
  (tttLargeFiber60Block5Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber60Block5Chunk3Sources

theorem tttLargeFiber60Block5Chunk3SourcesCheck_ok :
    tttLargeFiber60Block5Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber60Block5Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block5Chunk3RowValid
    (listGetD tttLargeFiber60Block5Chunk3Rows i default)

def tttLargeFiber60Block5Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block5Chunk3Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block5Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block5Chunk3Sources 0 0 == 1200
      && tttLargeFiber60ParentOf 1200 == 656
      && tttLargeFiber60ParentOf 656 == 592
      && tttLargeFiber60ParentOf 592 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block5Chunk3Sources 1 0 == 1201
      && tttLargeFiber60ParentOf 1201 == 657
      && tttLargeFiber60ParentOf 657 == 593
      && tttLargeFiber60ParentOf 593 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block5Chunk3Sources 2 0 == 1202
      && tttLargeFiber60ParentOf 1202 == 658
      && tttLargeFiber60ParentOf 658 == 594
      && tttLargeFiber60ParentOf 594 == 554
      && tttLargeFiber60ParentOf 554 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block5Chunk3Sources 3 0 == 1203
      && tttLargeFiber60ParentOf 1203 == 1187
      && tttLargeFiber60ParentOf 1187 == 1155
      && tttLargeFiber60ParentOf 1155 == 1152
      && tttLargeFiber60ParentOf 1152 == 608
      && tttLargeFiber60ParentOf 608 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block5Chunk3Sources 4 0 == 1204
      && tttLargeFiber60ParentOf 1204 == 1172
      && tttLargeFiber60ParentOf 1172 == 1160
      && tttLargeFiber60ParentOf 1160 == 616
      && tttLargeFiber60ParentOf 616 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block5Chunk3Sources 5 0 == 1205
      && tttLargeFiber60ParentOf 1205 == 1173
      && tttLargeFiber60ParentOf 1173 == 1161
      && tttLargeFiber60ParentOf 1161 == 617
      && tttLargeFiber60ParentOf 617 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (6 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block5Chunk3Sources 6 0 == 1206
      && tttLargeFiber60ParentOf 1206 == 662
      && tttLargeFiber60ParentOf 662 == 598
      && tttLargeFiber60ParentOf 598 == 558
      && tttLargeFiber60ParentOf 558 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (6 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block5Chunk3Sources 7 0 == 1207
      && tttLargeFiber60ParentOf 1207 == 663
      && tttLargeFiber60ParentOf 663 == 599
      && tttLargeFiber60ParentOf 599 == 559
      && tttLargeFiber60ParentOf 559 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block5Chunk3Sources 8 0 == 1208
      && tttLargeFiber60ParentOf 1208 == 664
      && tttLargeFiber60ParentOf 664 == 600
      && tttLargeFiber60ParentOf 600 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block5Chunk3Sources 9 0 == 1209
      && tttLargeFiber60ParentOf 1209 == 665
      && tttLargeFiber60ParentOf 665 == 601
      && tttLargeFiber60ParentOf 601 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block5Chunk3Sources 10 0 == 1210
      && tttLargeFiber60ParentOf 1210 == 666
      && tttLargeFiber60ParentOf 666 == 602
      && tttLargeFiber60ParentOf 602 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block5Chunk3Sources 11 0 == 1211
      && tttLargeFiber60ParentOf 1211 == 667
      && tttLargeFiber60ParentOf 667 == 603
      && tttLargeFiber60ParentOf 603 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block5Chunk3Sources 12 0 == 1212
      && tttLargeFiber60ParentOf 1212 == 1180
      && tttLargeFiber60ParentOf 1180 == 1152
      && tttLargeFiber60ParentOf 1152 == 608
      && tttLargeFiber60ParentOf 608 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block5Chunk3Sources 13 0 == 1213
      && tttLargeFiber60ParentOf 1213 == 1181
      && tttLargeFiber60ParentOf 1181 == 1153
      && tttLargeFiber60ParentOf 1153 == 609
      && tttLargeFiber60ParentOf 609 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block5Chunk3Sources 14 0 == 1214
      && tttLargeFiber60ParentOf 1214 == 670
      && tttLargeFiber60ParentOf 670 == 606
      && tttLargeFiber60ParentOf 606 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block5Chunk3Sources 15 0 == 1215
      && tttLargeFiber60ParentOf 1215 == 671
      && tttLargeFiber60ParentOf 671 == 607
      && tttLargeFiber60ParentOf 607 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block5Chunk3Row_0_ok :
    tttLargeFiber60Block5Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3Row_1_ok :
    tttLargeFiber60Block5Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3Row_2_ok :
    tttLargeFiber60Block5Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3Row_3_ok :
    tttLargeFiber60Block5Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3Row_4_ok :
    tttLargeFiber60Block5Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3Row_5_ok :
    tttLargeFiber60Block5Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3Row_6_ok :
    tttLargeFiber60Block5Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3Row_7_ok :
    tttLargeFiber60Block5Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3Row_8_ok :
    tttLargeFiber60Block5Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3Row_9_ok :
    tttLargeFiber60Block5Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3Row_10_ok :
    tttLargeFiber60Block5Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3Row_11_ok :
    tttLargeFiber60Block5Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3Row_12_ok :
    tttLargeFiber60Block5Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3Row_13_ok :
    tttLargeFiber60Block5Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3Row_14_ok :
    tttLargeFiber60Block5Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3Row_15_ok :
    tttLargeFiber60Block5Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentMap_0_ok :
    tttLargeFiber60Block5Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentMap_1_ok :
    tttLargeFiber60Block5Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentMap_2_ok :
    tttLargeFiber60Block5Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentMap_3_ok :
    tttLargeFiber60Block5Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentMap_4_ok :
    tttLargeFiber60Block5Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentMap_5_ok :
    tttLargeFiber60Block5Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentMap_6_ok :
    tttLargeFiber60Block5Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentMap_7_ok :
    tttLargeFiber60Block5Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentMap_8_ok :
    tttLargeFiber60Block5Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentMap_9_ok :
    tttLargeFiber60Block5Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentMap_10_ok :
    tttLargeFiber60Block5Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentMap_11_ok :
    tttLargeFiber60Block5Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentMap_12_ok :
    tttLargeFiber60Block5Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentMap_13_ok :
    tttLargeFiber60Block5Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentMap_14_ok :
    tttLargeFiber60Block5Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentMap_15_ok :
    tttLargeFiber60Block5Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentPath_0_ok :
    tttLargeFiber60Block5Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentPath_1_ok :
    tttLargeFiber60Block5Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentPath_2_ok :
    tttLargeFiber60Block5Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentPath_3_ok :
    tttLargeFiber60Block5Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentPath_4_ok :
    tttLargeFiber60Block5Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentPath_5_ok :
    tttLargeFiber60Block5Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentPath_6_ok :
    tttLargeFiber60Block5Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentPath_7_ok :
    tttLargeFiber60Block5Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentPath_8_ok :
    tttLargeFiber60Block5Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentPath_9_ok :
    tttLargeFiber60Block5Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentPath_10_ok :
    tttLargeFiber60Block5Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentPath_11_ok :
    tttLargeFiber60Block5Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentPath_12_ok :
    tttLargeFiber60Block5Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentPath_13_ok :
    tttLargeFiber60Block5Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentPath_14_ok :
    tttLargeFiber60Block5Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block5Chunk3ParentPath_15_ok :
    tttLargeFiber60Block5Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block5Chunk3RowsAudit : Bool :=
  tttLargeFiber60Block5Chunk3RowCheck 0
    && tttLargeFiber60Block5Chunk3RowCheck 1
    && tttLargeFiber60Block5Chunk3RowCheck 2
    && tttLargeFiber60Block5Chunk3RowCheck 3
    && tttLargeFiber60Block5Chunk3RowCheck 4
    && tttLargeFiber60Block5Chunk3RowCheck 5
    && tttLargeFiber60Block5Chunk3RowCheck 6
    && tttLargeFiber60Block5Chunk3RowCheck 7
    && tttLargeFiber60Block5Chunk3RowCheck 8
    && tttLargeFiber60Block5Chunk3RowCheck 9
    && tttLargeFiber60Block5Chunk3RowCheck 10
    && tttLargeFiber60Block5Chunk3RowCheck 11
    && tttLargeFiber60Block5Chunk3RowCheck 12
    && tttLargeFiber60Block5Chunk3RowCheck 13
    && tttLargeFiber60Block5Chunk3RowCheck 14
    && tttLargeFiber60Block5Chunk3RowCheck 15

theorem tttLargeFiber60Block5Chunk3RowsAudit_ok :
    tttLargeFiber60Block5Chunk3RowsAudit = true := by
  simp [tttLargeFiber60Block5Chunk3RowsAudit,
    tttLargeFiber60Block5Chunk3Row_0_ok,
    tttLargeFiber60Block5Chunk3Row_1_ok,
    tttLargeFiber60Block5Chunk3Row_2_ok,
    tttLargeFiber60Block5Chunk3Row_3_ok,
    tttLargeFiber60Block5Chunk3Row_4_ok,
    tttLargeFiber60Block5Chunk3Row_5_ok,
    tttLargeFiber60Block5Chunk3Row_6_ok,
    tttLargeFiber60Block5Chunk3Row_7_ok,
    tttLargeFiber60Block5Chunk3Row_8_ok,
    tttLargeFiber60Block5Chunk3Row_9_ok,
    tttLargeFiber60Block5Chunk3Row_10_ok,
    tttLargeFiber60Block5Chunk3Row_11_ok,
    tttLargeFiber60Block5Chunk3Row_12_ok,
    tttLargeFiber60Block5Chunk3Row_13_ok,
    tttLargeFiber60Block5Chunk3Row_14_ok,
    tttLargeFiber60Block5Chunk3Row_15_ok]

def tttLargeFiber60Block5Chunk3ParentMapAudit : Bool :=
  tttLargeFiber60Block5Chunk3ParentMapCheck 0
    && tttLargeFiber60Block5Chunk3ParentMapCheck 1
    && tttLargeFiber60Block5Chunk3ParentMapCheck 2
    && tttLargeFiber60Block5Chunk3ParentMapCheck 3
    && tttLargeFiber60Block5Chunk3ParentMapCheck 4
    && tttLargeFiber60Block5Chunk3ParentMapCheck 5
    && tttLargeFiber60Block5Chunk3ParentMapCheck 6
    && tttLargeFiber60Block5Chunk3ParentMapCheck 7
    && tttLargeFiber60Block5Chunk3ParentMapCheck 8
    && tttLargeFiber60Block5Chunk3ParentMapCheck 9
    && tttLargeFiber60Block5Chunk3ParentMapCheck 10
    && tttLargeFiber60Block5Chunk3ParentMapCheck 11
    && tttLargeFiber60Block5Chunk3ParentMapCheck 12
    && tttLargeFiber60Block5Chunk3ParentMapCheck 13
    && tttLargeFiber60Block5Chunk3ParentMapCheck 14
    && tttLargeFiber60Block5Chunk3ParentMapCheck 15

theorem tttLargeFiber60Block5Chunk3ParentMapAudit_ok :
    tttLargeFiber60Block5Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber60Block5Chunk3ParentMapAudit,
    tttLargeFiber60Block5Chunk3ParentMap_0_ok,
    tttLargeFiber60Block5Chunk3ParentMap_1_ok,
    tttLargeFiber60Block5Chunk3ParentMap_2_ok,
    tttLargeFiber60Block5Chunk3ParentMap_3_ok,
    tttLargeFiber60Block5Chunk3ParentMap_4_ok,
    tttLargeFiber60Block5Chunk3ParentMap_5_ok,
    tttLargeFiber60Block5Chunk3ParentMap_6_ok,
    tttLargeFiber60Block5Chunk3ParentMap_7_ok,
    tttLargeFiber60Block5Chunk3ParentMap_8_ok,
    tttLargeFiber60Block5Chunk3ParentMap_9_ok,
    tttLargeFiber60Block5Chunk3ParentMap_10_ok,
    tttLargeFiber60Block5Chunk3ParentMap_11_ok,
    tttLargeFiber60Block5Chunk3ParentMap_12_ok,
    tttLargeFiber60Block5Chunk3ParentMap_13_ok,
    tttLargeFiber60Block5Chunk3ParentMap_14_ok,
    tttLargeFiber60Block5Chunk3ParentMap_15_ok]

def tttLargeFiber60Block5Chunk3ParentsAudit : Bool :=
  tttLargeFiber60Block5Chunk3ParentPathCheck 0
    && tttLargeFiber60Block5Chunk3ParentPathCheck 1
    && tttLargeFiber60Block5Chunk3ParentPathCheck 2
    && tttLargeFiber60Block5Chunk3ParentPathCheck 3
    && tttLargeFiber60Block5Chunk3ParentPathCheck 4
    && tttLargeFiber60Block5Chunk3ParentPathCheck 5
    && tttLargeFiber60Block5Chunk3ParentPathCheck 6
    && tttLargeFiber60Block5Chunk3ParentPathCheck 7
    && tttLargeFiber60Block5Chunk3ParentPathCheck 8
    && tttLargeFiber60Block5Chunk3ParentPathCheck 9
    && tttLargeFiber60Block5Chunk3ParentPathCheck 10
    && tttLargeFiber60Block5Chunk3ParentPathCheck 11
    && tttLargeFiber60Block5Chunk3ParentPathCheck 12
    && tttLargeFiber60Block5Chunk3ParentPathCheck 13
    && tttLargeFiber60Block5Chunk3ParentPathCheck 14
    && tttLargeFiber60Block5Chunk3ParentPathCheck 15

theorem tttLargeFiber60Block5Chunk3ParentsAudit_ok :
    tttLargeFiber60Block5Chunk3ParentsAudit = true := by
  simp [tttLargeFiber60Block5Chunk3ParentsAudit,
    tttLargeFiber60Block5Chunk3ParentPath_0_ok,
    tttLargeFiber60Block5Chunk3ParentPath_1_ok,
    tttLargeFiber60Block5Chunk3ParentPath_2_ok,
    tttLargeFiber60Block5Chunk3ParentPath_3_ok,
    tttLargeFiber60Block5Chunk3ParentPath_4_ok,
    tttLargeFiber60Block5Chunk3ParentPath_5_ok,
    tttLargeFiber60Block5Chunk3ParentPath_6_ok,
    tttLargeFiber60Block5Chunk3ParentPath_7_ok,
    tttLargeFiber60Block5Chunk3ParentPath_8_ok,
    tttLargeFiber60Block5Chunk3ParentPath_9_ok,
    tttLargeFiber60Block5Chunk3ParentPath_10_ok,
    tttLargeFiber60Block5Chunk3ParentPath_11_ok,
    tttLargeFiber60Block5Chunk3ParentPath_12_ok,
    tttLargeFiber60Block5Chunk3ParentPath_13_ok,
    tttLargeFiber60Block5Chunk3ParentPath_14_ok,
    tttLargeFiber60Block5Chunk3ParentPath_15_ok]

def tttLargeFiber60Block5Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block5Chunk3SourcesCheck &&
    tttLargeFiber60Block5Chunk3RowsAudit &&
    tttLargeFiber60Block5Chunk3ParentMapAudit &&
    tttLargeFiber60Block5Chunk3ParentsAudit

theorem tttLargeFiber60Block5Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber60Block5Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block5Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block5Chunk3SourcesCheck_ok,
    tttLargeFiber60Block5Chunk3RowsAudit_ok,
    tttLargeFiber60Block5Chunk3ParentMapAudit_ok,
    tttLargeFiber60Block5Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block5Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
