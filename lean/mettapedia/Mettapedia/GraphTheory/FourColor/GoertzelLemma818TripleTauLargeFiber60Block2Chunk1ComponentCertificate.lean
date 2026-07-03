import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 2 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block2Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block2Chunk1Sources : List Nat :=
  [   688, 689, 690, 691, 692, 693, 694, 695,
   696, 697, 698, 699, 700, 701, 702, 703]

def tttLargeFiber60Row144 : TripleComponentParentRow :=
  tripleRow 688 560 18 18 16 16 82 16
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber60Row145 : TripleComponentParentRow :=
  tripleRow 689 561 18 18 17 16 82 17
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber60Row146 : TripleComponentParentRow :=
  tripleRow 690 562 18 18 18 16 82 18
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber60Row147 : TripleComponentParentRow :=
  tripleRow 691 563 18 18 19 16 82 19
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber60Row148 : TripleComponentParentRow :=
  tripleRow 692 564 18 18 32 16 82 32
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber60Row149 : TripleComponentParentRow :=
  tripleRow 693 565 18 18 33 16 82 33
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber60Row150 : TripleComponentParentRow :=
  tripleRow 694 566 18 18 34 16 82 34
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber60Row151 : TripleComponentParentRow :=
  tripleRow 695 567 18 18 35 16 82 35
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber60Row152 : TripleComponentParentRow :=
  tripleRow 696 568 18 19 24 16 83 24
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber60Row153 : TripleComponentParentRow :=
  tripleRow 697 569 18 19 25 16 83 25
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber60Row154 : TripleComponentParentRow :=
  tripleRow 698 570 18 19 26 16 83 26
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber60Row155 : TripleComponentParentRow :=
  tripleRow 699 571 18 19 27 16 83 27
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber60Row156 : TripleComponentParentRow :=
  tripleRow 700 572 18 19 40 16 83 40
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber60Row157 : TripleComponentParentRow :=
  tripleRow 701 573 18 19 41 16 83 41
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber60Row158 : TripleComponentParentRow :=
  tripleRow 702 574 18 19 42 16 83 42
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber60Row159 : TripleComponentParentRow :=
  tripleRow 703 575 18 19 43 16 83 43
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber60Block2Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row144
  , tttLargeFiber60Row145
  , tttLargeFiber60Row146
  , tttLargeFiber60Row147
  , tttLargeFiber60Row148
  , tttLargeFiber60Row149
  , tttLargeFiber60Row150
  , tttLargeFiber60Row151
  , tttLargeFiber60Row152
  , tttLargeFiber60Row153
  , tttLargeFiber60Row154
  , tttLargeFiber60Row155
  , tttLargeFiber60Row156
  , tttLargeFiber60Row157
  , tttLargeFiber60Row158
  , tttLargeFiber60Row159
  ]

def tttLargeFiber60Block2Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block2Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block2Chunk1ExpectedContains row.source &&
    tttLargeFiber60Block2Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block2Chunk1SourcesCheck : Bool :=
  (tttLargeFiber60Block2Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber60Block2Chunk1Sources

theorem tttLargeFiber60Block2Chunk1SourcesCheck_ok :
    tttLargeFiber60Block2Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber60Block2Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block2Chunk1RowValid
    (listGetD tttLargeFiber60Block2Chunk1Rows i default)

def tttLargeFiber60Block2Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block2Chunk1Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block2Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block2Chunk1Sources 0 0 == 688
      && tttLargeFiber60ParentOf 688 == 560
      && tttLargeFiber60ParentOf 560 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block2Chunk1Sources 1 0 == 689
      && tttLargeFiber60ParentOf 689 == 561
      && tttLargeFiber60ParentOf 561 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block2Chunk1Sources 2 0 == 690
      && tttLargeFiber60ParentOf 690 == 562
      && tttLargeFiber60ParentOf 562 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block2Chunk1Sources 3 0 == 691
      && tttLargeFiber60ParentOf 691 == 563
      && tttLargeFiber60ParentOf 563 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block2Chunk1Sources 4 0 == 692
      && tttLargeFiber60ParentOf 692 == 564
      && tttLargeFiber60ParentOf 564 == 560
      && tttLargeFiber60ParentOf 560 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block2Chunk1Sources 5 0 == 693
      && tttLargeFiber60ParentOf 693 == 565
      && tttLargeFiber60ParentOf 565 == 561
      && tttLargeFiber60ParentOf 561 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block2Chunk1Sources 6 0 == 694
      && tttLargeFiber60ParentOf 694 == 566
      && tttLargeFiber60ParentOf 566 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block2Chunk1Sources 7 0 == 695
      && tttLargeFiber60ParentOf 695 == 567
      && tttLargeFiber60ParentOf 567 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block2Chunk1Sources 8 0 == 696
      && tttLargeFiber60ParentOf 696 == 568
      && tttLargeFiber60ParentOf 568 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block2Chunk1Sources 9 0 == 697
      && tttLargeFiber60ParentOf 697 == 569
      && tttLargeFiber60ParentOf 569 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block2Chunk1Sources 10 0 == 698
      && tttLargeFiber60ParentOf 698 == 570
      && tttLargeFiber60ParentOf 570 == 554
      && tttLargeFiber60ParentOf 554 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block2Chunk1Sources 11 0 == 699
      && tttLargeFiber60ParentOf 699 == 571
      && tttLargeFiber60ParentOf 571 == 555
      && tttLargeFiber60ParentOf 555 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block2Chunk1Sources 12 0 == 700
      && tttLargeFiber60ParentOf 700 == 572
      && tttLargeFiber60ParentOf 572 == 568
      && tttLargeFiber60ParentOf 568 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block2Chunk1Sources 13 0 == 701
      && tttLargeFiber60ParentOf 701 == 573
      && tttLargeFiber60ParentOf 573 == 569
      && tttLargeFiber60ParentOf 569 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block2Chunk1Sources 14 0 == 702
      && tttLargeFiber60ParentOf 702 == 574
      && tttLargeFiber60ParentOf 574 == 558
      && tttLargeFiber60ParentOf 558 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block2Chunk1Sources 15 0 == 703
      && tttLargeFiber60ParentOf 703 == 575
      && tttLargeFiber60ParentOf 575 == 559
      && tttLargeFiber60ParentOf 559 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block2Chunk1Row_0_ok :
    tttLargeFiber60Block2Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1Row_1_ok :
    tttLargeFiber60Block2Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1Row_2_ok :
    tttLargeFiber60Block2Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1Row_3_ok :
    tttLargeFiber60Block2Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1Row_4_ok :
    tttLargeFiber60Block2Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1Row_5_ok :
    tttLargeFiber60Block2Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1Row_6_ok :
    tttLargeFiber60Block2Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1Row_7_ok :
    tttLargeFiber60Block2Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1Row_8_ok :
    tttLargeFiber60Block2Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1Row_9_ok :
    tttLargeFiber60Block2Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1Row_10_ok :
    tttLargeFiber60Block2Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1Row_11_ok :
    tttLargeFiber60Block2Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1Row_12_ok :
    tttLargeFiber60Block2Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1Row_13_ok :
    tttLargeFiber60Block2Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1Row_14_ok :
    tttLargeFiber60Block2Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1Row_15_ok :
    tttLargeFiber60Block2Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentMap_0_ok :
    tttLargeFiber60Block2Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentMap_1_ok :
    tttLargeFiber60Block2Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentMap_2_ok :
    tttLargeFiber60Block2Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentMap_3_ok :
    tttLargeFiber60Block2Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentMap_4_ok :
    tttLargeFiber60Block2Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentMap_5_ok :
    tttLargeFiber60Block2Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentMap_6_ok :
    tttLargeFiber60Block2Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentMap_7_ok :
    tttLargeFiber60Block2Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentMap_8_ok :
    tttLargeFiber60Block2Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentMap_9_ok :
    tttLargeFiber60Block2Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentMap_10_ok :
    tttLargeFiber60Block2Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentMap_11_ok :
    tttLargeFiber60Block2Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentMap_12_ok :
    tttLargeFiber60Block2Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentMap_13_ok :
    tttLargeFiber60Block2Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentMap_14_ok :
    tttLargeFiber60Block2Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentMap_15_ok :
    tttLargeFiber60Block2Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentPath_0_ok :
    tttLargeFiber60Block2Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentPath_1_ok :
    tttLargeFiber60Block2Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentPath_2_ok :
    tttLargeFiber60Block2Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentPath_3_ok :
    tttLargeFiber60Block2Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentPath_4_ok :
    tttLargeFiber60Block2Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentPath_5_ok :
    tttLargeFiber60Block2Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentPath_6_ok :
    tttLargeFiber60Block2Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentPath_7_ok :
    tttLargeFiber60Block2Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentPath_8_ok :
    tttLargeFiber60Block2Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentPath_9_ok :
    tttLargeFiber60Block2Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentPath_10_ok :
    tttLargeFiber60Block2Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentPath_11_ok :
    tttLargeFiber60Block2Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentPath_12_ok :
    tttLargeFiber60Block2Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentPath_13_ok :
    tttLargeFiber60Block2Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentPath_14_ok :
    tttLargeFiber60Block2Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block2Chunk1ParentPath_15_ok :
    tttLargeFiber60Block2Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block2Chunk1RowsAudit : Bool :=
  tttLargeFiber60Block2Chunk1RowCheck 0
    && tttLargeFiber60Block2Chunk1RowCheck 1
    && tttLargeFiber60Block2Chunk1RowCheck 2
    && tttLargeFiber60Block2Chunk1RowCheck 3
    && tttLargeFiber60Block2Chunk1RowCheck 4
    && tttLargeFiber60Block2Chunk1RowCheck 5
    && tttLargeFiber60Block2Chunk1RowCheck 6
    && tttLargeFiber60Block2Chunk1RowCheck 7
    && tttLargeFiber60Block2Chunk1RowCheck 8
    && tttLargeFiber60Block2Chunk1RowCheck 9
    && tttLargeFiber60Block2Chunk1RowCheck 10
    && tttLargeFiber60Block2Chunk1RowCheck 11
    && tttLargeFiber60Block2Chunk1RowCheck 12
    && tttLargeFiber60Block2Chunk1RowCheck 13
    && tttLargeFiber60Block2Chunk1RowCheck 14
    && tttLargeFiber60Block2Chunk1RowCheck 15

theorem tttLargeFiber60Block2Chunk1RowsAudit_ok :
    tttLargeFiber60Block2Chunk1RowsAudit = true := by
  simp [tttLargeFiber60Block2Chunk1RowsAudit,
    tttLargeFiber60Block2Chunk1Row_0_ok,
    tttLargeFiber60Block2Chunk1Row_1_ok,
    tttLargeFiber60Block2Chunk1Row_2_ok,
    tttLargeFiber60Block2Chunk1Row_3_ok,
    tttLargeFiber60Block2Chunk1Row_4_ok,
    tttLargeFiber60Block2Chunk1Row_5_ok,
    tttLargeFiber60Block2Chunk1Row_6_ok,
    tttLargeFiber60Block2Chunk1Row_7_ok,
    tttLargeFiber60Block2Chunk1Row_8_ok,
    tttLargeFiber60Block2Chunk1Row_9_ok,
    tttLargeFiber60Block2Chunk1Row_10_ok,
    tttLargeFiber60Block2Chunk1Row_11_ok,
    tttLargeFiber60Block2Chunk1Row_12_ok,
    tttLargeFiber60Block2Chunk1Row_13_ok,
    tttLargeFiber60Block2Chunk1Row_14_ok,
    tttLargeFiber60Block2Chunk1Row_15_ok]

def tttLargeFiber60Block2Chunk1ParentMapAudit : Bool :=
  tttLargeFiber60Block2Chunk1ParentMapCheck 0
    && tttLargeFiber60Block2Chunk1ParentMapCheck 1
    && tttLargeFiber60Block2Chunk1ParentMapCheck 2
    && tttLargeFiber60Block2Chunk1ParentMapCheck 3
    && tttLargeFiber60Block2Chunk1ParentMapCheck 4
    && tttLargeFiber60Block2Chunk1ParentMapCheck 5
    && tttLargeFiber60Block2Chunk1ParentMapCheck 6
    && tttLargeFiber60Block2Chunk1ParentMapCheck 7
    && tttLargeFiber60Block2Chunk1ParentMapCheck 8
    && tttLargeFiber60Block2Chunk1ParentMapCheck 9
    && tttLargeFiber60Block2Chunk1ParentMapCheck 10
    && tttLargeFiber60Block2Chunk1ParentMapCheck 11
    && tttLargeFiber60Block2Chunk1ParentMapCheck 12
    && tttLargeFiber60Block2Chunk1ParentMapCheck 13
    && tttLargeFiber60Block2Chunk1ParentMapCheck 14
    && tttLargeFiber60Block2Chunk1ParentMapCheck 15

theorem tttLargeFiber60Block2Chunk1ParentMapAudit_ok :
    tttLargeFiber60Block2Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber60Block2Chunk1ParentMapAudit,
    tttLargeFiber60Block2Chunk1ParentMap_0_ok,
    tttLargeFiber60Block2Chunk1ParentMap_1_ok,
    tttLargeFiber60Block2Chunk1ParentMap_2_ok,
    tttLargeFiber60Block2Chunk1ParentMap_3_ok,
    tttLargeFiber60Block2Chunk1ParentMap_4_ok,
    tttLargeFiber60Block2Chunk1ParentMap_5_ok,
    tttLargeFiber60Block2Chunk1ParentMap_6_ok,
    tttLargeFiber60Block2Chunk1ParentMap_7_ok,
    tttLargeFiber60Block2Chunk1ParentMap_8_ok,
    tttLargeFiber60Block2Chunk1ParentMap_9_ok,
    tttLargeFiber60Block2Chunk1ParentMap_10_ok,
    tttLargeFiber60Block2Chunk1ParentMap_11_ok,
    tttLargeFiber60Block2Chunk1ParentMap_12_ok,
    tttLargeFiber60Block2Chunk1ParentMap_13_ok,
    tttLargeFiber60Block2Chunk1ParentMap_14_ok,
    tttLargeFiber60Block2Chunk1ParentMap_15_ok]

def tttLargeFiber60Block2Chunk1ParentsAudit : Bool :=
  tttLargeFiber60Block2Chunk1ParentPathCheck 0
    && tttLargeFiber60Block2Chunk1ParentPathCheck 1
    && tttLargeFiber60Block2Chunk1ParentPathCheck 2
    && tttLargeFiber60Block2Chunk1ParentPathCheck 3
    && tttLargeFiber60Block2Chunk1ParentPathCheck 4
    && tttLargeFiber60Block2Chunk1ParentPathCheck 5
    && tttLargeFiber60Block2Chunk1ParentPathCheck 6
    && tttLargeFiber60Block2Chunk1ParentPathCheck 7
    && tttLargeFiber60Block2Chunk1ParentPathCheck 8
    && tttLargeFiber60Block2Chunk1ParentPathCheck 9
    && tttLargeFiber60Block2Chunk1ParentPathCheck 10
    && tttLargeFiber60Block2Chunk1ParentPathCheck 11
    && tttLargeFiber60Block2Chunk1ParentPathCheck 12
    && tttLargeFiber60Block2Chunk1ParentPathCheck 13
    && tttLargeFiber60Block2Chunk1ParentPathCheck 14
    && tttLargeFiber60Block2Chunk1ParentPathCheck 15

theorem tttLargeFiber60Block2Chunk1ParentsAudit_ok :
    tttLargeFiber60Block2Chunk1ParentsAudit = true := by
  simp [tttLargeFiber60Block2Chunk1ParentsAudit,
    tttLargeFiber60Block2Chunk1ParentPath_0_ok,
    tttLargeFiber60Block2Chunk1ParentPath_1_ok,
    tttLargeFiber60Block2Chunk1ParentPath_2_ok,
    tttLargeFiber60Block2Chunk1ParentPath_3_ok,
    tttLargeFiber60Block2Chunk1ParentPath_4_ok,
    tttLargeFiber60Block2Chunk1ParentPath_5_ok,
    tttLargeFiber60Block2Chunk1ParentPath_6_ok,
    tttLargeFiber60Block2Chunk1ParentPath_7_ok,
    tttLargeFiber60Block2Chunk1ParentPath_8_ok,
    tttLargeFiber60Block2Chunk1ParentPath_9_ok,
    tttLargeFiber60Block2Chunk1ParentPath_10_ok,
    tttLargeFiber60Block2Chunk1ParentPath_11_ok,
    tttLargeFiber60Block2Chunk1ParentPath_12_ok,
    tttLargeFiber60Block2Chunk1ParentPath_13_ok,
    tttLargeFiber60Block2Chunk1ParentPath_14_ok,
    tttLargeFiber60Block2Chunk1ParentPath_15_ok]

def tttLargeFiber60Block2Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block2Chunk1SourcesCheck &&
    tttLargeFiber60Block2Chunk1RowsAudit &&
    tttLargeFiber60Block2Chunk1ParentMapAudit &&
    tttLargeFiber60Block2Chunk1ParentsAudit

theorem tttLargeFiber60Block2Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber60Block2Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block2Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block2Chunk1SourcesCheck_ok,
    tttLargeFiber60Block2Chunk1RowsAudit_ok,
    tttLargeFiber60Block2Chunk1ParentMapAudit_ok,
    tttLargeFiber60Block2Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block2Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
