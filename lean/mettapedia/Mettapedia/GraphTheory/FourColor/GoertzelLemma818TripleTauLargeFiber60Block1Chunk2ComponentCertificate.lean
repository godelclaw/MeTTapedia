import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 1 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block1Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block1Chunk2Sources : List Nat :=
  [   640, 641, 642, 643, 644, 645, 646, 647,
   648, 649, 650, 651, 652, 653, 654, 655]

def tttLargeFiber60Row96 : TripleComponentParentRow :=
  tripleRow 640 576 17 108 132 16 100 132
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row97 : TripleComponentParentRow :=
  tripleRow 641 577 17 108 133 16 100 133
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row98 : TripleComponentParentRow :=
  tripleRow 642 578 17 108 134 16 100 134
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row99 : TripleComponentParentRow :=
  tripleRow 643 579 17 108 135 16 100 135
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row100 : TripleComponentParentRow :=
  tripleRow 644 580 17 108 180 16 100 180
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row101 : TripleComponentParentRow :=
  tripleRow 645 581 17 108 181 16 100 181
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row102 : TripleComponentParentRow :=
  tripleRow 646 582 17 108 182 16 100 182
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row103 : TripleComponentParentRow :=
  tripleRow 647 583 17 108 183 16 100 183
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row104 : TripleComponentParentRow :=
  tripleRow 648 584 17 109 140 16 101 140
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row105 : TripleComponentParentRow :=
  tripleRow 649 585 17 109 141 16 101 141
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row106 : TripleComponentParentRow :=
  tripleRow 650 586 17 109 142 16 101 142
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row107 : TripleComponentParentRow :=
  tripleRow 651 587 17 109 143 16 101 143
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row108 : TripleComponentParentRow :=
  tripleRow 652 588 17 109 188 16 101 188
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row109 : TripleComponentParentRow :=
  tripleRow 653 589 17 109 189 16 101 189
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row110 : TripleComponentParentRow :=
  tripleRow 654 590 17 109 190 16 101 190
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row111 : TripleComponentParentRow :=
  tripleRow 655 591 17 109 191 16 101 191
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Block1Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row96
  , tttLargeFiber60Row97
  , tttLargeFiber60Row98
  , tttLargeFiber60Row99
  , tttLargeFiber60Row100
  , tttLargeFiber60Row101
  , tttLargeFiber60Row102
  , tttLargeFiber60Row103
  , tttLargeFiber60Row104
  , tttLargeFiber60Row105
  , tttLargeFiber60Row106
  , tttLargeFiber60Row107
  , tttLargeFiber60Row108
  , tttLargeFiber60Row109
  , tttLargeFiber60Row110
  , tttLargeFiber60Row111
  ]

def tttLargeFiber60Block1Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block1Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block1Chunk2ExpectedContains row.source &&
    tttLargeFiber60Block1Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block1Chunk2SourcesCheck : Bool :=
  (tttLargeFiber60Block1Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber60Block1Chunk2Sources

theorem tttLargeFiber60Block1Chunk2SourcesCheck_ok :
    tttLargeFiber60Block1Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber60Block1Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block1Chunk2RowValid
    (listGetD tttLargeFiber60Block1Chunk2Rows i default)

def tttLargeFiber60Block1Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block1Chunk2Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block1Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block1Chunk2Sources 0 0 == 640
      && tttLargeFiber60ParentOf 640 == 576
      && tttLargeFiber60ParentOf 576 == 592
      && tttLargeFiber60ParentOf 592 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block1Chunk2Sources 1 0 == 641
      && tttLargeFiber60ParentOf 641 == 577
      && tttLargeFiber60ParentOf 577 == 593
      && tttLargeFiber60ParentOf 593 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block1Chunk2Sources 2 0 == 642
      && tttLargeFiber60ParentOf 642 == 578
      && tttLargeFiber60ParentOf 578 == 566
      && tttLargeFiber60ParentOf 566 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block1Chunk2Sources 3 0 == 643
      && tttLargeFiber60ParentOf 643 == 579
      && tttLargeFiber60ParentOf 579 == 567
      && tttLargeFiber60ParentOf 567 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block1Chunk2Sources 4 0 == 644
      && tttLargeFiber60ParentOf 644 == 580
      && tttLargeFiber60ParentOf 580 == 562
      && tttLargeFiber60ParentOf 562 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block1Chunk2Sources 5 0 == 645
      && tttLargeFiber60ParentOf 645 == 581
      && tttLargeFiber60ParentOf 581 == 583
      && tttLargeFiber60ParentOf 583 == 560
      && tttLargeFiber60ParentOf 560 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block1Chunk2Sources 6 0 == 646
      && tttLargeFiber60ParentOf 646 == 582
      && tttLargeFiber60ParentOf 582 == 561
      && tttLargeFiber60ParentOf 561 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block1Chunk2Sources 7 0 == 647
      && tttLargeFiber60ParentOf 647 == 583
      && tttLargeFiber60ParentOf 583 == 560
      && tttLargeFiber60ParentOf 560 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block1Chunk2Sources 8 0 == 648
      && tttLargeFiber60ParentOf 648 == 584
      && tttLargeFiber60ParentOf 584 == 600
      && tttLargeFiber60ParentOf 600 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block1Chunk2Sources 9 0 == 649
      && tttLargeFiber60ParentOf 649 == 585
      && tttLargeFiber60ParentOf 585 == 601
      && tttLargeFiber60ParentOf 601 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block1Chunk2Sources 10 0 == 650
      && tttLargeFiber60ParentOf 650 == 586
      && tttLargeFiber60ParentOf 586 == 602
      && tttLargeFiber60ParentOf 602 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block1Chunk2Sources 11 0 == 651
      && tttLargeFiber60ParentOf 651 == 587
      && tttLargeFiber60ParentOf 587 == 584
      && tttLargeFiber60ParentOf 584 == 600
      && tttLargeFiber60ParentOf 600 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block1Chunk2Sources 12 0 == 652
      && tttLargeFiber60ParentOf 652 == 588
      && tttLargeFiber60ParentOf 588 == 584
      && tttLargeFiber60ParentOf 584 == 600
      && tttLargeFiber60ParentOf 600 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block1Chunk2Sources 13 0 == 653
      && tttLargeFiber60ParentOf 653 == 589
      && tttLargeFiber60ParentOf 589 == 585
      && tttLargeFiber60ParentOf 585 == 601
      && tttLargeFiber60ParentOf 601 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block1Chunk2Sources 14 0 == 654
      && tttLargeFiber60ParentOf 654 == 590
      && tttLargeFiber60ParentOf 590 == 606
      && tttLargeFiber60ParentOf 606 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block1Chunk2Sources 15 0 == 655
      && tttLargeFiber60ParentOf 655 == 591
      && tttLargeFiber60ParentOf 591 == 607
      && tttLargeFiber60ParentOf 607 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block1Chunk2Row_0_ok :
    tttLargeFiber60Block1Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2Row_1_ok :
    tttLargeFiber60Block1Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2Row_2_ok :
    tttLargeFiber60Block1Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2Row_3_ok :
    tttLargeFiber60Block1Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2Row_4_ok :
    tttLargeFiber60Block1Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2Row_5_ok :
    tttLargeFiber60Block1Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2Row_6_ok :
    tttLargeFiber60Block1Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2Row_7_ok :
    tttLargeFiber60Block1Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2Row_8_ok :
    tttLargeFiber60Block1Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2Row_9_ok :
    tttLargeFiber60Block1Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2Row_10_ok :
    tttLargeFiber60Block1Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2Row_11_ok :
    tttLargeFiber60Block1Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2Row_12_ok :
    tttLargeFiber60Block1Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2Row_13_ok :
    tttLargeFiber60Block1Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2Row_14_ok :
    tttLargeFiber60Block1Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2Row_15_ok :
    tttLargeFiber60Block1Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentMap_0_ok :
    tttLargeFiber60Block1Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentMap_1_ok :
    tttLargeFiber60Block1Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentMap_2_ok :
    tttLargeFiber60Block1Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentMap_3_ok :
    tttLargeFiber60Block1Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentMap_4_ok :
    tttLargeFiber60Block1Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentMap_5_ok :
    tttLargeFiber60Block1Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentMap_6_ok :
    tttLargeFiber60Block1Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentMap_7_ok :
    tttLargeFiber60Block1Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentMap_8_ok :
    tttLargeFiber60Block1Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentMap_9_ok :
    tttLargeFiber60Block1Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentMap_10_ok :
    tttLargeFiber60Block1Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentMap_11_ok :
    tttLargeFiber60Block1Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentMap_12_ok :
    tttLargeFiber60Block1Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentMap_13_ok :
    tttLargeFiber60Block1Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentMap_14_ok :
    tttLargeFiber60Block1Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentMap_15_ok :
    tttLargeFiber60Block1Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentPath_0_ok :
    tttLargeFiber60Block1Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentPath_1_ok :
    tttLargeFiber60Block1Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentPath_2_ok :
    tttLargeFiber60Block1Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentPath_3_ok :
    tttLargeFiber60Block1Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentPath_4_ok :
    tttLargeFiber60Block1Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentPath_5_ok :
    tttLargeFiber60Block1Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentPath_6_ok :
    tttLargeFiber60Block1Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentPath_7_ok :
    tttLargeFiber60Block1Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentPath_8_ok :
    tttLargeFiber60Block1Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentPath_9_ok :
    tttLargeFiber60Block1Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentPath_10_ok :
    tttLargeFiber60Block1Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentPath_11_ok :
    tttLargeFiber60Block1Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentPath_12_ok :
    tttLargeFiber60Block1Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentPath_13_ok :
    tttLargeFiber60Block1Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentPath_14_ok :
    tttLargeFiber60Block1Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block1Chunk2ParentPath_15_ok :
    tttLargeFiber60Block1Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block1Chunk2RowsAudit : Bool :=
  tttLargeFiber60Block1Chunk2RowCheck 0
    && tttLargeFiber60Block1Chunk2RowCheck 1
    && tttLargeFiber60Block1Chunk2RowCheck 2
    && tttLargeFiber60Block1Chunk2RowCheck 3
    && tttLargeFiber60Block1Chunk2RowCheck 4
    && tttLargeFiber60Block1Chunk2RowCheck 5
    && tttLargeFiber60Block1Chunk2RowCheck 6
    && tttLargeFiber60Block1Chunk2RowCheck 7
    && tttLargeFiber60Block1Chunk2RowCheck 8
    && tttLargeFiber60Block1Chunk2RowCheck 9
    && tttLargeFiber60Block1Chunk2RowCheck 10
    && tttLargeFiber60Block1Chunk2RowCheck 11
    && tttLargeFiber60Block1Chunk2RowCheck 12
    && tttLargeFiber60Block1Chunk2RowCheck 13
    && tttLargeFiber60Block1Chunk2RowCheck 14
    && tttLargeFiber60Block1Chunk2RowCheck 15

theorem tttLargeFiber60Block1Chunk2RowsAudit_ok :
    tttLargeFiber60Block1Chunk2RowsAudit = true := by
  simp [tttLargeFiber60Block1Chunk2RowsAudit,
    tttLargeFiber60Block1Chunk2Row_0_ok,
    tttLargeFiber60Block1Chunk2Row_1_ok,
    tttLargeFiber60Block1Chunk2Row_2_ok,
    tttLargeFiber60Block1Chunk2Row_3_ok,
    tttLargeFiber60Block1Chunk2Row_4_ok,
    tttLargeFiber60Block1Chunk2Row_5_ok,
    tttLargeFiber60Block1Chunk2Row_6_ok,
    tttLargeFiber60Block1Chunk2Row_7_ok,
    tttLargeFiber60Block1Chunk2Row_8_ok,
    tttLargeFiber60Block1Chunk2Row_9_ok,
    tttLargeFiber60Block1Chunk2Row_10_ok,
    tttLargeFiber60Block1Chunk2Row_11_ok,
    tttLargeFiber60Block1Chunk2Row_12_ok,
    tttLargeFiber60Block1Chunk2Row_13_ok,
    tttLargeFiber60Block1Chunk2Row_14_ok,
    tttLargeFiber60Block1Chunk2Row_15_ok]

def tttLargeFiber60Block1Chunk2ParentMapAudit : Bool :=
  tttLargeFiber60Block1Chunk2ParentMapCheck 0
    && tttLargeFiber60Block1Chunk2ParentMapCheck 1
    && tttLargeFiber60Block1Chunk2ParentMapCheck 2
    && tttLargeFiber60Block1Chunk2ParentMapCheck 3
    && tttLargeFiber60Block1Chunk2ParentMapCheck 4
    && tttLargeFiber60Block1Chunk2ParentMapCheck 5
    && tttLargeFiber60Block1Chunk2ParentMapCheck 6
    && tttLargeFiber60Block1Chunk2ParentMapCheck 7
    && tttLargeFiber60Block1Chunk2ParentMapCheck 8
    && tttLargeFiber60Block1Chunk2ParentMapCheck 9
    && tttLargeFiber60Block1Chunk2ParentMapCheck 10
    && tttLargeFiber60Block1Chunk2ParentMapCheck 11
    && tttLargeFiber60Block1Chunk2ParentMapCheck 12
    && tttLargeFiber60Block1Chunk2ParentMapCheck 13
    && tttLargeFiber60Block1Chunk2ParentMapCheck 14
    && tttLargeFiber60Block1Chunk2ParentMapCheck 15

theorem tttLargeFiber60Block1Chunk2ParentMapAudit_ok :
    tttLargeFiber60Block1Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber60Block1Chunk2ParentMapAudit,
    tttLargeFiber60Block1Chunk2ParentMap_0_ok,
    tttLargeFiber60Block1Chunk2ParentMap_1_ok,
    tttLargeFiber60Block1Chunk2ParentMap_2_ok,
    tttLargeFiber60Block1Chunk2ParentMap_3_ok,
    tttLargeFiber60Block1Chunk2ParentMap_4_ok,
    tttLargeFiber60Block1Chunk2ParentMap_5_ok,
    tttLargeFiber60Block1Chunk2ParentMap_6_ok,
    tttLargeFiber60Block1Chunk2ParentMap_7_ok,
    tttLargeFiber60Block1Chunk2ParentMap_8_ok,
    tttLargeFiber60Block1Chunk2ParentMap_9_ok,
    tttLargeFiber60Block1Chunk2ParentMap_10_ok,
    tttLargeFiber60Block1Chunk2ParentMap_11_ok,
    tttLargeFiber60Block1Chunk2ParentMap_12_ok,
    tttLargeFiber60Block1Chunk2ParentMap_13_ok,
    tttLargeFiber60Block1Chunk2ParentMap_14_ok,
    tttLargeFiber60Block1Chunk2ParentMap_15_ok]

def tttLargeFiber60Block1Chunk2ParentsAudit : Bool :=
  tttLargeFiber60Block1Chunk2ParentPathCheck 0
    && tttLargeFiber60Block1Chunk2ParentPathCheck 1
    && tttLargeFiber60Block1Chunk2ParentPathCheck 2
    && tttLargeFiber60Block1Chunk2ParentPathCheck 3
    && tttLargeFiber60Block1Chunk2ParentPathCheck 4
    && tttLargeFiber60Block1Chunk2ParentPathCheck 5
    && tttLargeFiber60Block1Chunk2ParentPathCheck 6
    && tttLargeFiber60Block1Chunk2ParentPathCheck 7
    && tttLargeFiber60Block1Chunk2ParentPathCheck 8
    && tttLargeFiber60Block1Chunk2ParentPathCheck 9
    && tttLargeFiber60Block1Chunk2ParentPathCheck 10
    && tttLargeFiber60Block1Chunk2ParentPathCheck 11
    && tttLargeFiber60Block1Chunk2ParentPathCheck 12
    && tttLargeFiber60Block1Chunk2ParentPathCheck 13
    && tttLargeFiber60Block1Chunk2ParentPathCheck 14
    && tttLargeFiber60Block1Chunk2ParentPathCheck 15

theorem tttLargeFiber60Block1Chunk2ParentsAudit_ok :
    tttLargeFiber60Block1Chunk2ParentsAudit = true := by
  simp [tttLargeFiber60Block1Chunk2ParentsAudit,
    tttLargeFiber60Block1Chunk2ParentPath_0_ok,
    tttLargeFiber60Block1Chunk2ParentPath_1_ok,
    tttLargeFiber60Block1Chunk2ParentPath_2_ok,
    tttLargeFiber60Block1Chunk2ParentPath_3_ok,
    tttLargeFiber60Block1Chunk2ParentPath_4_ok,
    tttLargeFiber60Block1Chunk2ParentPath_5_ok,
    tttLargeFiber60Block1Chunk2ParentPath_6_ok,
    tttLargeFiber60Block1Chunk2ParentPath_7_ok,
    tttLargeFiber60Block1Chunk2ParentPath_8_ok,
    tttLargeFiber60Block1Chunk2ParentPath_9_ok,
    tttLargeFiber60Block1Chunk2ParentPath_10_ok,
    tttLargeFiber60Block1Chunk2ParentPath_11_ok,
    tttLargeFiber60Block1Chunk2ParentPath_12_ok,
    tttLargeFiber60Block1Chunk2ParentPath_13_ok,
    tttLargeFiber60Block1Chunk2ParentPath_14_ok,
    tttLargeFiber60Block1Chunk2ParentPath_15_ok]

def tttLargeFiber60Block1Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block1Chunk2SourcesCheck &&
    tttLargeFiber60Block1Chunk2RowsAudit &&
    tttLargeFiber60Block1Chunk2ParentMapAudit &&
    tttLargeFiber60Block1Chunk2ParentsAudit

theorem tttLargeFiber60Block1Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber60Block1Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block1Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block1Chunk2SourcesCheck_ok,
    tttLargeFiber60Block1Chunk2RowsAudit_ok,
    tttLargeFiber60Block1Chunk2ParentMapAudit_ok,
    tttLargeFiber60Block1Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block1Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
