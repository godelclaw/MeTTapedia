import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 1 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block1Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block1Chunk3Sources : List Nat :=
  [   656, 657, 658, 659, 660, 661, 662, 663,
   664, 665, 666, 667, 668, 669, 670, 671]

def tttLargeFiber60Row112 : TripleComponentParentRow :=
  tripleRow 656 592 17 110 64 16 102 64
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row113 : TripleComponentParentRow :=
  tripleRow 657 593 17 110 65 16 102 65
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row114 : TripleComponentParentRow :=
  tripleRow 658 594 17 110 66 16 102 66
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row115 : TripleComponentParentRow :=
  tripleRow 659 595 17 110 67 16 102 67
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row116 : TripleComponentParentRow :=
  tripleRow 660 596 17 110 116 16 102 116
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row117 : TripleComponentParentRow :=
  tripleRow 661 597 17 110 117 16 102 117
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row118 : TripleComponentParentRow :=
  tripleRow 662 598 17 110 118 16 102 118
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row119 : TripleComponentParentRow :=
  tripleRow 663 599 17 110 119 16 102 119
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row120 : TripleComponentParentRow :=
  tripleRow 664 600 17 111 72 16 103 72
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row121 : TripleComponentParentRow :=
  tripleRow 665 601 17 111 73 16 103 73
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row122 : TripleComponentParentRow :=
  tripleRow 666 602 17 111 74 16 103 74
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row123 : TripleComponentParentRow :=
  tripleRow 667 603 17 111 75 16 103 75
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row124 : TripleComponentParentRow :=
  tripleRow 668 604 17 111 124 16 103 124
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row125 : TripleComponentParentRow :=
  tripleRow 669 605 17 111 125 16 103 125
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row126 : TripleComponentParentRow :=
  tripleRow 670 606 17 111 126 16 103 126
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Row127 : TripleComponentParentRow :=
  tripleRow 671 607 17 111 127 16 103 127
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber60Block1Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row112
  , tttLargeFiber60Row113
  , tttLargeFiber60Row114
  , tttLargeFiber60Row115
  , tttLargeFiber60Row116
  , tttLargeFiber60Row117
  , tttLargeFiber60Row118
  , tttLargeFiber60Row119
  , tttLargeFiber60Row120
  , tttLargeFiber60Row121
  , tttLargeFiber60Row122
  , tttLargeFiber60Row123
  , tttLargeFiber60Row124
  , tttLargeFiber60Row125
  , tttLargeFiber60Row126
  , tttLargeFiber60Row127
  ]

def tttLargeFiber60Block1Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block1Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block1Chunk3ExpectedContains row.source &&
    tttLargeFiber60Block1Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block1Chunk3SourcesCheck : Bool :=
  (tttLargeFiber60Block1Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber60Block1Chunk3Sources

theorem tttLargeFiber60Block1Chunk3SourcesCheck_ok :
    tttLargeFiber60Block1Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber60Block1Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block1Chunk3RowValid
    (listGetD tttLargeFiber60Block1Chunk3Rows i default)

def tttLargeFiber60Block1Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block1Chunk3Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block1Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block1Chunk3Sources 0 0 == 656
      && tttLargeFiber60ParentOf 656 == 592
      && tttLargeFiber60ParentOf 592 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block1Chunk3Sources 1 0 == 657
      && tttLargeFiber60ParentOf 657 == 593
      && tttLargeFiber60ParentOf 593 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block1Chunk3Sources 2 0 == 658
      && tttLargeFiber60ParentOf 658 == 594
      && tttLargeFiber60ParentOf 594 == 554
      && tttLargeFiber60ParentOf 554 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block1Chunk3Sources 3 0 == 659
      && tttLargeFiber60ParentOf 659 == 595
      && tttLargeFiber60ParentOf 595 == 555
      && tttLargeFiber60ParentOf 555 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block1Chunk3Sources 4 0 == 660
      && tttLargeFiber60ParentOf 660 == 596
      && tttLargeFiber60ParentOf 596 == 556
      && tttLargeFiber60ParentOf 556 == 548
      && tttLargeFiber60ParentOf 548 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block1Chunk3Sources 5 0 == 661
      && tttLargeFiber60ParentOf 661 == 597
      && tttLargeFiber60ParentOf 597 == 557
      && tttLargeFiber60ParentOf 557 == 549
      && tttLargeFiber60ParentOf 549 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block1Chunk3Sources 6 0 == 662
      && tttLargeFiber60ParentOf 662 == 598
      && tttLargeFiber60ParentOf 598 == 558
      && tttLargeFiber60ParentOf 558 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block1Chunk3Sources 7 0 == 663
      && tttLargeFiber60ParentOf 663 == 599
      && tttLargeFiber60ParentOf 599 == 559
      && tttLargeFiber60ParentOf 559 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block1Chunk3Sources 8 0 == 664
      && tttLargeFiber60ParentOf 664 == 600
      && tttLargeFiber60ParentOf 600 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block1Chunk3Sources 9 0 == 665
      && tttLargeFiber60ParentOf 665 == 601
      && tttLargeFiber60ParentOf 601 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block1Chunk3Sources 10 0 == 666
      && tttLargeFiber60ParentOf 666 == 602
      && tttLargeFiber60ParentOf 602 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block1Chunk3Sources 11 0 == 667
      && tttLargeFiber60ParentOf 667 == 603
      && tttLargeFiber60ParentOf 603 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block1Chunk3Sources 12 0 == 668
      && tttLargeFiber60ParentOf 668 == 604
      && tttLargeFiber60ParentOf 604 == 548
      && tttLargeFiber60ParentOf 548 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block1Chunk3Sources 13 0 == 669
      && tttLargeFiber60ParentOf 669 == 605
      && tttLargeFiber60ParentOf 605 == 549
      && tttLargeFiber60ParentOf 549 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block1Chunk3Sources 14 0 == 670
      && tttLargeFiber60ParentOf 670 == 606
      && tttLargeFiber60ParentOf 606 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block1Chunk3Sources 15 0 == 671
      && tttLargeFiber60ParentOf 671 == 607
      && tttLargeFiber60ParentOf 607 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block1Chunk3Row_0_ok :
    tttLargeFiber60Block1Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3Row_1_ok :
    tttLargeFiber60Block1Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3Row_2_ok :
    tttLargeFiber60Block1Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3Row_3_ok :
    tttLargeFiber60Block1Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3Row_4_ok :
    tttLargeFiber60Block1Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3Row_5_ok :
    tttLargeFiber60Block1Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3Row_6_ok :
    tttLargeFiber60Block1Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3Row_7_ok :
    tttLargeFiber60Block1Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3Row_8_ok :
    tttLargeFiber60Block1Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3Row_9_ok :
    tttLargeFiber60Block1Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3Row_10_ok :
    tttLargeFiber60Block1Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3Row_11_ok :
    tttLargeFiber60Block1Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3Row_12_ok :
    tttLargeFiber60Block1Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3Row_13_ok :
    tttLargeFiber60Block1Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3Row_14_ok :
    tttLargeFiber60Block1Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3Row_15_ok :
    tttLargeFiber60Block1Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentMap_0_ok :
    tttLargeFiber60Block1Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentMap_1_ok :
    tttLargeFiber60Block1Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentMap_2_ok :
    tttLargeFiber60Block1Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentMap_3_ok :
    tttLargeFiber60Block1Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentMap_4_ok :
    tttLargeFiber60Block1Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentMap_5_ok :
    tttLargeFiber60Block1Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentMap_6_ok :
    tttLargeFiber60Block1Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentMap_7_ok :
    tttLargeFiber60Block1Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentMap_8_ok :
    tttLargeFiber60Block1Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentMap_9_ok :
    tttLargeFiber60Block1Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentMap_10_ok :
    tttLargeFiber60Block1Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentMap_11_ok :
    tttLargeFiber60Block1Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentMap_12_ok :
    tttLargeFiber60Block1Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentMap_13_ok :
    tttLargeFiber60Block1Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentMap_14_ok :
    tttLargeFiber60Block1Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentMap_15_ok :
    tttLargeFiber60Block1Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentPath_0_ok :
    tttLargeFiber60Block1Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentPath_1_ok :
    tttLargeFiber60Block1Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentPath_2_ok :
    tttLargeFiber60Block1Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentPath_3_ok :
    tttLargeFiber60Block1Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentPath_4_ok :
    tttLargeFiber60Block1Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentPath_5_ok :
    tttLargeFiber60Block1Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentPath_6_ok :
    tttLargeFiber60Block1Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentPath_7_ok :
    tttLargeFiber60Block1Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentPath_8_ok :
    tttLargeFiber60Block1Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentPath_9_ok :
    tttLargeFiber60Block1Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentPath_10_ok :
    tttLargeFiber60Block1Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentPath_11_ok :
    tttLargeFiber60Block1Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentPath_12_ok :
    tttLargeFiber60Block1Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentPath_13_ok :
    tttLargeFiber60Block1Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentPath_14_ok :
    tttLargeFiber60Block1Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block1Chunk3ParentPath_15_ok :
    tttLargeFiber60Block1Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block1Chunk3RowsAudit : Bool :=
  tttLargeFiber60Block1Chunk3RowCheck 0
    && tttLargeFiber60Block1Chunk3RowCheck 1
    && tttLargeFiber60Block1Chunk3RowCheck 2
    && tttLargeFiber60Block1Chunk3RowCheck 3
    && tttLargeFiber60Block1Chunk3RowCheck 4
    && tttLargeFiber60Block1Chunk3RowCheck 5
    && tttLargeFiber60Block1Chunk3RowCheck 6
    && tttLargeFiber60Block1Chunk3RowCheck 7
    && tttLargeFiber60Block1Chunk3RowCheck 8
    && tttLargeFiber60Block1Chunk3RowCheck 9
    && tttLargeFiber60Block1Chunk3RowCheck 10
    && tttLargeFiber60Block1Chunk3RowCheck 11
    && tttLargeFiber60Block1Chunk3RowCheck 12
    && tttLargeFiber60Block1Chunk3RowCheck 13
    && tttLargeFiber60Block1Chunk3RowCheck 14
    && tttLargeFiber60Block1Chunk3RowCheck 15

theorem tttLargeFiber60Block1Chunk3RowsAudit_ok :
    tttLargeFiber60Block1Chunk3RowsAudit = true := by
  simp [tttLargeFiber60Block1Chunk3RowsAudit,
    tttLargeFiber60Block1Chunk3Row_0_ok,
    tttLargeFiber60Block1Chunk3Row_1_ok,
    tttLargeFiber60Block1Chunk3Row_2_ok,
    tttLargeFiber60Block1Chunk3Row_3_ok,
    tttLargeFiber60Block1Chunk3Row_4_ok,
    tttLargeFiber60Block1Chunk3Row_5_ok,
    tttLargeFiber60Block1Chunk3Row_6_ok,
    tttLargeFiber60Block1Chunk3Row_7_ok,
    tttLargeFiber60Block1Chunk3Row_8_ok,
    tttLargeFiber60Block1Chunk3Row_9_ok,
    tttLargeFiber60Block1Chunk3Row_10_ok,
    tttLargeFiber60Block1Chunk3Row_11_ok,
    tttLargeFiber60Block1Chunk3Row_12_ok,
    tttLargeFiber60Block1Chunk3Row_13_ok,
    tttLargeFiber60Block1Chunk3Row_14_ok,
    tttLargeFiber60Block1Chunk3Row_15_ok]

def tttLargeFiber60Block1Chunk3ParentMapAudit : Bool :=
  tttLargeFiber60Block1Chunk3ParentMapCheck 0
    && tttLargeFiber60Block1Chunk3ParentMapCheck 1
    && tttLargeFiber60Block1Chunk3ParentMapCheck 2
    && tttLargeFiber60Block1Chunk3ParentMapCheck 3
    && tttLargeFiber60Block1Chunk3ParentMapCheck 4
    && tttLargeFiber60Block1Chunk3ParentMapCheck 5
    && tttLargeFiber60Block1Chunk3ParentMapCheck 6
    && tttLargeFiber60Block1Chunk3ParentMapCheck 7
    && tttLargeFiber60Block1Chunk3ParentMapCheck 8
    && tttLargeFiber60Block1Chunk3ParentMapCheck 9
    && tttLargeFiber60Block1Chunk3ParentMapCheck 10
    && tttLargeFiber60Block1Chunk3ParentMapCheck 11
    && tttLargeFiber60Block1Chunk3ParentMapCheck 12
    && tttLargeFiber60Block1Chunk3ParentMapCheck 13
    && tttLargeFiber60Block1Chunk3ParentMapCheck 14
    && tttLargeFiber60Block1Chunk3ParentMapCheck 15

theorem tttLargeFiber60Block1Chunk3ParentMapAudit_ok :
    tttLargeFiber60Block1Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber60Block1Chunk3ParentMapAudit,
    tttLargeFiber60Block1Chunk3ParentMap_0_ok,
    tttLargeFiber60Block1Chunk3ParentMap_1_ok,
    tttLargeFiber60Block1Chunk3ParentMap_2_ok,
    tttLargeFiber60Block1Chunk3ParentMap_3_ok,
    tttLargeFiber60Block1Chunk3ParentMap_4_ok,
    tttLargeFiber60Block1Chunk3ParentMap_5_ok,
    tttLargeFiber60Block1Chunk3ParentMap_6_ok,
    tttLargeFiber60Block1Chunk3ParentMap_7_ok,
    tttLargeFiber60Block1Chunk3ParentMap_8_ok,
    tttLargeFiber60Block1Chunk3ParentMap_9_ok,
    tttLargeFiber60Block1Chunk3ParentMap_10_ok,
    tttLargeFiber60Block1Chunk3ParentMap_11_ok,
    tttLargeFiber60Block1Chunk3ParentMap_12_ok,
    tttLargeFiber60Block1Chunk3ParentMap_13_ok,
    tttLargeFiber60Block1Chunk3ParentMap_14_ok,
    tttLargeFiber60Block1Chunk3ParentMap_15_ok]

def tttLargeFiber60Block1Chunk3ParentsAudit : Bool :=
  tttLargeFiber60Block1Chunk3ParentPathCheck 0
    && tttLargeFiber60Block1Chunk3ParentPathCheck 1
    && tttLargeFiber60Block1Chunk3ParentPathCheck 2
    && tttLargeFiber60Block1Chunk3ParentPathCheck 3
    && tttLargeFiber60Block1Chunk3ParentPathCheck 4
    && tttLargeFiber60Block1Chunk3ParentPathCheck 5
    && tttLargeFiber60Block1Chunk3ParentPathCheck 6
    && tttLargeFiber60Block1Chunk3ParentPathCheck 7
    && tttLargeFiber60Block1Chunk3ParentPathCheck 8
    && tttLargeFiber60Block1Chunk3ParentPathCheck 9
    && tttLargeFiber60Block1Chunk3ParentPathCheck 10
    && tttLargeFiber60Block1Chunk3ParentPathCheck 11
    && tttLargeFiber60Block1Chunk3ParentPathCheck 12
    && tttLargeFiber60Block1Chunk3ParentPathCheck 13
    && tttLargeFiber60Block1Chunk3ParentPathCheck 14
    && tttLargeFiber60Block1Chunk3ParentPathCheck 15

theorem tttLargeFiber60Block1Chunk3ParentsAudit_ok :
    tttLargeFiber60Block1Chunk3ParentsAudit = true := by
  simp [tttLargeFiber60Block1Chunk3ParentsAudit,
    tttLargeFiber60Block1Chunk3ParentPath_0_ok,
    tttLargeFiber60Block1Chunk3ParentPath_1_ok,
    tttLargeFiber60Block1Chunk3ParentPath_2_ok,
    tttLargeFiber60Block1Chunk3ParentPath_3_ok,
    tttLargeFiber60Block1Chunk3ParentPath_4_ok,
    tttLargeFiber60Block1Chunk3ParentPath_5_ok,
    tttLargeFiber60Block1Chunk3ParentPath_6_ok,
    tttLargeFiber60Block1Chunk3ParentPath_7_ok,
    tttLargeFiber60Block1Chunk3ParentPath_8_ok,
    tttLargeFiber60Block1Chunk3ParentPath_9_ok,
    tttLargeFiber60Block1Chunk3ParentPath_10_ok,
    tttLargeFiber60Block1Chunk3ParentPath_11_ok,
    tttLargeFiber60Block1Chunk3ParentPath_12_ok,
    tttLargeFiber60Block1Chunk3ParentPath_13_ok,
    tttLargeFiber60Block1Chunk3ParentPath_14_ok,
    tttLargeFiber60Block1Chunk3ParentPath_15_ok]

def tttLargeFiber60Block1Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block1Chunk3SourcesCheck &&
    tttLargeFiber60Block1Chunk3RowsAudit &&
    tttLargeFiber60Block1Chunk3ParentMapAudit &&
    tttLargeFiber60Block1Chunk3ParentsAudit

theorem tttLargeFiber60Block1Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber60Block1Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block1Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block1Chunk3SourcesCheck_ok,
    tttLargeFiber60Block1Chunk3RowsAudit_ok,
    tttLargeFiber60Block1Chunk3ParentMapAudit_ok,
    tttLargeFiber60Block1Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block1Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
