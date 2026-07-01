import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 3 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block3Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block3Chunk3Sources : List Nat :=
  [   784, 785, 786, 787, 788, 789, 790, 791,
   792, 793, 794, 795, 796, 797, 798, 799]

def tttLargeFiber60Row240 : TripleComponentParentRow :=
  tripleRow 784 656 19 42 0 17 110 64
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber60Row241 : TripleComponentParentRow :=
  tripleRow 785 657 19 42 1 17 110 65
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber60Row242 : TripleComponentParentRow :=
  tripleRow 786 658 19 42 2 17 110 66
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber60Row243 : TripleComponentParentRow :=
  tripleRow 787 659 19 42 3 17 110 67
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber60Row244 : TripleComponentParentRow :=
  tripleRow 788 784 19 42 48 19 42 0
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row245 : TripleComponentParentRow :=
  tripleRow 789 785 19 42 49 19 42 1
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row246 : TripleComponentParentRow :=
  tripleRow 790 662 19 42 50 17 110 118
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber60Row247 : TripleComponentParentRow :=
  tripleRow 791 663 19 42 51 17 110 119
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber60Row248 : TripleComponentParentRow :=
  tripleRow 792 664 19 43 8 17 111 72
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber60Row249 : TripleComponentParentRow :=
  tripleRow 793 665 19 43 9 17 111 73
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber60Row250 : TripleComponentParentRow :=
  tripleRow 794 666 19 43 10 17 111 74
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber60Row251 : TripleComponentParentRow :=
  tripleRow 795 667 19 43 11 17 111 75
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber60Row252 : TripleComponentParentRow :=
  tripleRow 796 792 19 43 56 19 43 8
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row253 : TripleComponentParentRow :=
  tripleRow 797 793 19 43 57 19 43 9
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row254 : TripleComponentParentRow :=
  tripleRow 798 670 19 43 58 17 111 126
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber60Row255 : TripleComponentParentRow :=
  tripleRow 799 671 19 43 59 17 111 127
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber60Block3Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row240
  , tttLargeFiber60Row241
  , tttLargeFiber60Row242
  , tttLargeFiber60Row243
  , tttLargeFiber60Row244
  , tttLargeFiber60Row245
  , tttLargeFiber60Row246
  , tttLargeFiber60Row247
  , tttLargeFiber60Row248
  , tttLargeFiber60Row249
  , tttLargeFiber60Row250
  , tttLargeFiber60Row251
  , tttLargeFiber60Row252
  , tttLargeFiber60Row253
  , tttLargeFiber60Row254
  , tttLargeFiber60Row255
  ]

def tttLargeFiber60Block3Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block3Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block3Chunk3ExpectedContains row.source &&
    tttLargeFiber60Block3Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block3Chunk3SourcesCheck : Bool :=
  (tttLargeFiber60Block3Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber60Block3Chunk3Sources

theorem tttLargeFiber60Block3Chunk3SourcesCheck_ok :
    tttLargeFiber60Block3Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber60Block3Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block3Chunk3RowValid
    (listGetD tttLargeFiber60Block3Chunk3Rows i default)

def tttLargeFiber60Block3Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block3Chunk3Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block3Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block3Chunk3Sources 0 0 == 784
      && tttLargeFiber60ParentOf 784 == 656
      && tttLargeFiber60ParentOf 656 == 592
      && tttLargeFiber60ParentOf 592 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block3Chunk3Sources 1 0 == 785
      && tttLargeFiber60ParentOf 785 == 657
      && tttLargeFiber60ParentOf 657 == 593
      && tttLargeFiber60ParentOf 593 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block3Chunk3Sources 2 0 == 786
      && tttLargeFiber60ParentOf 786 == 658
      && tttLargeFiber60ParentOf 658 == 594
      && tttLargeFiber60ParentOf 594 == 554
      && tttLargeFiber60ParentOf 554 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block3Chunk3Sources 3 0 == 787
      && tttLargeFiber60ParentOf 787 == 659
      && tttLargeFiber60ParentOf 659 == 595
      && tttLargeFiber60ParentOf 595 == 555
      && tttLargeFiber60ParentOf 555 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (6 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block3Chunk3Sources 4 0 == 788
      && tttLargeFiber60ParentOf 788 == 784
      && tttLargeFiber60ParentOf 784 == 656
      && tttLargeFiber60ParentOf 656 == 592
      && tttLargeFiber60ParentOf 592 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block3Chunk3Sources 5 0 == 789
      && tttLargeFiber60ParentOf 789 == 785
      && tttLargeFiber60ParentOf 785 == 657
      && tttLargeFiber60ParentOf 657 == 593
      && tttLargeFiber60ParentOf 593 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (6 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block3Chunk3Sources 6 0 == 790
      && tttLargeFiber60ParentOf 790 == 662
      && tttLargeFiber60ParentOf 662 == 598
      && tttLargeFiber60ParentOf 598 == 558
      && tttLargeFiber60ParentOf 558 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (6 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block3Chunk3Sources 7 0 == 791
      && tttLargeFiber60ParentOf 791 == 663
      && tttLargeFiber60ParentOf 663 == 599
      && tttLargeFiber60ParentOf 599 == 559
      && tttLargeFiber60ParentOf 559 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block3Chunk3Sources 8 0 == 792
      && tttLargeFiber60ParentOf 792 == 664
      && tttLargeFiber60ParentOf 664 == 600
      && tttLargeFiber60ParentOf 600 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block3Chunk3Sources 9 0 == 793
      && tttLargeFiber60ParentOf 793 == 665
      && tttLargeFiber60ParentOf 665 == 601
      && tttLargeFiber60ParentOf 601 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block3Chunk3Sources 10 0 == 794
      && tttLargeFiber60ParentOf 794 == 666
      && tttLargeFiber60ParentOf 666 == 602
      && tttLargeFiber60ParentOf 602 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block3Chunk3Sources 11 0 == 795
      && tttLargeFiber60ParentOf 795 == 667
      && tttLargeFiber60ParentOf 667 == 603
      && tttLargeFiber60ParentOf 603 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block3Chunk3Sources 12 0 == 796
      && tttLargeFiber60ParentOf 796 == 792
      && tttLargeFiber60ParentOf 792 == 664
      && tttLargeFiber60ParentOf 664 == 600
      && tttLargeFiber60ParentOf 600 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block3Chunk3Sources 13 0 == 797
      && tttLargeFiber60ParentOf 797 == 793
      && tttLargeFiber60ParentOf 793 == 665
      && tttLargeFiber60ParentOf 665 == 601
      && tttLargeFiber60ParentOf 601 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block3Chunk3Sources 14 0 == 798
      && tttLargeFiber60ParentOf 798 == 670
      && tttLargeFiber60ParentOf 670 == 606
      && tttLargeFiber60ParentOf 606 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block3Chunk3Sources 15 0 == 799
      && tttLargeFiber60ParentOf 799 == 671
      && tttLargeFiber60ParentOf 671 == 607
      && tttLargeFiber60ParentOf 607 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block3Chunk3Row_0_ok :
    tttLargeFiber60Block3Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3Row_1_ok :
    tttLargeFiber60Block3Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3Row_2_ok :
    tttLargeFiber60Block3Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3Row_3_ok :
    tttLargeFiber60Block3Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3Row_4_ok :
    tttLargeFiber60Block3Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3Row_5_ok :
    tttLargeFiber60Block3Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3Row_6_ok :
    tttLargeFiber60Block3Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3Row_7_ok :
    tttLargeFiber60Block3Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3Row_8_ok :
    tttLargeFiber60Block3Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3Row_9_ok :
    tttLargeFiber60Block3Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3Row_10_ok :
    tttLargeFiber60Block3Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3Row_11_ok :
    tttLargeFiber60Block3Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3Row_12_ok :
    tttLargeFiber60Block3Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3Row_13_ok :
    tttLargeFiber60Block3Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3Row_14_ok :
    tttLargeFiber60Block3Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3Row_15_ok :
    tttLargeFiber60Block3Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentMap_0_ok :
    tttLargeFiber60Block3Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentMap_1_ok :
    tttLargeFiber60Block3Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentMap_2_ok :
    tttLargeFiber60Block3Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentMap_3_ok :
    tttLargeFiber60Block3Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentMap_4_ok :
    tttLargeFiber60Block3Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentMap_5_ok :
    tttLargeFiber60Block3Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentMap_6_ok :
    tttLargeFiber60Block3Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentMap_7_ok :
    tttLargeFiber60Block3Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentMap_8_ok :
    tttLargeFiber60Block3Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentMap_9_ok :
    tttLargeFiber60Block3Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentMap_10_ok :
    tttLargeFiber60Block3Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentMap_11_ok :
    tttLargeFiber60Block3Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentMap_12_ok :
    tttLargeFiber60Block3Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentMap_13_ok :
    tttLargeFiber60Block3Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentMap_14_ok :
    tttLargeFiber60Block3Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentMap_15_ok :
    tttLargeFiber60Block3Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentPath_0_ok :
    tttLargeFiber60Block3Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentPath_1_ok :
    tttLargeFiber60Block3Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentPath_2_ok :
    tttLargeFiber60Block3Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentPath_3_ok :
    tttLargeFiber60Block3Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentPath_4_ok :
    tttLargeFiber60Block3Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentPath_5_ok :
    tttLargeFiber60Block3Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentPath_6_ok :
    tttLargeFiber60Block3Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentPath_7_ok :
    tttLargeFiber60Block3Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentPath_8_ok :
    tttLargeFiber60Block3Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentPath_9_ok :
    tttLargeFiber60Block3Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentPath_10_ok :
    tttLargeFiber60Block3Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentPath_11_ok :
    tttLargeFiber60Block3Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentPath_12_ok :
    tttLargeFiber60Block3Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentPath_13_ok :
    tttLargeFiber60Block3Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentPath_14_ok :
    tttLargeFiber60Block3Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block3Chunk3ParentPath_15_ok :
    tttLargeFiber60Block3Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block3Chunk3RowsAudit : Bool :=
  tttLargeFiber60Block3Chunk3RowCheck 0
    && tttLargeFiber60Block3Chunk3RowCheck 1
    && tttLargeFiber60Block3Chunk3RowCheck 2
    && tttLargeFiber60Block3Chunk3RowCheck 3
    && tttLargeFiber60Block3Chunk3RowCheck 4
    && tttLargeFiber60Block3Chunk3RowCheck 5
    && tttLargeFiber60Block3Chunk3RowCheck 6
    && tttLargeFiber60Block3Chunk3RowCheck 7
    && tttLargeFiber60Block3Chunk3RowCheck 8
    && tttLargeFiber60Block3Chunk3RowCheck 9
    && tttLargeFiber60Block3Chunk3RowCheck 10
    && tttLargeFiber60Block3Chunk3RowCheck 11
    && tttLargeFiber60Block3Chunk3RowCheck 12
    && tttLargeFiber60Block3Chunk3RowCheck 13
    && tttLargeFiber60Block3Chunk3RowCheck 14
    && tttLargeFiber60Block3Chunk3RowCheck 15

theorem tttLargeFiber60Block3Chunk3RowsAudit_ok :
    tttLargeFiber60Block3Chunk3RowsAudit = true := by
  simp [tttLargeFiber60Block3Chunk3RowsAudit,
    tttLargeFiber60Block3Chunk3Row_0_ok,
    tttLargeFiber60Block3Chunk3Row_1_ok,
    tttLargeFiber60Block3Chunk3Row_2_ok,
    tttLargeFiber60Block3Chunk3Row_3_ok,
    tttLargeFiber60Block3Chunk3Row_4_ok,
    tttLargeFiber60Block3Chunk3Row_5_ok,
    tttLargeFiber60Block3Chunk3Row_6_ok,
    tttLargeFiber60Block3Chunk3Row_7_ok,
    tttLargeFiber60Block3Chunk3Row_8_ok,
    tttLargeFiber60Block3Chunk3Row_9_ok,
    tttLargeFiber60Block3Chunk3Row_10_ok,
    tttLargeFiber60Block3Chunk3Row_11_ok,
    tttLargeFiber60Block3Chunk3Row_12_ok,
    tttLargeFiber60Block3Chunk3Row_13_ok,
    tttLargeFiber60Block3Chunk3Row_14_ok,
    tttLargeFiber60Block3Chunk3Row_15_ok]

def tttLargeFiber60Block3Chunk3ParentMapAudit : Bool :=
  tttLargeFiber60Block3Chunk3ParentMapCheck 0
    && tttLargeFiber60Block3Chunk3ParentMapCheck 1
    && tttLargeFiber60Block3Chunk3ParentMapCheck 2
    && tttLargeFiber60Block3Chunk3ParentMapCheck 3
    && tttLargeFiber60Block3Chunk3ParentMapCheck 4
    && tttLargeFiber60Block3Chunk3ParentMapCheck 5
    && tttLargeFiber60Block3Chunk3ParentMapCheck 6
    && tttLargeFiber60Block3Chunk3ParentMapCheck 7
    && tttLargeFiber60Block3Chunk3ParentMapCheck 8
    && tttLargeFiber60Block3Chunk3ParentMapCheck 9
    && tttLargeFiber60Block3Chunk3ParentMapCheck 10
    && tttLargeFiber60Block3Chunk3ParentMapCheck 11
    && tttLargeFiber60Block3Chunk3ParentMapCheck 12
    && tttLargeFiber60Block3Chunk3ParentMapCheck 13
    && tttLargeFiber60Block3Chunk3ParentMapCheck 14
    && tttLargeFiber60Block3Chunk3ParentMapCheck 15

theorem tttLargeFiber60Block3Chunk3ParentMapAudit_ok :
    tttLargeFiber60Block3Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber60Block3Chunk3ParentMapAudit,
    tttLargeFiber60Block3Chunk3ParentMap_0_ok,
    tttLargeFiber60Block3Chunk3ParentMap_1_ok,
    tttLargeFiber60Block3Chunk3ParentMap_2_ok,
    tttLargeFiber60Block3Chunk3ParentMap_3_ok,
    tttLargeFiber60Block3Chunk3ParentMap_4_ok,
    tttLargeFiber60Block3Chunk3ParentMap_5_ok,
    tttLargeFiber60Block3Chunk3ParentMap_6_ok,
    tttLargeFiber60Block3Chunk3ParentMap_7_ok,
    tttLargeFiber60Block3Chunk3ParentMap_8_ok,
    tttLargeFiber60Block3Chunk3ParentMap_9_ok,
    tttLargeFiber60Block3Chunk3ParentMap_10_ok,
    tttLargeFiber60Block3Chunk3ParentMap_11_ok,
    tttLargeFiber60Block3Chunk3ParentMap_12_ok,
    tttLargeFiber60Block3Chunk3ParentMap_13_ok,
    tttLargeFiber60Block3Chunk3ParentMap_14_ok,
    tttLargeFiber60Block3Chunk3ParentMap_15_ok]

def tttLargeFiber60Block3Chunk3ParentsAudit : Bool :=
  tttLargeFiber60Block3Chunk3ParentPathCheck 0
    && tttLargeFiber60Block3Chunk3ParentPathCheck 1
    && tttLargeFiber60Block3Chunk3ParentPathCheck 2
    && tttLargeFiber60Block3Chunk3ParentPathCheck 3
    && tttLargeFiber60Block3Chunk3ParentPathCheck 4
    && tttLargeFiber60Block3Chunk3ParentPathCheck 5
    && tttLargeFiber60Block3Chunk3ParentPathCheck 6
    && tttLargeFiber60Block3Chunk3ParentPathCheck 7
    && tttLargeFiber60Block3Chunk3ParentPathCheck 8
    && tttLargeFiber60Block3Chunk3ParentPathCheck 9
    && tttLargeFiber60Block3Chunk3ParentPathCheck 10
    && tttLargeFiber60Block3Chunk3ParentPathCheck 11
    && tttLargeFiber60Block3Chunk3ParentPathCheck 12
    && tttLargeFiber60Block3Chunk3ParentPathCheck 13
    && tttLargeFiber60Block3Chunk3ParentPathCheck 14
    && tttLargeFiber60Block3Chunk3ParentPathCheck 15

theorem tttLargeFiber60Block3Chunk3ParentsAudit_ok :
    tttLargeFiber60Block3Chunk3ParentsAudit = true := by
  simp [tttLargeFiber60Block3Chunk3ParentsAudit,
    tttLargeFiber60Block3Chunk3ParentPath_0_ok,
    tttLargeFiber60Block3Chunk3ParentPath_1_ok,
    tttLargeFiber60Block3Chunk3ParentPath_2_ok,
    tttLargeFiber60Block3Chunk3ParentPath_3_ok,
    tttLargeFiber60Block3Chunk3ParentPath_4_ok,
    tttLargeFiber60Block3Chunk3ParentPath_5_ok,
    tttLargeFiber60Block3Chunk3ParentPath_6_ok,
    tttLargeFiber60Block3Chunk3ParentPath_7_ok,
    tttLargeFiber60Block3Chunk3ParentPath_8_ok,
    tttLargeFiber60Block3Chunk3ParentPath_9_ok,
    tttLargeFiber60Block3Chunk3ParentPath_10_ok,
    tttLargeFiber60Block3Chunk3ParentPath_11_ok,
    tttLargeFiber60Block3Chunk3ParentPath_12_ok,
    tttLargeFiber60Block3Chunk3ParentPath_13_ok,
    tttLargeFiber60Block3Chunk3ParentPath_14_ok,
    tttLargeFiber60Block3Chunk3ParentPath_15_ok]

def tttLargeFiber60Block3Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block3Chunk3SourcesCheck &&
    tttLargeFiber60Block3Chunk3RowsAudit &&
    tttLargeFiber60Block3Chunk3ParentMapAudit &&
    tttLargeFiber60Block3Chunk3ParentsAudit

theorem tttLargeFiber60Block3Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber60Block3Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block3Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block3Chunk3SourcesCheck_ok,
    tttLargeFiber60Block3Chunk3RowsAudit_ok,
    tttLargeFiber60Block3Chunk3ParentMapAudit_ok,
    tttLargeFiber60Block3Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block3Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
