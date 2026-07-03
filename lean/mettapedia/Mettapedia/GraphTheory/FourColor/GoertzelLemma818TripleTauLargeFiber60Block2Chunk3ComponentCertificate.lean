import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 2 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block2Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block2Chunk3Sources : List Nat :=
  [   720, 721, 722, 723, 724, 725, 726, 727,
   728, 729, 730, 731, 732, 733, 734, 735]

def tttLargeFiber60Row176 : TripleComponentParentRow :=
  tripleRow 720 592 18 34 0 16 102 64
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber60Row177 : TripleComponentParentRow :=
  tripleRow 721 593 18 34 1 16 102 65
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber60Row178 : TripleComponentParentRow :=
  tripleRow 722 594 18 34 2 16 102 66
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber60Row179 : TripleComponentParentRow :=
  tripleRow 723 595 18 34 3 16 102 67
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber60Row180 : TripleComponentParentRow :=
  tripleRow 724 720 18 34 48 18 34 0
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row181 : TripleComponentParentRow :=
  tripleRow 725 721 18 34 49 18 34 1
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row182 : TripleComponentParentRow :=
  tripleRow 726 598 18 34 50 16 102 118
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber60Row183 : TripleComponentParentRow :=
  tripleRow 727 599 18 34 51 16 102 119
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber60Row184 : TripleComponentParentRow :=
  tripleRow 728 600 18 35 8 16 103 72
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber60Row185 : TripleComponentParentRow :=
  tripleRow 729 601 18 35 9 16 103 73
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber60Row186 : TripleComponentParentRow :=
  tripleRow 730 602 18 35 10 16 103 74
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber60Row187 : TripleComponentParentRow :=
  tripleRow 731 603 18 35 11 16 103 75
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber60Row188 : TripleComponentParentRow :=
  tripleRow 732 728 18 35 56 18 35 8
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row189 : TripleComponentParentRow :=
  tripleRow 733 729 18 35 57 18 35 9
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row190 : TripleComponentParentRow :=
  tripleRow 734 606 18 35 58 16 103 126
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber60Row191 : TripleComponentParentRow :=
  tripleRow 735 607 18 35 59 16 103 127
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber60Block2Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row176
  , tttLargeFiber60Row177
  , tttLargeFiber60Row178
  , tttLargeFiber60Row179
  , tttLargeFiber60Row180
  , tttLargeFiber60Row181
  , tttLargeFiber60Row182
  , tttLargeFiber60Row183
  , tttLargeFiber60Row184
  , tttLargeFiber60Row185
  , tttLargeFiber60Row186
  , tttLargeFiber60Row187
  , tttLargeFiber60Row188
  , tttLargeFiber60Row189
  , tttLargeFiber60Row190
  , tttLargeFiber60Row191
  ]

def tttLargeFiber60Block2Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block2Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block2Chunk3ExpectedContains row.source &&
    tttLargeFiber60Block2Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block2Chunk3SourcesCheck : Bool :=
  (tttLargeFiber60Block2Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber60Block2Chunk3Sources

theorem tttLargeFiber60Block2Chunk3SourcesCheck_ok :
    tttLargeFiber60Block2Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber60Block2Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block2Chunk3RowValid
    (listGetD tttLargeFiber60Block2Chunk3Rows i default)

def tttLargeFiber60Block2Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block2Chunk3Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block2Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block2Chunk3Sources 0 0 == 720
      && tttLargeFiber60ParentOf 720 == 592
      && tttLargeFiber60ParentOf 592 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block2Chunk3Sources 1 0 == 721
      && tttLargeFiber60ParentOf 721 == 593
      && tttLargeFiber60ParentOf 593 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block2Chunk3Sources 2 0 == 722
      && tttLargeFiber60ParentOf 722 == 594
      && tttLargeFiber60ParentOf 594 == 554
      && tttLargeFiber60ParentOf 554 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block2Chunk3Sources 3 0 == 723
      && tttLargeFiber60ParentOf 723 == 595
      && tttLargeFiber60ParentOf 595 == 555
      && tttLargeFiber60ParentOf 555 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block2Chunk3Sources 4 0 == 724
      && tttLargeFiber60ParentOf 724 == 720
      && tttLargeFiber60ParentOf 720 == 592
      && tttLargeFiber60ParentOf 592 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block2Chunk3Sources 5 0 == 725
      && tttLargeFiber60ParentOf 725 == 721
      && tttLargeFiber60ParentOf 721 == 593
      && tttLargeFiber60ParentOf 593 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block2Chunk3Sources 6 0 == 726
      && tttLargeFiber60ParentOf 726 == 598
      && tttLargeFiber60ParentOf 598 == 558
      && tttLargeFiber60ParentOf 558 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block2Chunk3Sources 7 0 == 727
      && tttLargeFiber60ParentOf 727 == 599
      && tttLargeFiber60ParentOf 599 == 559
      && tttLargeFiber60ParentOf 559 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block2Chunk3Sources 8 0 == 728
      && tttLargeFiber60ParentOf 728 == 600
      && tttLargeFiber60ParentOf 600 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block2Chunk3Sources 9 0 == 729
      && tttLargeFiber60ParentOf 729 == 601
      && tttLargeFiber60ParentOf 601 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block2Chunk3Sources 10 0 == 730
      && tttLargeFiber60ParentOf 730 == 602
      && tttLargeFiber60ParentOf 602 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block2Chunk3Sources 11 0 == 731
      && tttLargeFiber60ParentOf 731 == 603
      && tttLargeFiber60ParentOf 603 == 547
      && tttLargeFiber60ParentOf 547 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block2Chunk3Sources 12 0 == 732
      && tttLargeFiber60ParentOf 732 == 728
      && tttLargeFiber60ParentOf 728 == 600
      && tttLargeFiber60ParentOf 600 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block2Chunk3Sources 13 0 == 733
      && tttLargeFiber60ParentOf 733 == 729
      && tttLargeFiber60ParentOf 729 == 601
      && tttLargeFiber60ParentOf 601 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block2Chunk3Sources 14 0 == 734
      && tttLargeFiber60ParentOf 734 == 606
      && tttLargeFiber60ParentOf 606 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block2Chunk3Sources 15 0 == 735
      && tttLargeFiber60ParentOf 735 == 607
      && tttLargeFiber60ParentOf 607 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block2Chunk3Row_0_ok :
    tttLargeFiber60Block2Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3Row_1_ok :
    tttLargeFiber60Block2Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3Row_2_ok :
    tttLargeFiber60Block2Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3Row_3_ok :
    tttLargeFiber60Block2Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3Row_4_ok :
    tttLargeFiber60Block2Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3Row_5_ok :
    tttLargeFiber60Block2Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3Row_6_ok :
    tttLargeFiber60Block2Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3Row_7_ok :
    tttLargeFiber60Block2Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3Row_8_ok :
    tttLargeFiber60Block2Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3Row_9_ok :
    tttLargeFiber60Block2Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3Row_10_ok :
    tttLargeFiber60Block2Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3Row_11_ok :
    tttLargeFiber60Block2Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3Row_12_ok :
    tttLargeFiber60Block2Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3Row_13_ok :
    tttLargeFiber60Block2Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3Row_14_ok :
    tttLargeFiber60Block2Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3Row_15_ok :
    tttLargeFiber60Block2Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentMap_0_ok :
    tttLargeFiber60Block2Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentMap_1_ok :
    tttLargeFiber60Block2Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentMap_2_ok :
    tttLargeFiber60Block2Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentMap_3_ok :
    tttLargeFiber60Block2Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentMap_4_ok :
    tttLargeFiber60Block2Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentMap_5_ok :
    tttLargeFiber60Block2Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentMap_6_ok :
    tttLargeFiber60Block2Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentMap_7_ok :
    tttLargeFiber60Block2Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentMap_8_ok :
    tttLargeFiber60Block2Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentMap_9_ok :
    tttLargeFiber60Block2Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentMap_10_ok :
    tttLargeFiber60Block2Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentMap_11_ok :
    tttLargeFiber60Block2Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentMap_12_ok :
    tttLargeFiber60Block2Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentMap_13_ok :
    tttLargeFiber60Block2Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentMap_14_ok :
    tttLargeFiber60Block2Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentMap_15_ok :
    tttLargeFiber60Block2Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentPath_0_ok :
    tttLargeFiber60Block2Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentPath_1_ok :
    tttLargeFiber60Block2Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentPath_2_ok :
    tttLargeFiber60Block2Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentPath_3_ok :
    tttLargeFiber60Block2Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentPath_4_ok :
    tttLargeFiber60Block2Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentPath_5_ok :
    tttLargeFiber60Block2Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentPath_6_ok :
    tttLargeFiber60Block2Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentPath_7_ok :
    tttLargeFiber60Block2Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentPath_8_ok :
    tttLargeFiber60Block2Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentPath_9_ok :
    tttLargeFiber60Block2Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentPath_10_ok :
    tttLargeFiber60Block2Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentPath_11_ok :
    tttLargeFiber60Block2Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentPath_12_ok :
    tttLargeFiber60Block2Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentPath_13_ok :
    tttLargeFiber60Block2Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentPath_14_ok :
    tttLargeFiber60Block2Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block2Chunk3ParentPath_15_ok :
    tttLargeFiber60Block2Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block2Chunk3RowsAudit : Bool :=
  tttLargeFiber60Block2Chunk3RowCheck 0
    && tttLargeFiber60Block2Chunk3RowCheck 1
    && tttLargeFiber60Block2Chunk3RowCheck 2
    && tttLargeFiber60Block2Chunk3RowCheck 3
    && tttLargeFiber60Block2Chunk3RowCheck 4
    && tttLargeFiber60Block2Chunk3RowCheck 5
    && tttLargeFiber60Block2Chunk3RowCheck 6
    && tttLargeFiber60Block2Chunk3RowCheck 7
    && tttLargeFiber60Block2Chunk3RowCheck 8
    && tttLargeFiber60Block2Chunk3RowCheck 9
    && tttLargeFiber60Block2Chunk3RowCheck 10
    && tttLargeFiber60Block2Chunk3RowCheck 11
    && tttLargeFiber60Block2Chunk3RowCheck 12
    && tttLargeFiber60Block2Chunk3RowCheck 13
    && tttLargeFiber60Block2Chunk3RowCheck 14
    && tttLargeFiber60Block2Chunk3RowCheck 15

theorem tttLargeFiber60Block2Chunk3RowsAudit_ok :
    tttLargeFiber60Block2Chunk3RowsAudit = true := by
  simp [tttLargeFiber60Block2Chunk3RowsAudit,
    tttLargeFiber60Block2Chunk3Row_0_ok,
    tttLargeFiber60Block2Chunk3Row_1_ok,
    tttLargeFiber60Block2Chunk3Row_2_ok,
    tttLargeFiber60Block2Chunk3Row_3_ok,
    tttLargeFiber60Block2Chunk3Row_4_ok,
    tttLargeFiber60Block2Chunk3Row_5_ok,
    tttLargeFiber60Block2Chunk3Row_6_ok,
    tttLargeFiber60Block2Chunk3Row_7_ok,
    tttLargeFiber60Block2Chunk3Row_8_ok,
    tttLargeFiber60Block2Chunk3Row_9_ok,
    tttLargeFiber60Block2Chunk3Row_10_ok,
    tttLargeFiber60Block2Chunk3Row_11_ok,
    tttLargeFiber60Block2Chunk3Row_12_ok,
    tttLargeFiber60Block2Chunk3Row_13_ok,
    tttLargeFiber60Block2Chunk3Row_14_ok,
    tttLargeFiber60Block2Chunk3Row_15_ok]

def tttLargeFiber60Block2Chunk3ParentMapAudit : Bool :=
  tttLargeFiber60Block2Chunk3ParentMapCheck 0
    && tttLargeFiber60Block2Chunk3ParentMapCheck 1
    && tttLargeFiber60Block2Chunk3ParentMapCheck 2
    && tttLargeFiber60Block2Chunk3ParentMapCheck 3
    && tttLargeFiber60Block2Chunk3ParentMapCheck 4
    && tttLargeFiber60Block2Chunk3ParentMapCheck 5
    && tttLargeFiber60Block2Chunk3ParentMapCheck 6
    && tttLargeFiber60Block2Chunk3ParentMapCheck 7
    && tttLargeFiber60Block2Chunk3ParentMapCheck 8
    && tttLargeFiber60Block2Chunk3ParentMapCheck 9
    && tttLargeFiber60Block2Chunk3ParentMapCheck 10
    && tttLargeFiber60Block2Chunk3ParentMapCheck 11
    && tttLargeFiber60Block2Chunk3ParentMapCheck 12
    && tttLargeFiber60Block2Chunk3ParentMapCheck 13
    && tttLargeFiber60Block2Chunk3ParentMapCheck 14
    && tttLargeFiber60Block2Chunk3ParentMapCheck 15

theorem tttLargeFiber60Block2Chunk3ParentMapAudit_ok :
    tttLargeFiber60Block2Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber60Block2Chunk3ParentMapAudit,
    tttLargeFiber60Block2Chunk3ParentMap_0_ok,
    tttLargeFiber60Block2Chunk3ParentMap_1_ok,
    tttLargeFiber60Block2Chunk3ParentMap_2_ok,
    tttLargeFiber60Block2Chunk3ParentMap_3_ok,
    tttLargeFiber60Block2Chunk3ParentMap_4_ok,
    tttLargeFiber60Block2Chunk3ParentMap_5_ok,
    tttLargeFiber60Block2Chunk3ParentMap_6_ok,
    tttLargeFiber60Block2Chunk3ParentMap_7_ok,
    tttLargeFiber60Block2Chunk3ParentMap_8_ok,
    tttLargeFiber60Block2Chunk3ParentMap_9_ok,
    tttLargeFiber60Block2Chunk3ParentMap_10_ok,
    tttLargeFiber60Block2Chunk3ParentMap_11_ok,
    tttLargeFiber60Block2Chunk3ParentMap_12_ok,
    tttLargeFiber60Block2Chunk3ParentMap_13_ok,
    tttLargeFiber60Block2Chunk3ParentMap_14_ok,
    tttLargeFiber60Block2Chunk3ParentMap_15_ok]

def tttLargeFiber60Block2Chunk3ParentsAudit : Bool :=
  tttLargeFiber60Block2Chunk3ParentPathCheck 0
    && tttLargeFiber60Block2Chunk3ParentPathCheck 1
    && tttLargeFiber60Block2Chunk3ParentPathCheck 2
    && tttLargeFiber60Block2Chunk3ParentPathCheck 3
    && tttLargeFiber60Block2Chunk3ParentPathCheck 4
    && tttLargeFiber60Block2Chunk3ParentPathCheck 5
    && tttLargeFiber60Block2Chunk3ParentPathCheck 6
    && tttLargeFiber60Block2Chunk3ParentPathCheck 7
    && tttLargeFiber60Block2Chunk3ParentPathCheck 8
    && tttLargeFiber60Block2Chunk3ParentPathCheck 9
    && tttLargeFiber60Block2Chunk3ParentPathCheck 10
    && tttLargeFiber60Block2Chunk3ParentPathCheck 11
    && tttLargeFiber60Block2Chunk3ParentPathCheck 12
    && tttLargeFiber60Block2Chunk3ParentPathCheck 13
    && tttLargeFiber60Block2Chunk3ParentPathCheck 14
    && tttLargeFiber60Block2Chunk3ParentPathCheck 15

theorem tttLargeFiber60Block2Chunk3ParentsAudit_ok :
    tttLargeFiber60Block2Chunk3ParentsAudit = true := by
  simp [tttLargeFiber60Block2Chunk3ParentsAudit,
    tttLargeFiber60Block2Chunk3ParentPath_0_ok,
    tttLargeFiber60Block2Chunk3ParentPath_1_ok,
    tttLargeFiber60Block2Chunk3ParentPath_2_ok,
    tttLargeFiber60Block2Chunk3ParentPath_3_ok,
    tttLargeFiber60Block2Chunk3ParentPath_4_ok,
    tttLargeFiber60Block2Chunk3ParentPath_5_ok,
    tttLargeFiber60Block2Chunk3ParentPath_6_ok,
    tttLargeFiber60Block2Chunk3ParentPath_7_ok,
    tttLargeFiber60Block2Chunk3ParentPath_8_ok,
    tttLargeFiber60Block2Chunk3ParentPath_9_ok,
    tttLargeFiber60Block2Chunk3ParentPath_10_ok,
    tttLargeFiber60Block2Chunk3ParentPath_11_ok,
    tttLargeFiber60Block2Chunk3ParentPath_12_ok,
    tttLargeFiber60Block2Chunk3ParentPath_13_ok,
    tttLargeFiber60Block2Chunk3ParentPath_14_ok,
    tttLargeFiber60Block2Chunk3ParentPath_15_ok]

def tttLargeFiber60Block2Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block2Chunk3SourcesCheck &&
    tttLargeFiber60Block2Chunk3RowsAudit &&
    tttLargeFiber60Block2Chunk3ParentMapAudit &&
    tttLargeFiber60Block2Chunk3ParentsAudit

theorem tttLargeFiber60Block2Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber60Block2Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block2Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block2Chunk3SourcesCheck_ok,
    tttLargeFiber60Block2Chunk3RowsAudit_ok,
    tttLargeFiber60Block2Chunk3ParentMapAudit_ok,
    tttLargeFiber60Block2Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block2Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
