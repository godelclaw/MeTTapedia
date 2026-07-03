import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 3 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block3Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block3Chunk2Sources : List Nat :=
  [   768, 769, 770, 771, 772, 773, 774, 775,
   776, 777, 778, 779, 780, 781, 782, 783]

def tttLargeFiber60Row224 : TripleComponentParentRow :=
  tripleRow 768 736 19 40 148 19 24 80
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row225 : TripleComponentParentRow :=
  tripleRow 769 737 19 40 149 19 24 81
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row226 : TripleComponentParentRow :=
  tripleRow 770 738 19 40 150 19 24 82
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber60Row227 : TripleComponentParentRow :=
  tripleRow 771 768 19 40 151 19 40 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row228 : TripleComponentParentRow :=
  tripleRow 772 768 19 40 164 19 40 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber60Row229 : TripleComponentParentRow :=
  tripleRow 773 769 19 40 165 19 40 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber60Row230 : TripleComponentParentRow :=
  tripleRow 774 742 19 40 166 19 24 102
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber60Row231 : TripleComponentParentRow :=
  tripleRow 775 743 19 40 167 19 24 103
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber60Row232 : TripleComponentParentRow :=
  tripleRow 776 744 19 41 156 19 25 88
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row233 : TripleComponentParentRow :=
  tripleRow 777 745 19 41 157 19 25 89
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row234 : TripleComponentParentRow :=
  tripleRow 778 746 19 41 158 19 25 90
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber60Row235 : TripleComponentParentRow :=
  tripleRow 779 776 19 41 159 19 41 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row236 : TripleComponentParentRow :=
  tripleRow 780 776 19 41 172 19 41 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber60Row237 : TripleComponentParentRow :=
  tripleRow 781 777 19 41 173 19 41 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber60Row238 : TripleComponentParentRow :=
  tripleRow 782 750 19 41 174 19 25 110
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber60Row239 : TripleComponentParentRow :=
  tripleRow 783 751 19 41 175 19 25 111
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber60Block3Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row224
  , tttLargeFiber60Row225
  , tttLargeFiber60Row226
  , tttLargeFiber60Row227
  , tttLargeFiber60Row228
  , tttLargeFiber60Row229
  , tttLargeFiber60Row230
  , tttLargeFiber60Row231
  , tttLargeFiber60Row232
  , tttLargeFiber60Row233
  , tttLargeFiber60Row234
  , tttLargeFiber60Row235
  , tttLargeFiber60Row236
  , tttLargeFiber60Row237
  , tttLargeFiber60Row238
  , tttLargeFiber60Row239
  ]

def tttLargeFiber60Block3Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block3Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block3Chunk2ExpectedContains row.source &&
    tttLargeFiber60Block3Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block3Chunk2SourcesCheck : Bool :=
  (tttLargeFiber60Block3Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber60Block3Chunk2Sources

theorem tttLargeFiber60Block3Chunk2SourcesCheck_ok :
    tttLargeFiber60Block3Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber60Block3Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block3Chunk2RowValid
    (listGetD tttLargeFiber60Block3Chunk2Rows i default)

def tttLargeFiber60Block3Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block3Chunk2Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block3Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block3Chunk2Sources 0 0 == 768
      && tttLargeFiber60ParentOf 768 == 736
      && tttLargeFiber60ParentOf 736 == 608
      && tttLargeFiber60ParentOf 608 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block3Chunk2Sources 1 0 == 769
      && tttLargeFiber60ParentOf 769 == 737
      && tttLargeFiber60ParentOf 737 == 609
      && tttLargeFiber60ParentOf 609 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block3Chunk2Sources 2 0 == 770
      && tttLargeFiber60ParentOf 770 == 738
      && tttLargeFiber60ParentOf 738 == 610
      && tttLargeFiber60ParentOf 610 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block3Chunk2Sources 3 0 == 771
      && tttLargeFiber60ParentOf 771 == 768
      && tttLargeFiber60ParentOf 768 == 736
      && tttLargeFiber60ParentOf 736 == 608
      && tttLargeFiber60ParentOf 608 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block3Chunk2Sources 4 0 == 772
      && tttLargeFiber60ParentOf 772 == 768
      && tttLargeFiber60ParentOf 768 == 736
      && tttLargeFiber60ParentOf 736 == 608
      && tttLargeFiber60ParentOf 608 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block3Chunk2Sources 5 0 == 773
      && tttLargeFiber60ParentOf 773 == 769
      && tttLargeFiber60ParentOf 769 == 737
      && tttLargeFiber60ParentOf 737 == 609
      && tttLargeFiber60ParentOf 609 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block3Chunk2Sources 6 0 == 774
      && tttLargeFiber60ParentOf 774 == 742
      && tttLargeFiber60ParentOf 742 == 614
      && tttLargeFiber60ParentOf 614 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block3Chunk2Sources 7 0 == 775
      && tttLargeFiber60ParentOf 775 == 743
      && tttLargeFiber60ParentOf 743 == 615
      && tttLargeFiber60ParentOf 615 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block3Chunk2Sources 8 0 == 776
      && tttLargeFiber60ParentOf 776 == 744
      && tttLargeFiber60ParentOf 744 == 616
      && tttLargeFiber60ParentOf 616 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block3Chunk2Sources 9 0 == 777
      && tttLargeFiber60ParentOf 777 == 745
      && tttLargeFiber60ParentOf 745 == 617
      && tttLargeFiber60ParentOf 617 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block3Chunk2Sources 10 0 == 778
      && tttLargeFiber60ParentOf 778 == 746
      && tttLargeFiber60ParentOf 746 == 618
      && tttLargeFiber60ParentOf 618 == 554
      && tttLargeFiber60ParentOf 554 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block3Chunk2Sources 11 0 == 779
      && tttLargeFiber60ParentOf 779 == 776
      && tttLargeFiber60ParentOf 776 == 744
      && tttLargeFiber60ParentOf 744 == 616
      && tttLargeFiber60ParentOf 616 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block3Chunk2Sources 12 0 == 780
      && tttLargeFiber60ParentOf 780 == 776
      && tttLargeFiber60ParentOf 776 == 744
      && tttLargeFiber60ParentOf 744 == 616
      && tttLargeFiber60ParentOf 616 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block3Chunk2Sources 13 0 == 781
      && tttLargeFiber60ParentOf 781 == 777
      && tttLargeFiber60ParentOf 777 == 745
      && tttLargeFiber60ParentOf 745 == 617
      && tttLargeFiber60ParentOf 617 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (6 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block3Chunk2Sources 14 0 == 782
      && tttLargeFiber60ParentOf 782 == 750
      && tttLargeFiber60ParentOf 750 == 622
      && tttLargeFiber60ParentOf 622 == 558
      && tttLargeFiber60ParentOf 558 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (6 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block3Chunk2Sources 15 0 == 783
      && tttLargeFiber60ParentOf 783 == 751
      && tttLargeFiber60ParentOf 751 == 623
      && tttLargeFiber60ParentOf 623 == 559
      && tttLargeFiber60ParentOf 559 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block3Chunk2Row_0_ok :
    tttLargeFiber60Block3Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2Row_1_ok :
    tttLargeFiber60Block3Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2Row_2_ok :
    tttLargeFiber60Block3Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2Row_3_ok :
    tttLargeFiber60Block3Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2Row_4_ok :
    tttLargeFiber60Block3Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2Row_5_ok :
    tttLargeFiber60Block3Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2Row_6_ok :
    tttLargeFiber60Block3Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2Row_7_ok :
    tttLargeFiber60Block3Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2Row_8_ok :
    tttLargeFiber60Block3Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2Row_9_ok :
    tttLargeFiber60Block3Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2Row_10_ok :
    tttLargeFiber60Block3Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2Row_11_ok :
    tttLargeFiber60Block3Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2Row_12_ok :
    tttLargeFiber60Block3Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2Row_13_ok :
    tttLargeFiber60Block3Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2Row_14_ok :
    tttLargeFiber60Block3Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2Row_15_ok :
    tttLargeFiber60Block3Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentMap_0_ok :
    tttLargeFiber60Block3Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentMap_1_ok :
    tttLargeFiber60Block3Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentMap_2_ok :
    tttLargeFiber60Block3Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentMap_3_ok :
    tttLargeFiber60Block3Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentMap_4_ok :
    tttLargeFiber60Block3Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentMap_5_ok :
    tttLargeFiber60Block3Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentMap_6_ok :
    tttLargeFiber60Block3Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentMap_7_ok :
    tttLargeFiber60Block3Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentMap_8_ok :
    tttLargeFiber60Block3Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentMap_9_ok :
    tttLargeFiber60Block3Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentMap_10_ok :
    tttLargeFiber60Block3Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentMap_11_ok :
    tttLargeFiber60Block3Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentMap_12_ok :
    tttLargeFiber60Block3Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentMap_13_ok :
    tttLargeFiber60Block3Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentMap_14_ok :
    tttLargeFiber60Block3Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentMap_15_ok :
    tttLargeFiber60Block3Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentPath_0_ok :
    tttLargeFiber60Block3Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentPath_1_ok :
    tttLargeFiber60Block3Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentPath_2_ok :
    tttLargeFiber60Block3Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentPath_3_ok :
    tttLargeFiber60Block3Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentPath_4_ok :
    tttLargeFiber60Block3Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentPath_5_ok :
    tttLargeFiber60Block3Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentPath_6_ok :
    tttLargeFiber60Block3Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentPath_7_ok :
    tttLargeFiber60Block3Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentPath_8_ok :
    tttLargeFiber60Block3Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentPath_9_ok :
    tttLargeFiber60Block3Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentPath_10_ok :
    tttLargeFiber60Block3Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentPath_11_ok :
    tttLargeFiber60Block3Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentPath_12_ok :
    tttLargeFiber60Block3Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentPath_13_ok :
    tttLargeFiber60Block3Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentPath_14_ok :
    tttLargeFiber60Block3Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block3Chunk2ParentPath_15_ok :
    tttLargeFiber60Block3Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block3Chunk2RowsAudit : Bool :=
  tttLargeFiber60Block3Chunk2RowCheck 0
    && tttLargeFiber60Block3Chunk2RowCheck 1
    && tttLargeFiber60Block3Chunk2RowCheck 2
    && tttLargeFiber60Block3Chunk2RowCheck 3
    && tttLargeFiber60Block3Chunk2RowCheck 4
    && tttLargeFiber60Block3Chunk2RowCheck 5
    && tttLargeFiber60Block3Chunk2RowCheck 6
    && tttLargeFiber60Block3Chunk2RowCheck 7
    && tttLargeFiber60Block3Chunk2RowCheck 8
    && tttLargeFiber60Block3Chunk2RowCheck 9
    && tttLargeFiber60Block3Chunk2RowCheck 10
    && tttLargeFiber60Block3Chunk2RowCheck 11
    && tttLargeFiber60Block3Chunk2RowCheck 12
    && tttLargeFiber60Block3Chunk2RowCheck 13
    && tttLargeFiber60Block3Chunk2RowCheck 14
    && tttLargeFiber60Block3Chunk2RowCheck 15

theorem tttLargeFiber60Block3Chunk2RowsAudit_ok :
    tttLargeFiber60Block3Chunk2RowsAudit = true := by
  simp [tttLargeFiber60Block3Chunk2RowsAudit,
    tttLargeFiber60Block3Chunk2Row_0_ok,
    tttLargeFiber60Block3Chunk2Row_1_ok,
    tttLargeFiber60Block3Chunk2Row_2_ok,
    tttLargeFiber60Block3Chunk2Row_3_ok,
    tttLargeFiber60Block3Chunk2Row_4_ok,
    tttLargeFiber60Block3Chunk2Row_5_ok,
    tttLargeFiber60Block3Chunk2Row_6_ok,
    tttLargeFiber60Block3Chunk2Row_7_ok,
    tttLargeFiber60Block3Chunk2Row_8_ok,
    tttLargeFiber60Block3Chunk2Row_9_ok,
    tttLargeFiber60Block3Chunk2Row_10_ok,
    tttLargeFiber60Block3Chunk2Row_11_ok,
    tttLargeFiber60Block3Chunk2Row_12_ok,
    tttLargeFiber60Block3Chunk2Row_13_ok,
    tttLargeFiber60Block3Chunk2Row_14_ok,
    tttLargeFiber60Block3Chunk2Row_15_ok]

def tttLargeFiber60Block3Chunk2ParentMapAudit : Bool :=
  tttLargeFiber60Block3Chunk2ParentMapCheck 0
    && tttLargeFiber60Block3Chunk2ParentMapCheck 1
    && tttLargeFiber60Block3Chunk2ParentMapCheck 2
    && tttLargeFiber60Block3Chunk2ParentMapCheck 3
    && tttLargeFiber60Block3Chunk2ParentMapCheck 4
    && tttLargeFiber60Block3Chunk2ParentMapCheck 5
    && tttLargeFiber60Block3Chunk2ParentMapCheck 6
    && tttLargeFiber60Block3Chunk2ParentMapCheck 7
    && tttLargeFiber60Block3Chunk2ParentMapCheck 8
    && tttLargeFiber60Block3Chunk2ParentMapCheck 9
    && tttLargeFiber60Block3Chunk2ParentMapCheck 10
    && tttLargeFiber60Block3Chunk2ParentMapCheck 11
    && tttLargeFiber60Block3Chunk2ParentMapCheck 12
    && tttLargeFiber60Block3Chunk2ParentMapCheck 13
    && tttLargeFiber60Block3Chunk2ParentMapCheck 14
    && tttLargeFiber60Block3Chunk2ParentMapCheck 15

theorem tttLargeFiber60Block3Chunk2ParentMapAudit_ok :
    tttLargeFiber60Block3Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber60Block3Chunk2ParentMapAudit,
    tttLargeFiber60Block3Chunk2ParentMap_0_ok,
    tttLargeFiber60Block3Chunk2ParentMap_1_ok,
    tttLargeFiber60Block3Chunk2ParentMap_2_ok,
    tttLargeFiber60Block3Chunk2ParentMap_3_ok,
    tttLargeFiber60Block3Chunk2ParentMap_4_ok,
    tttLargeFiber60Block3Chunk2ParentMap_5_ok,
    tttLargeFiber60Block3Chunk2ParentMap_6_ok,
    tttLargeFiber60Block3Chunk2ParentMap_7_ok,
    tttLargeFiber60Block3Chunk2ParentMap_8_ok,
    tttLargeFiber60Block3Chunk2ParentMap_9_ok,
    tttLargeFiber60Block3Chunk2ParentMap_10_ok,
    tttLargeFiber60Block3Chunk2ParentMap_11_ok,
    tttLargeFiber60Block3Chunk2ParentMap_12_ok,
    tttLargeFiber60Block3Chunk2ParentMap_13_ok,
    tttLargeFiber60Block3Chunk2ParentMap_14_ok,
    tttLargeFiber60Block3Chunk2ParentMap_15_ok]

def tttLargeFiber60Block3Chunk2ParentsAudit : Bool :=
  tttLargeFiber60Block3Chunk2ParentPathCheck 0
    && tttLargeFiber60Block3Chunk2ParentPathCheck 1
    && tttLargeFiber60Block3Chunk2ParentPathCheck 2
    && tttLargeFiber60Block3Chunk2ParentPathCheck 3
    && tttLargeFiber60Block3Chunk2ParentPathCheck 4
    && tttLargeFiber60Block3Chunk2ParentPathCheck 5
    && tttLargeFiber60Block3Chunk2ParentPathCheck 6
    && tttLargeFiber60Block3Chunk2ParentPathCheck 7
    && tttLargeFiber60Block3Chunk2ParentPathCheck 8
    && tttLargeFiber60Block3Chunk2ParentPathCheck 9
    && tttLargeFiber60Block3Chunk2ParentPathCheck 10
    && tttLargeFiber60Block3Chunk2ParentPathCheck 11
    && tttLargeFiber60Block3Chunk2ParentPathCheck 12
    && tttLargeFiber60Block3Chunk2ParentPathCheck 13
    && tttLargeFiber60Block3Chunk2ParentPathCheck 14
    && tttLargeFiber60Block3Chunk2ParentPathCheck 15

theorem tttLargeFiber60Block3Chunk2ParentsAudit_ok :
    tttLargeFiber60Block3Chunk2ParentsAudit = true := by
  simp [tttLargeFiber60Block3Chunk2ParentsAudit,
    tttLargeFiber60Block3Chunk2ParentPath_0_ok,
    tttLargeFiber60Block3Chunk2ParentPath_1_ok,
    tttLargeFiber60Block3Chunk2ParentPath_2_ok,
    tttLargeFiber60Block3Chunk2ParentPath_3_ok,
    tttLargeFiber60Block3Chunk2ParentPath_4_ok,
    tttLargeFiber60Block3Chunk2ParentPath_5_ok,
    tttLargeFiber60Block3Chunk2ParentPath_6_ok,
    tttLargeFiber60Block3Chunk2ParentPath_7_ok,
    tttLargeFiber60Block3Chunk2ParentPath_8_ok,
    tttLargeFiber60Block3Chunk2ParentPath_9_ok,
    tttLargeFiber60Block3Chunk2ParentPath_10_ok,
    tttLargeFiber60Block3Chunk2ParentPath_11_ok,
    tttLargeFiber60Block3Chunk2ParentPath_12_ok,
    tttLargeFiber60Block3Chunk2ParentPath_13_ok,
    tttLargeFiber60Block3Chunk2ParentPath_14_ok,
    tttLargeFiber60Block3Chunk2ParentPath_15_ok]

def tttLargeFiber60Block3Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block3Chunk2SourcesCheck &&
    tttLargeFiber60Block3Chunk2RowsAudit &&
    tttLargeFiber60Block3Chunk2ParentMapAudit &&
    tttLargeFiber60Block3Chunk2ParentsAudit

theorem tttLargeFiber60Block3Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber60Block3Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block3Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block3Chunk2SourcesCheck_ok,
    tttLargeFiber60Block3Chunk2RowsAudit_ok,
    tttLargeFiber60Block3Chunk2ParentMapAudit_ok,
    tttLargeFiber60Block3Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block3Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
