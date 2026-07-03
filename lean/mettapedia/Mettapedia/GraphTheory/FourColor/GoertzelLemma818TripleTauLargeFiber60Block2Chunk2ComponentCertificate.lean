import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 60, block 2 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber60Block2Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber60Data

def tttLargeFiber60Block2Chunk2Sources : List Nat :=
  [   704, 705, 706, 707, 708, 709, 710, 711,
   712, 713, 714, 715, 716, 717, 718, 719]

def tttLargeFiber60Row160 : TripleComponentParentRow :=
  tripleRow 704 672 18 32 148 18 16 80
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

def tttLargeFiber60Row161 : TripleComponentParentRow :=
  tripleRow 705 673 18 32 149 18 16 81
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

def tttLargeFiber60Row162 : TripleComponentParentRow :=
  tripleRow 706 674 18 32 150 18 16 82
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

def tttLargeFiber60Row163 : TripleComponentParentRow :=
  tripleRow 707 704 18 32 151 18 32 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row164 : TripleComponentParentRow :=
  tripleRow 708 704 18 32 164 18 32 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber60Row165 : TripleComponentParentRow :=
  tripleRow 709 705 18 32 165 18 32 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber60Row166 : TripleComponentParentRow :=
  tripleRow 710 678 18 32 166 18 16 102
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber60Row167 : TripleComponentParentRow :=
  tripleRow 711 679 18 32 167 18 16 103
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber60Row168 : TripleComponentParentRow :=
  tripleRow 712 680 18 33 156 18 17 88
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

def tttLargeFiber60Row169 : TripleComponentParentRow :=
  tripleRow 713 681 18 33 157 18 17 89
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

def tttLargeFiber60Row170 : TripleComponentParentRow :=
  tripleRow 714 682 18 33 158 18 17 90
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

def tttLargeFiber60Row171 : TripleComponentParentRow :=
  tripleRow 715 712 18 33 159 18 33 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber60Row172 : TripleComponentParentRow :=
  tripleRow 716 712 18 33 172 18 33 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber60Row173 : TripleComponentParentRow :=
  tripleRow 717 713 18 33 173 18 33 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber60Row174 : TripleComponentParentRow :=
  tripleRow 718 686 18 33 174 18 17 110
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber60Row175 : TripleComponentParentRow :=
  tripleRow 719 687 18 33 175 18 17 111
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber60Block2Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber60Row160
  , tttLargeFiber60Row161
  , tttLargeFiber60Row162
  , tttLargeFiber60Row163
  , tttLargeFiber60Row164
  , tttLargeFiber60Row165
  , tttLargeFiber60Row166
  , tttLargeFiber60Row167
  , tttLargeFiber60Row168
  , tttLargeFiber60Row169
  , tttLargeFiber60Row170
  , tttLargeFiber60Row171
  , tttLargeFiber60Row172
  , tttLargeFiber60Row173
  , tttLargeFiber60Row174
  , tttLargeFiber60Row175
  ]

def tttLargeFiber60Block2Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (544 <= i) && decide (i < 800)) ||
    (decide (1088 <= i) && decide (i < 1344))

def tttLargeFiber60Block2Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber60Block2Chunk2ExpectedContains row.source &&
    tttLargeFiber60Block2Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber60Key &&
          chainInputKey tttWord t == tttLargeFiber60Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber60Block2Chunk2SourcesCheck : Bool :=
  (tttLargeFiber60Block2Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber60Block2Chunk2Sources

theorem tttLargeFiber60Block2Chunk2SourcesCheck_ok :
    tttLargeFiber60Block2Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber60Block2Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber60Block2Chunk2RowValid
    (listGetD tttLargeFiber60Block2Chunk2Rows i default)

def tttLargeFiber60Block2Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber60Block2Chunk2Rows i default
  row.parent == tttLargeFiber60ParentOf row.source

def tttLargeFiber60Block2Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber60Block2Chunk2Sources 0 0 == 704
      && tttLargeFiber60ParentOf 704 == 672
      && tttLargeFiber60ParentOf 672 == 544
      && 544 == tttLargeFiber60Root
      && decide (2 <= tttLargeFiber60MaxParentDepth)
  | 1 => listGetD tttLargeFiber60Block2Chunk2Sources 1 0 == 705
      && tttLargeFiber60ParentOf 705 == 673
      && tttLargeFiber60ParentOf 673 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 2 => listGetD tttLargeFiber60Block2Chunk2Sources 2 0 == 706
      && tttLargeFiber60ParentOf 706 == 674
      && tttLargeFiber60ParentOf 674 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 3 => listGetD tttLargeFiber60Block2Chunk2Sources 3 0 == 707
      && tttLargeFiber60ParentOf 707 == 704
      && tttLargeFiber60ParentOf 704 == 672
      && tttLargeFiber60ParentOf 672 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 4 => listGetD tttLargeFiber60Block2Chunk2Sources 4 0 == 708
      && tttLargeFiber60ParentOf 708 == 704
      && tttLargeFiber60ParentOf 704 == 672
      && tttLargeFiber60ParentOf 672 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 5 => listGetD tttLargeFiber60Block2Chunk2Sources 5 0 == 709
      && tttLargeFiber60ParentOf 709 == 705
      && tttLargeFiber60ParentOf 705 == 673
      && tttLargeFiber60ParentOf 673 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 6 => listGetD tttLargeFiber60Block2Chunk2Sources 6 0 == 710
      && tttLargeFiber60ParentOf 710 == 678
      && tttLargeFiber60ParentOf 678 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 7 => listGetD tttLargeFiber60Block2Chunk2Sources 7 0 == 711
      && tttLargeFiber60ParentOf 711 == 679
      && tttLargeFiber60ParentOf 679 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 8 => listGetD tttLargeFiber60Block2Chunk2Sources 8 0 == 712
      && tttLargeFiber60ParentOf 712 == 680
      && tttLargeFiber60ParentOf 680 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (3 <= tttLargeFiber60MaxParentDepth)
  | 9 => listGetD tttLargeFiber60Block2Chunk2Sources 9 0 == 713
      && tttLargeFiber60ParentOf 713 == 681
      && tttLargeFiber60ParentOf 681 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 10 => listGetD tttLargeFiber60Block2Chunk2Sources 10 0 == 714
      && tttLargeFiber60ParentOf 714 == 682
      && tttLargeFiber60ParentOf 682 == 554
      && tttLargeFiber60ParentOf 554 == 546
      && tttLargeFiber60ParentOf 546 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 11 => listGetD tttLargeFiber60Block2Chunk2Sources 11 0 == 715
      && tttLargeFiber60ParentOf 715 == 712
      && tttLargeFiber60ParentOf 712 == 680
      && tttLargeFiber60ParentOf 680 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 12 => listGetD tttLargeFiber60Block2Chunk2Sources 12 0 == 716
      && tttLargeFiber60ParentOf 716 == 712
      && tttLargeFiber60ParentOf 712 == 680
      && tttLargeFiber60ParentOf 680 == 552
      && tttLargeFiber60ParentOf 552 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | 13 => listGetD tttLargeFiber60Block2Chunk2Sources 13 0 == 717
      && tttLargeFiber60ParentOf 717 == 713
      && tttLargeFiber60ParentOf 713 == 681
      && tttLargeFiber60ParentOf 681 == 553
      && tttLargeFiber60ParentOf 553 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 14 => listGetD tttLargeFiber60Block2Chunk2Sources 14 0 == 718
      && tttLargeFiber60ParentOf 718 == 686
      && tttLargeFiber60ParentOf 686 == 558
      && tttLargeFiber60ParentOf 558 == 550
      && tttLargeFiber60ParentOf 550 == 545
      && tttLargeFiber60ParentOf 545 == 544
      && 544 == tttLargeFiber60Root
      && decide (5 <= tttLargeFiber60MaxParentDepth)
  | 15 => listGetD tttLargeFiber60Block2Chunk2Sources 15 0 == 719
      && tttLargeFiber60ParentOf 719 == 687
      && tttLargeFiber60ParentOf 687 == 559
      && tttLargeFiber60ParentOf 559 == 551
      && tttLargeFiber60ParentOf 551 == 544
      && 544 == tttLargeFiber60Root
      && decide (4 <= tttLargeFiber60MaxParentDepth)
  | _ => false

theorem tttLargeFiber60Block2Chunk2Row_0_ok :
    tttLargeFiber60Block2Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2Row_1_ok :
    tttLargeFiber60Block2Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2Row_2_ok :
    tttLargeFiber60Block2Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2Row_3_ok :
    tttLargeFiber60Block2Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2Row_4_ok :
    tttLargeFiber60Block2Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2Row_5_ok :
    tttLargeFiber60Block2Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2Row_6_ok :
    tttLargeFiber60Block2Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2Row_7_ok :
    tttLargeFiber60Block2Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2Row_8_ok :
    tttLargeFiber60Block2Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2Row_9_ok :
    tttLargeFiber60Block2Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2Row_10_ok :
    tttLargeFiber60Block2Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2Row_11_ok :
    tttLargeFiber60Block2Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2Row_12_ok :
    tttLargeFiber60Block2Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2Row_13_ok :
    tttLargeFiber60Block2Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2Row_14_ok :
    tttLargeFiber60Block2Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2Row_15_ok :
    tttLargeFiber60Block2Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentMap_0_ok :
    tttLargeFiber60Block2Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentMap_1_ok :
    tttLargeFiber60Block2Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentMap_2_ok :
    tttLargeFiber60Block2Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentMap_3_ok :
    tttLargeFiber60Block2Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentMap_4_ok :
    tttLargeFiber60Block2Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentMap_5_ok :
    tttLargeFiber60Block2Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentMap_6_ok :
    tttLargeFiber60Block2Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentMap_7_ok :
    tttLargeFiber60Block2Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentMap_8_ok :
    tttLargeFiber60Block2Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentMap_9_ok :
    tttLargeFiber60Block2Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentMap_10_ok :
    tttLargeFiber60Block2Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentMap_11_ok :
    tttLargeFiber60Block2Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentMap_12_ok :
    tttLargeFiber60Block2Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentMap_13_ok :
    tttLargeFiber60Block2Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentMap_14_ok :
    tttLargeFiber60Block2Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentMap_15_ok :
    tttLargeFiber60Block2Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentPath_0_ok :
    tttLargeFiber60Block2Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentPath_1_ok :
    tttLargeFiber60Block2Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentPath_2_ok :
    tttLargeFiber60Block2Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentPath_3_ok :
    tttLargeFiber60Block2Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentPath_4_ok :
    tttLargeFiber60Block2Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentPath_5_ok :
    tttLargeFiber60Block2Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentPath_6_ok :
    tttLargeFiber60Block2Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentPath_7_ok :
    tttLargeFiber60Block2Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentPath_8_ok :
    tttLargeFiber60Block2Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentPath_9_ok :
    tttLargeFiber60Block2Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentPath_10_ok :
    tttLargeFiber60Block2Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentPath_11_ok :
    tttLargeFiber60Block2Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentPath_12_ok :
    tttLargeFiber60Block2Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentPath_13_ok :
    tttLargeFiber60Block2Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentPath_14_ok :
    tttLargeFiber60Block2Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber60Block2Chunk2ParentPath_15_ok :
    tttLargeFiber60Block2Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber60Block2Chunk2RowsAudit : Bool :=
  tttLargeFiber60Block2Chunk2RowCheck 0
    && tttLargeFiber60Block2Chunk2RowCheck 1
    && tttLargeFiber60Block2Chunk2RowCheck 2
    && tttLargeFiber60Block2Chunk2RowCheck 3
    && tttLargeFiber60Block2Chunk2RowCheck 4
    && tttLargeFiber60Block2Chunk2RowCheck 5
    && tttLargeFiber60Block2Chunk2RowCheck 6
    && tttLargeFiber60Block2Chunk2RowCheck 7
    && tttLargeFiber60Block2Chunk2RowCheck 8
    && tttLargeFiber60Block2Chunk2RowCheck 9
    && tttLargeFiber60Block2Chunk2RowCheck 10
    && tttLargeFiber60Block2Chunk2RowCheck 11
    && tttLargeFiber60Block2Chunk2RowCheck 12
    && tttLargeFiber60Block2Chunk2RowCheck 13
    && tttLargeFiber60Block2Chunk2RowCheck 14
    && tttLargeFiber60Block2Chunk2RowCheck 15

theorem tttLargeFiber60Block2Chunk2RowsAudit_ok :
    tttLargeFiber60Block2Chunk2RowsAudit = true := by
  simp [tttLargeFiber60Block2Chunk2RowsAudit,
    tttLargeFiber60Block2Chunk2Row_0_ok,
    tttLargeFiber60Block2Chunk2Row_1_ok,
    tttLargeFiber60Block2Chunk2Row_2_ok,
    tttLargeFiber60Block2Chunk2Row_3_ok,
    tttLargeFiber60Block2Chunk2Row_4_ok,
    tttLargeFiber60Block2Chunk2Row_5_ok,
    tttLargeFiber60Block2Chunk2Row_6_ok,
    tttLargeFiber60Block2Chunk2Row_7_ok,
    tttLargeFiber60Block2Chunk2Row_8_ok,
    tttLargeFiber60Block2Chunk2Row_9_ok,
    tttLargeFiber60Block2Chunk2Row_10_ok,
    tttLargeFiber60Block2Chunk2Row_11_ok,
    tttLargeFiber60Block2Chunk2Row_12_ok,
    tttLargeFiber60Block2Chunk2Row_13_ok,
    tttLargeFiber60Block2Chunk2Row_14_ok,
    tttLargeFiber60Block2Chunk2Row_15_ok]

def tttLargeFiber60Block2Chunk2ParentMapAudit : Bool :=
  tttLargeFiber60Block2Chunk2ParentMapCheck 0
    && tttLargeFiber60Block2Chunk2ParentMapCheck 1
    && tttLargeFiber60Block2Chunk2ParentMapCheck 2
    && tttLargeFiber60Block2Chunk2ParentMapCheck 3
    && tttLargeFiber60Block2Chunk2ParentMapCheck 4
    && tttLargeFiber60Block2Chunk2ParentMapCheck 5
    && tttLargeFiber60Block2Chunk2ParentMapCheck 6
    && tttLargeFiber60Block2Chunk2ParentMapCheck 7
    && tttLargeFiber60Block2Chunk2ParentMapCheck 8
    && tttLargeFiber60Block2Chunk2ParentMapCheck 9
    && tttLargeFiber60Block2Chunk2ParentMapCheck 10
    && tttLargeFiber60Block2Chunk2ParentMapCheck 11
    && tttLargeFiber60Block2Chunk2ParentMapCheck 12
    && tttLargeFiber60Block2Chunk2ParentMapCheck 13
    && tttLargeFiber60Block2Chunk2ParentMapCheck 14
    && tttLargeFiber60Block2Chunk2ParentMapCheck 15

theorem tttLargeFiber60Block2Chunk2ParentMapAudit_ok :
    tttLargeFiber60Block2Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber60Block2Chunk2ParentMapAudit,
    tttLargeFiber60Block2Chunk2ParentMap_0_ok,
    tttLargeFiber60Block2Chunk2ParentMap_1_ok,
    tttLargeFiber60Block2Chunk2ParentMap_2_ok,
    tttLargeFiber60Block2Chunk2ParentMap_3_ok,
    tttLargeFiber60Block2Chunk2ParentMap_4_ok,
    tttLargeFiber60Block2Chunk2ParentMap_5_ok,
    tttLargeFiber60Block2Chunk2ParentMap_6_ok,
    tttLargeFiber60Block2Chunk2ParentMap_7_ok,
    tttLargeFiber60Block2Chunk2ParentMap_8_ok,
    tttLargeFiber60Block2Chunk2ParentMap_9_ok,
    tttLargeFiber60Block2Chunk2ParentMap_10_ok,
    tttLargeFiber60Block2Chunk2ParentMap_11_ok,
    tttLargeFiber60Block2Chunk2ParentMap_12_ok,
    tttLargeFiber60Block2Chunk2ParentMap_13_ok,
    tttLargeFiber60Block2Chunk2ParentMap_14_ok,
    tttLargeFiber60Block2Chunk2ParentMap_15_ok]

def tttLargeFiber60Block2Chunk2ParentsAudit : Bool :=
  tttLargeFiber60Block2Chunk2ParentPathCheck 0
    && tttLargeFiber60Block2Chunk2ParentPathCheck 1
    && tttLargeFiber60Block2Chunk2ParentPathCheck 2
    && tttLargeFiber60Block2Chunk2ParentPathCheck 3
    && tttLargeFiber60Block2Chunk2ParentPathCheck 4
    && tttLargeFiber60Block2Chunk2ParentPathCheck 5
    && tttLargeFiber60Block2Chunk2ParentPathCheck 6
    && tttLargeFiber60Block2Chunk2ParentPathCheck 7
    && tttLargeFiber60Block2Chunk2ParentPathCheck 8
    && tttLargeFiber60Block2Chunk2ParentPathCheck 9
    && tttLargeFiber60Block2Chunk2ParentPathCheck 10
    && tttLargeFiber60Block2Chunk2ParentPathCheck 11
    && tttLargeFiber60Block2Chunk2ParentPathCheck 12
    && tttLargeFiber60Block2Chunk2ParentPathCheck 13
    && tttLargeFiber60Block2Chunk2ParentPathCheck 14
    && tttLargeFiber60Block2Chunk2ParentPathCheck 15

theorem tttLargeFiber60Block2Chunk2ParentsAudit_ok :
    tttLargeFiber60Block2Chunk2ParentsAudit = true := by
  simp [tttLargeFiber60Block2Chunk2ParentsAudit,
    tttLargeFiber60Block2Chunk2ParentPath_0_ok,
    tttLargeFiber60Block2Chunk2ParentPath_1_ok,
    tttLargeFiber60Block2Chunk2ParentPath_2_ok,
    tttLargeFiber60Block2Chunk2ParentPath_3_ok,
    tttLargeFiber60Block2Chunk2ParentPath_4_ok,
    tttLargeFiber60Block2Chunk2ParentPath_5_ok,
    tttLargeFiber60Block2Chunk2ParentPath_6_ok,
    tttLargeFiber60Block2Chunk2ParentPath_7_ok,
    tttLargeFiber60Block2Chunk2ParentPath_8_ok,
    tttLargeFiber60Block2Chunk2ParentPath_9_ok,
    tttLargeFiber60Block2Chunk2ParentPath_10_ok,
    tttLargeFiber60Block2Chunk2ParentPath_11_ok,
    tttLargeFiber60Block2Chunk2ParentPath_12_ok,
    tttLargeFiber60Block2Chunk2ParentPath_13_ok,
    tttLargeFiber60Block2Chunk2ParentPath_14_ok,
    tttLargeFiber60Block2Chunk2ParentPath_15_ok]

def tttLargeFiber60Block2Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber60CountsAudit &&
    tttLargeFiber60Block2Chunk2SourcesCheck &&
    tttLargeFiber60Block2Chunk2RowsAudit &&
    tttLargeFiber60Block2Chunk2ParentMapAudit &&
    tttLargeFiber60Block2Chunk2ParentsAudit

theorem tttLargeFiber60Block2Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber60Block2Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber60Block2Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber60CountsAudit_ok,
    tttLargeFiber60Block2Chunk2SourcesCheck_ok,
    tttLargeFiber60Block2Chunk2RowsAudit_ok,
    tttLargeFiber60Block2Chunk2ParentMapAudit_ok,
    tttLargeFiber60Block2Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber60Block2Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
