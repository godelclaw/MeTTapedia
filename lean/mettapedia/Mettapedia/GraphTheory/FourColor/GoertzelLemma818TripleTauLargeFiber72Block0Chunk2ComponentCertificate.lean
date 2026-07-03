import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber72Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 72, block 0 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber72Block0Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber72Data

def tttLargeFiber72Block0Chunk2Sources : List Nat :=
  [   848, 849, 850, 851, 852, 853, 854, 855,
   856, 857, 858, 859, 860, 861, 862, 863]

def tttLargeFiber72Row32 : TripleComponentParentRow :=
  tripleRow 848 864 24 100 132 24 102 64
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row33 : TripleComponentParentRow :=
  tripleRow 849 865 24 100 133 24 102 65
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row34 : TripleComponentParentRow :=
  tripleRow 850 838 24 100 134 24 82 34
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber72Row35 : TripleComponentParentRow :=
  tripleRow 851 839 24 100 135 24 82 35
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber72Row36 : TripleComponentParentRow :=
  tripleRow 852 834 24 100 180 24 82 18
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row37 : TripleComponentParentRow :=
  tripleRow 853 855 24 100 181 24 100 183
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row38 : TripleComponentParentRow :=
  tripleRow 854 833 24 100 182 24 82 17
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber72Row39 : TripleComponentParentRow :=
  tripleRow 855 832 24 100 183 24 82 16
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber72Row40 : TripleComponentParentRow :=
  tripleRow 856 872 24 101 140 24 103 72
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row41 : TripleComponentParentRow :=
  tripleRow 857 873 24 101 141 24 103 73
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row42 : TripleComponentParentRow :=
  tripleRow 858 874 24 101 142 24 103 74
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber72Row43 : TripleComponentParentRow :=
  tripleRow 859 856 24 101 143 24 101 140
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row44 : TripleComponentParentRow :=
  tripleRow 860 856 24 101 188 24 101 140
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber72Row45 : TripleComponentParentRow :=
  tripleRow 861 857 24 101 189 24 101 141
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber72Row46 : TripleComponentParentRow :=
  tripleRow 862 878 24 101 190 24 103 126
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber72Row47 : TripleComponentParentRow :=
  tripleRow 863 879 24 101 191 24 103 127
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber72Block0Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber72Row32
  , tttLargeFiber72Row33
  , tttLargeFiber72Row34
  , tttLargeFiber72Row35
  , tttLargeFiber72Row36
  , tttLargeFiber72Row37
  , tttLargeFiber72Row38
  , tttLargeFiber72Row39
  , tttLargeFiber72Row40
  , tttLargeFiber72Row41
  , tttLargeFiber72Row42
  , tttLargeFiber72Row43
  , tttLargeFiber72Row44
  , tttLargeFiber72Row45
  , tttLargeFiber72Row46
  , tttLargeFiber72Row47
  ]

def tttLargeFiber72Block0Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (816 <= i) && decide (i < 1072)) ||
    (decide (1360 <= i) && decide (i < 1616))

def tttLargeFiber72Block0Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber72Block0Chunk2ExpectedContains row.source &&
    tttLargeFiber72Block0Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber72Key &&
          chainInputKey tttWord t == tttLargeFiber72Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber72Block0Chunk2SourcesCheck : Bool :=
  (tttLargeFiber72Block0Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber72Block0Chunk2Sources

theorem tttLargeFiber72Block0Chunk2SourcesCheck_ok :
    tttLargeFiber72Block0Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber72Block0Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber72Block0Chunk2RowValid
    (listGetD tttLargeFiber72Block0Chunk2Rows i default)

def tttLargeFiber72Block0Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber72Block0Chunk2Rows i default
  row.parent == tttLargeFiber72ParentOf row.source

def tttLargeFiber72Block0Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber72Block0Chunk2Sources 0 0 == 848
      && tttLargeFiber72ParentOf 848 == 864
      && tttLargeFiber72ParentOf 864 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 1 => listGetD tttLargeFiber72Block0Chunk2Sources 1 0 == 849
      && tttLargeFiber72ParentOf 849 == 865
      && tttLargeFiber72ParentOf 865 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 2 => listGetD tttLargeFiber72Block0Chunk2Sources 2 0 == 850
      && tttLargeFiber72ParentOf 850 == 838
      && tttLargeFiber72ParentOf 838 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 3 => listGetD tttLargeFiber72Block0Chunk2Sources 3 0 == 851
      && tttLargeFiber72ParentOf 851 == 839
      && tttLargeFiber72ParentOf 839 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 4 => listGetD tttLargeFiber72Block0Chunk2Sources 4 0 == 852
      && tttLargeFiber72ParentOf 852 == 834
      && tttLargeFiber72ParentOf 834 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 5 => listGetD tttLargeFiber72Block0Chunk2Sources 5 0 == 853
      && tttLargeFiber72ParentOf 853 == 855
      && tttLargeFiber72ParentOf 855 == 832
      && tttLargeFiber72ParentOf 832 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 6 => listGetD tttLargeFiber72Block0Chunk2Sources 6 0 == 854
      && tttLargeFiber72ParentOf 854 == 833
      && tttLargeFiber72ParentOf 833 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 7 => listGetD tttLargeFiber72Block0Chunk2Sources 7 0 == 855
      && tttLargeFiber72ParentOf 855 == 832
      && tttLargeFiber72ParentOf 832 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 8 => listGetD tttLargeFiber72Block0Chunk2Sources 8 0 == 856
      && tttLargeFiber72ParentOf 856 == 872
      && tttLargeFiber72ParentOf 872 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 9 => listGetD tttLargeFiber72Block0Chunk2Sources 9 0 == 857
      && tttLargeFiber72ParentOf 857 == 873
      && tttLargeFiber72ParentOf 873 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 10 => listGetD tttLargeFiber72Block0Chunk2Sources 10 0 == 858
      && tttLargeFiber72ParentOf 858 == 874
      && tttLargeFiber72ParentOf 874 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 11 => listGetD tttLargeFiber72Block0Chunk2Sources 11 0 == 859
      && tttLargeFiber72ParentOf 859 == 856
      && tttLargeFiber72ParentOf 856 == 872
      && tttLargeFiber72ParentOf 872 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 12 => listGetD tttLargeFiber72Block0Chunk2Sources 12 0 == 860
      && tttLargeFiber72ParentOf 860 == 856
      && tttLargeFiber72ParentOf 856 == 872
      && tttLargeFiber72ParentOf 872 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 13 => listGetD tttLargeFiber72Block0Chunk2Sources 13 0 == 861
      && tttLargeFiber72ParentOf 861 == 857
      && tttLargeFiber72ParentOf 857 == 873
      && tttLargeFiber72ParentOf 873 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 14 => listGetD tttLargeFiber72Block0Chunk2Sources 14 0 == 862
      && tttLargeFiber72ParentOf 862 == 878
      && tttLargeFiber72ParentOf 878 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 15 => listGetD tttLargeFiber72Block0Chunk2Sources 15 0 == 863
      && tttLargeFiber72ParentOf 863 == 879
      && tttLargeFiber72ParentOf 879 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | _ => false

theorem tttLargeFiber72Block0Chunk2Row_0_ok :
    tttLargeFiber72Block0Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2Row_1_ok :
    tttLargeFiber72Block0Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2Row_2_ok :
    tttLargeFiber72Block0Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2Row_3_ok :
    tttLargeFiber72Block0Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2Row_4_ok :
    tttLargeFiber72Block0Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2Row_5_ok :
    tttLargeFiber72Block0Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2Row_6_ok :
    tttLargeFiber72Block0Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2Row_7_ok :
    tttLargeFiber72Block0Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2Row_8_ok :
    tttLargeFiber72Block0Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2Row_9_ok :
    tttLargeFiber72Block0Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2Row_10_ok :
    tttLargeFiber72Block0Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2Row_11_ok :
    tttLargeFiber72Block0Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2Row_12_ok :
    tttLargeFiber72Block0Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2Row_13_ok :
    tttLargeFiber72Block0Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2Row_14_ok :
    tttLargeFiber72Block0Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2Row_15_ok :
    tttLargeFiber72Block0Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentMap_0_ok :
    tttLargeFiber72Block0Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentMap_1_ok :
    tttLargeFiber72Block0Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentMap_2_ok :
    tttLargeFiber72Block0Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentMap_3_ok :
    tttLargeFiber72Block0Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentMap_4_ok :
    tttLargeFiber72Block0Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentMap_5_ok :
    tttLargeFiber72Block0Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentMap_6_ok :
    tttLargeFiber72Block0Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentMap_7_ok :
    tttLargeFiber72Block0Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentMap_8_ok :
    tttLargeFiber72Block0Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentMap_9_ok :
    tttLargeFiber72Block0Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentMap_10_ok :
    tttLargeFiber72Block0Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentMap_11_ok :
    tttLargeFiber72Block0Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentMap_12_ok :
    tttLargeFiber72Block0Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentMap_13_ok :
    tttLargeFiber72Block0Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentMap_14_ok :
    tttLargeFiber72Block0Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentMap_15_ok :
    tttLargeFiber72Block0Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentPath_0_ok :
    tttLargeFiber72Block0Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentPath_1_ok :
    tttLargeFiber72Block0Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentPath_2_ok :
    tttLargeFiber72Block0Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentPath_3_ok :
    tttLargeFiber72Block0Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentPath_4_ok :
    tttLargeFiber72Block0Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentPath_5_ok :
    tttLargeFiber72Block0Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentPath_6_ok :
    tttLargeFiber72Block0Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentPath_7_ok :
    tttLargeFiber72Block0Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentPath_8_ok :
    tttLargeFiber72Block0Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentPath_9_ok :
    tttLargeFiber72Block0Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentPath_10_ok :
    tttLargeFiber72Block0Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentPath_11_ok :
    tttLargeFiber72Block0Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentPath_12_ok :
    tttLargeFiber72Block0Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentPath_13_ok :
    tttLargeFiber72Block0Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentPath_14_ok :
    tttLargeFiber72Block0Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber72Block0Chunk2ParentPath_15_ok :
    tttLargeFiber72Block0Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber72Block0Chunk2RowsAudit : Bool :=
  tttLargeFiber72Block0Chunk2RowCheck 0
    && tttLargeFiber72Block0Chunk2RowCheck 1
    && tttLargeFiber72Block0Chunk2RowCheck 2
    && tttLargeFiber72Block0Chunk2RowCheck 3
    && tttLargeFiber72Block0Chunk2RowCheck 4
    && tttLargeFiber72Block0Chunk2RowCheck 5
    && tttLargeFiber72Block0Chunk2RowCheck 6
    && tttLargeFiber72Block0Chunk2RowCheck 7
    && tttLargeFiber72Block0Chunk2RowCheck 8
    && tttLargeFiber72Block0Chunk2RowCheck 9
    && tttLargeFiber72Block0Chunk2RowCheck 10
    && tttLargeFiber72Block0Chunk2RowCheck 11
    && tttLargeFiber72Block0Chunk2RowCheck 12
    && tttLargeFiber72Block0Chunk2RowCheck 13
    && tttLargeFiber72Block0Chunk2RowCheck 14
    && tttLargeFiber72Block0Chunk2RowCheck 15

theorem tttLargeFiber72Block0Chunk2RowsAudit_ok :
    tttLargeFiber72Block0Chunk2RowsAudit = true := by
  simp [tttLargeFiber72Block0Chunk2RowsAudit,
    tttLargeFiber72Block0Chunk2Row_0_ok,
    tttLargeFiber72Block0Chunk2Row_1_ok,
    tttLargeFiber72Block0Chunk2Row_2_ok,
    tttLargeFiber72Block0Chunk2Row_3_ok,
    tttLargeFiber72Block0Chunk2Row_4_ok,
    tttLargeFiber72Block0Chunk2Row_5_ok,
    tttLargeFiber72Block0Chunk2Row_6_ok,
    tttLargeFiber72Block0Chunk2Row_7_ok,
    tttLargeFiber72Block0Chunk2Row_8_ok,
    tttLargeFiber72Block0Chunk2Row_9_ok,
    tttLargeFiber72Block0Chunk2Row_10_ok,
    tttLargeFiber72Block0Chunk2Row_11_ok,
    tttLargeFiber72Block0Chunk2Row_12_ok,
    tttLargeFiber72Block0Chunk2Row_13_ok,
    tttLargeFiber72Block0Chunk2Row_14_ok,
    tttLargeFiber72Block0Chunk2Row_15_ok]

def tttLargeFiber72Block0Chunk2ParentMapAudit : Bool :=
  tttLargeFiber72Block0Chunk2ParentMapCheck 0
    && tttLargeFiber72Block0Chunk2ParentMapCheck 1
    && tttLargeFiber72Block0Chunk2ParentMapCheck 2
    && tttLargeFiber72Block0Chunk2ParentMapCheck 3
    && tttLargeFiber72Block0Chunk2ParentMapCheck 4
    && tttLargeFiber72Block0Chunk2ParentMapCheck 5
    && tttLargeFiber72Block0Chunk2ParentMapCheck 6
    && tttLargeFiber72Block0Chunk2ParentMapCheck 7
    && tttLargeFiber72Block0Chunk2ParentMapCheck 8
    && tttLargeFiber72Block0Chunk2ParentMapCheck 9
    && tttLargeFiber72Block0Chunk2ParentMapCheck 10
    && tttLargeFiber72Block0Chunk2ParentMapCheck 11
    && tttLargeFiber72Block0Chunk2ParentMapCheck 12
    && tttLargeFiber72Block0Chunk2ParentMapCheck 13
    && tttLargeFiber72Block0Chunk2ParentMapCheck 14
    && tttLargeFiber72Block0Chunk2ParentMapCheck 15

theorem tttLargeFiber72Block0Chunk2ParentMapAudit_ok :
    tttLargeFiber72Block0Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber72Block0Chunk2ParentMapAudit,
    tttLargeFiber72Block0Chunk2ParentMap_0_ok,
    tttLargeFiber72Block0Chunk2ParentMap_1_ok,
    tttLargeFiber72Block0Chunk2ParentMap_2_ok,
    tttLargeFiber72Block0Chunk2ParentMap_3_ok,
    tttLargeFiber72Block0Chunk2ParentMap_4_ok,
    tttLargeFiber72Block0Chunk2ParentMap_5_ok,
    tttLargeFiber72Block0Chunk2ParentMap_6_ok,
    tttLargeFiber72Block0Chunk2ParentMap_7_ok,
    tttLargeFiber72Block0Chunk2ParentMap_8_ok,
    tttLargeFiber72Block0Chunk2ParentMap_9_ok,
    tttLargeFiber72Block0Chunk2ParentMap_10_ok,
    tttLargeFiber72Block0Chunk2ParentMap_11_ok,
    tttLargeFiber72Block0Chunk2ParentMap_12_ok,
    tttLargeFiber72Block0Chunk2ParentMap_13_ok,
    tttLargeFiber72Block0Chunk2ParentMap_14_ok,
    tttLargeFiber72Block0Chunk2ParentMap_15_ok]

def tttLargeFiber72Block0Chunk2ParentsAudit : Bool :=
  tttLargeFiber72Block0Chunk2ParentPathCheck 0
    && tttLargeFiber72Block0Chunk2ParentPathCheck 1
    && tttLargeFiber72Block0Chunk2ParentPathCheck 2
    && tttLargeFiber72Block0Chunk2ParentPathCheck 3
    && tttLargeFiber72Block0Chunk2ParentPathCheck 4
    && tttLargeFiber72Block0Chunk2ParentPathCheck 5
    && tttLargeFiber72Block0Chunk2ParentPathCheck 6
    && tttLargeFiber72Block0Chunk2ParentPathCheck 7
    && tttLargeFiber72Block0Chunk2ParentPathCheck 8
    && tttLargeFiber72Block0Chunk2ParentPathCheck 9
    && tttLargeFiber72Block0Chunk2ParentPathCheck 10
    && tttLargeFiber72Block0Chunk2ParentPathCheck 11
    && tttLargeFiber72Block0Chunk2ParentPathCheck 12
    && tttLargeFiber72Block0Chunk2ParentPathCheck 13
    && tttLargeFiber72Block0Chunk2ParentPathCheck 14
    && tttLargeFiber72Block0Chunk2ParentPathCheck 15

theorem tttLargeFiber72Block0Chunk2ParentsAudit_ok :
    tttLargeFiber72Block0Chunk2ParentsAudit = true := by
  simp [tttLargeFiber72Block0Chunk2ParentsAudit,
    tttLargeFiber72Block0Chunk2ParentPath_0_ok,
    tttLargeFiber72Block0Chunk2ParentPath_1_ok,
    tttLargeFiber72Block0Chunk2ParentPath_2_ok,
    tttLargeFiber72Block0Chunk2ParentPath_3_ok,
    tttLargeFiber72Block0Chunk2ParentPath_4_ok,
    tttLargeFiber72Block0Chunk2ParentPath_5_ok,
    tttLargeFiber72Block0Chunk2ParentPath_6_ok,
    tttLargeFiber72Block0Chunk2ParentPath_7_ok,
    tttLargeFiber72Block0Chunk2ParentPath_8_ok,
    tttLargeFiber72Block0Chunk2ParentPath_9_ok,
    tttLargeFiber72Block0Chunk2ParentPath_10_ok,
    tttLargeFiber72Block0Chunk2ParentPath_11_ok,
    tttLargeFiber72Block0Chunk2ParentPath_12_ok,
    tttLargeFiber72Block0Chunk2ParentPath_13_ok,
    tttLargeFiber72Block0Chunk2ParentPath_14_ok,
    tttLargeFiber72Block0Chunk2ParentPath_15_ok]

def tttLargeFiber72Block0Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber72CountsAudit &&
    tttLargeFiber72Block0Chunk2SourcesCheck &&
    tttLargeFiber72Block0Chunk2RowsAudit &&
    tttLargeFiber72Block0Chunk2ParentMapAudit &&
    tttLargeFiber72Block0Chunk2ParentsAudit

theorem tttLargeFiber72Block0Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber72Block0Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber72Block0Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber72CountsAudit_ok,
    tttLargeFiber72Block0Chunk2SourcesCheck_ok,
    tttLargeFiber72Block0Chunk2RowsAudit_ok,
    tttLargeFiber72Block0Chunk2ParentMapAudit_ok,
    tttLargeFiber72Block0Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber72Block0Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
