import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber72Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 72, block 1 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber72Block1Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber72Data

def tttLargeFiber72Block1Chunk2Sources : List Nat :=
  [   912, 913, 914, 915, 916, 917, 918, 919,
   920, 921, 922, 923, 924, 925, 926, 927]

def tttLargeFiber72Row96 : TripleComponentParentRow :=
  tripleRow 912 848 25 108 132 24 100 132
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row97 : TripleComponentParentRow :=
  tripleRow 913 849 25 108 133 24 100 133
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row98 : TripleComponentParentRow :=
  tripleRow 914 850 25 108 134 24 100 134
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row99 : TripleComponentParentRow :=
  tripleRow 915 851 25 108 135 24 100 135
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row100 : TripleComponentParentRow :=
  tripleRow 916 852 25 108 180 24 100 180
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row101 : TripleComponentParentRow :=
  tripleRow 917 853 25 108 181 24 100 181
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row102 : TripleComponentParentRow :=
  tripleRow 918 854 25 108 182 24 100 182
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row103 : TripleComponentParentRow :=
  tripleRow 919 855 25 108 183 24 100 183
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row104 : TripleComponentParentRow :=
  tripleRow 920 856 25 109 140 24 101 140
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row105 : TripleComponentParentRow :=
  tripleRow 921 857 25 109 141 24 101 141
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row106 : TripleComponentParentRow :=
  tripleRow 922 858 25 109 142 24 101 142
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row107 : TripleComponentParentRow :=
  tripleRow 923 859 25 109 143 24 101 143
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row108 : TripleComponentParentRow :=
  tripleRow 924 860 25 109 188 24 101 188
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row109 : TripleComponentParentRow :=
  tripleRow 925 861 25 109 189 24 101 189
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row110 : TripleComponentParentRow :=
  tripleRow 926 862 25 109 190 24 101 190
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Row111 : TripleComponentParentRow :=
  tripleRow 927 863 25 109 191 24 101 191
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber72Block1Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber72Row96
  , tttLargeFiber72Row97
  , tttLargeFiber72Row98
  , tttLargeFiber72Row99
  , tttLargeFiber72Row100
  , tttLargeFiber72Row101
  , tttLargeFiber72Row102
  , tttLargeFiber72Row103
  , tttLargeFiber72Row104
  , tttLargeFiber72Row105
  , tttLargeFiber72Row106
  , tttLargeFiber72Row107
  , tttLargeFiber72Row108
  , tttLargeFiber72Row109
  , tttLargeFiber72Row110
  , tttLargeFiber72Row111
  ]

def tttLargeFiber72Block1Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (816 <= i) && decide (i < 1072)) ||
    (decide (1360 <= i) && decide (i < 1616))

def tttLargeFiber72Block1Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber72Block1Chunk2ExpectedContains row.source &&
    tttLargeFiber72Block1Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber72Key &&
          chainInputKey tttWord t == tttLargeFiber72Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber72Block1Chunk2SourcesCheck : Bool :=
  (tttLargeFiber72Block1Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber72Block1Chunk2Sources

theorem tttLargeFiber72Block1Chunk2SourcesCheck_ok :
    tttLargeFiber72Block1Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber72Block1Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber72Block1Chunk2RowValid
    (listGetD tttLargeFiber72Block1Chunk2Rows i default)

def tttLargeFiber72Block1Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber72Block1Chunk2Rows i default
  row.parent == tttLargeFiber72ParentOf row.source

def tttLargeFiber72Block1Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber72Block1Chunk2Sources 0 0 == 912
      && tttLargeFiber72ParentOf 912 == 848
      && tttLargeFiber72ParentOf 848 == 864
      && tttLargeFiber72ParentOf 864 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 1 => listGetD tttLargeFiber72Block1Chunk2Sources 1 0 == 913
      && tttLargeFiber72ParentOf 913 == 849
      && tttLargeFiber72ParentOf 849 == 865
      && tttLargeFiber72ParentOf 865 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 2 => listGetD tttLargeFiber72Block1Chunk2Sources 2 0 == 914
      && tttLargeFiber72ParentOf 914 == 850
      && tttLargeFiber72ParentOf 850 == 838
      && tttLargeFiber72ParentOf 838 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 3 => listGetD tttLargeFiber72Block1Chunk2Sources 3 0 == 915
      && tttLargeFiber72ParentOf 915 == 851
      && tttLargeFiber72ParentOf 851 == 839
      && tttLargeFiber72ParentOf 839 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 4 => listGetD tttLargeFiber72Block1Chunk2Sources 4 0 == 916
      && tttLargeFiber72ParentOf 916 == 852
      && tttLargeFiber72ParentOf 852 == 834
      && tttLargeFiber72ParentOf 834 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 5 => listGetD tttLargeFiber72Block1Chunk2Sources 5 0 == 917
      && tttLargeFiber72ParentOf 917 == 853
      && tttLargeFiber72ParentOf 853 == 855
      && tttLargeFiber72ParentOf 855 == 832
      && tttLargeFiber72ParentOf 832 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 6 => listGetD tttLargeFiber72Block1Chunk2Sources 6 0 == 918
      && tttLargeFiber72ParentOf 918 == 854
      && tttLargeFiber72ParentOf 854 == 833
      && tttLargeFiber72ParentOf 833 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 7 => listGetD tttLargeFiber72Block1Chunk2Sources 7 0 == 919
      && tttLargeFiber72ParentOf 919 == 855
      && tttLargeFiber72ParentOf 855 == 832
      && tttLargeFiber72ParentOf 832 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 8 => listGetD tttLargeFiber72Block1Chunk2Sources 8 0 == 920
      && tttLargeFiber72ParentOf 920 == 856
      && tttLargeFiber72ParentOf 856 == 872
      && tttLargeFiber72ParentOf 872 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 9 => listGetD tttLargeFiber72Block1Chunk2Sources 9 0 == 921
      && tttLargeFiber72ParentOf 921 == 857
      && tttLargeFiber72ParentOf 857 == 873
      && tttLargeFiber72ParentOf 873 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 10 => listGetD tttLargeFiber72Block1Chunk2Sources 10 0 == 922
      && tttLargeFiber72ParentOf 922 == 858
      && tttLargeFiber72ParentOf 858 == 874
      && tttLargeFiber72ParentOf 874 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 11 => listGetD tttLargeFiber72Block1Chunk2Sources 11 0 == 923
      && tttLargeFiber72ParentOf 923 == 859
      && tttLargeFiber72ParentOf 859 == 856
      && tttLargeFiber72ParentOf 856 == 872
      && tttLargeFiber72ParentOf 872 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 12 => listGetD tttLargeFiber72Block1Chunk2Sources 12 0 == 924
      && tttLargeFiber72ParentOf 924 == 860
      && tttLargeFiber72ParentOf 860 == 856
      && tttLargeFiber72ParentOf 856 == 872
      && tttLargeFiber72ParentOf 872 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 13 => listGetD tttLargeFiber72Block1Chunk2Sources 13 0 == 925
      && tttLargeFiber72ParentOf 925 == 861
      && tttLargeFiber72ParentOf 861 == 857
      && tttLargeFiber72ParentOf 857 == 873
      && tttLargeFiber72ParentOf 873 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 14 => listGetD tttLargeFiber72Block1Chunk2Sources 14 0 == 926
      && tttLargeFiber72ParentOf 926 == 862
      && tttLargeFiber72ParentOf 862 == 878
      && tttLargeFiber72ParentOf 878 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 15 => listGetD tttLargeFiber72Block1Chunk2Sources 15 0 == 927
      && tttLargeFiber72ParentOf 927 == 863
      && tttLargeFiber72ParentOf 863 == 879
      && tttLargeFiber72ParentOf 879 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | _ => false

theorem tttLargeFiber72Block1Chunk2Row_0_ok :
    tttLargeFiber72Block1Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2Row_1_ok :
    tttLargeFiber72Block1Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2Row_2_ok :
    tttLargeFiber72Block1Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2Row_3_ok :
    tttLargeFiber72Block1Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2Row_4_ok :
    tttLargeFiber72Block1Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2Row_5_ok :
    tttLargeFiber72Block1Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2Row_6_ok :
    tttLargeFiber72Block1Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2Row_7_ok :
    tttLargeFiber72Block1Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2Row_8_ok :
    tttLargeFiber72Block1Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2Row_9_ok :
    tttLargeFiber72Block1Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2Row_10_ok :
    tttLargeFiber72Block1Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2Row_11_ok :
    tttLargeFiber72Block1Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2Row_12_ok :
    tttLargeFiber72Block1Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2Row_13_ok :
    tttLargeFiber72Block1Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2Row_14_ok :
    tttLargeFiber72Block1Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2Row_15_ok :
    tttLargeFiber72Block1Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentMap_0_ok :
    tttLargeFiber72Block1Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentMap_1_ok :
    tttLargeFiber72Block1Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentMap_2_ok :
    tttLargeFiber72Block1Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentMap_3_ok :
    tttLargeFiber72Block1Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentMap_4_ok :
    tttLargeFiber72Block1Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentMap_5_ok :
    tttLargeFiber72Block1Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentMap_6_ok :
    tttLargeFiber72Block1Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentMap_7_ok :
    tttLargeFiber72Block1Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentMap_8_ok :
    tttLargeFiber72Block1Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentMap_9_ok :
    tttLargeFiber72Block1Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentMap_10_ok :
    tttLargeFiber72Block1Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentMap_11_ok :
    tttLargeFiber72Block1Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentMap_12_ok :
    tttLargeFiber72Block1Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentMap_13_ok :
    tttLargeFiber72Block1Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentMap_14_ok :
    tttLargeFiber72Block1Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentMap_15_ok :
    tttLargeFiber72Block1Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentPath_0_ok :
    tttLargeFiber72Block1Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentPath_1_ok :
    tttLargeFiber72Block1Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentPath_2_ok :
    tttLargeFiber72Block1Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentPath_3_ok :
    tttLargeFiber72Block1Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentPath_4_ok :
    tttLargeFiber72Block1Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentPath_5_ok :
    tttLargeFiber72Block1Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentPath_6_ok :
    tttLargeFiber72Block1Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentPath_7_ok :
    tttLargeFiber72Block1Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentPath_8_ok :
    tttLargeFiber72Block1Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentPath_9_ok :
    tttLargeFiber72Block1Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentPath_10_ok :
    tttLargeFiber72Block1Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentPath_11_ok :
    tttLargeFiber72Block1Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentPath_12_ok :
    tttLargeFiber72Block1Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentPath_13_ok :
    tttLargeFiber72Block1Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentPath_14_ok :
    tttLargeFiber72Block1Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber72Block1Chunk2ParentPath_15_ok :
    tttLargeFiber72Block1Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber72Block1Chunk2RowsAudit : Bool :=
  tttLargeFiber72Block1Chunk2RowCheck 0
    && tttLargeFiber72Block1Chunk2RowCheck 1
    && tttLargeFiber72Block1Chunk2RowCheck 2
    && tttLargeFiber72Block1Chunk2RowCheck 3
    && tttLargeFiber72Block1Chunk2RowCheck 4
    && tttLargeFiber72Block1Chunk2RowCheck 5
    && tttLargeFiber72Block1Chunk2RowCheck 6
    && tttLargeFiber72Block1Chunk2RowCheck 7
    && tttLargeFiber72Block1Chunk2RowCheck 8
    && tttLargeFiber72Block1Chunk2RowCheck 9
    && tttLargeFiber72Block1Chunk2RowCheck 10
    && tttLargeFiber72Block1Chunk2RowCheck 11
    && tttLargeFiber72Block1Chunk2RowCheck 12
    && tttLargeFiber72Block1Chunk2RowCheck 13
    && tttLargeFiber72Block1Chunk2RowCheck 14
    && tttLargeFiber72Block1Chunk2RowCheck 15

theorem tttLargeFiber72Block1Chunk2RowsAudit_ok :
    tttLargeFiber72Block1Chunk2RowsAudit = true := by
  simp [tttLargeFiber72Block1Chunk2RowsAudit,
    tttLargeFiber72Block1Chunk2Row_0_ok,
    tttLargeFiber72Block1Chunk2Row_1_ok,
    tttLargeFiber72Block1Chunk2Row_2_ok,
    tttLargeFiber72Block1Chunk2Row_3_ok,
    tttLargeFiber72Block1Chunk2Row_4_ok,
    tttLargeFiber72Block1Chunk2Row_5_ok,
    tttLargeFiber72Block1Chunk2Row_6_ok,
    tttLargeFiber72Block1Chunk2Row_7_ok,
    tttLargeFiber72Block1Chunk2Row_8_ok,
    tttLargeFiber72Block1Chunk2Row_9_ok,
    tttLargeFiber72Block1Chunk2Row_10_ok,
    tttLargeFiber72Block1Chunk2Row_11_ok,
    tttLargeFiber72Block1Chunk2Row_12_ok,
    tttLargeFiber72Block1Chunk2Row_13_ok,
    tttLargeFiber72Block1Chunk2Row_14_ok,
    tttLargeFiber72Block1Chunk2Row_15_ok]

def tttLargeFiber72Block1Chunk2ParentMapAudit : Bool :=
  tttLargeFiber72Block1Chunk2ParentMapCheck 0
    && tttLargeFiber72Block1Chunk2ParentMapCheck 1
    && tttLargeFiber72Block1Chunk2ParentMapCheck 2
    && tttLargeFiber72Block1Chunk2ParentMapCheck 3
    && tttLargeFiber72Block1Chunk2ParentMapCheck 4
    && tttLargeFiber72Block1Chunk2ParentMapCheck 5
    && tttLargeFiber72Block1Chunk2ParentMapCheck 6
    && tttLargeFiber72Block1Chunk2ParentMapCheck 7
    && tttLargeFiber72Block1Chunk2ParentMapCheck 8
    && tttLargeFiber72Block1Chunk2ParentMapCheck 9
    && tttLargeFiber72Block1Chunk2ParentMapCheck 10
    && tttLargeFiber72Block1Chunk2ParentMapCheck 11
    && tttLargeFiber72Block1Chunk2ParentMapCheck 12
    && tttLargeFiber72Block1Chunk2ParentMapCheck 13
    && tttLargeFiber72Block1Chunk2ParentMapCheck 14
    && tttLargeFiber72Block1Chunk2ParentMapCheck 15

theorem tttLargeFiber72Block1Chunk2ParentMapAudit_ok :
    tttLargeFiber72Block1Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber72Block1Chunk2ParentMapAudit,
    tttLargeFiber72Block1Chunk2ParentMap_0_ok,
    tttLargeFiber72Block1Chunk2ParentMap_1_ok,
    tttLargeFiber72Block1Chunk2ParentMap_2_ok,
    tttLargeFiber72Block1Chunk2ParentMap_3_ok,
    tttLargeFiber72Block1Chunk2ParentMap_4_ok,
    tttLargeFiber72Block1Chunk2ParentMap_5_ok,
    tttLargeFiber72Block1Chunk2ParentMap_6_ok,
    tttLargeFiber72Block1Chunk2ParentMap_7_ok,
    tttLargeFiber72Block1Chunk2ParentMap_8_ok,
    tttLargeFiber72Block1Chunk2ParentMap_9_ok,
    tttLargeFiber72Block1Chunk2ParentMap_10_ok,
    tttLargeFiber72Block1Chunk2ParentMap_11_ok,
    tttLargeFiber72Block1Chunk2ParentMap_12_ok,
    tttLargeFiber72Block1Chunk2ParentMap_13_ok,
    tttLargeFiber72Block1Chunk2ParentMap_14_ok,
    tttLargeFiber72Block1Chunk2ParentMap_15_ok]

def tttLargeFiber72Block1Chunk2ParentsAudit : Bool :=
  tttLargeFiber72Block1Chunk2ParentPathCheck 0
    && tttLargeFiber72Block1Chunk2ParentPathCheck 1
    && tttLargeFiber72Block1Chunk2ParentPathCheck 2
    && tttLargeFiber72Block1Chunk2ParentPathCheck 3
    && tttLargeFiber72Block1Chunk2ParentPathCheck 4
    && tttLargeFiber72Block1Chunk2ParentPathCheck 5
    && tttLargeFiber72Block1Chunk2ParentPathCheck 6
    && tttLargeFiber72Block1Chunk2ParentPathCheck 7
    && tttLargeFiber72Block1Chunk2ParentPathCheck 8
    && tttLargeFiber72Block1Chunk2ParentPathCheck 9
    && tttLargeFiber72Block1Chunk2ParentPathCheck 10
    && tttLargeFiber72Block1Chunk2ParentPathCheck 11
    && tttLargeFiber72Block1Chunk2ParentPathCheck 12
    && tttLargeFiber72Block1Chunk2ParentPathCheck 13
    && tttLargeFiber72Block1Chunk2ParentPathCheck 14
    && tttLargeFiber72Block1Chunk2ParentPathCheck 15

theorem tttLargeFiber72Block1Chunk2ParentsAudit_ok :
    tttLargeFiber72Block1Chunk2ParentsAudit = true := by
  simp [tttLargeFiber72Block1Chunk2ParentsAudit,
    tttLargeFiber72Block1Chunk2ParentPath_0_ok,
    tttLargeFiber72Block1Chunk2ParentPath_1_ok,
    tttLargeFiber72Block1Chunk2ParentPath_2_ok,
    tttLargeFiber72Block1Chunk2ParentPath_3_ok,
    tttLargeFiber72Block1Chunk2ParentPath_4_ok,
    tttLargeFiber72Block1Chunk2ParentPath_5_ok,
    tttLargeFiber72Block1Chunk2ParentPath_6_ok,
    tttLargeFiber72Block1Chunk2ParentPath_7_ok,
    tttLargeFiber72Block1Chunk2ParentPath_8_ok,
    tttLargeFiber72Block1Chunk2ParentPath_9_ok,
    tttLargeFiber72Block1Chunk2ParentPath_10_ok,
    tttLargeFiber72Block1Chunk2ParentPath_11_ok,
    tttLargeFiber72Block1Chunk2ParentPath_12_ok,
    tttLargeFiber72Block1Chunk2ParentPath_13_ok,
    tttLargeFiber72Block1Chunk2ParentPath_14_ok,
    tttLargeFiber72Block1Chunk2ParentPath_15_ok]

def tttLargeFiber72Block1Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber72CountsAudit &&
    tttLargeFiber72Block1Chunk2SourcesCheck &&
    tttLargeFiber72Block1Chunk2RowsAudit &&
    tttLargeFiber72Block1Chunk2ParentMapAudit &&
    tttLargeFiber72Block1Chunk2ParentsAudit

theorem tttLargeFiber72Block1Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber72Block1Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber72Block1Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber72CountsAudit_ok,
    tttLargeFiber72Block1Chunk2SourcesCheck_ok,
    tttLargeFiber72Block1Chunk2RowsAudit_ok,
    tttLargeFiber72Block1Chunk2ParentMapAudit_ok,
    tttLargeFiber72Block1Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber72Block1Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
