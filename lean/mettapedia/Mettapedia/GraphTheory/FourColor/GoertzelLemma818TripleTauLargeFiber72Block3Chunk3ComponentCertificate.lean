import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber72Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 72, block 3 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber72Block3Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber72Data

def tttLargeFiber72Block3Chunk3Sources : List Nat :=
  [   1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063,
   1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071]

def tttLargeFiber72Row240 : TripleComponentParentRow :=
  tripleRow 1056 928 27 42 0 25 110 64
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

def tttLargeFiber72Row241 : TripleComponentParentRow :=
  tripleRow 1057 929 27 42 1 25 110 65
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

def tttLargeFiber72Row242 : TripleComponentParentRow :=
  tripleRow 1058 930 27 42 2 25 110 66
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

def tttLargeFiber72Row243 : TripleComponentParentRow :=
  tripleRow 1059 931 27 42 3 25 110 67
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

def tttLargeFiber72Row244 : TripleComponentParentRow :=
  tripleRow 1060 1056 27 42 48 27 42 0
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row245 : TripleComponentParentRow :=
  tripleRow 1061 1057 27 42 49 27 42 1
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row246 : TripleComponentParentRow :=
  tripleRow 1062 934 27 42 50 25 110 118
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

def tttLargeFiber72Row247 : TripleComponentParentRow :=
  tripleRow 1063 935 27 42 51 25 110 119
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

def tttLargeFiber72Row248 : TripleComponentParentRow :=
  tripleRow 1064 936 27 43 8 25 111 72
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

def tttLargeFiber72Row249 : TripleComponentParentRow :=
  tripleRow 1065 937 27 43 9 25 111 73
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

def tttLargeFiber72Row250 : TripleComponentParentRow :=
  tripleRow 1066 938 27 43 10 25 111 74
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

def tttLargeFiber72Row251 : TripleComponentParentRow :=
  tripleRow 1067 939 27 43 11 25 111 75
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

def tttLargeFiber72Row252 : TripleComponentParentRow :=
  tripleRow 1068 1064 27 43 56 27 43 8
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row253 : TripleComponentParentRow :=
  tripleRow 1069 1065 27 43 57 27 43 9
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row254 : TripleComponentParentRow :=
  tripleRow 1070 942 27 43 58 25 111 126
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

def tttLargeFiber72Row255 : TripleComponentParentRow :=
  tripleRow 1071 943 27 43 59 25 111 127
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

def tttLargeFiber72Block3Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber72Row240
  , tttLargeFiber72Row241
  , tttLargeFiber72Row242
  , tttLargeFiber72Row243
  , tttLargeFiber72Row244
  , tttLargeFiber72Row245
  , tttLargeFiber72Row246
  , tttLargeFiber72Row247
  , tttLargeFiber72Row248
  , tttLargeFiber72Row249
  , tttLargeFiber72Row250
  , tttLargeFiber72Row251
  , tttLargeFiber72Row252
  , tttLargeFiber72Row253
  , tttLargeFiber72Row254
  , tttLargeFiber72Row255
  ]

def tttLargeFiber72Block3Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (816 <= i) && decide (i < 1072)) ||
    (decide (1360 <= i) && decide (i < 1616))

def tttLargeFiber72Block3Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber72Block3Chunk3ExpectedContains row.source &&
    tttLargeFiber72Block3Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber72Key &&
          chainInputKey tttWord t == tttLargeFiber72Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber72Block3Chunk3SourcesCheck : Bool :=
  (tttLargeFiber72Block3Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber72Block3Chunk3Sources

theorem tttLargeFiber72Block3Chunk3SourcesCheck_ok :
    tttLargeFiber72Block3Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber72Block3Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber72Block3Chunk3RowValid
    (listGetD tttLargeFiber72Block3Chunk3Rows i default)

def tttLargeFiber72Block3Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber72Block3Chunk3Rows i default
  row.parent == tttLargeFiber72ParentOf row.source

def tttLargeFiber72Block3Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber72Block3Chunk3Sources 0 0 == 1056
      && tttLargeFiber72ParentOf 1056 == 928
      && tttLargeFiber72ParentOf 928 == 864
      && tttLargeFiber72ParentOf 864 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 1 => listGetD tttLargeFiber72Block3Chunk3Sources 1 0 == 1057
      && tttLargeFiber72ParentOf 1057 == 929
      && tttLargeFiber72ParentOf 929 == 865
      && tttLargeFiber72ParentOf 865 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 2 => listGetD tttLargeFiber72Block3Chunk3Sources 2 0 == 1058
      && tttLargeFiber72ParentOf 1058 == 930
      && tttLargeFiber72ParentOf 930 == 866
      && tttLargeFiber72ParentOf 866 == 826
      && tttLargeFiber72ParentOf 826 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 3 => listGetD tttLargeFiber72Block3Chunk3Sources 3 0 == 1059
      && tttLargeFiber72ParentOf 1059 == 931
      && tttLargeFiber72ParentOf 931 == 867
      && tttLargeFiber72ParentOf 867 == 827
      && tttLargeFiber72ParentOf 827 == 819
      && tttLargeFiber72ParentOf 819 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (6 <= tttLargeFiber72MaxParentDepth)
  | 4 => listGetD tttLargeFiber72Block3Chunk3Sources 4 0 == 1060
      && tttLargeFiber72ParentOf 1060 == 1056
      && tttLargeFiber72ParentOf 1056 == 928
      && tttLargeFiber72ParentOf 928 == 864
      && tttLargeFiber72ParentOf 864 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 5 => listGetD tttLargeFiber72Block3Chunk3Sources 5 0 == 1061
      && tttLargeFiber72ParentOf 1061 == 1057
      && tttLargeFiber72ParentOf 1057 == 929
      && tttLargeFiber72ParentOf 929 == 865
      && tttLargeFiber72ParentOf 865 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (6 <= tttLargeFiber72MaxParentDepth)
  | 6 => listGetD tttLargeFiber72Block3Chunk3Sources 6 0 == 1062
      && tttLargeFiber72ParentOf 1062 == 934
      && tttLargeFiber72ParentOf 934 == 870
      && tttLargeFiber72ParentOf 870 == 830
      && tttLargeFiber72ParentOf 830 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (6 <= tttLargeFiber72MaxParentDepth)
  | 7 => listGetD tttLargeFiber72Block3Chunk3Sources 7 0 == 1063
      && tttLargeFiber72ParentOf 1063 == 935
      && tttLargeFiber72ParentOf 935 == 871
      && tttLargeFiber72ParentOf 871 == 831
      && tttLargeFiber72ParentOf 831 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 8 => listGetD tttLargeFiber72Block3Chunk3Sources 8 0 == 1064
      && tttLargeFiber72ParentOf 1064 == 936
      && tttLargeFiber72ParentOf 936 == 872
      && tttLargeFiber72ParentOf 872 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 9 => listGetD tttLargeFiber72Block3Chunk3Sources 9 0 == 1065
      && tttLargeFiber72ParentOf 1065 == 937
      && tttLargeFiber72ParentOf 937 == 873
      && tttLargeFiber72ParentOf 873 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 10 => listGetD tttLargeFiber72Block3Chunk3Sources 10 0 == 1066
      && tttLargeFiber72ParentOf 1066 == 938
      && tttLargeFiber72ParentOf 938 == 874
      && tttLargeFiber72ParentOf 874 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 11 => listGetD tttLargeFiber72Block3Chunk3Sources 11 0 == 1067
      && tttLargeFiber72ParentOf 1067 == 939
      && tttLargeFiber72ParentOf 939 == 875
      && tttLargeFiber72ParentOf 875 == 819
      && tttLargeFiber72ParentOf 819 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 12 => listGetD tttLargeFiber72Block3Chunk3Sources 12 0 == 1068
      && tttLargeFiber72ParentOf 1068 == 1064
      && tttLargeFiber72ParentOf 1064 == 936
      && tttLargeFiber72ParentOf 936 == 872
      && tttLargeFiber72ParentOf 872 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 13 => listGetD tttLargeFiber72Block3Chunk3Sources 13 0 == 1069
      && tttLargeFiber72ParentOf 1069 == 1065
      && tttLargeFiber72ParentOf 1065 == 937
      && tttLargeFiber72ParentOf 937 == 873
      && tttLargeFiber72ParentOf 873 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 14 => listGetD tttLargeFiber72Block3Chunk3Sources 14 0 == 1070
      && tttLargeFiber72ParentOf 1070 == 942
      && tttLargeFiber72ParentOf 942 == 878
      && tttLargeFiber72ParentOf 878 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 15 => listGetD tttLargeFiber72Block3Chunk3Sources 15 0 == 1071
      && tttLargeFiber72ParentOf 1071 == 943
      && tttLargeFiber72ParentOf 943 == 879
      && tttLargeFiber72ParentOf 879 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | _ => false

theorem tttLargeFiber72Block3Chunk3Row_0_ok :
    tttLargeFiber72Block3Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3Row_1_ok :
    tttLargeFiber72Block3Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3Row_2_ok :
    tttLargeFiber72Block3Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3Row_3_ok :
    tttLargeFiber72Block3Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3Row_4_ok :
    tttLargeFiber72Block3Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3Row_5_ok :
    tttLargeFiber72Block3Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3Row_6_ok :
    tttLargeFiber72Block3Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3Row_7_ok :
    tttLargeFiber72Block3Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3Row_8_ok :
    tttLargeFiber72Block3Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3Row_9_ok :
    tttLargeFiber72Block3Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3Row_10_ok :
    tttLargeFiber72Block3Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3Row_11_ok :
    tttLargeFiber72Block3Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3Row_12_ok :
    tttLargeFiber72Block3Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3Row_13_ok :
    tttLargeFiber72Block3Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3Row_14_ok :
    tttLargeFiber72Block3Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3Row_15_ok :
    tttLargeFiber72Block3Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentMap_0_ok :
    tttLargeFiber72Block3Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentMap_1_ok :
    tttLargeFiber72Block3Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentMap_2_ok :
    tttLargeFiber72Block3Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentMap_3_ok :
    tttLargeFiber72Block3Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentMap_4_ok :
    tttLargeFiber72Block3Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentMap_5_ok :
    tttLargeFiber72Block3Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentMap_6_ok :
    tttLargeFiber72Block3Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentMap_7_ok :
    tttLargeFiber72Block3Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentMap_8_ok :
    tttLargeFiber72Block3Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentMap_9_ok :
    tttLargeFiber72Block3Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentMap_10_ok :
    tttLargeFiber72Block3Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentMap_11_ok :
    tttLargeFiber72Block3Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentMap_12_ok :
    tttLargeFiber72Block3Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentMap_13_ok :
    tttLargeFiber72Block3Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentMap_14_ok :
    tttLargeFiber72Block3Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentMap_15_ok :
    tttLargeFiber72Block3Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentPath_0_ok :
    tttLargeFiber72Block3Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentPath_1_ok :
    tttLargeFiber72Block3Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentPath_2_ok :
    tttLargeFiber72Block3Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentPath_3_ok :
    tttLargeFiber72Block3Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentPath_4_ok :
    tttLargeFiber72Block3Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentPath_5_ok :
    tttLargeFiber72Block3Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentPath_6_ok :
    tttLargeFiber72Block3Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentPath_7_ok :
    tttLargeFiber72Block3Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentPath_8_ok :
    tttLargeFiber72Block3Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentPath_9_ok :
    tttLargeFiber72Block3Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentPath_10_ok :
    tttLargeFiber72Block3Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentPath_11_ok :
    tttLargeFiber72Block3Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentPath_12_ok :
    tttLargeFiber72Block3Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentPath_13_ok :
    tttLargeFiber72Block3Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentPath_14_ok :
    tttLargeFiber72Block3Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber72Block3Chunk3ParentPath_15_ok :
    tttLargeFiber72Block3Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber72Block3Chunk3RowsAudit : Bool :=
  tttLargeFiber72Block3Chunk3RowCheck 0
    && tttLargeFiber72Block3Chunk3RowCheck 1
    && tttLargeFiber72Block3Chunk3RowCheck 2
    && tttLargeFiber72Block3Chunk3RowCheck 3
    && tttLargeFiber72Block3Chunk3RowCheck 4
    && tttLargeFiber72Block3Chunk3RowCheck 5
    && tttLargeFiber72Block3Chunk3RowCheck 6
    && tttLargeFiber72Block3Chunk3RowCheck 7
    && tttLargeFiber72Block3Chunk3RowCheck 8
    && tttLargeFiber72Block3Chunk3RowCheck 9
    && tttLargeFiber72Block3Chunk3RowCheck 10
    && tttLargeFiber72Block3Chunk3RowCheck 11
    && tttLargeFiber72Block3Chunk3RowCheck 12
    && tttLargeFiber72Block3Chunk3RowCheck 13
    && tttLargeFiber72Block3Chunk3RowCheck 14
    && tttLargeFiber72Block3Chunk3RowCheck 15

theorem tttLargeFiber72Block3Chunk3RowsAudit_ok :
    tttLargeFiber72Block3Chunk3RowsAudit = true := by
  simp [tttLargeFiber72Block3Chunk3RowsAudit,
    tttLargeFiber72Block3Chunk3Row_0_ok,
    tttLargeFiber72Block3Chunk3Row_1_ok,
    tttLargeFiber72Block3Chunk3Row_2_ok,
    tttLargeFiber72Block3Chunk3Row_3_ok,
    tttLargeFiber72Block3Chunk3Row_4_ok,
    tttLargeFiber72Block3Chunk3Row_5_ok,
    tttLargeFiber72Block3Chunk3Row_6_ok,
    tttLargeFiber72Block3Chunk3Row_7_ok,
    tttLargeFiber72Block3Chunk3Row_8_ok,
    tttLargeFiber72Block3Chunk3Row_9_ok,
    tttLargeFiber72Block3Chunk3Row_10_ok,
    tttLargeFiber72Block3Chunk3Row_11_ok,
    tttLargeFiber72Block3Chunk3Row_12_ok,
    tttLargeFiber72Block3Chunk3Row_13_ok,
    tttLargeFiber72Block3Chunk3Row_14_ok,
    tttLargeFiber72Block3Chunk3Row_15_ok]

def tttLargeFiber72Block3Chunk3ParentMapAudit : Bool :=
  tttLargeFiber72Block3Chunk3ParentMapCheck 0
    && tttLargeFiber72Block3Chunk3ParentMapCheck 1
    && tttLargeFiber72Block3Chunk3ParentMapCheck 2
    && tttLargeFiber72Block3Chunk3ParentMapCheck 3
    && tttLargeFiber72Block3Chunk3ParentMapCheck 4
    && tttLargeFiber72Block3Chunk3ParentMapCheck 5
    && tttLargeFiber72Block3Chunk3ParentMapCheck 6
    && tttLargeFiber72Block3Chunk3ParentMapCheck 7
    && tttLargeFiber72Block3Chunk3ParentMapCheck 8
    && tttLargeFiber72Block3Chunk3ParentMapCheck 9
    && tttLargeFiber72Block3Chunk3ParentMapCheck 10
    && tttLargeFiber72Block3Chunk3ParentMapCheck 11
    && tttLargeFiber72Block3Chunk3ParentMapCheck 12
    && tttLargeFiber72Block3Chunk3ParentMapCheck 13
    && tttLargeFiber72Block3Chunk3ParentMapCheck 14
    && tttLargeFiber72Block3Chunk3ParentMapCheck 15

theorem tttLargeFiber72Block3Chunk3ParentMapAudit_ok :
    tttLargeFiber72Block3Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber72Block3Chunk3ParentMapAudit,
    tttLargeFiber72Block3Chunk3ParentMap_0_ok,
    tttLargeFiber72Block3Chunk3ParentMap_1_ok,
    tttLargeFiber72Block3Chunk3ParentMap_2_ok,
    tttLargeFiber72Block3Chunk3ParentMap_3_ok,
    tttLargeFiber72Block3Chunk3ParentMap_4_ok,
    tttLargeFiber72Block3Chunk3ParentMap_5_ok,
    tttLargeFiber72Block3Chunk3ParentMap_6_ok,
    tttLargeFiber72Block3Chunk3ParentMap_7_ok,
    tttLargeFiber72Block3Chunk3ParentMap_8_ok,
    tttLargeFiber72Block3Chunk3ParentMap_9_ok,
    tttLargeFiber72Block3Chunk3ParentMap_10_ok,
    tttLargeFiber72Block3Chunk3ParentMap_11_ok,
    tttLargeFiber72Block3Chunk3ParentMap_12_ok,
    tttLargeFiber72Block3Chunk3ParentMap_13_ok,
    tttLargeFiber72Block3Chunk3ParentMap_14_ok,
    tttLargeFiber72Block3Chunk3ParentMap_15_ok]

def tttLargeFiber72Block3Chunk3ParentsAudit : Bool :=
  tttLargeFiber72Block3Chunk3ParentPathCheck 0
    && tttLargeFiber72Block3Chunk3ParentPathCheck 1
    && tttLargeFiber72Block3Chunk3ParentPathCheck 2
    && tttLargeFiber72Block3Chunk3ParentPathCheck 3
    && tttLargeFiber72Block3Chunk3ParentPathCheck 4
    && tttLargeFiber72Block3Chunk3ParentPathCheck 5
    && tttLargeFiber72Block3Chunk3ParentPathCheck 6
    && tttLargeFiber72Block3Chunk3ParentPathCheck 7
    && tttLargeFiber72Block3Chunk3ParentPathCheck 8
    && tttLargeFiber72Block3Chunk3ParentPathCheck 9
    && tttLargeFiber72Block3Chunk3ParentPathCheck 10
    && tttLargeFiber72Block3Chunk3ParentPathCheck 11
    && tttLargeFiber72Block3Chunk3ParentPathCheck 12
    && tttLargeFiber72Block3Chunk3ParentPathCheck 13
    && tttLargeFiber72Block3Chunk3ParentPathCheck 14
    && tttLargeFiber72Block3Chunk3ParentPathCheck 15

theorem tttLargeFiber72Block3Chunk3ParentsAudit_ok :
    tttLargeFiber72Block3Chunk3ParentsAudit = true := by
  simp [tttLargeFiber72Block3Chunk3ParentsAudit,
    tttLargeFiber72Block3Chunk3ParentPath_0_ok,
    tttLargeFiber72Block3Chunk3ParentPath_1_ok,
    tttLargeFiber72Block3Chunk3ParentPath_2_ok,
    tttLargeFiber72Block3Chunk3ParentPath_3_ok,
    tttLargeFiber72Block3Chunk3ParentPath_4_ok,
    tttLargeFiber72Block3Chunk3ParentPath_5_ok,
    tttLargeFiber72Block3Chunk3ParentPath_6_ok,
    tttLargeFiber72Block3Chunk3ParentPath_7_ok,
    tttLargeFiber72Block3Chunk3ParentPath_8_ok,
    tttLargeFiber72Block3Chunk3ParentPath_9_ok,
    tttLargeFiber72Block3Chunk3ParentPath_10_ok,
    tttLargeFiber72Block3Chunk3ParentPath_11_ok,
    tttLargeFiber72Block3Chunk3ParentPath_12_ok,
    tttLargeFiber72Block3Chunk3ParentPath_13_ok,
    tttLargeFiber72Block3Chunk3ParentPath_14_ok,
    tttLargeFiber72Block3Chunk3ParentPath_15_ok]

def tttLargeFiber72Block3Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber72CountsAudit &&
    tttLargeFiber72Block3Chunk3SourcesCheck &&
    tttLargeFiber72Block3Chunk3RowsAudit &&
    tttLargeFiber72Block3Chunk3ParentMapAudit &&
    tttLargeFiber72Block3Chunk3ParentsAudit

theorem tttLargeFiber72Block3Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber72Block3Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber72Block3Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber72CountsAudit_ok,
    tttLargeFiber72Block3Chunk3SourcesCheck_ok,
    tttLargeFiber72Block3Chunk3RowsAudit_ok,
    tttLargeFiber72Block3Chunk3ParentMapAudit_ok,
    tttLargeFiber72Block3Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber72Block3Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
