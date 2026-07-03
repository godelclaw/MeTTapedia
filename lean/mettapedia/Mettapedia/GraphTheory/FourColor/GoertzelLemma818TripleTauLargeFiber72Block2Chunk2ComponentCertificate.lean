import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber72Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 72, block 2 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber72Block2Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber72Data

def tttLargeFiber72Block2Chunk2Sources : List Nat :=
  [   976, 977, 978, 979, 980, 981, 982, 983,
   984, 985, 986, 987, 988, 989, 990, 991]

def tttLargeFiber72Row160 : TripleComponentParentRow :=
  tripleRow 976 944 26 32 148 26 16 80
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

def tttLargeFiber72Row161 : TripleComponentParentRow :=
  tripleRow 977 945 26 32 149 26 16 81
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

def tttLargeFiber72Row162 : TripleComponentParentRow :=
  tripleRow 978 946 26 32 150 26 16 82
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

def tttLargeFiber72Row163 : TripleComponentParentRow :=
  tripleRow 979 976 26 32 151 26 32 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row164 : TripleComponentParentRow :=
  tripleRow 980 976 26 32 164 26 32 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber72Row165 : TripleComponentParentRow :=
  tripleRow 981 977 26 32 165 26 32 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber72Row166 : TripleComponentParentRow :=
  tripleRow 982 950 26 32 166 26 16 102
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber72Row167 : TripleComponentParentRow :=
  tripleRow 983 951 26 32 167 26 16 103
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber72Row168 : TripleComponentParentRow :=
  tripleRow 984 952 26 33 156 26 17 88
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

def tttLargeFiber72Row169 : TripleComponentParentRow :=
  tripleRow 985 953 26 33 157 26 17 89
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

def tttLargeFiber72Row170 : TripleComponentParentRow :=
  tripleRow 986 954 26 33 158 26 17 90
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

def tttLargeFiber72Row171 : TripleComponentParentRow :=
  tripleRow 987 984 26 33 159 26 33 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row172 : TripleComponentParentRow :=
  tripleRow 988 984 26 33 172 26 33 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber72Row173 : TripleComponentParentRow :=
  tripleRow 989 985 26 33 173 26 33 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber72Row174 : TripleComponentParentRow :=
  tripleRow 990 958 26 33 174 26 17 110
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber72Row175 : TripleComponentParentRow :=
  tripleRow 991 959 26 33 175 26 17 111
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber72Block2Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber72Row160
  , tttLargeFiber72Row161
  , tttLargeFiber72Row162
  , tttLargeFiber72Row163
  , tttLargeFiber72Row164
  , tttLargeFiber72Row165
  , tttLargeFiber72Row166
  , tttLargeFiber72Row167
  , tttLargeFiber72Row168
  , tttLargeFiber72Row169
  , tttLargeFiber72Row170
  , tttLargeFiber72Row171
  , tttLargeFiber72Row172
  , tttLargeFiber72Row173
  , tttLargeFiber72Row174
  , tttLargeFiber72Row175
  ]

def tttLargeFiber72Block2Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (816 <= i) && decide (i < 1072)) ||
    (decide (1360 <= i) && decide (i < 1616))

def tttLargeFiber72Block2Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber72Block2Chunk2ExpectedContains row.source &&
    tttLargeFiber72Block2Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber72Key &&
          chainInputKey tttWord t == tttLargeFiber72Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber72Block2Chunk2SourcesCheck : Bool :=
  (tttLargeFiber72Block2Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber72Block2Chunk2Sources

theorem tttLargeFiber72Block2Chunk2SourcesCheck_ok :
    tttLargeFiber72Block2Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber72Block2Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber72Block2Chunk2RowValid
    (listGetD tttLargeFiber72Block2Chunk2Rows i default)

def tttLargeFiber72Block2Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber72Block2Chunk2Rows i default
  row.parent == tttLargeFiber72ParentOf row.source

def tttLargeFiber72Block2Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber72Block2Chunk2Sources 0 0 == 976
      && tttLargeFiber72ParentOf 976 == 944
      && tttLargeFiber72ParentOf 944 == 816
      && 816 == tttLargeFiber72Root
      && decide (2 <= tttLargeFiber72MaxParentDepth)
  | 1 => listGetD tttLargeFiber72Block2Chunk2Sources 1 0 == 977
      && tttLargeFiber72ParentOf 977 == 945
      && tttLargeFiber72ParentOf 945 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 2 => listGetD tttLargeFiber72Block2Chunk2Sources 2 0 == 978
      && tttLargeFiber72ParentOf 978 == 946
      && tttLargeFiber72ParentOf 946 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 3 => listGetD tttLargeFiber72Block2Chunk2Sources 3 0 == 979
      && tttLargeFiber72ParentOf 979 == 976
      && tttLargeFiber72ParentOf 976 == 944
      && tttLargeFiber72ParentOf 944 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 4 => listGetD tttLargeFiber72Block2Chunk2Sources 4 0 == 980
      && tttLargeFiber72ParentOf 980 == 976
      && tttLargeFiber72ParentOf 976 == 944
      && tttLargeFiber72ParentOf 944 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 5 => listGetD tttLargeFiber72Block2Chunk2Sources 5 0 == 981
      && tttLargeFiber72ParentOf 981 == 977
      && tttLargeFiber72ParentOf 977 == 945
      && tttLargeFiber72ParentOf 945 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 6 => listGetD tttLargeFiber72Block2Chunk2Sources 6 0 == 982
      && tttLargeFiber72ParentOf 982 == 950
      && tttLargeFiber72ParentOf 950 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 7 => listGetD tttLargeFiber72Block2Chunk2Sources 7 0 == 983
      && tttLargeFiber72ParentOf 983 == 951
      && tttLargeFiber72ParentOf 951 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 8 => listGetD tttLargeFiber72Block2Chunk2Sources 8 0 == 984
      && tttLargeFiber72ParentOf 984 == 952
      && tttLargeFiber72ParentOf 952 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 9 => listGetD tttLargeFiber72Block2Chunk2Sources 9 0 == 985
      && tttLargeFiber72ParentOf 985 == 953
      && tttLargeFiber72ParentOf 953 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 10 => listGetD tttLargeFiber72Block2Chunk2Sources 10 0 == 986
      && tttLargeFiber72ParentOf 986 == 954
      && tttLargeFiber72ParentOf 954 == 826
      && tttLargeFiber72ParentOf 826 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 11 => listGetD tttLargeFiber72Block2Chunk2Sources 11 0 == 987
      && tttLargeFiber72ParentOf 987 == 984
      && tttLargeFiber72ParentOf 984 == 952
      && tttLargeFiber72ParentOf 952 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 12 => listGetD tttLargeFiber72Block2Chunk2Sources 12 0 == 988
      && tttLargeFiber72ParentOf 988 == 984
      && tttLargeFiber72ParentOf 984 == 952
      && tttLargeFiber72ParentOf 952 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 13 => listGetD tttLargeFiber72Block2Chunk2Sources 13 0 == 989
      && tttLargeFiber72ParentOf 989 == 985
      && tttLargeFiber72ParentOf 985 == 953
      && tttLargeFiber72ParentOf 953 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 14 => listGetD tttLargeFiber72Block2Chunk2Sources 14 0 == 990
      && tttLargeFiber72ParentOf 990 == 958
      && tttLargeFiber72ParentOf 958 == 830
      && tttLargeFiber72ParentOf 830 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 15 => listGetD tttLargeFiber72Block2Chunk2Sources 15 0 == 991
      && tttLargeFiber72ParentOf 991 == 959
      && tttLargeFiber72ParentOf 959 == 831
      && tttLargeFiber72ParentOf 831 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | _ => false

theorem tttLargeFiber72Block2Chunk2Row_0_ok :
    tttLargeFiber72Block2Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2Row_1_ok :
    tttLargeFiber72Block2Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2Row_2_ok :
    tttLargeFiber72Block2Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2Row_3_ok :
    tttLargeFiber72Block2Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2Row_4_ok :
    tttLargeFiber72Block2Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2Row_5_ok :
    tttLargeFiber72Block2Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2Row_6_ok :
    tttLargeFiber72Block2Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2Row_7_ok :
    tttLargeFiber72Block2Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2Row_8_ok :
    tttLargeFiber72Block2Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2Row_9_ok :
    tttLargeFiber72Block2Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2Row_10_ok :
    tttLargeFiber72Block2Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2Row_11_ok :
    tttLargeFiber72Block2Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2Row_12_ok :
    tttLargeFiber72Block2Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2Row_13_ok :
    tttLargeFiber72Block2Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2Row_14_ok :
    tttLargeFiber72Block2Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2Row_15_ok :
    tttLargeFiber72Block2Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentMap_0_ok :
    tttLargeFiber72Block2Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentMap_1_ok :
    tttLargeFiber72Block2Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentMap_2_ok :
    tttLargeFiber72Block2Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentMap_3_ok :
    tttLargeFiber72Block2Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentMap_4_ok :
    tttLargeFiber72Block2Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentMap_5_ok :
    tttLargeFiber72Block2Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentMap_6_ok :
    tttLargeFiber72Block2Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentMap_7_ok :
    tttLargeFiber72Block2Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentMap_8_ok :
    tttLargeFiber72Block2Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentMap_9_ok :
    tttLargeFiber72Block2Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentMap_10_ok :
    tttLargeFiber72Block2Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentMap_11_ok :
    tttLargeFiber72Block2Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentMap_12_ok :
    tttLargeFiber72Block2Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentMap_13_ok :
    tttLargeFiber72Block2Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentMap_14_ok :
    tttLargeFiber72Block2Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentMap_15_ok :
    tttLargeFiber72Block2Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentPath_0_ok :
    tttLargeFiber72Block2Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentPath_1_ok :
    tttLargeFiber72Block2Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentPath_2_ok :
    tttLargeFiber72Block2Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentPath_3_ok :
    tttLargeFiber72Block2Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentPath_4_ok :
    tttLargeFiber72Block2Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentPath_5_ok :
    tttLargeFiber72Block2Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentPath_6_ok :
    tttLargeFiber72Block2Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentPath_7_ok :
    tttLargeFiber72Block2Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentPath_8_ok :
    tttLargeFiber72Block2Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentPath_9_ok :
    tttLargeFiber72Block2Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentPath_10_ok :
    tttLargeFiber72Block2Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentPath_11_ok :
    tttLargeFiber72Block2Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentPath_12_ok :
    tttLargeFiber72Block2Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentPath_13_ok :
    tttLargeFiber72Block2Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentPath_14_ok :
    tttLargeFiber72Block2Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber72Block2Chunk2ParentPath_15_ok :
    tttLargeFiber72Block2Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber72Block2Chunk2RowsAudit : Bool :=
  tttLargeFiber72Block2Chunk2RowCheck 0
    && tttLargeFiber72Block2Chunk2RowCheck 1
    && tttLargeFiber72Block2Chunk2RowCheck 2
    && tttLargeFiber72Block2Chunk2RowCheck 3
    && tttLargeFiber72Block2Chunk2RowCheck 4
    && tttLargeFiber72Block2Chunk2RowCheck 5
    && tttLargeFiber72Block2Chunk2RowCheck 6
    && tttLargeFiber72Block2Chunk2RowCheck 7
    && tttLargeFiber72Block2Chunk2RowCheck 8
    && tttLargeFiber72Block2Chunk2RowCheck 9
    && tttLargeFiber72Block2Chunk2RowCheck 10
    && tttLargeFiber72Block2Chunk2RowCheck 11
    && tttLargeFiber72Block2Chunk2RowCheck 12
    && tttLargeFiber72Block2Chunk2RowCheck 13
    && tttLargeFiber72Block2Chunk2RowCheck 14
    && tttLargeFiber72Block2Chunk2RowCheck 15

theorem tttLargeFiber72Block2Chunk2RowsAudit_ok :
    tttLargeFiber72Block2Chunk2RowsAudit = true := by
  simp [tttLargeFiber72Block2Chunk2RowsAudit,
    tttLargeFiber72Block2Chunk2Row_0_ok,
    tttLargeFiber72Block2Chunk2Row_1_ok,
    tttLargeFiber72Block2Chunk2Row_2_ok,
    tttLargeFiber72Block2Chunk2Row_3_ok,
    tttLargeFiber72Block2Chunk2Row_4_ok,
    tttLargeFiber72Block2Chunk2Row_5_ok,
    tttLargeFiber72Block2Chunk2Row_6_ok,
    tttLargeFiber72Block2Chunk2Row_7_ok,
    tttLargeFiber72Block2Chunk2Row_8_ok,
    tttLargeFiber72Block2Chunk2Row_9_ok,
    tttLargeFiber72Block2Chunk2Row_10_ok,
    tttLargeFiber72Block2Chunk2Row_11_ok,
    tttLargeFiber72Block2Chunk2Row_12_ok,
    tttLargeFiber72Block2Chunk2Row_13_ok,
    tttLargeFiber72Block2Chunk2Row_14_ok,
    tttLargeFiber72Block2Chunk2Row_15_ok]

def tttLargeFiber72Block2Chunk2ParentMapAudit : Bool :=
  tttLargeFiber72Block2Chunk2ParentMapCheck 0
    && tttLargeFiber72Block2Chunk2ParentMapCheck 1
    && tttLargeFiber72Block2Chunk2ParentMapCheck 2
    && tttLargeFiber72Block2Chunk2ParentMapCheck 3
    && tttLargeFiber72Block2Chunk2ParentMapCheck 4
    && tttLargeFiber72Block2Chunk2ParentMapCheck 5
    && tttLargeFiber72Block2Chunk2ParentMapCheck 6
    && tttLargeFiber72Block2Chunk2ParentMapCheck 7
    && tttLargeFiber72Block2Chunk2ParentMapCheck 8
    && tttLargeFiber72Block2Chunk2ParentMapCheck 9
    && tttLargeFiber72Block2Chunk2ParentMapCheck 10
    && tttLargeFiber72Block2Chunk2ParentMapCheck 11
    && tttLargeFiber72Block2Chunk2ParentMapCheck 12
    && tttLargeFiber72Block2Chunk2ParentMapCheck 13
    && tttLargeFiber72Block2Chunk2ParentMapCheck 14
    && tttLargeFiber72Block2Chunk2ParentMapCheck 15

theorem tttLargeFiber72Block2Chunk2ParentMapAudit_ok :
    tttLargeFiber72Block2Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber72Block2Chunk2ParentMapAudit,
    tttLargeFiber72Block2Chunk2ParentMap_0_ok,
    tttLargeFiber72Block2Chunk2ParentMap_1_ok,
    tttLargeFiber72Block2Chunk2ParentMap_2_ok,
    tttLargeFiber72Block2Chunk2ParentMap_3_ok,
    tttLargeFiber72Block2Chunk2ParentMap_4_ok,
    tttLargeFiber72Block2Chunk2ParentMap_5_ok,
    tttLargeFiber72Block2Chunk2ParentMap_6_ok,
    tttLargeFiber72Block2Chunk2ParentMap_7_ok,
    tttLargeFiber72Block2Chunk2ParentMap_8_ok,
    tttLargeFiber72Block2Chunk2ParentMap_9_ok,
    tttLargeFiber72Block2Chunk2ParentMap_10_ok,
    tttLargeFiber72Block2Chunk2ParentMap_11_ok,
    tttLargeFiber72Block2Chunk2ParentMap_12_ok,
    tttLargeFiber72Block2Chunk2ParentMap_13_ok,
    tttLargeFiber72Block2Chunk2ParentMap_14_ok,
    tttLargeFiber72Block2Chunk2ParentMap_15_ok]

def tttLargeFiber72Block2Chunk2ParentsAudit : Bool :=
  tttLargeFiber72Block2Chunk2ParentPathCheck 0
    && tttLargeFiber72Block2Chunk2ParentPathCheck 1
    && tttLargeFiber72Block2Chunk2ParentPathCheck 2
    && tttLargeFiber72Block2Chunk2ParentPathCheck 3
    && tttLargeFiber72Block2Chunk2ParentPathCheck 4
    && tttLargeFiber72Block2Chunk2ParentPathCheck 5
    && tttLargeFiber72Block2Chunk2ParentPathCheck 6
    && tttLargeFiber72Block2Chunk2ParentPathCheck 7
    && tttLargeFiber72Block2Chunk2ParentPathCheck 8
    && tttLargeFiber72Block2Chunk2ParentPathCheck 9
    && tttLargeFiber72Block2Chunk2ParentPathCheck 10
    && tttLargeFiber72Block2Chunk2ParentPathCheck 11
    && tttLargeFiber72Block2Chunk2ParentPathCheck 12
    && tttLargeFiber72Block2Chunk2ParentPathCheck 13
    && tttLargeFiber72Block2Chunk2ParentPathCheck 14
    && tttLargeFiber72Block2Chunk2ParentPathCheck 15

theorem tttLargeFiber72Block2Chunk2ParentsAudit_ok :
    tttLargeFiber72Block2Chunk2ParentsAudit = true := by
  simp [tttLargeFiber72Block2Chunk2ParentsAudit,
    tttLargeFiber72Block2Chunk2ParentPath_0_ok,
    tttLargeFiber72Block2Chunk2ParentPath_1_ok,
    tttLargeFiber72Block2Chunk2ParentPath_2_ok,
    tttLargeFiber72Block2Chunk2ParentPath_3_ok,
    tttLargeFiber72Block2Chunk2ParentPath_4_ok,
    tttLargeFiber72Block2Chunk2ParentPath_5_ok,
    tttLargeFiber72Block2Chunk2ParentPath_6_ok,
    tttLargeFiber72Block2Chunk2ParentPath_7_ok,
    tttLargeFiber72Block2Chunk2ParentPath_8_ok,
    tttLargeFiber72Block2Chunk2ParentPath_9_ok,
    tttLargeFiber72Block2Chunk2ParentPath_10_ok,
    tttLargeFiber72Block2Chunk2ParentPath_11_ok,
    tttLargeFiber72Block2Chunk2ParentPath_12_ok,
    tttLargeFiber72Block2Chunk2ParentPath_13_ok,
    tttLargeFiber72Block2Chunk2ParentPath_14_ok,
    tttLargeFiber72Block2Chunk2ParentPath_15_ok]

def tttLargeFiber72Block2Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber72CountsAudit &&
    tttLargeFiber72Block2Chunk2SourcesCheck &&
    tttLargeFiber72Block2Chunk2RowsAudit &&
    tttLargeFiber72Block2Chunk2ParentMapAudit &&
    tttLargeFiber72Block2Chunk2ParentsAudit

theorem tttLargeFiber72Block2Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber72Block2Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber72Block2Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber72CountsAudit_ok,
    tttLargeFiber72Block2Chunk2SourcesCheck_ok,
    tttLargeFiber72Block2Chunk2RowsAudit_ok,
    tttLargeFiber72Block2Chunk2ParentMapAudit_ok,
    tttLargeFiber72Block2Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber72Block2Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
