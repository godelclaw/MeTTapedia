import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber72Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 72, block 3 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber72Block3Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber72Data

def tttLargeFiber72Block3Chunk2Sources : List Nat :=
  [   1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047,
   1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055]

def tttLargeFiber72Row224 : TripleComponentParentRow :=
  tripleRow 1040 1008 27 40 148 27 24 80
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

def tttLargeFiber72Row225 : TripleComponentParentRow :=
  tripleRow 1041 1009 27 40 149 27 24 81
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

def tttLargeFiber72Row226 : TripleComponentParentRow :=
  tripleRow 1042 1010 27 40 150 27 24 82
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

def tttLargeFiber72Row227 : TripleComponentParentRow :=
  tripleRow 1043 1040 27 40 151 27 40 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row228 : TripleComponentParentRow :=
  tripleRow 1044 1040 27 40 164 27 40 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber72Row229 : TripleComponentParentRow :=
  tripleRow 1045 1041 27 40 165 27 40 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber72Row230 : TripleComponentParentRow :=
  tripleRow 1046 1014 27 40 166 27 24 102
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber72Row231 : TripleComponentParentRow :=
  tripleRow 1047 1015 27 40 167 27 24 103
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber72Row232 : TripleComponentParentRow :=
  tripleRow 1048 1016 27 41 156 27 25 88
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

def tttLargeFiber72Row233 : TripleComponentParentRow :=
  tripleRow 1049 1017 27 41 157 27 25 89
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

def tttLargeFiber72Row234 : TripleComponentParentRow :=
  tripleRow 1050 1018 27 41 158 27 25 90
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

def tttLargeFiber72Row235 : TripleComponentParentRow :=
  tripleRow 1051 1048 27 41 159 27 41 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber72Row236 : TripleComponentParentRow :=
  tripleRow 1052 1048 27 41 172 27 41 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber72Row237 : TripleComponentParentRow :=
  tripleRow 1053 1049 27 41 173 27 41 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber72Row238 : TripleComponentParentRow :=
  tripleRow 1054 1022 27 41 174 27 25 110
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber72Row239 : TripleComponentParentRow :=
  tripleRow 1055 1023 27 41 175 27 25 111
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber72Block3Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber72Row224
  , tttLargeFiber72Row225
  , tttLargeFiber72Row226
  , tttLargeFiber72Row227
  , tttLargeFiber72Row228
  , tttLargeFiber72Row229
  , tttLargeFiber72Row230
  , tttLargeFiber72Row231
  , tttLargeFiber72Row232
  , tttLargeFiber72Row233
  , tttLargeFiber72Row234
  , tttLargeFiber72Row235
  , tttLargeFiber72Row236
  , tttLargeFiber72Row237
  , tttLargeFiber72Row238
  , tttLargeFiber72Row239
  ]

def tttLargeFiber72Block3Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (816 <= i) && decide (i < 1072)) ||
    (decide (1360 <= i) && decide (i < 1616))

def tttLargeFiber72Block3Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber72Block3Chunk2ExpectedContains row.source &&
    tttLargeFiber72Block3Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber72Key &&
          chainInputKey tttWord t == tttLargeFiber72Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber72Block3Chunk2SourcesCheck : Bool :=
  (tttLargeFiber72Block3Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber72Block3Chunk2Sources

theorem tttLargeFiber72Block3Chunk2SourcesCheck_ok :
    tttLargeFiber72Block3Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber72Block3Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber72Block3Chunk2RowValid
    (listGetD tttLargeFiber72Block3Chunk2Rows i default)

def tttLargeFiber72Block3Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber72Block3Chunk2Rows i default
  row.parent == tttLargeFiber72ParentOf row.source

def tttLargeFiber72Block3Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber72Block3Chunk2Sources 0 0 == 1040
      && tttLargeFiber72ParentOf 1040 == 1008
      && tttLargeFiber72ParentOf 1008 == 880
      && tttLargeFiber72ParentOf 880 == 816
      && 816 == tttLargeFiber72Root
      && decide (3 <= tttLargeFiber72MaxParentDepth)
  | 1 => listGetD tttLargeFiber72Block3Chunk2Sources 1 0 == 1041
      && tttLargeFiber72ParentOf 1041 == 1009
      && tttLargeFiber72ParentOf 1009 == 881
      && tttLargeFiber72ParentOf 881 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 2 => listGetD tttLargeFiber72Block3Chunk2Sources 2 0 == 1042
      && tttLargeFiber72ParentOf 1042 == 1010
      && tttLargeFiber72ParentOf 1010 == 882
      && tttLargeFiber72ParentOf 882 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 3 => listGetD tttLargeFiber72Block3Chunk2Sources 3 0 == 1043
      && tttLargeFiber72ParentOf 1043 == 1040
      && tttLargeFiber72ParentOf 1040 == 1008
      && tttLargeFiber72ParentOf 1008 == 880
      && tttLargeFiber72ParentOf 880 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 4 => listGetD tttLargeFiber72Block3Chunk2Sources 4 0 == 1044
      && tttLargeFiber72ParentOf 1044 == 1040
      && tttLargeFiber72ParentOf 1040 == 1008
      && tttLargeFiber72ParentOf 1008 == 880
      && tttLargeFiber72ParentOf 880 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 5 => listGetD tttLargeFiber72Block3Chunk2Sources 5 0 == 1045
      && tttLargeFiber72ParentOf 1045 == 1041
      && tttLargeFiber72ParentOf 1041 == 1009
      && tttLargeFiber72ParentOf 1009 == 881
      && tttLargeFiber72ParentOf 881 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 6 => listGetD tttLargeFiber72Block3Chunk2Sources 6 0 == 1046
      && tttLargeFiber72ParentOf 1046 == 1014
      && tttLargeFiber72ParentOf 1014 == 886
      && tttLargeFiber72ParentOf 886 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 7 => listGetD tttLargeFiber72Block3Chunk2Sources 7 0 == 1047
      && tttLargeFiber72ParentOf 1047 == 1015
      && tttLargeFiber72ParentOf 1015 == 887
      && tttLargeFiber72ParentOf 887 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 8 => listGetD tttLargeFiber72Block3Chunk2Sources 8 0 == 1048
      && tttLargeFiber72ParentOf 1048 == 1016
      && tttLargeFiber72ParentOf 1016 == 888
      && tttLargeFiber72ParentOf 888 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (4 <= tttLargeFiber72MaxParentDepth)
  | 9 => listGetD tttLargeFiber72Block3Chunk2Sources 9 0 == 1049
      && tttLargeFiber72ParentOf 1049 == 1017
      && tttLargeFiber72ParentOf 1017 == 889
      && tttLargeFiber72ParentOf 889 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 10 => listGetD tttLargeFiber72Block3Chunk2Sources 10 0 == 1050
      && tttLargeFiber72ParentOf 1050 == 1018
      && tttLargeFiber72ParentOf 1018 == 890
      && tttLargeFiber72ParentOf 890 == 826
      && tttLargeFiber72ParentOf 826 == 818
      && tttLargeFiber72ParentOf 818 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 11 => listGetD tttLargeFiber72Block3Chunk2Sources 11 0 == 1051
      && tttLargeFiber72ParentOf 1051 == 1048
      && tttLargeFiber72ParentOf 1048 == 1016
      && tttLargeFiber72ParentOf 1016 == 888
      && tttLargeFiber72ParentOf 888 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 12 => listGetD tttLargeFiber72Block3Chunk2Sources 12 0 == 1052
      && tttLargeFiber72ParentOf 1052 == 1048
      && tttLargeFiber72ParentOf 1048 == 1016
      && tttLargeFiber72ParentOf 1016 == 888
      && tttLargeFiber72ParentOf 888 == 824
      && tttLargeFiber72ParentOf 824 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | 13 => listGetD tttLargeFiber72Block3Chunk2Sources 13 0 == 1053
      && tttLargeFiber72ParentOf 1053 == 1049
      && tttLargeFiber72ParentOf 1049 == 1017
      && tttLargeFiber72ParentOf 1017 == 889
      && tttLargeFiber72ParentOf 889 == 825
      && tttLargeFiber72ParentOf 825 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (6 <= tttLargeFiber72MaxParentDepth)
  | 14 => listGetD tttLargeFiber72Block3Chunk2Sources 14 0 == 1054
      && tttLargeFiber72ParentOf 1054 == 1022
      && tttLargeFiber72ParentOf 1022 == 894
      && tttLargeFiber72ParentOf 894 == 830
      && tttLargeFiber72ParentOf 830 == 822
      && tttLargeFiber72ParentOf 822 == 817
      && tttLargeFiber72ParentOf 817 == 816
      && 816 == tttLargeFiber72Root
      && decide (6 <= tttLargeFiber72MaxParentDepth)
  | 15 => listGetD tttLargeFiber72Block3Chunk2Sources 15 0 == 1055
      && tttLargeFiber72ParentOf 1055 == 1023
      && tttLargeFiber72ParentOf 1023 == 895
      && tttLargeFiber72ParentOf 895 == 831
      && tttLargeFiber72ParentOf 831 == 823
      && tttLargeFiber72ParentOf 823 == 816
      && 816 == tttLargeFiber72Root
      && decide (5 <= tttLargeFiber72MaxParentDepth)
  | _ => false

theorem tttLargeFiber72Block3Chunk2Row_0_ok :
    tttLargeFiber72Block3Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2Row_1_ok :
    tttLargeFiber72Block3Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2Row_2_ok :
    tttLargeFiber72Block3Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2Row_3_ok :
    tttLargeFiber72Block3Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2Row_4_ok :
    tttLargeFiber72Block3Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2Row_5_ok :
    tttLargeFiber72Block3Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2Row_6_ok :
    tttLargeFiber72Block3Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2Row_7_ok :
    tttLargeFiber72Block3Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2Row_8_ok :
    tttLargeFiber72Block3Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2Row_9_ok :
    tttLargeFiber72Block3Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2Row_10_ok :
    tttLargeFiber72Block3Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2Row_11_ok :
    tttLargeFiber72Block3Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2Row_12_ok :
    tttLargeFiber72Block3Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2Row_13_ok :
    tttLargeFiber72Block3Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2Row_14_ok :
    tttLargeFiber72Block3Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2Row_15_ok :
    tttLargeFiber72Block3Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentMap_0_ok :
    tttLargeFiber72Block3Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentMap_1_ok :
    tttLargeFiber72Block3Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentMap_2_ok :
    tttLargeFiber72Block3Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentMap_3_ok :
    tttLargeFiber72Block3Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentMap_4_ok :
    tttLargeFiber72Block3Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentMap_5_ok :
    tttLargeFiber72Block3Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentMap_6_ok :
    tttLargeFiber72Block3Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentMap_7_ok :
    tttLargeFiber72Block3Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentMap_8_ok :
    tttLargeFiber72Block3Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentMap_9_ok :
    tttLargeFiber72Block3Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentMap_10_ok :
    tttLargeFiber72Block3Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentMap_11_ok :
    tttLargeFiber72Block3Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentMap_12_ok :
    tttLargeFiber72Block3Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentMap_13_ok :
    tttLargeFiber72Block3Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentMap_14_ok :
    tttLargeFiber72Block3Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentMap_15_ok :
    tttLargeFiber72Block3Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentPath_0_ok :
    tttLargeFiber72Block3Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentPath_1_ok :
    tttLargeFiber72Block3Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentPath_2_ok :
    tttLargeFiber72Block3Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentPath_3_ok :
    tttLargeFiber72Block3Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentPath_4_ok :
    tttLargeFiber72Block3Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentPath_5_ok :
    tttLargeFiber72Block3Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentPath_6_ok :
    tttLargeFiber72Block3Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentPath_7_ok :
    tttLargeFiber72Block3Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentPath_8_ok :
    tttLargeFiber72Block3Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentPath_9_ok :
    tttLargeFiber72Block3Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentPath_10_ok :
    tttLargeFiber72Block3Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentPath_11_ok :
    tttLargeFiber72Block3Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentPath_12_ok :
    tttLargeFiber72Block3Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentPath_13_ok :
    tttLargeFiber72Block3Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentPath_14_ok :
    tttLargeFiber72Block3Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber72Block3Chunk2ParentPath_15_ok :
    tttLargeFiber72Block3Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber72Block3Chunk2RowsAudit : Bool :=
  tttLargeFiber72Block3Chunk2RowCheck 0
    && tttLargeFiber72Block3Chunk2RowCheck 1
    && tttLargeFiber72Block3Chunk2RowCheck 2
    && tttLargeFiber72Block3Chunk2RowCheck 3
    && tttLargeFiber72Block3Chunk2RowCheck 4
    && tttLargeFiber72Block3Chunk2RowCheck 5
    && tttLargeFiber72Block3Chunk2RowCheck 6
    && tttLargeFiber72Block3Chunk2RowCheck 7
    && tttLargeFiber72Block3Chunk2RowCheck 8
    && tttLargeFiber72Block3Chunk2RowCheck 9
    && tttLargeFiber72Block3Chunk2RowCheck 10
    && tttLargeFiber72Block3Chunk2RowCheck 11
    && tttLargeFiber72Block3Chunk2RowCheck 12
    && tttLargeFiber72Block3Chunk2RowCheck 13
    && tttLargeFiber72Block3Chunk2RowCheck 14
    && tttLargeFiber72Block3Chunk2RowCheck 15

theorem tttLargeFiber72Block3Chunk2RowsAudit_ok :
    tttLargeFiber72Block3Chunk2RowsAudit = true := by
  simp [tttLargeFiber72Block3Chunk2RowsAudit,
    tttLargeFiber72Block3Chunk2Row_0_ok,
    tttLargeFiber72Block3Chunk2Row_1_ok,
    tttLargeFiber72Block3Chunk2Row_2_ok,
    tttLargeFiber72Block3Chunk2Row_3_ok,
    tttLargeFiber72Block3Chunk2Row_4_ok,
    tttLargeFiber72Block3Chunk2Row_5_ok,
    tttLargeFiber72Block3Chunk2Row_6_ok,
    tttLargeFiber72Block3Chunk2Row_7_ok,
    tttLargeFiber72Block3Chunk2Row_8_ok,
    tttLargeFiber72Block3Chunk2Row_9_ok,
    tttLargeFiber72Block3Chunk2Row_10_ok,
    tttLargeFiber72Block3Chunk2Row_11_ok,
    tttLargeFiber72Block3Chunk2Row_12_ok,
    tttLargeFiber72Block3Chunk2Row_13_ok,
    tttLargeFiber72Block3Chunk2Row_14_ok,
    tttLargeFiber72Block3Chunk2Row_15_ok]

def tttLargeFiber72Block3Chunk2ParentMapAudit : Bool :=
  tttLargeFiber72Block3Chunk2ParentMapCheck 0
    && tttLargeFiber72Block3Chunk2ParentMapCheck 1
    && tttLargeFiber72Block3Chunk2ParentMapCheck 2
    && tttLargeFiber72Block3Chunk2ParentMapCheck 3
    && tttLargeFiber72Block3Chunk2ParentMapCheck 4
    && tttLargeFiber72Block3Chunk2ParentMapCheck 5
    && tttLargeFiber72Block3Chunk2ParentMapCheck 6
    && tttLargeFiber72Block3Chunk2ParentMapCheck 7
    && tttLargeFiber72Block3Chunk2ParentMapCheck 8
    && tttLargeFiber72Block3Chunk2ParentMapCheck 9
    && tttLargeFiber72Block3Chunk2ParentMapCheck 10
    && tttLargeFiber72Block3Chunk2ParentMapCheck 11
    && tttLargeFiber72Block3Chunk2ParentMapCheck 12
    && tttLargeFiber72Block3Chunk2ParentMapCheck 13
    && tttLargeFiber72Block3Chunk2ParentMapCheck 14
    && tttLargeFiber72Block3Chunk2ParentMapCheck 15

theorem tttLargeFiber72Block3Chunk2ParentMapAudit_ok :
    tttLargeFiber72Block3Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber72Block3Chunk2ParentMapAudit,
    tttLargeFiber72Block3Chunk2ParentMap_0_ok,
    tttLargeFiber72Block3Chunk2ParentMap_1_ok,
    tttLargeFiber72Block3Chunk2ParentMap_2_ok,
    tttLargeFiber72Block3Chunk2ParentMap_3_ok,
    tttLargeFiber72Block3Chunk2ParentMap_4_ok,
    tttLargeFiber72Block3Chunk2ParentMap_5_ok,
    tttLargeFiber72Block3Chunk2ParentMap_6_ok,
    tttLargeFiber72Block3Chunk2ParentMap_7_ok,
    tttLargeFiber72Block3Chunk2ParentMap_8_ok,
    tttLargeFiber72Block3Chunk2ParentMap_9_ok,
    tttLargeFiber72Block3Chunk2ParentMap_10_ok,
    tttLargeFiber72Block3Chunk2ParentMap_11_ok,
    tttLargeFiber72Block3Chunk2ParentMap_12_ok,
    tttLargeFiber72Block3Chunk2ParentMap_13_ok,
    tttLargeFiber72Block3Chunk2ParentMap_14_ok,
    tttLargeFiber72Block3Chunk2ParentMap_15_ok]

def tttLargeFiber72Block3Chunk2ParentsAudit : Bool :=
  tttLargeFiber72Block3Chunk2ParentPathCheck 0
    && tttLargeFiber72Block3Chunk2ParentPathCheck 1
    && tttLargeFiber72Block3Chunk2ParentPathCheck 2
    && tttLargeFiber72Block3Chunk2ParentPathCheck 3
    && tttLargeFiber72Block3Chunk2ParentPathCheck 4
    && tttLargeFiber72Block3Chunk2ParentPathCheck 5
    && tttLargeFiber72Block3Chunk2ParentPathCheck 6
    && tttLargeFiber72Block3Chunk2ParentPathCheck 7
    && tttLargeFiber72Block3Chunk2ParentPathCheck 8
    && tttLargeFiber72Block3Chunk2ParentPathCheck 9
    && tttLargeFiber72Block3Chunk2ParentPathCheck 10
    && tttLargeFiber72Block3Chunk2ParentPathCheck 11
    && tttLargeFiber72Block3Chunk2ParentPathCheck 12
    && tttLargeFiber72Block3Chunk2ParentPathCheck 13
    && tttLargeFiber72Block3Chunk2ParentPathCheck 14
    && tttLargeFiber72Block3Chunk2ParentPathCheck 15

theorem tttLargeFiber72Block3Chunk2ParentsAudit_ok :
    tttLargeFiber72Block3Chunk2ParentsAudit = true := by
  simp [tttLargeFiber72Block3Chunk2ParentsAudit,
    tttLargeFiber72Block3Chunk2ParentPath_0_ok,
    tttLargeFiber72Block3Chunk2ParentPath_1_ok,
    tttLargeFiber72Block3Chunk2ParentPath_2_ok,
    tttLargeFiber72Block3Chunk2ParentPath_3_ok,
    tttLargeFiber72Block3Chunk2ParentPath_4_ok,
    tttLargeFiber72Block3Chunk2ParentPath_5_ok,
    tttLargeFiber72Block3Chunk2ParentPath_6_ok,
    tttLargeFiber72Block3Chunk2ParentPath_7_ok,
    tttLargeFiber72Block3Chunk2ParentPath_8_ok,
    tttLargeFiber72Block3Chunk2ParentPath_9_ok,
    tttLargeFiber72Block3Chunk2ParentPath_10_ok,
    tttLargeFiber72Block3Chunk2ParentPath_11_ok,
    tttLargeFiber72Block3Chunk2ParentPath_12_ok,
    tttLargeFiber72Block3Chunk2ParentPath_13_ok,
    tttLargeFiber72Block3Chunk2ParentPath_14_ok,
    tttLargeFiber72Block3Chunk2ParentPath_15_ok]

def tttLargeFiber72Block3Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber72CountsAudit &&
    tttLargeFiber72Block3Chunk2SourcesCheck &&
    tttLargeFiber72Block3Chunk2RowsAudit &&
    tttLargeFiber72Block3Chunk2ParentMapAudit &&
    tttLargeFiber72Block3Chunk2ParentsAudit

theorem tttLargeFiber72Block3Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber72Block3Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber72Block3Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber72CountsAudit_ok,
    tttLargeFiber72Block3Chunk2SourcesCheck_ok,
    tttLargeFiber72Block3Chunk2RowsAudit_ok,
    tttLargeFiber72Block3Chunk2ParentMapAudit_ok,
    tttLargeFiber72Block3Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber72Block3Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
