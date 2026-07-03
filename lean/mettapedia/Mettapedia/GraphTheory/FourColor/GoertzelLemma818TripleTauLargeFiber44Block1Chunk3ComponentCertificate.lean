import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber44Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 44, block 1 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber44Block1Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber44Data

def tttLargeFiber44Block1Chunk3Sources : List Nat :=
  [   5024, 5025, 5026, 5027, 5028, 5029, 5030, 5031,
   5032, 5033, 5034, 5035, 5036, 5037, 5038, 5039]

def tttLargeFiber44Row112 : TripleComponentParentRow :=
  tripleRow 5024 4960 149 174 64 148 166 64
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row113 : TripleComponentParentRow :=
  tripleRow 5025 4961 149 174 65 148 166 65
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row114 : TripleComponentParentRow :=
  tripleRow 5026 4962 149 174 66 148 166 66
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row115 : TripleComponentParentRow :=
  tripleRow 5027 4963 149 174 67 148 166 67
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row116 : TripleComponentParentRow :=
  tripleRow 5028 4964 149 174 116 148 166 116
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row117 : TripleComponentParentRow :=
  tripleRow 5029 4965 149 174 117 148 166 117
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row118 : TripleComponentParentRow :=
  tripleRow 5030 4966 149 174 118 148 166 118
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row119 : TripleComponentParentRow :=
  tripleRow 5031 4967 149 174 119 148 166 119
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row120 : TripleComponentParentRow :=
  tripleRow 5032 4968 149 175 72 148 167 72
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row121 : TripleComponentParentRow :=
  tripleRow 5033 4969 149 175 73 148 167 73
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row122 : TripleComponentParentRow :=
  tripleRow 5034 4970 149 175 74 148 167 74
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row123 : TripleComponentParentRow :=
  tripleRow 5035 4971 149 175 75 148 167 75
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row124 : TripleComponentParentRow :=
  tripleRow 5036 4972 149 175 124 148 167 124
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row125 : TripleComponentParentRow :=
  tripleRow 5037 4973 149 175 125 148 167 125
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row126 : TripleComponentParentRow :=
  tripleRow 5038 4974 149 175 126 148 167 126
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Row127 : TripleComponentParentRow :=
  tripleRow 5039 4975 149 175 127 148 167 127
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber44Block1Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber44Row112
  , tttLargeFiber44Row113
  , tttLargeFiber44Row114
  , tttLargeFiber44Row115
  , tttLargeFiber44Row116
  , tttLargeFiber44Row117
  , tttLargeFiber44Row118
  , tttLargeFiber44Row119
  , tttLargeFiber44Row120
  , tttLargeFiber44Row121
  , tttLargeFiber44Row122
  , tttLargeFiber44Row123
  , tttLargeFiber44Row124
  , tttLargeFiber44Row125
  , tttLargeFiber44Row126
  , tttLargeFiber44Row127
  ]

def tttLargeFiber44Block1Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (4912 <= i) && decide (i < 5168)) ||
    (decide (5456 <= i) && decide (i < 5712))

def tttLargeFiber44Block1Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber44Block1Chunk3ExpectedContains row.source &&
    tttLargeFiber44Block1Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber44Key &&
          chainInputKey tttWord t == tttLargeFiber44Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber44Block1Chunk3SourcesCheck : Bool :=
  (tttLargeFiber44Block1Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber44Block1Chunk3Sources

theorem tttLargeFiber44Block1Chunk3SourcesCheck_ok :
    tttLargeFiber44Block1Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber44Block1Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber44Block1Chunk3RowValid
    (listGetD tttLargeFiber44Block1Chunk3Rows i default)

def tttLargeFiber44Block1Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber44Block1Chunk3Rows i default
  row.parent == tttLargeFiber44ParentOf row.source

def tttLargeFiber44Block1Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber44Block1Chunk3Sources 0 0 == 5024
      && tttLargeFiber44ParentOf 5024 == 4960
      && tttLargeFiber44ParentOf 4960 == 4944
      && tttLargeFiber44ParentOf 4944 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 1 => listGetD tttLargeFiber44Block1Chunk3Sources 1 0 == 5025
      && tttLargeFiber44ParentOf 5025 == 4961
      && tttLargeFiber44ParentOf 4961 == 4945
      && tttLargeFiber44ParentOf 4945 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 2 => listGetD tttLargeFiber44Block1Chunk3Sources 2 0 == 5026
      && tttLargeFiber44ParentOf 5026 == 4962
      && tttLargeFiber44ParentOf 4962 == 4960
      && tttLargeFiber44ParentOf 4960 == 4944
      && tttLargeFiber44ParentOf 4944 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 3 => listGetD tttLargeFiber44Block1Chunk3Sources 3 0 == 5027
      && tttLargeFiber44ParentOf 5027 == 4963
      && tttLargeFiber44ParentOf 4963 == 4947
      && tttLargeFiber44ParentOf 4947 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 4 => listGetD tttLargeFiber44Block1Chunk3Sources 4 0 == 5028
      && tttLargeFiber44ParentOf 5028 == 4964
      && tttLargeFiber44ParentOf 4964 == 4948
      && tttLargeFiber44ParentOf 4948 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 5 => listGetD tttLargeFiber44Block1Chunk3Sources 5 0 == 5029
      && tttLargeFiber44ParentOf 5029 == 4965
      && tttLargeFiber44ParentOf 4965 == 4949
      && tttLargeFiber44ParentOf 4949 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 6 => listGetD tttLargeFiber44Block1Chunk3Sources 6 0 == 5030
      && tttLargeFiber44ParentOf 5030 == 4966
      && tttLargeFiber44ParentOf 4966 == 4961
      && tttLargeFiber44ParentOf 4961 == 4945
      && tttLargeFiber44ParentOf 4945 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 7 => listGetD tttLargeFiber44Block1Chunk3Sources 7 0 == 5031
      && tttLargeFiber44ParentOf 5031 == 4967
      && tttLargeFiber44ParentOf 4967 == 4960
      && tttLargeFiber44ParentOf 4960 == 4944
      && tttLargeFiber44ParentOf 4944 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 8 => listGetD tttLargeFiber44Block1Chunk3Sources 8 0 == 5032
      && tttLargeFiber44ParentOf 5032 == 4968
      && tttLargeFiber44ParentOf 4968 == 4952
      && tttLargeFiber44ParentOf 4952 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 9 => listGetD tttLargeFiber44Block1Chunk3Sources 9 0 == 5033
      && tttLargeFiber44ParentOf 5033 == 4969
      && tttLargeFiber44ParentOf 4969 == 4953
      && tttLargeFiber44ParentOf 4953 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 10 => listGetD tttLargeFiber44Block1Chunk3Sources 10 0 == 5034
      && tttLargeFiber44ParentOf 5034 == 4970
      && tttLargeFiber44ParentOf 4970 == 4938
      && tttLargeFiber44ParentOf 4938 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 11 => listGetD tttLargeFiber44Block1Chunk3Sources 11 0 == 5035
      && tttLargeFiber44ParentOf 5035 == 4971
      && tttLargeFiber44ParentOf 4971 == 4939
      && tttLargeFiber44ParentOf 4939 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 12 => listGetD tttLargeFiber44Block1Chunk3Sources 12 0 == 5036
      && tttLargeFiber44ParentOf 5036 == 4972
      && tttLargeFiber44ParentOf 4972 == 4940
      && tttLargeFiber44ParentOf 4940 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 13 => listGetD tttLargeFiber44Block1Chunk3Sources 13 0 == 5037
      && tttLargeFiber44ParentOf 5037 == 4973
      && tttLargeFiber44ParentOf 4973 == 4941
      && tttLargeFiber44ParentOf 4941 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 14 => listGetD tttLargeFiber44Block1Chunk3Sources 14 0 == 5038
      && tttLargeFiber44ParentOf 5038 == 4974
      && tttLargeFiber44ParentOf 4974 == 4972
      && tttLargeFiber44ParentOf 4972 == 4940
      && tttLargeFiber44ParentOf 4940 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 15 => listGetD tttLargeFiber44Block1Chunk3Sources 15 0 == 5039
      && tttLargeFiber44ParentOf 5039 == 4975
      && tttLargeFiber44ParentOf 4975 == 4943
      && tttLargeFiber44ParentOf 4943 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | _ => false

theorem tttLargeFiber44Block1Chunk3Row_0_ok :
    tttLargeFiber44Block1Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3Row_1_ok :
    tttLargeFiber44Block1Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3Row_2_ok :
    tttLargeFiber44Block1Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3Row_3_ok :
    tttLargeFiber44Block1Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3Row_4_ok :
    tttLargeFiber44Block1Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3Row_5_ok :
    tttLargeFiber44Block1Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3Row_6_ok :
    tttLargeFiber44Block1Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3Row_7_ok :
    tttLargeFiber44Block1Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3Row_8_ok :
    tttLargeFiber44Block1Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3Row_9_ok :
    tttLargeFiber44Block1Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3Row_10_ok :
    tttLargeFiber44Block1Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3Row_11_ok :
    tttLargeFiber44Block1Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3Row_12_ok :
    tttLargeFiber44Block1Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3Row_13_ok :
    tttLargeFiber44Block1Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3Row_14_ok :
    tttLargeFiber44Block1Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3Row_15_ok :
    tttLargeFiber44Block1Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentMap_0_ok :
    tttLargeFiber44Block1Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentMap_1_ok :
    tttLargeFiber44Block1Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentMap_2_ok :
    tttLargeFiber44Block1Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentMap_3_ok :
    tttLargeFiber44Block1Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentMap_4_ok :
    tttLargeFiber44Block1Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentMap_5_ok :
    tttLargeFiber44Block1Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentMap_6_ok :
    tttLargeFiber44Block1Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentMap_7_ok :
    tttLargeFiber44Block1Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentMap_8_ok :
    tttLargeFiber44Block1Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentMap_9_ok :
    tttLargeFiber44Block1Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentMap_10_ok :
    tttLargeFiber44Block1Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentMap_11_ok :
    tttLargeFiber44Block1Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentMap_12_ok :
    tttLargeFiber44Block1Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentMap_13_ok :
    tttLargeFiber44Block1Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentMap_14_ok :
    tttLargeFiber44Block1Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentMap_15_ok :
    tttLargeFiber44Block1Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentPath_0_ok :
    tttLargeFiber44Block1Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentPath_1_ok :
    tttLargeFiber44Block1Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentPath_2_ok :
    tttLargeFiber44Block1Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentPath_3_ok :
    tttLargeFiber44Block1Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentPath_4_ok :
    tttLargeFiber44Block1Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentPath_5_ok :
    tttLargeFiber44Block1Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentPath_6_ok :
    tttLargeFiber44Block1Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentPath_7_ok :
    tttLargeFiber44Block1Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentPath_8_ok :
    tttLargeFiber44Block1Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentPath_9_ok :
    tttLargeFiber44Block1Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentPath_10_ok :
    tttLargeFiber44Block1Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentPath_11_ok :
    tttLargeFiber44Block1Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentPath_12_ok :
    tttLargeFiber44Block1Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentPath_13_ok :
    tttLargeFiber44Block1Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentPath_14_ok :
    tttLargeFiber44Block1Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber44Block1Chunk3ParentPath_15_ok :
    tttLargeFiber44Block1Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber44Block1Chunk3RowsAudit : Bool :=
  tttLargeFiber44Block1Chunk3RowCheck 0
    && tttLargeFiber44Block1Chunk3RowCheck 1
    && tttLargeFiber44Block1Chunk3RowCheck 2
    && tttLargeFiber44Block1Chunk3RowCheck 3
    && tttLargeFiber44Block1Chunk3RowCheck 4
    && tttLargeFiber44Block1Chunk3RowCheck 5
    && tttLargeFiber44Block1Chunk3RowCheck 6
    && tttLargeFiber44Block1Chunk3RowCheck 7
    && tttLargeFiber44Block1Chunk3RowCheck 8
    && tttLargeFiber44Block1Chunk3RowCheck 9
    && tttLargeFiber44Block1Chunk3RowCheck 10
    && tttLargeFiber44Block1Chunk3RowCheck 11
    && tttLargeFiber44Block1Chunk3RowCheck 12
    && tttLargeFiber44Block1Chunk3RowCheck 13
    && tttLargeFiber44Block1Chunk3RowCheck 14
    && tttLargeFiber44Block1Chunk3RowCheck 15

theorem tttLargeFiber44Block1Chunk3RowsAudit_ok :
    tttLargeFiber44Block1Chunk3RowsAudit = true := by
  simp [tttLargeFiber44Block1Chunk3RowsAudit,
    tttLargeFiber44Block1Chunk3Row_0_ok,
    tttLargeFiber44Block1Chunk3Row_1_ok,
    tttLargeFiber44Block1Chunk3Row_2_ok,
    tttLargeFiber44Block1Chunk3Row_3_ok,
    tttLargeFiber44Block1Chunk3Row_4_ok,
    tttLargeFiber44Block1Chunk3Row_5_ok,
    tttLargeFiber44Block1Chunk3Row_6_ok,
    tttLargeFiber44Block1Chunk3Row_7_ok,
    tttLargeFiber44Block1Chunk3Row_8_ok,
    tttLargeFiber44Block1Chunk3Row_9_ok,
    tttLargeFiber44Block1Chunk3Row_10_ok,
    tttLargeFiber44Block1Chunk3Row_11_ok,
    tttLargeFiber44Block1Chunk3Row_12_ok,
    tttLargeFiber44Block1Chunk3Row_13_ok,
    tttLargeFiber44Block1Chunk3Row_14_ok,
    tttLargeFiber44Block1Chunk3Row_15_ok]

def tttLargeFiber44Block1Chunk3ParentMapAudit : Bool :=
  tttLargeFiber44Block1Chunk3ParentMapCheck 0
    && tttLargeFiber44Block1Chunk3ParentMapCheck 1
    && tttLargeFiber44Block1Chunk3ParentMapCheck 2
    && tttLargeFiber44Block1Chunk3ParentMapCheck 3
    && tttLargeFiber44Block1Chunk3ParentMapCheck 4
    && tttLargeFiber44Block1Chunk3ParentMapCheck 5
    && tttLargeFiber44Block1Chunk3ParentMapCheck 6
    && tttLargeFiber44Block1Chunk3ParentMapCheck 7
    && tttLargeFiber44Block1Chunk3ParentMapCheck 8
    && tttLargeFiber44Block1Chunk3ParentMapCheck 9
    && tttLargeFiber44Block1Chunk3ParentMapCheck 10
    && tttLargeFiber44Block1Chunk3ParentMapCheck 11
    && tttLargeFiber44Block1Chunk3ParentMapCheck 12
    && tttLargeFiber44Block1Chunk3ParentMapCheck 13
    && tttLargeFiber44Block1Chunk3ParentMapCheck 14
    && tttLargeFiber44Block1Chunk3ParentMapCheck 15

theorem tttLargeFiber44Block1Chunk3ParentMapAudit_ok :
    tttLargeFiber44Block1Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber44Block1Chunk3ParentMapAudit,
    tttLargeFiber44Block1Chunk3ParentMap_0_ok,
    tttLargeFiber44Block1Chunk3ParentMap_1_ok,
    tttLargeFiber44Block1Chunk3ParentMap_2_ok,
    tttLargeFiber44Block1Chunk3ParentMap_3_ok,
    tttLargeFiber44Block1Chunk3ParentMap_4_ok,
    tttLargeFiber44Block1Chunk3ParentMap_5_ok,
    tttLargeFiber44Block1Chunk3ParentMap_6_ok,
    tttLargeFiber44Block1Chunk3ParentMap_7_ok,
    tttLargeFiber44Block1Chunk3ParentMap_8_ok,
    tttLargeFiber44Block1Chunk3ParentMap_9_ok,
    tttLargeFiber44Block1Chunk3ParentMap_10_ok,
    tttLargeFiber44Block1Chunk3ParentMap_11_ok,
    tttLargeFiber44Block1Chunk3ParentMap_12_ok,
    tttLargeFiber44Block1Chunk3ParentMap_13_ok,
    tttLargeFiber44Block1Chunk3ParentMap_14_ok,
    tttLargeFiber44Block1Chunk3ParentMap_15_ok]

def tttLargeFiber44Block1Chunk3ParentsAudit : Bool :=
  tttLargeFiber44Block1Chunk3ParentPathCheck 0
    && tttLargeFiber44Block1Chunk3ParentPathCheck 1
    && tttLargeFiber44Block1Chunk3ParentPathCheck 2
    && tttLargeFiber44Block1Chunk3ParentPathCheck 3
    && tttLargeFiber44Block1Chunk3ParentPathCheck 4
    && tttLargeFiber44Block1Chunk3ParentPathCheck 5
    && tttLargeFiber44Block1Chunk3ParentPathCheck 6
    && tttLargeFiber44Block1Chunk3ParentPathCheck 7
    && tttLargeFiber44Block1Chunk3ParentPathCheck 8
    && tttLargeFiber44Block1Chunk3ParentPathCheck 9
    && tttLargeFiber44Block1Chunk3ParentPathCheck 10
    && tttLargeFiber44Block1Chunk3ParentPathCheck 11
    && tttLargeFiber44Block1Chunk3ParentPathCheck 12
    && tttLargeFiber44Block1Chunk3ParentPathCheck 13
    && tttLargeFiber44Block1Chunk3ParentPathCheck 14
    && tttLargeFiber44Block1Chunk3ParentPathCheck 15

theorem tttLargeFiber44Block1Chunk3ParentsAudit_ok :
    tttLargeFiber44Block1Chunk3ParentsAudit = true := by
  simp [tttLargeFiber44Block1Chunk3ParentsAudit,
    tttLargeFiber44Block1Chunk3ParentPath_0_ok,
    tttLargeFiber44Block1Chunk3ParentPath_1_ok,
    tttLargeFiber44Block1Chunk3ParentPath_2_ok,
    tttLargeFiber44Block1Chunk3ParentPath_3_ok,
    tttLargeFiber44Block1Chunk3ParentPath_4_ok,
    tttLargeFiber44Block1Chunk3ParentPath_5_ok,
    tttLargeFiber44Block1Chunk3ParentPath_6_ok,
    tttLargeFiber44Block1Chunk3ParentPath_7_ok,
    tttLargeFiber44Block1Chunk3ParentPath_8_ok,
    tttLargeFiber44Block1Chunk3ParentPath_9_ok,
    tttLargeFiber44Block1Chunk3ParentPath_10_ok,
    tttLargeFiber44Block1Chunk3ParentPath_11_ok,
    tttLargeFiber44Block1Chunk3ParentPath_12_ok,
    tttLargeFiber44Block1Chunk3ParentPath_13_ok,
    tttLargeFiber44Block1Chunk3ParentPath_14_ok,
    tttLargeFiber44Block1Chunk3ParentPath_15_ok]

def tttLargeFiber44Block1Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber44CountsAudit &&
    tttLargeFiber44Block1Chunk3SourcesCheck &&
    tttLargeFiber44Block1Chunk3RowsAudit &&
    tttLargeFiber44Block1Chunk3ParentMapAudit &&
    tttLargeFiber44Block1Chunk3ParentsAudit

theorem tttLargeFiber44Block1Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber44Block1Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber44Block1Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber44CountsAudit_ok,
    tttLargeFiber44Block1Chunk3SourcesCheck_ok,
    tttLargeFiber44Block1Chunk3RowsAudit_ok,
    tttLargeFiber44Block1Chunk3ParentMapAudit_ok,
    tttLargeFiber44Block1Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber44Block1Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
