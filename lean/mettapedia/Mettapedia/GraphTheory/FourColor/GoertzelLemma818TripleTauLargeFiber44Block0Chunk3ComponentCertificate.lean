import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber44Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 44, block 0 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber44Block0Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber44Data

def tttLargeFiber44Block0Chunk3Sources : List Nat :=
  [   4960, 4961, 4962, 4963, 4964, 4965, 4966, 4967,
   4968, 4969, 4970, 4971, 4972, 4973, 4974, 4975]

def tttLargeFiber44Row48 : TripleComponentParentRow :=
  tripleRow 4960 4944 148 166 64 148 164 132
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

def tttLargeFiber44Row49 : TripleComponentParentRow :=
  tripleRow 4961 4945 148 166 65 148 164 133
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

def tttLargeFiber44Row50 : TripleComponentParentRow :=
  tripleRow 4962 4960 148 166 66 148 166 64
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row51 : TripleComponentParentRow :=
  tripleRow 4963 4947 148 166 67 148 164 135
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber44Row52 : TripleComponentParentRow :=
  tripleRow 4964 4948 148 166 116 148 164 180
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Row53 : TripleComponentParentRow :=
  tripleRow 4965 4949 148 166 117 148 164 181
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber44Row54 : TripleComponentParentRow :=
  tripleRow 4966 4961 148 166 118 148 166 65
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber44Row55 : TripleComponentParentRow :=
  tripleRow 4967 4960 148 166 119 148 166 64
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber44Row56 : TripleComponentParentRow :=
  tripleRow 4968 4952 148 167 72 148 165 140
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

def tttLargeFiber44Row57 : TripleComponentParentRow :=
  tripleRow 4969 4953 148 167 73 148 165 141
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

def tttLargeFiber44Row58 : TripleComponentParentRow :=
  tripleRow 4970 4938 148 167 74 148 151 10
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber44Row59 : TripleComponentParentRow :=
  tripleRow 4971 4939 148 167 75 148 151 11
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber44Row60 : TripleComponentParentRow :=
  tripleRow 4972 4940 148 167 124 148 151 56
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
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

def tttLargeFiber44Row61 : TripleComponentParentRow :=
  tripleRow 4973 4941 148 167 125 148 151 57
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
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

def tttLargeFiber44Row62 : TripleComponentParentRow :=
  tripleRow 4974 4972 148 167 126 148 167 124
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row63 : TripleComponentParentRow :=
  tripleRow 4975 4943 148 167 127 148 151 59
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Block0Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber44Row48
  , tttLargeFiber44Row49
  , tttLargeFiber44Row50
  , tttLargeFiber44Row51
  , tttLargeFiber44Row52
  , tttLargeFiber44Row53
  , tttLargeFiber44Row54
  , tttLargeFiber44Row55
  , tttLargeFiber44Row56
  , tttLargeFiber44Row57
  , tttLargeFiber44Row58
  , tttLargeFiber44Row59
  , tttLargeFiber44Row60
  , tttLargeFiber44Row61
  , tttLargeFiber44Row62
  , tttLargeFiber44Row63
  ]

def tttLargeFiber44Block0Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (4912 <= i) && decide (i < 5168)) ||
    (decide (5456 <= i) && decide (i < 5712))

def tttLargeFiber44Block0Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber44Block0Chunk3ExpectedContains row.source &&
    tttLargeFiber44Block0Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber44Key &&
          chainInputKey tttWord t == tttLargeFiber44Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber44Block0Chunk3SourcesCheck : Bool :=
  (tttLargeFiber44Block0Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber44Block0Chunk3Sources

theorem tttLargeFiber44Block0Chunk3SourcesCheck_ok :
    tttLargeFiber44Block0Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber44Block0Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber44Block0Chunk3RowValid
    (listGetD tttLargeFiber44Block0Chunk3Rows i default)

def tttLargeFiber44Block0Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber44Block0Chunk3Rows i default
  row.parent == tttLargeFiber44ParentOf row.source

def tttLargeFiber44Block0Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber44Block0Chunk3Sources 0 0 == 4960
      && tttLargeFiber44ParentOf 4960 == 4944
      && tttLargeFiber44ParentOf 4944 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (2 <= tttLargeFiber44MaxParentDepth)
  | 1 => listGetD tttLargeFiber44Block0Chunk3Sources 1 0 == 4961
      && tttLargeFiber44ParentOf 4961 == 4945
      && tttLargeFiber44ParentOf 4945 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 2 => listGetD tttLargeFiber44Block0Chunk3Sources 2 0 == 4962
      && tttLargeFiber44ParentOf 4962 == 4960
      && tttLargeFiber44ParentOf 4960 == 4944
      && tttLargeFiber44ParentOf 4944 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 3 => listGetD tttLargeFiber44Block0Chunk3Sources 3 0 == 4963
      && tttLargeFiber44ParentOf 4963 == 4947
      && tttLargeFiber44ParentOf 4947 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 4 => listGetD tttLargeFiber44Block0Chunk3Sources 4 0 == 4964
      && tttLargeFiber44ParentOf 4964 == 4948
      && tttLargeFiber44ParentOf 4948 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 5 => listGetD tttLargeFiber44Block0Chunk3Sources 5 0 == 4965
      && tttLargeFiber44ParentOf 4965 == 4949
      && tttLargeFiber44ParentOf 4949 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 6 => listGetD tttLargeFiber44Block0Chunk3Sources 6 0 == 4966
      && tttLargeFiber44ParentOf 4966 == 4961
      && tttLargeFiber44ParentOf 4961 == 4945
      && tttLargeFiber44ParentOf 4945 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 7 => listGetD tttLargeFiber44Block0Chunk3Sources 7 0 == 4967
      && tttLargeFiber44ParentOf 4967 == 4960
      && tttLargeFiber44ParentOf 4960 == 4944
      && tttLargeFiber44ParentOf 4944 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 8 => listGetD tttLargeFiber44Block0Chunk3Sources 8 0 == 4968
      && tttLargeFiber44ParentOf 4968 == 4952
      && tttLargeFiber44ParentOf 4952 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 9 => listGetD tttLargeFiber44Block0Chunk3Sources 9 0 == 4969
      && tttLargeFiber44ParentOf 4969 == 4953
      && tttLargeFiber44ParentOf 4953 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 10 => listGetD tttLargeFiber44Block0Chunk3Sources 10 0 == 4970
      && tttLargeFiber44ParentOf 4970 == 4938
      && tttLargeFiber44ParentOf 4938 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 11 => listGetD tttLargeFiber44Block0Chunk3Sources 11 0 == 4971
      && tttLargeFiber44ParentOf 4971 == 4939
      && tttLargeFiber44ParentOf 4939 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 12 => listGetD tttLargeFiber44Block0Chunk3Sources 12 0 == 4972
      && tttLargeFiber44ParentOf 4972 == 4940
      && tttLargeFiber44ParentOf 4940 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (2 <= tttLargeFiber44MaxParentDepth)
  | 13 => listGetD tttLargeFiber44Block0Chunk3Sources 13 0 == 4973
      && tttLargeFiber44ParentOf 4973 == 4941
      && tttLargeFiber44ParentOf 4941 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 14 => listGetD tttLargeFiber44Block0Chunk3Sources 14 0 == 4974
      && tttLargeFiber44ParentOf 4974 == 4972
      && tttLargeFiber44ParentOf 4972 == 4940
      && tttLargeFiber44ParentOf 4940 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 15 => listGetD tttLargeFiber44Block0Chunk3Sources 15 0 == 4975
      && tttLargeFiber44ParentOf 4975 == 4943
      && tttLargeFiber44ParentOf 4943 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | _ => false

theorem tttLargeFiber44Block0Chunk3Row_0_ok :
    tttLargeFiber44Block0Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3Row_1_ok :
    tttLargeFiber44Block0Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3Row_2_ok :
    tttLargeFiber44Block0Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3Row_3_ok :
    tttLargeFiber44Block0Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3Row_4_ok :
    tttLargeFiber44Block0Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3Row_5_ok :
    tttLargeFiber44Block0Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3Row_6_ok :
    tttLargeFiber44Block0Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3Row_7_ok :
    tttLargeFiber44Block0Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3Row_8_ok :
    tttLargeFiber44Block0Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3Row_9_ok :
    tttLargeFiber44Block0Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3Row_10_ok :
    tttLargeFiber44Block0Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3Row_11_ok :
    tttLargeFiber44Block0Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3Row_12_ok :
    tttLargeFiber44Block0Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3Row_13_ok :
    tttLargeFiber44Block0Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3Row_14_ok :
    tttLargeFiber44Block0Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3Row_15_ok :
    tttLargeFiber44Block0Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentMap_0_ok :
    tttLargeFiber44Block0Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentMap_1_ok :
    tttLargeFiber44Block0Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentMap_2_ok :
    tttLargeFiber44Block0Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentMap_3_ok :
    tttLargeFiber44Block0Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentMap_4_ok :
    tttLargeFiber44Block0Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentMap_5_ok :
    tttLargeFiber44Block0Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentMap_6_ok :
    tttLargeFiber44Block0Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentMap_7_ok :
    tttLargeFiber44Block0Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentMap_8_ok :
    tttLargeFiber44Block0Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentMap_9_ok :
    tttLargeFiber44Block0Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentMap_10_ok :
    tttLargeFiber44Block0Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentMap_11_ok :
    tttLargeFiber44Block0Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentMap_12_ok :
    tttLargeFiber44Block0Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentMap_13_ok :
    tttLargeFiber44Block0Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentMap_14_ok :
    tttLargeFiber44Block0Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentMap_15_ok :
    tttLargeFiber44Block0Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentPath_0_ok :
    tttLargeFiber44Block0Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentPath_1_ok :
    tttLargeFiber44Block0Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentPath_2_ok :
    tttLargeFiber44Block0Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentPath_3_ok :
    tttLargeFiber44Block0Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentPath_4_ok :
    tttLargeFiber44Block0Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentPath_5_ok :
    tttLargeFiber44Block0Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentPath_6_ok :
    tttLargeFiber44Block0Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentPath_7_ok :
    tttLargeFiber44Block0Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentPath_8_ok :
    tttLargeFiber44Block0Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentPath_9_ok :
    tttLargeFiber44Block0Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentPath_10_ok :
    tttLargeFiber44Block0Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentPath_11_ok :
    tttLargeFiber44Block0Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentPath_12_ok :
    tttLargeFiber44Block0Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentPath_13_ok :
    tttLargeFiber44Block0Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentPath_14_ok :
    tttLargeFiber44Block0Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber44Block0Chunk3ParentPath_15_ok :
    tttLargeFiber44Block0Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber44Block0Chunk3RowsAudit : Bool :=
  tttLargeFiber44Block0Chunk3RowCheck 0
    && tttLargeFiber44Block0Chunk3RowCheck 1
    && tttLargeFiber44Block0Chunk3RowCheck 2
    && tttLargeFiber44Block0Chunk3RowCheck 3
    && tttLargeFiber44Block0Chunk3RowCheck 4
    && tttLargeFiber44Block0Chunk3RowCheck 5
    && tttLargeFiber44Block0Chunk3RowCheck 6
    && tttLargeFiber44Block0Chunk3RowCheck 7
    && tttLargeFiber44Block0Chunk3RowCheck 8
    && tttLargeFiber44Block0Chunk3RowCheck 9
    && tttLargeFiber44Block0Chunk3RowCheck 10
    && tttLargeFiber44Block0Chunk3RowCheck 11
    && tttLargeFiber44Block0Chunk3RowCheck 12
    && tttLargeFiber44Block0Chunk3RowCheck 13
    && tttLargeFiber44Block0Chunk3RowCheck 14
    && tttLargeFiber44Block0Chunk3RowCheck 15

theorem tttLargeFiber44Block0Chunk3RowsAudit_ok :
    tttLargeFiber44Block0Chunk3RowsAudit = true := by
  simp [tttLargeFiber44Block0Chunk3RowsAudit,
    tttLargeFiber44Block0Chunk3Row_0_ok,
    tttLargeFiber44Block0Chunk3Row_1_ok,
    tttLargeFiber44Block0Chunk3Row_2_ok,
    tttLargeFiber44Block0Chunk3Row_3_ok,
    tttLargeFiber44Block0Chunk3Row_4_ok,
    tttLargeFiber44Block0Chunk3Row_5_ok,
    tttLargeFiber44Block0Chunk3Row_6_ok,
    tttLargeFiber44Block0Chunk3Row_7_ok,
    tttLargeFiber44Block0Chunk3Row_8_ok,
    tttLargeFiber44Block0Chunk3Row_9_ok,
    tttLargeFiber44Block0Chunk3Row_10_ok,
    tttLargeFiber44Block0Chunk3Row_11_ok,
    tttLargeFiber44Block0Chunk3Row_12_ok,
    tttLargeFiber44Block0Chunk3Row_13_ok,
    tttLargeFiber44Block0Chunk3Row_14_ok,
    tttLargeFiber44Block0Chunk3Row_15_ok]

def tttLargeFiber44Block0Chunk3ParentMapAudit : Bool :=
  tttLargeFiber44Block0Chunk3ParentMapCheck 0
    && tttLargeFiber44Block0Chunk3ParentMapCheck 1
    && tttLargeFiber44Block0Chunk3ParentMapCheck 2
    && tttLargeFiber44Block0Chunk3ParentMapCheck 3
    && tttLargeFiber44Block0Chunk3ParentMapCheck 4
    && tttLargeFiber44Block0Chunk3ParentMapCheck 5
    && tttLargeFiber44Block0Chunk3ParentMapCheck 6
    && tttLargeFiber44Block0Chunk3ParentMapCheck 7
    && tttLargeFiber44Block0Chunk3ParentMapCheck 8
    && tttLargeFiber44Block0Chunk3ParentMapCheck 9
    && tttLargeFiber44Block0Chunk3ParentMapCheck 10
    && tttLargeFiber44Block0Chunk3ParentMapCheck 11
    && tttLargeFiber44Block0Chunk3ParentMapCheck 12
    && tttLargeFiber44Block0Chunk3ParentMapCheck 13
    && tttLargeFiber44Block0Chunk3ParentMapCheck 14
    && tttLargeFiber44Block0Chunk3ParentMapCheck 15

theorem tttLargeFiber44Block0Chunk3ParentMapAudit_ok :
    tttLargeFiber44Block0Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber44Block0Chunk3ParentMapAudit,
    tttLargeFiber44Block0Chunk3ParentMap_0_ok,
    tttLargeFiber44Block0Chunk3ParentMap_1_ok,
    tttLargeFiber44Block0Chunk3ParentMap_2_ok,
    tttLargeFiber44Block0Chunk3ParentMap_3_ok,
    tttLargeFiber44Block0Chunk3ParentMap_4_ok,
    tttLargeFiber44Block0Chunk3ParentMap_5_ok,
    tttLargeFiber44Block0Chunk3ParentMap_6_ok,
    tttLargeFiber44Block0Chunk3ParentMap_7_ok,
    tttLargeFiber44Block0Chunk3ParentMap_8_ok,
    tttLargeFiber44Block0Chunk3ParentMap_9_ok,
    tttLargeFiber44Block0Chunk3ParentMap_10_ok,
    tttLargeFiber44Block0Chunk3ParentMap_11_ok,
    tttLargeFiber44Block0Chunk3ParentMap_12_ok,
    tttLargeFiber44Block0Chunk3ParentMap_13_ok,
    tttLargeFiber44Block0Chunk3ParentMap_14_ok,
    tttLargeFiber44Block0Chunk3ParentMap_15_ok]

def tttLargeFiber44Block0Chunk3ParentsAudit : Bool :=
  tttLargeFiber44Block0Chunk3ParentPathCheck 0
    && tttLargeFiber44Block0Chunk3ParentPathCheck 1
    && tttLargeFiber44Block0Chunk3ParentPathCheck 2
    && tttLargeFiber44Block0Chunk3ParentPathCheck 3
    && tttLargeFiber44Block0Chunk3ParentPathCheck 4
    && tttLargeFiber44Block0Chunk3ParentPathCheck 5
    && tttLargeFiber44Block0Chunk3ParentPathCheck 6
    && tttLargeFiber44Block0Chunk3ParentPathCheck 7
    && tttLargeFiber44Block0Chunk3ParentPathCheck 8
    && tttLargeFiber44Block0Chunk3ParentPathCheck 9
    && tttLargeFiber44Block0Chunk3ParentPathCheck 10
    && tttLargeFiber44Block0Chunk3ParentPathCheck 11
    && tttLargeFiber44Block0Chunk3ParentPathCheck 12
    && tttLargeFiber44Block0Chunk3ParentPathCheck 13
    && tttLargeFiber44Block0Chunk3ParentPathCheck 14
    && tttLargeFiber44Block0Chunk3ParentPathCheck 15

theorem tttLargeFiber44Block0Chunk3ParentsAudit_ok :
    tttLargeFiber44Block0Chunk3ParentsAudit = true := by
  simp [tttLargeFiber44Block0Chunk3ParentsAudit,
    tttLargeFiber44Block0Chunk3ParentPath_0_ok,
    tttLargeFiber44Block0Chunk3ParentPath_1_ok,
    tttLargeFiber44Block0Chunk3ParentPath_2_ok,
    tttLargeFiber44Block0Chunk3ParentPath_3_ok,
    tttLargeFiber44Block0Chunk3ParentPath_4_ok,
    tttLargeFiber44Block0Chunk3ParentPath_5_ok,
    tttLargeFiber44Block0Chunk3ParentPath_6_ok,
    tttLargeFiber44Block0Chunk3ParentPath_7_ok,
    tttLargeFiber44Block0Chunk3ParentPath_8_ok,
    tttLargeFiber44Block0Chunk3ParentPath_9_ok,
    tttLargeFiber44Block0Chunk3ParentPath_10_ok,
    tttLargeFiber44Block0Chunk3ParentPath_11_ok,
    tttLargeFiber44Block0Chunk3ParentPath_12_ok,
    tttLargeFiber44Block0Chunk3ParentPath_13_ok,
    tttLargeFiber44Block0Chunk3ParentPath_14_ok,
    tttLargeFiber44Block0Chunk3ParentPath_15_ok]

def tttLargeFiber44Block0Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber44CountsAudit &&
    tttLargeFiber44Block0Chunk3SourcesCheck &&
    tttLargeFiber44Block0Chunk3RowsAudit &&
    tttLargeFiber44Block0Chunk3ParentMapAudit &&
    tttLargeFiber44Block0Chunk3ParentsAudit

theorem tttLargeFiber44Block0Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber44Block0Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber44Block0Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber44CountsAudit_ok,
    tttLargeFiber44Block0Chunk3SourcesCheck_ok,
    tttLargeFiber44Block0Chunk3RowsAudit_ok,
    tttLargeFiber44Block0Chunk3ParentMapAudit_ok,
    tttLargeFiber44Block0Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber44Block0Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
