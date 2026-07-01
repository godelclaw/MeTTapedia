import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber44Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 44, block 2 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber44Block2Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber44Data

def tttLargeFiber44Block2Chunk0Sources : List Nat :=
  [   5040, 5041, 5042, 5043, 5044, 5045, 5046, 5047,
   5048, 5049, 5050, 5051, 5052, 5053, 5054, 5055]

def tttLargeFiber44Row128 : TripleComponentParentRow :=
  tripleRow 5040 5072 150 0 80 150 48 148
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

def tttLargeFiber44Row129 : TripleComponentParentRow :=
  tripleRow 5041 5073 150 0 81 150 48 149
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

def tttLargeFiber44Row130 : TripleComponentParentRow :=
  tripleRow 5042 5040 150 0 82 150 0 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row131 : TripleComponentParentRow :=
  tripleRow 5043 5075 150 0 83 150 48 151
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber44Row132 : TripleComponentParentRow :=
  tripleRow 5044 5076 150 0 100 150 48 164
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber44Row133 : TripleComponentParentRow :=
  tripleRow 5045 5077 150 0 101 150 48 165
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber44Row134 : TripleComponentParentRow :=
  tripleRow 5046 5041 150 0 102 150 0 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber44Row135 : TripleComponentParentRow :=
  tripleRow 5047 5040 150 0 103 150 0 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber44Row136 : TripleComponentParentRow :=
  tripleRow 5048 5080 150 1 88 150 49 156
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

def tttLargeFiber44Row137 : TripleComponentParentRow :=
  tripleRow 5049 5081 150 1 89 150 49 157
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

def tttLargeFiber44Row138 : TripleComponentParentRow :=
  tripleRow 5050 5048 150 1 90 150 1 88
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row139 : TripleComponentParentRow :=
  tripleRow 5051 5083 150 1 91 150 49 159
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber44Row140 : TripleComponentParentRow :=
  tripleRow 5052 5084 150 1 108 150 49 172
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber44Row141 : TripleComponentParentRow :=
  tripleRow 5053 5085 150 1 109 150 49 173
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber44Row142 : TripleComponentParentRow :=
  tripleRow 5054 5049 150 1 110 150 1 89
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber44Row143 : TripleComponentParentRow :=
  tripleRow 5055 5048 150 1 111 150 1 88
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber44Block2Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber44Row128
  , tttLargeFiber44Row129
  , tttLargeFiber44Row130
  , tttLargeFiber44Row131
  , tttLargeFiber44Row132
  , tttLargeFiber44Row133
  , tttLargeFiber44Row134
  , tttLargeFiber44Row135
  , tttLargeFiber44Row136
  , tttLargeFiber44Row137
  , tttLargeFiber44Row138
  , tttLargeFiber44Row139
  , tttLargeFiber44Row140
  , tttLargeFiber44Row141
  , tttLargeFiber44Row142
  , tttLargeFiber44Row143
  ]

def tttLargeFiber44Block2Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (4912 <= i) && decide (i < 5168)) ||
    (decide (5456 <= i) && decide (i < 5712))

def tttLargeFiber44Block2Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber44Block2Chunk0ExpectedContains row.source &&
    tttLargeFiber44Block2Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber44Key &&
          chainInputKey tttWord t == tttLargeFiber44Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber44Block2Chunk0SourcesCheck : Bool :=
  (tttLargeFiber44Block2Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber44Block2Chunk0Sources

theorem tttLargeFiber44Block2Chunk0SourcesCheck_ok :
    tttLargeFiber44Block2Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber44Block2Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber44Block2Chunk0RowValid
    (listGetD tttLargeFiber44Block2Chunk0Rows i default)

def tttLargeFiber44Block2Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber44Block2Chunk0Rows i default
  row.parent == tttLargeFiber44ParentOf row.source

def tttLargeFiber44Block2Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber44Block2Chunk0Sources 0 0 == 5040
      && tttLargeFiber44ParentOf 5040 == 5072
      && tttLargeFiber44ParentOf 5072 == 4976
      && tttLargeFiber44ParentOf 4976 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 1 => listGetD tttLargeFiber44Block2Chunk0Sources 1 0 == 5041
      && tttLargeFiber44ParentOf 5041 == 5073
      && tttLargeFiber44ParentOf 5073 == 4977
      && tttLargeFiber44ParentOf 4977 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 2 => listGetD tttLargeFiber44Block2Chunk0Sources 2 0 == 5042
      && tttLargeFiber44ParentOf 5042 == 5040
      && tttLargeFiber44ParentOf 5040 == 5072
      && tttLargeFiber44ParentOf 5072 == 4976
      && tttLargeFiber44ParentOf 4976 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 3 => listGetD tttLargeFiber44Block2Chunk0Sources 3 0 == 5043
      && tttLargeFiber44ParentOf 5043 == 5075
      && tttLargeFiber44ParentOf 5075 == 4979
      && tttLargeFiber44ParentOf 4979 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 4 => listGetD tttLargeFiber44Block2Chunk0Sources 4 0 == 5044
      && tttLargeFiber44ParentOf 5044 == 5076
      && tttLargeFiber44ParentOf 5076 == 4980
      && tttLargeFiber44ParentOf 4980 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 5 => listGetD tttLargeFiber44Block2Chunk0Sources 5 0 == 5045
      && tttLargeFiber44ParentOf 5045 == 5077
      && tttLargeFiber44ParentOf 5077 == 4981
      && tttLargeFiber44ParentOf 4981 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 6 => listGetD tttLargeFiber44Block2Chunk0Sources 6 0 == 5046
      && tttLargeFiber44ParentOf 5046 == 5041
      && tttLargeFiber44ParentOf 5041 == 5073
      && tttLargeFiber44ParentOf 5073 == 4977
      && tttLargeFiber44ParentOf 4977 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 7 => listGetD tttLargeFiber44Block2Chunk0Sources 7 0 == 5047
      && tttLargeFiber44ParentOf 5047 == 5040
      && tttLargeFiber44ParentOf 5040 == 5072
      && tttLargeFiber44ParentOf 5072 == 4976
      && tttLargeFiber44ParentOf 4976 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 8 => listGetD tttLargeFiber44Block2Chunk0Sources 8 0 == 5048
      && tttLargeFiber44ParentOf 5048 == 5080
      && tttLargeFiber44ParentOf 5080 == 4984
      && tttLargeFiber44ParentOf 4984 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 9 => listGetD tttLargeFiber44Block2Chunk0Sources 9 0 == 5049
      && tttLargeFiber44ParentOf 5049 == 5081
      && tttLargeFiber44ParentOf 5081 == 4985
      && tttLargeFiber44ParentOf 4985 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 10 => listGetD tttLargeFiber44Block2Chunk0Sources 10 0 == 5050
      && tttLargeFiber44ParentOf 5050 == 5048
      && tttLargeFiber44ParentOf 5048 == 5080
      && tttLargeFiber44ParentOf 5080 == 4984
      && tttLargeFiber44ParentOf 4984 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 11 => listGetD tttLargeFiber44Block2Chunk0Sources 11 0 == 5051
      && tttLargeFiber44ParentOf 5051 == 5083
      && tttLargeFiber44ParentOf 5083 == 4987
      && tttLargeFiber44ParentOf 4987 == 4923
      && tttLargeFiber44ParentOf 4923 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 12 => listGetD tttLargeFiber44Block2Chunk0Sources 12 0 == 5052
      && tttLargeFiber44ParentOf 5052 == 5084
      && tttLargeFiber44ParentOf 5084 == 4988
      && tttLargeFiber44ParentOf 4988 == 4924
      && tttLargeFiber44ParentOf 4924 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 13 => listGetD tttLargeFiber44Block2Chunk0Sources 13 0 == 5053
      && tttLargeFiber44ParentOf 5053 == 5085
      && tttLargeFiber44ParentOf 5085 == 4989
      && tttLargeFiber44ParentOf 4989 == 4925
      && tttLargeFiber44ParentOf 4925 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (6 <= tttLargeFiber44MaxParentDepth)
  | 14 => listGetD tttLargeFiber44Block2Chunk0Sources 14 0 == 5054
      && tttLargeFiber44ParentOf 5054 == 5049
      && tttLargeFiber44ParentOf 5049 == 5081
      && tttLargeFiber44ParentOf 5081 == 4985
      && tttLargeFiber44ParentOf 4985 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (6 <= tttLargeFiber44MaxParentDepth)
  | 15 => listGetD tttLargeFiber44Block2Chunk0Sources 15 0 == 5055
      && tttLargeFiber44ParentOf 5055 == 5048
      && tttLargeFiber44ParentOf 5048 == 5080
      && tttLargeFiber44ParentOf 5080 == 4984
      && tttLargeFiber44ParentOf 4984 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | _ => false

theorem tttLargeFiber44Block2Chunk0Row_0_ok :
    tttLargeFiber44Block2Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0Row_1_ok :
    tttLargeFiber44Block2Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0Row_2_ok :
    tttLargeFiber44Block2Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0Row_3_ok :
    tttLargeFiber44Block2Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0Row_4_ok :
    tttLargeFiber44Block2Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0Row_5_ok :
    tttLargeFiber44Block2Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0Row_6_ok :
    tttLargeFiber44Block2Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0Row_7_ok :
    tttLargeFiber44Block2Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0Row_8_ok :
    tttLargeFiber44Block2Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0Row_9_ok :
    tttLargeFiber44Block2Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0Row_10_ok :
    tttLargeFiber44Block2Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0Row_11_ok :
    tttLargeFiber44Block2Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0Row_12_ok :
    tttLargeFiber44Block2Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0Row_13_ok :
    tttLargeFiber44Block2Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0Row_14_ok :
    tttLargeFiber44Block2Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0Row_15_ok :
    tttLargeFiber44Block2Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentMap_0_ok :
    tttLargeFiber44Block2Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentMap_1_ok :
    tttLargeFiber44Block2Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentMap_2_ok :
    tttLargeFiber44Block2Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentMap_3_ok :
    tttLargeFiber44Block2Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentMap_4_ok :
    tttLargeFiber44Block2Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentMap_5_ok :
    tttLargeFiber44Block2Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentMap_6_ok :
    tttLargeFiber44Block2Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentMap_7_ok :
    tttLargeFiber44Block2Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentMap_8_ok :
    tttLargeFiber44Block2Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentMap_9_ok :
    tttLargeFiber44Block2Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentMap_10_ok :
    tttLargeFiber44Block2Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentMap_11_ok :
    tttLargeFiber44Block2Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentMap_12_ok :
    tttLargeFiber44Block2Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentMap_13_ok :
    tttLargeFiber44Block2Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentMap_14_ok :
    tttLargeFiber44Block2Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentMap_15_ok :
    tttLargeFiber44Block2Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentPath_0_ok :
    tttLargeFiber44Block2Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentPath_1_ok :
    tttLargeFiber44Block2Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentPath_2_ok :
    tttLargeFiber44Block2Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentPath_3_ok :
    tttLargeFiber44Block2Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentPath_4_ok :
    tttLargeFiber44Block2Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentPath_5_ok :
    tttLargeFiber44Block2Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentPath_6_ok :
    tttLargeFiber44Block2Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentPath_7_ok :
    tttLargeFiber44Block2Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentPath_8_ok :
    tttLargeFiber44Block2Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentPath_9_ok :
    tttLargeFiber44Block2Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentPath_10_ok :
    tttLargeFiber44Block2Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentPath_11_ok :
    tttLargeFiber44Block2Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentPath_12_ok :
    tttLargeFiber44Block2Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentPath_13_ok :
    tttLargeFiber44Block2Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentPath_14_ok :
    tttLargeFiber44Block2Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber44Block2Chunk0ParentPath_15_ok :
    tttLargeFiber44Block2Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber44Block2Chunk0RowsAudit : Bool :=
  tttLargeFiber44Block2Chunk0RowCheck 0
    && tttLargeFiber44Block2Chunk0RowCheck 1
    && tttLargeFiber44Block2Chunk0RowCheck 2
    && tttLargeFiber44Block2Chunk0RowCheck 3
    && tttLargeFiber44Block2Chunk0RowCheck 4
    && tttLargeFiber44Block2Chunk0RowCheck 5
    && tttLargeFiber44Block2Chunk0RowCheck 6
    && tttLargeFiber44Block2Chunk0RowCheck 7
    && tttLargeFiber44Block2Chunk0RowCheck 8
    && tttLargeFiber44Block2Chunk0RowCheck 9
    && tttLargeFiber44Block2Chunk0RowCheck 10
    && tttLargeFiber44Block2Chunk0RowCheck 11
    && tttLargeFiber44Block2Chunk0RowCheck 12
    && tttLargeFiber44Block2Chunk0RowCheck 13
    && tttLargeFiber44Block2Chunk0RowCheck 14
    && tttLargeFiber44Block2Chunk0RowCheck 15

theorem tttLargeFiber44Block2Chunk0RowsAudit_ok :
    tttLargeFiber44Block2Chunk0RowsAudit = true := by
  simp [tttLargeFiber44Block2Chunk0RowsAudit,
    tttLargeFiber44Block2Chunk0Row_0_ok,
    tttLargeFiber44Block2Chunk0Row_1_ok,
    tttLargeFiber44Block2Chunk0Row_2_ok,
    tttLargeFiber44Block2Chunk0Row_3_ok,
    tttLargeFiber44Block2Chunk0Row_4_ok,
    tttLargeFiber44Block2Chunk0Row_5_ok,
    tttLargeFiber44Block2Chunk0Row_6_ok,
    tttLargeFiber44Block2Chunk0Row_7_ok,
    tttLargeFiber44Block2Chunk0Row_8_ok,
    tttLargeFiber44Block2Chunk0Row_9_ok,
    tttLargeFiber44Block2Chunk0Row_10_ok,
    tttLargeFiber44Block2Chunk0Row_11_ok,
    tttLargeFiber44Block2Chunk0Row_12_ok,
    tttLargeFiber44Block2Chunk0Row_13_ok,
    tttLargeFiber44Block2Chunk0Row_14_ok,
    tttLargeFiber44Block2Chunk0Row_15_ok]

def tttLargeFiber44Block2Chunk0ParentMapAudit : Bool :=
  tttLargeFiber44Block2Chunk0ParentMapCheck 0
    && tttLargeFiber44Block2Chunk0ParentMapCheck 1
    && tttLargeFiber44Block2Chunk0ParentMapCheck 2
    && tttLargeFiber44Block2Chunk0ParentMapCheck 3
    && tttLargeFiber44Block2Chunk0ParentMapCheck 4
    && tttLargeFiber44Block2Chunk0ParentMapCheck 5
    && tttLargeFiber44Block2Chunk0ParentMapCheck 6
    && tttLargeFiber44Block2Chunk0ParentMapCheck 7
    && tttLargeFiber44Block2Chunk0ParentMapCheck 8
    && tttLargeFiber44Block2Chunk0ParentMapCheck 9
    && tttLargeFiber44Block2Chunk0ParentMapCheck 10
    && tttLargeFiber44Block2Chunk0ParentMapCheck 11
    && tttLargeFiber44Block2Chunk0ParentMapCheck 12
    && tttLargeFiber44Block2Chunk0ParentMapCheck 13
    && tttLargeFiber44Block2Chunk0ParentMapCheck 14
    && tttLargeFiber44Block2Chunk0ParentMapCheck 15

theorem tttLargeFiber44Block2Chunk0ParentMapAudit_ok :
    tttLargeFiber44Block2Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber44Block2Chunk0ParentMapAudit,
    tttLargeFiber44Block2Chunk0ParentMap_0_ok,
    tttLargeFiber44Block2Chunk0ParentMap_1_ok,
    tttLargeFiber44Block2Chunk0ParentMap_2_ok,
    tttLargeFiber44Block2Chunk0ParentMap_3_ok,
    tttLargeFiber44Block2Chunk0ParentMap_4_ok,
    tttLargeFiber44Block2Chunk0ParentMap_5_ok,
    tttLargeFiber44Block2Chunk0ParentMap_6_ok,
    tttLargeFiber44Block2Chunk0ParentMap_7_ok,
    tttLargeFiber44Block2Chunk0ParentMap_8_ok,
    tttLargeFiber44Block2Chunk0ParentMap_9_ok,
    tttLargeFiber44Block2Chunk0ParentMap_10_ok,
    tttLargeFiber44Block2Chunk0ParentMap_11_ok,
    tttLargeFiber44Block2Chunk0ParentMap_12_ok,
    tttLargeFiber44Block2Chunk0ParentMap_13_ok,
    tttLargeFiber44Block2Chunk0ParentMap_14_ok,
    tttLargeFiber44Block2Chunk0ParentMap_15_ok]

def tttLargeFiber44Block2Chunk0ParentsAudit : Bool :=
  tttLargeFiber44Block2Chunk0ParentPathCheck 0
    && tttLargeFiber44Block2Chunk0ParentPathCheck 1
    && tttLargeFiber44Block2Chunk0ParentPathCheck 2
    && tttLargeFiber44Block2Chunk0ParentPathCheck 3
    && tttLargeFiber44Block2Chunk0ParentPathCheck 4
    && tttLargeFiber44Block2Chunk0ParentPathCheck 5
    && tttLargeFiber44Block2Chunk0ParentPathCheck 6
    && tttLargeFiber44Block2Chunk0ParentPathCheck 7
    && tttLargeFiber44Block2Chunk0ParentPathCheck 8
    && tttLargeFiber44Block2Chunk0ParentPathCheck 9
    && tttLargeFiber44Block2Chunk0ParentPathCheck 10
    && tttLargeFiber44Block2Chunk0ParentPathCheck 11
    && tttLargeFiber44Block2Chunk0ParentPathCheck 12
    && tttLargeFiber44Block2Chunk0ParentPathCheck 13
    && tttLargeFiber44Block2Chunk0ParentPathCheck 14
    && tttLargeFiber44Block2Chunk0ParentPathCheck 15

theorem tttLargeFiber44Block2Chunk0ParentsAudit_ok :
    tttLargeFiber44Block2Chunk0ParentsAudit = true := by
  simp [tttLargeFiber44Block2Chunk0ParentsAudit,
    tttLargeFiber44Block2Chunk0ParentPath_0_ok,
    tttLargeFiber44Block2Chunk0ParentPath_1_ok,
    tttLargeFiber44Block2Chunk0ParentPath_2_ok,
    tttLargeFiber44Block2Chunk0ParentPath_3_ok,
    tttLargeFiber44Block2Chunk0ParentPath_4_ok,
    tttLargeFiber44Block2Chunk0ParentPath_5_ok,
    tttLargeFiber44Block2Chunk0ParentPath_6_ok,
    tttLargeFiber44Block2Chunk0ParentPath_7_ok,
    tttLargeFiber44Block2Chunk0ParentPath_8_ok,
    tttLargeFiber44Block2Chunk0ParentPath_9_ok,
    tttLargeFiber44Block2Chunk0ParentPath_10_ok,
    tttLargeFiber44Block2Chunk0ParentPath_11_ok,
    tttLargeFiber44Block2Chunk0ParentPath_12_ok,
    tttLargeFiber44Block2Chunk0ParentPath_13_ok,
    tttLargeFiber44Block2Chunk0ParentPath_14_ok,
    tttLargeFiber44Block2Chunk0ParentPath_15_ok]

def tttLargeFiber44Block2Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber44CountsAudit &&
    tttLargeFiber44Block2Chunk0SourcesCheck &&
    tttLargeFiber44Block2Chunk0RowsAudit &&
    tttLargeFiber44Block2Chunk0ParentMapAudit &&
    tttLargeFiber44Block2Chunk0ParentsAudit

theorem tttLargeFiber44Block2Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber44Block2Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber44Block2Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber44CountsAudit_ok,
    tttLargeFiber44Block2Chunk0SourcesCheck_ok,
    tttLargeFiber44Block2Chunk0RowsAudit_ok,
    tttLargeFiber44Block2Chunk0ParentMapAudit_ok,
    tttLargeFiber44Block2Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber44Block2Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
