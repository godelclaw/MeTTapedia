import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber44Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 44, block 3 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber44Block3Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber44Data

def tttLargeFiber44Block3Chunk1Sources : List Nat :=
  [   5120, 5121, 5122, 5123, 5124, 5125, 5126, 5127,
   5128, 5129, 5130, 5131, 5132, 5133, 5134, 5135]

def tttLargeFiber44Row208 : TripleComponentParentRow :=
  tripleRow 5120 5124 151 10 16 151 10 32
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row209 : TripleComponentParentRow :=
  tripleRow 5121 5125 151 10 17 151 10 33
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row210 : TripleComponentParentRow :=
  tripleRow 5122 4948 151 10 18 148 164 180
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber44Row211 : TripleComponentParentRow :=
  tripleRow 5123 4949 151 10 19 148 164 181
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber44Row212 : TripleComponentParentRow :=
  tripleRow 5124 4944 151 10 32 148 164 132
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber44Row213 : TripleComponentParentRow :=
  tripleRow 5125 4945 151 10 33 148 164 133
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber44Row214 : TripleComponentParentRow :=
  tripleRow 5126 4946 151 10 34 148 164 134
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber44Row215 : TripleComponentParentRow :=
  tripleRow 5127 4947 151 10 35 148 164 135
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber44Row216 : TripleComponentParentRow :=
  tripleRow 5128 5132 151 11 24 151 11 40
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row217 : TripleComponentParentRow :=
  tripleRow 5129 5133 151 11 25 151 11 41
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row218 : TripleComponentParentRow :=
  tripleRow 5130 4956 151 11 26 148 165 188
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber44Row219 : TripleComponentParentRow :=
  tripleRow 5131 4957 151 11 27 148 165 189
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber44Row220 : TripleComponentParentRow :=
  tripleRow 5132 4952 151 11 40 148 165 140
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber44Row221 : TripleComponentParentRow :=
  tripleRow 5133 4953 151 11 41 148 165 141
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber44Row222 : TripleComponentParentRow :=
  tripleRow 5134 4954 151 11 42 148 165 142
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber44Row223 : TripleComponentParentRow :=
  tripleRow 5135 4955 151 11 43 148 165 143
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
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

def tttLargeFiber44Block3Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber44Row208
  , tttLargeFiber44Row209
  , tttLargeFiber44Row210
  , tttLargeFiber44Row211
  , tttLargeFiber44Row212
  , tttLargeFiber44Row213
  , tttLargeFiber44Row214
  , tttLargeFiber44Row215
  , tttLargeFiber44Row216
  , tttLargeFiber44Row217
  , tttLargeFiber44Row218
  , tttLargeFiber44Row219
  , tttLargeFiber44Row220
  , tttLargeFiber44Row221
  , tttLargeFiber44Row222
  , tttLargeFiber44Row223
  ]

def tttLargeFiber44Block3Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (4912 <= i) && decide (i < 5168)) ||
    (decide (5456 <= i) && decide (i < 5712))

def tttLargeFiber44Block3Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber44Block3Chunk1ExpectedContains row.source &&
    tttLargeFiber44Block3Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber44Key &&
          chainInputKey tttWord t == tttLargeFiber44Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber44Block3Chunk1SourcesCheck : Bool :=
  (tttLargeFiber44Block3Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber44Block3Chunk1Sources

theorem tttLargeFiber44Block3Chunk1SourcesCheck_ok :
    tttLargeFiber44Block3Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber44Block3Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber44Block3Chunk1RowValid
    (listGetD tttLargeFiber44Block3Chunk1Rows i default)

def tttLargeFiber44Block3Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber44Block3Chunk1Rows i default
  row.parent == tttLargeFiber44ParentOf row.source

def tttLargeFiber44Block3Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber44Block3Chunk1Sources 0 0 == 5120
      && tttLargeFiber44ParentOf 5120 == 5124
      && tttLargeFiber44ParentOf 5124 == 4944
      && tttLargeFiber44ParentOf 4944 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 1 => listGetD tttLargeFiber44Block3Chunk1Sources 1 0 == 5121
      && tttLargeFiber44ParentOf 5121 == 5125
      && tttLargeFiber44ParentOf 5125 == 4945
      && tttLargeFiber44ParentOf 4945 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 2 => listGetD tttLargeFiber44Block3Chunk1Sources 2 0 == 5122
      && tttLargeFiber44ParentOf 5122 == 4948
      && tttLargeFiber44ParentOf 4948 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 3 => listGetD tttLargeFiber44Block3Chunk1Sources 3 0 == 5123
      && tttLargeFiber44ParentOf 5123 == 4949
      && tttLargeFiber44ParentOf 4949 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 4 => listGetD tttLargeFiber44Block3Chunk1Sources 4 0 == 5124
      && tttLargeFiber44ParentOf 5124 == 4944
      && tttLargeFiber44ParentOf 4944 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (2 <= tttLargeFiber44MaxParentDepth)
  | 5 => listGetD tttLargeFiber44Block3Chunk1Sources 5 0 == 5125
      && tttLargeFiber44ParentOf 5125 == 4945
      && tttLargeFiber44ParentOf 4945 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 6 => listGetD tttLargeFiber44Block3Chunk1Sources 6 0 == 5126
      && tttLargeFiber44ParentOf 5126 == 4946
      && tttLargeFiber44ParentOf 4946 == 4914
      && tttLargeFiber44ParentOf 4914 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 7 => listGetD tttLargeFiber44Block3Chunk1Sources 7 0 == 5127
      && tttLargeFiber44ParentOf 5127 == 4947
      && tttLargeFiber44ParentOf 4947 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 8 => listGetD tttLargeFiber44Block3Chunk1Sources 8 0 == 5128
      && tttLargeFiber44ParentOf 5128 == 5132
      && tttLargeFiber44ParentOf 5132 == 4952
      && tttLargeFiber44ParentOf 4952 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 9 => listGetD tttLargeFiber44Block3Chunk1Sources 9 0 == 5129
      && tttLargeFiber44ParentOf 5129 == 5133
      && tttLargeFiber44ParentOf 5133 == 4953
      && tttLargeFiber44ParentOf 4953 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 10 => listGetD tttLargeFiber44Block3Chunk1Sources 10 0 == 5130
      && tttLargeFiber44ParentOf 5130 == 4956
      && tttLargeFiber44ParentOf 4956 == 4924
      && tttLargeFiber44ParentOf 4924 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 11 => listGetD tttLargeFiber44Block3Chunk1Sources 11 0 == 5131
      && tttLargeFiber44ParentOf 5131 == 4957
      && tttLargeFiber44ParentOf 4957 == 4925
      && tttLargeFiber44ParentOf 4925 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 12 => listGetD tttLargeFiber44Block3Chunk1Sources 12 0 == 5132
      && tttLargeFiber44ParentOf 5132 == 4952
      && tttLargeFiber44ParentOf 4952 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 13 => listGetD tttLargeFiber44Block3Chunk1Sources 13 0 == 5133
      && tttLargeFiber44ParentOf 5133 == 4953
      && tttLargeFiber44ParentOf 4953 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 14 => listGetD tttLargeFiber44Block3Chunk1Sources 14 0 == 5134
      && tttLargeFiber44ParentOf 5134 == 4954
      && tttLargeFiber44ParentOf 4954 == 4922
      && tttLargeFiber44ParentOf 4922 == 4914
      && tttLargeFiber44ParentOf 4914 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 15 => listGetD tttLargeFiber44Block3Chunk1Sources 15 0 == 5135
      && tttLargeFiber44ParentOf 5135 == 4955
      && tttLargeFiber44ParentOf 4955 == 4923
      && tttLargeFiber44ParentOf 4923 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | _ => false

theorem tttLargeFiber44Block3Chunk1Row_0_ok :
    tttLargeFiber44Block3Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1Row_1_ok :
    tttLargeFiber44Block3Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1Row_2_ok :
    tttLargeFiber44Block3Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1Row_3_ok :
    tttLargeFiber44Block3Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1Row_4_ok :
    tttLargeFiber44Block3Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1Row_5_ok :
    tttLargeFiber44Block3Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1Row_6_ok :
    tttLargeFiber44Block3Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1Row_7_ok :
    tttLargeFiber44Block3Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1Row_8_ok :
    tttLargeFiber44Block3Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1Row_9_ok :
    tttLargeFiber44Block3Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1Row_10_ok :
    tttLargeFiber44Block3Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1Row_11_ok :
    tttLargeFiber44Block3Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1Row_12_ok :
    tttLargeFiber44Block3Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1Row_13_ok :
    tttLargeFiber44Block3Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1Row_14_ok :
    tttLargeFiber44Block3Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1Row_15_ok :
    tttLargeFiber44Block3Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentMap_0_ok :
    tttLargeFiber44Block3Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentMap_1_ok :
    tttLargeFiber44Block3Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentMap_2_ok :
    tttLargeFiber44Block3Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentMap_3_ok :
    tttLargeFiber44Block3Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentMap_4_ok :
    tttLargeFiber44Block3Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentMap_5_ok :
    tttLargeFiber44Block3Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentMap_6_ok :
    tttLargeFiber44Block3Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentMap_7_ok :
    tttLargeFiber44Block3Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentMap_8_ok :
    tttLargeFiber44Block3Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentMap_9_ok :
    tttLargeFiber44Block3Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentMap_10_ok :
    tttLargeFiber44Block3Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentMap_11_ok :
    tttLargeFiber44Block3Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentMap_12_ok :
    tttLargeFiber44Block3Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentMap_13_ok :
    tttLargeFiber44Block3Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentMap_14_ok :
    tttLargeFiber44Block3Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentMap_15_ok :
    tttLargeFiber44Block3Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentPath_0_ok :
    tttLargeFiber44Block3Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentPath_1_ok :
    tttLargeFiber44Block3Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentPath_2_ok :
    tttLargeFiber44Block3Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentPath_3_ok :
    tttLargeFiber44Block3Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentPath_4_ok :
    tttLargeFiber44Block3Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentPath_5_ok :
    tttLargeFiber44Block3Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentPath_6_ok :
    tttLargeFiber44Block3Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentPath_7_ok :
    tttLargeFiber44Block3Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentPath_8_ok :
    tttLargeFiber44Block3Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentPath_9_ok :
    tttLargeFiber44Block3Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentPath_10_ok :
    tttLargeFiber44Block3Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentPath_11_ok :
    tttLargeFiber44Block3Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentPath_12_ok :
    tttLargeFiber44Block3Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentPath_13_ok :
    tttLargeFiber44Block3Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentPath_14_ok :
    tttLargeFiber44Block3Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber44Block3Chunk1ParentPath_15_ok :
    tttLargeFiber44Block3Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber44Block3Chunk1RowsAudit : Bool :=
  tttLargeFiber44Block3Chunk1RowCheck 0
    && tttLargeFiber44Block3Chunk1RowCheck 1
    && tttLargeFiber44Block3Chunk1RowCheck 2
    && tttLargeFiber44Block3Chunk1RowCheck 3
    && tttLargeFiber44Block3Chunk1RowCheck 4
    && tttLargeFiber44Block3Chunk1RowCheck 5
    && tttLargeFiber44Block3Chunk1RowCheck 6
    && tttLargeFiber44Block3Chunk1RowCheck 7
    && tttLargeFiber44Block3Chunk1RowCheck 8
    && tttLargeFiber44Block3Chunk1RowCheck 9
    && tttLargeFiber44Block3Chunk1RowCheck 10
    && tttLargeFiber44Block3Chunk1RowCheck 11
    && tttLargeFiber44Block3Chunk1RowCheck 12
    && tttLargeFiber44Block3Chunk1RowCheck 13
    && tttLargeFiber44Block3Chunk1RowCheck 14
    && tttLargeFiber44Block3Chunk1RowCheck 15

theorem tttLargeFiber44Block3Chunk1RowsAudit_ok :
    tttLargeFiber44Block3Chunk1RowsAudit = true := by
  simp [tttLargeFiber44Block3Chunk1RowsAudit,
    tttLargeFiber44Block3Chunk1Row_0_ok,
    tttLargeFiber44Block3Chunk1Row_1_ok,
    tttLargeFiber44Block3Chunk1Row_2_ok,
    tttLargeFiber44Block3Chunk1Row_3_ok,
    tttLargeFiber44Block3Chunk1Row_4_ok,
    tttLargeFiber44Block3Chunk1Row_5_ok,
    tttLargeFiber44Block3Chunk1Row_6_ok,
    tttLargeFiber44Block3Chunk1Row_7_ok,
    tttLargeFiber44Block3Chunk1Row_8_ok,
    tttLargeFiber44Block3Chunk1Row_9_ok,
    tttLargeFiber44Block3Chunk1Row_10_ok,
    tttLargeFiber44Block3Chunk1Row_11_ok,
    tttLargeFiber44Block3Chunk1Row_12_ok,
    tttLargeFiber44Block3Chunk1Row_13_ok,
    tttLargeFiber44Block3Chunk1Row_14_ok,
    tttLargeFiber44Block3Chunk1Row_15_ok]

def tttLargeFiber44Block3Chunk1ParentMapAudit : Bool :=
  tttLargeFiber44Block3Chunk1ParentMapCheck 0
    && tttLargeFiber44Block3Chunk1ParentMapCheck 1
    && tttLargeFiber44Block3Chunk1ParentMapCheck 2
    && tttLargeFiber44Block3Chunk1ParentMapCheck 3
    && tttLargeFiber44Block3Chunk1ParentMapCheck 4
    && tttLargeFiber44Block3Chunk1ParentMapCheck 5
    && tttLargeFiber44Block3Chunk1ParentMapCheck 6
    && tttLargeFiber44Block3Chunk1ParentMapCheck 7
    && tttLargeFiber44Block3Chunk1ParentMapCheck 8
    && tttLargeFiber44Block3Chunk1ParentMapCheck 9
    && tttLargeFiber44Block3Chunk1ParentMapCheck 10
    && tttLargeFiber44Block3Chunk1ParentMapCheck 11
    && tttLargeFiber44Block3Chunk1ParentMapCheck 12
    && tttLargeFiber44Block3Chunk1ParentMapCheck 13
    && tttLargeFiber44Block3Chunk1ParentMapCheck 14
    && tttLargeFiber44Block3Chunk1ParentMapCheck 15

theorem tttLargeFiber44Block3Chunk1ParentMapAudit_ok :
    tttLargeFiber44Block3Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber44Block3Chunk1ParentMapAudit,
    tttLargeFiber44Block3Chunk1ParentMap_0_ok,
    tttLargeFiber44Block3Chunk1ParentMap_1_ok,
    tttLargeFiber44Block3Chunk1ParentMap_2_ok,
    tttLargeFiber44Block3Chunk1ParentMap_3_ok,
    tttLargeFiber44Block3Chunk1ParentMap_4_ok,
    tttLargeFiber44Block3Chunk1ParentMap_5_ok,
    tttLargeFiber44Block3Chunk1ParentMap_6_ok,
    tttLargeFiber44Block3Chunk1ParentMap_7_ok,
    tttLargeFiber44Block3Chunk1ParentMap_8_ok,
    tttLargeFiber44Block3Chunk1ParentMap_9_ok,
    tttLargeFiber44Block3Chunk1ParentMap_10_ok,
    tttLargeFiber44Block3Chunk1ParentMap_11_ok,
    tttLargeFiber44Block3Chunk1ParentMap_12_ok,
    tttLargeFiber44Block3Chunk1ParentMap_13_ok,
    tttLargeFiber44Block3Chunk1ParentMap_14_ok,
    tttLargeFiber44Block3Chunk1ParentMap_15_ok]

def tttLargeFiber44Block3Chunk1ParentsAudit : Bool :=
  tttLargeFiber44Block3Chunk1ParentPathCheck 0
    && tttLargeFiber44Block3Chunk1ParentPathCheck 1
    && tttLargeFiber44Block3Chunk1ParentPathCheck 2
    && tttLargeFiber44Block3Chunk1ParentPathCheck 3
    && tttLargeFiber44Block3Chunk1ParentPathCheck 4
    && tttLargeFiber44Block3Chunk1ParentPathCheck 5
    && tttLargeFiber44Block3Chunk1ParentPathCheck 6
    && tttLargeFiber44Block3Chunk1ParentPathCheck 7
    && tttLargeFiber44Block3Chunk1ParentPathCheck 8
    && tttLargeFiber44Block3Chunk1ParentPathCheck 9
    && tttLargeFiber44Block3Chunk1ParentPathCheck 10
    && tttLargeFiber44Block3Chunk1ParentPathCheck 11
    && tttLargeFiber44Block3Chunk1ParentPathCheck 12
    && tttLargeFiber44Block3Chunk1ParentPathCheck 13
    && tttLargeFiber44Block3Chunk1ParentPathCheck 14
    && tttLargeFiber44Block3Chunk1ParentPathCheck 15

theorem tttLargeFiber44Block3Chunk1ParentsAudit_ok :
    tttLargeFiber44Block3Chunk1ParentsAudit = true := by
  simp [tttLargeFiber44Block3Chunk1ParentsAudit,
    tttLargeFiber44Block3Chunk1ParentPath_0_ok,
    tttLargeFiber44Block3Chunk1ParentPath_1_ok,
    tttLargeFiber44Block3Chunk1ParentPath_2_ok,
    tttLargeFiber44Block3Chunk1ParentPath_3_ok,
    tttLargeFiber44Block3Chunk1ParentPath_4_ok,
    tttLargeFiber44Block3Chunk1ParentPath_5_ok,
    tttLargeFiber44Block3Chunk1ParentPath_6_ok,
    tttLargeFiber44Block3Chunk1ParentPath_7_ok,
    tttLargeFiber44Block3Chunk1ParentPath_8_ok,
    tttLargeFiber44Block3Chunk1ParentPath_9_ok,
    tttLargeFiber44Block3Chunk1ParentPath_10_ok,
    tttLargeFiber44Block3Chunk1ParentPath_11_ok,
    tttLargeFiber44Block3Chunk1ParentPath_12_ok,
    tttLargeFiber44Block3Chunk1ParentPath_13_ok,
    tttLargeFiber44Block3Chunk1ParentPath_14_ok,
    tttLargeFiber44Block3Chunk1ParentPath_15_ok]

def tttLargeFiber44Block3Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber44CountsAudit &&
    tttLargeFiber44Block3Chunk1SourcesCheck &&
    tttLargeFiber44Block3Chunk1RowsAudit &&
    tttLargeFiber44Block3Chunk1ParentMapAudit &&
    tttLargeFiber44Block3Chunk1ParentsAudit

theorem tttLargeFiber44Block3Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber44Block3Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber44Block3Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber44CountsAudit_ok,
    tttLargeFiber44Block3Chunk1SourcesCheck_ok,
    tttLargeFiber44Block3Chunk1RowsAudit_ok,
    tttLargeFiber44Block3Chunk1ParentMapAudit_ok,
    tttLargeFiber44Block3Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber44Block3Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
