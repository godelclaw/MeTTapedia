import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber44Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 44, block 2 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber44Block2Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber44Data

def tttLargeFiber44Block2Chunk1Sources : List Nat :=
  [   5056, 5057, 5058, 5059, 5060, 5061, 5062, 5063,
   5064, 5065, 5066, 5067, 5068, 5069, 5070, 5071]

def tttLargeFiber44Row144 : TripleComponentParentRow :=
  tripleRow 5056 5060 150 2 16 150 2 32
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row145 : TripleComponentParentRow :=
  tripleRow 5057 5061 150 2 17 150 2 33
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row146 : TripleComponentParentRow :=
  tripleRow 5058 5012 150 2 18 149 172 180
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber44Row147 : TripleComponentParentRow :=
  tripleRow 5059 5013 150 2 19 149 172 181
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber44Row148 : TripleComponentParentRow :=
  tripleRow 5060 5008 150 2 32 149 172 132
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber44Row149 : TripleComponentParentRow :=
  tripleRow 5061 5009 150 2 33 149 172 133
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber44Row150 : TripleComponentParentRow :=
  tripleRow 5062 5010 150 2 34 149 172 134
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber44Row151 : TripleComponentParentRow :=
  tripleRow 5063 5011 150 2 35 149 172 135
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber44Row152 : TripleComponentParentRow :=
  tripleRow 5064 5068 150 3 24 150 3 40
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row153 : TripleComponentParentRow :=
  tripleRow 5065 5069 150 3 25 150 3 41
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row154 : TripleComponentParentRow :=
  tripleRow 5066 5020 150 3 26 149 173 188
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber44Row155 : TripleComponentParentRow :=
  tripleRow 5067 5021 150 3 27 149 173 189
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
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

def tttLargeFiber44Row156 : TripleComponentParentRow :=
  tripleRow 5068 5016 150 3 40 149 173 140
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber44Row157 : TripleComponentParentRow :=
  tripleRow 5069 5017 150 3 41 149 173 141
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber44Row158 : TripleComponentParentRow :=
  tripleRow 5070 5018 150 3 42 149 173 142
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber44Row159 : TripleComponentParentRow :=
  tripleRow 5071 5019 150 3 43 149 173 143
    (chainMove LColor.r LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber44Block2Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber44Row144
  , tttLargeFiber44Row145
  , tttLargeFiber44Row146
  , tttLargeFiber44Row147
  , tttLargeFiber44Row148
  , tttLargeFiber44Row149
  , tttLargeFiber44Row150
  , tttLargeFiber44Row151
  , tttLargeFiber44Row152
  , tttLargeFiber44Row153
  , tttLargeFiber44Row154
  , tttLargeFiber44Row155
  , tttLargeFiber44Row156
  , tttLargeFiber44Row157
  , tttLargeFiber44Row158
  , tttLargeFiber44Row159
  ]

def tttLargeFiber44Block2Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (4912 <= i) && decide (i < 5168)) ||
    (decide (5456 <= i) && decide (i < 5712))

def tttLargeFiber44Block2Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber44Block2Chunk1ExpectedContains row.source &&
    tttLargeFiber44Block2Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber44Key &&
          chainInputKey tttWord t == tttLargeFiber44Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber44Block2Chunk1SourcesCheck : Bool :=
  (tttLargeFiber44Block2Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber44Block2Chunk1Sources

theorem tttLargeFiber44Block2Chunk1SourcesCheck_ok :
    tttLargeFiber44Block2Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber44Block2Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber44Block2Chunk1RowValid
    (listGetD tttLargeFiber44Block2Chunk1Rows i default)

def tttLargeFiber44Block2Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber44Block2Chunk1Rows i default
  row.parent == tttLargeFiber44ParentOf row.source

def tttLargeFiber44Block2Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber44Block2Chunk1Sources 0 0 == 5056
      && tttLargeFiber44ParentOf 5056 == 5060
      && tttLargeFiber44ParentOf 5060 == 5008
      && tttLargeFiber44ParentOf 5008 == 4944
      && tttLargeFiber44ParentOf 4944 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 1 => listGetD tttLargeFiber44Block2Chunk1Sources 1 0 == 5057
      && tttLargeFiber44ParentOf 5057 == 5061
      && tttLargeFiber44ParentOf 5061 == 5009
      && tttLargeFiber44ParentOf 5009 == 4945
      && tttLargeFiber44ParentOf 4945 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 2 => listGetD tttLargeFiber44Block2Chunk1Sources 2 0 == 5058
      && tttLargeFiber44ParentOf 5058 == 5012
      && tttLargeFiber44ParentOf 5012 == 4948
      && tttLargeFiber44ParentOf 4948 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 3 => listGetD tttLargeFiber44Block2Chunk1Sources 3 0 == 5059
      && tttLargeFiber44ParentOf 5059 == 5013
      && tttLargeFiber44ParentOf 5013 == 4949
      && tttLargeFiber44ParentOf 4949 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 4 => listGetD tttLargeFiber44Block2Chunk1Sources 4 0 == 5060
      && tttLargeFiber44ParentOf 5060 == 5008
      && tttLargeFiber44ParentOf 5008 == 4944
      && tttLargeFiber44ParentOf 4944 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 5 => listGetD tttLargeFiber44Block2Chunk1Sources 5 0 == 5061
      && tttLargeFiber44ParentOf 5061 == 5009
      && tttLargeFiber44ParentOf 5009 == 4945
      && tttLargeFiber44ParentOf 4945 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 6 => listGetD tttLargeFiber44Block2Chunk1Sources 6 0 == 5062
      && tttLargeFiber44ParentOf 5062 == 5010
      && tttLargeFiber44ParentOf 5010 == 4946
      && tttLargeFiber44ParentOf 4946 == 4914
      && tttLargeFiber44ParentOf 4914 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 7 => listGetD tttLargeFiber44Block2Chunk1Sources 7 0 == 5063
      && tttLargeFiber44ParentOf 5063 == 5011
      && tttLargeFiber44ParentOf 5011 == 4947
      && tttLargeFiber44ParentOf 4947 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 8 => listGetD tttLargeFiber44Block2Chunk1Sources 8 0 == 5064
      && tttLargeFiber44ParentOf 5064 == 5068
      && tttLargeFiber44ParentOf 5068 == 5016
      && tttLargeFiber44ParentOf 5016 == 4952
      && tttLargeFiber44ParentOf 4952 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 9 => listGetD tttLargeFiber44Block2Chunk1Sources 9 0 == 5065
      && tttLargeFiber44ParentOf 5065 == 5069
      && tttLargeFiber44ParentOf 5069 == 5017
      && tttLargeFiber44ParentOf 5017 == 4953
      && tttLargeFiber44ParentOf 4953 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (6 <= tttLargeFiber44MaxParentDepth)
  | 10 => listGetD tttLargeFiber44Block2Chunk1Sources 10 0 == 5066
      && tttLargeFiber44ParentOf 5066 == 5020
      && tttLargeFiber44ParentOf 5020 == 4956
      && tttLargeFiber44ParentOf 4956 == 4924
      && tttLargeFiber44ParentOf 4924 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 11 => listGetD tttLargeFiber44Block2Chunk1Sources 11 0 == 5067
      && tttLargeFiber44ParentOf 5067 == 5021
      && tttLargeFiber44ParentOf 5021 == 4957
      && tttLargeFiber44ParentOf 4957 == 4925
      && tttLargeFiber44ParentOf 4925 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (6 <= tttLargeFiber44MaxParentDepth)
  | 12 => listGetD tttLargeFiber44Block2Chunk1Sources 12 0 == 5068
      && tttLargeFiber44ParentOf 5068 == 5016
      && tttLargeFiber44ParentOf 5016 == 4952
      && tttLargeFiber44ParentOf 4952 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 13 => listGetD tttLargeFiber44Block2Chunk1Sources 13 0 == 5069
      && tttLargeFiber44ParentOf 5069 == 5017
      && tttLargeFiber44ParentOf 5017 == 4953
      && tttLargeFiber44ParentOf 4953 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 14 => listGetD tttLargeFiber44Block2Chunk1Sources 14 0 == 5070
      && tttLargeFiber44ParentOf 5070 == 5018
      && tttLargeFiber44ParentOf 5018 == 4954
      && tttLargeFiber44ParentOf 4954 == 4922
      && tttLargeFiber44ParentOf 4922 == 4914
      && tttLargeFiber44ParentOf 4914 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (6 <= tttLargeFiber44MaxParentDepth)
  | 15 => listGetD tttLargeFiber44Block2Chunk1Sources 15 0 == 5071
      && tttLargeFiber44ParentOf 5071 == 5019
      && tttLargeFiber44ParentOf 5019 == 4955
      && tttLargeFiber44ParentOf 4955 == 4923
      && tttLargeFiber44ParentOf 4923 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | _ => false

theorem tttLargeFiber44Block2Chunk1Row_0_ok :
    tttLargeFiber44Block2Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1Row_1_ok :
    tttLargeFiber44Block2Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1Row_2_ok :
    tttLargeFiber44Block2Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1Row_3_ok :
    tttLargeFiber44Block2Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1Row_4_ok :
    tttLargeFiber44Block2Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1Row_5_ok :
    tttLargeFiber44Block2Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1Row_6_ok :
    tttLargeFiber44Block2Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1Row_7_ok :
    tttLargeFiber44Block2Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1Row_8_ok :
    tttLargeFiber44Block2Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1Row_9_ok :
    tttLargeFiber44Block2Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1Row_10_ok :
    tttLargeFiber44Block2Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1Row_11_ok :
    tttLargeFiber44Block2Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1Row_12_ok :
    tttLargeFiber44Block2Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1Row_13_ok :
    tttLargeFiber44Block2Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1Row_14_ok :
    tttLargeFiber44Block2Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1Row_15_ok :
    tttLargeFiber44Block2Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentMap_0_ok :
    tttLargeFiber44Block2Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentMap_1_ok :
    tttLargeFiber44Block2Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentMap_2_ok :
    tttLargeFiber44Block2Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentMap_3_ok :
    tttLargeFiber44Block2Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentMap_4_ok :
    tttLargeFiber44Block2Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentMap_5_ok :
    tttLargeFiber44Block2Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentMap_6_ok :
    tttLargeFiber44Block2Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentMap_7_ok :
    tttLargeFiber44Block2Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentMap_8_ok :
    tttLargeFiber44Block2Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentMap_9_ok :
    tttLargeFiber44Block2Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentMap_10_ok :
    tttLargeFiber44Block2Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentMap_11_ok :
    tttLargeFiber44Block2Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentMap_12_ok :
    tttLargeFiber44Block2Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentMap_13_ok :
    tttLargeFiber44Block2Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentMap_14_ok :
    tttLargeFiber44Block2Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentMap_15_ok :
    tttLargeFiber44Block2Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentPath_0_ok :
    tttLargeFiber44Block2Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentPath_1_ok :
    tttLargeFiber44Block2Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentPath_2_ok :
    tttLargeFiber44Block2Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentPath_3_ok :
    tttLargeFiber44Block2Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentPath_4_ok :
    tttLargeFiber44Block2Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentPath_5_ok :
    tttLargeFiber44Block2Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentPath_6_ok :
    tttLargeFiber44Block2Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentPath_7_ok :
    tttLargeFiber44Block2Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentPath_8_ok :
    tttLargeFiber44Block2Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentPath_9_ok :
    tttLargeFiber44Block2Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentPath_10_ok :
    tttLargeFiber44Block2Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentPath_11_ok :
    tttLargeFiber44Block2Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentPath_12_ok :
    tttLargeFiber44Block2Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentPath_13_ok :
    tttLargeFiber44Block2Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentPath_14_ok :
    tttLargeFiber44Block2Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber44Block2Chunk1ParentPath_15_ok :
    tttLargeFiber44Block2Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber44Block2Chunk1RowsAudit : Bool :=
  tttLargeFiber44Block2Chunk1RowCheck 0
    && tttLargeFiber44Block2Chunk1RowCheck 1
    && tttLargeFiber44Block2Chunk1RowCheck 2
    && tttLargeFiber44Block2Chunk1RowCheck 3
    && tttLargeFiber44Block2Chunk1RowCheck 4
    && tttLargeFiber44Block2Chunk1RowCheck 5
    && tttLargeFiber44Block2Chunk1RowCheck 6
    && tttLargeFiber44Block2Chunk1RowCheck 7
    && tttLargeFiber44Block2Chunk1RowCheck 8
    && tttLargeFiber44Block2Chunk1RowCheck 9
    && tttLargeFiber44Block2Chunk1RowCheck 10
    && tttLargeFiber44Block2Chunk1RowCheck 11
    && tttLargeFiber44Block2Chunk1RowCheck 12
    && tttLargeFiber44Block2Chunk1RowCheck 13
    && tttLargeFiber44Block2Chunk1RowCheck 14
    && tttLargeFiber44Block2Chunk1RowCheck 15

theorem tttLargeFiber44Block2Chunk1RowsAudit_ok :
    tttLargeFiber44Block2Chunk1RowsAudit = true := by
  simp [tttLargeFiber44Block2Chunk1RowsAudit,
    tttLargeFiber44Block2Chunk1Row_0_ok,
    tttLargeFiber44Block2Chunk1Row_1_ok,
    tttLargeFiber44Block2Chunk1Row_2_ok,
    tttLargeFiber44Block2Chunk1Row_3_ok,
    tttLargeFiber44Block2Chunk1Row_4_ok,
    tttLargeFiber44Block2Chunk1Row_5_ok,
    tttLargeFiber44Block2Chunk1Row_6_ok,
    tttLargeFiber44Block2Chunk1Row_7_ok,
    tttLargeFiber44Block2Chunk1Row_8_ok,
    tttLargeFiber44Block2Chunk1Row_9_ok,
    tttLargeFiber44Block2Chunk1Row_10_ok,
    tttLargeFiber44Block2Chunk1Row_11_ok,
    tttLargeFiber44Block2Chunk1Row_12_ok,
    tttLargeFiber44Block2Chunk1Row_13_ok,
    tttLargeFiber44Block2Chunk1Row_14_ok,
    tttLargeFiber44Block2Chunk1Row_15_ok]

def tttLargeFiber44Block2Chunk1ParentMapAudit : Bool :=
  tttLargeFiber44Block2Chunk1ParentMapCheck 0
    && tttLargeFiber44Block2Chunk1ParentMapCheck 1
    && tttLargeFiber44Block2Chunk1ParentMapCheck 2
    && tttLargeFiber44Block2Chunk1ParentMapCheck 3
    && tttLargeFiber44Block2Chunk1ParentMapCheck 4
    && tttLargeFiber44Block2Chunk1ParentMapCheck 5
    && tttLargeFiber44Block2Chunk1ParentMapCheck 6
    && tttLargeFiber44Block2Chunk1ParentMapCheck 7
    && tttLargeFiber44Block2Chunk1ParentMapCheck 8
    && tttLargeFiber44Block2Chunk1ParentMapCheck 9
    && tttLargeFiber44Block2Chunk1ParentMapCheck 10
    && tttLargeFiber44Block2Chunk1ParentMapCheck 11
    && tttLargeFiber44Block2Chunk1ParentMapCheck 12
    && tttLargeFiber44Block2Chunk1ParentMapCheck 13
    && tttLargeFiber44Block2Chunk1ParentMapCheck 14
    && tttLargeFiber44Block2Chunk1ParentMapCheck 15

theorem tttLargeFiber44Block2Chunk1ParentMapAudit_ok :
    tttLargeFiber44Block2Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber44Block2Chunk1ParentMapAudit,
    tttLargeFiber44Block2Chunk1ParentMap_0_ok,
    tttLargeFiber44Block2Chunk1ParentMap_1_ok,
    tttLargeFiber44Block2Chunk1ParentMap_2_ok,
    tttLargeFiber44Block2Chunk1ParentMap_3_ok,
    tttLargeFiber44Block2Chunk1ParentMap_4_ok,
    tttLargeFiber44Block2Chunk1ParentMap_5_ok,
    tttLargeFiber44Block2Chunk1ParentMap_6_ok,
    tttLargeFiber44Block2Chunk1ParentMap_7_ok,
    tttLargeFiber44Block2Chunk1ParentMap_8_ok,
    tttLargeFiber44Block2Chunk1ParentMap_9_ok,
    tttLargeFiber44Block2Chunk1ParentMap_10_ok,
    tttLargeFiber44Block2Chunk1ParentMap_11_ok,
    tttLargeFiber44Block2Chunk1ParentMap_12_ok,
    tttLargeFiber44Block2Chunk1ParentMap_13_ok,
    tttLargeFiber44Block2Chunk1ParentMap_14_ok,
    tttLargeFiber44Block2Chunk1ParentMap_15_ok]

def tttLargeFiber44Block2Chunk1ParentsAudit : Bool :=
  tttLargeFiber44Block2Chunk1ParentPathCheck 0
    && tttLargeFiber44Block2Chunk1ParentPathCheck 1
    && tttLargeFiber44Block2Chunk1ParentPathCheck 2
    && tttLargeFiber44Block2Chunk1ParentPathCheck 3
    && tttLargeFiber44Block2Chunk1ParentPathCheck 4
    && tttLargeFiber44Block2Chunk1ParentPathCheck 5
    && tttLargeFiber44Block2Chunk1ParentPathCheck 6
    && tttLargeFiber44Block2Chunk1ParentPathCheck 7
    && tttLargeFiber44Block2Chunk1ParentPathCheck 8
    && tttLargeFiber44Block2Chunk1ParentPathCheck 9
    && tttLargeFiber44Block2Chunk1ParentPathCheck 10
    && tttLargeFiber44Block2Chunk1ParentPathCheck 11
    && tttLargeFiber44Block2Chunk1ParentPathCheck 12
    && tttLargeFiber44Block2Chunk1ParentPathCheck 13
    && tttLargeFiber44Block2Chunk1ParentPathCheck 14
    && tttLargeFiber44Block2Chunk1ParentPathCheck 15

theorem tttLargeFiber44Block2Chunk1ParentsAudit_ok :
    tttLargeFiber44Block2Chunk1ParentsAudit = true := by
  simp [tttLargeFiber44Block2Chunk1ParentsAudit,
    tttLargeFiber44Block2Chunk1ParentPath_0_ok,
    tttLargeFiber44Block2Chunk1ParentPath_1_ok,
    tttLargeFiber44Block2Chunk1ParentPath_2_ok,
    tttLargeFiber44Block2Chunk1ParentPath_3_ok,
    tttLargeFiber44Block2Chunk1ParentPath_4_ok,
    tttLargeFiber44Block2Chunk1ParentPath_5_ok,
    tttLargeFiber44Block2Chunk1ParentPath_6_ok,
    tttLargeFiber44Block2Chunk1ParentPath_7_ok,
    tttLargeFiber44Block2Chunk1ParentPath_8_ok,
    tttLargeFiber44Block2Chunk1ParentPath_9_ok,
    tttLargeFiber44Block2Chunk1ParentPath_10_ok,
    tttLargeFiber44Block2Chunk1ParentPath_11_ok,
    tttLargeFiber44Block2Chunk1ParentPath_12_ok,
    tttLargeFiber44Block2Chunk1ParentPath_13_ok,
    tttLargeFiber44Block2Chunk1ParentPath_14_ok,
    tttLargeFiber44Block2Chunk1ParentPath_15_ok]

def tttLargeFiber44Block2Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber44CountsAudit &&
    tttLargeFiber44Block2Chunk1SourcesCheck &&
    tttLargeFiber44Block2Chunk1RowsAudit &&
    tttLargeFiber44Block2Chunk1ParentMapAudit &&
    tttLargeFiber44Block2Chunk1ParentsAudit

theorem tttLargeFiber44Block2Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber44Block2Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber44Block2Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber44CountsAudit_ok,
    tttLargeFiber44Block2Chunk1SourcesCheck_ok,
    tttLargeFiber44Block2Chunk1RowsAudit_ok,
    tttLargeFiber44Block2Chunk1ParentMapAudit_ok,
    tttLargeFiber44Block2Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber44Block2Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
