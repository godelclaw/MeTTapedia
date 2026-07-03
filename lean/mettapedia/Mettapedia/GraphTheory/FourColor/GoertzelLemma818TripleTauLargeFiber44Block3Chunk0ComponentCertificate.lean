import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber44Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 44, block 3 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber44Block3Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber44Data

def tttLargeFiber44Block3Chunk0Sources : List Nat :=
  [   5104, 5105, 5106, 5107, 5108, 5109, 5110, 5111,
   5112, 5113, 5114, 5115, 5116, 5117, 5118, 5119]

def tttLargeFiber44Row192 : TripleComponentParentRow :=
  tripleRow 5104 5136 151 8 80 151 56 148
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

def tttLargeFiber44Row193 : TripleComponentParentRow :=
  tripleRow 5105 5137 151 8 81 151 56 149
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

def tttLargeFiber44Row194 : TripleComponentParentRow :=
  tripleRow 5106 5104 151 8 82 151 8 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row195 : TripleComponentParentRow :=
  tripleRow 5107 5139 151 8 83 151 56 151
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

def tttLargeFiber44Row196 : TripleComponentParentRow :=
  tripleRow 5108 5140 151 8 100 151 56 164
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber44Row197 : TripleComponentParentRow :=
  tripleRow 5109 5141 151 8 101 151 56 165
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber44Row198 : TripleComponentParentRow :=
  tripleRow 5110 5105 151 8 102 151 8 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber44Row199 : TripleComponentParentRow :=
  tripleRow 5111 5104 151 8 103 151 8 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber44Row200 : TripleComponentParentRow :=
  tripleRow 5112 5144 151 9 88 151 57 156
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

def tttLargeFiber44Row201 : TripleComponentParentRow :=
  tripleRow 5113 5145 151 9 89 151 57 157
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

def tttLargeFiber44Row202 : TripleComponentParentRow :=
  tripleRow 5114 5112 151 9 90 151 9 88
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber44Row203 : TripleComponentParentRow :=
  tripleRow 5115 5147 151 9 91 151 57 159
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

def tttLargeFiber44Row204 : TripleComponentParentRow :=
  tripleRow 5116 5148 151 9 108 151 57 172
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber44Row205 : TripleComponentParentRow :=
  tripleRow 5117 5149 151 9 109 151 57 173
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber44Row206 : TripleComponentParentRow :=
  tripleRow 5118 5113 151 9 110 151 9 89
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber44Row207 : TripleComponentParentRow :=
  tripleRow 5119 5112 151 9 111 151 9 88
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber44Block3Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber44Row192
  , tttLargeFiber44Row193
  , tttLargeFiber44Row194
  , tttLargeFiber44Row195
  , tttLargeFiber44Row196
  , tttLargeFiber44Row197
  , tttLargeFiber44Row198
  , tttLargeFiber44Row199
  , tttLargeFiber44Row200
  , tttLargeFiber44Row201
  , tttLargeFiber44Row202
  , tttLargeFiber44Row203
  , tttLargeFiber44Row204
  , tttLargeFiber44Row205
  , tttLargeFiber44Row206
  , tttLargeFiber44Row207
  ]

def tttLargeFiber44Block3Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (4912 <= i) && decide (i < 5168)) ||
    (decide (5456 <= i) && decide (i < 5712))

def tttLargeFiber44Block3Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber44Block3Chunk0ExpectedContains row.source &&
    tttLargeFiber44Block3Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber44Key &&
          chainInputKey tttWord t == tttLargeFiber44Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber44Block3Chunk0SourcesCheck : Bool :=
  (tttLargeFiber44Block3Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber44Block3Chunk0Sources

theorem tttLargeFiber44Block3Chunk0SourcesCheck_ok :
    tttLargeFiber44Block3Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber44Block3Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber44Block3Chunk0RowValid
    (listGetD tttLargeFiber44Block3Chunk0Rows i default)

def tttLargeFiber44Block3Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber44Block3Chunk0Rows i default
  row.parent == tttLargeFiber44ParentOf row.source

def tttLargeFiber44Block3Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber44Block3Chunk0Sources 0 0 == 5104
      && tttLargeFiber44ParentOf 5104 == 5136
      && tttLargeFiber44ParentOf 5136 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (2 <= tttLargeFiber44MaxParentDepth)
  | 1 => listGetD tttLargeFiber44Block3Chunk0Sources 1 0 == 5105
      && tttLargeFiber44ParentOf 5105 == 5137
      && tttLargeFiber44ParentOf 5137 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 2 => listGetD tttLargeFiber44Block3Chunk0Sources 2 0 == 5106
      && tttLargeFiber44ParentOf 5106 == 5104
      && tttLargeFiber44ParentOf 5104 == 5136
      && tttLargeFiber44ParentOf 5136 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 3 => listGetD tttLargeFiber44Block3Chunk0Sources 3 0 == 5107
      && tttLargeFiber44ParentOf 5107 == 5139
      && tttLargeFiber44ParentOf 5139 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 4 => listGetD tttLargeFiber44Block3Chunk0Sources 4 0 == 5108
      && tttLargeFiber44ParentOf 5108 == 5140
      && tttLargeFiber44ParentOf 5140 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 5 => listGetD tttLargeFiber44Block3Chunk0Sources 5 0 == 5109
      && tttLargeFiber44ParentOf 5109 == 5141
      && tttLargeFiber44ParentOf 5141 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 6 => listGetD tttLargeFiber44Block3Chunk0Sources 6 0 == 5110
      && tttLargeFiber44ParentOf 5110 == 5105
      && tttLargeFiber44ParentOf 5105 == 5137
      && tttLargeFiber44ParentOf 5137 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 7 => listGetD tttLargeFiber44Block3Chunk0Sources 7 0 == 5111
      && tttLargeFiber44ParentOf 5111 == 5104
      && tttLargeFiber44ParentOf 5104 == 5136
      && tttLargeFiber44ParentOf 5136 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 8 => listGetD tttLargeFiber44Block3Chunk0Sources 8 0 == 5112
      && tttLargeFiber44ParentOf 5112 == 5144
      && tttLargeFiber44ParentOf 5144 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (3 <= tttLargeFiber44MaxParentDepth)
  | 9 => listGetD tttLargeFiber44Block3Chunk0Sources 9 0 == 5113
      && tttLargeFiber44ParentOf 5113 == 5145
      && tttLargeFiber44ParentOf 5145 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 10 => listGetD tttLargeFiber44Block3Chunk0Sources 10 0 == 5114
      && tttLargeFiber44ParentOf 5114 == 5112
      && tttLargeFiber44ParentOf 5112 == 5144
      && tttLargeFiber44ParentOf 5144 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 11 => listGetD tttLargeFiber44Block3Chunk0Sources 11 0 == 5115
      && tttLargeFiber44ParentOf 5115 == 5147
      && tttLargeFiber44ParentOf 5147 == 4923
      && tttLargeFiber44ParentOf 4923 == 4915
      && tttLargeFiber44ParentOf 4915 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 12 => listGetD tttLargeFiber44Block3Chunk0Sources 12 0 == 5116
      && tttLargeFiber44ParentOf 5116 == 5148
      && tttLargeFiber44ParentOf 5148 == 4924
      && tttLargeFiber44ParentOf 4924 == 4916
      && tttLargeFiber44ParentOf 4916 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | 13 => listGetD tttLargeFiber44Block3Chunk0Sources 13 0 == 5117
      && tttLargeFiber44ParentOf 5117 == 5149
      && tttLargeFiber44ParentOf 5149 == 4925
      && tttLargeFiber44ParentOf 4925 == 4917
      && tttLargeFiber44ParentOf 4917 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 14 => listGetD tttLargeFiber44Block3Chunk0Sources 14 0 == 5118
      && tttLargeFiber44ParentOf 5118 == 5113
      && tttLargeFiber44ParentOf 5113 == 5145
      && tttLargeFiber44ParentOf 5145 == 4921
      && tttLargeFiber44ParentOf 4921 == 4913
      && tttLargeFiber44ParentOf 4913 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (5 <= tttLargeFiber44MaxParentDepth)
  | 15 => listGetD tttLargeFiber44Block3Chunk0Sources 15 0 == 5119
      && tttLargeFiber44ParentOf 5119 == 5112
      && tttLargeFiber44ParentOf 5112 == 5144
      && tttLargeFiber44ParentOf 5144 == 4920
      && tttLargeFiber44ParentOf 4920 == 4912
      && 4912 == tttLargeFiber44Root
      && decide (4 <= tttLargeFiber44MaxParentDepth)
  | _ => false

theorem tttLargeFiber44Block3Chunk0Row_0_ok :
    tttLargeFiber44Block3Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0Row_1_ok :
    tttLargeFiber44Block3Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0Row_2_ok :
    tttLargeFiber44Block3Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0Row_3_ok :
    tttLargeFiber44Block3Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0Row_4_ok :
    tttLargeFiber44Block3Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0Row_5_ok :
    tttLargeFiber44Block3Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0Row_6_ok :
    tttLargeFiber44Block3Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0Row_7_ok :
    tttLargeFiber44Block3Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0Row_8_ok :
    tttLargeFiber44Block3Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0Row_9_ok :
    tttLargeFiber44Block3Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0Row_10_ok :
    tttLargeFiber44Block3Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0Row_11_ok :
    tttLargeFiber44Block3Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0Row_12_ok :
    tttLargeFiber44Block3Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0Row_13_ok :
    tttLargeFiber44Block3Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0Row_14_ok :
    tttLargeFiber44Block3Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0Row_15_ok :
    tttLargeFiber44Block3Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentMap_0_ok :
    tttLargeFiber44Block3Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentMap_1_ok :
    tttLargeFiber44Block3Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentMap_2_ok :
    tttLargeFiber44Block3Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentMap_3_ok :
    tttLargeFiber44Block3Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentMap_4_ok :
    tttLargeFiber44Block3Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentMap_5_ok :
    tttLargeFiber44Block3Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentMap_6_ok :
    tttLargeFiber44Block3Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentMap_7_ok :
    tttLargeFiber44Block3Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentMap_8_ok :
    tttLargeFiber44Block3Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentMap_9_ok :
    tttLargeFiber44Block3Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentMap_10_ok :
    tttLargeFiber44Block3Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentMap_11_ok :
    tttLargeFiber44Block3Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentMap_12_ok :
    tttLargeFiber44Block3Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentMap_13_ok :
    tttLargeFiber44Block3Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentMap_14_ok :
    tttLargeFiber44Block3Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentMap_15_ok :
    tttLargeFiber44Block3Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentPath_0_ok :
    tttLargeFiber44Block3Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentPath_1_ok :
    tttLargeFiber44Block3Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentPath_2_ok :
    tttLargeFiber44Block3Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentPath_3_ok :
    tttLargeFiber44Block3Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentPath_4_ok :
    tttLargeFiber44Block3Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentPath_5_ok :
    tttLargeFiber44Block3Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentPath_6_ok :
    tttLargeFiber44Block3Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentPath_7_ok :
    tttLargeFiber44Block3Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentPath_8_ok :
    tttLargeFiber44Block3Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentPath_9_ok :
    tttLargeFiber44Block3Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentPath_10_ok :
    tttLargeFiber44Block3Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentPath_11_ok :
    tttLargeFiber44Block3Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentPath_12_ok :
    tttLargeFiber44Block3Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentPath_13_ok :
    tttLargeFiber44Block3Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentPath_14_ok :
    tttLargeFiber44Block3Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber44Block3Chunk0ParentPath_15_ok :
    tttLargeFiber44Block3Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber44Block3Chunk0RowsAudit : Bool :=
  tttLargeFiber44Block3Chunk0RowCheck 0
    && tttLargeFiber44Block3Chunk0RowCheck 1
    && tttLargeFiber44Block3Chunk0RowCheck 2
    && tttLargeFiber44Block3Chunk0RowCheck 3
    && tttLargeFiber44Block3Chunk0RowCheck 4
    && tttLargeFiber44Block3Chunk0RowCheck 5
    && tttLargeFiber44Block3Chunk0RowCheck 6
    && tttLargeFiber44Block3Chunk0RowCheck 7
    && tttLargeFiber44Block3Chunk0RowCheck 8
    && tttLargeFiber44Block3Chunk0RowCheck 9
    && tttLargeFiber44Block3Chunk0RowCheck 10
    && tttLargeFiber44Block3Chunk0RowCheck 11
    && tttLargeFiber44Block3Chunk0RowCheck 12
    && tttLargeFiber44Block3Chunk0RowCheck 13
    && tttLargeFiber44Block3Chunk0RowCheck 14
    && tttLargeFiber44Block3Chunk0RowCheck 15

theorem tttLargeFiber44Block3Chunk0RowsAudit_ok :
    tttLargeFiber44Block3Chunk0RowsAudit = true := by
  simp [tttLargeFiber44Block3Chunk0RowsAudit,
    tttLargeFiber44Block3Chunk0Row_0_ok,
    tttLargeFiber44Block3Chunk0Row_1_ok,
    tttLargeFiber44Block3Chunk0Row_2_ok,
    tttLargeFiber44Block3Chunk0Row_3_ok,
    tttLargeFiber44Block3Chunk0Row_4_ok,
    tttLargeFiber44Block3Chunk0Row_5_ok,
    tttLargeFiber44Block3Chunk0Row_6_ok,
    tttLargeFiber44Block3Chunk0Row_7_ok,
    tttLargeFiber44Block3Chunk0Row_8_ok,
    tttLargeFiber44Block3Chunk0Row_9_ok,
    tttLargeFiber44Block3Chunk0Row_10_ok,
    tttLargeFiber44Block3Chunk0Row_11_ok,
    tttLargeFiber44Block3Chunk0Row_12_ok,
    tttLargeFiber44Block3Chunk0Row_13_ok,
    tttLargeFiber44Block3Chunk0Row_14_ok,
    tttLargeFiber44Block3Chunk0Row_15_ok]

def tttLargeFiber44Block3Chunk0ParentMapAudit : Bool :=
  tttLargeFiber44Block3Chunk0ParentMapCheck 0
    && tttLargeFiber44Block3Chunk0ParentMapCheck 1
    && tttLargeFiber44Block3Chunk0ParentMapCheck 2
    && tttLargeFiber44Block3Chunk0ParentMapCheck 3
    && tttLargeFiber44Block3Chunk0ParentMapCheck 4
    && tttLargeFiber44Block3Chunk0ParentMapCheck 5
    && tttLargeFiber44Block3Chunk0ParentMapCheck 6
    && tttLargeFiber44Block3Chunk0ParentMapCheck 7
    && tttLargeFiber44Block3Chunk0ParentMapCheck 8
    && tttLargeFiber44Block3Chunk0ParentMapCheck 9
    && tttLargeFiber44Block3Chunk0ParentMapCheck 10
    && tttLargeFiber44Block3Chunk0ParentMapCheck 11
    && tttLargeFiber44Block3Chunk0ParentMapCheck 12
    && tttLargeFiber44Block3Chunk0ParentMapCheck 13
    && tttLargeFiber44Block3Chunk0ParentMapCheck 14
    && tttLargeFiber44Block3Chunk0ParentMapCheck 15

theorem tttLargeFiber44Block3Chunk0ParentMapAudit_ok :
    tttLargeFiber44Block3Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber44Block3Chunk0ParentMapAudit,
    tttLargeFiber44Block3Chunk0ParentMap_0_ok,
    tttLargeFiber44Block3Chunk0ParentMap_1_ok,
    tttLargeFiber44Block3Chunk0ParentMap_2_ok,
    tttLargeFiber44Block3Chunk0ParentMap_3_ok,
    tttLargeFiber44Block3Chunk0ParentMap_4_ok,
    tttLargeFiber44Block3Chunk0ParentMap_5_ok,
    tttLargeFiber44Block3Chunk0ParentMap_6_ok,
    tttLargeFiber44Block3Chunk0ParentMap_7_ok,
    tttLargeFiber44Block3Chunk0ParentMap_8_ok,
    tttLargeFiber44Block3Chunk0ParentMap_9_ok,
    tttLargeFiber44Block3Chunk0ParentMap_10_ok,
    tttLargeFiber44Block3Chunk0ParentMap_11_ok,
    tttLargeFiber44Block3Chunk0ParentMap_12_ok,
    tttLargeFiber44Block3Chunk0ParentMap_13_ok,
    tttLargeFiber44Block3Chunk0ParentMap_14_ok,
    tttLargeFiber44Block3Chunk0ParentMap_15_ok]

def tttLargeFiber44Block3Chunk0ParentsAudit : Bool :=
  tttLargeFiber44Block3Chunk0ParentPathCheck 0
    && tttLargeFiber44Block3Chunk0ParentPathCheck 1
    && tttLargeFiber44Block3Chunk0ParentPathCheck 2
    && tttLargeFiber44Block3Chunk0ParentPathCheck 3
    && tttLargeFiber44Block3Chunk0ParentPathCheck 4
    && tttLargeFiber44Block3Chunk0ParentPathCheck 5
    && tttLargeFiber44Block3Chunk0ParentPathCheck 6
    && tttLargeFiber44Block3Chunk0ParentPathCheck 7
    && tttLargeFiber44Block3Chunk0ParentPathCheck 8
    && tttLargeFiber44Block3Chunk0ParentPathCheck 9
    && tttLargeFiber44Block3Chunk0ParentPathCheck 10
    && tttLargeFiber44Block3Chunk0ParentPathCheck 11
    && tttLargeFiber44Block3Chunk0ParentPathCheck 12
    && tttLargeFiber44Block3Chunk0ParentPathCheck 13
    && tttLargeFiber44Block3Chunk0ParentPathCheck 14
    && tttLargeFiber44Block3Chunk0ParentPathCheck 15

theorem tttLargeFiber44Block3Chunk0ParentsAudit_ok :
    tttLargeFiber44Block3Chunk0ParentsAudit = true := by
  simp [tttLargeFiber44Block3Chunk0ParentsAudit,
    tttLargeFiber44Block3Chunk0ParentPath_0_ok,
    tttLargeFiber44Block3Chunk0ParentPath_1_ok,
    tttLargeFiber44Block3Chunk0ParentPath_2_ok,
    tttLargeFiber44Block3Chunk0ParentPath_3_ok,
    tttLargeFiber44Block3Chunk0ParentPath_4_ok,
    tttLargeFiber44Block3Chunk0ParentPath_5_ok,
    tttLargeFiber44Block3Chunk0ParentPath_6_ok,
    tttLargeFiber44Block3Chunk0ParentPath_7_ok,
    tttLargeFiber44Block3Chunk0ParentPath_8_ok,
    tttLargeFiber44Block3Chunk0ParentPath_9_ok,
    tttLargeFiber44Block3Chunk0ParentPath_10_ok,
    tttLargeFiber44Block3Chunk0ParentPath_11_ok,
    tttLargeFiber44Block3Chunk0ParentPath_12_ok,
    tttLargeFiber44Block3Chunk0ParentPath_13_ok,
    tttLargeFiber44Block3Chunk0ParentPath_14_ok,
    tttLargeFiber44Block3Chunk0ParentPath_15_ok]

def tttLargeFiber44Block3Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber44CountsAudit &&
    tttLargeFiber44Block3Chunk0SourcesCheck &&
    tttLargeFiber44Block3Chunk0RowsAudit &&
    tttLargeFiber44Block3Chunk0ParentMapAudit &&
    tttLargeFiber44Block3Chunk0ParentsAudit

theorem tttLargeFiber44Block3Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber44Block3Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber44Block3Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber44CountsAudit_ok,
    tttLargeFiber44Block3Chunk0SourcesCheck_ok,
    tttLargeFiber44Block3Chunk0RowsAudit_ok,
    tttLargeFiber44Block3Chunk0ParentMapAudit_ok,
    tttLargeFiber44Block3Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber44Block3Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
