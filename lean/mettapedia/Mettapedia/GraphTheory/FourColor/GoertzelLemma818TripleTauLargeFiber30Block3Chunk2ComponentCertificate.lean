import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 3 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block3Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block3Chunk2Sources : List Nat :=
  [   224, 225, 226, 227, 228, 229, 230, 231,
   232, 233, 234, 235, 236, 237, 238, 239]

def tttLargeFiber30Row224 : TripleComponentParentRow :=
  tripleRow 224 192 3 40 148 3 24 80
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

def tttLargeFiber30Row225 : TripleComponentParentRow :=
  tripleRow 225 193 3 40 149 3 24 81
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

def tttLargeFiber30Row226 : TripleComponentParentRow :=
  tripleRow 226 194 3 40 150 3 24 82
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

def tttLargeFiber30Row227 : TripleComponentParentRow :=
  tripleRow 227 224 3 40 151 3 40 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row228 : TripleComponentParentRow :=
  tripleRow 228 224 3 40 164 3 40 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber30Row229 : TripleComponentParentRow :=
  tripleRow 229 225 3 40 165 3 40 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber30Row230 : TripleComponentParentRow :=
  tripleRow 230 198 3 40 166 3 24 102
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber30Row231 : TripleComponentParentRow :=
  tripleRow 231 199 3 40 167 3 24 103
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber30Row232 : TripleComponentParentRow :=
  tripleRow 232 200 3 41 156 3 25 88
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

def tttLargeFiber30Row233 : TripleComponentParentRow :=
  tripleRow 233 201 3 41 157 3 25 89
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

def tttLargeFiber30Row234 : TripleComponentParentRow :=
  tripleRow 234 202 3 41 158 3 25 90
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

def tttLargeFiber30Row235 : TripleComponentParentRow :=
  tripleRow 235 232 3 41 159 3 41 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row236 : TripleComponentParentRow :=
  tripleRow 236 232 3 41 172 3 41 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber30Row237 : TripleComponentParentRow :=
  tripleRow 237 233 3 41 173 3 41 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber30Row238 : TripleComponentParentRow :=
  tripleRow 238 206 3 41 174 3 25 110
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber30Row239 : TripleComponentParentRow :=
  tripleRow 239 207 3 41 175 3 25 111
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber30Block3Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row224
  , tttLargeFiber30Row225
  , tttLargeFiber30Row226
  , tttLargeFiber30Row227
  , tttLargeFiber30Row228
  , tttLargeFiber30Row229
  , tttLargeFiber30Row230
  , tttLargeFiber30Row231
  , tttLargeFiber30Row232
  , tttLargeFiber30Row233
  , tttLargeFiber30Row234
  , tttLargeFiber30Row235
  , tttLargeFiber30Row236
  , tttLargeFiber30Row237
  , tttLargeFiber30Row238
  , tttLargeFiber30Row239
  ]

def tttLargeFiber30Block3Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block3Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block3Chunk2ExpectedContains row.source &&
    tttLargeFiber30Block3Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block3Chunk2SourcesCheck : Bool :=
  (tttLargeFiber30Block3Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber30Block3Chunk2Sources

theorem tttLargeFiber30Block3Chunk2SourcesCheck_ok :
    tttLargeFiber30Block3Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber30Block3Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block3Chunk2RowValid
    (listGetD tttLargeFiber30Block3Chunk2Rows i default)

def tttLargeFiber30Block3Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block3Chunk2Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block3Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block3Chunk2Sources 0 0 == 224
      && tttLargeFiber30ParentOf 224 == 192
      && tttLargeFiber30ParentOf 192 == 64
      && tttLargeFiber30ParentOf 64 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block3Chunk2Sources 1 0 == 225
      && tttLargeFiber30ParentOf 225 == 193
      && tttLargeFiber30ParentOf 193 == 65
      && tttLargeFiber30ParentOf 65 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block3Chunk2Sources 2 0 == 226
      && tttLargeFiber30ParentOf 226 == 194
      && tttLargeFiber30ParentOf 194 == 66
      && tttLargeFiber30ParentOf 66 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block3Chunk2Sources 3 0 == 227
      && tttLargeFiber30ParentOf 227 == 224
      && tttLargeFiber30ParentOf 224 == 192
      && tttLargeFiber30ParentOf 192 == 64
      && tttLargeFiber30ParentOf 64 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block3Chunk2Sources 4 0 == 228
      && tttLargeFiber30ParentOf 228 == 224
      && tttLargeFiber30ParentOf 224 == 192
      && tttLargeFiber30ParentOf 192 == 64
      && tttLargeFiber30ParentOf 64 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block3Chunk2Sources 5 0 == 229
      && tttLargeFiber30ParentOf 229 == 225
      && tttLargeFiber30ParentOf 225 == 193
      && tttLargeFiber30ParentOf 193 == 65
      && tttLargeFiber30ParentOf 65 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block3Chunk2Sources 6 0 == 230
      && tttLargeFiber30ParentOf 230 == 198
      && tttLargeFiber30ParentOf 198 == 70
      && tttLargeFiber30ParentOf 70 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block3Chunk2Sources 7 0 == 231
      && tttLargeFiber30ParentOf 231 == 199
      && tttLargeFiber30ParentOf 199 == 71
      && tttLargeFiber30ParentOf 71 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block3Chunk2Sources 8 0 == 232
      && tttLargeFiber30ParentOf 232 == 200
      && tttLargeFiber30ParentOf 200 == 72
      && tttLargeFiber30ParentOf 72 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block3Chunk2Sources 9 0 == 233
      && tttLargeFiber30ParentOf 233 == 201
      && tttLargeFiber30ParentOf 201 == 73
      && tttLargeFiber30ParentOf 73 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block3Chunk2Sources 10 0 == 234
      && tttLargeFiber30ParentOf 234 == 202
      && tttLargeFiber30ParentOf 202 == 74
      && tttLargeFiber30ParentOf 74 == 10
      && tttLargeFiber30ParentOf 10 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block3Chunk2Sources 11 0 == 235
      && tttLargeFiber30ParentOf 235 == 232
      && tttLargeFiber30ParentOf 232 == 200
      && tttLargeFiber30ParentOf 200 == 72
      && tttLargeFiber30ParentOf 72 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block3Chunk2Sources 12 0 == 236
      && tttLargeFiber30ParentOf 236 == 232
      && tttLargeFiber30ParentOf 232 == 200
      && tttLargeFiber30ParentOf 200 == 72
      && tttLargeFiber30ParentOf 72 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block3Chunk2Sources 13 0 == 237
      && tttLargeFiber30ParentOf 237 == 233
      && tttLargeFiber30ParentOf 233 == 201
      && tttLargeFiber30ParentOf 201 == 73
      && tttLargeFiber30ParentOf 73 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (6 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block3Chunk2Sources 14 0 == 238
      && tttLargeFiber30ParentOf 238 == 206
      && tttLargeFiber30ParentOf 206 == 78
      && tttLargeFiber30ParentOf 78 == 14
      && tttLargeFiber30ParentOf 14 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (6 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block3Chunk2Sources 15 0 == 239
      && tttLargeFiber30ParentOf 239 == 207
      && tttLargeFiber30ParentOf 207 == 79
      && tttLargeFiber30ParentOf 79 == 15
      && tttLargeFiber30ParentOf 15 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block3Chunk2Row_0_ok :
    tttLargeFiber30Block3Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2Row_1_ok :
    tttLargeFiber30Block3Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2Row_2_ok :
    tttLargeFiber30Block3Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2Row_3_ok :
    tttLargeFiber30Block3Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2Row_4_ok :
    tttLargeFiber30Block3Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2Row_5_ok :
    tttLargeFiber30Block3Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2Row_6_ok :
    tttLargeFiber30Block3Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2Row_7_ok :
    tttLargeFiber30Block3Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2Row_8_ok :
    tttLargeFiber30Block3Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2Row_9_ok :
    tttLargeFiber30Block3Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2Row_10_ok :
    tttLargeFiber30Block3Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2Row_11_ok :
    tttLargeFiber30Block3Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2Row_12_ok :
    tttLargeFiber30Block3Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2Row_13_ok :
    tttLargeFiber30Block3Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2Row_14_ok :
    tttLargeFiber30Block3Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2Row_15_ok :
    tttLargeFiber30Block3Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentMap_0_ok :
    tttLargeFiber30Block3Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentMap_1_ok :
    tttLargeFiber30Block3Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentMap_2_ok :
    tttLargeFiber30Block3Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentMap_3_ok :
    tttLargeFiber30Block3Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentMap_4_ok :
    tttLargeFiber30Block3Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentMap_5_ok :
    tttLargeFiber30Block3Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentMap_6_ok :
    tttLargeFiber30Block3Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentMap_7_ok :
    tttLargeFiber30Block3Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentMap_8_ok :
    tttLargeFiber30Block3Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentMap_9_ok :
    tttLargeFiber30Block3Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentMap_10_ok :
    tttLargeFiber30Block3Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentMap_11_ok :
    tttLargeFiber30Block3Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentMap_12_ok :
    tttLargeFiber30Block3Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentMap_13_ok :
    tttLargeFiber30Block3Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentMap_14_ok :
    tttLargeFiber30Block3Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentMap_15_ok :
    tttLargeFiber30Block3Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentPath_0_ok :
    tttLargeFiber30Block3Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentPath_1_ok :
    tttLargeFiber30Block3Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentPath_2_ok :
    tttLargeFiber30Block3Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentPath_3_ok :
    tttLargeFiber30Block3Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentPath_4_ok :
    tttLargeFiber30Block3Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentPath_5_ok :
    tttLargeFiber30Block3Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentPath_6_ok :
    tttLargeFiber30Block3Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentPath_7_ok :
    tttLargeFiber30Block3Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentPath_8_ok :
    tttLargeFiber30Block3Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentPath_9_ok :
    tttLargeFiber30Block3Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentPath_10_ok :
    tttLargeFiber30Block3Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentPath_11_ok :
    tttLargeFiber30Block3Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentPath_12_ok :
    tttLargeFiber30Block3Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentPath_13_ok :
    tttLargeFiber30Block3Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentPath_14_ok :
    tttLargeFiber30Block3Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block3Chunk2ParentPath_15_ok :
    tttLargeFiber30Block3Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block3Chunk2RowsAudit : Bool :=
  tttLargeFiber30Block3Chunk2RowCheck 0
    && tttLargeFiber30Block3Chunk2RowCheck 1
    && tttLargeFiber30Block3Chunk2RowCheck 2
    && tttLargeFiber30Block3Chunk2RowCheck 3
    && tttLargeFiber30Block3Chunk2RowCheck 4
    && tttLargeFiber30Block3Chunk2RowCheck 5
    && tttLargeFiber30Block3Chunk2RowCheck 6
    && tttLargeFiber30Block3Chunk2RowCheck 7
    && tttLargeFiber30Block3Chunk2RowCheck 8
    && tttLargeFiber30Block3Chunk2RowCheck 9
    && tttLargeFiber30Block3Chunk2RowCheck 10
    && tttLargeFiber30Block3Chunk2RowCheck 11
    && tttLargeFiber30Block3Chunk2RowCheck 12
    && tttLargeFiber30Block3Chunk2RowCheck 13
    && tttLargeFiber30Block3Chunk2RowCheck 14
    && tttLargeFiber30Block3Chunk2RowCheck 15

theorem tttLargeFiber30Block3Chunk2RowsAudit_ok :
    tttLargeFiber30Block3Chunk2RowsAudit = true := by
  simp [tttLargeFiber30Block3Chunk2RowsAudit,
    tttLargeFiber30Block3Chunk2Row_0_ok,
    tttLargeFiber30Block3Chunk2Row_1_ok,
    tttLargeFiber30Block3Chunk2Row_2_ok,
    tttLargeFiber30Block3Chunk2Row_3_ok,
    tttLargeFiber30Block3Chunk2Row_4_ok,
    tttLargeFiber30Block3Chunk2Row_5_ok,
    tttLargeFiber30Block3Chunk2Row_6_ok,
    tttLargeFiber30Block3Chunk2Row_7_ok,
    tttLargeFiber30Block3Chunk2Row_8_ok,
    tttLargeFiber30Block3Chunk2Row_9_ok,
    tttLargeFiber30Block3Chunk2Row_10_ok,
    tttLargeFiber30Block3Chunk2Row_11_ok,
    tttLargeFiber30Block3Chunk2Row_12_ok,
    tttLargeFiber30Block3Chunk2Row_13_ok,
    tttLargeFiber30Block3Chunk2Row_14_ok,
    tttLargeFiber30Block3Chunk2Row_15_ok]

def tttLargeFiber30Block3Chunk2ParentMapAudit : Bool :=
  tttLargeFiber30Block3Chunk2ParentMapCheck 0
    && tttLargeFiber30Block3Chunk2ParentMapCheck 1
    && tttLargeFiber30Block3Chunk2ParentMapCheck 2
    && tttLargeFiber30Block3Chunk2ParentMapCheck 3
    && tttLargeFiber30Block3Chunk2ParentMapCheck 4
    && tttLargeFiber30Block3Chunk2ParentMapCheck 5
    && tttLargeFiber30Block3Chunk2ParentMapCheck 6
    && tttLargeFiber30Block3Chunk2ParentMapCheck 7
    && tttLargeFiber30Block3Chunk2ParentMapCheck 8
    && tttLargeFiber30Block3Chunk2ParentMapCheck 9
    && tttLargeFiber30Block3Chunk2ParentMapCheck 10
    && tttLargeFiber30Block3Chunk2ParentMapCheck 11
    && tttLargeFiber30Block3Chunk2ParentMapCheck 12
    && tttLargeFiber30Block3Chunk2ParentMapCheck 13
    && tttLargeFiber30Block3Chunk2ParentMapCheck 14
    && tttLargeFiber30Block3Chunk2ParentMapCheck 15

theorem tttLargeFiber30Block3Chunk2ParentMapAudit_ok :
    tttLargeFiber30Block3Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber30Block3Chunk2ParentMapAudit,
    tttLargeFiber30Block3Chunk2ParentMap_0_ok,
    tttLargeFiber30Block3Chunk2ParentMap_1_ok,
    tttLargeFiber30Block3Chunk2ParentMap_2_ok,
    tttLargeFiber30Block3Chunk2ParentMap_3_ok,
    tttLargeFiber30Block3Chunk2ParentMap_4_ok,
    tttLargeFiber30Block3Chunk2ParentMap_5_ok,
    tttLargeFiber30Block3Chunk2ParentMap_6_ok,
    tttLargeFiber30Block3Chunk2ParentMap_7_ok,
    tttLargeFiber30Block3Chunk2ParentMap_8_ok,
    tttLargeFiber30Block3Chunk2ParentMap_9_ok,
    tttLargeFiber30Block3Chunk2ParentMap_10_ok,
    tttLargeFiber30Block3Chunk2ParentMap_11_ok,
    tttLargeFiber30Block3Chunk2ParentMap_12_ok,
    tttLargeFiber30Block3Chunk2ParentMap_13_ok,
    tttLargeFiber30Block3Chunk2ParentMap_14_ok,
    tttLargeFiber30Block3Chunk2ParentMap_15_ok]

def tttLargeFiber30Block3Chunk2ParentsAudit : Bool :=
  tttLargeFiber30Block3Chunk2ParentPathCheck 0
    && tttLargeFiber30Block3Chunk2ParentPathCheck 1
    && tttLargeFiber30Block3Chunk2ParentPathCheck 2
    && tttLargeFiber30Block3Chunk2ParentPathCheck 3
    && tttLargeFiber30Block3Chunk2ParentPathCheck 4
    && tttLargeFiber30Block3Chunk2ParentPathCheck 5
    && tttLargeFiber30Block3Chunk2ParentPathCheck 6
    && tttLargeFiber30Block3Chunk2ParentPathCheck 7
    && tttLargeFiber30Block3Chunk2ParentPathCheck 8
    && tttLargeFiber30Block3Chunk2ParentPathCheck 9
    && tttLargeFiber30Block3Chunk2ParentPathCheck 10
    && tttLargeFiber30Block3Chunk2ParentPathCheck 11
    && tttLargeFiber30Block3Chunk2ParentPathCheck 12
    && tttLargeFiber30Block3Chunk2ParentPathCheck 13
    && tttLargeFiber30Block3Chunk2ParentPathCheck 14
    && tttLargeFiber30Block3Chunk2ParentPathCheck 15

theorem tttLargeFiber30Block3Chunk2ParentsAudit_ok :
    tttLargeFiber30Block3Chunk2ParentsAudit = true := by
  simp [tttLargeFiber30Block3Chunk2ParentsAudit,
    tttLargeFiber30Block3Chunk2ParentPath_0_ok,
    tttLargeFiber30Block3Chunk2ParentPath_1_ok,
    tttLargeFiber30Block3Chunk2ParentPath_2_ok,
    tttLargeFiber30Block3Chunk2ParentPath_3_ok,
    tttLargeFiber30Block3Chunk2ParentPath_4_ok,
    tttLargeFiber30Block3Chunk2ParentPath_5_ok,
    tttLargeFiber30Block3Chunk2ParentPath_6_ok,
    tttLargeFiber30Block3Chunk2ParentPath_7_ok,
    tttLargeFiber30Block3Chunk2ParentPath_8_ok,
    tttLargeFiber30Block3Chunk2ParentPath_9_ok,
    tttLargeFiber30Block3Chunk2ParentPath_10_ok,
    tttLargeFiber30Block3Chunk2ParentPath_11_ok,
    tttLargeFiber30Block3Chunk2ParentPath_12_ok,
    tttLargeFiber30Block3Chunk2ParentPath_13_ok,
    tttLargeFiber30Block3Chunk2ParentPath_14_ok,
    tttLargeFiber30Block3Chunk2ParentPath_15_ok]

def tttLargeFiber30Block3Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block3Chunk2SourcesCheck &&
    tttLargeFiber30Block3Chunk2RowsAudit &&
    tttLargeFiber30Block3Chunk2ParentMapAudit &&
    tttLargeFiber30Block3Chunk2ParentsAudit

theorem tttLargeFiber30Block3Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber30Block3Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block3Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block3Chunk2SourcesCheck_ok,
    tttLargeFiber30Block3Chunk2RowsAudit_ok,
    tttLargeFiber30Block3Chunk2ParentMapAudit_ok,
    tttLargeFiber30Block3Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block3Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
