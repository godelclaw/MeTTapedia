import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 3 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block3Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block3Chunk3Sources : List Nat :=
  [   240, 241, 242, 243, 244, 245, 246, 247,
   248, 249, 250, 251, 252, 253, 254, 255]

def tttLargeFiber30Row240 : TripleComponentParentRow :=
  tripleRow 240 112 3 42 0 1 110 64
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

def tttLargeFiber30Row241 : TripleComponentParentRow :=
  tripleRow 241 113 3 42 1 1 110 65
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

def tttLargeFiber30Row242 : TripleComponentParentRow :=
  tripleRow 242 114 3 42 2 1 110 66
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

def tttLargeFiber30Row243 : TripleComponentParentRow :=
  tripleRow 243 115 3 42 3 1 110 67
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

def tttLargeFiber30Row244 : TripleComponentParentRow :=
  tripleRow 244 240 3 42 48 3 42 0
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row245 : TripleComponentParentRow :=
  tripleRow 245 241 3 42 49 3 42 1
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row246 : TripleComponentParentRow :=
  tripleRow 246 118 3 42 50 1 110 118
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

def tttLargeFiber30Row247 : TripleComponentParentRow :=
  tripleRow 247 119 3 42 51 1 110 119
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

def tttLargeFiber30Row248 : TripleComponentParentRow :=
  tripleRow 248 120 3 43 8 1 111 72
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

def tttLargeFiber30Row249 : TripleComponentParentRow :=
  tripleRow 249 121 3 43 9 1 111 73
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

def tttLargeFiber30Row250 : TripleComponentParentRow :=
  tripleRow 250 122 3 43 10 1 111 74
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

def tttLargeFiber30Row251 : TripleComponentParentRow :=
  tripleRow 251 123 3 43 11 1 111 75
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

def tttLargeFiber30Row252 : TripleComponentParentRow :=
  tripleRow 252 248 3 43 56 3 43 8
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row253 : TripleComponentParentRow :=
  tripleRow 253 249 3 43 57 3 43 9
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber30Row254 : TripleComponentParentRow :=
  tripleRow 254 126 3 43 58 1 111 126
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

def tttLargeFiber30Row255 : TripleComponentParentRow :=
  tripleRow 255 127 3 43 59 1 111 127
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

def tttLargeFiber30Block3Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row240
  , tttLargeFiber30Row241
  , tttLargeFiber30Row242
  , tttLargeFiber30Row243
  , tttLargeFiber30Row244
  , tttLargeFiber30Row245
  , tttLargeFiber30Row246
  , tttLargeFiber30Row247
  , tttLargeFiber30Row248
  , tttLargeFiber30Row249
  , tttLargeFiber30Row250
  , tttLargeFiber30Row251
  , tttLargeFiber30Row252
  , tttLargeFiber30Row253
  , tttLargeFiber30Row254
  , tttLargeFiber30Row255
  ]

def tttLargeFiber30Block3Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block3Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block3Chunk3ExpectedContains row.source &&
    tttLargeFiber30Block3Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block3Chunk3SourcesCheck : Bool :=
  (tttLargeFiber30Block3Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber30Block3Chunk3Sources

theorem tttLargeFiber30Block3Chunk3SourcesCheck_ok :
    tttLargeFiber30Block3Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber30Block3Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block3Chunk3RowValid
    (listGetD tttLargeFiber30Block3Chunk3Rows i default)

def tttLargeFiber30Block3Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block3Chunk3Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block3Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block3Chunk3Sources 0 0 == 240
      && tttLargeFiber30ParentOf 240 == 112
      && tttLargeFiber30ParentOf 112 == 48
      && tttLargeFiber30ParentOf 48 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block3Chunk3Sources 1 0 == 241
      && tttLargeFiber30ParentOf 241 == 113
      && tttLargeFiber30ParentOf 113 == 49
      && tttLargeFiber30ParentOf 49 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block3Chunk3Sources 2 0 == 242
      && tttLargeFiber30ParentOf 242 == 114
      && tttLargeFiber30ParentOf 114 == 50
      && tttLargeFiber30ParentOf 50 == 10
      && tttLargeFiber30ParentOf 10 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block3Chunk3Sources 3 0 == 243
      && tttLargeFiber30ParentOf 243 == 115
      && tttLargeFiber30ParentOf 115 == 51
      && tttLargeFiber30ParentOf 51 == 11
      && tttLargeFiber30ParentOf 11 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (6 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block3Chunk3Sources 4 0 == 244
      && tttLargeFiber30ParentOf 244 == 240
      && tttLargeFiber30ParentOf 240 == 112
      && tttLargeFiber30ParentOf 112 == 48
      && tttLargeFiber30ParentOf 48 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block3Chunk3Sources 5 0 == 245
      && tttLargeFiber30ParentOf 245 == 241
      && tttLargeFiber30ParentOf 241 == 113
      && tttLargeFiber30ParentOf 113 == 49
      && tttLargeFiber30ParentOf 49 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (6 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block3Chunk3Sources 6 0 == 246
      && tttLargeFiber30ParentOf 246 == 118
      && tttLargeFiber30ParentOf 118 == 54
      && tttLargeFiber30ParentOf 54 == 14
      && tttLargeFiber30ParentOf 14 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (6 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block3Chunk3Sources 7 0 == 247
      && tttLargeFiber30ParentOf 247 == 119
      && tttLargeFiber30ParentOf 119 == 55
      && tttLargeFiber30ParentOf 55 == 15
      && tttLargeFiber30ParentOf 15 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block3Chunk3Sources 8 0 == 248
      && tttLargeFiber30ParentOf 248 == 120
      && tttLargeFiber30ParentOf 120 == 56
      && tttLargeFiber30ParentOf 56 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block3Chunk3Sources 9 0 == 249
      && tttLargeFiber30ParentOf 249 == 121
      && tttLargeFiber30ParentOf 121 == 57
      && tttLargeFiber30ParentOf 57 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block3Chunk3Sources 10 0 == 250
      && tttLargeFiber30ParentOf 250 == 122
      && tttLargeFiber30ParentOf 122 == 58
      && tttLargeFiber30ParentOf 58 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block3Chunk3Sources 11 0 == 251
      && tttLargeFiber30ParentOf 251 == 123
      && tttLargeFiber30ParentOf 123 == 59
      && tttLargeFiber30ParentOf 59 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block3Chunk3Sources 12 0 == 252
      && tttLargeFiber30ParentOf 252 == 248
      && tttLargeFiber30ParentOf 248 == 120
      && tttLargeFiber30ParentOf 120 == 56
      && tttLargeFiber30ParentOf 56 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block3Chunk3Sources 13 0 == 253
      && tttLargeFiber30ParentOf 253 == 249
      && tttLargeFiber30ParentOf 249 == 121
      && tttLargeFiber30ParentOf 121 == 57
      && tttLargeFiber30ParentOf 57 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block3Chunk3Sources 14 0 == 254
      && tttLargeFiber30ParentOf 254 == 126
      && tttLargeFiber30ParentOf 126 == 62
      && tttLargeFiber30ParentOf 62 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (5 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block3Chunk3Sources 15 0 == 255
      && tttLargeFiber30ParentOf 255 == 127
      && tttLargeFiber30ParentOf 127 == 63
      && tttLargeFiber30ParentOf 63 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block3Chunk3Row_0_ok :
    tttLargeFiber30Block3Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3Row_1_ok :
    tttLargeFiber30Block3Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3Row_2_ok :
    tttLargeFiber30Block3Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3Row_3_ok :
    tttLargeFiber30Block3Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3Row_4_ok :
    tttLargeFiber30Block3Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3Row_5_ok :
    tttLargeFiber30Block3Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3Row_6_ok :
    tttLargeFiber30Block3Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3Row_7_ok :
    tttLargeFiber30Block3Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3Row_8_ok :
    tttLargeFiber30Block3Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3Row_9_ok :
    tttLargeFiber30Block3Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3Row_10_ok :
    tttLargeFiber30Block3Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3Row_11_ok :
    tttLargeFiber30Block3Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3Row_12_ok :
    tttLargeFiber30Block3Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3Row_13_ok :
    tttLargeFiber30Block3Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3Row_14_ok :
    tttLargeFiber30Block3Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3Row_15_ok :
    tttLargeFiber30Block3Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentMap_0_ok :
    tttLargeFiber30Block3Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentMap_1_ok :
    tttLargeFiber30Block3Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentMap_2_ok :
    tttLargeFiber30Block3Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentMap_3_ok :
    tttLargeFiber30Block3Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentMap_4_ok :
    tttLargeFiber30Block3Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentMap_5_ok :
    tttLargeFiber30Block3Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentMap_6_ok :
    tttLargeFiber30Block3Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentMap_7_ok :
    tttLargeFiber30Block3Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentMap_8_ok :
    tttLargeFiber30Block3Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentMap_9_ok :
    tttLargeFiber30Block3Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentMap_10_ok :
    tttLargeFiber30Block3Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentMap_11_ok :
    tttLargeFiber30Block3Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentMap_12_ok :
    tttLargeFiber30Block3Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentMap_13_ok :
    tttLargeFiber30Block3Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentMap_14_ok :
    tttLargeFiber30Block3Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentMap_15_ok :
    tttLargeFiber30Block3Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentPath_0_ok :
    tttLargeFiber30Block3Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentPath_1_ok :
    tttLargeFiber30Block3Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentPath_2_ok :
    tttLargeFiber30Block3Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentPath_3_ok :
    tttLargeFiber30Block3Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentPath_4_ok :
    tttLargeFiber30Block3Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentPath_5_ok :
    tttLargeFiber30Block3Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentPath_6_ok :
    tttLargeFiber30Block3Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentPath_7_ok :
    tttLargeFiber30Block3Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentPath_8_ok :
    tttLargeFiber30Block3Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentPath_9_ok :
    tttLargeFiber30Block3Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentPath_10_ok :
    tttLargeFiber30Block3Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentPath_11_ok :
    tttLargeFiber30Block3Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentPath_12_ok :
    tttLargeFiber30Block3Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentPath_13_ok :
    tttLargeFiber30Block3Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentPath_14_ok :
    tttLargeFiber30Block3Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block3Chunk3ParentPath_15_ok :
    tttLargeFiber30Block3Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block3Chunk3RowsAudit : Bool :=
  tttLargeFiber30Block3Chunk3RowCheck 0
    && tttLargeFiber30Block3Chunk3RowCheck 1
    && tttLargeFiber30Block3Chunk3RowCheck 2
    && tttLargeFiber30Block3Chunk3RowCheck 3
    && tttLargeFiber30Block3Chunk3RowCheck 4
    && tttLargeFiber30Block3Chunk3RowCheck 5
    && tttLargeFiber30Block3Chunk3RowCheck 6
    && tttLargeFiber30Block3Chunk3RowCheck 7
    && tttLargeFiber30Block3Chunk3RowCheck 8
    && tttLargeFiber30Block3Chunk3RowCheck 9
    && tttLargeFiber30Block3Chunk3RowCheck 10
    && tttLargeFiber30Block3Chunk3RowCheck 11
    && tttLargeFiber30Block3Chunk3RowCheck 12
    && tttLargeFiber30Block3Chunk3RowCheck 13
    && tttLargeFiber30Block3Chunk3RowCheck 14
    && tttLargeFiber30Block3Chunk3RowCheck 15

theorem tttLargeFiber30Block3Chunk3RowsAudit_ok :
    tttLargeFiber30Block3Chunk3RowsAudit = true := by
  simp [tttLargeFiber30Block3Chunk3RowsAudit,
    tttLargeFiber30Block3Chunk3Row_0_ok,
    tttLargeFiber30Block3Chunk3Row_1_ok,
    tttLargeFiber30Block3Chunk3Row_2_ok,
    tttLargeFiber30Block3Chunk3Row_3_ok,
    tttLargeFiber30Block3Chunk3Row_4_ok,
    tttLargeFiber30Block3Chunk3Row_5_ok,
    tttLargeFiber30Block3Chunk3Row_6_ok,
    tttLargeFiber30Block3Chunk3Row_7_ok,
    tttLargeFiber30Block3Chunk3Row_8_ok,
    tttLargeFiber30Block3Chunk3Row_9_ok,
    tttLargeFiber30Block3Chunk3Row_10_ok,
    tttLargeFiber30Block3Chunk3Row_11_ok,
    tttLargeFiber30Block3Chunk3Row_12_ok,
    tttLargeFiber30Block3Chunk3Row_13_ok,
    tttLargeFiber30Block3Chunk3Row_14_ok,
    tttLargeFiber30Block3Chunk3Row_15_ok]

def tttLargeFiber30Block3Chunk3ParentMapAudit : Bool :=
  tttLargeFiber30Block3Chunk3ParentMapCheck 0
    && tttLargeFiber30Block3Chunk3ParentMapCheck 1
    && tttLargeFiber30Block3Chunk3ParentMapCheck 2
    && tttLargeFiber30Block3Chunk3ParentMapCheck 3
    && tttLargeFiber30Block3Chunk3ParentMapCheck 4
    && tttLargeFiber30Block3Chunk3ParentMapCheck 5
    && tttLargeFiber30Block3Chunk3ParentMapCheck 6
    && tttLargeFiber30Block3Chunk3ParentMapCheck 7
    && tttLargeFiber30Block3Chunk3ParentMapCheck 8
    && tttLargeFiber30Block3Chunk3ParentMapCheck 9
    && tttLargeFiber30Block3Chunk3ParentMapCheck 10
    && tttLargeFiber30Block3Chunk3ParentMapCheck 11
    && tttLargeFiber30Block3Chunk3ParentMapCheck 12
    && tttLargeFiber30Block3Chunk3ParentMapCheck 13
    && tttLargeFiber30Block3Chunk3ParentMapCheck 14
    && tttLargeFiber30Block3Chunk3ParentMapCheck 15

theorem tttLargeFiber30Block3Chunk3ParentMapAudit_ok :
    tttLargeFiber30Block3Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber30Block3Chunk3ParentMapAudit,
    tttLargeFiber30Block3Chunk3ParentMap_0_ok,
    tttLargeFiber30Block3Chunk3ParentMap_1_ok,
    tttLargeFiber30Block3Chunk3ParentMap_2_ok,
    tttLargeFiber30Block3Chunk3ParentMap_3_ok,
    tttLargeFiber30Block3Chunk3ParentMap_4_ok,
    tttLargeFiber30Block3Chunk3ParentMap_5_ok,
    tttLargeFiber30Block3Chunk3ParentMap_6_ok,
    tttLargeFiber30Block3Chunk3ParentMap_7_ok,
    tttLargeFiber30Block3Chunk3ParentMap_8_ok,
    tttLargeFiber30Block3Chunk3ParentMap_9_ok,
    tttLargeFiber30Block3Chunk3ParentMap_10_ok,
    tttLargeFiber30Block3Chunk3ParentMap_11_ok,
    tttLargeFiber30Block3Chunk3ParentMap_12_ok,
    tttLargeFiber30Block3Chunk3ParentMap_13_ok,
    tttLargeFiber30Block3Chunk3ParentMap_14_ok,
    tttLargeFiber30Block3Chunk3ParentMap_15_ok]

def tttLargeFiber30Block3Chunk3ParentsAudit : Bool :=
  tttLargeFiber30Block3Chunk3ParentPathCheck 0
    && tttLargeFiber30Block3Chunk3ParentPathCheck 1
    && tttLargeFiber30Block3Chunk3ParentPathCheck 2
    && tttLargeFiber30Block3Chunk3ParentPathCheck 3
    && tttLargeFiber30Block3Chunk3ParentPathCheck 4
    && tttLargeFiber30Block3Chunk3ParentPathCheck 5
    && tttLargeFiber30Block3Chunk3ParentPathCheck 6
    && tttLargeFiber30Block3Chunk3ParentPathCheck 7
    && tttLargeFiber30Block3Chunk3ParentPathCheck 8
    && tttLargeFiber30Block3Chunk3ParentPathCheck 9
    && tttLargeFiber30Block3Chunk3ParentPathCheck 10
    && tttLargeFiber30Block3Chunk3ParentPathCheck 11
    && tttLargeFiber30Block3Chunk3ParentPathCheck 12
    && tttLargeFiber30Block3Chunk3ParentPathCheck 13
    && tttLargeFiber30Block3Chunk3ParentPathCheck 14
    && tttLargeFiber30Block3Chunk3ParentPathCheck 15

theorem tttLargeFiber30Block3Chunk3ParentsAudit_ok :
    tttLargeFiber30Block3Chunk3ParentsAudit = true := by
  simp [tttLargeFiber30Block3Chunk3ParentsAudit,
    tttLargeFiber30Block3Chunk3ParentPath_0_ok,
    tttLargeFiber30Block3Chunk3ParentPath_1_ok,
    tttLargeFiber30Block3Chunk3ParentPath_2_ok,
    tttLargeFiber30Block3Chunk3ParentPath_3_ok,
    tttLargeFiber30Block3Chunk3ParentPath_4_ok,
    tttLargeFiber30Block3Chunk3ParentPath_5_ok,
    tttLargeFiber30Block3Chunk3ParentPath_6_ok,
    tttLargeFiber30Block3Chunk3ParentPath_7_ok,
    tttLargeFiber30Block3Chunk3ParentPath_8_ok,
    tttLargeFiber30Block3Chunk3ParentPath_9_ok,
    tttLargeFiber30Block3Chunk3ParentPath_10_ok,
    tttLargeFiber30Block3Chunk3ParentPath_11_ok,
    tttLargeFiber30Block3Chunk3ParentPath_12_ok,
    tttLargeFiber30Block3Chunk3ParentPath_13_ok,
    tttLargeFiber30Block3Chunk3ParentPath_14_ok,
    tttLargeFiber30Block3Chunk3ParentPath_15_ok]

def tttLargeFiber30Block3Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block3Chunk3SourcesCheck &&
    tttLargeFiber30Block3Chunk3RowsAudit &&
    tttLargeFiber30Block3Chunk3ParentMapAudit &&
    tttLargeFiber30Block3Chunk3ParentsAudit

theorem tttLargeFiber30Block3Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber30Block3Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block3Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block3Chunk3SourcesCheck_ok,
    tttLargeFiber30Block3Chunk3RowsAudit_ok,
    tttLargeFiber30Block3Chunk3ParentMapAudit_ok,
    tttLargeFiber30Block3Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block3Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
