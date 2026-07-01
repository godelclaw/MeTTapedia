import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 30, block 2 chunk 0

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber30Block2Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber30Data

def tttLargeFiber30Block2Chunk0Sources : List Nat :=
  [   128, 129, 130, 131, 132, 133, 134, 135,
   136, 137, 138, 139, 140, 141, 142, 143]

def tttLargeFiber30Row128 : TripleComponentParentRow :=
  tripleRow 128 0 2 16 80 0 80 80
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row129 : TripleComponentParentRow :=
  tripleRow 129 1 2 16 81 0 80 81
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row130 : TripleComponentParentRow :=
  tripleRow 130 2 2 16 82 0 80 82
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row131 : TripleComponentParentRow :=
  tripleRow 131 3 2 16 83 0 80 83
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row132 : TripleComponentParentRow :=
  tripleRow 132 4 2 16 100 0 80 100
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row133 : TripleComponentParentRow :=
  tripleRow 133 5 2 16 101 0 80 101
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row134 : TripleComponentParentRow :=
  tripleRow 134 6 2 16 102 0 80 102
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row135 : TripleComponentParentRow :=
  tripleRow 135 7 2 16 103 0 80 103
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row136 : TripleComponentParentRow :=
  tripleRow 136 8 2 17 88 0 81 88
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row137 : TripleComponentParentRow :=
  tripleRow 137 9 2 17 89 0 81 89
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row138 : TripleComponentParentRow :=
  tripleRow 138 10 2 17 90 0 81 90
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row139 : TripleComponentParentRow :=
  tripleRow 139 11 2 17 91 0 81 91
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row140 : TripleComponentParentRow :=
  tripleRow 140 12 2 17 108 0 81 108
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row141 : TripleComponentParentRow :=
  tripleRow 141 13 2 17 109 0 81 109
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row142 : TripleComponentParentRow :=
  tripleRow 142 14 2 17 110 0 81 110
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Row143 : TripleComponentParentRow :=
  tripleRow 143 15 2 17 111 0 81 111
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber30Block2Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber30Row128
  , tttLargeFiber30Row129
  , tttLargeFiber30Row130
  , tttLargeFiber30Row131
  , tttLargeFiber30Row132
  , tttLargeFiber30Row133
  , tttLargeFiber30Row134
  , tttLargeFiber30Row135
  , tttLargeFiber30Row136
  , tttLargeFiber30Row137
  , tttLargeFiber30Row138
  , tttLargeFiber30Row139
  , tttLargeFiber30Row140
  , tttLargeFiber30Row141
  , tttLargeFiber30Row142
  , tttLargeFiber30Row143
  ]

def tttLargeFiber30Block2Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (0 <= i) && decide (i < 256)) ||
    (decide (1632 <= i) && decide (i < 1888))

def tttLargeFiber30Block2Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber30Block2Chunk0ExpectedContains row.source &&
    tttLargeFiber30Block2Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber30Key &&
          chainInputKey tttWord t == tttLargeFiber30Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber30Block2Chunk0SourcesCheck : Bool :=
  (tttLargeFiber30Block2Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber30Block2Chunk0Sources

theorem tttLargeFiber30Block2Chunk0SourcesCheck_ok :
    tttLargeFiber30Block2Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber30Block2Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber30Block2Chunk0RowValid
    (listGetD tttLargeFiber30Block2Chunk0Rows i default)

def tttLargeFiber30Block2Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber30Block2Chunk0Rows i default
  row.parent == tttLargeFiber30ParentOf row.source

def tttLargeFiber30Block2Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber30Block2Chunk0Sources 0 0 == 128
      && tttLargeFiber30ParentOf 128 == 0
      && 0 == tttLargeFiber30Root
      && decide (1 <= tttLargeFiber30MaxParentDepth)
  | 1 => listGetD tttLargeFiber30Block2Chunk0Sources 1 0 == 129
      && tttLargeFiber30ParentOf 129 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 2 => listGetD tttLargeFiber30Block2Chunk0Sources 2 0 == 130
      && tttLargeFiber30ParentOf 130 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 3 => listGetD tttLargeFiber30Block2Chunk0Sources 3 0 == 131
      && tttLargeFiber30ParentOf 131 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 4 => listGetD tttLargeFiber30Block2Chunk0Sources 4 0 == 132
      && tttLargeFiber30ParentOf 132 == 4
      && tttLargeFiber30ParentOf 4 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 5 => listGetD tttLargeFiber30Block2Chunk0Sources 5 0 == 133
      && tttLargeFiber30ParentOf 133 == 5
      && tttLargeFiber30ParentOf 5 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 6 => listGetD tttLargeFiber30Block2Chunk0Sources 6 0 == 134
      && tttLargeFiber30ParentOf 134 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 7 => listGetD tttLargeFiber30Block2Chunk0Sources 7 0 == 135
      && tttLargeFiber30ParentOf 135 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 8 => listGetD tttLargeFiber30Block2Chunk0Sources 8 0 == 136
      && tttLargeFiber30ParentOf 136 == 8
      && tttLargeFiber30ParentOf 8 == 0
      && 0 == tttLargeFiber30Root
      && decide (2 <= tttLargeFiber30MaxParentDepth)
  | 9 => listGetD tttLargeFiber30Block2Chunk0Sources 9 0 == 137
      && tttLargeFiber30ParentOf 137 == 9
      && tttLargeFiber30ParentOf 9 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 10 => listGetD tttLargeFiber30Block2Chunk0Sources 10 0 == 138
      && tttLargeFiber30ParentOf 138 == 10
      && tttLargeFiber30ParentOf 10 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | 11 => listGetD tttLargeFiber30Block2Chunk0Sources 11 0 == 139
      && tttLargeFiber30ParentOf 139 == 11
      && tttLargeFiber30ParentOf 11 == 3
      && tttLargeFiber30ParentOf 3 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 12 => listGetD tttLargeFiber30Block2Chunk0Sources 12 0 == 140
      && tttLargeFiber30ParentOf 140 == 12
      && tttLargeFiber30ParentOf 12 == 4
      && tttLargeFiber30ParentOf 4 == 2
      && tttLargeFiber30ParentOf 2 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 13 => listGetD tttLargeFiber30Block2Chunk0Sources 13 0 == 141
      && tttLargeFiber30ParentOf 141 == 13
      && tttLargeFiber30ParentOf 13 == 5
      && tttLargeFiber30ParentOf 5 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 14 => listGetD tttLargeFiber30Block2Chunk0Sources 14 0 == 142
      && tttLargeFiber30ParentOf 142 == 14
      && tttLargeFiber30ParentOf 14 == 6
      && tttLargeFiber30ParentOf 6 == 1
      && tttLargeFiber30ParentOf 1 == 0
      && 0 == tttLargeFiber30Root
      && decide (4 <= tttLargeFiber30MaxParentDepth)
  | 15 => listGetD tttLargeFiber30Block2Chunk0Sources 15 0 == 143
      && tttLargeFiber30ParentOf 143 == 15
      && tttLargeFiber30ParentOf 15 == 7
      && tttLargeFiber30ParentOf 7 == 0
      && 0 == tttLargeFiber30Root
      && decide (3 <= tttLargeFiber30MaxParentDepth)
  | _ => false

theorem tttLargeFiber30Block2Chunk0Row_0_ok :
    tttLargeFiber30Block2Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0Row_1_ok :
    tttLargeFiber30Block2Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0Row_2_ok :
    tttLargeFiber30Block2Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0Row_3_ok :
    tttLargeFiber30Block2Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0Row_4_ok :
    tttLargeFiber30Block2Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0Row_5_ok :
    tttLargeFiber30Block2Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0Row_6_ok :
    tttLargeFiber30Block2Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0Row_7_ok :
    tttLargeFiber30Block2Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0Row_8_ok :
    tttLargeFiber30Block2Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0Row_9_ok :
    tttLargeFiber30Block2Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0Row_10_ok :
    tttLargeFiber30Block2Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0Row_11_ok :
    tttLargeFiber30Block2Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0Row_12_ok :
    tttLargeFiber30Block2Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0Row_13_ok :
    tttLargeFiber30Block2Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0Row_14_ok :
    tttLargeFiber30Block2Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0Row_15_ok :
    tttLargeFiber30Block2Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentMap_0_ok :
    tttLargeFiber30Block2Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentMap_1_ok :
    tttLargeFiber30Block2Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentMap_2_ok :
    tttLargeFiber30Block2Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentMap_3_ok :
    tttLargeFiber30Block2Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentMap_4_ok :
    tttLargeFiber30Block2Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentMap_5_ok :
    tttLargeFiber30Block2Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentMap_6_ok :
    tttLargeFiber30Block2Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentMap_7_ok :
    tttLargeFiber30Block2Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentMap_8_ok :
    tttLargeFiber30Block2Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentMap_9_ok :
    tttLargeFiber30Block2Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentMap_10_ok :
    tttLargeFiber30Block2Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentMap_11_ok :
    tttLargeFiber30Block2Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentMap_12_ok :
    tttLargeFiber30Block2Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentMap_13_ok :
    tttLargeFiber30Block2Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentMap_14_ok :
    tttLargeFiber30Block2Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentMap_15_ok :
    tttLargeFiber30Block2Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentPath_0_ok :
    tttLargeFiber30Block2Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentPath_1_ok :
    tttLargeFiber30Block2Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentPath_2_ok :
    tttLargeFiber30Block2Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentPath_3_ok :
    tttLargeFiber30Block2Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentPath_4_ok :
    tttLargeFiber30Block2Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentPath_5_ok :
    tttLargeFiber30Block2Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentPath_6_ok :
    tttLargeFiber30Block2Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentPath_7_ok :
    tttLargeFiber30Block2Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentPath_8_ok :
    tttLargeFiber30Block2Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentPath_9_ok :
    tttLargeFiber30Block2Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentPath_10_ok :
    tttLargeFiber30Block2Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentPath_11_ok :
    tttLargeFiber30Block2Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentPath_12_ok :
    tttLargeFiber30Block2Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentPath_13_ok :
    tttLargeFiber30Block2Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentPath_14_ok :
    tttLargeFiber30Block2Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber30Block2Chunk0ParentPath_15_ok :
    tttLargeFiber30Block2Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber30Block2Chunk0RowsAudit : Bool :=
  tttLargeFiber30Block2Chunk0RowCheck 0
    && tttLargeFiber30Block2Chunk0RowCheck 1
    && tttLargeFiber30Block2Chunk0RowCheck 2
    && tttLargeFiber30Block2Chunk0RowCheck 3
    && tttLargeFiber30Block2Chunk0RowCheck 4
    && tttLargeFiber30Block2Chunk0RowCheck 5
    && tttLargeFiber30Block2Chunk0RowCheck 6
    && tttLargeFiber30Block2Chunk0RowCheck 7
    && tttLargeFiber30Block2Chunk0RowCheck 8
    && tttLargeFiber30Block2Chunk0RowCheck 9
    && tttLargeFiber30Block2Chunk0RowCheck 10
    && tttLargeFiber30Block2Chunk0RowCheck 11
    && tttLargeFiber30Block2Chunk0RowCheck 12
    && tttLargeFiber30Block2Chunk0RowCheck 13
    && tttLargeFiber30Block2Chunk0RowCheck 14
    && tttLargeFiber30Block2Chunk0RowCheck 15

theorem tttLargeFiber30Block2Chunk0RowsAudit_ok :
    tttLargeFiber30Block2Chunk0RowsAudit = true := by
  simp [tttLargeFiber30Block2Chunk0RowsAudit,
    tttLargeFiber30Block2Chunk0Row_0_ok,
    tttLargeFiber30Block2Chunk0Row_1_ok,
    tttLargeFiber30Block2Chunk0Row_2_ok,
    tttLargeFiber30Block2Chunk0Row_3_ok,
    tttLargeFiber30Block2Chunk0Row_4_ok,
    tttLargeFiber30Block2Chunk0Row_5_ok,
    tttLargeFiber30Block2Chunk0Row_6_ok,
    tttLargeFiber30Block2Chunk0Row_7_ok,
    tttLargeFiber30Block2Chunk0Row_8_ok,
    tttLargeFiber30Block2Chunk0Row_9_ok,
    tttLargeFiber30Block2Chunk0Row_10_ok,
    tttLargeFiber30Block2Chunk0Row_11_ok,
    tttLargeFiber30Block2Chunk0Row_12_ok,
    tttLargeFiber30Block2Chunk0Row_13_ok,
    tttLargeFiber30Block2Chunk0Row_14_ok,
    tttLargeFiber30Block2Chunk0Row_15_ok]

def tttLargeFiber30Block2Chunk0ParentMapAudit : Bool :=
  tttLargeFiber30Block2Chunk0ParentMapCheck 0
    && tttLargeFiber30Block2Chunk0ParentMapCheck 1
    && tttLargeFiber30Block2Chunk0ParentMapCheck 2
    && tttLargeFiber30Block2Chunk0ParentMapCheck 3
    && tttLargeFiber30Block2Chunk0ParentMapCheck 4
    && tttLargeFiber30Block2Chunk0ParentMapCheck 5
    && tttLargeFiber30Block2Chunk0ParentMapCheck 6
    && tttLargeFiber30Block2Chunk0ParentMapCheck 7
    && tttLargeFiber30Block2Chunk0ParentMapCheck 8
    && tttLargeFiber30Block2Chunk0ParentMapCheck 9
    && tttLargeFiber30Block2Chunk0ParentMapCheck 10
    && tttLargeFiber30Block2Chunk0ParentMapCheck 11
    && tttLargeFiber30Block2Chunk0ParentMapCheck 12
    && tttLargeFiber30Block2Chunk0ParentMapCheck 13
    && tttLargeFiber30Block2Chunk0ParentMapCheck 14
    && tttLargeFiber30Block2Chunk0ParentMapCheck 15

theorem tttLargeFiber30Block2Chunk0ParentMapAudit_ok :
    tttLargeFiber30Block2Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber30Block2Chunk0ParentMapAudit,
    tttLargeFiber30Block2Chunk0ParentMap_0_ok,
    tttLargeFiber30Block2Chunk0ParentMap_1_ok,
    tttLargeFiber30Block2Chunk0ParentMap_2_ok,
    tttLargeFiber30Block2Chunk0ParentMap_3_ok,
    tttLargeFiber30Block2Chunk0ParentMap_4_ok,
    tttLargeFiber30Block2Chunk0ParentMap_5_ok,
    tttLargeFiber30Block2Chunk0ParentMap_6_ok,
    tttLargeFiber30Block2Chunk0ParentMap_7_ok,
    tttLargeFiber30Block2Chunk0ParentMap_8_ok,
    tttLargeFiber30Block2Chunk0ParentMap_9_ok,
    tttLargeFiber30Block2Chunk0ParentMap_10_ok,
    tttLargeFiber30Block2Chunk0ParentMap_11_ok,
    tttLargeFiber30Block2Chunk0ParentMap_12_ok,
    tttLargeFiber30Block2Chunk0ParentMap_13_ok,
    tttLargeFiber30Block2Chunk0ParentMap_14_ok,
    tttLargeFiber30Block2Chunk0ParentMap_15_ok]

def tttLargeFiber30Block2Chunk0ParentsAudit : Bool :=
  tttLargeFiber30Block2Chunk0ParentPathCheck 0
    && tttLargeFiber30Block2Chunk0ParentPathCheck 1
    && tttLargeFiber30Block2Chunk0ParentPathCheck 2
    && tttLargeFiber30Block2Chunk0ParentPathCheck 3
    && tttLargeFiber30Block2Chunk0ParentPathCheck 4
    && tttLargeFiber30Block2Chunk0ParentPathCheck 5
    && tttLargeFiber30Block2Chunk0ParentPathCheck 6
    && tttLargeFiber30Block2Chunk0ParentPathCheck 7
    && tttLargeFiber30Block2Chunk0ParentPathCheck 8
    && tttLargeFiber30Block2Chunk0ParentPathCheck 9
    && tttLargeFiber30Block2Chunk0ParentPathCheck 10
    && tttLargeFiber30Block2Chunk0ParentPathCheck 11
    && tttLargeFiber30Block2Chunk0ParentPathCheck 12
    && tttLargeFiber30Block2Chunk0ParentPathCheck 13
    && tttLargeFiber30Block2Chunk0ParentPathCheck 14
    && tttLargeFiber30Block2Chunk0ParentPathCheck 15

theorem tttLargeFiber30Block2Chunk0ParentsAudit_ok :
    tttLargeFiber30Block2Chunk0ParentsAudit = true := by
  simp [tttLargeFiber30Block2Chunk0ParentsAudit,
    tttLargeFiber30Block2Chunk0ParentPath_0_ok,
    tttLargeFiber30Block2Chunk0ParentPath_1_ok,
    tttLargeFiber30Block2Chunk0ParentPath_2_ok,
    tttLargeFiber30Block2Chunk0ParentPath_3_ok,
    tttLargeFiber30Block2Chunk0ParentPath_4_ok,
    tttLargeFiber30Block2Chunk0ParentPath_5_ok,
    tttLargeFiber30Block2Chunk0ParentPath_6_ok,
    tttLargeFiber30Block2Chunk0ParentPath_7_ok,
    tttLargeFiber30Block2Chunk0ParentPath_8_ok,
    tttLargeFiber30Block2Chunk0ParentPath_9_ok,
    tttLargeFiber30Block2Chunk0ParentPath_10_ok,
    tttLargeFiber30Block2Chunk0ParentPath_11_ok,
    tttLargeFiber30Block2Chunk0ParentPath_12_ok,
    tttLargeFiber30Block2Chunk0ParentPath_13_ok,
    tttLargeFiber30Block2Chunk0ParentPath_14_ok,
    tttLargeFiber30Block2Chunk0ParentPath_15_ok]

def tttLargeFiber30Block2Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber30CountsAudit &&
    tttLargeFiber30Block2Chunk0SourcesCheck &&
    tttLargeFiber30Block2Chunk0RowsAudit &&
    tttLargeFiber30Block2Chunk0ParentMapAudit &&
    tttLargeFiber30Block2Chunk0ParentsAudit

theorem tttLargeFiber30Block2Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber30Block2Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber30Block2Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber30CountsAudit_ok,
    tttLargeFiber30Block2Chunk0SourcesCheck_ok,
    tttLargeFiber30Block2Chunk0RowsAudit_ok,
    tttLargeFiber30Block2Chunk0ParentMapAudit_ok,
    tttLargeFiber30Block2Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber30Block2Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
