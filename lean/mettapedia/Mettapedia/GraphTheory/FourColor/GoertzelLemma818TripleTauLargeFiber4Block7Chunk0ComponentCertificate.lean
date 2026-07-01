import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 7 chunk 0

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
For second-range rows it uses interval membership and explicit bounded parent
paths, avoiding broad expected-list traversal and recursive parent iteration.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block7Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block7Chunk0Sources : List Nat :=
  [4016, 4017, 4018, 4019, 4020, 4021, 4022, 4023,
   4024, 4025, 4026, 4027, 4028, 4029, 4030, 4031]

def tttLargeFiber4Row448 : TripleComponentParentRow :=
  tripleRow 4016 2176 119 72 80 64 80 80
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row449 : TripleComponentParentRow :=
  tripleRow 4017 2177 119 72 81 64 80 81
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row450 : TripleComponentParentRow :=
  tripleRow 4018 2178 119 72 82 64 80 82
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row451 : TripleComponentParentRow :=
  tripleRow 4019 2179 119 72 83 64 80 83
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row452 : TripleComponentParentRow :=
  tripleRow 4020 2180 119 72 100 64 80 100
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row453 : TripleComponentParentRow :=
  tripleRow 4021 2181 119 72 101 64 80 101
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row454 : TripleComponentParentRow :=
  tripleRow 4022 2182 119 72 102 64 80 102
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row455 : TripleComponentParentRow :=
  tripleRow 4023 2183 119 72 103 64 80 103
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row456 : TripleComponentParentRow :=
  tripleRow 4024 2184 119 73 88 64 81 88
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row457 : TripleComponentParentRow :=
  tripleRow 4025 2185 119 73 89 64 81 89
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row458 : TripleComponentParentRow :=
  tripleRow 4026 2186 119 73 90 64 81 90
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row459 : TripleComponentParentRow :=
  tripleRow 4027 2187 119 73 91 64 81 91
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row460 : TripleComponentParentRow :=
  tripleRow 4028 2188 119 73 108 64 81 108
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row461 : TripleComponentParentRow :=
  tripleRow 4029 2189 119 73 109 64 81 109
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row462 : TripleComponentParentRow :=
  tripleRow 4030 2190 119 73 110 64 81 110
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row463 : TripleComponentParentRow :=
  tripleRow 4031 2191 119 73 111 64 81 111
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Block7Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row448
  , tttLargeFiber4Row449
  , tttLargeFiber4Row450
  , tttLargeFiber4Row451
  , tttLargeFiber4Row452
  , tttLargeFiber4Row453
  , tttLargeFiber4Row454
  , tttLargeFiber4Row455
  , tttLargeFiber4Row456
  , tttLargeFiber4Row457
  , tttLargeFiber4Row458
  , tttLargeFiber4Row459
  , tttLargeFiber4Row460
  , tttLargeFiber4Row461
  , tttLargeFiber4Row462
  , tttLargeFiber4Row463
  ]

def tttLargeFiber4Block7Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (2176 <= i) && decide (i < 2432)) ||
    (decide (3824 <= i) && decide (i < 4080))

def tttLargeFiber4Block7Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber4Block7Chunk0ExpectedContains row.source &&
    tttLargeFiber4Block7Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber4Key &&
          chainInputKey tttWord t == tttLargeFiber4Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber4Block7Chunk0SourcesCheck : Bool :=
  (tttLargeFiber4Block7Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber4Block7Chunk0Sources

theorem tttLargeFiber4Block7Chunk0SourcesCheck_ok :
    tttLargeFiber4Block7Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber4Block7Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber4Block7Chunk0RowValid
    (listGetD tttLargeFiber4Block7Chunk0Rows i default)

def tttLargeFiber4Block7Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block7Chunk0Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block7Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block7Chunk0Sources 0 0 == 4016 &&
      tttLargeFiber4ParentOf 4016 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (1 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block7Chunk0Sources 1 0 == 4017 &&
      tttLargeFiber4ParentOf 4017 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (2 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block7Chunk0Sources 2 0 == 4018 &&
      tttLargeFiber4ParentOf 4018 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (2 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block7Chunk0Sources 3 0 == 4019 &&
      tttLargeFiber4ParentOf 4019 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block7Chunk0Sources 4 0 == 4020 &&
      tttLargeFiber4ParentOf 4020 == 2180 &&
      tttLargeFiber4ParentOf 2180 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block7Chunk0Sources 5 0 == 4021 &&
      tttLargeFiber4ParentOf 4021 == 2181 &&
      tttLargeFiber4ParentOf 2181 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block7Chunk0Sources 6 0 == 4022 &&
      tttLargeFiber4ParentOf 4022 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block7Chunk0Sources 7 0 == 4023 &&
      tttLargeFiber4ParentOf 4023 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (2 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block7Chunk0Sources 8 0 == 4024 &&
      tttLargeFiber4ParentOf 4024 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (2 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block7Chunk0Sources 9 0 == 4025 &&
      tttLargeFiber4ParentOf 4025 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block7Chunk0Sources 10 0 == 4026 &&
      tttLargeFiber4ParentOf 4026 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block7Chunk0Sources 11 0 == 4027 &&
      tttLargeFiber4ParentOf 4027 == 2187 &&
      tttLargeFiber4ParentOf 2187 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block7Chunk0Sources 12 0 == 4028 &&
      tttLargeFiber4ParentOf 4028 == 2188 &&
      tttLargeFiber4ParentOf 2188 == 2180 &&
      tttLargeFiber4ParentOf 2180 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block7Chunk0Sources 13 0 == 4029 &&
      tttLargeFiber4ParentOf 4029 == 2189 &&
      tttLargeFiber4ParentOf 2189 == 2181 &&
      tttLargeFiber4ParentOf 2181 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block7Chunk0Sources 14 0 == 4030 &&
      tttLargeFiber4ParentOf 4030 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block7Chunk0Sources 15 0 == 4031 &&
      tttLargeFiber4ParentOf 4031 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block7Chunk0Row_0_ok :
    tttLargeFiber4Block7Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0Row_1_ok :
    tttLargeFiber4Block7Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0Row_2_ok :
    tttLargeFiber4Block7Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0Row_3_ok :
    tttLargeFiber4Block7Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0Row_4_ok :
    tttLargeFiber4Block7Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0Row_5_ok :
    tttLargeFiber4Block7Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0Row_6_ok :
    tttLargeFiber4Block7Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0Row_7_ok :
    tttLargeFiber4Block7Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0Row_8_ok :
    tttLargeFiber4Block7Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0Row_9_ok :
    tttLargeFiber4Block7Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0Row_10_ok :
    tttLargeFiber4Block7Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0Row_11_ok :
    tttLargeFiber4Block7Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0Row_12_ok :
    tttLargeFiber4Block7Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0Row_13_ok :
    tttLargeFiber4Block7Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0Row_14_ok :
    tttLargeFiber4Block7Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0Row_15_ok :
    tttLargeFiber4Block7Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentMap_0_ok :
    tttLargeFiber4Block7Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentMap_1_ok :
    tttLargeFiber4Block7Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentMap_2_ok :
    tttLargeFiber4Block7Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentMap_3_ok :
    tttLargeFiber4Block7Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentMap_4_ok :
    tttLargeFiber4Block7Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentMap_5_ok :
    tttLargeFiber4Block7Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentMap_6_ok :
    tttLargeFiber4Block7Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentMap_7_ok :
    tttLargeFiber4Block7Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentMap_8_ok :
    tttLargeFiber4Block7Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentMap_9_ok :
    tttLargeFiber4Block7Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentMap_10_ok :
    tttLargeFiber4Block7Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentMap_11_ok :
    tttLargeFiber4Block7Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentMap_12_ok :
    tttLargeFiber4Block7Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentMap_13_ok :
    tttLargeFiber4Block7Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentMap_14_ok :
    tttLargeFiber4Block7Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentMap_15_ok :
    tttLargeFiber4Block7Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentPath_0_ok :
    tttLargeFiber4Block7Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentPath_1_ok :
    tttLargeFiber4Block7Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentPath_2_ok :
    tttLargeFiber4Block7Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentPath_3_ok :
    tttLargeFiber4Block7Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentPath_4_ok :
    tttLargeFiber4Block7Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentPath_5_ok :
    tttLargeFiber4Block7Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentPath_6_ok :
    tttLargeFiber4Block7Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentPath_7_ok :
    tttLargeFiber4Block7Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentPath_8_ok :
    tttLargeFiber4Block7Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentPath_9_ok :
    tttLargeFiber4Block7Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentPath_10_ok :
    tttLargeFiber4Block7Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentPath_11_ok :
    tttLargeFiber4Block7Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentPath_12_ok :
    tttLargeFiber4Block7Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentPath_13_ok :
    tttLargeFiber4Block7Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentPath_14_ok :
    tttLargeFiber4Block7Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block7Chunk0ParentPath_15_ok :
    tttLargeFiber4Block7Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block7Chunk0RowsAudit : Bool :=
  tttLargeFiber4Block7Chunk0RowCheck 0
    && tttLargeFiber4Block7Chunk0RowCheck 1
    && tttLargeFiber4Block7Chunk0RowCheck 2
    && tttLargeFiber4Block7Chunk0RowCheck 3
    && tttLargeFiber4Block7Chunk0RowCheck 4
    && tttLargeFiber4Block7Chunk0RowCheck 5
    && tttLargeFiber4Block7Chunk0RowCheck 6
    && tttLargeFiber4Block7Chunk0RowCheck 7
    && tttLargeFiber4Block7Chunk0RowCheck 8
    && tttLargeFiber4Block7Chunk0RowCheck 9
    && tttLargeFiber4Block7Chunk0RowCheck 10
    && tttLargeFiber4Block7Chunk0RowCheck 11
    && tttLargeFiber4Block7Chunk0RowCheck 12
    && tttLargeFiber4Block7Chunk0RowCheck 13
    && tttLargeFiber4Block7Chunk0RowCheck 14
    && tttLargeFiber4Block7Chunk0RowCheck 15

theorem tttLargeFiber4Block7Chunk0RowsAudit_ok :
    tttLargeFiber4Block7Chunk0RowsAudit = true := by
  simp [tttLargeFiber4Block7Chunk0RowsAudit,
    tttLargeFiber4Block7Chunk0Row_0_ok,
    tttLargeFiber4Block7Chunk0Row_1_ok,
    tttLargeFiber4Block7Chunk0Row_2_ok,
    tttLargeFiber4Block7Chunk0Row_3_ok,
    tttLargeFiber4Block7Chunk0Row_4_ok,
    tttLargeFiber4Block7Chunk0Row_5_ok,
    tttLargeFiber4Block7Chunk0Row_6_ok,
    tttLargeFiber4Block7Chunk0Row_7_ok,
    tttLargeFiber4Block7Chunk0Row_8_ok,
    tttLargeFiber4Block7Chunk0Row_9_ok,
    tttLargeFiber4Block7Chunk0Row_10_ok,
    tttLargeFiber4Block7Chunk0Row_11_ok,
    tttLargeFiber4Block7Chunk0Row_12_ok,
    tttLargeFiber4Block7Chunk0Row_13_ok,
    tttLargeFiber4Block7Chunk0Row_14_ok,
    tttLargeFiber4Block7Chunk0Row_15_ok]

def tttLargeFiber4Block7Chunk0ParentMapAudit : Bool :=
  tttLargeFiber4Block7Chunk0ParentMapCheck 0
    && tttLargeFiber4Block7Chunk0ParentMapCheck 1
    && tttLargeFiber4Block7Chunk0ParentMapCheck 2
    && tttLargeFiber4Block7Chunk0ParentMapCheck 3
    && tttLargeFiber4Block7Chunk0ParentMapCheck 4
    && tttLargeFiber4Block7Chunk0ParentMapCheck 5
    && tttLargeFiber4Block7Chunk0ParentMapCheck 6
    && tttLargeFiber4Block7Chunk0ParentMapCheck 7
    && tttLargeFiber4Block7Chunk0ParentMapCheck 8
    && tttLargeFiber4Block7Chunk0ParentMapCheck 9
    && tttLargeFiber4Block7Chunk0ParentMapCheck 10
    && tttLargeFiber4Block7Chunk0ParentMapCheck 11
    && tttLargeFiber4Block7Chunk0ParentMapCheck 12
    && tttLargeFiber4Block7Chunk0ParentMapCheck 13
    && tttLargeFiber4Block7Chunk0ParentMapCheck 14
    && tttLargeFiber4Block7Chunk0ParentMapCheck 15

theorem tttLargeFiber4Block7Chunk0ParentMapAudit_ok :
    tttLargeFiber4Block7Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber4Block7Chunk0ParentMapAudit,
    tttLargeFiber4Block7Chunk0ParentMap_0_ok,
    tttLargeFiber4Block7Chunk0ParentMap_1_ok,
    tttLargeFiber4Block7Chunk0ParentMap_2_ok,
    tttLargeFiber4Block7Chunk0ParentMap_3_ok,
    tttLargeFiber4Block7Chunk0ParentMap_4_ok,
    tttLargeFiber4Block7Chunk0ParentMap_5_ok,
    tttLargeFiber4Block7Chunk0ParentMap_6_ok,
    tttLargeFiber4Block7Chunk0ParentMap_7_ok,
    tttLargeFiber4Block7Chunk0ParentMap_8_ok,
    tttLargeFiber4Block7Chunk0ParentMap_9_ok,
    tttLargeFiber4Block7Chunk0ParentMap_10_ok,
    tttLargeFiber4Block7Chunk0ParentMap_11_ok,
    tttLargeFiber4Block7Chunk0ParentMap_12_ok,
    tttLargeFiber4Block7Chunk0ParentMap_13_ok,
    tttLargeFiber4Block7Chunk0ParentMap_14_ok,
    tttLargeFiber4Block7Chunk0ParentMap_15_ok]

def tttLargeFiber4Block7Chunk0ParentsAudit : Bool :=
  tttLargeFiber4Block7Chunk0ParentPathCheck 0
    && tttLargeFiber4Block7Chunk0ParentPathCheck 1
    && tttLargeFiber4Block7Chunk0ParentPathCheck 2
    && tttLargeFiber4Block7Chunk0ParentPathCheck 3
    && tttLargeFiber4Block7Chunk0ParentPathCheck 4
    && tttLargeFiber4Block7Chunk0ParentPathCheck 5
    && tttLargeFiber4Block7Chunk0ParentPathCheck 6
    && tttLargeFiber4Block7Chunk0ParentPathCheck 7
    && tttLargeFiber4Block7Chunk0ParentPathCheck 8
    && tttLargeFiber4Block7Chunk0ParentPathCheck 9
    && tttLargeFiber4Block7Chunk0ParentPathCheck 10
    && tttLargeFiber4Block7Chunk0ParentPathCheck 11
    && tttLargeFiber4Block7Chunk0ParentPathCheck 12
    && tttLargeFiber4Block7Chunk0ParentPathCheck 13
    && tttLargeFiber4Block7Chunk0ParentPathCheck 14
    && tttLargeFiber4Block7Chunk0ParentPathCheck 15

theorem tttLargeFiber4Block7Chunk0ParentsAudit_ok :
    tttLargeFiber4Block7Chunk0ParentsAudit = true := by
  simp [tttLargeFiber4Block7Chunk0ParentsAudit,
    tttLargeFiber4Block7Chunk0ParentPath_0_ok,
    tttLargeFiber4Block7Chunk0ParentPath_1_ok,
    tttLargeFiber4Block7Chunk0ParentPath_2_ok,
    tttLargeFiber4Block7Chunk0ParentPath_3_ok,
    tttLargeFiber4Block7Chunk0ParentPath_4_ok,
    tttLargeFiber4Block7Chunk0ParentPath_5_ok,
    tttLargeFiber4Block7Chunk0ParentPath_6_ok,
    tttLargeFiber4Block7Chunk0ParentPath_7_ok,
    tttLargeFiber4Block7Chunk0ParentPath_8_ok,
    tttLargeFiber4Block7Chunk0ParentPath_9_ok,
    tttLargeFiber4Block7Chunk0ParentPath_10_ok,
    tttLargeFiber4Block7Chunk0ParentPath_11_ok,
    tttLargeFiber4Block7Chunk0ParentPath_12_ok,
    tttLargeFiber4Block7Chunk0ParentPath_13_ok,
    tttLargeFiber4Block7Chunk0ParentPath_14_ok,
    tttLargeFiber4Block7Chunk0ParentPath_15_ok]

def tttLargeFiber4Block7Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block7Chunk0SourcesCheck &&
    tttLargeFiber4Block7Chunk0RowsAudit &&
    tttLargeFiber4Block7Chunk0ParentMapAudit &&
    tttLargeFiber4Block7Chunk0ParentsAudit

theorem tttLargeFiber4Block7Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber4Block7Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block7Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block7Chunk0SourcesCheck_ok,
    tttLargeFiber4Block7Chunk0RowsAudit_ok,
    tttLargeFiber4Block7Chunk0ParentMapAudit_ok,
    tttLargeFiber4Block7Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block7Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
