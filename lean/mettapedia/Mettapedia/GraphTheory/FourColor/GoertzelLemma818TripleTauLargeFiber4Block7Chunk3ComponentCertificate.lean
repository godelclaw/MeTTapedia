import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 7 chunk 3

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
For second-range rows it uses interval membership and explicit bounded parent
paths, avoiding broad expected-list traversal and recursive parent iteration.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block7Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block7Chunk3Sources : List Nat :=
  [4064, 4065, 4066, 4067, 4068, 4069, 4070, 4071,
   4072, 4073, 4074, 4075, 4076, 4077, 4078, 4079]

def tttLargeFiber4Row496 : TripleComponentParentRow :=
  tripleRow 4064 2224 119 126 64 64 102 64
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row497 : TripleComponentParentRow :=
  tripleRow 4065 2225 119 126 65 64 102 65
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row498 : TripleComponentParentRow :=
  tripleRow 4066 2226 119 126 66 64 102 66
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row499 : TripleComponentParentRow :=
  tripleRow 4067 2227 119 126 67 64 102 67
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row500 : TripleComponentParentRow :=
  tripleRow 4068 2228 119 126 116 64 102 116
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row501 : TripleComponentParentRow :=
  tripleRow 4069 2229 119 126 117 64 102 117
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row502 : TripleComponentParentRow :=
  tripleRow 4070 2230 119 126 118 64 102 118
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row503 : TripleComponentParentRow :=
  tripleRow 4071 2231 119 126 119 64 102 119
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row504 : TripleComponentParentRow :=
  tripleRow 4072 2232 119 127 72 64 103 72
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row505 : TripleComponentParentRow :=
  tripleRow 4073 2233 119 127 73 64 103 73
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row506 : TripleComponentParentRow :=
  tripleRow 4074 2234 119 127 74 64 103 74
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row507 : TripleComponentParentRow :=
  tripleRow 4075 2235 119 127 75 64 103 75
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row508 : TripleComponentParentRow :=
  tripleRow 4076 2236 119 127 124 64 103 124
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row509 : TripleComponentParentRow :=
  tripleRow 4077 2237 119 127 125 64 103 125
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row510 : TripleComponentParentRow :=
  tripleRow 4078 2238 119 127 126 64 103 126
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row511 : TripleComponentParentRow :=
  tripleRow 4079 2239 119 127 127 64 103 127
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Block7Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row496
  , tttLargeFiber4Row497
  , tttLargeFiber4Row498
  , tttLargeFiber4Row499
  , tttLargeFiber4Row500
  , tttLargeFiber4Row501
  , tttLargeFiber4Row502
  , tttLargeFiber4Row503
  , tttLargeFiber4Row504
  , tttLargeFiber4Row505
  , tttLargeFiber4Row506
  , tttLargeFiber4Row507
  , tttLargeFiber4Row508
  , tttLargeFiber4Row509
  , tttLargeFiber4Row510
  , tttLargeFiber4Row511
  ]

def tttLargeFiber4Block7Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (2176 <= i) && decide (i < 2432)) ||
    (decide (3824 <= i) && decide (i < 4080))

def tttLargeFiber4Block7Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber4Block7Chunk3ExpectedContains row.source &&
    tttLargeFiber4Block7Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber4Key &&
          chainInputKey tttWord t == tttLargeFiber4Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber4Block7Chunk3SourcesCheck : Bool :=
  (tttLargeFiber4Block7Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber4Block7Chunk3Sources

theorem tttLargeFiber4Block7Chunk3SourcesCheck_ok :
    tttLargeFiber4Block7Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber4Block7Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber4Block7Chunk3RowValid
    (listGetD tttLargeFiber4Block7Chunk3Rows i default)

def tttLargeFiber4Block7Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block7Chunk3Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block7Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block7Chunk3Sources 0 0 == 4064 &&
      tttLargeFiber4ParentOf 4064 == 2224 &&
      tttLargeFiber4ParentOf 2224 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block7Chunk3Sources 1 0 == 4065 &&
      tttLargeFiber4ParentOf 4065 == 2225 &&
      tttLargeFiber4ParentOf 2225 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block7Chunk3Sources 2 0 == 4066 &&
      tttLargeFiber4ParentOf 4066 == 2226 &&
      tttLargeFiber4ParentOf 2226 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block7Chunk3Sources 3 0 == 4067 &&
      tttLargeFiber4ParentOf 4067 == 2227 &&
      tttLargeFiber4ParentOf 2227 == 2187 &&
      tttLargeFiber4ParentOf 2187 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block7Chunk3Sources 4 0 == 4068 &&
      tttLargeFiber4ParentOf 4068 == 2228 &&
      tttLargeFiber4ParentOf 2228 == 2188 &&
      tttLargeFiber4ParentOf 2188 == 2180 &&
      tttLargeFiber4ParentOf 2180 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block7Chunk3Sources 5 0 == 4069 &&
      tttLargeFiber4ParentOf 4069 == 2229 &&
      tttLargeFiber4ParentOf 2229 == 2189 &&
      tttLargeFiber4ParentOf 2189 == 2181 &&
      tttLargeFiber4ParentOf 2181 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block7Chunk3Sources 6 0 == 4070 &&
      tttLargeFiber4ParentOf 4070 == 2230 &&
      tttLargeFiber4ParentOf 2230 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block7Chunk3Sources 7 0 == 4071 &&
      tttLargeFiber4ParentOf 4071 == 2231 &&
      tttLargeFiber4ParentOf 2231 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block7Chunk3Sources 8 0 == 4072 &&
      tttLargeFiber4ParentOf 4072 == 2232 &&
      tttLargeFiber4ParentOf 2232 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (2 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block7Chunk3Sources 9 0 == 4073 &&
      tttLargeFiber4ParentOf 4073 == 2233 &&
      tttLargeFiber4ParentOf 2233 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block7Chunk3Sources 10 0 == 4074 &&
      tttLargeFiber4ParentOf 4074 == 2234 &&
      tttLargeFiber4ParentOf 2234 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block7Chunk3Sources 11 0 == 4075 &&
      tttLargeFiber4ParentOf 4075 == 2235 &&
      tttLargeFiber4ParentOf 2235 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block7Chunk3Sources 12 0 == 4076 &&
      tttLargeFiber4ParentOf 4076 == 2236 &&
      tttLargeFiber4ParentOf 2236 == 2180 &&
      tttLargeFiber4ParentOf 2180 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block7Chunk3Sources 13 0 == 4077 &&
      tttLargeFiber4ParentOf 4077 == 2237 &&
      tttLargeFiber4ParentOf 2237 == 2181 &&
      tttLargeFiber4ParentOf 2181 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block7Chunk3Sources 14 0 == 4078 &&
      tttLargeFiber4ParentOf 4078 == 2238 &&
      tttLargeFiber4ParentOf 2238 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block7Chunk3Sources 15 0 == 4079 &&
      tttLargeFiber4ParentOf 4079 == 2239 &&
      tttLargeFiber4ParentOf 2239 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block7Chunk3Row_0_ok :
    tttLargeFiber4Block7Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3Row_1_ok :
    tttLargeFiber4Block7Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3Row_2_ok :
    tttLargeFiber4Block7Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3Row_3_ok :
    tttLargeFiber4Block7Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3Row_4_ok :
    tttLargeFiber4Block7Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3Row_5_ok :
    tttLargeFiber4Block7Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3Row_6_ok :
    tttLargeFiber4Block7Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3Row_7_ok :
    tttLargeFiber4Block7Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3Row_8_ok :
    tttLargeFiber4Block7Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3Row_9_ok :
    tttLargeFiber4Block7Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3Row_10_ok :
    tttLargeFiber4Block7Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3Row_11_ok :
    tttLargeFiber4Block7Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3Row_12_ok :
    tttLargeFiber4Block7Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3Row_13_ok :
    tttLargeFiber4Block7Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3Row_14_ok :
    tttLargeFiber4Block7Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3Row_15_ok :
    tttLargeFiber4Block7Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentMap_0_ok :
    tttLargeFiber4Block7Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentMap_1_ok :
    tttLargeFiber4Block7Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentMap_2_ok :
    tttLargeFiber4Block7Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentMap_3_ok :
    tttLargeFiber4Block7Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentMap_4_ok :
    tttLargeFiber4Block7Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentMap_5_ok :
    tttLargeFiber4Block7Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentMap_6_ok :
    tttLargeFiber4Block7Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentMap_7_ok :
    tttLargeFiber4Block7Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentMap_8_ok :
    tttLargeFiber4Block7Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentMap_9_ok :
    tttLargeFiber4Block7Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentMap_10_ok :
    tttLargeFiber4Block7Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentMap_11_ok :
    tttLargeFiber4Block7Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentMap_12_ok :
    tttLargeFiber4Block7Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentMap_13_ok :
    tttLargeFiber4Block7Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentMap_14_ok :
    tttLargeFiber4Block7Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentMap_15_ok :
    tttLargeFiber4Block7Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentPath_0_ok :
    tttLargeFiber4Block7Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentPath_1_ok :
    tttLargeFiber4Block7Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentPath_2_ok :
    tttLargeFiber4Block7Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentPath_3_ok :
    tttLargeFiber4Block7Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentPath_4_ok :
    tttLargeFiber4Block7Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentPath_5_ok :
    tttLargeFiber4Block7Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentPath_6_ok :
    tttLargeFiber4Block7Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentPath_7_ok :
    tttLargeFiber4Block7Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentPath_8_ok :
    tttLargeFiber4Block7Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentPath_9_ok :
    tttLargeFiber4Block7Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentPath_10_ok :
    tttLargeFiber4Block7Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentPath_11_ok :
    tttLargeFiber4Block7Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentPath_12_ok :
    tttLargeFiber4Block7Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentPath_13_ok :
    tttLargeFiber4Block7Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentPath_14_ok :
    tttLargeFiber4Block7Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block7Chunk3ParentPath_15_ok :
    tttLargeFiber4Block7Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block7Chunk3RowsAudit : Bool :=
  tttLargeFiber4Block7Chunk3RowCheck 0
    && tttLargeFiber4Block7Chunk3RowCheck 1
    && tttLargeFiber4Block7Chunk3RowCheck 2
    && tttLargeFiber4Block7Chunk3RowCheck 3
    && tttLargeFiber4Block7Chunk3RowCheck 4
    && tttLargeFiber4Block7Chunk3RowCheck 5
    && tttLargeFiber4Block7Chunk3RowCheck 6
    && tttLargeFiber4Block7Chunk3RowCheck 7
    && tttLargeFiber4Block7Chunk3RowCheck 8
    && tttLargeFiber4Block7Chunk3RowCheck 9
    && tttLargeFiber4Block7Chunk3RowCheck 10
    && tttLargeFiber4Block7Chunk3RowCheck 11
    && tttLargeFiber4Block7Chunk3RowCheck 12
    && tttLargeFiber4Block7Chunk3RowCheck 13
    && tttLargeFiber4Block7Chunk3RowCheck 14
    && tttLargeFiber4Block7Chunk3RowCheck 15

theorem tttLargeFiber4Block7Chunk3RowsAudit_ok :
    tttLargeFiber4Block7Chunk3RowsAudit = true := by
  simp [tttLargeFiber4Block7Chunk3RowsAudit,
    tttLargeFiber4Block7Chunk3Row_0_ok,
    tttLargeFiber4Block7Chunk3Row_1_ok,
    tttLargeFiber4Block7Chunk3Row_2_ok,
    tttLargeFiber4Block7Chunk3Row_3_ok,
    tttLargeFiber4Block7Chunk3Row_4_ok,
    tttLargeFiber4Block7Chunk3Row_5_ok,
    tttLargeFiber4Block7Chunk3Row_6_ok,
    tttLargeFiber4Block7Chunk3Row_7_ok,
    tttLargeFiber4Block7Chunk3Row_8_ok,
    tttLargeFiber4Block7Chunk3Row_9_ok,
    tttLargeFiber4Block7Chunk3Row_10_ok,
    tttLargeFiber4Block7Chunk3Row_11_ok,
    tttLargeFiber4Block7Chunk3Row_12_ok,
    tttLargeFiber4Block7Chunk3Row_13_ok,
    tttLargeFiber4Block7Chunk3Row_14_ok,
    tttLargeFiber4Block7Chunk3Row_15_ok]

def tttLargeFiber4Block7Chunk3ParentMapAudit : Bool :=
  tttLargeFiber4Block7Chunk3ParentMapCheck 0
    && tttLargeFiber4Block7Chunk3ParentMapCheck 1
    && tttLargeFiber4Block7Chunk3ParentMapCheck 2
    && tttLargeFiber4Block7Chunk3ParentMapCheck 3
    && tttLargeFiber4Block7Chunk3ParentMapCheck 4
    && tttLargeFiber4Block7Chunk3ParentMapCheck 5
    && tttLargeFiber4Block7Chunk3ParentMapCheck 6
    && tttLargeFiber4Block7Chunk3ParentMapCheck 7
    && tttLargeFiber4Block7Chunk3ParentMapCheck 8
    && tttLargeFiber4Block7Chunk3ParentMapCheck 9
    && tttLargeFiber4Block7Chunk3ParentMapCheck 10
    && tttLargeFiber4Block7Chunk3ParentMapCheck 11
    && tttLargeFiber4Block7Chunk3ParentMapCheck 12
    && tttLargeFiber4Block7Chunk3ParentMapCheck 13
    && tttLargeFiber4Block7Chunk3ParentMapCheck 14
    && tttLargeFiber4Block7Chunk3ParentMapCheck 15

theorem tttLargeFiber4Block7Chunk3ParentMapAudit_ok :
    tttLargeFiber4Block7Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber4Block7Chunk3ParentMapAudit,
    tttLargeFiber4Block7Chunk3ParentMap_0_ok,
    tttLargeFiber4Block7Chunk3ParentMap_1_ok,
    tttLargeFiber4Block7Chunk3ParentMap_2_ok,
    tttLargeFiber4Block7Chunk3ParentMap_3_ok,
    tttLargeFiber4Block7Chunk3ParentMap_4_ok,
    tttLargeFiber4Block7Chunk3ParentMap_5_ok,
    tttLargeFiber4Block7Chunk3ParentMap_6_ok,
    tttLargeFiber4Block7Chunk3ParentMap_7_ok,
    tttLargeFiber4Block7Chunk3ParentMap_8_ok,
    tttLargeFiber4Block7Chunk3ParentMap_9_ok,
    tttLargeFiber4Block7Chunk3ParentMap_10_ok,
    tttLargeFiber4Block7Chunk3ParentMap_11_ok,
    tttLargeFiber4Block7Chunk3ParentMap_12_ok,
    tttLargeFiber4Block7Chunk3ParentMap_13_ok,
    tttLargeFiber4Block7Chunk3ParentMap_14_ok,
    tttLargeFiber4Block7Chunk3ParentMap_15_ok]

def tttLargeFiber4Block7Chunk3ParentsAudit : Bool :=
  tttLargeFiber4Block7Chunk3ParentPathCheck 0
    && tttLargeFiber4Block7Chunk3ParentPathCheck 1
    && tttLargeFiber4Block7Chunk3ParentPathCheck 2
    && tttLargeFiber4Block7Chunk3ParentPathCheck 3
    && tttLargeFiber4Block7Chunk3ParentPathCheck 4
    && tttLargeFiber4Block7Chunk3ParentPathCheck 5
    && tttLargeFiber4Block7Chunk3ParentPathCheck 6
    && tttLargeFiber4Block7Chunk3ParentPathCheck 7
    && tttLargeFiber4Block7Chunk3ParentPathCheck 8
    && tttLargeFiber4Block7Chunk3ParentPathCheck 9
    && tttLargeFiber4Block7Chunk3ParentPathCheck 10
    && tttLargeFiber4Block7Chunk3ParentPathCheck 11
    && tttLargeFiber4Block7Chunk3ParentPathCheck 12
    && tttLargeFiber4Block7Chunk3ParentPathCheck 13
    && tttLargeFiber4Block7Chunk3ParentPathCheck 14
    && tttLargeFiber4Block7Chunk3ParentPathCheck 15

theorem tttLargeFiber4Block7Chunk3ParentsAudit_ok :
    tttLargeFiber4Block7Chunk3ParentsAudit = true := by
  simp [tttLargeFiber4Block7Chunk3ParentsAudit,
    tttLargeFiber4Block7Chunk3ParentPath_0_ok,
    tttLargeFiber4Block7Chunk3ParentPath_1_ok,
    tttLargeFiber4Block7Chunk3ParentPath_2_ok,
    tttLargeFiber4Block7Chunk3ParentPath_3_ok,
    tttLargeFiber4Block7Chunk3ParentPath_4_ok,
    tttLargeFiber4Block7Chunk3ParentPath_5_ok,
    tttLargeFiber4Block7Chunk3ParentPath_6_ok,
    tttLargeFiber4Block7Chunk3ParentPath_7_ok,
    tttLargeFiber4Block7Chunk3ParentPath_8_ok,
    tttLargeFiber4Block7Chunk3ParentPath_9_ok,
    tttLargeFiber4Block7Chunk3ParentPath_10_ok,
    tttLargeFiber4Block7Chunk3ParentPath_11_ok,
    tttLargeFiber4Block7Chunk3ParentPath_12_ok,
    tttLargeFiber4Block7Chunk3ParentPath_13_ok,
    tttLargeFiber4Block7Chunk3ParentPath_14_ok,
    tttLargeFiber4Block7Chunk3ParentPath_15_ok]

def tttLargeFiber4Block7Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block7Chunk3SourcesCheck &&
    tttLargeFiber4Block7Chunk3RowsAudit &&
    tttLargeFiber4Block7Chunk3ParentMapAudit &&
    tttLargeFiber4Block7Chunk3ParentsAudit

theorem tttLargeFiber4Block7Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber4Block7Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block7Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block7Chunk3SourcesCheck_ok,
    tttLargeFiber4Block7Chunk3RowsAudit_ok,
    tttLargeFiber4Block7Chunk3ParentMapAudit_ok,
    tttLargeFiber4Block7Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block7Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
