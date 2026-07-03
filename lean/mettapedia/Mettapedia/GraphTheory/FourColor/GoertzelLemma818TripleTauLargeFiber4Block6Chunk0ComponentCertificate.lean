import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 6 chunk 0

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
For second-range rows it uses interval membership and explicit bounded parent
paths, avoiding broad expected-list traversal and recursive parent iteration.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block6Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block6Chunk0Sources : List Nat :=
  [3952, 3953, 3954, 3955, 3956, 3957, 3958, 3959,
   3960, 3961, 3962, 3963, 3964, 3965, 3966, 3967]

def tttLargeFiber4Row384 : TripleComponentParentRow :=
  tripleRow 3952 2240 118 64 80 65 88 80
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row385 : TripleComponentParentRow :=
  tripleRow 3953 2241 118 64 81 65 88 81
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row386 : TripleComponentParentRow :=
  tripleRow 3954 2242 118 64 82 65 88 82
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row387 : TripleComponentParentRow :=
  tripleRow 3955 2243 118 64 83 65 88 83
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row388 : TripleComponentParentRow :=
  tripleRow 3956 2244 118 64 100 65 88 100
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row389 : TripleComponentParentRow :=
  tripleRow 3957 2245 118 64 101 65 88 101
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row390 : TripleComponentParentRow :=
  tripleRow 3958 2246 118 64 102 65 88 102
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row391 : TripleComponentParentRow :=
  tripleRow 3959 2247 118 64 103 65 88 103
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row392 : TripleComponentParentRow :=
  tripleRow 3960 2248 118 65 88 65 89 88
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row393 : TripleComponentParentRow :=
  tripleRow 3961 2249 118 65 89 65 89 89
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row394 : TripleComponentParentRow :=
  tripleRow 3962 2250 118 65 90 65 89 90
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row395 : TripleComponentParentRow :=
  tripleRow 3963 2251 118 65 91 65 89 91
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row396 : TripleComponentParentRow :=
  tripleRow 3964 2252 118 65 108 65 89 108
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row397 : TripleComponentParentRow :=
  tripleRow 3965 2253 118 65 109 65 89 109
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row398 : TripleComponentParentRow :=
  tripleRow 3966 2254 118 65 110 65 89 110
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row399 : TripleComponentParentRow :=
  tripleRow 3967 2255 118 65 111 65 89 111
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Block6Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row384
  , tttLargeFiber4Row385
  , tttLargeFiber4Row386
  , tttLargeFiber4Row387
  , tttLargeFiber4Row388
  , tttLargeFiber4Row389
  , tttLargeFiber4Row390
  , tttLargeFiber4Row391
  , tttLargeFiber4Row392
  , tttLargeFiber4Row393
  , tttLargeFiber4Row394
  , tttLargeFiber4Row395
  , tttLargeFiber4Row396
  , tttLargeFiber4Row397
  , tttLargeFiber4Row398
  , tttLargeFiber4Row399
  ]

def tttLargeFiber4Block6Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (2176 <= i) && decide (i < 2432)) ||
    (decide (3824 <= i) && decide (i < 4080))

def tttLargeFiber4Block6Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber4Block6Chunk0ExpectedContains row.source &&
    tttLargeFiber4Block6Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber4Key &&
          chainInputKey tttWord t == tttLargeFiber4Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber4Block6Chunk0SourcesCheck : Bool :=
  (tttLargeFiber4Block6Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber4Block6Chunk0Sources

theorem tttLargeFiber4Block6Chunk0SourcesCheck_ok :
    tttLargeFiber4Block6Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber4Block6Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber4Block6Chunk0RowValid
    (listGetD tttLargeFiber4Block6Chunk0Rows i default)

def tttLargeFiber4Block6Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block6Chunk0Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block6Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block6Chunk0Sources 0 0 == 3952 &&
      tttLargeFiber4ParentOf 3952 == 2240 &&
      tttLargeFiber4ParentOf 2240 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (2 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block6Chunk0Sources 1 0 == 3953 &&
      tttLargeFiber4ParentOf 3953 == 2241 &&
      tttLargeFiber4ParentOf 2241 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block6Chunk0Sources 2 0 == 3954 &&
      tttLargeFiber4ParentOf 3954 == 2242 &&
      tttLargeFiber4ParentOf 2242 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block6Chunk0Sources 3 0 == 3955 &&
      tttLargeFiber4ParentOf 3955 == 2243 &&
      tttLargeFiber4ParentOf 2243 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block6Chunk0Sources 4 0 == 3956 &&
      tttLargeFiber4ParentOf 3956 == 2244 &&
      tttLargeFiber4ParentOf 2244 == 2180 &&
      tttLargeFiber4ParentOf 2180 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block6Chunk0Sources 5 0 == 3957 &&
      tttLargeFiber4ParentOf 3957 == 2245 &&
      tttLargeFiber4ParentOf 2245 == 2181 &&
      tttLargeFiber4ParentOf 2181 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block6Chunk0Sources 6 0 == 3958 &&
      tttLargeFiber4ParentOf 3958 == 2246 &&
      tttLargeFiber4ParentOf 2246 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block6Chunk0Sources 7 0 == 3959 &&
      tttLargeFiber4ParentOf 3959 == 2247 &&
      tttLargeFiber4ParentOf 2247 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block6Chunk0Sources 8 0 == 3960 &&
      tttLargeFiber4ParentOf 3960 == 2248 &&
      tttLargeFiber4ParentOf 2248 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block6Chunk0Sources 9 0 == 3961 &&
      tttLargeFiber4ParentOf 3961 == 2249 &&
      tttLargeFiber4ParentOf 2249 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block6Chunk0Sources 10 0 == 3962 &&
      tttLargeFiber4ParentOf 3962 == 2250 &&
      tttLargeFiber4ParentOf 2250 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block6Chunk0Sources 11 0 == 3963 &&
      tttLargeFiber4ParentOf 3963 == 2251 &&
      tttLargeFiber4ParentOf 2251 == 2187 &&
      tttLargeFiber4ParentOf 2187 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block6Chunk0Sources 12 0 == 3964 &&
      tttLargeFiber4ParentOf 3964 == 2252 &&
      tttLargeFiber4ParentOf 2252 == 2188 &&
      tttLargeFiber4ParentOf 2188 == 2180 &&
      tttLargeFiber4ParentOf 2180 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block6Chunk0Sources 13 0 == 3965 &&
      tttLargeFiber4ParentOf 3965 == 2253 &&
      tttLargeFiber4ParentOf 2253 == 2189 &&
      tttLargeFiber4ParentOf 2189 == 2181 &&
      tttLargeFiber4ParentOf 2181 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block6Chunk0Sources 14 0 == 3966 &&
      tttLargeFiber4ParentOf 3966 == 2254 &&
      tttLargeFiber4ParentOf 2254 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block6Chunk0Sources 15 0 == 3967 &&
      tttLargeFiber4ParentOf 3967 == 2255 &&
      tttLargeFiber4ParentOf 2255 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block6Chunk0Row_0_ok :
    tttLargeFiber4Block6Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0Row_1_ok :
    tttLargeFiber4Block6Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0Row_2_ok :
    tttLargeFiber4Block6Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0Row_3_ok :
    tttLargeFiber4Block6Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0Row_4_ok :
    tttLargeFiber4Block6Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0Row_5_ok :
    tttLargeFiber4Block6Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0Row_6_ok :
    tttLargeFiber4Block6Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0Row_7_ok :
    tttLargeFiber4Block6Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0Row_8_ok :
    tttLargeFiber4Block6Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0Row_9_ok :
    tttLargeFiber4Block6Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0Row_10_ok :
    tttLargeFiber4Block6Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0Row_11_ok :
    tttLargeFiber4Block6Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0Row_12_ok :
    tttLargeFiber4Block6Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0Row_13_ok :
    tttLargeFiber4Block6Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0Row_14_ok :
    tttLargeFiber4Block6Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0Row_15_ok :
    tttLargeFiber4Block6Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentMap_0_ok :
    tttLargeFiber4Block6Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentMap_1_ok :
    tttLargeFiber4Block6Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentMap_2_ok :
    tttLargeFiber4Block6Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentMap_3_ok :
    tttLargeFiber4Block6Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentMap_4_ok :
    tttLargeFiber4Block6Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentMap_5_ok :
    tttLargeFiber4Block6Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentMap_6_ok :
    tttLargeFiber4Block6Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentMap_7_ok :
    tttLargeFiber4Block6Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentMap_8_ok :
    tttLargeFiber4Block6Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentMap_9_ok :
    tttLargeFiber4Block6Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentMap_10_ok :
    tttLargeFiber4Block6Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentMap_11_ok :
    tttLargeFiber4Block6Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentMap_12_ok :
    tttLargeFiber4Block6Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentMap_13_ok :
    tttLargeFiber4Block6Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentMap_14_ok :
    tttLargeFiber4Block6Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentMap_15_ok :
    tttLargeFiber4Block6Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentPath_0_ok :
    tttLargeFiber4Block6Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentPath_1_ok :
    tttLargeFiber4Block6Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentPath_2_ok :
    tttLargeFiber4Block6Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentPath_3_ok :
    tttLargeFiber4Block6Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentPath_4_ok :
    tttLargeFiber4Block6Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentPath_5_ok :
    tttLargeFiber4Block6Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentPath_6_ok :
    tttLargeFiber4Block6Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentPath_7_ok :
    tttLargeFiber4Block6Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentPath_8_ok :
    tttLargeFiber4Block6Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentPath_9_ok :
    tttLargeFiber4Block6Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentPath_10_ok :
    tttLargeFiber4Block6Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentPath_11_ok :
    tttLargeFiber4Block6Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentPath_12_ok :
    tttLargeFiber4Block6Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentPath_13_ok :
    tttLargeFiber4Block6Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentPath_14_ok :
    tttLargeFiber4Block6Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block6Chunk0ParentPath_15_ok :
    tttLargeFiber4Block6Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block6Chunk0RowsAudit : Bool :=
  tttLargeFiber4Block6Chunk0RowCheck 0
    && tttLargeFiber4Block6Chunk0RowCheck 1
    && tttLargeFiber4Block6Chunk0RowCheck 2
    && tttLargeFiber4Block6Chunk0RowCheck 3
    && tttLargeFiber4Block6Chunk0RowCheck 4
    && tttLargeFiber4Block6Chunk0RowCheck 5
    && tttLargeFiber4Block6Chunk0RowCheck 6
    && tttLargeFiber4Block6Chunk0RowCheck 7
    && tttLargeFiber4Block6Chunk0RowCheck 8
    && tttLargeFiber4Block6Chunk0RowCheck 9
    && tttLargeFiber4Block6Chunk0RowCheck 10
    && tttLargeFiber4Block6Chunk0RowCheck 11
    && tttLargeFiber4Block6Chunk0RowCheck 12
    && tttLargeFiber4Block6Chunk0RowCheck 13
    && tttLargeFiber4Block6Chunk0RowCheck 14
    && tttLargeFiber4Block6Chunk0RowCheck 15

theorem tttLargeFiber4Block6Chunk0RowsAudit_ok :
    tttLargeFiber4Block6Chunk0RowsAudit = true := by
  simp [tttLargeFiber4Block6Chunk0RowsAudit,
    tttLargeFiber4Block6Chunk0Row_0_ok,
    tttLargeFiber4Block6Chunk0Row_1_ok,
    tttLargeFiber4Block6Chunk0Row_2_ok,
    tttLargeFiber4Block6Chunk0Row_3_ok,
    tttLargeFiber4Block6Chunk0Row_4_ok,
    tttLargeFiber4Block6Chunk0Row_5_ok,
    tttLargeFiber4Block6Chunk0Row_6_ok,
    tttLargeFiber4Block6Chunk0Row_7_ok,
    tttLargeFiber4Block6Chunk0Row_8_ok,
    tttLargeFiber4Block6Chunk0Row_9_ok,
    tttLargeFiber4Block6Chunk0Row_10_ok,
    tttLargeFiber4Block6Chunk0Row_11_ok,
    tttLargeFiber4Block6Chunk0Row_12_ok,
    tttLargeFiber4Block6Chunk0Row_13_ok,
    tttLargeFiber4Block6Chunk0Row_14_ok,
    tttLargeFiber4Block6Chunk0Row_15_ok]

def tttLargeFiber4Block6Chunk0ParentMapAudit : Bool :=
  tttLargeFiber4Block6Chunk0ParentMapCheck 0
    && tttLargeFiber4Block6Chunk0ParentMapCheck 1
    && tttLargeFiber4Block6Chunk0ParentMapCheck 2
    && tttLargeFiber4Block6Chunk0ParentMapCheck 3
    && tttLargeFiber4Block6Chunk0ParentMapCheck 4
    && tttLargeFiber4Block6Chunk0ParentMapCheck 5
    && tttLargeFiber4Block6Chunk0ParentMapCheck 6
    && tttLargeFiber4Block6Chunk0ParentMapCheck 7
    && tttLargeFiber4Block6Chunk0ParentMapCheck 8
    && tttLargeFiber4Block6Chunk0ParentMapCheck 9
    && tttLargeFiber4Block6Chunk0ParentMapCheck 10
    && tttLargeFiber4Block6Chunk0ParentMapCheck 11
    && tttLargeFiber4Block6Chunk0ParentMapCheck 12
    && tttLargeFiber4Block6Chunk0ParentMapCheck 13
    && tttLargeFiber4Block6Chunk0ParentMapCheck 14
    && tttLargeFiber4Block6Chunk0ParentMapCheck 15

theorem tttLargeFiber4Block6Chunk0ParentMapAudit_ok :
    tttLargeFiber4Block6Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber4Block6Chunk0ParentMapAudit,
    tttLargeFiber4Block6Chunk0ParentMap_0_ok,
    tttLargeFiber4Block6Chunk0ParentMap_1_ok,
    tttLargeFiber4Block6Chunk0ParentMap_2_ok,
    tttLargeFiber4Block6Chunk0ParentMap_3_ok,
    tttLargeFiber4Block6Chunk0ParentMap_4_ok,
    tttLargeFiber4Block6Chunk0ParentMap_5_ok,
    tttLargeFiber4Block6Chunk0ParentMap_6_ok,
    tttLargeFiber4Block6Chunk0ParentMap_7_ok,
    tttLargeFiber4Block6Chunk0ParentMap_8_ok,
    tttLargeFiber4Block6Chunk0ParentMap_9_ok,
    tttLargeFiber4Block6Chunk0ParentMap_10_ok,
    tttLargeFiber4Block6Chunk0ParentMap_11_ok,
    tttLargeFiber4Block6Chunk0ParentMap_12_ok,
    tttLargeFiber4Block6Chunk0ParentMap_13_ok,
    tttLargeFiber4Block6Chunk0ParentMap_14_ok,
    tttLargeFiber4Block6Chunk0ParentMap_15_ok]

def tttLargeFiber4Block6Chunk0ParentsAudit : Bool :=
  tttLargeFiber4Block6Chunk0ParentPathCheck 0
    && tttLargeFiber4Block6Chunk0ParentPathCheck 1
    && tttLargeFiber4Block6Chunk0ParentPathCheck 2
    && tttLargeFiber4Block6Chunk0ParentPathCheck 3
    && tttLargeFiber4Block6Chunk0ParentPathCheck 4
    && tttLargeFiber4Block6Chunk0ParentPathCheck 5
    && tttLargeFiber4Block6Chunk0ParentPathCheck 6
    && tttLargeFiber4Block6Chunk0ParentPathCheck 7
    && tttLargeFiber4Block6Chunk0ParentPathCheck 8
    && tttLargeFiber4Block6Chunk0ParentPathCheck 9
    && tttLargeFiber4Block6Chunk0ParentPathCheck 10
    && tttLargeFiber4Block6Chunk0ParentPathCheck 11
    && tttLargeFiber4Block6Chunk0ParentPathCheck 12
    && tttLargeFiber4Block6Chunk0ParentPathCheck 13
    && tttLargeFiber4Block6Chunk0ParentPathCheck 14
    && tttLargeFiber4Block6Chunk0ParentPathCheck 15

theorem tttLargeFiber4Block6Chunk0ParentsAudit_ok :
    tttLargeFiber4Block6Chunk0ParentsAudit = true := by
  simp [tttLargeFiber4Block6Chunk0ParentsAudit,
    tttLargeFiber4Block6Chunk0ParentPath_0_ok,
    tttLargeFiber4Block6Chunk0ParentPath_1_ok,
    tttLargeFiber4Block6Chunk0ParentPath_2_ok,
    tttLargeFiber4Block6Chunk0ParentPath_3_ok,
    tttLargeFiber4Block6Chunk0ParentPath_4_ok,
    tttLargeFiber4Block6Chunk0ParentPath_5_ok,
    tttLargeFiber4Block6Chunk0ParentPath_6_ok,
    tttLargeFiber4Block6Chunk0ParentPath_7_ok,
    tttLargeFiber4Block6Chunk0ParentPath_8_ok,
    tttLargeFiber4Block6Chunk0ParentPath_9_ok,
    tttLargeFiber4Block6Chunk0ParentPath_10_ok,
    tttLargeFiber4Block6Chunk0ParentPath_11_ok,
    tttLargeFiber4Block6Chunk0ParentPath_12_ok,
    tttLargeFiber4Block6Chunk0ParentPath_13_ok,
    tttLargeFiber4Block6Chunk0ParentPath_14_ok,
    tttLargeFiber4Block6Chunk0ParentPath_15_ok]

def tttLargeFiber4Block6Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block6Chunk0SourcesCheck &&
    tttLargeFiber4Block6Chunk0RowsAudit &&
    tttLargeFiber4Block6Chunk0ParentMapAudit &&
    tttLargeFiber4Block6Chunk0ParentsAudit

theorem tttLargeFiber4Block6Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber4Block6Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block6Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block6Chunk0SourcesCheck_ok,
    tttLargeFiber4Block6Chunk0RowsAudit_ok,
    tttLargeFiber4Block6Chunk0ParentMapAudit_ok,
    tttLargeFiber4Block6Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block6Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
