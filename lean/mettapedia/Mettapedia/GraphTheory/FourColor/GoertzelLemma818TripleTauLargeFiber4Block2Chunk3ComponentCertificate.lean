import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 2 chunk 3

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
Parent-depth convergence is checked by explicit bounded parent paths rather
than by reducing the recursive parent iterator over large indices.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block2Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block2Chunk3Sources : List Nat :=
  [2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359,
   2360, 2361, 2362, 2363, 2364, 2365, 2366, 2367]

def tttLargeFiber4Row176 : TripleComponentParentRow :=
  tripleRow 2352 2224 66 34 0 64 102 64
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber4Row177 : TripleComponentParentRow :=
  tripleRow 2353 2225 66 34 1 64 102 65
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber4Row178 : TripleComponentParentRow :=
  tripleRow 2354 2226 66 34 2 64 102 66
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber4Row179 : TripleComponentParentRow :=
  tripleRow 2355 2227 66 34 3 64 102 67
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber4Row180 : TripleComponentParentRow :=
  tripleRow 2356 2352 66 34 48 66 34 0
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row181 : TripleComponentParentRow :=
  tripleRow 2357 2353 66 34 49 66 34 1
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row182 : TripleComponentParentRow :=
  tripleRow 2358 2230 66 34 50 64 102 118
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber4Row183 : TripleComponentParentRow :=
  tripleRow 2359 2231 66 34 51 64 102 119
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber4Row184 : TripleComponentParentRow :=
  tripleRow 2360 2232 66 35 8 64 103 72
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber4Row185 : TripleComponentParentRow :=
  tripleRow 2361 2233 66 35 9 64 103 73
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber4Row186 : TripleComponentParentRow :=
  tripleRow 2362 2234 66 35 10 64 103 74
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber4Row187 : TripleComponentParentRow :=
  tripleRow 2363 2235 66 35 11 64 103 75
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber4Row188 : TripleComponentParentRow :=
  tripleRow 2364 2360 66 35 56 66 35 8
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row189 : TripleComponentParentRow :=
  tripleRow 2365 2361 66 35 57 66 35 9
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row190 : TripleComponentParentRow :=
  tripleRow 2366 2238 66 35 58 64 103 126
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber4Row191 : TripleComponentParentRow :=
  tripleRow 2367 2239 66 35 59 64 103 127
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber4Block2Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row176
  , tttLargeFiber4Row177
  , tttLargeFiber4Row178
  , tttLargeFiber4Row179
  , tttLargeFiber4Row180
  , tttLargeFiber4Row181
  , tttLargeFiber4Row182
  , tttLargeFiber4Row183
  , tttLargeFiber4Row184
  , tttLargeFiber4Row185
  , tttLargeFiber4Row186
  , tttLargeFiber4Row187
  , tttLargeFiber4Row188
  , tttLargeFiber4Row189
  , tttLargeFiber4Row190
  , tttLargeFiber4Row191
  ]

def tttLargeFiber4Block2Chunk3SourcesCheck : Bool :=
  (tttLargeFiber4Block2Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber4Block2Chunk3Sources

theorem tttLargeFiber4Block2Chunk3SourcesCheck_ok :
    tttLargeFiber4Block2Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber4Block2Chunk3RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttLargeFiber4Key tttLargeFiber4Expected
    (listGetD tttLargeFiber4Block2Chunk3Rows i default)

def tttLargeFiber4Block2Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block2Chunk3Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block2Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block2Chunk3Sources 0 0 == 2352 &&
      tttLargeFiber4ParentOf 2352 == 2224 &&
      tttLargeFiber4ParentOf 2224 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block2Chunk3Sources 1 0 == 2353 &&
      tttLargeFiber4ParentOf 2353 == 2225 &&
      tttLargeFiber4ParentOf 2225 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block2Chunk3Sources 2 0 == 2354 &&
      tttLargeFiber4ParentOf 2354 == 2226 &&
      tttLargeFiber4ParentOf 2226 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block2Chunk3Sources 3 0 == 2355 &&
      tttLargeFiber4ParentOf 2355 == 2227 &&
      tttLargeFiber4ParentOf 2227 == 2187 &&
      tttLargeFiber4ParentOf 2187 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block2Chunk3Sources 4 0 == 2356 &&
      tttLargeFiber4ParentOf 2356 == 2352 &&
      tttLargeFiber4ParentOf 2352 == 2224 &&
      tttLargeFiber4ParentOf 2224 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block2Chunk3Sources 5 0 == 2357 &&
      tttLargeFiber4ParentOf 2357 == 2353 &&
      tttLargeFiber4ParentOf 2353 == 2225 &&
      tttLargeFiber4ParentOf 2225 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block2Chunk3Sources 6 0 == 2358 &&
      tttLargeFiber4ParentOf 2358 == 2230 &&
      tttLargeFiber4ParentOf 2230 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block2Chunk3Sources 7 0 == 2359 &&
      tttLargeFiber4ParentOf 2359 == 2231 &&
      tttLargeFiber4ParentOf 2231 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block2Chunk3Sources 8 0 == 2360 &&
      tttLargeFiber4ParentOf 2360 == 2232 &&
      tttLargeFiber4ParentOf 2232 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (2 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block2Chunk3Sources 9 0 == 2361 &&
      tttLargeFiber4ParentOf 2361 == 2233 &&
      tttLargeFiber4ParentOf 2233 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block2Chunk3Sources 10 0 == 2362 &&
      tttLargeFiber4ParentOf 2362 == 2234 &&
      tttLargeFiber4ParentOf 2234 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block2Chunk3Sources 11 0 == 2363 &&
      tttLargeFiber4ParentOf 2363 == 2235 &&
      tttLargeFiber4ParentOf 2235 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block2Chunk3Sources 12 0 == 2364 &&
      tttLargeFiber4ParentOf 2364 == 2360 &&
      tttLargeFiber4ParentOf 2360 == 2232 &&
      tttLargeFiber4ParentOf 2232 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block2Chunk3Sources 13 0 == 2365 &&
      tttLargeFiber4ParentOf 2365 == 2361 &&
      tttLargeFiber4ParentOf 2361 == 2233 &&
      tttLargeFiber4ParentOf 2233 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block2Chunk3Sources 14 0 == 2366 &&
      tttLargeFiber4ParentOf 2366 == 2238 &&
      tttLargeFiber4ParentOf 2238 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block2Chunk3Sources 15 0 == 2367 &&
      tttLargeFiber4ParentOf 2367 == 2239 &&
      tttLargeFiber4ParentOf 2239 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block2Chunk3Row_0_ok :
    tttLargeFiber4Block2Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3Row_1_ok :
    tttLargeFiber4Block2Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3Row_2_ok :
    tttLargeFiber4Block2Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3Row_3_ok :
    tttLargeFiber4Block2Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3Row_4_ok :
    tttLargeFiber4Block2Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3Row_5_ok :
    tttLargeFiber4Block2Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3Row_6_ok :
    tttLargeFiber4Block2Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3Row_7_ok :
    tttLargeFiber4Block2Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3Row_8_ok :
    tttLargeFiber4Block2Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3Row_9_ok :
    tttLargeFiber4Block2Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3Row_10_ok :
    tttLargeFiber4Block2Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3Row_11_ok :
    tttLargeFiber4Block2Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3Row_12_ok :
    tttLargeFiber4Block2Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3Row_13_ok :
    tttLargeFiber4Block2Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3Row_14_ok :
    tttLargeFiber4Block2Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3Row_15_ok :
    tttLargeFiber4Block2Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentMap_0_ok :
    tttLargeFiber4Block2Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentMap_1_ok :
    tttLargeFiber4Block2Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentMap_2_ok :
    tttLargeFiber4Block2Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentMap_3_ok :
    tttLargeFiber4Block2Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentMap_4_ok :
    tttLargeFiber4Block2Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentMap_5_ok :
    tttLargeFiber4Block2Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentMap_6_ok :
    tttLargeFiber4Block2Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentMap_7_ok :
    tttLargeFiber4Block2Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentMap_8_ok :
    tttLargeFiber4Block2Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentMap_9_ok :
    tttLargeFiber4Block2Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentMap_10_ok :
    tttLargeFiber4Block2Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentMap_11_ok :
    tttLargeFiber4Block2Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentMap_12_ok :
    tttLargeFiber4Block2Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentMap_13_ok :
    tttLargeFiber4Block2Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentMap_14_ok :
    tttLargeFiber4Block2Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentMap_15_ok :
    tttLargeFiber4Block2Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentPath_0_ok :
    tttLargeFiber4Block2Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentPath_1_ok :
    tttLargeFiber4Block2Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentPath_2_ok :
    tttLargeFiber4Block2Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentPath_3_ok :
    tttLargeFiber4Block2Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentPath_4_ok :
    tttLargeFiber4Block2Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentPath_5_ok :
    tttLargeFiber4Block2Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentPath_6_ok :
    tttLargeFiber4Block2Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentPath_7_ok :
    tttLargeFiber4Block2Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentPath_8_ok :
    tttLargeFiber4Block2Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentPath_9_ok :
    tttLargeFiber4Block2Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentPath_10_ok :
    tttLargeFiber4Block2Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentPath_11_ok :
    tttLargeFiber4Block2Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentPath_12_ok :
    tttLargeFiber4Block2Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentPath_13_ok :
    tttLargeFiber4Block2Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentPath_14_ok :
    tttLargeFiber4Block2Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block2Chunk3ParentPath_15_ok :
    tttLargeFiber4Block2Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block2Chunk3RowsAudit : Bool :=
  tttLargeFiber4Block2Chunk3RowCheck 0
    && tttLargeFiber4Block2Chunk3RowCheck 1
    && tttLargeFiber4Block2Chunk3RowCheck 2
    && tttLargeFiber4Block2Chunk3RowCheck 3
    && tttLargeFiber4Block2Chunk3RowCheck 4
    && tttLargeFiber4Block2Chunk3RowCheck 5
    && tttLargeFiber4Block2Chunk3RowCheck 6
    && tttLargeFiber4Block2Chunk3RowCheck 7
    && tttLargeFiber4Block2Chunk3RowCheck 8
    && tttLargeFiber4Block2Chunk3RowCheck 9
    && tttLargeFiber4Block2Chunk3RowCheck 10
    && tttLargeFiber4Block2Chunk3RowCheck 11
    && tttLargeFiber4Block2Chunk3RowCheck 12
    && tttLargeFiber4Block2Chunk3RowCheck 13
    && tttLargeFiber4Block2Chunk3RowCheck 14
    && tttLargeFiber4Block2Chunk3RowCheck 15

theorem tttLargeFiber4Block2Chunk3RowsAudit_ok :
    tttLargeFiber4Block2Chunk3RowsAudit = true := by
  simp [tttLargeFiber4Block2Chunk3RowsAudit,
    tttLargeFiber4Block2Chunk3Row_0_ok,
    tttLargeFiber4Block2Chunk3Row_1_ok,
    tttLargeFiber4Block2Chunk3Row_2_ok,
    tttLargeFiber4Block2Chunk3Row_3_ok,
    tttLargeFiber4Block2Chunk3Row_4_ok,
    tttLargeFiber4Block2Chunk3Row_5_ok,
    tttLargeFiber4Block2Chunk3Row_6_ok,
    tttLargeFiber4Block2Chunk3Row_7_ok,
    tttLargeFiber4Block2Chunk3Row_8_ok,
    tttLargeFiber4Block2Chunk3Row_9_ok,
    tttLargeFiber4Block2Chunk3Row_10_ok,
    tttLargeFiber4Block2Chunk3Row_11_ok,
    tttLargeFiber4Block2Chunk3Row_12_ok,
    tttLargeFiber4Block2Chunk3Row_13_ok,
    tttLargeFiber4Block2Chunk3Row_14_ok,
    tttLargeFiber4Block2Chunk3Row_15_ok]

def tttLargeFiber4Block2Chunk3ParentMapAudit : Bool :=
  tttLargeFiber4Block2Chunk3ParentMapCheck 0
    && tttLargeFiber4Block2Chunk3ParentMapCheck 1
    && tttLargeFiber4Block2Chunk3ParentMapCheck 2
    && tttLargeFiber4Block2Chunk3ParentMapCheck 3
    && tttLargeFiber4Block2Chunk3ParentMapCheck 4
    && tttLargeFiber4Block2Chunk3ParentMapCheck 5
    && tttLargeFiber4Block2Chunk3ParentMapCheck 6
    && tttLargeFiber4Block2Chunk3ParentMapCheck 7
    && tttLargeFiber4Block2Chunk3ParentMapCheck 8
    && tttLargeFiber4Block2Chunk3ParentMapCheck 9
    && tttLargeFiber4Block2Chunk3ParentMapCheck 10
    && tttLargeFiber4Block2Chunk3ParentMapCheck 11
    && tttLargeFiber4Block2Chunk3ParentMapCheck 12
    && tttLargeFiber4Block2Chunk3ParentMapCheck 13
    && tttLargeFiber4Block2Chunk3ParentMapCheck 14
    && tttLargeFiber4Block2Chunk3ParentMapCheck 15

theorem tttLargeFiber4Block2Chunk3ParentMapAudit_ok :
    tttLargeFiber4Block2Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber4Block2Chunk3ParentMapAudit,
    tttLargeFiber4Block2Chunk3ParentMap_0_ok,
    tttLargeFiber4Block2Chunk3ParentMap_1_ok,
    tttLargeFiber4Block2Chunk3ParentMap_2_ok,
    tttLargeFiber4Block2Chunk3ParentMap_3_ok,
    tttLargeFiber4Block2Chunk3ParentMap_4_ok,
    tttLargeFiber4Block2Chunk3ParentMap_5_ok,
    tttLargeFiber4Block2Chunk3ParentMap_6_ok,
    tttLargeFiber4Block2Chunk3ParentMap_7_ok,
    tttLargeFiber4Block2Chunk3ParentMap_8_ok,
    tttLargeFiber4Block2Chunk3ParentMap_9_ok,
    tttLargeFiber4Block2Chunk3ParentMap_10_ok,
    tttLargeFiber4Block2Chunk3ParentMap_11_ok,
    tttLargeFiber4Block2Chunk3ParentMap_12_ok,
    tttLargeFiber4Block2Chunk3ParentMap_13_ok,
    tttLargeFiber4Block2Chunk3ParentMap_14_ok,
    tttLargeFiber4Block2Chunk3ParentMap_15_ok]

def tttLargeFiber4Block2Chunk3ParentsAudit : Bool :=
  tttLargeFiber4Block2Chunk3ParentPathCheck 0
    && tttLargeFiber4Block2Chunk3ParentPathCheck 1
    && tttLargeFiber4Block2Chunk3ParentPathCheck 2
    && tttLargeFiber4Block2Chunk3ParentPathCheck 3
    && tttLargeFiber4Block2Chunk3ParentPathCheck 4
    && tttLargeFiber4Block2Chunk3ParentPathCheck 5
    && tttLargeFiber4Block2Chunk3ParentPathCheck 6
    && tttLargeFiber4Block2Chunk3ParentPathCheck 7
    && tttLargeFiber4Block2Chunk3ParentPathCheck 8
    && tttLargeFiber4Block2Chunk3ParentPathCheck 9
    && tttLargeFiber4Block2Chunk3ParentPathCheck 10
    && tttLargeFiber4Block2Chunk3ParentPathCheck 11
    && tttLargeFiber4Block2Chunk3ParentPathCheck 12
    && tttLargeFiber4Block2Chunk3ParentPathCheck 13
    && tttLargeFiber4Block2Chunk3ParentPathCheck 14
    && tttLargeFiber4Block2Chunk3ParentPathCheck 15

theorem tttLargeFiber4Block2Chunk3ParentsAudit_ok :
    tttLargeFiber4Block2Chunk3ParentsAudit = true := by
  simp [tttLargeFiber4Block2Chunk3ParentsAudit,
    tttLargeFiber4Block2Chunk3ParentPath_0_ok,
    tttLargeFiber4Block2Chunk3ParentPath_1_ok,
    tttLargeFiber4Block2Chunk3ParentPath_2_ok,
    tttLargeFiber4Block2Chunk3ParentPath_3_ok,
    tttLargeFiber4Block2Chunk3ParentPath_4_ok,
    tttLargeFiber4Block2Chunk3ParentPath_5_ok,
    tttLargeFiber4Block2Chunk3ParentPath_6_ok,
    tttLargeFiber4Block2Chunk3ParentPath_7_ok,
    tttLargeFiber4Block2Chunk3ParentPath_8_ok,
    tttLargeFiber4Block2Chunk3ParentPath_9_ok,
    tttLargeFiber4Block2Chunk3ParentPath_10_ok,
    tttLargeFiber4Block2Chunk3ParentPath_11_ok,
    tttLargeFiber4Block2Chunk3ParentPath_12_ok,
    tttLargeFiber4Block2Chunk3ParentPath_13_ok,
    tttLargeFiber4Block2Chunk3ParentPath_14_ok,
    tttLargeFiber4Block2Chunk3ParentPath_15_ok]

def tttLargeFiber4Block2Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block2Chunk3SourcesCheck &&
    tttLargeFiber4Block2Chunk3RowsAudit &&
    tttLargeFiber4Block2Chunk3ParentMapAudit &&
    tttLargeFiber4Block2Chunk3ParentsAudit

theorem tttLargeFiber4Block2Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber4Block2Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block2Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block2Chunk3SourcesCheck_ok,
    tttLargeFiber4Block2Chunk3RowsAudit_ok,
    tttLargeFiber4Block2Chunk3ParentMapAudit_ok,
    tttLargeFiber4Block2Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block2Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
