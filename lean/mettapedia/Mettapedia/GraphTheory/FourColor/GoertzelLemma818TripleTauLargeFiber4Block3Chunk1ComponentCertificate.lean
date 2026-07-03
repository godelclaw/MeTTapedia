import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 3 chunk 1

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
Parent-depth convergence is checked by explicit bounded parent paths rather
than by reducing the recursive parent iterator over large indices.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block3Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block3Chunk1Sources : List Nat :=
  [2384, 2385, 2386, 2387, 2388, 2389, 2390, 2391,
   2392, 2393, 2394, 2395, 2396, 2397, 2398, 2399]

def tttLargeFiber4Row208 : TripleComponentParentRow :=
  tripleRow 2384 2256 67 26 16 65 90 16
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row209 : TripleComponentParentRow :=
  tripleRow 2385 2257 67 26 17 65 90 17
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row210 : TripleComponentParentRow :=
  tripleRow 2386 2258 67 26 18 65 90 18
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row211 : TripleComponentParentRow :=
  tripleRow 2387 2259 67 26 19 65 90 19
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row212 : TripleComponentParentRow :=
  tripleRow 2388 2260 67 26 32 65 90 32
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row213 : TripleComponentParentRow :=
  tripleRow 2389 2261 67 26 33 65 90 33
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row214 : TripleComponentParentRow :=
  tripleRow 2390 2262 67 26 34 65 90 34
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row215 : TripleComponentParentRow :=
  tripleRow 2391 2263 67 26 35 65 90 35
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row216 : TripleComponentParentRow :=
  tripleRow 2392 2264 67 27 24 65 91 24
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row217 : TripleComponentParentRow :=
  tripleRow 2393 2265 67 27 25 65 91 25
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row218 : TripleComponentParentRow :=
  tripleRow 2394 2266 67 27 26 65 91 26
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row219 : TripleComponentParentRow :=
  tripleRow 2395 2267 67 27 27 65 91 27
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row220 : TripleComponentParentRow :=
  tripleRow 2396 2268 67 27 40 65 91 40
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row221 : TripleComponentParentRow :=
  tripleRow 2397 2269 67 27 41 65 91 41
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row222 : TripleComponentParentRow :=
  tripleRow 2398 2270 67 27 42 65 91 42
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row223 : TripleComponentParentRow :=
  tripleRow 2399 2271 67 27 43 65 91 43
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Block3Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row208
  , tttLargeFiber4Row209
  , tttLargeFiber4Row210
  , tttLargeFiber4Row211
  , tttLargeFiber4Row212
  , tttLargeFiber4Row213
  , tttLargeFiber4Row214
  , tttLargeFiber4Row215
  , tttLargeFiber4Row216
  , tttLargeFiber4Row217
  , tttLargeFiber4Row218
  , tttLargeFiber4Row219
  , tttLargeFiber4Row220
  , tttLargeFiber4Row221
  , tttLargeFiber4Row222
  , tttLargeFiber4Row223
  ]

def tttLargeFiber4Block3Chunk1SourcesCheck : Bool :=
  (tttLargeFiber4Block3Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber4Block3Chunk1Sources

theorem tttLargeFiber4Block3Chunk1SourcesCheck_ok :
    tttLargeFiber4Block3Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber4Block3Chunk1RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttLargeFiber4Key tttLargeFiber4Expected
    (listGetD tttLargeFiber4Block3Chunk1Rows i default)

def tttLargeFiber4Block3Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block3Chunk1Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block3Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block3Chunk1Sources 0 0 == 2384 &&
      tttLargeFiber4ParentOf 2384 == 2256 &&
      tttLargeFiber4ParentOf 2256 == 2192 &&
      tttLargeFiber4ParentOf 2192 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block3Chunk1Sources 1 0 == 2385 &&
      tttLargeFiber4ParentOf 2385 == 2257 &&
      tttLargeFiber4ParentOf 2257 == 2193 &&
      tttLargeFiber4ParentOf 2193 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block3Chunk1Sources 2 0 == 2386 &&
      tttLargeFiber4ParentOf 2386 == 2258 &&
      tttLargeFiber4ParentOf 2258 == 2194 &&
      tttLargeFiber4ParentOf 2194 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block3Chunk1Sources 3 0 == 2387 &&
      tttLargeFiber4ParentOf 2387 == 2259 &&
      tttLargeFiber4ParentOf 2259 == 2195 &&
      tttLargeFiber4ParentOf 2195 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block3Chunk1Sources 4 0 == 2388 &&
      tttLargeFiber4ParentOf 2388 == 2260 &&
      tttLargeFiber4ParentOf 2260 == 2196 &&
      tttLargeFiber4ParentOf 2196 == 2192 &&
      tttLargeFiber4ParentOf 2192 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block3Chunk1Sources 5 0 == 2389 &&
      tttLargeFiber4ParentOf 2389 == 2261 &&
      tttLargeFiber4ParentOf 2261 == 2197 &&
      tttLargeFiber4ParentOf 2197 == 2193 &&
      tttLargeFiber4ParentOf 2193 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block3Chunk1Sources 6 0 == 2390 &&
      tttLargeFiber4ParentOf 2390 == 2262 &&
      tttLargeFiber4ParentOf 2262 == 2198 &&
      tttLargeFiber4ParentOf 2198 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block3Chunk1Sources 7 0 == 2391 &&
      tttLargeFiber4ParentOf 2391 == 2263 &&
      tttLargeFiber4ParentOf 2263 == 2199 &&
      tttLargeFiber4ParentOf 2199 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block3Chunk1Sources 8 0 == 2392 &&
      tttLargeFiber4ParentOf 2392 == 2264 &&
      tttLargeFiber4ParentOf 2264 == 2200 &&
      tttLargeFiber4ParentOf 2200 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block3Chunk1Sources 9 0 == 2393 &&
      tttLargeFiber4ParentOf 2393 == 2265 &&
      tttLargeFiber4ParentOf 2265 == 2201 &&
      tttLargeFiber4ParentOf 2201 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block3Chunk1Sources 10 0 == 2394 &&
      tttLargeFiber4ParentOf 2394 == 2266 &&
      tttLargeFiber4ParentOf 2266 == 2202 &&
      tttLargeFiber4ParentOf 2202 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block3Chunk1Sources 11 0 == 2395 &&
      tttLargeFiber4ParentOf 2395 == 2267 &&
      tttLargeFiber4ParentOf 2267 == 2203 &&
      tttLargeFiber4ParentOf 2203 == 2187 &&
      tttLargeFiber4ParentOf 2187 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block3Chunk1Sources 12 0 == 2396 &&
      tttLargeFiber4ParentOf 2396 == 2268 &&
      tttLargeFiber4ParentOf 2268 == 2204 &&
      tttLargeFiber4ParentOf 2204 == 2200 &&
      tttLargeFiber4ParentOf 2200 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block3Chunk1Sources 13 0 == 2397 &&
      tttLargeFiber4ParentOf 2397 == 2269 &&
      tttLargeFiber4ParentOf 2269 == 2205 &&
      tttLargeFiber4ParentOf 2205 == 2201 &&
      tttLargeFiber4ParentOf 2201 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block3Chunk1Sources 14 0 == 2398 &&
      tttLargeFiber4ParentOf 2398 == 2270 &&
      tttLargeFiber4ParentOf 2270 == 2206 &&
      tttLargeFiber4ParentOf 2206 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block3Chunk1Sources 15 0 == 2399 &&
      tttLargeFiber4ParentOf 2399 == 2271 &&
      tttLargeFiber4ParentOf 2271 == 2207 &&
      tttLargeFiber4ParentOf 2207 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block3Chunk1Row_0_ok :
    tttLargeFiber4Block3Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1Row_1_ok :
    tttLargeFiber4Block3Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1Row_2_ok :
    tttLargeFiber4Block3Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1Row_3_ok :
    tttLargeFiber4Block3Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1Row_4_ok :
    tttLargeFiber4Block3Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1Row_5_ok :
    tttLargeFiber4Block3Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1Row_6_ok :
    tttLargeFiber4Block3Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1Row_7_ok :
    tttLargeFiber4Block3Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1Row_8_ok :
    tttLargeFiber4Block3Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1Row_9_ok :
    tttLargeFiber4Block3Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1Row_10_ok :
    tttLargeFiber4Block3Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1Row_11_ok :
    tttLargeFiber4Block3Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1Row_12_ok :
    tttLargeFiber4Block3Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1Row_13_ok :
    tttLargeFiber4Block3Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1Row_14_ok :
    tttLargeFiber4Block3Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1Row_15_ok :
    tttLargeFiber4Block3Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentMap_0_ok :
    tttLargeFiber4Block3Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentMap_1_ok :
    tttLargeFiber4Block3Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentMap_2_ok :
    tttLargeFiber4Block3Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentMap_3_ok :
    tttLargeFiber4Block3Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentMap_4_ok :
    tttLargeFiber4Block3Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentMap_5_ok :
    tttLargeFiber4Block3Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentMap_6_ok :
    tttLargeFiber4Block3Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentMap_7_ok :
    tttLargeFiber4Block3Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentMap_8_ok :
    tttLargeFiber4Block3Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentMap_9_ok :
    tttLargeFiber4Block3Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentMap_10_ok :
    tttLargeFiber4Block3Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentMap_11_ok :
    tttLargeFiber4Block3Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentMap_12_ok :
    tttLargeFiber4Block3Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentMap_13_ok :
    tttLargeFiber4Block3Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentMap_14_ok :
    tttLargeFiber4Block3Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentMap_15_ok :
    tttLargeFiber4Block3Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentPath_0_ok :
    tttLargeFiber4Block3Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentPath_1_ok :
    tttLargeFiber4Block3Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentPath_2_ok :
    tttLargeFiber4Block3Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentPath_3_ok :
    tttLargeFiber4Block3Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentPath_4_ok :
    tttLargeFiber4Block3Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentPath_5_ok :
    tttLargeFiber4Block3Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentPath_6_ok :
    tttLargeFiber4Block3Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentPath_7_ok :
    tttLargeFiber4Block3Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentPath_8_ok :
    tttLargeFiber4Block3Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentPath_9_ok :
    tttLargeFiber4Block3Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentPath_10_ok :
    tttLargeFiber4Block3Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentPath_11_ok :
    tttLargeFiber4Block3Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentPath_12_ok :
    tttLargeFiber4Block3Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentPath_13_ok :
    tttLargeFiber4Block3Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentPath_14_ok :
    tttLargeFiber4Block3Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block3Chunk1ParentPath_15_ok :
    tttLargeFiber4Block3Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block3Chunk1RowsAudit : Bool :=
  tttLargeFiber4Block3Chunk1RowCheck 0
    && tttLargeFiber4Block3Chunk1RowCheck 1
    && tttLargeFiber4Block3Chunk1RowCheck 2
    && tttLargeFiber4Block3Chunk1RowCheck 3
    && tttLargeFiber4Block3Chunk1RowCheck 4
    && tttLargeFiber4Block3Chunk1RowCheck 5
    && tttLargeFiber4Block3Chunk1RowCheck 6
    && tttLargeFiber4Block3Chunk1RowCheck 7
    && tttLargeFiber4Block3Chunk1RowCheck 8
    && tttLargeFiber4Block3Chunk1RowCheck 9
    && tttLargeFiber4Block3Chunk1RowCheck 10
    && tttLargeFiber4Block3Chunk1RowCheck 11
    && tttLargeFiber4Block3Chunk1RowCheck 12
    && tttLargeFiber4Block3Chunk1RowCheck 13
    && tttLargeFiber4Block3Chunk1RowCheck 14
    && tttLargeFiber4Block3Chunk1RowCheck 15

theorem tttLargeFiber4Block3Chunk1RowsAudit_ok :
    tttLargeFiber4Block3Chunk1RowsAudit = true := by
  simp [tttLargeFiber4Block3Chunk1RowsAudit,
    tttLargeFiber4Block3Chunk1Row_0_ok,
    tttLargeFiber4Block3Chunk1Row_1_ok,
    tttLargeFiber4Block3Chunk1Row_2_ok,
    tttLargeFiber4Block3Chunk1Row_3_ok,
    tttLargeFiber4Block3Chunk1Row_4_ok,
    tttLargeFiber4Block3Chunk1Row_5_ok,
    tttLargeFiber4Block3Chunk1Row_6_ok,
    tttLargeFiber4Block3Chunk1Row_7_ok,
    tttLargeFiber4Block3Chunk1Row_8_ok,
    tttLargeFiber4Block3Chunk1Row_9_ok,
    tttLargeFiber4Block3Chunk1Row_10_ok,
    tttLargeFiber4Block3Chunk1Row_11_ok,
    tttLargeFiber4Block3Chunk1Row_12_ok,
    tttLargeFiber4Block3Chunk1Row_13_ok,
    tttLargeFiber4Block3Chunk1Row_14_ok,
    tttLargeFiber4Block3Chunk1Row_15_ok]

def tttLargeFiber4Block3Chunk1ParentMapAudit : Bool :=
  tttLargeFiber4Block3Chunk1ParentMapCheck 0
    && tttLargeFiber4Block3Chunk1ParentMapCheck 1
    && tttLargeFiber4Block3Chunk1ParentMapCheck 2
    && tttLargeFiber4Block3Chunk1ParentMapCheck 3
    && tttLargeFiber4Block3Chunk1ParentMapCheck 4
    && tttLargeFiber4Block3Chunk1ParentMapCheck 5
    && tttLargeFiber4Block3Chunk1ParentMapCheck 6
    && tttLargeFiber4Block3Chunk1ParentMapCheck 7
    && tttLargeFiber4Block3Chunk1ParentMapCheck 8
    && tttLargeFiber4Block3Chunk1ParentMapCheck 9
    && tttLargeFiber4Block3Chunk1ParentMapCheck 10
    && tttLargeFiber4Block3Chunk1ParentMapCheck 11
    && tttLargeFiber4Block3Chunk1ParentMapCheck 12
    && tttLargeFiber4Block3Chunk1ParentMapCheck 13
    && tttLargeFiber4Block3Chunk1ParentMapCheck 14
    && tttLargeFiber4Block3Chunk1ParentMapCheck 15

theorem tttLargeFiber4Block3Chunk1ParentMapAudit_ok :
    tttLargeFiber4Block3Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber4Block3Chunk1ParentMapAudit,
    tttLargeFiber4Block3Chunk1ParentMap_0_ok,
    tttLargeFiber4Block3Chunk1ParentMap_1_ok,
    tttLargeFiber4Block3Chunk1ParentMap_2_ok,
    tttLargeFiber4Block3Chunk1ParentMap_3_ok,
    tttLargeFiber4Block3Chunk1ParentMap_4_ok,
    tttLargeFiber4Block3Chunk1ParentMap_5_ok,
    tttLargeFiber4Block3Chunk1ParentMap_6_ok,
    tttLargeFiber4Block3Chunk1ParentMap_7_ok,
    tttLargeFiber4Block3Chunk1ParentMap_8_ok,
    tttLargeFiber4Block3Chunk1ParentMap_9_ok,
    tttLargeFiber4Block3Chunk1ParentMap_10_ok,
    tttLargeFiber4Block3Chunk1ParentMap_11_ok,
    tttLargeFiber4Block3Chunk1ParentMap_12_ok,
    tttLargeFiber4Block3Chunk1ParentMap_13_ok,
    tttLargeFiber4Block3Chunk1ParentMap_14_ok,
    tttLargeFiber4Block3Chunk1ParentMap_15_ok]

def tttLargeFiber4Block3Chunk1ParentsAudit : Bool :=
  tttLargeFiber4Block3Chunk1ParentPathCheck 0
    && tttLargeFiber4Block3Chunk1ParentPathCheck 1
    && tttLargeFiber4Block3Chunk1ParentPathCheck 2
    && tttLargeFiber4Block3Chunk1ParentPathCheck 3
    && tttLargeFiber4Block3Chunk1ParentPathCheck 4
    && tttLargeFiber4Block3Chunk1ParentPathCheck 5
    && tttLargeFiber4Block3Chunk1ParentPathCheck 6
    && tttLargeFiber4Block3Chunk1ParentPathCheck 7
    && tttLargeFiber4Block3Chunk1ParentPathCheck 8
    && tttLargeFiber4Block3Chunk1ParentPathCheck 9
    && tttLargeFiber4Block3Chunk1ParentPathCheck 10
    && tttLargeFiber4Block3Chunk1ParentPathCheck 11
    && tttLargeFiber4Block3Chunk1ParentPathCheck 12
    && tttLargeFiber4Block3Chunk1ParentPathCheck 13
    && tttLargeFiber4Block3Chunk1ParentPathCheck 14
    && tttLargeFiber4Block3Chunk1ParentPathCheck 15

theorem tttLargeFiber4Block3Chunk1ParentsAudit_ok :
    tttLargeFiber4Block3Chunk1ParentsAudit = true := by
  simp [tttLargeFiber4Block3Chunk1ParentsAudit,
    tttLargeFiber4Block3Chunk1ParentPath_0_ok,
    tttLargeFiber4Block3Chunk1ParentPath_1_ok,
    tttLargeFiber4Block3Chunk1ParentPath_2_ok,
    tttLargeFiber4Block3Chunk1ParentPath_3_ok,
    tttLargeFiber4Block3Chunk1ParentPath_4_ok,
    tttLargeFiber4Block3Chunk1ParentPath_5_ok,
    tttLargeFiber4Block3Chunk1ParentPath_6_ok,
    tttLargeFiber4Block3Chunk1ParentPath_7_ok,
    tttLargeFiber4Block3Chunk1ParentPath_8_ok,
    tttLargeFiber4Block3Chunk1ParentPath_9_ok,
    tttLargeFiber4Block3Chunk1ParentPath_10_ok,
    tttLargeFiber4Block3Chunk1ParentPath_11_ok,
    tttLargeFiber4Block3Chunk1ParentPath_12_ok,
    tttLargeFiber4Block3Chunk1ParentPath_13_ok,
    tttLargeFiber4Block3Chunk1ParentPath_14_ok,
    tttLargeFiber4Block3Chunk1ParentPath_15_ok]

def tttLargeFiber4Block3Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block3Chunk1SourcesCheck &&
    tttLargeFiber4Block3Chunk1RowsAudit &&
    tttLargeFiber4Block3Chunk1ParentMapAudit &&
    tttLargeFiber4Block3Chunk1ParentsAudit

theorem tttLargeFiber4Block3Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber4Block3Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block3Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block3Chunk1SourcesCheck_ok,
    tttLargeFiber4Block3Chunk1RowsAudit_ok,
    tttLargeFiber4Block3Chunk1ParentMapAudit_ok,
    tttLargeFiber4Block3Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block3Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
