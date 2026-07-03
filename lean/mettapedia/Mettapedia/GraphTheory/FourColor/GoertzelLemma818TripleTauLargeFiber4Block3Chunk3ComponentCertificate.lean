import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 3 chunk 3

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
Parent-depth convergence is checked by explicit bounded parent paths rather
than by reducing the recursive parent iterator over large indices.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block3Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block3Chunk3Sources : List Nat :=
  [2416, 2417, 2418, 2419, 2420, 2421, 2422, 2423,
   2424, 2425, 2426, 2427, 2428, 2429, 2430, 2431]

def tttLargeFiber4Row240 : TripleComponentParentRow :=
  tripleRow 2416 2288 67 42 0 65 110 64
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

def tttLargeFiber4Row241 : TripleComponentParentRow :=
  tripleRow 2417 2289 67 42 1 65 110 65
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

def tttLargeFiber4Row242 : TripleComponentParentRow :=
  tripleRow 2418 2290 67 42 2 65 110 66
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

def tttLargeFiber4Row243 : TripleComponentParentRow :=
  tripleRow 2419 2291 67 42 3 65 110 67
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

def tttLargeFiber4Row244 : TripleComponentParentRow :=
  tripleRow 2420 2416 67 42 48 67 42 0
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row245 : TripleComponentParentRow :=
  tripleRow 2421 2417 67 42 49 67 42 1
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row246 : TripleComponentParentRow :=
  tripleRow 2422 2294 67 42 50 65 110 118
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

def tttLargeFiber4Row247 : TripleComponentParentRow :=
  tripleRow 2423 2295 67 42 51 65 110 119
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

def tttLargeFiber4Row248 : TripleComponentParentRow :=
  tripleRow 2424 2296 67 43 8 65 111 72
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

def tttLargeFiber4Row249 : TripleComponentParentRow :=
  tripleRow 2425 2297 67 43 9 65 111 73
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

def tttLargeFiber4Row250 : TripleComponentParentRow :=
  tripleRow 2426 2298 67 43 10 65 111 74
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

def tttLargeFiber4Row251 : TripleComponentParentRow :=
  tripleRow 2427 2299 67 43 11 65 111 75
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

def tttLargeFiber4Row252 : TripleComponentParentRow :=
  tripleRow 2428 2424 67 43 56 67 43 8
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row253 : TripleComponentParentRow :=
  tripleRow 2429 2425 67 43 57 67 43 9
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row254 : TripleComponentParentRow :=
  tripleRow 2430 2302 67 43 58 65 111 126
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

def tttLargeFiber4Row255 : TripleComponentParentRow :=
  tripleRow 2431 2303 67 43 59 65 111 127
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

def tttLargeFiber4Block3Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row240
  , tttLargeFiber4Row241
  , tttLargeFiber4Row242
  , tttLargeFiber4Row243
  , tttLargeFiber4Row244
  , tttLargeFiber4Row245
  , tttLargeFiber4Row246
  , tttLargeFiber4Row247
  , tttLargeFiber4Row248
  , tttLargeFiber4Row249
  , tttLargeFiber4Row250
  , tttLargeFiber4Row251
  , tttLargeFiber4Row252
  , tttLargeFiber4Row253
  , tttLargeFiber4Row254
  , tttLargeFiber4Row255
  ]

def tttLargeFiber4Block3Chunk3SourcesCheck : Bool :=
  (tttLargeFiber4Block3Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber4Block3Chunk3Sources

theorem tttLargeFiber4Block3Chunk3SourcesCheck_ok :
    tttLargeFiber4Block3Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber4Block3Chunk3RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttLargeFiber4Key tttLargeFiber4Expected
    (listGetD tttLargeFiber4Block3Chunk3Rows i default)

def tttLargeFiber4Block3Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block3Chunk3Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block3Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block3Chunk3Sources 0 0 == 2416 &&
      tttLargeFiber4ParentOf 2416 == 2288 &&
      tttLargeFiber4ParentOf 2288 == 2224 &&
      tttLargeFiber4ParentOf 2224 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block3Chunk3Sources 1 0 == 2417 &&
      tttLargeFiber4ParentOf 2417 == 2289 &&
      tttLargeFiber4ParentOf 2289 == 2225 &&
      tttLargeFiber4ParentOf 2225 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block3Chunk3Sources 2 0 == 2418 &&
      tttLargeFiber4ParentOf 2418 == 2290 &&
      tttLargeFiber4ParentOf 2290 == 2226 &&
      tttLargeFiber4ParentOf 2226 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block3Chunk3Sources 3 0 == 2419 &&
      tttLargeFiber4ParentOf 2419 == 2291 &&
      tttLargeFiber4ParentOf 2291 == 2227 &&
      tttLargeFiber4ParentOf 2227 == 2187 &&
      tttLargeFiber4ParentOf 2187 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block3Chunk3Sources 4 0 == 2420 &&
      tttLargeFiber4ParentOf 2420 == 2416 &&
      tttLargeFiber4ParentOf 2416 == 2288 &&
      tttLargeFiber4ParentOf 2288 == 2224 &&
      tttLargeFiber4ParentOf 2224 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block3Chunk3Sources 5 0 == 2421 &&
      tttLargeFiber4ParentOf 2421 == 2417 &&
      tttLargeFiber4ParentOf 2417 == 2289 &&
      tttLargeFiber4ParentOf 2289 == 2225 &&
      tttLargeFiber4ParentOf 2225 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block3Chunk3Sources 6 0 == 2422 &&
      tttLargeFiber4ParentOf 2422 == 2294 &&
      tttLargeFiber4ParentOf 2294 == 2230 &&
      tttLargeFiber4ParentOf 2230 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block3Chunk3Sources 7 0 == 2423 &&
      tttLargeFiber4ParentOf 2423 == 2295 &&
      tttLargeFiber4ParentOf 2295 == 2231 &&
      tttLargeFiber4ParentOf 2231 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block3Chunk3Sources 8 0 == 2424 &&
      tttLargeFiber4ParentOf 2424 == 2296 &&
      tttLargeFiber4ParentOf 2296 == 2232 &&
      tttLargeFiber4ParentOf 2232 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block3Chunk3Sources 9 0 == 2425 &&
      tttLargeFiber4ParentOf 2425 == 2297 &&
      tttLargeFiber4ParentOf 2297 == 2233 &&
      tttLargeFiber4ParentOf 2233 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block3Chunk3Sources 10 0 == 2426 &&
      tttLargeFiber4ParentOf 2426 == 2298 &&
      tttLargeFiber4ParentOf 2298 == 2234 &&
      tttLargeFiber4ParentOf 2234 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block3Chunk3Sources 11 0 == 2427 &&
      tttLargeFiber4ParentOf 2427 == 2299 &&
      tttLargeFiber4ParentOf 2299 == 2235 &&
      tttLargeFiber4ParentOf 2235 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block3Chunk3Sources 12 0 == 2428 &&
      tttLargeFiber4ParentOf 2428 == 2424 &&
      tttLargeFiber4ParentOf 2424 == 2296 &&
      tttLargeFiber4ParentOf 2296 == 2232 &&
      tttLargeFiber4ParentOf 2232 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block3Chunk3Sources 13 0 == 2429 &&
      tttLargeFiber4ParentOf 2429 == 2425 &&
      tttLargeFiber4ParentOf 2425 == 2297 &&
      tttLargeFiber4ParentOf 2297 == 2233 &&
      tttLargeFiber4ParentOf 2233 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block3Chunk3Sources 14 0 == 2430 &&
      tttLargeFiber4ParentOf 2430 == 2302 &&
      tttLargeFiber4ParentOf 2302 == 2238 &&
      tttLargeFiber4ParentOf 2238 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block3Chunk3Sources 15 0 == 2431 &&
      tttLargeFiber4ParentOf 2431 == 2303 &&
      tttLargeFiber4ParentOf 2303 == 2239 &&
      tttLargeFiber4ParentOf 2239 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block3Chunk3Row_0_ok :
    tttLargeFiber4Block3Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3Row_1_ok :
    tttLargeFiber4Block3Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3Row_2_ok :
    tttLargeFiber4Block3Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3Row_3_ok :
    tttLargeFiber4Block3Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3Row_4_ok :
    tttLargeFiber4Block3Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3Row_5_ok :
    tttLargeFiber4Block3Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3Row_6_ok :
    tttLargeFiber4Block3Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3Row_7_ok :
    tttLargeFiber4Block3Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3Row_8_ok :
    tttLargeFiber4Block3Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3Row_9_ok :
    tttLargeFiber4Block3Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3Row_10_ok :
    tttLargeFiber4Block3Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3Row_11_ok :
    tttLargeFiber4Block3Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3Row_12_ok :
    tttLargeFiber4Block3Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3Row_13_ok :
    tttLargeFiber4Block3Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3Row_14_ok :
    tttLargeFiber4Block3Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3Row_15_ok :
    tttLargeFiber4Block3Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentMap_0_ok :
    tttLargeFiber4Block3Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentMap_1_ok :
    tttLargeFiber4Block3Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentMap_2_ok :
    tttLargeFiber4Block3Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentMap_3_ok :
    tttLargeFiber4Block3Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentMap_4_ok :
    tttLargeFiber4Block3Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentMap_5_ok :
    tttLargeFiber4Block3Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentMap_6_ok :
    tttLargeFiber4Block3Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentMap_7_ok :
    tttLargeFiber4Block3Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentMap_8_ok :
    tttLargeFiber4Block3Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentMap_9_ok :
    tttLargeFiber4Block3Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentMap_10_ok :
    tttLargeFiber4Block3Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentMap_11_ok :
    tttLargeFiber4Block3Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentMap_12_ok :
    tttLargeFiber4Block3Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentMap_13_ok :
    tttLargeFiber4Block3Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentMap_14_ok :
    tttLargeFiber4Block3Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentMap_15_ok :
    tttLargeFiber4Block3Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentPath_0_ok :
    tttLargeFiber4Block3Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentPath_1_ok :
    tttLargeFiber4Block3Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentPath_2_ok :
    tttLargeFiber4Block3Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentPath_3_ok :
    tttLargeFiber4Block3Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentPath_4_ok :
    tttLargeFiber4Block3Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentPath_5_ok :
    tttLargeFiber4Block3Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentPath_6_ok :
    tttLargeFiber4Block3Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentPath_7_ok :
    tttLargeFiber4Block3Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentPath_8_ok :
    tttLargeFiber4Block3Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentPath_9_ok :
    tttLargeFiber4Block3Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentPath_10_ok :
    tttLargeFiber4Block3Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentPath_11_ok :
    tttLargeFiber4Block3Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentPath_12_ok :
    tttLargeFiber4Block3Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentPath_13_ok :
    tttLargeFiber4Block3Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentPath_14_ok :
    tttLargeFiber4Block3Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block3Chunk3ParentPath_15_ok :
    tttLargeFiber4Block3Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block3Chunk3RowsAudit : Bool :=
  tttLargeFiber4Block3Chunk3RowCheck 0
    && tttLargeFiber4Block3Chunk3RowCheck 1
    && tttLargeFiber4Block3Chunk3RowCheck 2
    && tttLargeFiber4Block3Chunk3RowCheck 3
    && tttLargeFiber4Block3Chunk3RowCheck 4
    && tttLargeFiber4Block3Chunk3RowCheck 5
    && tttLargeFiber4Block3Chunk3RowCheck 6
    && tttLargeFiber4Block3Chunk3RowCheck 7
    && tttLargeFiber4Block3Chunk3RowCheck 8
    && tttLargeFiber4Block3Chunk3RowCheck 9
    && tttLargeFiber4Block3Chunk3RowCheck 10
    && tttLargeFiber4Block3Chunk3RowCheck 11
    && tttLargeFiber4Block3Chunk3RowCheck 12
    && tttLargeFiber4Block3Chunk3RowCheck 13
    && tttLargeFiber4Block3Chunk3RowCheck 14
    && tttLargeFiber4Block3Chunk3RowCheck 15

theorem tttLargeFiber4Block3Chunk3RowsAudit_ok :
    tttLargeFiber4Block3Chunk3RowsAudit = true := by
  simp [tttLargeFiber4Block3Chunk3RowsAudit,
    tttLargeFiber4Block3Chunk3Row_0_ok,
    tttLargeFiber4Block3Chunk3Row_1_ok,
    tttLargeFiber4Block3Chunk3Row_2_ok,
    tttLargeFiber4Block3Chunk3Row_3_ok,
    tttLargeFiber4Block3Chunk3Row_4_ok,
    tttLargeFiber4Block3Chunk3Row_5_ok,
    tttLargeFiber4Block3Chunk3Row_6_ok,
    tttLargeFiber4Block3Chunk3Row_7_ok,
    tttLargeFiber4Block3Chunk3Row_8_ok,
    tttLargeFiber4Block3Chunk3Row_9_ok,
    tttLargeFiber4Block3Chunk3Row_10_ok,
    tttLargeFiber4Block3Chunk3Row_11_ok,
    tttLargeFiber4Block3Chunk3Row_12_ok,
    tttLargeFiber4Block3Chunk3Row_13_ok,
    tttLargeFiber4Block3Chunk3Row_14_ok,
    tttLargeFiber4Block3Chunk3Row_15_ok]

def tttLargeFiber4Block3Chunk3ParentMapAudit : Bool :=
  tttLargeFiber4Block3Chunk3ParentMapCheck 0
    && tttLargeFiber4Block3Chunk3ParentMapCheck 1
    && tttLargeFiber4Block3Chunk3ParentMapCheck 2
    && tttLargeFiber4Block3Chunk3ParentMapCheck 3
    && tttLargeFiber4Block3Chunk3ParentMapCheck 4
    && tttLargeFiber4Block3Chunk3ParentMapCheck 5
    && tttLargeFiber4Block3Chunk3ParentMapCheck 6
    && tttLargeFiber4Block3Chunk3ParentMapCheck 7
    && tttLargeFiber4Block3Chunk3ParentMapCheck 8
    && tttLargeFiber4Block3Chunk3ParentMapCheck 9
    && tttLargeFiber4Block3Chunk3ParentMapCheck 10
    && tttLargeFiber4Block3Chunk3ParentMapCheck 11
    && tttLargeFiber4Block3Chunk3ParentMapCheck 12
    && tttLargeFiber4Block3Chunk3ParentMapCheck 13
    && tttLargeFiber4Block3Chunk3ParentMapCheck 14
    && tttLargeFiber4Block3Chunk3ParentMapCheck 15

theorem tttLargeFiber4Block3Chunk3ParentMapAudit_ok :
    tttLargeFiber4Block3Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber4Block3Chunk3ParentMapAudit,
    tttLargeFiber4Block3Chunk3ParentMap_0_ok,
    tttLargeFiber4Block3Chunk3ParentMap_1_ok,
    tttLargeFiber4Block3Chunk3ParentMap_2_ok,
    tttLargeFiber4Block3Chunk3ParentMap_3_ok,
    tttLargeFiber4Block3Chunk3ParentMap_4_ok,
    tttLargeFiber4Block3Chunk3ParentMap_5_ok,
    tttLargeFiber4Block3Chunk3ParentMap_6_ok,
    tttLargeFiber4Block3Chunk3ParentMap_7_ok,
    tttLargeFiber4Block3Chunk3ParentMap_8_ok,
    tttLargeFiber4Block3Chunk3ParentMap_9_ok,
    tttLargeFiber4Block3Chunk3ParentMap_10_ok,
    tttLargeFiber4Block3Chunk3ParentMap_11_ok,
    tttLargeFiber4Block3Chunk3ParentMap_12_ok,
    tttLargeFiber4Block3Chunk3ParentMap_13_ok,
    tttLargeFiber4Block3Chunk3ParentMap_14_ok,
    tttLargeFiber4Block3Chunk3ParentMap_15_ok]

def tttLargeFiber4Block3Chunk3ParentsAudit : Bool :=
  tttLargeFiber4Block3Chunk3ParentPathCheck 0
    && tttLargeFiber4Block3Chunk3ParentPathCheck 1
    && tttLargeFiber4Block3Chunk3ParentPathCheck 2
    && tttLargeFiber4Block3Chunk3ParentPathCheck 3
    && tttLargeFiber4Block3Chunk3ParentPathCheck 4
    && tttLargeFiber4Block3Chunk3ParentPathCheck 5
    && tttLargeFiber4Block3Chunk3ParentPathCheck 6
    && tttLargeFiber4Block3Chunk3ParentPathCheck 7
    && tttLargeFiber4Block3Chunk3ParentPathCheck 8
    && tttLargeFiber4Block3Chunk3ParentPathCheck 9
    && tttLargeFiber4Block3Chunk3ParentPathCheck 10
    && tttLargeFiber4Block3Chunk3ParentPathCheck 11
    && tttLargeFiber4Block3Chunk3ParentPathCheck 12
    && tttLargeFiber4Block3Chunk3ParentPathCheck 13
    && tttLargeFiber4Block3Chunk3ParentPathCheck 14
    && tttLargeFiber4Block3Chunk3ParentPathCheck 15

theorem tttLargeFiber4Block3Chunk3ParentsAudit_ok :
    tttLargeFiber4Block3Chunk3ParentsAudit = true := by
  simp [tttLargeFiber4Block3Chunk3ParentsAudit,
    tttLargeFiber4Block3Chunk3ParentPath_0_ok,
    tttLargeFiber4Block3Chunk3ParentPath_1_ok,
    tttLargeFiber4Block3Chunk3ParentPath_2_ok,
    tttLargeFiber4Block3Chunk3ParentPath_3_ok,
    tttLargeFiber4Block3Chunk3ParentPath_4_ok,
    tttLargeFiber4Block3Chunk3ParentPath_5_ok,
    tttLargeFiber4Block3Chunk3ParentPath_6_ok,
    tttLargeFiber4Block3Chunk3ParentPath_7_ok,
    tttLargeFiber4Block3Chunk3ParentPath_8_ok,
    tttLargeFiber4Block3Chunk3ParentPath_9_ok,
    tttLargeFiber4Block3Chunk3ParentPath_10_ok,
    tttLargeFiber4Block3Chunk3ParentPath_11_ok,
    tttLargeFiber4Block3Chunk3ParentPath_12_ok,
    tttLargeFiber4Block3Chunk3ParentPath_13_ok,
    tttLargeFiber4Block3Chunk3ParentPath_14_ok,
    tttLargeFiber4Block3Chunk3ParentPath_15_ok]

def tttLargeFiber4Block3Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block3Chunk3SourcesCheck &&
    tttLargeFiber4Block3Chunk3RowsAudit &&
    tttLargeFiber4Block3Chunk3ParentMapAudit &&
    tttLargeFiber4Block3Chunk3ParentsAudit

theorem tttLargeFiber4Block3Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber4Block3Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block3Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block3Chunk3SourcesCheck_ok,
    tttLargeFiber4Block3Chunk3RowsAudit_ok,
    tttLargeFiber4Block3Chunk3ParentMapAudit_ok,
    tttLargeFiber4Block3Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block3Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
