import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 3 chunk 2

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
Parent-depth convergence is checked by explicit bounded parent paths rather
than by reducing the recursive parent iterator over large indices.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block3Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block3Chunk2Sources : List Nat :=
  [2400, 2401, 2402, 2403, 2404, 2405, 2406, 2407,
   2408, 2409, 2410, 2411, 2412, 2413, 2414, 2415]

def tttLargeFiber4Row224 : TripleComponentParentRow :=
  tripleRow 2400 2368 67 40 148 67 24 80
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

def tttLargeFiber4Row225 : TripleComponentParentRow :=
  tripleRow 2401 2369 67 40 149 67 24 81
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

def tttLargeFiber4Row226 : TripleComponentParentRow :=
  tripleRow 2402 2370 67 40 150 67 24 82
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

def tttLargeFiber4Row227 : TripleComponentParentRow :=
  tripleRow 2403 2400 67 40 151 67 40 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row228 : TripleComponentParentRow :=
  tripleRow 2404 2400 67 40 164 67 40 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber4Row229 : TripleComponentParentRow :=
  tripleRow 2405 2401 67 40 165 67 40 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber4Row230 : TripleComponentParentRow :=
  tripleRow 2406 2374 67 40 166 67 24 102
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber4Row231 : TripleComponentParentRow :=
  tripleRow 2407 2375 67 40 167 67 24 103
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber4Row232 : TripleComponentParentRow :=
  tripleRow 2408 2376 67 41 156 67 25 88
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

def tttLargeFiber4Row233 : TripleComponentParentRow :=
  tripleRow 2409 2377 67 41 157 67 25 89
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

def tttLargeFiber4Row234 : TripleComponentParentRow :=
  tripleRow 2410 2378 67 41 158 67 25 90
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

def tttLargeFiber4Row235 : TripleComponentParentRow :=
  tripleRow 2411 2408 67 41 159 67 41 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row236 : TripleComponentParentRow :=
  tripleRow 2412 2408 67 41 172 67 41 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber4Row237 : TripleComponentParentRow :=
  tripleRow 2413 2409 67 41 173 67 41 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber4Row238 : TripleComponentParentRow :=
  tripleRow 2414 2382 67 41 174 67 25 110
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber4Row239 : TripleComponentParentRow :=
  tripleRow 2415 2383 67 41 175 67 25 111
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber4Block3Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row224
  , tttLargeFiber4Row225
  , tttLargeFiber4Row226
  , tttLargeFiber4Row227
  , tttLargeFiber4Row228
  , tttLargeFiber4Row229
  , tttLargeFiber4Row230
  , tttLargeFiber4Row231
  , tttLargeFiber4Row232
  , tttLargeFiber4Row233
  , tttLargeFiber4Row234
  , tttLargeFiber4Row235
  , tttLargeFiber4Row236
  , tttLargeFiber4Row237
  , tttLargeFiber4Row238
  , tttLargeFiber4Row239
  ]

def tttLargeFiber4Block3Chunk2SourcesCheck : Bool :=
  (tttLargeFiber4Block3Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber4Block3Chunk2Sources

theorem tttLargeFiber4Block3Chunk2SourcesCheck_ok :
    tttLargeFiber4Block3Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber4Block3Chunk2RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttLargeFiber4Key tttLargeFiber4Expected
    (listGetD tttLargeFiber4Block3Chunk2Rows i default)

def tttLargeFiber4Block3Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block3Chunk2Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block3Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block3Chunk2Sources 0 0 == 2400 &&
      tttLargeFiber4ParentOf 2400 == 2368 &&
      tttLargeFiber4ParentOf 2368 == 2240 &&
      tttLargeFiber4ParentOf 2240 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block3Chunk2Sources 1 0 == 2401 &&
      tttLargeFiber4ParentOf 2401 == 2369 &&
      tttLargeFiber4ParentOf 2369 == 2241 &&
      tttLargeFiber4ParentOf 2241 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block3Chunk2Sources 2 0 == 2402 &&
      tttLargeFiber4ParentOf 2402 == 2370 &&
      tttLargeFiber4ParentOf 2370 == 2242 &&
      tttLargeFiber4ParentOf 2242 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block3Chunk2Sources 3 0 == 2403 &&
      tttLargeFiber4ParentOf 2403 == 2400 &&
      tttLargeFiber4ParentOf 2400 == 2368 &&
      tttLargeFiber4ParentOf 2368 == 2240 &&
      tttLargeFiber4ParentOf 2240 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block3Chunk2Sources 4 0 == 2404 &&
      tttLargeFiber4ParentOf 2404 == 2400 &&
      tttLargeFiber4ParentOf 2400 == 2368 &&
      tttLargeFiber4ParentOf 2368 == 2240 &&
      tttLargeFiber4ParentOf 2240 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block3Chunk2Sources 5 0 == 2405 &&
      tttLargeFiber4ParentOf 2405 == 2401 &&
      tttLargeFiber4ParentOf 2401 == 2369 &&
      tttLargeFiber4ParentOf 2369 == 2241 &&
      tttLargeFiber4ParentOf 2241 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block3Chunk2Sources 6 0 == 2406 &&
      tttLargeFiber4ParentOf 2406 == 2374 &&
      tttLargeFiber4ParentOf 2374 == 2246 &&
      tttLargeFiber4ParentOf 2246 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block3Chunk2Sources 7 0 == 2407 &&
      tttLargeFiber4ParentOf 2407 == 2375 &&
      tttLargeFiber4ParentOf 2375 == 2247 &&
      tttLargeFiber4ParentOf 2247 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block3Chunk2Sources 8 0 == 2408 &&
      tttLargeFiber4ParentOf 2408 == 2376 &&
      tttLargeFiber4ParentOf 2376 == 2248 &&
      tttLargeFiber4ParentOf 2248 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block3Chunk2Sources 9 0 == 2409 &&
      tttLargeFiber4ParentOf 2409 == 2377 &&
      tttLargeFiber4ParentOf 2377 == 2249 &&
      tttLargeFiber4ParentOf 2249 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block3Chunk2Sources 10 0 == 2410 &&
      tttLargeFiber4ParentOf 2410 == 2378 &&
      tttLargeFiber4ParentOf 2378 == 2250 &&
      tttLargeFiber4ParentOf 2250 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block3Chunk2Sources 11 0 == 2411 &&
      tttLargeFiber4ParentOf 2411 == 2408 &&
      tttLargeFiber4ParentOf 2408 == 2376 &&
      tttLargeFiber4ParentOf 2376 == 2248 &&
      tttLargeFiber4ParentOf 2248 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block3Chunk2Sources 12 0 == 2412 &&
      tttLargeFiber4ParentOf 2412 == 2408 &&
      tttLargeFiber4ParentOf 2408 == 2376 &&
      tttLargeFiber4ParentOf 2376 == 2248 &&
      tttLargeFiber4ParentOf 2248 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block3Chunk2Sources 13 0 == 2413 &&
      tttLargeFiber4ParentOf 2413 == 2409 &&
      tttLargeFiber4ParentOf 2409 == 2377 &&
      tttLargeFiber4ParentOf 2377 == 2249 &&
      tttLargeFiber4ParentOf 2249 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block3Chunk2Sources 14 0 == 2414 &&
      tttLargeFiber4ParentOf 2414 == 2382 &&
      tttLargeFiber4ParentOf 2382 == 2254 &&
      tttLargeFiber4ParentOf 2254 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block3Chunk2Sources 15 0 == 2415 &&
      tttLargeFiber4ParentOf 2415 == 2383 &&
      tttLargeFiber4ParentOf 2383 == 2255 &&
      tttLargeFiber4ParentOf 2255 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block3Chunk2Row_0_ok :
    tttLargeFiber4Block3Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2Row_1_ok :
    tttLargeFiber4Block3Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2Row_2_ok :
    tttLargeFiber4Block3Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2Row_3_ok :
    tttLargeFiber4Block3Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2Row_4_ok :
    tttLargeFiber4Block3Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2Row_5_ok :
    tttLargeFiber4Block3Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2Row_6_ok :
    tttLargeFiber4Block3Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2Row_7_ok :
    tttLargeFiber4Block3Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2Row_8_ok :
    tttLargeFiber4Block3Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2Row_9_ok :
    tttLargeFiber4Block3Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2Row_10_ok :
    tttLargeFiber4Block3Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2Row_11_ok :
    tttLargeFiber4Block3Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2Row_12_ok :
    tttLargeFiber4Block3Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2Row_13_ok :
    tttLargeFiber4Block3Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2Row_14_ok :
    tttLargeFiber4Block3Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2Row_15_ok :
    tttLargeFiber4Block3Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentMap_0_ok :
    tttLargeFiber4Block3Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentMap_1_ok :
    tttLargeFiber4Block3Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentMap_2_ok :
    tttLargeFiber4Block3Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentMap_3_ok :
    tttLargeFiber4Block3Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentMap_4_ok :
    tttLargeFiber4Block3Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentMap_5_ok :
    tttLargeFiber4Block3Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentMap_6_ok :
    tttLargeFiber4Block3Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentMap_7_ok :
    tttLargeFiber4Block3Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentMap_8_ok :
    tttLargeFiber4Block3Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentMap_9_ok :
    tttLargeFiber4Block3Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentMap_10_ok :
    tttLargeFiber4Block3Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentMap_11_ok :
    tttLargeFiber4Block3Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentMap_12_ok :
    tttLargeFiber4Block3Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentMap_13_ok :
    tttLargeFiber4Block3Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentMap_14_ok :
    tttLargeFiber4Block3Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentMap_15_ok :
    tttLargeFiber4Block3Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentPath_0_ok :
    tttLargeFiber4Block3Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentPath_1_ok :
    tttLargeFiber4Block3Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentPath_2_ok :
    tttLargeFiber4Block3Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentPath_3_ok :
    tttLargeFiber4Block3Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentPath_4_ok :
    tttLargeFiber4Block3Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentPath_5_ok :
    tttLargeFiber4Block3Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentPath_6_ok :
    tttLargeFiber4Block3Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentPath_7_ok :
    tttLargeFiber4Block3Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentPath_8_ok :
    tttLargeFiber4Block3Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentPath_9_ok :
    tttLargeFiber4Block3Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentPath_10_ok :
    tttLargeFiber4Block3Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentPath_11_ok :
    tttLargeFiber4Block3Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentPath_12_ok :
    tttLargeFiber4Block3Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentPath_13_ok :
    tttLargeFiber4Block3Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentPath_14_ok :
    tttLargeFiber4Block3Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block3Chunk2ParentPath_15_ok :
    tttLargeFiber4Block3Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block3Chunk2RowsAudit : Bool :=
  tttLargeFiber4Block3Chunk2RowCheck 0
    && tttLargeFiber4Block3Chunk2RowCheck 1
    && tttLargeFiber4Block3Chunk2RowCheck 2
    && tttLargeFiber4Block3Chunk2RowCheck 3
    && tttLargeFiber4Block3Chunk2RowCheck 4
    && tttLargeFiber4Block3Chunk2RowCheck 5
    && tttLargeFiber4Block3Chunk2RowCheck 6
    && tttLargeFiber4Block3Chunk2RowCheck 7
    && tttLargeFiber4Block3Chunk2RowCheck 8
    && tttLargeFiber4Block3Chunk2RowCheck 9
    && tttLargeFiber4Block3Chunk2RowCheck 10
    && tttLargeFiber4Block3Chunk2RowCheck 11
    && tttLargeFiber4Block3Chunk2RowCheck 12
    && tttLargeFiber4Block3Chunk2RowCheck 13
    && tttLargeFiber4Block3Chunk2RowCheck 14
    && tttLargeFiber4Block3Chunk2RowCheck 15

theorem tttLargeFiber4Block3Chunk2RowsAudit_ok :
    tttLargeFiber4Block3Chunk2RowsAudit = true := by
  simp [tttLargeFiber4Block3Chunk2RowsAudit,
    tttLargeFiber4Block3Chunk2Row_0_ok,
    tttLargeFiber4Block3Chunk2Row_1_ok,
    tttLargeFiber4Block3Chunk2Row_2_ok,
    tttLargeFiber4Block3Chunk2Row_3_ok,
    tttLargeFiber4Block3Chunk2Row_4_ok,
    tttLargeFiber4Block3Chunk2Row_5_ok,
    tttLargeFiber4Block3Chunk2Row_6_ok,
    tttLargeFiber4Block3Chunk2Row_7_ok,
    tttLargeFiber4Block3Chunk2Row_8_ok,
    tttLargeFiber4Block3Chunk2Row_9_ok,
    tttLargeFiber4Block3Chunk2Row_10_ok,
    tttLargeFiber4Block3Chunk2Row_11_ok,
    tttLargeFiber4Block3Chunk2Row_12_ok,
    tttLargeFiber4Block3Chunk2Row_13_ok,
    tttLargeFiber4Block3Chunk2Row_14_ok,
    tttLargeFiber4Block3Chunk2Row_15_ok]

def tttLargeFiber4Block3Chunk2ParentMapAudit : Bool :=
  tttLargeFiber4Block3Chunk2ParentMapCheck 0
    && tttLargeFiber4Block3Chunk2ParentMapCheck 1
    && tttLargeFiber4Block3Chunk2ParentMapCheck 2
    && tttLargeFiber4Block3Chunk2ParentMapCheck 3
    && tttLargeFiber4Block3Chunk2ParentMapCheck 4
    && tttLargeFiber4Block3Chunk2ParentMapCheck 5
    && tttLargeFiber4Block3Chunk2ParentMapCheck 6
    && tttLargeFiber4Block3Chunk2ParentMapCheck 7
    && tttLargeFiber4Block3Chunk2ParentMapCheck 8
    && tttLargeFiber4Block3Chunk2ParentMapCheck 9
    && tttLargeFiber4Block3Chunk2ParentMapCheck 10
    && tttLargeFiber4Block3Chunk2ParentMapCheck 11
    && tttLargeFiber4Block3Chunk2ParentMapCheck 12
    && tttLargeFiber4Block3Chunk2ParentMapCheck 13
    && tttLargeFiber4Block3Chunk2ParentMapCheck 14
    && tttLargeFiber4Block3Chunk2ParentMapCheck 15

theorem tttLargeFiber4Block3Chunk2ParentMapAudit_ok :
    tttLargeFiber4Block3Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber4Block3Chunk2ParentMapAudit,
    tttLargeFiber4Block3Chunk2ParentMap_0_ok,
    tttLargeFiber4Block3Chunk2ParentMap_1_ok,
    tttLargeFiber4Block3Chunk2ParentMap_2_ok,
    tttLargeFiber4Block3Chunk2ParentMap_3_ok,
    tttLargeFiber4Block3Chunk2ParentMap_4_ok,
    tttLargeFiber4Block3Chunk2ParentMap_5_ok,
    tttLargeFiber4Block3Chunk2ParentMap_6_ok,
    tttLargeFiber4Block3Chunk2ParentMap_7_ok,
    tttLargeFiber4Block3Chunk2ParentMap_8_ok,
    tttLargeFiber4Block3Chunk2ParentMap_9_ok,
    tttLargeFiber4Block3Chunk2ParentMap_10_ok,
    tttLargeFiber4Block3Chunk2ParentMap_11_ok,
    tttLargeFiber4Block3Chunk2ParentMap_12_ok,
    tttLargeFiber4Block3Chunk2ParentMap_13_ok,
    tttLargeFiber4Block3Chunk2ParentMap_14_ok,
    tttLargeFiber4Block3Chunk2ParentMap_15_ok]

def tttLargeFiber4Block3Chunk2ParentsAudit : Bool :=
  tttLargeFiber4Block3Chunk2ParentPathCheck 0
    && tttLargeFiber4Block3Chunk2ParentPathCheck 1
    && tttLargeFiber4Block3Chunk2ParentPathCheck 2
    && tttLargeFiber4Block3Chunk2ParentPathCheck 3
    && tttLargeFiber4Block3Chunk2ParentPathCheck 4
    && tttLargeFiber4Block3Chunk2ParentPathCheck 5
    && tttLargeFiber4Block3Chunk2ParentPathCheck 6
    && tttLargeFiber4Block3Chunk2ParentPathCheck 7
    && tttLargeFiber4Block3Chunk2ParentPathCheck 8
    && tttLargeFiber4Block3Chunk2ParentPathCheck 9
    && tttLargeFiber4Block3Chunk2ParentPathCheck 10
    && tttLargeFiber4Block3Chunk2ParentPathCheck 11
    && tttLargeFiber4Block3Chunk2ParentPathCheck 12
    && tttLargeFiber4Block3Chunk2ParentPathCheck 13
    && tttLargeFiber4Block3Chunk2ParentPathCheck 14
    && tttLargeFiber4Block3Chunk2ParentPathCheck 15

theorem tttLargeFiber4Block3Chunk2ParentsAudit_ok :
    tttLargeFiber4Block3Chunk2ParentsAudit = true := by
  simp [tttLargeFiber4Block3Chunk2ParentsAudit,
    tttLargeFiber4Block3Chunk2ParentPath_0_ok,
    tttLargeFiber4Block3Chunk2ParentPath_1_ok,
    tttLargeFiber4Block3Chunk2ParentPath_2_ok,
    tttLargeFiber4Block3Chunk2ParentPath_3_ok,
    tttLargeFiber4Block3Chunk2ParentPath_4_ok,
    tttLargeFiber4Block3Chunk2ParentPath_5_ok,
    tttLargeFiber4Block3Chunk2ParentPath_6_ok,
    tttLargeFiber4Block3Chunk2ParentPath_7_ok,
    tttLargeFiber4Block3Chunk2ParentPath_8_ok,
    tttLargeFiber4Block3Chunk2ParentPath_9_ok,
    tttLargeFiber4Block3Chunk2ParentPath_10_ok,
    tttLargeFiber4Block3Chunk2ParentPath_11_ok,
    tttLargeFiber4Block3Chunk2ParentPath_12_ok,
    tttLargeFiber4Block3Chunk2ParentPath_13_ok,
    tttLargeFiber4Block3Chunk2ParentPath_14_ok,
    tttLargeFiber4Block3Chunk2ParentPath_15_ok]

def tttLargeFiber4Block3Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block3Chunk2SourcesCheck &&
    tttLargeFiber4Block3Chunk2RowsAudit &&
    tttLargeFiber4Block3Chunk2ParentMapAudit &&
    tttLargeFiber4Block3Chunk2ParentsAudit

theorem tttLargeFiber4Block3Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber4Block3Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block3Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block3Chunk2SourcesCheck_ok,
    tttLargeFiber4Block3Chunk2RowsAudit_ok,
    tttLargeFiber4Block3Chunk2ParentMapAudit_ok,
    tttLargeFiber4Block3Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block3Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
