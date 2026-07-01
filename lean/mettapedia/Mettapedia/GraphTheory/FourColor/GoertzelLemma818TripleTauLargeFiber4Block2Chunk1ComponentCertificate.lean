import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 2 chunk 1

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
Parent-depth convergence is checked by explicit bounded parent paths rather
than by reducing the recursive parent iterator over large indices.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block2Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block2Chunk1Sources : List Nat :=
  [2320, 2321, 2322, 2323, 2324, 2325, 2326, 2327,
   2328, 2329, 2330, 2331, 2332, 2333, 2334, 2335]

def tttLargeFiber4Row144 : TripleComponentParentRow :=
  tripleRow 2320 2192 66 18 16 64 82 16
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row145 : TripleComponentParentRow :=
  tripleRow 2321 2193 66 18 17 64 82 17
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row146 : TripleComponentParentRow :=
  tripleRow 2322 2194 66 18 18 64 82 18
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row147 : TripleComponentParentRow :=
  tripleRow 2323 2195 66 18 19 64 82 19
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row148 : TripleComponentParentRow :=
  tripleRow 2324 2196 66 18 32 64 82 32
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row149 : TripleComponentParentRow :=
  tripleRow 2325 2197 66 18 33 64 82 33
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row150 : TripleComponentParentRow :=
  tripleRow 2326 2198 66 18 34 64 82 34
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row151 : TripleComponentParentRow :=
  tripleRow 2327 2199 66 18 35 64 82 35
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row152 : TripleComponentParentRow :=
  tripleRow 2328 2200 66 19 24 64 83 24
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row153 : TripleComponentParentRow :=
  tripleRow 2329 2201 66 19 25 64 83 25
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row154 : TripleComponentParentRow :=
  tripleRow 2330 2202 66 19 26 64 83 26
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row155 : TripleComponentParentRow :=
  tripleRow 2331 2203 66 19 27 64 83 27
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row156 : TripleComponentParentRow :=
  tripleRow 2332 2204 66 19 40 64 83 40
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row157 : TripleComponentParentRow :=
  tripleRow 2333 2205 66 19 41 64 83 41
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row158 : TripleComponentParentRow :=
  tripleRow 2334 2206 66 19 42 64 83 42
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row159 : TripleComponentParentRow :=
  tripleRow 2335 2207 66 19 43 64 83 43
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Block2Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row144
  , tttLargeFiber4Row145
  , tttLargeFiber4Row146
  , tttLargeFiber4Row147
  , tttLargeFiber4Row148
  , tttLargeFiber4Row149
  , tttLargeFiber4Row150
  , tttLargeFiber4Row151
  , tttLargeFiber4Row152
  , tttLargeFiber4Row153
  , tttLargeFiber4Row154
  , tttLargeFiber4Row155
  , tttLargeFiber4Row156
  , tttLargeFiber4Row157
  , tttLargeFiber4Row158
  , tttLargeFiber4Row159
  ]

def tttLargeFiber4Block2Chunk1SourcesCheck : Bool :=
  (tttLargeFiber4Block2Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber4Block2Chunk1Sources

theorem tttLargeFiber4Block2Chunk1SourcesCheck_ok :
    tttLargeFiber4Block2Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber4Block2Chunk1RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttLargeFiber4Key tttLargeFiber4Expected
    (listGetD tttLargeFiber4Block2Chunk1Rows i default)

def tttLargeFiber4Block2Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block2Chunk1Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block2Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block2Chunk1Sources 0 0 == 2320 &&
      tttLargeFiber4ParentOf 2320 == 2192 &&
      tttLargeFiber4ParentOf 2192 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (2 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block2Chunk1Sources 1 0 == 2321 &&
      tttLargeFiber4ParentOf 2321 == 2193 &&
      tttLargeFiber4ParentOf 2193 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block2Chunk1Sources 2 0 == 2322 &&
      tttLargeFiber4ParentOf 2322 == 2194 &&
      tttLargeFiber4ParentOf 2194 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block2Chunk1Sources 3 0 == 2323 &&
      tttLargeFiber4ParentOf 2323 == 2195 &&
      tttLargeFiber4ParentOf 2195 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block2Chunk1Sources 4 0 == 2324 &&
      tttLargeFiber4ParentOf 2324 == 2196 &&
      tttLargeFiber4ParentOf 2196 == 2192 &&
      tttLargeFiber4ParentOf 2192 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block2Chunk1Sources 5 0 == 2325 &&
      tttLargeFiber4ParentOf 2325 == 2197 &&
      tttLargeFiber4ParentOf 2197 == 2193 &&
      tttLargeFiber4ParentOf 2193 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block2Chunk1Sources 6 0 == 2326 &&
      tttLargeFiber4ParentOf 2326 == 2198 &&
      tttLargeFiber4ParentOf 2198 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block2Chunk1Sources 7 0 == 2327 &&
      tttLargeFiber4ParentOf 2327 == 2199 &&
      tttLargeFiber4ParentOf 2199 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block2Chunk1Sources 8 0 == 2328 &&
      tttLargeFiber4ParentOf 2328 == 2200 &&
      tttLargeFiber4ParentOf 2200 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block2Chunk1Sources 9 0 == 2329 &&
      tttLargeFiber4ParentOf 2329 == 2201 &&
      tttLargeFiber4ParentOf 2201 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block2Chunk1Sources 10 0 == 2330 &&
      tttLargeFiber4ParentOf 2330 == 2202 &&
      tttLargeFiber4ParentOf 2202 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block2Chunk1Sources 11 0 == 2331 &&
      tttLargeFiber4ParentOf 2331 == 2203 &&
      tttLargeFiber4ParentOf 2203 == 2187 &&
      tttLargeFiber4ParentOf 2187 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block2Chunk1Sources 12 0 == 2332 &&
      tttLargeFiber4ParentOf 2332 == 2204 &&
      tttLargeFiber4ParentOf 2204 == 2200 &&
      tttLargeFiber4ParentOf 2200 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block2Chunk1Sources 13 0 == 2333 &&
      tttLargeFiber4ParentOf 2333 == 2205 &&
      tttLargeFiber4ParentOf 2205 == 2201 &&
      tttLargeFiber4ParentOf 2201 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block2Chunk1Sources 14 0 == 2334 &&
      tttLargeFiber4ParentOf 2334 == 2206 &&
      tttLargeFiber4ParentOf 2206 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block2Chunk1Sources 15 0 == 2335 &&
      tttLargeFiber4ParentOf 2335 == 2207 &&
      tttLargeFiber4ParentOf 2207 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block2Chunk1Row_0_ok :
    tttLargeFiber4Block2Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1Row_1_ok :
    tttLargeFiber4Block2Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1Row_2_ok :
    tttLargeFiber4Block2Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1Row_3_ok :
    tttLargeFiber4Block2Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1Row_4_ok :
    tttLargeFiber4Block2Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1Row_5_ok :
    tttLargeFiber4Block2Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1Row_6_ok :
    tttLargeFiber4Block2Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1Row_7_ok :
    tttLargeFiber4Block2Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1Row_8_ok :
    tttLargeFiber4Block2Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1Row_9_ok :
    tttLargeFiber4Block2Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1Row_10_ok :
    tttLargeFiber4Block2Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1Row_11_ok :
    tttLargeFiber4Block2Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1Row_12_ok :
    tttLargeFiber4Block2Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1Row_13_ok :
    tttLargeFiber4Block2Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1Row_14_ok :
    tttLargeFiber4Block2Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1Row_15_ok :
    tttLargeFiber4Block2Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentMap_0_ok :
    tttLargeFiber4Block2Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentMap_1_ok :
    tttLargeFiber4Block2Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentMap_2_ok :
    tttLargeFiber4Block2Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentMap_3_ok :
    tttLargeFiber4Block2Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentMap_4_ok :
    tttLargeFiber4Block2Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentMap_5_ok :
    tttLargeFiber4Block2Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentMap_6_ok :
    tttLargeFiber4Block2Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentMap_7_ok :
    tttLargeFiber4Block2Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentMap_8_ok :
    tttLargeFiber4Block2Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentMap_9_ok :
    tttLargeFiber4Block2Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentMap_10_ok :
    tttLargeFiber4Block2Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentMap_11_ok :
    tttLargeFiber4Block2Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentMap_12_ok :
    tttLargeFiber4Block2Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentMap_13_ok :
    tttLargeFiber4Block2Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentMap_14_ok :
    tttLargeFiber4Block2Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentMap_15_ok :
    tttLargeFiber4Block2Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentPath_0_ok :
    tttLargeFiber4Block2Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentPath_1_ok :
    tttLargeFiber4Block2Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentPath_2_ok :
    tttLargeFiber4Block2Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentPath_3_ok :
    tttLargeFiber4Block2Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentPath_4_ok :
    tttLargeFiber4Block2Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentPath_5_ok :
    tttLargeFiber4Block2Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentPath_6_ok :
    tttLargeFiber4Block2Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentPath_7_ok :
    tttLargeFiber4Block2Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentPath_8_ok :
    tttLargeFiber4Block2Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentPath_9_ok :
    tttLargeFiber4Block2Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentPath_10_ok :
    tttLargeFiber4Block2Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentPath_11_ok :
    tttLargeFiber4Block2Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentPath_12_ok :
    tttLargeFiber4Block2Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentPath_13_ok :
    tttLargeFiber4Block2Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentPath_14_ok :
    tttLargeFiber4Block2Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block2Chunk1ParentPath_15_ok :
    tttLargeFiber4Block2Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block2Chunk1RowsAudit : Bool :=
  tttLargeFiber4Block2Chunk1RowCheck 0
    && tttLargeFiber4Block2Chunk1RowCheck 1
    && tttLargeFiber4Block2Chunk1RowCheck 2
    && tttLargeFiber4Block2Chunk1RowCheck 3
    && tttLargeFiber4Block2Chunk1RowCheck 4
    && tttLargeFiber4Block2Chunk1RowCheck 5
    && tttLargeFiber4Block2Chunk1RowCheck 6
    && tttLargeFiber4Block2Chunk1RowCheck 7
    && tttLargeFiber4Block2Chunk1RowCheck 8
    && tttLargeFiber4Block2Chunk1RowCheck 9
    && tttLargeFiber4Block2Chunk1RowCheck 10
    && tttLargeFiber4Block2Chunk1RowCheck 11
    && tttLargeFiber4Block2Chunk1RowCheck 12
    && tttLargeFiber4Block2Chunk1RowCheck 13
    && tttLargeFiber4Block2Chunk1RowCheck 14
    && tttLargeFiber4Block2Chunk1RowCheck 15

theorem tttLargeFiber4Block2Chunk1RowsAudit_ok :
    tttLargeFiber4Block2Chunk1RowsAudit = true := by
  simp [tttLargeFiber4Block2Chunk1RowsAudit,
    tttLargeFiber4Block2Chunk1Row_0_ok,
    tttLargeFiber4Block2Chunk1Row_1_ok,
    tttLargeFiber4Block2Chunk1Row_2_ok,
    tttLargeFiber4Block2Chunk1Row_3_ok,
    tttLargeFiber4Block2Chunk1Row_4_ok,
    tttLargeFiber4Block2Chunk1Row_5_ok,
    tttLargeFiber4Block2Chunk1Row_6_ok,
    tttLargeFiber4Block2Chunk1Row_7_ok,
    tttLargeFiber4Block2Chunk1Row_8_ok,
    tttLargeFiber4Block2Chunk1Row_9_ok,
    tttLargeFiber4Block2Chunk1Row_10_ok,
    tttLargeFiber4Block2Chunk1Row_11_ok,
    tttLargeFiber4Block2Chunk1Row_12_ok,
    tttLargeFiber4Block2Chunk1Row_13_ok,
    tttLargeFiber4Block2Chunk1Row_14_ok,
    tttLargeFiber4Block2Chunk1Row_15_ok]

def tttLargeFiber4Block2Chunk1ParentMapAudit : Bool :=
  tttLargeFiber4Block2Chunk1ParentMapCheck 0
    && tttLargeFiber4Block2Chunk1ParentMapCheck 1
    && tttLargeFiber4Block2Chunk1ParentMapCheck 2
    && tttLargeFiber4Block2Chunk1ParentMapCheck 3
    && tttLargeFiber4Block2Chunk1ParentMapCheck 4
    && tttLargeFiber4Block2Chunk1ParentMapCheck 5
    && tttLargeFiber4Block2Chunk1ParentMapCheck 6
    && tttLargeFiber4Block2Chunk1ParentMapCheck 7
    && tttLargeFiber4Block2Chunk1ParentMapCheck 8
    && tttLargeFiber4Block2Chunk1ParentMapCheck 9
    && tttLargeFiber4Block2Chunk1ParentMapCheck 10
    && tttLargeFiber4Block2Chunk1ParentMapCheck 11
    && tttLargeFiber4Block2Chunk1ParentMapCheck 12
    && tttLargeFiber4Block2Chunk1ParentMapCheck 13
    && tttLargeFiber4Block2Chunk1ParentMapCheck 14
    && tttLargeFiber4Block2Chunk1ParentMapCheck 15

theorem tttLargeFiber4Block2Chunk1ParentMapAudit_ok :
    tttLargeFiber4Block2Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber4Block2Chunk1ParentMapAudit,
    tttLargeFiber4Block2Chunk1ParentMap_0_ok,
    tttLargeFiber4Block2Chunk1ParentMap_1_ok,
    tttLargeFiber4Block2Chunk1ParentMap_2_ok,
    tttLargeFiber4Block2Chunk1ParentMap_3_ok,
    tttLargeFiber4Block2Chunk1ParentMap_4_ok,
    tttLargeFiber4Block2Chunk1ParentMap_5_ok,
    tttLargeFiber4Block2Chunk1ParentMap_6_ok,
    tttLargeFiber4Block2Chunk1ParentMap_7_ok,
    tttLargeFiber4Block2Chunk1ParentMap_8_ok,
    tttLargeFiber4Block2Chunk1ParentMap_9_ok,
    tttLargeFiber4Block2Chunk1ParentMap_10_ok,
    tttLargeFiber4Block2Chunk1ParentMap_11_ok,
    tttLargeFiber4Block2Chunk1ParentMap_12_ok,
    tttLargeFiber4Block2Chunk1ParentMap_13_ok,
    tttLargeFiber4Block2Chunk1ParentMap_14_ok,
    tttLargeFiber4Block2Chunk1ParentMap_15_ok]

def tttLargeFiber4Block2Chunk1ParentsAudit : Bool :=
  tttLargeFiber4Block2Chunk1ParentPathCheck 0
    && tttLargeFiber4Block2Chunk1ParentPathCheck 1
    && tttLargeFiber4Block2Chunk1ParentPathCheck 2
    && tttLargeFiber4Block2Chunk1ParentPathCheck 3
    && tttLargeFiber4Block2Chunk1ParentPathCheck 4
    && tttLargeFiber4Block2Chunk1ParentPathCheck 5
    && tttLargeFiber4Block2Chunk1ParentPathCheck 6
    && tttLargeFiber4Block2Chunk1ParentPathCheck 7
    && tttLargeFiber4Block2Chunk1ParentPathCheck 8
    && tttLargeFiber4Block2Chunk1ParentPathCheck 9
    && tttLargeFiber4Block2Chunk1ParentPathCheck 10
    && tttLargeFiber4Block2Chunk1ParentPathCheck 11
    && tttLargeFiber4Block2Chunk1ParentPathCheck 12
    && tttLargeFiber4Block2Chunk1ParentPathCheck 13
    && tttLargeFiber4Block2Chunk1ParentPathCheck 14
    && tttLargeFiber4Block2Chunk1ParentPathCheck 15

theorem tttLargeFiber4Block2Chunk1ParentsAudit_ok :
    tttLargeFiber4Block2Chunk1ParentsAudit = true := by
  simp [tttLargeFiber4Block2Chunk1ParentsAudit,
    tttLargeFiber4Block2Chunk1ParentPath_0_ok,
    tttLargeFiber4Block2Chunk1ParentPath_1_ok,
    tttLargeFiber4Block2Chunk1ParentPath_2_ok,
    tttLargeFiber4Block2Chunk1ParentPath_3_ok,
    tttLargeFiber4Block2Chunk1ParentPath_4_ok,
    tttLargeFiber4Block2Chunk1ParentPath_5_ok,
    tttLargeFiber4Block2Chunk1ParentPath_6_ok,
    tttLargeFiber4Block2Chunk1ParentPath_7_ok,
    tttLargeFiber4Block2Chunk1ParentPath_8_ok,
    tttLargeFiber4Block2Chunk1ParentPath_9_ok,
    tttLargeFiber4Block2Chunk1ParentPath_10_ok,
    tttLargeFiber4Block2Chunk1ParentPath_11_ok,
    tttLargeFiber4Block2Chunk1ParentPath_12_ok,
    tttLargeFiber4Block2Chunk1ParentPath_13_ok,
    tttLargeFiber4Block2Chunk1ParentPath_14_ok,
    tttLargeFiber4Block2Chunk1ParentPath_15_ok]

def tttLargeFiber4Block2Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block2Chunk1SourcesCheck &&
    tttLargeFiber4Block2Chunk1RowsAudit &&
    tttLargeFiber4Block2Chunk1ParentMapAudit &&
    tttLargeFiber4Block2Chunk1ParentsAudit

theorem tttLargeFiber4Block2Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber4Block2Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block2Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block2Chunk1SourcesCheck_ok,
    tttLargeFiber4Block2Chunk1RowsAudit_ok,
    tttLargeFiber4Block2Chunk1ParentMapAudit_ok,
    tttLargeFiber4Block2Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block2Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
