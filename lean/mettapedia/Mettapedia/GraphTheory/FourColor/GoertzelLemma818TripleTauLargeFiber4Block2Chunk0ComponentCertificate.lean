import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 2 chunk 0

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
Parent-depth convergence is checked by explicit bounded parent paths rather
than by reducing the recursive parent iterator over large indices.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block2Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block2Chunk0Sources : List Nat :=
  [2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311,
   2312, 2313, 2314, 2315, 2316, 2317, 2318, 2319]

def tttLargeFiber4Row128 : TripleComponentParentRow :=
  tripleRow 2304 2176 66 16 80 64 80 80
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row129 : TripleComponentParentRow :=
  tripleRow 2305 2177 66 16 81 64 80 81
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row130 : TripleComponentParentRow :=
  tripleRow 2306 2178 66 16 82 64 80 82
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row131 : TripleComponentParentRow :=
  tripleRow 2307 2179 66 16 83 64 80 83
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row132 : TripleComponentParentRow :=
  tripleRow 2308 2180 66 16 100 64 80 100
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row133 : TripleComponentParentRow :=
  tripleRow 2309 2181 66 16 101 64 80 101
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row134 : TripleComponentParentRow :=
  tripleRow 2310 2182 66 16 102 64 80 102
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row135 : TripleComponentParentRow :=
  tripleRow 2311 2183 66 16 103 64 80 103
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row136 : TripleComponentParentRow :=
  tripleRow 2312 2184 66 17 88 64 81 88
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row137 : TripleComponentParentRow :=
  tripleRow 2313 2185 66 17 89 64 81 89
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row138 : TripleComponentParentRow :=
  tripleRow 2314 2186 66 17 90 64 81 90
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row139 : TripleComponentParentRow :=
  tripleRow 2315 2187 66 17 91 64 81 91
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row140 : TripleComponentParentRow :=
  tripleRow 2316 2188 66 17 108 64 81 108
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row141 : TripleComponentParentRow :=
  tripleRow 2317 2189 66 17 109 64 81 109
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row142 : TripleComponentParentRow :=
  tripleRow 2318 2190 66 17 110 64 81 110
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row143 : TripleComponentParentRow :=
  tripleRow 2319 2191 66 17 111 64 81 111
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Block2Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row128
  , tttLargeFiber4Row129
  , tttLargeFiber4Row130
  , tttLargeFiber4Row131
  , tttLargeFiber4Row132
  , tttLargeFiber4Row133
  , tttLargeFiber4Row134
  , tttLargeFiber4Row135
  , tttLargeFiber4Row136
  , tttLargeFiber4Row137
  , tttLargeFiber4Row138
  , tttLargeFiber4Row139
  , tttLargeFiber4Row140
  , tttLargeFiber4Row141
  , tttLargeFiber4Row142
  , tttLargeFiber4Row143
  ]

def tttLargeFiber4Block2Chunk0SourcesCheck : Bool :=
  (tttLargeFiber4Block2Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber4Block2Chunk0Sources

theorem tttLargeFiber4Block2Chunk0SourcesCheck_ok :
    tttLargeFiber4Block2Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber4Block2Chunk0RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttLargeFiber4Key tttLargeFiber4Expected
    (listGetD tttLargeFiber4Block2Chunk0Rows i default)

def tttLargeFiber4Block2Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block2Chunk0Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block2Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block2Chunk0Sources 0 0 == 2304 &&
      tttLargeFiber4ParentOf 2304 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (1 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block2Chunk0Sources 1 0 == 2305 &&
      tttLargeFiber4ParentOf 2305 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (2 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block2Chunk0Sources 2 0 == 2306 &&
      tttLargeFiber4ParentOf 2306 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (2 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block2Chunk0Sources 3 0 == 2307 &&
      tttLargeFiber4ParentOf 2307 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block2Chunk0Sources 4 0 == 2308 &&
      tttLargeFiber4ParentOf 2308 == 2180 &&
      tttLargeFiber4ParentOf 2180 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block2Chunk0Sources 5 0 == 2309 &&
      tttLargeFiber4ParentOf 2309 == 2181 &&
      tttLargeFiber4ParentOf 2181 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block2Chunk0Sources 6 0 == 2310 &&
      tttLargeFiber4ParentOf 2310 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block2Chunk0Sources 7 0 == 2311 &&
      tttLargeFiber4ParentOf 2311 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (2 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block2Chunk0Sources 8 0 == 2312 &&
      tttLargeFiber4ParentOf 2312 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (2 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block2Chunk0Sources 9 0 == 2313 &&
      tttLargeFiber4ParentOf 2313 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block2Chunk0Sources 10 0 == 2314 &&
      tttLargeFiber4ParentOf 2314 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block2Chunk0Sources 11 0 == 2315 &&
      tttLargeFiber4ParentOf 2315 == 2187 &&
      tttLargeFiber4ParentOf 2187 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block2Chunk0Sources 12 0 == 2316 &&
      tttLargeFiber4ParentOf 2316 == 2188 &&
      tttLargeFiber4ParentOf 2188 == 2180 &&
      tttLargeFiber4ParentOf 2180 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block2Chunk0Sources 13 0 == 2317 &&
      tttLargeFiber4ParentOf 2317 == 2189 &&
      tttLargeFiber4ParentOf 2189 == 2181 &&
      tttLargeFiber4ParentOf 2181 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block2Chunk0Sources 14 0 == 2318 &&
      tttLargeFiber4ParentOf 2318 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block2Chunk0Sources 15 0 == 2319 &&
      tttLargeFiber4ParentOf 2319 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block2Chunk0Row_0_ok :
    tttLargeFiber4Block2Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0Row_1_ok :
    tttLargeFiber4Block2Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0Row_2_ok :
    tttLargeFiber4Block2Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0Row_3_ok :
    tttLargeFiber4Block2Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0Row_4_ok :
    tttLargeFiber4Block2Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0Row_5_ok :
    tttLargeFiber4Block2Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0Row_6_ok :
    tttLargeFiber4Block2Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0Row_7_ok :
    tttLargeFiber4Block2Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0Row_8_ok :
    tttLargeFiber4Block2Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0Row_9_ok :
    tttLargeFiber4Block2Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0Row_10_ok :
    tttLargeFiber4Block2Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0Row_11_ok :
    tttLargeFiber4Block2Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0Row_12_ok :
    tttLargeFiber4Block2Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0Row_13_ok :
    tttLargeFiber4Block2Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0Row_14_ok :
    tttLargeFiber4Block2Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0Row_15_ok :
    tttLargeFiber4Block2Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentMap_0_ok :
    tttLargeFiber4Block2Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentMap_1_ok :
    tttLargeFiber4Block2Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentMap_2_ok :
    tttLargeFiber4Block2Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentMap_3_ok :
    tttLargeFiber4Block2Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentMap_4_ok :
    tttLargeFiber4Block2Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentMap_5_ok :
    tttLargeFiber4Block2Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentMap_6_ok :
    tttLargeFiber4Block2Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentMap_7_ok :
    tttLargeFiber4Block2Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentMap_8_ok :
    tttLargeFiber4Block2Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentMap_9_ok :
    tttLargeFiber4Block2Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentMap_10_ok :
    tttLargeFiber4Block2Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentMap_11_ok :
    tttLargeFiber4Block2Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentMap_12_ok :
    tttLargeFiber4Block2Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentMap_13_ok :
    tttLargeFiber4Block2Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentMap_14_ok :
    tttLargeFiber4Block2Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentMap_15_ok :
    tttLargeFiber4Block2Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentPath_0_ok :
    tttLargeFiber4Block2Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentPath_1_ok :
    tttLargeFiber4Block2Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentPath_2_ok :
    tttLargeFiber4Block2Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentPath_3_ok :
    tttLargeFiber4Block2Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentPath_4_ok :
    tttLargeFiber4Block2Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentPath_5_ok :
    tttLargeFiber4Block2Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentPath_6_ok :
    tttLargeFiber4Block2Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentPath_7_ok :
    tttLargeFiber4Block2Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentPath_8_ok :
    tttLargeFiber4Block2Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentPath_9_ok :
    tttLargeFiber4Block2Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentPath_10_ok :
    tttLargeFiber4Block2Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentPath_11_ok :
    tttLargeFiber4Block2Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentPath_12_ok :
    tttLargeFiber4Block2Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentPath_13_ok :
    tttLargeFiber4Block2Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentPath_14_ok :
    tttLargeFiber4Block2Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block2Chunk0ParentPath_15_ok :
    tttLargeFiber4Block2Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block2Chunk0RowsAudit : Bool :=
  tttLargeFiber4Block2Chunk0RowCheck 0
    && tttLargeFiber4Block2Chunk0RowCheck 1
    && tttLargeFiber4Block2Chunk0RowCheck 2
    && tttLargeFiber4Block2Chunk0RowCheck 3
    && tttLargeFiber4Block2Chunk0RowCheck 4
    && tttLargeFiber4Block2Chunk0RowCheck 5
    && tttLargeFiber4Block2Chunk0RowCheck 6
    && tttLargeFiber4Block2Chunk0RowCheck 7
    && tttLargeFiber4Block2Chunk0RowCheck 8
    && tttLargeFiber4Block2Chunk0RowCheck 9
    && tttLargeFiber4Block2Chunk0RowCheck 10
    && tttLargeFiber4Block2Chunk0RowCheck 11
    && tttLargeFiber4Block2Chunk0RowCheck 12
    && tttLargeFiber4Block2Chunk0RowCheck 13
    && tttLargeFiber4Block2Chunk0RowCheck 14
    && tttLargeFiber4Block2Chunk0RowCheck 15

theorem tttLargeFiber4Block2Chunk0RowsAudit_ok :
    tttLargeFiber4Block2Chunk0RowsAudit = true := by
  simp [tttLargeFiber4Block2Chunk0RowsAudit,
    tttLargeFiber4Block2Chunk0Row_0_ok,
    tttLargeFiber4Block2Chunk0Row_1_ok,
    tttLargeFiber4Block2Chunk0Row_2_ok,
    tttLargeFiber4Block2Chunk0Row_3_ok,
    tttLargeFiber4Block2Chunk0Row_4_ok,
    tttLargeFiber4Block2Chunk0Row_5_ok,
    tttLargeFiber4Block2Chunk0Row_6_ok,
    tttLargeFiber4Block2Chunk0Row_7_ok,
    tttLargeFiber4Block2Chunk0Row_8_ok,
    tttLargeFiber4Block2Chunk0Row_9_ok,
    tttLargeFiber4Block2Chunk0Row_10_ok,
    tttLargeFiber4Block2Chunk0Row_11_ok,
    tttLargeFiber4Block2Chunk0Row_12_ok,
    tttLargeFiber4Block2Chunk0Row_13_ok,
    tttLargeFiber4Block2Chunk0Row_14_ok,
    tttLargeFiber4Block2Chunk0Row_15_ok]

def tttLargeFiber4Block2Chunk0ParentMapAudit : Bool :=
  tttLargeFiber4Block2Chunk0ParentMapCheck 0
    && tttLargeFiber4Block2Chunk0ParentMapCheck 1
    && tttLargeFiber4Block2Chunk0ParentMapCheck 2
    && tttLargeFiber4Block2Chunk0ParentMapCheck 3
    && tttLargeFiber4Block2Chunk0ParentMapCheck 4
    && tttLargeFiber4Block2Chunk0ParentMapCheck 5
    && tttLargeFiber4Block2Chunk0ParentMapCheck 6
    && tttLargeFiber4Block2Chunk0ParentMapCheck 7
    && tttLargeFiber4Block2Chunk0ParentMapCheck 8
    && tttLargeFiber4Block2Chunk0ParentMapCheck 9
    && tttLargeFiber4Block2Chunk0ParentMapCheck 10
    && tttLargeFiber4Block2Chunk0ParentMapCheck 11
    && tttLargeFiber4Block2Chunk0ParentMapCheck 12
    && tttLargeFiber4Block2Chunk0ParentMapCheck 13
    && tttLargeFiber4Block2Chunk0ParentMapCheck 14
    && tttLargeFiber4Block2Chunk0ParentMapCheck 15

theorem tttLargeFiber4Block2Chunk0ParentMapAudit_ok :
    tttLargeFiber4Block2Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber4Block2Chunk0ParentMapAudit,
    tttLargeFiber4Block2Chunk0ParentMap_0_ok,
    tttLargeFiber4Block2Chunk0ParentMap_1_ok,
    tttLargeFiber4Block2Chunk0ParentMap_2_ok,
    tttLargeFiber4Block2Chunk0ParentMap_3_ok,
    tttLargeFiber4Block2Chunk0ParentMap_4_ok,
    tttLargeFiber4Block2Chunk0ParentMap_5_ok,
    tttLargeFiber4Block2Chunk0ParentMap_6_ok,
    tttLargeFiber4Block2Chunk0ParentMap_7_ok,
    tttLargeFiber4Block2Chunk0ParentMap_8_ok,
    tttLargeFiber4Block2Chunk0ParentMap_9_ok,
    tttLargeFiber4Block2Chunk0ParentMap_10_ok,
    tttLargeFiber4Block2Chunk0ParentMap_11_ok,
    tttLargeFiber4Block2Chunk0ParentMap_12_ok,
    tttLargeFiber4Block2Chunk0ParentMap_13_ok,
    tttLargeFiber4Block2Chunk0ParentMap_14_ok,
    tttLargeFiber4Block2Chunk0ParentMap_15_ok]

def tttLargeFiber4Block2Chunk0ParentsAudit : Bool :=
  tttLargeFiber4Block2Chunk0ParentPathCheck 0
    && tttLargeFiber4Block2Chunk0ParentPathCheck 1
    && tttLargeFiber4Block2Chunk0ParentPathCheck 2
    && tttLargeFiber4Block2Chunk0ParentPathCheck 3
    && tttLargeFiber4Block2Chunk0ParentPathCheck 4
    && tttLargeFiber4Block2Chunk0ParentPathCheck 5
    && tttLargeFiber4Block2Chunk0ParentPathCheck 6
    && tttLargeFiber4Block2Chunk0ParentPathCheck 7
    && tttLargeFiber4Block2Chunk0ParentPathCheck 8
    && tttLargeFiber4Block2Chunk0ParentPathCheck 9
    && tttLargeFiber4Block2Chunk0ParentPathCheck 10
    && tttLargeFiber4Block2Chunk0ParentPathCheck 11
    && tttLargeFiber4Block2Chunk0ParentPathCheck 12
    && tttLargeFiber4Block2Chunk0ParentPathCheck 13
    && tttLargeFiber4Block2Chunk0ParentPathCheck 14
    && tttLargeFiber4Block2Chunk0ParentPathCheck 15

theorem tttLargeFiber4Block2Chunk0ParentsAudit_ok :
    tttLargeFiber4Block2Chunk0ParentsAudit = true := by
  simp [tttLargeFiber4Block2Chunk0ParentsAudit,
    tttLargeFiber4Block2Chunk0ParentPath_0_ok,
    tttLargeFiber4Block2Chunk0ParentPath_1_ok,
    tttLargeFiber4Block2Chunk0ParentPath_2_ok,
    tttLargeFiber4Block2Chunk0ParentPath_3_ok,
    tttLargeFiber4Block2Chunk0ParentPath_4_ok,
    tttLargeFiber4Block2Chunk0ParentPath_5_ok,
    tttLargeFiber4Block2Chunk0ParentPath_6_ok,
    tttLargeFiber4Block2Chunk0ParentPath_7_ok,
    tttLargeFiber4Block2Chunk0ParentPath_8_ok,
    tttLargeFiber4Block2Chunk0ParentPath_9_ok,
    tttLargeFiber4Block2Chunk0ParentPath_10_ok,
    tttLargeFiber4Block2Chunk0ParentPath_11_ok,
    tttLargeFiber4Block2Chunk0ParentPath_12_ok,
    tttLargeFiber4Block2Chunk0ParentPath_13_ok,
    tttLargeFiber4Block2Chunk0ParentPath_14_ok,
    tttLargeFiber4Block2Chunk0ParentPath_15_ok]

def tttLargeFiber4Block2Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block2Chunk0SourcesCheck &&
    tttLargeFiber4Block2Chunk0RowsAudit &&
    tttLargeFiber4Block2Chunk0ParentMapAudit &&
    tttLargeFiber4Block2Chunk0ParentsAudit

theorem tttLargeFiber4Block2Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber4Block2Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block2Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block2Chunk0SourcesCheck_ok,
    tttLargeFiber4Block2Chunk0RowsAudit_ok,
    tttLargeFiber4Block2Chunk0ParentMapAudit_ok,
    tttLargeFiber4Block2Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block2Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
