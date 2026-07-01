import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 2 chunk 2

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
Parent-depth convergence is checked by explicit bounded parent paths rather
than by reducing the recursive parent iterator over large indices.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block2Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block2Chunk2Sources : List Nat :=
  [2336, 2337, 2338, 2339, 2340, 2341, 2342, 2343,
   2344, 2345, 2346, 2347, 2348, 2349, 2350, 2351]

def tttLargeFiber4Row160 : TripleComponentParentRow :=
  tripleRow 2336 2304 66 32 148 66 16 80
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

def tttLargeFiber4Row161 : TripleComponentParentRow :=
  tripleRow 2337 2305 66 32 149 66 16 81
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

def tttLargeFiber4Row162 : TripleComponentParentRow :=
  tripleRow 2338 2306 66 32 150 66 16 82
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

def tttLargeFiber4Row163 : TripleComponentParentRow :=
  tripleRow 2339 2336 66 32 151 66 32 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row164 : TripleComponentParentRow :=
  tripleRow 2340 2336 66 32 164 66 32 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber4Row165 : TripleComponentParentRow :=
  tripleRow 2341 2337 66 32 165 66 32 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber4Row166 : TripleComponentParentRow :=
  tripleRow 2342 2310 66 32 166 66 16 102
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber4Row167 : TripleComponentParentRow :=
  tripleRow 2343 2311 66 32 167 66 16 103
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber4Row168 : TripleComponentParentRow :=
  tripleRow 2344 2312 66 33 156 66 17 88
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

def tttLargeFiber4Row169 : TripleComponentParentRow :=
  tripleRow 2345 2313 66 33 157 66 17 89
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

def tttLargeFiber4Row170 : TripleComponentParentRow :=
  tripleRow 2346 2314 66 33 158 66 17 90
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

def tttLargeFiber4Row171 : TripleComponentParentRow :=
  tripleRow 2347 2344 66 33 159 66 33 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row172 : TripleComponentParentRow :=
  tripleRow 2348 2344 66 33 172 66 33 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber4Row173 : TripleComponentParentRow :=
  tripleRow 2349 2345 66 33 173 66 33 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber4Row174 : TripleComponentParentRow :=
  tripleRow 2350 2318 66 33 174 66 17 110
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber4Row175 : TripleComponentParentRow :=
  tripleRow 2351 2319 66 33 175 66 17 111
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber4Block2Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row160
  , tttLargeFiber4Row161
  , tttLargeFiber4Row162
  , tttLargeFiber4Row163
  , tttLargeFiber4Row164
  , tttLargeFiber4Row165
  , tttLargeFiber4Row166
  , tttLargeFiber4Row167
  , tttLargeFiber4Row168
  , tttLargeFiber4Row169
  , tttLargeFiber4Row170
  , tttLargeFiber4Row171
  , tttLargeFiber4Row172
  , tttLargeFiber4Row173
  , tttLargeFiber4Row174
  , tttLargeFiber4Row175
  ]

def tttLargeFiber4Block2Chunk2SourcesCheck : Bool :=
  (tttLargeFiber4Block2Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber4Block2Chunk2Sources

theorem tttLargeFiber4Block2Chunk2SourcesCheck_ok :
    tttLargeFiber4Block2Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber4Block2Chunk2RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttLargeFiber4Key tttLargeFiber4Expected
    (listGetD tttLargeFiber4Block2Chunk2Rows i default)

def tttLargeFiber4Block2Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block2Chunk2Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block2Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block2Chunk2Sources 0 0 == 2336 &&
      tttLargeFiber4ParentOf 2336 == 2304 &&
      tttLargeFiber4ParentOf 2304 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (2 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block2Chunk2Sources 1 0 == 2337 &&
      tttLargeFiber4ParentOf 2337 == 2305 &&
      tttLargeFiber4ParentOf 2305 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block2Chunk2Sources 2 0 == 2338 &&
      tttLargeFiber4ParentOf 2338 == 2306 &&
      tttLargeFiber4ParentOf 2306 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block2Chunk2Sources 3 0 == 2339 &&
      tttLargeFiber4ParentOf 2339 == 2336 &&
      tttLargeFiber4ParentOf 2336 == 2304 &&
      tttLargeFiber4ParentOf 2304 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block2Chunk2Sources 4 0 == 2340 &&
      tttLargeFiber4ParentOf 2340 == 2336 &&
      tttLargeFiber4ParentOf 2336 == 2304 &&
      tttLargeFiber4ParentOf 2304 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block2Chunk2Sources 5 0 == 2341 &&
      tttLargeFiber4ParentOf 2341 == 2337 &&
      tttLargeFiber4ParentOf 2337 == 2305 &&
      tttLargeFiber4ParentOf 2305 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block2Chunk2Sources 6 0 == 2342 &&
      tttLargeFiber4ParentOf 2342 == 2310 &&
      tttLargeFiber4ParentOf 2310 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block2Chunk2Sources 7 0 == 2343 &&
      tttLargeFiber4ParentOf 2343 == 2311 &&
      tttLargeFiber4ParentOf 2311 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block2Chunk2Sources 8 0 == 2344 &&
      tttLargeFiber4ParentOf 2344 == 2312 &&
      tttLargeFiber4ParentOf 2312 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block2Chunk2Sources 9 0 == 2345 &&
      tttLargeFiber4ParentOf 2345 == 2313 &&
      tttLargeFiber4ParentOf 2313 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block2Chunk2Sources 10 0 == 2346 &&
      tttLargeFiber4ParentOf 2346 == 2314 &&
      tttLargeFiber4ParentOf 2314 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block2Chunk2Sources 11 0 == 2347 &&
      tttLargeFiber4ParentOf 2347 == 2344 &&
      tttLargeFiber4ParentOf 2344 == 2312 &&
      tttLargeFiber4ParentOf 2312 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block2Chunk2Sources 12 0 == 2348 &&
      tttLargeFiber4ParentOf 2348 == 2344 &&
      tttLargeFiber4ParentOf 2344 == 2312 &&
      tttLargeFiber4ParentOf 2312 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block2Chunk2Sources 13 0 == 2349 &&
      tttLargeFiber4ParentOf 2349 == 2345 &&
      tttLargeFiber4ParentOf 2345 == 2313 &&
      tttLargeFiber4ParentOf 2313 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block2Chunk2Sources 14 0 == 2350 &&
      tttLargeFiber4ParentOf 2350 == 2318 &&
      tttLargeFiber4ParentOf 2318 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block2Chunk2Sources 15 0 == 2351 &&
      tttLargeFiber4ParentOf 2351 == 2319 &&
      tttLargeFiber4ParentOf 2319 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block2Chunk2Row_0_ok :
    tttLargeFiber4Block2Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2Row_1_ok :
    tttLargeFiber4Block2Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2Row_2_ok :
    tttLargeFiber4Block2Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2Row_3_ok :
    tttLargeFiber4Block2Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2Row_4_ok :
    tttLargeFiber4Block2Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2Row_5_ok :
    tttLargeFiber4Block2Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2Row_6_ok :
    tttLargeFiber4Block2Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2Row_7_ok :
    tttLargeFiber4Block2Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2Row_8_ok :
    tttLargeFiber4Block2Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2Row_9_ok :
    tttLargeFiber4Block2Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2Row_10_ok :
    tttLargeFiber4Block2Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2Row_11_ok :
    tttLargeFiber4Block2Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2Row_12_ok :
    tttLargeFiber4Block2Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2Row_13_ok :
    tttLargeFiber4Block2Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2Row_14_ok :
    tttLargeFiber4Block2Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2Row_15_ok :
    tttLargeFiber4Block2Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentMap_0_ok :
    tttLargeFiber4Block2Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentMap_1_ok :
    tttLargeFiber4Block2Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentMap_2_ok :
    tttLargeFiber4Block2Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentMap_3_ok :
    tttLargeFiber4Block2Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentMap_4_ok :
    tttLargeFiber4Block2Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentMap_5_ok :
    tttLargeFiber4Block2Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentMap_6_ok :
    tttLargeFiber4Block2Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentMap_7_ok :
    tttLargeFiber4Block2Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentMap_8_ok :
    tttLargeFiber4Block2Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentMap_9_ok :
    tttLargeFiber4Block2Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentMap_10_ok :
    tttLargeFiber4Block2Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentMap_11_ok :
    tttLargeFiber4Block2Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentMap_12_ok :
    tttLargeFiber4Block2Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentMap_13_ok :
    tttLargeFiber4Block2Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentMap_14_ok :
    tttLargeFiber4Block2Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentMap_15_ok :
    tttLargeFiber4Block2Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentPath_0_ok :
    tttLargeFiber4Block2Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentPath_1_ok :
    tttLargeFiber4Block2Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentPath_2_ok :
    tttLargeFiber4Block2Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentPath_3_ok :
    tttLargeFiber4Block2Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentPath_4_ok :
    tttLargeFiber4Block2Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentPath_5_ok :
    tttLargeFiber4Block2Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentPath_6_ok :
    tttLargeFiber4Block2Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentPath_7_ok :
    tttLargeFiber4Block2Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentPath_8_ok :
    tttLargeFiber4Block2Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentPath_9_ok :
    tttLargeFiber4Block2Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentPath_10_ok :
    tttLargeFiber4Block2Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentPath_11_ok :
    tttLargeFiber4Block2Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentPath_12_ok :
    tttLargeFiber4Block2Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentPath_13_ok :
    tttLargeFiber4Block2Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentPath_14_ok :
    tttLargeFiber4Block2Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block2Chunk2ParentPath_15_ok :
    tttLargeFiber4Block2Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block2Chunk2RowsAudit : Bool :=
  tttLargeFiber4Block2Chunk2RowCheck 0
    && tttLargeFiber4Block2Chunk2RowCheck 1
    && tttLargeFiber4Block2Chunk2RowCheck 2
    && tttLargeFiber4Block2Chunk2RowCheck 3
    && tttLargeFiber4Block2Chunk2RowCheck 4
    && tttLargeFiber4Block2Chunk2RowCheck 5
    && tttLargeFiber4Block2Chunk2RowCheck 6
    && tttLargeFiber4Block2Chunk2RowCheck 7
    && tttLargeFiber4Block2Chunk2RowCheck 8
    && tttLargeFiber4Block2Chunk2RowCheck 9
    && tttLargeFiber4Block2Chunk2RowCheck 10
    && tttLargeFiber4Block2Chunk2RowCheck 11
    && tttLargeFiber4Block2Chunk2RowCheck 12
    && tttLargeFiber4Block2Chunk2RowCheck 13
    && tttLargeFiber4Block2Chunk2RowCheck 14
    && tttLargeFiber4Block2Chunk2RowCheck 15

theorem tttLargeFiber4Block2Chunk2RowsAudit_ok :
    tttLargeFiber4Block2Chunk2RowsAudit = true := by
  simp [tttLargeFiber4Block2Chunk2RowsAudit,
    tttLargeFiber4Block2Chunk2Row_0_ok,
    tttLargeFiber4Block2Chunk2Row_1_ok,
    tttLargeFiber4Block2Chunk2Row_2_ok,
    tttLargeFiber4Block2Chunk2Row_3_ok,
    tttLargeFiber4Block2Chunk2Row_4_ok,
    tttLargeFiber4Block2Chunk2Row_5_ok,
    tttLargeFiber4Block2Chunk2Row_6_ok,
    tttLargeFiber4Block2Chunk2Row_7_ok,
    tttLargeFiber4Block2Chunk2Row_8_ok,
    tttLargeFiber4Block2Chunk2Row_9_ok,
    tttLargeFiber4Block2Chunk2Row_10_ok,
    tttLargeFiber4Block2Chunk2Row_11_ok,
    tttLargeFiber4Block2Chunk2Row_12_ok,
    tttLargeFiber4Block2Chunk2Row_13_ok,
    tttLargeFiber4Block2Chunk2Row_14_ok,
    tttLargeFiber4Block2Chunk2Row_15_ok]

def tttLargeFiber4Block2Chunk2ParentMapAudit : Bool :=
  tttLargeFiber4Block2Chunk2ParentMapCheck 0
    && tttLargeFiber4Block2Chunk2ParentMapCheck 1
    && tttLargeFiber4Block2Chunk2ParentMapCheck 2
    && tttLargeFiber4Block2Chunk2ParentMapCheck 3
    && tttLargeFiber4Block2Chunk2ParentMapCheck 4
    && tttLargeFiber4Block2Chunk2ParentMapCheck 5
    && tttLargeFiber4Block2Chunk2ParentMapCheck 6
    && tttLargeFiber4Block2Chunk2ParentMapCheck 7
    && tttLargeFiber4Block2Chunk2ParentMapCheck 8
    && tttLargeFiber4Block2Chunk2ParentMapCheck 9
    && tttLargeFiber4Block2Chunk2ParentMapCheck 10
    && tttLargeFiber4Block2Chunk2ParentMapCheck 11
    && tttLargeFiber4Block2Chunk2ParentMapCheck 12
    && tttLargeFiber4Block2Chunk2ParentMapCheck 13
    && tttLargeFiber4Block2Chunk2ParentMapCheck 14
    && tttLargeFiber4Block2Chunk2ParentMapCheck 15

theorem tttLargeFiber4Block2Chunk2ParentMapAudit_ok :
    tttLargeFiber4Block2Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber4Block2Chunk2ParentMapAudit,
    tttLargeFiber4Block2Chunk2ParentMap_0_ok,
    tttLargeFiber4Block2Chunk2ParentMap_1_ok,
    tttLargeFiber4Block2Chunk2ParentMap_2_ok,
    tttLargeFiber4Block2Chunk2ParentMap_3_ok,
    tttLargeFiber4Block2Chunk2ParentMap_4_ok,
    tttLargeFiber4Block2Chunk2ParentMap_5_ok,
    tttLargeFiber4Block2Chunk2ParentMap_6_ok,
    tttLargeFiber4Block2Chunk2ParentMap_7_ok,
    tttLargeFiber4Block2Chunk2ParentMap_8_ok,
    tttLargeFiber4Block2Chunk2ParentMap_9_ok,
    tttLargeFiber4Block2Chunk2ParentMap_10_ok,
    tttLargeFiber4Block2Chunk2ParentMap_11_ok,
    tttLargeFiber4Block2Chunk2ParentMap_12_ok,
    tttLargeFiber4Block2Chunk2ParentMap_13_ok,
    tttLargeFiber4Block2Chunk2ParentMap_14_ok,
    tttLargeFiber4Block2Chunk2ParentMap_15_ok]

def tttLargeFiber4Block2Chunk2ParentsAudit : Bool :=
  tttLargeFiber4Block2Chunk2ParentPathCheck 0
    && tttLargeFiber4Block2Chunk2ParentPathCheck 1
    && tttLargeFiber4Block2Chunk2ParentPathCheck 2
    && tttLargeFiber4Block2Chunk2ParentPathCheck 3
    && tttLargeFiber4Block2Chunk2ParentPathCheck 4
    && tttLargeFiber4Block2Chunk2ParentPathCheck 5
    && tttLargeFiber4Block2Chunk2ParentPathCheck 6
    && tttLargeFiber4Block2Chunk2ParentPathCheck 7
    && tttLargeFiber4Block2Chunk2ParentPathCheck 8
    && tttLargeFiber4Block2Chunk2ParentPathCheck 9
    && tttLargeFiber4Block2Chunk2ParentPathCheck 10
    && tttLargeFiber4Block2Chunk2ParentPathCheck 11
    && tttLargeFiber4Block2Chunk2ParentPathCheck 12
    && tttLargeFiber4Block2Chunk2ParentPathCheck 13
    && tttLargeFiber4Block2Chunk2ParentPathCheck 14
    && tttLargeFiber4Block2Chunk2ParentPathCheck 15

theorem tttLargeFiber4Block2Chunk2ParentsAudit_ok :
    tttLargeFiber4Block2Chunk2ParentsAudit = true := by
  simp [tttLargeFiber4Block2Chunk2ParentsAudit,
    tttLargeFiber4Block2Chunk2ParentPath_0_ok,
    tttLargeFiber4Block2Chunk2ParentPath_1_ok,
    tttLargeFiber4Block2Chunk2ParentPath_2_ok,
    tttLargeFiber4Block2Chunk2ParentPath_3_ok,
    tttLargeFiber4Block2Chunk2ParentPath_4_ok,
    tttLargeFiber4Block2Chunk2ParentPath_5_ok,
    tttLargeFiber4Block2Chunk2ParentPath_6_ok,
    tttLargeFiber4Block2Chunk2ParentPath_7_ok,
    tttLargeFiber4Block2Chunk2ParentPath_8_ok,
    tttLargeFiber4Block2Chunk2ParentPath_9_ok,
    tttLargeFiber4Block2Chunk2ParentPath_10_ok,
    tttLargeFiber4Block2Chunk2ParentPath_11_ok,
    tttLargeFiber4Block2Chunk2ParentPath_12_ok,
    tttLargeFiber4Block2Chunk2ParentPath_13_ok,
    tttLargeFiber4Block2Chunk2ParentPath_14_ok,
    tttLargeFiber4Block2Chunk2ParentPath_15_ok]

def tttLargeFiber4Block2Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block2Chunk2SourcesCheck &&
    tttLargeFiber4Block2Chunk2RowsAudit &&
    tttLargeFiber4Block2Chunk2ParentMapAudit &&
    tttLargeFiber4Block2Chunk2ParentsAudit

theorem tttLargeFiber4Block2Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber4Block2Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block2Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block2Chunk2SourcesCheck_ok,
    tttLargeFiber4Block2Chunk2RowsAudit_ok,
    tttLargeFiber4Block2Chunk2ParentMapAudit_ok,
    tttLargeFiber4Block2Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block2Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
