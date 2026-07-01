import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 7 chunk 2

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
For second-range rows it uses interval membership and explicit bounded parent
paths, avoiding broad expected-list traversal and recursive parent iteration.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block7Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block7Chunk2Sources : List Nat :=
  [4048, 4049, 4050, 4051, 4052, 4053, 4054, 4055,
   4056, 4057, 4058, 4059, 4060, 4061, 4062, 4063]

def tttLargeFiber4Row480 : TripleComponentParentRow :=
  tripleRow 4048 2208 119 124 132 64 100 132
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row481 : TripleComponentParentRow :=
  tripleRow 4049 2209 119 124 133 64 100 133
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row482 : TripleComponentParentRow :=
  tripleRow 4050 2210 119 124 134 64 100 134
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row483 : TripleComponentParentRow :=
  tripleRow 4051 2211 119 124 135 64 100 135
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row484 : TripleComponentParentRow :=
  tripleRow 4052 2212 119 124 180 64 100 180
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row485 : TripleComponentParentRow :=
  tripleRow 4053 2213 119 124 181 64 100 181
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row486 : TripleComponentParentRow :=
  tripleRow 4054 2214 119 124 182 64 100 182
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row487 : TripleComponentParentRow :=
  tripleRow 4055 2215 119 124 183 64 100 183
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row488 : TripleComponentParentRow :=
  tripleRow 4056 2216 119 125 140 64 101 140
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row489 : TripleComponentParentRow :=
  tripleRow 4057 2217 119 125 141 64 101 141
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row490 : TripleComponentParentRow :=
  tripleRow 4058 2218 119 125 142 64 101 142
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row491 : TripleComponentParentRow :=
  tripleRow 4059 2219 119 125 143 64 101 143
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row492 : TripleComponentParentRow :=
  tripleRow 4060 2220 119 125 188 64 101 188
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row493 : TripleComponentParentRow :=
  tripleRow 4061 2221 119 125 189 64 101 189
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row494 : TripleComponentParentRow :=
  tripleRow 4062 2222 119 125 190 64 101 190
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row495 : TripleComponentParentRow :=
  tripleRow 4063 2223 119 125 191 64 101 191
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Block7Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row480
  , tttLargeFiber4Row481
  , tttLargeFiber4Row482
  , tttLargeFiber4Row483
  , tttLargeFiber4Row484
  , tttLargeFiber4Row485
  , tttLargeFiber4Row486
  , tttLargeFiber4Row487
  , tttLargeFiber4Row488
  , tttLargeFiber4Row489
  , tttLargeFiber4Row490
  , tttLargeFiber4Row491
  , tttLargeFiber4Row492
  , tttLargeFiber4Row493
  , tttLargeFiber4Row494
  , tttLargeFiber4Row495
  ]

def tttLargeFiber4Block7Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (2176 <= i) && decide (i < 2432)) ||
    (decide (3824 <= i) && decide (i < 4080))

def tttLargeFiber4Block7Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber4Block7Chunk2ExpectedContains row.source &&
    tttLargeFiber4Block7Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber4Key &&
          chainInputKey tttWord t == tttLargeFiber4Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber4Block7Chunk2SourcesCheck : Bool :=
  (tttLargeFiber4Block7Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber4Block7Chunk2Sources

theorem tttLargeFiber4Block7Chunk2SourcesCheck_ok :
    tttLargeFiber4Block7Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber4Block7Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber4Block7Chunk2RowValid
    (listGetD tttLargeFiber4Block7Chunk2Rows i default)

def tttLargeFiber4Block7Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block7Chunk2Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block7Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block7Chunk2Sources 0 0 == 4048 &&
      tttLargeFiber4ParentOf 4048 == 2208 &&
      tttLargeFiber4ParentOf 2208 == 2224 &&
      tttLargeFiber4ParentOf 2224 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block7Chunk2Sources 1 0 == 4049 &&
      tttLargeFiber4ParentOf 4049 == 2209 &&
      tttLargeFiber4ParentOf 2209 == 2225 &&
      tttLargeFiber4ParentOf 2225 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block7Chunk2Sources 2 0 == 4050 &&
      tttLargeFiber4ParentOf 4050 == 2210 &&
      tttLargeFiber4ParentOf 2210 == 2198 &&
      tttLargeFiber4ParentOf 2198 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block7Chunk2Sources 3 0 == 4051 &&
      tttLargeFiber4ParentOf 4051 == 2211 &&
      tttLargeFiber4ParentOf 2211 == 2199 &&
      tttLargeFiber4ParentOf 2199 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block7Chunk2Sources 4 0 == 4052 &&
      tttLargeFiber4ParentOf 4052 == 2212 &&
      tttLargeFiber4ParentOf 2212 == 2194 &&
      tttLargeFiber4ParentOf 2194 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block7Chunk2Sources 5 0 == 4053 &&
      tttLargeFiber4ParentOf 4053 == 2213 &&
      tttLargeFiber4ParentOf 2213 == 2215 &&
      tttLargeFiber4ParentOf 2215 == 2192 &&
      tttLargeFiber4ParentOf 2192 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block7Chunk2Sources 6 0 == 4054 &&
      tttLargeFiber4ParentOf 4054 == 2214 &&
      tttLargeFiber4ParentOf 2214 == 2193 &&
      tttLargeFiber4ParentOf 2193 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block7Chunk2Sources 7 0 == 4055 &&
      tttLargeFiber4ParentOf 4055 == 2215 &&
      tttLargeFiber4ParentOf 2215 == 2192 &&
      tttLargeFiber4ParentOf 2192 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block7Chunk2Sources 8 0 == 4056 &&
      tttLargeFiber4ParentOf 4056 == 2216 &&
      tttLargeFiber4ParentOf 2216 == 2232 &&
      tttLargeFiber4ParentOf 2232 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block7Chunk2Sources 9 0 == 4057 &&
      tttLargeFiber4ParentOf 4057 == 2217 &&
      tttLargeFiber4ParentOf 2217 == 2233 &&
      tttLargeFiber4ParentOf 2233 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block7Chunk2Sources 10 0 == 4058 &&
      tttLargeFiber4ParentOf 4058 == 2218 &&
      tttLargeFiber4ParentOf 2218 == 2234 &&
      tttLargeFiber4ParentOf 2234 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block7Chunk2Sources 11 0 == 4059 &&
      tttLargeFiber4ParentOf 4059 == 2219 &&
      tttLargeFiber4ParentOf 2219 == 2216 &&
      tttLargeFiber4ParentOf 2216 == 2232 &&
      tttLargeFiber4ParentOf 2232 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block7Chunk2Sources 12 0 == 4060 &&
      tttLargeFiber4ParentOf 4060 == 2220 &&
      tttLargeFiber4ParentOf 2220 == 2216 &&
      tttLargeFiber4ParentOf 2216 == 2232 &&
      tttLargeFiber4ParentOf 2232 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block7Chunk2Sources 13 0 == 4061 &&
      tttLargeFiber4ParentOf 4061 == 2221 &&
      tttLargeFiber4ParentOf 2221 == 2217 &&
      tttLargeFiber4ParentOf 2217 == 2233 &&
      tttLargeFiber4ParentOf 2233 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block7Chunk2Sources 14 0 == 4062 &&
      tttLargeFiber4ParentOf 4062 == 2222 &&
      tttLargeFiber4ParentOf 2222 == 2238 &&
      tttLargeFiber4ParentOf 2238 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block7Chunk2Sources 15 0 == 4063 &&
      tttLargeFiber4ParentOf 4063 == 2223 &&
      tttLargeFiber4ParentOf 2223 == 2239 &&
      tttLargeFiber4ParentOf 2239 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block7Chunk2Row_0_ok :
    tttLargeFiber4Block7Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2Row_1_ok :
    tttLargeFiber4Block7Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2Row_2_ok :
    tttLargeFiber4Block7Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2Row_3_ok :
    tttLargeFiber4Block7Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2Row_4_ok :
    tttLargeFiber4Block7Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2Row_5_ok :
    tttLargeFiber4Block7Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2Row_6_ok :
    tttLargeFiber4Block7Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2Row_7_ok :
    tttLargeFiber4Block7Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2Row_8_ok :
    tttLargeFiber4Block7Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2Row_9_ok :
    tttLargeFiber4Block7Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2Row_10_ok :
    tttLargeFiber4Block7Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2Row_11_ok :
    tttLargeFiber4Block7Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2Row_12_ok :
    tttLargeFiber4Block7Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2Row_13_ok :
    tttLargeFiber4Block7Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2Row_14_ok :
    tttLargeFiber4Block7Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2Row_15_ok :
    tttLargeFiber4Block7Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentMap_0_ok :
    tttLargeFiber4Block7Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentMap_1_ok :
    tttLargeFiber4Block7Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentMap_2_ok :
    tttLargeFiber4Block7Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentMap_3_ok :
    tttLargeFiber4Block7Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentMap_4_ok :
    tttLargeFiber4Block7Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentMap_5_ok :
    tttLargeFiber4Block7Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentMap_6_ok :
    tttLargeFiber4Block7Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentMap_7_ok :
    tttLargeFiber4Block7Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentMap_8_ok :
    tttLargeFiber4Block7Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentMap_9_ok :
    tttLargeFiber4Block7Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentMap_10_ok :
    tttLargeFiber4Block7Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentMap_11_ok :
    tttLargeFiber4Block7Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentMap_12_ok :
    tttLargeFiber4Block7Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentMap_13_ok :
    tttLargeFiber4Block7Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentMap_14_ok :
    tttLargeFiber4Block7Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentMap_15_ok :
    tttLargeFiber4Block7Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentPath_0_ok :
    tttLargeFiber4Block7Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentPath_1_ok :
    tttLargeFiber4Block7Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentPath_2_ok :
    tttLargeFiber4Block7Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentPath_3_ok :
    tttLargeFiber4Block7Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentPath_4_ok :
    tttLargeFiber4Block7Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentPath_5_ok :
    tttLargeFiber4Block7Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentPath_6_ok :
    tttLargeFiber4Block7Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentPath_7_ok :
    tttLargeFiber4Block7Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentPath_8_ok :
    tttLargeFiber4Block7Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentPath_9_ok :
    tttLargeFiber4Block7Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentPath_10_ok :
    tttLargeFiber4Block7Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentPath_11_ok :
    tttLargeFiber4Block7Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentPath_12_ok :
    tttLargeFiber4Block7Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentPath_13_ok :
    tttLargeFiber4Block7Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentPath_14_ok :
    tttLargeFiber4Block7Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block7Chunk2ParentPath_15_ok :
    tttLargeFiber4Block7Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block7Chunk2RowsAudit : Bool :=
  tttLargeFiber4Block7Chunk2RowCheck 0
    && tttLargeFiber4Block7Chunk2RowCheck 1
    && tttLargeFiber4Block7Chunk2RowCheck 2
    && tttLargeFiber4Block7Chunk2RowCheck 3
    && tttLargeFiber4Block7Chunk2RowCheck 4
    && tttLargeFiber4Block7Chunk2RowCheck 5
    && tttLargeFiber4Block7Chunk2RowCheck 6
    && tttLargeFiber4Block7Chunk2RowCheck 7
    && tttLargeFiber4Block7Chunk2RowCheck 8
    && tttLargeFiber4Block7Chunk2RowCheck 9
    && tttLargeFiber4Block7Chunk2RowCheck 10
    && tttLargeFiber4Block7Chunk2RowCheck 11
    && tttLargeFiber4Block7Chunk2RowCheck 12
    && tttLargeFiber4Block7Chunk2RowCheck 13
    && tttLargeFiber4Block7Chunk2RowCheck 14
    && tttLargeFiber4Block7Chunk2RowCheck 15

theorem tttLargeFiber4Block7Chunk2RowsAudit_ok :
    tttLargeFiber4Block7Chunk2RowsAudit = true := by
  simp [tttLargeFiber4Block7Chunk2RowsAudit,
    tttLargeFiber4Block7Chunk2Row_0_ok,
    tttLargeFiber4Block7Chunk2Row_1_ok,
    tttLargeFiber4Block7Chunk2Row_2_ok,
    tttLargeFiber4Block7Chunk2Row_3_ok,
    tttLargeFiber4Block7Chunk2Row_4_ok,
    tttLargeFiber4Block7Chunk2Row_5_ok,
    tttLargeFiber4Block7Chunk2Row_6_ok,
    tttLargeFiber4Block7Chunk2Row_7_ok,
    tttLargeFiber4Block7Chunk2Row_8_ok,
    tttLargeFiber4Block7Chunk2Row_9_ok,
    tttLargeFiber4Block7Chunk2Row_10_ok,
    tttLargeFiber4Block7Chunk2Row_11_ok,
    tttLargeFiber4Block7Chunk2Row_12_ok,
    tttLargeFiber4Block7Chunk2Row_13_ok,
    tttLargeFiber4Block7Chunk2Row_14_ok,
    tttLargeFiber4Block7Chunk2Row_15_ok]

def tttLargeFiber4Block7Chunk2ParentMapAudit : Bool :=
  tttLargeFiber4Block7Chunk2ParentMapCheck 0
    && tttLargeFiber4Block7Chunk2ParentMapCheck 1
    && tttLargeFiber4Block7Chunk2ParentMapCheck 2
    && tttLargeFiber4Block7Chunk2ParentMapCheck 3
    && tttLargeFiber4Block7Chunk2ParentMapCheck 4
    && tttLargeFiber4Block7Chunk2ParentMapCheck 5
    && tttLargeFiber4Block7Chunk2ParentMapCheck 6
    && tttLargeFiber4Block7Chunk2ParentMapCheck 7
    && tttLargeFiber4Block7Chunk2ParentMapCheck 8
    && tttLargeFiber4Block7Chunk2ParentMapCheck 9
    && tttLargeFiber4Block7Chunk2ParentMapCheck 10
    && tttLargeFiber4Block7Chunk2ParentMapCheck 11
    && tttLargeFiber4Block7Chunk2ParentMapCheck 12
    && tttLargeFiber4Block7Chunk2ParentMapCheck 13
    && tttLargeFiber4Block7Chunk2ParentMapCheck 14
    && tttLargeFiber4Block7Chunk2ParentMapCheck 15

theorem tttLargeFiber4Block7Chunk2ParentMapAudit_ok :
    tttLargeFiber4Block7Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber4Block7Chunk2ParentMapAudit,
    tttLargeFiber4Block7Chunk2ParentMap_0_ok,
    tttLargeFiber4Block7Chunk2ParentMap_1_ok,
    tttLargeFiber4Block7Chunk2ParentMap_2_ok,
    tttLargeFiber4Block7Chunk2ParentMap_3_ok,
    tttLargeFiber4Block7Chunk2ParentMap_4_ok,
    tttLargeFiber4Block7Chunk2ParentMap_5_ok,
    tttLargeFiber4Block7Chunk2ParentMap_6_ok,
    tttLargeFiber4Block7Chunk2ParentMap_7_ok,
    tttLargeFiber4Block7Chunk2ParentMap_8_ok,
    tttLargeFiber4Block7Chunk2ParentMap_9_ok,
    tttLargeFiber4Block7Chunk2ParentMap_10_ok,
    tttLargeFiber4Block7Chunk2ParentMap_11_ok,
    tttLargeFiber4Block7Chunk2ParentMap_12_ok,
    tttLargeFiber4Block7Chunk2ParentMap_13_ok,
    tttLargeFiber4Block7Chunk2ParentMap_14_ok,
    tttLargeFiber4Block7Chunk2ParentMap_15_ok]

def tttLargeFiber4Block7Chunk2ParentsAudit : Bool :=
  tttLargeFiber4Block7Chunk2ParentPathCheck 0
    && tttLargeFiber4Block7Chunk2ParentPathCheck 1
    && tttLargeFiber4Block7Chunk2ParentPathCheck 2
    && tttLargeFiber4Block7Chunk2ParentPathCheck 3
    && tttLargeFiber4Block7Chunk2ParentPathCheck 4
    && tttLargeFiber4Block7Chunk2ParentPathCheck 5
    && tttLargeFiber4Block7Chunk2ParentPathCheck 6
    && tttLargeFiber4Block7Chunk2ParentPathCheck 7
    && tttLargeFiber4Block7Chunk2ParentPathCheck 8
    && tttLargeFiber4Block7Chunk2ParentPathCheck 9
    && tttLargeFiber4Block7Chunk2ParentPathCheck 10
    && tttLargeFiber4Block7Chunk2ParentPathCheck 11
    && tttLargeFiber4Block7Chunk2ParentPathCheck 12
    && tttLargeFiber4Block7Chunk2ParentPathCheck 13
    && tttLargeFiber4Block7Chunk2ParentPathCheck 14
    && tttLargeFiber4Block7Chunk2ParentPathCheck 15

theorem tttLargeFiber4Block7Chunk2ParentsAudit_ok :
    tttLargeFiber4Block7Chunk2ParentsAudit = true := by
  simp [tttLargeFiber4Block7Chunk2ParentsAudit,
    tttLargeFiber4Block7Chunk2ParentPath_0_ok,
    tttLargeFiber4Block7Chunk2ParentPath_1_ok,
    tttLargeFiber4Block7Chunk2ParentPath_2_ok,
    tttLargeFiber4Block7Chunk2ParentPath_3_ok,
    tttLargeFiber4Block7Chunk2ParentPath_4_ok,
    tttLargeFiber4Block7Chunk2ParentPath_5_ok,
    tttLargeFiber4Block7Chunk2ParentPath_6_ok,
    tttLargeFiber4Block7Chunk2ParentPath_7_ok,
    tttLargeFiber4Block7Chunk2ParentPath_8_ok,
    tttLargeFiber4Block7Chunk2ParentPath_9_ok,
    tttLargeFiber4Block7Chunk2ParentPath_10_ok,
    tttLargeFiber4Block7Chunk2ParentPath_11_ok,
    tttLargeFiber4Block7Chunk2ParentPath_12_ok,
    tttLargeFiber4Block7Chunk2ParentPath_13_ok,
    tttLargeFiber4Block7Chunk2ParentPath_14_ok,
    tttLargeFiber4Block7Chunk2ParentPath_15_ok]

def tttLargeFiber4Block7Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block7Chunk2SourcesCheck &&
    tttLargeFiber4Block7Chunk2RowsAudit &&
    tttLargeFiber4Block7Chunk2ParentMapAudit &&
    tttLargeFiber4Block7Chunk2ParentsAudit

theorem tttLargeFiber4Block7Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber4Block7Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block7Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block7Chunk2SourcesCheck_ok,
    tttLargeFiber4Block7Chunk2RowsAudit_ok,
    tttLargeFiber4Block7Chunk2ParentMapAudit_ok,
    tttLargeFiber4Block7Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block7Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
