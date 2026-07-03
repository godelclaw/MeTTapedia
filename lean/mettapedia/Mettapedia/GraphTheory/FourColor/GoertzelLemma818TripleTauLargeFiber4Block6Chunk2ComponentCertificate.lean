import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 6 chunk 2

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
For second-range rows it uses interval membership and explicit bounded parent
paths, avoiding broad expected-list traversal and recursive parent iteration.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block6Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block6Chunk2Sources : List Nat :=
  [3984, 3985, 3986, 3987, 3988, 3989, 3990, 3991,
   3992, 3993, 3994, 3995, 3996, 3997, 3998, 3999]

def tttLargeFiber4Row416 : TripleComponentParentRow :=
  tripleRow 3984 2272 118 116 132 65 108 132
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row417 : TripleComponentParentRow :=
  tripleRow 3985 2273 118 116 133 65 108 133
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row418 : TripleComponentParentRow :=
  tripleRow 3986 2274 118 116 134 65 108 134
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row419 : TripleComponentParentRow :=
  tripleRow 3987 2275 118 116 135 65 108 135
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row420 : TripleComponentParentRow :=
  tripleRow 3988 2276 118 116 180 65 108 180
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row421 : TripleComponentParentRow :=
  tripleRow 3989 2277 118 116 181 65 108 181
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row422 : TripleComponentParentRow :=
  tripleRow 3990 2278 118 116 182 65 108 182
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row423 : TripleComponentParentRow :=
  tripleRow 3991 2279 118 116 183 65 108 183
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row424 : TripleComponentParentRow :=
  tripleRow 3992 2280 118 117 140 65 109 140
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row425 : TripleComponentParentRow :=
  tripleRow 3993 2281 118 117 141 65 109 141
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row426 : TripleComponentParentRow :=
  tripleRow 3994 2282 118 117 142 65 109 142
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row427 : TripleComponentParentRow :=
  tripleRow 3995 2283 118 117 143 65 109 143
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row428 : TripleComponentParentRow :=
  tripleRow 3996 2284 118 117 188 65 109 188
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row429 : TripleComponentParentRow :=
  tripleRow 3997 2285 118 117 189 65 109 189
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row430 : TripleComponentParentRow :=
  tripleRow 3998 2286 118 117 190 65 109 190
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row431 : TripleComponentParentRow :=
  tripleRow 3999 2287 118 117 191 65 109 191
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Block6Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row416
  , tttLargeFiber4Row417
  , tttLargeFiber4Row418
  , tttLargeFiber4Row419
  , tttLargeFiber4Row420
  , tttLargeFiber4Row421
  , tttLargeFiber4Row422
  , tttLargeFiber4Row423
  , tttLargeFiber4Row424
  , tttLargeFiber4Row425
  , tttLargeFiber4Row426
  , tttLargeFiber4Row427
  , tttLargeFiber4Row428
  , tttLargeFiber4Row429
  , tttLargeFiber4Row430
  , tttLargeFiber4Row431
  ]

def tttLargeFiber4Block6Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (2176 <= i) && decide (i < 2432)) ||
    (decide (3824 <= i) && decide (i < 4080))

def tttLargeFiber4Block6Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber4Block6Chunk2ExpectedContains row.source &&
    tttLargeFiber4Block6Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber4Key &&
          chainInputKey tttWord t == tttLargeFiber4Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber4Block6Chunk2SourcesCheck : Bool :=
  (tttLargeFiber4Block6Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber4Block6Chunk2Sources

theorem tttLargeFiber4Block6Chunk2SourcesCheck_ok :
    tttLargeFiber4Block6Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber4Block6Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber4Block6Chunk2RowValid
    (listGetD tttLargeFiber4Block6Chunk2Rows i default)

def tttLargeFiber4Block6Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block6Chunk2Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block6Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block6Chunk2Sources 0 0 == 3984 &&
      tttLargeFiber4ParentOf 3984 == 2272 &&
      tttLargeFiber4ParentOf 2272 == 2208 &&
      tttLargeFiber4ParentOf 2208 == 2224 &&
      tttLargeFiber4ParentOf 2224 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block6Chunk2Sources 1 0 == 3985 &&
      tttLargeFiber4ParentOf 3985 == 2273 &&
      tttLargeFiber4ParentOf 2273 == 2209 &&
      tttLargeFiber4ParentOf 2209 == 2225 &&
      tttLargeFiber4ParentOf 2225 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block6Chunk2Sources 2 0 == 3986 &&
      tttLargeFiber4ParentOf 3986 == 2274 &&
      tttLargeFiber4ParentOf 2274 == 2210 &&
      tttLargeFiber4ParentOf 2210 == 2198 &&
      tttLargeFiber4ParentOf 2198 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block6Chunk2Sources 3 0 == 3987 &&
      tttLargeFiber4ParentOf 3987 == 2275 &&
      tttLargeFiber4ParentOf 2275 == 2211 &&
      tttLargeFiber4ParentOf 2211 == 2199 &&
      tttLargeFiber4ParentOf 2199 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block6Chunk2Sources 4 0 == 3988 &&
      tttLargeFiber4ParentOf 3988 == 2276 &&
      tttLargeFiber4ParentOf 2276 == 2212 &&
      tttLargeFiber4ParentOf 2212 == 2194 &&
      tttLargeFiber4ParentOf 2194 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block6Chunk2Sources 5 0 == 3989 &&
      tttLargeFiber4ParentOf 3989 == 2277 &&
      tttLargeFiber4ParentOf 2277 == 2213 &&
      tttLargeFiber4ParentOf 2213 == 2215 &&
      tttLargeFiber4ParentOf 2215 == 2192 &&
      tttLargeFiber4ParentOf 2192 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block6Chunk2Sources 6 0 == 3990 &&
      tttLargeFiber4ParentOf 3990 == 2278 &&
      tttLargeFiber4ParentOf 2278 == 2214 &&
      tttLargeFiber4ParentOf 2214 == 2193 &&
      tttLargeFiber4ParentOf 2193 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block6Chunk2Sources 7 0 == 3991 &&
      tttLargeFiber4ParentOf 3991 == 2279 &&
      tttLargeFiber4ParentOf 2279 == 2215 &&
      tttLargeFiber4ParentOf 2215 == 2192 &&
      tttLargeFiber4ParentOf 2192 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block6Chunk2Sources 8 0 == 3992 &&
      tttLargeFiber4ParentOf 3992 == 2280 &&
      tttLargeFiber4ParentOf 2280 == 2216 &&
      tttLargeFiber4ParentOf 2216 == 2232 &&
      tttLargeFiber4ParentOf 2232 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block6Chunk2Sources 9 0 == 3993 &&
      tttLargeFiber4ParentOf 3993 == 2281 &&
      tttLargeFiber4ParentOf 2281 == 2217 &&
      tttLargeFiber4ParentOf 2217 == 2233 &&
      tttLargeFiber4ParentOf 2233 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block6Chunk2Sources 10 0 == 3994 &&
      tttLargeFiber4ParentOf 3994 == 2282 &&
      tttLargeFiber4ParentOf 2282 == 2218 &&
      tttLargeFiber4ParentOf 2218 == 2234 &&
      tttLargeFiber4ParentOf 2234 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block6Chunk2Sources 11 0 == 3995 &&
      tttLargeFiber4ParentOf 3995 == 2283 &&
      tttLargeFiber4ParentOf 2283 == 2219 &&
      tttLargeFiber4ParentOf 2219 == 2216 &&
      tttLargeFiber4ParentOf 2216 == 2232 &&
      tttLargeFiber4ParentOf 2232 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block6Chunk2Sources 12 0 == 3996 &&
      tttLargeFiber4ParentOf 3996 == 2284 &&
      tttLargeFiber4ParentOf 2284 == 2220 &&
      tttLargeFiber4ParentOf 2220 == 2216 &&
      tttLargeFiber4ParentOf 2216 == 2232 &&
      tttLargeFiber4ParentOf 2232 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block6Chunk2Sources 13 0 == 3997 &&
      tttLargeFiber4ParentOf 3997 == 2285 &&
      tttLargeFiber4ParentOf 2285 == 2221 &&
      tttLargeFiber4ParentOf 2221 == 2217 &&
      tttLargeFiber4ParentOf 2217 == 2233 &&
      tttLargeFiber4ParentOf 2233 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block6Chunk2Sources 14 0 == 3998 &&
      tttLargeFiber4ParentOf 3998 == 2286 &&
      tttLargeFiber4ParentOf 2286 == 2222 &&
      tttLargeFiber4ParentOf 2222 == 2238 &&
      tttLargeFiber4ParentOf 2238 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block6Chunk2Sources 15 0 == 3999 &&
      tttLargeFiber4ParentOf 3999 == 2287 &&
      tttLargeFiber4ParentOf 2287 == 2223 &&
      tttLargeFiber4ParentOf 2223 == 2239 &&
      tttLargeFiber4ParentOf 2239 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block6Chunk2Row_0_ok :
    tttLargeFiber4Block6Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2Row_1_ok :
    tttLargeFiber4Block6Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2Row_2_ok :
    tttLargeFiber4Block6Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2Row_3_ok :
    tttLargeFiber4Block6Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2Row_4_ok :
    tttLargeFiber4Block6Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2Row_5_ok :
    tttLargeFiber4Block6Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2Row_6_ok :
    tttLargeFiber4Block6Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2Row_7_ok :
    tttLargeFiber4Block6Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2Row_8_ok :
    tttLargeFiber4Block6Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2Row_9_ok :
    tttLargeFiber4Block6Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2Row_10_ok :
    tttLargeFiber4Block6Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2Row_11_ok :
    tttLargeFiber4Block6Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2Row_12_ok :
    tttLargeFiber4Block6Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2Row_13_ok :
    tttLargeFiber4Block6Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2Row_14_ok :
    tttLargeFiber4Block6Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2Row_15_ok :
    tttLargeFiber4Block6Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentMap_0_ok :
    tttLargeFiber4Block6Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentMap_1_ok :
    tttLargeFiber4Block6Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentMap_2_ok :
    tttLargeFiber4Block6Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentMap_3_ok :
    tttLargeFiber4Block6Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentMap_4_ok :
    tttLargeFiber4Block6Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentMap_5_ok :
    tttLargeFiber4Block6Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentMap_6_ok :
    tttLargeFiber4Block6Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentMap_7_ok :
    tttLargeFiber4Block6Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentMap_8_ok :
    tttLargeFiber4Block6Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentMap_9_ok :
    tttLargeFiber4Block6Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentMap_10_ok :
    tttLargeFiber4Block6Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentMap_11_ok :
    tttLargeFiber4Block6Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentMap_12_ok :
    tttLargeFiber4Block6Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentMap_13_ok :
    tttLargeFiber4Block6Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentMap_14_ok :
    tttLargeFiber4Block6Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentMap_15_ok :
    tttLargeFiber4Block6Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentPath_0_ok :
    tttLargeFiber4Block6Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentPath_1_ok :
    tttLargeFiber4Block6Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentPath_2_ok :
    tttLargeFiber4Block6Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentPath_3_ok :
    tttLargeFiber4Block6Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentPath_4_ok :
    tttLargeFiber4Block6Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentPath_5_ok :
    tttLargeFiber4Block6Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentPath_6_ok :
    tttLargeFiber4Block6Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentPath_7_ok :
    tttLargeFiber4Block6Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentPath_8_ok :
    tttLargeFiber4Block6Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentPath_9_ok :
    tttLargeFiber4Block6Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentPath_10_ok :
    tttLargeFiber4Block6Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentPath_11_ok :
    tttLargeFiber4Block6Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentPath_12_ok :
    tttLargeFiber4Block6Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentPath_13_ok :
    tttLargeFiber4Block6Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentPath_14_ok :
    tttLargeFiber4Block6Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block6Chunk2ParentPath_15_ok :
    tttLargeFiber4Block6Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block6Chunk2RowsAudit : Bool :=
  tttLargeFiber4Block6Chunk2RowCheck 0
    && tttLargeFiber4Block6Chunk2RowCheck 1
    && tttLargeFiber4Block6Chunk2RowCheck 2
    && tttLargeFiber4Block6Chunk2RowCheck 3
    && tttLargeFiber4Block6Chunk2RowCheck 4
    && tttLargeFiber4Block6Chunk2RowCheck 5
    && tttLargeFiber4Block6Chunk2RowCheck 6
    && tttLargeFiber4Block6Chunk2RowCheck 7
    && tttLargeFiber4Block6Chunk2RowCheck 8
    && tttLargeFiber4Block6Chunk2RowCheck 9
    && tttLargeFiber4Block6Chunk2RowCheck 10
    && tttLargeFiber4Block6Chunk2RowCheck 11
    && tttLargeFiber4Block6Chunk2RowCheck 12
    && tttLargeFiber4Block6Chunk2RowCheck 13
    && tttLargeFiber4Block6Chunk2RowCheck 14
    && tttLargeFiber4Block6Chunk2RowCheck 15

theorem tttLargeFiber4Block6Chunk2RowsAudit_ok :
    tttLargeFiber4Block6Chunk2RowsAudit = true := by
  simp [tttLargeFiber4Block6Chunk2RowsAudit,
    tttLargeFiber4Block6Chunk2Row_0_ok,
    tttLargeFiber4Block6Chunk2Row_1_ok,
    tttLargeFiber4Block6Chunk2Row_2_ok,
    tttLargeFiber4Block6Chunk2Row_3_ok,
    tttLargeFiber4Block6Chunk2Row_4_ok,
    tttLargeFiber4Block6Chunk2Row_5_ok,
    tttLargeFiber4Block6Chunk2Row_6_ok,
    tttLargeFiber4Block6Chunk2Row_7_ok,
    tttLargeFiber4Block6Chunk2Row_8_ok,
    tttLargeFiber4Block6Chunk2Row_9_ok,
    tttLargeFiber4Block6Chunk2Row_10_ok,
    tttLargeFiber4Block6Chunk2Row_11_ok,
    tttLargeFiber4Block6Chunk2Row_12_ok,
    tttLargeFiber4Block6Chunk2Row_13_ok,
    tttLargeFiber4Block6Chunk2Row_14_ok,
    tttLargeFiber4Block6Chunk2Row_15_ok]

def tttLargeFiber4Block6Chunk2ParentMapAudit : Bool :=
  tttLargeFiber4Block6Chunk2ParentMapCheck 0
    && tttLargeFiber4Block6Chunk2ParentMapCheck 1
    && tttLargeFiber4Block6Chunk2ParentMapCheck 2
    && tttLargeFiber4Block6Chunk2ParentMapCheck 3
    && tttLargeFiber4Block6Chunk2ParentMapCheck 4
    && tttLargeFiber4Block6Chunk2ParentMapCheck 5
    && tttLargeFiber4Block6Chunk2ParentMapCheck 6
    && tttLargeFiber4Block6Chunk2ParentMapCheck 7
    && tttLargeFiber4Block6Chunk2ParentMapCheck 8
    && tttLargeFiber4Block6Chunk2ParentMapCheck 9
    && tttLargeFiber4Block6Chunk2ParentMapCheck 10
    && tttLargeFiber4Block6Chunk2ParentMapCheck 11
    && tttLargeFiber4Block6Chunk2ParentMapCheck 12
    && tttLargeFiber4Block6Chunk2ParentMapCheck 13
    && tttLargeFiber4Block6Chunk2ParentMapCheck 14
    && tttLargeFiber4Block6Chunk2ParentMapCheck 15

theorem tttLargeFiber4Block6Chunk2ParentMapAudit_ok :
    tttLargeFiber4Block6Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber4Block6Chunk2ParentMapAudit,
    tttLargeFiber4Block6Chunk2ParentMap_0_ok,
    tttLargeFiber4Block6Chunk2ParentMap_1_ok,
    tttLargeFiber4Block6Chunk2ParentMap_2_ok,
    tttLargeFiber4Block6Chunk2ParentMap_3_ok,
    tttLargeFiber4Block6Chunk2ParentMap_4_ok,
    tttLargeFiber4Block6Chunk2ParentMap_5_ok,
    tttLargeFiber4Block6Chunk2ParentMap_6_ok,
    tttLargeFiber4Block6Chunk2ParentMap_7_ok,
    tttLargeFiber4Block6Chunk2ParentMap_8_ok,
    tttLargeFiber4Block6Chunk2ParentMap_9_ok,
    tttLargeFiber4Block6Chunk2ParentMap_10_ok,
    tttLargeFiber4Block6Chunk2ParentMap_11_ok,
    tttLargeFiber4Block6Chunk2ParentMap_12_ok,
    tttLargeFiber4Block6Chunk2ParentMap_13_ok,
    tttLargeFiber4Block6Chunk2ParentMap_14_ok,
    tttLargeFiber4Block6Chunk2ParentMap_15_ok]

def tttLargeFiber4Block6Chunk2ParentsAudit : Bool :=
  tttLargeFiber4Block6Chunk2ParentPathCheck 0
    && tttLargeFiber4Block6Chunk2ParentPathCheck 1
    && tttLargeFiber4Block6Chunk2ParentPathCheck 2
    && tttLargeFiber4Block6Chunk2ParentPathCheck 3
    && tttLargeFiber4Block6Chunk2ParentPathCheck 4
    && tttLargeFiber4Block6Chunk2ParentPathCheck 5
    && tttLargeFiber4Block6Chunk2ParentPathCheck 6
    && tttLargeFiber4Block6Chunk2ParentPathCheck 7
    && tttLargeFiber4Block6Chunk2ParentPathCheck 8
    && tttLargeFiber4Block6Chunk2ParentPathCheck 9
    && tttLargeFiber4Block6Chunk2ParentPathCheck 10
    && tttLargeFiber4Block6Chunk2ParentPathCheck 11
    && tttLargeFiber4Block6Chunk2ParentPathCheck 12
    && tttLargeFiber4Block6Chunk2ParentPathCheck 13
    && tttLargeFiber4Block6Chunk2ParentPathCheck 14
    && tttLargeFiber4Block6Chunk2ParentPathCheck 15

theorem tttLargeFiber4Block6Chunk2ParentsAudit_ok :
    tttLargeFiber4Block6Chunk2ParentsAudit = true := by
  simp [tttLargeFiber4Block6Chunk2ParentsAudit,
    tttLargeFiber4Block6Chunk2ParentPath_0_ok,
    tttLargeFiber4Block6Chunk2ParentPath_1_ok,
    tttLargeFiber4Block6Chunk2ParentPath_2_ok,
    tttLargeFiber4Block6Chunk2ParentPath_3_ok,
    tttLargeFiber4Block6Chunk2ParentPath_4_ok,
    tttLargeFiber4Block6Chunk2ParentPath_5_ok,
    tttLargeFiber4Block6Chunk2ParentPath_6_ok,
    tttLargeFiber4Block6Chunk2ParentPath_7_ok,
    tttLargeFiber4Block6Chunk2ParentPath_8_ok,
    tttLargeFiber4Block6Chunk2ParentPath_9_ok,
    tttLargeFiber4Block6Chunk2ParentPath_10_ok,
    tttLargeFiber4Block6Chunk2ParentPath_11_ok,
    tttLargeFiber4Block6Chunk2ParentPath_12_ok,
    tttLargeFiber4Block6Chunk2ParentPath_13_ok,
    tttLargeFiber4Block6Chunk2ParentPath_14_ok,
    tttLargeFiber4Block6Chunk2ParentPath_15_ok]

def tttLargeFiber4Block6Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block6Chunk2SourcesCheck &&
    tttLargeFiber4Block6Chunk2RowsAudit &&
    tttLargeFiber4Block6Chunk2ParentMapAudit &&
    tttLargeFiber4Block6Chunk2ParentsAudit

theorem tttLargeFiber4Block6Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber4Block6Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block6Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block6Chunk2SourcesCheck_ok,
    tttLargeFiber4Block6Chunk2RowsAudit_ok,
    tttLargeFiber4Block6Chunk2ParentMapAudit_ok,
    tttLargeFiber4Block6Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block6Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
