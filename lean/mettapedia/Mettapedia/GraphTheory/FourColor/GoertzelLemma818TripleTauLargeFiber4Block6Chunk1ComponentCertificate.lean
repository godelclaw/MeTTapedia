import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 6 chunk 1

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
For second-range rows it uses interval membership and explicit bounded parent
paths, avoiding broad expected-list traversal and recursive parent iteration.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block6Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block6Chunk1Sources : List Nat :=
  [3968, 3969, 3970, 3971, 3972, 3973, 3974, 3975,
   3976, 3977, 3978, 3979, 3980, 3981, 3982, 3983]

def tttLargeFiber4Row400 : TripleComponentParentRow :=
  tripleRow 3968 2256 118 66 16 65 90 16
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row401 : TripleComponentParentRow :=
  tripleRow 3969 2257 118 66 17 65 90 17
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row402 : TripleComponentParentRow :=
  tripleRow 3970 2258 118 66 18 65 90 18
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row403 : TripleComponentParentRow :=
  tripleRow 3971 2259 118 66 19 65 90 19
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row404 : TripleComponentParentRow :=
  tripleRow 3972 2260 118 66 32 65 90 32
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row405 : TripleComponentParentRow :=
  tripleRow 3973 2261 118 66 33 65 90 33
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row406 : TripleComponentParentRow :=
  tripleRow 3974 2262 118 66 34 65 90 34
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row407 : TripleComponentParentRow :=
  tripleRow 3975 2263 118 66 35 65 90 35
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row408 : TripleComponentParentRow :=
  tripleRow 3976 2264 118 67 24 65 91 24
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row409 : TripleComponentParentRow :=
  tripleRow 3977 2265 118 67 25 65 91 25
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row410 : TripleComponentParentRow :=
  tripleRow 3978 2266 118 67 26 65 91 26
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row411 : TripleComponentParentRow :=
  tripleRow 3979 2267 118 67 27 65 91 27
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row412 : TripleComponentParentRow :=
  tripleRow 3980 2268 118 67 40 65 91 40
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row413 : TripleComponentParentRow :=
  tripleRow 3981 2269 118 67 41 65 91 41
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row414 : TripleComponentParentRow :=
  tripleRow 3982 2270 118 67 42 65 91 42
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row415 : TripleComponentParentRow :=
  tripleRow 3983 2271 118 67 43 65 91 43
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Block6Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row400
  , tttLargeFiber4Row401
  , tttLargeFiber4Row402
  , tttLargeFiber4Row403
  , tttLargeFiber4Row404
  , tttLargeFiber4Row405
  , tttLargeFiber4Row406
  , tttLargeFiber4Row407
  , tttLargeFiber4Row408
  , tttLargeFiber4Row409
  , tttLargeFiber4Row410
  , tttLargeFiber4Row411
  , tttLargeFiber4Row412
  , tttLargeFiber4Row413
  , tttLargeFiber4Row414
  , tttLargeFiber4Row415
  ]

def tttLargeFiber4Block6Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (2176 <= i) && decide (i < 2432)) ||
    (decide (3824 <= i) && decide (i < 4080))

def tttLargeFiber4Block6Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber4Block6Chunk1ExpectedContains row.source &&
    tttLargeFiber4Block6Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber4Key &&
          chainInputKey tttWord t == tttLargeFiber4Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber4Block6Chunk1SourcesCheck : Bool :=
  (tttLargeFiber4Block6Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber4Block6Chunk1Sources

theorem tttLargeFiber4Block6Chunk1SourcesCheck_ok :
    tttLargeFiber4Block6Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber4Block6Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber4Block6Chunk1RowValid
    (listGetD tttLargeFiber4Block6Chunk1Rows i default)

def tttLargeFiber4Block6Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block6Chunk1Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block6Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block6Chunk1Sources 0 0 == 3968 &&
      tttLargeFiber4ParentOf 3968 == 2256 &&
      tttLargeFiber4ParentOf 2256 == 2192 &&
      tttLargeFiber4ParentOf 2192 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block6Chunk1Sources 1 0 == 3969 &&
      tttLargeFiber4ParentOf 3969 == 2257 &&
      tttLargeFiber4ParentOf 2257 == 2193 &&
      tttLargeFiber4ParentOf 2193 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block6Chunk1Sources 2 0 == 3970 &&
      tttLargeFiber4ParentOf 3970 == 2258 &&
      tttLargeFiber4ParentOf 2258 == 2194 &&
      tttLargeFiber4ParentOf 2194 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block6Chunk1Sources 3 0 == 3971 &&
      tttLargeFiber4ParentOf 3971 == 2259 &&
      tttLargeFiber4ParentOf 2259 == 2195 &&
      tttLargeFiber4ParentOf 2195 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block6Chunk1Sources 4 0 == 3972 &&
      tttLargeFiber4ParentOf 3972 == 2260 &&
      tttLargeFiber4ParentOf 2260 == 2196 &&
      tttLargeFiber4ParentOf 2196 == 2192 &&
      tttLargeFiber4ParentOf 2192 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block6Chunk1Sources 5 0 == 3973 &&
      tttLargeFiber4ParentOf 3973 == 2261 &&
      tttLargeFiber4ParentOf 2261 == 2197 &&
      tttLargeFiber4ParentOf 2197 == 2193 &&
      tttLargeFiber4ParentOf 2193 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block6Chunk1Sources 6 0 == 3974 &&
      tttLargeFiber4ParentOf 3974 == 2262 &&
      tttLargeFiber4ParentOf 2262 == 2198 &&
      tttLargeFiber4ParentOf 2198 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block6Chunk1Sources 7 0 == 3975 &&
      tttLargeFiber4ParentOf 3975 == 2263 &&
      tttLargeFiber4ParentOf 2263 == 2199 &&
      tttLargeFiber4ParentOf 2199 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block6Chunk1Sources 8 0 == 3976 &&
      tttLargeFiber4ParentOf 3976 == 2264 &&
      tttLargeFiber4ParentOf 2264 == 2200 &&
      tttLargeFiber4ParentOf 2200 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block6Chunk1Sources 9 0 == 3977 &&
      tttLargeFiber4ParentOf 3977 == 2265 &&
      tttLargeFiber4ParentOf 2265 == 2201 &&
      tttLargeFiber4ParentOf 2201 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block6Chunk1Sources 10 0 == 3978 &&
      tttLargeFiber4ParentOf 3978 == 2266 &&
      tttLargeFiber4ParentOf 2266 == 2202 &&
      tttLargeFiber4ParentOf 2202 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block6Chunk1Sources 11 0 == 3979 &&
      tttLargeFiber4ParentOf 3979 == 2267 &&
      tttLargeFiber4ParentOf 2267 == 2203 &&
      tttLargeFiber4ParentOf 2203 == 2187 &&
      tttLargeFiber4ParentOf 2187 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block6Chunk1Sources 12 0 == 3980 &&
      tttLargeFiber4ParentOf 3980 == 2268 &&
      tttLargeFiber4ParentOf 2268 == 2204 &&
      tttLargeFiber4ParentOf 2204 == 2200 &&
      tttLargeFiber4ParentOf 2200 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block6Chunk1Sources 13 0 == 3981 &&
      tttLargeFiber4ParentOf 3981 == 2269 &&
      tttLargeFiber4ParentOf 2269 == 2205 &&
      tttLargeFiber4ParentOf 2205 == 2201 &&
      tttLargeFiber4ParentOf 2201 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block6Chunk1Sources 14 0 == 3982 &&
      tttLargeFiber4ParentOf 3982 == 2270 &&
      tttLargeFiber4ParentOf 2270 == 2206 &&
      tttLargeFiber4ParentOf 2206 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block6Chunk1Sources 15 0 == 3983 &&
      tttLargeFiber4ParentOf 3983 == 2271 &&
      tttLargeFiber4ParentOf 2271 == 2207 &&
      tttLargeFiber4ParentOf 2207 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block6Chunk1Row_0_ok :
    tttLargeFiber4Block6Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1Row_1_ok :
    tttLargeFiber4Block6Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1Row_2_ok :
    tttLargeFiber4Block6Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1Row_3_ok :
    tttLargeFiber4Block6Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1Row_4_ok :
    tttLargeFiber4Block6Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1Row_5_ok :
    tttLargeFiber4Block6Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1Row_6_ok :
    tttLargeFiber4Block6Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1Row_7_ok :
    tttLargeFiber4Block6Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1Row_8_ok :
    tttLargeFiber4Block6Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1Row_9_ok :
    tttLargeFiber4Block6Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1Row_10_ok :
    tttLargeFiber4Block6Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1Row_11_ok :
    tttLargeFiber4Block6Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1Row_12_ok :
    tttLargeFiber4Block6Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1Row_13_ok :
    tttLargeFiber4Block6Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1Row_14_ok :
    tttLargeFiber4Block6Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1Row_15_ok :
    tttLargeFiber4Block6Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentMap_0_ok :
    tttLargeFiber4Block6Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentMap_1_ok :
    tttLargeFiber4Block6Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentMap_2_ok :
    tttLargeFiber4Block6Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentMap_3_ok :
    tttLargeFiber4Block6Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentMap_4_ok :
    tttLargeFiber4Block6Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentMap_5_ok :
    tttLargeFiber4Block6Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentMap_6_ok :
    tttLargeFiber4Block6Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentMap_7_ok :
    tttLargeFiber4Block6Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentMap_8_ok :
    tttLargeFiber4Block6Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentMap_9_ok :
    tttLargeFiber4Block6Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentMap_10_ok :
    tttLargeFiber4Block6Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentMap_11_ok :
    tttLargeFiber4Block6Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentMap_12_ok :
    tttLargeFiber4Block6Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentMap_13_ok :
    tttLargeFiber4Block6Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentMap_14_ok :
    tttLargeFiber4Block6Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentMap_15_ok :
    tttLargeFiber4Block6Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentPath_0_ok :
    tttLargeFiber4Block6Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentPath_1_ok :
    tttLargeFiber4Block6Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentPath_2_ok :
    tttLargeFiber4Block6Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentPath_3_ok :
    tttLargeFiber4Block6Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentPath_4_ok :
    tttLargeFiber4Block6Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentPath_5_ok :
    tttLargeFiber4Block6Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentPath_6_ok :
    tttLargeFiber4Block6Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentPath_7_ok :
    tttLargeFiber4Block6Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentPath_8_ok :
    tttLargeFiber4Block6Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentPath_9_ok :
    tttLargeFiber4Block6Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentPath_10_ok :
    tttLargeFiber4Block6Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentPath_11_ok :
    tttLargeFiber4Block6Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentPath_12_ok :
    tttLargeFiber4Block6Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentPath_13_ok :
    tttLargeFiber4Block6Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentPath_14_ok :
    tttLargeFiber4Block6Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block6Chunk1ParentPath_15_ok :
    tttLargeFiber4Block6Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block6Chunk1RowsAudit : Bool :=
  tttLargeFiber4Block6Chunk1RowCheck 0
    && tttLargeFiber4Block6Chunk1RowCheck 1
    && tttLargeFiber4Block6Chunk1RowCheck 2
    && tttLargeFiber4Block6Chunk1RowCheck 3
    && tttLargeFiber4Block6Chunk1RowCheck 4
    && tttLargeFiber4Block6Chunk1RowCheck 5
    && tttLargeFiber4Block6Chunk1RowCheck 6
    && tttLargeFiber4Block6Chunk1RowCheck 7
    && tttLargeFiber4Block6Chunk1RowCheck 8
    && tttLargeFiber4Block6Chunk1RowCheck 9
    && tttLargeFiber4Block6Chunk1RowCheck 10
    && tttLargeFiber4Block6Chunk1RowCheck 11
    && tttLargeFiber4Block6Chunk1RowCheck 12
    && tttLargeFiber4Block6Chunk1RowCheck 13
    && tttLargeFiber4Block6Chunk1RowCheck 14
    && tttLargeFiber4Block6Chunk1RowCheck 15

theorem tttLargeFiber4Block6Chunk1RowsAudit_ok :
    tttLargeFiber4Block6Chunk1RowsAudit = true := by
  simp [tttLargeFiber4Block6Chunk1RowsAudit,
    tttLargeFiber4Block6Chunk1Row_0_ok,
    tttLargeFiber4Block6Chunk1Row_1_ok,
    tttLargeFiber4Block6Chunk1Row_2_ok,
    tttLargeFiber4Block6Chunk1Row_3_ok,
    tttLargeFiber4Block6Chunk1Row_4_ok,
    tttLargeFiber4Block6Chunk1Row_5_ok,
    tttLargeFiber4Block6Chunk1Row_6_ok,
    tttLargeFiber4Block6Chunk1Row_7_ok,
    tttLargeFiber4Block6Chunk1Row_8_ok,
    tttLargeFiber4Block6Chunk1Row_9_ok,
    tttLargeFiber4Block6Chunk1Row_10_ok,
    tttLargeFiber4Block6Chunk1Row_11_ok,
    tttLargeFiber4Block6Chunk1Row_12_ok,
    tttLargeFiber4Block6Chunk1Row_13_ok,
    tttLargeFiber4Block6Chunk1Row_14_ok,
    tttLargeFiber4Block6Chunk1Row_15_ok]

def tttLargeFiber4Block6Chunk1ParentMapAudit : Bool :=
  tttLargeFiber4Block6Chunk1ParentMapCheck 0
    && tttLargeFiber4Block6Chunk1ParentMapCheck 1
    && tttLargeFiber4Block6Chunk1ParentMapCheck 2
    && tttLargeFiber4Block6Chunk1ParentMapCheck 3
    && tttLargeFiber4Block6Chunk1ParentMapCheck 4
    && tttLargeFiber4Block6Chunk1ParentMapCheck 5
    && tttLargeFiber4Block6Chunk1ParentMapCheck 6
    && tttLargeFiber4Block6Chunk1ParentMapCheck 7
    && tttLargeFiber4Block6Chunk1ParentMapCheck 8
    && tttLargeFiber4Block6Chunk1ParentMapCheck 9
    && tttLargeFiber4Block6Chunk1ParentMapCheck 10
    && tttLargeFiber4Block6Chunk1ParentMapCheck 11
    && tttLargeFiber4Block6Chunk1ParentMapCheck 12
    && tttLargeFiber4Block6Chunk1ParentMapCheck 13
    && tttLargeFiber4Block6Chunk1ParentMapCheck 14
    && tttLargeFiber4Block6Chunk1ParentMapCheck 15

theorem tttLargeFiber4Block6Chunk1ParentMapAudit_ok :
    tttLargeFiber4Block6Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber4Block6Chunk1ParentMapAudit,
    tttLargeFiber4Block6Chunk1ParentMap_0_ok,
    tttLargeFiber4Block6Chunk1ParentMap_1_ok,
    tttLargeFiber4Block6Chunk1ParentMap_2_ok,
    tttLargeFiber4Block6Chunk1ParentMap_3_ok,
    tttLargeFiber4Block6Chunk1ParentMap_4_ok,
    tttLargeFiber4Block6Chunk1ParentMap_5_ok,
    tttLargeFiber4Block6Chunk1ParentMap_6_ok,
    tttLargeFiber4Block6Chunk1ParentMap_7_ok,
    tttLargeFiber4Block6Chunk1ParentMap_8_ok,
    tttLargeFiber4Block6Chunk1ParentMap_9_ok,
    tttLargeFiber4Block6Chunk1ParentMap_10_ok,
    tttLargeFiber4Block6Chunk1ParentMap_11_ok,
    tttLargeFiber4Block6Chunk1ParentMap_12_ok,
    tttLargeFiber4Block6Chunk1ParentMap_13_ok,
    tttLargeFiber4Block6Chunk1ParentMap_14_ok,
    tttLargeFiber4Block6Chunk1ParentMap_15_ok]

def tttLargeFiber4Block6Chunk1ParentsAudit : Bool :=
  tttLargeFiber4Block6Chunk1ParentPathCheck 0
    && tttLargeFiber4Block6Chunk1ParentPathCheck 1
    && tttLargeFiber4Block6Chunk1ParentPathCheck 2
    && tttLargeFiber4Block6Chunk1ParentPathCheck 3
    && tttLargeFiber4Block6Chunk1ParentPathCheck 4
    && tttLargeFiber4Block6Chunk1ParentPathCheck 5
    && tttLargeFiber4Block6Chunk1ParentPathCheck 6
    && tttLargeFiber4Block6Chunk1ParentPathCheck 7
    && tttLargeFiber4Block6Chunk1ParentPathCheck 8
    && tttLargeFiber4Block6Chunk1ParentPathCheck 9
    && tttLargeFiber4Block6Chunk1ParentPathCheck 10
    && tttLargeFiber4Block6Chunk1ParentPathCheck 11
    && tttLargeFiber4Block6Chunk1ParentPathCheck 12
    && tttLargeFiber4Block6Chunk1ParentPathCheck 13
    && tttLargeFiber4Block6Chunk1ParentPathCheck 14
    && tttLargeFiber4Block6Chunk1ParentPathCheck 15

theorem tttLargeFiber4Block6Chunk1ParentsAudit_ok :
    tttLargeFiber4Block6Chunk1ParentsAudit = true := by
  simp [tttLargeFiber4Block6Chunk1ParentsAudit,
    tttLargeFiber4Block6Chunk1ParentPath_0_ok,
    tttLargeFiber4Block6Chunk1ParentPath_1_ok,
    tttLargeFiber4Block6Chunk1ParentPath_2_ok,
    tttLargeFiber4Block6Chunk1ParentPath_3_ok,
    tttLargeFiber4Block6Chunk1ParentPath_4_ok,
    tttLargeFiber4Block6Chunk1ParentPath_5_ok,
    tttLargeFiber4Block6Chunk1ParentPath_6_ok,
    tttLargeFiber4Block6Chunk1ParentPath_7_ok,
    tttLargeFiber4Block6Chunk1ParentPath_8_ok,
    tttLargeFiber4Block6Chunk1ParentPath_9_ok,
    tttLargeFiber4Block6Chunk1ParentPath_10_ok,
    tttLargeFiber4Block6Chunk1ParentPath_11_ok,
    tttLargeFiber4Block6Chunk1ParentPath_12_ok,
    tttLargeFiber4Block6Chunk1ParentPath_13_ok,
    tttLargeFiber4Block6Chunk1ParentPath_14_ok,
    tttLargeFiber4Block6Chunk1ParentPath_15_ok]

def tttLargeFiber4Block6Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block6Chunk1SourcesCheck &&
    tttLargeFiber4Block6Chunk1RowsAudit &&
    tttLargeFiber4Block6Chunk1ParentMapAudit &&
    tttLargeFiber4Block6Chunk1ParentsAudit

theorem tttLargeFiber4Block6Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber4Block6Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block6Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block6Chunk1SourcesCheck_ok,
    tttLargeFiber4Block6Chunk1RowsAudit_ok,
    tttLargeFiber4Block6Chunk1ParentMapAudit_ok,
    tttLargeFiber4Block6Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block6Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
