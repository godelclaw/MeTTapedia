import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 4 chunk 1

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
For second-range rows it uses interval membership and explicit bounded parent
paths, avoiding broad expected-list traversal and recursive parent iteration.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block4Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block4Chunk1Sources : List Nat :=
  [3840, 3841, 3842, 3843, 3844, 3845, 3846, 3847,
   3848, 3849, 3850, 3851, 3852, 3853, 3854, 3855]

def tttLargeFiber4Row272 : TripleComponentParentRow :=
  tripleRow 3840 2352 116 134 0 66 34 0
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber4Row273 : TripleComponentParentRow :=
  tripleRow 3841 2353 116 134 1 66 34 1
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber4Row274 : TripleComponentParentRow :=
  tripleRow 3842 2354 116 134 2 66 34 2
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber4Row275 : TripleComponentParentRow :=
  tripleRow 3843 2355 116 134 3 66 34 3
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber4Row276 : TripleComponentParentRow :=
  tripleRow 3844 2356 116 134 48 66 34 48
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber4Row277 : TripleComponentParentRow :=
  tripleRow 3845 2357 116 134 49 66 34 49
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber4Row278 : TripleComponentParentRow :=
  tripleRow 3846 2358 116 134 50 66 34 50
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber4Row279 : TripleComponentParentRow :=
  tripleRow 3847 2359 116 134 51 66 34 51
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber4Row280 : TripleComponentParentRow :=
  tripleRow 3848 2360 116 135 8 66 35 8
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber4Row281 : TripleComponentParentRow :=
  tripleRow 3849 2361 116 135 9 66 35 9
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber4Row282 : TripleComponentParentRow :=
  tripleRow 3850 2362 116 135 10 66 35 10
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber4Row283 : TripleComponentParentRow :=
  tripleRow 3851 2363 116 135 11 66 35 11
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber4Row284 : TripleComponentParentRow :=
  tripleRow 3852 2364 116 135 56 66 35 56
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber4Row285 : TripleComponentParentRow :=
  tripleRow 3853 2365 116 135 57 66 35 57
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber4Row286 : TripleComponentParentRow :=
  tripleRow 3854 2366 116 135 58 66 35 58
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber4Row287 : TripleComponentParentRow :=
  tripleRow 3855 2367 116 135 59 66 35 59
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F3
    ]

def tttLargeFiber4Block4Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row272
  , tttLargeFiber4Row273
  , tttLargeFiber4Row274
  , tttLargeFiber4Row275
  , tttLargeFiber4Row276
  , tttLargeFiber4Row277
  , tttLargeFiber4Row278
  , tttLargeFiber4Row279
  , tttLargeFiber4Row280
  , tttLargeFiber4Row281
  , tttLargeFiber4Row282
  , tttLargeFiber4Row283
  , tttLargeFiber4Row284
  , tttLargeFiber4Row285
  , tttLargeFiber4Row286
  , tttLargeFiber4Row287
  ]

def tttLargeFiber4Block4Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (2176 <= i) && decide (i < 2432)) ||
    (decide (3824 <= i) && decide (i < 4080))

def tttLargeFiber4Block4Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber4Block4Chunk1ExpectedContains row.source &&
    tttLargeFiber4Block4Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber4Key &&
          chainInputKey tttWord t == tttLargeFiber4Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber4Block4Chunk1SourcesCheck : Bool :=
  (tttLargeFiber4Block4Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber4Block4Chunk1Sources

theorem tttLargeFiber4Block4Chunk1SourcesCheck_ok :
    tttLargeFiber4Block4Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber4Block4Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber4Block4Chunk1RowValid
    (listGetD tttLargeFiber4Block4Chunk1Rows i default)

def tttLargeFiber4Block4Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block4Chunk1Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block4Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block4Chunk1Sources 0 0 == 3840 &&
      tttLargeFiber4ParentOf 3840 == 2352 &&
      tttLargeFiber4ParentOf 2352 == 2224 &&
      tttLargeFiber4ParentOf 2224 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block4Chunk1Sources 1 0 == 3841 &&
      tttLargeFiber4ParentOf 3841 == 2353 &&
      tttLargeFiber4ParentOf 2353 == 2225 &&
      tttLargeFiber4ParentOf 2225 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block4Chunk1Sources 2 0 == 3842 &&
      tttLargeFiber4ParentOf 3842 == 2354 &&
      tttLargeFiber4ParentOf 2354 == 2226 &&
      tttLargeFiber4ParentOf 2226 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block4Chunk1Sources 3 0 == 3843 &&
      tttLargeFiber4ParentOf 3843 == 2355 &&
      tttLargeFiber4ParentOf 2355 == 2227 &&
      tttLargeFiber4ParentOf 2227 == 2187 &&
      tttLargeFiber4ParentOf 2187 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block4Chunk1Sources 4 0 == 3844 &&
      tttLargeFiber4ParentOf 3844 == 2356 &&
      tttLargeFiber4ParentOf 2356 == 2352 &&
      tttLargeFiber4ParentOf 2352 == 2224 &&
      tttLargeFiber4ParentOf 2224 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block4Chunk1Sources 5 0 == 3845 &&
      tttLargeFiber4ParentOf 3845 == 2357 &&
      tttLargeFiber4ParentOf 2357 == 2353 &&
      tttLargeFiber4ParentOf 2353 == 2225 &&
      tttLargeFiber4ParentOf 2225 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block4Chunk1Sources 6 0 == 3846 &&
      tttLargeFiber4ParentOf 3846 == 2358 &&
      tttLargeFiber4ParentOf 2358 == 2230 &&
      tttLargeFiber4ParentOf 2230 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block4Chunk1Sources 7 0 == 3847 &&
      tttLargeFiber4ParentOf 3847 == 2359 &&
      tttLargeFiber4ParentOf 2359 == 2231 &&
      tttLargeFiber4ParentOf 2231 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block4Chunk1Sources 8 0 == 3848 &&
      tttLargeFiber4ParentOf 3848 == 2360 &&
      tttLargeFiber4ParentOf 2360 == 2232 &&
      tttLargeFiber4ParentOf 2232 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block4Chunk1Sources 9 0 == 3849 &&
      tttLargeFiber4ParentOf 3849 == 2361 &&
      tttLargeFiber4ParentOf 2361 == 2233 &&
      tttLargeFiber4ParentOf 2233 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block4Chunk1Sources 10 0 == 3850 &&
      tttLargeFiber4ParentOf 3850 == 2362 &&
      tttLargeFiber4ParentOf 2362 == 2234 &&
      tttLargeFiber4ParentOf 2234 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block4Chunk1Sources 11 0 == 3851 &&
      tttLargeFiber4ParentOf 3851 == 2363 &&
      tttLargeFiber4ParentOf 2363 == 2235 &&
      tttLargeFiber4ParentOf 2235 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block4Chunk1Sources 12 0 == 3852 &&
      tttLargeFiber4ParentOf 3852 == 2364 &&
      tttLargeFiber4ParentOf 2364 == 2360 &&
      tttLargeFiber4ParentOf 2360 == 2232 &&
      tttLargeFiber4ParentOf 2232 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block4Chunk1Sources 13 0 == 3853 &&
      tttLargeFiber4ParentOf 3853 == 2365 &&
      tttLargeFiber4ParentOf 2365 == 2361 &&
      tttLargeFiber4ParentOf 2361 == 2233 &&
      tttLargeFiber4ParentOf 2233 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block4Chunk1Sources 14 0 == 3854 &&
      tttLargeFiber4ParentOf 3854 == 2366 &&
      tttLargeFiber4ParentOf 2366 == 2238 &&
      tttLargeFiber4ParentOf 2238 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block4Chunk1Sources 15 0 == 3855 &&
      tttLargeFiber4ParentOf 3855 == 2367 &&
      tttLargeFiber4ParentOf 2367 == 2239 &&
      tttLargeFiber4ParentOf 2239 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block4Chunk1Row_0_ok :
    tttLargeFiber4Block4Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1Row_1_ok :
    tttLargeFiber4Block4Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1Row_2_ok :
    tttLargeFiber4Block4Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1Row_3_ok :
    tttLargeFiber4Block4Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1Row_4_ok :
    tttLargeFiber4Block4Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1Row_5_ok :
    tttLargeFiber4Block4Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1Row_6_ok :
    tttLargeFiber4Block4Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1Row_7_ok :
    tttLargeFiber4Block4Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1Row_8_ok :
    tttLargeFiber4Block4Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1Row_9_ok :
    tttLargeFiber4Block4Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1Row_10_ok :
    tttLargeFiber4Block4Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1Row_11_ok :
    tttLargeFiber4Block4Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1Row_12_ok :
    tttLargeFiber4Block4Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1Row_13_ok :
    tttLargeFiber4Block4Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1Row_14_ok :
    tttLargeFiber4Block4Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1Row_15_ok :
    tttLargeFiber4Block4Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentMap_0_ok :
    tttLargeFiber4Block4Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentMap_1_ok :
    tttLargeFiber4Block4Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentMap_2_ok :
    tttLargeFiber4Block4Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentMap_3_ok :
    tttLargeFiber4Block4Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentMap_4_ok :
    tttLargeFiber4Block4Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentMap_5_ok :
    tttLargeFiber4Block4Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentMap_6_ok :
    tttLargeFiber4Block4Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentMap_7_ok :
    tttLargeFiber4Block4Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentMap_8_ok :
    tttLargeFiber4Block4Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentMap_9_ok :
    tttLargeFiber4Block4Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentMap_10_ok :
    tttLargeFiber4Block4Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentMap_11_ok :
    tttLargeFiber4Block4Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentMap_12_ok :
    tttLargeFiber4Block4Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentMap_13_ok :
    tttLargeFiber4Block4Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentMap_14_ok :
    tttLargeFiber4Block4Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentMap_15_ok :
    tttLargeFiber4Block4Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentPath_0_ok :
    tttLargeFiber4Block4Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentPath_1_ok :
    tttLargeFiber4Block4Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentPath_2_ok :
    tttLargeFiber4Block4Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentPath_3_ok :
    tttLargeFiber4Block4Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentPath_4_ok :
    tttLargeFiber4Block4Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentPath_5_ok :
    tttLargeFiber4Block4Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentPath_6_ok :
    tttLargeFiber4Block4Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentPath_7_ok :
    tttLargeFiber4Block4Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentPath_8_ok :
    tttLargeFiber4Block4Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentPath_9_ok :
    tttLargeFiber4Block4Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentPath_10_ok :
    tttLargeFiber4Block4Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentPath_11_ok :
    tttLargeFiber4Block4Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentPath_12_ok :
    tttLargeFiber4Block4Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentPath_13_ok :
    tttLargeFiber4Block4Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentPath_14_ok :
    tttLargeFiber4Block4Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block4Chunk1ParentPath_15_ok :
    tttLargeFiber4Block4Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block4Chunk1RowsAudit : Bool :=
  tttLargeFiber4Block4Chunk1RowCheck 0
    && tttLargeFiber4Block4Chunk1RowCheck 1
    && tttLargeFiber4Block4Chunk1RowCheck 2
    && tttLargeFiber4Block4Chunk1RowCheck 3
    && tttLargeFiber4Block4Chunk1RowCheck 4
    && tttLargeFiber4Block4Chunk1RowCheck 5
    && tttLargeFiber4Block4Chunk1RowCheck 6
    && tttLargeFiber4Block4Chunk1RowCheck 7
    && tttLargeFiber4Block4Chunk1RowCheck 8
    && tttLargeFiber4Block4Chunk1RowCheck 9
    && tttLargeFiber4Block4Chunk1RowCheck 10
    && tttLargeFiber4Block4Chunk1RowCheck 11
    && tttLargeFiber4Block4Chunk1RowCheck 12
    && tttLargeFiber4Block4Chunk1RowCheck 13
    && tttLargeFiber4Block4Chunk1RowCheck 14
    && tttLargeFiber4Block4Chunk1RowCheck 15

theorem tttLargeFiber4Block4Chunk1RowsAudit_ok :
    tttLargeFiber4Block4Chunk1RowsAudit = true := by
  simp [tttLargeFiber4Block4Chunk1RowsAudit,
    tttLargeFiber4Block4Chunk1Row_0_ok,
    tttLargeFiber4Block4Chunk1Row_1_ok,
    tttLargeFiber4Block4Chunk1Row_2_ok,
    tttLargeFiber4Block4Chunk1Row_3_ok,
    tttLargeFiber4Block4Chunk1Row_4_ok,
    tttLargeFiber4Block4Chunk1Row_5_ok,
    tttLargeFiber4Block4Chunk1Row_6_ok,
    tttLargeFiber4Block4Chunk1Row_7_ok,
    tttLargeFiber4Block4Chunk1Row_8_ok,
    tttLargeFiber4Block4Chunk1Row_9_ok,
    tttLargeFiber4Block4Chunk1Row_10_ok,
    tttLargeFiber4Block4Chunk1Row_11_ok,
    tttLargeFiber4Block4Chunk1Row_12_ok,
    tttLargeFiber4Block4Chunk1Row_13_ok,
    tttLargeFiber4Block4Chunk1Row_14_ok,
    tttLargeFiber4Block4Chunk1Row_15_ok]

def tttLargeFiber4Block4Chunk1ParentMapAudit : Bool :=
  tttLargeFiber4Block4Chunk1ParentMapCheck 0
    && tttLargeFiber4Block4Chunk1ParentMapCheck 1
    && tttLargeFiber4Block4Chunk1ParentMapCheck 2
    && tttLargeFiber4Block4Chunk1ParentMapCheck 3
    && tttLargeFiber4Block4Chunk1ParentMapCheck 4
    && tttLargeFiber4Block4Chunk1ParentMapCheck 5
    && tttLargeFiber4Block4Chunk1ParentMapCheck 6
    && tttLargeFiber4Block4Chunk1ParentMapCheck 7
    && tttLargeFiber4Block4Chunk1ParentMapCheck 8
    && tttLargeFiber4Block4Chunk1ParentMapCheck 9
    && tttLargeFiber4Block4Chunk1ParentMapCheck 10
    && tttLargeFiber4Block4Chunk1ParentMapCheck 11
    && tttLargeFiber4Block4Chunk1ParentMapCheck 12
    && tttLargeFiber4Block4Chunk1ParentMapCheck 13
    && tttLargeFiber4Block4Chunk1ParentMapCheck 14
    && tttLargeFiber4Block4Chunk1ParentMapCheck 15

theorem tttLargeFiber4Block4Chunk1ParentMapAudit_ok :
    tttLargeFiber4Block4Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber4Block4Chunk1ParentMapAudit,
    tttLargeFiber4Block4Chunk1ParentMap_0_ok,
    tttLargeFiber4Block4Chunk1ParentMap_1_ok,
    tttLargeFiber4Block4Chunk1ParentMap_2_ok,
    tttLargeFiber4Block4Chunk1ParentMap_3_ok,
    tttLargeFiber4Block4Chunk1ParentMap_4_ok,
    tttLargeFiber4Block4Chunk1ParentMap_5_ok,
    tttLargeFiber4Block4Chunk1ParentMap_6_ok,
    tttLargeFiber4Block4Chunk1ParentMap_7_ok,
    tttLargeFiber4Block4Chunk1ParentMap_8_ok,
    tttLargeFiber4Block4Chunk1ParentMap_9_ok,
    tttLargeFiber4Block4Chunk1ParentMap_10_ok,
    tttLargeFiber4Block4Chunk1ParentMap_11_ok,
    tttLargeFiber4Block4Chunk1ParentMap_12_ok,
    tttLargeFiber4Block4Chunk1ParentMap_13_ok,
    tttLargeFiber4Block4Chunk1ParentMap_14_ok,
    tttLargeFiber4Block4Chunk1ParentMap_15_ok]

def tttLargeFiber4Block4Chunk1ParentsAudit : Bool :=
  tttLargeFiber4Block4Chunk1ParentPathCheck 0
    && tttLargeFiber4Block4Chunk1ParentPathCheck 1
    && tttLargeFiber4Block4Chunk1ParentPathCheck 2
    && tttLargeFiber4Block4Chunk1ParentPathCheck 3
    && tttLargeFiber4Block4Chunk1ParentPathCheck 4
    && tttLargeFiber4Block4Chunk1ParentPathCheck 5
    && tttLargeFiber4Block4Chunk1ParentPathCheck 6
    && tttLargeFiber4Block4Chunk1ParentPathCheck 7
    && tttLargeFiber4Block4Chunk1ParentPathCheck 8
    && tttLargeFiber4Block4Chunk1ParentPathCheck 9
    && tttLargeFiber4Block4Chunk1ParentPathCheck 10
    && tttLargeFiber4Block4Chunk1ParentPathCheck 11
    && tttLargeFiber4Block4Chunk1ParentPathCheck 12
    && tttLargeFiber4Block4Chunk1ParentPathCheck 13
    && tttLargeFiber4Block4Chunk1ParentPathCheck 14
    && tttLargeFiber4Block4Chunk1ParentPathCheck 15

theorem tttLargeFiber4Block4Chunk1ParentsAudit_ok :
    tttLargeFiber4Block4Chunk1ParentsAudit = true := by
  simp [tttLargeFiber4Block4Chunk1ParentsAudit,
    tttLargeFiber4Block4Chunk1ParentPath_0_ok,
    tttLargeFiber4Block4Chunk1ParentPath_1_ok,
    tttLargeFiber4Block4Chunk1ParentPath_2_ok,
    tttLargeFiber4Block4Chunk1ParentPath_3_ok,
    tttLargeFiber4Block4Chunk1ParentPath_4_ok,
    tttLargeFiber4Block4Chunk1ParentPath_5_ok,
    tttLargeFiber4Block4Chunk1ParentPath_6_ok,
    tttLargeFiber4Block4Chunk1ParentPath_7_ok,
    tttLargeFiber4Block4Chunk1ParentPath_8_ok,
    tttLargeFiber4Block4Chunk1ParentPath_9_ok,
    tttLargeFiber4Block4Chunk1ParentPath_10_ok,
    tttLargeFiber4Block4Chunk1ParentPath_11_ok,
    tttLargeFiber4Block4Chunk1ParentPath_12_ok,
    tttLargeFiber4Block4Chunk1ParentPath_13_ok,
    tttLargeFiber4Block4Chunk1ParentPath_14_ok,
    tttLargeFiber4Block4Chunk1ParentPath_15_ok]

def tttLargeFiber4Block4Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block4Chunk1SourcesCheck &&
    tttLargeFiber4Block4Chunk1RowsAudit &&
    tttLargeFiber4Block4Chunk1ParentMapAudit &&
    tttLargeFiber4Block4Chunk1ParentsAudit

theorem tttLargeFiber4Block4Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber4Block4Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block4Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block4Chunk1SourcesCheck_ok,
    tttLargeFiber4Block4Chunk1RowsAudit_ok,
    tttLargeFiber4Block4Chunk1ParentMapAudit_ok,
    tttLargeFiber4Block4Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block4Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
