import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 6 chunk 3

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
For second-range rows it uses interval membership and explicit bounded parent
paths, avoiding broad expected-list traversal and recursive parent iteration.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block6Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block6Chunk3Sources : List Nat :=
  [4000, 4001, 4002, 4003, 4004, 4005, 4006, 4007,
   4008, 4009, 4010, 4011, 4012, 4013, 4014, 4015]

def tttLargeFiber4Row432 : TripleComponentParentRow :=
  tripleRow 4000 2288 118 118 64 65 110 64
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row433 : TripleComponentParentRow :=
  tripleRow 4001 2289 118 118 65 65 110 65
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row434 : TripleComponentParentRow :=
  tripleRow 4002 2290 118 118 66 65 110 66
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row435 : TripleComponentParentRow :=
  tripleRow 4003 2291 118 118 67 65 110 67
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row436 : TripleComponentParentRow :=
  tripleRow 4004 2292 118 118 116 65 110 116
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row437 : TripleComponentParentRow :=
  tripleRow 4005 2293 118 118 117 65 110 117
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row438 : TripleComponentParentRow :=
  tripleRow 4006 2294 118 118 118 65 110 118
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row439 : TripleComponentParentRow :=
  tripleRow 4007 2295 118 118 119 65 110 119
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row440 : TripleComponentParentRow :=
  tripleRow 4008 2296 118 119 72 65 111 72
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row441 : TripleComponentParentRow :=
  tripleRow 4009 2297 118 119 73 65 111 73
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row442 : TripleComponentParentRow :=
  tripleRow 4010 2298 118 119 74 65 111 74
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row443 : TripleComponentParentRow :=
  tripleRow 4011 2299 118 119 75 65 111 75
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row444 : TripleComponentParentRow :=
  tripleRow 4012 2300 118 119 124 65 111 124
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row445 : TripleComponentParentRow :=
  tripleRow 4013 2301 118 119 125 65 111 125
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row446 : TripleComponentParentRow :=
  tripleRow 4014 2302 118 119 126 65 111 126
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Row447 : TripleComponentParentRow :=
  tripleRow 4015 2303 118 119 127 65 111 127
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B5
    ]

def tttLargeFiber4Block6Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row432
  , tttLargeFiber4Row433
  , tttLargeFiber4Row434
  , tttLargeFiber4Row435
  , tttLargeFiber4Row436
  , tttLargeFiber4Row437
  , tttLargeFiber4Row438
  , tttLargeFiber4Row439
  , tttLargeFiber4Row440
  , tttLargeFiber4Row441
  , tttLargeFiber4Row442
  , tttLargeFiber4Row443
  , tttLargeFiber4Row444
  , tttLargeFiber4Row445
  , tttLargeFiber4Row446
  , tttLargeFiber4Row447
  ]

def tttLargeFiber4Block6Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (2176 <= i) && decide (i < 2432)) ||
    (decide (3824 <= i) && decide (i < 4080))

def tttLargeFiber4Block6Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber4Block6Chunk3ExpectedContains row.source &&
    tttLargeFiber4Block6Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber4Key &&
          chainInputKey tttWord t == tttLargeFiber4Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber4Block6Chunk3SourcesCheck : Bool :=
  (tttLargeFiber4Block6Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber4Block6Chunk3Sources

theorem tttLargeFiber4Block6Chunk3SourcesCheck_ok :
    tttLargeFiber4Block6Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber4Block6Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber4Block6Chunk3RowValid
    (listGetD tttLargeFiber4Block6Chunk3Rows i default)

def tttLargeFiber4Block6Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block6Chunk3Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block6Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block6Chunk3Sources 0 0 == 4000 &&
      tttLargeFiber4ParentOf 4000 == 2288 &&
      tttLargeFiber4ParentOf 2288 == 2224 &&
      tttLargeFiber4ParentOf 2224 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block6Chunk3Sources 1 0 == 4001 &&
      tttLargeFiber4ParentOf 4001 == 2289 &&
      tttLargeFiber4ParentOf 2289 == 2225 &&
      tttLargeFiber4ParentOf 2225 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block6Chunk3Sources 2 0 == 4002 &&
      tttLargeFiber4ParentOf 4002 == 2290 &&
      tttLargeFiber4ParentOf 2290 == 2226 &&
      tttLargeFiber4ParentOf 2226 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block6Chunk3Sources 3 0 == 4003 &&
      tttLargeFiber4ParentOf 4003 == 2291 &&
      tttLargeFiber4ParentOf 2291 == 2227 &&
      tttLargeFiber4ParentOf 2227 == 2187 &&
      tttLargeFiber4ParentOf 2187 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block6Chunk3Sources 4 0 == 4004 &&
      tttLargeFiber4ParentOf 4004 == 2292 &&
      tttLargeFiber4ParentOf 2292 == 2228 &&
      tttLargeFiber4ParentOf 2228 == 2188 &&
      tttLargeFiber4ParentOf 2188 == 2180 &&
      tttLargeFiber4ParentOf 2180 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block6Chunk3Sources 5 0 == 4005 &&
      tttLargeFiber4ParentOf 4005 == 2293 &&
      tttLargeFiber4ParentOf 2293 == 2229 &&
      tttLargeFiber4ParentOf 2229 == 2189 &&
      tttLargeFiber4ParentOf 2189 == 2181 &&
      tttLargeFiber4ParentOf 2181 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block6Chunk3Sources 6 0 == 4006 &&
      tttLargeFiber4ParentOf 4006 == 2294 &&
      tttLargeFiber4ParentOf 2294 == 2230 &&
      tttLargeFiber4ParentOf 2230 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block6Chunk3Sources 7 0 == 4007 &&
      tttLargeFiber4ParentOf 4007 == 2295 &&
      tttLargeFiber4ParentOf 2295 == 2231 &&
      tttLargeFiber4ParentOf 2231 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block6Chunk3Sources 8 0 == 4008 &&
      tttLargeFiber4ParentOf 4008 == 2296 &&
      tttLargeFiber4ParentOf 2296 == 2232 &&
      tttLargeFiber4ParentOf 2232 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block6Chunk3Sources 9 0 == 4009 &&
      tttLargeFiber4ParentOf 4009 == 2297 &&
      tttLargeFiber4ParentOf 2297 == 2233 &&
      tttLargeFiber4ParentOf 2233 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block6Chunk3Sources 10 0 == 4010 &&
      tttLargeFiber4ParentOf 4010 == 2298 &&
      tttLargeFiber4ParentOf 2298 == 2234 &&
      tttLargeFiber4ParentOf 2234 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block6Chunk3Sources 11 0 == 4011 &&
      tttLargeFiber4ParentOf 4011 == 2299 &&
      tttLargeFiber4ParentOf 2299 == 2235 &&
      tttLargeFiber4ParentOf 2235 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block6Chunk3Sources 12 0 == 4012 &&
      tttLargeFiber4ParentOf 4012 == 2300 &&
      tttLargeFiber4ParentOf 2300 == 2236 &&
      tttLargeFiber4ParentOf 2236 == 2180 &&
      tttLargeFiber4ParentOf 2180 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block6Chunk3Sources 13 0 == 4013 &&
      tttLargeFiber4ParentOf 4013 == 2301 &&
      tttLargeFiber4ParentOf 2301 == 2237 &&
      tttLargeFiber4ParentOf 2237 == 2181 &&
      tttLargeFiber4ParentOf 2181 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block6Chunk3Sources 14 0 == 4014 &&
      tttLargeFiber4ParentOf 4014 == 2302 &&
      tttLargeFiber4ParentOf 2302 == 2238 &&
      tttLargeFiber4ParentOf 2238 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block6Chunk3Sources 15 0 == 4015 &&
      tttLargeFiber4ParentOf 4015 == 2303 &&
      tttLargeFiber4ParentOf 2303 == 2239 &&
      tttLargeFiber4ParentOf 2239 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block6Chunk3Row_0_ok :
    tttLargeFiber4Block6Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3Row_1_ok :
    tttLargeFiber4Block6Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3Row_2_ok :
    tttLargeFiber4Block6Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3Row_3_ok :
    tttLargeFiber4Block6Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3Row_4_ok :
    tttLargeFiber4Block6Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3Row_5_ok :
    tttLargeFiber4Block6Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3Row_6_ok :
    tttLargeFiber4Block6Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3Row_7_ok :
    tttLargeFiber4Block6Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3Row_8_ok :
    tttLargeFiber4Block6Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3Row_9_ok :
    tttLargeFiber4Block6Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3Row_10_ok :
    tttLargeFiber4Block6Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3Row_11_ok :
    tttLargeFiber4Block6Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3Row_12_ok :
    tttLargeFiber4Block6Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3Row_13_ok :
    tttLargeFiber4Block6Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3Row_14_ok :
    tttLargeFiber4Block6Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3Row_15_ok :
    tttLargeFiber4Block6Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentMap_0_ok :
    tttLargeFiber4Block6Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentMap_1_ok :
    tttLargeFiber4Block6Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentMap_2_ok :
    tttLargeFiber4Block6Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentMap_3_ok :
    tttLargeFiber4Block6Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentMap_4_ok :
    tttLargeFiber4Block6Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentMap_5_ok :
    tttLargeFiber4Block6Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentMap_6_ok :
    tttLargeFiber4Block6Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentMap_7_ok :
    tttLargeFiber4Block6Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentMap_8_ok :
    tttLargeFiber4Block6Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentMap_9_ok :
    tttLargeFiber4Block6Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentMap_10_ok :
    tttLargeFiber4Block6Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentMap_11_ok :
    tttLargeFiber4Block6Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentMap_12_ok :
    tttLargeFiber4Block6Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentMap_13_ok :
    tttLargeFiber4Block6Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentMap_14_ok :
    tttLargeFiber4Block6Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentMap_15_ok :
    tttLargeFiber4Block6Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentPath_0_ok :
    tttLargeFiber4Block6Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentPath_1_ok :
    tttLargeFiber4Block6Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentPath_2_ok :
    tttLargeFiber4Block6Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentPath_3_ok :
    tttLargeFiber4Block6Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentPath_4_ok :
    tttLargeFiber4Block6Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentPath_5_ok :
    tttLargeFiber4Block6Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentPath_6_ok :
    tttLargeFiber4Block6Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentPath_7_ok :
    tttLargeFiber4Block6Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentPath_8_ok :
    tttLargeFiber4Block6Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentPath_9_ok :
    tttLargeFiber4Block6Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentPath_10_ok :
    tttLargeFiber4Block6Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentPath_11_ok :
    tttLargeFiber4Block6Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentPath_12_ok :
    tttLargeFiber4Block6Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentPath_13_ok :
    tttLargeFiber4Block6Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentPath_14_ok :
    tttLargeFiber4Block6Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block6Chunk3ParentPath_15_ok :
    tttLargeFiber4Block6Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block6Chunk3RowsAudit : Bool :=
  tttLargeFiber4Block6Chunk3RowCheck 0
    && tttLargeFiber4Block6Chunk3RowCheck 1
    && tttLargeFiber4Block6Chunk3RowCheck 2
    && tttLargeFiber4Block6Chunk3RowCheck 3
    && tttLargeFiber4Block6Chunk3RowCheck 4
    && tttLargeFiber4Block6Chunk3RowCheck 5
    && tttLargeFiber4Block6Chunk3RowCheck 6
    && tttLargeFiber4Block6Chunk3RowCheck 7
    && tttLargeFiber4Block6Chunk3RowCheck 8
    && tttLargeFiber4Block6Chunk3RowCheck 9
    && tttLargeFiber4Block6Chunk3RowCheck 10
    && tttLargeFiber4Block6Chunk3RowCheck 11
    && tttLargeFiber4Block6Chunk3RowCheck 12
    && tttLargeFiber4Block6Chunk3RowCheck 13
    && tttLargeFiber4Block6Chunk3RowCheck 14
    && tttLargeFiber4Block6Chunk3RowCheck 15

theorem tttLargeFiber4Block6Chunk3RowsAudit_ok :
    tttLargeFiber4Block6Chunk3RowsAudit = true := by
  simp [tttLargeFiber4Block6Chunk3RowsAudit,
    tttLargeFiber4Block6Chunk3Row_0_ok,
    tttLargeFiber4Block6Chunk3Row_1_ok,
    tttLargeFiber4Block6Chunk3Row_2_ok,
    tttLargeFiber4Block6Chunk3Row_3_ok,
    tttLargeFiber4Block6Chunk3Row_4_ok,
    tttLargeFiber4Block6Chunk3Row_5_ok,
    tttLargeFiber4Block6Chunk3Row_6_ok,
    tttLargeFiber4Block6Chunk3Row_7_ok,
    tttLargeFiber4Block6Chunk3Row_8_ok,
    tttLargeFiber4Block6Chunk3Row_9_ok,
    tttLargeFiber4Block6Chunk3Row_10_ok,
    tttLargeFiber4Block6Chunk3Row_11_ok,
    tttLargeFiber4Block6Chunk3Row_12_ok,
    tttLargeFiber4Block6Chunk3Row_13_ok,
    tttLargeFiber4Block6Chunk3Row_14_ok,
    tttLargeFiber4Block6Chunk3Row_15_ok]

def tttLargeFiber4Block6Chunk3ParentMapAudit : Bool :=
  tttLargeFiber4Block6Chunk3ParentMapCheck 0
    && tttLargeFiber4Block6Chunk3ParentMapCheck 1
    && tttLargeFiber4Block6Chunk3ParentMapCheck 2
    && tttLargeFiber4Block6Chunk3ParentMapCheck 3
    && tttLargeFiber4Block6Chunk3ParentMapCheck 4
    && tttLargeFiber4Block6Chunk3ParentMapCheck 5
    && tttLargeFiber4Block6Chunk3ParentMapCheck 6
    && tttLargeFiber4Block6Chunk3ParentMapCheck 7
    && tttLargeFiber4Block6Chunk3ParentMapCheck 8
    && tttLargeFiber4Block6Chunk3ParentMapCheck 9
    && tttLargeFiber4Block6Chunk3ParentMapCheck 10
    && tttLargeFiber4Block6Chunk3ParentMapCheck 11
    && tttLargeFiber4Block6Chunk3ParentMapCheck 12
    && tttLargeFiber4Block6Chunk3ParentMapCheck 13
    && tttLargeFiber4Block6Chunk3ParentMapCheck 14
    && tttLargeFiber4Block6Chunk3ParentMapCheck 15

theorem tttLargeFiber4Block6Chunk3ParentMapAudit_ok :
    tttLargeFiber4Block6Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber4Block6Chunk3ParentMapAudit,
    tttLargeFiber4Block6Chunk3ParentMap_0_ok,
    tttLargeFiber4Block6Chunk3ParentMap_1_ok,
    tttLargeFiber4Block6Chunk3ParentMap_2_ok,
    tttLargeFiber4Block6Chunk3ParentMap_3_ok,
    tttLargeFiber4Block6Chunk3ParentMap_4_ok,
    tttLargeFiber4Block6Chunk3ParentMap_5_ok,
    tttLargeFiber4Block6Chunk3ParentMap_6_ok,
    tttLargeFiber4Block6Chunk3ParentMap_7_ok,
    tttLargeFiber4Block6Chunk3ParentMap_8_ok,
    tttLargeFiber4Block6Chunk3ParentMap_9_ok,
    tttLargeFiber4Block6Chunk3ParentMap_10_ok,
    tttLargeFiber4Block6Chunk3ParentMap_11_ok,
    tttLargeFiber4Block6Chunk3ParentMap_12_ok,
    tttLargeFiber4Block6Chunk3ParentMap_13_ok,
    tttLargeFiber4Block6Chunk3ParentMap_14_ok,
    tttLargeFiber4Block6Chunk3ParentMap_15_ok]

def tttLargeFiber4Block6Chunk3ParentsAudit : Bool :=
  tttLargeFiber4Block6Chunk3ParentPathCheck 0
    && tttLargeFiber4Block6Chunk3ParentPathCheck 1
    && tttLargeFiber4Block6Chunk3ParentPathCheck 2
    && tttLargeFiber4Block6Chunk3ParentPathCheck 3
    && tttLargeFiber4Block6Chunk3ParentPathCheck 4
    && tttLargeFiber4Block6Chunk3ParentPathCheck 5
    && tttLargeFiber4Block6Chunk3ParentPathCheck 6
    && tttLargeFiber4Block6Chunk3ParentPathCheck 7
    && tttLargeFiber4Block6Chunk3ParentPathCheck 8
    && tttLargeFiber4Block6Chunk3ParentPathCheck 9
    && tttLargeFiber4Block6Chunk3ParentPathCheck 10
    && tttLargeFiber4Block6Chunk3ParentPathCheck 11
    && tttLargeFiber4Block6Chunk3ParentPathCheck 12
    && tttLargeFiber4Block6Chunk3ParentPathCheck 13
    && tttLargeFiber4Block6Chunk3ParentPathCheck 14
    && tttLargeFiber4Block6Chunk3ParentPathCheck 15

theorem tttLargeFiber4Block6Chunk3ParentsAudit_ok :
    tttLargeFiber4Block6Chunk3ParentsAudit = true := by
  simp [tttLargeFiber4Block6Chunk3ParentsAudit,
    tttLargeFiber4Block6Chunk3ParentPath_0_ok,
    tttLargeFiber4Block6Chunk3ParentPath_1_ok,
    tttLargeFiber4Block6Chunk3ParentPath_2_ok,
    tttLargeFiber4Block6Chunk3ParentPath_3_ok,
    tttLargeFiber4Block6Chunk3ParentPath_4_ok,
    tttLargeFiber4Block6Chunk3ParentPath_5_ok,
    tttLargeFiber4Block6Chunk3ParentPath_6_ok,
    tttLargeFiber4Block6Chunk3ParentPath_7_ok,
    tttLargeFiber4Block6Chunk3ParentPath_8_ok,
    tttLargeFiber4Block6Chunk3ParentPath_9_ok,
    tttLargeFiber4Block6Chunk3ParentPath_10_ok,
    tttLargeFiber4Block6Chunk3ParentPath_11_ok,
    tttLargeFiber4Block6Chunk3ParentPath_12_ok,
    tttLargeFiber4Block6Chunk3ParentPath_13_ok,
    tttLargeFiber4Block6Chunk3ParentPath_14_ok,
    tttLargeFiber4Block6Chunk3ParentPath_15_ok]

def tttLargeFiber4Block6Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block6Chunk3SourcesCheck &&
    tttLargeFiber4Block6Chunk3RowsAudit &&
    tttLargeFiber4Block6Chunk3ParentMapAudit &&
    tttLargeFiber4Block6Chunk3ParentsAudit

theorem tttLargeFiber4Block6Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber4Block6Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block6Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block6Chunk3SourcesCheck_ok,
    tttLargeFiber4Block6Chunk3RowsAudit_ok,
    tttLargeFiber4Block6Chunk3ParentMapAudit_ok,
    tttLargeFiber4Block6Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block6Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
