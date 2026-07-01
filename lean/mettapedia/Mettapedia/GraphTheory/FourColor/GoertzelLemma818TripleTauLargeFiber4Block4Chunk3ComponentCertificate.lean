import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 4 chunk 3

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
For second-range rows it uses interval membership and explicit bounded parent
paths, avoiding broad expected-list traversal and recursive parent iteration.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block4Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block4Chunk3Sources : List Nat :=
  [3872, 3873, 3874, 3875, 3876, 3877, 3878, 3879,
   3880, 3881, 3882, 3883, 3884, 3885, 3886, 3887]

def tttLargeFiber4Row304 : TripleComponentParentRow :=
  tripleRow 3872 2312 116 182 64 66 17 88
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row305 : TripleComponentParentRow :=
  tripleRow 3873 2313 116 182 65 66 17 89
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row306 : TripleComponentParentRow :=
  tripleRow 3874 2314 116 182 66 66 17 90
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row307 : TripleComponentParentRow :=
  tripleRow 3875 2315 116 182 67 66 17 91
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row308 : TripleComponentParentRow :=
  tripleRow 3876 2316 116 182 116 66 17 108
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row309 : TripleComponentParentRow :=
  tripleRow 3877 2317 116 182 117 66 17 109
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row310 : TripleComponentParentRow :=
  tripleRow 3878 2318 116 182 118 66 17 110
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row311 : TripleComponentParentRow :=
  tripleRow 3879 2319 116 182 119 66 17 111
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row312 : TripleComponentParentRow :=
  tripleRow 3880 2304 116 183 72 66 16 80
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row313 : TripleComponentParentRow :=
  tripleRow 3881 2305 116 183 73 66 16 81
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row314 : TripleComponentParentRow :=
  tripleRow 3882 2306 116 183 74 66 16 82
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row315 : TripleComponentParentRow :=
  tripleRow 3883 2307 116 183 75 66 16 83
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row316 : TripleComponentParentRow :=
  tripleRow 3884 2308 116 183 124 66 16 100
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row317 : TripleComponentParentRow :=
  tripleRow 3885 2309 116 183 125 66 16 101
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row318 : TripleComponentParentRow :=
  tripleRow 3886 2310 116 183 126 66 16 102
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row319 : TripleComponentParentRow :=
  tripleRow 3887 2311 116 183 127 66 16 103
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Block4Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row304
  , tttLargeFiber4Row305
  , tttLargeFiber4Row306
  , tttLargeFiber4Row307
  , tttLargeFiber4Row308
  , tttLargeFiber4Row309
  , tttLargeFiber4Row310
  , tttLargeFiber4Row311
  , tttLargeFiber4Row312
  , tttLargeFiber4Row313
  , tttLargeFiber4Row314
  , tttLargeFiber4Row315
  , tttLargeFiber4Row316
  , tttLargeFiber4Row317
  , tttLargeFiber4Row318
  , tttLargeFiber4Row319
  ]

def tttLargeFiber4Block4Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (2176 <= i) && decide (i < 2432)) ||
    (decide (3824 <= i) && decide (i < 4080))

def tttLargeFiber4Block4Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber4Block4Chunk3ExpectedContains row.source &&
    tttLargeFiber4Block4Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber4Key &&
          chainInputKey tttWord t == tttLargeFiber4Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber4Block4Chunk3SourcesCheck : Bool :=
  (tttLargeFiber4Block4Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber4Block4Chunk3Sources

theorem tttLargeFiber4Block4Chunk3SourcesCheck_ok :
    tttLargeFiber4Block4Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber4Block4Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber4Block4Chunk3RowValid
    (listGetD tttLargeFiber4Block4Chunk3Rows i default)

def tttLargeFiber4Block4Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block4Chunk3Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block4Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block4Chunk3Sources 0 0 == 3872 &&
      tttLargeFiber4ParentOf 3872 == 2312 &&
      tttLargeFiber4ParentOf 2312 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block4Chunk3Sources 1 0 == 3873 &&
      tttLargeFiber4ParentOf 3873 == 2313 &&
      tttLargeFiber4ParentOf 2313 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block4Chunk3Sources 2 0 == 3874 &&
      tttLargeFiber4ParentOf 3874 == 2314 &&
      tttLargeFiber4ParentOf 2314 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block4Chunk3Sources 3 0 == 3875 &&
      tttLargeFiber4ParentOf 3875 == 2315 &&
      tttLargeFiber4ParentOf 2315 == 2187 &&
      tttLargeFiber4ParentOf 2187 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block4Chunk3Sources 4 0 == 3876 &&
      tttLargeFiber4ParentOf 3876 == 2316 &&
      tttLargeFiber4ParentOf 2316 == 2188 &&
      tttLargeFiber4ParentOf 2188 == 2180 &&
      tttLargeFiber4ParentOf 2180 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block4Chunk3Sources 5 0 == 3877 &&
      tttLargeFiber4ParentOf 3877 == 2317 &&
      tttLargeFiber4ParentOf 2317 == 2189 &&
      tttLargeFiber4ParentOf 2189 == 2181 &&
      tttLargeFiber4ParentOf 2181 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block4Chunk3Sources 6 0 == 3878 &&
      tttLargeFiber4ParentOf 3878 == 2318 &&
      tttLargeFiber4ParentOf 2318 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block4Chunk3Sources 7 0 == 3879 &&
      tttLargeFiber4ParentOf 3879 == 2319 &&
      tttLargeFiber4ParentOf 2319 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block4Chunk3Sources 8 0 == 3880 &&
      tttLargeFiber4ParentOf 3880 == 2304 &&
      tttLargeFiber4ParentOf 2304 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (2 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block4Chunk3Sources 9 0 == 3881 &&
      tttLargeFiber4ParentOf 3881 == 2305 &&
      tttLargeFiber4ParentOf 2305 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block4Chunk3Sources 10 0 == 3882 &&
      tttLargeFiber4ParentOf 3882 == 2306 &&
      tttLargeFiber4ParentOf 2306 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block4Chunk3Sources 11 0 == 3883 &&
      tttLargeFiber4ParentOf 3883 == 2307 &&
      tttLargeFiber4ParentOf 2307 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block4Chunk3Sources 12 0 == 3884 &&
      tttLargeFiber4ParentOf 3884 == 2308 &&
      tttLargeFiber4ParentOf 2308 == 2180 &&
      tttLargeFiber4ParentOf 2180 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block4Chunk3Sources 13 0 == 3885 &&
      tttLargeFiber4ParentOf 3885 == 2309 &&
      tttLargeFiber4ParentOf 2309 == 2181 &&
      tttLargeFiber4ParentOf 2181 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block4Chunk3Sources 14 0 == 3886 &&
      tttLargeFiber4ParentOf 3886 == 2310 &&
      tttLargeFiber4ParentOf 2310 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block4Chunk3Sources 15 0 == 3887 &&
      tttLargeFiber4ParentOf 3887 == 2311 &&
      tttLargeFiber4ParentOf 2311 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block4Chunk3Row_0_ok :
    tttLargeFiber4Block4Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3Row_1_ok :
    tttLargeFiber4Block4Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3Row_2_ok :
    tttLargeFiber4Block4Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3Row_3_ok :
    tttLargeFiber4Block4Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3Row_4_ok :
    tttLargeFiber4Block4Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3Row_5_ok :
    tttLargeFiber4Block4Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3Row_6_ok :
    tttLargeFiber4Block4Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3Row_7_ok :
    tttLargeFiber4Block4Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3Row_8_ok :
    tttLargeFiber4Block4Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3Row_9_ok :
    tttLargeFiber4Block4Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3Row_10_ok :
    tttLargeFiber4Block4Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3Row_11_ok :
    tttLargeFiber4Block4Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3Row_12_ok :
    tttLargeFiber4Block4Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3Row_13_ok :
    tttLargeFiber4Block4Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3Row_14_ok :
    tttLargeFiber4Block4Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3Row_15_ok :
    tttLargeFiber4Block4Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentMap_0_ok :
    tttLargeFiber4Block4Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentMap_1_ok :
    tttLargeFiber4Block4Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentMap_2_ok :
    tttLargeFiber4Block4Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentMap_3_ok :
    tttLargeFiber4Block4Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentMap_4_ok :
    tttLargeFiber4Block4Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentMap_5_ok :
    tttLargeFiber4Block4Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentMap_6_ok :
    tttLargeFiber4Block4Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentMap_7_ok :
    tttLargeFiber4Block4Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentMap_8_ok :
    tttLargeFiber4Block4Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentMap_9_ok :
    tttLargeFiber4Block4Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentMap_10_ok :
    tttLargeFiber4Block4Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentMap_11_ok :
    tttLargeFiber4Block4Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentMap_12_ok :
    tttLargeFiber4Block4Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentMap_13_ok :
    tttLargeFiber4Block4Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentMap_14_ok :
    tttLargeFiber4Block4Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentMap_15_ok :
    tttLargeFiber4Block4Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentPath_0_ok :
    tttLargeFiber4Block4Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentPath_1_ok :
    tttLargeFiber4Block4Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentPath_2_ok :
    tttLargeFiber4Block4Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentPath_3_ok :
    tttLargeFiber4Block4Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentPath_4_ok :
    tttLargeFiber4Block4Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentPath_5_ok :
    tttLargeFiber4Block4Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentPath_6_ok :
    tttLargeFiber4Block4Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentPath_7_ok :
    tttLargeFiber4Block4Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentPath_8_ok :
    tttLargeFiber4Block4Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentPath_9_ok :
    tttLargeFiber4Block4Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentPath_10_ok :
    tttLargeFiber4Block4Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentPath_11_ok :
    tttLargeFiber4Block4Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentPath_12_ok :
    tttLargeFiber4Block4Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentPath_13_ok :
    tttLargeFiber4Block4Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentPath_14_ok :
    tttLargeFiber4Block4Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block4Chunk3ParentPath_15_ok :
    tttLargeFiber4Block4Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block4Chunk3RowsAudit : Bool :=
  tttLargeFiber4Block4Chunk3RowCheck 0
    && tttLargeFiber4Block4Chunk3RowCheck 1
    && tttLargeFiber4Block4Chunk3RowCheck 2
    && tttLargeFiber4Block4Chunk3RowCheck 3
    && tttLargeFiber4Block4Chunk3RowCheck 4
    && tttLargeFiber4Block4Chunk3RowCheck 5
    && tttLargeFiber4Block4Chunk3RowCheck 6
    && tttLargeFiber4Block4Chunk3RowCheck 7
    && tttLargeFiber4Block4Chunk3RowCheck 8
    && tttLargeFiber4Block4Chunk3RowCheck 9
    && tttLargeFiber4Block4Chunk3RowCheck 10
    && tttLargeFiber4Block4Chunk3RowCheck 11
    && tttLargeFiber4Block4Chunk3RowCheck 12
    && tttLargeFiber4Block4Chunk3RowCheck 13
    && tttLargeFiber4Block4Chunk3RowCheck 14
    && tttLargeFiber4Block4Chunk3RowCheck 15

theorem tttLargeFiber4Block4Chunk3RowsAudit_ok :
    tttLargeFiber4Block4Chunk3RowsAudit = true := by
  simp [tttLargeFiber4Block4Chunk3RowsAudit,
    tttLargeFiber4Block4Chunk3Row_0_ok,
    tttLargeFiber4Block4Chunk3Row_1_ok,
    tttLargeFiber4Block4Chunk3Row_2_ok,
    tttLargeFiber4Block4Chunk3Row_3_ok,
    tttLargeFiber4Block4Chunk3Row_4_ok,
    tttLargeFiber4Block4Chunk3Row_5_ok,
    tttLargeFiber4Block4Chunk3Row_6_ok,
    tttLargeFiber4Block4Chunk3Row_7_ok,
    tttLargeFiber4Block4Chunk3Row_8_ok,
    tttLargeFiber4Block4Chunk3Row_9_ok,
    tttLargeFiber4Block4Chunk3Row_10_ok,
    tttLargeFiber4Block4Chunk3Row_11_ok,
    tttLargeFiber4Block4Chunk3Row_12_ok,
    tttLargeFiber4Block4Chunk3Row_13_ok,
    tttLargeFiber4Block4Chunk3Row_14_ok,
    tttLargeFiber4Block4Chunk3Row_15_ok]

def tttLargeFiber4Block4Chunk3ParentMapAudit : Bool :=
  tttLargeFiber4Block4Chunk3ParentMapCheck 0
    && tttLargeFiber4Block4Chunk3ParentMapCheck 1
    && tttLargeFiber4Block4Chunk3ParentMapCheck 2
    && tttLargeFiber4Block4Chunk3ParentMapCheck 3
    && tttLargeFiber4Block4Chunk3ParentMapCheck 4
    && tttLargeFiber4Block4Chunk3ParentMapCheck 5
    && tttLargeFiber4Block4Chunk3ParentMapCheck 6
    && tttLargeFiber4Block4Chunk3ParentMapCheck 7
    && tttLargeFiber4Block4Chunk3ParentMapCheck 8
    && tttLargeFiber4Block4Chunk3ParentMapCheck 9
    && tttLargeFiber4Block4Chunk3ParentMapCheck 10
    && tttLargeFiber4Block4Chunk3ParentMapCheck 11
    && tttLargeFiber4Block4Chunk3ParentMapCheck 12
    && tttLargeFiber4Block4Chunk3ParentMapCheck 13
    && tttLargeFiber4Block4Chunk3ParentMapCheck 14
    && tttLargeFiber4Block4Chunk3ParentMapCheck 15

theorem tttLargeFiber4Block4Chunk3ParentMapAudit_ok :
    tttLargeFiber4Block4Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber4Block4Chunk3ParentMapAudit,
    tttLargeFiber4Block4Chunk3ParentMap_0_ok,
    tttLargeFiber4Block4Chunk3ParentMap_1_ok,
    tttLargeFiber4Block4Chunk3ParentMap_2_ok,
    tttLargeFiber4Block4Chunk3ParentMap_3_ok,
    tttLargeFiber4Block4Chunk3ParentMap_4_ok,
    tttLargeFiber4Block4Chunk3ParentMap_5_ok,
    tttLargeFiber4Block4Chunk3ParentMap_6_ok,
    tttLargeFiber4Block4Chunk3ParentMap_7_ok,
    tttLargeFiber4Block4Chunk3ParentMap_8_ok,
    tttLargeFiber4Block4Chunk3ParentMap_9_ok,
    tttLargeFiber4Block4Chunk3ParentMap_10_ok,
    tttLargeFiber4Block4Chunk3ParentMap_11_ok,
    tttLargeFiber4Block4Chunk3ParentMap_12_ok,
    tttLargeFiber4Block4Chunk3ParentMap_13_ok,
    tttLargeFiber4Block4Chunk3ParentMap_14_ok,
    tttLargeFiber4Block4Chunk3ParentMap_15_ok]

def tttLargeFiber4Block4Chunk3ParentsAudit : Bool :=
  tttLargeFiber4Block4Chunk3ParentPathCheck 0
    && tttLargeFiber4Block4Chunk3ParentPathCheck 1
    && tttLargeFiber4Block4Chunk3ParentPathCheck 2
    && tttLargeFiber4Block4Chunk3ParentPathCheck 3
    && tttLargeFiber4Block4Chunk3ParentPathCheck 4
    && tttLargeFiber4Block4Chunk3ParentPathCheck 5
    && tttLargeFiber4Block4Chunk3ParentPathCheck 6
    && tttLargeFiber4Block4Chunk3ParentPathCheck 7
    && tttLargeFiber4Block4Chunk3ParentPathCheck 8
    && tttLargeFiber4Block4Chunk3ParentPathCheck 9
    && tttLargeFiber4Block4Chunk3ParentPathCheck 10
    && tttLargeFiber4Block4Chunk3ParentPathCheck 11
    && tttLargeFiber4Block4Chunk3ParentPathCheck 12
    && tttLargeFiber4Block4Chunk3ParentPathCheck 13
    && tttLargeFiber4Block4Chunk3ParentPathCheck 14
    && tttLargeFiber4Block4Chunk3ParentPathCheck 15

theorem tttLargeFiber4Block4Chunk3ParentsAudit_ok :
    tttLargeFiber4Block4Chunk3ParentsAudit = true := by
  simp [tttLargeFiber4Block4Chunk3ParentsAudit,
    tttLargeFiber4Block4Chunk3ParentPath_0_ok,
    tttLargeFiber4Block4Chunk3ParentPath_1_ok,
    tttLargeFiber4Block4Chunk3ParentPath_2_ok,
    tttLargeFiber4Block4Chunk3ParentPath_3_ok,
    tttLargeFiber4Block4Chunk3ParentPath_4_ok,
    tttLargeFiber4Block4Chunk3ParentPath_5_ok,
    tttLargeFiber4Block4Chunk3ParentPath_6_ok,
    tttLargeFiber4Block4Chunk3ParentPath_7_ok,
    tttLargeFiber4Block4Chunk3ParentPath_8_ok,
    tttLargeFiber4Block4Chunk3ParentPath_9_ok,
    tttLargeFiber4Block4Chunk3ParentPath_10_ok,
    tttLargeFiber4Block4Chunk3ParentPath_11_ok,
    tttLargeFiber4Block4Chunk3ParentPath_12_ok,
    tttLargeFiber4Block4Chunk3ParentPath_13_ok,
    tttLargeFiber4Block4Chunk3ParentPath_14_ok,
    tttLargeFiber4Block4Chunk3ParentPath_15_ok]

def tttLargeFiber4Block4Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block4Chunk3SourcesCheck &&
    tttLargeFiber4Block4Chunk3RowsAudit &&
    tttLargeFiber4Block4Chunk3ParentMapAudit &&
    tttLargeFiber4Block4Chunk3ParentsAudit

theorem tttLargeFiber4Block4Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber4Block4Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block4Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block4Chunk3SourcesCheck_ok,
    tttLargeFiber4Block4Chunk3RowsAudit_ok,
    tttLargeFiber4Block4Chunk3ParentMapAudit_ok,
    tttLargeFiber4Block4Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block4Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
