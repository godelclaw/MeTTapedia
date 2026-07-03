import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 7 chunk 1

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
For second-range rows it uses interval membership and explicit bounded parent
paths, avoiding broad expected-list traversal and recursive parent iteration.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block7Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block7Chunk1Sources : List Nat :=
  [4032, 4033, 4034, 4035, 4036, 4037, 4038, 4039,
   4040, 4041, 4042, 4043, 4044, 4045, 4046, 4047]

def tttLargeFiber4Row464 : TripleComponentParentRow :=
  tripleRow 4032 2192 119 74 16 64 82 16
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row465 : TripleComponentParentRow :=
  tripleRow 4033 2193 119 74 17 64 82 17
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row466 : TripleComponentParentRow :=
  tripleRow 4034 2194 119 74 18 64 82 18
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row467 : TripleComponentParentRow :=
  tripleRow 4035 2195 119 74 19 64 82 19
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row468 : TripleComponentParentRow :=
  tripleRow 4036 2196 119 74 32 64 82 32
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row469 : TripleComponentParentRow :=
  tripleRow 4037 2197 119 74 33 64 82 33
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row470 : TripleComponentParentRow :=
  tripleRow 4038 2198 119 74 34 64 82 34
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row471 : TripleComponentParentRow :=
  tripleRow 4039 2199 119 74 35 64 82 35
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row472 : TripleComponentParentRow :=
  tripleRow 4040 2200 119 75 24 64 83 24
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row473 : TripleComponentParentRow :=
  tripleRow 4041 2201 119 75 25 64 83 25
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row474 : TripleComponentParentRow :=
  tripleRow 4042 2202 119 75 26 64 83 26
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row475 : TripleComponentParentRow :=
  tripleRow 4043 2203 119 75 27 64 83 27
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row476 : TripleComponentParentRow :=
  tripleRow 4044 2204 119 75 40 64 83 40
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row477 : TripleComponentParentRow :=
  tripleRow 4045 2205 119 75 41 64 83 41
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row478 : TripleComponentParentRow :=
  tripleRow 4046 2206 119 75 42 64 83 42
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row479 : TripleComponentParentRow :=
  tripleRow 4047 2207 119 75 43 64 83 43
    (chainMove LColor.r LColor.p 0 TauEdge.F2F3)
    [ chainEdge 0 TauEdge.F2F3
    , chainEdge 0 TauEdge.F2F4
    , chainEdge 0 TauEdge.B4
    , chainEdge 0 TauEdge.F4F5
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Block7Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row464
  , tttLargeFiber4Row465
  , tttLargeFiber4Row466
  , tttLargeFiber4Row467
  , tttLargeFiber4Row468
  , tttLargeFiber4Row469
  , tttLargeFiber4Row470
  , tttLargeFiber4Row471
  , tttLargeFiber4Row472
  , tttLargeFiber4Row473
  , tttLargeFiber4Row474
  , tttLargeFiber4Row475
  , tttLargeFiber4Row476
  , tttLargeFiber4Row477
  , tttLargeFiber4Row478
  , tttLargeFiber4Row479
  ]

def tttLargeFiber4Block7Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (2176 <= i) && decide (i < 2432)) ||
    (decide (3824 <= i) && decide (i < 4080))

def tttLargeFiber4Block7Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber4Block7Chunk1ExpectedContains row.source &&
    tttLargeFiber4Block7Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber4Key &&
          chainInputKey tttWord t == tttLargeFiber4Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber4Block7Chunk1SourcesCheck : Bool :=
  (tttLargeFiber4Block7Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber4Block7Chunk1Sources

theorem tttLargeFiber4Block7Chunk1SourcesCheck_ok :
    tttLargeFiber4Block7Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber4Block7Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber4Block7Chunk1RowValid
    (listGetD tttLargeFiber4Block7Chunk1Rows i default)

def tttLargeFiber4Block7Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block7Chunk1Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block7Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block7Chunk1Sources 0 0 == 4032 &&
      tttLargeFiber4ParentOf 4032 == 2192 &&
      tttLargeFiber4ParentOf 2192 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (2 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block7Chunk1Sources 1 0 == 4033 &&
      tttLargeFiber4ParentOf 4033 == 2193 &&
      tttLargeFiber4ParentOf 2193 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block7Chunk1Sources 2 0 == 4034 &&
      tttLargeFiber4ParentOf 4034 == 2194 &&
      tttLargeFiber4ParentOf 2194 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block7Chunk1Sources 3 0 == 4035 &&
      tttLargeFiber4ParentOf 4035 == 2195 &&
      tttLargeFiber4ParentOf 2195 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block7Chunk1Sources 4 0 == 4036 &&
      tttLargeFiber4ParentOf 4036 == 2196 &&
      tttLargeFiber4ParentOf 2196 == 2192 &&
      tttLargeFiber4ParentOf 2192 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block7Chunk1Sources 5 0 == 4037 &&
      tttLargeFiber4ParentOf 4037 == 2197 &&
      tttLargeFiber4ParentOf 2197 == 2193 &&
      tttLargeFiber4ParentOf 2193 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block7Chunk1Sources 6 0 == 4038 &&
      tttLargeFiber4ParentOf 4038 == 2198 &&
      tttLargeFiber4ParentOf 2198 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block7Chunk1Sources 7 0 == 4039 &&
      tttLargeFiber4ParentOf 4039 == 2199 &&
      tttLargeFiber4ParentOf 2199 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block7Chunk1Sources 8 0 == 4040 &&
      tttLargeFiber4ParentOf 4040 == 2200 &&
      tttLargeFiber4ParentOf 2200 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block7Chunk1Sources 9 0 == 4041 &&
      tttLargeFiber4ParentOf 4041 == 2201 &&
      tttLargeFiber4ParentOf 2201 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block7Chunk1Sources 10 0 == 4042 &&
      tttLargeFiber4ParentOf 4042 == 2202 &&
      tttLargeFiber4ParentOf 2202 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block7Chunk1Sources 11 0 == 4043 &&
      tttLargeFiber4ParentOf 4043 == 2203 &&
      tttLargeFiber4ParentOf 2203 == 2187 &&
      tttLargeFiber4ParentOf 2187 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block7Chunk1Sources 12 0 == 4044 &&
      tttLargeFiber4ParentOf 4044 == 2204 &&
      tttLargeFiber4ParentOf 2204 == 2200 &&
      tttLargeFiber4ParentOf 2200 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block7Chunk1Sources 13 0 == 4045 &&
      tttLargeFiber4ParentOf 4045 == 2205 &&
      tttLargeFiber4ParentOf 2205 == 2201 &&
      tttLargeFiber4ParentOf 2201 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block7Chunk1Sources 14 0 == 4046 &&
      tttLargeFiber4ParentOf 4046 == 2206 &&
      tttLargeFiber4ParentOf 2206 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block7Chunk1Sources 15 0 == 4047 &&
      tttLargeFiber4ParentOf 4047 == 2207 &&
      tttLargeFiber4ParentOf 2207 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block7Chunk1Row_0_ok :
    tttLargeFiber4Block7Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1Row_1_ok :
    tttLargeFiber4Block7Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1Row_2_ok :
    tttLargeFiber4Block7Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1Row_3_ok :
    tttLargeFiber4Block7Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1Row_4_ok :
    tttLargeFiber4Block7Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1Row_5_ok :
    tttLargeFiber4Block7Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1Row_6_ok :
    tttLargeFiber4Block7Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1Row_7_ok :
    tttLargeFiber4Block7Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1Row_8_ok :
    tttLargeFiber4Block7Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1Row_9_ok :
    tttLargeFiber4Block7Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1Row_10_ok :
    tttLargeFiber4Block7Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1Row_11_ok :
    tttLargeFiber4Block7Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1Row_12_ok :
    tttLargeFiber4Block7Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1Row_13_ok :
    tttLargeFiber4Block7Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1Row_14_ok :
    tttLargeFiber4Block7Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1Row_15_ok :
    tttLargeFiber4Block7Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentMap_0_ok :
    tttLargeFiber4Block7Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentMap_1_ok :
    tttLargeFiber4Block7Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentMap_2_ok :
    tttLargeFiber4Block7Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentMap_3_ok :
    tttLargeFiber4Block7Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentMap_4_ok :
    tttLargeFiber4Block7Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentMap_5_ok :
    tttLargeFiber4Block7Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentMap_6_ok :
    tttLargeFiber4Block7Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentMap_7_ok :
    tttLargeFiber4Block7Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentMap_8_ok :
    tttLargeFiber4Block7Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentMap_9_ok :
    tttLargeFiber4Block7Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentMap_10_ok :
    tttLargeFiber4Block7Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentMap_11_ok :
    tttLargeFiber4Block7Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentMap_12_ok :
    tttLargeFiber4Block7Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentMap_13_ok :
    tttLargeFiber4Block7Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentMap_14_ok :
    tttLargeFiber4Block7Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentMap_15_ok :
    tttLargeFiber4Block7Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentPath_0_ok :
    tttLargeFiber4Block7Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentPath_1_ok :
    tttLargeFiber4Block7Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentPath_2_ok :
    tttLargeFiber4Block7Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentPath_3_ok :
    tttLargeFiber4Block7Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentPath_4_ok :
    tttLargeFiber4Block7Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentPath_5_ok :
    tttLargeFiber4Block7Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentPath_6_ok :
    tttLargeFiber4Block7Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentPath_7_ok :
    tttLargeFiber4Block7Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentPath_8_ok :
    tttLargeFiber4Block7Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentPath_9_ok :
    tttLargeFiber4Block7Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentPath_10_ok :
    tttLargeFiber4Block7Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentPath_11_ok :
    tttLargeFiber4Block7Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentPath_12_ok :
    tttLargeFiber4Block7Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentPath_13_ok :
    tttLargeFiber4Block7Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentPath_14_ok :
    tttLargeFiber4Block7Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block7Chunk1ParentPath_15_ok :
    tttLargeFiber4Block7Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block7Chunk1RowsAudit : Bool :=
  tttLargeFiber4Block7Chunk1RowCheck 0
    && tttLargeFiber4Block7Chunk1RowCheck 1
    && tttLargeFiber4Block7Chunk1RowCheck 2
    && tttLargeFiber4Block7Chunk1RowCheck 3
    && tttLargeFiber4Block7Chunk1RowCheck 4
    && tttLargeFiber4Block7Chunk1RowCheck 5
    && tttLargeFiber4Block7Chunk1RowCheck 6
    && tttLargeFiber4Block7Chunk1RowCheck 7
    && tttLargeFiber4Block7Chunk1RowCheck 8
    && tttLargeFiber4Block7Chunk1RowCheck 9
    && tttLargeFiber4Block7Chunk1RowCheck 10
    && tttLargeFiber4Block7Chunk1RowCheck 11
    && tttLargeFiber4Block7Chunk1RowCheck 12
    && tttLargeFiber4Block7Chunk1RowCheck 13
    && tttLargeFiber4Block7Chunk1RowCheck 14
    && tttLargeFiber4Block7Chunk1RowCheck 15

theorem tttLargeFiber4Block7Chunk1RowsAudit_ok :
    tttLargeFiber4Block7Chunk1RowsAudit = true := by
  simp [tttLargeFiber4Block7Chunk1RowsAudit,
    tttLargeFiber4Block7Chunk1Row_0_ok,
    tttLargeFiber4Block7Chunk1Row_1_ok,
    tttLargeFiber4Block7Chunk1Row_2_ok,
    tttLargeFiber4Block7Chunk1Row_3_ok,
    tttLargeFiber4Block7Chunk1Row_4_ok,
    tttLargeFiber4Block7Chunk1Row_5_ok,
    tttLargeFiber4Block7Chunk1Row_6_ok,
    tttLargeFiber4Block7Chunk1Row_7_ok,
    tttLargeFiber4Block7Chunk1Row_8_ok,
    tttLargeFiber4Block7Chunk1Row_9_ok,
    tttLargeFiber4Block7Chunk1Row_10_ok,
    tttLargeFiber4Block7Chunk1Row_11_ok,
    tttLargeFiber4Block7Chunk1Row_12_ok,
    tttLargeFiber4Block7Chunk1Row_13_ok,
    tttLargeFiber4Block7Chunk1Row_14_ok,
    tttLargeFiber4Block7Chunk1Row_15_ok]

def tttLargeFiber4Block7Chunk1ParentMapAudit : Bool :=
  tttLargeFiber4Block7Chunk1ParentMapCheck 0
    && tttLargeFiber4Block7Chunk1ParentMapCheck 1
    && tttLargeFiber4Block7Chunk1ParentMapCheck 2
    && tttLargeFiber4Block7Chunk1ParentMapCheck 3
    && tttLargeFiber4Block7Chunk1ParentMapCheck 4
    && tttLargeFiber4Block7Chunk1ParentMapCheck 5
    && tttLargeFiber4Block7Chunk1ParentMapCheck 6
    && tttLargeFiber4Block7Chunk1ParentMapCheck 7
    && tttLargeFiber4Block7Chunk1ParentMapCheck 8
    && tttLargeFiber4Block7Chunk1ParentMapCheck 9
    && tttLargeFiber4Block7Chunk1ParentMapCheck 10
    && tttLargeFiber4Block7Chunk1ParentMapCheck 11
    && tttLargeFiber4Block7Chunk1ParentMapCheck 12
    && tttLargeFiber4Block7Chunk1ParentMapCheck 13
    && tttLargeFiber4Block7Chunk1ParentMapCheck 14
    && tttLargeFiber4Block7Chunk1ParentMapCheck 15

theorem tttLargeFiber4Block7Chunk1ParentMapAudit_ok :
    tttLargeFiber4Block7Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber4Block7Chunk1ParentMapAudit,
    tttLargeFiber4Block7Chunk1ParentMap_0_ok,
    tttLargeFiber4Block7Chunk1ParentMap_1_ok,
    tttLargeFiber4Block7Chunk1ParentMap_2_ok,
    tttLargeFiber4Block7Chunk1ParentMap_3_ok,
    tttLargeFiber4Block7Chunk1ParentMap_4_ok,
    tttLargeFiber4Block7Chunk1ParentMap_5_ok,
    tttLargeFiber4Block7Chunk1ParentMap_6_ok,
    tttLargeFiber4Block7Chunk1ParentMap_7_ok,
    tttLargeFiber4Block7Chunk1ParentMap_8_ok,
    tttLargeFiber4Block7Chunk1ParentMap_9_ok,
    tttLargeFiber4Block7Chunk1ParentMap_10_ok,
    tttLargeFiber4Block7Chunk1ParentMap_11_ok,
    tttLargeFiber4Block7Chunk1ParentMap_12_ok,
    tttLargeFiber4Block7Chunk1ParentMap_13_ok,
    tttLargeFiber4Block7Chunk1ParentMap_14_ok,
    tttLargeFiber4Block7Chunk1ParentMap_15_ok]

def tttLargeFiber4Block7Chunk1ParentsAudit : Bool :=
  tttLargeFiber4Block7Chunk1ParentPathCheck 0
    && tttLargeFiber4Block7Chunk1ParentPathCheck 1
    && tttLargeFiber4Block7Chunk1ParentPathCheck 2
    && tttLargeFiber4Block7Chunk1ParentPathCheck 3
    && tttLargeFiber4Block7Chunk1ParentPathCheck 4
    && tttLargeFiber4Block7Chunk1ParentPathCheck 5
    && tttLargeFiber4Block7Chunk1ParentPathCheck 6
    && tttLargeFiber4Block7Chunk1ParentPathCheck 7
    && tttLargeFiber4Block7Chunk1ParentPathCheck 8
    && tttLargeFiber4Block7Chunk1ParentPathCheck 9
    && tttLargeFiber4Block7Chunk1ParentPathCheck 10
    && tttLargeFiber4Block7Chunk1ParentPathCheck 11
    && tttLargeFiber4Block7Chunk1ParentPathCheck 12
    && tttLargeFiber4Block7Chunk1ParentPathCheck 13
    && tttLargeFiber4Block7Chunk1ParentPathCheck 14
    && tttLargeFiber4Block7Chunk1ParentPathCheck 15

theorem tttLargeFiber4Block7Chunk1ParentsAudit_ok :
    tttLargeFiber4Block7Chunk1ParentsAudit = true := by
  simp [tttLargeFiber4Block7Chunk1ParentsAudit,
    tttLargeFiber4Block7Chunk1ParentPath_0_ok,
    tttLargeFiber4Block7Chunk1ParentPath_1_ok,
    tttLargeFiber4Block7Chunk1ParentPath_2_ok,
    tttLargeFiber4Block7Chunk1ParentPath_3_ok,
    tttLargeFiber4Block7Chunk1ParentPath_4_ok,
    tttLargeFiber4Block7Chunk1ParentPath_5_ok,
    tttLargeFiber4Block7Chunk1ParentPath_6_ok,
    tttLargeFiber4Block7Chunk1ParentPath_7_ok,
    tttLargeFiber4Block7Chunk1ParentPath_8_ok,
    tttLargeFiber4Block7Chunk1ParentPath_9_ok,
    tttLargeFiber4Block7Chunk1ParentPath_10_ok,
    tttLargeFiber4Block7Chunk1ParentPath_11_ok,
    tttLargeFiber4Block7Chunk1ParentPath_12_ok,
    tttLargeFiber4Block7Chunk1ParentPath_13_ok,
    tttLargeFiber4Block7Chunk1ParentPath_14_ok,
    tttLargeFiber4Block7Chunk1ParentPath_15_ok]

def tttLargeFiber4Block7Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block7Chunk1SourcesCheck &&
    tttLargeFiber4Block7Chunk1RowsAudit &&
    tttLargeFiber4Block7Chunk1ParentMapAudit &&
    tttLargeFiber4Block7Chunk1ParentsAudit

theorem tttLargeFiber4Block7Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber4Block7Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block7Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block7Chunk1SourcesCheck_ok,
    tttLargeFiber4Block7Chunk1RowsAudit_ok,
    tttLargeFiber4Block7Chunk1ParentMapAudit_ok,
    tttLargeFiber4Block7Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block7Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
