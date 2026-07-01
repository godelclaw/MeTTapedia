import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 5 chunk 3

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
For second-range rows it uses interval membership and explicit bounded parent
paths, avoiding broad expected-list traversal and recursive parent iteration.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block5Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block5Chunk3Sources : List Nat :=
  [3936, 3937, 3938, 3939, 3940, 3941, 3942, 3943,
   3944, 3945, 3946, 3947, 3948, 3949, 3950, 3951]

def tttLargeFiber4Row368 : TripleComponentParentRow :=
  tripleRow 3936 4064 117 190 64 119 126 64
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row369 : TripleComponentParentRow :=
  tripleRow 3937 4065 117 190 65 119 126 65
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row370 : TripleComponentParentRow :=
  tripleRow 3938 4066 117 190 66 119 126 66
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row371 : TripleComponentParentRow :=
  tripleRow 3939 3923 117 190 67 117 188 135
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber4Row372 : TripleComponentParentRow :=
  tripleRow 3940 3908 117 190 116 117 142 48
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber4Row373 : TripleComponentParentRow :=
  tripleRow 3941 3909 117 190 117 117 142 49
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
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

def tttLargeFiber4Row374 : TripleComponentParentRow :=
  tripleRow 3942 4070 117 190 118 119 126 118
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row375 : TripleComponentParentRow :=
  tripleRow 3943 4071 117 190 119 119 126 119
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row376 : TripleComponentParentRow :=
  tripleRow 3944 4072 117 191 72 119 127 72
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row377 : TripleComponentParentRow :=
  tripleRow 3945 4073 117 191 73 119 127 73
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row378 : TripleComponentParentRow :=
  tripleRow 3946 4074 117 191 74 119 127 74
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row379 : TripleComponentParentRow :=
  tripleRow 3947 4075 117 191 75 119 127 75
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row380 : TripleComponentParentRow :=
  tripleRow 3948 3916 117 191 124 117 143 56
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber4Row381 : TripleComponentParentRow :=
  tripleRow 3949 3917 117 191 125 117 143 57
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
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

def tttLargeFiber4Row382 : TripleComponentParentRow :=
  tripleRow 3950 4078 117 191 126 119 127 126
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Row383 : TripleComponentParentRow :=
  tripleRow 3951 4079 117 191 127 119 127 127
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F0F2
    ]

def tttLargeFiber4Block5Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row368
  , tttLargeFiber4Row369
  , tttLargeFiber4Row370
  , tttLargeFiber4Row371
  , tttLargeFiber4Row372
  , tttLargeFiber4Row373
  , tttLargeFiber4Row374
  , tttLargeFiber4Row375
  , tttLargeFiber4Row376
  , tttLargeFiber4Row377
  , tttLargeFiber4Row378
  , tttLargeFiber4Row379
  , tttLargeFiber4Row380
  , tttLargeFiber4Row381
  , tttLargeFiber4Row382
  , tttLargeFiber4Row383
  ]

def tttLargeFiber4Block5Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (2176 <= i) && decide (i < 2432)) ||
    (decide (3824 <= i) && decide (i < 4080))

def tttLargeFiber4Block5Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber4Block5Chunk3ExpectedContains row.source &&
    tttLargeFiber4Block5Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber4Key &&
          chainInputKey tttWord t == tttLargeFiber4Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber4Block5Chunk3SourcesCheck : Bool :=
  (tttLargeFiber4Block5Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber4Block5Chunk3Sources

theorem tttLargeFiber4Block5Chunk3SourcesCheck_ok :
    tttLargeFiber4Block5Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber4Block5Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber4Block5Chunk3RowValid
    (listGetD tttLargeFiber4Block5Chunk3Rows i default)

def tttLargeFiber4Block5Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block5Chunk3Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block5Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block5Chunk3Sources 0 0 == 3936 &&
      tttLargeFiber4ParentOf 3936 == 4064 &&
      tttLargeFiber4ParentOf 4064 == 2224 &&
      tttLargeFiber4ParentOf 2224 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block5Chunk3Sources 1 0 == 3937 &&
      tttLargeFiber4ParentOf 3937 == 4065 &&
      tttLargeFiber4ParentOf 4065 == 2225 &&
      tttLargeFiber4ParentOf 2225 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block5Chunk3Sources 2 0 == 3938 &&
      tttLargeFiber4ParentOf 3938 == 4066 &&
      tttLargeFiber4ParentOf 4066 == 2226 &&
      tttLargeFiber4ParentOf 2226 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block5Chunk3Sources 3 0 == 3939 &&
      tttLargeFiber4ParentOf 3939 == 3923 &&
      tttLargeFiber4ParentOf 3923 == 3891 &&
      tttLargeFiber4ParentOf 3891 == 3888 &&
      tttLargeFiber4ParentOf 3888 == 4016 &&
      tttLargeFiber4ParentOf 4016 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block5Chunk3Sources 4 0 == 3940 &&
      tttLargeFiber4ParentOf 3940 == 3908 &&
      tttLargeFiber4ParentOf 3908 == 3896 &&
      tttLargeFiber4ParentOf 3896 == 4024 &&
      tttLargeFiber4ParentOf 4024 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block5Chunk3Sources 5 0 == 3941 &&
      tttLargeFiber4ParentOf 3941 == 3909 &&
      tttLargeFiber4ParentOf 3909 == 3897 &&
      tttLargeFiber4ParentOf 3897 == 4025 &&
      tttLargeFiber4ParentOf 4025 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block5Chunk3Sources 6 0 == 3942 &&
      tttLargeFiber4ParentOf 3942 == 4070 &&
      tttLargeFiber4ParentOf 4070 == 2230 &&
      tttLargeFiber4ParentOf 2230 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block5Chunk3Sources 7 0 == 3943 &&
      tttLargeFiber4ParentOf 3943 == 4071 &&
      tttLargeFiber4ParentOf 4071 == 2231 &&
      tttLargeFiber4ParentOf 2231 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block5Chunk3Sources 8 0 == 3944 &&
      tttLargeFiber4ParentOf 3944 == 4072 &&
      tttLargeFiber4ParentOf 4072 == 2232 &&
      tttLargeFiber4ParentOf 2232 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block5Chunk3Sources 9 0 == 3945 &&
      tttLargeFiber4ParentOf 3945 == 4073 &&
      tttLargeFiber4ParentOf 4073 == 2233 &&
      tttLargeFiber4ParentOf 2233 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block5Chunk3Sources 10 0 == 3946 &&
      tttLargeFiber4ParentOf 3946 == 4074 &&
      tttLargeFiber4ParentOf 4074 == 2234 &&
      tttLargeFiber4ParentOf 2234 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block5Chunk3Sources 11 0 == 3947 &&
      tttLargeFiber4ParentOf 3947 == 4075 &&
      tttLargeFiber4ParentOf 4075 == 2235 &&
      tttLargeFiber4ParentOf 2235 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block5Chunk3Sources 12 0 == 3948 &&
      tttLargeFiber4ParentOf 3948 == 3916 &&
      tttLargeFiber4ParentOf 3916 == 3888 &&
      tttLargeFiber4ParentOf 3888 == 4016 &&
      tttLargeFiber4ParentOf 4016 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block5Chunk3Sources 13 0 == 3949 &&
      tttLargeFiber4ParentOf 3949 == 3917 &&
      tttLargeFiber4ParentOf 3917 == 3889 &&
      tttLargeFiber4ParentOf 3889 == 4017 &&
      tttLargeFiber4ParentOf 4017 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block5Chunk3Sources 14 0 == 3950 &&
      tttLargeFiber4ParentOf 3950 == 4078 &&
      tttLargeFiber4ParentOf 4078 == 2238 &&
      tttLargeFiber4ParentOf 2238 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block5Chunk3Sources 15 0 == 3951 &&
      tttLargeFiber4ParentOf 3951 == 4079 &&
      tttLargeFiber4ParentOf 4079 == 2239 &&
      tttLargeFiber4ParentOf 2239 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block5Chunk3Row_0_ok :
    tttLargeFiber4Block5Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3Row_1_ok :
    tttLargeFiber4Block5Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3Row_2_ok :
    tttLargeFiber4Block5Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3Row_3_ok :
    tttLargeFiber4Block5Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3Row_4_ok :
    tttLargeFiber4Block5Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3Row_5_ok :
    tttLargeFiber4Block5Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3Row_6_ok :
    tttLargeFiber4Block5Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3Row_7_ok :
    tttLargeFiber4Block5Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3Row_8_ok :
    tttLargeFiber4Block5Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3Row_9_ok :
    tttLargeFiber4Block5Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3Row_10_ok :
    tttLargeFiber4Block5Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3Row_11_ok :
    tttLargeFiber4Block5Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3Row_12_ok :
    tttLargeFiber4Block5Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3Row_13_ok :
    tttLargeFiber4Block5Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3Row_14_ok :
    tttLargeFiber4Block5Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3Row_15_ok :
    tttLargeFiber4Block5Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentMap_0_ok :
    tttLargeFiber4Block5Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentMap_1_ok :
    tttLargeFiber4Block5Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentMap_2_ok :
    tttLargeFiber4Block5Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentMap_3_ok :
    tttLargeFiber4Block5Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentMap_4_ok :
    tttLargeFiber4Block5Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentMap_5_ok :
    tttLargeFiber4Block5Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentMap_6_ok :
    tttLargeFiber4Block5Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentMap_7_ok :
    tttLargeFiber4Block5Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentMap_8_ok :
    tttLargeFiber4Block5Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentMap_9_ok :
    tttLargeFiber4Block5Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentMap_10_ok :
    tttLargeFiber4Block5Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentMap_11_ok :
    tttLargeFiber4Block5Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentMap_12_ok :
    tttLargeFiber4Block5Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentMap_13_ok :
    tttLargeFiber4Block5Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentMap_14_ok :
    tttLargeFiber4Block5Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentMap_15_ok :
    tttLargeFiber4Block5Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentPath_0_ok :
    tttLargeFiber4Block5Chunk3ParentPathCheck 0 = true := by
  rfl

theorem tttLargeFiber4Block5Chunk3ParentPath_1_ok :
    tttLargeFiber4Block5Chunk3ParentPathCheck 1 = true := by
  rfl

theorem tttLargeFiber4Block5Chunk3ParentPath_2_ok :
    tttLargeFiber4Block5Chunk3ParentPathCheck 2 = true := by
  rfl

theorem tttLargeFiber4Block5Chunk3ParentPath_3_ok :
    tttLargeFiber4Block5Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentPath_4_ok :
    tttLargeFiber4Block5Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentPath_5_ok :
    tttLargeFiber4Block5Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentPath_6_ok :
    tttLargeFiber4Block5Chunk3ParentPathCheck 6 = true := by
  rfl

theorem tttLargeFiber4Block5Chunk3ParentPath_7_ok :
    tttLargeFiber4Block5Chunk3ParentPathCheck 7 = true := by
  rfl

theorem tttLargeFiber4Block5Chunk3ParentPath_8_ok :
    tttLargeFiber4Block5Chunk3ParentPathCheck 8 = true := by
  rfl

theorem tttLargeFiber4Block5Chunk3ParentPath_9_ok :
    tttLargeFiber4Block5Chunk3ParentPathCheck 9 = true := by
  rfl

theorem tttLargeFiber4Block5Chunk3ParentPath_10_ok :
    tttLargeFiber4Block5Chunk3ParentPathCheck 10 = true := by
  rfl

theorem tttLargeFiber4Block5Chunk3ParentPath_11_ok :
    tttLargeFiber4Block5Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentPath_12_ok :
    tttLargeFiber4Block5Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentPath_13_ok :
    tttLargeFiber4Block5Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block5Chunk3ParentPath_14_ok :
    tttLargeFiber4Block5Chunk3ParentPathCheck 14 = true := by
  rfl

theorem tttLargeFiber4Block5Chunk3ParentPath_15_ok :
    tttLargeFiber4Block5Chunk3ParentPathCheck 15 = true := by
  rfl

def tttLargeFiber4Block5Chunk3RowsAudit : Bool :=
  tttLargeFiber4Block5Chunk3RowCheck 0
    && tttLargeFiber4Block5Chunk3RowCheck 1
    && tttLargeFiber4Block5Chunk3RowCheck 2
    && tttLargeFiber4Block5Chunk3RowCheck 3
    && tttLargeFiber4Block5Chunk3RowCheck 4
    && tttLargeFiber4Block5Chunk3RowCheck 5
    && tttLargeFiber4Block5Chunk3RowCheck 6
    && tttLargeFiber4Block5Chunk3RowCheck 7
    && tttLargeFiber4Block5Chunk3RowCheck 8
    && tttLargeFiber4Block5Chunk3RowCheck 9
    && tttLargeFiber4Block5Chunk3RowCheck 10
    && tttLargeFiber4Block5Chunk3RowCheck 11
    && tttLargeFiber4Block5Chunk3RowCheck 12
    && tttLargeFiber4Block5Chunk3RowCheck 13
    && tttLargeFiber4Block5Chunk3RowCheck 14
    && tttLargeFiber4Block5Chunk3RowCheck 15

theorem tttLargeFiber4Block5Chunk3RowsAudit_ok :
    tttLargeFiber4Block5Chunk3RowsAudit = true := by
  simp [tttLargeFiber4Block5Chunk3RowsAudit,
    tttLargeFiber4Block5Chunk3Row_0_ok,
    tttLargeFiber4Block5Chunk3Row_1_ok,
    tttLargeFiber4Block5Chunk3Row_2_ok,
    tttLargeFiber4Block5Chunk3Row_3_ok,
    tttLargeFiber4Block5Chunk3Row_4_ok,
    tttLargeFiber4Block5Chunk3Row_5_ok,
    tttLargeFiber4Block5Chunk3Row_6_ok,
    tttLargeFiber4Block5Chunk3Row_7_ok,
    tttLargeFiber4Block5Chunk3Row_8_ok,
    tttLargeFiber4Block5Chunk3Row_9_ok,
    tttLargeFiber4Block5Chunk3Row_10_ok,
    tttLargeFiber4Block5Chunk3Row_11_ok,
    tttLargeFiber4Block5Chunk3Row_12_ok,
    tttLargeFiber4Block5Chunk3Row_13_ok,
    tttLargeFiber4Block5Chunk3Row_14_ok,
    tttLargeFiber4Block5Chunk3Row_15_ok]

def tttLargeFiber4Block5Chunk3ParentMapAudit : Bool :=
  tttLargeFiber4Block5Chunk3ParentMapCheck 0
    && tttLargeFiber4Block5Chunk3ParentMapCheck 1
    && tttLargeFiber4Block5Chunk3ParentMapCheck 2
    && tttLargeFiber4Block5Chunk3ParentMapCheck 3
    && tttLargeFiber4Block5Chunk3ParentMapCheck 4
    && tttLargeFiber4Block5Chunk3ParentMapCheck 5
    && tttLargeFiber4Block5Chunk3ParentMapCheck 6
    && tttLargeFiber4Block5Chunk3ParentMapCheck 7
    && tttLargeFiber4Block5Chunk3ParentMapCheck 8
    && tttLargeFiber4Block5Chunk3ParentMapCheck 9
    && tttLargeFiber4Block5Chunk3ParentMapCheck 10
    && tttLargeFiber4Block5Chunk3ParentMapCheck 11
    && tttLargeFiber4Block5Chunk3ParentMapCheck 12
    && tttLargeFiber4Block5Chunk3ParentMapCheck 13
    && tttLargeFiber4Block5Chunk3ParentMapCheck 14
    && tttLargeFiber4Block5Chunk3ParentMapCheck 15

theorem tttLargeFiber4Block5Chunk3ParentMapAudit_ok :
    tttLargeFiber4Block5Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber4Block5Chunk3ParentMapAudit,
    tttLargeFiber4Block5Chunk3ParentMap_0_ok,
    tttLargeFiber4Block5Chunk3ParentMap_1_ok,
    tttLargeFiber4Block5Chunk3ParentMap_2_ok,
    tttLargeFiber4Block5Chunk3ParentMap_3_ok,
    tttLargeFiber4Block5Chunk3ParentMap_4_ok,
    tttLargeFiber4Block5Chunk3ParentMap_5_ok,
    tttLargeFiber4Block5Chunk3ParentMap_6_ok,
    tttLargeFiber4Block5Chunk3ParentMap_7_ok,
    tttLargeFiber4Block5Chunk3ParentMap_8_ok,
    tttLargeFiber4Block5Chunk3ParentMap_9_ok,
    tttLargeFiber4Block5Chunk3ParentMap_10_ok,
    tttLargeFiber4Block5Chunk3ParentMap_11_ok,
    tttLargeFiber4Block5Chunk3ParentMap_12_ok,
    tttLargeFiber4Block5Chunk3ParentMap_13_ok,
    tttLargeFiber4Block5Chunk3ParentMap_14_ok,
    tttLargeFiber4Block5Chunk3ParentMap_15_ok]

def tttLargeFiber4Block5Chunk3ParentsAudit : Bool :=
  tttLargeFiber4Block5Chunk3ParentPathCheck 0
    && tttLargeFiber4Block5Chunk3ParentPathCheck 1
    && tttLargeFiber4Block5Chunk3ParentPathCheck 2
    && tttLargeFiber4Block5Chunk3ParentPathCheck 3
    && tttLargeFiber4Block5Chunk3ParentPathCheck 4
    && tttLargeFiber4Block5Chunk3ParentPathCheck 5
    && tttLargeFiber4Block5Chunk3ParentPathCheck 6
    && tttLargeFiber4Block5Chunk3ParentPathCheck 7
    && tttLargeFiber4Block5Chunk3ParentPathCheck 8
    && tttLargeFiber4Block5Chunk3ParentPathCheck 9
    && tttLargeFiber4Block5Chunk3ParentPathCheck 10
    && tttLargeFiber4Block5Chunk3ParentPathCheck 11
    && tttLargeFiber4Block5Chunk3ParentPathCheck 12
    && tttLargeFiber4Block5Chunk3ParentPathCheck 13
    && tttLargeFiber4Block5Chunk3ParentPathCheck 14
    && tttLargeFiber4Block5Chunk3ParentPathCheck 15

theorem tttLargeFiber4Block5Chunk3ParentsAudit_ok :
    tttLargeFiber4Block5Chunk3ParentsAudit = true := by
  simp [tttLargeFiber4Block5Chunk3ParentsAudit,
    tttLargeFiber4Block5Chunk3ParentPath_0_ok,
    tttLargeFiber4Block5Chunk3ParentPath_1_ok,
    tttLargeFiber4Block5Chunk3ParentPath_2_ok,
    tttLargeFiber4Block5Chunk3ParentPath_3_ok,
    tttLargeFiber4Block5Chunk3ParentPath_4_ok,
    tttLargeFiber4Block5Chunk3ParentPath_5_ok,
    tttLargeFiber4Block5Chunk3ParentPath_6_ok,
    tttLargeFiber4Block5Chunk3ParentPath_7_ok,
    tttLargeFiber4Block5Chunk3ParentPath_8_ok,
    tttLargeFiber4Block5Chunk3ParentPath_9_ok,
    tttLargeFiber4Block5Chunk3ParentPath_10_ok,
    tttLargeFiber4Block5Chunk3ParentPath_11_ok,
    tttLargeFiber4Block5Chunk3ParentPath_12_ok,
    tttLargeFiber4Block5Chunk3ParentPath_13_ok,
    tttLargeFiber4Block5Chunk3ParentPath_14_ok,
    tttLargeFiber4Block5Chunk3ParentPath_15_ok]

def tttLargeFiber4Block5Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block5Chunk3SourcesCheck &&
    tttLargeFiber4Block5Chunk3RowsAudit &&
    tttLargeFiber4Block5Chunk3ParentMapAudit &&
    tttLargeFiber4Block5Chunk3ParentsAudit

theorem tttLargeFiber4Block5Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber4Block5Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block5Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block5Chunk3SourcesCheck_ok,
    tttLargeFiber4Block5Chunk3RowsAudit_ok,
    tttLargeFiber4Block5Chunk3ParentMapAudit_ok,
    tttLargeFiber4Block5Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block5Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
