import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 5 chunk 0

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
For second-range rows it uses interval membership and explicit bounded parent
paths, avoiding broad expected-list traversal and recursive parent iteration.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block5Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block5Chunk0Sources : List Nat :=
  [3888, 3889, 3890, 3891, 3892, 3893, 3894, 3895,
   3896, 3897, 3898, 3899, 3900, 3901, 3902, 3903]

def tttLargeFiber4Row320 : TripleComponentParentRow :=
  tripleRow 3888 4016 117 140 148 119 72 80
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.B7
    , chainEdge 2 TauEdge.B4
    ]

def tttLargeFiber4Row321 : TripleComponentParentRow :=
  tripleRow 3889 4017 117 140 149 119 72 81
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.B7
    , chainEdge 2 TauEdge.B4
    ]

def tttLargeFiber4Row322 : TripleComponentParentRow :=
  tripleRow 3890 4018 117 140 150 119 72 82
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber4Row323 : TripleComponentParentRow :=
  tripleRow 3891 3888 117 140 151 117 140 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row324 : TripleComponentParentRow :=
  tripleRow 3892 3888 117 140 164 117 140 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber4Row325 : TripleComponentParentRow :=
  tripleRow 3893 3889 117 140 165 117 140 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber4Row326 : TripleComponentParentRow :=
  tripleRow 3894 4022 117 140 166 119 72 102
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber4Row327 : TripleComponentParentRow :=
  tripleRow 3895 4023 117 140 167 119 72 103
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber4Row328 : TripleComponentParentRow :=
  tripleRow 3896 4024 117 141 156 119 73 88
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.B7
    , chainEdge 2 TauEdge.B4
    ]

def tttLargeFiber4Row329 : TripleComponentParentRow :=
  tripleRow 3897 4025 117 141 157 119 73 89
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.B7
    , chainEdge 2 TauEdge.B4
    ]

def tttLargeFiber4Row330 : TripleComponentParentRow :=
  tripleRow 3898 4026 117 141 158 119 73 90
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber4Row331 : TripleComponentParentRow :=
  tripleRow 3899 3896 117 141 159 117 141 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row332 : TripleComponentParentRow :=
  tripleRow 3900 3896 117 141 172 117 141 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber4Row333 : TripleComponentParentRow :=
  tripleRow 3901 3897 117 141 173 117 141 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber4Row334 : TripleComponentParentRow :=
  tripleRow 3902 4030 117 141 174 119 73 110
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber4Row335 : TripleComponentParentRow :=
  tripleRow 3903 4031 117 141 175 119 73 111
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber4Block5Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row320
  , tttLargeFiber4Row321
  , tttLargeFiber4Row322
  , tttLargeFiber4Row323
  , tttLargeFiber4Row324
  , tttLargeFiber4Row325
  , tttLargeFiber4Row326
  , tttLargeFiber4Row327
  , tttLargeFiber4Row328
  , tttLargeFiber4Row329
  , tttLargeFiber4Row330
  , tttLargeFiber4Row331
  , tttLargeFiber4Row332
  , tttLargeFiber4Row333
  , tttLargeFiber4Row334
  , tttLargeFiber4Row335
  ]

def tttLargeFiber4Block5Chunk0ExpectedContains (i : Nat) : Bool :=
  (decide (2176 <= i) && decide (i < 2432)) ||
    (decide (3824 <= i) && decide (i < 4080))

def tttLargeFiber4Block5Chunk0RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber4Block5Chunk0ExpectedContains row.source &&
    tttLargeFiber4Block5Chunk0ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber4Key &&
          chainInputKey tttWord t == tttLargeFiber4Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber4Block5Chunk0SourcesCheck : Bool :=
  (tttLargeFiber4Block5Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber4Block5Chunk0Sources

theorem tttLargeFiber4Block5Chunk0SourcesCheck_ok :
    tttLargeFiber4Block5Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber4Block5Chunk0RowCheck (i : Nat) : Bool :=
  tttLargeFiber4Block5Chunk0RowValid
    (listGetD tttLargeFiber4Block5Chunk0Rows i default)

def tttLargeFiber4Block5Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block5Chunk0Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block5Chunk0ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block5Chunk0Sources 0 0 == 3888 &&
      tttLargeFiber4ParentOf 3888 == 4016 &&
      tttLargeFiber4ParentOf 4016 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (2 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block5Chunk0Sources 1 0 == 3889 &&
      tttLargeFiber4ParentOf 3889 == 4017 &&
      tttLargeFiber4ParentOf 4017 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block5Chunk0Sources 2 0 == 3890 &&
      tttLargeFiber4ParentOf 3890 == 4018 &&
      tttLargeFiber4ParentOf 4018 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block5Chunk0Sources 3 0 == 3891 &&
      tttLargeFiber4ParentOf 3891 == 3888 &&
      tttLargeFiber4ParentOf 3888 == 4016 &&
      tttLargeFiber4ParentOf 4016 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block5Chunk0Sources 4 0 == 3892 &&
      tttLargeFiber4ParentOf 3892 == 3888 &&
      tttLargeFiber4ParentOf 3888 == 4016 &&
      tttLargeFiber4ParentOf 4016 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block5Chunk0Sources 5 0 == 3893 &&
      tttLargeFiber4ParentOf 3893 == 3889 &&
      tttLargeFiber4ParentOf 3889 == 4017 &&
      tttLargeFiber4ParentOf 4017 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block5Chunk0Sources 6 0 == 3894 &&
      tttLargeFiber4ParentOf 3894 == 4022 &&
      tttLargeFiber4ParentOf 4022 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block5Chunk0Sources 7 0 == 3895 &&
      tttLargeFiber4ParentOf 3895 == 4023 &&
      tttLargeFiber4ParentOf 4023 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block5Chunk0Sources 8 0 == 3896 &&
      tttLargeFiber4ParentOf 3896 == 4024 &&
      tttLargeFiber4ParentOf 4024 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block5Chunk0Sources 9 0 == 3897 &&
      tttLargeFiber4ParentOf 3897 == 4025 &&
      tttLargeFiber4ParentOf 4025 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block5Chunk0Sources 10 0 == 3898 &&
      tttLargeFiber4ParentOf 3898 == 4026 &&
      tttLargeFiber4ParentOf 4026 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block5Chunk0Sources 11 0 == 3899 &&
      tttLargeFiber4ParentOf 3899 == 3896 &&
      tttLargeFiber4ParentOf 3896 == 4024 &&
      tttLargeFiber4ParentOf 4024 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block5Chunk0Sources 12 0 == 3900 &&
      tttLargeFiber4ParentOf 3900 == 3896 &&
      tttLargeFiber4ParentOf 3896 == 4024 &&
      tttLargeFiber4ParentOf 4024 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block5Chunk0Sources 13 0 == 3901 &&
      tttLargeFiber4ParentOf 3901 == 3897 &&
      tttLargeFiber4ParentOf 3897 == 4025 &&
      tttLargeFiber4ParentOf 4025 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block5Chunk0Sources 14 0 == 3902 &&
      tttLargeFiber4ParentOf 3902 == 4030 &&
      tttLargeFiber4ParentOf 4030 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block5Chunk0Sources 15 0 == 3903 &&
      tttLargeFiber4ParentOf 3903 == 4031 &&
      tttLargeFiber4ParentOf 4031 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block5Chunk0Row_0_ok :
    tttLargeFiber4Block5Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0Row_1_ok :
    tttLargeFiber4Block5Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0Row_2_ok :
    tttLargeFiber4Block5Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0Row_3_ok :
    tttLargeFiber4Block5Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0Row_4_ok :
    tttLargeFiber4Block5Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0Row_5_ok :
    tttLargeFiber4Block5Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0Row_6_ok :
    tttLargeFiber4Block5Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0Row_7_ok :
    tttLargeFiber4Block5Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0Row_8_ok :
    tttLargeFiber4Block5Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0Row_9_ok :
    tttLargeFiber4Block5Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0Row_10_ok :
    tttLargeFiber4Block5Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0Row_11_ok :
    tttLargeFiber4Block5Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0Row_12_ok :
    tttLargeFiber4Block5Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0Row_13_ok :
    tttLargeFiber4Block5Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0Row_14_ok :
    tttLargeFiber4Block5Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0Row_15_ok :
    tttLargeFiber4Block5Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentMap_0_ok :
    tttLargeFiber4Block5Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentMap_1_ok :
    tttLargeFiber4Block5Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentMap_2_ok :
    tttLargeFiber4Block5Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentMap_3_ok :
    tttLargeFiber4Block5Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentMap_4_ok :
    tttLargeFiber4Block5Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentMap_5_ok :
    tttLargeFiber4Block5Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentMap_6_ok :
    tttLargeFiber4Block5Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentMap_7_ok :
    tttLargeFiber4Block5Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentMap_8_ok :
    tttLargeFiber4Block5Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentMap_9_ok :
    tttLargeFiber4Block5Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentMap_10_ok :
    tttLargeFiber4Block5Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentMap_11_ok :
    tttLargeFiber4Block5Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentMap_12_ok :
    tttLargeFiber4Block5Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentMap_13_ok :
    tttLargeFiber4Block5Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentMap_14_ok :
    tttLargeFiber4Block5Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentMap_15_ok :
    tttLargeFiber4Block5Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentPath_0_ok :
    tttLargeFiber4Block5Chunk0ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentPath_1_ok :
    tttLargeFiber4Block5Chunk0ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentPath_2_ok :
    tttLargeFiber4Block5Chunk0ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentPath_3_ok :
    tttLargeFiber4Block5Chunk0ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentPath_4_ok :
    tttLargeFiber4Block5Chunk0ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentPath_5_ok :
    tttLargeFiber4Block5Chunk0ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentPath_6_ok :
    tttLargeFiber4Block5Chunk0ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentPath_7_ok :
    tttLargeFiber4Block5Chunk0ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentPath_8_ok :
    tttLargeFiber4Block5Chunk0ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentPath_9_ok :
    tttLargeFiber4Block5Chunk0ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentPath_10_ok :
    tttLargeFiber4Block5Chunk0ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentPath_11_ok :
    tttLargeFiber4Block5Chunk0ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentPath_12_ok :
    tttLargeFiber4Block5Chunk0ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentPath_13_ok :
    tttLargeFiber4Block5Chunk0ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentPath_14_ok :
    tttLargeFiber4Block5Chunk0ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block5Chunk0ParentPath_15_ok :
    tttLargeFiber4Block5Chunk0ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block5Chunk0RowsAudit : Bool :=
  tttLargeFiber4Block5Chunk0RowCheck 0
    && tttLargeFiber4Block5Chunk0RowCheck 1
    && tttLargeFiber4Block5Chunk0RowCheck 2
    && tttLargeFiber4Block5Chunk0RowCheck 3
    && tttLargeFiber4Block5Chunk0RowCheck 4
    && tttLargeFiber4Block5Chunk0RowCheck 5
    && tttLargeFiber4Block5Chunk0RowCheck 6
    && tttLargeFiber4Block5Chunk0RowCheck 7
    && tttLargeFiber4Block5Chunk0RowCheck 8
    && tttLargeFiber4Block5Chunk0RowCheck 9
    && tttLargeFiber4Block5Chunk0RowCheck 10
    && tttLargeFiber4Block5Chunk0RowCheck 11
    && tttLargeFiber4Block5Chunk0RowCheck 12
    && tttLargeFiber4Block5Chunk0RowCheck 13
    && tttLargeFiber4Block5Chunk0RowCheck 14
    && tttLargeFiber4Block5Chunk0RowCheck 15

theorem tttLargeFiber4Block5Chunk0RowsAudit_ok :
    tttLargeFiber4Block5Chunk0RowsAudit = true := by
  simp [tttLargeFiber4Block5Chunk0RowsAudit,
    tttLargeFiber4Block5Chunk0Row_0_ok,
    tttLargeFiber4Block5Chunk0Row_1_ok,
    tttLargeFiber4Block5Chunk0Row_2_ok,
    tttLargeFiber4Block5Chunk0Row_3_ok,
    tttLargeFiber4Block5Chunk0Row_4_ok,
    tttLargeFiber4Block5Chunk0Row_5_ok,
    tttLargeFiber4Block5Chunk0Row_6_ok,
    tttLargeFiber4Block5Chunk0Row_7_ok,
    tttLargeFiber4Block5Chunk0Row_8_ok,
    tttLargeFiber4Block5Chunk0Row_9_ok,
    tttLargeFiber4Block5Chunk0Row_10_ok,
    tttLargeFiber4Block5Chunk0Row_11_ok,
    tttLargeFiber4Block5Chunk0Row_12_ok,
    tttLargeFiber4Block5Chunk0Row_13_ok,
    tttLargeFiber4Block5Chunk0Row_14_ok,
    tttLargeFiber4Block5Chunk0Row_15_ok]

def tttLargeFiber4Block5Chunk0ParentMapAudit : Bool :=
  tttLargeFiber4Block5Chunk0ParentMapCheck 0
    && tttLargeFiber4Block5Chunk0ParentMapCheck 1
    && tttLargeFiber4Block5Chunk0ParentMapCheck 2
    && tttLargeFiber4Block5Chunk0ParentMapCheck 3
    && tttLargeFiber4Block5Chunk0ParentMapCheck 4
    && tttLargeFiber4Block5Chunk0ParentMapCheck 5
    && tttLargeFiber4Block5Chunk0ParentMapCheck 6
    && tttLargeFiber4Block5Chunk0ParentMapCheck 7
    && tttLargeFiber4Block5Chunk0ParentMapCheck 8
    && tttLargeFiber4Block5Chunk0ParentMapCheck 9
    && tttLargeFiber4Block5Chunk0ParentMapCheck 10
    && tttLargeFiber4Block5Chunk0ParentMapCheck 11
    && tttLargeFiber4Block5Chunk0ParentMapCheck 12
    && tttLargeFiber4Block5Chunk0ParentMapCheck 13
    && tttLargeFiber4Block5Chunk0ParentMapCheck 14
    && tttLargeFiber4Block5Chunk0ParentMapCheck 15

theorem tttLargeFiber4Block5Chunk0ParentMapAudit_ok :
    tttLargeFiber4Block5Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber4Block5Chunk0ParentMapAudit,
    tttLargeFiber4Block5Chunk0ParentMap_0_ok,
    tttLargeFiber4Block5Chunk0ParentMap_1_ok,
    tttLargeFiber4Block5Chunk0ParentMap_2_ok,
    tttLargeFiber4Block5Chunk0ParentMap_3_ok,
    tttLargeFiber4Block5Chunk0ParentMap_4_ok,
    tttLargeFiber4Block5Chunk0ParentMap_5_ok,
    tttLargeFiber4Block5Chunk0ParentMap_6_ok,
    tttLargeFiber4Block5Chunk0ParentMap_7_ok,
    tttLargeFiber4Block5Chunk0ParentMap_8_ok,
    tttLargeFiber4Block5Chunk0ParentMap_9_ok,
    tttLargeFiber4Block5Chunk0ParentMap_10_ok,
    tttLargeFiber4Block5Chunk0ParentMap_11_ok,
    tttLargeFiber4Block5Chunk0ParentMap_12_ok,
    tttLargeFiber4Block5Chunk0ParentMap_13_ok,
    tttLargeFiber4Block5Chunk0ParentMap_14_ok,
    tttLargeFiber4Block5Chunk0ParentMap_15_ok]

def tttLargeFiber4Block5Chunk0ParentsAudit : Bool :=
  tttLargeFiber4Block5Chunk0ParentPathCheck 0
    && tttLargeFiber4Block5Chunk0ParentPathCheck 1
    && tttLargeFiber4Block5Chunk0ParentPathCheck 2
    && tttLargeFiber4Block5Chunk0ParentPathCheck 3
    && tttLargeFiber4Block5Chunk0ParentPathCheck 4
    && tttLargeFiber4Block5Chunk0ParentPathCheck 5
    && tttLargeFiber4Block5Chunk0ParentPathCheck 6
    && tttLargeFiber4Block5Chunk0ParentPathCheck 7
    && tttLargeFiber4Block5Chunk0ParentPathCheck 8
    && tttLargeFiber4Block5Chunk0ParentPathCheck 9
    && tttLargeFiber4Block5Chunk0ParentPathCheck 10
    && tttLargeFiber4Block5Chunk0ParentPathCheck 11
    && tttLargeFiber4Block5Chunk0ParentPathCheck 12
    && tttLargeFiber4Block5Chunk0ParentPathCheck 13
    && tttLargeFiber4Block5Chunk0ParentPathCheck 14
    && tttLargeFiber4Block5Chunk0ParentPathCheck 15

theorem tttLargeFiber4Block5Chunk0ParentsAudit_ok :
    tttLargeFiber4Block5Chunk0ParentsAudit = true := by
  simp [tttLargeFiber4Block5Chunk0ParentsAudit,
    tttLargeFiber4Block5Chunk0ParentPath_0_ok,
    tttLargeFiber4Block5Chunk0ParentPath_1_ok,
    tttLargeFiber4Block5Chunk0ParentPath_2_ok,
    tttLargeFiber4Block5Chunk0ParentPath_3_ok,
    tttLargeFiber4Block5Chunk0ParentPath_4_ok,
    tttLargeFiber4Block5Chunk0ParentPath_5_ok,
    tttLargeFiber4Block5Chunk0ParentPath_6_ok,
    tttLargeFiber4Block5Chunk0ParentPath_7_ok,
    tttLargeFiber4Block5Chunk0ParentPath_8_ok,
    tttLargeFiber4Block5Chunk0ParentPath_9_ok,
    tttLargeFiber4Block5Chunk0ParentPath_10_ok,
    tttLargeFiber4Block5Chunk0ParentPath_11_ok,
    tttLargeFiber4Block5Chunk0ParentPath_12_ok,
    tttLargeFiber4Block5Chunk0ParentPath_13_ok,
    tttLargeFiber4Block5Chunk0ParentPath_14_ok,
    tttLargeFiber4Block5Chunk0ParentPath_15_ok]

def tttLargeFiber4Block5Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block5Chunk0SourcesCheck &&
    tttLargeFiber4Block5Chunk0RowsAudit &&
    tttLargeFiber4Block5Chunk0ParentMapAudit &&
    tttLargeFiber4Block5Chunk0ParentsAudit

theorem tttLargeFiber4Block5Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber4Block5Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block5Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block5Chunk0SourcesCheck_ok,
    tttLargeFiber4Block5Chunk0RowsAudit_ok,
    tttLargeFiber4Block5Chunk0ParentMapAudit_ok,
    tttLargeFiber4Block5Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block5Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
