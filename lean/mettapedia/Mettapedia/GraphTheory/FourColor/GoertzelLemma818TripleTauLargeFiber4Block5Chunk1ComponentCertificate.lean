import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 5 chunk 1

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
For second-range rows it uses interval membership and explicit bounded parent
paths, avoiding broad expected-list traversal and recursive parent iteration.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block5Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block5Chunk1Sources : List Nat :=
  [3904, 3905, 3906, 3907, 3908, 3909, 3910, 3911,
   3912, 3913, 3914, 3915, 3916, 3917, 3918, 3919]

def tttLargeFiber4Row336 : TripleComponentParentRow :=
  tripleRow 3904 4032 117 142 0 119 74 16
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber4Row337 : TripleComponentParentRow :=
  tripleRow 3905 4033 117 142 1 119 74 17
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber4Row338 : TripleComponentParentRow :=
  tripleRow 3906 4034 117 142 2 119 74 18
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber4Row339 : TripleComponentParentRow :=
  tripleRow 3907 4035 117 142 3 119 74 19
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber4Row340 : TripleComponentParentRow :=
  tripleRow 3908 3896 117 142 48 117 141 156
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Row341 : TripleComponentParentRow :=
  tripleRow 3909 3897 117 142 49 117 141 157
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Row342 : TripleComponentParentRow :=
  tripleRow 3910 4038 117 142 50 119 74 34
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber4Row343 : TripleComponentParentRow :=
  tripleRow 3911 4039 117 142 51 119 74 35
    (chainMove LColor.b LColor.p 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.F4F5
    ]

def tttLargeFiber4Row344 : TripleComponentParentRow :=
  tripleRow 3912 3895 117 143 8 117 140 167
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber4Row345 : TripleComponentParentRow :=
  tripleRow 3913 3894 117 143 9 117 140 166
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
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

def tttLargeFiber4Row346 : TripleComponentParentRow :=
  tripleRow 3914 3892 117 143 10 117 140 164
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row347 : TripleComponentParentRow :=
  tripleRow 3915 3893 117 143 11 117 140 165
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row348 : TripleComponentParentRow :=
  tripleRow 3916 3888 117 143 56 117 140 148
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Row349 : TripleComponentParentRow :=
  tripleRow 3917 3889 117 143 57 117 140 149
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Row350 : TripleComponentParentRow :=
  tripleRow 3918 3890 117 143 58 117 140 150
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Row351 : TripleComponentParentRow :=
  tripleRow 3919 3891 117 143 59 117 140 151
    (chainMove LColor.r LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Block5Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row336
  , tttLargeFiber4Row337
  , tttLargeFiber4Row338
  , tttLargeFiber4Row339
  , tttLargeFiber4Row340
  , tttLargeFiber4Row341
  , tttLargeFiber4Row342
  , tttLargeFiber4Row343
  , tttLargeFiber4Row344
  , tttLargeFiber4Row345
  , tttLargeFiber4Row346
  , tttLargeFiber4Row347
  , tttLargeFiber4Row348
  , tttLargeFiber4Row349
  , tttLargeFiber4Row350
  , tttLargeFiber4Row351
  ]

def tttLargeFiber4Block5Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (2176 <= i) && decide (i < 2432)) ||
    (decide (3824 <= i) && decide (i < 4080))

def tttLargeFiber4Block5Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber4Block5Chunk1ExpectedContains row.source &&
    tttLargeFiber4Block5Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber4Key &&
          chainInputKey tttWord t == tttLargeFiber4Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber4Block5Chunk1SourcesCheck : Bool :=
  (tttLargeFiber4Block5Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber4Block5Chunk1Sources

theorem tttLargeFiber4Block5Chunk1SourcesCheck_ok :
    tttLargeFiber4Block5Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber4Block5Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber4Block5Chunk1RowValid
    (listGetD tttLargeFiber4Block5Chunk1Rows i default)

def tttLargeFiber4Block5Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block5Chunk1Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block5Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block5Chunk1Sources 0 0 == 3904 &&
      tttLargeFiber4ParentOf 3904 == 4032 &&
      tttLargeFiber4ParentOf 4032 == 2192 &&
      tttLargeFiber4ParentOf 2192 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block5Chunk1Sources 1 0 == 3905 &&
      tttLargeFiber4ParentOf 3905 == 4033 &&
      tttLargeFiber4ParentOf 4033 == 2193 &&
      tttLargeFiber4ParentOf 2193 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block5Chunk1Sources 2 0 == 3906 &&
      tttLargeFiber4ParentOf 3906 == 4034 &&
      tttLargeFiber4ParentOf 4034 == 2194 &&
      tttLargeFiber4ParentOf 2194 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block5Chunk1Sources 3 0 == 3907 &&
      tttLargeFiber4ParentOf 3907 == 4035 &&
      tttLargeFiber4ParentOf 4035 == 2195 &&
      tttLargeFiber4ParentOf 2195 == 2179 &&
      tttLargeFiber4ParentOf 2179 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block5Chunk1Sources 4 0 == 3908 &&
      tttLargeFiber4ParentOf 3908 == 3896 &&
      tttLargeFiber4ParentOf 3896 == 4024 &&
      tttLargeFiber4ParentOf 4024 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block5Chunk1Sources 5 0 == 3909 &&
      tttLargeFiber4ParentOf 3909 == 3897 &&
      tttLargeFiber4ParentOf 3897 == 4025 &&
      tttLargeFiber4ParentOf 4025 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block5Chunk1Sources 6 0 == 3910 &&
      tttLargeFiber4ParentOf 3910 == 4038 &&
      tttLargeFiber4ParentOf 4038 == 2198 &&
      tttLargeFiber4ParentOf 2198 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block5Chunk1Sources 7 0 == 3911 &&
      tttLargeFiber4ParentOf 3911 == 4039 &&
      tttLargeFiber4ParentOf 4039 == 2199 &&
      tttLargeFiber4ParentOf 2199 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block5Chunk1Sources 8 0 == 3912 &&
      tttLargeFiber4ParentOf 3912 == 3895 &&
      tttLargeFiber4ParentOf 3895 == 4023 &&
      tttLargeFiber4ParentOf 4023 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block5Chunk1Sources 9 0 == 3913 &&
      tttLargeFiber4ParentOf 3913 == 3894 &&
      tttLargeFiber4ParentOf 3894 == 4022 &&
      tttLargeFiber4ParentOf 4022 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block5Chunk1Sources 10 0 == 3914 &&
      tttLargeFiber4ParentOf 3914 == 3892 &&
      tttLargeFiber4ParentOf 3892 == 3888 &&
      tttLargeFiber4ParentOf 3888 == 4016 &&
      tttLargeFiber4ParentOf 4016 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block5Chunk1Sources 11 0 == 3915 &&
      tttLargeFiber4ParentOf 3915 == 3893 &&
      tttLargeFiber4ParentOf 3893 == 3889 &&
      tttLargeFiber4ParentOf 3889 == 4017 &&
      tttLargeFiber4ParentOf 4017 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block5Chunk1Sources 12 0 == 3916 &&
      tttLargeFiber4ParentOf 3916 == 3888 &&
      tttLargeFiber4ParentOf 3888 == 4016 &&
      tttLargeFiber4ParentOf 4016 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block5Chunk1Sources 13 0 == 3917 &&
      tttLargeFiber4ParentOf 3917 == 3889 &&
      tttLargeFiber4ParentOf 3889 == 4017 &&
      tttLargeFiber4ParentOf 4017 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block5Chunk1Sources 14 0 == 3918 &&
      tttLargeFiber4ParentOf 3918 == 3890 &&
      tttLargeFiber4ParentOf 3890 == 4018 &&
      tttLargeFiber4ParentOf 4018 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block5Chunk1Sources 15 0 == 3919 &&
      tttLargeFiber4ParentOf 3919 == 3891 &&
      tttLargeFiber4ParentOf 3891 == 3888 &&
      tttLargeFiber4ParentOf 3888 == 4016 &&
      tttLargeFiber4ParentOf 4016 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block5Chunk1Row_0_ok :
    tttLargeFiber4Block5Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1Row_1_ok :
    tttLargeFiber4Block5Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1Row_2_ok :
    tttLargeFiber4Block5Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1Row_3_ok :
    tttLargeFiber4Block5Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1Row_4_ok :
    tttLargeFiber4Block5Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1Row_5_ok :
    tttLargeFiber4Block5Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1Row_6_ok :
    tttLargeFiber4Block5Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1Row_7_ok :
    tttLargeFiber4Block5Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1Row_8_ok :
    tttLargeFiber4Block5Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1Row_9_ok :
    tttLargeFiber4Block5Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1Row_10_ok :
    tttLargeFiber4Block5Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1Row_11_ok :
    tttLargeFiber4Block5Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1Row_12_ok :
    tttLargeFiber4Block5Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1Row_13_ok :
    tttLargeFiber4Block5Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1Row_14_ok :
    tttLargeFiber4Block5Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1Row_15_ok :
    tttLargeFiber4Block5Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentMap_0_ok :
    tttLargeFiber4Block5Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentMap_1_ok :
    tttLargeFiber4Block5Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentMap_2_ok :
    tttLargeFiber4Block5Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentMap_3_ok :
    tttLargeFiber4Block5Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentMap_4_ok :
    tttLargeFiber4Block5Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentMap_5_ok :
    tttLargeFiber4Block5Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentMap_6_ok :
    tttLargeFiber4Block5Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentMap_7_ok :
    tttLargeFiber4Block5Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentMap_8_ok :
    tttLargeFiber4Block5Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentMap_9_ok :
    tttLargeFiber4Block5Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentMap_10_ok :
    tttLargeFiber4Block5Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentMap_11_ok :
    tttLargeFiber4Block5Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentMap_12_ok :
    tttLargeFiber4Block5Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentMap_13_ok :
    tttLargeFiber4Block5Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentMap_14_ok :
    tttLargeFiber4Block5Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentMap_15_ok :
    tttLargeFiber4Block5Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentPath_0_ok :
    tttLargeFiber4Block5Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentPath_1_ok :
    tttLargeFiber4Block5Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentPath_2_ok :
    tttLargeFiber4Block5Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentPath_3_ok :
    tttLargeFiber4Block5Chunk1ParentPathCheck 3 = true := by
  rfl

theorem tttLargeFiber4Block5Chunk1ParentPath_4_ok :
    tttLargeFiber4Block5Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentPath_5_ok :
    tttLargeFiber4Block5Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentPath_6_ok :
    tttLargeFiber4Block5Chunk1ParentPathCheck 6 = true := by
  rfl

theorem tttLargeFiber4Block5Chunk1ParentPath_7_ok :
    tttLargeFiber4Block5Chunk1ParentPathCheck 7 = true := by
  rfl

theorem tttLargeFiber4Block5Chunk1ParentPath_8_ok :
    tttLargeFiber4Block5Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentPath_9_ok :
    tttLargeFiber4Block5Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentPath_10_ok :
    tttLargeFiber4Block5Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentPath_11_ok :
    tttLargeFiber4Block5Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentPath_12_ok :
    tttLargeFiber4Block5Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentPath_13_ok :
    tttLargeFiber4Block5Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentPath_14_ok :
    tttLargeFiber4Block5Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block5Chunk1ParentPath_15_ok :
    tttLargeFiber4Block5Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block5Chunk1RowsAudit : Bool :=
  tttLargeFiber4Block5Chunk1RowCheck 0
    && tttLargeFiber4Block5Chunk1RowCheck 1
    && tttLargeFiber4Block5Chunk1RowCheck 2
    && tttLargeFiber4Block5Chunk1RowCheck 3
    && tttLargeFiber4Block5Chunk1RowCheck 4
    && tttLargeFiber4Block5Chunk1RowCheck 5
    && tttLargeFiber4Block5Chunk1RowCheck 6
    && tttLargeFiber4Block5Chunk1RowCheck 7
    && tttLargeFiber4Block5Chunk1RowCheck 8
    && tttLargeFiber4Block5Chunk1RowCheck 9
    && tttLargeFiber4Block5Chunk1RowCheck 10
    && tttLargeFiber4Block5Chunk1RowCheck 11
    && tttLargeFiber4Block5Chunk1RowCheck 12
    && tttLargeFiber4Block5Chunk1RowCheck 13
    && tttLargeFiber4Block5Chunk1RowCheck 14
    && tttLargeFiber4Block5Chunk1RowCheck 15

theorem tttLargeFiber4Block5Chunk1RowsAudit_ok :
    tttLargeFiber4Block5Chunk1RowsAudit = true := by
  simp [tttLargeFiber4Block5Chunk1RowsAudit,
    tttLargeFiber4Block5Chunk1Row_0_ok,
    tttLargeFiber4Block5Chunk1Row_1_ok,
    tttLargeFiber4Block5Chunk1Row_2_ok,
    tttLargeFiber4Block5Chunk1Row_3_ok,
    tttLargeFiber4Block5Chunk1Row_4_ok,
    tttLargeFiber4Block5Chunk1Row_5_ok,
    tttLargeFiber4Block5Chunk1Row_6_ok,
    tttLargeFiber4Block5Chunk1Row_7_ok,
    tttLargeFiber4Block5Chunk1Row_8_ok,
    tttLargeFiber4Block5Chunk1Row_9_ok,
    tttLargeFiber4Block5Chunk1Row_10_ok,
    tttLargeFiber4Block5Chunk1Row_11_ok,
    tttLargeFiber4Block5Chunk1Row_12_ok,
    tttLargeFiber4Block5Chunk1Row_13_ok,
    tttLargeFiber4Block5Chunk1Row_14_ok,
    tttLargeFiber4Block5Chunk1Row_15_ok]

def tttLargeFiber4Block5Chunk1ParentMapAudit : Bool :=
  tttLargeFiber4Block5Chunk1ParentMapCheck 0
    && tttLargeFiber4Block5Chunk1ParentMapCheck 1
    && tttLargeFiber4Block5Chunk1ParentMapCheck 2
    && tttLargeFiber4Block5Chunk1ParentMapCheck 3
    && tttLargeFiber4Block5Chunk1ParentMapCheck 4
    && tttLargeFiber4Block5Chunk1ParentMapCheck 5
    && tttLargeFiber4Block5Chunk1ParentMapCheck 6
    && tttLargeFiber4Block5Chunk1ParentMapCheck 7
    && tttLargeFiber4Block5Chunk1ParentMapCheck 8
    && tttLargeFiber4Block5Chunk1ParentMapCheck 9
    && tttLargeFiber4Block5Chunk1ParentMapCheck 10
    && tttLargeFiber4Block5Chunk1ParentMapCheck 11
    && tttLargeFiber4Block5Chunk1ParentMapCheck 12
    && tttLargeFiber4Block5Chunk1ParentMapCheck 13
    && tttLargeFiber4Block5Chunk1ParentMapCheck 14
    && tttLargeFiber4Block5Chunk1ParentMapCheck 15

theorem tttLargeFiber4Block5Chunk1ParentMapAudit_ok :
    tttLargeFiber4Block5Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber4Block5Chunk1ParentMapAudit,
    tttLargeFiber4Block5Chunk1ParentMap_0_ok,
    tttLargeFiber4Block5Chunk1ParentMap_1_ok,
    tttLargeFiber4Block5Chunk1ParentMap_2_ok,
    tttLargeFiber4Block5Chunk1ParentMap_3_ok,
    tttLargeFiber4Block5Chunk1ParentMap_4_ok,
    tttLargeFiber4Block5Chunk1ParentMap_5_ok,
    tttLargeFiber4Block5Chunk1ParentMap_6_ok,
    tttLargeFiber4Block5Chunk1ParentMap_7_ok,
    tttLargeFiber4Block5Chunk1ParentMap_8_ok,
    tttLargeFiber4Block5Chunk1ParentMap_9_ok,
    tttLargeFiber4Block5Chunk1ParentMap_10_ok,
    tttLargeFiber4Block5Chunk1ParentMap_11_ok,
    tttLargeFiber4Block5Chunk1ParentMap_12_ok,
    tttLargeFiber4Block5Chunk1ParentMap_13_ok,
    tttLargeFiber4Block5Chunk1ParentMap_14_ok,
    tttLargeFiber4Block5Chunk1ParentMap_15_ok]

def tttLargeFiber4Block5Chunk1ParentsAudit : Bool :=
  tttLargeFiber4Block5Chunk1ParentPathCheck 0
    && tttLargeFiber4Block5Chunk1ParentPathCheck 1
    && tttLargeFiber4Block5Chunk1ParentPathCheck 2
    && tttLargeFiber4Block5Chunk1ParentPathCheck 3
    && tttLargeFiber4Block5Chunk1ParentPathCheck 4
    && tttLargeFiber4Block5Chunk1ParentPathCheck 5
    && tttLargeFiber4Block5Chunk1ParentPathCheck 6
    && tttLargeFiber4Block5Chunk1ParentPathCheck 7
    && tttLargeFiber4Block5Chunk1ParentPathCheck 8
    && tttLargeFiber4Block5Chunk1ParentPathCheck 9
    && tttLargeFiber4Block5Chunk1ParentPathCheck 10
    && tttLargeFiber4Block5Chunk1ParentPathCheck 11
    && tttLargeFiber4Block5Chunk1ParentPathCheck 12
    && tttLargeFiber4Block5Chunk1ParentPathCheck 13
    && tttLargeFiber4Block5Chunk1ParentPathCheck 14
    && tttLargeFiber4Block5Chunk1ParentPathCheck 15

theorem tttLargeFiber4Block5Chunk1ParentsAudit_ok :
    tttLargeFiber4Block5Chunk1ParentsAudit = true := by
  simp [tttLargeFiber4Block5Chunk1ParentsAudit,
    tttLargeFiber4Block5Chunk1ParentPath_0_ok,
    tttLargeFiber4Block5Chunk1ParentPath_1_ok,
    tttLargeFiber4Block5Chunk1ParentPath_2_ok,
    tttLargeFiber4Block5Chunk1ParentPath_3_ok,
    tttLargeFiber4Block5Chunk1ParentPath_4_ok,
    tttLargeFiber4Block5Chunk1ParentPath_5_ok,
    tttLargeFiber4Block5Chunk1ParentPath_6_ok,
    tttLargeFiber4Block5Chunk1ParentPath_7_ok,
    tttLargeFiber4Block5Chunk1ParentPath_8_ok,
    tttLargeFiber4Block5Chunk1ParentPath_9_ok,
    tttLargeFiber4Block5Chunk1ParentPath_10_ok,
    tttLargeFiber4Block5Chunk1ParentPath_11_ok,
    tttLargeFiber4Block5Chunk1ParentPath_12_ok,
    tttLargeFiber4Block5Chunk1ParentPath_13_ok,
    tttLargeFiber4Block5Chunk1ParentPath_14_ok,
    tttLargeFiber4Block5Chunk1ParentPath_15_ok]

def tttLargeFiber4Block5Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block5Chunk1SourcesCheck &&
    tttLargeFiber4Block5Chunk1RowsAudit &&
    tttLargeFiber4Block5Chunk1ParentMapAudit &&
    tttLargeFiber4Block5Chunk1ParentsAudit

theorem tttLargeFiber4Block5Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber4Block5Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block5Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block5Chunk1SourcesCheck_ok,
    tttLargeFiber4Block5Chunk1RowsAudit_ok,
    tttLargeFiber4Block5Chunk1ParentMapAudit_ok,
    tttLargeFiber4Block5Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block5Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
