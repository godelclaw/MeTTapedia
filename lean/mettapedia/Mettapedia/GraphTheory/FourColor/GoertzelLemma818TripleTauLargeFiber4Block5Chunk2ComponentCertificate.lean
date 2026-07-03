import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 5 chunk 2

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
For second-range rows it uses interval membership and explicit bounded parent
paths, avoiding broad expected-list traversal and recursive parent iteration.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block5Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block5Chunk2Sources : List Nat :=
  [3920, 3921, 3922, 3923, 3924, 3925, 3926, 3927,
   3928, 3929, 3930, 3931, 3932, 3933, 3934, 3935]

def tttLargeFiber4Row352 : TripleComponentParentRow :=
  tripleRow 3920 3888 117 188 132 117 140 148
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row353 : TripleComponentParentRow :=
  tripleRow 3921 3889 117 188 133 117 140 149
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row354 : TripleComponentParentRow :=
  tripleRow 3922 3890 117 188 134 117 140 150
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row355 : TripleComponentParentRow :=
  tripleRow 3923 3891 117 188 135 117 140 151
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row356 : TripleComponentParentRow :=
  tripleRow 3924 3892 117 188 180 117 140 164
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row357 : TripleComponentParentRow :=
  tripleRow 3925 3893 117 188 181 117 140 165
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row358 : TripleComponentParentRow :=
  tripleRow 3926 3894 117 188 182 117 140 166
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row359 : TripleComponentParentRow :=
  tripleRow 3927 3895 117 188 183 117 140 167
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row360 : TripleComponentParentRow :=
  tripleRow 3928 3896 117 189 140 117 141 156
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row361 : TripleComponentParentRow :=
  tripleRow 3929 3897 117 189 141 117 141 157
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row362 : TripleComponentParentRow :=
  tripleRow 3930 3898 117 189 142 117 141 158
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row363 : TripleComponentParentRow :=
  tripleRow 3931 3899 117 189 143 117 141 159
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row364 : TripleComponentParentRow :=
  tripleRow 3932 3900 117 189 188 117 141 172
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row365 : TripleComponentParentRow :=
  tripleRow 3933 3901 117 189 189 117 141 173
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row366 : TripleComponentParentRow :=
  tripleRow 3934 3902 117 189 190 117 141 174
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row367 : TripleComponentParentRow :=
  tripleRow 3935 3903 117 189 191 117 141 175
    (chainMove LColor.r LColor.b 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Block5Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row352
  , tttLargeFiber4Row353
  , tttLargeFiber4Row354
  , tttLargeFiber4Row355
  , tttLargeFiber4Row356
  , tttLargeFiber4Row357
  , tttLargeFiber4Row358
  , tttLargeFiber4Row359
  , tttLargeFiber4Row360
  , tttLargeFiber4Row361
  , tttLargeFiber4Row362
  , tttLargeFiber4Row363
  , tttLargeFiber4Row364
  , tttLargeFiber4Row365
  , tttLargeFiber4Row366
  , tttLargeFiber4Row367
  ]

def tttLargeFiber4Block5Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (2176 <= i) && decide (i < 2432)) ||
    (decide (3824 <= i) && decide (i < 4080))

def tttLargeFiber4Block5Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber4Block5Chunk2ExpectedContains row.source &&
    tttLargeFiber4Block5Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber4Key &&
          chainInputKey tttWord t == tttLargeFiber4Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber4Block5Chunk2SourcesCheck : Bool :=
  (tttLargeFiber4Block5Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber4Block5Chunk2Sources

theorem tttLargeFiber4Block5Chunk2SourcesCheck_ok :
    tttLargeFiber4Block5Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber4Block5Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber4Block5Chunk2RowValid
    (listGetD tttLargeFiber4Block5Chunk2Rows i default)

def tttLargeFiber4Block5Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block5Chunk2Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block5Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber4Block5Chunk2Sources 0 0 == 3920 &&
      tttLargeFiber4ParentOf 3920 == 3888 &&
      tttLargeFiber4ParentOf 3888 == 4016 &&
      tttLargeFiber4ParentOf 4016 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (3 <= tttLargeFiber4MaxParentDepth)
  | 1 => listGetD tttLargeFiber4Block5Chunk2Sources 1 0 == 3921 &&
      tttLargeFiber4ParentOf 3921 == 3889 &&
      tttLargeFiber4ParentOf 3889 == 4017 &&
      tttLargeFiber4ParentOf 4017 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 2 => listGetD tttLargeFiber4Block5Chunk2Sources 2 0 == 3922 &&
      tttLargeFiber4ParentOf 3922 == 3890 &&
      tttLargeFiber4ParentOf 3890 == 4018 &&
      tttLargeFiber4ParentOf 4018 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 3 => listGetD tttLargeFiber4Block5Chunk2Sources 3 0 == 3923 &&
      tttLargeFiber4ParentOf 3923 == 3891 &&
      tttLargeFiber4ParentOf 3891 == 3888 &&
      tttLargeFiber4ParentOf 3888 == 4016 &&
      tttLargeFiber4ParentOf 4016 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 4 => listGetD tttLargeFiber4Block5Chunk2Sources 4 0 == 3924 &&
      tttLargeFiber4ParentOf 3924 == 3892 &&
      tttLargeFiber4ParentOf 3892 == 3888 &&
      tttLargeFiber4ParentOf 3888 == 4016 &&
      tttLargeFiber4ParentOf 4016 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 5 => listGetD tttLargeFiber4Block5Chunk2Sources 5 0 == 3925 &&
      tttLargeFiber4ParentOf 3925 == 3893 &&
      tttLargeFiber4ParentOf 3893 == 3889 &&
      tttLargeFiber4ParentOf 3889 == 4017 &&
      tttLargeFiber4ParentOf 4017 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 6 => listGetD tttLargeFiber4Block5Chunk2Sources 6 0 == 3926 &&
      tttLargeFiber4ParentOf 3926 == 3894 &&
      tttLargeFiber4ParentOf 3894 == 4022 &&
      tttLargeFiber4ParentOf 4022 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 7 => listGetD tttLargeFiber4Block5Chunk2Sources 7 0 == 3927 &&
      tttLargeFiber4ParentOf 3927 == 3895 &&
      tttLargeFiber4ParentOf 3895 == 4023 &&
      tttLargeFiber4ParentOf 4023 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 8 => listGetD tttLargeFiber4Block5Chunk2Sources 8 0 == 3928 &&
      tttLargeFiber4ParentOf 3928 == 3896 &&
      tttLargeFiber4ParentOf 3896 == 4024 &&
      tttLargeFiber4ParentOf 4024 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (4 <= tttLargeFiber4MaxParentDepth)
  | 9 => listGetD tttLargeFiber4Block5Chunk2Sources 9 0 == 3929 &&
      tttLargeFiber4ParentOf 3929 == 3897 &&
      tttLargeFiber4ParentOf 3897 == 4025 &&
      tttLargeFiber4ParentOf 4025 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 10 => listGetD tttLargeFiber4Block5Chunk2Sources 10 0 == 3930 &&
      tttLargeFiber4ParentOf 3930 == 3898 &&
      tttLargeFiber4ParentOf 3898 == 4026 &&
      tttLargeFiber4ParentOf 4026 == 2186 &&
      tttLargeFiber4ParentOf 2186 == 2178 &&
      tttLargeFiber4ParentOf 2178 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 11 => listGetD tttLargeFiber4Block5Chunk2Sources 11 0 == 3931 &&
      tttLargeFiber4ParentOf 3931 == 3899 &&
      tttLargeFiber4ParentOf 3899 == 3896 &&
      tttLargeFiber4ParentOf 3896 == 4024 &&
      tttLargeFiber4ParentOf 4024 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 12 => listGetD tttLargeFiber4Block5Chunk2Sources 12 0 == 3932 &&
      tttLargeFiber4ParentOf 3932 == 3900 &&
      tttLargeFiber4ParentOf 3900 == 3896 &&
      tttLargeFiber4ParentOf 3896 == 4024 &&
      tttLargeFiber4ParentOf 4024 == 2184 &&
      tttLargeFiber4ParentOf 2184 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | 13 => listGetD tttLargeFiber4Block5Chunk2Sources 13 0 == 3933 &&
      tttLargeFiber4ParentOf 3933 == 3901 &&
      tttLargeFiber4ParentOf 3901 == 3897 &&
      tttLargeFiber4ParentOf 3897 == 4025 &&
      tttLargeFiber4ParentOf 4025 == 2185 &&
      tttLargeFiber4ParentOf 2185 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 14 => listGetD tttLargeFiber4Block5Chunk2Sources 14 0 == 3934 &&
      tttLargeFiber4ParentOf 3934 == 3902 &&
      tttLargeFiber4ParentOf 3902 == 4030 &&
      tttLargeFiber4ParentOf 4030 == 2190 &&
      tttLargeFiber4ParentOf 2190 == 2182 &&
      tttLargeFiber4ParentOf 2182 == 2177 &&
      tttLargeFiber4ParentOf 2177 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (6 <= tttLargeFiber4MaxParentDepth)
  | 15 => listGetD tttLargeFiber4Block5Chunk2Sources 15 0 == 3935 &&
      tttLargeFiber4ParentOf 3935 == 3903 &&
      tttLargeFiber4ParentOf 3903 == 4031 &&
      tttLargeFiber4ParentOf 4031 == 2191 &&
      tttLargeFiber4ParentOf 2191 == 2183 &&
      tttLargeFiber4ParentOf 2183 == 2176 &&
      2176 == tttLargeFiber4Root &&
      decide (5 <= tttLargeFiber4MaxParentDepth)
  | _ => false

theorem tttLargeFiber4Block5Chunk2Row_0_ok :
    tttLargeFiber4Block5Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2Row_1_ok :
    tttLargeFiber4Block5Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2Row_2_ok :
    tttLargeFiber4Block5Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2Row_3_ok :
    tttLargeFiber4Block5Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2Row_4_ok :
    tttLargeFiber4Block5Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2Row_5_ok :
    tttLargeFiber4Block5Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2Row_6_ok :
    tttLargeFiber4Block5Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2Row_7_ok :
    tttLargeFiber4Block5Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2Row_8_ok :
    tttLargeFiber4Block5Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2Row_9_ok :
    tttLargeFiber4Block5Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2Row_10_ok :
    tttLargeFiber4Block5Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2Row_11_ok :
    tttLargeFiber4Block5Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2Row_12_ok :
    tttLargeFiber4Block5Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2Row_13_ok :
    tttLargeFiber4Block5Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2Row_14_ok :
    tttLargeFiber4Block5Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2Row_15_ok :
    tttLargeFiber4Block5Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentMap_0_ok :
    tttLargeFiber4Block5Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentMap_1_ok :
    tttLargeFiber4Block5Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentMap_2_ok :
    tttLargeFiber4Block5Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentMap_3_ok :
    tttLargeFiber4Block5Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentMap_4_ok :
    tttLargeFiber4Block5Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentMap_5_ok :
    tttLargeFiber4Block5Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentMap_6_ok :
    tttLargeFiber4Block5Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentMap_7_ok :
    tttLargeFiber4Block5Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentMap_8_ok :
    tttLargeFiber4Block5Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentMap_9_ok :
    tttLargeFiber4Block5Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentMap_10_ok :
    tttLargeFiber4Block5Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentMap_11_ok :
    tttLargeFiber4Block5Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentMap_12_ok :
    tttLargeFiber4Block5Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentMap_13_ok :
    tttLargeFiber4Block5Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentMap_14_ok :
    tttLargeFiber4Block5Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentMap_15_ok :
    tttLargeFiber4Block5Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentPath_0_ok :
    tttLargeFiber4Block5Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentPath_1_ok :
    tttLargeFiber4Block5Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentPath_2_ok :
    tttLargeFiber4Block5Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentPath_3_ok :
    tttLargeFiber4Block5Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentPath_4_ok :
    tttLargeFiber4Block5Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentPath_5_ok :
    tttLargeFiber4Block5Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentPath_6_ok :
    tttLargeFiber4Block5Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentPath_7_ok :
    tttLargeFiber4Block5Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentPath_8_ok :
    tttLargeFiber4Block5Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentPath_9_ok :
    tttLargeFiber4Block5Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentPath_10_ok :
    tttLargeFiber4Block5Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentPath_11_ok :
    tttLargeFiber4Block5Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentPath_12_ok :
    tttLargeFiber4Block5Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentPath_13_ok :
    tttLargeFiber4Block5Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentPath_14_ok :
    tttLargeFiber4Block5Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber4Block5Chunk2ParentPath_15_ok :
    tttLargeFiber4Block5Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber4Block5Chunk2RowsAudit : Bool :=
  tttLargeFiber4Block5Chunk2RowCheck 0
    && tttLargeFiber4Block5Chunk2RowCheck 1
    && tttLargeFiber4Block5Chunk2RowCheck 2
    && tttLargeFiber4Block5Chunk2RowCheck 3
    && tttLargeFiber4Block5Chunk2RowCheck 4
    && tttLargeFiber4Block5Chunk2RowCheck 5
    && tttLargeFiber4Block5Chunk2RowCheck 6
    && tttLargeFiber4Block5Chunk2RowCheck 7
    && tttLargeFiber4Block5Chunk2RowCheck 8
    && tttLargeFiber4Block5Chunk2RowCheck 9
    && tttLargeFiber4Block5Chunk2RowCheck 10
    && tttLargeFiber4Block5Chunk2RowCheck 11
    && tttLargeFiber4Block5Chunk2RowCheck 12
    && tttLargeFiber4Block5Chunk2RowCheck 13
    && tttLargeFiber4Block5Chunk2RowCheck 14
    && tttLargeFiber4Block5Chunk2RowCheck 15

theorem tttLargeFiber4Block5Chunk2RowsAudit_ok :
    tttLargeFiber4Block5Chunk2RowsAudit = true := by
  simp [tttLargeFiber4Block5Chunk2RowsAudit,
    tttLargeFiber4Block5Chunk2Row_0_ok,
    tttLargeFiber4Block5Chunk2Row_1_ok,
    tttLargeFiber4Block5Chunk2Row_2_ok,
    tttLargeFiber4Block5Chunk2Row_3_ok,
    tttLargeFiber4Block5Chunk2Row_4_ok,
    tttLargeFiber4Block5Chunk2Row_5_ok,
    tttLargeFiber4Block5Chunk2Row_6_ok,
    tttLargeFiber4Block5Chunk2Row_7_ok,
    tttLargeFiber4Block5Chunk2Row_8_ok,
    tttLargeFiber4Block5Chunk2Row_9_ok,
    tttLargeFiber4Block5Chunk2Row_10_ok,
    tttLargeFiber4Block5Chunk2Row_11_ok,
    tttLargeFiber4Block5Chunk2Row_12_ok,
    tttLargeFiber4Block5Chunk2Row_13_ok,
    tttLargeFiber4Block5Chunk2Row_14_ok,
    tttLargeFiber4Block5Chunk2Row_15_ok]

def tttLargeFiber4Block5Chunk2ParentMapAudit : Bool :=
  tttLargeFiber4Block5Chunk2ParentMapCheck 0
    && tttLargeFiber4Block5Chunk2ParentMapCheck 1
    && tttLargeFiber4Block5Chunk2ParentMapCheck 2
    && tttLargeFiber4Block5Chunk2ParentMapCheck 3
    && tttLargeFiber4Block5Chunk2ParentMapCheck 4
    && tttLargeFiber4Block5Chunk2ParentMapCheck 5
    && tttLargeFiber4Block5Chunk2ParentMapCheck 6
    && tttLargeFiber4Block5Chunk2ParentMapCheck 7
    && tttLargeFiber4Block5Chunk2ParentMapCheck 8
    && tttLargeFiber4Block5Chunk2ParentMapCheck 9
    && tttLargeFiber4Block5Chunk2ParentMapCheck 10
    && tttLargeFiber4Block5Chunk2ParentMapCheck 11
    && tttLargeFiber4Block5Chunk2ParentMapCheck 12
    && tttLargeFiber4Block5Chunk2ParentMapCheck 13
    && tttLargeFiber4Block5Chunk2ParentMapCheck 14
    && tttLargeFiber4Block5Chunk2ParentMapCheck 15

theorem tttLargeFiber4Block5Chunk2ParentMapAudit_ok :
    tttLargeFiber4Block5Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber4Block5Chunk2ParentMapAudit,
    tttLargeFiber4Block5Chunk2ParentMap_0_ok,
    tttLargeFiber4Block5Chunk2ParentMap_1_ok,
    tttLargeFiber4Block5Chunk2ParentMap_2_ok,
    tttLargeFiber4Block5Chunk2ParentMap_3_ok,
    tttLargeFiber4Block5Chunk2ParentMap_4_ok,
    tttLargeFiber4Block5Chunk2ParentMap_5_ok,
    tttLargeFiber4Block5Chunk2ParentMap_6_ok,
    tttLargeFiber4Block5Chunk2ParentMap_7_ok,
    tttLargeFiber4Block5Chunk2ParentMap_8_ok,
    tttLargeFiber4Block5Chunk2ParentMap_9_ok,
    tttLargeFiber4Block5Chunk2ParentMap_10_ok,
    tttLargeFiber4Block5Chunk2ParentMap_11_ok,
    tttLargeFiber4Block5Chunk2ParentMap_12_ok,
    tttLargeFiber4Block5Chunk2ParentMap_13_ok,
    tttLargeFiber4Block5Chunk2ParentMap_14_ok,
    tttLargeFiber4Block5Chunk2ParentMap_15_ok]

def tttLargeFiber4Block5Chunk2ParentsAudit : Bool :=
  tttLargeFiber4Block5Chunk2ParentPathCheck 0
    && tttLargeFiber4Block5Chunk2ParentPathCheck 1
    && tttLargeFiber4Block5Chunk2ParentPathCheck 2
    && tttLargeFiber4Block5Chunk2ParentPathCheck 3
    && tttLargeFiber4Block5Chunk2ParentPathCheck 4
    && tttLargeFiber4Block5Chunk2ParentPathCheck 5
    && tttLargeFiber4Block5Chunk2ParentPathCheck 6
    && tttLargeFiber4Block5Chunk2ParentPathCheck 7
    && tttLargeFiber4Block5Chunk2ParentPathCheck 8
    && tttLargeFiber4Block5Chunk2ParentPathCheck 9
    && tttLargeFiber4Block5Chunk2ParentPathCheck 10
    && tttLargeFiber4Block5Chunk2ParentPathCheck 11
    && tttLargeFiber4Block5Chunk2ParentPathCheck 12
    && tttLargeFiber4Block5Chunk2ParentPathCheck 13
    && tttLargeFiber4Block5Chunk2ParentPathCheck 14
    && tttLargeFiber4Block5Chunk2ParentPathCheck 15

theorem tttLargeFiber4Block5Chunk2ParentsAudit_ok :
    tttLargeFiber4Block5Chunk2ParentsAudit = true := by
  simp [tttLargeFiber4Block5Chunk2ParentsAudit,
    tttLargeFiber4Block5Chunk2ParentPath_0_ok,
    tttLargeFiber4Block5Chunk2ParentPath_1_ok,
    tttLargeFiber4Block5Chunk2ParentPath_2_ok,
    tttLargeFiber4Block5Chunk2ParentPath_3_ok,
    tttLargeFiber4Block5Chunk2ParentPath_4_ok,
    tttLargeFiber4Block5Chunk2ParentPath_5_ok,
    tttLargeFiber4Block5Chunk2ParentPath_6_ok,
    tttLargeFiber4Block5Chunk2ParentPath_7_ok,
    tttLargeFiber4Block5Chunk2ParentPath_8_ok,
    tttLargeFiber4Block5Chunk2ParentPath_9_ok,
    tttLargeFiber4Block5Chunk2ParentPath_10_ok,
    tttLargeFiber4Block5Chunk2ParentPath_11_ok,
    tttLargeFiber4Block5Chunk2ParentPath_12_ok,
    tttLargeFiber4Block5Chunk2ParentPath_13_ok,
    tttLargeFiber4Block5Chunk2ParentPath_14_ok,
    tttLargeFiber4Block5Chunk2ParentPath_15_ok]

def tttLargeFiber4Block5Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block5Chunk2SourcesCheck &&
    tttLargeFiber4Block5Chunk2RowsAudit &&
    tttLargeFiber4Block5Chunk2ParentMapAudit &&
    tttLargeFiber4Block5Chunk2ParentsAudit

theorem tttLargeFiber4Block5Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber4Block5Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block5Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block5Chunk2SourcesCheck_ok,
    tttLargeFiber4Block5Chunk2RowsAudit_ok,
    tttLargeFiber4Block5Chunk2ParentMapAudit_ok,
    tttLargeFiber4Block5Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block5Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
