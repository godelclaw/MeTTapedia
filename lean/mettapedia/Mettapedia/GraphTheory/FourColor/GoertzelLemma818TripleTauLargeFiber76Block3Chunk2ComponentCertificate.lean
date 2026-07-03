import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber76Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 76, block 3 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber76Block3Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber76Data

def tttLargeFiber76Block3Chunk2Sources : List Nat :=
  [   3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223,
   3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231]

def tttLargeFiber76Row224 : TripleComponentParentRow :=
  tripleRow 3216 3184 91 40 148 91 24 80
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row225 : TripleComponentParentRow :=
  tripleRow 3217 3185 91 40 149 91 24 81
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row226 : TripleComponentParentRow :=
  tripleRow 3218 3186 91 40 150 91 24 82
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber76Row227 : TripleComponentParentRow :=
  tripleRow 3219 3216 91 40 151 91 40 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row228 : TripleComponentParentRow :=
  tripleRow 3220 3216 91 40 164 91 40 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber76Row229 : TripleComponentParentRow :=
  tripleRow 3221 3217 91 40 165 91 40 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber76Row230 : TripleComponentParentRow :=
  tripleRow 3222 3190 91 40 166 91 24 102
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber76Row231 : TripleComponentParentRow :=
  tripleRow 3223 3191 91 40 167 91 24 103
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber76Row232 : TripleComponentParentRow :=
  tripleRow 3224 3192 91 41 156 91 25 88
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row233 : TripleComponentParentRow :=
  tripleRow 3225 3193 91 41 157 91 25 89
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row234 : TripleComponentParentRow :=
  tripleRow 3226 3194 91 41 158 91 25 90
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
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

def tttLargeFiber76Row235 : TripleComponentParentRow :=
  tripleRow 3227 3224 91 41 159 91 41 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row236 : TripleComponentParentRow :=
  tripleRow 3228 3224 91 41 172 91 41 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber76Row237 : TripleComponentParentRow :=
  tripleRow 3229 3225 91 41 173 91 41 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber76Row238 : TripleComponentParentRow :=
  tripleRow 3230 3198 91 41 174 91 25 110
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber76Row239 : TripleComponentParentRow :=
  tripleRow 3231 3199 91 41 175 91 25 111
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber76Block3Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber76Row224
  , tttLargeFiber76Row225
  , tttLargeFiber76Row226
  , tttLargeFiber76Row227
  , tttLargeFiber76Row228
  , tttLargeFiber76Row229
  , tttLargeFiber76Row230
  , tttLargeFiber76Row231
  , tttLargeFiber76Row232
  , tttLargeFiber76Row233
  , tttLargeFiber76Row234
  , tttLargeFiber76Row235
  , tttLargeFiber76Row236
  , tttLargeFiber76Row237
  , tttLargeFiber76Row238
  , tttLargeFiber76Row239
  ]

def tttLargeFiber76Block3Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (2992 <= i) && decide (i < 3248)) ||
    (decide (3552 <= i) && decide (i < 3808))

def tttLargeFiber76Block3Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber76Block3Chunk2ExpectedContains row.source &&
    tttLargeFiber76Block3Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber76Key &&
          chainInputKey tttWord t == tttLargeFiber76Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber76Block3Chunk2SourcesCheck : Bool :=
  (tttLargeFiber76Block3Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber76Block3Chunk2Sources

theorem tttLargeFiber76Block3Chunk2SourcesCheck_ok :
    tttLargeFiber76Block3Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber76Block3Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber76Block3Chunk2RowValid
    (listGetD tttLargeFiber76Block3Chunk2Rows i default)

def tttLargeFiber76Block3Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber76Block3Chunk2Rows i default
  row.parent == tttLargeFiber76ParentOf row.source

def tttLargeFiber76Block3Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber76Block3Chunk2Sources 0 0 == 3216
      && tttLargeFiber76ParentOf 3216 == 3184
      && tttLargeFiber76ParentOf 3184 == 3056
      && tttLargeFiber76ParentOf 3056 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 1 => listGetD tttLargeFiber76Block3Chunk2Sources 1 0 == 3217
      && tttLargeFiber76ParentOf 3217 == 3185
      && tttLargeFiber76ParentOf 3185 == 3057
      && tttLargeFiber76ParentOf 3057 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 2 => listGetD tttLargeFiber76Block3Chunk2Sources 2 0 == 3218
      && tttLargeFiber76ParentOf 3218 == 3186
      && tttLargeFiber76ParentOf 3186 == 3058
      && tttLargeFiber76ParentOf 3058 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 3 => listGetD tttLargeFiber76Block3Chunk2Sources 3 0 == 3219
      && tttLargeFiber76ParentOf 3219 == 3216
      && tttLargeFiber76ParentOf 3216 == 3184
      && tttLargeFiber76ParentOf 3184 == 3056
      && tttLargeFiber76ParentOf 3056 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 4 => listGetD tttLargeFiber76Block3Chunk2Sources 4 0 == 3220
      && tttLargeFiber76ParentOf 3220 == 3216
      && tttLargeFiber76ParentOf 3216 == 3184
      && tttLargeFiber76ParentOf 3184 == 3056
      && tttLargeFiber76ParentOf 3056 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 5 => listGetD tttLargeFiber76Block3Chunk2Sources 5 0 == 3221
      && tttLargeFiber76ParentOf 3221 == 3217
      && tttLargeFiber76ParentOf 3217 == 3185
      && tttLargeFiber76ParentOf 3185 == 3057
      && tttLargeFiber76ParentOf 3057 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 6 => listGetD tttLargeFiber76Block3Chunk2Sources 6 0 == 3222
      && tttLargeFiber76ParentOf 3222 == 3190
      && tttLargeFiber76ParentOf 3190 == 3062
      && tttLargeFiber76ParentOf 3062 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 7 => listGetD tttLargeFiber76Block3Chunk2Sources 7 0 == 3223
      && tttLargeFiber76ParentOf 3223 == 3191
      && tttLargeFiber76ParentOf 3191 == 3063
      && tttLargeFiber76ParentOf 3063 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 8 => listGetD tttLargeFiber76Block3Chunk2Sources 8 0 == 3224
      && tttLargeFiber76ParentOf 3224 == 3192
      && tttLargeFiber76ParentOf 3192 == 3064
      && tttLargeFiber76ParentOf 3064 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 9 => listGetD tttLargeFiber76Block3Chunk2Sources 9 0 == 3225
      && tttLargeFiber76ParentOf 3225 == 3193
      && tttLargeFiber76ParentOf 3193 == 3065
      && tttLargeFiber76ParentOf 3065 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 10 => listGetD tttLargeFiber76Block3Chunk2Sources 10 0 == 3226
      && tttLargeFiber76ParentOf 3226 == 3194
      && tttLargeFiber76ParentOf 3194 == 3066
      && tttLargeFiber76ParentOf 3066 == 3002
      && tttLargeFiber76ParentOf 3002 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 11 => listGetD tttLargeFiber76Block3Chunk2Sources 11 0 == 3227
      && tttLargeFiber76ParentOf 3227 == 3224
      && tttLargeFiber76ParentOf 3224 == 3192
      && tttLargeFiber76ParentOf 3192 == 3064
      && tttLargeFiber76ParentOf 3064 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 12 => listGetD tttLargeFiber76Block3Chunk2Sources 12 0 == 3228
      && tttLargeFiber76ParentOf 3228 == 3224
      && tttLargeFiber76ParentOf 3224 == 3192
      && tttLargeFiber76ParentOf 3192 == 3064
      && tttLargeFiber76ParentOf 3064 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 13 => listGetD tttLargeFiber76Block3Chunk2Sources 13 0 == 3229
      && tttLargeFiber76ParentOf 3229 == 3225
      && tttLargeFiber76ParentOf 3225 == 3193
      && tttLargeFiber76ParentOf 3193 == 3065
      && tttLargeFiber76ParentOf 3065 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (6 <= tttLargeFiber76MaxParentDepth)
  | 14 => listGetD tttLargeFiber76Block3Chunk2Sources 14 0 == 3230
      && tttLargeFiber76ParentOf 3230 == 3198
      && tttLargeFiber76ParentOf 3198 == 3070
      && tttLargeFiber76ParentOf 3070 == 3006
      && tttLargeFiber76ParentOf 3006 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (6 <= tttLargeFiber76MaxParentDepth)
  | 15 => listGetD tttLargeFiber76Block3Chunk2Sources 15 0 == 3231
      && tttLargeFiber76ParentOf 3231 == 3199
      && tttLargeFiber76ParentOf 3199 == 3071
      && tttLargeFiber76ParentOf 3071 == 3007
      && tttLargeFiber76ParentOf 3007 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | _ => false

theorem tttLargeFiber76Block3Chunk2Row_0_ok :
    tttLargeFiber76Block3Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2Row_1_ok :
    tttLargeFiber76Block3Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2Row_2_ok :
    tttLargeFiber76Block3Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2Row_3_ok :
    tttLargeFiber76Block3Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2Row_4_ok :
    tttLargeFiber76Block3Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2Row_5_ok :
    tttLargeFiber76Block3Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2Row_6_ok :
    tttLargeFiber76Block3Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2Row_7_ok :
    tttLargeFiber76Block3Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2Row_8_ok :
    tttLargeFiber76Block3Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2Row_9_ok :
    tttLargeFiber76Block3Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2Row_10_ok :
    tttLargeFiber76Block3Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2Row_11_ok :
    tttLargeFiber76Block3Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2Row_12_ok :
    tttLargeFiber76Block3Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2Row_13_ok :
    tttLargeFiber76Block3Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2Row_14_ok :
    tttLargeFiber76Block3Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2Row_15_ok :
    tttLargeFiber76Block3Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentMap_0_ok :
    tttLargeFiber76Block3Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentMap_1_ok :
    tttLargeFiber76Block3Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentMap_2_ok :
    tttLargeFiber76Block3Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentMap_3_ok :
    tttLargeFiber76Block3Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentMap_4_ok :
    tttLargeFiber76Block3Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentMap_5_ok :
    tttLargeFiber76Block3Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentMap_6_ok :
    tttLargeFiber76Block3Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentMap_7_ok :
    tttLargeFiber76Block3Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentMap_8_ok :
    tttLargeFiber76Block3Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentMap_9_ok :
    tttLargeFiber76Block3Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentMap_10_ok :
    tttLargeFiber76Block3Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentMap_11_ok :
    tttLargeFiber76Block3Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentMap_12_ok :
    tttLargeFiber76Block3Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentMap_13_ok :
    tttLargeFiber76Block3Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentMap_14_ok :
    tttLargeFiber76Block3Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentMap_15_ok :
    tttLargeFiber76Block3Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentPath_0_ok :
    tttLargeFiber76Block3Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentPath_1_ok :
    tttLargeFiber76Block3Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentPath_2_ok :
    tttLargeFiber76Block3Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentPath_3_ok :
    tttLargeFiber76Block3Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentPath_4_ok :
    tttLargeFiber76Block3Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentPath_5_ok :
    tttLargeFiber76Block3Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentPath_6_ok :
    tttLargeFiber76Block3Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentPath_7_ok :
    tttLargeFiber76Block3Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentPath_8_ok :
    tttLargeFiber76Block3Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentPath_9_ok :
    tttLargeFiber76Block3Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentPath_10_ok :
    tttLargeFiber76Block3Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentPath_11_ok :
    tttLargeFiber76Block3Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentPath_12_ok :
    tttLargeFiber76Block3Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentPath_13_ok :
    tttLargeFiber76Block3Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentPath_14_ok :
    tttLargeFiber76Block3Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber76Block3Chunk2ParentPath_15_ok :
    tttLargeFiber76Block3Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber76Block3Chunk2RowsAudit : Bool :=
  tttLargeFiber76Block3Chunk2RowCheck 0
    && tttLargeFiber76Block3Chunk2RowCheck 1
    && tttLargeFiber76Block3Chunk2RowCheck 2
    && tttLargeFiber76Block3Chunk2RowCheck 3
    && tttLargeFiber76Block3Chunk2RowCheck 4
    && tttLargeFiber76Block3Chunk2RowCheck 5
    && tttLargeFiber76Block3Chunk2RowCheck 6
    && tttLargeFiber76Block3Chunk2RowCheck 7
    && tttLargeFiber76Block3Chunk2RowCheck 8
    && tttLargeFiber76Block3Chunk2RowCheck 9
    && tttLargeFiber76Block3Chunk2RowCheck 10
    && tttLargeFiber76Block3Chunk2RowCheck 11
    && tttLargeFiber76Block3Chunk2RowCheck 12
    && tttLargeFiber76Block3Chunk2RowCheck 13
    && tttLargeFiber76Block3Chunk2RowCheck 14
    && tttLargeFiber76Block3Chunk2RowCheck 15

theorem tttLargeFiber76Block3Chunk2RowsAudit_ok :
    tttLargeFiber76Block3Chunk2RowsAudit = true := by
  simp [tttLargeFiber76Block3Chunk2RowsAudit,
    tttLargeFiber76Block3Chunk2Row_0_ok,
    tttLargeFiber76Block3Chunk2Row_1_ok,
    tttLargeFiber76Block3Chunk2Row_2_ok,
    tttLargeFiber76Block3Chunk2Row_3_ok,
    tttLargeFiber76Block3Chunk2Row_4_ok,
    tttLargeFiber76Block3Chunk2Row_5_ok,
    tttLargeFiber76Block3Chunk2Row_6_ok,
    tttLargeFiber76Block3Chunk2Row_7_ok,
    tttLargeFiber76Block3Chunk2Row_8_ok,
    tttLargeFiber76Block3Chunk2Row_9_ok,
    tttLargeFiber76Block3Chunk2Row_10_ok,
    tttLargeFiber76Block3Chunk2Row_11_ok,
    tttLargeFiber76Block3Chunk2Row_12_ok,
    tttLargeFiber76Block3Chunk2Row_13_ok,
    tttLargeFiber76Block3Chunk2Row_14_ok,
    tttLargeFiber76Block3Chunk2Row_15_ok]

def tttLargeFiber76Block3Chunk2ParentMapAudit : Bool :=
  tttLargeFiber76Block3Chunk2ParentMapCheck 0
    && tttLargeFiber76Block3Chunk2ParentMapCheck 1
    && tttLargeFiber76Block3Chunk2ParentMapCheck 2
    && tttLargeFiber76Block3Chunk2ParentMapCheck 3
    && tttLargeFiber76Block3Chunk2ParentMapCheck 4
    && tttLargeFiber76Block3Chunk2ParentMapCheck 5
    && tttLargeFiber76Block3Chunk2ParentMapCheck 6
    && tttLargeFiber76Block3Chunk2ParentMapCheck 7
    && tttLargeFiber76Block3Chunk2ParentMapCheck 8
    && tttLargeFiber76Block3Chunk2ParentMapCheck 9
    && tttLargeFiber76Block3Chunk2ParentMapCheck 10
    && tttLargeFiber76Block3Chunk2ParentMapCheck 11
    && tttLargeFiber76Block3Chunk2ParentMapCheck 12
    && tttLargeFiber76Block3Chunk2ParentMapCheck 13
    && tttLargeFiber76Block3Chunk2ParentMapCheck 14
    && tttLargeFiber76Block3Chunk2ParentMapCheck 15

theorem tttLargeFiber76Block3Chunk2ParentMapAudit_ok :
    tttLargeFiber76Block3Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber76Block3Chunk2ParentMapAudit,
    tttLargeFiber76Block3Chunk2ParentMap_0_ok,
    tttLargeFiber76Block3Chunk2ParentMap_1_ok,
    tttLargeFiber76Block3Chunk2ParentMap_2_ok,
    tttLargeFiber76Block3Chunk2ParentMap_3_ok,
    tttLargeFiber76Block3Chunk2ParentMap_4_ok,
    tttLargeFiber76Block3Chunk2ParentMap_5_ok,
    tttLargeFiber76Block3Chunk2ParentMap_6_ok,
    tttLargeFiber76Block3Chunk2ParentMap_7_ok,
    tttLargeFiber76Block3Chunk2ParentMap_8_ok,
    tttLargeFiber76Block3Chunk2ParentMap_9_ok,
    tttLargeFiber76Block3Chunk2ParentMap_10_ok,
    tttLargeFiber76Block3Chunk2ParentMap_11_ok,
    tttLargeFiber76Block3Chunk2ParentMap_12_ok,
    tttLargeFiber76Block3Chunk2ParentMap_13_ok,
    tttLargeFiber76Block3Chunk2ParentMap_14_ok,
    tttLargeFiber76Block3Chunk2ParentMap_15_ok]

def tttLargeFiber76Block3Chunk2ParentsAudit : Bool :=
  tttLargeFiber76Block3Chunk2ParentPathCheck 0
    && tttLargeFiber76Block3Chunk2ParentPathCheck 1
    && tttLargeFiber76Block3Chunk2ParentPathCheck 2
    && tttLargeFiber76Block3Chunk2ParentPathCheck 3
    && tttLargeFiber76Block3Chunk2ParentPathCheck 4
    && tttLargeFiber76Block3Chunk2ParentPathCheck 5
    && tttLargeFiber76Block3Chunk2ParentPathCheck 6
    && tttLargeFiber76Block3Chunk2ParentPathCheck 7
    && tttLargeFiber76Block3Chunk2ParentPathCheck 8
    && tttLargeFiber76Block3Chunk2ParentPathCheck 9
    && tttLargeFiber76Block3Chunk2ParentPathCheck 10
    && tttLargeFiber76Block3Chunk2ParentPathCheck 11
    && tttLargeFiber76Block3Chunk2ParentPathCheck 12
    && tttLargeFiber76Block3Chunk2ParentPathCheck 13
    && tttLargeFiber76Block3Chunk2ParentPathCheck 14
    && tttLargeFiber76Block3Chunk2ParentPathCheck 15

theorem tttLargeFiber76Block3Chunk2ParentsAudit_ok :
    tttLargeFiber76Block3Chunk2ParentsAudit = true := by
  simp [tttLargeFiber76Block3Chunk2ParentsAudit,
    tttLargeFiber76Block3Chunk2ParentPath_0_ok,
    tttLargeFiber76Block3Chunk2ParentPath_1_ok,
    tttLargeFiber76Block3Chunk2ParentPath_2_ok,
    tttLargeFiber76Block3Chunk2ParentPath_3_ok,
    tttLargeFiber76Block3Chunk2ParentPath_4_ok,
    tttLargeFiber76Block3Chunk2ParentPath_5_ok,
    tttLargeFiber76Block3Chunk2ParentPath_6_ok,
    tttLargeFiber76Block3Chunk2ParentPath_7_ok,
    tttLargeFiber76Block3Chunk2ParentPath_8_ok,
    tttLargeFiber76Block3Chunk2ParentPath_9_ok,
    tttLargeFiber76Block3Chunk2ParentPath_10_ok,
    tttLargeFiber76Block3Chunk2ParentPath_11_ok,
    tttLargeFiber76Block3Chunk2ParentPath_12_ok,
    tttLargeFiber76Block3Chunk2ParentPath_13_ok,
    tttLargeFiber76Block3Chunk2ParentPath_14_ok,
    tttLargeFiber76Block3Chunk2ParentPath_15_ok]

def tttLargeFiber76Block3Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber76CountsAudit &&
    tttLargeFiber76Block3Chunk2SourcesCheck &&
    tttLargeFiber76Block3Chunk2RowsAudit &&
    tttLargeFiber76Block3Chunk2ParentMapAudit &&
    tttLargeFiber76Block3Chunk2ParentsAudit

theorem tttLargeFiber76Block3Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber76Block3Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber76Block3Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber76CountsAudit_ok,
    tttLargeFiber76Block3Chunk2SourcesCheck_ok,
    tttLargeFiber76Block3Chunk2RowsAudit_ok,
    tttLargeFiber76Block3Chunk2ParentMapAudit_ok,
    tttLargeFiber76Block3Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber76Block3Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
