import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber76Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 76, block 3 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber76Block3Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber76Data

def tttLargeFiber76Block3Chunk3Sources : List Nat :=
  [   3232, 3233, 3234, 3235, 3236, 3237, 3238, 3239,
   3240, 3241, 3242, 3243, 3244, 3245, 3246, 3247]

def tttLargeFiber76Row240 : TripleComponentParentRow :=
  tripleRow 3232 3104 91 42 0 89 110 64
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber76Row241 : TripleComponentParentRow :=
  tripleRow 3233 3105 91 42 1 89 110 65
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber76Row242 : TripleComponentParentRow :=
  tripleRow 3234 3106 91 42 2 89 110 66
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber76Row243 : TripleComponentParentRow :=
  tripleRow 3235 3107 91 42 3 89 110 67
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber76Row244 : TripleComponentParentRow :=
  tripleRow 3236 3232 91 42 48 91 42 0
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row245 : TripleComponentParentRow :=
  tripleRow 3237 3233 91 42 49 91 42 1
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row246 : TripleComponentParentRow :=
  tripleRow 3238 3110 91 42 50 89 110 118
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber76Row247 : TripleComponentParentRow :=
  tripleRow 3239 3111 91 42 51 89 110 119
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber76Row248 : TripleComponentParentRow :=
  tripleRow 3240 3112 91 43 8 89 111 72
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber76Row249 : TripleComponentParentRow :=
  tripleRow 3241 3113 91 43 9 89 111 73
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber76Row250 : TripleComponentParentRow :=
  tripleRow 3242 3114 91 43 10 89 111 74
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber76Row251 : TripleComponentParentRow :=
  tripleRow 3243 3115 91 43 11 89 111 75
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
    , chainEdge 0 TauEdge.B7
    , chainEdge 1 TauEdge.F1F0
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F0F2
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 1 TauEdge.B7
    ]

def tttLargeFiber76Row252 : TripleComponentParentRow :=
  tripleRow 3244 3240 91 43 56 91 43 8
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row253 : TripleComponentParentRow :=
  tripleRow 3245 3241 91 43 57 91 43 9
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row254 : TripleComponentParentRow :=
  tripleRow 3246 3118 91 43 58 89 111 126
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber76Row255 : TripleComponentParentRow :=
  tripleRow 3247 3119 91 43 59 89 111 127
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
    [ chainEdge 0 TauEdge.F4F5
    , chainEdge 0 TauEdge.B6
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

def tttLargeFiber76Block3Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber76Row240
  , tttLargeFiber76Row241
  , tttLargeFiber76Row242
  , tttLargeFiber76Row243
  , tttLargeFiber76Row244
  , tttLargeFiber76Row245
  , tttLargeFiber76Row246
  , tttLargeFiber76Row247
  , tttLargeFiber76Row248
  , tttLargeFiber76Row249
  , tttLargeFiber76Row250
  , tttLargeFiber76Row251
  , tttLargeFiber76Row252
  , tttLargeFiber76Row253
  , tttLargeFiber76Row254
  , tttLargeFiber76Row255
  ]

def tttLargeFiber76Block3Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (2992 <= i) && decide (i < 3248)) ||
    (decide (3552 <= i) && decide (i < 3808))

def tttLargeFiber76Block3Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber76Block3Chunk3ExpectedContains row.source &&
    tttLargeFiber76Block3Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber76Key &&
          chainInputKey tttWord t == tttLargeFiber76Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber76Block3Chunk3SourcesCheck : Bool :=
  (tttLargeFiber76Block3Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber76Block3Chunk3Sources

theorem tttLargeFiber76Block3Chunk3SourcesCheck_ok :
    tttLargeFiber76Block3Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber76Block3Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber76Block3Chunk3RowValid
    (listGetD tttLargeFiber76Block3Chunk3Rows i default)

def tttLargeFiber76Block3Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber76Block3Chunk3Rows i default
  row.parent == tttLargeFiber76ParentOf row.source

def tttLargeFiber76Block3Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber76Block3Chunk3Sources 0 0 == 3232
      && tttLargeFiber76ParentOf 3232 == 3104
      && tttLargeFiber76ParentOf 3104 == 3040
      && tttLargeFiber76ParentOf 3040 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 1 => listGetD tttLargeFiber76Block3Chunk3Sources 1 0 == 3233
      && tttLargeFiber76ParentOf 3233 == 3105
      && tttLargeFiber76ParentOf 3105 == 3041
      && tttLargeFiber76ParentOf 3041 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 2 => listGetD tttLargeFiber76Block3Chunk3Sources 2 0 == 3234
      && tttLargeFiber76ParentOf 3234 == 3106
      && tttLargeFiber76ParentOf 3106 == 3042
      && tttLargeFiber76ParentOf 3042 == 3002
      && tttLargeFiber76ParentOf 3002 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 3 => listGetD tttLargeFiber76Block3Chunk3Sources 3 0 == 3235
      && tttLargeFiber76ParentOf 3235 == 3107
      && tttLargeFiber76ParentOf 3107 == 3043
      && tttLargeFiber76ParentOf 3043 == 3003
      && tttLargeFiber76ParentOf 3003 == 2995
      && tttLargeFiber76ParentOf 2995 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (6 <= tttLargeFiber76MaxParentDepth)
  | 4 => listGetD tttLargeFiber76Block3Chunk3Sources 4 0 == 3236
      && tttLargeFiber76ParentOf 3236 == 3232
      && tttLargeFiber76ParentOf 3232 == 3104
      && tttLargeFiber76ParentOf 3104 == 3040
      && tttLargeFiber76ParentOf 3040 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 5 => listGetD tttLargeFiber76Block3Chunk3Sources 5 0 == 3237
      && tttLargeFiber76ParentOf 3237 == 3233
      && tttLargeFiber76ParentOf 3233 == 3105
      && tttLargeFiber76ParentOf 3105 == 3041
      && tttLargeFiber76ParentOf 3041 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (6 <= tttLargeFiber76MaxParentDepth)
  | 6 => listGetD tttLargeFiber76Block3Chunk3Sources 6 0 == 3238
      && tttLargeFiber76ParentOf 3238 == 3110
      && tttLargeFiber76ParentOf 3110 == 3046
      && tttLargeFiber76ParentOf 3046 == 3006
      && tttLargeFiber76ParentOf 3006 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (6 <= tttLargeFiber76MaxParentDepth)
  | 7 => listGetD tttLargeFiber76Block3Chunk3Sources 7 0 == 3239
      && tttLargeFiber76ParentOf 3239 == 3111
      && tttLargeFiber76ParentOf 3111 == 3047
      && tttLargeFiber76ParentOf 3047 == 3007
      && tttLargeFiber76ParentOf 3007 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 8 => listGetD tttLargeFiber76Block3Chunk3Sources 8 0 == 3240
      && tttLargeFiber76ParentOf 3240 == 3112
      && tttLargeFiber76ParentOf 3112 == 3048
      && tttLargeFiber76ParentOf 3048 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 9 => listGetD tttLargeFiber76Block3Chunk3Sources 9 0 == 3241
      && tttLargeFiber76ParentOf 3241 == 3113
      && tttLargeFiber76ParentOf 3113 == 3049
      && tttLargeFiber76ParentOf 3049 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 10 => listGetD tttLargeFiber76Block3Chunk3Sources 10 0 == 3242
      && tttLargeFiber76ParentOf 3242 == 3114
      && tttLargeFiber76ParentOf 3114 == 3050
      && tttLargeFiber76ParentOf 3050 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 11 => listGetD tttLargeFiber76Block3Chunk3Sources 11 0 == 3243
      && tttLargeFiber76ParentOf 3243 == 3115
      && tttLargeFiber76ParentOf 3115 == 3051
      && tttLargeFiber76ParentOf 3051 == 2995
      && tttLargeFiber76ParentOf 2995 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 12 => listGetD tttLargeFiber76Block3Chunk3Sources 12 0 == 3244
      && tttLargeFiber76ParentOf 3244 == 3240
      && tttLargeFiber76ParentOf 3240 == 3112
      && tttLargeFiber76ParentOf 3112 == 3048
      && tttLargeFiber76ParentOf 3048 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 13 => listGetD tttLargeFiber76Block3Chunk3Sources 13 0 == 3245
      && tttLargeFiber76ParentOf 3245 == 3241
      && tttLargeFiber76ParentOf 3241 == 3113
      && tttLargeFiber76ParentOf 3113 == 3049
      && tttLargeFiber76ParentOf 3049 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 14 => listGetD tttLargeFiber76Block3Chunk3Sources 14 0 == 3246
      && tttLargeFiber76ParentOf 3246 == 3118
      && tttLargeFiber76ParentOf 3118 == 3054
      && tttLargeFiber76ParentOf 3054 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 15 => listGetD tttLargeFiber76Block3Chunk3Sources 15 0 == 3247
      && tttLargeFiber76ParentOf 3247 == 3119
      && tttLargeFiber76ParentOf 3119 == 3055
      && tttLargeFiber76ParentOf 3055 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | _ => false

theorem tttLargeFiber76Block3Chunk3Row_0_ok :
    tttLargeFiber76Block3Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3Row_1_ok :
    tttLargeFiber76Block3Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3Row_2_ok :
    tttLargeFiber76Block3Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3Row_3_ok :
    tttLargeFiber76Block3Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3Row_4_ok :
    tttLargeFiber76Block3Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3Row_5_ok :
    tttLargeFiber76Block3Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3Row_6_ok :
    tttLargeFiber76Block3Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3Row_7_ok :
    tttLargeFiber76Block3Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3Row_8_ok :
    tttLargeFiber76Block3Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3Row_9_ok :
    tttLargeFiber76Block3Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3Row_10_ok :
    tttLargeFiber76Block3Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3Row_11_ok :
    tttLargeFiber76Block3Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3Row_12_ok :
    tttLargeFiber76Block3Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3Row_13_ok :
    tttLargeFiber76Block3Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3Row_14_ok :
    tttLargeFiber76Block3Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3Row_15_ok :
    tttLargeFiber76Block3Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentMap_0_ok :
    tttLargeFiber76Block3Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentMap_1_ok :
    tttLargeFiber76Block3Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentMap_2_ok :
    tttLargeFiber76Block3Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentMap_3_ok :
    tttLargeFiber76Block3Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentMap_4_ok :
    tttLargeFiber76Block3Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentMap_5_ok :
    tttLargeFiber76Block3Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentMap_6_ok :
    tttLargeFiber76Block3Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentMap_7_ok :
    tttLargeFiber76Block3Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentMap_8_ok :
    tttLargeFiber76Block3Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentMap_9_ok :
    tttLargeFiber76Block3Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentMap_10_ok :
    tttLargeFiber76Block3Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentMap_11_ok :
    tttLargeFiber76Block3Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentMap_12_ok :
    tttLargeFiber76Block3Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentMap_13_ok :
    tttLargeFiber76Block3Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentMap_14_ok :
    tttLargeFiber76Block3Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentMap_15_ok :
    tttLargeFiber76Block3Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentPath_0_ok :
    tttLargeFiber76Block3Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentPath_1_ok :
    tttLargeFiber76Block3Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentPath_2_ok :
    tttLargeFiber76Block3Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentPath_3_ok :
    tttLargeFiber76Block3Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentPath_4_ok :
    tttLargeFiber76Block3Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentPath_5_ok :
    tttLargeFiber76Block3Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentPath_6_ok :
    tttLargeFiber76Block3Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentPath_7_ok :
    tttLargeFiber76Block3Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentPath_8_ok :
    tttLargeFiber76Block3Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentPath_9_ok :
    tttLargeFiber76Block3Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentPath_10_ok :
    tttLargeFiber76Block3Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentPath_11_ok :
    tttLargeFiber76Block3Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentPath_12_ok :
    tttLargeFiber76Block3Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentPath_13_ok :
    tttLargeFiber76Block3Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentPath_14_ok :
    tttLargeFiber76Block3Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber76Block3Chunk3ParentPath_15_ok :
    tttLargeFiber76Block3Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber76Block3Chunk3RowsAudit : Bool :=
  tttLargeFiber76Block3Chunk3RowCheck 0
    && tttLargeFiber76Block3Chunk3RowCheck 1
    && tttLargeFiber76Block3Chunk3RowCheck 2
    && tttLargeFiber76Block3Chunk3RowCheck 3
    && tttLargeFiber76Block3Chunk3RowCheck 4
    && tttLargeFiber76Block3Chunk3RowCheck 5
    && tttLargeFiber76Block3Chunk3RowCheck 6
    && tttLargeFiber76Block3Chunk3RowCheck 7
    && tttLargeFiber76Block3Chunk3RowCheck 8
    && tttLargeFiber76Block3Chunk3RowCheck 9
    && tttLargeFiber76Block3Chunk3RowCheck 10
    && tttLargeFiber76Block3Chunk3RowCheck 11
    && tttLargeFiber76Block3Chunk3RowCheck 12
    && tttLargeFiber76Block3Chunk3RowCheck 13
    && tttLargeFiber76Block3Chunk3RowCheck 14
    && tttLargeFiber76Block3Chunk3RowCheck 15

theorem tttLargeFiber76Block3Chunk3RowsAudit_ok :
    tttLargeFiber76Block3Chunk3RowsAudit = true := by
  simp [tttLargeFiber76Block3Chunk3RowsAudit,
    tttLargeFiber76Block3Chunk3Row_0_ok,
    tttLargeFiber76Block3Chunk3Row_1_ok,
    tttLargeFiber76Block3Chunk3Row_2_ok,
    tttLargeFiber76Block3Chunk3Row_3_ok,
    tttLargeFiber76Block3Chunk3Row_4_ok,
    tttLargeFiber76Block3Chunk3Row_5_ok,
    tttLargeFiber76Block3Chunk3Row_6_ok,
    tttLargeFiber76Block3Chunk3Row_7_ok,
    tttLargeFiber76Block3Chunk3Row_8_ok,
    tttLargeFiber76Block3Chunk3Row_9_ok,
    tttLargeFiber76Block3Chunk3Row_10_ok,
    tttLargeFiber76Block3Chunk3Row_11_ok,
    tttLargeFiber76Block3Chunk3Row_12_ok,
    tttLargeFiber76Block3Chunk3Row_13_ok,
    tttLargeFiber76Block3Chunk3Row_14_ok,
    tttLargeFiber76Block3Chunk3Row_15_ok]

def tttLargeFiber76Block3Chunk3ParentMapAudit : Bool :=
  tttLargeFiber76Block3Chunk3ParentMapCheck 0
    && tttLargeFiber76Block3Chunk3ParentMapCheck 1
    && tttLargeFiber76Block3Chunk3ParentMapCheck 2
    && tttLargeFiber76Block3Chunk3ParentMapCheck 3
    && tttLargeFiber76Block3Chunk3ParentMapCheck 4
    && tttLargeFiber76Block3Chunk3ParentMapCheck 5
    && tttLargeFiber76Block3Chunk3ParentMapCheck 6
    && tttLargeFiber76Block3Chunk3ParentMapCheck 7
    && tttLargeFiber76Block3Chunk3ParentMapCheck 8
    && tttLargeFiber76Block3Chunk3ParentMapCheck 9
    && tttLargeFiber76Block3Chunk3ParentMapCheck 10
    && tttLargeFiber76Block3Chunk3ParentMapCheck 11
    && tttLargeFiber76Block3Chunk3ParentMapCheck 12
    && tttLargeFiber76Block3Chunk3ParentMapCheck 13
    && tttLargeFiber76Block3Chunk3ParentMapCheck 14
    && tttLargeFiber76Block3Chunk3ParentMapCheck 15

theorem tttLargeFiber76Block3Chunk3ParentMapAudit_ok :
    tttLargeFiber76Block3Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber76Block3Chunk3ParentMapAudit,
    tttLargeFiber76Block3Chunk3ParentMap_0_ok,
    tttLargeFiber76Block3Chunk3ParentMap_1_ok,
    tttLargeFiber76Block3Chunk3ParentMap_2_ok,
    tttLargeFiber76Block3Chunk3ParentMap_3_ok,
    tttLargeFiber76Block3Chunk3ParentMap_4_ok,
    tttLargeFiber76Block3Chunk3ParentMap_5_ok,
    tttLargeFiber76Block3Chunk3ParentMap_6_ok,
    tttLargeFiber76Block3Chunk3ParentMap_7_ok,
    tttLargeFiber76Block3Chunk3ParentMap_8_ok,
    tttLargeFiber76Block3Chunk3ParentMap_9_ok,
    tttLargeFiber76Block3Chunk3ParentMap_10_ok,
    tttLargeFiber76Block3Chunk3ParentMap_11_ok,
    tttLargeFiber76Block3Chunk3ParentMap_12_ok,
    tttLargeFiber76Block3Chunk3ParentMap_13_ok,
    tttLargeFiber76Block3Chunk3ParentMap_14_ok,
    tttLargeFiber76Block3Chunk3ParentMap_15_ok]

def tttLargeFiber76Block3Chunk3ParentsAudit : Bool :=
  tttLargeFiber76Block3Chunk3ParentPathCheck 0
    && tttLargeFiber76Block3Chunk3ParentPathCheck 1
    && tttLargeFiber76Block3Chunk3ParentPathCheck 2
    && tttLargeFiber76Block3Chunk3ParentPathCheck 3
    && tttLargeFiber76Block3Chunk3ParentPathCheck 4
    && tttLargeFiber76Block3Chunk3ParentPathCheck 5
    && tttLargeFiber76Block3Chunk3ParentPathCheck 6
    && tttLargeFiber76Block3Chunk3ParentPathCheck 7
    && tttLargeFiber76Block3Chunk3ParentPathCheck 8
    && tttLargeFiber76Block3Chunk3ParentPathCheck 9
    && tttLargeFiber76Block3Chunk3ParentPathCheck 10
    && tttLargeFiber76Block3Chunk3ParentPathCheck 11
    && tttLargeFiber76Block3Chunk3ParentPathCheck 12
    && tttLargeFiber76Block3Chunk3ParentPathCheck 13
    && tttLargeFiber76Block3Chunk3ParentPathCheck 14
    && tttLargeFiber76Block3Chunk3ParentPathCheck 15

theorem tttLargeFiber76Block3Chunk3ParentsAudit_ok :
    tttLargeFiber76Block3Chunk3ParentsAudit = true := by
  simp [tttLargeFiber76Block3Chunk3ParentsAudit,
    tttLargeFiber76Block3Chunk3ParentPath_0_ok,
    tttLargeFiber76Block3Chunk3ParentPath_1_ok,
    tttLargeFiber76Block3Chunk3ParentPath_2_ok,
    tttLargeFiber76Block3Chunk3ParentPath_3_ok,
    tttLargeFiber76Block3Chunk3ParentPath_4_ok,
    tttLargeFiber76Block3Chunk3ParentPath_5_ok,
    tttLargeFiber76Block3Chunk3ParentPath_6_ok,
    tttLargeFiber76Block3Chunk3ParentPath_7_ok,
    tttLargeFiber76Block3Chunk3ParentPath_8_ok,
    tttLargeFiber76Block3Chunk3ParentPath_9_ok,
    tttLargeFiber76Block3Chunk3ParentPath_10_ok,
    tttLargeFiber76Block3Chunk3ParentPath_11_ok,
    tttLargeFiber76Block3Chunk3ParentPath_12_ok,
    tttLargeFiber76Block3Chunk3ParentPath_13_ok,
    tttLargeFiber76Block3Chunk3ParentPath_14_ok,
    tttLargeFiber76Block3Chunk3ParentPath_15_ok]

def tttLargeFiber76Block3Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber76CountsAudit &&
    tttLargeFiber76Block3Chunk3SourcesCheck &&
    tttLargeFiber76Block3Chunk3RowsAudit &&
    tttLargeFiber76Block3Chunk3ParentMapAudit &&
    tttLargeFiber76Block3Chunk3ParentsAudit

theorem tttLargeFiber76Block3Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber76Block3Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber76Block3Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber76CountsAudit_ok,
    tttLargeFiber76Block3Chunk3SourcesCheck_ok,
    tttLargeFiber76Block3Chunk3RowsAudit_ok,
    tttLargeFiber76Block3Chunk3ParentMapAudit_ok,
    tttLargeFiber76Block3Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber76Block3Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
