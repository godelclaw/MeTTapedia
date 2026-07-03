import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber76Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 76, block 2 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber76Block2Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber76Data

def tttLargeFiber76Block2Chunk3Sources : List Nat :=
  [   3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175,
   3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183]

def tttLargeFiber76Row176 : TripleComponentParentRow :=
  tripleRow 3168 3040 90 34 0 88 102 64
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber76Row177 : TripleComponentParentRow :=
  tripleRow 3169 3041 90 34 1 88 102 65
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber76Row178 : TripleComponentParentRow :=
  tripleRow 3170 3042 90 34 2 88 102 66
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber76Row179 : TripleComponentParentRow :=
  tripleRow 3171 3043 90 34 3 88 102 67
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber76Row180 : TripleComponentParentRow :=
  tripleRow 3172 3168 90 34 48 90 34 0
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row181 : TripleComponentParentRow :=
  tripleRow 3173 3169 90 34 49 90 34 1
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row182 : TripleComponentParentRow :=
  tripleRow 3174 3046 90 34 50 88 102 118
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber76Row183 : TripleComponentParentRow :=
  tripleRow 3175 3047 90 34 51 88 102 119
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber76Row184 : TripleComponentParentRow :=
  tripleRow 3176 3048 90 35 8 88 103 72
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber76Row185 : TripleComponentParentRow :=
  tripleRow 3177 3049 90 35 9 88 103 73
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber76Row186 : TripleComponentParentRow :=
  tripleRow 3178 3050 90 35 10 88 103 74
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber76Row187 : TripleComponentParentRow :=
  tripleRow 3179 3051 90 35 11 88 103 75
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber76Row188 : TripleComponentParentRow :=
  tripleRow 3180 3176 90 35 56 90 35 8
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row189 : TripleComponentParentRow :=
  tripleRow 3181 3177 90 35 57 90 35 9
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row190 : TripleComponentParentRow :=
  tripleRow 3182 3054 90 35 58 88 103 126
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber76Row191 : TripleComponentParentRow :=
  tripleRow 3183 3055 90 35 59 88 103 127
    (chainMove LColor.r LColor.b 0 TauEdge.F4F5)
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

def tttLargeFiber76Block2Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber76Row176
  , tttLargeFiber76Row177
  , tttLargeFiber76Row178
  , tttLargeFiber76Row179
  , tttLargeFiber76Row180
  , tttLargeFiber76Row181
  , tttLargeFiber76Row182
  , tttLargeFiber76Row183
  , tttLargeFiber76Row184
  , tttLargeFiber76Row185
  , tttLargeFiber76Row186
  , tttLargeFiber76Row187
  , tttLargeFiber76Row188
  , tttLargeFiber76Row189
  , tttLargeFiber76Row190
  , tttLargeFiber76Row191
  ]

def tttLargeFiber76Block2Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (2992 <= i) && decide (i < 3248)) ||
    (decide (3552 <= i) && decide (i < 3808))

def tttLargeFiber76Block2Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber76Block2Chunk3ExpectedContains row.source &&
    tttLargeFiber76Block2Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber76Key &&
          chainInputKey tttWord t == tttLargeFiber76Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber76Block2Chunk3SourcesCheck : Bool :=
  (tttLargeFiber76Block2Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber76Block2Chunk3Sources

theorem tttLargeFiber76Block2Chunk3SourcesCheck_ok :
    tttLargeFiber76Block2Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber76Block2Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber76Block2Chunk3RowValid
    (listGetD tttLargeFiber76Block2Chunk3Rows i default)

def tttLargeFiber76Block2Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber76Block2Chunk3Rows i default
  row.parent == tttLargeFiber76ParentOf row.source

def tttLargeFiber76Block2Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber76Block2Chunk3Sources 0 0 == 3168
      && tttLargeFiber76ParentOf 3168 == 3040
      && tttLargeFiber76ParentOf 3040 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 1 => listGetD tttLargeFiber76Block2Chunk3Sources 1 0 == 3169
      && tttLargeFiber76ParentOf 3169 == 3041
      && tttLargeFiber76ParentOf 3041 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 2 => listGetD tttLargeFiber76Block2Chunk3Sources 2 0 == 3170
      && tttLargeFiber76ParentOf 3170 == 3042
      && tttLargeFiber76ParentOf 3042 == 3002
      && tttLargeFiber76ParentOf 3002 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 3 => listGetD tttLargeFiber76Block2Chunk3Sources 3 0 == 3171
      && tttLargeFiber76ParentOf 3171 == 3043
      && tttLargeFiber76ParentOf 3043 == 3003
      && tttLargeFiber76ParentOf 3003 == 2995
      && tttLargeFiber76ParentOf 2995 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 4 => listGetD tttLargeFiber76Block2Chunk3Sources 4 0 == 3172
      && tttLargeFiber76ParentOf 3172 == 3168
      && tttLargeFiber76ParentOf 3168 == 3040
      && tttLargeFiber76ParentOf 3040 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 5 => listGetD tttLargeFiber76Block2Chunk3Sources 5 0 == 3173
      && tttLargeFiber76ParentOf 3173 == 3169
      && tttLargeFiber76ParentOf 3169 == 3041
      && tttLargeFiber76ParentOf 3041 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 6 => listGetD tttLargeFiber76Block2Chunk3Sources 6 0 == 3174
      && tttLargeFiber76ParentOf 3174 == 3046
      && tttLargeFiber76ParentOf 3046 == 3006
      && tttLargeFiber76ParentOf 3006 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 7 => listGetD tttLargeFiber76Block2Chunk3Sources 7 0 == 3175
      && tttLargeFiber76ParentOf 3175 == 3047
      && tttLargeFiber76ParentOf 3047 == 3007
      && tttLargeFiber76ParentOf 3007 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 8 => listGetD tttLargeFiber76Block2Chunk3Sources 8 0 == 3176
      && tttLargeFiber76ParentOf 3176 == 3048
      && tttLargeFiber76ParentOf 3048 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (2 <= tttLargeFiber76MaxParentDepth)
  | 9 => listGetD tttLargeFiber76Block2Chunk3Sources 9 0 == 3177
      && tttLargeFiber76ParentOf 3177 == 3049
      && tttLargeFiber76ParentOf 3049 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 10 => listGetD tttLargeFiber76Block2Chunk3Sources 10 0 == 3178
      && tttLargeFiber76ParentOf 3178 == 3050
      && tttLargeFiber76ParentOf 3050 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 11 => listGetD tttLargeFiber76Block2Chunk3Sources 11 0 == 3179
      && tttLargeFiber76ParentOf 3179 == 3051
      && tttLargeFiber76ParentOf 3051 == 2995
      && tttLargeFiber76ParentOf 2995 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 12 => listGetD tttLargeFiber76Block2Chunk3Sources 12 0 == 3180
      && tttLargeFiber76ParentOf 3180 == 3176
      && tttLargeFiber76ParentOf 3176 == 3048
      && tttLargeFiber76ParentOf 3048 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 13 => listGetD tttLargeFiber76Block2Chunk3Sources 13 0 == 3181
      && tttLargeFiber76ParentOf 3181 == 3177
      && tttLargeFiber76ParentOf 3177 == 3049
      && tttLargeFiber76ParentOf 3049 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 14 => listGetD tttLargeFiber76Block2Chunk3Sources 14 0 == 3182
      && tttLargeFiber76ParentOf 3182 == 3054
      && tttLargeFiber76ParentOf 3054 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 15 => listGetD tttLargeFiber76Block2Chunk3Sources 15 0 == 3183
      && tttLargeFiber76ParentOf 3183 == 3055
      && tttLargeFiber76ParentOf 3055 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | _ => false

theorem tttLargeFiber76Block2Chunk3Row_0_ok :
    tttLargeFiber76Block2Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3Row_1_ok :
    tttLargeFiber76Block2Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3Row_2_ok :
    tttLargeFiber76Block2Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3Row_3_ok :
    tttLargeFiber76Block2Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3Row_4_ok :
    tttLargeFiber76Block2Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3Row_5_ok :
    tttLargeFiber76Block2Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3Row_6_ok :
    tttLargeFiber76Block2Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3Row_7_ok :
    tttLargeFiber76Block2Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3Row_8_ok :
    tttLargeFiber76Block2Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3Row_9_ok :
    tttLargeFiber76Block2Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3Row_10_ok :
    tttLargeFiber76Block2Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3Row_11_ok :
    tttLargeFiber76Block2Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3Row_12_ok :
    tttLargeFiber76Block2Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3Row_13_ok :
    tttLargeFiber76Block2Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3Row_14_ok :
    tttLargeFiber76Block2Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3Row_15_ok :
    tttLargeFiber76Block2Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentMap_0_ok :
    tttLargeFiber76Block2Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentMap_1_ok :
    tttLargeFiber76Block2Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentMap_2_ok :
    tttLargeFiber76Block2Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentMap_3_ok :
    tttLargeFiber76Block2Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentMap_4_ok :
    tttLargeFiber76Block2Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentMap_5_ok :
    tttLargeFiber76Block2Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentMap_6_ok :
    tttLargeFiber76Block2Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentMap_7_ok :
    tttLargeFiber76Block2Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentMap_8_ok :
    tttLargeFiber76Block2Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentMap_9_ok :
    tttLargeFiber76Block2Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentMap_10_ok :
    tttLargeFiber76Block2Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentMap_11_ok :
    tttLargeFiber76Block2Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentMap_12_ok :
    tttLargeFiber76Block2Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentMap_13_ok :
    tttLargeFiber76Block2Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentMap_14_ok :
    tttLargeFiber76Block2Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentMap_15_ok :
    tttLargeFiber76Block2Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentPath_0_ok :
    tttLargeFiber76Block2Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentPath_1_ok :
    tttLargeFiber76Block2Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentPath_2_ok :
    tttLargeFiber76Block2Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentPath_3_ok :
    tttLargeFiber76Block2Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentPath_4_ok :
    tttLargeFiber76Block2Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentPath_5_ok :
    tttLargeFiber76Block2Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentPath_6_ok :
    tttLargeFiber76Block2Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentPath_7_ok :
    tttLargeFiber76Block2Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentPath_8_ok :
    tttLargeFiber76Block2Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentPath_9_ok :
    tttLargeFiber76Block2Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentPath_10_ok :
    tttLargeFiber76Block2Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentPath_11_ok :
    tttLargeFiber76Block2Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentPath_12_ok :
    tttLargeFiber76Block2Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentPath_13_ok :
    tttLargeFiber76Block2Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentPath_14_ok :
    tttLargeFiber76Block2Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber76Block2Chunk3ParentPath_15_ok :
    tttLargeFiber76Block2Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber76Block2Chunk3RowsAudit : Bool :=
  tttLargeFiber76Block2Chunk3RowCheck 0
    && tttLargeFiber76Block2Chunk3RowCheck 1
    && tttLargeFiber76Block2Chunk3RowCheck 2
    && tttLargeFiber76Block2Chunk3RowCheck 3
    && tttLargeFiber76Block2Chunk3RowCheck 4
    && tttLargeFiber76Block2Chunk3RowCheck 5
    && tttLargeFiber76Block2Chunk3RowCheck 6
    && tttLargeFiber76Block2Chunk3RowCheck 7
    && tttLargeFiber76Block2Chunk3RowCheck 8
    && tttLargeFiber76Block2Chunk3RowCheck 9
    && tttLargeFiber76Block2Chunk3RowCheck 10
    && tttLargeFiber76Block2Chunk3RowCheck 11
    && tttLargeFiber76Block2Chunk3RowCheck 12
    && tttLargeFiber76Block2Chunk3RowCheck 13
    && tttLargeFiber76Block2Chunk3RowCheck 14
    && tttLargeFiber76Block2Chunk3RowCheck 15

theorem tttLargeFiber76Block2Chunk3RowsAudit_ok :
    tttLargeFiber76Block2Chunk3RowsAudit = true := by
  simp [tttLargeFiber76Block2Chunk3RowsAudit,
    tttLargeFiber76Block2Chunk3Row_0_ok,
    tttLargeFiber76Block2Chunk3Row_1_ok,
    tttLargeFiber76Block2Chunk3Row_2_ok,
    tttLargeFiber76Block2Chunk3Row_3_ok,
    tttLargeFiber76Block2Chunk3Row_4_ok,
    tttLargeFiber76Block2Chunk3Row_5_ok,
    tttLargeFiber76Block2Chunk3Row_6_ok,
    tttLargeFiber76Block2Chunk3Row_7_ok,
    tttLargeFiber76Block2Chunk3Row_8_ok,
    tttLargeFiber76Block2Chunk3Row_9_ok,
    tttLargeFiber76Block2Chunk3Row_10_ok,
    tttLargeFiber76Block2Chunk3Row_11_ok,
    tttLargeFiber76Block2Chunk3Row_12_ok,
    tttLargeFiber76Block2Chunk3Row_13_ok,
    tttLargeFiber76Block2Chunk3Row_14_ok,
    tttLargeFiber76Block2Chunk3Row_15_ok]

def tttLargeFiber76Block2Chunk3ParentMapAudit : Bool :=
  tttLargeFiber76Block2Chunk3ParentMapCheck 0
    && tttLargeFiber76Block2Chunk3ParentMapCheck 1
    && tttLargeFiber76Block2Chunk3ParentMapCheck 2
    && tttLargeFiber76Block2Chunk3ParentMapCheck 3
    && tttLargeFiber76Block2Chunk3ParentMapCheck 4
    && tttLargeFiber76Block2Chunk3ParentMapCheck 5
    && tttLargeFiber76Block2Chunk3ParentMapCheck 6
    && tttLargeFiber76Block2Chunk3ParentMapCheck 7
    && tttLargeFiber76Block2Chunk3ParentMapCheck 8
    && tttLargeFiber76Block2Chunk3ParentMapCheck 9
    && tttLargeFiber76Block2Chunk3ParentMapCheck 10
    && tttLargeFiber76Block2Chunk3ParentMapCheck 11
    && tttLargeFiber76Block2Chunk3ParentMapCheck 12
    && tttLargeFiber76Block2Chunk3ParentMapCheck 13
    && tttLargeFiber76Block2Chunk3ParentMapCheck 14
    && tttLargeFiber76Block2Chunk3ParentMapCheck 15

theorem tttLargeFiber76Block2Chunk3ParentMapAudit_ok :
    tttLargeFiber76Block2Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber76Block2Chunk3ParentMapAudit,
    tttLargeFiber76Block2Chunk3ParentMap_0_ok,
    tttLargeFiber76Block2Chunk3ParentMap_1_ok,
    tttLargeFiber76Block2Chunk3ParentMap_2_ok,
    tttLargeFiber76Block2Chunk3ParentMap_3_ok,
    tttLargeFiber76Block2Chunk3ParentMap_4_ok,
    tttLargeFiber76Block2Chunk3ParentMap_5_ok,
    tttLargeFiber76Block2Chunk3ParentMap_6_ok,
    tttLargeFiber76Block2Chunk3ParentMap_7_ok,
    tttLargeFiber76Block2Chunk3ParentMap_8_ok,
    tttLargeFiber76Block2Chunk3ParentMap_9_ok,
    tttLargeFiber76Block2Chunk3ParentMap_10_ok,
    tttLargeFiber76Block2Chunk3ParentMap_11_ok,
    tttLargeFiber76Block2Chunk3ParentMap_12_ok,
    tttLargeFiber76Block2Chunk3ParentMap_13_ok,
    tttLargeFiber76Block2Chunk3ParentMap_14_ok,
    tttLargeFiber76Block2Chunk3ParentMap_15_ok]

def tttLargeFiber76Block2Chunk3ParentsAudit : Bool :=
  tttLargeFiber76Block2Chunk3ParentPathCheck 0
    && tttLargeFiber76Block2Chunk3ParentPathCheck 1
    && tttLargeFiber76Block2Chunk3ParentPathCheck 2
    && tttLargeFiber76Block2Chunk3ParentPathCheck 3
    && tttLargeFiber76Block2Chunk3ParentPathCheck 4
    && tttLargeFiber76Block2Chunk3ParentPathCheck 5
    && tttLargeFiber76Block2Chunk3ParentPathCheck 6
    && tttLargeFiber76Block2Chunk3ParentPathCheck 7
    && tttLargeFiber76Block2Chunk3ParentPathCheck 8
    && tttLargeFiber76Block2Chunk3ParentPathCheck 9
    && tttLargeFiber76Block2Chunk3ParentPathCheck 10
    && tttLargeFiber76Block2Chunk3ParentPathCheck 11
    && tttLargeFiber76Block2Chunk3ParentPathCheck 12
    && tttLargeFiber76Block2Chunk3ParentPathCheck 13
    && tttLargeFiber76Block2Chunk3ParentPathCheck 14
    && tttLargeFiber76Block2Chunk3ParentPathCheck 15

theorem tttLargeFiber76Block2Chunk3ParentsAudit_ok :
    tttLargeFiber76Block2Chunk3ParentsAudit = true := by
  simp [tttLargeFiber76Block2Chunk3ParentsAudit,
    tttLargeFiber76Block2Chunk3ParentPath_0_ok,
    tttLargeFiber76Block2Chunk3ParentPath_1_ok,
    tttLargeFiber76Block2Chunk3ParentPath_2_ok,
    tttLargeFiber76Block2Chunk3ParentPath_3_ok,
    tttLargeFiber76Block2Chunk3ParentPath_4_ok,
    tttLargeFiber76Block2Chunk3ParentPath_5_ok,
    tttLargeFiber76Block2Chunk3ParentPath_6_ok,
    tttLargeFiber76Block2Chunk3ParentPath_7_ok,
    tttLargeFiber76Block2Chunk3ParentPath_8_ok,
    tttLargeFiber76Block2Chunk3ParentPath_9_ok,
    tttLargeFiber76Block2Chunk3ParentPath_10_ok,
    tttLargeFiber76Block2Chunk3ParentPath_11_ok,
    tttLargeFiber76Block2Chunk3ParentPath_12_ok,
    tttLargeFiber76Block2Chunk3ParentPath_13_ok,
    tttLargeFiber76Block2Chunk3ParentPath_14_ok,
    tttLargeFiber76Block2Chunk3ParentPath_15_ok]

def tttLargeFiber76Block2Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber76CountsAudit &&
    tttLargeFiber76Block2Chunk3SourcesCheck &&
    tttLargeFiber76Block2Chunk3RowsAudit &&
    tttLargeFiber76Block2Chunk3ParentMapAudit &&
    tttLargeFiber76Block2Chunk3ParentsAudit

theorem tttLargeFiber76Block2Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber76Block2Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber76Block2Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber76CountsAudit_ok,
    tttLargeFiber76Block2Chunk3SourcesCheck_ok,
    tttLargeFiber76Block2Chunk3RowsAudit_ok,
    tttLargeFiber76Block2Chunk3ParentMapAudit_ok,
    tttLargeFiber76Block2Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber76Block2Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
