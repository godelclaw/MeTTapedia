import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber76Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 76, block 1 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber76Block1Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber76Data

def tttLargeFiber76Block1Chunk3Sources : List Nat :=
  [   3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111,
   3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119]

def tttLargeFiber76Row112 : TripleComponentParentRow :=
  tripleRow 3104 3040 89 110 64 88 102 64
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row113 : TripleComponentParentRow :=
  tripleRow 3105 3041 89 110 65 88 102 65
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row114 : TripleComponentParentRow :=
  tripleRow 3106 3042 89 110 66 88 102 66
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row115 : TripleComponentParentRow :=
  tripleRow 3107 3043 89 110 67 88 102 67
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row116 : TripleComponentParentRow :=
  tripleRow 3108 3044 89 110 116 88 102 116
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row117 : TripleComponentParentRow :=
  tripleRow 3109 3045 89 110 117 88 102 117
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row118 : TripleComponentParentRow :=
  tripleRow 3110 3046 89 110 118 88 102 118
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row119 : TripleComponentParentRow :=
  tripleRow 3111 3047 89 110 119 88 102 119
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row120 : TripleComponentParentRow :=
  tripleRow 3112 3048 89 111 72 88 103 72
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row121 : TripleComponentParentRow :=
  tripleRow 3113 3049 89 111 73 88 103 73
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row122 : TripleComponentParentRow :=
  tripleRow 3114 3050 89 111 74 88 103 74
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row123 : TripleComponentParentRow :=
  tripleRow 3115 3051 89 111 75 88 103 75
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row124 : TripleComponentParentRow :=
  tripleRow 3116 3052 89 111 124 88 103 124
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row125 : TripleComponentParentRow :=
  tripleRow 3117 3053 89 111 125 88 103 125
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row126 : TripleComponentParentRow :=
  tripleRow 3118 3054 89 111 126 88 103 126
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row127 : TripleComponentParentRow :=
  tripleRow 3119 3055 89 111 127 88 103 127
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Block1Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber76Row112
  , tttLargeFiber76Row113
  , tttLargeFiber76Row114
  , tttLargeFiber76Row115
  , tttLargeFiber76Row116
  , tttLargeFiber76Row117
  , tttLargeFiber76Row118
  , tttLargeFiber76Row119
  , tttLargeFiber76Row120
  , tttLargeFiber76Row121
  , tttLargeFiber76Row122
  , tttLargeFiber76Row123
  , tttLargeFiber76Row124
  , tttLargeFiber76Row125
  , tttLargeFiber76Row126
  , tttLargeFiber76Row127
  ]

def tttLargeFiber76Block1Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (2992 <= i) && decide (i < 3248)) ||
    (decide (3552 <= i) && decide (i < 3808))

def tttLargeFiber76Block1Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber76Block1Chunk3ExpectedContains row.source &&
    tttLargeFiber76Block1Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber76Key &&
          chainInputKey tttWord t == tttLargeFiber76Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber76Block1Chunk3SourcesCheck : Bool :=
  (tttLargeFiber76Block1Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber76Block1Chunk3Sources

theorem tttLargeFiber76Block1Chunk3SourcesCheck_ok :
    tttLargeFiber76Block1Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber76Block1Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber76Block1Chunk3RowValid
    (listGetD tttLargeFiber76Block1Chunk3Rows i default)

def tttLargeFiber76Block1Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber76Block1Chunk3Rows i default
  row.parent == tttLargeFiber76ParentOf row.source

def tttLargeFiber76Block1Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber76Block1Chunk3Sources 0 0 == 3104
      && tttLargeFiber76ParentOf 3104 == 3040
      && tttLargeFiber76ParentOf 3040 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 1 => listGetD tttLargeFiber76Block1Chunk3Sources 1 0 == 3105
      && tttLargeFiber76ParentOf 3105 == 3041
      && tttLargeFiber76ParentOf 3041 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 2 => listGetD tttLargeFiber76Block1Chunk3Sources 2 0 == 3106
      && tttLargeFiber76ParentOf 3106 == 3042
      && tttLargeFiber76ParentOf 3042 == 3002
      && tttLargeFiber76ParentOf 3002 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 3 => listGetD tttLargeFiber76Block1Chunk3Sources 3 0 == 3107
      && tttLargeFiber76ParentOf 3107 == 3043
      && tttLargeFiber76ParentOf 3043 == 3003
      && tttLargeFiber76ParentOf 3003 == 2995
      && tttLargeFiber76ParentOf 2995 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 4 => listGetD tttLargeFiber76Block1Chunk3Sources 4 0 == 3108
      && tttLargeFiber76ParentOf 3108 == 3044
      && tttLargeFiber76ParentOf 3044 == 3004
      && tttLargeFiber76ParentOf 3004 == 2996
      && tttLargeFiber76ParentOf 2996 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 5 => listGetD tttLargeFiber76Block1Chunk3Sources 5 0 == 3109
      && tttLargeFiber76ParentOf 3109 == 3045
      && tttLargeFiber76ParentOf 3045 == 3005
      && tttLargeFiber76ParentOf 3005 == 2997
      && tttLargeFiber76ParentOf 2997 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 6 => listGetD tttLargeFiber76Block1Chunk3Sources 6 0 == 3110
      && tttLargeFiber76ParentOf 3110 == 3046
      && tttLargeFiber76ParentOf 3046 == 3006
      && tttLargeFiber76ParentOf 3006 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 7 => listGetD tttLargeFiber76Block1Chunk3Sources 7 0 == 3111
      && tttLargeFiber76ParentOf 3111 == 3047
      && tttLargeFiber76ParentOf 3047 == 3007
      && tttLargeFiber76ParentOf 3007 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 8 => listGetD tttLargeFiber76Block1Chunk3Sources 8 0 == 3112
      && tttLargeFiber76ParentOf 3112 == 3048
      && tttLargeFiber76ParentOf 3048 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (2 <= tttLargeFiber76MaxParentDepth)
  | 9 => listGetD tttLargeFiber76Block1Chunk3Sources 9 0 == 3113
      && tttLargeFiber76ParentOf 3113 == 3049
      && tttLargeFiber76ParentOf 3049 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 10 => listGetD tttLargeFiber76Block1Chunk3Sources 10 0 == 3114
      && tttLargeFiber76ParentOf 3114 == 3050
      && tttLargeFiber76ParentOf 3050 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 11 => listGetD tttLargeFiber76Block1Chunk3Sources 11 0 == 3115
      && tttLargeFiber76ParentOf 3115 == 3051
      && tttLargeFiber76ParentOf 3051 == 2995
      && tttLargeFiber76ParentOf 2995 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 12 => listGetD tttLargeFiber76Block1Chunk3Sources 12 0 == 3116
      && tttLargeFiber76ParentOf 3116 == 3052
      && tttLargeFiber76ParentOf 3052 == 2996
      && tttLargeFiber76ParentOf 2996 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 13 => listGetD tttLargeFiber76Block1Chunk3Sources 13 0 == 3117
      && tttLargeFiber76ParentOf 3117 == 3053
      && tttLargeFiber76ParentOf 3053 == 2997
      && tttLargeFiber76ParentOf 2997 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 14 => listGetD tttLargeFiber76Block1Chunk3Sources 14 0 == 3118
      && tttLargeFiber76ParentOf 3118 == 3054
      && tttLargeFiber76ParentOf 3054 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 15 => listGetD tttLargeFiber76Block1Chunk3Sources 15 0 == 3119
      && tttLargeFiber76ParentOf 3119 == 3055
      && tttLargeFiber76ParentOf 3055 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | _ => false

theorem tttLargeFiber76Block1Chunk3Row_0_ok :
    tttLargeFiber76Block1Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3Row_1_ok :
    tttLargeFiber76Block1Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3Row_2_ok :
    tttLargeFiber76Block1Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3Row_3_ok :
    tttLargeFiber76Block1Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3Row_4_ok :
    tttLargeFiber76Block1Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3Row_5_ok :
    tttLargeFiber76Block1Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3Row_6_ok :
    tttLargeFiber76Block1Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3Row_7_ok :
    tttLargeFiber76Block1Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3Row_8_ok :
    tttLargeFiber76Block1Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3Row_9_ok :
    tttLargeFiber76Block1Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3Row_10_ok :
    tttLargeFiber76Block1Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3Row_11_ok :
    tttLargeFiber76Block1Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3Row_12_ok :
    tttLargeFiber76Block1Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3Row_13_ok :
    tttLargeFiber76Block1Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3Row_14_ok :
    tttLargeFiber76Block1Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3Row_15_ok :
    tttLargeFiber76Block1Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentMap_0_ok :
    tttLargeFiber76Block1Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentMap_1_ok :
    tttLargeFiber76Block1Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentMap_2_ok :
    tttLargeFiber76Block1Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentMap_3_ok :
    tttLargeFiber76Block1Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentMap_4_ok :
    tttLargeFiber76Block1Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentMap_5_ok :
    tttLargeFiber76Block1Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentMap_6_ok :
    tttLargeFiber76Block1Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentMap_7_ok :
    tttLargeFiber76Block1Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentMap_8_ok :
    tttLargeFiber76Block1Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentMap_9_ok :
    tttLargeFiber76Block1Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentMap_10_ok :
    tttLargeFiber76Block1Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentMap_11_ok :
    tttLargeFiber76Block1Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentMap_12_ok :
    tttLargeFiber76Block1Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentMap_13_ok :
    tttLargeFiber76Block1Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentMap_14_ok :
    tttLargeFiber76Block1Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentMap_15_ok :
    tttLargeFiber76Block1Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentPath_0_ok :
    tttLargeFiber76Block1Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentPath_1_ok :
    tttLargeFiber76Block1Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentPath_2_ok :
    tttLargeFiber76Block1Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentPath_3_ok :
    tttLargeFiber76Block1Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentPath_4_ok :
    tttLargeFiber76Block1Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentPath_5_ok :
    tttLargeFiber76Block1Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentPath_6_ok :
    tttLargeFiber76Block1Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentPath_7_ok :
    tttLargeFiber76Block1Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentPath_8_ok :
    tttLargeFiber76Block1Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentPath_9_ok :
    tttLargeFiber76Block1Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentPath_10_ok :
    tttLargeFiber76Block1Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentPath_11_ok :
    tttLargeFiber76Block1Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentPath_12_ok :
    tttLargeFiber76Block1Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentPath_13_ok :
    tttLargeFiber76Block1Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentPath_14_ok :
    tttLargeFiber76Block1Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber76Block1Chunk3ParentPath_15_ok :
    tttLargeFiber76Block1Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber76Block1Chunk3RowsAudit : Bool :=
  tttLargeFiber76Block1Chunk3RowCheck 0
    && tttLargeFiber76Block1Chunk3RowCheck 1
    && tttLargeFiber76Block1Chunk3RowCheck 2
    && tttLargeFiber76Block1Chunk3RowCheck 3
    && tttLargeFiber76Block1Chunk3RowCheck 4
    && tttLargeFiber76Block1Chunk3RowCheck 5
    && tttLargeFiber76Block1Chunk3RowCheck 6
    && tttLargeFiber76Block1Chunk3RowCheck 7
    && tttLargeFiber76Block1Chunk3RowCheck 8
    && tttLargeFiber76Block1Chunk3RowCheck 9
    && tttLargeFiber76Block1Chunk3RowCheck 10
    && tttLargeFiber76Block1Chunk3RowCheck 11
    && tttLargeFiber76Block1Chunk3RowCheck 12
    && tttLargeFiber76Block1Chunk3RowCheck 13
    && tttLargeFiber76Block1Chunk3RowCheck 14
    && tttLargeFiber76Block1Chunk3RowCheck 15

theorem tttLargeFiber76Block1Chunk3RowsAudit_ok :
    tttLargeFiber76Block1Chunk3RowsAudit = true := by
  simp [tttLargeFiber76Block1Chunk3RowsAudit,
    tttLargeFiber76Block1Chunk3Row_0_ok,
    tttLargeFiber76Block1Chunk3Row_1_ok,
    tttLargeFiber76Block1Chunk3Row_2_ok,
    tttLargeFiber76Block1Chunk3Row_3_ok,
    tttLargeFiber76Block1Chunk3Row_4_ok,
    tttLargeFiber76Block1Chunk3Row_5_ok,
    tttLargeFiber76Block1Chunk3Row_6_ok,
    tttLargeFiber76Block1Chunk3Row_7_ok,
    tttLargeFiber76Block1Chunk3Row_8_ok,
    tttLargeFiber76Block1Chunk3Row_9_ok,
    tttLargeFiber76Block1Chunk3Row_10_ok,
    tttLargeFiber76Block1Chunk3Row_11_ok,
    tttLargeFiber76Block1Chunk3Row_12_ok,
    tttLargeFiber76Block1Chunk3Row_13_ok,
    tttLargeFiber76Block1Chunk3Row_14_ok,
    tttLargeFiber76Block1Chunk3Row_15_ok]

def tttLargeFiber76Block1Chunk3ParentMapAudit : Bool :=
  tttLargeFiber76Block1Chunk3ParentMapCheck 0
    && tttLargeFiber76Block1Chunk3ParentMapCheck 1
    && tttLargeFiber76Block1Chunk3ParentMapCheck 2
    && tttLargeFiber76Block1Chunk3ParentMapCheck 3
    && tttLargeFiber76Block1Chunk3ParentMapCheck 4
    && tttLargeFiber76Block1Chunk3ParentMapCheck 5
    && tttLargeFiber76Block1Chunk3ParentMapCheck 6
    && tttLargeFiber76Block1Chunk3ParentMapCheck 7
    && tttLargeFiber76Block1Chunk3ParentMapCheck 8
    && tttLargeFiber76Block1Chunk3ParentMapCheck 9
    && tttLargeFiber76Block1Chunk3ParentMapCheck 10
    && tttLargeFiber76Block1Chunk3ParentMapCheck 11
    && tttLargeFiber76Block1Chunk3ParentMapCheck 12
    && tttLargeFiber76Block1Chunk3ParentMapCheck 13
    && tttLargeFiber76Block1Chunk3ParentMapCheck 14
    && tttLargeFiber76Block1Chunk3ParentMapCheck 15

theorem tttLargeFiber76Block1Chunk3ParentMapAudit_ok :
    tttLargeFiber76Block1Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber76Block1Chunk3ParentMapAudit,
    tttLargeFiber76Block1Chunk3ParentMap_0_ok,
    tttLargeFiber76Block1Chunk3ParentMap_1_ok,
    tttLargeFiber76Block1Chunk3ParentMap_2_ok,
    tttLargeFiber76Block1Chunk3ParentMap_3_ok,
    tttLargeFiber76Block1Chunk3ParentMap_4_ok,
    tttLargeFiber76Block1Chunk3ParentMap_5_ok,
    tttLargeFiber76Block1Chunk3ParentMap_6_ok,
    tttLargeFiber76Block1Chunk3ParentMap_7_ok,
    tttLargeFiber76Block1Chunk3ParentMap_8_ok,
    tttLargeFiber76Block1Chunk3ParentMap_9_ok,
    tttLargeFiber76Block1Chunk3ParentMap_10_ok,
    tttLargeFiber76Block1Chunk3ParentMap_11_ok,
    tttLargeFiber76Block1Chunk3ParentMap_12_ok,
    tttLargeFiber76Block1Chunk3ParentMap_13_ok,
    tttLargeFiber76Block1Chunk3ParentMap_14_ok,
    tttLargeFiber76Block1Chunk3ParentMap_15_ok]

def tttLargeFiber76Block1Chunk3ParentsAudit : Bool :=
  tttLargeFiber76Block1Chunk3ParentPathCheck 0
    && tttLargeFiber76Block1Chunk3ParentPathCheck 1
    && tttLargeFiber76Block1Chunk3ParentPathCheck 2
    && tttLargeFiber76Block1Chunk3ParentPathCheck 3
    && tttLargeFiber76Block1Chunk3ParentPathCheck 4
    && tttLargeFiber76Block1Chunk3ParentPathCheck 5
    && tttLargeFiber76Block1Chunk3ParentPathCheck 6
    && tttLargeFiber76Block1Chunk3ParentPathCheck 7
    && tttLargeFiber76Block1Chunk3ParentPathCheck 8
    && tttLargeFiber76Block1Chunk3ParentPathCheck 9
    && tttLargeFiber76Block1Chunk3ParentPathCheck 10
    && tttLargeFiber76Block1Chunk3ParentPathCheck 11
    && tttLargeFiber76Block1Chunk3ParentPathCheck 12
    && tttLargeFiber76Block1Chunk3ParentPathCheck 13
    && tttLargeFiber76Block1Chunk3ParentPathCheck 14
    && tttLargeFiber76Block1Chunk3ParentPathCheck 15

theorem tttLargeFiber76Block1Chunk3ParentsAudit_ok :
    tttLargeFiber76Block1Chunk3ParentsAudit = true := by
  simp [tttLargeFiber76Block1Chunk3ParentsAudit,
    tttLargeFiber76Block1Chunk3ParentPath_0_ok,
    tttLargeFiber76Block1Chunk3ParentPath_1_ok,
    tttLargeFiber76Block1Chunk3ParentPath_2_ok,
    tttLargeFiber76Block1Chunk3ParentPath_3_ok,
    tttLargeFiber76Block1Chunk3ParentPath_4_ok,
    tttLargeFiber76Block1Chunk3ParentPath_5_ok,
    tttLargeFiber76Block1Chunk3ParentPath_6_ok,
    tttLargeFiber76Block1Chunk3ParentPath_7_ok,
    tttLargeFiber76Block1Chunk3ParentPath_8_ok,
    tttLargeFiber76Block1Chunk3ParentPath_9_ok,
    tttLargeFiber76Block1Chunk3ParentPath_10_ok,
    tttLargeFiber76Block1Chunk3ParentPath_11_ok,
    tttLargeFiber76Block1Chunk3ParentPath_12_ok,
    tttLargeFiber76Block1Chunk3ParentPath_13_ok,
    tttLargeFiber76Block1Chunk3ParentPath_14_ok,
    tttLargeFiber76Block1Chunk3ParentPath_15_ok]

def tttLargeFiber76Block1Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber76CountsAudit &&
    tttLargeFiber76Block1Chunk3SourcesCheck &&
    tttLargeFiber76Block1Chunk3RowsAudit &&
    tttLargeFiber76Block1Chunk3ParentMapAudit &&
    tttLargeFiber76Block1Chunk3ParentsAudit

theorem tttLargeFiber76Block1Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber76Block1Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber76Block1Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber76CountsAudit_ok,
    tttLargeFiber76Block1Chunk3SourcesCheck_ok,
    tttLargeFiber76Block1Chunk3RowsAudit_ok,
    tttLargeFiber76Block1Chunk3ParentMapAudit_ok,
    tttLargeFiber76Block1Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber76Block1Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
