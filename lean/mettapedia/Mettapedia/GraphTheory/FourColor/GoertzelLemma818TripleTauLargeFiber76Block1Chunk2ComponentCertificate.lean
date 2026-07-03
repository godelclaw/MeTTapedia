import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber76Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 76, block 1 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber76Block1Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber76Data

def tttLargeFiber76Block1Chunk2Sources : List Nat :=
  [   3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095,
   3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103]

def tttLargeFiber76Row96 : TripleComponentParentRow :=
  tripleRow 3088 3024 89 108 132 88 100 132
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row97 : TripleComponentParentRow :=
  tripleRow 3089 3025 89 108 133 88 100 133
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row98 : TripleComponentParentRow :=
  tripleRow 3090 3026 89 108 134 88 100 134
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row99 : TripleComponentParentRow :=
  tripleRow 3091 3027 89 108 135 88 100 135
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row100 : TripleComponentParentRow :=
  tripleRow 3092 3028 89 108 180 88 100 180
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row101 : TripleComponentParentRow :=
  tripleRow 3093 3029 89 108 181 88 100 181
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row102 : TripleComponentParentRow :=
  tripleRow 3094 3030 89 108 182 88 100 182
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row103 : TripleComponentParentRow :=
  tripleRow 3095 3031 89 108 183 88 100 183
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row104 : TripleComponentParentRow :=
  tripleRow 3096 3032 89 109 140 88 101 140
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row105 : TripleComponentParentRow :=
  tripleRow 3097 3033 89 109 141 88 101 141
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row106 : TripleComponentParentRow :=
  tripleRow 3098 3034 89 109 142 88 101 142
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row107 : TripleComponentParentRow :=
  tripleRow 3099 3035 89 109 143 88 101 143
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row108 : TripleComponentParentRow :=
  tripleRow 3100 3036 89 109 188 88 101 188
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row109 : TripleComponentParentRow :=
  tripleRow 3101 3037 89 109 189 88 101 189
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row110 : TripleComponentParentRow :=
  tripleRow 3102 3038 89 109 190 88 101 190
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Row111 : TripleComponentParentRow :=
  tripleRow 3103 3039 89 109 191 88 101 191
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber76Block1Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber76Row96
  , tttLargeFiber76Row97
  , tttLargeFiber76Row98
  , tttLargeFiber76Row99
  , tttLargeFiber76Row100
  , tttLargeFiber76Row101
  , tttLargeFiber76Row102
  , tttLargeFiber76Row103
  , tttLargeFiber76Row104
  , tttLargeFiber76Row105
  , tttLargeFiber76Row106
  , tttLargeFiber76Row107
  , tttLargeFiber76Row108
  , tttLargeFiber76Row109
  , tttLargeFiber76Row110
  , tttLargeFiber76Row111
  ]

def tttLargeFiber76Block1Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (2992 <= i) && decide (i < 3248)) ||
    (decide (3552 <= i) && decide (i < 3808))

def tttLargeFiber76Block1Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber76Block1Chunk2ExpectedContains row.source &&
    tttLargeFiber76Block1Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber76Key &&
          chainInputKey tttWord t == tttLargeFiber76Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber76Block1Chunk2SourcesCheck : Bool :=
  (tttLargeFiber76Block1Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber76Block1Chunk2Sources

theorem tttLargeFiber76Block1Chunk2SourcesCheck_ok :
    tttLargeFiber76Block1Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber76Block1Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber76Block1Chunk2RowValid
    (listGetD tttLargeFiber76Block1Chunk2Rows i default)

def tttLargeFiber76Block1Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber76Block1Chunk2Rows i default
  row.parent == tttLargeFiber76ParentOf row.source

def tttLargeFiber76Block1Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber76Block1Chunk2Sources 0 0 == 3088
      && tttLargeFiber76ParentOf 3088 == 3024
      && tttLargeFiber76ParentOf 3024 == 3040
      && tttLargeFiber76ParentOf 3040 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 1 => listGetD tttLargeFiber76Block1Chunk2Sources 1 0 == 3089
      && tttLargeFiber76ParentOf 3089 == 3025
      && tttLargeFiber76ParentOf 3025 == 3041
      && tttLargeFiber76ParentOf 3041 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 2 => listGetD tttLargeFiber76Block1Chunk2Sources 2 0 == 3090
      && tttLargeFiber76ParentOf 3090 == 3026
      && tttLargeFiber76ParentOf 3026 == 3014
      && tttLargeFiber76ParentOf 3014 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 3 => listGetD tttLargeFiber76Block1Chunk2Sources 3 0 == 3091
      && tttLargeFiber76ParentOf 3091 == 3027
      && tttLargeFiber76ParentOf 3027 == 3015
      && tttLargeFiber76ParentOf 3015 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 4 => listGetD tttLargeFiber76Block1Chunk2Sources 4 0 == 3092
      && tttLargeFiber76ParentOf 3092 == 3028
      && tttLargeFiber76ParentOf 3028 == 3010
      && tttLargeFiber76ParentOf 3010 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 5 => listGetD tttLargeFiber76Block1Chunk2Sources 5 0 == 3093
      && tttLargeFiber76ParentOf 3093 == 3029
      && tttLargeFiber76ParentOf 3029 == 3031
      && tttLargeFiber76ParentOf 3031 == 3008
      && tttLargeFiber76ParentOf 3008 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 6 => listGetD tttLargeFiber76Block1Chunk2Sources 6 0 == 3094
      && tttLargeFiber76ParentOf 3094 == 3030
      && tttLargeFiber76ParentOf 3030 == 3009
      && tttLargeFiber76ParentOf 3009 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 7 => listGetD tttLargeFiber76Block1Chunk2Sources 7 0 == 3095
      && tttLargeFiber76ParentOf 3095 == 3031
      && tttLargeFiber76ParentOf 3031 == 3008
      && tttLargeFiber76ParentOf 3008 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 8 => listGetD tttLargeFiber76Block1Chunk2Sources 8 0 == 3096
      && tttLargeFiber76ParentOf 3096 == 3032
      && tttLargeFiber76ParentOf 3032 == 3048
      && tttLargeFiber76ParentOf 3048 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 9 => listGetD tttLargeFiber76Block1Chunk2Sources 9 0 == 3097
      && tttLargeFiber76ParentOf 3097 == 3033
      && tttLargeFiber76ParentOf 3033 == 3049
      && tttLargeFiber76ParentOf 3049 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 10 => listGetD tttLargeFiber76Block1Chunk2Sources 10 0 == 3098
      && tttLargeFiber76ParentOf 3098 == 3034
      && tttLargeFiber76ParentOf 3034 == 3050
      && tttLargeFiber76ParentOf 3050 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 11 => listGetD tttLargeFiber76Block1Chunk2Sources 11 0 == 3099
      && tttLargeFiber76ParentOf 3099 == 3035
      && tttLargeFiber76ParentOf 3035 == 3032
      && tttLargeFiber76ParentOf 3032 == 3048
      && tttLargeFiber76ParentOf 3048 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 12 => listGetD tttLargeFiber76Block1Chunk2Sources 12 0 == 3100
      && tttLargeFiber76ParentOf 3100 == 3036
      && tttLargeFiber76ParentOf 3036 == 3032
      && tttLargeFiber76ParentOf 3032 == 3048
      && tttLargeFiber76ParentOf 3048 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 13 => listGetD tttLargeFiber76Block1Chunk2Sources 13 0 == 3101
      && tttLargeFiber76ParentOf 3101 == 3037
      && tttLargeFiber76ParentOf 3037 == 3033
      && tttLargeFiber76ParentOf 3033 == 3049
      && tttLargeFiber76ParentOf 3049 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 14 => listGetD tttLargeFiber76Block1Chunk2Sources 14 0 == 3102
      && tttLargeFiber76ParentOf 3102 == 3038
      && tttLargeFiber76ParentOf 3038 == 3054
      && tttLargeFiber76ParentOf 3054 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 15 => listGetD tttLargeFiber76Block1Chunk2Sources 15 0 == 3103
      && tttLargeFiber76ParentOf 3103 == 3039
      && tttLargeFiber76ParentOf 3039 == 3055
      && tttLargeFiber76ParentOf 3055 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | _ => false

theorem tttLargeFiber76Block1Chunk2Row_0_ok :
    tttLargeFiber76Block1Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2Row_1_ok :
    tttLargeFiber76Block1Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2Row_2_ok :
    tttLargeFiber76Block1Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2Row_3_ok :
    tttLargeFiber76Block1Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2Row_4_ok :
    tttLargeFiber76Block1Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2Row_5_ok :
    tttLargeFiber76Block1Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2Row_6_ok :
    tttLargeFiber76Block1Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2Row_7_ok :
    tttLargeFiber76Block1Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2Row_8_ok :
    tttLargeFiber76Block1Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2Row_9_ok :
    tttLargeFiber76Block1Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2Row_10_ok :
    tttLargeFiber76Block1Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2Row_11_ok :
    tttLargeFiber76Block1Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2Row_12_ok :
    tttLargeFiber76Block1Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2Row_13_ok :
    tttLargeFiber76Block1Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2Row_14_ok :
    tttLargeFiber76Block1Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2Row_15_ok :
    tttLargeFiber76Block1Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentMap_0_ok :
    tttLargeFiber76Block1Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentMap_1_ok :
    tttLargeFiber76Block1Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentMap_2_ok :
    tttLargeFiber76Block1Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentMap_3_ok :
    tttLargeFiber76Block1Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentMap_4_ok :
    tttLargeFiber76Block1Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentMap_5_ok :
    tttLargeFiber76Block1Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentMap_6_ok :
    tttLargeFiber76Block1Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentMap_7_ok :
    tttLargeFiber76Block1Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentMap_8_ok :
    tttLargeFiber76Block1Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentMap_9_ok :
    tttLargeFiber76Block1Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentMap_10_ok :
    tttLargeFiber76Block1Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentMap_11_ok :
    tttLargeFiber76Block1Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentMap_12_ok :
    tttLargeFiber76Block1Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentMap_13_ok :
    tttLargeFiber76Block1Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentMap_14_ok :
    tttLargeFiber76Block1Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentMap_15_ok :
    tttLargeFiber76Block1Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentPath_0_ok :
    tttLargeFiber76Block1Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentPath_1_ok :
    tttLargeFiber76Block1Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentPath_2_ok :
    tttLargeFiber76Block1Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentPath_3_ok :
    tttLargeFiber76Block1Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentPath_4_ok :
    tttLargeFiber76Block1Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentPath_5_ok :
    tttLargeFiber76Block1Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentPath_6_ok :
    tttLargeFiber76Block1Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentPath_7_ok :
    tttLargeFiber76Block1Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentPath_8_ok :
    tttLargeFiber76Block1Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentPath_9_ok :
    tttLargeFiber76Block1Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentPath_10_ok :
    tttLargeFiber76Block1Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentPath_11_ok :
    tttLargeFiber76Block1Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentPath_12_ok :
    tttLargeFiber76Block1Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentPath_13_ok :
    tttLargeFiber76Block1Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentPath_14_ok :
    tttLargeFiber76Block1Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber76Block1Chunk2ParentPath_15_ok :
    tttLargeFiber76Block1Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber76Block1Chunk2RowsAudit : Bool :=
  tttLargeFiber76Block1Chunk2RowCheck 0
    && tttLargeFiber76Block1Chunk2RowCheck 1
    && tttLargeFiber76Block1Chunk2RowCheck 2
    && tttLargeFiber76Block1Chunk2RowCheck 3
    && tttLargeFiber76Block1Chunk2RowCheck 4
    && tttLargeFiber76Block1Chunk2RowCheck 5
    && tttLargeFiber76Block1Chunk2RowCheck 6
    && tttLargeFiber76Block1Chunk2RowCheck 7
    && tttLargeFiber76Block1Chunk2RowCheck 8
    && tttLargeFiber76Block1Chunk2RowCheck 9
    && tttLargeFiber76Block1Chunk2RowCheck 10
    && tttLargeFiber76Block1Chunk2RowCheck 11
    && tttLargeFiber76Block1Chunk2RowCheck 12
    && tttLargeFiber76Block1Chunk2RowCheck 13
    && tttLargeFiber76Block1Chunk2RowCheck 14
    && tttLargeFiber76Block1Chunk2RowCheck 15

theorem tttLargeFiber76Block1Chunk2RowsAudit_ok :
    tttLargeFiber76Block1Chunk2RowsAudit = true := by
  simp [tttLargeFiber76Block1Chunk2RowsAudit,
    tttLargeFiber76Block1Chunk2Row_0_ok,
    tttLargeFiber76Block1Chunk2Row_1_ok,
    tttLargeFiber76Block1Chunk2Row_2_ok,
    tttLargeFiber76Block1Chunk2Row_3_ok,
    tttLargeFiber76Block1Chunk2Row_4_ok,
    tttLargeFiber76Block1Chunk2Row_5_ok,
    tttLargeFiber76Block1Chunk2Row_6_ok,
    tttLargeFiber76Block1Chunk2Row_7_ok,
    tttLargeFiber76Block1Chunk2Row_8_ok,
    tttLargeFiber76Block1Chunk2Row_9_ok,
    tttLargeFiber76Block1Chunk2Row_10_ok,
    tttLargeFiber76Block1Chunk2Row_11_ok,
    tttLargeFiber76Block1Chunk2Row_12_ok,
    tttLargeFiber76Block1Chunk2Row_13_ok,
    tttLargeFiber76Block1Chunk2Row_14_ok,
    tttLargeFiber76Block1Chunk2Row_15_ok]

def tttLargeFiber76Block1Chunk2ParentMapAudit : Bool :=
  tttLargeFiber76Block1Chunk2ParentMapCheck 0
    && tttLargeFiber76Block1Chunk2ParentMapCheck 1
    && tttLargeFiber76Block1Chunk2ParentMapCheck 2
    && tttLargeFiber76Block1Chunk2ParentMapCheck 3
    && tttLargeFiber76Block1Chunk2ParentMapCheck 4
    && tttLargeFiber76Block1Chunk2ParentMapCheck 5
    && tttLargeFiber76Block1Chunk2ParentMapCheck 6
    && tttLargeFiber76Block1Chunk2ParentMapCheck 7
    && tttLargeFiber76Block1Chunk2ParentMapCheck 8
    && tttLargeFiber76Block1Chunk2ParentMapCheck 9
    && tttLargeFiber76Block1Chunk2ParentMapCheck 10
    && tttLargeFiber76Block1Chunk2ParentMapCheck 11
    && tttLargeFiber76Block1Chunk2ParentMapCheck 12
    && tttLargeFiber76Block1Chunk2ParentMapCheck 13
    && tttLargeFiber76Block1Chunk2ParentMapCheck 14
    && tttLargeFiber76Block1Chunk2ParentMapCheck 15

theorem tttLargeFiber76Block1Chunk2ParentMapAudit_ok :
    tttLargeFiber76Block1Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber76Block1Chunk2ParentMapAudit,
    tttLargeFiber76Block1Chunk2ParentMap_0_ok,
    tttLargeFiber76Block1Chunk2ParentMap_1_ok,
    tttLargeFiber76Block1Chunk2ParentMap_2_ok,
    tttLargeFiber76Block1Chunk2ParentMap_3_ok,
    tttLargeFiber76Block1Chunk2ParentMap_4_ok,
    tttLargeFiber76Block1Chunk2ParentMap_5_ok,
    tttLargeFiber76Block1Chunk2ParentMap_6_ok,
    tttLargeFiber76Block1Chunk2ParentMap_7_ok,
    tttLargeFiber76Block1Chunk2ParentMap_8_ok,
    tttLargeFiber76Block1Chunk2ParentMap_9_ok,
    tttLargeFiber76Block1Chunk2ParentMap_10_ok,
    tttLargeFiber76Block1Chunk2ParentMap_11_ok,
    tttLargeFiber76Block1Chunk2ParentMap_12_ok,
    tttLargeFiber76Block1Chunk2ParentMap_13_ok,
    tttLargeFiber76Block1Chunk2ParentMap_14_ok,
    tttLargeFiber76Block1Chunk2ParentMap_15_ok]

def tttLargeFiber76Block1Chunk2ParentsAudit : Bool :=
  tttLargeFiber76Block1Chunk2ParentPathCheck 0
    && tttLargeFiber76Block1Chunk2ParentPathCheck 1
    && tttLargeFiber76Block1Chunk2ParentPathCheck 2
    && tttLargeFiber76Block1Chunk2ParentPathCheck 3
    && tttLargeFiber76Block1Chunk2ParentPathCheck 4
    && tttLargeFiber76Block1Chunk2ParentPathCheck 5
    && tttLargeFiber76Block1Chunk2ParentPathCheck 6
    && tttLargeFiber76Block1Chunk2ParentPathCheck 7
    && tttLargeFiber76Block1Chunk2ParentPathCheck 8
    && tttLargeFiber76Block1Chunk2ParentPathCheck 9
    && tttLargeFiber76Block1Chunk2ParentPathCheck 10
    && tttLargeFiber76Block1Chunk2ParentPathCheck 11
    && tttLargeFiber76Block1Chunk2ParentPathCheck 12
    && tttLargeFiber76Block1Chunk2ParentPathCheck 13
    && tttLargeFiber76Block1Chunk2ParentPathCheck 14
    && tttLargeFiber76Block1Chunk2ParentPathCheck 15

theorem tttLargeFiber76Block1Chunk2ParentsAudit_ok :
    tttLargeFiber76Block1Chunk2ParentsAudit = true := by
  simp [tttLargeFiber76Block1Chunk2ParentsAudit,
    tttLargeFiber76Block1Chunk2ParentPath_0_ok,
    tttLargeFiber76Block1Chunk2ParentPath_1_ok,
    tttLargeFiber76Block1Chunk2ParentPath_2_ok,
    tttLargeFiber76Block1Chunk2ParentPath_3_ok,
    tttLargeFiber76Block1Chunk2ParentPath_4_ok,
    tttLargeFiber76Block1Chunk2ParentPath_5_ok,
    tttLargeFiber76Block1Chunk2ParentPath_6_ok,
    tttLargeFiber76Block1Chunk2ParentPath_7_ok,
    tttLargeFiber76Block1Chunk2ParentPath_8_ok,
    tttLargeFiber76Block1Chunk2ParentPath_9_ok,
    tttLargeFiber76Block1Chunk2ParentPath_10_ok,
    tttLargeFiber76Block1Chunk2ParentPath_11_ok,
    tttLargeFiber76Block1Chunk2ParentPath_12_ok,
    tttLargeFiber76Block1Chunk2ParentPath_13_ok,
    tttLargeFiber76Block1Chunk2ParentPath_14_ok,
    tttLargeFiber76Block1Chunk2ParentPath_15_ok]

def tttLargeFiber76Block1Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber76CountsAudit &&
    tttLargeFiber76Block1Chunk2SourcesCheck &&
    tttLargeFiber76Block1Chunk2RowsAudit &&
    tttLargeFiber76Block1Chunk2ParentMapAudit &&
    tttLargeFiber76Block1Chunk2ParentsAudit

theorem tttLargeFiber76Block1Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber76Block1Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber76Block1Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber76CountsAudit_ok,
    tttLargeFiber76Block1Chunk2SourcesCheck_ok,
    tttLargeFiber76Block1Chunk2RowsAudit_ok,
    tttLargeFiber76Block1Chunk2ParentMapAudit_ok,
    tttLargeFiber76Block1Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber76Block1Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
