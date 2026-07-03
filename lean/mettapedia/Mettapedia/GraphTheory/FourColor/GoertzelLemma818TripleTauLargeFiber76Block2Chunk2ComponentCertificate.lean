import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber76Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 76, block 2 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber76Block2Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber76Data

def tttLargeFiber76Block2Chunk2Sources : List Nat :=
  [   3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159,
   3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167]

def tttLargeFiber76Row160 : TripleComponentParentRow :=
  tripleRow 3152 3120 90 32 148 90 16 80
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

def tttLargeFiber76Row161 : TripleComponentParentRow :=
  tripleRow 3153 3121 90 32 149 90 16 81
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

def tttLargeFiber76Row162 : TripleComponentParentRow :=
  tripleRow 3154 3122 90 32 150 90 16 82
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

def tttLargeFiber76Row163 : TripleComponentParentRow :=
  tripleRow 3155 3152 90 32 151 90 32 148
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row164 : TripleComponentParentRow :=
  tripleRow 3156 3152 90 32 164 90 32 148
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber76Row165 : TripleComponentParentRow :=
  tripleRow 3157 3153 90 32 165 90 32 149
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber76Row166 : TripleComponentParentRow :=
  tripleRow 3158 3126 90 32 166 90 16 102
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber76Row167 : TripleComponentParentRow :=
  tripleRow 3159 3127 90 32 167 90 16 103
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber76Row168 : TripleComponentParentRow :=
  tripleRow 3160 3128 90 33 156 90 17 88
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

def tttLargeFiber76Row169 : TripleComponentParentRow :=
  tripleRow 3161 3129 90 33 157 90 17 89
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

def tttLargeFiber76Row170 : TripleComponentParentRow :=
  tripleRow 3162 3130 90 33 158 90 17 90
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

def tttLargeFiber76Row171 : TripleComponentParentRow :=
  tripleRow 3163 3160 90 33 159 90 33 156
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber76Row172 : TripleComponentParentRow :=
  tripleRow 3164 3160 90 33 172 90 33 156
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber76Row173 : TripleComponentParentRow :=
  tripleRow 3165 3161 90 33 173 90 33 157
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber76Row174 : TripleComponentParentRow :=
  tripleRow 3166 3134 90 33 174 90 17 110
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber76Row175 : TripleComponentParentRow :=
  tripleRow 3167 3135 90 33 175 90 17 111
    (chainMove LColor.b LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber76Block2Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber76Row160
  , tttLargeFiber76Row161
  , tttLargeFiber76Row162
  , tttLargeFiber76Row163
  , tttLargeFiber76Row164
  , tttLargeFiber76Row165
  , tttLargeFiber76Row166
  , tttLargeFiber76Row167
  , tttLargeFiber76Row168
  , tttLargeFiber76Row169
  , tttLargeFiber76Row170
  , tttLargeFiber76Row171
  , tttLargeFiber76Row172
  , tttLargeFiber76Row173
  , tttLargeFiber76Row174
  , tttLargeFiber76Row175
  ]

def tttLargeFiber76Block2Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (2992 <= i) && decide (i < 3248)) ||
    (decide (3552 <= i) && decide (i < 3808))

def tttLargeFiber76Block2Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber76Block2Chunk2ExpectedContains row.source &&
    tttLargeFiber76Block2Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber76Key &&
          chainInputKey tttWord t == tttLargeFiber76Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber76Block2Chunk2SourcesCheck : Bool :=
  (tttLargeFiber76Block2Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber76Block2Chunk2Sources

theorem tttLargeFiber76Block2Chunk2SourcesCheck_ok :
    tttLargeFiber76Block2Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber76Block2Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber76Block2Chunk2RowValid
    (listGetD tttLargeFiber76Block2Chunk2Rows i default)

def tttLargeFiber76Block2Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber76Block2Chunk2Rows i default
  row.parent == tttLargeFiber76ParentOf row.source

def tttLargeFiber76Block2Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber76Block2Chunk2Sources 0 0 == 3152
      && tttLargeFiber76ParentOf 3152 == 3120
      && tttLargeFiber76ParentOf 3120 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (2 <= tttLargeFiber76MaxParentDepth)
  | 1 => listGetD tttLargeFiber76Block2Chunk2Sources 1 0 == 3153
      && tttLargeFiber76ParentOf 3153 == 3121
      && tttLargeFiber76ParentOf 3121 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 2 => listGetD tttLargeFiber76Block2Chunk2Sources 2 0 == 3154
      && tttLargeFiber76ParentOf 3154 == 3122
      && tttLargeFiber76ParentOf 3122 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 3 => listGetD tttLargeFiber76Block2Chunk2Sources 3 0 == 3155
      && tttLargeFiber76ParentOf 3155 == 3152
      && tttLargeFiber76ParentOf 3152 == 3120
      && tttLargeFiber76ParentOf 3120 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 4 => listGetD tttLargeFiber76Block2Chunk2Sources 4 0 == 3156
      && tttLargeFiber76ParentOf 3156 == 3152
      && tttLargeFiber76ParentOf 3152 == 3120
      && tttLargeFiber76ParentOf 3120 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 5 => listGetD tttLargeFiber76Block2Chunk2Sources 5 0 == 3157
      && tttLargeFiber76ParentOf 3157 == 3153
      && tttLargeFiber76ParentOf 3153 == 3121
      && tttLargeFiber76ParentOf 3121 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 6 => listGetD tttLargeFiber76Block2Chunk2Sources 6 0 == 3158
      && tttLargeFiber76ParentOf 3158 == 3126
      && tttLargeFiber76ParentOf 3126 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 7 => listGetD tttLargeFiber76Block2Chunk2Sources 7 0 == 3159
      && tttLargeFiber76ParentOf 3159 == 3127
      && tttLargeFiber76ParentOf 3127 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 8 => listGetD tttLargeFiber76Block2Chunk2Sources 8 0 == 3160
      && tttLargeFiber76ParentOf 3160 == 3128
      && tttLargeFiber76ParentOf 3128 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (3 <= tttLargeFiber76MaxParentDepth)
  | 9 => listGetD tttLargeFiber76Block2Chunk2Sources 9 0 == 3161
      && tttLargeFiber76ParentOf 3161 == 3129
      && tttLargeFiber76ParentOf 3129 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 10 => listGetD tttLargeFiber76Block2Chunk2Sources 10 0 == 3162
      && tttLargeFiber76ParentOf 3162 == 3130
      && tttLargeFiber76ParentOf 3130 == 3002
      && tttLargeFiber76ParentOf 3002 == 2994
      && tttLargeFiber76ParentOf 2994 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 11 => listGetD tttLargeFiber76Block2Chunk2Sources 11 0 == 3163
      && tttLargeFiber76ParentOf 3163 == 3160
      && tttLargeFiber76ParentOf 3160 == 3128
      && tttLargeFiber76ParentOf 3128 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 12 => listGetD tttLargeFiber76Block2Chunk2Sources 12 0 == 3164
      && tttLargeFiber76ParentOf 3164 == 3160
      && tttLargeFiber76ParentOf 3160 == 3128
      && tttLargeFiber76ParentOf 3128 == 3000
      && tttLargeFiber76ParentOf 3000 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | 13 => listGetD tttLargeFiber76Block2Chunk2Sources 13 0 == 3165
      && tttLargeFiber76ParentOf 3165 == 3161
      && tttLargeFiber76ParentOf 3161 == 3129
      && tttLargeFiber76ParentOf 3129 == 3001
      && tttLargeFiber76ParentOf 3001 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 14 => listGetD tttLargeFiber76Block2Chunk2Sources 14 0 == 3166
      && tttLargeFiber76ParentOf 3166 == 3134
      && tttLargeFiber76ParentOf 3134 == 3006
      && tttLargeFiber76ParentOf 3006 == 2998
      && tttLargeFiber76ParentOf 2998 == 2993
      && tttLargeFiber76ParentOf 2993 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (5 <= tttLargeFiber76MaxParentDepth)
  | 15 => listGetD tttLargeFiber76Block2Chunk2Sources 15 0 == 3167
      && tttLargeFiber76ParentOf 3167 == 3135
      && tttLargeFiber76ParentOf 3135 == 3007
      && tttLargeFiber76ParentOf 3007 == 2999
      && tttLargeFiber76ParentOf 2999 == 2992
      && 2992 == tttLargeFiber76Root
      && decide (4 <= tttLargeFiber76MaxParentDepth)
  | _ => false

theorem tttLargeFiber76Block2Chunk2Row_0_ok :
    tttLargeFiber76Block2Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2Row_1_ok :
    tttLargeFiber76Block2Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2Row_2_ok :
    tttLargeFiber76Block2Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2Row_3_ok :
    tttLargeFiber76Block2Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2Row_4_ok :
    tttLargeFiber76Block2Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2Row_5_ok :
    tttLargeFiber76Block2Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2Row_6_ok :
    tttLargeFiber76Block2Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2Row_7_ok :
    tttLargeFiber76Block2Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2Row_8_ok :
    tttLargeFiber76Block2Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2Row_9_ok :
    tttLargeFiber76Block2Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2Row_10_ok :
    tttLargeFiber76Block2Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2Row_11_ok :
    tttLargeFiber76Block2Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2Row_12_ok :
    tttLargeFiber76Block2Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2Row_13_ok :
    tttLargeFiber76Block2Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2Row_14_ok :
    tttLargeFiber76Block2Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2Row_15_ok :
    tttLargeFiber76Block2Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentMap_0_ok :
    tttLargeFiber76Block2Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentMap_1_ok :
    tttLargeFiber76Block2Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentMap_2_ok :
    tttLargeFiber76Block2Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentMap_3_ok :
    tttLargeFiber76Block2Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentMap_4_ok :
    tttLargeFiber76Block2Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentMap_5_ok :
    tttLargeFiber76Block2Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentMap_6_ok :
    tttLargeFiber76Block2Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentMap_7_ok :
    tttLargeFiber76Block2Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentMap_8_ok :
    tttLargeFiber76Block2Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentMap_9_ok :
    tttLargeFiber76Block2Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentMap_10_ok :
    tttLargeFiber76Block2Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentMap_11_ok :
    tttLargeFiber76Block2Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentMap_12_ok :
    tttLargeFiber76Block2Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentMap_13_ok :
    tttLargeFiber76Block2Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentMap_14_ok :
    tttLargeFiber76Block2Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentMap_15_ok :
    tttLargeFiber76Block2Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentPath_0_ok :
    tttLargeFiber76Block2Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentPath_1_ok :
    tttLargeFiber76Block2Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentPath_2_ok :
    tttLargeFiber76Block2Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentPath_3_ok :
    tttLargeFiber76Block2Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentPath_4_ok :
    tttLargeFiber76Block2Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentPath_5_ok :
    tttLargeFiber76Block2Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentPath_6_ok :
    tttLargeFiber76Block2Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentPath_7_ok :
    tttLargeFiber76Block2Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentPath_8_ok :
    tttLargeFiber76Block2Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentPath_9_ok :
    tttLargeFiber76Block2Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentPath_10_ok :
    tttLargeFiber76Block2Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentPath_11_ok :
    tttLargeFiber76Block2Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentPath_12_ok :
    tttLargeFiber76Block2Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentPath_13_ok :
    tttLargeFiber76Block2Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentPath_14_ok :
    tttLargeFiber76Block2Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber76Block2Chunk2ParentPath_15_ok :
    tttLargeFiber76Block2Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber76Block2Chunk2RowsAudit : Bool :=
  tttLargeFiber76Block2Chunk2RowCheck 0
    && tttLargeFiber76Block2Chunk2RowCheck 1
    && tttLargeFiber76Block2Chunk2RowCheck 2
    && tttLargeFiber76Block2Chunk2RowCheck 3
    && tttLargeFiber76Block2Chunk2RowCheck 4
    && tttLargeFiber76Block2Chunk2RowCheck 5
    && tttLargeFiber76Block2Chunk2RowCheck 6
    && tttLargeFiber76Block2Chunk2RowCheck 7
    && tttLargeFiber76Block2Chunk2RowCheck 8
    && tttLargeFiber76Block2Chunk2RowCheck 9
    && tttLargeFiber76Block2Chunk2RowCheck 10
    && tttLargeFiber76Block2Chunk2RowCheck 11
    && tttLargeFiber76Block2Chunk2RowCheck 12
    && tttLargeFiber76Block2Chunk2RowCheck 13
    && tttLargeFiber76Block2Chunk2RowCheck 14
    && tttLargeFiber76Block2Chunk2RowCheck 15

theorem tttLargeFiber76Block2Chunk2RowsAudit_ok :
    tttLargeFiber76Block2Chunk2RowsAudit = true := by
  simp [tttLargeFiber76Block2Chunk2RowsAudit,
    tttLargeFiber76Block2Chunk2Row_0_ok,
    tttLargeFiber76Block2Chunk2Row_1_ok,
    tttLargeFiber76Block2Chunk2Row_2_ok,
    tttLargeFiber76Block2Chunk2Row_3_ok,
    tttLargeFiber76Block2Chunk2Row_4_ok,
    tttLargeFiber76Block2Chunk2Row_5_ok,
    tttLargeFiber76Block2Chunk2Row_6_ok,
    tttLargeFiber76Block2Chunk2Row_7_ok,
    tttLargeFiber76Block2Chunk2Row_8_ok,
    tttLargeFiber76Block2Chunk2Row_9_ok,
    tttLargeFiber76Block2Chunk2Row_10_ok,
    tttLargeFiber76Block2Chunk2Row_11_ok,
    tttLargeFiber76Block2Chunk2Row_12_ok,
    tttLargeFiber76Block2Chunk2Row_13_ok,
    tttLargeFiber76Block2Chunk2Row_14_ok,
    tttLargeFiber76Block2Chunk2Row_15_ok]

def tttLargeFiber76Block2Chunk2ParentMapAudit : Bool :=
  tttLargeFiber76Block2Chunk2ParentMapCheck 0
    && tttLargeFiber76Block2Chunk2ParentMapCheck 1
    && tttLargeFiber76Block2Chunk2ParentMapCheck 2
    && tttLargeFiber76Block2Chunk2ParentMapCheck 3
    && tttLargeFiber76Block2Chunk2ParentMapCheck 4
    && tttLargeFiber76Block2Chunk2ParentMapCheck 5
    && tttLargeFiber76Block2Chunk2ParentMapCheck 6
    && tttLargeFiber76Block2Chunk2ParentMapCheck 7
    && tttLargeFiber76Block2Chunk2ParentMapCheck 8
    && tttLargeFiber76Block2Chunk2ParentMapCheck 9
    && tttLargeFiber76Block2Chunk2ParentMapCheck 10
    && tttLargeFiber76Block2Chunk2ParentMapCheck 11
    && tttLargeFiber76Block2Chunk2ParentMapCheck 12
    && tttLargeFiber76Block2Chunk2ParentMapCheck 13
    && tttLargeFiber76Block2Chunk2ParentMapCheck 14
    && tttLargeFiber76Block2Chunk2ParentMapCheck 15

theorem tttLargeFiber76Block2Chunk2ParentMapAudit_ok :
    tttLargeFiber76Block2Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber76Block2Chunk2ParentMapAudit,
    tttLargeFiber76Block2Chunk2ParentMap_0_ok,
    tttLargeFiber76Block2Chunk2ParentMap_1_ok,
    tttLargeFiber76Block2Chunk2ParentMap_2_ok,
    tttLargeFiber76Block2Chunk2ParentMap_3_ok,
    tttLargeFiber76Block2Chunk2ParentMap_4_ok,
    tttLargeFiber76Block2Chunk2ParentMap_5_ok,
    tttLargeFiber76Block2Chunk2ParentMap_6_ok,
    tttLargeFiber76Block2Chunk2ParentMap_7_ok,
    tttLargeFiber76Block2Chunk2ParentMap_8_ok,
    tttLargeFiber76Block2Chunk2ParentMap_9_ok,
    tttLargeFiber76Block2Chunk2ParentMap_10_ok,
    tttLargeFiber76Block2Chunk2ParentMap_11_ok,
    tttLargeFiber76Block2Chunk2ParentMap_12_ok,
    tttLargeFiber76Block2Chunk2ParentMap_13_ok,
    tttLargeFiber76Block2Chunk2ParentMap_14_ok,
    tttLargeFiber76Block2Chunk2ParentMap_15_ok]

def tttLargeFiber76Block2Chunk2ParentsAudit : Bool :=
  tttLargeFiber76Block2Chunk2ParentPathCheck 0
    && tttLargeFiber76Block2Chunk2ParentPathCheck 1
    && tttLargeFiber76Block2Chunk2ParentPathCheck 2
    && tttLargeFiber76Block2Chunk2ParentPathCheck 3
    && tttLargeFiber76Block2Chunk2ParentPathCheck 4
    && tttLargeFiber76Block2Chunk2ParentPathCheck 5
    && tttLargeFiber76Block2Chunk2ParentPathCheck 6
    && tttLargeFiber76Block2Chunk2ParentPathCheck 7
    && tttLargeFiber76Block2Chunk2ParentPathCheck 8
    && tttLargeFiber76Block2Chunk2ParentPathCheck 9
    && tttLargeFiber76Block2Chunk2ParentPathCheck 10
    && tttLargeFiber76Block2Chunk2ParentPathCheck 11
    && tttLargeFiber76Block2Chunk2ParentPathCheck 12
    && tttLargeFiber76Block2Chunk2ParentPathCheck 13
    && tttLargeFiber76Block2Chunk2ParentPathCheck 14
    && tttLargeFiber76Block2Chunk2ParentPathCheck 15

theorem tttLargeFiber76Block2Chunk2ParentsAudit_ok :
    tttLargeFiber76Block2Chunk2ParentsAudit = true := by
  simp [tttLargeFiber76Block2Chunk2ParentsAudit,
    tttLargeFiber76Block2Chunk2ParentPath_0_ok,
    tttLargeFiber76Block2Chunk2ParentPath_1_ok,
    tttLargeFiber76Block2Chunk2ParentPath_2_ok,
    tttLargeFiber76Block2Chunk2ParentPath_3_ok,
    tttLargeFiber76Block2Chunk2ParentPath_4_ok,
    tttLargeFiber76Block2Chunk2ParentPath_5_ok,
    tttLargeFiber76Block2Chunk2ParentPath_6_ok,
    tttLargeFiber76Block2Chunk2ParentPath_7_ok,
    tttLargeFiber76Block2Chunk2ParentPath_8_ok,
    tttLargeFiber76Block2Chunk2ParentPath_9_ok,
    tttLargeFiber76Block2Chunk2ParentPath_10_ok,
    tttLargeFiber76Block2Chunk2ParentPath_11_ok,
    tttLargeFiber76Block2Chunk2ParentPath_12_ok,
    tttLargeFiber76Block2Chunk2ParentPath_13_ok,
    tttLargeFiber76Block2Chunk2ParentPath_14_ok,
    tttLargeFiber76Block2Chunk2ParentPath_15_ok]

def tttLargeFiber76Block2Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber76CountsAudit &&
    tttLargeFiber76Block2Chunk2SourcesCheck &&
    tttLargeFiber76Block2Chunk2RowsAudit &&
    tttLargeFiber76Block2Chunk2ParentMapAudit &&
    tttLargeFiber76Block2Chunk2ParentsAudit

theorem tttLargeFiber76Block2Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber76Block2Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber76Block2Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber76CountsAudit_ok,
    tttLargeFiber76Block2Chunk2SourcesCheck_ok,
    tttLargeFiber76Block2Chunk2RowsAudit_ok,
    tttLargeFiber76Block2Chunk2ParentMapAudit_ok,
    tttLargeFiber76Block2Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber76Block2Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
