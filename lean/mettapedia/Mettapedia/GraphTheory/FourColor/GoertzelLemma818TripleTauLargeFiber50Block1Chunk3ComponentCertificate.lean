import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber50Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 50, block 1 chunk 3

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber50Block1Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber50Data

def tttLargeFiber50Block1Chunk3Sources : List Nat :=
  [   5296, 5297, 5298, 5299, 5300, 5301, 5302, 5303,
   5304, 5305, 5306, 5307, 5308, 5309, 5310, 5311]

def tttLargeFiber50Row112 : TripleComponentParentRow :=
  tripleRow 5296 5232 157 174 64 156 166 64
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row113 : TripleComponentParentRow :=
  tripleRow 5297 5233 157 174 65 156 166 65
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row114 : TripleComponentParentRow :=
  tripleRow 5298 5234 157 174 66 156 166 66
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row115 : TripleComponentParentRow :=
  tripleRow 5299 5235 157 174 67 156 166 67
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row116 : TripleComponentParentRow :=
  tripleRow 5300 5236 157 174 116 156 166 116
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row117 : TripleComponentParentRow :=
  tripleRow 5301 5237 157 174 117 156 166 117
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row118 : TripleComponentParentRow :=
  tripleRow 5302 5238 157 174 118 156 166 118
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row119 : TripleComponentParentRow :=
  tripleRow 5303 5239 157 174 119 156 166 119
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row120 : TripleComponentParentRow :=
  tripleRow 5304 5240 157 175 72 156 167 72
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row121 : TripleComponentParentRow :=
  tripleRow 5305 5241 157 175 73 156 167 73
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row122 : TripleComponentParentRow :=
  tripleRow 5306 5242 157 175 74 156 167 74
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row123 : TripleComponentParentRow :=
  tripleRow 5307 5243 157 175 75 156 167 75
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row124 : TripleComponentParentRow :=
  tripleRow 5308 5244 157 175 124 156 167 124
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row125 : TripleComponentParentRow :=
  tripleRow 5309 5245 157 175 125 156 167 125
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row126 : TripleComponentParentRow :=
  tripleRow 5310 5246 157 175 126 156 167 126
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row127 : TripleComponentParentRow :=
  tripleRow 5311 5247 157 175 127 156 167 127
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Block1Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber50Row112
  , tttLargeFiber50Row113
  , tttLargeFiber50Row114
  , tttLargeFiber50Row115
  , tttLargeFiber50Row116
  , tttLargeFiber50Row117
  , tttLargeFiber50Row118
  , tttLargeFiber50Row119
  , tttLargeFiber50Row120
  , tttLargeFiber50Row121
  , tttLargeFiber50Row122
  , tttLargeFiber50Row123
  , tttLargeFiber50Row124
  , tttLargeFiber50Row125
  , tttLargeFiber50Row126
  , tttLargeFiber50Row127
  ]

def tttLargeFiber50Block1Chunk3ExpectedContains (i : Nat) : Bool :=
  (decide (5184 <= i) && decide (i < 5440)) ||
    (decide (5728 <= i) && decide (i < 5984))

def tttLargeFiber50Block1Chunk3RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber50Block1Chunk3ExpectedContains row.source &&
    tttLargeFiber50Block1Chunk3ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber50Key &&
          chainInputKey tttWord t == tttLargeFiber50Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber50Block1Chunk3SourcesCheck : Bool :=
  (tttLargeFiber50Block1Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber50Block1Chunk3Sources

theorem tttLargeFiber50Block1Chunk3SourcesCheck_ok :
    tttLargeFiber50Block1Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber50Block1Chunk3RowCheck (i : Nat) : Bool :=
  tttLargeFiber50Block1Chunk3RowValid
    (listGetD tttLargeFiber50Block1Chunk3Rows i default)

def tttLargeFiber50Block1Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber50Block1Chunk3Rows i default
  row.parent == tttLargeFiber50ParentOf row.source

def tttLargeFiber50Block1Chunk3ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber50Block1Chunk3Sources 0 0 == 5296
      && tttLargeFiber50ParentOf 5296 == 5232
      && tttLargeFiber50ParentOf 5232 == 5216
      && tttLargeFiber50ParentOf 5216 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 1 => listGetD tttLargeFiber50Block1Chunk3Sources 1 0 == 5297
      && tttLargeFiber50ParentOf 5297 == 5233
      && tttLargeFiber50ParentOf 5233 == 5217
      && tttLargeFiber50ParentOf 5217 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 2 => listGetD tttLargeFiber50Block1Chunk3Sources 2 0 == 5298
      && tttLargeFiber50ParentOf 5298 == 5234
      && tttLargeFiber50ParentOf 5234 == 5232
      && tttLargeFiber50ParentOf 5232 == 5216
      && tttLargeFiber50ParentOf 5216 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 3 => listGetD tttLargeFiber50Block1Chunk3Sources 3 0 == 5299
      && tttLargeFiber50ParentOf 5299 == 5235
      && tttLargeFiber50ParentOf 5235 == 5219
      && tttLargeFiber50ParentOf 5219 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 4 => listGetD tttLargeFiber50Block1Chunk3Sources 4 0 == 5300
      && tttLargeFiber50ParentOf 5300 == 5236
      && tttLargeFiber50ParentOf 5236 == 5220
      && tttLargeFiber50ParentOf 5220 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 5 => listGetD tttLargeFiber50Block1Chunk3Sources 5 0 == 5301
      && tttLargeFiber50ParentOf 5301 == 5237
      && tttLargeFiber50ParentOf 5237 == 5221
      && tttLargeFiber50ParentOf 5221 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 6 => listGetD tttLargeFiber50Block1Chunk3Sources 6 0 == 5302
      && tttLargeFiber50ParentOf 5302 == 5238
      && tttLargeFiber50ParentOf 5238 == 5233
      && tttLargeFiber50ParentOf 5233 == 5217
      && tttLargeFiber50ParentOf 5217 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 7 => listGetD tttLargeFiber50Block1Chunk3Sources 7 0 == 5303
      && tttLargeFiber50ParentOf 5303 == 5239
      && tttLargeFiber50ParentOf 5239 == 5232
      && tttLargeFiber50ParentOf 5232 == 5216
      && tttLargeFiber50ParentOf 5216 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 8 => listGetD tttLargeFiber50Block1Chunk3Sources 8 0 == 5304
      && tttLargeFiber50ParentOf 5304 == 5240
      && tttLargeFiber50ParentOf 5240 == 5224
      && tttLargeFiber50ParentOf 5224 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 9 => listGetD tttLargeFiber50Block1Chunk3Sources 9 0 == 5305
      && tttLargeFiber50ParentOf 5305 == 5241
      && tttLargeFiber50ParentOf 5241 == 5225
      && tttLargeFiber50ParentOf 5225 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 10 => listGetD tttLargeFiber50Block1Chunk3Sources 10 0 == 5306
      && tttLargeFiber50ParentOf 5306 == 5242
      && tttLargeFiber50ParentOf 5242 == 5210
      && tttLargeFiber50ParentOf 5210 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 11 => listGetD tttLargeFiber50Block1Chunk3Sources 11 0 == 5307
      && tttLargeFiber50ParentOf 5307 == 5243
      && tttLargeFiber50ParentOf 5243 == 5211
      && tttLargeFiber50ParentOf 5211 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 12 => listGetD tttLargeFiber50Block1Chunk3Sources 12 0 == 5308
      && tttLargeFiber50ParentOf 5308 == 5244
      && tttLargeFiber50ParentOf 5244 == 5212
      && tttLargeFiber50ParentOf 5212 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 13 => listGetD tttLargeFiber50Block1Chunk3Sources 13 0 == 5309
      && tttLargeFiber50ParentOf 5309 == 5245
      && tttLargeFiber50ParentOf 5245 == 5213
      && tttLargeFiber50ParentOf 5213 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 14 => listGetD tttLargeFiber50Block1Chunk3Sources 14 0 == 5310
      && tttLargeFiber50ParentOf 5310 == 5246
      && tttLargeFiber50ParentOf 5246 == 5244
      && tttLargeFiber50ParentOf 5244 == 5212
      && tttLargeFiber50ParentOf 5212 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 15 => listGetD tttLargeFiber50Block1Chunk3Sources 15 0 == 5311
      && tttLargeFiber50ParentOf 5311 == 5247
      && tttLargeFiber50ParentOf 5247 == 5215
      && tttLargeFiber50ParentOf 5215 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | _ => false

theorem tttLargeFiber50Block1Chunk3Row_0_ok :
    tttLargeFiber50Block1Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3Row_1_ok :
    tttLargeFiber50Block1Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3Row_2_ok :
    tttLargeFiber50Block1Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3Row_3_ok :
    tttLargeFiber50Block1Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3Row_4_ok :
    tttLargeFiber50Block1Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3Row_5_ok :
    tttLargeFiber50Block1Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3Row_6_ok :
    tttLargeFiber50Block1Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3Row_7_ok :
    tttLargeFiber50Block1Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3Row_8_ok :
    tttLargeFiber50Block1Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3Row_9_ok :
    tttLargeFiber50Block1Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3Row_10_ok :
    tttLargeFiber50Block1Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3Row_11_ok :
    tttLargeFiber50Block1Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3Row_12_ok :
    tttLargeFiber50Block1Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3Row_13_ok :
    tttLargeFiber50Block1Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3Row_14_ok :
    tttLargeFiber50Block1Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3Row_15_ok :
    tttLargeFiber50Block1Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentMap_0_ok :
    tttLargeFiber50Block1Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentMap_1_ok :
    tttLargeFiber50Block1Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentMap_2_ok :
    tttLargeFiber50Block1Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentMap_3_ok :
    tttLargeFiber50Block1Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentMap_4_ok :
    tttLargeFiber50Block1Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentMap_5_ok :
    tttLargeFiber50Block1Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentMap_6_ok :
    tttLargeFiber50Block1Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentMap_7_ok :
    tttLargeFiber50Block1Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentMap_8_ok :
    tttLargeFiber50Block1Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentMap_9_ok :
    tttLargeFiber50Block1Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentMap_10_ok :
    tttLargeFiber50Block1Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentMap_11_ok :
    tttLargeFiber50Block1Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentMap_12_ok :
    tttLargeFiber50Block1Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentMap_13_ok :
    tttLargeFiber50Block1Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentMap_14_ok :
    tttLargeFiber50Block1Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentMap_15_ok :
    tttLargeFiber50Block1Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentPath_0_ok :
    tttLargeFiber50Block1Chunk3ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentPath_1_ok :
    tttLargeFiber50Block1Chunk3ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentPath_2_ok :
    tttLargeFiber50Block1Chunk3ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentPath_3_ok :
    tttLargeFiber50Block1Chunk3ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentPath_4_ok :
    tttLargeFiber50Block1Chunk3ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentPath_5_ok :
    tttLargeFiber50Block1Chunk3ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentPath_6_ok :
    tttLargeFiber50Block1Chunk3ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentPath_7_ok :
    tttLargeFiber50Block1Chunk3ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentPath_8_ok :
    tttLargeFiber50Block1Chunk3ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentPath_9_ok :
    tttLargeFiber50Block1Chunk3ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentPath_10_ok :
    tttLargeFiber50Block1Chunk3ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentPath_11_ok :
    tttLargeFiber50Block1Chunk3ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentPath_12_ok :
    tttLargeFiber50Block1Chunk3ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentPath_13_ok :
    tttLargeFiber50Block1Chunk3ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentPath_14_ok :
    tttLargeFiber50Block1Chunk3ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber50Block1Chunk3ParentPath_15_ok :
    tttLargeFiber50Block1Chunk3ParentPathCheck 15 = true := by
  decide

def tttLargeFiber50Block1Chunk3RowsAudit : Bool :=
  tttLargeFiber50Block1Chunk3RowCheck 0
    && tttLargeFiber50Block1Chunk3RowCheck 1
    && tttLargeFiber50Block1Chunk3RowCheck 2
    && tttLargeFiber50Block1Chunk3RowCheck 3
    && tttLargeFiber50Block1Chunk3RowCheck 4
    && tttLargeFiber50Block1Chunk3RowCheck 5
    && tttLargeFiber50Block1Chunk3RowCheck 6
    && tttLargeFiber50Block1Chunk3RowCheck 7
    && tttLargeFiber50Block1Chunk3RowCheck 8
    && tttLargeFiber50Block1Chunk3RowCheck 9
    && tttLargeFiber50Block1Chunk3RowCheck 10
    && tttLargeFiber50Block1Chunk3RowCheck 11
    && tttLargeFiber50Block1Chunk3RowCheck 12
    && tttLargeFiber50Block1Chunk3RowCheck 13
    && tttLargeFiber50Block1Chunk3RowCheck 14
    && tttLargeFiber50Block1Chunk3RowCheck 15

theorem tttLargeFiber50Block1Chunk3RowsAudit_ok :
    tttLargeFiber50Block1Chunk3RowsAudit = true := by
  simp [tttLargeFiber50Block1Chunk3RowsAudit,
    tttLargeFiber50Block1Chunk3Row_0_ok,
    tttLargeFiber50Block1Chunk3Row_1_ok,
    tttLargeFiber50Block1Chunk3Row_2_ok,
    tttLargeFiber50Block1Chunk3Row_3_ok,
    tttLargeFiber50Block1Chunk3Row_4_ok,
    tttLargeFiber50Block1Chunk3Row_5_ok,
    tttLargeFiber50Block1Chunk3Row_6_ok,
    tttLargeFiber50Block1Chunk3Row_7_ok,
    tttLargeFiber50Block1Chunk3Row_8_ok,
    tttLargeFiber50Block1Chunk3Row_9_ok,
    tttLargeFiber50Block1Chunk3Row_10_ok,
    tttLargeFiber50Block1Chunk3Row_11_ok,
    tttLargeFiber50Block1Chunk3Row_12_ok,
    tttLargeFiber50Block1Chunk3Row_13_ok,
    tttLargeFiber50Block1Chunk3Row_14_ok,
    tttLargeFiber50Block1Chunk3Row_15_ok]

def tttLargeFiber50Block1Chunk3ParentMapAudit : Bool :=
  tttLargeFiber50Block1Chunk3ParentMapCheck 0
    && tttLargeFiber50Block1Chunk3ParentMapCheck 1
    && tttLargeFiber50Block1Chunk3ParentMapCheck 2
    && tttLargeFiber50Block1Chunk3ParentMapCheck 3
    && tttLargeFiber50Block1Chunk3ParentMapCheck 4
    && tttLargeFiber50Block1Chunk3ParentMapCheck 5
    && tttLargeFiber50Block1Chunk3ParentMapCheck 6
    && tttLargeFiber50Block1Chunk3ParentMapCheck 7
    && tttLargeFiber50Block1Chunk3ParentMapCheck 8
    && tttLargeFiber50Block1Chunk3ParentMapCheck 9
    && tttLargeFiber50Block1Chunk3ParentMapCheck 10
    && tttLargeFiber50Block1Chunk3ParentMapCheck 11
    && tttLargeFiber50Block1Chunk3ParentMapCheck 12
    && tttLargeFiber50Block1Chunk3ParentMapCheck 13
    && tttLargeFiber50Block1Chunk3ParentMapCheck 14
    && tttLargeFiber50Block1Chunk3ParentMapCheck 15

theorem tttLargeFiber50Block1Chunk3ParentMapAudit_ok :
    tttLargeFiber50Block1Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber50Block1Chunk3ParentMapAudit,
    tttLargeFiber50Block1Chunk3ParentMap_0_ok,
    tttLargeFiber50Block1Chunk3ParentMap_1_ok,
    tttLargeFiber50Block1Chunk3ParentMap_2_ok,
    tttLargeFiber50Block1Chunk3ParentMap_3_ok,
    tttLargeFiber50Block1Chunk3ParentMap_4_ok,
    tttLargeFiber50Block1Chunk3ParentMap_5_ok,
    tttLargeFiber50Block1Chunk3ParentMap_6_ok,
    tttLargeFiber50Block1Chunk3ParentMap_7_ok,
    tttLargeFiber50Block1Chunk3ParentMap_8_ok,
    tttLargeFiber50Block1Chunk3ParentMap_9_ok,
    tttLargeFiber50Block1Chunk3ParentMap_10_ok,
    tttLargeFiber50Block1Chunk3ParentMap_11_ok,
    tttLargeFiber50Block1Chunk3ParentMap_12_ok,
    tttLargeFiber50Block1Chunk3ParentMap_13_ok,
    tttLargeFiber50Block1Chunk3ParentMap_14_ok,
    tttLargeFiber50Block1Chunk3ParentMap_15_ok]

def tttLargeFiber50Block1Chunk3ParentsAudit : Bool :=
  tttLargeFiber50Block1Chunk3ParentPathCheck 0
    && tttLargeFiber50Block1Chunk3ParentPathCheck 1
    && tttLargeFiber50Block1Chunk3ParentPathCheck 2
    && tttLargeFiber50Block1Chunk3ParentPathCheck 3
    && tttLargeFiber50Block1Chunk3ParentPathCheck 4
    && tttLargeFiber50Block1Chunk3ParentPathCheck 5
    && tttLargeFiber50Block1Chunk3ParentPathCheck 6
    && tttLargeFiber50Block1Chunk3ParentPathCheck 7
    && tttLargeFiber50Block1Chunk3ParentPathCheck 8
    && tttLargeFiber50Block1Chunk3ParentPathCheck 9
    && tttLargeFiber50Block1Chunk3ParentPathCheck 10
    && tttLargeFiber50Block1Chunk3ParentPathCheck 11
    && tttLargeFiber50Block1Chunk3ParentPathCheck 12
    && tttLargeFiber50Block1Chunk3ParentPathCheck 13
    && tttLargeFiber50Block1Chunk3ParentPathCheck 14
    && tttLargeFiber50Block1Chunk3ParentPathCheck 15

theorem tttLargeFiber50Block1Chunk3ParentsAudit_ok :
    tttLargeFiber50Block1Chunk3ParentsAudit = true := by
  simp [tttLargeFiber50Block1Chunk3ParentsAudit,
    tttLargeFiber50Block1Chunk3ParentPath_0_ok,
    tttLargeFiber50Block1Chunk3ParentPath_1_ok,
    tttLargeFiber50Block1Chunk3ParentPath_2_ok,
    tttLargeFiber50Block1Chunk3ParentPath_3_ok,
    tttLargeFiber50Block1Chunk3ParentPath_4_ok,
    tttLargeFiber50Block1Chunk3ParentPath_5_ok,
    tttLargeFiber50Block1Chunk3ParentPath_6_ok,
    tttLargeFiber50Block1Chunk3ParentPath_7_ok,
    tttLargeFiber50Block1Chunk3ParentPath_8_ok,
    tttLargeFiber50Block1Chunk3ParentPath_9_ok,
    tttLargeFiber50Block1Chunk3ParentPath_10_ok,
    tttLargeFiber50Block1Chunk3ParentPath_11_ok,
    tttLargeFiber50Block1Chunk3ParentPath_12_ok,
    tttLargeFiber50Block1Chunk3ParentPath_13_ok,
    tttLargeFiber50Block1Chunk3ParentPath_14_ok,
    tttLargeFiber50Block1Chunk3ParentPath_15_ok]

def tttLargeFiber50Block1Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber50CountsAudit &&
    tttLargeFiber50Block1Chunk3SourcesCheck &&
    tttLargeFiber50Block1Chunk3RowsAudit &&
    tttLargeFiber50Block1Chunk3ParentMapAudit &&
    tttLargeFiber50Block1Chunk3ParentsAudit

theorem tttLargeFiber50Block1Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber50Block1Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber50Block1Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber50CountsAudit_ok,
    tttLargeFiber50Block1Chunk3SourcesCheck_ok,
    tttLargeFiber50Block1Chunk3RowsAudit_ok,
    tttLargeFiber50Block1Chunk3ParentMapAudit_ok,
    tttLargeFiber50Block1Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber50Block1Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
