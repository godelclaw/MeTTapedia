import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber50Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 50, block 1 chunk 2

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber50Block1Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber50Data

def tttLargeFiber50Block1Chunk2Sources : List Nat :=
  [   5280, 5281, 5282, 5283, 5284, 5285, 5286, 5287,
   5288, 5289, 5290, 5291, 5292, 5293, 5294, 5295]

def tttLargeFiber50Row96 : TripleComponentParentRow :=
  tripleRow 5280 5216 157 172 132 156 164 132
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row97 : TripleComponentParentRow :=
  tripleRow 5281 5217 157 172 133 156 164 133
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row98 : TripleComponentParentRow :=
  tripleRow 5282 5218 157 172 134 156 164 134
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row99 : TripleComponentParentRow :=
  tripleRow 5283 5219 157 172 135 156 164 135
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row100 : TripleComponentParentRow :=
  tripleRow 5284 5220 157 172 180 156 164 180
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row101 : TripleComponentParentRow :=
  tripleRow 5285 5221 157 172 181 156 164 181
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row102 : TripleComponentParentRow :=
  tripleRow 5286 5222 157 172 182 156 164 182
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row103 : TripleComponentParentRow :=
  tripleRow 5287 5223 157 172 183 156 164 183
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row104 : TripleComponentParentRow :=
  tripleRow 5288 5224 157 173 140 156 165 140
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row105 : TripleComponentParentRow :=
  tripleRow 5289 5225 157 173 141 156 165 141
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row106 : TripleComponentParentRow :=
  tripleRow 5290 5226 157 173 142 156 165 142
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row107 : TripleComponentParentRow :=
  tripleRow 5291 5227 157 173 143 156 165 143
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row108 : TripleComponentParentRow :=
  tripleRow 5292 5228 157 173 188 156 165 188
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row109 : TripleComponentParentRow :=
  tripleRow 5293 5229 157 173 189 156 165 189
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row110 : TripleComponentParentRow :=
  tripleRow 5294 5230 157 173 190 156 165 190
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row111 : TripleComponentParentRow :=
  tripleRow 5295 5231 157 173 191 156 165 191
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Block1Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber50Row96
  , tttLargeFiber50Row97
  , tttLargeFiber50Row98
  , tttLargeFiber50Row99
  , tttLargeFiber50Row100
  , tttLargeFiber50Row101
  , tttLargeFiber50Row102
  , tttLargeFiber50Row103
  , tttLargeFiber50Row104
  , tttLargeFiber50Row105
  , tttLargeFiber50Row106
  , tttLargeFiber50Row107
  , tttLargeFiber50Row108
  , tttLargeFiber50Row109
  , tttLargeFiber50Row110
  , tttLargeFiber50Row111
  ]

def tttLargeFiber50Block1Chunk2ExpectedContains (i : Nat) : Bool :=
  (decide (5184 <= i) && decide (i < 5440)) ||
    (decide (5728 <= i) && decide (i < 5984))

def tttLargeFiber50Block1Chunk2RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber50Block1Chunk2ExpectedContains row.source &&
    tttLargeFiber50Block1Chunk2ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber50Key &&
          chainInputKey tttWord t == tttLargeFiber50Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber50Block1Chunk2SourcesCheck : Bool :=
  (tttLargeFiber50Block1Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber50Block1Chunk2Sources

theorem tttLargeFiber50Block1Chunk2SourcesCheck_ok :
    tttLargeFiber50Block1Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber50Block1Chunk2RowCheck (i : Nat) : Bool :=
  tttLargeFiber50Block1Chunk2RowValid
    (listGetD tttLargeFiber50Block1Chunk2Rows i default)

def tttLargeFiber50Block1Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber50Block1Chunk2Rows i default
  row.parent == tttLargeFiber50ParentOf row.source

def tttLargeFiber50Block1Chunk2ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber50Block1Chunk2Sources 0 0 == 5280
      && tttLargeFiber50ParentOf 5280 == 5216
      && tttLargeFiber50ParentOf 5216 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 1 => listGetD tttLargeFiber50Block1Chunk2Sources 1 0 == 5281
      && tttLargeFiber50ParentOf 5281 == 5217
      && tttLargeFiber50ParentOf 5217 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 2 => listGetD tttLargeFiber50Block1Chunk2Sources 2 0 == 5282
      && tttLargeFiber50ParentOf 5282 == 5218
      && tttLargeFiber50ParentOf 5218 == 5186
      && tttLargeFiber50ParentOf 5186 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 3 => listGetD tttLargeFiber50Block1Chunk2Sources 3 0 == 5283
      && tttLargeFiber50ParentOf 5283 == 5219
      && tttLargeFiber50ParentOf 5219 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 4 => listGetD tttLargeFiber50Block1Chunk2Sources 4 0 == 5284
      && tttLargeFiber50ParentOf 5284 == 5220
      && tttLargeFiber50ParentOf 5220 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 5 => listGetD tttLargeFiber50Block1Chunk2Sources 5 0 == 5285
      && tttLargeFiber50ParentOf 5285 == 5221
      && tttLargeFiber50ParentOf 5221 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 6 => listGetD tttLargeFiber50Block1Chunk2Sources 6 0 == 5286
      && tttLargeFiber50ParentOf 5286 == 5222
      && tttLargeFiber50ParentOf 5222 == 5190
      && tttLargeFiber50ParentOf 5190 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 7 => listGetD tttLargeFiber50Block1Chunk2Sources 7 0 == 5287
      && tttLargeFiber50ParentOf 5287 == 5223
      && tttLargeFiber50ParentOf 5223 == 5191
      && tttLargeFiber50ParentOf 5191 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 8 => listGetD tttLargeFiber50Block1Chunk2Sources 8 0 == 5288
      && tttLargeFiber50ParentOf 5288 == 5224
      && tttLargeFiber50ParentOf 5224 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 9 => listGetD tttLargeFiber50Block1Chunk2Sources 9 0 == 5289
      && tttLargeFiber50ParentOf 5289 == 5225
      && tttLargeFiber50ParentOf 5225 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 10 => listGetD tttLargeFiber50Block1Chunk2Sources 10 0 == 5290
      && tttLargeFiber50ParentOf 5290 == 5226
      && tttLargeFiber50ParentOf 5226 == 5194
      && tttLargeFiber50ParentOf 5194 == 5186
      && tttLargeFiber50ParentOf 5186 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 11 => listGetD tttLargeFiber50Block1Chunk2Sources 11 0 == 5291
      && tttLargeFiber50ParentOf 5291 == 5227
      && tttLargeFiber50ParentOf 5227 == 5195
      && tttLargeFiber50ParentOf 5195 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 12 => listGetD tttLargeFiber50Block1Chunk2Sources 12 0 == 5292
      && tttLargeFiber50ParentOf 5292 == 5228
      && tttLargeFiber50ParentOf 5228 == 5196
      && tttLargeFiber50ParentOf 5196 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 13 => listGetD tttLargeFiber50Block1Chunk2Sources 13 0 == 5293
      && tttLargeFiber50ParentOf 5293 == 5229
      && tttLargeFiber50ParentOf 5229 == 5197
      && tttLargeFiber50ParentOf 5197 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 14 => listGetD tttLargeFiber50Block1Chunk2Sources 14 0 == 5294
      && tttLargeFiber50ParentOf 5294 == 5230
      && tttLargeFiber50ParentOf 5230 == 5198
      && tttLargeFiber50ParentOf 5198 == 5190
      && tttLargeFiber50ParentOf 5190 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 15 => listGetD tttLargeFiber50Block1Chunk2Sources 15 0 == 5295
      && tttLargeFiber50ParentOf 5295 == 5231
      && tttLargeFiber50ParentOf 5231 == 5199
      && tttLargeFiber50ParentOf 5199 == 5191
      && tttLargeFiber50ParentOf 5191 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | _ => false

theorem tttLargeFiber50Block1Chunk2Row_0_ok :
    tttLargeFiber50Block1Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2Row_1_ok :
    tttLargeFiber50Block1Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2Row_2_ok :
    tttLargeFiber50Block1Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2Row_3_ok :
    tttLargeFiber50Block1Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2Row_4_ok :
    tttLargeFiber50Block1Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2Row_5_ok :
    tttLargeFiber50Block1Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2Row_6_ok :
    tttLargeFiber50Block1Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2Row_7_ok :
    tttLargeFiber50Block1Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2Row_8_ok :
    tttLargeFiber50Block1Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2Row_9_ok :
    tttLargeFiber50Block1Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2Row_10_ok :
    tttLargeFiber50Block1Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2Row_11_ok :
    tttLargeFiber50Block1Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2Row_12_ok :
    tttLargeFiber50Block1Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2Row_13_ok :
    tttLargeFiber50Block1Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2Row_14_ok :
    tttLargeFiber50Block1Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2Row_15_ok :
    tttLargeFiber50Block1Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentMap_0_ok :
    tttLargeFiber50Block1Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentMap_1_ok :
    tttLargeFiber50Block1Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentMap_2_ok :
    tttLargeFiber50Block1Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentMap_3_ok :
    tttLargeFiber50Block1Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentMap_4_ok :
    tttLargeFiber50Block1Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentMap_5_ok :
    tttLargeFiber50Block1Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentMap_6_ok :
    tttLargeFiber50Block1Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentMap_7_ok :
    tttLargeFiber50Block1Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentMap_8_ok :
    tttLargeFiber50Block1Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentMap_9_ok :
    tttLargeFiber50Block1Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentMap_10_ok :
    tttLargeFiber50Block1Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentMap_11_ok :
    tttLargeFiber50Block1Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentMap_12_ok :
    tttLargeFiber50Block1Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentMap_13_ok :
    tttLargeFiber50Block1Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentMap_14_ok :
    tttLargeFiber50Block1Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentMap_15_ok :
    tttLargeFiber50Block1Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentPath_0_ok :
    tttLargeFiber50Block1Chunk2ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentPath_1_ok :
    tttLargeFiber50Block1Chunk2ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentPath_2_ok :
    tttLargeFiber50Block1Chunk2ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentPath_3_ok :
    tttLargeFiber50Block1Chunk2ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentPath_4_ok :
    tttLargeFiber50Block1Chunk2ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentPath_5_ok :
    tttLargeFiber50Block1Chunk2ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentPath_6_ok :
    tttLargeFiber50Block1Chunk2ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentPath_7_ok :
    tttLargeFiber50Block1Chunk2ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentPath_8_ok :
    tttLargeFiber50Block1Chunk2ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentPath_9_ok :
    tttLargeFiber50Block1Chunk2ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentPath_10_ok :
    tttLargeFiber50Block1Chunk2ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentPath_11_ok :
    tttLargeFiber50Block1Chunk2ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentPath_12_ok :
    tttLargeFiber50Block1Chunk2ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentPath_13_ok :
    tttLargeFiber50Block1Chunk2ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentPath_14_ok :
    tttLargeFiber50Block1Chunk2ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber50Block1Chunk2ParentPath_15_ok :
    tttLargeFiber50Block1Chunk2ParentPathCheck 15 = true := by
  decide

def tttLargeFiber50Block1Chunk2RowsAudit : Bool :=
  tttLargeFiber50Block1Chunk2RowCheck 0
    && tttLargeFiber50Block1Chunk2RowCheck 1
    && tttLargeFiber50Block1Chunk2RowCheck 2
    && tttLargeFiber50Block1Chunk2RowCheck 3
    && tttLargeFiber50Block1Chunk2RowCheck 4
    && tttLargeFiber50Block1Chunk2RowCheck 5
    && tttLargeFiber50Block1Chunk2RowCheck 6
    && tttLargeFiber50Block1Chunk2RowCheck 7
    && tttLargeFiber50Block1Chunk2RowCheck 8
    && tttLargeFiber50Block1Chunk2RowCheck 9
    && tttLargeFiber50Block1Chunk2RowCheck 10
    && tttLargeFiber50Block1Chunk2RowCheck 11
    && tttLargeFiber50Block1Chunk2RowCheck 12
    && tttLargeFiber50Block1Chunk2RowCheck 13
    && tttLargeFiber50Block1Chunk2RowCheck 14
    && tttLargeFiber50Block1Chunk2RowCheck 15

theorem tttLargeFiber50Block1Chunk2RowsAudit_ok :
    tttLargeFiber50Block1Chunk2RowsAudit = true := by
  simp [tttLargeFiber50Block1Chunk2RowsAudit,
    tttLargeFiber50Block1Chunk2Row_0_ok,
    tttLargeFiber50Block1Chunk2Row_1_ok,
    tttLargeFiber50Block1Chunk2Row_2_ok,
    tttLargeFiber50Block1Chunk2Row_3_ok,
    tttLargeFiber50Block1Chunk2Row_4_ok,
    tttLargeFiber50Block1Chunk2Row_5_ok,
    tttLargeFiber50Block1Chunk2Row_6_ok,
    tttLargeFiber50Block1Chunk2Row_7_ok,
    tttLargeFiber50Block1Chunk2Row_8_ok,
    tttLargeFiber50Block1Chunk2Row_9_ok,
    tttLargeFiber50Block1Chunk2Row_10_ok,
    tttLargeFiber50Block1Chunk2Row_11_ok,
    tttLargeFiber50Block1Chunk2Row_12_ok,
    tttLargeFiber50Block1Chunk2Row_13_ok,
    tttLargeFiber50Block1Chunk2Row_14_ok,
    tttLargeFiber50Block1Chunk2Row_15_ok]

def tttLargeFiber50Block1Chunk2ParentMapAudit : Bool :=
  tttLargeFiber50Block1Chunk2ParentMapCheck 0
    && tttLargeFiber50Block1Chunk2ParentMapCheck 1
    && tttLargeFiber50Block1Chunk2ParentMapCheck 2
    && tttLargeFiber50Block1Chunk2ParentMapCheck 3
    && tttLargeFiber50Block1Chunk2ParentMapCheck 4
    && tttLargeFiber50Block1Chunk2ParentMapCheck 5
    && tttLargeFiber50Block1Chunk2ParentMapCheck 6
    && tttLargeFiber50Block1Chunk2ParentMapCheck 7
    && tttLargeFiber50Block1Chunk2ParentMapCheck 8
    && tttLargeFiber50Block1Chunk2ParentMapCheck 9
    && tttLargeFiber50Block1Chunk2ParentMapCheck 10
    && tttLargeFiber50Block1Chunk2ParentMapCheck 11
    && tttLargeFiber50Block1Chunk2ParentMapCheck 12
    && tttLargeFiber50Block1Chunk2ParentMapCheck 13
    && tttLargeFiber50Block1Chunk2ParentMapCheck 14
    && tttLargeFiber50Block1Chunk2ParentMapCheck 15

theorem tttLargeFiber50Block1Chunk2ParentMapAudit_ok :
    tttLargeFiber50Block1Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber50Block1Chunk2ParentMapAudit,
    tttLargeFiber50Block1Chunk2ParentMap_0_ok,
    tttLargeFiber50Block1Chunk2ParentMap_1_ok,
    tttLargeFiber50Block1Chunk2ParentMap_2_ok,
    tttLargeFiber50Block1Chunk2ParentMap_3_ok,
    tttLargeFiber50Block1Chunk2ParentMap_4_ok,
    tttLargeFiber50Block1Chunk2ParentMap_5_ok,
    tttLargeFiber50Block1Chunk2ParentMap_6_ok,
    tttLargeFiber50Block1Chunk2ParentMap_7_ok,
    tttLargeFiber50Block1Chunk2ParentMap_8_ok,
    tttLargeFiber50Block1Chunk2ParentMap_9_ok,
    tttLargeFiber50Block1Chunk2ParentMap_10_ok,
    tttLargeFiber50Block1Chunk2ParentMap_11_ok,
    tttLargeFiber50Block1Chunk2ParentMap_12_ok,
    tttLargeFiber50Block1Chunk2ParentMap_13_ok,
    tttLargeFiber50Block1Chunk2ParentMap_14_ok,
    tttLargeFiber50Block1Chunk2ParentMap_15_ok]

def tttLargeFiber50Block1Chunk2ParentsAudit : Bool :=
  tttLargeFiber50Block1Chunk2ParentPathCheck 0
    && tttLargeFiber50Block1Chunk2ParentPathCheck 1
    && tttLargeFiber50Block1Chunk2ParentPathCheck 2
    && tttLargeFiber50Block1Chunk2ParentPathCheck 3
    && tttLargeFiber50Block1Chunk2ParentPathCheck 4
    && tttLargeFiber50Block1Chunk2ParentPathCheck 5
    && tttLargeFiber50Block1Chunk2ParentPathCheck 6
    && tttLargeFiber50Block1Chunk2ParentPathCheck 7
    && tttLargeFiber50Block1Chunk2ParentPathCheck 8
    && tttLargeFiber50Block1Chunk2ParentPathCheck 9
    && tttLargeFiber50Block1Chunk2ParentPathCheck 10
    && tttLargeFiber50Block1Chunk2ParentPathCheck 11
    && tttLargeFiber50Block1Chunk2ParentPathCheck 12
    && tttLargeFiber50Block1Chunk2ParentPathCheck 13
    && tttLargeFiber50Block1Chunk2ParentPathCheck 14
    && tttLargeFiber50Block1Chunk2ParentPathCheck 15

theorem tttLargeFiber50Block1Chunk2ParentsAudit_ok :
    tttLargeFiber50Block1Chunk2ParentsAudit = true := by
  simp [tttLargeFiber50Block1Chunk2ParentsAudit,
    tttLargeFiber50Block1Chunk2ParentPath_0_ok,
    tttLargeFiber50Block1Chunk2ParentPath_1_ok,
    tttLargeFiber50Block1Chunk2ParentPath_2_ok,
    tttLargeFiber50Block1Chunk2ParentPath_3_ok,
    tttLargeFiber50Block1Chunk2ParentPath_4_ok,
    tttLargeFiber50Block1Chunk2ParentPath_5_ok,
    tttLargeFiber50Block1Chunk2ParentPath_6_ok,
    tttLargeFiber50Block1Chunk2ParentPath_7_ok,
    tttLargeFiber50Block1Chunk2ParentPath_8_ok,
    tttLargeFiber50Block1Chunk2ParentPath_9_ok,
    tttLargeFiber50Block1Chunk2ParentPath_10_ok,
    tttLargeFiber50Block1Chunk2ParentPath_11_ok,
    tttLargeFiber50Block1Chunk2ParentPath_12_ok,
    tttLargeFiber50Block1Chunk2ParentPath_13_ok,
    tttLargeFiber50Block1Chunk2ParentPath_14_ok,
    tttLargeFiber50Block1Chunk2ParentPath_15_ok]

def tttLargeFiber50Block1Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber50CountsAudit &&
    tttLargeFiber50Block1Chunk2SourcesCheck &&
    tttLargeFiber50Block1Chunk2RowsAudit &&
    tttLargeFiber50Block1Chunk2ParentMapAudit &&
    tttLargeFiber50Block1Chunk2ParentsAudit

theorem tttLargeFiber50Block1Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber50Block1Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber50Block1Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber50CountsAudit_ok,
    tttLargeFiber50Block1Chunk2SourcesCheck_ok,
    tttLargeFiber50Block1Chunk2RowsAudit_ok,
    tttLargeFiber50Block1Chunk2ParentMapAudit_ok,
    tttLargeFiber50Block1Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber50Block1Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
