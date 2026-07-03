import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber50Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: large `TTT` fiber 50, block 1 chunk 1

This generated module checks 16 explicit-component rows for one
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It uses interval membership and explicit bounded parent paths.
-/

namespace GoertzelLemma818TripleTauLargeFiber50Block1Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber50Data

def tttLargeFiber50Block1Chunk1Sources : List Nat :=
  [   5264, 5265, 5266, 5267, 5268, 5269, 5270, 5271,
   5272, 5273, 5274, 5275, 5276, 5277, 5278, 5279]

def tttLargeFiber50Row80 : TripleComponentParentRow :=
  tripleRow 5264 5200 157 158 0 156 150 0
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row81 : TripleComponentParentRow :=
  tripleRow 5265 5201 157 158 1 156 150 1
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row82 : TripleComponentParentRow :=
  tripleRow 5266 5202 157 158 2 156 150 2
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row83 : TripleComponentParentRow :=
  tripleRow 5267 5203 157 158 3 156 150 3
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row84 : TripleComponentParentRow :=
  tripleRow 5268 5204 157 158 48 156 150 48
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row85 : TripleComponentParentRow :=
  tripleRow 5269 5205 157 158 49 156 150 49
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row86 : TripleComponentParentRow :=
  tripleRow 5270 5206 157 158 50 156 150 50
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row87 : TripleComponentParentRow :=
  tripleRow 5271 5207 157 158 51 156 150 51
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row88 : TripleComponentParentRow :=
  tripleRow 5272 5208 157 159 8 156 151 8
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row89 : TripleComponentParentRow :=
  tripleRow 5273 5209 157 159 9 156 151 9
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row90 : TripleComponentParentRow :=
  tripleRow 5274 5210 157 159 10 156 151 10
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row91 : TripleComponentParentRow :=
  tripleRow 5275 5211 157 159 11 156 151 11
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row92 : TripleComponentParentRow :=
  tripleRow 5276 5212 157 159 56 156 151 56
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row93 : TripleComponentParentRow :=
  tripleRow 5277 5213 157 159 57 156 151 57
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row94 : TripleComponentParentRow :=
  tripleRow 5278 5214 157 159 58 156 151 58
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Row95 : TripleComponentParentRow :=
  tripleRow 5279 5215 157 159 59 156 151 59
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber50Block1Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber50Row80
  , tttLargeFiber50Row81
  , tttLargeFiber50Row82
  , tttLargeFiber50Row83
  , tttLargeFiber50Row84
  , tttLargeFiber50Row85
  , tttLargeFiber50Row86
  , tttLargeFiber50Row87
  , tttLargeFiber50Row88
  , tttLargeFiber50Row89
  , tttLargeFiber50Row90
  , tttLargeFiber50Row91
  , tttLargeFiber50Row92
  , tttLargeFiber50Row93
  , tttLargeFiber50Row94
  , tttLargeFiber50Row95
  ]

def tttLargeFiber50Block1Chunk1ExpectedContains (i : Nat) : Bool :=
  (decide (5184 <= i) && decide (i < 5440)) ||
    (decide (5728 <= i) && decide (i < 5984))

def tttLargeFiber50Block1Chunk1RowValid
    (row : TripleComponentParentRow) : Bool :=
  tttLargeFiber50Block1Chunk1ExpectedContains row.source &&
    tttLargeFiber50Block1Chunk1ExpectedContains row.parent &&
      let s := tripleStates row.sourceLeft row.sourceMiddle row.sourceRight
      let t := tripleStates row.parentLeft row.parentMiddle row.parentRight
      compatibleChainStates tttWord s && compatibleChainStates tttWord t &&
        chainInputKey tttWord s == tttLargeFiber50Key &&
          chainInputKey tttWord t == tttLargeFiber50Key &&
            (row.source == row.parent ||
              chainCertifiedKempeStep tttWord s t row.cert)

def tttLargeFiber50Block1Chunk1SourcesCheck : Bool :=
  (tttLargeFiber50Block1Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber50Block1Chunk1Sources

theorem tttLargeFiber50Block1Chunk1SourcesCheck_ok :
    tttLargeFiber50Block1Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber50Block1Chunk1RowCheck (i : Nat) : Bool :=
  tttLargeFiber50Block1Chunk1RowValid
    (listGetD tttLargeFiber50Block1Chunk1Rows i default)

def tttLargeFiber50Block1Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber50Block1Chunk1Rows i default
  row.parent == tttLargeFiber50ParentOf row.source

def tttLargeFiber50Block1Chunk1ParentPathCheck : Nat -> Bool
  | 0 => listGetD tttLargeFiber50Block1Chunk1Sources 0 0 == 5264
      && tttLargeFiber50ParentOf 5264 == 5200
      && tttLargeFiber50ParentOf 5200 == 5204
      && tttLargeFiber50ParentOf 5204 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 1 => listGetD tttLargeFiber50Block1Chunk1Sources 1 0 == 5265
      && tttLargeFiber50ParentOf 5265 == 5201
      && tttLargeFiber50ParentOf 5201 == 5205
      && tttLargeFiber50ParentOf 5205 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 2 => listGetD tttLargeFiber50Block1Chunk1Sources 2 0 == 5266
      && tttLargeFiber50ParentOf 5266 == 5202
      && tttLargeFiber50ParentOf 5202 == 5196
      && tttLargeFiber50ParentOf 5196 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 3 => listGetD tttLargeFiber50Block1Chunk1Sources 3 0 == 5267
      && tttLargeFiber50ParentOf 5267 == 5203
      && tttLargeFiber50ParentOf 5203 == 5197
      && tttLargeFiber50ParentOf 5197 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 4 => listGetD tttLargeFiber50Block1Chunk1Sources 4 0 == 5268
      && tttLargeFiber50ParentOf 5268 == 5204
      && tttLargeFiber50ParentOf 5204 == 5192
      && tttLargeFiber50ParentOf 5192 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 5 => listGetD tttLargeFiber50Block1Chunk1Sources 5 0 == 5269
      && tttLargeFiber50ParentOf 5269 == 5205
      && tttLargeFiber50ParentOf 5205 == 5193
      && tttLargeFiber50ParentOf 5193 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 6 => listGetD tttLargeFiber50Block1Chunk1Sources 6 0 == 5270
      && tttLargeFiber50ParentOf 5270 == 5206
      && tttLargeFiber50ParentOf 5206 == 5194
      && tttLargeFiber50ParentOf 5194 == 5186
      && tttLargeFiber50ParentOf 5186 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (5 <= tttLargeFiber50MaxParentDepth)
  | 7 => listGetD tttLargeFiber50Block1Chunk1Sources 7 0 == 5271
      && tttLargeFiber50ParentOf 5271 == 5207
      && tttLargeFiber50ParentOf 5207 == 5195
      && tttLargeFiber50ParentOf 5195 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 8 => listGetD tttLargeFiber50Block1Chunk1Sources 8 0 == 5272
      && tttLargeFiber50ParentOf 5272 == 5208
      && tttLargeFiber50ParentOf 5208 == 5212
      && tttLargeFiber50ParentOf 5212 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 9 => listGetD tttLargeFiber50Block1Chunk1Sources 9 0 == 5273
      && tttLargeFiber50ParentOf 5273 == 5209
      && tttLargeFiber50ParentOf 5209 == 5213
      && tttLargeFiber50ParentOf 5213 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 10 => listGetD tttLargeFiber50Block1Chunk1Sources 10 0 == 5274
      && tttLargeFiber50ParentOf 5274 == 5210
      && tttLargeFiber50ParentOf 5210 == 5188
      && tttLargeFiber50ParentOf 5188 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 11 => listGetD tttLargeFiber50Block1Chunk1Sources 11 0 == 5275
      && tttLargeFiber50ParentOf 5275 == 5211
      && tttLargeFiber50ParentOf 5211 == 5189
      && tttLargeFiber50ParentOf 5189 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 12 => listGetD tttLargeFiber50Block1Chunk1Sources 12 0 == 5276
      && tttLargeFiber50ParentOf 5276 == 5212
      && tttLargeFiber50ParentOf 5212 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (2 <= tttLargeFiber50MaxParentDepth)
  | 13 => listGetD tttLargeFiber50Block1Chunk1Sources 13 0 == 5277
      && tttLargeFiber50ParentOf 5277 == 5213
      && tttLargeFiber50ParentOf 5213 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | 14 => listGetD tttLargeFiber50Block1Chunk1Sources 14 0 == 5278
      && tttLargeFiber50ParentOf 5278 == 5214
      && tttLargeFiber50ParentOf 5214 == 5186
      && tttLargeFiber50ParentOf 5186 == 5185
      && tttLargeFiber50ParentOf 5185 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (4 <= tttLargeFiber50MaxParentDepth)
  | 15 => listGetD tttLargeFiber50Block1Chunk1Sources 15 0 == 5279
      && tttLargeFiber50ParentOf 5279 == 5215
      && tttLargeFiber50ParentOf 5215 == 5187
      && tttLargeFiber50ParentOf 5187 == 5184
      && 5184 == tttLargeFiber50Root
      && decide (3 <= tttLargeFiber50MaxParentDepth)
  | _ => false

theorem tttLargeFiber50Block1Chunk1Row_0_ok :
    tttLargeFiber50Block1Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1Row_1_ok :
    tttLargeFiber50Block1Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1Row_2_ok :
    tttLargeFiber50Block1Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1Row_3_ok :
    tttLargeFiber50Block1Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1Row_4_ok :
    tttLargeFiber50Block1Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1Row_5_ok :
    tttLargeFiber50Block1Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1Row_6_ok :
    tttLargeFiber50Block1Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1Row_7_ok :
    tttLargeFiber50Block1Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1Row_8_ok :
    tttLargeFiber50Block1Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1Row_9_ok :
    tttLargeFiber50Block1Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1Row_10_ok :
    tttLargeFiber50Block1Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1Row_11_ok :
    tttLargeFiber50Block1Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1Row_12_ok :
    tttLargeFiber50Block1Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1Row_13_ok :
    tttLargeFiber50Block1Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1Row_14_ok :
    tttLargeFiber50Block1Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1Row_15_ok :
    tttLargeFiber50Block1Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentMap_0_ok :
    tttLargeFiber50Block1Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentMap_1_ok :
    tttLargeFiber50Block1Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentMap_2_ok :
    tttLargeFiber50Block1Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentMap_3_ok :
    tttLargeFiber50Block1Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentMap_4_ok :
    tttLargeFiber50Block1Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentMap_5_ok :
    tttLargeFiber50Block1Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentMap_6_ok :
    tttLargeFiber50Block1Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentMap_7_ok :
    tttLargeFiber50Block1Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentMap_8_ok :
    tttLargeFiber50Block1Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentMap_9_ok :
    tttLargeFiber50Block1Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentMap_10_ok :
    tttLargeFiber50Block1Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentMap_11_ok :
    tttLargeFiber50Block1Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentMap_12_ok :
    tttLargeFiber50Block1Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentMap_13_ok :
    tttLargeFiber50Block1Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentMap_14_ok :
    tttLargeFiber50Block1Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentMap_15_ok :
    tttLargeFiber50Block1Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentPath_0_ok :
    tttLargeFiber50Block1Chunk1ParentPathCheck 0 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentPath_1_ok :
    tttLargeFiber50Block1Chunk1ParentPathCheck 1 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentPath_2_ok :
    tttLargeFiber50Block1Chunk1ParentPathCheck 2 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentPath_3_ok :
    tttLargeFiber50Block1Chunk1ParentPathCheck 3 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentPath_4_ok :
    tttLargeFiber50Block1Chunk1ParentPathCheck 4 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentPath_5_ok :
    tttLargeFiber50Block1Chunk1ParentPathCheck 5 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentPath_6_ok :
    tttLargeFiber50Block1Chunk1ParentPathCheck 6 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentPath_7_ok :
    tttLargeFiber50Block1Chunk1ParentPathCheck 7 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentPath_8_ok :
    tttLargeFiber50Block1Chunk1ParentPathCheck 8 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentPath_9_ok :
    tttLargeFiber50Block1Chunk1ParentPathCheck 9 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentPath_10_ok :
    tttLargeFiber50Block1Chunk1ParentPathCheck 10 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentPath_11_ok :
    tttLargeFiber50Block1Chunk1ParentPathCheck 11 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentPath_12_ok :
    tttLargeFiber50Block1Chunk1ParentPathCheck 12 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentPath_13_ok :
    tttLargeFiber50Block1Chunk1ParentPathCheck 13 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentPath_14_ok :
    tttLargeFiber50Block1Chunk1ParentPathCheck 14 = true := by
  decide

theorem tttLargeFiber50Block1Chunk1ParentPath_15_ok :
    tttLargeFiber50Block1Chunk1ParentPathCheck 15 = true := by
  decide

def tttLargeFiber50Block1Chunk1RowsAudit : Bool :=
  tttLargeFiber50Block1Chunk1RowCheck 0
    && tttLargeFiber50Block1Chunk1RowCheck 1
    && tttLargeFiber50Block1Chunk1RowCheck 2
    && tttLargeFiber50Block1Chunk1RowCheck 3
    && tttLargeFiber50Block1Chunk1RowCheck 4
    && tttLargeFiber50Block1Chunk1RowCheck 5
    && tttLargeFiber50Block1Chunk1RowCheck 6
    && tttLargeFiber50Block1Chunk1RowCheck 7
    && tttLargeFiber50Block1Chunk1RowCheck 8
    && tttLargeFiber50Block1Chunk1RowCheck 9
    && tttLargeFiber50Block1Chunk1RowCheck 10
    && tttLargeFiber50Block1Chunk1RowCheck 11
    && tttLargeFiber50Block1Chunk1RowCheck 12
    && tttLargeFiber50Block1Chunk1RowCheck 13
    && tttLargeFiber50Block1Chunk1RowCheck 14
    && tttLargeFiber50Block1Chunk1RowCheck 15

theorem tttLargeFiber50Block1Chunk1RowsAudit_ok :
    tttLargeFiber50Block1Chunk1RowsAudit = true := by
  simp [tttLargeFiber50Block1Chunk1RowsAudit,
    tttLargeFiber50Block1Chunk1Row_0_ok,
    tttLargeFiber50Block1Chunk1Row_1_ok,
    tttLargeFiber50Block1Chunk1Row_2_ok,
    tttLargeFiber50Block1Chunk1Row_3_ok,
    tttLargeFiber50Block1Chunk1Row_4_ok,
    tttLargeFiber50Block1Chunk1Row_5_ok,
    tttLargeFiber50Block1Chunk1Row_6_ok,
    tttLargeFiber50Block1Chunk1Row_7_ok,
    tttLargeFiber50Block1Chunk1Row_8_ok,
    tttLargeFiber50Block1Chunk1Row_9_ok,
    tttLargeFiber50Block1Chunk1Row_10_ok,
    tttLargeFiber50Block1Chunk1Row_11_ok,
    tttLargeFiber50Block1Chunk1Row_12_ok,
    tttLargeFiber50Block1Chunk1Row_13_ok,
    tttLargeFiber50Block1Chunk1Row_14_ok,
    tttLargeFiber50Block1Chunk1Row_15_ok]

def tttLargeFiber50Block1Chunk1ParentMapAudit : Bool :=
  tttLargeFiber50Block1Chunk1ParentMapCheck 0
    && tttLargeFiber50Block1Chunk1ParentMapCheck 1
    && tttLargeFiber50Block1Chunk1ParentMapCheck 2
    && tttLargeFiber50Block1Chunk1ParentMapCheck 3
    && tttLargeFiber50Block1Chunk1ParentMapCheck 4
    && tttLargeFiber50Block1Chunk1ParentMapCheck 5
    && tttLargeFiber50Block1Chunk1ParentMapCheck 6
    && tttLargeFiber50Block1Chunk1ParentMapCheck 7
    && tttLargeFiber50Block1Chunk1ParentMapCheck 8
    && tttLargeFiber50Block1Chunk1ParentMapCheck 9
    && tttLargeFiber50Block1Chunk1ParentMapCheck 10
    && tttLargeFiber50Block1Chunk1ParentMapCheck 11
    && tttLargeFiber50Block1Chunk1ParentMapCheck 12
    && tttLargeFiber50Block1Chunk1ParentMapCheck 13
    && tttLargeFiber50Block1Chunk1ParentMapCheck 14
    && tttLargeFiber50Block1Chunk1ParentMapCheck 15

theorem tttLargeFiber50Block1Chunk1ParentMapAudit_ok :
    tttLargeFiber50Block1Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber50Block1Chunk1ParentMapAudit,
    tttLargeFiber50Block1Chunk1ParentMap_0_ok,
    tttLargeFiber50Block1Chunk1ParentMap_1_ok,
    tttLargeFiber50Block1Chunk1ParentMap_2_ok,
    tttLargeFiber50Block1Chunk1ParentMap_3_ok,
    tttLargeFiber50Block1Chunk1ParentMap_4_ok,
    tttLargeFiber50Block1Chunk1ParentMap_5_ok,
    tttLargeFiber50Block1Chunk1ParentMap_6_ok,
    tttLargeFiber50Block1Chunk1ParentMap_7_ok,
    tttLargeFiber50Block1Chunk1ParentMap_8_ok,
    tttLargeFiber50Block1Chunk1ParentMap_9_ok,
    tttLargeFiber50Block1Chunk1ParentMap_10_ok,
    tttLargeFiber50Block1Chunk1ParentMap_11_ok,
    tttLargeFiber50Block1Chunk1ParentMap_12_ok,
    tttLargeFiber50Block1Chunk1ParentMap_13_ok,
    tttLargeFiber50Block1Chunk1ParentMap_14_ok,
    tttLargeFiber50Block1Chunk1ParentMap_15_ok]

def tttLargeFiber50Block1Chunk1ParentsAudit : Bool :=
  tttLargeFiber50Block1Chunk1ParentPathCheck 0
    && tttLargeFiber50Block1Chunk1ParentPathCheck 1
    && tttLargeFiber50Block1Chunk1ParentPathCheck 2
    && tttLargeFiber50Block1Chunk1ParentPathCheck 3
    && tttLargeFiber50Block1Chunk1ParentPathCheck 4
    && tttLargeFiber50Block1Chunk1ParentPathCheck 5
    && tttLargeFiber50Block1Chunk1ParentPathCheck 6
    && tttLargeFiber50Block1Chunk1ParentPathCheck 7
    && tttLargeFiber50Block1Chunk1ParentPathCheck 8
    && tttLargeFiber50Block1Chunk1ParentPathCheck 9
    && tttLargeFiber50Block1Chunk1ParentPathCheck 10
    && tttLargeFiber50Block1Chunk1ParentPathCheck 11
    && tttLargeFiber50Block1Chunk1ParentPathCheck 12
    && tttLargeFiber50Block1Chunk1ParentPathCheck 13
    && tttLargeFiber50Block1Chunk1ParentPathCheck 14
    && tttLargeFiber50Block1Chunk1ParentPathCheck 15

theorem tttLargeFiber50Block1Chunk1ParentsAudit_ok :
    tttLargeFiber50Block1Chunk1ParentsAudit = true := by
  simp [tttLargeFiber50Block1Chunk1ParentsAudit,
    tttLargeFiber50Block1Chunk1ParentPath_0_ok,
    tttLargeFiber50Block1Chunk1ParentPath_1_ok,
    tttLargeFiber50Block1Chunk1ParentPath_2_ok,
    tttLargeFiber50Block1Chunk1ParentPath_3_ok,
    tttLargeFiber50Block1Chunk1ParentPath_4_ok,
    tttLargeFiber50Block1Chunk1ParentPath_5_ok,
    tttLargeFiber50Block1Chunk1ParentPath_6_ok,
    tttLargeFiber50Block1Chunk1ParentPath_7_ok,
    tttLargeFiber50Block1Chunk1ParentPath_8_ok,
    tttLargeFiber50Block1Chunk1ParentPath_9_ok,
    tttLargeFiber50Block1Chunk1ParentPath_10_ok,
    tttLargeFiber50Block1Chunk1ParentPath_11_ok,
    tttLargeFiber50Block1Chunk1ParentPath_12_ok,
    tttLargeFiber50Block1Chunk1ParentPath_13_ok,
    tttLargeFiber50Block1Chunk1ParentPath_14_ok,
    tttLargeFiber50Block1Chunk1ParentPath_15_ok]

def tttLargeFiber50Block1Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber50CountsAudit &&
    tttLargeFiber50Block1Chunk1SourcesCheck &&
    tttLargeFiber50Block1Chunk1RowsAudit &&
    tttLargeFiber50Block1Chunk1ParentMapAudit &&
    tttLargeFiber50Block1Chunk1ParentsAudit

theorem tttLargeFiber50Block1Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber50Block1Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber50Block1Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber50CountsAudit_ok,
    tttLargeFiber50Block1Chunk1SourcesCheck_ok,
    tttLargeFiber50Block1Chunk1RowsAudit_ok,
    tttLargeFiber50Block1Chunk1ParentMapAudit_ok,
    tttLargeFiber50Block1Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber50Block1Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
